/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.Wirtinger
import RiemannDynamics.Analysis.SingularIntegral.Cauchy
import RiemannDynamics.Analysis.SingularIntegral.CalderonZygmund
import RiemannDynamics.Analysis.SingularIntegral.CotlarStein
import RiemannDynamics.Analysis.SingularIntegral.AnnulusIntegral
import RiemannDynamics.Analysis.SingularIntegral.LpDuality
import RiemannDynamics.Analysis.SingularIntegral.RieszThorin
import Carleson.TwoSidedCarleson.Basic
import Carleson.TwoSidedCarleson.WeakCalderonZygmund
import Carleson.TwoSidedCarleson.NontangentialOperator
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Beurling transform

The **Beurling transform** of `μ : ℂ → ℂ` is the principal-value singular
integral

`Tμ(z) = -(1/π) p.v.∫ μ(ζ)/(z - ζ)² dA(ζ)`,

realized here as the `r → 0⁺` limit of the truncated singular integral
`czOperator` (the Carleson-project Calderón–Zygmund operator) with the Beurling
kernel `K(z, ζ) = (z - ζ)⁻²`. It is the holomorphic Wirtinger derivative of the
Cauchy transform, `T = ∂ ∘ P` (`beurling_eq_dz_cauchyTransform`), so it carries
`∂̄f` to `∂f` and inverts the Beltrami equation.

Its analytic content is the engine input to the measurable Riemann mapping
theorem:

* `beurling_l2_isometry` — `T` is an `L²` isometry (Fourier multiplier `ξ̄/ξ`,
  modulus one), so `‖T‖₂ = 1`;
* `beurling_lp_bound` — `T` is bounded `Lᵖ(ℂ) → Lᵖ(ℂ)` for `1 < p < ∞`
  (Calderón–Zygmund: the Beurling kernel satisfies the kernel hypotheses, giving
  weak-(1,1) via `czOperator_weak_1_1`, then `Lᵖ` by real interpolation against
  the `L²` isometry);
* `beurling_opNorm_continuous` — the `Lᵖ` constant tends to `1` as `p → 2`, the
  qualitative input the MRMT Neumann series consumes.
-/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal NNReal Convolution InnerProductSpace

namespace RiemannDynamics

variable {μ : ℂ → ℂ} {z : ℂ} {p : ℝ≥0∞}

/-- The **Beurling transform** `Tμ(z) = -(1/π) p.v.∫ μ(ζ)/(z - ζ)² dA(ζ)`, the
principal value taken as the `r → 0⁺` limit of the truncated Calderón–Zygmund
operator with the Beurling kernel `K(z, ζ) = (z - ζ)⁻²`. -/
noncomputable def beurling (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / (π : ℂ)) * limUnder (𝓝[>] (0 : ℝ))
    (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r μ z)

/-! ## The Beurling kernel as a Calderón–Zygmund kernel

To feed the Beurling transform into the Carleson project's Calderón–Zygmund
machinery (`czOperator_weak_1_1`, real interpolation) we record that its kernel
`K(z, ζ) = (z - ζ)⁻²` is a two-sided Calderón–Zygmund kernel on `ℂ` in Carleson's
sense, with `a = 4`. Two facts are needed: that `ℂ` is a doubling metric measure
space with Carleson constant `defaultA 4 = 2⁴` (it is `ℝ²`, doubling constant
`2² = 4 ≤ 16`), and that `K` satisfies the kernel size and Hölder bounds. The
constant `C_K a = 2 ^ (a ³)` is astronomically larger than the geometric
constants (`π` from the area of a disc, the Lipschitz factor of `(·)⁻²`), so the
bounds hold with room to spare; the regularity exponent `(a : ℝ)⁻¹ = 1/4` is
weaker than the true Lipschitz exponent `1` of `(·)⁻²` away from the diagonal. -/

/-- The **Beurling kernel** `K(z, ζ) = (z - ζ)⁻²`, the Calderón–Zygmund kernel of
the Beurling transform (definitionally the kernel `beurling` truncates). -/
noncomputable def beurlingKernel (z ζ : ℂ) : ℂ := (z - ζ) ^ (-2 : ℤ)

/-- `ℂ = ℝ²` is a doubling metric measure space with Carleson constant
`defaultA 4 = 2⁴ = 16`: its true doubling constant is `2 ^ finrank ℝ ℂ = 4`, and
`4 ≤ 16`. This is the doubling datum the Beurling kernel's Calderón–Zygmund theory
runs over (mirrors Carleson's own `doublingMeasure_real_16` for `ℝ`). -/
noncomputable instance doublingMeasure_complex_defaultA4 :
    DoublingMeasure ℂ (defaultA 4) :=
  (inferInstance : DoublingMeasure ℂ (2 ^ Module.finrank ℝ ℂ)).mono (by
    simp only [defaultA, Complex.finrank_real_complex]; norm_num)

open ENNReal in
/-- The **Beurling kernel is a two-sided Calderón–Zygmund kernel** on `ℂ` (Carleson
sense), with `a = 4`: it is measurable, satisfies the size bound
`‖K z ζ‖ ≤ C_K 4 / vol z ζ`, and is Hölder-`1/4` regular in each argument. These
are the inputs the Carleson weak-`(1,1)` theorem `czOperator_weak_1_1` consumes for
the Beurling transform's `Lᵖ` bound. -/
instance isTwoSidedKernel_beurlingKernel : IsTwoSidedKernel 4 beurlingKernel := by
  -- Shared numeric facts: `C_K 4 = 2^64` and the area of a disc `Real.vol x y = (dist x y)² · π`.
  have hCK : (↑(C_K (4:ℝ)) : ℝ) = 2 ^ (64 : ℕ) := by simp only [C_K]; push_cast; norm_num
  have hvol : ∀ x y : ℂ, Real.vol x y = dist x y ^ 2 * Real.pi := by
    intro x y
    rw [Real.vol, Measure.real, Complex.volume_ball, ENNReal.toReal_mul,
      ← ENNReal.ofReal_pow dist_nonneg, ENNReal.toReal_ofReal (by positivity),
      ENNReal.coe_toReal, NNReal.coe_real_pi]
  refine { measurable_K := ?_, norm_K_le_vol_inv := ?_, norm_K_sub_le := ?_,
           enorm_K_sub_le' := ?_ }
  · -- Field 1: measurability of `(p.1 - p.2)⁻²`.
    have heq : Function.uncurry beurlingKernel
        = fun p : ℂ × ℂ => ((p.1 - p.2) ^ 2)⁻¹ := by
      funext p; rw [Function.uncurry, beurlingKernel, zpow_neg, zpow_two, sq]
    rw [heq]
    exact ((measurable_fst.sub measurable_snd).pow_const 2).inv
  · -- Field 2: size bound `‖K x y‖ ≤ C_K 4 / vol x y`.
    intro x y
    simp only [Nat.cast_ofNat]
    have hnorm : ‖beurlingKernel x y‖ = ‖x - y‖ ^ (-2 : ℤ) := by rw [beurlingKernel, norm_zpow]
    have hdist : ‖x - y‖ = dist x y := (Complex.dist_eq x y).symm
    rw [hnorm, hvol x y, hCK, hdist]
    rcases eq_or_lt_of_le (dist_nonneg : (0:ℝ) ≤ dist x y) with hd | hd
    · rw [← hd]; norm_num
    · have hpi : (0:ℝ) < Real.pi := Real.pi_pos
      rw [zpow_neg, zpow_two, mul_inv, ← zpow_two, le_div_iff₀ (by positivity)]
      have hcancel : (dist x y)⁻¹ ^ 2 * (dist x y ^ 2 * Real.pi) = Real.pi := by field_simp
      calc (dist x y)⁻¹ ^ 2 * (dist x y ^ 2 * Real.pi) = Real.pi := hcancel
        _ ≤ 2 ^ (64 : ℕ) := by nlinarith [Real.pi_le_four]
  · -- Field 3: right Hölder bound.
    intro x y y' h
    simp only [Nat.cast_ofNat]
    rcases eq_or_lt_of_le (dist_nonneg : (0:ℝ) ≤ dist x y) with hdz | hdpos
    · -- `dist x y = 0` forces `y = y'` and the difference is zero.
      have he0 : dist y y' = 0 :=
        le_antisymm (by linarith [h, dist_nonneg (x := y) (y := y')]) dist_nonneg
      have hxy : x = y := by
        have := hdz.symm; rw [dist_eq] at this; rw [← sub_eq_zero]; exact norm_eq_zero.mp this
      have hyy' : y = y' := by
        rw [dist_eq] at he0; rw [← sub_eq_zero]; exact norm_eq_zero.mp he0
      rw [← hyy', hxy]; simp [beurlingKernel]
    · have hdxy : ‖x - y‖ = dist x y := (Complex.dist_eq x y).symm
      have hdyy' : ‖y - y'‖ = dist y y' := (Complex.dist_eq y y').symm
      have hxy_ne : x - y ≠ 0 := by
        rw [sub_ne_zero]; intro he; rw [he] at hdpos; simp at hdpos
      have hnpos : (0:ℝ) < ‖x - y‖ := by rw [hdxy]; exact hdpos
      have hkey : 2 * ‖y - y'‖ ≤ ‖x - y‖ := by rw [hdxy, hdyy']; exact h
      have hyy'_nn : (0:ℝ) ≤ ‖y - y'‖ := norm_nonneg _
      have hsplit : x - y' = (x - y) + (y - y') := by ring
      have hlow : ‖x - y‖ - ‖y - y'‖ ≤ ‖x - y'‖ := by
        have := norm_sub_norm_le (x - y) (-(y - y'))
        rw [norm_neg] at this
        calc ‖x - y‖ - ‖y - y'‖ ≤ ‖(x - y) - (-(y - y'))‖ := this
          _ = ‖x - y'‖ := by rw [sub_neg_eq_add, ← hsplit]
      have hxy'_low : ‖x - y‖ / 2 ≤ ‖x - y'‖ := by linarith
      have hxy'_pos : (0:ℝ) < ‖x - y'‖ := by linarith
      have hxy'_ne : x - y' ≠ 0 := norm_pos_iff.mp hxy'_pos
      have hsplit2 : 2 * x - y - y' = (x - y) + (x - y') := by ring
      have hmid : ‖2 * x - y - y'‖ ≤ (5/2) * ‖x - y‖ := by
        have h1 := norm_add_le (x - y) (x - y'); rw [← hsplit2] at h1
        have h2 := norm_add_le (x - y) (y - y'); rw [← hsplit] at h2; linarith
      have hmid_nn : (0:ℝ) ≤ ‖2 * x - y - y'‖ := norm_nonneg _
      have hfact : beurlingKernel x y - beurlingKernel x y'
          = (y - y') * (2 * x - y - y') / ((x - y) ^ 2 * (x - y') ^ 2) := by
        rw [beurlingKernel, beurlingKernel, zpow_neg, zpow_neg, zpow_two, zpow_two]
        field_simp; ring
      have hnormdiff : ‖beurlingKernel x y - beurlingKernel x y'‖
          = ‖y - y'‖ * ‖2 * x - y - y'‖ / (‖x - y‖ ^ 2 * ‖x - y'‖ ^ 2) := by
        rw [hfact, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
      have hbound1 : ‖beurlingKernel x y - beurlingKernel x y'‖
          ≤ 10 * (‖y - y'‖ / ‖x - y‖) / ‖x - y‖ ^ 2 := by
        rw [hnormdiff]
        have hnum : ‖y - y'‖ * ‖2 * x - y - y'‖ ≤ ‖y - y'‖ * ((5/2) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left hmid hyy'_nn
        have hden : ‖x - y‖ ^ 2 * (‖x - y‖ ^ 2 / 4) ≤ ‖x - y‖ ^ 2 * ‖x - y'‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [hxy'_low, hxy'_pos, hnpos]
        have hden_pos1 : (0:ℝ) < ‖x - y‖ ^ 2 * (‖x - y‖ ^ 2 / 4) := by positivity
        calc ‖y - y'‖ * ‖2 * x - y - y'‖ / (‖x - y‖ ^ 2 * ‖x - y'‖ ^ 2)
            ≤ ‖y - y'‖ * ((5/2) * ‖x - y‖) / (‖x - y‖ ^ 2 * (‖x - y‖ ^ 2 / 4)) :=
              div_le_div₀ (by positivity) hnum hden_pos1 hden
          _ = 10 * (‖y - y'‖ / ‖x - y‖) / ‖x - y‖ ^ 2 := by field_simp; ring
      refine hbound1.trans ?_
      set t := dist y y' / dist x y with ht_def
      have ht_nn : (0:ℝ) ≤ t := by rw [ht_def]; positivity
      have ht_le1 : t ≤ 1 := by
        rw [ht_def, div_le_one hdpos]; linarith [dist_nonneg (x := y) (y := y'), h]
      have hratio_eq : ‖y - y'‖ / ‖x - y‖ = t := by rw [ht_def, hdxy, hdyy']
      rw [hratio_eq, hvol x y, hCK, hdxy]
      have hpi : (0:ℝ) < Real.pi := Real.pi_pos
      have hsq : (0:ℝ) < dist x y ^ 2 := by positivity
      have ht_rpow : t ≤ t ^ ((4:ℝ))⁻¹ := by
        rcases eq_or_lt_of_le ht_nn with h0 | hpos
        · rw [← h0, Real.zero_rpow (by norm_num)]
        · calc t = t ^ (1:ℝ) := (Real.rpow_one t).symm
            _ ≤ t ^ ((4:ℝ))⁻¹ := Real.rpow_le_rpow_of_exponent_ge hpos ht_le1 (by norm_num)
      have h10 : (10:ℝ) * t ≤ t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / Real.pi) := by
        have hb : (10:ℝ) ≤ 2 ^ (64:ℕ) / Real.pi := by
          rw [le_div_iff₀ hpi]; nlinarith [Real.pi_le_four]
        have hrp_nn : (0:ℝ) ≤ t ^ ((4:ℝ))⁻¹ := Real.rpow_nonneg ht_nn _
        calc (10:ℝ) * t ≤ 10 * t ^ ((4:ℝ))⁻¹ := mul_le_mul_of_nonneg_left ht_rpow (by norm_num)
          _ ≤ (2 ^ (64:ℕ) / Real.pi) * t ^ ((4:ℝ))⁻¹ := mul_le_mul_of_nonneg_right hb hrp_nn
          _ = t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / Real.pi) := by ring
      rw [div_le_iff₀ hsq]
      have hgoal : t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / (dist x y ^ 2 * Real.pi)) * dist x y ^ 2
          = t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / Real.pi) := by field_simp
      rw [hgoal]; exact h10
  · -- Field 4: left Hölder bound in `enorm` form.
    intro x x' y h
    simp only [Nat.cast_ofNat]
    -- First the norm-form left bound, symmetric to Field 3.
    have hnorm : ‖beurlingKernel x y - beurlingKernel x' y‖ ≤
        (dist x x' / dist x y) ^ ((4:ℝ))⁻¹ * (↑(C_K (4:ℝ)) / Real.vol x y) := by
      rcases eq_or_lt_of_le (dist_nonneg : (0:ℝ) ≤ dist x y) with hdz | hdpos
      · have he0 : dist x x' = 0 :=
          le_antisymm (by linarith [h, dist_nonneg (x := x) (y := x')]) dist_nonneg
        have hxy : x = y := by
          have := hdz.symm; rw [dist_eq] at this; rw [← sub_eq_zero]; exact norm_eq_zero.mp this
        have hxx' : x = x' := by
          rw [dist_eq] at he0; rw [← sub_eq_zero]; exact norm_eq_zero.mp he0
        rw [← hxx', hxy]; simp [beurlingKernel]
      · have hdxy : ‖x - y‖ = dist x y := (Complex.dist_eq x y).symm
        have hdxx' : ‖x' - x‖ = dist x x' := by rw [Complex.dist_eq, ← norm_neg, neg_sub]
        have hxy_ne : x - y ≠ 0 := by
          rw [sub_ne_zero]; intro he; rw [he] at hdpos; simp at hdpos
        have hnpos : (0:ℝ) < ‖x - y‖ := by rw [hdxy]; exact hdpos
        have hkey : 2 * ‖x' - x‖ ≤ ‖x - y‖ := by rw [hdxy, hdxx']; exact h
        have hxx'_nn : (0:ℝ) ≤ ‖x' - x‖ := norm_nonneg _
        have hsplit : x' - y = (x - y) + (x' - x) := by ring
        have hlow : ‖x - y‖ - ‖x' - x‖ ≤ ‖x' - y‖ := by
          have := norm_sub_norm_le (x - y) (-(x' - x))
          rw [norm_neg] at this
          calc ‖x - y‖ - ‖x' - x‖ ≤ ‖(x - y) - (-(x' - x))‖ := this
            _ = ‖x' - y‖ := by rw [sub_neg_eq_add, ← hsplit]
        have hx'y_low : ‖x - y‖ / 2 ≤ ‖x' - y‖ := by linarith
        have hx'y_pos : (0:ℝ) < ‖x' - y‖ := by linarith
        have hx'y_ne : x' - y ≠ 0 := norm_pos_iff.mp hx'y_pos
        have hsplit2 : x + x' - 2 * y = (x - y) + (x' - y) := by ring
        have hmid : ‖x + x' - 2 * y‖ ≤ (5/2) * ‖x - y‖ := by
          have h1 := norm_add_le (x - y) (x' - y); rw [← hsplit2] at h1
          have h2 := norm_add_le (x - y) (x' - x); rw [← hsplit] at h2; linarith
        have hmid_nn : (0:ℝ) ≤ ‖x + x' - 2 * y‖ := norm_nonneg _
        have hfact : beurlingKernel x y - beurlingKernel x' y
            = (x' - x) * (x + x' - 2 * y) / ((x - y) ^ 2 * (x' - y) ^ 2) := by
          rw [beurlingKernel, beurlingKernel, zpow_neg, zpow_neg, zpow_two, zpow_two]
          field_simp; ring
        have hnormdiff : ‖beurlingKernel x y - beurlingKernel x' y‖
            = ‖x' - x‖ * ‖x + x' - 2 * y‖ / (‖x - y‖ ^ 2 * ‖x' - y‖ ^ 2) := by
          rw [hfact, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
        have hbound1 : ‖beurlingKernel x y - beurlingKernel x' y‖
            ≤ 10 * (‖x' - x‖ / ‖x - y‖) / ‖x - y‖ ^ 2 := by
          rw [hnormdiff]
          have hnum : ‖x' - x‖ * ‖x + x' - 2 * y‖ ≤ ‖x' - x‖ * ((5/2) * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left hmid hxx'_nn
          have hden : ‖x - y‖ ^ 2 * (‖x - y‖ ^ 2 / 4) ≤ ‖x - y‖ ^ 2 * ‖x' - y‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hx'y_low, hx'y_pos, hnpos]
          have hden_pos1 : (0:ℝ) < ‖x - y‖ ^ 2 * (‖x - y‖ ^ 2 / 4) := by positivity
          calc ‖x' - x‖ * ‖x + x' - 2 * y‖ / (‖x - y‖ ^ 2 * ‖x' - y‖ ^ 2)
              ≤ ‖x' - x‖ * ((5/2) * ‖x - y‖) / (‖x - y‖ ^ 2 * (‖x - y‖ ^ 2 / 4)) :=
                div_le_div₀ (by positivity) hnum hden_pos1 hden
            _ = 10 * (‖x' - x‖ / ‖x - y‖) / ‖x - y‖ ^ 2 := by field_simp; ring
        refine hbound1.trans ?_
        set t := dist x x' / dist x y with ht_def
        have ht_nn : (0:ℝ) ≤ t := by rw [ht_def]; positivity
        have ht_le1 : t ≤ 1 := by
          rw [ht_def, div_le_one hdpos]; linarith [dist_nonneg (x := x) (y := x'), h]
        have hratio_eq : ‖x' - x‖ / ‖x - y‖ = t := by rw [ht_def, hdxy, hdxx']
        rw [hratio_eq, hvol x y, hCK, hdxy]
        have hpi : (0:ℝ) < Real.pi := Real.pi_pos
        have hsq : (0:ℝ) < dist x y ^ 2 := by positivity
        have ht_rpow : t ≤ t ^ ((4:ℝ))⁻¹ := by
          rcases eq_or_lt_of_le ht_nn with h0 | hpos
          · rw [← h0, Real.zero_rpow (by norm_num)]
          · calc t = t ^ (1:ℝ) := (Real.rpow_one t).symm
              _ ≤ t ^ ((4:ℝ))⁻¹ := Real.rpow_le_rpow_of_exponent_ge hpos ht_le1 (by norm_num)
        have h10 : (10:ℝ) * t ≤ t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / Real.pi) := by
          have hb : (10:ℝ) ≤ 2 ^ (64:ℕ) / Real.pi := by
            rw [le_div_iff₀ hpi]; nlinarith [Real.pi_le_four]
          have hrp_nn : (0:ℝ) ≤ t ^ ((4:ℝ))⁻¹ := Real.rpow_nonneg ht_nn _
          calc (10:ℝ) * t ≤ 10 * t ^ ((4:ℝ))⁻¹ := mul_le_mul_of_nonneg_left ht_rpow (by norm_num)
            _ ≤ (2 ^ (64:ℕ) / Real.pi) * t ^ ((4:ℝ))⁻¹ := mul_le_mul_of_nonneg_right hb hrp_nn
            _ = t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / Real.pi) := by ring
        rw [div_le_iff₀ hsq]
        have hgoal : t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / (dist x y ^ 2 * Real.pi)) * dist x y ^ 2
            = t ^ ((4:ℝ))⁻¹ * (2 ^ (64:ℕ) / Real.pi) := by field_simp
        rw [hgoal]; exact h10
    -- Convert the norm bound to the `enorm` bound (mirrors Carleson's `enorm_K_sub_le`).
    simp_rw [← ofReal_norm, ← ofReal_vol, ← ofReal_coe_nnreal, edist_dist]
    calc
      _ ≤ ENNReal.ofReal ((dist x x' / dist x y) ^ ((4:ℝ))⁻¹ * (↑(C_K (4:ℝ)) / Real.vol x y)) := by
          gcongr
      _ ≤ _ := by
          rw [ENNReal.ofReal_mul']; swap
          · exact div_nonneg NNReal.zero_le_coe measureReal_nonneg
          gcongr
          · rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
            gcongr
            apply ofReal_div_le (by positivity)
          · exact ofReal_div_le measureReal_nonneg


/-- **Truncated Beurling integrals converge to the Cauchy principal value** on the
smooth compactly supported class. For `μ ∈ C¹_c`, the truncated singular integrals
`czOperator beurlingKernel r μ z = ∫_{|y-z|≥r} (z-y)⁻² μ(y) dy` converge as `r → 0⁺`
to `∫ ζ, (∂μ ζ)/(ζ - z)`. This is the Tendsto exhibited (internally) by the proof of
`beurling_eq_dz_cauchyTransform`, extracted here for reuse. -/
lemma czOperator_beurling_tendsto_smooth (hμ : ContDiff ℝ 1 μ) (hμc : HasCompactSupport μ)
    (z : ℂ) :
    Filter.Tendsto (fun r : ℝ => czOperator beurlingKernel r μ z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ ζ, (dz μ ζ) / (ζ - z))) := by
  classical
  -- Basic data about `μ` and the unit-circle parametrization `e`.
  set e : ℝ → ℂ := fun t => (Real.cos t : ℂ) + (Real.sin t : ℂ) * I with he_def
  have hgdiff : ∀ ζ : ℂ, DifferentiableAt ℝ μ ζ := fun ζ => hμ.differentiable one_ne_zero ζ
  have he_cont : Continuous e := by rw [he_def]; fun_prop
  have he_mul_conj : ∀ θ : ℝ, e θ * (starRingEnd ℂ) (e θ) = 1 := by
    intro θ
    simp only [he_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    have h1 : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := by
      rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
    have h2 : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast h1
    linear_combination h2
  have he_ne : ∀ θ : ℝ, e θ ≠ 0 := by
    intro θ h; have := he_mul_conj θ; rw [h] at this; simp at this
  have he_inv : ∀ θ : ℝ, (e θ)⁻¹ = (starRingEnd ℂ) (e θ) := fun θ =>
    inv_eq_of_mul_eq_one_right (he_mul_conj θ)
  have he_norm : ∀ θ : ℝ, ‖e θ‖ = 1 := by
    intro θ
    have h := he_mul_conj θ
    have : ‖e θ * (starRingEnd ℂ) (e θ)‖ = ‖e θ‖ ^ 2 := by
      rw [norm_mul, Complex.norm_conj]; ring
    rw [h, norm_one] at this
    nlinarith [norm_nonneg (e θ), this]
  have he_deriv : ∀ θ : ℝ, HasDerivAt e (I * e θ) θ := by
    intro θ
    have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
      (Real.hasDerivAt_cos θ).ofReal_comp
    have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
      (Real.hasDerivAt_sin θ).ofReal_comp
    have hd : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ) + (Real.sin s : ℂ) * I)
        ((((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I) θ :=
      hcos.add (hsin.mul_const I)
    have hev : (((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I = I * e θ := by
      rw [he_def, Complex.ofReal_neg]
      linear_combination (-(Real.sin θ : ℂ)) * Complex.I_mul_I
    rw [he_def, ← hev]; exact hd
  have he_diff : ∀ t : ℝ, DifferentiableAt ℝ e t := by
    intro t; rw [he_def]
    apply DifferentiableAt.add
    · exact Complex.ofRealCLM.differentiableAt.comp t Real.differentiable_cos.differentiableAt
    · exact (Complex.ofRealCLM.differentiableAt.comp t
        Real.differentiable_sin.differentiableAt).mul_const _
  -- Continuity and compact support of `dz μ`.
  have hdzμ_cont : Continuous (fun ζ => dz μ ζ) := by unfold dz; fun_prop
  have hdzμ_cs : HasCompactSupport (fun ζ => dz μ ζ) := by
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ μ ζ) := hμc.fderiv (𝕜 := ℝ)
    have hcomp : (fun ζ => dz μ ζ)
        = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 - I * D I)) ∘ (fun ζ => fderiv ℝ μ ζ) := by
      funext ζ; rfl
    rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  -- Local integrability of the kernel `ζ ↦ (z - ζ)⁻¹`.
  have hloc0 : LocallyIntegrable (fun u : ℂ => u⁻¹) volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set lhs : ℝ × ℝ → ENNReal := fun p =>
      ENNReal.ofReal p.1 •
        (Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)
      with hlhs
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ p ∈ polarCoord.target, lhs p ≤ box p := by
      intro p hp
      simp only [hlhs, hbox]
      rw [polarCoord_target, Set.mem_prod] at hp
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hmem]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
            ENNReal.ofReal_lt_top.ne]
        have hpR : p.1 ≤ R := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩)]
      · rw [Set.indicator_of_notMem hmem]; simp
    calc
      ∫⁻ p in polarCoord.target, lhs p
          ≤ ∫⁻ p in polarCoord.target, box p :=
            setLIntegral_mono (measurable_const.indicator
              (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
      _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) := by
            rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]; simp
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hloc : LocallyIntegrable (fun ζ : ℂ => (z - ζ)⁻¹) volume := by
    set hh : ℂ ≃ₜ ℂ := (Homeomorph.neg ℂ).trans (Homeomorph.addLeft z) with hh_def
    have hmap : Measure.map hh (volume : Measure ℂ) = volume := by
      have hmp : MeasurePreserving (fun ζ : ℂ => z - ζ) volume volume := by
        have h1 : MeasurePreserving (fun ζ : ℂ => z + ζ) volume volume :=
          measurePreserving_add_left volume z
        have h2 : MeasurePreserving (fun ζ : ℂ => -ζ) volume volume :=
          Measure.measurePreserving_neg volume
        have := h1.comp h2
        simpa [Function.comp, sub_eq_add_neg] using this
      have hh_eq : (hh : ℂ → ℂ) = fun ζ : ℂ => z - ζ := by
        funext ζ; simp [hh_def, Homeomorph.trans, Homeomorph.neg, Homeomorph.addLeft,
          sub_eq_add_neg]
      rw [show (Measure.map hh (volume : Measure ℂ))
          = Measure.map (fun ζ : ℂ => z - ζ) volume by rw [hh_eq]]
      exact hmp.map_eq
    have hiff := locallyIntegrable_map_homeomorph hh (f := fun u : ℂ => u⁻¹) (μ := volume)
    rw [hmap] at hiff
    have hcomp : (fun u : ℂ => u⁻¹) ∘ hh = fun ζ : ℂ => (z - ζ)⁻¹ := by
      funext ζ; simp [hh_def, Homeomorph.trans, Homeomorph.neg, Homeomorph.addLeft,
        sub_eq_add_neg]
    rw [hcomp] at hiff
    exact hiff.mp hloc0
  -- Integrability of the kernel integrand `g`.
  have hg_int : Integrable (fun ζ => (dz μ ζ) * (z - ζ)⁻¹) volume := by
    have := hloc.integrable_smul_left_of_hasCompactSupport hdzμ_cont hdzμ_cs
    simpa [smul_eq_mul] using this
  -- A radius `R` enclosing the support of `μ`, off which `μ` and `dz μ` vanish.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport μ ⊆ Metric.closedBall z R :=
    (hμc.isCompact.isBounded).subset_closedBall z
  have hμ_van : ∀ ζ : ℂ, R < ‖ζ - z‖ → μ ζ = 0 := by
    intro ζ hζ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR hmem
    rw [Metric.mem_closedBall, dist_eq] at this
    linarith
  -- The kernel-integral limit (Step B.1).
  have hB1 : Tendsto (fun r : ℝ => ∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ ζ, (dz μ ζ) * (z - ζ)⁻¹)) := by
    have hballvol : Tendsto (fun r : ℝ => (volume ∘ (fun r => Metric.ball z r)) r)
        (𝓝[>] 0) (𝓝 0) := by
      simp only [Function.comp]
      have heqv : (fun r : ℝ => volume (Metric.ball z r))
          = fun r : ℝ => ENNReal.ofReal r ^ 2 * ↑NNReal.pi := by
        funext r; rw [Complex.volume_ball]
      rw [heqv, show (0 : ENNReal) = ENNReal.ofReal 0 ^ 2 * ↑NNReal.pi by simp]
      have htof : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝[>] 0) (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp nhdsWithin_le_nhds
      exact ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow htof) (Or.inr (by simp))
    have hzero : Tendsto (fun r : ℝ => ∫ y in Metric.ball z r, (dz μ y) * (z - y)⁻¹)
        (𝓝[>] 0) (𝓝 0) := hg_int.tendsto_setIntegral_nhds_zero hballvol
    have heq : ∀ r : ℝ, (∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹)
        = (∫ ζ, (dz μ ζ) * (z - ζ)⁻¹) - ∫ y in Metric.ball z r, (dz μ y) * (z - y)⁻¹ := by
      intro r; rw [setIntegral_compl measurableSet_ball hg_int]
    rw [funext heq]
    simpa using tendsto_const_nhds.sub hzero
  -- The angular integral of `conj(e θ)^2` over a full turn vanishes.
  have hconjint : (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (e θ))^2) = 0 := by
    have hper : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (I/2) * ((starRingEnd ℂ) (e t))^2)
        (((starRingEnd ℂ) (e s))^2) s := by
      intro s
      have hconj_d : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (e t))
          (-I * (starRingEnd ℂ) (e s)) s := by
        have hconj_eq : (fun t : ℝ => (starRingEnd ℂ) (e t))
            = fun t : ℝ => (Real.cos t : ℂ) - (Real.sin t : ℂ) * I := by
          funext t; rw [he_def]
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
        rw [hconj_eq]
        have hcos : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) ((-Real.sin s : ℝ) : ℂ) s :=
          (Real.hasDerivAt_cos s).ofReal_comp
        have hsin : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) ((Real.cos s : ℝ) : ℂ) s :=
          (Real.hasDerivAt_sin s).ofReal_comp
        have hd := hcos.sub (hsin.mul_const I)
        convert hd using 1
        rw [he_def]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
        linear_combination (Real.sin s : ℂ) * Complex.I_mul_I
      have h2 := (hconj_d.pow 2).const_mul (I/2)
      convert h2 using 1
      have hps : (2:ℕ) - 1 = 1 := rfl
      rw [hps, pow_one]
      have hI2 : (I:ℂ)^2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
      field_simp
      rw [hI2]; ring
    have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hper θ)]
    · have hπ : e π = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
      have hmπ : e (-π) = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
      rw [hπ, hmπ]; simp
    · apply Continuous.intervalIntegrable
      rw [he_def]; fun_prop
  -- The boundary-term limit (Step B.2 endpoint).
  have hB2 : Tendsto (fun r : ℝ => (1/2 : ℂ) * ∫ θ in Set.Ioo (-π) π,
        ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖μ ζ‖ ≤ M := hμc.exists_bound_of_continuous hμ.continuous
    set F : ℝ → ℝ → ℂ := fun r θ => ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ) with hF
    have hFcont : ∀ r : ℝ, Continuous (fun θ : ℝ => F r θ) := by
      intro r
      rw [hF]
      have h1 : Continuous (fun θ : ℝ => ((starRingEnd ℂ) (e θ))^2) :=
        ((Complex.continuous_conj.comp he_cont)).pow 2
      have h2 : Continuous (fun θ : ℝ => μ (z + (r : ℂ) * e θ)) :=
        hμ.continuous.comp (continuous_const.add (continuous_const.mul he_cont))
      exact h1.mul h2
    have hcontAt : ContinuousAt (fun r : ℝ => ∫ θ in Set.Ioo (-π) π, F r θ) 0 := by
      apply continuousAt_of_dominated (bound := fun _ => M)
      · filter_upwards with r
        exact (hFcont r).aestronglyMeasurable
      · filter_upwards with r
        filter_upwards with θ
        rw [hF, norm_mul]
        have hc : ‖((starRingEnd ℂ) (e θ))^2‖ = 1 := by
          rw [norm_pow, Complex.norm_conj, he_norm]; ring
        rw [hc, one_mul]; exact hM _
      · exact integrableOn_const measure_Ioo_lt_top.ne (by finiteness)
      · filter_upwards with θ
        apply Continuous.continuousAt
        rw [hF]
        exact continuous_const.mul (hμ.continuous.comp
          (continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)))
    have hAt0 : (∫ θ in Set.Ioo (-π) π, F 0 θ) = 0 := by
      have hsimp : (fun θ : ℝ => F 0 θ) = fun θ => ((starRingEnd ℂ) (e θ))^2 * μ z := by
        funext θ; rw [hF]; simp
      rw [hsimp]
      rw [show (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (e θ))^2 * μ z)
          = (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (e θ))^2) * μ z from
        integral_mul_const (μ z) (fun θ => ((starRingEnd ℂ) (e θ))^2)]
      rw [hconjint, zero_mul]
    have htend : Tendsto (fun r : ℝ => ∫ θ in Set.Ioo (-π) π, F r θ) (𝓝[>] 0)
        (𝓝 (∫ θ in Set.Ioo (-π) π, F 0 θ)) :=
      (hcontAt.tendsto).comp nhdsWithin_le_nhds
    rw [hAt0] at htend
    have hfin : Tendsto (fun r : ℝ => (1/2 : ℂ) * ∫ θ in Set.Ioo (-π) π, F r θ) (𝓝[>] 0)
        (𝓝 ((1/2 : ℂ) * 0)) := htend.const_mul _
    simpa using hfin
  -- Prerequisites for the polar identity.
  obtain ⟨Mμ, hMμ⟩ : ∃ M, ∀ ζ, ‖μ ζ‖ ≤ M := hμc.exists_bound_of_continuous hμ.continuous
  have hfderiv_cont : Continuous (fun ζ => fderiv ℝ μ ζ) := hμ.continuous_fderiv one_ne_zero
  have hfderiv_van : ∀ ζ : ℂ, R < ‖ζ - z‖ → fderiv ℝ μ ζ = 0 := by
    intro ζ hζ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := (tsupport_fderiv_subset ℝ (f := μ)) hmem
    have h2 := hR h1
    rw [Metric.mem_closedBall, dist_eq] at h2
    linarith
  obtain ⟨Mf, hMf⟩ : ∃ M, ∀ ζ : ℂ, ‖fderiv ℝ μ ζ‖ ≤ M :=
    (hμc.fderiv ℝ).exists_bound_of_continuous hfderiv_cont
  -- The polar change-of-variables on the exterior of a disc.
  have hpolar : ∀ (r' : ℝ), 0 < r' → ∀ (φ : ℂ → ℂ),
      (∫ ζ in (Metric.ball z r')ᶜ, φ ζ)
        = ∫ p in (Set.Ioi r' ×ˢ Set.Ioo (-π) π), p.1 • φ (z + Complex.polarCoord.symm p) := by
    intro r' hr' φ
    have hshift : (∫ ζ in (Metric.ball z r')ᶜ, φ ζ)
        = ∫ ξ in (Metric.ball (0:ℂ) r')ᶜ, φ (z + ξ) := by
      have hmp : MeasurePreserving (fun ξ : ℂ => z + ξ) volume volume :=
        measurePreserving_add_left volume z
      have hemb : MeasurableEmbedding (fun ξ : ℂ => z + ξ) :=
        (Homeomorph.addLeft z).measurableEmbedding
      have hpre : (fun ξ : ℂ => z + ξ) ⁻¹' (Metric.ball z r')ᶜ = (Metric.ball (0:ℂ) r')ᶜ := by
        ext ξ; simp [Metric.mem_ball]
      have := hmp.setIntegral_preimage_emb hemb φ (Metric.ball z r')ᶜ
      rw [hpre] at this; rw [← this]
    rw [hshift]
    set ψ : ℂ → ℂ := fun ξ => φ (z + ξ) with hψ
    rw [← integral_indicator measurableSet_ball.compl,
      ← Complex.integral_comp_polarCoord_symm ((Metric.ball (0:ℂ) r')ᶜ.indicator ψ),
      polarCoord_target]
    have hae : ∀ᵐ p : ℝ × ℝ ∂volume,
        p ∈ (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π) \ (Set.Ioi r' ×ˢ Set.Ioo (-π) π) →
          p.1 • (Metric.ball (0:ℂ) r')ᶜ.indicator ψ (Complex.polarCoord.symm p) = 0 := by
      have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = r'} = 0 := by
        have heq : {p : ℝ × ℝ | p.1 = r'} = Prod.fst ⁻¹' {r'} := rfl
        rw [heq, Measure.volume_eq_prod, ← Set.prod_univ, Measure.prod_prod]; simp
      have haene : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ r' := by rw [ae_iff]; simpa using hnull
      filter_upwards [haene] with p hpne hpdiff
      obtain ⟨hpt, hps⟩ := hpdiff
      obtain ⟨hp1, hp2⟩ := hpt
      simp only [Set.mem_Ioi] at hp1
      simp only [Set.mem_prod, Set.mem_Ioi, not_and] at hps
      have hpr : p.1 ≤ r' := not_lt.mp (fun h => hps h hp2)
      have hplt : p.1 < r' := lt_of_le_of_ne hpr hpne
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
      have hnotmem : Complex.polarCoord.symm p ∉ (Metric.ball (0:ℂ) r')ᶜ := by
        simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, hnorm, not_not]
        exact hplt
      change p.1 • (Metric.ball (0:ℂ) r')ᶜ.indicator ψ (Complex.polarCoord.symm p) = 0
      rw [Set.indicator_of_notMem hnotmem]; simp
    refine (setIntegral_eq_of_subset_of_ae_diff_eq_zero
        (measurableSet_Ioi.prod measurableSet_Ioo).nullMeasurableSet
        (Set.prod_mono (Set.Ioi_subset_Ioi (le_of_lt hr')) (le_refl _)) hae).trans ?_
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    obtain ⟨hpr, hp2⟩ := hp
    simp only [Set.mem_Ioi] at hpr
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos (lt_trans hr' hpr)]
    have hmem : Complex.polarCoord.symm p ∈ (Metric.ball (0:ℂ) r')ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, hnorm, not_lt]
      exact le_of_lt hpr
    change p.1 • (Metric.ball (0:ℂ) r')ᶜ.indicator ψ (Complex.polarCoord.symm p)
      = p.1 • φ (z + Complex.polarCoord.symm p)
    rw [Set.indicator_of_mem hmem]
  -- Integrability of the singular kernel integrand on the exterior of a disc.
  have hext_int : ∀ r' : ℝ, 0 < r' →
      IntegrableOn (fun y => (z - y) ^ (-2 : ℤ) * μ y) (Metric.ball z r')ᶜ volume := by
    intro r' hr'
    set f : ℂ → ℂ := fun y => (z - y) ^ (-2 : ℤ) * μ y with hf
    set t : Set ℂ := (Metric.ball z r')ᶜ ∩ Metric.closedBall z R with ht
    have htmeas : MeasurableSet t := measurableSet_ball.compl.inter measurableSet_closedBall
    have htfin : volume t ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_closedBall_lt_top)
    have hfmeas : AEStronglyMeasurable f volume := by
      apply Measurable.aestronglyMeasurable
      apply Measurable.mul _ hμ.continuous.measurable
      fun_prop
    have hbound : ∀ᵐ y ∂volume.restrict t, ‖f y‖ ≤ Mμ * r'⁻¹^2 := by
      rw [ae_restrict_iff' htmeas]
      filter_upwards with y hy
      obtain ⟨hy1, _⟩ := hy
      simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_eq] at hy1
      rw [hf, norm_mul, norm_zpow]
      have hzy : r' ≤ ‖z - y‖ := by rw [← norm_neg, neg_sub]; exact hy1
      have hpos : (0:ℝ) < ‖z - y‖ := lt_of_lt_of_le hr' hzy
      have hk : ‖z - y‖ ^ (-2 : ℤ) ≤ r'⁻¹^2 := by
        rw [zpow_neg, zpow_two, show r'⁻¹^2 = (r'*r')⁻¹ by rw [mul_inv]; ring]
        apply inv_anti₀ (by positivity)
        exact mul_le_mul hzy hzy (le_of_lt hr') (le_of_lt hpos)
      calc ‖z - y‖ ^ (-2:ℤ) * ‖μ y‖ ≤ r'⁻¹^2 * Mμ :=
              mul_le_mul hk (hMμ y) (norm_nonneg _) (by positivity)
        _ = Mμ * r'⁻¹^2 := by ring
    have hint_t : IntegrableOn f t volume :=
      Measure.integrableOn_of_bounded htfin hfmeas hbound
    refine hint_t.of_forall_diff_eq_zero measurableSet_ball.compl ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [ht, Set.mem_inter_iff, not_and] at hy2
    have hyR := hy2 hy1
    simp only [Metric.mem_closedBall, not_le, dist_eq] at hyR
    change (z - y) ^ (-2 : ℤ) * μ y = 0
    rw [hμ_van y hyR, mul_zero]
  -- The per-`r` polar identity (Step B.2 core / the integration-by-parts).
  have hPolar : ∀ r : ℝ, 0 < r →
      (∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y)
        = (1/2 : ℂ) * (∫ θ in Set.Ioo (-π) π, ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ))
          - ∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹ := by
    intro r hr
    rw [eq_sub_iff_add_eq, ← integral_add (hext_int r hr) (hg_int.integrableOn)]
    have hIBP : ∀ y ∈ (Metric.ball z r)ᶜ,
        (z - y) ^ (-2 : ℤ) * μ y + (dz μ y) * (z - y)⁻¹ = dz (fun w => μ w * (z - w)⁻¹) y := by
      intro y hy
      have hyz : y ≠ z := by
        intro h; rw [h] at hy
        simp only [Set.mem_compl_iff, Metric.mem_ball, dist_self] at hy
        exact hy hr
      have hsub : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
      have hμd : DifferentiableAt ℝ μ y := hgdiff y
      have hkerℂ : DifferentiableAt ℂ (fun w => (z - w)⁻¹) y :=
        DifferentiableAt.inv ((differentiableAt_const z).sub differentiableAt_id) hsub
      have hkerℝ : DifferentiableAt ℝ (fun w => (z - w)⁻¹) y :=
        (differentiableAt_complex_iff_differentiableAt_real.mp hkerℂ).1
      rw [dz_mul hμd hkerℝ]
      have hdzker : dz (fun w => (z - w)⁻¹) y = (z - y) ^ (-2 : ℤ) := by
        rw [dz_eq_deriv_of_differentiableAt hkerℂ]
        have hderiv : HasDerivAt (fun w => (z - w)⁻¹) ((z - y) ^ (-2 : ℤ)) y := by
          have h1 : HasDerivAt (fun w : ℂ => z - w) (-1) y := by
            simpa using (hasDerivAt_id y).const_sub z
          have h2 := (h1.inv hsub)
          convert h2 using 1
          rw [zpow_neg, zpow_two]; field_simp
        exact hderiv.deriv
      rw [hdzker]; ring
    rw [setIntegral_congr_fun measurableSet_ball.compl hIBP,
      hpolar r hr (fun w => dz (fun w => μ w * (z - w)⁻¹) w)]
    set RIfn : ℝ × ℝ → ℂ := fun p => (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
        * (deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1) with hRIfn
    set AIfn : ℝ × ℝ → ℂ := fun p => (I/2 : ℂ)
        * (deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2
            * μ (z + (p.1:ℂ) * e t)) p.2)
        with hAIfn
    have hsplit : ∀ p ∈ Set.Ioi r ×ˢ Set.Ioo (-π : ℝ) π,
        p.1 • (dz (fun w => μ w * (z - w)⁻¹) (z + Complex.polarCoord.symm p))
          = RIfn p - AIfn p := by
      intro p hp
      obtain ⟨hpr, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hpr
      have hp1 : 0 < p.1 := lt_trans hr hpr
      have hPp : Complex.polarCoord.symm p = (p.1 : ℂ) * e p.2 := by
        rw [Complex.polarCoord_symm_apply, he_def]
      set Rrad : ℂ :=
        deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1 with hRrad_def
      set Aang : ℂ :=
        deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t)) p.2
        with hAang_def
      have hRrad : HasDerivAt
          (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) Rrad p.1 := by
        apply DifferentiableAt.hasDerivAt
        apply DifferentiableAt.const_mul
        apply (hgdiff _).comp
        exact (differentiableAt_const _).add (Complex.ofRealCLM.differentiableAt.mul_const _)
      have hAang : HasDerivAt
          (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t))
          Aang p.2 := by
        apply DifferentiableAt.hasDerivAt
        apply DifferentiableAt.mul
        · apply (differentiableAt_const _).mul
          apply DifferentiableAt.pow
          exact (Complex.conjCLE.differentiableAt).comp p.2 (he_diff p.2)
        · apply (hgdiff _).comp
          exact (differentiableAt_const _).add ((differentiableAt_const _).mul (he_diff p.2))
      rw [hPp]
      change p.1 • (dz (fun w => μ w * (z - w)⁻¹) (z + (p.1 : ℂ) * e p.2))
          = (1/2 : ℂ) * (starRingEnd ℂ) (e p.2) * Rrad - (I/2) * Aang
      set ρ := p.1
      set θ := p.2
      set D := fderiv ℝ μ (z + (ρ:ℂ) * e θ) with hD
      -- dz F value via IBP identity
      have hyz : z + (ρ:ℂ) * e θ ≠ z := by
        intro h
        exact (mul_ne_zero (by exact_mod_cast ne_of_gt hp1) (he_ne θ)) (add_eq_left.mp h)
      have hsub : z - (z + (ρ:ℂ)*e θ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
      have hμd : DifferentiableAt ℝ μ (z + (ρ:ℂ)*e θ) := hgdiff _
      have hkerℂ : DifferentiableAt ℂ (fun w => (z - w)⁻¹) (z + (ρ:ℂ)*e θ) :=
        DifferentiableAt.inv ((differentiableAt_const z).sub differentiableAt_id) hsub
      have hkerℝ : DifferentiableAt ℝ (fun w => (z - w)⁻¹) (z + (ρ:ℂ)*e θ) :=
        (differentiableAt_complex_iff_differentiableAt_real.mp hkerℂ).1
      have hdzF : dz (fun w => μ w * (z - w)⁻¹) (z + (ρ:ℂ)*e θ)
          = μ (z + (ρ:ℂ)*e θ) * (z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ)
            + (dz μ (z + (ρ:ℂ)*e θ)) * (z - (z + (ρ:ℂ)*e θ))⁻¹ := by
        rw [dz_mul hμd hkerℝ]
        have hdzker : dz (fun w => (z - w)⁻¹) (z + (ρ:ℂ)*e θ)
            = (z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ) := by
          rw [dz_eq_deriv_of_differentiableAt hkerℂ]
          have hderiv : HasDerivAt (fun w => (z - w)⁻¹)
              ((z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ)) (z + (ρ:ℂ)*e θ) := by
            have h1 : HasDerivAt (fun w : ℂ => z - w) (-1) (z + (ρ:ℂ)*e θ) := by
              simpa using (hasDerivAt_id _).const_sub z
            have h2 := (h1.inv hsub)
            convert h2 using 1
            rw [zpow_neg, zpow_two]; field_simp
          exact hderiv.deriv
        rw [hdzker]; ring
      rw [hdzF]
      -- bridge dz μ
      have hdzμ_eq : dz μ (z + (ρ:ℂ)*e θ)
          = (1/2 : ℂ) * (starRingEnd ℂ) (e θ) * (D (e θ) - I * D (I * e θ)) := by
        rw [dz, ← hD]
        have hDe : D (e θ) = (Real.cos θ : ℂ) * D 1 + (Real.sin θ : ℂ) * D I := by
          have hee : e θ = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • I := by
            rw [he_def]; simp [Complex.real_smul]
          rw [hee, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
        have hDIe : D (I * e θ) = -(Real.sin θ : ℂ) * D 1 + (Real.cos θ : ℂ) * D I := by
          have hIe : I * e θ = (-(Real.sin θ) : ℝ) • (1 : ℂ) + (Real.cos θ : ℝ) • I := by
            rw [he_def, Complex.real_smul, Complex.real_smul, Complex.ofReal_neg]
            linear_combination ((Real.sin θ : ℂ)) * Complex.I_mul_I
          rw [hIe, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul,
            Complex.ofReal_neg]
        have hconj : (starRingEnd ℂ) (e θ) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
          rw [he_def]; simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
        rw [hDe, hDIe, hconj]
        have hI2 : (I:ℂ)^2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
        have hcs : (Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2 = 1 := by
          have : (Real.cos θ)^2 + (Real.sin θ)^2 = 1 := Real.cos_sq_add_sin_sq θ
          exact_mod_cast this
        ring_nf
        rw [hI2]
        linear_combination (-(1/2 : ℂ) * (D 1 - I * D I)) * hcs
      -- radial deriv value
      have hRrad_eq : Rrad = -(starRingEnd ℂ) (e θ) * D (e θ) := by
        have hd : HasDerivAt (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ))
            (-((starRingEnd ℂ) (e θ)) * D (e θ)) p.1 := by
          have hinner : HasDerivAt (fun s : ℝ => z + (s : ℂ) * e θ) (e θ) p.1 := by
            have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * e θ) (e θ) p.1 := by
              have := (Complex.ofRealCLM.hasDerivAt (x := p.1)).mul_const (e θ); simpa using this
            exact h1.const_add z
          have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt p.1 hinner
          exact hcomp.const_mul (-(starRingEnd ℂ) (e θ))
        exact hRrad.unique hd
      -- angular deriv value
      have hAang_eq : Aang
          = -((ρ:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e θ))^2) * μ (z + (ρ:ℂ) * e θ)
            + ((starRingEnd ℂ) (e θ))^2 * ((ρ:ℂ) * D (I * e θ))) := by
        have hd : HasDerivAt
            (fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))
            (-((ρ:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e θ))^2) * μ (z + (ρ:ℂ) * e θ)
              + ((starRingEnd ℂ) (e θ))^2 * ((ρ:ℂ) * D (I * e θ)))) θ := by
          have hconj_d : HasDerivAt (fun s : ℝ => (starRingEnd ℂ) (e s))
              (-I * (starRingEnd ℂ) (e θ)) θ := by
            have hconj_eq : (fun s : ℝ => (starRingEnd ℂ) (e s))
                = fun s : ℝ => (Real.cos s : ℂ) - (Real.sin s : ℂ) * I := by
              funext s; rw [he_def]
              simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
            rw [hconj_eq]
            have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_cos θ).ofReal_comp
            have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_sin θ).ofReal_comp
            have hdd := hcos.sub (hsin.mul_const I)
            convert hdd using 1
            rw [he_def]
            simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
            linear_combination (Real.sin θ : ℂ) * Complex.I_mul_I
          have hconj2_d : HasDerivAt (fun s : ℝ => ((starRingEnd ℂ) (e s))^2)
              (-2 * I * ((starRingEnd ℂ) (e θ))^2) θ := by
            have h := hconj_d.pow 2
            convert h using 1
            have hps : (2:ℕ) - 1 = 1 := rfl
            rw [hps, pow_one]; push_cast; ring
          have hμ_d : HasDerivAt (fun t : ℝ => μ (z + (ρ:ℂ) * e t))
              ((ρ:ℂ) * D (I * e θ)) θ := by
            have hinner : HasDerivAt (fun t : ℝ => z + (ρ:ℂ) * e t) ((ρ:ℂ) * (I * e θ)) θ :=
              ((he_deriv θ).const_mul (ρ:ℂ)).const_add z
            have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt θ hinner
            have hsm : (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) ((ρ:ℂ) * (I * e θ))
                = (ρ:ℂ) * D (I * e θ) := by
              rw [show ((ρ:ℂ) * (I * e θ)) = (ρ:ℝ) • (I * e θ) by rw [Complex.real_smul], map_smul,
                Complex.real_smul, ← hD]
            rwa [hsm] at hcomp
          have hprod := hconj2_d.mul hμ_d
          have hfull := hprod.const_mul (-((ρ:ℂ)⁻¹))
          have hfun : (fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))
              = (fun t : ℝ => -((ρ:ℂ)⁻¹) * (((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))) := by
            funext t; ring
          rw [hfun]; exact hfull
        exact hAang.unique hd
      rw [hRrad_eq, hAang_eq, hdzμ_eq]
      -- now the algebraic split (ptsplit3 core)
      have hρne : (ρ:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp1
      have hinv1 : (z - (z + (ρ:ℂ)*e θ))⁻¹ = -((ρ:ℂ)⁻¹) * (starRingEnd ℂ) (e θ) := by
        have hzz : z - (z + (ρ:ℂ)*e θ) = -((ρ:ℂ)*e θ) := by ring
        rw [hzz, mul_comm (ρ:ℂ) (e θ), show -(e θ * (ρ:ℂ)) = (e θ) * (-(ρ:ℂ)) by ring,
          mul_inv, he_inv]; field_simp
      have hinv2 : (z - (z + (ρ:ℂ)*e θ)) ^ (-2 : ℤ) = ((ρ:ℂ)⁻¹)^2 * (starRingEnd ℂ) (e θ)^2 := by
        have hzz : z - (z + (ρ:ℂ)*e θ) = -((ρ:ℂ)*e θ) := by ring
        rw [hzz, zpow_neg, zpow_two, neg_mul_neg, mul_inv, mul_inv, he_inv]; ring
      rw [hinv1, hinv2, Complex.real_smul]
      have hI2 : (I:ℂ)^2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
      field_simp
      linear_combination ((starRingEnd ℂ) (e θ)^2 * μ (z + (ρ:ℂ)*e θ) * 2) * hI2
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hsplit]
    -- Integrability of RIfn on the product domain.
    have hRval : ∀ p : ℝ × ℝ,
        deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1
          = -((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2) := by
      intro p
      apply HasDerivAt.deriv
      have hinner : HasDerivAt (fun s : ℝ => z + (s : ℂ) * e p.2) (e p.2) p.1 := by
        have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * e p.2) (e p.2) p.1 := by
          have := (Complex.ofRealCLM.hasDerivAt (x := p.1)).mul_const (e p.2); simpa using this
        exact h1.const_add z
      have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt p.1 hinner
      exact hcomp.const_mul (-(starRingEnd ℂ) (e p.2))
    set RI : ℝ × ℝ → ℂ := fun p => (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
        * (-((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)) with hRI
    have hRIfn_eq : ∀ p, RIfn p = RI p := by
      intro p
      change (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
          * (deriv (fun s : ℝ => -((starRingEnd ℂ) (e p.2)) * μ (z + (s : ℂ) * e p.2)) p.1)
        = (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
          * (-((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2))
      rw [hRval]
    have hP_cont : Continuous (fun p : ℝ × ℝ => z + (p.1:ℂ) * e p.2) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (he_cont.comp continuous_snd))
    have hconj_c : Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) (e p.2)) :=
      Complex.continuous_conj.comp (he_cont.comp continuous_snd)
    have hRI_cont : Continuous RI := by
      rw [hRI]
      exact (continuous_const.mul hconj_c).mul (hconj_c.neg.mul
        ((hfderiv_cont.comp hP_cont).clm_apply (he_cont.comp continuous_snd)))
    have hRI_bound : ∀ p, ‖RI p‖ ≤ (1/2) * Mf := by
      intro p
      rw [hRI]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      rw [norm_mul, norm_mul, norm_mul, h1, Complex.norm_conj, he_norm, norm_neg, Complex.norm_conj,
        he_norm]
      have h2 : ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)‖ ≤ Mf := by
        calc ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)‖
            ≤ ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ * ‖e p.2‖ := ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ := by rw [he_norm, mul_one]
          _ ≤ Mf := hMf _
      nlinarith [norm_nonneg ((fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2))]
    have hRI_supp : ∀ p : ℝ × ℝ, R < p.1 → RI p = 0 := by
      intro p hp
      have hv : fderiv ℝ μ (z + (p.1:ℂ) * e p.2) = 0 := by
        apply hfderiv_van
        rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact lt_of_lt_of_le hp (le_abs_self _)
      change (1/2 : ℂ) * (starRingEnd ℂ) (e p.2)
          * (-((starRingEnd ℂ) (e p.2)) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (e p.2)) = 0
      rw [hv]; simp
    have hRI_base : IntegrableOn RI (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume := by
      set S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (R + 1) ×ˢ Set.Ioo (-π) π with hS
      have hSfin : volume S ≠ ⊤ := by
        rw [hS, Measure.volume_eq_prod, Measure.prod_prod]
        exact (ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioo_lt_top).ne
      have hintS : IntegrableOn RI S volume :=
        Measure.integrableOn_of_bounded hSfin hRI_cont.aestronglyMeasurable
          (ae_of_all _ (fun p => hRI_bound p))
      apply hintS.of_forall_diff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      obtain ⟨hpT, hpnS⟩ := hp
      obtain ⟨hr', hθ⟩ := hpT
      simp only [Set.mem_Ioi] at hr'
      apply hRI_supp
      by_contra hle
      rw [not_lt] at hle
      apply hpnS
      exact ⟨Set.mem_Ioo.mpr ⟨lt_trans hr hr', by linarith⟩, hθ⟩
    have hRI_int : IntegrableOn RIfn (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume :=
      hRI_base.congr_fun (fun p _ => (hRIfn_eq p).symm) (measurableSet_Ioi.prod measurableSet_Ioo)
    -- The value of the radial integral S1.
    have hS1 : (∫ p in (Set.Ioi r ×ˢ Set.Ioo (-π) π), RIfn p)
        = (1/2 : ℂ)
          * (∫ θ in Set.Ioo (-π) π, ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ)) := by
      rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p _ => hRIfn_eq p)]
      have hRI_int' : IntegrableOn RI (Set.Ioi r ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod ℝ ℝ]; exact hRI_base
      have hswapint : IntegrableOn (fun q : ℝ × ℝ => RI q.swap)
          (Set.Ioo (-π) π ×ˢ Set.Ioi r) (volume.prod volume) := by
        have h1 : Integrable RI
            ((volume.restrict (Set.Ioi r)).prod (volume.restrict (Set.Ioo (-π) π))) := by
          rw [Measure.prod_restrict]; exact hRI_int'
        have h2 := h1.swap
        rw [IntegrableOn, ← Measure.prod_restrict]
        exact h2
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      rw [← setIntegral_prod_swap (Set.Ioi r) (Set.Ioo (-π) π) RI, setIntegral_prod _ hswapint]
      -- Inner radial integral evaluation.
      have hinner : ∀ θ : ℝ, θ ∈ Set.Ioo (-π : ℝ) π →
          (∫ ρ in Set.Ioi r, RI (ρ, θ))
            = (1/2 : ℂ) * (((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ)) := by
        intro θ _
        have hconst : ∀ ρ : ℝ, RI (ρ, θ) = ((1/2 : ℂ) * (starRingEnd ℂ) (e θ))
            • (deriv (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) ρ) := by
          intro ρ
          have hv := hRval (ρ, θ)
          simp only at hv
          change (1/2 : ℂ) * (starRingEnd ℂ) (e θ)
              * (-((starRingEnd ℂ) (e θ)) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (e θ))
            = ((1/2 : ℂ) * (starRingEnd ℂ) (e θ))
              • (deriv (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) ρ)
          rw [hv, smul_eq_mul]
        rw [setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => hconst ρ), integral_smul]
        -- radial FTC
        have hFCD : ContDiff ℝ 1
            (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) := by
          have h1 : ContDiff ℝ 1 (fun s : ℝ => z + (s : ℂ) * e θ) :=
            contDiff_const.add ((Complex.ofRealCLM.contDiff).mul contDiff_const)
          exact contDiff_const.mul (hμ.comp h1)
        have hFCS : HasCompactSupport
            (fun s : ℝ => -((starRingEnd ℂ) (e θ)) * μ (z + (s : ℂ) * e θ)) := by
          apply HasCompactSupport.intro (K := Set.Icc (-(|R| + 1)) (|R| + 1)) isCompact_Icc
          intro s hs
          rw [Set.mem_Icc, not_and_or] at hs
          have hvan : μ (z + (s:ℂ) * e θ) = 0 := by
            apply hμ_van
            rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real,
              Real.norm_eq_abs]
            rcases hs with h | h
            · rw [abs_of_neg (by nlinarith [abs_nonneg R] : s < 0)]
              nlinarith [abs_nonneg R, le_abs_self R]
            · rw [abs_of_pos (by nlinarith [abs_nonneg R] : (0:ℝ) < s)]
              nlinarith [abs_nonneg R, le_abs_self R]
          change -((starRingEnd ℂ) (e θ)) * μ (z + (s:ℂ) * e θ) = 0
          rw [hvan, mul_zero]
        rw [HasCompactSupport.integral_Ioi_deriv_eq hFCD hFCS r, smul_eq_mul]
        change (1/2 : ℂ) * (starRingEnd ℂ) (e θ)
            * (-(-((starRingEnd ℂ) (e θ)) * μ (z + (r : ℂ) * e θ)))
            = (1/2 : ℂ) * (((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ))
        ring
      have hswap_eq : ∀ x : ℝ, (∫ y in Set.Ioi r, RI (x, y).swap)
          = ∫ ρ in Set.Ioi r, RI (ρ, x) := by
        intro x; rfl
      rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => (hswap_eq x).trans (hinner x hx))]
      rw [show (∫ x in Set.Ioo (-π : ℝ) π,
            (1/2 : ℂ) * (((starRingEnd ℂ) (e x))^2 * μ (z + (r : ℂ) * e x)))
          = (1/2 : ℂ) * ∫ x in Set.Ioo (-π : ℝ) π,
            ((starRingEnd ℂ) (e x))^2 * μ (z + (r : ℂ) * e x) from
        integral_const_mul (1/2 : ℂ) (fun x => ((starRingEnd ℂ) (e x))^2 * μ (z + (r : ℂ) * e x))]
    -- The angular deriv value (uniqueness).
    have hAval : ∀ p : ℝ × ℝ, 0 < p.1 →
        deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t)) p.2
          = -((p.1:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)
              + ((starRingEnd ℂ) (e p.2))^2
                * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2))) := by
      intro p hp1
      apply HasDerivAt.deriv
      have hconj_d : HasDerivAt (fun s : ℝ => (starRingEnd ℂ) (e s))
          (-I * (starRingEnd ℂ) (e p.2)) p.2 := by
        have hconj_eq : (fun s : ℝ => (starRingEnd ℂ) (e s))
            = fun s : ℝ => (Real.cos s : ℂ) - (Real.sin s : ℂ) * I := by
          funext s; rw [he_def]
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
        rw [hconj_eq]
        have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin p.2 : ℝ) : ℂ) p.2 :=
          (Real.hasDerivAt_cos p.2).ofReal_comp
        have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos p.2 : ℝ) : ℂ) p.2 :=
          (Real.hasDerivAt_sin p.2).ofReal_comp
        have hdd := hcos.sub (hsin.mul_const I)
        convert hdd using 1
        rw [he_def]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
        linear_combination (Real.sin p.2 : ℂ) * Complex.I_mul_I
      have hconj2_d : HasDerivAt (fun s : ℝ => ((starRingEnd ℂ) (e s))^2)
          (-2 * I * ((starRingEnd ℂ) (e p.2))^2) p.2 := by
        have h := hconj_d.pow 2
        convert h using 1
        have hps : (2:ℕ) - 1 = 1 := rfl
        rw [hps, pow_one]; push_cast; ring
      have hμ_d : HasDerivAt (fun t : ℝ => μ (z + (p.1:ℂ) * e t))
          ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)) p.2 := by
        have hinner : HasDerivAt (fun t : ℝ => z + (p.1:ℂ) * e t) ((p.1:ℂ) * (I * e p.2)) p.2 :=
          ((he_deriv p.2).const_mul (p.1:ℂ)).const_add z
        have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt p.2 hinner
        have hsm : (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) ((p.1:ℂ) * (I * e p.2))
            = (p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2) := by
          rw [show ((p.1:ℂ) * (I * e p.2)) = (p.1:ℝ) • (I * e p.2) by rw [Complex.real_smul],
            map_smul,
            Complex.real_smul]
        rwa [hsm] at hcomp
      have hprod := hconj2_d.mul hμ_d
      have hfull := hprod.const_mul (-((p.1:ℂ)⁻¹))
      have hfun : (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t))
          = (fun t : ℝ => -((p.1:ℂ)⁻¹) * (((starRingEnd ℂ) (e t))^2 * μ (z + (p.1:ℂ) * e t))) := by
        funext t; ring
      rw [hfun]; exact hfull
    -- The angular integrand (continuous, bounded, supported in {ρ ≤ R}).
    set AI : ℝ × ℝ → ℂ := fun p => (I/2 : ℂ)
        * (-((p.1:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)
            + ((starRingEnd ℂ) (e p.2))^2
              * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)))) with hAI
    have hAI_contOn : ContinuousOn AI (Set.Ioi r ×ˢ Set.Ioo (-π) π) := by
      rw [hAI]
      have hP : Continuous (fun p : ℝ × ℝ => z + (p.1:ℂ) * e p.2) :=
        continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
          (he_cont.comp continuous_snd))
      have hconj : Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) (e p.2)) :=
        Complex.continuous_conj.comp (he_cont.comp continuous_snd)
      have hp1inv : ContinuousOn (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) (Set.Ioi r ×ˢ Set.Ioo (-π) π) := by
        apply ContinuousOn.inv₀ (Complex.continuous_ofReal.comp continuous_fst).continuousOn
        intro p hp
        obtain ⟨hp1, _⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [Function.comp_apply, ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt (lt_trans hr hp1)
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.mul (hp1inv.neg)
      apply ContinuousOn.add
      · apply ContinuousOn.mul (continuousOn_const.mul (hconj.pow 2).continuousOn)
        exact (hμ.continuous.comp hP).continuousOn
      · apply ContinuousOn.mul (hconj.pow 2).continuousOn
        apply ContinuousOn.mul (Complex.continuous_ofReal.comp continuous_fst).continuousOn
        exact ((hfderiv_cont.comp hP).clm_apply
          (continuous_const.mul (he_cont.comp continuous_snd))).continuousOn
    have hAI_int : IntegrableOn AI (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume := by
      set S : Set (ℝ × ℝ) := Set.Ioo r (R + 1) ×ˢ Set.Ioo (-π) π with hS
      have hSmeas : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
      have hSfin : volume S ≠ ⊤ := by
        rw [hS, Measure.volume_eq_prod, Measure.prod_prod]
        exact (ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioo_lt_top).ne
      have hSsub : S ⊆ Set.Ioi r ×ˢ Set.Ioo (-π) π :=
        Set.prod_mono Set.Ioo_subset_Ioi_self (le_refl _)
      have haem : AEStronglyMeasurable AI (volume.restrict S) :=
        (hAI_contOn.mono hSsub).aestronglyMeasurable hSmeas
      have hbnd : ∀ᵐ p ∂volume.restrict S,
          ‖AI p‖ ≤ (1/2) * (r⁻¹ * (2 * Mμ + (R + 1) * Mf)) := by
        rw [ae_restrict_iff' hSmeas]
        filter_upwards with p hp
        obtain ⟨hp1, _⟩ := hp
        simp only [Set.mem_Ioo] at hp1
        obtain ⟨hpr, hpR⟩ := hp1
        have hp1pos : 0 < p.1 := lt_trans hr hpr
        rw [hAI]
        have hnorm12 : ‖(I/2 : ℂ)‖ = 1/2 := by
          rw [show (I/2 : ℂ) = (1/2 : ℂ) * I by ring, norm_mul, Complex.norm_I, mul_one]; norm_num
        rw [norm_mul, hnorm12, norm_mul, norm_neg, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hp1pos]
        have hT1 : ‖(-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)‖ ≤ 2 * Mμ := by
          have hcc : ‖((starRingEnd ℂ) (e p.2))^2‖ = 1 := by
            rw [norm_pow, Complex.norm_conj, he_norm]; ring
          have hco : ‖(-2 * I * ((starRingEnd ℂ) (e p.2))^2)‖ = 2 := by
            rw [norm_mul, norm_mul, hcc, mul_one, Complex.norm_I, mul_one,
              show ‖(-2 : ℂ)‖ = 2 by norm_num]
          rw [norm_mul, hco]
          nlinarith [hMμ (z + (p.1:ℂ) * e p.2), norm_nonneg (μ (z + (p.1:ℂ) * e p.2))]
        have hT2 : ‖((starRingEnd ℂ) (e p.2))^2
            * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2))‖
            ≤ (R + 1) * Mf := by
          rw [norm_mul, norm_mul]
          have hc1 : ‖((starRingEnd ℂ) (e p.2))^2‖ = 1 := by
            rw [norm_pow, Complex.norm_conj, he_norm]; ring
          rw [hc1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1pos]
          have hfb : ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)‖ ≤ Mf := by
            calc ‖(fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)‖
                ≤ ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ * ‖I * e p.2‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ = ‖fderiv ℝ μ (z + (p.1:ℂ) * e p.2)‖ := by
                    rw [norm_mul, Complex.norm_I, he_norm, mul_one, mul_one]
              _ ≤ Mf := hMf _
          have hp1le : p.1 ≤ R + 1 := le_of_lt hpR
          nlinarith [norm_nonneg (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)
            (I * e p.2)), hMf (z + (p.1:ℂ) * e p.2), norm_nonneg (μ (z + (p.1:ℂ) * e p.2))]
        have hsum : ‖(-2 * I * ((starRingEnd ℂ) (e p.2))^2) * μ (z + (p.1:ℂ) * e p.2)
            + ((starRingEnd ℂ) (e p.2))^2
              * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2))‖
            ≤ 2 * Mμ + (R + 1) * Mf := le_trans (norm_add_le _ _) (add_le_add hT1 hT2)
        have hrinv : p.1⁻¹ ≤ r⁻¹ := by
          rw [inv_le_inv₀ hp1pos hr]; exact le_of_lt hpr
        have hMμnn : 0 ≤ Mμ := le_trans (norm_nonneg _) (hMμ z)
        have hsum_nn : 0 ≤ 2 * Mμ + (R + 1) * Mf := le_trans (norm_nonneg _) hsum
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
        apply mul_le_mul hrinv hsum (norm_nonneg _) (by positivity)
      have hIFM : IsFiniteMeasure (volume.restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
      have hintS : IntegrableOn AI S volume := ⟨haem, HasFiniteIntegral.of_bounded hbnd⟩
      apply hintS.of_forall_diff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      obtain ⟨hpT, hpnS⟩ := hp
      obtain ⟨hr', hθ⟩ := hpT
      simp only [Set.mem_Ioi] at hr'
      have hpR : R + 1 ≤ p.1 := by
        by_contra hlt
        rw [not_le] at hlt
        exact hpnS ⟨Set.mem_Ioo.mpr ⟨hr', hlt⟩, hθ⟩
      change (I/2 : ℂ) * (-((p.1:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e p.2))^2)
            * μ (z + (p.1:ℂ) * e p.2)
          + ((starRingEnd ℂ) (e p.2))^2
            * ((p.1:ℂ) * (fderiv ℝ μ (z + (p.1:ℂ) * e p.2)) (I * e p.2)))) = 0
      have hvμ : μ (z + (p.1:ℂ) * e p.2) = 0 := by
        apply hμ_van
        rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      have hv : fderiv ℝ μ (z + (p.1:ℂ) * e p.2) = 0 := by
        apply hfderiv_van
        rw [add_sub_cancel_left, norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      rw [hvμ, hv]; simp
    have hAIfn_eq : ∀ p ∈ Set.Ioi r ×ˢ Set.Ioo (-π : ℝ) π, AIfn p = AI p := by
      intro p hp
      obtain ⟨hp1, _⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      change (I/2 : ℂ) * (deriv (fun t : ℝ => -((p.1:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2
          * μ (z + (p.1:ℂ) * e t)) p.2) = AI p
      rw [hAI, hAval p (lt_trans hr hp1)]
    have hAI_int_fn : IntegrableOn AIfn (Set.Ioi r ×ˢ Set.Ioo (-π) π) volume :=
      hAI_int.congr_fun (fun p hp => (hAIfn_eq p hp).symm)
        (measurableSet_Ioi.prod measurableSet_Ioo)
    have hS2 : (∫ p in (Set.Ioi r ×ˢ Set.Ioo (-π) π), AIfn p) = 0 := by
      rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hAIfn_eq]
      -- Fubini: ρ outer, θ inner, with the inner integral vanishing.
      have hAI_int' : IntegrableOn AI (Set.Ioi r ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod ℝ ℝ]; exact hAI_int
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      rw [setIntegral_prod _ hAI_int']
      -- inner angular integral vanishes for each ρ > r.
      have hinner : ∀ ρ : ℝ, ρ ∈ Set.Ioi r → (∫ θ in Set.Ioo (-π) π, AI (ρ, θ)) = 0 := by
        intro ρ hρ
        simp only [Set.mem_Ioi] at hρ
        have hρpos : 0 < ρ := lt_trans hr hρ
        set g : ℝ → ℂ := fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t)
          with hg
        -- explicit derivative value V θ, continuous in θ, with HasDerivAt g (V θ) θ
        set V : ℝ → ℂ := fun θ => -((ρ:ℂ)⁻¹) * ((-2 * I * ((starRingEnd ℂ) (e θ))^2)
              * μ (z + (ρ:ℂ) * e θ)
            + ((starRingEnd ℂ) (e θ))^2
              * ((ρ:ℂ) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (I * e θ))) with hV
        have hg_deriv : ∀ θ : ℝ, HasDerivAt g (V θ) θ := by
          intro θ
          have hconj_d : HasDerivAt (fun s : ℝ => (starRingEnd ℂ) (e s))
              (-I * (starRingEnd ℂ) (e θ)) θ := by
            have hconj_eq : (fun s : ℝ => (starRingEnd ℂ) (e s))
                = fun s : ℝ => (Real.cos s : ℂ) - (Real.sin s : ℂ) * I := by
              funext s; rw [he_def]
              simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
            rw [hconj_eq]
            have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_cos θ).ofReal_comp
            have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
              (Real.hasDerivAt_sin θ).ofReal_comp
            have hdd := hcos.sub (hsin.mul_const I)
            convert hdd using 1
            rw [he_def]
            simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
            linear_combination (Real.sin θ : ℂ) * Complex.I_mul_I
          have hconj2_d : HasDerivAt (fun s : ℝ => ((starRingEnd ℂ) (e s))^2)
              (-2 * I * ((starRingEnd ℂ) (e θ))^2) θ := by
            have h := hconj_d.pow 2
            convert h using 1
            have hps : (2:ℕ) - 1 = 1 := rfl
            rw [hps, pow_one]; push_cast; ring
          have hμ_d : HasDerivAt (fun t : ℝ => μ (z + (ρ:ℂ) * e t))
              ((ρ:ℂ) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (I * e θ)) θ := by
            have hinner2 : HasDerivAt (fun t : ℝ => z + (ρ:ℂ) * e t) ((ρ:ℂ) * (I * e θ)) θ :=
              ((he_deriv θ).const_mul (ρ:ℂ)).const_add z
            have hcomp := (hgdiff _).hasFDerivAt.comp_hasDerivAt θ hinner2
            have hsm : (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) ((ρ:ℂ) * (I * e θ))
                = (ρ:ℂ) * (fderiv ℝ μ (z + (ρ:ℂ) * e θ)) (I * e θ) := by
              rw [show ((ρ:ℂ) * (I * e θ)) = (ρ:ℝ) • (I * e θ) by rw [Complex.real_smul], map_smul,
                Complex.real_smul]
            rwa [hsm] at hcomp
          have hprod := hconj2_d.mul hμ_d
          have hfull := hprod.const_mul (-((ρ:ℂ)⁻¹))
          have hfun : (fun t : ℝ => -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))
              = (fun t : ℝ => -((ρ:ℂ)⁻¹) * (((starRingEnd ℂ) (e t))^2 * μ (z + (ρ:ℂ) * e t))) := by
            funext t; ring
          rw [hg, hfun]
          exact hfull
        have hV_cont : Continuous V := by
          rw [hV]
          have hP : Continuous (fun θ : ℝ => z + (ρ:ℂ) * e θ) :=
            continuous_const.add (continuous_const.mul he_cont)
          have hconj : Continuous (fun θ : ℝ => (starRingEnd ℂ) (e θ)) :=
            Complex.continuous_conj.comp he_cont
          apply Continuous.mul continuous_const
          apply Continuous.add
          · exact ((continuous_const.mul (hconj.pow 2))).mul (hμ.continuous.comp hP)
          · apply Continuous.mul (hconj.pow 2)
            apply Continuous.mul continuous_const
            exact (hfderiv_cont.comp hP).clm_apply (continuous_const.mul he_cont)
        have hAIeq : ∀ θ : ℝ, AI (ρ, θ) = (I/2 : ℂ) * V θ := by
          intro θ; rw [hAI, hV]
        rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hAIeq θ)]
        rw [show (∫ θ in Set.Ioo (-π : ℝ) π, (I/2 : ℂ) * V θ)
            = (I/2 : ℂ) * ∫ θ in Set.Ioo (-π : ℝ) π, V θ from integral_const_mul (I/2 : ℂ) V]
        have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hg_deriv θ)
          (hV_cont.intervalIntegrable _ _)]
        have hπ : e π = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
        have hmπ : e (-π) = (-1 : ℂ) := by rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
        have hper : g π = g (-π) := by
          change -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e π))^2 * μ (z + (ρ:ℂ) * e π)
            = -((ρ:ℂ)⁻¹) * ((starRingEnd ℂ) (e (-π)))^2 * μ (z + (ρ:ℂ) * e (-π))
          rw [hπ, hmπ]
        rw [hper, sub_self, mul_zero]
      rw [setIntegral_congr_fun measurableSet_Ioi hinner]
      simp
    rw [integral_sub hRI_int hAI_int_fn, hS1, hS2, sub_zero]
  -- Assemble: `czOp r = boundary r - kernel r`, take `r → 0`.
  have hmain : Tendsto (fun r : ℝ => ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ ζ, (dz μ ζ) / (ζ - z))) := by
    have hcongr : ∀ᶠ r in 𝓝[>] (0:ℝ),
        (∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y)
          = ((1/2 : ℂ) * ∫ θ in Set.Ioo (-π) π,
                ((starRingEnd ℂ) (e θ))^2 * μ (z + (r : ℂ) * e θ))
            - ∫ y in (Metric.ball z r)ᶜ, (dz μ y) * (z - y)⁻¹ := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hPolar r hr
    have htarget : (∫ ζ, (dz μ ζ) / (ζ - z)) = 0 - ∫ ζ, (dz μ ζ) * (z - ζ)⁻¹ := by
      rw [zero_sub, ← integral_neg]
      apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
      rw [div_eq_mul_inv, ← neg_sub z ζ, inv_neg, mul_neg]
    rw [htarget]
    refine (hB2.sub hB1).congr' ?_
    filter_upwards [hcongr] with r hr
    exact hr.symm
  -- Express the `czOperator` truncation via the explicit integral (`rfl`).
  have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r μ z
      = ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * μ y := fun r => rfl
  simpa [hcz] using hmain

/-- **`T = ∂ ∘ P`.** The Beurling transform is the holomorphic Wirtinger
derivative of the Cauchy transform. -/
theorem beurling_eq_dz_cauchyTransform (hμ : ContDiff ℝ 1 μ) (hμc : HasCompactSupport μ)
    (z : ℂ) : dz (cauchyTransform μ) z = beurling μ z := by
  -- Part A: `∂(Pμ) = P(∂μ)`, the `dz` analog of `dzbar_cauchyTransform_eq`.
  have hA : dz (cauchyTransform μ) z = cauchyTransform (fun ζ => dz μ ζ) z := by
    set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
    set k : ℂ → ℂ := fun u => -u⁻¹ with hk
    have hk_loc : LocallyIntegrable k volume := by
      rw [hk]
      apply LocallyIntegrable.neg
      rw [MeasureTheory.locallyIntegrable_iff]
      intro K hK
      obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
      apply MeasureTheory.IntegrableOn.mono_set _ hR
      rw [IntegrableOn]
      refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
        ← Complex.lintegral_comp_polarCoord_symm]
      set lhs : ℝ × ℝ → ENNReal := fun p =>
        ENNReal.ofReal p.1 •
          (Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)
        with hlhs
      set box : ℝ × ℝ → ENNReal :=
        (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
      have hbound : ∀ p ∈ polarCoord.target, lhs p ≤ box p := by
        intro p hp
        simp only [hlhs, hbox]
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R
        · rw [Set.indicator_of_mem hmem]
          have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
          have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
            rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
          rw [enorm_inv hsymm_ne]
          have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
            rw [← ofReal_norm_eq_enorm, hnorm]
          rw [henorm, smul_eq_mul,
            ENNReal.mul_inv_cancel (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
              ENNReal.ofReal_lt_top.ne]
          have hpR : p.1 ≤ R := by
            rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem
            exact hmem
          have hmem2 : p ∈ Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π :=
            Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩
          rw [Set.indicator_of_mem hmem2]
        · rw [Set.indicator_of_notMem hmem]
          simp
      have hmeas : Measurable box :=
        measurable_const.indicator (measurableSet_Ioc.prod measurableSet_Ioo)
      have hbox_meas : MeasurableSet (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) :=
        measurableSet_Ioc.prod measurableSet_Ioo
      calc
        ∫⁻ p in polarCoord.target, lhs p
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = volume (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) := by
              rw [hbox, lintegral_indicator hbox_meas]; simp
        _ < ⊤ := by
              have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
                Measure.volume_eq_prod ℝ ℝ
              rw [hvol, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
              exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hCT : cauchyTransform μ
        = fun w => (-(1 / (π : ℂ))) • (MeasureTheory.convolution μ k L volume) w := by
      funext w
      rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
      congr 1
      apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
      rw [hL, ContinuousLinearMap.mul_apply']
      change μ ζ / (ζ - w) = μ ζ * -(w - ζ)⁻¹
      have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
      rw [hflip, div_eq_mul_inv]
    have hfd0 : HasFDerivAt (MeasureTheory.convolution μ k L volume)
        (MeasureTheory.convolution (fderiv ℝ μ) k (ContinuousLinearMap.precompL ℂ L) volume z) z :=
      hμc.hasFDerivAt_convolution_left L hμ hk_loc z
    set D₀ := MeasureTheory.convolution (fderiv ℝ μ) k (ContinuousLinearMap.precompL ℂ L) volume z
      with hD₀
    have hfderiv : fderiv ℝ (cauchyTransform μ) z = (-(1 / (π : ℂ))) • D₀ := by
      have hfd : HasFDerivAt (cauchyTransform μ) ((-(1 / (π : ℂ))) • D₀) z := by
        rw [hCT]; exact hfd0.const_smul (-(1 / (π : ℂ)))
      exact hfd.fderiv
    have hex : ConvolutionExistsAt (fderiv ℝ μ) k z (ContinuousLinearMap.precompL ℂ L) volume :=
      ((hμc.fderiv ℝ).convolutionExists_left (ContinuousLinearMap.precompL ℂ L)
        (hμ.continuous_fderiv one_ne_zero) hk_loc) z
    have hex_int : Integrable
        (fun t => (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ μ t) (k (z - t))) volume :=
      hex
    set A : ℂ → ℂ := fun t => (fderiv ℝ μ t) 1 * k (z - t) with hA_def
    set B : ℂ → ℂ := fun t => (fderiv ℝ μ t) Complex.I * k (z - t) with hB_def
    have hA_int : Integrable A volume := by
      have h := hex_int.apply_continuousLinearMap (1 : ℂ)
      apply h.congr; apply ae_of_all _ fun t => ?_
      change (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ μ t) (k (z - t)) 1 = A t
      rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
    have hB_int : Integrable B volume := by
      have h := hex_int.apply_continuousLinearMap Complex.I
      apply h.congr; apply ae_of_all _ fun t => ?_
      change (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ μ t) (k (z - t)) Complex.I = B t
      rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
    have hD₀_eval : ∀ v : ℂ, D₀ v = ∫ t, ((fderiv ℝ μ t) v) * (k (z - t)) ∂volume := by
      intro v
      rw [hD₀, MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hex_int]
      apply integral_congr_ae (ae_of_all _ fun t => ?_)
      rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
    have hD₀1 : D₀ 1 = ∫ t, A t := hD₀_eval 1
    have hD₀I : D₀ Complex.I = ∫ t, B t := hD₀_eval Complex.I
    have hRHS : cauchyTransform (fun ζ => dz μ ζ) z
        = (-(1 / (π : ℂ))) * ((1 / 2) * ((∫ t, A t) - Complex.I * (∫ t, B t))) := by
      rw [cauchyTransform]
      congr 1
      have hker : ∀ t : ℂ, (dz μ t) / (t - z) = (1 / 2 : ℂ) * (A t - Complex.I * B t) := by
        intro t
        rw [dz]
        have hk_eq : (t - z)⁻¹ = k (z - t) := by
          rw [hk]; change (t - z)⁻¹ = -(z - t)⁻¹
          rw [← neg_sub t z, inv_neg, neg_neg]
        rw [div_eq_mul_inv, hk_eq, hA_def, hB_def]; ring
      rw [integral_congr_ae (ae_of_all _ hker)]
      have h1 : ∫ (a : ℂ), (1 : ℂ) / 2 * (A a - Complex.I * B a)
          = (1 : ℂ) / 2 * ∫ a, (A a - Complex.I * B a) :=
        MeasureTheory.integral_const_mul ((1 : ℂ) / 2) _
      rw [h1]; congr 1
      have h2 : ∫ a, (A a - Complex.I * B a) = (∫ a, A a) - ∫ a, Complex.I * B a :=
        integral_sub hA_int (hB_int.const_mul Complex.I)
      rw [h2]; congr 1
      exact MeasureTheory.integral_const_mul Complex.I B
    rw [hRHS, dz, hfderiv]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hD₀1, hD₀I]
    ring
  rw [hA]
  -- Part B: `P(∂μ) = beurling μ`, via the extracted truncation Tendsto.
  rw [cauchyTransform, beurling]
  congr 1
  refine (Filter.Tendsto.limUnder_eq ?_).symm
  have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r μ z
      = czOperator beurlingKernel r μ z := fun r => rfl
  simpa only [hcz] using czOperator_beurling_tendsto_smooth hμ hμc z

/-! ## `Lᵖ` boundedness — supporting lemmas

The three boundedness theorems below rest on a dependency tree rooted at the
`L²` isometry on the smooth dense class (`beurling_l2_isometry_smooth`). The
helpers here build that tree leaf-first. -/

/-- Additivity of the truncated Beurling operator in the function argument. -/
lemma czOperator_beurling_add {f g : ℂ → ℂ} {r : ℝ} {w : ℂ}
    (hf : IntegrableOn (fun y => beurlingKernel w y * f y) (Metric.ball w r)ᶜ volume)
    (hg : IntegrableOn (fun y => beurlingKernel w y * g y) (Metric.ball w r)ᶜ volume) :
    czOperator beurlingKernel r (f + g) w
      = czOperator beurlingKernel r f w + czOperator beurlingKernel r g w := by
  change (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * (f + g) y)
      = (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * f y)
        + ∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * g y
  simp only [Pi.add_apply, mul_add]
  exact integral_add hf hg

/-- Homogeneity of the truncated Beurling operator in the function argument. -/
lemma czOperator_beurling_const_smul {f : ℂ → ℂ} {r : ℝ} {w : ℂ} (c : ℂ) :
    czOperator beurlingKernel r (c • f) w = c * czOperator beurlingKernel r f w := by
  change (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * (c • f) y)
      = c * ∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * f y
  have h1 : (∫ y in (Metric.ball w r)ᶜ, beurlingKernel w y * (c • f) y)
      = ∫ y in (Metric.ball w r)ᶜ, c * (beurlingKernel w y * f y) := by
    refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h1]
  exact integral_const_mul c _

/-- On the smooth compactly supported class the truncated Beurling integrals
converge as `r → 0⁺` to `-π · beurling μ` — read off the proof of
`beurling_eq_dz_cauchyTransform`, which already exhibits this limit. -/
lemma beurling_ae_tendsto_smooth {ν : ℂ → ℂ} (hν : ContDiff ℝ 1 ν)
    (hνc : HasCompactSupport ν) (w : ℂ) :
    Filter.Tendsto (fun r => czOperator beurlingKernel r ν w) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * beurling ν w)) := by
  have h := czOperator_beurling_tendsto_smooth hν hνc w
  have hval : (∫ ζ, (dz ν ζ) / (ζ - w)) = -(π : ℂ) * beurling ν w := by
    have hlim : limUnder (𝓝[>] (0:ℝ))
        (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w)
        = (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      apply Filter.Tendsto.limUnder_eq
      have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w
          = czOperator beurlingKernel r ν w := fun r => rfl
      simpa only [hcz] using h
    have hb : beurling ν w = -(1 / (π : ℂ)) * (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      rw [beurling, hlim]
    rw [hb]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rwa [hval] at h

set_option maxHeartbeats 400000 in
-- The proof inlines, as one local `mult_ae` helper, the whole-plane distributional
-- integration by parts (the `bridge`), the line-derivative Fourier multiplier, and the
-- a.e. extraction against smooth compactly supported test functions; elaborating these
-- many nested `have`s in a single declaration needs extra budget.
open FourierTransform TemperedDistribution SchwartzMap in
open scoped LineDeriv in
/-- **Wirtinger / Dirichlet-energy `L²` isometry.** For two `C¹` `L²` functions
`B` and `N` on `ℂ` whose first directional derivatives all lie in `L²` and which
satisfy the Beltrami-type identity `∂̄B = ∂N` pointwise, the `L²` norms agree:
`‖B‖₂ = ‖N‖₂`.

This is the analytic linchpin of the Beurling `L²` isometry. The proof is the
whole-plane integration by parts identifying the *distributional* line-derivative
of a `C¹` `L²` function with the tempered distribution of its *classical*
directional derivative (boundary terms vanish by `L²` decay against Schwartz test
functions, via `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), combined
with the modulus-one Fourier multiplier `ξ̄/ξ`: applying
`TemperedDistribution.fourier_lineDerivOp_eq` to `∂̄B = ∂N` turns the identity into
`ξ · 𝓕B = ξ̄ · 𝓕N` a.e., whence `|𝓕B| = |𝓕N|` a.e. and Plancherel
(`Lp.norm_fourier_eq`) gives the claim. -/
lemma dirichlet_energy_isometry {B N : ℂ → ℂ}
    (hB : ContDiff ℝ 1 B) (hN : ContDiff ℝ 1 N)
    (hBL2 : MemLp B 2 volume) (hNL2 : MemLp N 2 volume)
    (hB1L2 : MemLp (fun z => (fderiv ℝ B z) 1) 2 volume)
    (hBIL2 : MemLp (fun z => (fderiv ℝ B z) Complex.I) 2 volume)
    (hN1L2 : MemLp (fun z => (fderiv ℝ N z) 1) 2 volume)
    (hNIL2 : MemLp (fun z => (fderiv ℝ N z) Complex.I) 2 volume)
    (hClairaut : ∀ z, dzbar B z = dz N z) :
    eLpNorm B 2 volume = eLpNorm N 2 volume := by
  -- Local helper: the a.e. Fourier-multiplier identity for one `C¹` `L²` function `g`
  -- and one direction `m`, the combination of the distributional integration by parts
  -- (`bridge`) with the line-derivative Fourier multiplier.
  have mult_ae : ∀ (g : ℂ → ℂ), ContDiff ℝ 1 g → ∀ (hgL2 : MemLp g 2 volume) (m : ℂ)
      (hdgL2 : MemLp (fun z => (fderiv ℝ g z) m) 2 volume),
      (fun ζ => (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ) *
          (𝓕 (hgL2.toLp g) : Lp ℂ 2 volume) ζ)
        =ᵐ[volume]
          (fun ζ => (𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) : Lp ℂ 2 volume) ζ) := by
    intro g hg hgL2 m hdgL2
    -- distributional integration by parts (the bridge)
    have bridge : ∂_{m} (Lp.toTemperedDistribution (hgL2.toLp g))
        = Lp.toTemperedDistribution (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) := by
      ext φ
      rw [lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
        Lp.toTemperedDistribution_apply]
      have hL : ∫ (x : ℂ), (-∂_{m} φ) x • (hgL2.toLp g) x
          = ∫ (x : ℂ), -((fderiv ℝ φ x) m) * g x := by
        apply integral_congr_ae
        filter_upwards [hgL2.coeFn_toLp] with x hx
        rw [hx]; simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
      have hR : ∫ (x : ℂ), φ x • (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) x
          = ∫ (x : ℂ), φ x * (fderiv ℝ g x m) := by
        apply integral_congr_ae
        filter_upwards [hdgL2.coeFn_toLp] with x hx
        rw [hx]; simp [smul_eq_mul]
      rw [hL, hR]
      have hφmem : MemLp (φ : ℂ → ℂ) 2 volume := φ.memLp 2 volume
      have hφ'mem : MemLp (fun x => (fderiv ℝ φ x) m) 2 volume :=
        (∂_{m} φ : 𝓢(ℂ, ℂ)).memLp 2 volume
      have I1 : Integrable (fun x => (fderiv ℝ g x m) * φ x) volume :=
        hdgL2.integrable_mul hφmem
      have I2 : Integrable (fun x => g x * (fderiv ℝ φ x m)) volume :=
        hgL2.integrable_mul hφ'mem
      have I3 : Integrable (fun x => g x * φ x) volume := hgL2.integrable_mul hφmem
      have key : ∫ x, g x * (fderiv ℝ φ x m) = - ∫ x, (fderiv ℝ g x m) * φ x :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable I1 I2 I3
          (fun x _ => hg.differentiable (by norm_num) x) (fun x _ => φ.differentiableAt)
      have hLgoal : ∫ (x : ℂ), -((fderiv ℝ φ x) m) * g x
          = -∫ x, g x * (fderiv ℝ φ x m) := by
        rw [← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only []; rw [neg_mul, mul_comm]
      have hRgoal : ∫ (x : ℂ), φ x * (fderiv ℝ g x m)
          = ∫ x, (fderiv ℝ g x m) * φ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only []; rw [mul_comm (φ x)]
      rw [hLgoal, hRgoal, key, neg_neg]
    -- distributional multiplier identity
    have mult_dist : (2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (𝓕 (Lp.toTemperedDistribution (hgL2.toLp g)))
        = Lp.toTemperedDistribution
            (𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) : Lp ℂ 2 volume) := by
      have hf := TemperedDistribution.fourier_lineDerivOp_eq
        (Lp.toTemperedDistribution (hgL2.toLp g)) m
      rw [bridge] at hf
      rw [Lp.fourier_toTemperedDistribution_eq] at hf
      rw [← hf]
    -- distributional identity transported to L²-Fourier on both sides
    have hmd0 : (2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ))
          (Lp.toTemperedDistribution (𝓕 (hgL2.toLp g) : Lp ℂ 2 volume))
        = Lp.toTemperedDistribution
            (𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) : Lp ℂ 2 volume) := by
      rw [← Lp.fourier_toTemperedDistribution_eq]
      exact mult_dist
    -- extract the a.e. identity
    set Fg : Lp ℂ 2 volume := 𝓕 (hgL2.toLp g) with hFg
    set Fdg : Lp ℂ 2 volume := 𝓕 (hdgL2.toLp (fun z => (fderiv ℝ g z) m)) with hFdg
    have hcont : Continuous
        (fun ζ : ℂ => (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ)) := by
      fun_prop
    have hFgli : LocallyIntegrable (fun ζ => Fg ζ) volume :=
      (Lp.memLp Fg).locallyIntegrable (by norm_num)
    have hFdgli : LocallyIntegrable (fun ζ => Fdg ζ) volume :=
      (Lp.memLp Fdg).locallyIntegrable (by norm_num)
    have hfli : LocallyIntegrable
        (fun ζ => (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ) * Fg ζ) volume := by
      rw [MeasureTheory.locallyIntegrable_iff]
      intro K hK
      have hIK : IntegrableOn (fun ζ => Fg ζ) K volume := hFgli.integrableOn_isCompact hK
      have := hIK.continuousOn_mul (hcont.continuousOn) hK
      simpa [mul_assoc] using this
    refine ae_eq_of_integral_contDiff_smul_eq hfli hFdgli (fun χ hχ hχc => ?_)
    have hmd := hmd0
    have hχcs : HasCompactSupport (fun x => (Complex.ofRealCLM (χ x))) := hχc.comp_left rfl
    have hχsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => (Complex.ofRealCLM (χ x))) :=
      Complex.ofRealCLM.contDiff.comp hχ
    set φ : 𝓢(ℂ, ℂ) := hχcs.toSchwartzMap hχsm with hφ
    have hφval : ∀ x, φ x = ((χ x : ℝ) : ℂ) := fun x => rfl
    have hev := congrArg (fun (D : 𝓢'(ℂ, ℂ)) => D φ) hmd
    have hLHS : ((2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (Lp.toTemperedDistribution Fg)) φ
        = (2 * Real.pi * Complex.I) *
            ∫ ζ, (((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ := by
      rw [show ((2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (Lp.toTemperedDistribution Fg)) φ
          = (2 * Real.pi * Complex.I) • (TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((inner ℝ x m : ℝ) : ℂ)) (Lp.toTemperedDistribution Fg)) φ from rfl]
      rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards with ζ
      have htg : (fun x => ((inner ℝ x m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
      rw [SchwartzMap.smulLeftCLM_apply_apply htg]
    have hRHS : (Lp.toTemperedDistribution Fdg) φ = ∫ ζ, φ ζ • Fdg ζ :=
      Lp.toTemperedDistribution_apply Fdg φ
    simp only at hev
    rw [hLHS, hRHS] at hev
    have hLconv : (∫ x, χ x • (2 * Real.pi * Complex.I * ((inner ℝ x m : ℝ) : ℂ) * Fg x))
        = 2 * Real.pi * Complex.I
            * ∫ ζ, (((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ := by
      rw [show (2 * Real.pi * Complex.I
              * ∫ ζ, (((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ)
          = ∫ ζ, 2 * Real.pi * Complex.I * ((((inner ℝ ζ m : ℝ) : ℂ) • φ ζ) • Fg ζ)
          from (MeasureTheory.integral_const_mul _ _).symm]
      apply integral_congr_ae
      filter_upwards with ζ
      rw [hφval]
      simp only [Complex.real_smul, smul_eq_mul]
      ring
    have hRconv : (∫ x, χ x • Fdg x) = ∫ ζ, φ ζ • Fdg ζ := by
      apply integral_congr_ae
      filter_upwards with ζ
      rw [hφval, Complex.real_smul, smul_eq_mul]
    exact hLconv.trans (hev.trans hRconv.symm)
  -- ===== final assembly =====
  set FB : Lp ℂ 2 volume := 𝓕 (hBL2.toLp B) with hFB
  set FN : Lp ℂ 2 volume := 𝓕 (hNL2.toLp N) with hFN
  have mB1 := mult_ae B hB hBL2 1 hB1L2
  have mBI := mult_ae B hB hBL2 Complex.I hBIL2
  have mN1 := mult_ae N hN hNL2 1 hN1L2
  have mNI := mult_ae N hN hNL2 Complex.I hNIL2
  have hin1 : ∀ ζ : ℂ, (inner ℝ ζ (1 : ℂ) : ℝ) = ζ.re := by
    intro ζ; rw [Complex.inner]; simp
  have hinI : ∀ ζ : ℂ, (inner ℝ ζ Complex.I : ℝ) = ζ.im := by
    intro ζ; rw [Complex.inner]; simp
  have hLpfn :
      (hB1L2.toLp (fun z => (fderiv ℝ B z) 1)
        + Complex.I • hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))
      = (hN1L2.toLp (fun z => (fderiv ℝ N z) 1)
        - Complex.I • hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (hB1L2.toLp (fun z => (fderiv ℝ B z) 1))
        (Complex.I • hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I)),
      Lp.coeFn_smul Complex.I (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I)),
      Lp.coeFn_sub (hN1L2.toLp (fun z => (fderiv ℝ N z) 1))
        (Complex.I • hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)),
      Lp.coeFn_smul Complex.I (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)),
      hB1L2.coeFn_toLp, hBIL2.coeFn_toLp, hN1L2.coeFn_toLp, hNIL2.coeFn_toLp]
      with ζ ha hsmB hs hsmN hb1 hbi hn1 hni
    rw [ha, hs]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hsmB, hsmN, hb1, hbi, hn1, hni,
      smul_eq_mul]
    have hcl := hClairaut ζ
    rw [dzbar, dz] at hcl
    linear_combination 2 * hcl
  have hLpeq :
      𝓕 (hB1L2.toLp (fun z => (fderiv ℝ B z) 1))
        + Complex.I • 𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))
      = 𝓕 (hN1L2.toLp (fun z => (fderiv ℝ N z) 1))
        - Complex.I • 𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)) := by
    have hap := congrArg (fun (x : Lp ℂ 2 volume) => 𝓕 x) hLpfn
    simp only at hap
    rw [FourierAdd.fourier_add, FourierSMul.fourier_smul,
      sub_eq_add_neg, ← neg_smul, FourierAdd.fourier_add, FourierSMul.fourier_smul,
      neg_smul, ← sub_eq_add_neg] at hap
    exact hap
  have hLpeq_ae :
      (fun ζ => 𝓕 (hB1L2.toLp (fun z => (fderiv ℝ B z) 1)) ζ
          + Complex.I * 𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I)) ζ)
      =ᵐ[volume]
      (fun ζ => 𝓕 (hN1L2.toLp (fun z => (fderiv ℝ N z) 1)) ζ
          - Complex.I * 𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)) ζ) := by
    have hc := congrArg (fun (x : Lp ℂ 2 volume) => (x : ℂ → ℂ)) hLpeq
    filter_upwards [Lp.coeFn_add (𝓕 (hB1L2.toLp (fun z => (fderiv ℝ B z) 1)))
        (Complex.I • 𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))),
      Lp.coeFn_smul Complex.I (𝓕 (hBIL2.toLp (fun z => (fderiv ℝ B z) Complex.I))),
      Lp.coeFn_sub (𝓕 (hN1L2.toLp (fun z => (fderiv ℝ N z) 1)))
        (Complex.I • 𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I))),
      Lp.coeFn_smul Complex.I (𝓕 (hNIL2.toLp (fun z => (fderiv ℝ N z) Complex.I)))]
      with ζ ha hsmB hs hsmN
    have := congrFun hc ζ
    simp only at this
    rw [ha, hs] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hsmB, hsmN, smul_eq_mul] at this
    exact this
  have hmod : (fun ζ => ζ * FB ζ) =ᵐ[volume] (fun ζ => (starRingEnd ℂ) ζ * FN ζ) := by
    filter_upwards [mB1, mBI, mN1, mNI, hLpeq_ae] with ζ hB1 hBI hN1 hNI hcomb
    rw [hin1] at hB1 hN1
    rw [hinI] at hBI hNI
    rw [← hB1, ← hBI, ← hN1, ← hNI] at hcomb
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hre : ζ = (ζ.re : ℂ) + ζ.im * Complex.I := by
      rw [Complex.ext_iff]; simp
    have hconj : (starRingEnd ℂ) ζ = (ζ.re : ℂ) - ζ.im * Complex.I := by
      rw [Complex.ext_iff]; simp
    have hkey : (2 * (Real.pi : ℂ) * Complex.I) * (ζ * FB ζ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((starRingEnd ℂ) ζ * FN ζ) := by
      rw [hconj]
      nth_rewrite 1 [hre]
      linear_combination hcomb
    exact mul_left_cancel₀ hpi hkey
  have habs : (fun ζ => ‖FB ζ‖) =ᵐ[volume] (fun ζ => ‖FN ζ‖) := by
    filter_upwards [hmod, volume.ae_ne (0 : ℂ)] with ζ hm hne
    have h1 : ‖ζ * FB ζ‖ = ‖(starRingEnd ℂ) ζ * FN ζ‖ := by rw [hm]
    rw [norm_mul, norm_mul, RCLike.norm_conj] at h1
    exact mul_left_cancel₀ (by simpa [norm_eq_zero] using hne) h1
  have henorm : (fun ζ => ‖FB ζ‖ₑ) =ᵐ[volume] (fun ζ => ‖FN ζ‖ₑ) := by
    filter_upwards [habs] with ζ h
    simp only [enorm_eq_nnnorm, ← norm_toNNReal]
    rw [h]
  have hnormeq : ‖FB‖ = ‖FN‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_enorm_ae henorm
  rw [hFB, hFN, Lp.norm_fourier_eq, Lp.norm_fourier_eq,
    Lp.norm_toLp B hBL2, Lp.norm_toLp N hNL2] at hnormeq
  have hBfin : eLpNorm B 2 volume ≠ ⊤ := hBL2.2.ne
  have hNfin : eLpNorm N 2 volume ≠ ⊤ := hNL2.2.ne
  exact (ENNReal.toReal_eq_toReal_iff' hBfin hNfin).mp hnormeq

set_option maxHeartbeats 400000 in
-- The proof inlines the smoothness of the Cauchy transform, the integral
-- representation of `beurling ν` off the support, and the differentiation-under-
-- the-integral decay estimates for `beurling ν` and its directional derivatives;
-- elaborating this many nested `have`s in a single declaration needs extra budget.
/-- **`L²` isometry on the smooth dense class** — the analytic core of the whole
milestone. For `μ ∈ C^∞_c`, `‖beurling μ‖₂ = ‖μ‖₂`. On this class
`beurling μ = ∂(Pμ)` (`beurling_eq_dz_cauchyTransform`) and `μ = ∂̄(Pμ)`
(`dzbar_cauchyTransform`), so the statement is the Dirichlet-energy identity
`‖∂F‖₂ = ‖∂̄F‖₂` for `F = Pμ`. -/
lemma beurling_l2_isometry_smooth {ν : ℂ → ℂ} (hν : ContDiff ℝ (⊤ : ℕ∞) ν)
    (hνc : HasCompactSupport ν) :
    eLpNorm (beurling ν) 2 volume = eLpNorm ν 2 volume := by
  have hν1 : ContDiff ℝ 1 ν := hν.of_le (by exact_mod_cast le_top)
  set B : ℂ → ℂ := beurling ν with hBdef
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport ν ⊆ Metric.closedBall (0 : ℂ) R :=
    (hνc.isCompact.isBounded).subset_closedBall 0
  have hClairaut : ∀ z, dzbar B z = dz ν z := by
    rw [hBdef]
    -- F smooth (inlined, abbreviated by reusing the lemma's existing infra via cauchyTransform)
    have hF : ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform ν) := by
      set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
      set k : ℂ → ℂ := fun u => -u⁻¹ with hk
      have hk_loc : LocallyIntegrable k volume := by
        rw [hk]
        apply LocallyIntegrable.neg
        rw [MeasureTheory.locallyIntegrable_iff]
        intro K hK
        obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
        apply MeasureTheory.IntegrableOn.mono_set _ hR₀
        rw [IntegrableOn]
        refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
        rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
          ← Complex.lintegral_comp_polarCoord_symm]
        set box : ℝ × ℝ → ENNReal :=
          (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
        have hbound : ∀ p ∈ polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
              (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p) ≤ box p := by
          intro p hp
          simp only [hbox]
          rw [polarCoord_target, Set.mem_prod] at hp
          obtain ⟨hp1, hp2⟩ := hp
          simp only [Set.mem_Ioi] at hp1
          by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R₀
          · rw [Set.indicator_of_mem hmem]
            have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
              rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
            have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
              rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
            rw [enorm_inv hsymm_ne]
            have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
              rw [← ofReal_norm_eq_enorm, hnorm]
            rw [henorm, smul_eq_mul,
              ENNReal.mul_inv_cancel
                (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
                ENNReal.ofReal_lt_top.ne]
            have hpR : p.1 ≤ R₀ := by
              rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
            rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩)]
          · rw [Set.indicator_of_notMem hmem]; simp
        calc
          ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
              (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)
              ≤ ∫⁻ p in polarCoord.target, box p :=
                setLIntegral_mono (measurable_const.indicator
                  (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
          _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
          _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π) := by
                rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]; simp
          _ < ⊤ := by
                rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
                exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hCT : cauchyTransform ν
          = fun w => (-(1 / (π : ℂ))) • (MeasureTheory.convolution ν k L volume) w := by
        funext w
        rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
        congr 1
        apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
        rw [hL, ContinuousLinearMap.mul_apply']
        change ν ζ / (ζ - w) = ν ζ * -(w - ζ)⁻¹
        have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
        rw [hflip, div_eq_mul_inv]
      rw [hCT]
      exact (hνc.contDiff_convolution_left L hν hk_loc).const_smul _
    -- B = dz F
    have hBeqF : beurling ν = fun z => dz (cauchyTransform ν) z := by
      funext z; exact (beurling_eq_dz_cauchyTransform hν1 hνc z).symm
    -- Clairaut core for F
    intro z
    rw [hBeqF]
    set F := cauchyTransform ν with hFdef
    -- mixed-partial symmetry core
    have hClairautCore : dzbar (fun w => dz F w) z = dz (fun w => dzbar F w) z := by
      set S := fderiv ℝ (fderiv ℝ F) z with hS
      have hfd : ContDiff ℝ (⊤:ℕ∞) (fun w => fderiv ℝ F w) := hF.fderiv_right (by simp)
      have hf'diff : Differentiable ℝ (fun w => fderiv ℝ F w) := hfd.differentiable (by simp)
      have hsymm : ∀ v w : ℂ, (S v) w = (S w) v := by
        have hsymF : IsSymmSndFDerivAt ℝ F z := by
          apply (hF.contDiffAt).isSymmSndFDerivAt
          rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top
        intro v w; exact hsymF.eq v w
      have hdzF : ∀ m' : ℂ, (fderiv ℝ (fun w => dz F w) z) m'
          = (1/2 : ℂ) * ((S m') 1 - Complex.I * (S m') Complex.I) := by
        intro m'
        have hd1 : HasFDerivAt (fun w => (fderiv ℝ F w) (1:ℂ))
            ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hdI : HasFDerivAt (fun w => (fderiv ℝ F w) Complex.I)
            ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ Complex.I).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hcomb : HasFDerivAt (fun w => dz F w)
            ((1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S
              - Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S)) z :=
          (hd1.sub (hdI.const_smul Complex.I)).const_smul (1/2 : ℂ)
        rw [hcomb.fderiv]
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
      have hdzbarF : ∀ m' : ℂ, (fderiv ℝ (fun w => dzbar F w) z) m'
          = (1/2 : ℂ) * ((S m') 1 + Complex.I * (S m') Complex.I) := by
        intro m'
        have hd1 : HasFDerivAt (fun w => (fderiv ℝ F w) (1:ℂ))
            ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hdI : HasFDerivAt (fun w => (fderiv ℝ F w) Complex.I)
            ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S) z := by
          rw [hS]
          exact (ContinuousLinearMap.apply ℝ ℂ Complex.I).hasFDerivAt.comp z (hf'diff z).hasFDerivAt
        have hcomb : HasFDerivAt (fun w => dzbar F w)
            ((1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).comp S
              + Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp S)) z :=
          (hd1.add (hdI.const_smul Complex.I)).const_smul (1/2 : ℂ)
        rw [hcomb.fderiv]
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
      rw [dzbar, dz, hdzF 1, hdzF Complex.I, hdzbarF 1, hdzbarF Complex.I]
      rw [hsymm Complex.I 1, hsymm 1 Complex.I]
      ring
    -- dzbar F = ν as functions
    have hdzbarF_eq : (fun w => dzbar F w) = ν := by
      funext w; rw [hFdef]; exact dzbar_cauchyTransform hν1 hνc w
    rw [hClairautCore, hdzbarF_eq]
  have hB : ContDiff ℝ 1 B := by
    rw [hBdef]
    -- F = cauchyTransform ν is C^∞
    have hF : ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform ν) := by
      set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
      set k : ℂ → ℂ := fun u => -u⁻¹ with hk
      have hk_loc : LocallyIntegrable k volume := by
        rw [hk]
        apply LocallyIntegrable.neg
        rw [MeasureTheory.locallyIntegrable_iff]
        intro K hK
        obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
        apply MeasureTheory.IntegrableOn.mono_set _ hR₀
        rw [IntegrableOn]
        refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
        rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
          ← Complex.lintegral_comp_polarCoord_symm]
        set lhs : ℝ × ℝ → ENNReal := fun p =>
          ENNReal.ofReal p.1 •
            (Metric.closedBall (0 : ℂ) R₀).indicator (fun u : ℂ => ‖u⁻¹‖ₑ)
              (Complex.polarCoord.symm p)
          with hlhs
        set box : ℝ × ℝ → ENNReal :=
          (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
        have hbound : ∀ p ∈ polarCoord.target, lhs p ≤ box p := by
          intro p hp
          simp only [hlhs, hbox]
          rw [polarCoord_target, Set.mem_prod] at hp
          obtain ⟨hp1, hp2⟩ := hp
          simp only [Set.mem_Ioi] at hp1
          by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R₀
          · rw [Set.indicator_of_mem hmem]
            have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
              rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
            have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
              rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
            rw [enorm_inv hsymm_ne]
            have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
              rw [← ofReal_norm_eq_enorm, hnorm]
            rw [henorm, smul_eq_mul,
              ENNReal.mul_inv_cancel
                (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
                ENNReal.ofReal_lt_top.ne]
            have hpR : p.1 ≤ R₀ := by
              rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
            rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩)]
          · rw [Set.indicator_of_notMem hmem]; simp
        calc
          ∫⁻ p in polarCoord.target, lhs p
              ≤ ∫⁻ p in polarCoord.target, box p :=
                setLIntegral_mono (measurable_const.indicator
                  (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
          _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
          _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-π) π) := by
                rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]; simp
          _ < ⊤ := by
                rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
                exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hCT : cauchyTransform ν
          = fun w => (-(1 / (π : ℂ))) • (MeasureTheory.convolution ν k L volume) w := by
        funext w
        rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
        congr 1
        apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
        rw [hL, ContinuousLinearMap.mul_apply']
        change ν ζ / (ζ - w) = ν ζ * -(w - ζ)⁻¹
        have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
        rw [hflip, div_eq_mul_inv]
      rw [hCT]
      exact (hνc.contDiff_convolution_left L hν hk_loc).const_smul _
    -- B = dz F
    have hBeqF : beurling ν = fun z => dz (cauchyTransform ν) z := by
      funext z; exact (beurling_eq_dz_cauchyTransform hν1 hνc z).symm
    rw [hBeqF]
    -- dz F is C^1
    apply ContDiff.of_le _ (by exact_mod_cast le_top : (1:WithTop ℕ∞) ≤ (⊤:ℕ∞))
    have hfd : ContDiff ℝ (⊤:ℕ∞) (fun w => fderiv ℝ (cauchyTransform ν) w) :=
      hF.fderiv_right (by simp)
    have h1 : ContDiff ℝ (⊤:ℕ∞) (fun w => (fderiv ℝ (cauchyTransform ν) w) (1:ℂ)) :=
      hfd.clm_apply contDiff_const
    have hI : ContDiff ℝ (⊤:ℕ∞) (fun w => (fderiv ℝ (cauchyTransform ν) w) Complex.I) :=
      hfd.clm_apply contDiff_const
    have heq : (fun z => dz (cauchyTransform ν) z)
        = fun z => (1/2:ℂ) * ((fderiv ℝ (cauchyTransform ν) z) 1
          - Complex.I * (fderiv ℝ (cauchyTransform ν) z) Complex.I) := by
      funext z; rw [dz]
    rw [heq]
    exact (contDiff_const.mul (h1.sub (contDiff_const.mul hI)))
  have hNL2 : MemLp ν 2 volume := hν1.continuous.memLp_of_hasCompactSupport hνc
  have hderivMemLp : ∀ (f : ℂ → ℂ), ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ m : ℂ, MemLp (fun z => (fderiv ℝ f z) m) 2 volume := by
    intro f hf hfc m
    have hcont : Continuous (fun z => (fderiv ℝ f z) m) :=
      (hf.continuous_fderiv (n := 1) one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (fun z => (fderiv ℝ f z) m) := by
      have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ f ζ) := hfc.fderiv (𝕜 := ℝ)
      have heq : (fun z => (fderiv ℝ f z) m)
          = (fun D : ℂ →L[ℝ] ℂ => D m) ∘ (fun ζ => fderiv ℝ f ζ) := rfl
      rw [heq]; exact hfderiv_cs.comp_left (by simp)
    exact hcont.memLp_of_hasCompactSupport hcs
  have hN1L2 : MemLp (fun z => (fderiv ℝ ν z) 1) 2 volume := hderivMemLp ν hν1 hνc 1
  have hNIL2 : MemLp (fun z => (fderiv ℝ ν z) Complex.I) 2 volume :=
    hderivMemLp ν hν1 hνc Complex.I
  have hBL2 : MemLp B 2 volume := by
    rw [hBdef]
    -- nonneg radius
    set R' : ℝ := max R 0 with hR'def
    have hR'nn : 0 ≤ R' := le_max_right _ _
    have hR' : tsupport ν ⊆ Metric.closedBall (0 : ℂ) R' :=
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    -- M = sup ‖ν‖
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖ν ζ‖ ≤ M := hνc.exists_bound_of_continuous hν1.continuous
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    -- integral representation for ‖z‖ > R' + 1
    have Hrepr : ∀ z : ℂ, R' + 1 < ‖z‖ →
        beurling ν z = -(1/(π:ℂ)) * ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
      intro z hz
      have hvanr : ∀ r : ℝ, r ≤ 1 → ∀ y ∈ Metric.ball z r, ν y = 0 := by
        intro r hr y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := hR' hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := norm_le_insert y z
        have h3 : ‖y - z‖ < 1 := lt_of_lt_of_le hy hr
        linarith
      have hcont : Continuous (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        rw [← continuousOn_univ]
        apply ContinuousOn.mono (s := {y | y ≠ z} ∪ Metric.ball z 1) _ (by
          intro y _; by_cases h : y = z
          · right; rw [h]; simp [Metric.mem_ball]
          · left; exact h)
        apply ContinuousOn.union_of_isOpen _ _ isOpen_ne Metric.isOpen_ball
        · apply ContinuousOn.mul _ hν1.continuous.continuousOn
          apply ContinuousOn.zpow₀ (by fun_prop)
          intro y hy; left; rw [sub_ne_zero]; exact fun h => hy h.symm
        · have hg : ContinuousOn (fun _ : ℂ => (0:ℂ)) (Metric.ball z 1) := continuousOn_const
          refine hg.congr ?_
          intro y hy
          change (z - y) ^ (-2:ℤ) * ν y = 0
          rw [hvanr 1 le_rfl y hy, mul_zero]
      have hcs : HasCompactSupport (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        have heq : (fun y => (z - y) ^ (-2:ℤ) * ν y) = (fun y => (z - y) ^ (-2:ℤ)) * ν := rfl
        rw [heq]; exact hνc.mul_left
      have hint : Integrable (fun y => (z - y) ^ (-2:ℤ) * ν y) volume :=
        hcont.integrable_of_hasCompactSupport hcs
      have hcz : ∀ r : ℝ, r ≤ 1 →
          czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z = ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
        intro r hr
        rw [czOperator]
        have hfull : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
            = (∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y)
              + ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * ν y := by
          rw [← setIntegral_univ (μ := volume), ← Set.union_compl_self (Metric.ball z r),
            setIntegral_union disjoint_compl_right measurableSet_ball.compl
              hint.integrableOn hint.integrableOn]
        have hzero : ∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y = 0 := by
          rw [setIntegral_eq_zero_of_forall_eq_zero]
          intro y hy; rw [hvanr r hr y hy, mul_zero]
        rw [hfull, hzero, zero_add]
      rw [beurling]
      congr 1
      apply Filter.Tendsto.limUnder_eq
      have hev : (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => ∫ y, (z - y) ^ (-2 : ℤ) * ν y) := by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with r hr
        exact hcz r (le_of_lt hr.2)
      exact Tendsto.congr' hev.symm tendsto_const_nhds
    -- decay bound: ‖B z‖ ≤ Cb / ‖z‖² for ‖z‖ > 2R'+2
    set Cb : ℝ := M * (volume (Metric.closedBall (0:ℂ) R')).toReal / π * 4 with hCb
    have hCbnn : 0 ≤ Cb := by
      rw [hCb]; positivity
    have hdecay : ∀ z : ℂ, (2*R'+2) < ‖z‖ → ‖beurling ν z‖ ≤ Cb / ‖z‖^2 := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hhalf : ‖z‖ / 2 ≤ ‖z‖ - R' := by linarith
      have hsupp : ∀ y ∉ Metric.closedBall (0:ℂ) R', (z - y) ^ (-2:ℤ) * ν y = 0 := by
        intro y hy; rw [image_eq_zero_of_notMem_tsupport (fun hmem => hy (hR' hmem)), mul_zero]
      have hinteq : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
          = ∫ y in Metric.closedBall (0:ℂ) R', (z - y) ^ (-2 : ℤ) * ν y :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
      set Cval : ℝ := M * (‖z‖/2)⁻¹^2 with hCval
      have hbd : ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖(z - y) ^ (-2:ℤ) * ν y‖ ≤ Cval := by
        intro y hy
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        rw [norm_mul]
        have hzy : ‖z‖ / 2 ≤ ‖z - y‖ := by
          have : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
          linarith
        have hzhalfpos : (0:ℝ) < ‖z‖/2 := by positivity
        have hkn : ‖(z - y) ^ (-2:ℤ)‖ = ‖z - y‖⁻¹^2 := by
          rw [norm_zpow, zpow_neg, zpow_two, mul_inv, ← pow_two]
        rw [hkn, hCval]
        have h1 : ‖z - y‖⁻¹^2 ≤ (‖z‖/2)⁻¹^2 := by gcongr
        calc ‖z - y‖⁻¹^2 * ‖ν y‖
            ≤ (‖z‖/2)⁻¹^2 * M := mul_le_mul h1 (hM y) (norm_nonneg _) (by positivity)
          _ = M * (‖z‖/2)⁻¹^2 := by ring
      rw [Hrepr z (by linarith), norm_mul, hinteq]
      have hballfin : volume (Metric.closedBall (0:ℂ) R') < ⊤ := by
        rw [Complex.volume_closedBall]; finiteness
      have hib := norm_setIntegral_le_of_norm_le_const hballfin hbd
      have hnormconst : ‖-(1/(π:ℂ))‖ = 1/π := by
        rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hnormconst]
      have hπpos : 0 < π := Real.pi_pos
      have hvolnn : 0 ≤ (volume (Metric.closedBall (0:ℂ) R')).toReal := ENNReal.toReal_nonneg
      calc (1/π) * ‖∫ y in Metric.closedBall (0:ℂ) R', (z - y) ^ (-2 : ℤ) * ν y‖
          ≤ (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal) :=
            mul_le_mul_of_nonneg_left hib (by positivity)
        _ ≤ Cb / ‖z‖^2 := by
            rw [hCval, hCb]
            have he : (‖z‖/2)⁻¹^2 = 4 / ‖z‖^2 := by rw [inv_div, div_pow]; norm_num
            rw [he]
            have hzne : ‖z‖ ≠ 0 := ne_of_gt hzpos
            have hπne : π ≠ 0 := ne_of_gt hπpos
            apply le_of_eq
            field_simp
    -- apply MemLp decay helper
    have hcont : Continuous (beurling ν) := hB.continuous
    have haesm : AEStronglyMeasurable (beurling ν) volume := hcont.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm haesm]
    set R'' : ℝ := 2*R'+2 with hR''def
    have hR''pos : 0 < R'' := by rw [hR''def]; positivity
    have hball : IntegrableOn (fun z => ‖beurling ν z‖^2) (Metric.closedBall (0:ℂ) R'') volume :=
      (hcont.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R'')
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (Cb / p.1^2)^2)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      apply Measurable.pow_const
      exact measurable_const.div (measurable_fst.pow_const 2)
    have hcompl : IntegrableOn (fun z => ‖beurling ν z‖^2)
        (Metric.closedBall (0:ℂ) R'')ᶜ volume := by
      refine ⟨((hcont.norm.pow 2).aestronglyMeasurable).restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hpt : ∀ z ∈ (Metric.closedBall (0:ℂ) R'')ᶜ,
          ‖(‖beurling ν z‖^2 : ℝ)‖ₑ ≤ ENNReal.ofReal ((Cb / ‖z‖^2)^2) := by
        intro z hz
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := hdecay z hz
        have hnn : 0 ≤ ‖beurling ν z‖ := norm_nonneg _
        nlinarith [hb, hnn]
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall.compl hpt) ?_
      rw [← lintegral_indicator measurableSet_closedBall.compl]
      rw [← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ioi R'' ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * (Cb / p.1^2)^2)) p with hbox
      have hbound : ∀ p ∈ polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
            (fun z => ENNReal.ofReal ((Cb / ‖z‖^2)^2)) (Complex.polarCoord.symm p) ≤ box p := by
        intro p hp
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        by_cases hmem : Complex.polarCoord.symm p ∈ (Metric.closedBall (0:ℂ) R'')ᶜ
        · rw [Set.indicator_of_mem hmem]
          have hpR : R'' < p.1 := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hnorm, not_le] at hmem
            exact hmem
          rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hpR, hp2⟩)]
          rw [hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]
          exact zero_le _
      have hboxmeas : Measurable box :=
        hmeas_polar.indicator (measurableSet_Ioi.prod measurableSet_Ioo)
      calc
        ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
              (fun z => ENNReal.ofReal ((Cb / ‖z‖^2)^2)) (Complex.polarCoord.symm p)
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hboxmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = ∫⁻ p in (Set.Ioi R'' ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (p.1 * (Cb / p.1^2)^2) := by
              rw [hbox, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ]
              rw [setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint : IntegrableOn (fun r : ℝ => r * (Cb / r^2)^2) (Set.Ioi R'') volume := by
                have heq : (fun r : ℝ => r * (Cb / r^2)^2) =ᶠ[ae (volume.restrict (Set.Ioi R''))]
                    (fun r : ℝ => Cb^2 * r^(-3 : ℝ)) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
                  simp only [Set.mem_Ioi] at hr
                  have hrpos : 0 < r := lt_trans hR''pos hr
                  have hrne : r ≠ 0 := ne_of_gt hrpos
                  rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
                  field_simp
                rw [integrableOn_congr_fun_ae heq]
                apply Integrable.const_mul
                rw [← IntegrableOn, integrableOn_Ioi_rpow_iff hR''pos]
                norm_num
              have hfin := hint.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
              · apply Measurable.enorm
                apply Measurable.mul measurable_id
                apply Measurable.pow_const
                exact measurable_const.div (measurable_id.pow_const 2)
              · simp only [Set.mem_Ioi] at hx
                have hxpos : 0 < x := lt_trans hR''pos hx
                rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hball.union hcompl
    rw [Set.union_compl_self, integrableOn_univ] at this
    exact this
  have hB1L2 : MemLp (fun z => (fderiv ℝ B z) 1) 2 volume := by
    rw [hBdef]
    suffices h : ∀ m : ℂ, MemLp (fun z => (fderiv ℝ (beurling ν) z) m) 2 volume from h 1
    intro m
    set R' : ℝ := max R 0 with hR'def
    have hR'nn : 0 ≤ R' := le_max_right _ _
    have hR' : tsupport ν ⊆ Metric.closedBall (0 : ℂ) R' :=
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖ν ζ‖ ≤ M := hνc.exists_bound_of_continuous hν1.continuous
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    -- representation (as in hBL2)
    have Hrepr : ∀ z : ℂ, R' + 1 < ‖z‖ →
        beurling ν z = -(1/(π:ℂ)) * ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
      intro z hz
      have hvanr : ∀ r : ℝ, r ≤ 1 → ∀ y ∈ Metric.ball z r, ν y = 0 := by
        intro r hr y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := hR' hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := norm_le_insert y z
        have h3 : ‖y - z‖ < 1 := lt_of_lt_of_le hy hr
        linarith
      have hcont : Continuous (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        rw [← continuousOn_univ]
        apply ContinuousOn.mono (s := {y | y ≠ z} ∪ Metric.ball z 1) _ (by
          intro y _; by_cases h : y = z
          · right; rw [h]; simp [Metric.mem_ball]
          · left; exact h)
        apply ContinuousOn.union_of_isOpen _ _ isOpen_ne Metric.isOpen_ball
        · apply ContinuousOn.mul _ hν1.continuous.continuousOn
          apply ContinuousOn.zpow₀ (by fun_prop)
          intro y hy; left; rw [sub_ne_zero]; exact fun h => hy h.symm
        · have hg : ContinuousOn (fun _ : ℂ => (0:ℂ)) (Metric.ball z 1) := continuousOn_const
          refine hg.congr ?_
          intro y hy
          change (z - y) ^ (-2:ℤ) * ν y = 0
          rw [hvanr 1 le_rfl y hy, mul_zero]
      have hcs : HasCompactSupport (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        have heq : (fun y => (z - y) ^ (-2:ℤ) * ν y) = (fun y => (z - y) ^ (-2:ℤ)) * ν := rfl
        rw [heq]; exact hνc.mul_left
      have hint : Integrable (fun y => (z - y) ^ (-2:ℤ) * ν y) volume :=
        hcont.integrable_of_hasCompactSupport hcs
      have hcz : ∀ r : ℝ, r ≤ 1 →
          czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z = ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
        intro r hr
        rw [czOperator]
        have hfull : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
            = (∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y)
              + ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * ν y := by
          rw [← setIntegral_univ (μ := volume), ← Set.union_compl_self (Metric.ball z r),
            setIntegral_union disjoint_compl_right measurableSet_ball.compl
              hint.integrableOn hint.integrableOn]
        have hzero : ∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y = 0 := by
          rw [setIntegral_eq_zero_of_forall_eq_zero]
          intro y hy; rw [hvanr r hr y hy, mul_zero]
        rw [hfull, hzero, zero_add]
      rw [beurling]
      congr 1
      apply Filter.Tendsto.limUnder_eq
      have hev : (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => ∫ y, (z - y) ^ (-2 : ℤ) * ν y) := by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with r hr
        exact hcz r (le_of_lt hr.2)
      exact Tendsto.congr' hev.symm tendsto_const_nhds
    -- DUI: HasFDerivAt of parametric integral over ball
    have hG : ∀ w : ℂ, 2 * R' + 3 < ‖w‖ → HasFDerivAt
        (fun u => ∫ y in Metric.closedBall (0:ℂ) R', (u - y) ^ (-2 : ℤ) * ν y)
        (∫ y in Metric.closedBall (0:ℂ) R',
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ))) w := by
      intro z hz
      set Fp' : ℂ → ℂ → (ℂ →L[ℝ] ℂ) := fun w y =>
        (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      set s : Set ℂ := Metric.ball z 1 with hs_def
      set bnd : ℝ := 2 * (‖z‖ - R' - 1)⁻¹^3 * M with hbnd
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hbdpos : 0 < ‖z‖ - R' - 1 := by linarith
      have hgeo : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖z‖ - R' - 1 ≤ ‖w - y‖ := by
        intro w hw y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have h1 : ‖w - y‖ ≥ ‖z - y‖ - ‖z - w‖ := by
          have := norm_sub_norm_le (z - y) (z - w)
          have heq : (z - y) - (z - w) = w - y := by ring
          rw [heq] at this; linarith
        have h2 : ‖z - y‖ ≥ ‖z‖ - ‖y‖ := norm_sub_norm_le z y
        have h3 : ‖z - w‖ < 1 := by rw [norm_sub_rev]; exact hw
        linarith
      have hne : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', w ≠ y := by
        intro w hw y hy h
        have := hgeo w hw y hy; rw [h, sub_self, norm_zero] at this; linarith
      have hcontFp : ∀ w ∈ s, ContinuousOn (fun y => (w - y)^(-2:ℤ) * ν y)
          (Metric.closedBall (0:ℂ) R') := by
        intro w hw
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne w hw y hy
      have hFp'_cont : ContinuousOn (fun y => Fp' z y) (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne z (Metric.mem_ball_self (by norm_num)) y hy
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => bnd)
        (F' := Fp') (s := s) (Metric.ball_mem_nhds z (by norm_num))
      · filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1)] with w hw
        exact (hcontFp w hw).aestronglyMeasurable measurableSet_closedBall
      · exact (hcontFp z (Metric.mem_ball_self (by norm_num))).integrableOn_compact
          (isCompact_closedBall 0 R')
      · exact hFp'_cont.aestronglyMeasurable measurableSet_closedBall
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        rw [hFp', hbnd]
        rw [norm_smul]
        have h1norm : ‖(1 : ℂ →L[ℝ] ℂ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have hwy : ‖z‖ - R' - 1 ≤ ‖w - y‖ := hgeo w hw y hy
        have hwypos : 0 < ‖w - y‖ := lt_of_lt_of_le hbdpos hwy
        have hknorm : ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖
            ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by
          rw [norm_mul, norm_mul]
          have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
          have hk2 : ‖(w - y) ^ ((-2:ℤ) - 1)‖ = ‖w - y‖⁻¹^3 := by
            rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
              show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
          rw [hk1, hk2]
          have hmono : ‖w - y‖⁻¹^3 ≤ (‖z‖ - R' - 1)⁻¹^3 := by gcongr
          have h2 : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 := by positivity
          exact mul_le_mul (by apply mul_le_mul_of_nonneg_left hmono (by norm_num)) (hM y)
            (norm_nonneg _) h2
        have hbndnn : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by positivity
        calc ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖
            ≤ (2 * (‖z‖ - R' - 1)⁻¹^3 * M) * 1 :=
              mul_le_mul hknorm h1norm (norm_nonneg _) hbndnn
          _ = 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by ring
      · exact integrableOn_const (by rw [Complex.volume_closedBall]; finiteness) (by finiteness)
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y) (Fp' w y) w
        have hsub : HasFDerivAt (fun u : ℂ => u - y) (1 : ℂ →L[ℝ] ℂ) w := by
          simpa using (hasFDerivAt_id w).sub_const y
        have hzpw : HasFDerivAt (fun u : ℂ => (u - y) ^ (-2:ℤ))
            ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) w := by
          have hc := (hasDerivAt_zpow (-2 : ℤ) (w - y)
            (Or.inl (sub_ne_zero.mpr (hne w hw y hy)))).comp_hasFDerivAt w hsub
          exact hc
        have hmul := hzpw.mul_const (ν y)
        rw [hFp']
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y)
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)) w
        have heq : (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)
            = (ν y) • ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) := by
          rw [smul_smul]; ring_nf
        rw [heq]; exact hmul
    -- derivative decay bound: ‖fderiv B z m‖ ≤ Cd / ‖z‖²  for ‖z‖ > 2R'+4
    set Cd : ℝ := 16 * (volume (Metric.closedBall (0:ℂ) R')).toReal * M * ‖m‖ / π with hCd
    have hCdnn : 0 ≤ Cd := by rw [hCd]; positivity
    have hdecay : ∀ z : ℂ, (2*R'+4) < ‖z‖ → ‖(fderiv ℝ (beurling ν) z) m‖ ≤ Cd / ‖z‖^2 := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hsuppeq : ∀ w : ℂ, R' + 1 < ‖w‖ →
          (∫ y, (w - y) ^ (-2 : ℤ) * ν y)
            = ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        intro w hw
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro y hy; rw [image_eq_zero_of_notMem_tsupport (fun hmem => hy (hR' hmem)), mul_zero]
      have hBeq : (beurling ν) =ᶠ[nhds z]
          fun w => -(1/(π:ℂ)) * ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        have hopen : {w : ℂ | 2 * R' + 4 < ‖w‖} ∈ nhds z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hz
        filter_upwards [hopen] with w hw
        rw [Hrepr w (by linarith), hsuppeq w (by linarith)]
      have hGz := hG z (by linarith)
      have hBfd : HasFDerivAt (beurling ν)
          ((-(1/(π:ℂ))) • (∫ y in Metric.closedBall (0:ℂ) R',
              ((((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)))) z := by
        apply HasFDerivAt.congr_of_eventuallyEq _ hBeq
        exact hGz.const_smul (-(1/(π:ℂ)))
      rw [hBfd.fderiv]
      have hbdpos : 0 < ‖z‖ - R' := by linarith [hz]
      have hne : ∀ y ∈ Metric.closedBall (0:ℂ) R', z ≠ y := by
        intro y hy h
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        rw [h] at hz; linarith
      set Fp' : ℂ → (ℂ →L[ℝ] ℂ) := fun y =>
        (((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      have hFp'_cont : ContinuousOn Fp' (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne y hy
      have hFp'_int : IntegrableOn Fp' (Metric.closedBall (0:ℂ) R') volume :=
        hFp'_cont.integrableOn_compact (isCompact_closedBall 0 R')
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply hFp'_int]
      rw [norm_smul]
      have hnormconst : ‖-(1/(π:ℂ))‖ = 1/π := by
        rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hnormconst]
      have hπpos : 0 < π := Real.pi_pos
      set Cval : ℝ := 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ with hCval
      have hbd : ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖(Fp' y) m‖ ≤ Cval := by
        intro y hy
        rw [hFp', ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have hzy : ‖z‖ - R' ≤ ‖z - y‖ := by
          have : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
          linarith
        have hzypos : 0 < ‖z - y‖ := lt_of_lt_of_le hbdpos hzy
        rw [norm_mul, norm_mul, norm_mul]
        have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
        have hk2 : ‖(z - y) ^ ((-2:ℤ) - 1)‖ = ‖z - y‖⁻¹^3 := by
          rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
            show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
        rw [hk1, hk2, hCval]
        have hmono : ‖z - y‖⁻¹^3 ≤ (‖z‖ - R')⁻¹^3 := by gcongr
        have hstep : 2 * ‖z - y‖⁻¹^3 * ‖ν y‖ * ‖m‖ ≤ 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ := by
          apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
          apply mul_le_mul _ (hM y) (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left hmono (by norm_num)
        exact hstep
      have hballfin : volume (Metric.closedBall (0:ℂ) R') < ⊤ := by
        rw [Complex.volume_closedBall]; finiteness
      have hib := norm_setIntegral_le_of_norm_le_const hballfin hbd
      have hvolnn : 0 ≤ (volume (Metric.closedBall (0:ℂ) R')).toReal := ENNReal.toReal_nonneg
      have hCvalbd : Cval ≤ 16 * M * ‖m‖ / ‖z‖^2 := by
        rw [hCval]
        have he : (‖z‖ - R')⁻¹^3 ≤ (‖z‖/2)⁻¹^3 := by
          apply pow_le_pow_left₀ (inv_nonneg.mpr hbdpos.le)
          apply inv_anti₀ (by positivity)
          linarith [hz]
        have he2 : (‖z‖/2)⁻¹^3 ≤ 8 / ‖z‖^2 := by
          rw [inv_div, div_pow]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (1:ℝ) ≤ ‖z‖ := by linarith [hz]
          nlinarith [pow_pos hzpos 2, sq_nonneg ‖z‖, hzpos.le]
        calc 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖
            ≤ 2 * (8 / ‖z‖^2) * M * ‖m‖ := by
              apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
              apply mul_le_mul _ le_rfl hMnn (by positivity)
              apply mul_le_mul_of_nonneg_left (le_trans he he2) (by norm_num)
          _ = 16 * M * ‖m‖ / ‖z‖^2 := by ring
      calc (1/π) * ‖∫ y in Metric.closedBall (0:ℂ) R', (Fp' y) m‖
          ≤ (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [Measure.real] at hib; exact hib
        _ ≤ Cd / ‖z‖^2 := by
            rw [hCd]
            have hstep : (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal)
                ≤ (1/π) * ((16 * M * ‖m‖ / ‖z‖^2)
                  * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul_of_nonneg_right hCvalbd hvolnn
            refine le_trans hstep (le_of_eq ?_)
            field_simp
    -- now MemLp via decay helper
    have hcont : Continuous (fun z => (fderiv ℝ (beurling ν) z) m) :=
      (hB.continuous_fderiv (n := 1) one_ne_zero).clm_apply continuous_const
    have haesm : AEStronglyMeasurable (fun z => (fderiv ℝ (beurling ν) z) m) volume :=
      hcont.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm haesm]
    set R'' : ℝ := 2*R'+4 with hR''def
    have hR''pos : 0 < R'' := by rw [hR''def]; positivity
    have hball : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'') volume :=
      (hcont.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R'')
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      apply Measurable.pow_const
      exact measurable_const.div (measurable_fst.pow_const 2)
    have hcompl : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'')ᶜ volume := by
      refine ⟨((hcont.norm.pow 2).aestronglyMeasurable).restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hpt : ∀ z ∈ (Metric.closedBall (0:ℂ) R'')ᶜ,
          ‖(‖(fderiv ℝ (beurling ν) z) m‖^2 : ℝ)‖ₑ ≤ ENNReal.ofReal ((Cd / ‖z‖^2)^2) := by
        intro z hz
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := hdecay z hz
        have hnn : 0 ≤ ‖(fderiv ℝ (beurling ν) z) m‖ := norm_nonneg _
        nlinarith [hb, hnn]
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall.compl hpt) ?_
      rw [← lintegral_indicator measurableSet_closedBall.compl]
      rw [← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ioi R'' ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) p with hbox
      have hbound : ∀ p ∈ polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
            (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p) ≤ box p := by
        intro p hp
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        by_cases hmem : Complex.polarCoord.symm p ∈ (Metric.closedBall (0:ℂ) R'')ᶜ
        · rw [Set.indicator_of_mem hmem]
          have hpR : R'' < p.1 := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hnorm, not_le] at hmem
            exact hmem
          rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hpR, hp2⟩)]
          rw [hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]
          exact zero_le _
      have hboxmeas : Measurable box :=
        hmeas_polar.indicator (measurableSet_Ioi.prod measurableSet_Ioo)
      calc
        ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
              (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p)
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hboxmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = ∫⁻ p in (Set.Ioi R'' ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (p.1 * (Cd / p.1^2)^2) := by
              rw [hbox, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ]
              rw [setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint : IntegrableOn (fun r : ℝ => r * (Cd / r^2)^2) (Set.Ioi R'') volume := by
                have heq : (fun r : ℝ => r * (Cd / r^2)^2) =ᶠ[ae (volume.restrict (Set.Ioi R''))]
                    (fun r : ℝ => Cd^2 * r^(-3 : ℝ)) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
                  simp only [Set.mem_Ioi] at hr
                  have hrpos : 0 < r := lt_trans hR''pos hr
                  have hrne : r ≠ 0 := ne_of_gt hrpos
                  rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
                  field_simp
                rw [integrableOn_congr_fun_ae heq]
                apply Integrable.const_mul
                rw [← IntegrableOn, integrableOn_Ioi_rpow_iff hR''pos]
                norm_num
              have hfin := hint.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
              · apply Measurable.enorm
                apply Measurable.mul measurable_id
                apply Measurable.pow_const
                exact measurable_const.div (measurable_id.pow_const 2)
              · simp only [Set.mem_Ioi] at hx
                have hxpos : 0 < x := lt_trans hR''pos hx
                rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hball.union hcompl
    rw [Set.union_compl_self, integrableOn_univ] at this
    exact this
  have hBIL2 : MemLp (fun z => (fderiv ℝ B z) Complex.I) 2 volume := by
    rw [hBdef]
    suffices h : ∀ m : ℂ, MemLp (fun z => (fderiv ℝ (beurling ν) z) m) 2 volume from h Complex.I
    intro m
    set R' : ℝ := max R 0 with hR'def
    have hR'nn : 0 ≤ R' := le_max_right _ _
    have hR' : tsupport ν ⊆ Metric.closedBall (0 : ℂ) R' :=
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ, ‖ν ζ‖ ≤ M := hνc.exists_bound_of_continuous hν1.continuous
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    -- representation (as in hBL2)
    have Hrepr : ∀ z : ℂ, R' + 1 < ‖z‖ →
        beurling ν z = -(1/(π:ℂ)) * ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
      intro z hz
      have hvanr : ∀ r : ℝ, r ≤ 1 → ∀ y ∈ Metric.ball z r, ν y = 0 := by
        intro r hr y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := hR' hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := norm_le_insert y z
        have h3 : ‖y - z‖ < 1 := lt_of_lt_of_le hy hr
        linarith
      have hcont : Continuous (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        rw [← continuousOn_univ]
        apply ContinuousOn.mono (s := {y | y ≠ z} ∪ Metric.ball z 1) _ (by
          intro y _; by_cases h : y = z
          · right; rw [h]; simp [Metric.mem_ball]
          · left; exact h)
        apply ContinuousOn.union_of_isOpen _ _ isOpen_ne Metric.isOpen_ball
        · apply ContinuousOn.mul _ hν1.continuous.continuousOn
          apply ContinuousOn.zpow₀ (by fun_prop)
          intro y hy; left; rw [sub_ne_zero]; exact fun h => hy h.symm
        · have hg : ContinuousOn (fun _ : ℂ => (0:ℂ)) (Metric.ball z 1) := continuousOn_const
          refine hg.congr ?_
          intro y hy
          change (z - y) ^ (-2:ℤ) * ν y = 0
          rw [hvanr 1 le_rfl y hy, mul_zero]
      have hcs : HasCompactSupport (fun y => (z - y) ^ (-2:ℤ) * ν y) := by
        have heq : (fun y => (z - y) ^ (-2:ℤ) * ν y) = (fun y => (z - y) ^ (-2:ℤ)) * ν := rfl
        rw [heq]; exact hνc.mul_left
      have hint : Integrable (fun y => (z - y) ^ (-2:ℤ) * ν y) volume :=
        hcont.integrable_of_hasCompactSupport hcs
      have hcz : ∀ r : ℝ, r ≤ 1 →
          czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z = ∫ y, (z - y) ^ (-2 : ℤ) * ν y := by
        intro r hr
        rw [czOperator]
        have hfull : (∫ y, (z - y) ^ (-2 : ℤ) * ν y)
            = (∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y)
              + ∫ y in (Metric.ball z r)ᶜ, (z - y) ^ (-2 : ℤ) * ν y := by
          rw [← setIntegral_univ (μ := volume), ← Set.union_compl_self (Metric.ball z r),
            setIntegral_union disjoint_compl_right measurableSet_ball.compl
              hint.integrableOn hint.integrableOn]
        have hzero : ∫ y in Metric.ball z r, (z - y) ^ (-2 : ℤ) * ν y = 0 := by
          rw [setIntegral_eq_zero_of_forall_eq_zero]
          intro y hy; rw [hvanr r hr y hy, mul_zero]
        rw [hfull, hzero, zero_add]
      rw [beurling]
      congr 1
      apply Filter.Tendsto.limUnder_eq
      have hev : (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν z)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => ∫ y, (z - y) ^ (-2 : ℤ) * ν y) := by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with r hr
        exact hcz r (le_of_lt hr.2)
      exact Tendsto.congr' hev.symm tendsto_const_nhds
    -- DUI: HasFDerivAt of parametric integral over ball
    have hG : ∀ w : ℂ, 2 * R' + 3 < ‖w‖ → HasFDerivAt
        (fun u => ∫ y in Metric.closedBall (0:ℂ) R', (u - y) ^ (-2 : ℤ) * ν y)
        (∫ y in Metric.closedBall (0:ℂ) R',
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ))) w := by
      intro z hz
      set Fp' : ℂ → ℂ → (ℂ →L[ℝ] ℂ) := fun w y =>
        (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      set s : Set ℂ := Metric.ball z 1 with hs_def
      set bnd : ℝ := 2 * (‖z‖ - R' - 1)⁻¹^3 * M with hbnd
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hbdpos : 0 < ‖z‖ - R' - 1 := by linarith
      have hgeo : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖z‖ - R' - 1 ≤ ‖w - y‖ := by
        intro w hw y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have h1 : ‖w - y‖ ≥ ‖z - y‖ - ‖z - w‖ := by
          have := norm_sub_norm_le (z - y) (z - w)
          have heq : (z - y) - (z - w) = w - y := by ring
          rw [heq] at this; linarith
        have h2 : ‖z - y‖ ≥ ‖z‖ - ‖y‖ := norm_sub_norm_le z y
        have h3 : ‖z - w‖ < 1 := by rw [norm_sub_rev]; exact hw
        linarith
      have hne : ∀ w ∈ s, ∀ y ∈ Metric.closedBall (0:ℂ) R', w ≠ y := by
        intro w hw y hy h
        have := hgeo w hw y hy; rw [h, sub_self, norm_zero] at this; linarith
      have hcontFp : ∀ w ∈ s, ContinuousOn (fun y => (w - y)^(-2:ℤ) * ν y)
          (Metric.closedBall (0:ℂ) R') := by
        intro w hw
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne w hw y hy
      have hFp'_cont : ContinuousOn (fun y => Fp' z y) (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne z (Metric.mem_ball_self (by norm_num)) y hy
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => bnd)
        (F' := Fp') (s := s) (Metric.ball_mem_nhds z (by norm_num))
      · filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1)] with w hw
        exact (hcontFp w hw).aestronglyMeasurable measurableSet_closedBall
      · exact (hcontFp z (Metric.mem_ball_self (by norm_num))).integrableOn_compact
          (isCompact_closedBall 0 R')
      · exact hFp'_cont.aestronglyMeasurable measurableSet_closedBall
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        rw [hFp', hbnd]
        rw [norm_smul]
        have h1norm : ‖(1 : ℂ →L[ℝ] ℂ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have hwy : ‖z‖ - R' - 1 ≤ ‖w - y‖ := hgeo w hw y hy
        have hwypos : 0 < ‖w - y‖ := lt_of_lt_of_le hbdpos hwy
        have hknorm : ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖
            ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by
          rw [norm_mul, norm_mul]
          have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
          have hk2 : ‖(w - y) ^ ((-2:ℤ) - 1)‖ = ‖w - y‖⁻¹^3 := by
            rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
              show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
          rw [hk1, hk2]
          have hmono : ‖w - y‖⁻¹^3 ≤ (‖z‖ - R' - 1)⁻¹^3 := by gcongr
          have h2 : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 := by positivity
          exact mul_le_mul (by apply mul_le_mul_of_nonneg_left hmono (by norm_num)) (hM y)
            (norm_nonneg _) h2
        have hbndnn : (0:ℝ) ≤ 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by positivity
        calc ‖((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖
            ≤ (2 * (‖z‖ - R' - 1)⁻¹^3 * M) * 1 :=
              mul_le_mul hknorm h1norm (norm_nonneg _) hbndnn
          _ = 2 * (‖z‖ - R' - 1)⁻¹^3 * M := by ring
      · exact integrableOn_const (by rw [Complex.volume_closedBall]; finiteness) (by finiteness)
      · rw [ae_restrict_iff' measurableSet_closedBall]
        apply ae_of_all
        intro y hy w hw
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y) (Fp' w y) w
        have hsub : HasFDerivAt (fun u : ℂ => u - y) (1 : ℂ →L[ℝ] ℂ) w := by
          simpa using (hasFDerivAt_id w).sub_const y
        have hzpw : HasFDerivAt (fun u : ℂ => (u - y) ^ (-2:ℤ))
            ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) w := by
          have hc := (hasDerivAt_zpow (-2 : ℤ) (w - y)
            (Or.inl (sub_ne_zero.mpr (hne w hw y hy)))).comp_hasFDerivAt w hsub
          exact hc
        have hmul := hzpw.mul_const (ν y)
        rw [hFp']
        change HasFDerivAt (fun u => (u - y) ^ (-2:ℤ) * ν y)
          ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)) w
        have heq : (((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)
            = (ν y) • ((((-2 : ℤ):ℂ) * (w - y) ^ ((-2:ℤ) - 1)) • (1 : ℂ →L[ℝ] ℂ)) := by
          rw [smul_smul]; ring_nf
        rw [heq]; exact hmul
    -- derivative decay bound: ‖fderiv B z m‖ ≤ Cd / ‖z‖²  for ‖z‖ > 2R'+4
    set Cd : ℝ := 16 * (volume (Metric.closedBall (0:ℂ) R')).toReal * M * ‖m‖ / π with hCd
    have hCdnn : 0 ≤ Cd := by rw [hCd]; positivity
    have hdecay : ∀ z : ℂ, (2*R'+4) < ‖z‖ → ‖(fderiv ℝ (beurling ν) z) m‖ ≤ Cd / ‖z‖^2 := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
      have hsuppeq : ∀ w : ℂ, R' + 1 < ‖w‖ →
          (∫ y, (w - y) ^ (-2 : ℤ) * ν y)
            = ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        intro w hw
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro y hy; rw [image_eq_zero_of_notMem_tsupport (fun hmem => hy (hR' hmem)), mul_zero]
      have hBeq : (beurling ν) =ᶠ[nhds z]
          fun w => -(1/(π:ℂ)) * ∫ y in Metric.closedBall (0:ℂ) R', (w - y) ^ (-2 : ℤ) * ν y := by
        have hopen : {w : ℂ | 2 * R' + 4 < ‖w‖} ∈ nhds z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hz
        filter_upwards [hopen] with w hw
        rw [Hrepr w (by linarith), hsuppeq w (by linarith)]
      have hGz := hG z (by linarith)
      have hBfd : HasFDerivAt (beurling ν)
          ((-(1/(π:ℂ))) • (∫ y in Metric.closedBall (0:ℂ) R',
              ((((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ)))) z := by
        apply HasFDerivAt.congr_of_eventuallyEq _ hBeq
        exact hGz.const_smul (-(1/(π:ℂ)))
      rw [hBfd.fderiv]
      have hbdpos : 0 < ‖z‖ - R' := by linarith [hz]
      have hne : ∀ y ∈ Metric.closedBall (0:ℂ) R', z ≠ y := by
        intro y hy h
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        rw [h] at hz; linarith
      set Fp' : ℂ → (ℂ →L[ℝ] ℂ) := fun y =>
        (((-2 : ℤ):ℂ) * (z - y) ^ ((-2:ℤ) - 1) * ν y) • (1 : ℂ →L[ℝ] ℂ) with hFp'
      have hFp'_cont : ContinuousOn Fp' (Metric.closedBall (0:ℂ) R') := by
        rw [hFp']
        apply ContinuousOn.smul _ continuousOn_const
        apply ContinuousOn.mul _ hν1.continuous.continuousOn
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.zpow₀ (by fun_prop)
        intro y hy; left; rw [sub_ne_zero]; exact hne y hy
      have hFp'_int : IntegrableOn Fp' (Metric.closedBall (0:ℂ) R') volume :=
        hFp'_cont.integrableOn_compact (isCompact_closedBall 0 R')
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply hFp'_int]
      rw [norm_smul]
      have hnormconst : ‖-(1/(π:ℂ))‖ = 1/π := by
        rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hnormconst]
      have hπpos : 0 < π := Real.pi_pos
      set Cval : ℝ := 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ with hCval
      have hbd : ∀ y ∈ Metric.closedBall (0:ℂ) R', ‖(Fp' y) m‖ ≤ Cval := by
        intro y hy
        rw [hFp', ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        have hzy : ‖z‖ - R' ≤ ‖z - y‖ := by
          have : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
          linarith
        have hzypos : 0 < ‖z - y‖ := lt_of_lt_of_le hbdpos hzy
        rw [norm_mul, norm_mul, norm_mul]
        have hk1 : ‖((-2:ℤ):ℂ)‖ = 2 := by norm_num
        have hk2 : ‖(z - y) ^ ((-2:ℤ) - 1)‖ = ‖z - y‖⁻¹^3 := by
          rw [norm_zpow, show ((-2:ℤ) - 1) = (-3:ℤ) by ring, zpow_neg,
            show ((3:ℤ)) = ((3:ℕ):ℤ) by norm_num, zpow_natCast, inv_pow]
        rw [hk1, hk2, hCval]
        have hmono : ‖z - y‖⁻¹^3 ≤ (‖z‖ - R')⁻¹^3 := by gcongr
        have hstep : 2 * ‖z - y‖⁻¹^3 * ‖ν y‖ * ‖m‖ ≤ 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖ := by
          apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
          apply mul_le_mul _ (hM y) (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left hmono (by norm_num)
        exact hstep
      have hballfin : volume (Metric.closedBall (0:ℂ) R') < ⊤ := by
        rw [Complex.volume_closedBall]; finiteness
      have hib := norm_setIntegral_le_of_norm_le_const hballfin hbd
      have hvolnn : 0 ≤ (volume (Metric.closedBall (0:ℂ) R')).toReal := ENNReal.toReal_nonneg
      have hCvalbd : Cval ≤ 16 * M * ‖m‖ / ‖z‖^2 := by
        rw [hCval]
        have he : (‖z‖ - R')⁻¹^3 ≤ (‖z‖/2)⁻¹^3 := by
          apply pow_le_pow_left₀ (inv_nonneg.mpr hbdpos.le)
          apply inv_anti₀ (by positivity)
          linarith [hz]
        have he2 : (‖z‖/2)⁻¹^3 ≤ 8 / ‖z‖^2 := by
          rw [inv_div, div_pow]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (1:ℝ) ≤ ‖z‖ := by linarith [hz]
          nlinarith [pow_pos hzpos 2, sq_nonneg ‖z‖, hzpos.le]
        calc 2 * (‖z‖ - R')⁻¹^3 * M * ‖m‖
            ≤ 2 * (8 / ‖z‖^2) * M * ‖m‖ := by
              apply mul_le_mul _ le_rfl (norm_nonneg _) (by positivity)
              apply mul_le_mul _ le_rfl hMnn (by positivity)
              apply mul_le_mul_of_nonneg_left (le_trans he he2) (by norm_num)
          _ = 16 * M * ‖m‖ / ‖z‖^2 := by ring
      calc (1/π) * ‖∫ y in Metric.closedBall (0:ℂ) R', (Fp' y) m‖
          ≤ (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [Measure.real] at hib; exact hib
        _ ≤ Cd / ‖z‖^2 := by
            rw [hCd]
            have hstep : (1/π) * (Cval * (volume (Metric.closedBall (0:ℂ) R')).toReal)
                ≤ (1/π) * ((16 * M * ‖m‖ / ‖z‖^2)
                  * (volume (Metric.closedBall (0:ℂ) R')).toReal) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul_of_nonneg_right hCvalbd hvolnn
            refine le_trans hstep (le_of_eq ?_)
            field_simp
    -- now MemLp via decay helper
    have hcont : Continuous (fun z => (fderiv ℝ (beurling ν) z) m) :=
      (hB.continuous_fderiv (n := 1) one_ne_zero).clm_apply continuous_const
    have haesm : AEStronglyMeasurable (fun z => (fderiv ℝ (beurling ν) z) m) volume :=
      hcont.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm haesm]
    set R'' : ℝ := 2*R'+4 with hR''def
    have hR''pos : 0 < R'' := by rw [hR''def]; positivity
    have hball : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'') volume :=
      (hcont.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R'')
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      apply Measurable.pow_const
      exact measurable_const.div (measurable_fst.pow_const 2)
    have hcompl : IntegrableOn (fun z => ‖(fderiv ℝ (beurling ν) z) m‖^2)
        (Metric.closedBall (0:ℂ) R'')ᶜ volume := by
      refine ⟨((hcont.norm.pow 2).aestronglyMeasurable).restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hpt : ∀ z ∈ (Metric.closedBall (0:ℂ) R'')ᶜ,
          ‖(‖(fderiv ℝ (beurling ν) z) m‖^2 : ℝ)‖ₑ ≤ ENNReal.ofReal ((Cd / ‖z‖^2)^2) := by
        intro z hz
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := hdecay z hz
        have hnn : 0 ≤ ‖(fderiv ℝ (beurling ν) z) m‖ := norm_nonneg _
        nlinarith [hb, hnn]
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall.compl hpt) ?_
      rw [← lintegral_indicator measurableSet_closedBall.compl]
      rw [← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ioi R'' ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * (Cd / p.1^2)^2)) p with hbox
      have hbound : ∀ p ∈ polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
            (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p) ≤ box p := by
        intro p hp
        rw [polarCoord_target, Set.mem_prod] at hp
        obtain ⟨hp1, hp2⟩ := hp
        simp only [Set.mem_Ioi] at hp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        by_cases hmem : Complex.polarCoord.symm p ∈ (Metric.closedBall (0:ℂ) R'')ᶜ
        · rw [Set.indicator_of_mem hmem]
          have hpR : R'' < p.1 := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hnorm, not_le] at hmem
            exact hmem
          rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hpR, hp2⟩)]
          rw [hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]
          exact zero_le _
      have hboxmeas : Measurable box :=
        hmeas_polar.indicator (measurableSet_Ioi.prod measurableSet_Ioo)
      calc
        ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • (Metric.closedBall (0:ℂ) R'')ᶜ.indicator
              (fun z => ENNReal.ofReal ((Cd / ‖z‖^2)^2)) (Complex.polarCoord.symm p)
            ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hboxmeas hbound
        _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
        _ = ∫⁻ p in (Set.Ioi R'' ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (p.1 * (Cd / p.1^2)^2) := by
              rw [hbox, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ]
              rw [setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint : IntegrableOn (fun r : ℝ => r * (Cd / r^2)^2) (Set.Ioi R'') volume := by
                have heq : (fun r : ℝ => r * (Cd / r^2)^2) =ᶠ[ae (volume.restrict (Set.Ioi R''))]
                    (fun r : ℝ => Cd^2 * r^(-3 : ℝ)) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
                  simp only [Set.mem_Ioi] at hr
                  have hrpos : 0 < r := lt_trans hR''pos hr
                  have hrne : r ≠ 0 := ne_of_gt hrpos
                  rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
                  field_simp
                rw [integrableOn_congr_fun_ae heq]
                apply Integrable.const_mul
                rw [← IntegrableOn, integrableOn_Ioi_rpow_iff hR''pos]
                norm_num
              have hfin := hint.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
              · apply Measurable.enorm
                apply Measurable.mul measurable_id
                apply Measurable.pow_const
                exact measurable_const.div (measurable_id.pow_const 2)
              · simp only [Set.mem_Ioi] at hx
                have hxpos : 0 < x := lt_trans hR''pos hx
                rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hball.union hcompl
    rw [Set.union_compl_self, integrableOn_univ] at this
    exact this
  exact dirichlet_energy_isometry hB hν1 hBL2 hNL2 hB1L2 hBIL2 hN1L2 hNIL2 hClairaut

/-- The **truncated Beurling convolution kernel** `k_r(u) = u⁻² · 1_{‖u‖ ≥ r}`.

This is the translation-invariant kernel of the truncated Beurling operator:
`czOperator beurlingKernel r f = k_r ⋆ f` (`czOperator_beurling_eq_convolution`).
Truncating below `r` removes the non-integrable singularity at `0`; the remaining
`|u|⁻²` tail is square-integrable on `ℂ = ℝ²` (`‖k_r‖₂² = π r⁻²`) but *not*
integrable (the `2D` tail `∫_{|u|>r} |u|⁻² = 2π ∫_r^∞ ρ⁻¹ dρ` diverges
logarithmically), so the operator is a genuine principal-value singular integral,
not a Young-type `L¹⋆L²` convolution.

The set `{u | r ≤ ‖u‖}` (closed) is chosen to match `(ball x r)ᶜ` exactly, so the
identification with `czOperator` is a strict equality (no `a.e.` slack). -/
noncomputable def truncBeurlingKernel (r : ℝ) (u : ℂ) : ℂ :=
  Set.indicator {u : ℂ | r ≤ ‖u‖} (fun u => u ^ (-2 : ℤ)) u

/-- **The truncated Beurling operator is convolution against `truncBeurlingKernel`.**
`czOperator beurlingKernel r f x = ∫_{‖y-x‖≥r} (x-y)⁻² f y dy = (k_r ⋆ f)(x)`, with
`k_r(u) = u⁻²·1_{‖u‖≥r}`. The substitution `t = x - y` turns the `(ball x r)ᶜ`
integral over `y` into the convolution integral `∫ t, k_r t · f(x-t)`; left
invariance of Lebesgue measure (`integral_sub_left_eq_self`) supplies the change of
variables, and the truncation sets match on the nose because `(ball x r)ᶜ =
{y | r ≤ ‖y-x‖}` corresponds under `t = x-y` to `{t | r ≤ ‖t‖}`. -/
lemma czOperator_beurling_eq_convolution (r : ℝ) (f : ℂ → ℂ) :
    czOperator beurlingKernel r f
      = MeasureTheory.convolution (truncBeurlingKernel r) f
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  rw [MeasureTheory.convolution_mul]
  change (∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * f y)
      = ∫ t, truncBeurlingKernel r t * f (x - t)
  rw [← integral_indicator measurableSet_ball.compl]
  rw [show (fun t => truncBeurlingKernel r t * f (x - t))
        = (fun t => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y * f y) (x - t))
        from ?_]
  · rw [MeasureTheory.integral_sub_left_eq_self
        (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y * f y) y) volume x]
  · funext t
    have hmem : (x - t ∈ (Metric.ball x r)ᶜ) ↔ (t ∈ {u : ℂ | r ≤ ‖u‖}) := by
      simp only [Set.mem_compl_iff, Metric.mem_ball, Set.mem_setOf_eq, not_lt, dist_eq_norm,
        show x - t - x = -t by ring, norm_neg]
    by_cases h : t ∈ {u : ℂ | r ≤ ‖u‖}
    · have h2 : (x - t) ∈ (Metric.ball x r)ᶜ := hmem.mpr h
      rw [truncBeurlingKernel, Set.indicator_of_mem h, Set.indicator_of_mem h2, beurlingKernel,
        show x - (x - t) = t by ring]
    · have h2 : (x - t) ∉ (Metric.ball x r)ᶜ := fun hc => h (hmem.mp hc)
      rw [truncBeurlingKernel, Set.indicator_of_notMem h, Set.indicator_of_notMem h2, zero_mul]

/-- **Young's convolution inequality `L¹ ⋆ L² → L²`.** For `g ∈ L¹(ℂ)` and
`f ∈ L²(ℂ)` the convolution `g ⋆ f` lies in `L²(ℂ)` with `‖g ⋆ f‖₂ ≤ ‖g‖₁ ‖f‖₂`.

Mathlib has *no* `Lᵖ` Young inequality (an explicit "To do" in
`Mathlib/Analysis/Convolution.lean`), so we build it here from the continuous
Minkowski integral inequality (`MeasureTheory.lintegral_lintegral_pow_swap`,
supplied by the Carleson `RealInterpolation.Minkowski` file): writing
`‖(g ⋆ f)(x)‖ₑ ≤ ∫ ‖g(t)‖ ‖f(x-t)‖ dt` (triangle inequality for the Bochner
integral) and applying Minkowski with exponent `2` reduces to the translation
invariance `‖f(·-t)‖₂ = ‖f‖₂`, which factors out the `t`-integral of `‖g‖`. -/
lemma eLpNorm_convolution_le {g f : ℂ → ℂ}
    (hg : MemLp g 1 volume) (hf : MemLp f 2 volume) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume
      ≤ eLpNorm g 1 volume * eLpNorm f 2 volume := by
  set G : ℂ → ℂ → ℝ≥0∞ := fun x t => ‖g t‖ₑ * ‖f (x - t)‖ₑ with hG
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  -- Step 1: pointwise enorm bound on the convolution integral
  have hpt : ∀ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ
      ≤ ∫⁻ t, G x t ∂volume := by
    intro x
    rw [MeasureTheory.convolution_mul]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    apply lintegral_mono
    intro t
    simp only [hG, enorm_mul, le_refl]
  -- Step 2: rewrite `eLpNorm 2` as a lintegral and monotone-bound
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num]
  have hmono :
      (∫⁻ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ ^ (2:ℝ)
          ∂volume) ^ (1 / (2:ℝ))
        ≤ (∫⁻ x, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) ∂volume) ^ (1 / (2:ℝ)) := by
    gcongr with x
    exact hpt x
  refine le_trans hmono ?_
  -- Step 3: Minkowski's integral inequality (p = 2)
  have hGmeas : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
    apply AEMeasurable.mul
    · exact hgm.comp_snd
    · have hsub : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact hsub.enorm
  have hMink := MeasureTheory.lintegral_lintegral_pow_swap (p := (2:ℝ)) (by norm_num)
    (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) (f := G) hGmeas
  rw [show (1 / (2:ℝ)) = (2:ℝ)⁻¹ by norm_num]
  refine le_trans hMink ?_
  -- Step 4: evaluate the inner lintegral via translation invariance
  have hinner : ∀ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹
      = ‖g t‖ₑ * eLpNorm f 2 volume := by
    intro t
    simp only [hG]
    have hsplit : (fun x => (‖g t‖ₑ * ‖f (x - t)‖ₑ) ^ (2:ℝ))
        = (fun x => ‖g t‖ₑ ^ (2:ℝ) * ‖f (x - t)‖ₑ ^ (2:ℝ)) := by
      funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    rw [hsplit, lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp))]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    rw [← ENNReal.rpow_mul]
    rw [show (2:ℝ) * (2:ℝ)⁻¹ = 1 by norm_num, ENNReal.rpow_one]
    have htrans : eLpNorm (fun x => f (x - t)) 2 volume = eLpNorm f 2 volume :=
      eLpNorm_comp_measurePreserving hfm (measurePreserving_sub_right volume t)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at htrans
    simp only [show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num] at htrans
    rw [one_div] at htrans
    rw [htrans]
  rw [lintegral_congr hinner]
  rw [lintegral_mul_const'' _ hgm]
  rw [← eLpNorm_one_eq_lintegral_enorm]

/-- **Dyadic piece of the (truncated) Beurling kernel.** The annular restriction
`ψ_j(u) = u⁻²·1_{2ʲr ≤ ‖u‖ < 2ʲ⁺¹r}` of the singular kernel `u⁻²`. The truncated
Beurling kernel `k_r = u⁻²·1_{‖u‖≥r}` is the (a.e.) sum `∑_j ψ_j` of these dyadic
pieces, each of which is genuinely `L¹` (the divergence is only in summing over
`j`). These are the building blocks of the dyadic almost-orthogonality
decomposition. -/
noncomputable def dyadicBeurling (r : ℝ) (j : ℕ) (u : ℂ) : ℂ :=
  Set.indicator {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
    (fun u => u ^ (-2 : ℤ)) u

/-- The dyadic annulus `{2ʲr ≤ ‖u‖ < 2ʲ⁺¹r}` is measurable. -/
lemma measurableSet_dyadicAnnulus (r : ℝ) (j : ℕ) :
    MeasurableSet {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := by
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const measurable_norm
  · exact measurableSet_lt measurable_norm measurable_const

/-- The `enorm` of a dyadic piece is the annular indicator of `‖u⁻²‖ₑ`. -/
lemma enorm_dyadicBeurling (r : ℝ) (j : ℕ) (u : ℂ) :
    ‖dyadicBeurling r j u‖ₑ
      = Set.indicator {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
          (fun u => ‖(u ^ (-2:ℤ) : ℂ)‖ₑ) u := by
  rw [dyadicBeurling]
  by_cases h : u ∈ {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

/-- **The `L¹` norm of every dyadic piece is `2π log 2`,** uniform in `j` and `r`.
This is the key uniform bound: each annular piece has the same `L¹` mass, the
logarithmic divergence of `‖k_r‖₁` arising purely from the (infinitely many)
dyadic scales `∑_j 2π log 2 = ∞`. Computed via `annulus_lintegral` with the
endpoints `a = 2ʲr`, `b = 2ʲ⁺¹r`, where `log(b/a) = log 2`. -/
lemma eLpNorm_dyadicBeurling (r : ℝ) (hr : 0 < r) (j : ℕ) :
    eLpNorm (dyadicBeurling r j) 1 volume = ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hpt : (fun u => ‖dyadicBeurling r j u‖ₑ)
      = Set.indicator {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
          (fun u => ‖(u ^ (-2:ℤ) : ℂ)‖ₑ) := by
    funext u; exact enorm_dyadicBeurling r j u
  rw [hpt]
  rw [lintegral_indicator (measurableSet_dyadicAnnulus r j)]
  have ha : 0 < (2:ℝ)^j * r := by positivity
  have hab : (2:ℝ)^j * r < (2:ℝ)^(j+1) * r := by
    apply mul_lt_mul_of_pos_right _ hr
    apply pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [SingularIntegral.annulus_lintegral _ _ ha hab]
  have heq : (2:ℝ)^(j+1) * r / ((2:ℝ)^j * r) = 2 := by
    rw [pow_succ]
    have h2j : (2:ℝ)^j ≠ 0 := by positivity
    field_simp
  rw [heq]

/-- **Each dyadic piece lies in `L¹`.** Immediate from
`eLpNorm_dyadicBeurling` (finite `L¹` mass) plus measurability of the annular
indicator of `u ↦ u⁻²`. -/
lemma memLp_dyadicBeurling (r : ℝ) (hr : 0 < r) (j : ℕ) :
    MemLp (dyadicBeurling r j) 1 volume := by
  constructor
  · apply AEStronglyMeasurable.indicator _ (measurableSet_dyadicAnnulus r j)
    apply Measurable.aestronglyMeasurable
    have : (fun u : ℂ => u ^ (-2 : ℤ)) = (fun u : ℂ => (u * u)⁻¹) := by
      funext u; rw [zpow_neg, zpow_two]
    rw [this]
    exact (measurable_id.mul measurable_id).inv
  · rw [eLpNorm_dyadicBeurling r hr j]
    exact ENNReal.ofReal_lt_top

/-- **`L¹ ⋆ L² ⊆ L²`.** For `g ∈ L¹(ℂ)` and `f ∈ L²(ℂ)` the convolution `g ⋆ f`
again lies in `L²(ℂ)`. The `eLpNorm < ∞` half is the Young inequality
`eLpNorm_convolution_le`; the `AEStronglyMeasurable` half is measurability of the
parametrized integral `x ↦ ∫ t, g t · f (x - t)` via
`AEStronglyMeasurable.integral_prod_right'`. This packages a convolution against a
fixed `L¹` kernel as a self-map of `L²`, the analytic substrate of the
Cotlar–Stein dyadic operators. -/
lemma memLp_convolution_two {g : ℂ → ℂ} (hg : MemLp g 1 volume) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) :
    MemLp (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume := by
  constructor
  · have hint : AEStronglyMeasurable
        (Function.uncurry fun x t => g t * f (x - t)) (volume.prod volume) := by
      apply AEStronglyMeasurable.mul
      · exact hg.1.comp_snd
      · exact hf.1.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    have hmeas := hint.integral_prod_right' (ν := (volume : Measure ℂ))
    simp only [Function.uncurry] at hmeas
    have hconv : (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume)
        = (fun x => ∫ t, g t * f (x - t) ∂volume) := by
      funext x; rw [MeasureTheory.convolution_mul]
    rw [hconv]
    exact hmeas
  · exact lt_of_le_of_lt (eLpNorm_convolution_le hg hf)
      (ENNReal.mul_lt_top hg.2 hf.2)

/-- For `g ∈ L¹` and `f ∈ L²`, the convolution integrand `t ↦ g t * f (x - t)` is
integrable for a.e. `x`. This is the a.e. existence of the L¹⋆L² convolution. -/
lemma ae_convolutionExistsAt {g : ℂ → ℂ} (hg : MemLp g 1 volume) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, ConvolutionExistsAt g f x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  -- enorm integrand as a lintegral; finiteness for a.e. x from Young.
  set G : ℂ → ℂ → ℝ≥0∞ := fun x t => ‖g t‖ₑ * ‖f (x - t)‖ₑ with hG
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  have hGmeas : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
    apply AEMeasurable.mul
    · exact hgm.comp_snd
    · have hsub : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact hsub.enorm
  have hMink := MeasureTheory.lintegral_lintegral_pow_swap (p := (2:ℝ)) (by norm_num)
    (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) (f := G) hGmeas
  have hinner : ∀ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹
      = ‖g t‖ₑ * eLpNorm f 2 volume := by
    intro t
    simp only [hG]
    have hsplit : (fun x => (‖g t‖ₑ * ‖f (x - t)‖ₑ) ^ (2:ℝ))
        = (fun x => ‖g t‖ₑ ^ (2:ℝ) * ‖f (x - t)‖ₑ ^ (2:ℝ)) := by
      funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    rw [hsplit, lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp))]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    rw [← ENNReal.rpow_mul]
    rw [show (2:ℝ) * (2:ℝ)⁻¹ = 1 by norm_num, ENNReal.rpow_one]
    have htrans : eLpNorm (fun x => f (x - t)) 2 volume = eLpNorm f 2 volume :=
      eLpNorm_comp_measurePreserving hfm (measurePreserving_sub_right volume t)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at htrans
    simp only [show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num] at htrans
    rw [one_div] at htrans
    rw [htrans]
  have hRHS : (∫⁻ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹ ∂volume)
      = eLpNorm g 1 volume * eLpNorm f 2 volume := by
    rw [lintegral_congr hinner, lintegral_mul_const'' _ hgm, ← eLpNorm_one_eq_lintegral_enorm]
  have hRHS_lt : (∫⁻ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹ ∂volume) < ⊤ := by
    rw [hRHS]; exact ENNReal.mul_lt_top hg.2 hf.2
  have hLHS_lt : (∫⁻ x, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹ < ⊤ :=
    lt_of_le_of_lt hMink hRHS_lt
  have hdouble_lt : (∫⁻ x, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) ∂volume) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h] at hLHS_lt
    simp only [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)] at hLHS_lt
    exact (lt_irrefl _ hLHS_lt)
  have hae_pow : ∀ᵐ x ∂volume, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) < ⊤ :=
    ae_lt_top' (by
      apply AEMeasurable.pow_const
      exact hGmeas.lintegral_prod_right') hdouble_lt.ne
  have hae_inner : ∀ᵐ x ∂volume, (∫⁻ t, G x t ∂volume) < ⊤ := by
    filter_upwards [hae_pow] with x hx
    rw [lt_top_iff_ne_top]
    intro h
    rw [h] at hx
    simp only [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < (2:ℝ))] at hx
    exact (lt_irrefl _ hx)
  filter_upwards [hae_inner] with x hx
  refine ⟨?_, ?_⟩
  · apply hg.1.mul
    exact hfm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℂ) x)
  · rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ hx
    apply lintegral_mono
    intro t
    simp only [hG, ContinuousLinearMap.mul_apply', enorm_mul, le_refl]

/-- The convolution `g ⋆ F` of an `L¹` kernel `g` with the `L²` representative of
`F`, packaged back into `L²`. -/
noncomputable def convToLp (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F : Lp ℂ 2 (volume : Measure ℂ)) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  (memLp_convolution_two hg (Lp.memLp F)).toLp
    (MeasureTheory.convolution g (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume)

/-- Convolution by `g` is additive (a.e.) in the second argument, for `g ∈ L¹` and
`F₁, F₂ ∈ L²`. -/
lemma convolution_ae_add {g : ℂ → ℂ} (hg : MemLp g 1 volume)
    {f₁ f₂ : ℂ → ℂ} (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) :
    MeasureTheory.convolution g (f₁ + f₂) (ContinuousLinearMap.mul ℂ ℂ) volume
      =ᵐ[volume]
        MeasureTheory.convolution g f₁ (ContinuousLinearMap.mul ℂ ℂ) volume
          + MeasureTheory.convolution g f₂ (ContinuousLinearMap.mul ℂ ℂ) volume := by
  filter_upwards [ae_convolutionExistsAt hg hf₁, ae_convolutionExistsAt hg hf₂] with x h₁ h₂
  exact h₁.distrib_add h₂

/-- The underlying linear map `F ↦ g ⋆ F` on `L²`. -/
noncomputable def convLM (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    (Lp ℂ 2 (volume : Measure ℂ)) →ₗ[ℂ] (Lp ℂ 2 (volume : Measure ℂ)) where
  toFun F := convToLp g hg F
  map_add' F₁ F₂ := by
    have hF₁ : MemLp (F₁ : ℂ → ℂ) 2 volume := Lp.memLp F₁
    have hF₂ : MemLp (F₂ : ℂ → ℂ) 2 volume := Lp.memLp F₂
    apply Lp.ext
    have hadd : (↑(F₁ + F₂) : ℂ → ℂ) =ᵐ[volume] (F₁ : ℂ → ℂ) + (F₂ : ℂ → ℂ) :=
      Lp.coeFn_add F₁ F₂
    have hL : (convToLp g hg (F₁ + F₂) : ℂ → ℂ)
        =ᵐ[volume] MeasureTheory.convolution g (↑(F₁ + F₂))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MemLp.coeFn_toLp _
    have hR : ((convToLp g hg F₁ + convToLp g hg F₂ : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume]
          MeasureTheory.convolution g (F₁ : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume
            + MeasureTheory.convolution g (F₂ : ℂ → ℂ)
              (ContinuousLinearMap.mul ℂ ℂ) volume := by
      filter_upwards [Lp.coeFn_add (convToLp g hg F₁) (convToLp g hg F₂),
        (MemLp.coeFn_toLp (memLp_convolution_two hg hF₁)),
        (MemLp.coeFn_toLp (memLp_convolution_two hg hF₂))] with x hx h1 h2
      rw [hx]
      simp only [Pi.add_apply, convToLp]
      rw [h1, h2]
    have hconveq : MeasureTheory.convolution g (↑(F₁ + F₂))
          (ContinuousLinearMap.mul ℂ ℂ) volume
        = MeasureTheory.convolution g ((F₁ : ℂ → ℂ) + (F₂ : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
        (μ := (volume : Measure ℂ)) (Filter.EventuallyEq.refl _ g) hadd
    have hsplit := convolution_ae_add hg hF₁ hF₂
    rw [hconveq] at hL
    exact hL.trans (hsplit.trans hR.symm)
  map_smul' c F := by
    have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
    apply Lp.ext
    simp only [RingHom.id_apply]
    have hL : (convToLp g hg (c • F) : ℂ → ℂ)
        =ᵐ[volume] MeasureTheory.convolution g (↑(c • F))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MemLp.coeFn_toLp _
    have hsmul : (↑(c • F) : ℂ → ℂ) =ᵐ[volume] c • (F : ℂ → ℂ) := Lp.coeFn_smul c F
    have hconveq : MeasureTheory.convolution g (↑(c • F))
          (ContinuousLinearMap.mul ℂ ℂ) volume
        = MeasureTheory.convolution g (c • (F : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
        (μ := (volume : Measure ℂ)) (Filter.EventuallyEq.refl _ g) hsmul
    have hpull : MeasureTheory.convolution g (c • (F : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume
        = c • MeasureTheory.convolution g (F : ℂ → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MeasureTheory.convolution_smul
    have hR : ((c • convToLp g hg F : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume] c • MeasureTheory.convolution g (F : ℂ → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
      filter_upwards [Lp.coeFn_smul c (convToLp g hg F),
        MemLp.coeFn_toLp (memLp_convolution_two hg hF)] with x hx h1
      rw [hx]
      simp only [Pi.smul_apply, convToLp]
      rw [h1]
    rw [hconveq, hpull] at hL
    exact hL.trans hR.symm

/-- The operator "convolve by `g`" as a continuous linear self-map of `L²(ℂ)`,
for `g ∈ L¹`, with operator-norm bound `(eLpNorm g 1 volume).toReal` from Young's
inequality. This is the dyadic Cotlar–Stein operator `T_j = convCLM (ψ_j)`. -/
noncomputable def convCLM (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    (Lp ℂ 2 (volume : Measure ℂ)) →L[ℂ] (Lp ℂ 2 (volume : Measure ℂ)) :=
  LinearMap.mkContinuous (convLM g hg) (eLpNorm g 1 volume).toReal (by
    intro F
    have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
    change ‖convToLp g hg F‖ ≤ _
    rw [convToLp, Lp.norm_toLp, Lp.norm_def]
    have hYoung := eLpNorm_convolution_le hg hF
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal (memLp_convolution_two hg hF).2.ne
      (ENNReal.mul_ne_top hg.2.ne (Lp.eLpNorm_ne_top F))).mpr hYoung)

/-- The action of `convCLM g hg` on a representative: `(convCLM g hg F) =ᵐ g ⋆ F`. -/
theorem convCLM_apply_coeFn (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F : Lp ℂ 2 (volume : Measure ℂ)) :
    (convCLM g hg F : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution g (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
  MemLp.coeFn_toLp (memLp_convolution_two hg (Lp.memLp F))

/-- The operator-norm bound from Young's inequality:
`‖convCLM g hg‖ ≤ (eLpNorm g 1 volume).toReal`. -/
theorem convCLM_opNorm_le (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    ‖convCLM g hg‖ ≤ (eLpNorm g 1 volume).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- The **adjoint kernel** `g̃ u = conj (g (-u))`. The Hilbert adjoint on `L²` of
convolution-by-`g` is convolution-by-`g̃` (`adjoint_convCLM`). -/
noncomputable def convKernelStar (g : ℂ → ℂ) : ℂ → ℂ := fun u => starRingEnd ℂ (g (-u))

/-- The `L¹` norm of `g̃ u = conj (g (-u))` equals that of `g`: conjugation preserves
the pointwise norm and `u ↦ -u` is measure preserving. -/
theorem eLpNorm_convKernelStar (g : ℂ → ℂ) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (convKernelStar g) 1 volume = eLpNorm g 1 volume := by
  have hconj : eLpNorm (convKernelStar g) 1 volume = eLpNorm (fun u => g (-u)) 1 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with u
    exact Complex.norm_conj (g (-u))
  rw [hconj, show (fun u : ℂ => g (-u)) = g ∘ (fun u : ℂ => -u) from rfl]
  exact eLpNorm_comp_measurePreserving hg (Measure.measurePreserving_neg volume)

/-- `g̃ ∈ L¹` whenever `g ∈ L¹`. -/
theorem memLp_convKernelStar {g : ℂ → ℂ} (hg : MemLp g 1 volume) :
    MemLp (convKernelStar g) 1 volume := by
  refine ⟨?_, ?_⟩
  · apply Complex.continuous_conj.comp_aestronglyMeasurable
    exact hg.1.comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  · rw [eLpNorm_convKernelStar g hg.1]
    exact hg.2

/-- `(∫ ‖f‖²)^(1/2)` equals `(‖f‖₂).toReal` for `f ∈ L²`. -/
theorem rpow_half_eq (f : ℂ → ℂ) (hf : MemLp f 2 volume) :
    (∫ a, ‖f a‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) = (eLpNorm f 2 volume).toReal := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
  rw [ENNReal.toReal_ofReal (by positivity)]; norm_num

/-- Uniform Cauchy–Schwarz bound (translate on the left factor):
`∫ x, ‖F (x-t)‖·‖H x‖ ≤ ‖F‖₂·‖H‖₂`, independent of `t`. -/
theorem cs_unif (F H : ℂ → ℂ) (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) (t : ℂ) :
    ∫ x, ‖F (x - t)‖ * ‖H x‖ ∂volume
      ≤ (eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal := by
  have hFt : MemLp (fun x => F (x - t)) 2 volume :=
    hF.comp_measurePreserving (measurePreserving_sub_right volume t)
  have heq : eLpNorm (fun x => F (x - t)) 2 volume = eLpNorm F 2 volume :=
    eLpNorm_comp_measurePreserving (p := 2) hF.1 (measurePreserving_sub_right volume t)
  have hCS := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
    (p := 2) (q := 2) (Real.HolderConjugate.two_two) (by simpa using hFt) (by simpa using hH)
  refine hCS.trans ?_
  rw [rpow_half_eq _ hFt, rpow_half_eq _ hH, heq]

/-- Uniform Cauchy–Schwarz bound (translate on the right factor):
`∫ y, ‖F y‖·‖H (y-t)‖ ≤ ‖F‖₂·‖H‖₂`, independent of `t`. -/
theorem cs_unif2 (F H : ℂ → ℂ) (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) (t : ℂ) :
    ∫ y, ‖F y‖ * ‖H (y - t)‖ ∂volume
      ≤ (eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal := by
  have hHt : MemLp (fun y => H (y - t)) 2 volume :=
    hH.comp_measurePreserving (measurePreserving_sub_right volume t)
  have heq : eLpNorm (fun y => H (y - t)) 2 volume = eLpNorm H 2 volume :=
    eLpNorm_comp_measurePreserving (p := 2) hH.1 (measurePreserving_sub_right volume t)
  have hCS := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
    (p := 2) (q := 2) (Real.HolderConjugate.two_two) (by simpa using hF) (by simpa using hHt)
  refine hCS.trans ?_
  rw [rpow_half_eq _ hF, rpow_half_eq _ hHt, heq]

private theorem qmp_sub21 : Measure.QuasiMeasurePreserving (fun p : ℂ × ℂ => p.2 - p.1)
    (volume.prod volume) volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun p : ℂ × ℂ => p.1 - p.2)
      (volume.prod volume) volume := quasiMeasurePreserving_sub_of_right_invariant volume volume
  simpa [Function.comp, Prod.swap] using
    h1.comp (Measure.measurePreserving_swap).quasiMeasurePreserving

private theorem qmp_sub12 : Measure.QuasiMeasurePreserving (fun p : ℂ × ℂ => p.1 - p.2)
    (volume.prod volume) volume := quasiMeasurePreserving_sub_of_right_invariant volume volume

/-- Joint integrability of the LHS bilinear integrand
`(t, x) ↦ conj(g t)·(conj(F(x-t))·H x)` (coordinates `p.1 = t`, `p.2 = x`). -/
theorem joint_int (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    Integrable (fun p : ℂ × ℂ =>
      starRingEnd ℂ (g p.1) * (starRingEnd ℂ (F (p.2 - p.1)) * H p.2))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℂ × ℂ => starRingEnd ℂ (g p.1) * (starRingEnd ℂ (F (p.2 - p.1)) * H p.2))
      (volume.prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable hg.1).comp_fst
    · apply AEStronglyMeasurable.mul
      · exact Complex.continuous_conj.comp_aestronglyMeasurable
          (hF.1.comp_quasiMeasurePreserving qmp_sub21)
      · exact hH.1.comp_snd
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards with t
    have hFt : MemLp (fun x => F (x - t)) 2 volume :=
      hF.comp_measurePreserving (measurePreserving_sub_right volume t)
    have hconjFt : MemLp (fun x => starRingEnd ℂ (F (x - t))) 2 volume := by
      have heqn : eLpNorm (fun x => starRingEnd ℂ (F (x - t))) 2 volume
          = eLpNorm (fun x => F (x - t)) 2 volume := by
        apply eLpNorm_congr_norm_ae; filter_upwards with x; exact Complex.norm_conj _
      exact ⟨Complex.continuous_conj.comp_aestronglyMeasurable hFt.1, by rw [heqn]; exact hFt.2⟩
    exact (MemLp.integrable_mul (p := 2) (q := 2) hconjFt hH).const_mul (starRingEnd ℂ (g t))
  · have hgn : Integrable (fun a => ‖g a‖) volume := (memLp_one_iff_integrable.mp hg).norm
    have hdom : Integrable
        (fun t => ‖g t‖ * ((eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal)) volume :=
      Integrable.mul_const hgn _
    refine Integrable.mono' hdom hmeas.norm.integral_prod_right' ?_
    filter_upwards with t
    have hnn : (0 : ℝ) ≤ ∫ x, ‖starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)‖ ∂volume :=
      integral_nonneg (fun x => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    have heq2 : (fun x => ‖starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)‖)
        = (fun x => ‖g t‖ * (‖F (x - t)‖ * ‖H x‖)) := by
      funext x; rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    rw [heq2, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (cs_unif F H hF hH t) (norm_nonneg _)

/-- Joint integrability of the RHS bilinear integrand
`(y, t) ↦ conj(F y)·(conj(g(-t))·H(y-t))` (coordinates `p.1 = y`, `p.2 = t`). -/
theorem joint_int2 (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    Integrable (fun p : ℂ × ℂ =>
      starRingEnd ℂ (F p.1) * (starRingEnd ℂ (g (-p.2)) * H (p.1 - p.2)))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℂ × ℂ => starRingEnd ℂ (F p.1) * (starRingEnd ℂ (g (-p.2)) * H (p.1 - p.2)))
      (volume.prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable hF.1).comp_fst
    · apply AEStronglyMeasurable.mul
      · apply Complex.continuous_conj.comp_aestronglyMeasurable
        exact (hg.1.comp_quasiMeasurePreserving
          ((Measure.measurePreserving_neg volume).quasiMeasurePreserving)).comp_snd
      · exact hH.1.comp_quasiMeasurePreserving qmp_sub12
  rw [integrable_prod_iff' hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards with t
    have hHt : MemLp (fun y => H (y - t)) 2 volume :=
      hH.comp_measurePreserving (measurePreserving_sub_right volume t)
    have hconjF : MemLp (fun y => starRingEnd ℂ (F y)) 2 volume := by
      have heqn : eLpNorm (fun y => starRingEnd ℂ (F y)) 2 volume = eLpNorm F 2 volume := by
        apply eLpNorm_congr_norm_ae; filter_upwards with y; exact Complex.norm_conj _
      exact ⟨Complex.continuous_conj.comp_aestronglyMeasurable hF.1, by rw [heqn]; exact hF.2⟩
    have hprod : Integrable (fun y => starRingEnd ℂ (F y) * H (y - t)) volume :=
      MemLp.integrable_mul (p := 2) (q := 2) hconjF hHt
    have hc := hprod.const_mul (starRingEnd ℂ (g (-t)))
    apply hc.congr; filter_upwards with y; ring
  · have hgn : Integrable (fun a => ‖g (-a)‖) volume :=
      ((memLp_one_iff_integrable.mp hg).comp_neg).norm
    have hdom : Integrable
        (fun t => ‖g (-t)‖ * ((eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal)) volume :=
      Integrable.mul_const hgn _
    have hmeasL : AEStronglyMeasurable
        (fun t => ∫ y, ‖starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))‖ ∂volume)
        volume := by
      have hsw : AEStronglyMeasurable
          (fun p : ℂ × ℂ => ‖starRingEnd ℂ (F p.2) * (starRingEnd ℂ (g (-p.1)) * H (p.2 - p.1))‖)
          (volume.prod volume) := by
        have := hmeas.norm.comp_measurePreserving
          (Measure.measurePreserving_swap (μ := (volume : Measure ℂ)) (ν := volume))
        simpa [Function.comp, Prod.swap] using this
      exact hsw.integral_prod_right'
    refine Integrable.mono' hdom hmeasL ?_
    filter_upwards with t
    have hnn : (0 : ℝ)
        ≤ ∫ y, ‖starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))‖ ∂volume :=
      integral_nonneg (fun y => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    have heq2 : (fun y => ‖starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))‖)
        = (fun y => ‖g (-t)‖ * (‖F y‖ * ‖H (y - t)‖)) := by
      funext y; rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]; ring
    rw [heq2, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (cs_unif2 F H hF hH t) (norm_nonneg _)

/-- The left inner product `⟪g ⋆ F, H⟫` as an iterated integral. -/
theorem lhs_eq (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F H : Lp ℂ 2 (volume : Measure ℂ)) :
    (inner ℂ (convCLM g hg F) H : ℂ)
      = ∫ x, ∫ t, starRingEnd ℂ (g t) *
          (starRingEnd ℂ ((F : ℂ → ℂ) (x - t)) * (H : ℂ → ℂ) x) ∂volume ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [convCLM_apply_coeFn g hg F] with x hx
  rw [RCLike.inner_apply', hx, MeasureTheory.convolution_mul]
  calc (starRingEnd ℂ) (∫ (t : ℂ), g t * (F : ℂ → ℂ) (x - t)) * (H : ℂ → ℂ) x
      = (∫ t, starRingEnd ℂ (g t) * starRingEnd ℂ ((F : ℂ → ℂ) (x - t)) ∂volume)
          * (H : ℂ → ℂ) x := by
        congr 1
        rw [show (starRingEnd ℂ) (∫ (t : ℂ), g t * (F : ℂ → ℂ) (x - t))
            = ∫ t, (starRingEnd ℂ) (g t * (F : ℂ → ℂ) (x - t)) from (integral_conj).symm]
        apply integral_congr_ae; filter_upwards with t; rw [map_mul]
    _ = ∫ t, (starRingEnd ℂ (g t) * starRingEnd ℂ ((F : ℂ → ℂ) (x - t))) * (H : ℂ → ℂ) x
          ∂volume :=
        (integral_mul_const ((H : ℂ → ℂ) x) _).symm
    _ = ∫ t, starRingEnd ℂ (g t)
          * (starRingEnd ℂ ((F : ℂ → ℂ) (x - t)) * (H : ℂ → ℂ) x) ∂volume := by
        apply integral_congr_ae; filter_upwards with t; ring

/-- The right inner product `⟪F, g̃ ⋆ H⟫` as an iterated integral. -/
theorem rhs_eq (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F H : Lp ℂ 2 (volume : Measure ℂ)) :
    (inner ℂ F (convCLM (convKernelStar g) (memLp_convKernelStar hg) H) : ℂ)
      = ∫ y, ∫ t, starRingEnd ℂ ((F : ℂ → ℂ) y) *
          (starRingEnd ℂ (g (-t)) * (H : ℂ → ℂ) (y - t)) ∂volume ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [convCLM_apply_coeFn (convKernelStar g) (memLp_convKernelStar hg) H] with y hy
  rw [RCLike.inner_apply', hy, MeasureTheory.convolution_mul]
  have hstep : (∫ (t : ℂ), convKernelStar g t * (H : ℂ → ℂ) (y - t) ∂volume)
      = ∫ t, starRingEnd ℂ (g (-t)) * (H : ℂ → ℂ) (y - t) ∂volume := by
    apply integral_congr_ae; filter_upwards with t; simp only [convKernelStar]
  rw [hstep]
  exact (integral_const_mul ((starRingEnd ℂ) ((F : ℂ → ℂ) y)) _).symm

/-- `D_L` after Fubini (swap `x ↔ t`) and the substitution `x ↦ x + t`. -/
theorem dL_eq (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    (∫ x, ∫ t, starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x) ∂volume ∂volume)
      = ∫ t, ∫ x, starRingEnd ℂ (g t) * (starRingEnd ℂ (F x) * H (x + t)) ∂volume ∂volume := by
  have hLint : Integrable (Function.uncurry
      (fun x t => starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)))
      (volume.prod volume) := by
    have := (joint_int g F H hg hF hH).swap
    simpa [Function.uncurry, Function.comp, Prod.swap] using this
  rw [integral_integral_swap hLint]
  apply integral_congr_ae; filter_upwards with t
  rw [← integral_add_right_eq_self
      (fun x => starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)) t]
  apply integral_congr_ae; filter_upwards with x
  rw [show x + t - t = x by ring]

/-- `D_R` after Fubini (swap `y ↔ t`) and the substitution `t ↦ -t`. -/
theorem dR_eq (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    (∫ y, ∫ t, starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t)) ∂volume ∂volume)
      = ∫ t, ∫ x, starRingEnd ℂ (g t) * (starRingEnd ℂ (F x) * H (x + t)) ∂volume ∂volume := by
  have hRint : Integrable (Function.uncurry
      (fun y t => starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))))
      (volume.prod volume) := by
    simpa [Function.uncurry] using (joint_int2 g F H hg hF hH)
  rw [integral_integral_swap hRint]
  rw [← integral_neg_eq_self
      (fun t => ∫ y, starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t)) ∂volume)]
  apply integral_congr_ae; filter_upwards with t
  apply integral_congr_ae; filter_upwards with y
  rw [neg_neg, sub_neg_eq_add]; ring

/-- **The Hilbert adjoint of convolution-by-`g` is convolution-by-`g̃`,** where
`g̃ u = conj (g (-u))`. This identifies `(T_i)* T_j` as convolution by
`ψ̃_i ⋆ ψ_j`, the kernel whose `L¹` cancellation drives almost-orthogonality. -/
theorem adjoint_convCLM (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    ContinuousLinearMap.adjoint (convCLM g hg)
      = convCLM (convKernelStar g) (memLp_convKernelStar hg) := by
  have key : ∀ (F H : Lp ℂ 2 (volume : Measure ℂ)),
      inner ℂ (convCLM g hg F) H
        = inner ℂ F (convCLM (convKernelStar g) (memLp_convKernelStar hg) H) := by
    intro F H
    rw [lhs_eq g hg F H, rhs_eq g hg F H,
      (dL_eq g (F : ℂ → ℂ) (H : ℂ → ℂ) hg (Lp.memLp F) (Lp.memLp H)).trans
        (dR_eq g (F : ℂ → ℂ) (H : ℂ → ℂ) hg (Lp.memLp F) (Lp.memLp H)).symm]
  have hA : convCLM g hg
      = ContinuousLinearMap.adjoint (convCLM (convKernelStar g) (memLp_convKernelStar hg)) :=
    (ContinuousLinearMap.eq_adjoint_iff _ _).mpr key
  rw [← ContinuousLinearMap.adjoint_adjoint
        (convCLM (convKernelStar g) (memLp_convKernelStar hg))]
  exact congrArg ContinuousLinearMap.adjoint hA

/-! ### Dyadic almost-orthogonality assembly (Cotlar–Stein) -/

/-- The coercion `u ↦ (‖a u‖ : ℂ)` of a pointwise norm preserves membership in `Lᵖ`. -/
lemma memLp_coe_norm {a : ℂ → ℂ} {p : ℝ≥0∞} (ha : MemLp a p volume) :
    MemLp (fun u => (‖a u‖ : ℂ)) p volume := by
  refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable ha.1.norm, ?_⟩
  have : eLpNorm (fun u => ((‖a u‖ : ℝ) : ℂ)) p volume = eLpNorm a p volume := by
    apply eLpNorm_congr_norm_ae; filter_upwards with u; simp
  rw [this]; exact ha.2

/-- The real-valued convolution `‖b‖ ⋆ ‖F‖` exists at `x` whenever the complex one does. -/
lemma convExists_norm_of_complex {b F : ℂ → ℂ} {x : ℂ}
    (h : ConvolutionExistsAt b F x (ContinuousLinearMap.mul ℂ ℂ) volume) :
    ConvolutionExistsAt (fun u => ‖b u‖) (fun u => ‖F u‖) x
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  have hnorm : Integrable (fun t => ‖(ContinuousLinearMap.mul ℂ ℂ) (b t) (F (x - t))‖) volume :=
    h.norm
  simp only [ContinuousLinearMap.mul_apply', norm_mul] at hnorm
  show Integrable (fun t => (ContinuousLinearMap.mul ℝ ℝ) (‖b t‖) (‖F (x - t)‖)) volume
  simpa only [ContinuousLinearMap.mul_apply'] using hnorm

/-- The ℂ-convolution of the coerced norms equals the coercion of the real convolution. -/
lemma conv_coe_norm_eq {b F : ℂ → ℂ} (y : ℂ) :
    MeasureTheory.convolution (fun u => (‖b u‖:ℂ)) (fun u => (‖F u‖:ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume y
      = ((MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
          (ContinuousLinearMap.mul ℝ ℝ) volume y : ℝ) : ℂ) := by
  rw [MeasureTheory.convolution_mul, MeasureTheory.convolution_mul]
  simp only [← Complex.ofReal_mul]; exact integral_ofReal

/-- The real convolution of two pointwise norms is nonnegative. -/
lemma conv_norm_nonneg {b F : ℂ → ℂ} (y : ℂ) :
    0 ≤ MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
        (ContinuousLinearMap.mul ℝ ℝ) volume y := by
  rw [MeasureTheory.convolution_mul]; apply integral_nonneg; intro t; positivity

set_option maxHeartbeats 400000 in
/-- **Almost-everywhere associativity of convolution** for two `L¹` kernels and an `L²`
function: `(a ⋆ b) ⋆ F =ᵐ a ⋆ (b ⋆ F)`. Discharges the three integrability conditions of
`MeasureTheory.convolution_assoc` via the `L¹/L²` substrate. -/
lemma ae_convolution_assoc {a b : ℂ → ℂ} (ha : MemLp a 1 volume) (hb : MemLp b 1 volume)
    {F : ℂ → ℂ} (hF : MemLp F 2 volume) :
    MeasureTheory.convolution (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume)
        F (ContinuousLinearMap.mul ℂ ℂ) volume
      =ᵐ[volume]
        MeasureTheory.convolution a
          (MeasureTheory.convolution b F (ContinuousLinearMap.mul ℂ ℂ) volume)
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
  have hia : Integrable a volume := (memLp_one_iff_integrable).mp ha
  have hib : Integrable b volume := (memLp_one_iff_integrable).mp hb
  have hfg : ∀ᵐ y ∂volume, ConvolutionExistsAt a b y (ContinuousLinearMap.mul ℂ ℂ) volume :=
    hia.ae_convolution_exists _ hib
  have hgk : ∀ᵐ x ∂volume, ConvolutionExistsAt (fun u => ‖b u‖) (fun u => ‖F u‖) x
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    filter_upwards [ae_convolutionExistsAt hb hF] with x hx
    exact convExists_norm_of_complex hx
  have hA : MemLp (fun u => (‖a u‖:ℂ)) 1 volume := memLp_coe_norm ha
  have hB : MemLp (fun u => (‖b u‖:ℂ)) 1 volume := memLp_coe_norm hb
  have hΦ : MemLp (fun u => (‖F u‖:ℂ)) 2 volume := memLp_coe_norm hF
  have hBΦ : MemLp (MeasureTheory.convolution (fun u => (‖b u‖:ℂ)) (fun u => (‖F u‖:ℂ))
      (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume := memLp_convolution_two hB hΦ
  have hfgk_C : ∀ᵐ x ∂volume, ConvolutionExistsAt (fun u => (‖a u‖:ℂ))
      (MeasureTheory.convolution (fun u => (‖b u‖:ℂ)) (fun u => (‖F u‖:ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume) x (ContinuousLinearMap.mul ℂ ℂ) volume :=
    ae_convolutionExistsAt hA hBΦ
  have hfgk : ∀ᵐ x ∂volume, ConvolutionExistsAt (fun u => ‖a u‖)
      (MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
          (ContinuousLinearMap.mul ℝ ℝ) volume) x (ContinuousLinearMap.mul ℝ ℝ) volume := by
    filter_upwards [hfgk_C] with x hx
    have hxn := hx.norm
    simp only [ContinuousLinearMap.mul_apply', norm_mul, Complex.norm_real,
      conv_coe_norm_eq] at hxn
    show Integrable (fun t => (ContinuousLinearMap.mul ℝ ℝ) (‖a t‖)
      (MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
        (ContinuousLinearMap.mul ℝ ℝ) volume (x-t))) volume
    simp only [ContinuousLinearMap.mul_apply']
    refine hxn.congr ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs, abs_of_nonneg (conv_norm_nonneg _)]
  filter_upwards [hfgk] with x₀ hx_fgk
  exact MeasureTheory.convolution_assoc (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (fun x y z => by simp [mul_assoc]) ha.1 hb.1 hF.1 hfg hgk hx_fgk

/-- **`L¹ ⋆ L¹ ⊆ L¹`** (Young at exponent one): the convolution of two `L¹` functions is `L¹`. -/
lemma memLp_convolution_one {a b : ℂ → ℂ} (ha : MemLp a 1 volume) (hb : MemLp b 1 volume) :
    MemLp (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume := by
  have hia : Integrable a volume := (memLp_one_iff_integrable).mp ha
  have hib : Integrable b volume := (memLp_one_iff_integrable).mp hb
  exact (memLp_one_iff_integrable).mpr (hia.integrable_convolution _ hib)

/-- **Composition of convolution operators.** On `L²`, convolving by `a ∈ L¹` then by `b ∈ L¹`
equals convolving by `a ⋆ b`. -/
lemma convCLM_comp {a b : ℂ → ℂ} (ha : MemLp a 1 volume) (hb : MemLp b 1 volume) :
    (convCLM a ha) ∘L (convCLM b hb)
      = convCLM (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume)
          (memLp_convolution_one ha hb) := by
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
  have hL1 : ((convCLM a ha) ((convCLM b hb) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution a (((convCLM b hb) F : ℂ → ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    convCLM_apply_coeFn a ha _
  have hbF : ((convCLM b hb) F : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution b (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume :=
    convCLM_apply_coeFn b hb F
  have hL2 : MeasureTheory.convolution a (((convCLM b hb) F : ℂ → ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume
      = MeasureTheory.convolution a
        (MeasureTheory.convolution b (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
      (Filter.EventuallyEq.refl _ a) hbF
  have hR1 : ((convCLM (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume)
        (memLp_convolution_one ha hb) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution
        (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    convCLM_apply_coeFn _ _ F
  have hLHS : ((((convCLM a ha) ∘L (convCLM b hb)) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution a
        (MeasureTheory.convolution b (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    (show ((((convCLM a ha) ∘L (convCLM b hb)) F) : ℂ → ℂ)
        =ᵐ[volume] MeasureTheory.convolution a (((convCLM b hb) F : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume from hL1).trans (hL2 ▸ Filter.EventuallyEq.rfl)
  refine hLHS.trans ?_
  exact (ae_convolution_assoc ha hb hF).symm.trans hR1.symm

/-- **Young's convolution inequality `L¹ ⋆ L¹ → L¹`.** For `g, f ∈ L¹(ℂ)`,
`‖g ⋆ f‖₁ ≤ ‖g‖₁ ‖f‖₁`. Proved via Tonelli and translation invariance. -/
lemma eLpNorm_convolution_one_le {g f : ℂ → ℂ}
    (hg : MemLp g 1 volume) (hf : MemLp f 1 volume) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
      ≤ eLpNorm g 1 volume * eLpNorm f 1 volume := by
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  have hpt : ∀ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ
      ≤ ∫⁻ t, ‖g t‖ₑ * ‖f (x - t)‖ₑ ∂volume := by
    intro x
    rw [MeasureTheory.convolution_mul]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    apply lintegral_mono
    intro t
    simp only [enorm_mul, le_refl]
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hmono :
      (∫⁻ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ ∂volume)
        ≤ ∫⁻ x, (∫⁻ t, ‖g t‖ₑ * ‖f (x - t)‖ₑ ∂volume) ∂volume := by
    apply lintegral_mono
    exact hpt
  refine le_trans hmono ?_
  have hGmeas : AEMeasurable (Function.uncurry fun x t => ‖g t‖ₑ * ‖f (x - t)‖ₑ)
      (volume.prod volume) := by
    apply AEMeasurable.mul
    · exact hgm.comp_snd
    · have hsub : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact hsub.enorm
  rw [lintegral_lintegral_swap hGmeas]
  have hinner : ∀ t, (∫⁻ x, ‖g t‖ₑ * ‖f (x - t)‖ₑ ∂volume) = ‖g t‖ₑ * eLpNorm f 1 volume := by
    intro t
    rw [lintegral_const_mul'' _ (by
      have hsub : AEStronglyMeasurable (fun x : ℂ => f (x - t)) volume :=
        hfm.comp_quasiMeasurePreserving
          (measurePreserving_sub_right volume t).quasiMeasurePreserving
      exact hsub.enorm)]
    have htrans : eLpNorm (fun x => f (x - t)) 1 volume = eLpNorm f 1 volume :=
      eLpNorm_comp_measurePreserving hfm (measurePreserving_sub_right volume t)
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm] at htrans
    rw [eLpNorm_one_eq_lintegral_enorm]
    rw [htrans]
  rw [lintegral_congr hinner, lintegral_mul_const'' _ hgm, ← eLpNorm_one_eq_lintegral_enorm]

/-- **Trivial Young `L¹` bound for the cross-convolution.** Both `ψ̃_i ⋆ ψ_j` and
`ψ_i ⋆ ψ̃_j` have `L¹` mass at most `(2π log 2)²`, the product of the (equal) `L¹` masses of
the two factors. The universal, no-cancellation bound. -/
lemma eLpNorm_cross_le_sq (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    eLpNorm (MeasureTheory.convolution (convKernelStar (dyadicBeurling r i)) (dyadicBeurling r j)
        (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal ((2 * Real.pi * Real.log 2) ^ 2)
      ∧ eLpNorm (MeasureTheory.convolution (dyadicBeurling r i)
          (convKernelStar (dyadicBeurling r j))
          (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal ((2 * Real.pi * Real.log 2) ^ 2) := by
  have hψi := memLp_dyadicBeurling r hr i
  have hψj := memLp_dyadicBeurling r hr j
  have hgi := memLp_convKernelStar hψi
  have hgj := memLp_convKernelStar hψj
  have hni : eLpNorm (convKernelStar (dyadicBeurling r i)) 1 volume
      = ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
    rw [eLpNorm_convKernelStar _ hψi.1, eLpNorm_dyadicBeurling r hr i]
  have hnj : eLpNorm (convKernelStar (dyadicBeurling r j)) 1 volume
      = ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
    rw [eLpNorm_convKernelStar _ hψj.1, eLpNorm_dyadicBeurling r hr j]
  have hpos : (0:ℝ) ≤ 2 * Real.pi * Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    positivity
  refine ⟨?_, ?_⟩
  · refine (eLpNorm_convolution_one_le hgi hψj).trans ?_
    rw [hni, eLpNorm_dyadicBeurling r hr j, ← ENNReal.ofReal_mul hpos, ← sq]
  · refine (eLpNorm_convolution_one_le hψi hgj).trans ?_
    rw [hnj, eLpNorm_dyadicBeurling r hr i, ← ENNReal.ofReal_mul hpos, ← sq]

/-- The numeric comparison powering the small-separation case: `(2π log 2)² ≤ 4096·(1/2)^d`
whenever `d ≤ 7`. Indeed `(2π log 2)² ≤ 64` and `4096·(1/2)^7 = 32`, but `(2π log 2)² ≤ 32`
fails the trivial nlinarith bound, so we use the sharper `(2π log 2)² ≤ 64` only and require
`64 ≤ 4096·(1/2)^d`, i.e. `(1/2)^d ≥ 1/64`, i.e. `d ≤ 6`. We therefore split at `d ≤ 6`. -/
lemma sq_logmass_le (d : ℕ) (hd : d ≤ 6) :
    (2 * Real.pi * Real.log 2) ^ 2 ≤ 4096 * ((1:ℝ)/2) ^ d := by
  have hπ : Real.pi ≤ 4 := Real.pi_le_four
  have hlog2 : Real.log 2 ≤ 1 := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply le_of_lt
    apply Real.log_lt_log (by norm_num)
    have := Real.add_one_lt_exp (x := 1) (by norm_num)
    linarith
  have hπpos : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  have hlogpos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLHS : (2 * Real.pi * Real.log 2) ^ 2 ≤ 64 := by
    have hbase : 2 * Real.pi * Real.log 2 ≤ 8 := by
      nlinarith [hπpos, hlogpos, hπ, hlog2]
    have hbase_nn : (0:ℝ) ≤ 2 * Real.pi * Real.log 2 :=
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hπpos) hlogpos
    nlinarith [hbase, hbase_nn]
  have hRHS : (64:ℝ) ≤ 4096 * ((1:ℝ)/2) ^ d := by
    have hmono : ((1:ℝ)/2) ^ 6 ≤ ((1:ℝ)/2) ^ d :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
    have heq : (4096:ℝ) * ((1:ℝ)/2) ^ 6 = 64 := by norm_num
    nlinarith [hmono]
  linarith

/-- The unit-circle parametrization `e θ = cos θ + i sin θ`. -/
noncomputable def eCirc (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

lemma eCirc_norm (θ : ℝ) : ‖eCirc θ‖ = 1 := by
  rw [eCirc, Complex.norm_add_mul_I,
    show Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ]
  simp

lemma eCirc_ne_zero (θ : ℝ) : eCirc θ ≠ 0 := by
  rw [← norm_ne_zero_iff, eCirc_norm]; norm_num

/-- `e θ · conj (e θ) = 1`, so `(e θ)⁻¹ = conj (e θ)`. -/
lemma eCirc_mul_conj (θ : ℝ) : eCirc θ * (starRingEnd ℂ) (eCirc θ) = 1 := by
  have h : ‖eCirc θ‖ ^ 2 = 1 := by rw [eCirc_norm]; norm_num
  rw [Complex.mul_conj]
  rw [← Complex.normSq_eq_norm_sq] at h
  rw [show ((Complex.normSq (eCirc θ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) by rw [h]]; norm_num

lemma eCirc_inv (θ : ℝ) : (eCirc θ)⁻¹ = (starRingEnd ℂ) (eCirc θ) :=
  inv_eq_of_mul_eq_one_right (eCirc_mul_conj θ)

/-- The derivative of `e θ = cos θ + sin θ I` is `I · e θ`. -/
lemma eCirc_hasDerivAt (θ : ℝ) : HasDerivAt eCirc (I * eCirc θ) θ := by
  have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_cos θ).ofReal_comp
  have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_sin θ).ofReal_comp
  have hd : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ) + (Real.sin s : ℂ) * I)
      ((((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I) θ :=
    hcos.add (hsin.mul_const I)
  have hev : (((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I = I * eCirc θ := by
    rw [eCirc, Complex.ofReal_neg]
    linear_combination (-(Real.sin θ : ℂ)) * Complex.I_mul_I
  have : HasDerivAt eCirc ((((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I) θ := hd
  rwa [hev] at this

/-- The conjugate has derivative `-I · conj (e θ)`. -/
lemma eCirc_conj_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (eCirc t)) (-I * (starRingEnd ℂ) (eCirc θ)) θ := by
  have hconj_eq : (fun t : ℝ => (starRingEnd ℂ) (eCirc t))
      = fun t : ℝ => (Real.cos t : ℂ) - (Real.sin t : ℂ) * I := by
    funext t; rw [eCirc]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [hconj_eq]
  have hcos : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_cos θ).ofReal_comp
  have hsin : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_sin θ).ofReal_comp
  have hd := hcos.sub (hsin.mul_const I)
  convert hd using 1
  rw [eCirc]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  linear_combination (Real.sin θ : ℂ) * Complex.I_mul_I

/-- **The angular integral vanishes:** `∫_{-π}^{π} (conj (e θ))² dθ = 0`. The integrand has
the `2π`-periodic primitive `(I/2)(conj (e θ))²`, and `e π = e (-π) = -1`. -/
lemma angular_integral_eq_zero :
    (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (eCirc θ)) ^ 2) = 0 := by
  have hper : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (I / 2) * ((starRingEnd ℂ) (eCirc t)) ^ 2)
      (((starRingEnd ℂ) (eCirc s)) ^ 2) s := by
    intro s
    have h2 := ((eCirc_conj_hasDerivAt s).pow 2).const_mul (I / 2)
    convert h2 using 1
    have hps : (2:ℕ) - 1 = 1 := rfl
    rw [hps, pow_one]
    have hI2 : (I:ℂ) ^ 2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
    field_simp
    rw [hI2]; ring
  have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hper θ)]
  · have hπ : eCirc π = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    have hmπ : eCirc (-π) = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    rw [hπ, hmπ]; simp
  · apply Continuous.intervalIntegrable
    have hcont_e : Continuous eCirc := by unfold eCirc; fun_prop
    exact ((Complex.continuous_conj.comp hcont_e)).pow 2

/-- **General angular integral of a nonzero power of `e θ` vanishes:** for `n ≥ 1`,
`∫_{-π}^{π} (e θ)^n dθ = 0`. The primitive is `(e θ)^n / (n·I)` (since `(e θ)^n` has
derivative `n·I·(e θ)^n`), and `e π = e (-π) = -1` makes the boundary terms cancel. -/
lemma angular_integral_pow_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    (∫ θ in Set.Ioo (-π : ℝ) π, (eCirc θ) ^ n) = 0 := by
  have hnne : (n : ℂ) ≠ 0 := by
    have : (0:ℕ) < n := hn
    exact_mod_cast this.ne'
  have hni : (n : ℂ) * I ≠ 0 := mul_ne_zero hnne Complex.I_ne_zero
  -- Primitive `F θ = (e θ)^n / (n·I)` has derivative `(e θ)^n`.
  have hper : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (eCirc t) ^ n / ((n : ℂ) * I))
      ((eCirc s) ^ n) s := by
    intro s
    have hd : HasDerivAt (fun t : ℝ => (eCirc t) ^ n)
        ((n : ℂ) * (eCirc s) ^ (n - 1) * (I * eCirc s)) s :=
      (eCirc_hasDerivAt s).pow n
    have hd2 := hd.div_const ((n : ℂ) * I)
    convert hd2 using 1
    rw [eq_div_iff hni]
    have hns : (eCirc s) ^ (n - 1) * eCirc s = (eCirc s) ^ n := by
      rw [← pow_succ]; congr 1; omega
    have : (n : ℂ) * (eCirc s) ^ (n - 1) * (I * eCirc s)
        = (n : ℂ) * I * ((eCirc s) ^ (n - 1) * eCirc s) := by ring
    rw [this, hns]; ring
  have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hper θ)]
  · have hπ : eCirc π = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    have hmπ : eCirc (-π) = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    rw [hπ, hmπ]; simp
  · apply Continuous.intervalIntegrable
    have hcont_e : Continuous eCirc := by unfold eCirc; fun_prop
    exact hcont_e.pow n

/-- `polarCoord.symm p = p.1 • eCirc p.2` (the complex form of the polar symm map). -/
lemma polarCoord_symm_eq (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * eCirc p.2 := by
  rw [Complex.polarCoord_symm_apply, eCirc]

/-- **Mean-zero of the dyadic Beurling piece.** `∫_ℂ ψ_i = 0`. In polar coordinates the
integrand factors into a radial part (`ρ⁻¹`, integrable over `[2ⁱr, 2ⁱ⁺¹r)`) times the angular
part `(conj (e θ))²`, whose integral over a full turn vanishes. -/
lemma integral_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ u, dyadicBeurling r i u ∂volume = 0 := by
  classical
  set a := (2:ℝ)^i * r with ha_def
  set b := (2:ℝ)^(i+1) * r with hb_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have hab : a < b := by
    rw [ha_def, hb_def]
    apply mul_lt_mul_of_pos_right _ hr
    apply pow_lt_pow_right₀ (by norm_num) (by omega)
  have hb : 0 < b := ha.trans hab
  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [← Complex.integral_comp_polarCoord_symm (fun u => dyadicBeurling r i u)]
  set F : ℝ × ℝ → ℂ := fun p =>
    (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)) p.1 * ((starRingEnd ℂ) (eCirc p.2)) ^ 2
    with hF_def
  have hcongr : ∀ p ∈ (polarCoord.target : Set (ℝ × ℝ)),
      p.1 • dyadicBeurling r i (Complex.polarCoord.symm p) = F p := by
    intro p hp
    rw [htarget, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    obtain ⟨hp1, _⟩ := hp
    simp only [hF_def]
    rw [dyadicBeurling]
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hmem : Complex.polarCoord.symm p ∈
        {u : ℂ | (2:ℝ)^i * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(i+1) * r}
    · rw [Set.indicator_of_mem hmem]
      simp only [Set.mem_setOf_eq, hnorm, ← ha_def, ← hb_def] at hmem
      rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hmem.1, hmem.2⟩)]
      rw [polarCoord_symm_eq]
      have hp1ne : (p.1 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp1
      have heinv : (eCirc p.2)⁻¹ = (starRingEnd ℂ) (eCirc p.2) := eCirc_inv p.2
      rw [zpow_neg, zpow_two, mul_inv, ← heinv]
      rw [real_smul]
      field_simp
    · rw [Set.indicator_of_notMem hmem]
      simp only [Set.mem_setOf_eq, hnorm, ← ha_def, ← hb_def] at hmem
      rw [Set.indicator_of_notMem (by
        simp only [Set.mem_Ico, not_and, not_lt]
        intro h1; by_contra h2; exact hmem ⟨h1, not_le.mp h2⟩)]
      simp
  refine (setIntegral_congr_fun
    (by rw [htarget]; exact measurableSet_Ioi.prod measurableSet_Ioo) hcongr).trans ?_
  rw [htarget]
  have hfubini := MeasureTheory.setIntegral_prod_mul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)))
    (g := fun θ : ℝ => ((starRingEnd ℂ) (eCirc θ)) ^ 2)
    (Set.Ioi (0:ℝ)) (Set.Ioo (-π) π)
  have hang : (∫ θ in Set.Ioo (-π:ℝ) π, ((starRingEnd ℂ) (eCirc θ)) ^ 2) = 0 :=
    angular_integral_eq_zero
  calc (∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π, F p)
      = ∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π,
          (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)) p.1
            * ((starRingEnd ℂ) (eCirc p.2)) ^ 2 ∂(volume.prod volume) := by
            rw [Measure.volume_eq_prod ℝ ℝ]
    _ = (∫ x in Set.Ioi (0:ℝ), (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)) x)
          * ∫ y in Set.Ioo (-π:ℝ) π, ((starRingEnd ℂ) (eCirc y)) ^ 2 := hfubini
    _ = 0 := by rw [hang, mul_zero]

/-- The reflected/conjugated kernel `ψ̃_i = conj (ψ_i (-·))` is also mean-zero. -/
lemma integral_convKernelStar_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ u, convKernelStar (dyadicBeurling r i) u ∂volume = 0 := by
  unfold convKernelStar
  rw [show (∫ (u : ℂ), (starRingEnd ℂ) (dyadicBeurling r i (-u)) ∂volume)
      = (starRingEnd ℂ) (∫ (u : ℂ), dyadicBeurling r i (-u) ∂volume) from integral_conj]
  rw [integral_neg_eq_self (fun u => dyadicBeurling r i u) volume]
  rw [integral_dyadicBeurling_eq_zero r hr i, map_zero]

/-- **Polar separation of a radially-`ρ`-power × angular integral over an annulus.**
If a function `H : ℂ → ℂ` agrees on the annulus `{a ≤ ‖u‖ < b}` (and vanishes off it) with the
polar product `ρ^k · A(θ)` (i.e. `H (ρ • eCirc θ) = (ρ:ℂ)^k * A θ` on the target), then its
integral is `(∫_{[a,b)} ρ^{k+1} dρ) · (∫_{(-π,π)} A)`. When the angular integral `∫ A` vanishes,
so does `∫ H`. This is the abstract engine behind all the moment computations. -/
lemma integral_annulus_polar_factor (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (k : ℤ) (A : ℝ → ℂ)
    (H : ℂ → ℂ)
    (hzero : ∀ u : ℂ, ¬ (a ≤ ‖u‖ ∧ ‖u‖ < b) → H u = 0)
    (hpolar : ∀ ρ : ℝ, 0 < ρ → a ≤ ρ → ρ < b → ∀ θ : ℝ,
      H ((ρ : ℂ) * eCirc θ) = (ρ : ℂ) ^ k * A θ)
    (hAzero : (∫ θ in Set.Ioo (-π : ℝ) π, A θ) = 0) :
    ∫ u, H u ∂volume = 0 := by
  classical
  have hb : 0 < b := ha.trans hab
  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [← Complex.integral_comp_polarCoord_symm H]
  set F : ℝ × ℝ → ℂ := fun p =>
    (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))) p.1 * A p.2 with hF_def
  have hcongr : ∀ p ∈ (polarCoord.target : Set (ℝ × ℝ)),
      p.1 • H (Complex.polarCoord.symm p) = F p := by
    intro p hp
    rw [htarget, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    obtain ⟨hp1, _⟩ := hp
    simp only [hF_def]
    rw [polarCoord_symm_eq]
    have hnorm : ‖(p.1 : ℂ) * eCirc p.2‖ = p.1 := by
      rw [norm_mul, eCirc_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hp1.le]
    by_cases hmem : a ≤ p.1 ∧ p.1 < b
    · rw [hpolar p.1 hp1 hmem.1 hmem.2 p.2]
      rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hmem.1, hmem.2⟩)]
      rw [Complex.real_smul]
      rw [zpow_add_one₀ (by exact_mod_cast ne_of_gt hp1)]
      ring
    · rw [hzero _ (by rw [hnorm]; exact hmem)]
      rw [Set.indicator_of_notMem (by
        simp only [Set.mem_Ico, not_and, not_lt]
        intro h1; by_contra h2; exact hmem ⟨h1, not_le.mp h2⟩)]
      simp
  refine (setIntegral_congr_fun
    (by rw [htarget]; exact measurableSet_Ioi.prod measurableSet_Ioo) hcongr).trans ?_
  rw [htarget]
  have hfubini := MeasureTheory.setIntegral_prod_mul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))))
    (g := A) (Set.Ioi (0:ℝ)) (Set.Ioo (-π) π)
  calc (∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π, F p)
      = ∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π,
          (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))) p.1
            * A p.2 ∂(volume.prod volume) := by rw [Measure.volume_eq_prod ℝ ℝ]
    _ = (∫ x in Set.Ioi (0:ℝ), (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))) x)
          * ∫ y in Set.Ioo (-π:ℝ) π, A y := hfubini
    _ = 0 := by rw [hAzero, mul_zero]

/-- The polar value of `u·ψ_j` on the annulus is `ρ⁻¹·conj(e θ)`: helper computation. -/
lemma polar_value_id_mul (ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ) :
    ((ρ : ℂ) * eCirc θ) * ((ρ : ℂ) * eCirc θ) ^ (-2 : ℤ)
      = (ρ : ℂ) ^ (-1 : ℤ) * (starRingEnd ℂ) (eCirc θ) := by
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have heθ : eCirc θ ≠ 0 := eCirc_ne_zero θ
  rw [zpow_neg, zpow_two, mul_inv]
  rw [show ((ρ : ℂ) * eCirc θ) * (((ρ:ℂ)*eCirc θ)⁻¹ * ((ρ:ℂ)*eCirc θ)⁻¹)
      = (((ρ:ℂ)*eCirc θ) * ((ρ:ℂ)*eCirc θ)⁻¹) * ((ρ:ℂ)*eCirc θ)⁻¹ by ring]
  rw [mul_inv_cancel₀ (mul_ne_zero hρne heθ), one_mul, mul_inv, eCirc_inv]
  rw [zpow_neg, zpow_one]

/-- **First moment of the dyadic Beurling piece vanishes (holomorphic component):**
`∫ u · ψ_j(u) du = 0`. In polar the integrand is `ρ⁻¹ · conj(e θ)`, so the radial profile is
`ρ⁰ = 1` and the angular part `conj(e θ)` integrates to `conj(∫ e θ) = 0`
(`angular_integral_pow_eq_zero 1`). -/
lemma integral_id_mul_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∫ u, u * dyadicBeurling r j u ∂volume = 0 := by
  refine integral_annulus_polar_factor ((2:ℝ)^j * r) ((2:ℝ)^(j+1) * r) (by positivity)
    (by apply mul_lt_mul_of_pos_right _ hr; exact pow_lt_pow_right₀ (by norm_num) (by omega))
    (-1) (fun θ => (starRingEnd ℂ) (eCirc θ)) (fun u => u * dyadicBeurling r j u) ?_ ?_ ?_
  · -- vanishes off the annulus
    intro u hu
    have hu' : u ∉ {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := hu
    simp only [dyadicBeurling, Set.indicator_of_notMem hu', mul_zero]
  · -- polar value on the annulus
    intro ρ hρ hρa hρb θ
    simp only [dyadicBeurling]
    have hmem : (ρ : ℂ) * eCirc θ ∈
        {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := by
      have hnorm : ‖(ρ : ℂ) * eCirc θ‖ = ρ := by
        rw [norm_mul, eCirc_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      simp only [Set.mem_setOf_eq, hnorm]; exact ⟨hρa, hρb⟩
    rw [Set.indicator_of_mem hmem]
    exact polar_value_id_mul ρ hρ θ
  · -- angular integral vanishes: ∫ conj(e θ) = conj(∫ e θ) = conj(∫ (e θ)^1) = 0
    have hconj : (∫ θ in Set.Ioo (-π : ℝ) π, (starRingEnd ℂ) (eCirc θ))
        = (starRingEnd ℂ) (∫ θ in Set.Ioo (-π : ℝ) π, eCirc θ) :=
      integral_conj
    rw [hconj]
    have he1 : (∫ θ in Set.Ioo (-π : ℝ) π, eCirc θ)
        = ∫ θ in Set.Ioo (-π : ℝ) π, (eCirc θ) ^ 1 := by simp
    rw [he1, angular_integral_pow_eq_zero 1 (le_refl 1), map_zero]

/-- The polar value of `ū·ψ_j` on the annulus is `ρ⁻¹·conj((e θ)³)`: helper computation.
Here `ū = ρ·conj(e θ)` and `ψ_j = (ρ e θ)⁻²`, so the product is `ρ⁻¹·conj(e θ)·(e θ)⁻²
= ρ⁻¹·conj(e θ)³`. -/
lemma polar_value_conj_mul (ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ) :
    (starRingEnd ℂ) ((ρ : ℂ) * eCirc θ) * ((ρ : ℂ) * eCirc θ) ^ (-2 : ℤ)
      = (ρ : ℂ) ^ (-1 : ℤ) * ((starRingEnd ℂ) (eCirc θ)) ^ 3 := by
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have heθ : eCirc θ ≠ 0 := eCirc_ne_zero θ
  have hconjρ : (starRingEnd ℂ) (ρ : ℂ) = (ρ : ℂ) := Complex.conj_ofReal ρ
  have heinv : (eCirc θ)⁻¹ = (starRingEnd ℂ) (eCirc θ) := eCirc_inv θ
  rw [map_mul, hconjρ, zpow_neg, zpow_two, mul_inv, mul_inv, zpow_neg, zpow_one]
  rw [show ((ρ : ℂ) * (starRingEnd ℂ) (eCirc θ))
        * (((ρ:ℂ)⁻¹ * (eCirc θ)⁻¹) * ((ρ:ℂ)⁻¹ * (eCirc θ)⁻¹))
      = ((ρ:ℂ) * (ρ:ℂ)⁻¹) * (ρ:ℂ)⁻¹
        * ((starRingEnd ℂ) (eCirc θ) * (eCirc θ)⁻¹ * (eCirc θ)⁻¹) by ring]
  rw [mul_inv_cancel₀ hρne, one_mul, heinv]
  ring

/-- **First moment of the dyadic Beurling piece vanishes (anti-holomorphic component):**
`∫ ū · ψ_j(u) du = 0`. In polar the integrand is `ρ⁻¹ · conj((e θ)³)`, radial profile `ρ⁰=1`,
angular `conj((e θ)³)` integrates to `conj(∫ (e θ)³) = 0` (`angular_integral_pow_eq_zero 3`). -/
lemma integral_conj_mul_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∫ u, (starRingEnd ℂ) u * dyadicBeurling r j u ∂volume = 0 := by
  refine integral_annulus_polar_factor ((2:ℝ)^j * r) ((2:ℝ)^(j+1) * r) (by positivity)
    (by apply mul_lt_mul_of_pos_right _ hr; exact pow_lt_pow_right₀ (by norm_num) (by omega))
    (-1) (fun θ => ((starRingEnd ℂ) (eCirc θ)) ^ 3)
    (fun u => (starRingEnd ℂ) u * dyadicBeurling r j u) ?_ ?_ ?_
  · -- vanishes off the annulus
    intro u hu
    have hu' : u ∉ {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := hu
    simp only [dyadicBeurling, Set.indicator_of_notMem hu', mul_zero]
  · -- polar value on the annulus
    intro ρ hρ hρa hρb θ
    simp only [dyadicBeurling]
    have hmem : (ρ : ℂ) * eCirc θ ∈
        {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := by
      have hnorm : ‖(ρ : ℂ) * eCirc θ‖ = ρ := by
        rw [norm_mul, eCirc_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      simp only [Set.mem_setOf_eq, hnorm]; exact ⟨hρa, hρb⟩
    rw [Set.indicator_of_mem hmem]
    exact polar_value_conj_mul ρ hρ θ
  · -- angular integral vanishes
    rw [show (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (eCirc θ)) ^ 3)
        = ∫ θ in Set.Ioo (-π : ℝ) π, (starRingEnd ℂ) ((eCirc θ) ^ 3) by
          simp only [map_pow]]
    have hconj : (∫ θ in Set.Ioo (-π : ℝ) π, (starRingEnd ℂ) ((eCirc θ) ^ 3))
        = (starRingEnd ℂ) (∫ θ in Set.Ioo (-π : ℝ) π, (eCirc θ) ^ 3) :=
      integral_conj
    rw [hconj, angular_integral_pow_eq_zero 3 (by norm_num), map_zero]

/-- **First moment of the reflected kernel `ψ̃_i = conj(ψ_i(-·))` vanishes (holomorphic
component):** `∫ t · ψ̃_i(t) dt = 0`. Reduces to the anti-holomorphic first moment of `ψ_i`
via the reflection `t ↦ -t` (measure preserving) and `conj`. -/
lemma integral_id_mul_convKernelStar_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ t, t * convKernelStar (dyadicBeurling r i) t ∂volume = 0 := by
  unfold convKernelStar
  -- ∫ t·conj(ψ_i(-t)) = ∫ (-t)·conj(ψ_i t) (sub t↦-t) = -∫ conj(conj t · ψ_i t) = -conj 0 = 0
  rw [← integral_neg_eq_self (fun t => t * (starRingEnd ℂ) (dyadicBeurling r i (-t))) volume]
  have hcongr : (fun t => (fun s => s * (starRingEnd ℂ) (dyadicBeurling r i (-s))) (-t))
      = fun t => (starRingEnd ℂ) (-((starRingEnd ℂ) t * dyadicBeurling r i t)) := by
    funext t; simp only [neg_neg, map_neg, map_mul, Complex.conj_conj]; ring
  rw [hcongr]
  have hci : (∫ t, (starRingEnd ℂ) (-((starRingEnd ℂ) t * dyadicBeurling r i t)) ∂volume)
      = (starRingEnd ℂ) (∫ t, -((starRingEnd ℂ) t * dyadicBeurling r i t) ∂volume) :=
    integral_conj
  rw [hci, integral_neg, integral_conj_mul_dyadicBeurling_eq_zero r hr i, neg_zero, map_zero]

/-- **First moment of the reflected kernel `ψ̃_i` vanishes (anti-holomorphic component):**
`∫ conj(t) · ψ̃_i(t) dt = 0`. Reduces to the holomorphic first moment of `ψ_i`. -/
lemma integral_conj_mul_convKernelStar_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ t, (starRingEnd ℂ) t * convKernelStar (dyadicBeurling r i) t ∂volume = 0 := by
  unfold convKernelStar
  rw [← integral_neg_eq_self
    (fun t => (starRingEnd ℂ) t * (starRingEnd ℂ) (dyadicBeurling r i (-t))) volume]
  have hcongr : (fun t => (fun s => (starRingEnd ℂ) s * (starRingEnd ℂ) (dyadicBeurling r i (-s)))
      (-t)) = fun t => (starRingEnd ℂ) (-(t * dyadicBeurling r i t)) := by
    funext t; simp only [neg_neg, map_neg, map_mul]; ring
  rw [hcongr]
  have hci : (∫ t, (starRingEnd ℂ) (-(t * dyadicBeurling r i t)) ∂volume)
      = (starRingEnd ℂ) (∫ t, -(t * dyadicBeurling r i t) ∂volume) :=
    integral_conj
  rw [hci, integral_neg, integral_id_mul_dyadicBeurling_eq_zero r hr i, neg_zero, map_zero]

/-- **Mean-zero reduces convolution to a difference.** If the kernel `g ∈ L¹` has integral zero
and the convolution `(g ⋆ f)(x)` exists at `x`, then `(g ⋆ f)(x) = ∫ g(t)·(f(x - t) - f(x)) dt`.
This is the entry point of the MVT cancellation: the inserted `-g(t)·f(x)` integrates to
`-f(x)·∫ g = 0`. -/
lemma convolution_apply_eq_of_integral_zero {g f : ℂ → ℂ} (hg : MemLp g 1 volume)
    (hgz : ∫ t, g t ∂volume = 0) (x : ℂ)
    (hex : ConvolutionExistsAt g f x (ContinuousLinearMap.mul ℂ ℂ) volume) :
    MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x
      = ∫ t, g t * (f (x - t) - f x) ∂volume := by
  rw [MeasureTheory.convolution_mul]
  have hgint : Integrable g volume := (memLp_one_iff_integrable).mp hg
  have hint1 : Integrable (fun t => g t * f (x - t)) volume := by
    have := hex
    rw [ConvolutionExistsAt] at this
    simpa [ContinuousLinearMap.mul_apply'] using this
  have hint2 : Integrable (fun t => g t * f x) volume := hgint.mul_const _
  have hsub : (fun t => g t * (f (x - t) - f x)) = (fun t => g t * f (x - t) - g t * f x) := by
    funext t; ring
  have hzero2 : (∫ t, g t * f x ∂volume) = 0 := by
    have h2 : (∫ t, g t * f x ∂volume) = (∫ t, g t ∂volume) * f x :=
      integral_mul_const (f x) g
    rw [h2, hgz, zero_mul]
  rw [hsub, integral_sub hint1 hint2, hzero2, sub_zero]

/-- **Modulus-of-continuity Fubini reduction.** For a mean-zero `L¹` kernel `g` and `L¹`
function `f`, the `L¹` mass of `g ⋆ f` is controlled by the `g`-weighted integral of the
first-order modulus of continuity `ω_f(t) = ∫ ‖f(·-t) - f‖`. This is the entry point that
converts cancellation (mean-zero) into geometric decay. -/
lemma eLpNorm_convolution_meanZero_le {g f : ℂ → ℂ}
    (hg : MemLp g 1 volume) (hf : MemLp f 1 volume) (hgz : ∫ t, g t ∂volume = 0) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
      ≤ ∫⁻ t, ‖g t‖ₑ * (∫⁻ x, ‖f (x - t) - f x‖ₑ ∂volume) ∂volume := by
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  have hgint : Integrable g volume := (memLp_one_iff_integrable).mp hg
  have hfint : Integrable f volume := (memLp_one_iff_integrable).mp hf
  -- a.e. existence of the convolution (L¹ ⋆ L¹).
  have hex : ∀ᵐ x ∂volume,
      ConvolutionExistsAt g f x (ContinuousLinearMap.mul ℂ ℂ) volume :=
    hgint.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ) hfint
  -- pointwise a.e. bound on the convolution enorm.
  have hpt : ∀ᵐ x ∂volume,
      ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ
        ≤ ∫⁻ t, ‖g t‖ₑ * ‖f (x - t) - f x‖ₑ ∂volume := by
    filter_upwards [hex] with x hxe
    rw [convolution_apply_eq_of_integral_zero hg hgz x hxe]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    apply lintegral_mono
    intro t
    simp only [enorm_mul, le_refl]
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hmono :
      (∫⁻ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ ∂volume)
        ≤ ∫⁻ x, (∫⁻ t, ‖g t‖ₑ * ‖f (x - t) - f x‖ₑ ∂volume) ∂volume :=
    lintegral_mono_ae hpt
  refine le_trans hmono ?_
  -- Fubini swap.
  have hGmeas : AEMeasurable
      (Function.uncurry fun x t => ‖g t‖ₑ * ‖f (x - t) - f x‖ₑ) (volume.prod volume) := by
    apply AEMeasurable.mul
    · exact hgm.comp_snd
    · have hsub1 : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      have hsub2 : AEStronglyMeasurable (fun p : ℂ × ℂ => f p.1) (volume.prod volume) :=
        hfm.comp_fst
      exact (hsub1.sub hsub2).enorm
  rw [lintegral_lintegral_swap hGmeas]
  apply lintegral_mono
  intro t
  simp only
  rw [lintegral_const_mul'' _ (by
    have hsub1 : AEStronglyMeasurable (fun x : ℂ => f (x - t)) volume :=
      hfm.comp_quasiMeasurePreserving
        (measurePreserving_sub_right volume t).quasiMeasurePreserving
    exact (hsub1.sub hfm).enorm)]

/-- **Pointwise value-variation bound.** For `P, Q ∈ ℂ` with `Q = P + t`,
`‖P⁻² - Q⁻²‖ ≤ ‖t‖·‖P+Q‖ / (‖P‖²·‖Q‖²)`. Pure algebra: `P⁻²-Q⁻² = (Q²-P²)/(P²Q²)` and
`Q²-P² = (Q-P)(Q+P)`. -/
lemma norm_zpow_neg_two_sub_le {P Q : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ‖P ^ (-2 : ℤ) - Q ^ (-2 : ℤ)‖ ≤ ‖Q - P‖ * ‖P + Q‖ / (‖P‖ ^ 2 * ‖Q‖ ^ 2) := by
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ hP
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero _ hQ
  have hid : P ^ (-2 : ℤ) - Q ^ (-2 : ℤ) = (Q - P) * (P + Q) / (P ^ 2 * Q ^ 2) := by
    rw [zpow_neg, zpow_neg, zpow_two, zpow_two]
    field_simp
    ring
  rw [hid, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]

/-- The annular shell `{c ≤ ‖x‖ < d}` equals `ball 0 d \ ball 0 c`. -/
lemma shell_eq_ball_diff (c d : ℝ) :
    {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d} = Metric.ball (0 : ℂ) d \ Metric.ball (0 : ℂ) c := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_diff, Metric.mem_ball, dist_zero_right, not_lt]
  tauto

/-- **Volume of an annular shell.** For `0 ≤ c ≤ d`, the shell `{c ≤ ‖x‖ < d}` has volume
`ofReal (d²·π) - ofReal (c²·π)`. -/
lemma volume_shell (c d : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    volume {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d}
      = ENNReal.ofReal (d ^ 2 * Real.pi) - ENNReal.ofReal (c ^ 2 * Real.pi) := by
  have hd : 0 ≤ d := hc.trans hcd
  rw [shell_eq_ball_diff]
  rw [measure_diff (Metric.ball_subset_ball hcd) measurableSet_ball.nullMeasurableSet]
  · rw [Complex.volume_ball, Complex.volume_ball]
    have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi]
    congr 1
    · rw [← ENNReal.ofReal_pow hd, ← ENNReal.ofReal_mul (by positivity)]
    · rw [← ENNReal.ofReal_pow hc, ← ENNReal.ofReal_mul (by positivity)]
  · rw [Complex.volume_ball]
    exact ne_top_of_lt (ENNReal.mul_lt_top (by simp) (by simp))

/-- **Volume of an annular shell, packaged form.** For `0 ≤ c ≤ d`, the shell `{c ≤ ‖x‖ < d}`
has volume `ofReal ((d²-c²)·π)`. -/
lemma volume_shell' (c d : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    volume {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d} = ENNReal.ofReal ((d ^ 2 - c ^ 2) * Real.pi) := by
  rw [volume_shell c d hc hcd, ← ENNReal.ofReal_sub _ (by positivity), sub_mul]

/-- The annular shell `{c ≤ ‖x‖ < d}` is measurable. -/
lemma measurableSet_shell (c d : ℝ) :
    MeasurableSet {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d} := by
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const measurable_norm
  · exact measurableSet_lt measurable_norm measurable_const

/-- **Pointwise modulus-of-continuity bound for a dyadic piece.** With `R₁ = 2ᵐr`,
`R₂ = 2ᵐ⁺¹r`, `A` the annulus, `B = A + t`, and `S` the two boundary shells thickened by `‖t‖`,
the pointwise difference `‖ψ(x-t) - ψ(x)‖ₑ` is bounded by a value-variation term supported on
`B` plus a boundary-jump term supported on `S`. -/
lemma omega_pointwise_le (r : ℝ) (hr : 0 < r) (m : ℕ) (t : ℂ)
    (ht : 2 * ‖t‖ ≤ (2:ℝ)^m * r) (x : ℂ) :
    ‖dyadicBeurling r m (x - t) - dyadicBeurling r m x‖ₑ
      ≤ Set.indicator {x : ℂ | (2:ℝ)^m * r ≤ ‖x - t‖ ∧ ‖x - t‖ < (2:ℝ)^(m+1) * r}
          (fun _ => ENNReal.ofReal (24 * ‖t‖ / ((2:ℝ)^m * r) ^ 3)) x
        + Set.indicator
            ({x : ℂ | (2:ℝ)^m * r - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^m * r + ‖t‖}
              ∪ {x : ℂ | (2:ℝ)^(m+1) * r - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(m+1) * r + ‖t‖})
            (fun _ => ENNReal.ofReal (4 / ((2:ℝ)^m * r) ^ 2)) x := by
  set R₁ : ℝ := (2:ℝ)^m * r with hR₁
  set R₂ : ℝ := (2:ℝ)^(m+1) * r with hR₂
  have hR₁pos : 0 < R₁ := by rw [hR₁]; positivity
  have hR₂eq : R₂ = 2 * R₁ := by rw [hR₂, hR₁, pow_succ]; ring
  have htle : ‖t‖ ≤ R₁ / 2 := by rw [hR₁] at ht ⊢; linarith
  have htnn : 0 ≤ ‖t‖ := norm_nonneg t
  set A : Set ℂ := {u : ℂ | R₁ ≤ ‖u‖ ∧ ‖u‖ < R₂}
  set B : Set ℂ := {x : ℂ | R₁ ≤ ‖x - t‖ ∧ ‖x - t‖ < R₂}
  set Inner : Set ℂ := {x : ℂ | R₁ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₁ + ‖t‖}
  set Outer : Set ℂ := {x : ℂ | R₂ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₂ + ‖t‖}
  -- enorm difference of indicators of `u^(-2)`.
  have hψ : ∀ u : ℂ, dyadicBeurling r m u = Set.indicator A (fun u => u ^ (-2:ℤ)) u := by
    intro u; rfl
  -- membership predicates
  have hPmem : (x - t ∈ A) ↔ (R₁ ≤ ‖x - t‖ ∧ ‖x - t‖ < R₂) := Iff.rfl
  have hQmem : (x ∈ A) ↔ (R₁ ≤ ‖x‖ ∧ ‖x‖ < R₂) := Iff.rfl
  by_cases hP : x - t ∈ A
  · by_cases hQ : x ∈ A
    · -- both in A: value-variation bound, x ∈ B.
      rw [hψ, hψ, Set.indicator_of_mem hP, Set.indicator_of_mem hQ]
      have hPne : (x - t) ≠ 0 := by
        intro h; have := hP.1; rw [h, norm_zero] at this; linarith
      have hQne : x ≠ 0 := by
        intro h; have := hQ.1; rw [h, norm_zero] at this; linarith
      have hnormP : R₁ ≤ ‖x - t‖ := hP.1
      have hnormP2 : ‖x - t‖ < R₂ := hP.2
      have hnormQ : R₁ ≤ ‖x‖ := hQ.1
      -- pointwise value bound: ‖(x-t)^(-2) - x^(-2)‖ ≤ 24‖t‖/R₁³.
      have hval : ‖(x - t) ^ (-2:ℤ) - x ^ (-2:ℤ)‖ ≤ 24 * ‖t‖ / R₁ ^ 3 := by
        refine (norm_zpow_neg_two_sub_le hPne hQne).trans ?_
        -- ‖x - (x-t)‖ = ‖t‖, ‖(x-t)+x‖ ≤ ‖x-t‖+‖x‖
        have hdiff : ‖x - (x - t)‖ = ‖t‖ := by rw [sub_sub_cancel]
        have hsum : ‖(x - t) + x‖ ≤ ‖x - t‖ + ‖x‖ := norm_add_le _ _
        have hxub : ‖x‖ ≤ R₂ + ‖t‖ := by
          calc ‖x‖ = ‖(x - t) + t‖ := by ring_nf
            _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
            _ ≤ R₂ + ‖t‖ := by linarith
        have hsum2 : ‖(x - t) + x‖ ≤ R₂ + (R₂ + ‖t‖) := by
          refine hsum.trans ?_; linarith [hnormP2, hxub]
        -- numerator ≤ ‖t‖·(2R₂+‖t‖), denominator ≥ R₁²·R₁² (since ‖x‖ ≥ R₁)
        rw [hdiff]
        have hPnn : 0 ≤ ‖x - t‖ := norm_nonneg _
        have hQnn : 0 ≤ ‖x‖ := norm_nonneg _
        have hnum : ‖t‖ * ‖(x - t) + x‖ ≤ ‖t‖ * (R₂ + (R₂ + ‖t‖)) :=
          mul_le_mul_of_nonneg_left hsum2 htnn
        have hden : R₁ ^ 2 * R₁ ^ 2 ≤ ‖x - t‖ ^ 2 * ‖x‖ ^ 2 := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ hR₁pos.le hnormP 2
          · exact pow_le_pow_left₀ hR₁pos.le hnormQ 2
          · positivity
          · positivity
        -- clear denominators: a/b ≤ c/d  ⇐  a*d ≤ c*b with b,d > 0.
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc ‖t‖ * ‖(x - t) + x‖ * R₁ ^ 3
            ≤ (‖t‖ * (R₂ + (R₂ + ‖t‖))) * R₁ ^ 3 :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
          _ ≤ 24 * ‖t‖ * (R₁ ^ 2 * R₁ ^ 2) := by
              rw [hR₂eq]
              have hR3 : (0:ℝ) ≤ R₁ ^ 3 := by positivity
              have hkey : ‖t‖ * (2 * R₁ + (2 * R₁ + ‖t‖)) ≤ 24 * ‖t‖ * R₁ := by
                nlinarith [hR₁pos, htle, htnn]
              have : R₁ ^ 2 * R₁ ^ 2 = R₁ * R₁ ^ 3 := by ring
              rw [this]
              calc ‖t‖ * (2 * R₁ + (2 * R₁ + ‖t‖)) * R₁ ^ 3
                  ≤ (24 * ‖t‖ * R₁) * R₁ ^ 3 := mul_le_mul_of_nonneg_right hkey hR3
                _ = 24 * ‖t‖ * (R₁ * R₁ ^ 3) := by ring
          _ ≤ 24 * ‖t‖ * (‖x - t‖ ^ 2 * ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hden (by positivity)
      rw [Set.indicator_of_mem (show x ∈ B from hP)]
      calc ‖(x - t) ^ (-2:ℤ) - x ^ (-2:ℤ)‖ₑ
          = ENNReal.ofReal ‖(x - t) ^ (-2:ℤ) - x ^ (-2:ℤ)‖ := (ofReal_norm_eq_enorm _).symm
        _ ≤ ENNReal.ofReal (24 * ‖t‖ / R₁ ^ 3) := ENNReal.ofReal_le_ofReal hval
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · -- x-t ∈ A, x ∉ A: boundary term active (x ∈ S), value `(x-t)^(-2)`.
      rw [hψ, hψ, Set.indicator_of_mem hP, Set.indicator_of_notMem hQ, sub_zero]
      have hnormP : R₁ ≤ ‖x - t‖ := hP.1
      have hnormP2 : ‖x - t‖ < R₂ := hP.2
      -- enorm value bound `‖(x-t)^(-2)‖ₑ ≤ ofReal (4 / R₁²)`.
      have hvalbd : ‖(x - t) ^ (-2:ℤ)‖ₑ ≤ ENNReal.ofReal (4 / R₁ ^ 2) := by
        rw [← ofReal_norm_eq_enorm, norm_zpow]
        apply ENNReal.ofReal_le_ofReal
        rw [zpow_neg, zpow_two]
        have hsq : R₁ * R₁ ≤ ‖x - t‖ * ‖x - t‖ := by nlinarith [hR₁pos, hnormP, norm_nonneg (x - t)]
        calc (‖x - t‖ * ‖x - t‖)⁻¹ ≤ (R₁ * R₁)⁻¹ := inv_anti₀ (by positivity) hsq
          _ ≤ 4 / R₁ ^ 2 := by
              rw [div_eq_mul_inv, sq]
              nlinarith [inv_nonneg.mpr (mul_nonneg hR₁pos.le hR₁pos.le)]
      -- membership x ∈ S.
      have hQA : ‖x‖ < R₁ ∨ R₂ ≤ ‖x‖ := by
        rcases le_or_gt R₁ ‖x‖ with h | h
        · rcases lt_or_ge ‖x‖ R₂ with h2 | h2
          · exact absurd ⟨h, h2⟩ hQ
          · exact Or.inr h2
        · exact Or.inl h
      have hxsub : ‖x - t‖ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ ≤ ‖x - t‖ + ‖t‖ := by
        constructor
        · have := norm_sub_norm_le (x - t) x
          rw [show (x - t) - x = -t by ring, norm_neg] at this; linarith
        · calc ‖x‖ = ‖(x - t) + t‖ := by ring_nf
            _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
      have hmemS : x ∈ Inner ∪ Outer := by
        rcases hQA with h | h
        · left
          refine ⟨?_, ?_⟩
          · linarith [hxsub.1, hnormP]
          · linarith [h]
        · right
          refine ⟨?_, ?_⟩
          · linarith [h]
          · linarith [hxsub.2, hnormP2]
      rw [Set.indicator_of_mem (show x ∈ Inner ∪ Outer from hmemS)]
      exact le_add_of_nonneg_of_le (by positivity) hvalbd
  · by_cases hQ : x ∈ A
    · -- x-t ∉ A, x ∈ A: boundary term active (x ∈ S), value `-x^(-2)`.
      rw [hψ, hψ, Set.indicator_of_notMem hP, Set.indicator_of_mem hQ, zero_sub, enorm_neg]
      have hnormQ : R₁ ≤ ‖x‖ := hQ.1
      have hnormQ2 : ‖x‖ < R₂ := hQ.2
      have hvalbd : ‖x ^ (-2:ℤ)‖ₑ ≤ ENNReal.ofReal (4 / R₁ ^ 2) := by
        rw [← ofReal_norm_eq_enorm, norm_zpow]
        apply ENNReal.ofReal_le_ofReal
        rw [zpow_neg, zpow_two]
        have hsq : R₁ * R₁ ≤ ‖x‖ * ‖x‖ := by nlinarith [hR₁pos, hnormQ, norm_nonneg x]
        calc (‖x‖ * ‖x‖)⁻¹ ≤ (R₁ * R₁)⁻¹ := inv_anti₀ (by positivity) hsq
          _ ≤ 4 / R₁ ^ 2 := by
              rw [div_eq_mul_inv, sq]
              nlinarith [inv_nonneg.mpr (mul_nonneg hR₁pos.le hR₁pos.le)]
      have hPA : ‖x - t‖ < R₁ ∨ R₂ ≤ ‖x - t‖ := by
        rcases le_or_gt R₁ ‖x - t‖ with h | h
        · rcases lt_or_ge ‖x - t‖ R₂ with h2 | h2
          · exact absurd ⟨h, h2⟩ hP
          · exact Or.inr h2
        · exact Or.inl h
      have hxsub : ‖x‖ - ‖t‖ ≤ ‖x - t‖ ∧ ‖x - t‖ ≤ ‖x‖ + ‖t‖ := by
        constructor
        · have := norm_sub_norm_le x (x - t); rw [sub_sub_cancel] at this; linarith
        · have := norm_add_le x (-t); rw [show x + -t = x - t by ring, norm_neg] at this; linarith
      have hmemS : x ∈ Inner ∪ Outer := by
        rcases hPA with h | h
        · left
          refine ⟨?_, ?_⟩
          · linarith [hnormQ]
          · linarith [hxsub.2, h]
        · right
          refine ⟨?_, ?_⟩
          · linarith [hxsub.1, h]
          · linarith [hnormQ2]
      rw [Set.indicator_of_mem (show x ∈ Inner ∪ Outer from hmemS)]
      exact le_add_of_nonneg_of_le (by positivity) hvalbd
    · -- neither in A: difference is 0.
      rw [hψ, hψ, Set.indicator_of_notMem hP, Set.indicator_of_notMem hQ, sub_zero, enorm_zero]
      positivity

/-- **First-order modulus of continuity of a dyadic piece.** For a translation `t` with
`2‖t‖ ≤ 2ᵐr` (so the segment stays in the annulus and the boundary layer is thin), the `L¹`
modulus `∫ ‖ψₘ(·-t) - ψₘ‖` is `≤ 120π·‖t‖/(2ᵐr)`, linear in `‖t‖`. This is the quantitative
smoothness that, paired with mean-zero, yields the geometric almost-orthogonality decay. -/
lemma omega_dyadicBeurling_le (r : ℝ) (hr : 0 < r) (m : ℕ) (t : ℂ)
    (ht : 2 * ‖t‖ ≤ (2:ℝ)^m * r) :
    (∫⁻ x, ‖dyadicBeurling r m (x - t) - dyadicBeurling r m x‖ₑ ∂volume)
      ≤ ENNReal.ofReal (120 * Real.pi * ‖t‖ / ((2:ℝ)^m * r)) := by
  set R₁ : ℝ := (2:ℝ)^m * r with hR₁
  set R₂ : ℝ := (2:ℝ)^(m+1) * r with hR₂
  have hR₁pos : 0 < R₁ := by rw [hR₁]; positivity
  have hR₂eq : R₂ = 2 * R₁ := by rw [hR₂, hR₁, pow_succ]; ring
  have htle : ‖t‖ ≤ R₁ / 2 := by rw [hR₁] at ht ⊢; linarith
  have htnn : 0 ≤ ‖t‖ := norm_nonneg t
  set B : Set ℂ := {x : ℂ | R₁ ≤ ‖x - t‖ ∧ ‖x - t‖ < R₂} with hB
  set Inner : Set ℂ := {x : ℂ | R₁ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₁ + ‖t‖} with hInner
  set Outer : Set ℂ := {x : ℂ | R₂ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₂ + ‖t‖} with hOuter
  -- Bound the integrand pointwise by the value+boundary terms.
  have hpt := fun x => omega_pointwise_le r hr m t ht x
  refine le_trans (lintegral_mono hpt) ?_
  -- split the integral of the sum.
  have hBmeas : MeasurableSet B := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const (measurable_norm.comp (measurable_id.sub_const t))
    · exact measurableSet_lt (measurable_norm.comp (measurable_id.sub_const t)) measurable_const
  have hSmeas : MeasurableSet (Inner ∪ Outer) :=
    (measurableSet_shell _ _).union (measurableSet_shell _ _)
  rw [lintegral_add_left
    ((measurable_const.indicator hBmeas))]
  rw [lintegral_indicator_const hBmeas, lintegral_indicator_const hSmeas]
  -- volume B = volume of annulus shell R₁..R₂.
  have hvolB : volume B = ENNReal.ofReal ((R₂ ^ 2 - R₁ ^ 2) * Real.pi) := by
    have hpre : B = (fun x : ℂ => x - t) ⁻¹' {y : ℂ | R₁ ≤ ‖y‖ ∧ ‖y‖ < R₂} := rfl
    rw [hpre, (measurePreserving_sub_right volume t).measure_preimage
      (measurableSet_shell _ _).nullMeasurableSet]
    exact volume_shell' R₁ R₂ hR₁pos.le (by rw [hR₂eq]; linarith)
  -- bound volume (Inner ∪ Outer) by sum of the two shells.
  have hvolS : volume (Inner ∪ Outer)
      ≤ ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) + ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi) := by
    refine (measure_union_le _ _).trans ?_
    have hvolI : volume Inner = ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) := by
      rw [hInner, volume_shell' (R₁ - ‖t‖) (R₁ + ‖t‖) (by linarith) (by linarith)]
      congr 1; ring
    have hvolO : volume Outer = ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi) := by
      rw [hOuter, volume_shell' (R₂ - ‖t‖) (R₂ + ‖t‖) (by rw [hR₂eq]; linarith) (by linarith)]
      rw [hR₂eq]; congr 1; ring
    rw [hvolI, hvolO]
  -- combine.
  rw [hvolB]
  have hval_bound :
      ENNReal.ofReal (24 * ‖t‖ / R₁ ^ 3) * ENNReal.ofReal ((R₂ ^ 2 - R₁ ^ 2) * Real.pi)
        ≤ ENNReal.ofReal (72 * Real.pi * ‖t‖ / R₁) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hR₂eq, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hR₁pos]
    nlinarith [hR₁pos, htnn, Real.pi_pos]
  have hbdy_bound :
      ENNReal.ofReal (4 / R₁ ^ 2)
          * (ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) + ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi))
        ≤ ENNReal.ofReal (48 * Real.pi * ‖t‖ / R₁) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hR₁pos]
    nlinarith [hR₁pos, Real.pi_pos, htnn]
  calc ENNReal.ofReal (24 * ‖t‖ / R₁ ^ 3) * ENNReal.ofReal ((R₂ ^ 2 - R₁ ^ 2) * Real.pi)
        + ENNReal.ofReal (4 / R₁ ^ 2) * volume (Inner ∪ Outer)
      ≤ ENNReal.ofReal (72 * Real.pi * ‖t‖ / R₁)
          + ENNReal.ofReal (4 / R₁ ^ 2)
            * (ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) + ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi)) :=
        add_le_add hval_bound (mul_le_mul_left' hvolS _)
    _ ≤ ENNReal.ofReal (72 * Real.pi * ‖t‖ / R₁) + ENNReal.ofReal (48 * Real.pi * ‖t‖ / R₁) :=
        add_le_add le_rfl hbdy_bound
    _ = ENNReal.ofReal (120 * Real.pi * ‖t‖ / R₁) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **Support of a dyadic piece.** Outside the annulus `[2ᵃr, 2ᵃ⁺¹r)` the dyadic piece
vanishes. -/
lemma enorm_dyadicBeurling_eq_zero_of_large (r : ℝ) (a : ℕ) (t : ℂ)
    (ht : (2:ℝ)^(a+1) * r ≤ ‖t‖) : ‖dyadicBeurling r a t‖ₑ = 0 := by
  rw [enorm_dyadicBeurling]
  rw [Set.indicator_of_notMem]
  intro hmem
  exact absurd hmem.2 (not_lt.mpr ht)

/-- The dyadic piece is measurable. -/
lemma measurable_dyadicBeurling (r : ℝ) (b : ℕ) : Measurable (dyadicBeurling r b) := by
  apply Measurable.indicator _ (measurableSet_dyadicAnnulus r b)
  have : (fun u : ℂ => u ^ (-2 : ℤ)) = (fun u : ℂ => (u * u)⁻¹) := by
    funext u; rw [zpow_neg, zpow_two]
  rw [this]
  exact (measurable_id.mul measurable_id).inv

/-- **Support of the reflected kernel.** Outside the annulus the reflected kernel vanishes. -/
lemma enorm_convKernelStar_dyadicBeurling_eq_zero_of_large (r : ℝ) (a : ℕ) (t : ℂ)
    (ht : (2:ℝ)^(a+1) * r ≤ ‖t‖) : ‖convKernelStar (dyadicBeurling r a) t‖ₑ = 0 := by
  rw [convKernelStar, RCLike.enorm_conj]
  exact enorm_dyadicBeurling_eq_zero_of_large r a (-t) (by rwa [norm_neg])

/-- **First-order modulus of continuity of the reflected kernel.** Reduces to the dyadic-piece
estimate by the reflection `x ↦ -x` (measure preserving) and conjugation. -/
lemma omega_convKernelStar_le (r : ℝ) (hr : 0 < r) (b : ℕ) (s : ℂ)
    (hs : 2 * ‖s‖ ≤ (2:ℝ)^b * r) :
    (∫⁻ x, ‖convKernelStar (dyadicBeurling r b) (x - s)
        - convKernelStar (dyadicBeurling r b) x‖ₑ ∂volume)
      ≤ ENNReal.ofReal (120 * Real.pi * ‖s‖ / ((2:ℝ)^b * r)) := by
  -- pointwise: ‖K(x-s) - K(x)‖ₑ = ‖ψ(s-x) - ψ(-x)‖ₑ.
  have hpt : ∀ x : ℂ, ‖convKernelStar (dyadicBeurling r b) (x - s)
      - convKernelStar (dyadicBeurling r b) x‖ₑ
      = ‖dyadicBeurling r b ((-x) - (-s)) - dyadicBeurling r b (-x)‖ₑ := by
    intro x
    rw [convKernelStar, convKernelStar]
    rw [show -(x - s) = (-x) - (-s) by ring]
    rw [← map_sub, RCLike.enorm_conj]
  simp_rw [hpt]
  -- change of variables y = -x (measure preserving negation).
  set F : ℂ → ℝ≥0∞ := fun y => ‖dyadicBeurling r b (y - (-s)) - dyadicBeurling r b y‖ₑ with hF
  have hFmeas : Measurable F := by
    apply Measurable.enorm
    apply Measurable.sub
    · exact (measurable_dyadicBeurling r b).comp (measurable_id.sub_const (-s))
    · exact measurable_dyadicBeurling r b
  have hcomp : (∫⁻ x, F (-x) ∂volume) = ∫⁻ y, F y ∂volume :=
    (Measure.measurePreserving_neg volume).lintegral_comp hFmeas
  have hrw : (∫⁻ x, ‖dyadicBeurling r b ((-x) - (-s)) - dyadicBeurling r b (-x)‖ₑ ∂volume)
      = ∫⁻ x, F (-x) ∂volume := rfl
  rw [hrw, hcomp]
  -- now ∫⁻ y, F y = ω_{ψ_b}(-s).
  have heq : (∫⁻ y, F y ∂volume)
      = ∫⁻ y, ‖dyadicBeurling r b (y - (-s)) - dyadicBeurling r b y‖ₑ ∂volume := rfl
  rw [heq]
  have := omega_dyadicBeurling_le r hr b (-s) (by rwa [norm_neg])
  rwa [norm_neg] at this

/-- **Abstract cross-convolution decay.** If `g` is a mean-zero `L¹` kernel supported in
`‖t‖ < 2ᵃ⁺¹r` with mass `≤ 2π log 2`, and `f` has first-order modulus of continuity
`≤ 120π‖s‖/2ᵇr`, then for `a + 2 ≤ b` the convolution has `L¹` mass `≤ 4096·(1/2)ᵇ⁻ᵃ`.
This packages the modulus-of-continuity estimate against the kernel support. -/
lemma cross_conv_decay_le (r : ℝ) (hr : 0 < r) {g f : ℂ → ℂ} (a b : ℕ) (hab : a + 2 ≤ b)
    (hg : MemLp g 1 volume) (hgz : ∫ t, g t ∂volume = 0)
    (hg_supp : ∀ t : ℂ, (2:ℝ)^(a+1) * r ≤ ‖t‖ → ‖g t‖ₑ = 0)
    (hg_mass : (∫⁻ t, ‖g t‖ₑ ∂volume) ≤ ENNReal.ofReal (2 * Real.pi * Real.log 2))
    (hf : MemLp f 1 volume)
    (hf_omega : ∀ s : ℂ, 2 * ‖s‖ ≤ (2:ℝ)^b * r →
        (∫⁻ x, ‖f (x - s) - f x‖ₑ ∂volume) ≤ ENNReal.ofReal (120 * Real.pi * ‖s‖ / ((2:ℝ)^b * r))) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
      ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ (b - a)) := by
  refine (eLpNorm_convolution_meanZero_le hg hf hgz).trans ?_
  -- pointwise bound on the integrand `‖g t‖ₑ · ω_f(t)`.
  set c : ℝ := 120 * Real.pi * (2:ℝ)^(a+1) * r / ((2:ℝ)^b * r) with hc
  have hra : (0:ℝ) < (2:ℝ)^(a+1) * r := by positivity
  have hrb : (0:ℝ) < (2:ℝ)^b * r := by positivity
  have hptbound : ∀ t : ℂ,
      ‖g t‖ₑ * (∫⁻ x, ‖f (x - t) - f x‖ₑ ∂volume) ≤ ‖g t‖ₑ * ENNReal.ofReal c := by
    intro t
    by_cases htlarge : (2:ℝ)^(a+1) * r ≤ ‖t‖
    · rw [hg_supp t htlarge]; simp
    · push_neg at htlarge
      apply mul_le_mul_left'
      have hts : 2 * ‖t‖ ≤ (2:ℝ)^b * r := by
        have h1 : (2:ℝ)^(a+1) * r ≤ (2:ℝ)^(b-1) * r := by
          apply mul_le_mul_of_nonneg_right _ hr.le
          apply pow_le_pow_right₀ (by norm_num)
          omega
        have hbb : (2:ℝ)^b = 2 * (2:ℝ)^(b-1) := by
          conv_lhs => rw [show b = (b - 1) + 1 by omega]
          rw [pow_succ]; ring
        have h2 : 2 * ((2:ℝ)^(b-1) * r) = (2:ℝ)^b * r := by rw [hbb]; ring
        nlinarith [htlarge, h1, h2, norm_nonneg t]
      refine (hf_omega t hts).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hc, div_le_div_iff₀ hrb hrb]
      apply mul_le_mul_of_nonneg_right _ hrb.le
      nlinarith [htlarge.le, Real.pi_pos, mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) (a+1)) hr]
  refine (lintegral_mono hptbound).trans ?_
  rw [lintegral_mul_const'' _ hg.1.enorm]
  refine (mul_le_mul_right' hg_mass _).trans ?_
  -- (2π log2)·c ≤ 4096·(1/2)^(b-a).
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- c = 120π·2^(a+1)/2^b = 240π·(1/2)^(b-a).
  have hpow : (2:ℝ)^(a+1) / (2:ℝ)^b = 2 * ((1:ℝ)/2) ^ (b - a) := by
    have h2bne : (2:ℝ)^b ≠ 0 := by positivity
    have h2bane : (2:ℝ)^(b-a) ≠ 0 := by positivity
    rw [one_div, inv_pow, div_eq_iff h2bne, eq_comm]
    rw [show (2:ℝ) * (2 ^ (b - a))⁻¹ * 2 ^ b = (2 * 2 ^ b) * (2 ^ (b - a))⁻¹ by ring]
    rw [mul_inv_eq_iff_eq_mul₀ h2bane]
    rw [show (2:ℝ) * 2 ^ b = 2 ^ (b + 1) by rw [pow_succ]; ring, ← pow_add]
    congr 1
    omega
  have hceq : c = 240 * Real.pi * ((1:ℝ)/2) ^ (b - a) := by
    rw [hc, mul_div_mul_right _ _ (ne_of_gt hr)]
    rw [show 120 * Real.pi * (2:ℝ)^(a+1) / (2:ℝ)^b
        = 120 * Real.pi * ((2:ℝ)^(a+1) / (2:ℝ)^b) by ring]
    rw [hpow]; ring
  rw [hceq]
  -- (2π log2)·240π·(1/2)^(b-a) ≤ 4096·(1/2)^(b-a).
  have hpos : (0:ℝ) ≤ ((1:ℝ)/2) ^ (b - a) := by positivity
  have hnum : (2 * Real.pi * Real.log 2) * (240 * Real.pi) ≤ 4096 := by
    have hπ : Real.pi < 3.15 := Real.pi_lt_d2
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hπpos : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
    have hlogpos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hπsq : Real.pi ^ 2 ≤ 9.9225 := by nlinarith [hπ, hπpos]
    have hkey : Real.pi ^ 2 * Real.log 2 ≤ 9.9225 * 0.6931471808 := by
      apply mul_le_mul hπsq hlog2.le hlogpos (by norm_num)
    have hrw : (2 * Real.pi * Real.log 2) * (240 * Real.pi)
        = 480 * (Real.pi ^ 2 * Real.log 2) := by ring
    rw [hrw]
    nlinarith [hkey]
  calc 2 * Real.pi * Real.log 2 * (240 * Real.pi * ((1:ℝ)/2) ^ (b - a))
      = (2 * Real.pi * Real.log 2 * (240 * Real.pi)) * ((1:ℝ)/2) ^ (b - a) := by ring
    _ ≤ 4096 * ((1:ℝ)/2) ^ (b - a) := mul_le_mul_of_nonneg_right hnum hpos

/-- **Annular almost-orthogonality (the cancellation estimate).**
The `L¹` mass of the cross-convolution of two dyadic Beurling pieces (in either of the two
orders relevant to the two Schur bounds) decays geometrically in the scale separation
`d = (i - j) + (j - i) = |i - j|`, with the geometric constant `4096`. After taking square
roots (`√(4096·(1/2)^d) = 64·(1/2)^{d/2}`) and summing the geometric row, the Cotlar–Stein
constant is bounded.

The **small-separation case `d ≤ 6`** is the trivial Young `L¹⋆L¹` bound `eLpNorm_cross_le_sq`
(`‖ψ̃_i ⋆ ψ_j‖₁ ≤ (2π log 2)²`) plus the numeric comparison `sq_logmass_le`.

The **large-separation case `d ≥ 7`** is the genuine cancellation. It uses the zeroth moment
(mean-zero) of the smaller-scale factor to write the convolution value as a difference
`(g ⋆ f)(x) = ∫ g(t)·(f(x-t) - f(x)) dt` (`convolution_apply_eq_of_integral_zero`), reducing the
`L¹` norm to `∫ ‖g(t)‖·ω_f(t) dt` where `ω_f(t) = ‖f(·-t) - f‖₁` is the first-order modulus of
continuity (`eLpNorm_convolution_meanZero_le`). The dyadic pieces have `ω_f(t) ≤ 120π‖t‖/2ᵇr`
(`omega_dyadicBeurling_le`, `omega_convKernelStar_le`) — a value-variation part
(`norm_zpow_neg_two_sub_le`) plus a boundary-layer part controlled by the thin-shell measure
(`volume_shell'`). Against the kernel support `‖t‖ < 2ᵃ⁺¹r` this gives the `2^{a+1-b} = 2·2^{-d}`
decay (`cross_conv_decay_le`). Both factor orderings and both convolution orders reduce to this
single shape via commutativity of convolution. -/
lemma truncBeurling_almostOrthogonal (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    eLpNorm (MeasureTheory.convolution (convKernelStar (dyadicBeurling r i)) (dyadicBeurling r j)
        (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)))
      ∧ eLpNorm (MeasureTheory.convolution (dyadicBeurling r i) (convKernelStar (dyadicBeurling r j))
        (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i))) := by
  set d := (i - j) + (j - i) with hd_def
  by_cases hsmall : d ≤ 6
  · -- Small separation: trivial Young bound + numeric comparison (fully proved).
    have htriv := eLpNorm_cross_le_sq r hr i j
    have hnum : (2 * Real.pi * Real.log 2) ^ 2 ≤ 4096 * ((1:ℝ)/2) ^ d := sq_logmass_le d hsmall
    have hmono : ENNReal.ofReal ((2 * Real.pi * Real.log 2) ^ 2)
        ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ d) := ENNReal.ofReal_le_ofReal hnum
    exact ⟨htriv.1.trans hmono, htriv.2.trans hmono⟩
  · -- Large separation `d ≥ 7`: first-order modulus-of-continuity estimate giving `2^{-d}`.
    -- The target `4096·(1/2)^d = 4096·2^{-d}` decays like `2^{-d}`, which is exactly what a
    -- first-order modulus-of-continuity bound delivers: writing the convolution value as a
    -- difference `(g⋆f)(x) = ∫ g(t)·(f(x-t)-f(x)) dt` using the mean-zero of the smaller-scale
    -- factor `g`, the `L¹` norm is `≤ ∫ ‖g(t)‖·ω_f(t) dt` with `ω_f(t) = ‖f(·-t)-f‖₁ ≤ 120π‖t‖/2ᵇr`
    -- (value-variation part + boundary-layer part, the latter controlled by the thin-shell measure).
    -- Against the kernel support `‖t‖ < 2ᵃ⁺¹r` this yields the `2^{a+1-b} = 2·2^{-d}` decay; the
    -- numeric slack `480·π²·log2 ≈ 3283 ≤ 4096` closes the constant (`cross_conv_decay_le`).
    -- All four sub-cases (two conjuncts × `i<j`/`i>j`) reduce to this single shape, using
    -- commutativity of convolution with the commutative `mul`.
    have hflip : ∀ g f : ℂ → ℂ,
        MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume
          = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume := by
      intro g f
      have hmf : (ContinuousLinearMap.mul ℂ ℂ).flip = ContinuousLinearMap.mul ℂ ℂ := by
        ext a b
        simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_comm]
      calc MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume
          = MeasureTheory.convolution g f ((ContinuousLinearMap.mul ℂ ℂ).flip) volume := by
            rw [hmf]
        _ = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume :=
            convolution_flip (ContinuousLinearMap.mul ℂ ℂ)
    -- Mass of each kernel (zeroth moment of the absolute value): `2π log 2`.
    have hmassψ : ∀ a : ℕ, (∫⁻ t, ‖dyadicBeurling r a t‖ₑ ∂volume)
        ≤ ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
      intro a
      rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_dyadicBeurling r hr a]
    have hmassK : ∀ a : ℕ, (∫⁻ t, ‖convKernelStar (dyadicBeurling r a) t‖ₑ ∂volume)
        ≤ ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
      intro a
      rw [← eLpNorm_one_eq_lintegral_enorm,
        eLpNorm_convKernelStar _ (memLp_dyadicBeurling r hr a).1, eLpNorm_dyadicBeurling r hr a]
    -- `i ≠ j` (else `d = 0 ≤ 6`).
    rcases lt_or_gt_of_ne (show i ≠ j by rintro rfl; simp only [Nat.sub_self] at hd_def; omega)
      with hij | hij
    · -- i < j: smaller scale `i`, larger scale `j`.
      have hab : i + 2 ≤ j := by omega
      have hd_eq : j - i = d := by omega
      refine ⟨?_, ?_⟩
      · -- K_i ⋆ ψ_j: kernel K_i (scale i, mean-zero), difference ψ_j (scale j).
        have := cross_conv_decay_le r hr i j hab
          (memLp_convKernelStar (memLp_dyadicBeurling r hr i))
          (integral_convKernelStar_dyadicBeurling_eq_zero r hr i)
          (fun t ht => enorm_convKernelStar_dyadicBeurling_eq_zero_of_large r i t ht)
          (hmassK i) (memLp_dyadicBeurling r hr j)
          (fun s hs => omega_dyadicBeurling_le r hr j s hs)
        rwa [hd_eq] at this
      · -- ψ_i ⋆ K_j: kernel ψ_i (scale i, mean-zero), difference K_j (scale j).
        have := cross_conv_decay_le r hr i j hab
          (memLp_dyadicBeurling r hr i) (integral_dyadicBeurling_eq_zero r hr i)
          (fun t ht => enorm_dyadicBeurling_eq_zero_of_large r i t ht)
          (hmassψ i) (memLp_convKernelStar (memLp_dyadicBeurling r hr j))
          (fun s hs => omega_convKernelStar_le r hr j s hs)
        rwa [hd_eq] at this
    · -- i > j: smaller scale `j`, larger scale `i`; flip convolutions.
      have hab : j + 2 ≤ i := by omega
      have hd_eq : i - j = d := by omega
      refine ⟨?_, ?_⟩
      · -- K_i ⋆ ψ_j = ψ_j ⋆ K_i: kernel ψ_j (scale j, mean-zero), difference K_i (scale i).
        rw [hflip (convKernelStar (dyadicBeurling r i)) (dyadicBeurling r j)]
        have := cross_conv_decay_le r hr j i hab
          (memLp_dyadicBeurling r hr j) (integral_dyadicBeurling_eq_zero r hr j)
          (fun t ht => enorm_dyadicBeurling_eq_zero_of_large r j t ht)
          (hmassψ j) (memLp_convKernelStar (memLp_dyadicBeurling r hr i))
          (fun s hs => omega_convKernelStar_le r hr i s hs)
        rwa [hd_eq] at this
      · -- ψ_i ⋆ K_j = K_j ⋆ ψ_i: kernel K_j (scale j, mean-zero), difference ψ_i (scale i).
        rw [hflip (dyadicBeurling r i) (convKernelStar (dyadicBeurling r j))]
        have := cross_conv_decay_le r hr j i hab
          (memLp_convKernelStar (memLp_dyadicBeurling r hr j))
          (integral_convKernelStar_dyadicBeurling_eq_zero r hr j)
          (fun t ht => enorm_convKernelStar_dyadicBeurling_eq_zero_of_large r j t ht)
          (hmassK j) (memLp_dyadicBeurling r hr i)
          (fun s hs => omega_dyadicBeurling_le r hr i s hs)
        rwa [hd_eq] at this

/-- `√(1/2) ≤ 3/4`, since `√2 ≥ 4/3 ⟺ 2 ≥ 16/9`. -/
lemma sqrt_half_le_three_quarters : Real.sqrt (1/2) ≤ 3/4 := by
  rw [show (3:ℝ)/4 = Real.sqrt ((3/4)^2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt; norm_num

/-- `∑_{j ∈ Fin N} (√(1/2))^|i-j| ≤ 7`, uniformly in `N`. Proof: bound the base
`√(1/2) ≤ 3/4` pointwise, so each half is a geometric `3/4`-tail; the `j ≤ i` half is
`≤ ∑_{k<N}(3/4)^k < 4` and the `j > i` half (indices `≥ 1`) is `≤ 4 - 1 = 3`. -/
lemma rowsum_half_dist_le (N : ℕ) (i : Fin N) :
    ∑ j : Fin N, (Real.sqrt (1/2)) ^ ((i.val - j.val) + (j.val - i.val)) ≤ 7 := by
  classical
  set q : ℝ := Real.sqrt (1/2) with hq_def
  have hq_pos : 0 < q := Real.sqrt_pos.mpr (by norm_num)
  have hq_le : q ≤ 3/4 := sqrt_half_le_three_quarters
  -- Pointwise: q^k ≤ (3/4)^k.
  have hqpow : ∀ k : ℕ, q ^ k ≤ ((3:ℝ)/4) ^ k := fun k =>
    pow_le_pow_left₀ hq_pos.le hq_le k
  -- Geometric bound: ∑_{k<M} (3/4)^k ≤ 4 (partial sum bounded by the tsum = (1-3/4)⁻¹ = 4).
  have hsummable : Summable (fun k : ℕ => ((3:ℝ)/4) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have htsum : (∑' k : ℕ, ((3:ℝ)/4) ^ k) = 4 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.range M, ((3:ℝ)/4) ^ k ≤ 4 := by
    intro M
    have h := hsummable.sum_le_tsum (Finset.range M) (fun k _ => by positivity)
    rw [htsum] at h; exact h
  have hsplit : ∑ j : Fin N, q ^ ((i.val - j.val) + (j.val - i.val))
      = (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ i.val),
            q ^ ((i.val - j.val) + (j.val - i.val)))
        + (∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val),
            q ^ ((i.val - j.val) + (j.val - i.val))) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit, show (7:ℝ) = 4 + 3 by norm_num]
  apply add_le_add
  · -- j ≤ i half: indices i-j range in {0,...}, bound by ∑_{k<N}(3/4)^k < 4.
    have hinj : Set.InjOn (fun j : Fin N => i.val - j.val)
        (Finset.univ.filter (fun j : Fin N => j.val ≤ i.val)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      apply Fin.ext; simp only at hab; omega
    have hrw : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ i.val),
          q ^ ((i.val - j.val) + (j.val - i.val)))
        = ∑ k ∈ (Finset.univ.filter (fun j : Fin N => j.val ≤ i.val)).image
            (fun j => i.val - j.val), q ^ k := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      congr 1; omega
    rw [hrw]
    refine le_trans (Finset.sum_le_sum (fun k _ => hqpow k)) ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity))
      (hgeom N)
    intro k hk
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    simp only [Finset.mem_range]; omega
  · -- j > i half: indices j-i ≥ 1, bound by ∑_{1≤k<N}(3/4)^k = (∑_{k<N}(3/4)^k) - 1 ≤ 3.
    have hinj : Set.InjOn (fun j : Fin N => j.val - i.val)
        (Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      apply Fin.ext; simp only at hab; omega
    have hrw : (∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val),
          q ^ ((i.val - j.val) + (j.val - i.val)))
        = ∑ k ∈ (Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val)).image
            (fun j => j.val - i.val), q ^ k := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      congr 1; omega
    rw [hrw]
    refine le_trans (Finset.sum_le_sum (fun k _ => hqpow k)) ?_
    -- The image is contained in `Finset.Ico 1 N` (indices ≥ 1).
    have hsub : (Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val)).image
        (fun j => j.val - i.val) ⊆ Finset.Ico 1 N := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      simp only [Finset.mem_Ico]; omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)) ?_
    -- ∑_{k ∈ Ico 1 N} (3/4)^k = (∑_{k<N}(3/4)^k) - 1 (if N ≥ 1) ≤ 4 - 1 = 3.
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hrange : Finset.range N = insert 0 (Finset.Ico 1 N) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      have hnotmem : (0:ℕ) ∉ Finset.Ico 1 N := by simp
      have hsum0 : (∑ k ∈ Finset.range N, ((3:ℝ)/4) ^ k)
          = 1 + ∑ k ∈ Finset.Ico 1 N, ((3:ℝ)/4) ^ k := by
        rw [hrange, Finset.sum_insert hnotmem]; norm_num
      have := hgeom N
      linarith [hsum0]

/-- `√(4096·(1/2)^d) = 64·(√(1/2))^d`. -/
lemma sqrt_const_geom (d : ℕ) :
    Real.sqrt (4096 * ((1:ℝ)/2)^d) = 64 * (Real.sqrt (1/2))^d := by
  have h1 : ((1:ℝ)/2)^d = ((Real.sqrt (1/2))^d)^2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [show (4096:ℝ) = 64^2 by norm_num, h1, ← mul_pow, Real.sqrt_sq (by positivity)]

/-- The dyadic Cotlar–Stein operator `T_j = convolution by ψ_j` on `L²`. -/
noncomputable def dyadicT (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (Lp ℂ 2 (volume : Measure ℂ)) →L[ℂ] (Lp ℂ 2 (volume : Measure ℂ)) :=
  convCLM (dyadicBeurling r j) (memLp_dyadicBeurling r hr j)

/-- Per-pair Schur bound (adjoint·op direction): `‖T_i* ∘ T_j‖ ≤ 4096·(1/2)^|i-j|`. -/
lemma adjMul_pair_le (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    ‖(ContinuousLinearMap.adjoint (dyadicT r hr i)) ∘L (dyadicT r hr j)‖
      ≤ 4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)) := by
  unfold dyadicT
  rw [adjoint_convCLM, convCLM_comp (memLp_convKernelStar (memLp_dyadicBeurling r hr i))
    (memLp_dyadicBeurling r hr j)]
  refine (convCLM_opNorm_le _ _).trans ?_
  have hbd := (truncBeurling_almostOrthogonal r hr i j).1
  have : (eLpNorm (MeasureTheory.convolution (convKernelStar (dyadicBeurling r i))
      (dyadicBeurling r j) (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume).toReal
      ≤ (ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)))).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
  refine this.trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- Per-pair Schur bound (op·adjoint direction): `‖T_i ∘ T_j*‖ ≤ 4096·(1/2)^|i-j|`. -/
lemma mulAdj_pair_le (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    ‖(dyadicT r hr i) ∘L (ContinuousLinearMap.adjoint (dyadicT r hr j))‖
      ≤ 4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)) := by
  unfold dyadicT
  rw [adjoint_convCLM, convCLM_comp (memLp_dyadicBeurling r hr i)
    (memLp_convKernelStar (memLp_dyadicBeurling r hr j))]
  refine (convCLM_opNorm_le _ _).trans ?_
  have hbd := (truncBeurling_almostOrthogonal r hr i j).2
  have : (eLpNorm (MeasureTheory.convolution (dyadicBeurling r i)
      (convKernelStar (dyadicBeurling r j)) (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume).toReal
      ≤ (ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)))).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
  refine this.trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- First Schur sum bound: `∑_j √‖T_i* ∘ T_j‖ ≤ 2⁹`, uniformly in `N` and `i`. -/
lemma schur_adjMul (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    ∑ j : Fin N,
        Real.sqrt ‖(ContinuousLinearMap.adjoint (dyadicT r hr i.val)) ∘L (dyadicT r hr j.val)‖
      ≤ (2:ℝ)^9 := by
  have hstep : ∀ j : Fin N,
      Real.sqrt ‖(ContinuousLinearMap.adjoint (dyadicT r hr i.val)) ∘L (dyadicT r hr j.val)‖
        ≤ 64 * (Real.sqrt (1/2)) ^ ((i.val - j.val) + (j.val - i.val)) := by
    intro j
    refine le_trans (Real.sqrt_le_sqrt (adjMul_pair_le r hr i.val j.val)) ?_
    rw [sqrt_const_geom]
  refine le_trans (Finset.sum_le_sum (fun j _ => hstep j)) ?_
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (rowsum_half_dist_le N i) (by norm_num)) ?_
  norm_num

/-- Second Schur sum bound: `∑_j √‖T_i ∘ T_j*‖ ≤ 2⁹`, uniformly in `N` and `i`. -/
lemma schur_mulAdj (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    ∑ j : Fin N,
        Real.sqrt ‖(dyadicT r hr i.val) ∘L (ContinuousLinearMap.adjoint (dyadicT r hr j.val))‖
      ≤ (2:ℝ)^9 := by
  have hstep : ∀ j : Fin N,
      Real.sqrt ‖(dyadicT r hr i.val) ∘L (ContinuousLinearMap.adjoint (dyadicT r hr j.val))‖
        ≤ 64 * (Real.sqrt (1/2)) ^ ((i.val - j.val) + (j.val - i.val)) := by
    intro j
    refine le_trans (Real.sqrt_le_sqrt (mulAdj_pair_le r hr i.val j.val)) ?_
    rw [sqrt_const_geom]
  refine le_trans (Finset.sum_le_sum (fun j _ => hstep j)) ?_
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (rowsum_half_dist_le N i) (by norm_num)) ?_
  norm_num

/-- **Cotlar–Stein operator bound.** The partial sum `∑_{j<N} T_j` of dyadic Beurling operators
has `L²` operator norm `≤ 2⁹`, uniformly in `N`. -/
lemma partialSum_opNorm_le (r : ℝ) (hr : 0 < r) (N : ℕ) :
    ‖∑ j : Fin N, dyadicT r hr j.val‖ ≤ (2:ℝ)^9 :=
  SingularIntegral.cotlarStein (fun j : Fin N => dyadicT r hr j.val) ((2:ℝ)^9) (by positivity)
    (fun i => schur_adjMul r hr N i) (fun i => schur_mulAdj r hr N i)

/-- The partial-sum kernel `∑_{j<N} ψ_j`. -/
noncomputable def partialKernel (r : ℝ) (N : ℕ) : ℂ → ℂ :=
  fun u => ∑ j : Fin N, dyadicBeurling r j.val u

/-- The partial-sum kernel lies in `L¹`. -/
lemma memLp_partialKernel (r : ℝ) (hr : 0 < r) (N : ℕ) :
    MemLp (partialKernel r N) 1 volume := by
  have heq : partialKernel r N = ∑ j : Fin N, dyadicBeurling r j.val := by
    funext u; rw [partialKernel, Finset.sum_apply]
  rw [heq]
  exact memLp_finset_sum' _ (fun j _ => memLp_dyadicBeurling r hr j.val)

/-- The coercion of a finite `Lp`-sum is a.e. the pointwise finite sum of the coercions. -/
lemma Lp_coeFn_sum {ι : Type*} (s : Finset ι) (g : ι → Lp ℂ 2 (volume : Measure ℂ)) :
    ((∑ i ∈ s, g i : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] fun x => ∑ i ∈ s, ((g i : ℂ → ℂ) x) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a) (∑ i ∈ s, g i), ih] with x hx hix
    rw [hx]
    simp only [Pi.add_apply, Finset.sum_insert ha, hix]

/-- Pointwise: convolution by the partial-sum kernel equals the sum of the dyadic
convolutions (a.e.), since each summand convolution exists a.e. -/
lemma partial_conv_eq_sum (r : ℝ) (hr : 0 < r) (N : ℕ) {F : ℂ → ℂ} (hF : MemLp F 2 volume) :
    ∀ᵐ x ∂volume,
      MeasureTheory.convolution (partialKernel r N) F (ContinuousLinearMap.mul ℂ ℂ) volume x
        = ∑ j : Fin N, MeasureTheory.convolution (dyadicBeurling r j.val) F
            (ContinuousLinearMap.mul ℂ ℂ) volume x := by
  have hex : ∀ j : Fin N, ∀ᵐ x ∂volume,
      ConvolutionExistsAt (dyadicBeurling r j.val) F x (ContinuousLinearMap.mul ℂ ℂ) volume :=
    fun j => ae_convolutionExistsAt (memLp_dyadicBeurling r hr j.val) hF
  rw [← ae_all_iff] at hex
  filter_upwards [hex] with x hx
  rw [MeasureTheory.convolution_mul]
  have heq : (fun t => partialKernel r N t * F (x - t))
      = fun t => ∑ j : Fin N, dyadicBeurling r j.val t * F (x - t) := by
    funext t; rw [partialKernel, Finset.sum_mul]
  rw [heq, integral_finset_sum]
  · exact Finset.sum_congr rfl (fun j _ => (MeasureTheory.convolution_mul ..).symm)
  · intro j _
    have hjx := hx j
    rw [ConvolutionExistsAt] at hjx
    simpa only [ContinuousLinearMap.mul_apply'] using hjx

/-- `(∑_{j<N} T_j) F =ᵐ (partialKernel r N) ⋆ F` for every `F ∈ L²`. -/
lemma sumT_apply_coeFn (r : ℝ) (hr : 0 < r) (N : ℕ) (F : Lp ℂ 2 (volume : Measure ℂ)) :
    (((∑ j : Fin N, dyadicT r hr j.val) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution (partialKernel r N) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
  have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
  have h1 : ((∑ j : Fin N, dyadicT r hr j.val) F : ℂ → ℂ)
      =ᵐ[volume] fun x => ∑ j : Fin N, ((dyadicT r hr j.val F : ℂ → ℂ) x) := by
    rw [ContinuousLinearMap.sum_apply]
    exact Lp_coeFn_sum _ _
  have h2 : ∀ᵐ x ∂volume, ∀ j : Fin N, ((dyadicT r hr j.val F : ℂ → ℂ) x)
      = MeasureTheory.convolution (dyadicBeurling r j.val) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume x := by
    rw [ae_all_iff]
    exact fun j => convCLM_apply_coeFn _ _ F
  filter_upwards [h1, h2, partial_conv_eq_sum r hr N hF] with x hx1 hx2 hx3
  rw [hx1, hx3]
  exact Finset.sum_congr rfl (fun j _ => hx2 j)

/-- **Uniform `L²` bound for the partial-sum convolution.** `‖(∑_{j<N} ψ_j) ⋆ f‖₂ ≤ 2⁹ ‖f‖₂`,
uniformly in `N`; the operator translation of `partialSum_opNorm_le`. -/
lemma eLpNorm_partial_conv_le (r : ℝ) (hr : 0 < r) (N : ℕ) {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume
      ≤ (2:ℝ≥0∞)^9 * eLpNorm f 2 volume := by
  set F : Lp ℂ 2 (volume : Measure ℂ) := hf.toLp f with hFdef
  have hFf : (F : ℂ → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have hconv_eq : MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume
      = MeasureTheory.convolution (partialKernel r N) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
      (Filter.EventuallyEq.refl _ _) hFf.symm
  have hconv_congr : MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume
      =ᵐ[volume] (((∑ j : Fin N, dyadicT r hr j.val) F) : ℂ → ℂ) := by
    rw [hconv_eq]; exact (sumT_apply_coeFn r hr N F).symm
  rw [eLpNorm_congr_ae hconv_congr]
  have hnorm_le : ‖(∑ j : Fin N, dyadicT r hr j.val) F‖ ≤ (2:ℝ)^9 * ‖F‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (partialSum_opNorm_le r hr N) (norm_nonneg _))
  rw [Lp.norm_def] at hnorm_le
  have hFnorm : ‖F‖ = (eLpNorm f 2 volume).toReal := by rw [hFdef, Lp.norm_toLp]
  rw [hFnorm] at hnorm_le
  have h29 : (2:ℝ≥0∞)^9 = ENNReal.ofReal ((2:ℝ)^9) := by
    rw [show ((2:ℝ)^9) = (512:ℝ) by norm_num, show (2:ℝ≥0∞)^9 = (512:ℝ≥0∞) by norm_num,
      show (512:ℝ≥0∞) = ENNReal.ofReal 512 by rw [ENNReal.ofReal]; norm_num]
  have hRHSeq : (2:ℝ≥0∞)^9 * eLpNorm f 2 volume
      = ENNReal.ofReal ((2:ℝ)^9 * (eLpNorm f 2 volume).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity), h29, ENNReal.ofReal_toReal hf.2.ne]
  rw [hRHSeq, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top ((∑ j : Fin N, dyadicT r hr j.val) F))]
  apply ENNReal.ofReal_le_ofReal
  convert hnorm_le using 2

/-- Core scalar bound `‖t⁻²‖ ≤ r⁻²` whenever `r ≤ ‖t‖`. -/
lemma norminv_le (r : ℝ) (hr : 0 < r) (t : ℂ) (ht : r ≤ ‖t‖) :
    ‖(t^(-2:ℤ) : ℂ)‖ ≤ r⁻¹^2 := by
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr ht
  rw [norm_zpow, show ((-2:ℤ)) = -(2:ℤ) by ring, zpow_neg, zpow_two, ← pow_two, inv_pow]
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_left₀ hr.le ht 2

/-- The partial-sum kernel is uniformly (in `N`) bounded by `r⁻²` pointwise. -/
lemma norm_partialKernel_le (r : ℝ) (hr : 0 < r) (N : ℕ) (t : ℂ) :
    ‖partialKernel r N t‖ ≤ r⁻¹^2 := by
  classical
  unfold partialKernel
  by_cases h : ∃ j : Fin N, t ∈ {u : ℂ | (2:ℝ)^j.val * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j.val+1) * r}
  · obtain ⟨j0, hj0⟩ := h
    rw [Finset.sum_eq_single j0]
    · rw [dyadicBeurling, Set.indicator_of_mem hj0]
      apply norminv_le r hr
      exact le_trans
        (by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j0.val), hr]) hj0.1
    · intro j _ hjne
      rw [dyadicBeurling, Set.indicator_of_notMem]
      intro hmem
      rcases lt_or_gt_of_ne (fun hc => hjne (Fin.ext hc)) with hlt | hgt
      · have h1 : (2:ℝ)^(j.val+1) * r ≤ (2:ℝ)^j0.val * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [hmem.2, hj0.1, h1]
      · have h1 : (2:ℝ)^(j0.val+1) * r ≤ (2:ℝ)^j.val * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [hj0.2, hmem.1, h1]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [not_exists] at h
    rw [Finset.sum_eq_zero]
    · simp only [norm_zero]; positivity
    · intro j _
      rw [dyadicBeurling, Set.indicator_of_notMem (h j)]

/-- **Pointwise convergence of the partial-sum kernel:** `∑_{j<N} ψ_j(u) → k_r(u)` for every `u`
(the dyadic annuli partition `[r,∞)`; the sum is eventually constant). -/
lemma partialKernel_tendsto (r : ℝ) (hr : 0 < r) (u : ℂ) :
    Filter.Tendsto (fun N => partialKernel r N u) Filter.atTop
      (nhds (truncBeurlingKernel r u)) := by
  apply Filter.Tendsto.congr' (f₁ := fun _ => truncBeurlingKernel r u) _ tendsto_const_nhds
  by_cases hu : r ≤ ‖u‖
  · obtain ⟨j0, hj0le, hj0lt⟩ := exists_nat_pow_near (x := ‖u‖/r) (y := 2)
      (by rw [le_div_iff₀ hr]; linarith) (by norm_num)
    have hle : (2:ℝ)^j0 * r ≤ ‖u‖ := (le_div_iff₀ hr).mp hj0le
    have hlt : ‖u‖ < (2:ℝ)^(j0+1) * r := (div_lt_iff₀ hr).mp hj0lt
    refine Filter.eventuallyEq_of_mem (s := {N | j0 + 1 ≤ N}) (Filter.mem_atTop _) ?_
    intro N hN
    simp only [Set.mem_setOf_eq] at hN
    change truncBeurlingKernel r u = partialKernel r N u
    have hj0N : j0 < N := by omega
    rw [truncBeurlingKernel, Set.indicator_of_mem (by simpa using hu)]
    unfold partialKernel
    rw [Finset.sum_eq_single (⟨j0, hj0N⟩ : Fin N)]
    · rw [dyadicBeurling, Set.indicator_of_mem (by exact ⟨hle, hlt⟩)]
    · intro j _ hjne
      rw [dyadicBeurling, Set.indicator_of_notMem]
      simp only [Set.mem_setOf_eq, not_and, not_lt]
      intro hjge
      have hjval : j.val ≠ j0 := fun h => hjne (Fin.ext (by simpa using h))
      rcases lt_or_gt_of_ne hjval with hlt' | hgt'
      · have hpow : (2:ℝ)^(j.val+1) * r ≤ (2:ℝ)^j0 * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [le_trans hpow hle]
      · exfalso
        have hpow : (2:ℝ)^(j0+1) * r ≤ (2:ℝ)^j.val * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [le_trans hpow hjge]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Filter.eventuallyEq_of_mem (s := Set.univ) Filter.univ_mem ?_
    intro N _
    change truncBeurlingKernel r u = partialKernel r N u
    rw [truncBeurlingKernel, Set.indicator_of_notMem (by simpa using hu)]
    unfold partialKernel
    rw [Finset.sum_eq_zero]
    intro j _
    rw [dyadicBeurling, Set.indicator_of_notMem]
    simp only [Set.mem_setOf_eq, not_and, not_lt]
    intro hge
    exfalso
    have hge' : r ≤ (2:ℝ)^j.val * r := by
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j.val), hr]
    linarith [le_trans hge' hge]

/-- **Convergence of the partial-sum convolutions** at every point, for `f` of bounded finite
support, via dominated convergence (uniform domination by `r⁻²‖f(x-·)‖ ∈ L¹`). -/
lemma conv_partial_tendsto (r : ℝ) (hr : 0 < r) {f : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) (x : ℂ) :
    Filter.Tendsto (fun N => MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume x) Filter.atTop
      (nhds (MeasureTheory.convolution (truncBeurlingKernel r) f
        (ContinuousLinearMap.mul ℂ ℂ) volume x)) := by
  have hfint : Integrable f volume := hf.integrable
  simp only [MeasureTheory.convolution_mul]
  apply tendsto_integral_of_dominated_convergence (bound := fun t => r⁻¹^2 * ‖f (x - t)‖)
  · intro n
    refine AEStronglyMeasurable.mul (memLp_partialKernel r hr n).1 ?_
    exact hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℂ) x)
  · exact ((hfint.comp_sub_left x).norm).const_mul _
  · intro n
    filter_upwards with t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_partialKernel_le r hr n t) (norm_nonneg _)
  · filter_upwards with t
    exact (partialKernel_tendsto r hr t).mul_const (f (x - t))

/-- **Uniform `L²` bound for convolution against the truncated Beurling kernel.**
For every `r > 0` and every bounded, finitely-supported `f`,
`‖k_r ⋆ f‖₂ ≤ 2⁹ ‖f‖₂`, with the constant uniform in `r`.

This is the analytic heart of the Calderón–Zygmund theory of the Beurling
transform: the `L²(ℂ)→L²(ℂ)` operator norm of the singular-integral convolution
`f ↦ k_r ⋆ f`, `k_r(u) = u⁻²·1_{‖u‖≥r}`, is bounded uniformly in the truncation
scale `r`. By the dilation relation `k_r(u) = r⁻² k_1(u/r)` and the `L²`-isometric
dilation `f ↦ f(r·)` the operator `f ↦ k_r ⋆ f` is unitarily conjugate to the
single-scale operator `f ↦ k_1 ⋆ f`, so all scales share one operator norm; that
norm equals the sup of the truncated Beurling Fourier symbol `m_r(ξ) = 𝓕 k_r(ξ)`,
a function bounded uniformly in `r` (Plancherel on `Lp ℂ 2 volume`:
`‖k_r ⋆ f‖₂ = ‖m_r · 𝓕f‖₂ ≤ ‖m_r‖∞ ‖f‖₂`, with `‖m_r‖∞ = 1` the true value).
The true operator norm is `1`; the slack to `2⁹` is enormous.

PROOF: the full dyadic almost-orthogonality (Cotlar–Stein) machine is built here.
Because `k_r ∉ L¹` (its `2D` tail `∫_{|u|>r}|u|⁻²` diverges logarithmically) the
elementary Young route fails by a hair, so the bound is genuinely a *cancellation*
phenomenon. The pipeline, all proved above/in sibling files: the dyadic pieces
`ψ_j(u) = u⁻²·1_{2ʲr ≤ |u| < 2ʲ⁺¹r}` (`dyadicBeurling`) lie in `L¹`
(`memLp_dyadicBeurling`) with mass `2π log 2` uniform in `j` (`eLpNorm_dyadicBeurling`,
from the polar-coordinate annular norm `SingularIntegral.annulus_lintegral`);
`eLpNorm_convolution_le` is the Young `L¹⋆L²→L²` inequality; `convCLM` realizes
`f ↦ ψ_j ⋆ f` as a CLM on `L²` with `adjoint_convCLM` identifying its Hilbert adjoint
as convolution by `ψ̃_j(u) = conj(ψ_j(-u))`; `convCLM_comp` composes such operators;
`SingularIntegral.cotlarStein` (the abstract almost-orthogonality lemma, fully proved
in `CotlarStein.lean`) bounds `‖∑_{j<N} T_j‖ ≤ 2⁹` from the two Schur √-sum bounds
(`schur_adjMul`, `schur_mulAdj`); `eLpNorm_partial_conv_le` transports this to
`‖(∑_{j<N} ψ_j) ⋆ f‖₂ ≤ 2⁹‖f‖₂`; and `conv_partial_tendsto` + lower semicontinuity of
the `L²` norm (`Lp.eLpNorm_le_of_ae_tendsto`) pass to the `N → ∞` limit
`∑_{j<N} ψ_j ⋆ f → k_r ⋆ f`. The ONE remaining input is the deep **annular mean-zero
cancellation estimate** `truncBeurling_almostOrthogonal`
(`‖ψ̃_i ⋆ ψ_j‖₁ ≤ 16384·(1/4)^{|i-j|}`), a research-level `2D` geometric calculation
absent from Mathlib/Carleson; everything else here is proved from it. -/
lemma eLpNorm_truncBeurling_convolution_le {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) :
    eLpNorm (MeasureTheory.convolution (truncBeurlingKernel r) f
        (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume
      ≤ (2 : ℝ≥0∞) ^ 9 * eLpNorm f 2 volume := by
  have hf2 : MemLp f 2 volume := hf.memLp 2
  refine MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop)
    (f := fun N => MeasureTheory.convolution (partialKernel r N) f
      (ContinuousLinearMap.mul ℂ ℂ) volume)
    (C := (2:ℝ≥0∞)^9 * eLpNorm f 2 volume) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun N => eLpNorm_partial_conv_le r hr N hf2)
  · exact fun N => (memLp_convolution_two (memLp_partialKernel r hr N) hf2).1
  · exact Filter.Eventually.of_forall (fun x => conv_partial_tendsto r hr hf x)

/-- **Single-scale `L²` bound for the truncated Beurling operator.** The truncated
Beurling operator `czOperator beurlingKernel r` (convolution against the
translation-invariant kernel `k_r(u) = u⁻² · 1_{‖u‖>r}`) is bounded `L²(ℂ) → L²(ℂ)`
with a constant `2⁹` that is *uniform in `r > 0`*.

This is the analytic core of `czOperator_beurling_strongType_L2`. By the dilation
relation `k_r(u) = r⁻² k_1(u/r)` the operator `f ↦ k_r ⋆ f` is conjugate, by the
`L²`-isometric dilation `f ↦ f(r·)`, to the single-scale operator `f ↦ k_1 ⋆ f`,
so all truncated operators share one `L²` operator norm; that single norm is the
sup of the truncated Beurling Fourier symbol `m(ξ) = 𝓕 k_1(ξ)`, a bounded function
(Plancherel: `‖k_1 ⋆ f‖₂ = ‖m · 𝓕 f‖₂ ≤ ‖m‖∞ ‖f‖₂`). The constant `2⁹` is far
from sharp; only finiteness and uniformity in `r` are used downstream.

The proof rewrites the truncated operator as the convolution `k_r ⋆ f`
(`czOperator_beurling_eq_convolution`) and applies the uniform `L²` convolution
bound `eLpNorm_truncBeurling_convolution_le`. -/
lemma eLpNorm_czOperator_beurling {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) :
    eLpNorm (czOperator beurlingKernel r f) 2 volume
      ≤ (2 : ℝ≥0∞) ^ 9 * eLpNorm f 2 volume := by
  rw [czOperator_beurling_eq_convolution]
  exact eLpNorm_truncBeurling_convolution_le hr hf

/-- **Gateway `L²` bound for the truncated operator.** Each truncated Beurling
operator `czOperator beurlingKernel r` is bounded `L² → L²` with a constant
uniform in `r > 0` (`C_Ts 4`). This is the precondition `hT` threaded through the
Carleson Calderón–Zygmund machinery (`czOperator_weak_1_1`, `cotlar_estimate`,
`nontangential_from_simple`): the truncated kernel `k_r(u) = u⁻² · 1_{|u|>r}` is a
convolution kernel whose Fourier symbol is bounded uniformly in `r`. -/
lemma czOperator_beurling_strongType_L2 {r : ℝ} (hr : 0 < r) :
    HasBoundedStrongType (czOperator beurlingKernel r) 2 2 volume volume (C_Ts 4 : ℝ≥0∞) := by
  intro f hf
  refine ⟨czOperator_aestronglyMeasurable_aux hf, ?_⟩
  refine (eLpNorm_czOperator_beurling hr hf).trans ?_
  gcongr
  -- `2⁹ ≤ C_Ts 4 = 2 ^ (4 ^ 3) = 2 ^ 64`
  have hCTs : (C_Ts 4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 64 := by
    rw [C_Ts]
    push_cast
    norm_num
  rw [hCTs]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)


/-! ## Maximal-operator `L²` bound and a.e. convergence (Theorem 1 core)

The `L²` isometry on general `μ ∈ L²` is reached from the smooth dense class by
(i) the uniform-in-`r` `L²` bound on the truncations, lifted to a maximal-operator
bound via the Carleson nontangential machinery, and (ii) the resulting a.e.
convergence of the truncations as `r → 0⁺`. The leaf lemmas build that tree. -/

/-- The truncated Beurling kernel section `1_{‖u‖≥R}·‖u‖⁻⁴` has finite mass:
`∫_{‖u‖≥R} ‖u‖⁻⁴ du < ∞` (polar coordinates, `∫_R^∞ ρ⁻³ dρ < ∞`). -/
lemma lintegral_kernelSection_lt_top (R : ℝ) (hR : 0 < R) :
    ∫⁻ u : ℂ in {u : ℂ | R ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ 2 < ⊤ := by
  rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
    ← Complex.lintegral_comp_polarCoord_symm]
  set box : ℝ × ℝ → ENNReal := fun p =>
    (Set.Ici R ×ˢ Set.Ioo (-π) π).indicator
      (fun p => ENNReal.ofReal (p.1 * (p.1^2)⁻¹^2)) p with hbox
  have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (p.1^2)⁻¹^2)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_fst.mul (((measurable_fst.pow_const 2).inv).pow_const 2))
  have hbound : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • {u : ℂ | R ≤ ‖u‖}.indicator
        (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ 2) (Complex.polarCoord.symm p) ≤ box p := by
    intro p hp
    rw [polarCoord_target, Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [Set.mem_Ioi] at hp1
    simp only [hbox]
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hmem : Complex.polarCoord.symm p ∈ {u : ℂ | R ≤ ‖u‖}
    · have hpR : R ≤ p.1 := by rw [Set.mem_setOf_eq, hnorm] at hmem; exact hmem
      rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hp2⟩)]
      have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
        rw [← ofReal_norm_eq_enorm, hnorm]
      rw [henorm, smul_eq_mul,
        show ((ENNReal.ofReal p.1 ^ 2)⁻¹)^2 = ENNReal.ofReal ((p.1^2)⁻¹^2) by
          rw [← ENNReal.ofReal_pow hp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
            ← ENNReal.ofReal_pow (by positivity)],
        ← ENNReal.ofReal_mul hp1.le]
    · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le _
  refine lt_of_le_of_lt (setLIntegral_mono
    (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
  calc ∫⁻ p in polarCoord.target, box p
      ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p in (Set.Ici R ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (p.1 * (p.1^2)⁻¹^2) := by
          rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
    _ < ⊤ := by
          rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
          simp only [setLIntegral_const]
          rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
          apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
          have hint : IntegrableOn (fun r : ℝ => r * (r^2)⁻¹^2) (Set.Ici R) volume := by
            have heq : (fun r : ℝ => r * (r^2)⁻¹^2) =ᶠ[ae (volume.restrict (Set.Ici R))]
                (fun r : ℝ => r^(-3 : ℝ)) := by
              filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
              simp only [Set.mem_Ici] at hr
              have hrpos : 0 < r := lt_of_lt_of_le hR hr
              rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              field_simp
            rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
              integrableOn_Ioi_rpow_iff hR]
            norm_num
          have hfin := hint.2
          rw [hasFiniteIntegral_iff_enorm] at hfin
          refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
          · exact (measurable_id.mul (((measurable_id.pow_const 2).inv).pow_const 2)).enorm
          · simp only [Set.mem_Ici] at hx
            have hxpos : 0 < x := lt_of_lt_of_le hR hx
            rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]


/-- **Kernel section is `L²`.** For `R > 0` the truncated Beurling kernel
`y ↦ 1_{(ball x R)ᶜ}(y)·(x-y)⁻²` lies in `L²(ℂ)`. -/
lemma memLp_kernelSection (x : ℂ) (R : ℝ) (hR : 0 < R) :
    MemLp (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) volume := by
    apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
    apply Measurable.aestronglyMeasurable
    unfold beurlingKernel; fun_prop
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  simp_rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  -- ∫⁻ ‖indicator ...‖ₑ^2 = ∫⁻_{(ball x R)ᶜ} ‖beurlingKernel x y‖ₑ^2
  have hpt : ∀ y, ‖(Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y‖ₑ ^ 2
      = (Metric.ball x R)ᶜ.indicator (fun y => ‖beurlingKernel x y‖ₑ ^ 2) y := by
    intro y
    by_cases h : y ∈ (Metric.ball x R)ᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]; ring
  refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
  rw [lintegral_indicator measurableSet_ball.compl]
  -- bound ‖beurlingKernel x y‖ₑ^2 ≤ ((‖x-y‖ₑ^2)⁻¹)^2
  have hkb : ∀ y, ‖beurlingKernel x y‖ₑ ^ 2 ≤ ((‖x - y‖ₑ ^ 2)⁻¹) ^ 2 := by
    intro y
    apply pow_le_pow_left'
    by_cases h : x = y
    · subst h; simp [beurlingKernel]
    · have hne : x - y ≠ 0 := sub_ne_zero.mpr h
      have he : beurlingKernel x y = ((x-y) * (x-y))⁻¹ := by rw [beurlingKernel, zpow_neg, zpow_two]
      rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
  refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
  · fun_prop
  -- now ∫⁻_{(ball x R)ᶜ} ((‖x-y‖ₑ^2)⁻¹)^2 = ∫⁻_{‖u‖≥R} ((‖u‖ₑ^2)⁻¹)^2 via u = x - y
  rw [← lintegral_indicator measurableSet_ball.compl]
  have hsub : (fun y => (Metric.ball x R)ᶜ.indicator (fun y => ((‖x - y‖ₑ ^ 2)⁻¹) ^ 2) y)
      = (fun y => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ 2) (x - y)) := by
    funext y
    have hiff : (y ∈ (Metric.ball x R)ᶜ) ↔ (x - y ∈ {u : ℂ | R ≤ ‖u‖}) := by
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_setOf_eq, dist_comm, Complex.dist_eq]
    by_cases h : y ∈ (Metric.ball x R)ᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
  rw [hsub, lintegral_sub_left_eq_self
    (fun u => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ 2) u) x]
  rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
  exact lintegral_kernelSection_lt_top R hR

/-- **Integrability of the truncated Beurling integrand.** For `f ∈ L²` the
integrand `y ↦ (x-y)⁻² f(y)` is integrable over `(ball x r)ᶜ` (Hölder: the kernel
section is `L²` by `memLp_kernelSection`, `f ∈ L²`, product `∈ L¹`). -/
lemma integrableOn_beurlingKernel_mul {r : ℝ} (hr : 0 < r) (x : ℂ) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  have hker : MemLp (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) 2
      volume := memLp_kernelSection x r hr
  rw [IntegrableOn]
  have h1 : MemLp (fun y => beurlingKernel x y) 2 (volume.restrict (Metric.ball x r)ᶜ) := by
    apply MemLp.ae_eq _ (hker.restrict (Metric.ball x r)ᶜ)
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [Set.indicator_of_mem hy]
  exact h1.integrable_mul (hf.restrict _)

/-- **`L²`-linearity of the truncated Beurling operator.** For `f, g ∈ L²`,
`czOperator beurlingKernel r (f - g) = czOperator beurlingKernel r f
  - czOperator beurlingKernel r g` pointwise (integrability from
`integrableOn_beurlingKernel_mul`). -/
lemma czOperator_beurling_sub {r : ℝ} (hr : 0 < r) (x : ℂ) {f g : ℂ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    czOperator beurlingKernel r (f - g) x
      = czOperator beurlingKernel r f x - czOperator beurlingKernel r g x := by
  have h1 := integrableOn_beurlingKernel_mul hr x hf
  have h2 := integrableOn_beurlingKernel_mul hr x hg
  unfold czOperator
  rw [← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
  simp only [Pi.sub_apply]; ring

/-- **Cauchy–Schwarz bound for the truncated operator.** Pointwise,
`‖czOperator beurlingKernel R h x‖ ≤ ‖kernel section‖₂ · ‖h‖₂`, the bounded-linear
estimate that makes `czOperator beurlingKernel R · x` `L²`-continuous in `h`. -/
lemma enorm_czOperator_beurling_le_mul {R : ℝ} (_hR : 0 < R) (x : ℂ) {h : ℂ → ℂ}
    (hh : MemLp h 2 volume) :
    ‖czOperator beurlingKernel R h x‖ₑ
      ≤ eLpNorm (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) 2 volume
        * eLpNorm h 2 volume := by
  unfold czOperator
  have hcs : ∫⁻ y in (Metric.ball x R)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ
      ≤ eLpNorm (fun y => beurlingKernel x y) 2 (volume.restrict (Metric.ball x R)ᶜ)
        * eLpNorm h 2 (volume.restrict (Metric.ball x R)ᶜ) := by
    have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
      (μ := volume.restrict (Metric.ball x R)ᶜ)
      (p := 2) (q := 2) ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
      (f := fun y => ‖beurlingKernel x y‖ₑ) (g := fun y => ‖h y‖ₑ)
      (by unfold beurlingKernel; fun_prop) hh.aestronglyMeasurable.enorm.restrict
    simpa [eLpNorm_enorm] using this
  calc ‖∫ y in (Metric.ball x R)ᶜ, beurlingKernel x y * h y‖ₑ
      ≤ ∫⁻ y in (Metric.ball x R)ᶜ, ‖beurlingKernel x y * h y‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in (Metric.ball x R)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
    _ ≤ eLpNorm (fun y => beurlingKernel x y) 2 (volume.restrict (Metric.ball x R)ᶜ)
          * eLpNorm h 2 (volume.restrict (Metric.ball x R)ᶜ) := hcs
    _ ≤ eLpNorm (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) 2 volume
          * eLpNorm h 2 volume := by
        refine mul_le_mul' ?_ ?_
        · exact le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm
        · exact eLpNorm_restrict_le h 2 volume _

/-- **Maximal-operator `L²` bound on the smooth dense class.** For `f` smooth with
compact support (`BoundedFiniteSupport`), the simple nontangential (maximal
truncated) Beurling operator is bounded `L² → L²` with constant `C10_1_6 4`
(`simple_nontangential_operator_le`, threading the uniform truncation bound). -/
lemma eLpNorm_simpleNontangential_beurling_le {f : ℂ → ℂ} (hf : BoundedFiniteSupport f volume) :
    eLpNorm (simpleNontangentialOperator beurlingKernel 0 f) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume :=
  (simple_nontangential_operator_le (a := 4) (by norm_num)
    (fun r hr => czOperator_beurling_strongType_L2 hr) (le_refl 0) f hf).2

/-- `eLpNorm`-convergence from `eLpNorm`-difference convergence: if
`‖f - gₙ‖₂ → 0` then `‖gₙ‖₂ → ‖f‖₂` (reverse triangle, `ℝ≥0∞` squeeze). -/
lemma tendsto_eLpNorm_of_tendsto_sub {f : ℂ → ℂ} {g : ℕ → ℂ → ℂ}
    (hf : MemLp f 2 volume) (hg : ∀ n, MemLp (g n) 2 volume)
    (htend : Tendsto (fun n => eLpNorm (f - g n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (g n) 2 volume) atTop (𝓝 (eLpNorm f 2 volume)) := by
  set L := eLpNorm f 2 volume with hL
  set d := fun n => eLpNorm (f - g n) 2 volume with hd
  have hupper : ∀ n, eLpNorm (g n) 2 volume ≤ L + d n := by
    intro n
    have h : eLpNorm (g n) 2 volume ≤ eLpNorm f 2 volume + eLpNorm (g n - f) 2 volume := by
      calc eLpNorm (g n) 2 volume = eLpNorm (f + (g n - f)) 2 volume := by
            congr 1; funext x; simp
        _ ≤ eLpNorm f 2 volume + eLpNorm (g n - f) 2 volume :=
            eLpNorm_add_le hf.aestronglyMeasurable ((hg n).sub hf).aestronglyMeasurable one_le_two
    rw [hL, hd]
    rw [show eLpNorm (g n - f) 2 volume = eLpNorm (f - g n) 2 volume from by
      rw [← eLpNorm_neg]; congr 1; funext x; simp] at h
    exact h
  have hlower : ∀ n, L - d n ≤ eLpNorm (g n) 2 volume := by
    intro n
    rw [tsub_le_iff_right]
    calc L = eLpNorm ((g n) + (f - g n)) 2 volume := by rw [hL]; congr 1; funext x; simp
      _ ≤ eLpNorm (g n) 2 volume + eLpNorm (f - g n) 2 volume :=
          eLpNorm_add_le (hg n).aestronglyMeasurable (hf.sub (hg n)).aestronglyMeasurable one_le_two
  have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
    simpa using tendsto_const_nhds.add htend
  have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
    simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend (Or.inr (by simp)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper

/-- A smooth compactly supported `L²`-approximating sequence: for `f ∈ L²` there is
a sequence `gₙ ∈ C^∞_c` with `‖f - gₙ‖₂ → 0` (`MemLp.exist_eLpNorm_sub_le`). -/
lemma exists_contDiff_seq_tendsto_L2 {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    ∃ g : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ (⊤:ℕ∞) (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      Tendsto (fun n => eLpNorm (f - g n) 2 volume) atTop (𝓝 0) := by
  choose g hgc hgsmooth hgle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le (by norm_num) one_le_two (ε := 1/(n+1)) (by positivity)
  refine ⟨g, hgsmooth, hgc, ?_⟩
  have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
    rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
    (fun n => zero_le _) hgle

/-- `BoundedFiniteSupport` for a smooth compactly supported function. -/
lemma boundedFiniteSupport_of_contDiff {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (hgc : HasCompactSupport g) : BoundedFiniteSupport g volume :=
  ⟨hg.continuous.memLp_top_of_hasCompactSupport hgc volume,
   lt_of_le_of_lt (measure_mono (subset_tsupport g)) hgc.measure_lt_top⟩

/-- **Per-point lower-semicontinuity of the truncation.** For fixed `R > 0`, `x'`,
the value `‖czOperator beurlingKernel R f x'‖` is `≤ liminf` of the corresponding
values for an `L²`-approximating sequence (Cauchy–Schwarz `L²`-continuity in `f`). -/
lemma enorm_czOperator_le_liminf {R : ℝ} (hR : 0 < R) (x' : ℂ) {f : ℂ → ℂ} {g : ℕ → ℂ → ℂ}
    (hf : MemLp f 2 volume) (hg : ∀ n, MemLp (g n) 2 volume)
    (htend : Tendsto (fun n => eLpNorm (f - g n) 2 volume) atTop (𝓝 0)) :
    ‖czOperator beurlingKernel R f x'‖ₑ
      ≤ liminf (fun n => ‖czOperator beurlingKernel R (g n) x'‖ₑ) atTop := by
  set C := eLpNorm
    (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) 2 volume
    with hC
  have hbd : ∀ n, ‖czOperator beurlingKernel R f x'‖ₑ
      ≤ ‖czOperator beurlingKernel R (g n) x'‖ₑ + C * eLpNorm (f - g n) 2 volume := by
    intro n
    have hsub : ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (g n) x'‖ₑ
        ≤ C * eLpNorm (f - g n) 2 volume := by
      rw [← czOperator_beurling_sub hR x' hf (hg n)]
      exact enorm_czOperator_beurling_le_mul hR x' (hf.sub (hg n))
    calc ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ ‖czOperator beurlingKernel R (g n) x'‖ₑ
          + ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (g n) x'‖ₑ := by
            rw [add_comm]
            exact le_trans (by rw [sub_add_cancel]) (enorm_add_le _ _)
      _ ≤ _ := by gcongr
  have hCne : C ≠ ⊤ := by rw [hC]; exact (memLp_kernelSection x' R hR).2.ne
  have hC0 : Tendsto (fun n => C * eLpNorm (f - g n) 2 volume) atTop (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul htend (Or.inr hCne))
  calc ‖czOperator beurlingKernel R f x'‖ₑ
      ≤ liminf (fun n => ‖czOperator beurlingKernel R (g n) x'‖ₑ
          + C * eLpNorm (f - g n) 2 volume) atTop :=
        le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hbd)
    _ = liminf (fun n => ‖czOperator beurlingKernel R (g n) x'‖ₑ) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero hC0 _

/-- **Maximal-operator `L²` bound on all of `L²`.** The simple nontangential
Beurling operator is bounded `L² → L²` (constant `C10_1_6 4`) for every `f ∈ L²`,
extended from the smooth dense class by per-point lower semicontinuity and Fatou. -/
lemma eLpNorm_simpleNontangential_beurling_le_L2 {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (simpleNontangentialOperator beurlingKernel 0 f) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume := by
  obtain ⟨g, hgsmooth, hgc, htend⟩ := exists_contDiff_seq_tendsto_L2 hf
  have hg : ∀ n, MemLp (g n) 2 volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  have hgBFS : ∀ n, BoundedFiniteSupport (g n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hgsmooth n) (hgc n)
  -- per-point: simpleNTO 0 f x ≤ liminf (simpleNTO 0 gₙ x)
  have hsup : ∀ x, simpleNontangentialOperator beurlingKernel 0 f x
      ≤ liminf (fun n => simpleNontangentialOperator beurlingKernel 0 (g n) x) atTop := by
    intro x
    unfold simpleNontangentialOperator
    refine iSup_le (fun R => iSup_le (fun hR => iSup_le (fun x' => iSup_le (fun hx' => ?_))))
    refine le_trans (enorm_czOperator_le_liminf hR x' hf hg htend) ?_
    refine liminf_le_liminf (Eventually.of_forall (fun n => ?_))
    exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x' (le_iSup_of_le hx' (le_refl _))))
  -- BFS bound on gₙ
  have hgbd : ∀ n, eLpNorm (simpleNontangentialOperator beurlingKernel 0 (g n)) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm (g n) 2 volume := fun n =>
    eLpNorm_simpleNontangential_beurling_le (hgBFS n)
  -- ‖gₙ‖₂ → ‖f‖₂
  have htnorm : Tendsto (fun n => (C10_1_6 4 : ℝ≥0∞) * eLpNorm (g n) 2 volume) atTop
      (𝓝 ((C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume)) := by
    refine ENNReal.Tendsto.const_mul (tendsto_eLpNorm_of_tendsto_sub hf hg htend) ?_
    right; exact ENNReal.coe_ne_top
  -- Fatou
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  have hpowliminf : ∀ (u : ℕ → ℝ≥0∞),
      liminf (fun n => (u n) ^ (2:ℝ)) atTop = (liminf u atTop) ^ (2:ℝ) := by
    intro u
    have hmono : Monotone (fun x : ℝ≥0∞ => x ^ (2:ℝ)) :=
      fun a b h => ENNReal.rpow_le_rpow h (by norm_num)
    exact (hmono.map_liminf_of_continuousAt u (ENNReal.continuous_rpow_const).continuousAt).symm
  have hmono : ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 f x‖ₑ ^ (2:ℝ)
      ≤ liminf (fun n => ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
        atTop := by
    have hle : ∀ x, ‖simpleNontangentialOperator beurlingKernel 0 f x‖ₑ ^ (2:ℝ)
        ≤ liminf (fun n => ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
          atTop := by
      intro x
      simp_rw [enorm_eq_self]
      rw [hpowliminf]
      gcongr
      exact hsup x
    refine le_trans (lintegral_mono hle) ?_
    refine lintegral_liminf_le (fun n => ?_)
    exact (lowerSemicontinuous_simpleNontangentialOperator.measurable).enorm.pow_const _
  calc (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 f x‖ₑ ^ (2:ℝ)) ^ (2:ℝ)⁻¹
      ≤ (liminf (fun n => ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
          atTop) ^ (2:ℝ)⁻¹ := by gcongr
    _ = liminf (fun n => (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
          ^ (2:ℝ)⁻¹) atTop := by
        have hmono2 : Monotone (fun x : ℝ≥0∞ => x ^ (2:ℝ)⁻¹) :=
          fun a b h => ENNReal.rpow_le_rpow h (by norm_num)
        exact hmono2.map_liminf_of_continuousAt _ (ENNReal.continuous_rpow_const).continuousAt
    _ = liminf (fun n => eLpNorm (simpleNontangentialOperator beurlingKernel 0 (g n)) 2 volume)
          atTop := by
        congr 1; funext n
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
        simp only [ENNReal.toReal_ofNat, one_div]
    _ ≤ liminf (fun n => (C10_1_6 4 : ℝ≥0∞) * eLpNorm (g n) 2 volume) atTop :=
        liminf_le_liminf (Eventually.of_forall hgbd)
    _ = (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume := htnorm.liminf_eq


/-- **Pointwise domination by the maximal operator.** For `R > 0`,
`‖czOperator beurlingKernel R f x‖ ≤ simpleNontangentialOperator beurlingKernel 0 f x`
(take the supremand at scale `R`, centre `x ∈ ball x R`). -/
lemma enorm_czOperator_le_simpleNontangential {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (x : ℂ) :
    ‖czOperator beurlingKernel R f x‖ₑ ≤ simpleNontangentialOperator beurlingKernel 0 f x := by
  unfold simpleNontangentialOperator
  exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x
    (le_iSup_of_le (Metric.mem_ball_self hR) (le_refl _))))

/-- **Uniform-in-`r` `L²` bound for the truncations on all of `L²`.** For every
`f ∈ L²` and `r > 0`, `‖czOperator beurlingKernel r f‖₂ ≤ C10_1_6 4 · ‖f‖₂`
(pointwise domination by the maximal operator, then `eLpNorm_simpleNontangential…`). -/
lemma eLpNorm_czOperator_beurling_L2 {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (czOperator beurlingKernel r f) 2 volume ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume := by
  refine le_trans (eLpNorm_mono_enorm (fun x => ?_)) (eLpNorm_simpleNontangential_beurling_le_L2 hf)
  exact enorm_czOperator_le_simpleNontangential hr f x

/-- The truncations are `AEStronglyMeasurable` for `f ∈ L²`. -/
lemma aestronglyMeasurable_czOperator_beurling {r : ℝ} {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    AEStronglyMeasurable (czOperator beurlingKernel r f) volume :=
  czOperator_aestronglyMeasurable hf.aestronglyMeasurable

/-- The truncations lie in `L²` for `f ∈ L²` (`r > 0`). -/
lemma memLp_czOperator_beurling {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (czOperator beurlingKernel r f) 2 volume :=
  ⟨aestronglyMeasurable_czOperator_beurling hf,
   lt_of_le_of_lt (eLpNorm_czOperator_beurling_L2 hr hf)
     (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

/-- **Smooth pointwise convergence of the truncations to the Beurling transform.**
For `ν ∈ C¹_c`, the truncated Beurling integrals converge as `r → 0⁺` to
`-π · beurling ν`. (Own helper, proved from `czOperator_beurling_tendsto_smooth`;
distinct from the untouched `beurling_ae_tendsto_smooth`.) -/
lemma czOperator_beurling_tendsto_neg_pi {ν : ℂ → ℂ} (hν : ContDiff ℝ 1 ν)
    (hνc : HasCompactSupport ν) (w : ℂ) :
    Filter.Tendsto (fun r => czOperator beurlingKernel r ν w) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * beurling ν w)) := by
  have h := czOperator_beurling_tendsto_smooth hν hνc w
  have hval : (∫ ζ, (dz ν ζ) / (ζ - w)) = -(π : ℂ) * beurling ν w := by
    have hlim : limUnder (𝓝[>] (0:ℝ))
        (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w)
        = (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      apply Filter.Tendsto.limUnder_eq
      have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w
          = czOperator beurlingKernel r ν w := fun r => rfl
      simpa only [hcz] using h
    have hb : beurling ν w = -(1 / (π : ℂ)) * (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      rw [beurling, hlim]
    rw [hb]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rwa [hval] at h

/-- `simpleNontangentialOperator beurlingKernel 0 g ∈ L²` for `g ∈ L²`. -/
lemma memLp_simpleNontangential_beurling {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (simpleNontangentialOperator beurlingKernel 0 g) 2 volume :=
  ⟨aestronglyMeasurable_simpleNontangentialOperator,
   lt_of_le_of_lt (eLpNorm_simpleNontangential_beurling_le_L2 hg)
     (ENNReal.mul_lt_top ENNReal.coe_lt_top hg.2)⟩

/-- **Chebyshev bound for the maximal Beurling operator.** The level set
`{simpleNontangentialOperator beurlingKernel 0 g ≥ a}` has measure
`≤ a⁻² (C10_1_6 4 · ‖g‖₂)²` (Markov–Chebyshev + the maximal `L²` bound). -/
lemma volume_simpleNontangential_ge_le {g : ℂ → ℂ} (hg : MemLp g 2 volume) {a : ℝ≥0∞}
    (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    volume {z | a ≤ simpleNontangentialOperator beurlingKernel 0 g z}
      ≤ a⁻¹ ^ 2 * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm g 2 volume) ^ 2 := by
  have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm volume (p := 2) (by norm_num) (by norm_num)
    (f := simpleNontangentialOperator beurlingKernel 0 g)
    aestronglyMeasurable_simpleNontangentialOperator (ε := a) ha (fun h => absurd h ha')
  simp only [ENNReal.toReal_ofNat, enorm_eq_self] at hcheb
  rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.rpow_natCast] at hcheb
  refine le_trans hcheb (mul_le_mul' (le_refl (a⁻¹ ^ 2)) ?_)
  exact pow_le_pow_left' (eLpNorm_simpleNontangential_beurling_le_L2 hg) 2

/-- **A net Cauchy criterion via `edist`.** If for every `ε > 0` the values
`F r` are eventually within `edist < ε` of each other (along `𝓝[>] 0` squared),
then `F` converges (completeness of `ℂ`). -/
lemma tendsto_of_cauchy_edist {F : ℝ → ℂ}
    (hcauchy : ∀ ε : ℝ≥0∞, 0 < ε →
      ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), edist (F p.1) (F p.2) < ε) :
    ∃ L, Tendsto F (𝓝[>] (0:ℝ)) (𝓝 L) := by
  have hC : Cauchy (map F (𝓝[>] (0:ℝ))) := by
    rw [cauchy_map_iff]
    refine ⟨by infer_instance, ?_⟩
    rw [(uniformity_basis_edist).tendsto_right_iff]
    intro ε hε
    exact hcauchy ε hε
  obtain ⟨L, hL⟩ := CompleteSpace.complete hC
  exact ⟨L, hL⟩

/-- **Oscillation control by the maximal operator.** For `f, ν ∈ L²`,
`edist (czOp r₁ f z) (czOp r₂ f z) ≤ edist (czOp r₁ ν z) (czOp r₂ ν z)
  + 2·simpleNontangentialOperator beurlingKernel 0 (f - ν) z`. -/
lemma edist_czOperator_oscillation {f ν : ℂ → ℂ} (hf : MemLp f 2 volume) (hν : MemLp ν 2 volume)
    (z : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    edist (czOperator beurlingKernel r₁ f z) (czOperator beurlingKernel r₂ f z)
      ≤ edist (czOperator beurlingKernel r₁ ν z) (czOperator beurlingKernel r₂ ν z)
        + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
  have hd1 : czOperator beurlingKernel r₁ f z - czOperator beurlingKernel r₁ ν z
      = czOperator beurlingKernel r₁ (f - ν) z := (czOperator_beurling_sub hr₁ z hf hν).symm
  have hd2 : czOperator beurlingKernel r₂ f z - czOperator beurlingKernel r₂ ν z
      = czOperator beurlingKernel r₂ (f - ν) z := (czOperator_beurling_sub hr₂ z hf hν).symm
  set Sf1 := czOperator beurlingKernel r₁ f z
  set Sf2 := czOperator beurlingKernel r₂ f z
  set Sn1 := czOperator beurlingKernel r₁ ν z
  set Sn2 := czOperator beurlingKernel r₂ ν z
  have hb1 : edist Sf1 Sn1 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    rw [edist_eq_enorm_sub, hd1]; exact enorm_czOperator_le_simpleNontangential hr₁ (f - ν) z
  have hb2 : edist Sn2 Sf2 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    rw [edist_comm, edist_eq_enorm_sub, hd2]
    exact enorm_czOperator_le_simpleNontangential hr₂ (f - ν) z
  calc edist Sf1 Sf2 ≤ edist Sf1 Sn1 + edist Sn1 Sn2 + edist Sn2 Sf2 := by
        refine le_trans (edist_triangle Sf1 Sn2 Sf2) ?_
        gcongr
        exact edist_triangle Sf1 Sn1 Sn2
    _ = edist Sn1 Sn2 + (edist Sf1 Sn1 + edist Sn2 Sf2) := by ring
    _ ≤ edist Sn1 Sn2 + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
        gcongr; rw [two_mul]; gcongr

/-- **Per-point Cauchy from smooth convergence + small maximal value.** If
`czOp · ν z` converges and `2·simpleNontangentialOperator beurlingKernel 0 (f-ν) z
< a/2`, then `edist (czOp p.1 f z) (czOp p.2 f z) < a` eventually. -/
lemma eventually_edist_lt_of_smooth_conv {f ν : ℂ → ℂ} (hf : MemLp f 2 volume)
    (hν : MemLp ν 2 volume) (z : ℂ) {a : ℝ≥0∞} (ha : 0 < a)
    (hconv : ∃ L, Tendsto (fun r => czOperator beurlingKernel r ν z) (𝓝[>] (0:ℝ)) (𝓝 L))
    (hsmall : 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z < a / 2) :
    ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a := by
  obtain ⟨L, hL⟩ := hconv
  have hνcauchy : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 ν z) (czOperator beurlingKernel p.2 ν z) < a / 2 := by
    have hmap : Tendsto (fun p : ℝ × ℝ =>
        (czOperator beurlingKernel p.1 ν z, czOperator beurlingKernel p.2 ν z))
        ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (L, L)) :=
      (hL.comp tendsto_fst).prodMk_nhds (hL.comp tendsto_snd)
    have ht : Tendsto (fun p : ℝ × ℝ =>
        edist (czOperator beurlingKernel p.1 ν z) (czOperator beurlingKernel p.2 ν z))
        ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (edist L L)) :=
      (continuous_edist.tendsto _).comp hmap
    rw [edist_self] at ht
    exact ht (Iio_mem_nhds (ENNReal.half_pos (ne_of_gt ha)))
  have hpos : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), 0 < p.1 ∧ 0 < p.2 := by
    rw [eventually_prod_iff]
    refine ⟨fun r => 0 < r, ?_, fun r => 0 < r, ?_, fun {r₁} h1 {r₂} h2 => ⟨h1, h2⟩⟩
    · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
    · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
  filter_upwards [hνcauchy, hpos] with p hp hppos
  obtain ⟨hp1, hp2⟩ := hppos
  calc edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z)
      ≤ edist (czOperator beurlingKernel p.1 ν z) (czOperator beurlingKernel p.2 ν z)
        + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z :=
        edist_czOperator_oscillation hf hν z hp1 hp2
    _ < a / 2 + a / 2 := ENNReal.add_lt_add hp hsmall
    _ = a := ENNReal.add_halves a

/-- **Null oscillation set.** For `f ∈ L²` and `a > 0`, the set where the
truncations fail to be `edist`-Cauchy at level `a` is null. The smooth dense
approximants converge everywhere (`czOperator_beurling_tendsto_neg_pi`), so the
bad set sits inside `{simpleNontangentialOperator beurlingKernel 0 (f-gₙ) ≥ a/4}`,
whose measure `→ 0` as `gₙ → f` in `L²` (Chebyshev). -/
lemma volume_oscillation_set_eq_zero {f : ℂ → ℂ} (hf : MemLp f 2 volume) {a : ℝ≥0∞}
    (ha : 0 < a) (ha' : a ≠ ⊤) :
    volume {z | ¬ ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a} = 0 := by
  set b := a / 4 with hb
  have hbpos : 0 < b := ENNReal.div_pos (ne_of_gt ha) (by norm_num)
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hbtop : b ≠ ⊤ := (ENNReal.div_lt_top ha' (by norm_num)).ne
  obtain ⟨g, hgsmooth, hgc, htend⟩ := exists_contDiff_seq_tendsto_L2 hf
  have hg : ∀ n, MemLp (g n) 2 volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  set B := {z | ¬ ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a} with hBdef
  have hsubset : ∀ n, B ⊆ {z | b ≤ simpleNontangentialOperator beurlingKernel 0 (f - g n) z} := by
    intro n z hz
    by_contra hlt
    rw [Set.mem_setOf_eq, not_le] at hlt
    apply hz
    refine eventually_edist_lt_of_smooth_conv hf (hg n) z ha
      ⟨_, czOperator_beurling_tendsto_neg_pi ((hgsmooth n).of_le (by exact_mod_cast le_top))
        (hgc n) z⟩ ?_
    rw [hb] at hlt
    calc 2 * simpleNontangentialOperator beurlingKernel 0 (f - g n) z
        < 2 * (a / 4) := by gcongr; exact (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
      _ = a / 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm (2:ℝ≥0∞) a, mul_assoc]
          congr 1
          rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
            ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hmeas : ∀ n, volume B ≤ b⁻¹ ^ 2 * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) ^ 2 :=
    fun n => le_trans (measure_mono (hsubset n))
      (volume_simpleNontangential_ge_le (hf.sub (hg n)) hbne hbtop)
  have hto0 : Tendsto (fun n => b⁻¹ ^ 2 * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.coe_ne_top)
    have h2 : Tendsto (fun n => ((C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) ^ 2) atTop
        (𝓝 0) := by
      have h := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h1
      rw [show ((0:ℝ≥0∞)^2) = 0 by norm_num] at h
      exact h
    have hbinv : b⁻¹ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hbne)
    have h3 := ENNReal.Tendsto.const_mul (a := b⁻¹ ^ 2) h2 (Or.inr hbinv)
    rw [mul_zero] at h3
    exact h3
  exact le_antisymm (ge_of_tendsto hto0 (Eventually.of_forall hmeas)) (zero_le _)

/-- **A.e. existence of the principal-value limit.** For every `f ∈ L²` the
truncated Beurling integrals `czOperator beurlingKernel r f z` converge as
`r → 0⁺` for almost every `z` (maximal-operator + dense-class a.e. convergence). -/
lemma czOperator_beurling_ae_tendsto {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    ∀ᵐ z ∂volume, ∃ L, Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ)) (𝓝 L) := by
  set Bk := fun k : ℕ => {z | ¬ ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z)
        < 1/((k:ℝ≥0∞)+1)} with hBk
  have hBknull : ∀ k, volume (Bk k) = 0 := by
    intro k
    apply volume_oscillation_set_eq_zero hf
    · apply ENNReal.div_pos one_ne_zero
      exact (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩).ne
    · apply ENNReal.div_ne_top ENNReal.one_ne_top
      have hkp : (0:ℝ≥0∞) < (k:ℝ≥0∞)+1 := by positivity
      exact hkp.ne'
  have hunionnull : volume (⋃ k, Bk k) = 0 := measure_iUnion_null hBknull
  rw [ae_iff]
  refine measure_mono_null ?_ hunionnull
  intro z hz
  rw [Set.mem_setOf_eq] at hz
  rw [Set.mem_iUnion]
  by_contra hnot
  push_neg at hnot
  apply hz
  apply tendsto_of_cauchy_edist
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
  have hmem := hnot k
  simp only [hBk, Set.mem_setOf_eq, not_not] at hmem
  refine hmem.mono (fun p hp => lt_of_lt_of_le hp ?_)
  rw [one_div]
  calc ((k:ℝ≥0∞)+1)⁻¹ ≤ ((k:ℝ≥0∞))⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    _ ≤ ε := le_of_lt hk

/-- **A.e. convergence to the Beurling transform.** For `f ∈ L²`, the truncated
integrals converge a.e. as `r → 0⁺` to `-π · beurling f`. Where the limit exists
(`czOperator_beurling_ae_tendsto`) it pins the defining `limUnder`, identifying
`beurling f z` with `-(1/π)·(a.e. limit)`. -/
lemma czOperator_beurling_ae_tendsto_neg_pi {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    ∀ᵐ z ∂volume, Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π:ℂ) * beurling f z)) := by
  filter_upwards [czOperator_beurling_ae_tendsto hf] with z hz
  obtain ⟨L, hL⟩ := hz
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z) = L := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z
        = czOperator beurlingKernel r f z := fun r => rfl
    simpa only [hcz] using hL
  have hb : beurling f z = -(1 / (π : ℂ)) * L := by rw [beurling, hlim]
  have hval : -(π:ℂ) * beurling f z = L := by
    rw [hb]; have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hval]; exact hL

/-- **`Lᵖ`-bound shape for the Beurling transform (`p = 2`).** `eLpNorm (beurling h) 2
≤ (C10_1_6 4 / π) · eLpNorm h 2` for `h ∈ L²` — Fatou applied to the uniformly
`L²`-bounded truncations along a sequence `rₙ → 0⁺`, using the a.e. limit
`-π·beurling h`. (`AEStronglyMeasurable (beurling h)` follows.) -/
lemma eLpNorm_beurling_le {h : ℂ → ℂ} (hh : MemLp h 2 volume) :
    eLpNorm (beurling h) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ * eLpNorm h 2 volume := by
  set r : ℕ → ℝ := fun n => 1/(n+1:ℝ) with hr
  have hrpos : ∀ n, 0 < r n := fun n => by rw [hr]; positivity
  have hrto : Tendsto r atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop), ?_⟩
    filter_upwards with n; simp only [Set.mem_Ioi, hr]; positivity
  have hbound : ∀ n, eLpNorm (czOperator beurlingKernel (r n) h) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm h 2 volume :=
    fun n => eLpNorm_czOperator_beurling_L2 (hrpos n) hh
  have hmeas : ∀ n, AEStronglyMeasurable (czOperator beurlingKernel (r n) h) volume :=
    fun n => aestronglyMeasurable_czOperator_beurling hh
  have hae : ∀ᵐ z ∂volume, Tendsto (fun n => czOperator beurlingKernel (r n) h z) atTop
      (𝓝 (-(π:ℂ) * beurling h z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi hh] with z hz
    exact hz.comp hrto
  have hfatou := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound) hmeas hae
  have heq : eLpNorm (fun z => -(π:ℂ) * beurling h z) 2 volume
      = ENNReal.ofReal π * eLpNorm (beurling h) 2 volume := by
    have he : (fun z => -(π:ℂ) * beurling h z) = (-(π:ℂ)) • (beurling h) := by
      funext z; simp [Pi.smul_apply, smul_eq_mul]
    rw [he, eLpNorm_const_smul]
    congr 1
    rw [← ofReal_norm_eq_enorm, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [heq] at hfatou
  -- π · ‖Th‖ ≤ C ‖h‖  ⟹  ‖Th‖ ≤ C π⁻¹ ‖h‖
  have hπpos : (0:ℝ≥0∞) < ENNReal.ofReal π := by simp [Real.pi_pos]
  have hπtop : ENNReal.ofReal π ≠ ⊤ := ENNReal.ofReal_ne_top
  have hπne : ENNReal.ofReal π ≠ 0 := ne_of_gt hπpos
  calc eLpNorm (beurling h) 2 volume
      = (ENNReal.ofReal π)⁻¹ * (ENNReal.ofReal π * eLpNorm (beurling h) 2 volume) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hπne hπtop, one_mul]
    _ ≤ (ENNReal.ofReal π)⁻¹ * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm h 2 volume) := by gcongr
    _ = (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ * eLpNorm h 2 volume := by ring

/-- **A.e. additivity of the Beurling transform.** For `f, g ∈ L²`,
`beurling (f - g) =ᵐ beurling f - beurling g` (the truncations are linear and all
three limits exist a.e.). -/
lemma beurling_sub_ae {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    beurling (f - g) =ᵐ[volume] fun z => beurling f z - beurling g z := by
  filter_upwards [czOperator_beurling_ae_tendsto_neg_pi hf,
    czOperator_beurling_ae_tendsto_neg_pi hg,
    czOperator_beurling_ae_tendsto_neg_pi (hf.sub hg)] with z hzf hzg hzfg
  have hlin : ∀ᶠ r in 𝓝[>] (0:ℝ), czOperator beurlingKernel r (f - g) z
      = czOperator beurlingKernel r f z - czOperator beurlingKernel r g z := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact czOperator_beurling_sub hr z hf hg
  have hsub : Tendsto (fun r => czOperator beurlingKernel r (f - g) z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π:ℂ) * beurling f z - -(π:ℂ) * beurling g z)) := by
    refine (hzf.sub hzg).congr' ?_
    filter_upwards [hlin] with r hr; exact hr.symm
  have huniq := tendsto_nhds_unique hzfg hsub
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hmul : -(π:ℂ) * beurling (f - g) z = -(π:ℂ) * (beurling f z - beurling g z) := by
    rw [huniq]; ring
  exact mul_left_cancel₀ (by simp [hπ]) hmul

/-- `AEStronglyMeasurable (beurling f)` for `f ∈ L²` (it is `-(1/π)` times the a.e.
limit of the measurable truncations). -/
lemma aestronglyMeasurable_beurling {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    AEStronglyMeasurable (beurling f) volume := by
  set r : ℕ → ℝ := fun n => 1/(n+1:ℝ) with hr
  have hrpos : ∀ n, 0 < r n := fun n => by rw [hr]; positivity
  have hrto : Tendsto r atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop), ?_⟩
    filter_upwards with n; simp only [Set.mem_Ioi, hr]; positivity
  have hae : ∀ᵐ z ∂volume, Tendsto (fun n => czOperator beurlingKernel (r n) f z) atTop
      (𝓝 (-(π:ℂ) * beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi hf] with z hz
    exact hz.comp hrto
  have hmeas : AEStronglyMeasurable (fun z => -(π:ℂ) * beurling f z) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_czOperator_beurling hf) hae
  have heq : beurling f = fun z => (-(1/(π:ℂ))) * (-(π:ℂ) * beurling f z) := by
    funext z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [heq]
  exact hmeas.const_mul _

/-- `beurling f ∈ L²` for `f ∈ L²`. -/
lemma memLp_beurling {f : ℂ → ℂ} (hf : MemLp f 2 volume) : MemLp (beurling f) 2 volume :=
  ⟨aestronglyMeasurable_beurling hf,
   lt_of_le_of_lt (eLpNorm_beurling_le hf)
     (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
       (by simp [ENNReal.inv_lt_top, Real.pi_pos])) hf.2)⟩

/-- **`L²` bound for the Beurling transform of a difference.** For `f, ν ∈ L²`,
`eLpNorm (beurling f - beurling ν) 2 ≤ (C10_1_6 4 / π) · ‖f - ν‖₂` (`beurling_sub_ae`
turns the difference into `beurling (f - ν)`, then `eLpNorm_beurling_le`). -/
lemma eLpNorm_beurling_sub_le {f ν : ℂ → ℂ} (hf : MemLp f 2 volume) (hν : MemLp ν 2 volume) :
    eLpNorm (fun z => beurling f z - beurling ν z) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ * eLpNorm (f - ν) 2 volume := by
  rw [← eLpNorm_congr_ae (beurling_sub_ae hf hν)]
  exact eLpNorm_beurling_le (hf.sub hν)

/-- **`L²` isometry.** `‖Tμ‖₂ = ‖μ‖₂`: the Beurling transform is an `L²`
isometry, its Fourier multiplier `ξ̄/ξ` having modulus one. -/
theorem beurling_l2_isometry (hμ : MemLp μ 2 volume) :
    eLpNorm (beurling μ) 2 volume = eLpNorm μ 2 volume := by
  set Cst : ℝ≥0∞ := (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ with hCst
  have hCsttop : Cst ≠ ⊤ := by
    rw [hCst]
    exact (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (by simp [ENNReal.inv_lt_top, Real.pi_pos])).ne
  set A := (eLpNorm (beurling μ) 2 volume).toReal with hA
  set B := (eLpNorm μ 2 volume).toReal with hB
  set Cr : ℝ := Cst.toReal with hCr
  have hCrnn : 0 ≤ Cr := ENNReal.toReal_nonneg
  have hAf : eLpNorm (beurling μ) 2 volume ≠ ⊤ := (memLp_beurling hμ).2.ne
  have hBf : eLpNorm μ 2 volume ≠ ⊤ := hμ.2.ne
  -- main estimate: |A - B| ≤ (Cr + 1) * ε for all ε > 0
  have hmain : ∀ ε : ℝ, 0 < ε → |A - B| ≤ (Cr + 1) * ε := by
    intro ε hε
    obtain ⟨ν, hνc, hνsmooth, hνle⟩ :=
      hμ.exist_eLpNorm_sub_le (by norm_num) one_le_two (ε := ε) hε
    have hνmem : MemLp ν 2 volume := hνsmooth.continuous.memLp_of_hasCompactSupport hνc
    -- smooth isometry
    have hiso : eLpNorm (beurling ν) 2 volume = eLpNorm ν 2 volume :=
      beurling_l2_isometry_smooth hνsmooth hνc
    -- ‖μ - ν‖₂ ≤ ε
    have hsubnorm : eLpNorm (μ - ν) 2 volume ≤ ENNReal.ofReal ε := hνle
    -- ‖Tμ - Tν‖₂ ≤ Cst * ‖μ - ν‖₂ ≤ Cst * ε
    have hTsub : eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume
        ≤ Cst * ENNReal.ofReal ε := by
      refine le_trans (eLpNorm_beurling_sub_le hμ hνmem) ?_
      rw [hCst]; gcongr
    -- Now convert to ℝ.  Let Nν := ‖ν‖₂.toReal = ‖Tν‖₂.toReal.
    set Nν := (eLpNorm ν 2 volume).toReal with hNν
    have hνf : eLpNorm ν 2 volume ≠ ⊤ := hνmem.2.ne
    -- |A - Nν| ≤ Cr ε  (from triangle both ways)
    have hub1 : eLpNorm (beurling μ) 2 volume ≤ eLpNorm (beurling ν) 2 volume
        + eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume := by
      calc eLpNorm (beurling μ) 2 volume
          = eLpNorm (beurling ν + (fun z => beurling μ z - beurling ν z)) 2 volume := by
            congr 1; funext z; simp
        _ ≤ _ := eLpNorm_add_le (memLp_beurling hνmem).1
            ((memLp_beurling hμ).sub (memLp_beurling hνmem)).1 one_le_two
    have hub2 : eLpNorm (beurling ν) 2 volume ≤ eLpNorm (beurling μ) 2 volume
        + eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume := by
      calc eLpNorm (beurling ν) 2 volume
          = eLpNorm (beurling μ - (fun z => beurling μ z - beurling ν z)) 2 volume := by
            congr 1; funext z; simp
        _ ≤ eLpNorm (beurling μ) 2 volume
            + eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume :=
            eLpNorm_sub_le (memLp_beurling hμ).1
              ((memLp_beurling hμ).sub (memLp_beurling hνmem)).1 one_le_two
    -- toReal: A ≤ Nν + Cr ε  and Nν ≤ A + Cr ε
    have hCstε : (Cst * ENNReal.ofReal ε).toReal = Cr * ε := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le, hCr]
    have hTsubR : (eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume).toReal ≤ Cr * ε := by
      rw [← hCstε]
      exact ENNReal.toReal_mono (by finiteness) hTsub
    have hTsubfin : eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume ≠ ⊤ :=
      ne_top_of_le_ne_top (by finiteness) hTsub
    have hAub : A ≤ Nν + Cr * ε := by
      rw [hA, hNν, ← hiso]
      refine le_trans (ENNReal.toReal_mono ?_ hub1) ?_
      · exact ENNReal.add_ne_top.mpr ⟨(memLp_beurling hνmem).2.ne, hTsubfin⟩
      · rw [ENNReal.toReal_add (memLp_beurling hνmem).2.ne hTsubfin]
        gcongr
    have hNνub : Nν ≤ A + Cr * ε := by
      rw [hNν, hA, ← hiso]
      refine le_trans (ENNReal.toReal_mono ?_ hub2) ?_
      · exact ENNReal.add_ne_top.mpr ⟨(memLp_beurling hμ).2.ne, hTsubfin⟩
      · rw [ENNReal.toReal_add (memLp_beurling hμ).2.ne hTsubfin]
        gcongr
    -- |Nν - B| ≤ ε
    have hμνR : (eLpNorm (μ - ν) 2 volume).toReal ≤ ε :=
      le_trans (ENNReal.toReal_mono (by finiteness) hsubnorm) (by rw [ENNReal.toReal_ofReal hε.le])
    have hμνfin : eLpNorm (μ - ν) 2 volume ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hsubnorm
    have hNνB1 : Nν ≤ B + ε := by
      rw [hNν, hB]
      have : eLpNorm ν 2 volume ≤ eLpNorm μ 2 volume + eLpNorm (μ - ν) 2 volume := by
        calc eLpNorm ν 2 volume = eLpNorm (μ - (μ - ν)) 2 volume := by congr 1; funext z; simp
          _ ≤ _ := eLpNorm_sub_le hμ.1 (hμ.sub hνmem).1 one_le_two
      refine le_trans (ENNReal.toReal_mono (by finiteness) this) ?_
      rw [ENNReal.toReal_add hBf hμνfin]; gcongr
    have hNνB2 : B ≤ Nν + ε := by
      rw [hNν, hB]
      have : eLpNorm μ 2 volume ≤ eLpNorm ν 2 volume + eLpNorm (μ - ν) 2 volume := by
        calc eLpNorm μ 2 volume = eLpNorm (ν + (μ - ν)) 2 volume := by congr 1; funext z; simp
          _ ≤ _ := eLpNorm_add_le hνmem.1 (hμ.sub hνmem).1 one_le_two
      refine le_trans (ENNReal.toReal_mono (by finiteness) this) ?_
      rw [ENNReal.toReal_add hνf hμνfin]; gcongr
    -- combine: |A - B| ≤ |A - Nν| + |Nν - B| ≤ Cr ε + ε ≤ (Cr+1) ε
    have h1 : |A - Nν| ≤ Cr * ε := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |Nν - B| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |A - B| ≤ |A - Nν| + |Nν - B| := by
          rw [show A - B = (A - Nν) + (Nν - B) by ring]; exact abs_add_le _ _
      _ ≤ Cr * ε + ε := add_le_add h1 h2
      _ = (Cr + 1) * ε := by ring
  -- from |A - B| ≤ (Cr+1) ε for all ε ⟹ A = B ⟹ eLpNorm equal
  have hAB : A = B := by
    have h0 : |A - B| ≤ 0 := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      rw [zero_add]
      calc |A - B| ≤ (Cr+1) * (ε / (Cr+1)) := hmain _ (by positivity)
        _ = ε := by field_simp
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _)))
  rw [← ENNReal.toReal_eq_toReal hAf hBf]; exact hAB



/-! ## `Lᵖ` boundedness: uniform bounds on the truncations

For `1 < p < 2` the truncated Beurling operator `czOperator beurlingKernel r` is
bounded `Lᵖ → Lᵖ` with a constant independent of `r`, by Marcinkiewicz
interpolation between its weak-(1,1) bound (`czOperator_weak_1_1`, upgraded from
`BoundedFiniteSupport` to all of `L¹`) and its strong-(2,2) bound
(`eLpNorm_czOperator_beurling_L2`). Passing `r → 0⁺` (a.e. convergence + Fatou)
then transfers the bound to the Beurling transform itself. -/

/-- Integrability of the truncated Beurling integrand against an `L¹` function:
on `(ball x r)ᶜ` the kernel is bounded by `r⁻²`, so `K(x,·)·f` is integrable for
`f ∈ L¹`. -/
lemma integrableOn_beurlingKernel_mul_L1 {r : ℝ} (hr : 0 < r) (x : ℂ) {f : ℂ → ℂ}
    (hf : MemLp f 1 volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  -- `f` is integrable; restrict to `(ball x r)ᶜ`.
  have hfint : Integrable f volume := memLp_one_iff_integrable.mp hf
  rw [IntegrableOn]
  -- The kernel `beurlingKernel x ·` is `AEStronglyMeasurable`.
  have hker_meas : AEStronglyMeasurable (fun y => beurlingKernel x y)
      (volume.restrict (Metric.ball x r)ᶜ) := by
    apply Measurable.aestronglyMeasurable
    unfold beurlingKernel; fun_prop
  -- On `(ball x r)ᶜ` the kernel is bounded by `r⁻²`.
  have hbound : ∀ᵐ y ∂(volume.restrict (Metric.ball x r)ᶜ),
      ‖beurlingKernel x y‖ ≤ (r : ℝ) ^ (-2 : ℤ) := by
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    -- `y ∉ ball x r ⇒ r ≤ dist x y = ‖x - y‖`.
    have hr_le : r ≤ ‖x - y‖ := by
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_comm] at hy
      rw [Complex.dist_eq] at hy; exact hy
    have hxy_pos : 0 < ‖x - y‖ := lt_of_lt_of_le hr hr_le
    have hnorm : ‖beurlingKernel x y‖ = ‖x - y‖ ^ (-2 : ℤ) := by
      rw [beurlingKernel, norm_zpow]
    rw [hnorm, zpow_neg, zpow_neg, zpow_two, zpow_two]
    -- `(‖x-y‖ * ‖x-y‖)⁻¹ ≤ (r * r)⁻¹`.
    apply inv_anti₀ (by positivity)
    exact mul_le_mul hr_le hr_le hr.le hxy_pos.le
  -- Apply `Integrable.bdd_mul` with bounded factor the kernel.
  exact Integrable.bdd_mul (hfint.restrict) hker_meas hbound

/-- Integrability of the truncated Beurling integrand against an `Lᵖ` function,
`1 < p < ∞`: the kernel section lies in `Lᵖ'` (since `∫_{|u|≥r} |u|^{-2p'} < ∞`
for `p' < ∞`), so the product is in `L¹` by Hölder. -/
lemma integrableOn_beurlingKernel_mul_Lp {r : ℝ} (hr : 0 < r) (x : ℂ) {p p' : ℝ≥0∞}
    (hp1 : 1 < p) (hp_top : p ≠ ⊤) [ENNReal.HolderConjugate p p'] {f : ℂ → ℂ}
    (hf : MemLp f p volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  -- The conjugate exponent `p'` is finite and `> 1`.
  haveI : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
  have hp'_top : p' ≠ ⊤ := by
    have : p' < ⊤ := (ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1
    exact this.ne
  have hp'1 : 1 < p' := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp
    (lt_of_le_of_ne le_top hp_top)
  set q' : ℝ := p'.toReal with hq'_def
  have hp'0 : p' ≠ 0 := by
    rintro rfl; exact absurd hp'1 (by simp)
  have hq'1 : 1 < q' := by
    rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
    exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
  have hq'0 : 0 < q' := lt_trans one_pos hq'1
  -- **Finite mass of the truncated kernel section at exponent `q'`.**
  -- `∫_{‖u‖≥r} ((‖u‖ₑ^2)⁻¹)^q' < ∞` via polar coordinates, `∫_r^∞ ρ^{1-2q'} dρ < ∞`.
  have hlint : ∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
    rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal := fun p =>
      (Set.Ici r ×ˢ Set.Ioo (-π) π).indicator
        (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      exact (Real.continuous_rpow_const hq'0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
    have hbound : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • {u : ℂ | r ≤ ‖u‖}.indicator
          (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm p) ≤ box p := by
      intro p hp
      rw [polarCoord_target, Set.mem_prod] at hp
      obtain ⟨hp1', hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1'
      simp only [hbox]
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp1']
      by_cases hmem : Complex.polarCoord.symm p ∈ {u : ℂ | r ≤ ‖u‖}
      · have hpR : r ≤ p.1 := by rw [Set.mem_setOf_eq, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hp2⟩)]
        have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          show ((ENNReal.ofReal p.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((p.1^2)⁻¹)^q') by
            rw [← ENNReal.ofReal_pow hp1'.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
              ENNReal.ofReal_rpow_of_pos (by positivity)],
          ← ENNReal.ofReal_mul hp1'.le]
      · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le _
    refine lt_of_le_of_lt (setLIntegral_mono
      (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
    calc ∫⁻ p in polarCoord.target, box p
        ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
      _ = ∫⁻ p in (Set.Ici r ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q') := by
            rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
            simp only [setLIntegral_const]
            rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
            apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
            have hint : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici r) volume := by
              have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                  =ᶠ[ae (volume.restrict (Set.Ici r))]
                  (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                simp only [Set.mem_Ici] at hρ
                have hρpos : 0 < ρ := lt_of_lt_of_le hr hρ
                have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                  rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                have h1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                  rw [hbase, ← Real.rpow_mul hρpos.le]
                have h2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                  nth_rewrite 1 [← Real.rpow_one ρ]
                  rw [← Real.rpow_add hρpos]; congr 1; ring
                rw [h1, h2]
              rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                integrableOn_Ioi_rpow_iff hr]
              -- `1 - 2 q' < -1 ↔ q' > 1`.
              nlinarith [hq'1]
            have hfin := hint.2
            rw [hasFiniteIntegral_iff_enorm] at hfin
            refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
            · refine (measurable_id.mul ?_).enorm
              exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                ((measurable_id.pow_const 2).inv)
            · simp only [Set.mem_Ici] at hy
              have hypos : 0 < y := lt_of_lt_of_le hr hy
              rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- **Kernel section ∈ Lᵖ'.**
  have hker : MemLp (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p'
      volume := by
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top]
    rw [← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y‖ₑ ^ q'
        = (Metric.ball x r)ᶜ.indicator (fun y => ‖beurlingKernel x y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x y‖ₑ ^ q' ≤ ((‖x - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x = y
      · subst h; simp [beurlingKernel]
      · have hne : x - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x y = ((x-y) * (x-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x r)ᶜ.indicator (fun y => ((‖x - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x r)ᶜ) ↔ (x - y ∈ {u : ℂ | r ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_setOf_eq, dist_comm, Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x]
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint
  rw [IntegrableOn]
  have h1 : MemLp (fun y => beurlingKernel x y) p' (volume.restrict (Metric.ball x r)ᶜ) := by
    apply MemLp.ae_eq _ (hker.restrict (Metric.ball x r)ᶜ)
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [Set.indicator_of_mem hy]
  exact h1.integrable_mul (hf.restrict _)

/-- The truncations are `AEStronglyMeasurable` for any measurable `f`. -/
lemma aestronglyMeasurable_czOperator_beurling' {r : ℝ} {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (czOperator beurlingKernel r f) volume :=
  czOperator_aestronglyMeasurable hf

/-- The truncated Beurling operator is weak-(1,1) on all of `L¹` (not just
`BoundedFiniteSupport`): the Carleson bound `czOperator_weak_1_1` extends by
`L¹` density and `wnorm` lower semicontinuity (the truncations converge uniformly
since the kernel is bounded by `r⁻²` on `(ball x r)ᶜ`). -/
lemma hasWeakType_czOperator_beurling_one {r : ℝ} (hr : 0 < r) :
    HasWeakType (czOperator beurlingKernel r) 1 1 volume volume (C10_0_3 4) := by
  intro f hf
  refine ⟨aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable, ?_⟩
  -- Carleson weak-(1,1) on `BoundedFiniteSupport`.
  have hBWT : HasBoundedWeakType (czOperator beurlingKernel r) 1 1 volume volume (C10_0_3 4) :=
    czOperator_weak_1_1 (show (4:ℕ) ≤ 4 by norm_num) hr (czOperator_beurling_strongType_L2 hr)
  -- The enorm of the truncated kernel on `(ball x r)ᶜ` is `≤ ofReal (r⁻²)`.
  have hkernelEnorm : ∀ (x y : ℂ), y ∈ (Metric.ball x r)ᶜ →
      ‖beurlingKernel x y‖ₑ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := by
    intro x y hy
    have hr_le : r ≤ ‖x - y‖ := by
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_comm] at hy
      rw [Complex.dist_eq] at hy; exact hy
    have hxy_pos : 0 < ‖x - y‖ := lt_of_lt_of_le hr hr_le
    have hnorm : ‖beurlingKernel x y‖ = ‖x - y‖ ^ (-2 : ℤ) := by
      rw [beurlingKernel, norm_zpow]
    have hle : ‖beurlingKernel x y‖ ≤ (r : ℝ) ^ (-2 : ℤ) := by
      rw [hnorm, zpow_neg, zpow_neg, zpow_two, zpow_two]
      apply inv_anti₀ (by positivity)
      exact mul_le_mul hr_le hr_le hr.le hxy_pos.le
    calc ‖beurlingKernel x y‖ₑ = ENNReal.ofReal ‖beurlingKernel x y‖ :=
          (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := ENNReal.ofReal_le_ofReal hle
  -- The `L¹` operator bound: `‖czOp h x‖ₑ ≤ ofReal(r⁻²) · ‖h‖₁`.
  have hOpBound : ∀ (h : ℂ → ℂ) (x : ℂ),
      ‖czOperator beurlingKernel r h x‖ₑ
        ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
    intro h x
    have hczeq : czOperator beurlingKernel r h x
        = ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y := rfl
    rw [hczeq]
    calc ‖∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y * h y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ‖h y‖ₑ := by
          refine setLIntegral_mono' measurableSet_ball.compl (fun y hy => ?_)
          exact mul_le_mul' (hkernelEnorm x y hy) le_rfl
      _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ))
            * ∫⁻ y in (Metric.ball x r)ᶜ, ‖h y‖ₑ := by rw [lintegral_const_mul']; finiteness
      _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ∫⁻ y, ‖h y‖ₑ := by
          exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm]
  -- An approximating sequence of simple functions, `‖f - gₖ‖₁ → 0`, each `BoundedFiniteSupport`.
  have hεne : ∀ k : ℕ, (((k : ℝ≥0∞) + 1))⁻¹ ≠ 0 := by
    intro k; exact ENNReal.inv_ne_zero.mpr (by finiteness)
  choose g hgle hgmem using fun k : ℕ =>
    hf.exists_simpleFunc_eLpNorm_sub_lt (by simp) (hεne k)
  -- Each `gₖ` (as a function) is `BoundedFiniteSupport`.
  have hgBFS : ∀ k, BoundedFiniteSupport (⇑(g k)) volume := by
    intro k
    refine ⟨(g k).memLp_top volume, ?_⟩
    exact (g k).measure_support_lt_top_of_memLp (hgmem k) one_ne_zero ENNReal.one_ne_top
  -- `‖f - gₖ‖₁ → 0`.
  have htend0 : Tendsto (fun k => eLpNorm (f - ⇑(g k)) 1 volume) atTop (𝓝 0) := by
    have hinv0 : Tendsto (fun k : ℕ => (((k : ℝ≥0∞) + 1))⁻¹) atTop (𝓝 0) := by
      have hcomp : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine hcomp.congr (fun k => ?_)
      push_cast; ring_nf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv0
      (fun k => zero_le _) (fun k => (hgle k).le)
  -- Each `gₖ ∈ L¹`.
  have hgL1 : ∀ k, MemLp (⇑(g k)) 1 volume := fun k => (hgBFS k).memLp 1
  -- Pointwise convergence of the truncations.
  have hconv : ∀ x : ℂ, Tendsto (fun k => czOperator beurlingKernel r (⇑(g k)) x) atTop
      (𝓝 (czOperator beurlingKernel r f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    -- `czOp gₖ x - czOp f x = czOp (gₖ - f) x` (linearity from integrability).
    have hdiff : ∀ k, czOperator beurlingKernel r (⇑(g k)) x - czOperator beurlingKernel r f x
        = czOperator beurlingKernel r (⇑(g k) - f) x := by
      intro k
      have h1 := integrableOn_beurlingKernel_mul_L1 hr x (hgL1 k)
      have h2 := integrableOn_beurlingKernel_mul_L1 hr x hf
      unfold czOperator
      rw [← integral_sub h1 h2]
      refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
      simp only [Pi.sub_apply]; ring
    -- The enorm bound `‖czOp gₖ x − czOp f x‖ₑ ≤ ofReal(r⁻²)·‖gₖ − f‖₁`.
    have hbdE : ∀ k, ‖czOperator beurlingKernel r (⇑(g k)) x - czOperator beurlingKernel r f x‖ₑ
        ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm (⇑(g k) - f) 1 volume := by
      intro k; rw [hdiff k]; exact hOpBound (⇑(g k) - f) x
    -- The RHS tends to `0` in `ℝ≥0∞`.
    have hRHS0 : Tendsto
        (fun k => ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm (⇑(g k) - f) 1 volume) atTop
        (𝓝 0) := by
      have heq : ∀ k, eLpNorm (⇑(g k) - f) 1 volume = eLpNorm (f - ⇑(g k)) 1 volume := by
        intro k; rw [← eLpNorm_neg]; congr 1; funext y; simp
      have : Tendsto (fun k => ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ))
          * eLpNorm (f - ⇑(g k)) 1 volume) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul htend0
          (Or.inr (by simp : ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) ≠ ⊤))
        simpa using this
      exact this.congr (fun k => by rw [heq k])
    -- The enorm of the difference tends to `0`, hence so does the norm.
    have henorm0 : Tendsto
        (fun k => ‖czOperator beurlingKernel r (⇑(g k)) x - czOperator beurlingKernel r f x‖ₑ)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHS0
        (fun k => zero_le _) hbdE
    -- Convert `‖·‖ₑ → 0` to `‖·‖ → 0`.
    have := (ENNReal.tendsto_toReal (by simp)).comp henorm0
    simpa [Function.comp, toReal_enorm] using this
  -- Apply the `wnorm` Fatou lemma via the `ε`-route.
  -- `‖gₖ‖₁ → ‖f‖₁` (reverse triangle inequality, `ℝ≥0∞` squeeze).
  have hgnorm : Tendsto (fun k => eLpNorm (⇑(g k)) 1 volume) atTop (𝓝 (eLpNorm f 1 volume)) := by
    set L := eLpNorm f 1 volume with hL
    set d := fun k => eLpNorm (f - ⇑(g k)) 1 volume with hd
    have hupper : ∀ k, eLpNorm (⇑(g k)) 1 volume ≤ L + d k := by
      intro k
      have h : eLpNorm (⇑(g k)) 1 volume
          ≤ eLpNorm f 1 volume + eLpNorm (⇑(g k) - f) 1 volume := by
        calc eLpNorm (⇑(g k)) 1 volume = eLpNorm (f + (⇑(g k) - f)) 1 volume := by
              congr 1; funext y; simp
          _ ≤ eLpNorm f 1 volume + eLpNorm (⇑(g k) - f) 1 volume :=
              eLpNorm_add_le hf.aestronglyMeasurable ((hgL1 k).sub hf).aestronglyMeasurable le_rfl
      rw [hL, hd]
      rwa [show eLpNorm (⇑(g k) - f) 1 volume = eLpNorm (f - ⇑(g k)) 1 volume from by
        rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
    have hlower : ∀ k, L - d k ≤ eLpNorm (⇑(g k)) 1 volume := by
      intro k
      rw [tsub_le_iff_right]
      calc L = eLpNorm ((⇑(g k)) + (f - ⇑(g k))) 1 volume := by rw [hL]; congr 1; funext y; simp
        _ ≤ eLpNorm (⇑(g k)) 1 volume + eLpNorm (f - ⇑(g k)) 1 volume :=
            eLpNorm_add_le (hgL1 k).aestronglyMeasurable
              (hf.sub (hgL1 k)).aestronglyMeasurable le_rfl
    have hupper' : Tendsto (fun k => L + d k) atTop (𝓝 L) := by
      simpa using tendsto_const_nhds.add htend0
    have hlower' : Tendsto (fun k => L - d k) atTop (𝓝 L) := by
      simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend0
        (Or.inr (by simp)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
  -- `C10_0_3 4 · ‖gₖ‖₁ → C10_0_3 4 · ‖f‖₁`.
  have hCgnorm : Tendsto (fun k => (C10_0_3 4 : ℝ≥0∞) * eLpNorm (⇑(g k)) 1 volume) atTop
      (𝓝 ((C10_0_3 4 : ℝ≥0∞) * eLpNorm f 1 volume)) :=
    ENNReal.Tendsto.const_mul hgnorm (Or.inr (by finiteness))
  -- Finite-ness of the target product.
  have hbfin : (C10_0_3 4 : ℝ≥0∞) * eLpNorm f 1 volume < ⊤ :=
    ENNReal.mul_lt_top (by finiteness) hf.2
  -- Now the `ε`-route.
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  set L := (C10_0_3 4 : ℝ≥0∞) * eLpNorm f 1 volume with hLdef
  have hLlt : L < L + (ε : ℝ≥0∞) :=
    ENNReal.lt_add_right hbfin.ne (by exact_mod_cast hε.ne')
  -- Eventually `C10_0_3 4 · ‖gₖ‖₁ ≤ L + ε`.
  have hbound : ∀ᶠ k in atTop,
      wnorm (czOperator beurlingKernel r (⇑(g k))) 1 volume ≤ L + (ε : ℝ≥0∞) := by
    have hev := hCgnorm.eventually_le_const hLlt
    filter_upwards [hev] with k hk
    exact le_trans (hBWT (⇑(g k)) (hgBFS k)).2 hk
  -- Conclude by the `wnorm` Fatou lemma.
  exact wnorm_le_of_ae_tendsto hbound
    (fun k => aestronglyMeasurable_czOperator_beurling' (hgL1 k).aestronglyMeasurable)
    (Filter.Eventually.of_forall hconv)

/-- The truncated Beurling operator is strong-(2,2) on all of `L²`
(`eLpNorm_czOperator_beurling_L2`). -/
lemma hasStrongType_czOperator_beurling_two {r : ℝ} (hr : 0 < r) :
    HasStrongType (czOperator beurlingKernel r) 2 2 volume volume (C10_1_6 4) := by
  intro f hf
  exact ⟨aestronglyMeasurable_czOperator_beurling hf, eLpNorm_czOperator_beurling_L2 hr hf⟩

/-- The truncated Beurling operator is subadditive (in fact linear) on the
union class `L¹ ∪ L²`. -/
lemma aesubadditiveOn_czOperator_beurling {r : ℝ} (hr : 0 < r) :
    AESubadditiveOn (czOperator beurlingKernel r)
      (fun f : ℂ → ℂ => MemLp f 1 volume ∨ MemLp f 2 volume) 1 volume := by
  intro f g hf hg
  -- From the `L¹ ∪ L²` membership, get integrability of the kernel product on `(ball x r)ᶜ`.
  have hf_int : ∀ x : ℂ,
      IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
    intro x
    rcases hf with hf1 | hf2
    · exact integrableOn_beurlingKernel_mul_L1 hr x hf1
    · exact integrableOn_beurlingKernel_mul hr x hf2
  have hg_int : ∀ x : ℂ,
      IntegrableOn (fun y => beurlingKernel x y * g y) (Metric.ball x r)ᶜ volume := by
    intro x
    rcases hg with hg1 | hg1
    · exact integrableOn_beurlingKernel_mul_L1 hr x hg1
    · exact integrableOn_beurlingKernel_mul hr x hg1
  -- The operator is additive, so the bound holds pointwise (for all `x`).
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [czOperator_beurling_add (hf_int x) (hg_int x), one_mul]
  exact enorm_add_le _ _

/-- The interpolation constant for the truncated Beurling operator on `Lᵖ`,
`1 < p < 2`: independent of `r`. -/
noncomputable def beurlingTruncLpConst (p : ℝ≥0∞) : ℝ≥0 :=
  C_realInterpolation 1 2 1 2 p (C10_0_3 4) (C10_1_6 4) 1 (2 * (1 - p⁻¹))

/-- **Uniform-in-`r` `Lᵖ` bound for the truncations**, `1 < p < 2`, by
Marcinkiewicz interpolation. The constant `beurlingTruncLpConst p` does not depend
on `r`. -/
lemma eLpNorm_czOperator_beurling_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) {r : ℝ} (hr : 0 < r)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    eLpNorm (czOperator beurlingKernel r f) p volume
      ≤ (beurlingTruncLpConst p : ℝ≥0∞) * eLpNorm f p volume := by
  -- interpolation parameter (verbatim arithmetic from `isCalderonZygmundBound_of_hasWeakType`)
  set t : ℝ≥0∞ := 2 * (1 - p⁻¹) with ht_def
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  have hpinv_lt1 : p⁻¹ < 1 := by rw [ENNReal.inv_lt_one]; exact hp1
  have hhalf_lt : (2:ℝ≥0∞)⁻¹ < p⁻¹ := by rw [ENNReal.inv_lt_inv]; exact hp2
  have hpinv_ne_top : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hp0
  have h2mulinv : (2:ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have h2 : (1:ℝ≥0∞) - p⁻¹ < 2⁻¹ := by
    have htwo_inv_ne : (2:ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    have hadd : (1:ℝ≥0∞) - p⁻¹ + p⁻¹ < 2⁻¹ + p⁻¹ := by
      rw [tsub_add_cancel_of_le hpinv_lt1.le]
      calc (1:ℝ≥0∞) = 2⁻¹ + 2⁻¹ := (ENNReal.inv_two_add_inv_two).symm
        _ < 2⁻¹ + p⁻¹ := by
          rw [ENNReal.add_lt_add_iff_left htwo_inv_ne]; exact hhalf_lt
    exact lt_of_add_lt_add_right hadd
  have ht : t ∈ Set.Ioo (0:ℝ≥0∞) 1 := by
    constructor
    · have : 0 < 1 - p⁻¹ := tsub_pos_of_lt hpinv_lt1
      rw [ht_def]; positivity
    · rw [ht_def]
      calc 2 * (1 - p⁻¹) < 2 * 2⁻¹ := by gcongr; simp
        _ = 1 := h2mulinv
  have h2pinv : (1:ℝ≥0∞) ≤ 2 * p⁻¹ := by
    calc (1:ℝ≥0∞) = 2 * 2⁻¹ := h2mulinv.symm
      _ ≤ 2 * p⁻¹ := by gcongr
  have hp : p⁻¹ = (1 - t) / 1 + t / 2 := by
    rw [ht_def, div_one]
    have htle1 : 2 * (1 - p⁻¹) ≤ 1 := ht.2.le
    lift p⁻¹ to ℝ≥0 using hpinv_ne_top with y
    have hy1 : y ≤ 1 := by exact_mod_cast hpinv_lt1.le
    have hone_sub : (1:ℝ≥0∞) - (y : ℝ≥0∞) = ((1 - y : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_one, ← ENNReal.coe_sub]
    rw [hone_sub, show (2:ℝ≥0∞) = ((2:ℝ≥0):ℝ≥0∞) by simp, ← ENNReal.coe_mul] at htle1 ⊢
    have htle1' : 2 * (1 - y) ≤ 1 := by exact_mod_cast htle1
    rw [show (1:ℝ≥0∞) = ((1:ℝ≥0):ℝ≥0∞) by simp, ← ENNReal.coe_sub,
      ← ENNReal.coe_div (by simp), ← ENNReal.coe_add, ENNReal.coe_inj]
    rw [NNReal.eq_iff]
    push_cast [NNReal.coe_sub, NNReal.coe_div, htle1', hy1]
    ring
  have hp0' : (1:ℝ≥0∞) ∈ Set.Ioc 0 1 := by constructor <;> simp
  have hp1' : (2:ℝ≥0∞) ∈ Set.Ioc 0 2 := by constructor <;> simp
  have hq0q1 : (1:ℝ≥0∞) ≠ 2 := by norm_num
  -- endpoint hypotheses for the truncated Beurling operator
  have hmeas : ∀ g : ℂ → ℂ, MemLp g p volume →
      AEStronglyMeasurable (czOperator beurlingKernel r g) volume :=
    fun g hg => aestronglyMeasurable_czOperator_beurling' hg.aestronglyMeasurable
  have hsub : AESubadditiveOn (czOperator beurlingKernel r)
      (fun g : ℂ → ℂ => MemLp g 1 volume ∨ MemLp g 2 volume) 1 volume :=
    aesubadditiveOn_czOperator_beurling hr
  have hweak₁ : HasWeakType (czOperator beurlingKernel r) 1 1 volume volume (C10_0_3 4) :=
    hasWeakType_czOperator_beurling_one hr
  have hweak₂ : HasWeakType (czOperator beurlingKernel r) 2 2 volume volume (C10_1_6 4) :=
    (hasStrongType_czOperator_beurling_two hr).hasWeakType (by norm_num)
  have hA : (1 : ℝ≥0) ≤ 1 := le_refl _
  have hC₁ : (0 : ℝ≥0) < C10_0_3 4 := by rw [C10_0_3]; positivity
  have hC₂ : (0 : ℝ≥0) < C10_1_6 4 := by rw [C10_1_6]; positivity
  -- apply the Carleson real-interpolation theorem
  have hST : HasStrongType (czOperator beurlingKernel r) p p volume volume
      (C_realInterpolation 1 2 1 2 p (C10_0_3 4) (C10_1_6 4) 1 t) :=
    exists_hasStrongType_real_interpolation hp0' hp1' hq0q1 hA ht hC₁ hC₂ hp hp
      hmeas hsub hweak₁ hweak₂
  have hbound := (hST f hf).2
  -- match the constant with `beurlingTruncLpConst p`
  rw [beurlingTruncLpConst]
  exact hbound

/-! ## `Lᵖ` bounds for the maximal truncated operator (`1 < p < 2`)

The `L²` maximal-operator development, replicated at exponent `p`: the maximal
operator `simpleNontangentialOperator beurlingKernel 0` is bounded `Lᵖ → Lᵖ`
(Cotlar's pointwise estimate `cotlar_estimate` + the Hardy–Littlewood maximal
`Lᵖ` bound `hasStrongType_globalMaximalFunction` + the truncation `Lᵖ` bound
`eLpNorm_czOperator_beurling_Lp`), which yields a.e. convergence of the
truncations on `Lᵖ`. The constants are immaterial here (only finiteness matters),
so the maximal bound is stated with an existential constant. -/

/-- `Lᵖ`-linearity of the truncated Beurling operator (`1 < p < ∞`): both kernel
products are integrable (`integrableOn_beurlingKernel_mul_Lp`), so the truncated
integral is additive. -/
lemma czOperator_beurling_sub_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp_top : p ≠ ⊤) {r : ℝ} (hr : 0 < r)
    (x : ℂ) {f g : ℂ → ℂ} (hf : MemLp f p volume) (hg : MemLp g p volume) :
    czOperator beurlingKernel r (f - g) x
      = czOperator beurlingKernel r f x - czOperator beurlingKernel r g x := by
  -- Construct the conjugate exponent `p' = (1 - p⁻¹)⁻¹` and its `HolderConjugate` instance.
  have hpinv_le_one : p⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]; exact hp1.le
  haveI hHC : ENNReal.HolderConjugate p ((1 - p⁻¹)⁻¹) := by
    rw [ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  have h1 := integrableOn_beurlingKernel_mul_Lp (p' := (1 - p⁻¹)⁻¹) hr x hp1 hp_top hf
  have h2 := integrableOn_beurlingKernel_mul_Lp (p' := (1 - p⁻¹)⁻¹) hr x hp1 hp_top hg
  unfold czOperator
  rw [← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
  simp only [Pi.sub_apply]; ring

/-- **Maximal-operator `Lᵖ` bound** (`1 < p < 2`): a finite constant `C` with
`‖simpleNontangentialOperator beurlingKernel 0 g‖_p ≤ C ‖g‖_p` for every `g ∈ Lᵖ`.
Proved by replicating `simple_nontangential_operator` at exponent `p` (Cotlar +
HL-maximal-`Lᵖ` + `eLpNorm_czOperator_beurling_Lp`) on `BoundedFiniteSupport`,
then extending to all of `Lᵖ` by lower semicontinuity + Fatou. -/
lemma exists_eLpNorm_simpleNontangential_beurling_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ≥0, ∀ g : ℂ → ℂ, MemLp g p volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C : ℝ≥0∞) * eLpNorm g p volume := by
  have hp_top : p ≠ ⊤ := (lt_trans hp2 (by norm_num : (2:ℝ≥0∞) < ⊤)).ne_top
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  -- `p` as an `ℝ≥0`, with `1 < pnn`.
  set pnn : ℝ≥0 := p.toNNReal with hpnn_def
  have hpnn_coe : (pnn : ℝ≥0∞) = p := by rw [hpnn_def, ENNReal.coe_toNNReal hp_top]
  have hpnn1 : 1 < pnn := by
    have : (1 : ℝ≥0∞) < (pnn : ℝ≥0∞) := by rw [hpnn_coe]; exact hp1
    exact_mod_cast this
  -- The HL maximal `Lᵖ` strong-type bound (constant `Cgmf`).
  -- Use the `defaultA 4` doubling structure (the one carried by the Carleson lemmas).
  haveI hA4 : (volume : Measure ℂ).IsDoubling ((defaultA 4 : ℕ) : ℝ≥0) :=
    doublingMeasure_complex_defaultA4.toIsDoubling
  set Cgmf : ℝ≥0 := C2_0_6' ((defaultA 4 : ℕ) : ℝ≥0) 1 pnn with hCgmf_def
  have hgmf : HasStrongType
      (globalMaximalFunction (X := ℂ) (E := ℂ) (A := ((defaultA 4 : ℕ) : ℝ≥0)) volume 1)
      (pnn : ℝ≥0∞) (pnn : ℝ≥0∞) volume volume Cgmf :=
    hasStrongType_globalMaximalFunction (X := ℂ) (E := ℂ) (μ := volume)
      (A := ((defaultA 4 : ℕ) : ℝ≥0)) (p₁ := 1) (p₂ := pnn) zero_lt_one hpnn1
  -- Abbreviations for the truncation constant.
  set Ctr : ℝ≥0 := beurlingTruncLpConst p with hCtr_def
  -- **Part (a): the BFS bound at a positive scale `r`.**
  set C₀ : ℝ≥0 := 4 * Cgmf * Ctr + (C10_1_5 4 + C10_1_2 4) * Cgmf with hC₀_def
  have hBFSscale : ∀ {r : ℝ}, 0 < r → ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel r g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro r hr g hg
    -- The strong-type input for Cotlar's estimate (`L²` truncation bound).
    have hT : ∀ s > 0, HasBoundedStrongType (czOperator beurlingKernel s) 2 2 volume volume
        (C_Ts 4 : ℝ≥0∞) := fun s hs => czOperator_beurling_strongType_L2 hs
    -- The pointwise dominating function (Cotlar + x-shift), exponent-free.
    set pointwise : ℂ → ℝ≥0∞ :=
      4 * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        + C10_1_5 4 • globalMaximalFunction volume 1 g
        + C10_1_2 4 • globalMaximalFunction volume 1 g with hpw_def
    -- Pointwise domination (verbatim from `simple_nontangential_operator`).
    have hdom : ∀ x, simpleNontangentialOperator beurlingKernel r g x ≤ pointwise x := by
      simp_rw [hpw_def, simpleNontangentialOperator, iSup_le_iff]
      intro x R hR x' hx'
      rw [Metric.mem_ball, dist_comm] at hx'
      trans ‖czOperator beurlingKernel R g x‖ₑ
          + C10_1_2 4 * globalMaximalFunction volume 1 g x
      · calc ‖czOperator beurlingKernel R g x'‖ₑ
            = ‖czOperator beurlingKernel R g x
              + (czOperator beurlingKernel R g x' - czOperator beurlingKernel R g x)‖ₑ := by
              congr 1; ring
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + ‖czOperator beurlingKernel R g x'
                - czOperator beurlingKernel R g x‖ₑ := enorm_add_le _ _
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + C10_1_2 4 * globalMaximalFunction volume 1 g x := by
              gcongr
              rw [← edist_eq_enorm_sub, edist_comm]
              exact estimate_x_shift (K := beurlingKernel) (by norm_num) hg
                (hr.trans hR.lt) hx'.le
      · refine add_le_add (cotlar_estimate (K := beurlingKernel) (r := r) (R := R)
          (by norm_num) hT hg ?_) (by rfl) |>.trans ?_
        · rw [Set.mem_Ioc]; exact ⟨hr, hR.le⟩
        · apply le_of_eq
          simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, ENNReal.smul_def, smul_eq_mul,
            Pi.ofNat_apply, add_assoc]
    -- Take `eLpNorm _ p` and use the additivity + maximal `Lᵖ` + truncation `Lᵖ` bounds.
    refine (eLpNorm_mono_enorm (g := pointwise) (fun x => by
      simp only [enorm_eq_self]; exact hdom x)).trans ?_
    -- `czOperator r g ∈ Lᵖ` and `g ∈ Lᵖ` (from `BoundedFiniteSupport`).
    have hgLp : MemLp g p volume := hg.memLp p
    have hczLp : MemLp (czOperator beurlingKernel r g) p volume := by
      refine ⟨aestronglyMeasurable_czOperator_beurling' hgLp.aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt (eLpNorm_czOperator_beurling_Lp hp1 hp2 hr hgLp)
        (ENNReal.mul_lt_top ENNReal.coe_lt_top hgLp.2)
    -- Strong-type bounds for the maximal functions.
    have hgmf_g := (hgmf g (by rw [hpnn_coe]; exact hgLp)).2
    have hgmf_czg := (hgmf (czOperator beurlingKernel r g) (by rw [hpnn_coe]; exact hczLp)).2
    rw [hpnn_coe] at hgmf_g hgmf_czg
    -- Measurability for `eLpNorm_add_le`.
    have hm_czg : AEStronglyMeasurable
        (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) volume :=
      MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    have hm_g : AEStronglyMeasurable (globalMaximalFunction volume 1 g) volume :=
      MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    rw [hpw_def, show (4 : ℂ → ℝ≥0∞) * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        = (4 : ℝ≥0) • globalMaximalFunction volume 1 (czOperator beurlingKernel r g) by
      ext y; simp [ENNReal.smul_def]]
    -- Split the eLpNorm of the sum.
    refine (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1').trans ?_
    refine (add_le_add (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1') (le_refl _)).trans ?_
    rw [show eLpNorm ((4 : ℝ≥0) • globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        = ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume from eLpNorm_const_smul',
      show eLpNorm (C10_1_5 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul',
      show eLpNorm (C10_1_2 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul']
    -- Apply the maximal `Lᵖ` bound and then the truncation `Lᵖ` bound.
    have hkey : ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
          + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
      have hb1 : eLpNorm (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) p volume
          ≤ (Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume) := by
        refine hgmf_czg.trans ?_
        rw [hCtr_def]
        exact mul_le_mul' (le_refl _) (eLpNorm_czOperator_beurling_Lp hp1 hp2 hr hgLp)
      have hb2 : eLpNorm (globalMaximalFunction volume 1 g) p volume
          ≤ (Cgmf : ℝ≥0∞) * eLpNorm g p volume := hgmf_g
      calc ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
              (czOperator beurlingKernel r g)) p volume
            + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
              + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
          ≤ ‖(4 : ℝ≥0)‖ₑ * ((Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume))
              + (‖C10_1_5 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)
                + ‖C10_1_2 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)) := by
            gcongr
        _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
            rw [hC₀_def]
            push_cast [enorm_NNReal]
            ring
    rw [add_assoc]; exact hkey
  -- **Scale-0 BFS bound** (monotone convergence over `r = (n+1)⁻¹`).
  have hBFS0 : ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro g hg
    set fseq : ℕ → ℂ → ℝ≥0∞ :=
      fun n => simpleNontangentialOperator beurlingKernel (n + 1 : ℝ)⁻¹ g with hfseq_def
    have f_mon : ∀ x : ℂ, Monotone fun n => fseq n x := by
      intro x m n hmn
      simp only [hfseq_def, simpleNontangentialOperator]
      gcongr with R
      apply iSup_const_mono (lt_of_le_of_lt _)
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      simp only [add_le_add_iff_right]
      exact_mod_cast hmn
    have snt0 : ⨆ (n : ℕ), fseq n = simpleNontangentialOperator beurlingKernel 0 g := by
      ext x
      simp only [hfseq_def]
      simp_rw [iSup_apply, simpleNontangentialOperator, gt_iff_lt]
      rw [iSup_comm]
      congr 1; ext R
      apply le_antisymm (iSup_le <| fun n => iSup_const_mono (lt_trans (by positivity)))
        (iSup_le _)
      intro hR
      set n := Nat.ceil R⁻¹ with hn_def
      have hn : (n + 1 : ℝ)⁻¹ < R :=
        inv_lt_of_inv_lt₀ hR <| (Nat.le_ceil R⁻¹).trans_lt (by exact_mod_cast lt_add_one _)
      refine le_iSup_of_le n ?_
      rw [iSup_pos hn]
    have mct := eLpNorm_iSup' (p := p) (f := fseq) (μ := volume)
      (fun n => aestronglyMeasurable_simpleNontangentialOperator.aemeasurable)
      (by filter_upwards; exact f_mon)
    rw [← snt0, ← mct]
    apply iSup_le
    intro n
    exact hBFSscale (r := (n + 1 : ℝ)⁻¹) (by positivity) g hg
  -- **Part (b): extend the scale-0 bound from `BoundedFiniteSupport` to all of `Lᵖ`.**
  -- The conjugate exponent and the kernel-section `Lᵖ'` membership.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'_def
  have hpinv_le_one : p⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; exact hp1.le
  haveI hHC : ENNReal.HolderConjugate p p' := by
    rw [hp'_def, ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  -- Per-point Hölder bound for the truncation against an `Lᵖ` function.
  have hHolderPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {h : ℂ → ℂ}, MemLp h p volume →
      ‖czOperator beurlingKernel R h x'‖ₑ
        ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
            volume * eLpNorm h p volume := by
    intro R hR x' h hh
    unfold czOperator
    have hcs : ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ
        ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
          * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := by
      have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
        (μ := volume.restrict (Metric.ball x' R)ᶜ) (p := p') (q := p)
        (ENNReal.HolderConjugate.symm)
        (f := fun y => ‖beurlingKernel x' y‖ₑ) (g := fun y => ‖h y‖ₑ)
        (by unfold beurlingKernel; fun_prop) hh.aestronglyMeasurable.enorm.restrict
      simpa [eLpNorm_enorm] using this
    calc ‖∫ y in (Metric.ball x' R)ᶜ, beurlingKernel x' y * h y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y * h y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
            * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := hcs
      _ ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
              volume * eLpNorm h p volume := by
          refine mul_le_mul' ?_ ?_
          · exact le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm
          · exact eLpNorm_restrict_le h p volume _
  -- Kernel-section `Lᵖ'` membership (so the per-point constant is finite).
  have hkermem : ∀ (x' : ℂ) (R : ℝ), 0 < R →
      MemLp (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p' volume := by
    intro x' R hR
    -- The membership via the `Lᵖ'` lintegral finiteness.
    haveI : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
    have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
    have hp'1 : 1 < p' :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
    set q' : ℝ := p'.toReal with hq'_def
    have hp'0 : p' ≠ 0 := ne_of_gt (lt_trans one_pos hp'1)
    have hq'1 : 1 < q' := by
      rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
      exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
    have hq'0 : 0 < q' := lt_trans one_pos hq'1
    have hlint : ∫⁻ u : ℂ in {u : ℂ | R ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
      rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
        ← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ici R ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
      have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
        apply ENNReal.measurable_ofReal.comp
        apply Measurable.mul measurable_fst
        exact (Real.continuous_rpow_const hq'0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
      have hbound : ∀ pp ∈ polarCoord.target,
          ENNReal.ofReal pp.1 • {u : ℂ | R ≤ ‖u‖}.indicator
            (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm pp) ≤ box pp := by
        intro pp hpp
        rw [polarCoord_target, Set.mem_prod] at hpp
        obtain ⟨hpp1, hpp2⟩ := hpp
        simp only [Set.mem_Ioi] at hpp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
        by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | R ≤ ‖u‖}
        · have hpR : R ≤ pp.1 := by rw [Set.mem_setOf_eq, hnorm] at hmem; exact hmem
          rw [Set.indicator_of_mem hmem,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
          have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
            rw [← ofReal_norm_eq_enorm, hnorm]
          rw [henorm, smul_eq_mul,
            show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((pp.1^2)⁻¹)^q') by
              rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
                ENNReal.ofReal_rpow_of_pos (by positivity)],
            ← ENNReal.ofReal_mul hpp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le _
      refine lt_of_le_of_lt (setLIntegral_mono
        (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
      calc ∫⁻ pp in polarCoord.target, box pp
          ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
        _ = ∫⁻ pp in (Set.Ici R ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q') := by
              rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint2 : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici R) volume := by
                have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                    =ᶠ[ae (volume.restrict (Set.Ici R))]
                    (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                  simp only [Set.mem_Ici] at hρ
                  have hρpos : 0 < ρ := lt_of_lt_of_le hR hρ
                  have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                    rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                  have hh1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                    rw [hbase, ← Real.rpow_mul hρpos.le]
                  have hh2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                    nth_rewrite 1 [← Real.rpow_one ρ]
                    rw [← Real.rpow_add hρpos]; congr 1; ring
                  rw [hh1, hh2]
                rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                  integrableOn_Ioi_rpow_iff hR]
                nlinarith [hq'1]
              have hfin := hint2.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
              · refine (measurable_id.mul ?_).enorm
                exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                  ((measurable_id.pow_const 2).inv)
              · simp only [Set.mem_Ici] at hy
                have hypos : 0 < y := lt_of_lt_of_le hR hy
                rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top, ← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y‖ₑ ^ q'
        = (Metric.ball x' R)ᶜ.indicator (fun y => ‖beurlingKernel x' y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x' y‖ₑ ^ q' ≤ ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x' = y
      · subst h; simp [beurlingKernel]
      · have hne : x' - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x' y = ((x'-y) * (x'-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x' - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x' R)ᶜ) ↔ (x' - y ∈ {u : ℂ | R ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_setOf_eq, dist_comm, Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x']
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint
  -- Per-point liminf bound (Hölder `Lᵖ`-continuity in the function argument).
  have hLiminfPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {f : ℂ → ℂ} {gg : ℕ → ℂ → ℂ},
      MemLp f p volume → (∀ n, MemLp (gg n) p volume) →
      Tendsto (fun n => eLpNorm (f - gg n) p volume) atTop (𝓝 0) →
      ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop := by
    intro R hR x' f gg hf hgmem htend
    set C := eLpNorm
      (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p' volume with hCdef
    have hbd : ∀ n, ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ + C * eLpNorm (f - gg n) p volume := by
      intro n
      have hsub : ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ
          ≤ C * eLpNorm (f - gg n) p volume := by
        rw [← czOperator_beurling_sub_Lp hp1 hp_top hR x' hf (hgmem n)]
        exact hHolderPt R hR x' (hf.sub (hgmem n))
      calc ‖czOperator beurlingKernel R f x'‖ₑ
          ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ := by
              rw [add_comm]
              exact le_trans (by rw [sub_add_cancel]) (enorm_add_le _ _)
        _ ≤ _ := by gcongr
    have hCne : C ≠ ⊤ := by rw [hCdef]; exact (hkermem x' R hR).2.ne
    have hC0 : Tendsto (fun n => C * eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul htend (Or.inr hCne))
    calc ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + C * eLpNorm (f - gg n) p volume) atTop :=
          le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hbd)
      _ = liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop :=
          ENNReal.liminf_add_of_right_tendsto_zero hC0 _
  refine ⟨C₀, fun g hg => ?_⟩
  -- Smooth compactly-supported `Lᵖ`-approximating sequence `gₙ → g`.
  have hp_top' : p ≠ ⊤ := hp_top
  choose gg hggc hggsmooth hggle using fun n : ℕ =>
    hg.exist_eLpNorm_sub_le hp_top' hp1' (ε := 1/(n+1)) (by positivity)
  have hggmem : ∀ n, MemLp (gg n) p volume := fun n =>
    (hggsmooth n).continuous.memLp_of_hasCompactSupport (hggc n)
  have hggBFS : ∀ n, BoundedFiniteSupport (gg n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hggsmooth n) (hggc n)
  have htend : Tendsto (fun n => eLpNorm (g - gg n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le _) hggle
  -- Per-point: `simpleNTO 0 g x ≤ liminf (simpleNTO 0 gₙ x)`.
  have hsup : ∀ x, simpleNontangentialOperator beurlingKernel 0 g x
      ≤ liminf (fun n => simpleNontangentialOperator beurlingKernel 0 (gg n) x) atTop := by
    intro x
    unfold simpleNontangentialOperator
    refine iSup_le (fun R => iSup_le (fun hR => iSup_le (fun x' => iSup_le (fun hx' => ?_))))
    refine le_trans (hLiminfPt R hR x' hg hggmem htend) ?_
    refine liminf_le_liminf (Eventually.of_forall (fun n => ?_))
    exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x' (le_iSup_of_le hx' (le_refl _))))
  -- BFS bound on each `gₙ`.
  have hggbd : ∀ n, eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume
      ≤ (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume := fun n => hBFS0 (gg n) (hggBFS n)
  -- `‖gₙ‖_p → ‖g‖_p`.
  have htnorm : Tendsto (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop
      (𝓝 ((C₀ : ℝ≥0∞) * eLpNorm g p volume)) := by
    have hgnorm : Tendsto (fun n => eLpNorm (gg n) p volume) atTop (𝓝 (eLpNorm g p volume)) := by
      set L := eLpNorm g p volume with hL
      set d := fun n => eLpNorm (g - gg n) p volume with hd
      have hupper : ∀ n, eLpNorm (gg n) p volume ≤ L + d n := by
        intro n
        have h : eLpNorm (gg n) p volume ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume := by
          calc eLpNorm (gg n) p volume = eLpNorm (g + (gg n - g)) p volume := by
                congr 1; funext y; simp
            _ ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume :=
                eLpNorm_add_le hg.aestronglyMeasurable ((hggmem n).sub hg).aestronglyMeasurable hp1'
        rw [hL, hd]
        rwa [show eLpNorm (gg n - g) p volume = eLpNorm (g - gg n) p volume from by
          rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
      have hlower : ∀ n, L - d n ≤ eLpNorm (gg n) p volume := by
        intro n
        rw [tsub_le_iff_right]
        calc L = eLpNorm ((gg n) + (g - gg n)) p volume := by rw [hL]; congr 1; funext y; simp
          _ ≤ eLpNorm (gg n) p volume + eLpNorm (g - gg n) p volume :=
              eLpNorm_add_le (hggmem n).aestronglyMeasurable
                (hg.sub (hggmem n)).aestronglyMeasurable hp1'
      have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
        simpa using tendsto_const_nhds.add htend
      have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
        simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend (Or.inr (by simp)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
    refine ENNReal.Tendsto.const_mul hgnorm ?_
    right; exact ENNReal.coe_ne_top
  -- Fatou on the `Lᵖ` lintegral.
  have hp_pos : (0:ℝ) < p.toReal := ENNReal.toReal_pos (by rintro rfl; exact absurd hp1 (by simp)) hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp)) hp_top]
  simp only [one_div]
  have hmono : ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
      ≤ liminf (fun n => ∫⁻ x,
        ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
    have hpowliminf : ∀ (u : ℕ → ℝ≥0∞),
        liminf (fun n => (u n) ^ p.toReal) atTop = (liminf u atTop) ^ p.toReal := by
      intro u
      have hmono' : Monotone (fun x : ℝ≥0∞ => x ^ p.toReal) :=
        fun a b h => ENNReal.rpow_le_rpow h hp_pos.le
      exact (hmono'.map_liminf_of_continuousAt u (ENNReal.continuous_rpow_const).continuousAt).symm
    have hle : ∀ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
        ≤ liminf (fun n =>
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
      intro x
      simp_rw [enorm_eq_self]
      rw [hpowliminf]
      gcongr
      exact hsup x
    refine le_trans (lintegral_mono hle) ?_
    refine lintegral_liminf_le (fun n => ?_)
    exact (lowerSemicontinuous_simpleNontangentialOperator.measurable).enorm.pow_const _
  calc (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal) ^ (p.toReal)⁻¹
      ≤ (liminf (fun n => ∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop)
            ^ (p.toReal)⁻¹ := by gcongr
    _ = liminf (fun n => (∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal)
            ^ (p.toReal)⁻¹) atTop := by
        have hmono2 : Monotone (fun x : ℝ≥0∞ => x ^ (p.toReal)⁻¹) :=
          fun a b h => ENNReal.rpow_le_rpow h (by positivity)
        exact hmono2.map_liminf_of_continuousAt _ (ENNReal.continuous_rpow_const).continuousAt
    _ = liminf (fun n => eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume)
          atTop := by
        congr 1; funext n
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp)) hp_top]
        simp only [one_div]
    _ ≤ liminf (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop :=
        liminf_le_liminf (Eventually.of_forall hggbd)
    _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := htnorm.liminf_eq

/-- **A.e. existence of the principal-value limit on `Lᵖ`** (`1 < p < 2`): for
`f ∈ Lᵖ` the truncations `czOperator beurlingKernel r f z` converge as `r → 0⁺`
for a.e. `z`. The oscillation argument (smooth `Lᵖ` density `MemLp.exist_eLpNorm_sub_le`
+ the maximal-`Lᵖ` bound via Markov–Chebyshev) replicates the `L²` proof. -/
lemma czOperator_beurling_ae_tendsto_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, ∃ L, Filter.Tendsto (fun r => czOperator beurlingKernel r f z)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  have hp_top : p ≠ ⊤ := (lt_trans hp2 (by norm_num : (2:ℝ≥0∞) < ⊤)).ne_top
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  have hp_pos : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  -- Inline helper: oscillation control by the maximal operator (the `Lᵖ` version of
  -- `edist_czOperator_oscillation`, using `czOperator_beurling_sub_Lp`).
  have edist_osc : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {r₁ r₂ : ℝ}, 0 < r₁ → 0 < r₂ →
      edist (czOperator beurlingKernel r₁ f z) (czOperator beurlingKernel r₂ f z)
        ≤ edist (czOperator beurlingKernel r₁ ν z) (czOperator beurlingKernel r₂ ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    intro ν hν z r₁ r₂ hr₁ hr₂
    have hd1 : czOperator beurlingKernel r₁ f z - czOperator beurlingKernel r₁ ν z
        = czOperator beurlingKernel r₁ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₁ z hf hν).symm
    have hd2 : czOperator beurlingKernel r₂ f z - czOperator beurlingKernel r₂ ν z
        = czOperator beurlingKernel r₂ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₂ z hf hν).symm
    set Sf1 := czOperator beurlingKernel r₁ f z
    set Sf2 := czOperator beurlingKernel r₂ f z
    set Sn1 := czOperator beurlingKernel r₁ ν z
    set Sn2 := czOperator beurlingKernel r₂ ν z
    have hb1 : edist Sf1 Sn1 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_eq_enorm_sub, hd1]; exact enorm_czOperator_le_simpleNontangential hr₁ (f - ν) z
    have hb2 : edist Sn2 Sf2 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_comm, edist_eq_enorm_sub, hd2]
      exact enorm_czOperator_le_simpleNontangential hr₂ (f - ν) z
    calc edist Sf1 Sf2 ≤ edist Sf1 Sn1 + edist Sn1 Sn2 + edist Sn2 Sf2 := by
          refine le_trans (edist_triangle Sf1 Sn2 Sf2) ?_
          gcongr
          exact edist_triangle Sf1 Sn1 Sn2
      _ = edist Sn1 Sn2 + (edist Sf1 Sn1 + edist Sn2 Sf2) := by ring
      _ ≤ edist Sn1 Sn2 + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
          gcongr; rw [two_mul]; gcongr
  -- Inline helper: per-point Cauchy from smooth convergence + small maximal value
  -- (the `Lᵖ` version of `eventually_edist_lt_of_smooth_conv`).
  have edist_lt_of_conv : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {a : ℝ≥0∞}, 0 < a →
      (∃ L, Tendsto (fun r => czOperator beurlingKernel r ν z) (𝓝[>] (0:ℝ)) (𝓝 L)) →
      2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z < a / 2 →
      ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a := by
    intro ν hν z a ha hconv hsmall
    obtain ⟨L, hL⟩ := hconv
    have hνcauchy : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z) < a / 2 := by
      have hmap : Tendsto (fun q : ℝ × ℝ =>
          (czOperator beurlingKernel q.1 ν z, czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (L, L)) :=
        (hL.comp tendsto_fst).prodMk_nhds (hL.comp tendsto_snd)
      have ht : Tendsto (fun q : ℝ × ℝ =>
          edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (edist L L)) :=
        (continuous_edist.tendsto _).comp hmap
      rw [edist_self] at ht
      exact ht (Iio_mem_nhds (ENNReal.half_pos (ne_of_gt ha)))
    have hpos : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), 0 < q.1 ∧ 0 < q.2 := by
      rw [eventually_prod_iff]
      refine ⟨fun r => 0 < r, ?_, fun r => 0 < r, ?_, fun {r₁} h1 {r₂} h2 => ⟨h1, h2⟩⟩
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
    filter_upwards [hνcauchy, hpos] with q hq hqpos
    obtain ⟨hq1, hq2⟩ := hqpos
    calc edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        ≤ edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z :=
          edist_osc hν z hq1 hq2
      _ < a / 2 + a / 2 := ENNReal.add_lt_add hq hsmall
      _ = a := ENNReal.add_halves a
  -- The smooth `Lᵖ`-dense sequence (inline version of `exists_contDiff_seq_tendsto_L2`).
  choose g hgc hgsmooth hgle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le hp_top hp1' (ε := 1/(n+1)) (by positivity)
  have hg : ∀ n, MemLp (g n) p volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  have htend : Tendsto (fun n => eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le _) hgle
  -- The maximal-`Lᵖ` Chebyshev bound (inline version of `volume_simpleNontangential_ge_le`).
  obtain ⟨C, hC⟩ := exists_eLpNorm_simpleNontangential_beurling_Lp hp1 hp2
  have vol_ge : ∀ {h : ℂ → ℂ}, MemLp h p volume → ∀ {a : ℝ≥0∞}, a ≠ 0 → a ≠ ⊤ →
      volume {z | a ≤ simpleNontangentialOperator beurlingKernel 0 h z}
        ≤ a⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm h p volume) ^ p.toReal := by
    intro h hh a hane hatop
    have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm volume hp_pos hp_top
      (f := simpleNontangentialOperator beurlingKernel 0 h)
      aestronglyMeasurable_simpleNontangentialOperator (ε := a) hane (fun heq => absurd heq hatop)
    refine le_trans hcheb (mul_le_mul' (le_refl (a⁻¹ ^ p.toReal)) ?_)
    exact ENNReal.rpow_le_rpow (hC h hh) (by positivity)
  -- Inline version of `volume_oscillation_set_eq_zero`.
  have osc_null : ∀ {a : ℝ≥0∞}, 0 < a → a ≠ ⊤ →
      volume {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a} = 0 := by
    intro a ha ha'
    set b := a / 4 with hbdef
    have hbpos : 0 < b := ENNReal.div_pos (ne_of_gt ha) (by norm_num)
    have hbne : b ≠ 0 := ne_of_gt hbpos
    have hbtop : b ≠ ⊤ := (ENNReal.div_lt_top ha' (by norm_num)).ne
    set B := {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a}
      with hBdef
    have hsubset : ∀ n, B ⊆ {z | b ≤ simpleNontangentialOperator beurlingKernel 0 (f - g n) z} := by
      intro n z hz
      by_contra hlt
      rw [Set.mem_setOf_eq, not_le] at hlt
      apply hz
      refine edist_lt_of_conv (hg n) z ha
        ⟨_, czOperator_beurling_tendsto_neg_pi ((hgsmooth n).of_le (by exact_mod_cast le_top))
          (hgc n) z⟩ ?_
      rw [hbdef] at hlt
      calc 2 * simpleNontangentialOperator beurlingKernel 0 (f - g n) z
          < 2 * (a / 4) := by gcongr; exact (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
        _ = a / 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm (2:ℝ≥0∞) a, mul_assoc]
            congr 1
            rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
              ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    have hmeas : ∀ n, volume B
        ≤ b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal :=
      fun n => le_trans (measure_mono (hsubset n)) (vol_ge (hf.sub (hg n)) hbne hbtop)
    have hto0 : Tendsto
        (fun n => b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.coe_ne_top)
      have h2 : Tendsto (fun n => ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal) atTop
          (𝓝 0) := by
        have h := (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp h1
        rw [show ((0:ℝ≥0∞) ^ p.toReal) = 0 by
          rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_pos hp_top)]] at h
        exact h
      have hbinv : b⁻¹ ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr hbne)
      have h3 := ENNReal.Tendsto.const_mul (a := b⁻¹ ^ p.toReal) h2 (Or.inr hbinv)
      rw [mul_zero] at h3
      exact h3
    exact le_antisymm (ge_of_tendsto hto0 (Eventually.of_forall hmeas)) (zero_le _)
  -- Assemble: union over the levels `1/(k+1)`, then `tendsto_of_cauchy_edist`.
  set Bk := fun k : ℕ => {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        < 1/((k:ℝ≥0∞)+1)} with hBk
  have hBknull : ∀ k, volume (Bk k) = 0 := by
    intro k
    apply osc_null
    · apply ENNReal.div_pos one_ne_zero
      exact (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩).ne
    · apply ENNReal.div_ne_top ENNReal.one_ne_top
      have hkp : (0:ℝ≥0∞) < (k:ℝ≥0∞)+1 := by positivity
      exact hkp.ne'
  have hunionnull : volume (⋃ k, Bk k) = 0 := measure_iUnion_null hBknull
  rw [ae_iff]
  refine measure_mono_null ?_ hunionnull
  intro z hz
  rw [Set.mem_setOf_eq] at hz
  rw [Set.mem_iUnion]
  by_contra hnot
  push_neg at hnot
  apply hz
  apply tendsto_of_cauchy_edist
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
  have hmem := hnot k
  simp only [hBk, Set.mem_setOf_eq, not_not] at hmem
  refine hmem.mono (fun q hq => lt_of_lt_of_le hq ?_)
  rw [one_div]
  calc ((k:ℝ≥0∞)+1)⁻¹ ≤ ((k:ℝ≥0∞))⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    _ ≤ ε := le_of_lt hk

/-! ## `Lᵖ` boundedness: passage to the Beurling transform

A.e. convergence of the truncations on `Lᵖ` (`1 < p < 2`), then Fatou, transfers
the uniform truncation bound to `beurling`. The `p = 2` case is the isometry; the
`p > 2` case is duality (the Beurling kernel is symmetric). -/

/-- **A.e. convergence of the truncations on `Lᵖ`**, `1 < p < 2`: the truncated
Beurling integrals converge a.e. as `r → 0⁺` to `-π · beurling f`. Extends the
`L²` result (`czOperator_beurling_ae_tendsto_neg_pi`) via the maximal-operator
weak-(1,1) bound and the `L¹ + L²` decomposition of `Lᵖ`. -/
lemma czOperator_beurling_ae_tendsto_neg_pi_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, Filter.Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π : ℂ) * beurling f z)) := by
  filter_upwards [czOperator_beurling_ae_tendsto_Lp hp1 hp2 hf] with z hz
  obtain ⟨L, hL⟩ := hz
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z) = L := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z
        = czOperator beurlingKernel r f z := fun r => rfl
    simpa only [hcz] using hL
  have hb : beurling f z = -(1 / (π : ℂ)) * L := by rw [beurling, hlim]
  have hval : -(π:ℂ) * beurling f z = L := by
    rw [hb]; have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hval]; exact hL

/-- **`Lᵖ` bound for the Beurling transform, `1 < p < 2`.** The uniform-in-`r`
truncation bound (`eLpNorm_czOperator_beurling_Lp`) passes to the limit by Fatou
(`eLpNorm_le_of_ae_tendsto` along `r → 0⁺`), using the a.e. convergence
`czOperator_beurling_ae_tendsto_neg_pi_Lp`. -/
lemma eLpNorm_beurling_Lp_le {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) {f : ℂ → ℂ}
    (hf : MemLp f p volume) :
    eLpNorm (beurling f) p volume
      ≤ (ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p : ℝ≥0∞)) * eLpNorm f p volume := by
  have hπpos : (0:ℝ) < 1 / π := by positivity
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set C : ℝ≥0∞ := (ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p : ℝ≥0∞)) * eLpNorm f p volume
    with hCdef
  -- The scaled family `F r = (-(1/π)) • czOperator beurlingKernel r f`.
  set F : ℝ → ℂ → ℂ := fun r => (-(1 / π : ℂ)) • czOperator beurlingKernel r f with hFdef
  -- Bound `eLpNorm (F r) p ≤ C` for `r > 0`.
  have hbound : ∀ᶠ r in 𝓝[>] (0:ℝ), eLpNorm (F r) p volume ≤ C := by
    refine eventually_nhdsWithin_of_forall (fun r hr => ?_)
    rw [Set.mem_Ioi] at hr
    rw [hFdef, eLpNorm_const_smul]
    have hnorm : ‖(-(1 / π : ℂ))‖ₑ = ENNReal.ofReal (1 / π) := by
      rw [← ofReal_norm_eq_enorm, norm_neg]
      congr 1
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnorm, hCdef, mul_assoc]
    exact mul_le_mul' (le_refl _) (eLpNorm_czOperator_beurling_Lp hp1 hp2 hr hf)
  -- Measurability of each `F r`.
  have hmeas : ∀ r, AEStronglyMeasurable (F r) volume := by
    intro r
    rw [hFdef]
    exact (aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable).const_smul _
  -- a.e. tendsto: scale the a.e. limit by `-(1/π)`.
  have hae : ∀ᵐ z ∂volume, Tendsto (fun r => F r z) (𝓝[>] (0:ℝ)) (𝓝 (beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi_Lp hp1 hp2 hf] with z hz
    have hscaled := hz.const_mul (-(1 / π : ℂ))
    have heq : -(1 / π : ℂ) * (-(π : ℂ) * beurling f z) = beurling f z := by
      field_simp
    rw [heq] at hscaled
    have hFz : (fun r => F r z) = fun r => -(1 / π : ℂ) * czOperator beurlingKernel r f z := by
      funext r; rw [hFdef]; simp [Pi.smul_apply, smul_eq_mul]
    rw [hFz]; exact hscaled
  exact Lp.eLpNorm_le_of_ae_tendsto hbound hmeas hae

/-- The Beurling kernel is symmetric: `K(z, ζ) = K(ζ, z)` (an even power of
`z - ζ`). This is the algebraic input that makes the Beurling transform its own
transpose, used for the `p > 2` range by duality. -/
lemma beurlingKernel_symm (z ζ : ℂ) : beurlingKernel z ζ = beurlingKernel ζ z := by
  unfold beurlingKernel
  rw [zpow_neg, zpow_neg, zpow_two, zpow_two,
    show (z - ζ) * (z - ζ) = (ζ - z) * (ζ - z) by ring]

/-! ## `Lᵖ` boundedness for `p > 2` by duality

The Beurling kernel is symmetric (`beurlingKernel_symm`), so the truncated
operator is its own transpose w.r.t. the bilinear pairing `∫ f·g`. For
`BoundedFiniteSupport` `f` (hence `f ∈ L¹`) the double integral is absolutely
convergent, so Fubini gives the truncation symmetry against any `g ∈ Lᵖ'`. By
duality (`eLpNorm_le_iSup_integral_mul`) and the `Lᵖ'` truncation bound (`p' < 2`,
`eLpNorm_czOperator_beurling_Lp`), `‖czOp r f‖_p ≤ C_{p'} ‖f‖_p`. The maximal
operator + a.e.-convergence development then transfers (as for `p < 2`) to
`beurling`. -/

/-- **Truncation symmetry.** For `f` of bounded finite support (hence in `L¹`) and
`g ∈ Lᵖ'`, the symmetric Beurling kernel and Fubini give
`∫ (czOp r f)·g = ∫ f·(czOp r g)`. -/
lemma czOperator_beurling_pairing_symm {p p' : ℝ≥0∞} (hp1 : 1 < p) (hp_top : p ≠ ⊤)
    [ENNReal.HolderConjugate p p'] {r : ℝ} (hr : 0 < r) {f g : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) (hg : MemLp g p' volume) :
    ∫ x, czOperator beurlingKernel r f x * g x ∂volume
      = ∫ x, f x * czOperator beurlingKernel r g x ∂volume := by
  haveI : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
  have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
  have hp'1 : 1 < p' :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
  have hf' : MemLp f p volume := hf.memLp p
  have hfint : Integrable f volume := hf.integrable
  -- For every `y`, the symmetric set `{x | r ≤ dist x y}` equals `(ball y r)ᶜ`.
  have hsetEq : ∀ y : ℂ, {x : ℂ | r ≤ dist x y} = (Metric.ball y r)ᶜ := by
    intro y; ext x; simp [Metric.mem_ball, not_lt, dist_comm]
  -- The kernel section centered at `y`, at exponent `p`, is in `Lᵖ`
  -- (`∫_{|u|≥r} |u|^{-2 p.toReal} < ∞` since `p.toReal > 1`), with a `y`-independent
  -- `Lᵖ` lintegral `Kr_lint = ∫⁻_{|u|≥r} ((‖u‖²)⁻¹)^{p.toReal}`.
  set q : ℝ := p.toReal with hq_def
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  have hq1 : 1 < q := by
    rw [hq_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
    exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top |>.mpr hp1
  have hq0 : 0 < q := lt_trans one_pos hq1
  -- `y`-independent finiteness of the kernel-section `Lᵖ` lintegral.
  have hlint : ∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q < ⊤ := by
    rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal := fun p =>
      (Set.Ici r ×ˢ Set.Ioo (-π) π).indicator
        (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q)) p with hbox
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      exact (Real.continuous_rpow_const hq0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
    have hbound : ∀ pp ∈ polarCoord.target,
        ENNReal.ofReal pp.1 • {u : ℂ | r ≤ ‖u‖}.indicator
          (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q) (Complex.polarCoord.symm pp) ≤ box pp := by
      intro pp hpp
      rw [polarCoord_target, Set.mem_prod] at hpp
      obtain ⟨hpp1, hpp2⟩ := hpp
      simp only [Set.mem_Ioi] at hpp1
      simp only [hbox]
      have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
      by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | r ≤ ‖u‖}
      · have hpR : r ≤ pp.1 := by rw [Set.mem_setOf_eq, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
        have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q = ENNReal.ofReal (((pp.1^2)⁻¹)^q) by
            rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
              ENNReal.ofReal_rpow_of_pos (by positivity)],
          ← ENNReal.ofReal_mul hpp1.le]
      · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le _
    refine lt_of_le_of_lt (setLIntegral_mono
      (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
    calc ∫⁻ pp in polarCoord.target, box pp
        ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
      _ = ∫⁻ pp in (Set.Ici r ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q) := by
            rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
            simp only [setLIntegral_const]
            rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
            apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
            have hint : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q) (Set.Ici r) volume := by
              have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q)
                  =ᶠ[ae (volume.restrict (Set.Ici r))]
                  (fun ρ : ℝ => ρ^(1 - 2 * q)) := by
                filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                simp only [Set.mem_Ici] at hρ
                have hρpos : 0 < ρ := lt_of_lt_of_le hr hρ
                have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                  rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                have h1 : ((ρ^2)⁻¹)^q = ρ^(-2 * q) := by
                  rw [hbase, ← Real.rpow_mul hρpos.le]
                have h2 : ρ * ρ^(-2 * q) = ρ^(1 - 2 * q) := by
                  nth_rewrite 1 [← Real.rpow_one ρ]
                  rw [← Real.rpow_add hρpos]; congr 1; ring
                rw [h1, h2]
              rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                integrableOn_Ioi_rpow_iff hr]
              nlinarith [hq1]
            have hfin := hint.2
            rw [hasFiniteIntegral_iff_enorm] at hfin
            refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
            · refine (measurable_id.mul ?_).enorm
              exact (Real.continuous_rpow_const hq0.le).measurable.comp
                ((measurable_id.pow_const 2).inv)
            · simp only [Set.mem_Ici] at hy
              have hypos : 0 < y := lt_of_lt_of_le hr hy
              rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- The kernel section centered at `y` lies in `Lᵖ`, with a `y`-independent `Lᵖ` norm bound.
  have hkermem_p : ∀ y : ℂ,
      eLpNorm (fun x => (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x) x) p volume
        ≤ (∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q) ^ (1 / q) := by
    intro y
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top, ← hq_def, one_div]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    have hpt : ∀ x, ‖(Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x) x‖ₑ ^ q
        = (Metric.ball y r)ᶜ.indicator (fun x => ‖beurlingKernel y x‖ₑ ^ q) x := by
      intro x
      by_cases h : x ∈ (Metric.ball y r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq0]
    refine le_of_eq_of_le (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ x, ‖beurlingKernel y x‖ₑ ^ q ≤ ((‖y - x‖ₑ ^ 2)⁻¹) ^ q := by
      intro x
      apply ENNReal.rpow_le_rpow _ hq0.le
      by_cases h : y = x
      · subst h; simp [beurlingKernel]
      · have hne : y - x ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel y x = ((y-x) * (y-x))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine le_trans (setLIntegral_mono ?_ (fun x _ => hkb x)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun x => (Metric.ball y r)ᶜ.indicator (fun x => ((‖y - x‖ₑ ^ 2)⁻¹) ^ q) x)
        = (fun x => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q) (y - x)) := by
      funext x
      have hiff : (x ∈ (Metric.ball y r)ᶜ) ↔ (y - x ∈ {u : ℂ | r ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_setOf_eq, dist_comm,
          Complex.dist_eq]
      by_cases h : x ∈ (Metric.ball y r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q) u) y]
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
  -- The `y`-independent Hölder constant.
  set Kr : ℝ≥0∞ := (∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q) ^ (1 / q) with hKr_def
  have hKr_ne_top : Kr ≠ ⊤ := by
    rw [hKr_def]; finiteness
  -- The Fubini integrand, oriented with the `L¹` variable `y` first.
  set F : ℂ → ℂ → ℂ := fun y x =>
    (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x * f y * g x) x with hF_def
  -- Pointwise: `∫ x, F y x = f y * czOperator beurlingKernel r g y` (kernel symmetry).
  have hFy : ∀ y, ∫ x, F y x = f y * czOperator beurlingKernel r g y := by
    intro y
    change ∫ x, (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x * f y * g x) x
      = f y * czOperator beurlingKernel r g y
    rw [integral_indicator measurableSet_ball.compl]
    change (∫ x in (Metric.ball y r)ᶜ, beurlingKernel y x * f y * g x)
      = f y * ∫ x in (Metric.ball y r)ᶜ, beurlingKernel y x * g x
    rw [show (f y * ∫ x in (Metric.ball y r)ᶜ, beurlingKernel y x * g x)
          = ∫ x in (Metric.ball y r)ᶜ, f y * (beurlingKernel y x * g x) from
        (integral_const_mul _ _).symm]
    refine setIntegral_congr_fun measurableSet_ball.compl (fun x _ => ?_)
    show beurlingKernel y x * f y * g x = f y * (beurlingKernel y x * g x)
    ring
  -- Pointwise: `∫ y, F y x = (czOperator beurlingKernel r f x) * g x`.
  have hFx : ∀ x, ∫ y, F y x = czOperator beurlingKernel r f x * g x := by
    intro x
    have hindEq : (fun y => F y x)
        = fun y => (Metric.ball x r)ᶜ.indicator
            (fun y => g x * (beurlingKernel x y * f y)) y := by
      funext y
      change (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x * f y * g x) x
        = (Metric.ball x r)ᶜ.indicator (fun y => g x * (beurlingKernel x y * f y)) y
      by_cases h : x ∈ Metric.ball y r
      · have hyc : y ∉ (Metric.ball x r)ᶜ := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_not]
          rw [Metric.mem_ball, dist_comm] at h; exact h
        have hxc : x ∉ (Metric.ball y r)ᶜ := by simp [h]
        rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hyc]
      · have hyc : y ∈ (Metric.ball x r)ᶜ := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt]
          rw [Metric.mem_ball, dist_comm, not_lt] at h; exact h
        have hxc : x ∈ (Metric.ball y r)ᶜ := by simp [h]
        rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hyc, beurlingKernel_symm y x]; ring
    rw [hindEq, integral_indicator measurableSet_ball.compl]
    rw [show (∫ y in (Metric.ball x r)ᶜ, g x * (beurlingKernel x y * f y))
          = g x * ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * f y from
        integral_const_mul _ _]
    change g x * czOperator beurlingKernel r f x = czOperator beurlingKernel r f x * g x
    rw [mul_comm]
  -- Absolute integrability of `uncurry F` on `volume.prod volume`.
  have hintF : Integrable (Function.uncurry F) (volume.prod volume) := by
    -- The "diagonal-shifted" support set, measurable in the product.
    have hSmeas : MeasurableSet {z : ℂ × ℂ | r ≤ dist z.2 z.1} :=
      measurableSet_le measurable_const (continuous_snd.dist continuous_fst).measurable
    have huncEq : Function.uncurry F
        = {z : ℂ × ℂ | r ≤ dist z.2 z.1}.indicator
            (fun z => beurlingKernel z.1 z.2 * f z.1 * g z.2) := by
      funext z
      change (Metric.ball z.1 r)ᶜ.indicator (fun x => beurlingKernel z.1 x * f z.1 * g x) z.2
        = {z : ℂ × ℂ | r ≤ dist z.2 z.1}.indicator
            (fun z => beurlingKernel z.1 z.2 * f z.1 * g z.2) z
      by_cases h : z.2 ∈ (Metric.ball z.1 r)ᶜ
      · have hz : z ∈ {z : ℂ × ℂ | r ≤ dist z.2 z.1} := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt] at h
          rw [Set.mem_setOf_eq]; exact h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hz]
      · have hz : z ∉ {z : ℂ × ℂ | r ≤ dist z.2 z.1} := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_not] at h
          rw [Set.mem_setOf_eq, not_le]; exact h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hz]
    have hmeasF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
      rw [huncEq]
      apply AEStronglyMeasurable.indicator _ hSmeas
      apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · apply Measurable.aestronglyMeasurable
          show Measurable (fun z : ℂ × ℂ => beurlingKernel z.1 z.2)
          unfold beurlingKernel; fun_prop
        · exact hf.aestronglyMeasurable.comp_fst
      · exact hg.aestronglyMeasurable.comp_snd
    rw [MeasureTheory.integrable_prod_iff hmeasF]
    constructor
    · -- a.e. `y`: `x ↦ F y x` integrable.
      filter_upwards with y
      change Integrable (fun x => (Metric.ball y r)ᶜ.indicator
        (fun x => beurlingKernel y x * f y * g x) x) volume
      rw [MeasureTheory.integrable_indicator_iff measurableSet_ball.compl]
      have hkg : IntegrableOn (fun x => beurlingKernel y x * g x) (Metric.ball y r)ᶜ volume :=
        integrableOn_beurlingKernel_mul_Lp (p := p') (p' := p) hr y hp'1 hp'_top hg
      have heq : (fun x => beurlingKernel y x * f y * g x)
          = (fun x => f y • (beurlingKernel y x * g x)) := by
        funext x; rw [smul_eq_mul]; ring
      rw [heq]
      exact (hkg.smul (f y))
    · -- `y ↦ ∫ x, ‖F y x‖` integrable, dominated by `Kr · ‖g‖_{p'} · ‖f y‖`.
      set Cg : ℝ≥0∞ := Kr * eLpNorm g p' volume with hCg_def
      have hCg_ne_top : Cg ≠ ⊤ := ENNReal.mul_ne_top hKr_ne_top hg.2.ne
      have hbd : ∀ y, ‖∫ x, ‖F y x‖ ∂volume‖ ≤ Cg.toReal * ‖f y‖ := by
        intro y
        have hnn : 0 ≤ ∫ x, ‖F y x‖ ∂volume := integral_nonneg (fun x => norm_nonneg _)
        rw [Real.norm_of_nonneg hnn]
        -- Express the real integral via its lintegral, then bound by Hölder.
        have hmeasFy : AEStronglyMeasurable (fun x => F y x) volume := by
          rw [hF_def]
          simp only
          apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
          apply AEStronglyMeasurable.mul _ (hg.aestronglyMeasurable)
          apply AEStronglyMeasurable.mul _ aestronglyMeasurable_const
          apply Measurable.aestronglyMeasurable
          unfold beurlingKernel; fun_prop
        have hle : (∫ x, ‖F y x‖ ∂volume) = (∫⁻ x, ‖F y x‖ₑ ∂volume).toReal :=
          integral_norm_eq_lintegral_enorm hmeasFy
        rw [hle]
        -- `∫⁻ x, ‖F y x‖ₑ = ‖f y‖ₑ · ∫⁻_{(ball y r)ᶜ} ‖K y x‖ₑ ‖g x‖ₑ`.
        have hlintEq : (∫⁻ x, ‖F y x‖ₑ ∂volume)
            = ‖f y‖ₑ * ∫⁻ x in (Metric.ball y r)ᶜ, ‖beurlingKernel y x‖ₑ * ‖g x‖ₑ := by
          rw [hF_def]
          simp only
          rw [show (fun x => ‖(Metric.ball y r)ᶜ.indicator
                (fun x => beurlingKernel y x * f y * g x) x‖ₑ)
              = (Metric.ball y r)ᶜ.indicator
                (fun x => ‖f y‖ₑ * (‖beurlingKernel y x‖ₑ * ‖g x‖ₑ)) from ?_]
          · rw [lintegral_indicator measurableSet_ball.compl, lintegral_const_mul']
            exact enorm_ne_top
          · funext x
            by_cases h : x ∈ (Metric.ball y r)ᶜ
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, enorm_mul, enorm_mul]; ring
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]
        rw [hlintEq]
        -- Hölder: `∫⁻_{(ball y r)ᶜ} ‖K y x‖ₑ ‖g x‖ₑ ≤ Kr · ‖g‖_{p'}`.
        have hHolder : (∫⁻ x in (Metric.ball y r)ᶜ, ‖beurlingKernel y x‖ₑ * ‖g x‖ₑ) ≤ Cg := by
          have hcs := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
            (μ := volume.restrict (Metric.ball y r)ᶜ) (p := p) (q := p')
            (ENNReal.HolderConjugate.symm)
            (f := fun x => ‖beurlingKernel y x‖ₑ) (g := fun x => ‖g x‖ₑ)
            (by unfold beurlingKernel; fun_prop) hg.aestronglyMeasurable.enorm.restrict
          simp only [eLpNorm_enorm] at hcs
          refine le_trans hcs ?_
          rw [hCg_def]
          refine mul_le_mul' ?_ (eLpNorm_restrict_le g p' volume _)
          refine le_trans ?_ (hkermem_p y)
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl]
        calc (‖f y‖ₑ * ∫⁻ x in (Metric.ball y r)ᶜ, ‖beurlingKernel y x‖ₑ * ‖g x‖ₑ).toReal
            ≤ (‖f y‖ₑ * Cg).toReal := by
              apply ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hCg_ne_top)
              exact mul_le_mul' le_rfl hHolder
          _ = Cg.toReal * ‖f y‖ := by
              rw [ENNReal.toReal_mul, toReal_enorm, mul_comm]
      refine Integrable.mono' (g := fun y => Cg.toReal * ‖f y‖) ?_ ?_ ?_
      · exact (hfint.norm.const_mul Cg.toReal)
      · exact (hmeasF.norm).integral_prod_right'
      · filter_upwards with y; exact hbd y
  -- Fubini: swap the order of integration.
  have hswap : ∫ y, ∫ x, F y x = ∫ x, ∫ y, F y x :=
    MeasureTheory.integral_integral_swap hintF
  -- Conclude.
  calc ∫ x, czOperator beurlingKernel r f x * g x ∂volume
      = ∫ x, ∫ y, F y x := by simp_rw [hFx]
    _ = ∫ y, ∫ x, F y x := hswap.symm
    _ = ∫ x, f x * czOperator beurlingKernel r g x ∂volume := by simp_rw [hFy]

/-- **Truncation `Lᵖ` bound for `p > 2`, by duality.** Using `Lᵖ` duality, the
truncation symmetry, and the `Lᵖ'` truncation bound (`p' ∈ (1,2)`),
`‖czOp r f‖_p ≤ beurlingTruncLpConst p' · ‖f‖_p` for all `f ∈ Lᵖ` (first for
bounded-finite-support `f`, then by density). -/
lemma eLpNorm_czOperator_beurling_Lp_high {p p' : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    [ENNReal.HolderConjugate p p'] {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : MemLp f p volume) :
    eLpNorm (czOperator beurlingKernel r f) p volume
      ≤ (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm f p volume := by
  haveI : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
  have hp1 : 1 < p := lt_trans (by norm_num) hp2
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  -- The conjugate exponent lies in `(1, 2)`.
  have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
  have hp'1 : 1 < p' :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
  have hp'0 : p' ≠ 0 := (ENNReal.HolderConjugate.pos p' p).ne'
  -- `p' < 2` from `2 < p` via the real Hölder identity.
  have hq2real : (2:ℝ) < p.toReal := by
    rw [show (2:ℝ) = (2:ℝ≥0∞).toReal from by simp]
    exact (ENNReal.toReal_lt_toReal (by simp) hp_top).mpr hp2
  have hinvReal : (p.toReal)⁻¹ + (p'.toReal)⁻¹ = 1 := by
    have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p p'
    have heq : (p⁻¹ + p'⁻¹).toReal = (1:ℝ≥0∞).toReal := by rw [h]
    rwa [ENNReal.toReal_add (by simp [hp0]) (by simp [hp'0]), ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_one] at heq
  have hp'2 : p' < 2 := by
    have hp'pos : 0 < p'.toReal := ENNReal.toReal_pos hp'0 hp'_top
    have hlt : p'.toReal < 2 := by
      have hppos : 0 < p.toReal := by linarith
      have hainv : (p.toReal)⁻¹ < 2⁻¹ := by
        rw [inv_lt_inv₀ hppos (by norm_num)]; exact hq2real
      have hbinv : 2⁻¹ < (p'.toReal)⁻¹ := by
        have hb : (p'.toReal)⁻¹ = 1 - (p.toReal)⁻¹ := by linarith
        rw [hb]; norm_num; linarith [hainv]
      rwa [inv_lt_inv₀ (by norm_num) hp'pos] at hbinv
    rw [← ENNReal.toReal_lt_toReal hp'_top (by simp), show (2:ℝ≥0∞).toReal = 2 from by simp]
    exact hlt
  have hq_pos : (0:ℝ) < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hq_ge2 : (2:ℝ) ≤ p.toReal := by
    rw [show (2:ℝ) = (2:ℝ≥0∞).toReal from by simp]
    exact ENNReal.toReal_le_toReal (by simp) hp_top |>.mpr hp2.le
  -- **MemLp helper:** a function in `L² ∩ L∞` is in `Lᵖ` for `2 ≤ p < ∞`.
  have hLp_of_L2_Linf : ∀ h : ℂ → ℂ, MemLp h 2 volume → MemLp h ∞ volume → MemLp h p volume := by
    intro h h2 hinf
    refine ⟨h2.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp_top]
    set C : ℝ≥0∞ := eLpNormEssSup h volume with hC_def
    have hC_top : C ≠ ⊤ := by
      rw [hC_def, ← eLpNorm_exponent_top]; exact hinf.2.ne
    have hbd : ∀ᵐ x ∂volume, ‖h x‖ₑ ^ p.toReal ≤ C ^ (p.toReal - 2) * ‖h x‖ₑ ^ (2:ℝ) := by
      filter_upwards [ae_le_eLpNormEssSup (f := h) (μ := volume)] with x hx
      by_cases hzero : ‖h x‖ₑ = 0
      · rw [hzero, ENNReal.zero_rpow_of_pos hq_pos,
          ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2), mul_zero]
      · have hnn : (0:ℝ) ≤ p.toReal - 2 := by linarith
        have hxtop : ‖h x‖ₑ ≠ ⊤ := (hx.trans_lt (lt_top_iff_ne_top.mpr hC_top)).ne
        calc ‖h x‖ₑ ^ p.toReal
            = ‖h x‖ₑ ^ (p.toReal - 2) * ‖h x‖ₑ ^ (2:ℝ) := by
              rw [← ENNReal.rpow_add _ _ hzero hxtop]; ring_nf
          _ ≤ C ^ (p.toReal - 2) * ‖h x‖ₑ ^ (2:ℝ) :=
              mul_le_mul' (ENNReal.rpow_le_rpow hx hnn) le_rfl
    refine lt_of_le_of_lt (lintegral_mono_ae hbd) ?_
    rw [lintegral_const_mul' _ _ (by
      apply ENNReal.rpow_ne_top_of_nonneg (by linarith) hC_top)]
    have h2lint : (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂volume) < ⊤ := by
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (μ := volume) (f := h) (p := 2) (by simp) (by simp)).mp h2.2
      simpa using this
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hC_top)) h2lint
  -- **Hölder pairing bound:** `‖∫ a·b‖ₑ ≤ eLpNorm a p · eLpNorm b p'`.
  have hPairing : ∀ a b : ℂ → ℂ, AEStronglyMeasurable a volume → AEStronglyMeasurable b volume →
      ‖∫ x, a x * b x ∂volume‖ₑ ≤ eLpNorm a p volume * eLpNorm b p' volume := by
    intro a b ha hb
    calc ‖∫ x, a x * b x ∂volume‖ₑ
        ≤ ∫⁻ x, ‖a x * b x‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ x, ‖a x‖ₑ * ‖b x‖ₑ ∂volume := by simp_rw [enorm_mul]
      _ ≤ eLpNorm a p volume * eLpNorm b p' volume := by
          have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
            (μ := volume) (p := p) (q := p') inferInstance
            (f := fun x => ‖a x‖ₑ) (g := fun x => ‖b x‖ₑ) ha.enorm hb.enorm
          simpa [eLpNorm_enorm] using this
  -- **Part (a): the bound for `BoundedFiniteSupport` `f`.**
  have hBFS : ∀ h : ℂ → ℂ, BoundedFiniteSupport h volume →
      eLpNorm (czOperator beurlingKernel r h) p volume
        ≤ (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm h p volume := by
    intro h hh
    have hhLp : MemLp h p volume := hh.memLp p
    -- `czOp r h ∈ L² ∩ L∞ ⊆ Lᵖ`.
    have hczL2 : MemLp (czOperator beurlingKernel r h) 2 volume :=
      ⟨aestronglyMeasurable_czOperator_beurling (hh.memLp 2),
        lt_of_le_of_lt (eLpNorm_czOperator_beurling_L2 hr (hh.memLp 2))
          (ENNReal.mul_lt_top (by finiteness) (hh.memLp 2).2)⟩
    -- The `L¹` operator enorm bound: `‖czOp r h x‖ₑ ≤ ofReal(r⁻²)·‖h‖₁`.
    have hOpBoundE : ∀ x : ℂ, ‖czOperator beurlingKernel r h x‖ₑ
        ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
      intro x
      have hkernelEnorm : ∀ y ∈ (Metric.ball x r)ᶜ,
          ‖beurlingKernel x y‖ₑ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := by
        intro y hy
        have hr_le : r ≤ ‖x - y‖ := by
          rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_comm] at hy
          rw [Complex.dist_eq] at hy; exact hy
        have hxy_pos : 0 < ‖x - y‖ := lt_of_lt_of_le hr hr_le
        have hnorm : ‖beurlingKernel x y‖ = ‖x - y‖ ^ (-2 : ℤ) := by
          rw [beurlingKernel, norm_zpow]
        have hle : ‖beurlingKernel x y‖ ≤ (r : ℝ) ^ (-2 : ℤ) := by
          rw [hnorm, zpow_neg, zpow_neg, zpow_two, zpow_two]
          exact inv_anti₀ (by positivity) (mul_le_mul hr_le hr_le hr.le hxy_pos.le)
        calc ‖beurlingKernel x y‖ₑ = ENNReal.ofReal ‖beurlingKernel x y‖ :=
              (ofReal_norm_eq_enorm _).symm
          _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := ENNReal.ofReal_le_ofReal hle
      have hczeq : czOperator beurlingKernel r h x
          = ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y := rfl
      rw [hczeq]
      calc ‖∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y‖ₑ
          ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y * h y‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
        _ ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ‖h y‖ₑ := by
            exact setLIntegral_mono' measurableSet_ball.compl
              (fun y hy => mul_le_mul' (hkernelEnorm y hy) le_rfl)
        _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ))
              * ∫⁻ y in (Metric.ball x r)ᶜ, ‖h y‖ₑ := by rw [lintegral_const_mul']; finiteness
        _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ∫⁻ y, ‖h y‖ₑ :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
        _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
            rw [eLpNorm_one_eq_lintegral_enorm]
    have hczLinf : MemLp (czOperator beurlingKernel r h) ∞ volume := by
      set M : ℝ := (r : ℝ) ^ (-2 : ℤ) * (eLpNorm h 1 volume).toReal with hM_def
      refine memLp_top_of_bound
        (aestronglyMeasurable_czOperator_beurling' hhLp.aestronglyMeasurable) M ?_
      filter_upwards with x
      have hbE := hOpBoundE x
      rw [← ofReal_norm_eq_enorm] at hbE
      have hh1 : eLpNorm h 1 volume ≠ ⊤ := (hh.memLp 1).2.ne
      have hprod : ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume
          = ENNReal.ofReal M := by
        rw [hM_def, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hh1]
      rw [hprod] at hbE
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbE
    have hczLp : MemLp (czOperator beurlingKernel r h) p volume :=
      hLp_of_L2_Linf _ hczL2 hczLinf
    -- Duality: bound `‖czOp r h‖_p` by the supremum of the pairing.
    refine le_trans (eLpNorm_le_iSup_integral_mul (p' := p') hp1 hp_top hczLp) ?_
    refine iSup_le (fun g => iSup_le (fun hgmem => iSup_le (fun hgle => ?_)))
    -- Pairing symmetry + Hölder + `Lᵖ'` truncation bound.
    calc ‖∫ x, czOperator beurlingKernel r h x * g x ∂volume‖ₑ
        = ‖∫ x, h x * czOperator beurlingKernel r g x ∂volume‖ₑ := by
          rw [czOperator_beurling_pairing_symm hp1 hp_top hr hh hgmem]
      _ ≤ eLpNorm h p volume * eLpNorm (czOperator beurlingKernel r g) p' volume :=
          hPairing h (czOperator beurlingKernel r g) hhLp.aestronglyMeasurable
            (aestronglyMeasurable_czOperator_beurling' hgmem.aestronglyMeasurable)
      _ ≤ eLpNorm h p volume * ((beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm g p' volume) :=
          mul_le_mul' le_rfl (eLpNorm_czOperator_beurling_Lp hp'1 hp'2 hr hgmem)
      _ ≤ eLpNorm h p volume * ((beurlingTruncLpConst p' : ℝ≥0∞) * 1) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hgle)
      _ = (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm h p volume := by
          rw [mul_one, mul_comm]
  -- **Part (b): density extension to all of `Lᵖ`.**
  have hp1' : (1:ℝ≥0∞) ≤ p := hp1.le
  -- Smooth compactly-supported `Lᵖ`-approximating sequence (`BoundedFiniteSupport`).
  choose gg hggc hggsmooth hggle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le hp_top hp1' (ε := 1/(n+1)) (by positivity)
  have hggmem : ∀ n, MemLp (gg n) p volume := fun n =>
    (hggsmooth n).continuous.memLp_of_hasCompactSupport (hggc n)
  have hggBFS : ∀ n, BoundedFiniteSupport (gg n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hggsmooth n) (hggc n)
  have htend : Tendsto (fun n => eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le _) hggle
  -- The kernel section centered at `x` is in `Lᵖ'` (`∫_{|u|≥r}|u|^{-2 p'.toReal} < ∞`).
  set q' : ℝ := p'.toReal with hq'_def
  have hq'1 : 1 < q' := by
    rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
    exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
  have hq'0 : 0 < q' := lt_trans one_pos hq'1
  have hlint' : ∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
    rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal := fun p =>
      (Set.Ici r ×ˢ Set.Ioo (-π) π).indicator
        (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      exact (Real.continuous_rpow_const hq'0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
    have hbound : ∀ pp ∈ polarCoord.target,
        ENNReal.ofReal pp.1 • {u : ℂ | r ≤ ‖u‖}.indicator
          (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm pp) ≤ box pp := by
      intro pp hpp
      rw [polarCoord_target, Set.mem_prod] at hpp
      obtain ⟨hpp1, hpp2⟩ := hpp
      simp only [Set.mem_Ioi] at hpp1
      simp only [hbox]
      have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
      by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | r ≤ ‖u‖}
      · have hpR : r ≤ pp.1 := by rw [Set.mem_setOf_eq, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
        have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((pp.1^2)⁻¹)^q') by
            rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
              ENNReal.ofReal_rpow_of_pos (by positivity)],
          ← ENNReal.ofReal_mul hpp1.le]
      · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le _
    refine lt_of_le_of_lt (setLIntegral_mono
      (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
    calc ∫⁻ pp in polarCoord.target, box pp
        ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
      _ = ∫⁻ pp in (Set.Ici r ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q') := by
            rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
            simp only [setLIntegral_const]
            rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
            apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
            have hint : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici r) volume := by
              have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                  =ᶠ[ae (volume.restrict (Set.Ici r))]
                  (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                simp only [Set.mem_Ici] at hρ
                have hρpos : 0 < ρ := lt_of_lt_of_le hr hρ
                have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                  rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                have h1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                  rw [hbase, ← Real.rpow_mul hρpos.le]
                have h2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                  nth_rewrite 1 [← Real.rpow_one ρ]
                  rw [← Real.rpow_add hρpos]; congr 1; ring
                rw [h1, h2]
              rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                integrableOn_Ioi_rpow_iff hr]
              nlinarith [hq'1]
            have hfin := hint.2
            rw [hasFiniteIntegral_iff_enorm] at hfin
            refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
            · refine (measurable_id.mul ?_).enorm
              exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                ((measurable_id.pow_const 2).inv)
            · simp only [Set.mem_Ici] at hy
              have hypos : 0 < y := lt_of_lt_of_le hr hy
              rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hkersec : ∀ x : ℂ, MemLp
      (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p' volume := by
    intro x
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top, ← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y‖ₑ ^ q'
        = (Metric.ball x r)ᶜ.indicator (fun y => ‖beurlingKernel x y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x y‖ₑ ^ q' ≤ ((‖x - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x = y
      · subst h; simp [beurlingKernel]
      · have hne : x - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x y = ((x-y) * (x-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x r)ᶜ.indicator (fun y => ((‖x - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x r)ᶜ) ↔ (x - y ∈ {u : ℂ | r ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_setOf_eq, dist_comm,
          Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x]
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint'
  -- Per-point Hölder bound: `‖czOp r u x‖ₑ ≤ ‖kernel section_x‖_{p'} · ‖u‖_p`.
  have hHolderPt : ∀ (x : ℂ) {u : ℂ → ℂ}, MemLp u p volume →
      ‖czOperator beurlingKernel r u x‖ₑ
        ≤ eLpNorm (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p'
            volume * eLpNorm u p volume := by
    intro x u hu
    have hcs : ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖u y‖ₑ
        ≤ eLpNorm (fun y => beurlingKernel x y) p' (volume.restrict (Metric.ball x r)ᶜ)
          * eLpNorm u p (volume.restrict (Metric.ball x r)ᶜ) := by
      have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
        (μ := volume.restrict (Metric.ball x r)ᶜ) (p := p') (q := p) (ENNReal.HolderConjugate.symm)
        (f := fun y => ‖beurlingKernel x y‖ₑ) (g := fun y => ‖u y‖ₑ)
        (by unfold beurlingKernel; fun_prop) hu.aestronglyMeasurable.enorm.restrict
      simpa [eLpNorm_enorm] using this
    have hczeq : czOperator beurlingKernel r u x
        = ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * u y := rfl
    rw [hczeq]
    calc ‖∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * u y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y * u y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖u y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ eLpNorm (fun y => beurlingKernel x y) p' (volume.restrict (Metric.ball x r)ᶜ)
            * eLpNorm u p (volume.restrict (Metric.ball x r)ᶜ) := hcs
      _ ≤ eLpNorm (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p'
              volume * eLpNorm u p volume :=
          mul_le_mul'
            (le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm)
            (eLpNorm_restrict_le u p volume _)
  -- `czOp r (gg n) x → czOp r f x` for every `x` (uniform Hölder bound on the difference).
  have hconv : ∀ x : ℂ, Tendsto (fun n => czOperator beurlingKernel r (gg n) x) atTop
      (𝓝 (czOperator beurlingKernel r f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set C := eLpNorm
      (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p' volume with hCdef
    have hCne : C ≠ ⊤ := by rw [hCdef]; exact (hkersec x).2.ne
    -- The enorm difference `→ 0`.
    have hbdE : ∀ n, ‖czOperator beurlingKernel r (gg n) x - czOperator beurlingKernel r f x‖ₑ
        ≤ C * eLpNorm (gg n - f) p volume := by
      intro n
      rw [← czOperator_beurling_sub_Lp hp1 hp_top hr x (hggmem n) hf]
      exact hHolderPt x ((hggmem n).sub hf)
    have hRHS0 : Tendsto (fun n => C * eLpNorm (gg n - f) p volume) atTop (𝓝 0) := by
      have heq : ∀ n, eLpNorm (gg n - f) p volume = eLpNorm (f - gg n) p volume := by
        intro n; rw [← eLpNorm_neg]; congr 1; funext y; simp
      have : Tendsto (fun n => C * eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul htend (Or.inr hCne)
      exact this.congr (fun n => by rw [heq n])
    have henorm0 : Tendsto
        (fun n => ‖czOperator beurlingKernel r (gg n) x - czOperator beurlingKernel r f x‖ₑ)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHS0
        (fun n => zero_le _) hbdE
    have := (ENNReal.tendsto_toReal (by simp)).comp henorm0
    simpa [Function.comp, toReal_enorm] using this
  -- Fatou: pass the BFS bound `eLpNorm (czOp r (gg n)) p ≤ C_{p'} · ‖gg n‖_p` to the limit.
  have hggnorm : Tendsto (fun n => eLpNorm (gg n) p volume) atTop (𝓝 (eLpNorm f p volume)) := by
    set L := eLpNorm f p volume with hL
    set d := fun n => eLpNorm (f - gg n) p volume with hd
    have hupper : ∀ n, eLpNorm (gg n) p volume ≤ L + d n := by
      intro n
      have h : eLpNorm (gg n) p volume ≤ eLpNorm f p volume + eLpNorm (gg n - f) p volume := by
        calc eLpNorm (gg n) p volume = eLpNorm (f + (gg n - f)) p volume := by
              congr 1; funext y; simp
          _ ≤ eLpNorm f p volume + eLpNorm (gg n - f) p volume :=
              eLpNorm_add_le hf.aestronglyMeasurable
                ((hggmem n).sub hf).aestronglyMeasurable hp1'
      rw [hL, hd]
      rwa [show eLpNorm (gg n - f) p volume = eLpNorm (f - gg n) p volume from by
        rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
    have hlower : ∀ n, L - d n ≤ eLpNorm (gg n) p volume := by
      intro n
      rw [tsub_le_iff_right]
      calc L = eLpNorm ((gg n) + (f - gg n)) p volume := by rw [hL]; congr 1; funext y; simp
        _ ≤ eLpNorm (gg n) p volume + eLpNorm (f - gg n) p volume :=
            eLpNorm_add_le (hggmem n).aestronglyMeasurable
              (hf.sub (hggmem n)).aestronglyMeasurable hp1'
    have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
      simpa using tendsto_const_nhds.add htend
    have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
      simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend
        (Or.inr (by simp)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
  have hCfin : Tendsto (fun n => (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop
      (𝓝 ((beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm f p volume)) :=
    ENNReal.Tendsto.const_mul hggnorm (Or.inr ENNReal.coe_ne_top)
  -- The BFS bound holds for each `gg n`.
  have hggbd : ∀ n, eLpNorm (czOperator beurlingKernel r (gg n)) p volume
      ≤ (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm (gg n) p volume :=
    fun n => hBFS (gg n) (hggBFS n)
  -- Pass to the limit by Fatou via the `ε`-route.
  set K := (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm f p volume with hKdef
  have hKfin : K < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hKlt : K < K + (ε : ℝ≥0∞) := ENNReal.lt_add_right hKfin.ne (by exact_mod_cast hε.ne')
  have hbound : ∀ᶠ n in atTop,
      eLpNorm (czOperator beurlingKernel r (gg n)) p volume ≤ K + (ε : ℝ≥0∞) := by
    have hev := hCfin.eventually_le_const hKlt
    filter_upwards [hev] with n hn
    exact le_trans (hggbd n) hn
  exact Lp.eLpNorm_le_of_ae_tendsto hbound
    (fun n => aestronglyMeasurable_czOperator_beurling' (hggmem n).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => hconv x))

/-- **Maximal-operator `Lᵖ` bound for `p > 2`** (the `p < 2` replication
`exists_eLpNorm_simpleNontangential_beurling_Lp` with the duality truncation bound
`eLpNorm_czOperator_beurling_Lp_high`). -/
lemma exists_eLpNorm_simpleNontangential_beurling_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p)
    (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ g : ℂ → ℂ, MemLp g p volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C : ℝ≥0∞) * eLpNorm g p volume := by
  have hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞) < 2) hp2
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  -- The conjugate exponent `p' = (1 - p⁻¹)⁻¹` and its `HolderConjugate` instance,
  -- needed for the duality (`p > 2`) truncation bound `eLpNorm_czOperator_beurling_Lp_high`.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'_def
  have hpinv_le_one : p⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; exact hp1.le
  haveI hHC : ENNReal.HolderConjugate p p' := by
    rw [hp'_def, ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  -- `p` as an `ℝ≥0`, with `1 < pnn`.
  set pnn : ℝ≥0 := p.toNNReal with hpnn_def
  have hpnn_coe : (pnn : ℝ≥0∞) = p := by rw [hpnn_def, ENNReal.coe_toNNReal hp_top]
  have hpnn1 : 1 < pnn := by
    have : (1 : ℝ≥0∞) < (pnn : ℝ≥0∞) := by rw [hpnn_coe]; exact hp1
    exact_mod_cast this
  -- The HL maximal `Lᵖ` strong-type bound (constant `Cgmf`).
  -- Use the `defaultA 4` doubling structure (the one carried by the Carleson lemmas).
  haveI hA4 : (volume : Measure ℂ).IsDoubling ((defaultA 4 : ℕ) : ℝ≥0) :=
    doublingMeasure_complex_defaultA4.toIsDoubling
  set Cgmf : ℝ≥0 := C2_0_6' ((defaultA 4 : ℕ) : ℝ≥0) 1 pnn with hCgmf_def
  have hgmf : HasStrongType
      (globalMaximalFunction (X := ℂ) (E := ℂ) (A := ((defaultA 4 : ℕ) : ℝ≥0)) volume 1)
      (pnn : ℝ≥0∞) (pnn : ℝ≥0∞) volume volume Cgmf :=
    hasStrongType_globalMaximalFunction (X := ℂ) (E := ℂ) (μ := volume)
      (A := ((defaultA 4 : ℕ) : ℝ≥0)) (p₁ := 1) (p₂ := pnn) zero_lt_one hpnn1
  -- Abbreviations for the truncation constant (the duality constant `beurlingTruncLpConst p'`).
  set Ctr : ℝ≥0 := beurlingTruncLpConst p' with hCtr_def
  -- **Part (a): the BFS bound at a positive scale `r`.**
  set C₀ : ℝ≥0 := 4 * Cgmf * Ctr + (C10_1_5 4 + C10_1_2 4) * Cgmf with hC₀_def
  have hBFSscale : ∀ {r : ℝ}, 0 < r → ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel r g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro r hr g hg
    -- The strong-type input for Cotlar's estimate (`L²` truncation bound).
    have hT : ∀ s > 0, HasBoundedStrongType (czOperator beurlingKernel s) 2 2 volume volume
        (C_Ts 4 : ℝ≥0∞) := fun s hs => czOperator_beurling_strongType_L2 hs
    -- The pointwise dominating function (Cotlar + x-shift), exponent-free.
    set pointwise : ℂ → ℝ≥0∞ :=
      4 * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        + C10_1_5 4 • globalMaximalFunction volume 1 g
        + C10_1_2 4 • globalMaximalFunction volume 1 g with hpw_def
    -- Pointwise domination (verbatim from `simple_nontangential_operator`).
    have hdom : ∀ x, simpleNontangentialOperator beurlingKernel r g x ≤ pointwise x := by
      simp_rw [hpw_def, simpleNontangentialOperator, iSup_le_iff]
      intro x R hR x' hx'
      rw [Metric.mem_ball, dist_comm] at hx'
      trans ‖czOperator beurlingKernel R g x‖ₑ
          + C10_1_2 4 * globalMaximalFunction volume 1 g x
      · calc ‖czOperator beurlingKernel R g x'‖ₑ
            = ‖czOperator beurlingKernel R g x
              + (czOperator beurlingKernel R g x' - czOperator beurlingKernel R g x)‖ₑ := by
              congr 1; ring
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + ‖czOperator beurlingKernel R g x'
                - czOperator beurlingKernel R g x‖ₑ := enorm_add_le _ _
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + C10_1_2 4 * globalMaximalFunction volume 1 g x := by
              gcongr
              rw [← edist_eq_enorm_sub, edist_comm]
              exact estimate_x_shift (K := beurlingKernel) (by norm_num) hg
                (hr.trans hR.lt) hx'.le
      · refine add_le_add (cotlar_estimate (K := beurlingKernel) (r := r) (R := R)
          (by norm_num) hT hg ?_) (by rfl) |>.trans ?_
        · rw [Set.mem_Ioc]; exact ⟨hr, hR.le⟩
        · apply le_of_eq
          simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, ENNReal.smul_def, smul_eq_mul,
            Pi.ofNat_apply, add_assoc]
    -- Take `eLpNorm _ p` and use the additivity + maximal `Lᵖ` + truncation `Lᵖ` bounds.
    refine (eLpNorm_mono_enorm (g := pointwise) (fun x => by
      simp only [enorm_eq_self]; exact hdom x)).trans ?_
    -- `czOperator r g ∈ Lᵖ` and `g ∈ Lᵖ` (from `BoundedFiniteSupport`).
    have hgLp : MemLp g p volume := hg.memLp p
    have hczLp : MemLp (czOperator beurlingKernel r g) p volume := by
      refine ⟨aestronglyMeasurable_czOperator_beurling' hgLp.aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt (eLpNorm_czOperator_beurling_Lp_high (p' := p') hp2 hp_top hr hgLp)
        (ENNReal.mul_lt_top ENNReal.coe_lt_top hgLp.2)
    -- Strong-type bounds for the maximal functions.
    have hgmf_g := (hgmf g (by rw [hpnn_coe]; exact hgLp)).2
    have hgmf_czg := (hgmf (czOperator beurlingKernel r g) (by rw [hpnn_coe]; exact hczLp)).2
    rw [hpnn_coe] at hgmf_g hgmf_czg
    -- Measurability for `eLpNorm_add_le`.
    have hm_czg : AEStronglyMeasurable
        (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) volume :=
      MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    have hm_g : AEStronglyMeasurable (globalMaximalFunction volume 1 g) volume :=
      MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    rw [hpw_def, show (4 : ℂ → ℝ≥0∞) * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        = (4 : ℝ≥0) • globalMaximalFunction volume 1 (czOperator beurlingKernel r g) by
      ext y; simp [ENNReal.smul_def]]
    -- Split the eLpNorm of the sum.
    refine (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1').trans ?_
    refine (add_le_add (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1') (le_refl _)).trans ?_
    rw [show eLpNorm ((4 : ℝ≥0) • globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        = ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume from eLpNorm_const_smul',
      show eLpNorm (C10_1_5 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul',
      show eLpNorm (C10_1_2 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul']
    -- Apply the maximal `Lᵖ` bound and then the truncation `Lᵖ` bound.
    have hkey : ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
          + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
      have hb1 : eLpNorm (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) p volume
          ≤ (Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume) := by
        refine hgmf_czg.trans ?_
        rw [hCtr_def]
        exact mul_le_mul' (le_refl _)
          (eLpNorm_czOperator_beurling_Lp_high (p' := p') hp2 hp_top hr hgLp)
      have hb2 : eLpNorm (globalMaximalFunction volume 1 g) p volume
          ≤ (Cgmf : ℝ≥0∞) * eLpNorm g p volume := hgmf_g
      calc ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
              (czOperator beurlingKernel r g)) p volume
            + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
              + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
          ≤ ‖(4 : ℝ≥0)‖ₑ * ((Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume))
              + (‖C10_1_5 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)
                + ‖C10_1_2 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)) := by
            gcongr
        _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
            rw [hC₀_def]
            push_cast [enorm_NNReal]
            ring
    rw [add_assoc]; exact hkey
  -- **Scale-0 BFS bound** (monotone convergence over `r = (n+1)⁻¹`).
  have hBFS0 : ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro g hg
    set fseq : ℕ → ℂ → ℝ≥0∞ :=
      fun n => simpleNontangentialOperator beurlingKernel (n + 1 : ℝ)⁻¹ g with hfseq_def
    have f_mon : ∀ x : ℂ, Monotone fun n => fseq n x := by
      intro x m n hmn
      simp only [hfseq_def, simpleNontangentialOperator]
      gcongr with R
      apply iSup_const_mono (lt_of_le_of_lt _)
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      simp only [add_le_add_iff_right]
      exact_mod_cast hmn
    have snt0 : ⨆ (n : ℕ), fseq n = simpleNontangentialOperator beurlingKernel 0 g := by
      ext x
      simp only [hfseq_def]
      simp_rw [iSup_apply, simpleNontangentialOperator, gt_iff_lt]
      rw [iSup_comm]
      congr 1; ext R
      apply le_antisymm (iSup_le <| fun n => iSup_const_mono (lt_trans (by positivity)))
        (iSup_le _)
      intro hR
      set n := Nat.ceil R⁻¹ with hn_def
      have hn : (n + 1 : ℝ)⁻¹ < R :=
        inv_lt_of_inv_lt₀ hR <| (Nat.le_ceil R⁻¹).trans_lt (by exact_mod_cast lt_add_one _)
      refine le_iSup_of_le n ?_
      rw [iSup_pos hn]
    have mct := eLpNorm_iSup' (p := p) (f := fseq) (μ := volume)
      (fun n => aestronglyMeasurable_simpleNontangentialOperator.aemeasurable)
      (by filter_upwards; exact f_mon)
    rw [← snt0, ← mct]
    apply iSup_le
    intro n
    exact hBFSscale (r := (n + 1 : ℝ)⁻¹) (by positivity) g hg
  -- **Part (b): extend the scale-0 bound from `BoundedFiniteSupport` to all of `Lᵖ`.**
  -- Per-point Hölder bound for the truncation against an `Lᵖ` function.
  have hHolderPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {h : ℂ → ℂ}, MemLp h p volume →
      ‖czOperator beurlingKernel R h x'‖ₑ
        ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
            volume * eLpNorm h p volume := by
    intro R hR x' h hh
    unfold czOperator
    have hcs : ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ
        ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
          * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := by
      have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
        (μ := volume.restrict (Metric.ball x' R)ᶜ) (p := p') (q := p)
        (ENNReal.HolderConjugate.symm)
        (f := fun y => ‖beurlingKernel x' y‖ₑ) (g := fun y => ‖h y‖ₑ)
        (by unfold beurlingKernel; fun_prop) hh.aestronglyMeasurable.enorm.restrict
      simpa [eLpNorm_enorm] using this
    calc ‖∫ y in (Metric.ball x' R)ᶜ, beurlingKernel x' y * h y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y * h y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
            * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := hcs
      _ ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
              volume * eLpNorm h p volume := by
          refine mul_le_mul' ?_ ?_
          · exact le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm
          · exact eLpNorm_restrict_le h p volume _
  -- Kernel-section `Lᵖ'` membership (so the per-point constant is finite).
  have hkermem : ∀ (x' : ℂ) (R : ℝ), 0 < R →
      MemLp (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p' volume := by
    intro x' R hR
    -- The membership via the `Lᵖ'` lintegral finiteness.
    haveI : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
    have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
    have hp'1 : 1 < p' :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
    set q' : ℝ := p'.toReal with hq'_def
    have hp'0 : p' ≠ 0 := ne_of_gt (lt_trans one_pos hp'1)
    have hq'1 : 1 < q' := by
      rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
      exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
    have hq'0 : 0 < q' := lt_trans one_pos hq'1
    have hlint : ∫⁻ u : ℂ in {u : ℂ | R ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
      rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
        ← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ici R ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
      have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
        apply ENNReal.measurable_ofReal.comp
        apply Measurable.mul measurable_fst
        exact (Real.continuous_rpow_const hq'0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
      have hbound : ∀ pp ∈ polarCoord.target,
          ENNReal.ofReal pp.1 • {u : ℂ | R ≤ ‖u‖}.indicator
            (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm pp) ≤ box pp := by
        intro pp hpp
        rw [polarCoord_target, Set.mem_prod] at hpp
        obtain ⟨hpp1, hpp2⟩ := hpp
        simp only [Set.mem_Ioi] at hpp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
        by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | R ≤ ‖u‖}
        · have hpR : R ≤ pp.1 := by rw [Set.mem_setOf_eq, hnorm] at hmem; exact hmem
          rw [Set.indicator_of_mem hmem,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
          have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
            rw [← ofReal_norm_eq_enorm, hnorm]
          rw [henorm, smul_eq_mul,
            show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((pp.1^2)⁻¹)^q') by
              rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
                ENNReal.ofReal_rpow_of_pos (by positivity)],
            ← ENNReal.ofReal_mul hpp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le _
      refine lt_of_le_of_lt (setLIntegral_mono
        (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
      calc ∫⁻ pp in polarCoord.target, box pp
          ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
        _ = ∫⁻ pp in (Set.Ici R ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q') := by
              rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint2 : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici R) volume := by
                have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                    =ᶠ[ae (volume.restrict (Set.Ici R))]
                    (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                  simp only [Set.mem_Ici] at hρ
                  have hρpos : 0 < ρ := lt_of_lt_of_le hR hρ
                  have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                    rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                  have hh1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                    rw [hbase, ← Real.rpow_mul hρpos.le]
                  have hh2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                    nth_rewrite 1 [← Real.rpow_one ρ]
                    rw [← Real.rpow_add hρpos]; congr 1; ring
                  rw [hh1, hh2]
                rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                  integrableOn_Ioi_rpow_iff hR]
                nlinarith [hq'1]
              have hfin := hint2.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
              · refine (measurable_id.mul ?_).enorm
                exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                  ((measurable_id.pow_const 2).inv)
              · simp only [Set.mem_Ici] at hy
                have hypos : 0 < y := lt_of_lt_of_le hR hy
                rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top, ← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y‖ₑ ^ q'
        = (Metric.ball x' R)ᶜ.indicator (fun y => ‖beurlingKernel x' y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x' y‖ₑ ^ q' ≤ ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x' = y
      · subst h; simp [beurlingKernel]
      · have hne : x' - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x' y = ((x'-y) * (x'-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x' - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x' R)ᶜ) ↔ (x' - y ∈ {u : ℂ | R ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_setOf_eq, dist_comm, Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x']
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint
  -- Per-point liminf bound (Hölder `Lᵖ`-continuity in the function argument).
  have hLiminfPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {f : ℂ → ℂ} {gg : ℕ → ℂ → ℂ},
      MemLp f p volume → (∀ n, MemLp (gg n) p volume) →
      Tendsto (fun n => eLpNorm (f - gg n) p volume) atTop (𝓝 0) →
      ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop := by
    intro R hR x' f gg hf hgmem htend
    set C := eLpNorm
      (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p' volume with hCdef
    have hbd : ∀ n, ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ + C * eLpNorm (f - gg n) p volume := by
      intro n
      have hsub : ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ
          ≤ C * eLpNorm (f - gg n) p volume := by
        rw [← czOperator_beurling_sub_Lp hp1 hp_top hR x' hf (hgmem n)]
        exact hHolderPt R hR x' (hf.sub (hgmem n))
      calc ‖czOperator beurlingKernel R f x'‖ₑ
          ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ := by
              rw [add_comm]
              exact le_trans (by rw [sub_add_cancel]) (enorm_add_le _ _)
        _ ≤ _ := by gcongr
    have hCne : C ≠ ⊤ := by rw [hCdef]; exact (hkermem x' R hR).2.ne
    have hC0 : Tendsto (fun n => C * eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul htend (Or.inr hCne))
    calc ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + C * eLpNorm (f - gg n) p volume) atTop :=
          le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hbd)
      _ = liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop :=
          ENNReal.liminf_add_of_right_tendsto_zero hC0 _
  refine ⟨C₀, fun g hg => ?_⟩
  -- Smooth compactly-supported `Lᵖ`-approximating sequence `gₙ → g`.
  have hp_top' : p ≠ ⊤ := hp_top
  choose gg hggc hggsmooth hggle using fun n : ℕ =>
    hg.exist_eLpNorm_sub_le hp_top' hp1' (ε := 1/(n+1)) (by positivity)
  have hggmem : ∀ n, MemLp (gg n) p volume := fun n =>
    (hggsmooth n).continuous.memLp_of_hasCompactSupport (hggc n)
  have hggBFS : ∀ n, BoundedFiniteSupport (gg n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hggsmooth n) (hggc n)
  have htend : Tendsto (fun n => eLpNorm (g - gg n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le _) hggle
  -- Per-point: `simpleNTO 0 g x ≤ liminf (simpleNTO 0 gₙ x)`.
  have hsup : ∀ x, simpleNontangentialOperator beurlingKernel 0 g x
      ≤ liminf (fun n => simpleNontangentialOperator beurlingKernel 0 (gg n) x) atTop := by
    intro x
    unfold simpleNontangentialOperator
    refine iSup_le (fun R => iSup_le (fun hR => iSup_le (fun x' => iSup_le (fun hx' => ?_))))
    refine le_trans (hLiminfPt R hR x' hg hggmem htend) ?_
    refine liminf_le_liminf (Eventually.of_forall (fun n => ?_))
    exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x' (le_iSup_of_le hx' (le_refl _))))
  -- BFS bound on each `gₙ`.
  have hggbd : ∀ n, eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume
      ≤ (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume := fun n => hBFS0 (gg n) (hggBFS n)
  -- `‖gₙ‖_p → ‖g‖_p`.
  have htnorm : Tendsto (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop
      (𝓝 ((C₀ : ℝ≥0∞) * eLpNorm g p volume)) := by
    have hgnorm : Tendsto (fun n => eLpNorm (gg n) p volume) atTop (𝓝 (eLpNorm g p volume)) := by
      set L := eLpNorm g p volume with hL
      set d := fun n => eLpNorm (g - gg n) p volume with hd
      have hupper : ∀ n, eLpNorm (gg n) p volume ≤ L + d n := by
        intro n
        have h : eLpNorm (gg n) p volume ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume := by
          calc eLpNorm (gg n) p volume = eLpNorm (g + (gg n - g)) p volume := by
                congr 1; funext y; simp
            _ ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume :=
                eLpNorm_add_le hg.aestronglyMeasurable ((hggmem n).sub hg).aestronglyMeasurable hp1'
        rw [hL, hd]
        rwa [show eLpNorm (gg n - g) p volume = eLpNorm (g - gg n) p volume from by
          rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
      have hlower : ∀ n, L - d n ≤ eLpNorm (gg n) p volume := by
        intro n
        rw [tsub_le_iff_right]
        calc L = eLpNorm ((gg n) + (g - gg n)) p volume := by rw [hL]; congr 1; funext y; simp
          _ ≤ eLpNorm (gg n) p volume + eLpNorm (g - gg n) p volume :=
              eLpNorm_add_le (hggmem n).aestronglyMeasurable
                (hg.sub (hggmem n)).aestronglyMeasurable hp1'
      have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
        simpa using tendsto_const_nhds.add htend
      have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
        simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend (Or.inr (by simp)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
    refine ENNReal.Tendsto.const_mul hgnorm ?_
    right; exact ENNReal.coe_ne_top
  -- Fatou on the `Lᵖ` lintegral.
  have hp_pos : (0:ℝ) < p.toReal := ENNReal.toReal_pos (by rintro rfl; exact absurd hp1 (by simp)) hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp)) hp_top]
  simp only [one_div]
  have hmono : ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
      ≤ liminf (fun n => ∫⁻ x,
        ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
    have hpowliminf : ∀ (u : ℕ → ℝ≥0∞),
        liminf (fun n => (u n) ^ p.toReal) atTop = (liminf u atTop) ^ p.toReal := by
      intro u
      have hmono' : Monotone (fun x : ℝ≥0∞ => x ^ p.toReal) :=
        fun a b h => ENNReal.rpow_le_rpow h hp_pos.le
      exact (hmono'.map_liminf_of_continuousAt u (ENNReal.continuous_rpow_const).continuousAt).symm
    have hle : ∀ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
        ≤ liminf (fun n =>
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
      intro x
      simp_rw [enorm_eq_self]
      rw [hpowliminf]
      gcongr
      exact hsup x
    refine le_trans (lintegral_mono hle) ?_
    refine lintegral_liminf_le (fun n => ?_)
    exact (lowerSemicontinuous_simpleNontangentialOperator.measurable).enorm.pow_const _
  calc (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal) ^ (p.toReal)⁻¹
      ≤ (liminf (fun n => ∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop)
            ^ (p.toReal)⁻¹ := by gcongr
    _ = liminf (fun n => (∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal)
            ^ (p.toReal)⁻¹) atTop := by
        have hmono2 : Monotone (fun x : ℝ≥0∞ => x ^ (p.toReal)⁻¹) :=
          fun a b h => ENNReal.rpow_le_rpow h (by positivity)
        exact hmono2.map_liminf_of_continuousAt _ (ENNReal.continuous_rpow_const).continuousAt
    _ = liminf (fun n => eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume)
          atTop := by
        congr 1; funext n
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp)) hp_top]
        simp only [one_div]
    _ ≤ liminf (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop :=
        liminf_le_liminf (Eventually.of_forall hggbd)
    _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := htnorm.liminf_eq

/-- **A.e. existence of the principal-value limit on `Lᵖ` for `p > 2`** (the
`p < 2` replication with the high maximal bound). -/
lemma czOperator_beurling_ae_tendsto_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, ∃ L, Filter.Tendsto (fun r => czOperator beurlingKernel r f z)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  have hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞) < 2) hp2
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  have hp_pos : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  -- Inline helper: oscillation control by the maximal operator (the `Lᵖ` version of
  -- `edist_czOperator_oscillation`, using `czOperator_beurling_sub_Lp`).
  have edist_osc : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {r₁ r₂ : ℝ}, 0 < r₁ → 0 < r₂ →
      edist (czOperator beurlingKernel r₁ f z) (czOperator beurlingKernel r₂ f z)
        ≤ edist (czOperator beurlingKernel r₁ ν z) (czOperator beurlingKernel r₂ ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    intro ν hν z r₁ r₂ hr₁ hr₂
    have hd1 : czOperator beurlingKernel r₁ f z - czOperator beurlingKernel r₁ ν z
        = czOperator beurlingKernel r₁ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₁ z hf hν).symm
    have hd2 : czOperator beurlingKernel r₂ f z - czOperator beurlingKernel r₂ ν z
        = czOperator beurlingKernel r₂ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₂ z hf hν).symm
    set Sf1 := czOperator beurlingKernel r₁ f z
    set Sf2 := czOperator beurlingKernel r₂ f z
    set Sn1 := czOperator beurlingKernel r₁ ν z
    set Sn2 := czOperator beurlingKernel r₂ ν z
    have hb1 : edist Sf1 Sn1 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_eq_enorm_sub, hd1]; exact enorm_czOperator_le_simpleNontangential hr₁ (f - ν) z
    have hb2 : edist Sn2 Sf2 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_comm, edist_eq_enorm_sub, hd2]
      exact enorm_czOperator_le_simpleNontangential hr₂ (f - ν) z
    calc edist Sf1 Sf2 ≤ edist Sf1 Sn1 + edist Sn1 Sn2 + edist Sn2 Sf2 := by
          refine le_trans (edist_triangle Sf1 Sn2 Sf2) ?_
          gcongr
          exact edist_triangle Sf1 Sn1 Sn2
      _ = edist Sn1 Sn2 + (edist Sf1 Sn1 + edist Sn2 Sf2) := by ring
      _ ≤ edist Sn1 Sn2 + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
          gcongr; rw [two_mul]; gcongr
  -- Inline helper: per-point Cauchy from smooth convergence + small maximal value
  -- (the `Lᵖ` version of `eventually_edist_lt_of_smooth_conv`).
  have edist_lt_of_conv : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {a : ℝ≥0∞}, 0 < a →
      (∃ L, Tendsto (fun r => czOperator beurlingKernel r ν z) (𝓝[>] (0:ℝ)) (𝓝 L)) →
      2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z < a / 2 →
      ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a := by
    intro ν hν z a ha hconv hsmall
    obtain ⟨L, hL⟩ := hconv
    have hνcauchy : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z) < a / 2 := by
      have hmap : Tendsto (fun q : ℝ × ℝ =>
          (czOperator beurlingKernel q.1 ν z, czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (L, L)) :=
        (hL.comp tendsto_fst).prodMk_nhds (hL.comp tendsto_snd)
      have ht : Tendsto (fun q : ℝ × ℝ =>
          edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (edist L L)) :=
        (continuous_edist.tendsto _).comp hmap
      rw [edist_self] at ht
      exact ht (Iio_mem_nhds (ENNReal.half_pos (ne_of_gt ha)))
    have hpos : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), 0 < q.1 ∧ 0 < q.2 := by
      rw [eventually_prod_iff]
      refine ⟨fun r => 0 < r, ?_, fun r => 0 < r, ?_, fun {r₁} h1 {r₂} h2 => ⟨h1, h2⟩⟩
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
    filter_upwards [hνcauchy, hpos] with q hq hqpos
    obtain ⟨hq1, hq2⟩ := hqpos
    calc edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        ≤ edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z :=
          edist_osc hν z hq1 hq2
      _ < a / 2 + a / 2 := ENNReal.add_lt_add hq hsmall
      _ = a := ENNReal.add_halves a
  -- The smooth `Lᵖ`-dense sequence (inline version of `exists_contDiff_seq_tendsto_L2`).
  choose g hgc hgsmooth hgle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le hp_top hp1' (ε := 1/(n+1)) (by positivity)
  have hg : ∀ n, MemLp (g n) p volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  have htend : Tendsto (fun n => eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le _) hgle
  -- The maximal-`Lᵖ` Chebyshev bound (inline version of `volume_simpleNontangential_ge_le`).
  obtain ⟨C, hC⟩ := exists_eLpNorm_simpleNontangential_beurling_Lp_high hp2 hp_top
  have vol_ge : ∀ {h : ℂ → ℂ}, MemLp h p volume → ∀ {a : ℝ≥0∞}, a ≠ 0 → a ≠ ⊤ →
      volume {z | a ≤ simpleNontangentialOperator beurlingKernel 0 h z}
        ≤ a⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm h p volume) ^ p.toReal := by
    intro h hh a hane hatop
    have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm volume hp_pos hp_top
      (f := simpleNontangentialOperator beurlingKernel 0 h)
      aestronglyMeasurable_simpleNontangentialOperator (ε := a) hane (fun heq => absurd heq hatop)
    refine le_trans hcheb (mul_le_mul' (le_refl (a⁻¹ ^ p.toReal)) ?_)
    exact ENNReal.rpow_le_rpow (hC h hh) (by positivity)
  -- Inline version of `volume_oscillation_set_eq_zero`.
  have osc_null : ∀ {a : ℝ≥0∞}, 0 < a → a ≠ ⊤ →
      volume {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a} = 0 := by
    intro a ha ha'
    set b := a / 4 with hbdef
    have hbpos : 0 < b := ENNReal.div_pos (ne_of_gt ha) (by norm_num)
    have hbne : b ≠ 0 := ne_of_gt hbpos
    have hbtop : b ≠ ⊤ := (ENNReal.div_lt_top ha' (by norm_num)).ne
    set B := {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a}
      with hBdef
    have hsubset : ∀ n, B ⊆ {z | b ≤ simpleNontangentialOperator beurlingKernel 0 (f - g n) z} := by
      intro n z hz
      by_contra hlt
      rw [Set.mem_setOf_eq, not_le] at hlt
      apply hz
      refine edist_lt_of_conv (hg n) z ha
        ⟨_, czOperator_beurling_tendsto_neg_pi ((hgsmooth n).of_le (by exact_mod_cast le_top))
          (hgc n) z⟩ ?_
      rw [hbdef] at hlt
      calc 2 * simpleNontangentialOperator beurlingKernel 0 (f - g n) z
          < 2 * (a / 4) := by gcongr; exact (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
        _ = a / 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm (2:ℝ≥0∞) a, mul_assoc]
            congr 1
            rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
              ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    have hmeas : ∀ n, volume B
        ≤ b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal :=
      fun n => le_trans (measure_mono (hsubset n)) (vol_ge (hf.sub (hg n)) hbne hbtop)
    have hto0 : Tendsto
        (fun n => b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.coe_ne_top)
      have h2 : Tendsto (fun n => ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal) atTop
          (𝓝 0) := by
        have h := (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp h1
        rw [show ((0:ℝ≥0∞) ^ p.toReal) = 0 by
          rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_pos hp_top)]] at h
        exact h
      have hbinv : b⁻¹ ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr hbne)
      have h3 := ENNReal.Tendsto.const_mul (a := b⁻¹ ^ p.toReal) h2 (Or.inr hbinv)
      rw [mul_zero] at h3
      exact h3
    exact le_antisymm (ge_of_tendsto hto0 (Eventually.of_forall hmeas)) (zero_le _)
  -- Assemble: union over the levels `1/(k+1)`, then `tendsto_of_cauchy_edist`.
  set Bk := fun k : ℕ => {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        < 1/((k:ℝ≥0∞)+1)} with hBk
  have hBknull : ∀ k, volume (Bk k) = 0 := by
    intro k
    apply osc_null
    · apply ENNReal.div_pos one_ne_zero
      exact (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩).ne
    · apply ENNReal.div_ne_top ENNReal.one_ne_top
      have hkp : (0:ℝ≥0∞) < (k:ℝ≥0∞)+1 := by positivity
      exact hkp.ne'
  have hunionnull : volume (⋃ k, Bk k) = 0 := measure_iUnion_null hBknull
  rw [ae_iff]
  refine measure_mono_null ?_ hunionnull
  intro z hz
  rw [Set.mem_setOf_eq] at hz
  rw [Set.mem_iUnion]
  by_contra hnot
  push_neg at hnot
  apply hz
  apply tendsto_of_cauchy_edist
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
  have hmem := hnot k
  simp only [hBk, Set.mem_setOf_eq, not_not] at hmem
  refine hmem.mono (fun q hq => lt_of_lt_of_le hq ?_)
  rw [one_div]
  calc ((k:ℝ≥0∞)+1)⁻¹ ≤ ((k:ℝ≥0∞))⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    _ ≤ ε := le_of_lt hk

/-- **A.e. convergence of the truncations to `-π · beurling f` on `Lᵖ`, `p > 2`.** -/
lemma czOperator_beurling_ae_tendsto_neg_pi_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, Filter.Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π : ℂ) * beurling f z)) := by
  filter_upwards [czOperator_beurling_ae_tendsto_Lp_high hp2 hp_top hf] with z hz
  obtain ⟨L, hL⟩ := hz
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z) = L := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z
        = czOperator beurlingKernel r f z := fun r => rfl
    simpa only [hcz] using hL
  have hb : beurling f z = -(1 / (π : ℂ)) * L := by rw [beurling, hlim]
  have hval : -(π:ℂ) * beurling f z = L := by
    rw [hb]; have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hval]; exact hL

/-- **`Lᵖ` bound for the Beurling transform, `p > 2`, by duality.** The high
truncation bound (`eLpNorm_czOperator_beurling_Lp_high`) passed to the limit by
Fatou using the a.e. convergence `czOperator_beurling_ae_tendsto_neg_pi_Lp_high`.
The constant is `(1/π) · beurlingTruncLpConst p'`. -/
lemma eLpNorm_beurling_Lp_le_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → ℂ, MemLp f p volume →
      eLpNorm (beurling f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  have hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞) < 2) hp2
  -- The conjugate exponent `p' = (1 - p⁻¹)⁻¹` and its `HolderConjugate` instance.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'_def
  have hpinv_le_one : p⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; exact hp1.le
  haveI hHC : ENNReal.HolderConjugate p p' := by
    rw [hp'_def, ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  -- The duality constant.
  set C : ℝ := 1 / π * (beurlingTruncLpConst p' : ℝ) with hCC_def
  refine ⟨C, by positivity, fun f hf => ?_⟩
  have hπpos : (0:ℝ) < 1 / π := by positivity
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- Convert the real constant to the Fatou form `ofReal(1/π) * beurlingTruncLpConst p'`.
  have hCconv : ENNReal.ofReal C
      = ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p' : ℝ≥0∞) := by
    rw [hCC_def, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
  rw [hCconv]
  set Cbound : ℝ≥0∞ :=
    (ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p' : ℝ≥0∞)) * eLpNorm f p volume
    with hCdef
  -- The scaled family `F r = (-(1/π)) • czOperator beurlingKernel r f`.
  set F : ℝ → ℂ → ℂ := fun r => (-(1 / π : ℂ)) • czOperator beurlingKernel r f with hFdef
  -- Bound `eLpNorm (F r) p ≤ Cbound` for `r > 0`.
  have hbound : ∀ᶠ r in 𝓝[>] (0:ℝ), eLpNorm (F r) p volume ≤ Cbound := by
    refine eventually_nhdsWithin_of_forall (fun r hr => ?_)
    rw [Set.mem_Ioi] at hr
    rw [hFdef, eLpNorm_const_smul]
    have hnorm : ‖(-(1 / π : ℂ))‖ₑ = ENNReal.ofReal (1 / π) := by
      rw [← ofReal_norm_eq_enorm, norm_neg]
      congr 1
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnorm, hCdef, mul_assoc]
    exact mul_le_mul' (le_refl _)
      (eLpNorm_czOperator_beurling_Lp_high (p' := p') hp2 hp_top hr hf)
  -- Measurability of each `F r`.
  have hmeas : ∀ r, AEStronglyMeasurable (F r) volume := by
    intro r
    rw [hFdef]
    exact (aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable).const_smul _
  -- a.e. tendsto: scale the a.e. limit by `-(1/π)`.
  have hae : ∀ᵐ z ∂volume, Tendsto (fun r => F r z) (𝓝[>] (0:ℝ)) (𝓝 (beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi_Lp_high hp2 hp_top hf] with z hz
    have hscaled := hz.const_mul (-(1 / π : ℂ))
    have heq : -(1 / π : ℂ) * (-(π : ℂ) * beurling f z) = beurling f z := by
      field_simp
    rw [heq] at hscaled
    have hFz : (fun r => F r z) = fun r => -(1 / π : ℂ) * czOperator beurlingKernel r f z := by
      funext r; rw [hFdef]; simp [Pi.smul_apply, smul_eq_mul]
    rw [hFz]; exact hscaled
  exact Lp.eLpNorm_le_of_ae_tendsto hbound hmeas hae

/-- **`Lᵖ` boundedness.** For `1 < p < ∞` the Beurling transform is bounded
`Lᵖ(ℂ) → Lᵖ(ℂ)` (Calderón–Zygmund). The range `1 < p < 2` is Marcinkiewicz
interpolation passed to the limit (`eLpNorm_beurling_Lp_le`), `p = 2` is the
`L²` isometry (`beurling_l2_isometry`), and `p > 2` is duality
(`eLpNorm_beurling_Lp_le_high`). -/
theorem beurling_lp_bound (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, IsCalderonZygmundBound beurling p C := by
  rcases lt_trichotomy p 2 with hlt | heq | hgt
  · -- `1 < p < 2`: the truncation bound passed to the limit.
    refine ⟨1 / π * (beurlingTruncLpConst p : ℝ), by positivity, fun f hf => ?_⟩
    have hconv : ENNReal.ofReal (1 / π * (beurlingTruncLpConst p : ℝ))
        = ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    rw [hconv]
    exact eLpNorm_beurling_Lp_le hp hlt hf
  · -- `p = 2`: the `L²` isometry.
    subst heq
    exact ⟨1, zero_le_one, fun f hf => by
      rw [beurling_l2_isometry hf, ENNReal.ofReal_one, one_mul]⟩
  · -- `p > 2`: duality.
    obtain ⟨C, hC0, hCb⟩ := eLpNorm_beurling_Lp_le_high hgt hp'
    exact ⟨C, hC0, hCb⟩

/-! ## Operator-norm continuity at `p = 2` (Riesz–Thorin)

The Beurling transform is an `L²` isometry and `Lᵖ`-bounded for every `1 < p < ∞`,
so by Riesz–Thorin complex interpolation (`eLpNorm_interpolation_of_hasStrongType`)
its `Lᵖ` operator norm tends to `1` as `p → 2`. The a.e.-linearity inputs to
interpolation are recorded first. -/

/-- **A.e. convergence of the truncations to `-π · beurling f` on `L² ∪ L⁴`**, a
uniform restatement of the `L²` (`czOperator_beurling_ae_tendsto_neg_pi`) and
`p > 2` (`..._Lp_high`) results — the form consumed by Riesz–Thorin interpolation
(endpoints `p₀ = 2`, `p₁ = 4`). -/
lemma beurling_ae_tendsto_neg_pi_two_four {f : ℂ → ℂ}
    (hf : MemLp f 2 volume ∨ MemLp f 4 volume) :
    ∀ᵐ z ∂volume, Filter.Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π : ℂ) * beurling f z)) := by
  rcases hf with hf | hf
  · exact czOperator_beurling_ae_tendsto_neg_pi hf
  · exact czOperator_beurling_ae_tendsto_neg_pi_Lp_high (by norm_num) (by norm_num) hf

/-- Integrability of the truncated Beurling integrand against an `L² ∪ L⁴`
function (`L²` Cauchy–Schwarz, or Hölder with the kernel section in `L^{4/3}`). -/
lemma integrableOn_beurling_two_four {r : ℝ} (hr : 0 < r) (x : ℂ) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume ∨ MemLp f 4 volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  rcases hf with hf | hf
  · exact integrableOn_beurlingKernel_mul hr x hf
  · haveI : ENNReal.HolderConjugate (4 : ℝ≥0∞) ((1 - (4 : ℝ≥0∞)⁻¹)⁻¹) :=
      ENNReal.holderConjugate_iff.mpr (by
        rw [inv_inv]; exact add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr (by norm_num)))
    exact integrableOn_beurlingKernel_mul_Lp (p' := (1 - (4 : ℝ≥0∞)⁻¹)⁻¹) hr x
      (by norm_num) (by norm_num) hf

/-- **`beurling` is additive a.e. on `L² ∪ L⁴`** (the truncations are additive and
the a.e. limits add; the limit pins the defining `limUnder` even though `f + g`
need not itself lie in `L² ∪ L⁴`). -/
lemma beurling_add_ae {f g : ℂ → ℂ} (hf : MemLp f 2 volume ∨ MemLp f 4 volume)
    (hg : MemLp g 2 volume ∨ MemLp g 4 volume) :
    beurling (f + g) =ᵐ[volume] beurling f + beurling g := by
  filter_upwards [beurling_ae_tendsto_neg_pi_two_four hf,
    beurling_ae_tendsto_neg_pi_two_four hg] with z hzf hzg
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hconv : Tendsto (fun r => czOperator beurlingKernel r (f + g) z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π:ℂ) * beurling f z + -(π:ℂ) * beurling g z)) := by
    refine (hzf.add hzg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (czOperator_beurling_add (integrableOn_beurling_two_four hr z hf)
      (integrableOn_beurling_two_four hr z hg)).symm
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z)
      = -(π:ℂ) * beurling f z + -(π:ℂ) * beurling g z := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z
        = czOperator beurlingKernel r (f + g) z := fun r => rfl
    simpa only [hcz] using hconv
  have hbfg : beurling (f + g) z = -(1 / (π:ℂ)) * limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z) := rfl
  have : beurling (f + g) z = beurling f z + beurling g z := by
    rw [hbfg, hlim]; field_simp; ring
  simpa [Pi.add_apply] using this

/-- **`beurling` is homogeneous a.e. on `L² ∪ L⁴`.** -/
lemma beurling_smul_ae (c : ℂ) {f : ℂ → ℂ} (hf : MemLp f 2 volume ∨ MemLp f 4 volume) :
    beurling (c • f) =ᵐ[volume] c • beurling f := by
  filter_upwards [beurling_ae_tendsto_neg_pi_two_four hf] with z hzf
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hconv : Tendsto (fun r => czOperator beurlingKernel r (c • f) z) (𝓝[>] (0:ℝ))
      (𝓝 (c * (-(π:ℂ) * beurling f z))) := by
    refine (hzf.const_mul c).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r _
    exact (czOperator_beurling_const_smul c).symm
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (c • f) z)
      = c * (-(π:ℂ) * beurling f z) := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (c • f) z
        = czOperator beurlingKernel r (c • f) z := fun r => rfl
    simpa only [hcz] using hconv
  have hbcf : beurling (c • f) z = -(1 / (π:ℂ)) * limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (c • f) z) := rfl
  have : beurling (c • f) z = c * beurling f z := by
    rw [hbcf, hlim]; field_simp
  simpa [Pi.smul_apply, smul_eq_mul] using this

/-- `beurling f` is a.e. strongly measurable for `f ∈ Lᵖ`, `p > 2`. -/
lemma aestronglyMeasurable_beurling_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    AEStronglyMeasurable (beurling f) volume := by
  set r : ℕ → ℝ := fun n => 1/(n+1:ℝ) with hr
  have hrpos : ∀ n, 0 < r n := fun n => by rw [hr]; positivity
  have hrto : Tendsto r atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop), ?_⟩
    filter_upwards with n; simp only [Set.mem_Ioi, hr]; positivity
  have hae : ∀ᵐ z ∂volume, Tendsto (fun n => czOperator beurlingKernel (r n) f z) atTop
      (𝓝 (-(π:ℂ) * beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi_Lp_high hp2 hp_top hf] with z hz
    exact hz.comp hrto
  have hmeas : AEStronglyMeasurable (fun z => -(π:ℂ) * beurling f z) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable) hae
  have heq : beurling f = fun z => (-(1/(π:ℂ))) * (-(π:ℂ) * beurling f z) := by
    funext z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [heq]
  exact hmeas.const_mul _

/-- **Operator-norm continuity at `p = 2`.** The `Lᵖ` bound constant can be taken
arbitrarily close to `1` for `p` near `2` — the qualitative input the Neumann
series of the measurable Riemann mapping theorem consumes. Riesz–Thorin
interpolation between the `L²` isometry (`beurling_l2_isometry`, constant `1`) and
the `L⁴` bound (`beurling_lp_bound`, constant `C₄`) gives `‖T‖_{p→p} ≤ C₄^θ` at
`p = 4/(2-θ) ∈ (2,4)`; choosing `θ` small makes `C₄^θ < 1 + ε`. -/
theorem beurling_opNorm_continuous (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ≥0∞, 2 < p ∧ p ≠ ⊤ ∧ ∃ C : ℝ, C < 1 + ε ∧ IsCalderonZygmundBound beurling p C := by
  -- The `L⁴` bound `‖beurling f‖₄ ≤ ofReal C₄ · ‖f‖₄`.
  obtain ⟨Cq, hCq0, hCqb⟩ := beurling_lp_bound (p := 4) (by norm_num) (by norm_num)
  set M₁ : ℝ≥0 := Cq.toNNReal with hM₁
  have hM₁coe : (M₁ : ℝ) = Cq := Real.coe_toNNReal Cq hCq0
  -- Choose `θ ∈ (0,1)` with `Cq ^ θ < 1 + ε`.
  obtain ⟨θ, hθ0, hθ1, hθlt⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ Cq ^ θ < 1 + ε := by
    by_cases hCq1 : Cq ≤ 1
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      calc Cq ^ (1 / 2 : ℝ) ≤ (1 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hCq0 hCq1 (by norm_num)
        _ = 1 := Real.one_rpow _
        _ < 1 + ε := by linarith
    · push_neg at hCq1
      have hlogpos : 0 < Real.log Cq := Real.log_pos hCq1
      have hlog1ε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
      refine ⟨min (1 / 2) (Real.log (1 + ε) / (2 * Real.log Cq)),
        lt_min (by norm_num) (by positivity),
        lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
      rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < Cq)]
      calc Real.exp (Real.log Cq * min (1 / 2) (Real.log (1 + ε) / (2 * Real.log Cq)))
          < Real.exp (Real.log (1 + ε)) := by
            apply Real.exp_lt_exp.mpr
            calc Real.log Cq * min (1 / 2) (Real.log (1 + ε) / (2 * Real.log Cq))
                ≤ Real.log Cq * (Real.log (1 + ε) / (2 * Real.log Cq)) :=
                  mul_le_mul_of_nonneg_left (min_le_right _ _) hlogpos.le
              _ = Real.log (1 + ε) / 2 := by field_simp
              _ < Real.log (1 + ε) := by linarith
        _ = 1 + ε := Real.exp_log (by linarith)
  -- The intermediate exponent `p = 4/(2-θ) ∈ (2,4)`.
  have h2θpos : (0 : ℝ) < 2 - θ := by linarith
  have hppos : (0 : ℝ) < 4 / (2 - θ) := by positivity
  set p : ℝ≥0∞ := ENNReal.ofReal (4 / (2 - θ)) with hpdef
  have hp2 : (2 : ℝ≥0∞) < p := by
    rw [hpdef, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ENNReal.ofReal_lt_ofReal_iff hppos, lt_div_iff₀ h2θpos]; linarith
  have hptop : p ≠ ⊤ := by rw [hpdef]; exact ENNReal.ofReal_ne_top
  -- The interpolation exponent relation `1/p = (1-θ)/2 + θ/4`.
  have hprel : p⁻¹ = ENNReal.ofReal (1 - θ) * (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * (4 : ℝ≥0∞)⁻¹ := by
    have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
        show ENNReal.ofReal 2 = 2 by simp, one_div]
    have h4 : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
        show ENNReal.ofReal 4 = 4 by simp, one_div]
    rw [hpdef, ← ENNReal.ofReal_inv_of_pos hppos, h2, h4,
      ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - θ),
      ← ENNReal.ofReal_mul hθ0.le,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) (by norm_num))
        (mul_nonneg hθ0.le (by norm_num))]
    congr 1
    field_simp
    ring
  refine ⟨p, hp2, hptop, Cq ^ θ, hθlt, by positivity, fun f hf => ?_⟩
  -- Apply Riesz–Thorin (`p₀ = 2`, `M₀ = 1`; `p₁ = 4`, `M₁ = C₄`).
  have hinterp := eLpNorm_interpolation_of_hasStrongType
    (T := beurling) (p₀ := 2) (p₁ := 4) (M₀ := 1) (M₁ := M₁) (θ := θ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨hθ0, hθ1⟩ hprel
    (fun s hs => aestronglyMeasurable_beurling_Lp_high hp2 hptop hs)
    (fun s t hs ht => beurling_add_ae hs ht)
    (fun c s hs => beurling_smul_ae c hs)
    (fun s hs => by rw [beurling_l2_isometry hs]; simp)
    (fun s hs => hCqb s hs)
    hf
  refine le_trans hinterp (le_of_eq ?_)
  congr 1
  rw [NNReal.one_rpow, one_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_rpow, hM₁coe]

end RiemannDynamics

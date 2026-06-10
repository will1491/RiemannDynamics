/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.Gamma2FundamentalDomain
import RiemannDynamics.Hyperbolic.WindingNumber
import RiemannDynamics.Hyperbolic.PathWinding

/-!
# Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`

The level-2 modular function `λ` is a holomorphic covering map of the
triply-punctured plane by the upper half-plane. The proof factors
through four classical statements:

* **Freeness mod `±I`** (`gamma_two_fixed_point_implies_pm_one`):
  any `γ ∈ Γ(2)` with a fixed point in `ℍ` is `±I`.
* **Proper discontinuity** (`gamma_two_properlyDiscontinuousSMul`):
  `Γ(2)` acts properly discontinuously on `ℍ`.
* **Non-vanishing derivative** (`modularLambdaH_deriv_ne_zero_on_upperHalf`):
  `λ' ≠ 0` on `ℍ`.
* **Orbit identification** (`modularLambdaH_eq_iff_gamma2_orbit`):
  `λ(τ₁) = λ(τ₂) ↔ ∃ γ ∈ Γ(2), γ • τ₁ = τ₂`.

The first two pillars depend only on the `SL₂(ℤ)`-action and live in
`Hyperbolic/ModularFunction.lean`. The last two pillars use the Step-D
biholomorphism `λ : F^o → {Im w > 0}`
(`modularLambdaH_image_fundamentalDomainInterior`) and the
"half-fundamental-domain" property of `F`, both established in
`Hyperbolic/Gamma2FundamentalDomain.lean`.

`F` has hyperbolic area `π` (an ideal triangle with vertices
`0, 1, ∞`), half the `Γ(2)`-covolume `2π`. So `F` is a *half*
fundamental domain: the upper-`λ`-image branch `λ : F^o → {Im w > 0}`
(Step D) is a biholomorphism, while the conjugation symmetry
`λ(-conj τ) = conj(λ τ)` produces the lower-`λ`-image branch on the
reflected half.

Pillars 3 and 4 consequently split into three cases each, separated
by the sign of `Im(λ τ)`. The `Im(λ) > 0` branch reduces to `F` via
the half-FD property. The `Im(λ) < 0` branch is handled by the
conjugation argument: for Pillar 4 by a direct matrix conjugation
turning `γ = ⟨⟨a, b⟩, ⟨c, d⟩⟩` into `γ' = ⟨⟨a, -b⟩, ⟨-c, d⟩⟩`, also
in `Γ(2)`. The `Im(λ) = 0` boundary branch reduces to the closed
boundary arcs of `F` and is handled by Schwarz reflection (still an
architectural sub-lemma).
-/

namespace RiemannDynamics

open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## Half-fundamental-domain infrastructure (sub-lemmas) -/

/-- The reflected half-fundamental domain `F^σ := { τ : -1 ≤ Re τ ≤ 0,
|2τ + 1| ≥ 1, Im τ > 0 }`. This is `-conj(F)`: the conjugation
`τ ↦ -conj τ` maps `F` (closed) to `F^σ` (closed) homeomorphically.
Together with `F`, `F^σ` tessellates a strict `Γ(2)`-fundamental
domain of `ℍ` with hyperbolic covolume `2π`. The image of `F^σ`
under `λ` is the closed lower half of `ℂ ∖ {0, 1}` (by
`modularLambdaH_conj_symmetry`). -/
def Gamma2FundamentalDomainReflected : Set ℂ :=
  { τ : ℂ | 0 < τ.im ∧ -1 ≤ τ.re ∧ τ.re ≤ 0 ∧ 1 ≤ ‖2 * τ + 1‖ }

/-! ### Tiles of the standard fundamental domain inside `F ∪ F^σ`

For `z` in the standard `SL(2, ℤ)` fundamental domain `𝒟`
(`1 ≤ |z|²`, `|Re z| ≤ 1/2`, `Im z > 0`), the twelve lemmas below
place an explicit Möbius image of `z` into the half-fundamental
domain `F` or its reflection `F^σ`, with the image chosen by the
sign of `Re z`. Together they cover the six classes of
`SL(2, ℤ/2) ≅ S₃`: the identity class (`z` itself), `S` (`−1/z`),
`T` (`z ± 1`), the lower-unipotent class (`z/(z+1)`, `z/(1−z)`),
`ST` (`−1/(z ± 1)`), and `TS` (`±1 − 1/z`). Each membership reduces
to a `normSq` inequality of the form `‖az + b‖² − ‖cz + d‖² ≥ 0`
valid on `𝒟`. -/

/-- **Identity tile, right half.** `z ∈ 𝒟` with `Re z ≥ 0` lies in `F`:
`‖2z − 1‖² = 4|z|² − 4 Re z + 1 ≥ 4 − 2 + 1 = 3 ≥ 1`. -/
theorem gamma2_tile_id_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : z ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hn := hz_norm
  rw [Complex.normSq_apply] at hn
  simp only [Gamma2FundamentalDomain, Set.mem_setOf_eq]
  refine ⟨hz_im, h_sign, by linarith, ?_⟩
  have hq : (1 : ℝ) ≤ Complex.normSq (2 * z - 1) := by
    rw [Complex.normSq_apply]
    have h1 : (2 * z - 1).re = 2 * z.re - 1 := by simp
    have h2 : (2 * z - 1).im = 2 * z.im := by simp
    rw [h1, h2]
    nlinarith
  have hsq := Complex.sq_norm (2 * z - 1)
  nlinarith [norm_nonneg (2 * z - 1)]

/-- **Identity tile, left half.** `z ∈ 𝒟` with `Re z ≤ 0` lies in `F^σ`:
`‖2z + 1‖² = 4|z|² + 4 Re z + 1 ≥ 4 − 2 + 1 = 3 ≥ 1`. -/
theorem gamma2_tile_id_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : z ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hn := hz_norm
  rw [Complex.normSq_apply] at hn
  simp only [Gamma2FundamentalDomainReflected, Set.mem_setOf_eq]
  refine ⟨hz_im, by linarith, h_sign, ?_⟩
  have hq : (1 : ℝ) ≤ Complex.normSq (2 * z + 1) := by
    rw [Complex.normSq_apply]
    have h1 : (2 * z + 1).re = 2 * z.re + 1 := by simp
    have h2 : (2 * z + 1).im = 2 * z.im := by simp
    rw [h1, h2]
    nlinarith
  have hsq := Complex.sq_norm (2 * z + 1)
  nlinarith [norm_nonneg (2 * z + 1)]

/-- **`S`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the image
`−1/z` lies in `F`: `Re(−1/z) = −Re z/|z|² ∈ [0, 1/2]`, and
`‖2(−1/z) − 1‖ = ‖z + 2‖/‖z‖ ≥ 1` since `‖z + 2‖² − ‖z‖² = 4 Re z + 4 ≥ 2`. -/
theorem gamma2_tile_S_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : -1 / z ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h] at hz_im
    simp at hz_im
  have h_nsq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have him : (-1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.div_im]
    simp
    ring
  have hre : (-1 / z).re = -z.re / Complex.normSq z := by
    rw [Complex.div_re]
    simp [neg_div]
  simp only [Gamma2FundamentalDomain, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]
    exact div_pos hz_im h_nsq_pos
  · rw [hre]
    exact div_nonneg (by linarith) h_nsq_pos.le
  · rw [hre, div_le_one h_nsq_pos]
    linarith
  · have key : 2 * (-1 / z) - 1 = -(z + 2) / z := by
      field_simp
      ring
    have hq : (1 : ℝ) ≤ Complex.normSq (2 * (-1 / z) - 1) := by
      rw [key, Complex.normSq_div, Complex.normSq_neg, le_div_iff₀ h_nsq_pos, one_mul]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      have h1 : (z + 2).re = z.re + 2 := by simp
      have h2 : (z + 2).im = z.im := by simp
      rw [h1, h2]
      nlinarith
    have hsq := Complex.sq_norm (2 * (-1 / z) - 1)
    nlinarith [norm_nonneg (2 * (-1 / z) - 1)]

/-- **`S`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the image
`−1/z` lies in `F^σ`: mirror of `gamma2_tile_S_F` using
`‖z − 2‖² − ‖z‖² = −4 Re z + 4 ≥ 2`. -/
theorem gamma2_tile_S_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : -1 / z ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h] at hz_im
    simp at hz_im
  have h_nsq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have him : (-1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.div_im]
    simp
    ring
  have hre : (-1 / z).re = -z.re / Complex.normSq z := by
    rw [Complex.div_re]
    simp [neg_div]
  simp only [Gamma2FundamentalDomainReflected, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]
    exact div_pos hz_im h_nsq_pos
  · rw [hre, neg_div]
    have h1 : z.re / Complex.normSq z ≤ 1 := by
      rw [div_le_one h_nsq_pos]
      linarith
    linarith
  · rw [hre]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h_nsq_pos.le
  · have key : 2 * (-1 / z) + 1 = (z - 2) / z := by
      field_simp
      ring
    have hq : (1 : ℝ) ≤ Complex.normSq (2 * (-1 / z) + 1) := by
      rw [key, Complex.normSq_div, le_div_iff₀ h_nsq_pos, one_mul]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      have h1 : (z - 2).re = z.re - 2 := by simp
      have h2 : (z - 2).im = z.im := by simp
      rw [h1, h2]
      nlinarith
    have hsq := Complex.sq_norm (2 * (-1 / z) + 1)
    nlinarith [norm_nonneg (2 * (-1 / z) + 1)]

/-- **`T`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the translate
`z + 1` lies in `F`: `Re(z + 1) ∈ [1/2, 1]` and
`‖2(z + 1) − 1‖² = ‖2z + 1‖² = 4|z|² + 4 Re z + 1 ≥ 3`. -/
theorem gamma2_tile_T_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : z + 1 ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have him : (z + 1).im = z.im := by simp
  have hre : (z + 1).re = z.re + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact hz_im
  · rw [hre]; linarith
  · rw [hre]; linarith
  · have hsq : (1 : ℝ) ≤ Complex.normSq (2 * (z + 1) - 1) := by
      have hval : Complex.normSq (2 * (z + 1) - 1)
          = 4 * Complex.normSq z + 4 * z.re + 1 := by
        simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
        ring
      rw [hval]; nlinarith
    have hsq' : (1 : ℝ) ≤ ‖2 * (z + 1) - 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact hsq
    nlinarith [norm_nonneg (2 * (z + 1) - 1)]

/-- **`T`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the translate
`z − 1` lies in `F^σ`: mirror of `gamma2_tile_T_F`. -/
theorem gamma2_tile_T_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : z - 1 ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have him : (z - 1).im = z.im := by simp
  have hre : (z - 1).re = z.re - 1 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact hz_im
  · rw [hre]; linarith
  · rw [hre]; linarith
  · have hsq : (1 : ℝ) ≤ Complex.normSq (2 * (z - 1) + 1) := by
      have hval : Complex.normSq (2 * (z - 1) + 1)
          = 4 * Complex.normSq z - 4 * z.re + 1 := by
        simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
        ring
      rw [hval]; nlinarith
    have hsq' : (1 : ℝ) ≤ ‖2 * (z - 1) + 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact hsq
    nlinarith [norm_nonneg (2 * (z - 1) + 1)]

/-- **Lower-unipotent tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`,
the image `z/(z + 1)` lies in `F`: `Im(z/(z+1)) = Im z/‖z+1‖² > 0`,
`Re(z/(z+1)) = (|z|² + Re z)/‖z+1‖² ∈ [0, 1]`, and
`‖2 z/(z+1) − 1‖ = ‖z − 1‖/‖z + 1‖ ≥ 1` iff `Re z ≤ 0`. -/
theorem gamma2_tile_L_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : z / (z + 1) ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have h' : (z + 1).im = 0 := by rw [h]; simp
    simp only [Complex.add_im, Complex.one_im, add_zero] at h'
    linarith
  have hN : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hz1
  have h1re : (z + 1).re = z.re + 1 := by simp
  have h1im : (z + 1).im = z.im := by simp
  have hN_eq : Complex.normSq (z + 1) = Complex.normSq z + 2 * z.re + 1 := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have him : (z / (z + 1)).im = z.im / Complex.normSq (z + 1) := by
    rw [Complex.div_im, h1re, h1im]
    ring
  have hre : (z / (z + 1)).re
      = (Complex.normSq z + z.re) / Complex.normSq (z + 1) := by
    rw [Complex.div_re, h1re, h1im, Complex.normSq_apply z]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact div_pos hz_im hN
  · rw [hre]
    apply div_nonneg _ hN.le
    linarith
  · rw [hre, div_le_one hN]
    linarith
  · have hquot : 2 * (z / (z + 1)) - 1 = (z - 1) / (z + 1) := by
      field_simp
      ring
    rw [hquot, Complex.norm_div, one_le_div₀ (norm_pos_iff.mpr hz1)]
    have hsq : Complex.normSq (z + 1) ≤ Complex.normSq (z - 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (z + 1), norm_nonneg (z - 1)]

/-- **Lower-unipotent tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`,
the image `z/(1 − z)` lies in `F^σ`: `Re(z/(1−z)) = (Re z − |z|²)/‖1−z‖²
∈ [−1, 0]` and `‖2 z/(1−z) + 1‖ = ‖z + 1‖/‖1 − z‖ ≥ 1` iff `Re z ≥ 0`. -/
theorem gamma2_tile_L_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : z / (1 - z) ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have h' : ((1 : ℂ) - z).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.one_im, zero_sub, neg_eq_zero] at h'
    linarith
  have hN : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hz1
  have h1re : ((1 : ℂ) - z).re = 1 - z.re := by simp
  have h1im : ((1 : ℂ) - z).im = -z.im := by simp
  have hN_eq : Complex.normSq (1 - z) = Complex.normSq z - 2 * z.re + 1 := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have him : (z / (1 - z)).im = z.im / Complex.normSq (1 - z) := by
    rw [Complex.div_im, h1re, h1im]
    ring
  have hre : (z / (1 - z)).re
      = (z.re - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [Complex.div_re, h1re, h1im, Complex.normSq_apply z]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact div_pos hz_im hN
  · rw [hre, le_div_iff₀ hN]
    nlinarith
  · rw [hre]
    apply div_nonpos_of_nonpos_of_nonneg _ hN.le
    linarith
  · have hquot : 2 * (z / (1 - z)) + 1 = (z + 1) / (1 - z) := by
      field_simp
      ring
    rw [hquot, Complex.norm_div, one_le_div₀ (norm_pos_iff.mpr hz1)]
    have hsq : Complex.normSq (1 - z) ≤ Complex.normSq (z + 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (1 - z), norm_nonneg (z + 1)]

/-- **`ST`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the image
`−1/(z + 1)` lies in `F^σ`: `Re(−1/(z+1)) = −(Re z + 1)/‖z+1‖² ∈ [−1, 0]`
and `‖2(−1/(z+1)) + 1‖ = ‖z − 1‖/‖z + 1‖ ≥ 1` iff `Re z ≤ 0`. -/
theorem gamma2_tile_ST_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : -1 / (z + 1) ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hd_ne : z + 1 ≠ 0 := by
    intro h
    have h' : (z + 1).im = 0 := by rw [h, Complex.zero_im]
    rw [Complex.add_im, Complex.one_im, add_zero] at h'
    linarith
  have hd_pos : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hd_ne
  have hd_eq : Complex.normSq (z + 1) = Complex.normSq z + 2 * z.re + 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, add_zero]
    ring
  have hre_w : (-1 / (z + 1)).re = -(z.re + 1) / Complex.normSq (z + 1) := by
    rw [Complex.div_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, neg_zero,
      add_zero, zero_mul, zero_div]
    ring
  have him_w : (-1 / (z + 1)).im = z.im / Complex.normSq (z + 1) := by
    rw [Complex.div_im]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, neg_zero, add_zero, zero_mul, zero_div]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hd_pos
  · rw [hre_w, le_div_iff₀ hd_pos]
    nlinarith [hd_eq]
  · rw [hre_w, div_le_iff₀ hd_pos]
    nlinarith
  · have key : 2 * (-1 / (z + 1)) + 1 = (z - 1) / (z + 1) := by
      field_simp
      ring
    have h1 : Complex.normSq (z + 1) ≤ Complex.normSq (z - 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero]
      nlinarith
    have h2 : ‖z + 1‖ ≤ ‖z - 1‖ := by
      have e1 := Complex.normSq_eq_norm_sq (z + 1)
      have e2 := Complex.normSq_eq_norm_sq (z - 1)
      nlinarith [norm_nonneg (z + 1), norm_nonneg (z - 1)]
    rw [key, norm_div, le_div_iff₀ (norm_pos_iff.mpr hd_ne), one_mul]
    exact h2

/-- **`ST`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the image
`−1/(z − 1)` lies in `F`: `Re(−1/(z−1)) = (1 − Re z)/‖z−1‖² ∈ [0, 1]`
and `‖2(−1/(z−1)) − 1‖ = ‖z + 1‖/‖z − 1‖ ≥ 1` iff `Re z ≥ 0`. -/
theorem gamma2_tile_ST_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : -1 / (z - 1) ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hd_ne : z - 1 ≠ 0 := by
    intro h
    have h' : (z - 1).im = 0 := by rw [h, Complex.zero_im]
    rw [Complex.sub_im, Complex.one_im, sub_zero] at h'
    linarith
  have hd_pos : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.mpr hd_ne
  have hd_eq : Complex.normSq (z - 1) = Complex.normSq z - 2 * z.re + 1 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero]
    ring
  have hre_w : (-1 / (z - 1)).re = (1 - z.re) / Complex.normSq (z - 1) := by
    rw [Complex.div_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, neg_zero, sub_zero, zero_mul, zero_div]
    ring
  have him_w : (-1 / (z - 1)).im = z.im / Complex.normSq (z - 1) := by
    rw [Complex.div_im]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, neg_zero, sub_zero, zero_mul, zero_div]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hd_pos
  · rw [hre_w, le_div_iff₀ hd_pos]
    nlinarith
  · rw [hre_w, div_le_iff₀ hd_pos]
    nlinarith [hd_eq]
  · have key : 2 * (-1 / (z - 1)) - 1 = -(z + 1) / (z - 1) := by
      field_simp
      ring
    have h1 : Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero]
      nlinarith
    have h2 : ‖z - 1‖ ≤ ‖z + 1‖ := by
      have e1 := Complex.normSq_eq_norm_sq (z + 1)
      have e2 := Complex.normSq_eq_norm_sq (z - 1)
      nlinarith [norm_nonneg (z + 1), norm_nonneg (z - 1)]
    rw [key, norm_div, norm_neg, le_div_iff₀ (norm_pos_iff.mpr hd_ne), one_mul]
    exact h2

/-- **`TS`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the image
`1 − 1/z` lies in `F`: `Re(1 − 1/z) = 1 − Re z/|z|² ∈ [1/2, 1]` and
`‖2(1 − 1/z) − 1‖ = ‖z − 2‖/‖z‖ ≥ 1` since `‖z − 2‖² − ‖z‖² = 4 − 4 Re z ≥ 2`. -/
theorem gamma2_tile_TS_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : 1 - 1 / z ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz_im
    linarith
  have hN_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have hN_ne : Complex.normSq z ≠ 0 := ne_of_gt hN_pos
  have hre_w : (1 - 1 / z).re = (Complex.normSq z - z.re) / Complex.normSq z := by
    rw [Complex.sub_re, Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, add_zero]
    field_simp
  have him_w : (1 - 1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.sub_im, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, zero_sub]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hN_pos
  · rw [hre_w, le_div_iff₀ hN_pos]
    nlinarith
  · rw [hre_w, div_le_iff₀ hN_pos]
    nlinarith
  · have key : 2 * (1 - 1 / z) - 1 = (z - 2) / z := by
      field_simp
      ring
    have h1 : Complex.normSq z ≤ Complex.normSq (z - 2) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.re_ofNat,
        Complex.im_ofNat, sub_zero]
      nlinarith
    have h2 : ‖z‖ ≤ ‖z - 2‖ := by
      have e1 := Complex.normSq_eq_norm_sq z
      have e2 := Complex.normSq_eq_norm_sq (z - 2)
      nlinarith [norm_nonneg z, norm_nonneg (z - 2)]
    rw [key, norm_div, le_div_iff₀ (norm_pos_iff.mpr hz_ne), one_mul]
    exact h2

/-- **`TS`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the image
`−1 − 1/z` lies in `F^σ`: `Re(−1 − 1/z) = −1 − Re z/|z|² ∈ [−1, −1/2]`
and `‖2(−1 − 1/z) + 1‖ = ‖z + 2‖/‖z‖ ≥ 1` since
`‖z + 2‖² − ‖z‖² = 4 Re z + 4 ≥ 2`. -/
theorem gamma2_tile_TS_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : -1 - 1 / z ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz_im
    linarith
  have hN_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have hN_ne : Complex.normSq z ≠ 0 := ne_of_gt hN_pos
  have hre_w : (-1 - 1 / z).re = -(Complex.normSq z + z.re) / Complex.normSq z := by
    rw [Complex.sub_re, Complex.neg_re, Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, add_zero]
    field_simp
    ring
  have him_w : (-1 - 1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.sub_im, Complex.neg_im, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, neg_zero,
      zero_sub]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hN_pos
  · rw [hre_w, le_div_iff₀ hN_pos]
    nlinarith
  · rw [hre_w, div_le_iff₀ hN_pos]
    nlinarith
  · have key : 2 * (-1 - 1 / z) + 1 = -(z + 2) / z := by
      field_simp
      ring
    have h1 : Complex.normSq z ≤ Complex.normSq (z + 2) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.re_ofNat,
        Complex.im_ofNat, add_zero]
      nlinarith
    have h2 : ‖z‖ ≤ ‖z + 2‖ := by
      have e1 := Complex.normSq_eq_norm_sq z
      have e2 := Complex.normSq_eq_norm_sq (z + 2)
      nlinarith [norm_nonneg z, norm_nonneg (z + 2)]
    rw [key, norm_div, norm_neg, le_div_iff₀ (norm_pos_iff.mpr hz_ne), one_mul]
    exact h2

/-- **Coercion formula for the `SL(2, ℤ)` action on `ℍ`.** The complex
coordinate of `g • z` is the Möbius image `(az + b)/(cz + d)` with the
integer entries of `g` cast into `ℂ`. Unfolds
`UpperHalfPlane.specialLinearGroup_apply` through the cast chain
`ℤ → ℝ → ℂ`. -/
theorem sl2z_smul_coe (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : UpperHalfPlane) :
    ((g • z : UpperHalfPlane) : ℂ) =
      ((g 0 0 : ℤ) * (z : ℂ) + (g 0 1 : ℤ)) /
        ((g 1 0 : ℤ) * (z : ℂ) + (g 1 1 : ℤ)) := by
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp [eq_intCast, Complex.ofReal_intCast]

/-- **Existence of a `Γ(2)`-translate in `F ∪ F^σ`.** For every
`τ ∈ ℍ`, there is `γ ∈ Γ(2)` such that `γ • τ` lies in either the
half-fundamental domain `F` or its reflection `F^σ`. This is the
classical strict fundamental-domain property of `Γ(2)`: place the
orbit into the standard `SL(2, ℤ)` fundamental domain `𝒟` via the
Mathlib reduction `ModularGroup.exists_smul_mem_fd`, say `g • τ ∈ 𝒟`;
the mod-2 reduction of `g⁻¹` is one of the six elements of
`SL(2, ℤ/2) ≅ S₃`, and for each class an explicit correction matrix
`h ≡ g⁻¹ (mod 2)` — chosen between two candidates by the sign of
`Re (g • τ)` — sends `g • τ` into `F ∪ F^σ` by the twelve tile
lemmas above. Then `γ := h * g ∈ Γ(2)` and
`γ • τ = h • (g • τ) ∈ F ∪ F^σ`. -/
theorem gamma2_translate_in_F_union_F_sigma (τ : UpperHalfPlane) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2,
      ((γ • τ : UpperHalfPlane) : ℂ) ∈
        Gamma2FundamentalDomain ∪ Gamma2FundamentalDomainReflected := by
  obtain ⟨g, hg_fd⟩ := ModularGroup.exists_smul_mem_fd τ
  have hg_pair : 1 ≤ Complex.normSq ((g • τ : UpperHalfPlane) : ℂ) ∧
      |(g • τ : UpperHalfPlane).re| ≤ 1 / 2 := hg_fd
  set z : ℂ := ((g • τ : UpperHalfPlane) : ℂ) with hz_def
  have hz_norm : 1 ≤ Complex.normSq z := hg_pair.1
  have hz_re : |z.re| ≤ 1 / 2 := by
    have h2 := hg_pair.2
    rwa [← UpperHalfPlane.coe_re, ← hz_def] at h2
  have hz_im : 0 < z.im := by
    rw [hz_def, UpperHalfPlane.coe_im]
    exact (g • τ).im_pos
  have hz_ne : z ≠ 0 := by
    intro h0
    rw [h0] at hz_im
    simp at hz_im
  -- determinant of `g`
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have hp := g.2
    rwa [Matrix.det_fin_two] at hp
  -- `ZMod 2` cast helpers
  have cast1 : ∀ x : ℤ, x % 2 = 1 → ((x : ZMod 2) = 1) := by
    intro x hx
    have hcast : ((x : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
      rw [ZMod.intCast_eq_intCast_iff]
      change x % ((2 : ℕ) : ℤ) = 1 % ((2 : ℕ) : ℤ)
      omega
    simpa using hcast
  have cast0 : ∀ x : ℤ, x % 2 = 0 → ((x : ZMod 2) = 0) := by
    intro x hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega
  -- master construction: given a correction matrix `h = !![p,q;r,s]` with
  -- `h * g ≡ 1 (mod 2)` and the Möbius image of `z` under `h` in `F ∪ F^σ`,
  -- produce the required `γ ∈ Γ(2)`.
  have main : ∀ p q r s : ℤ, ∀ u : ℂ, p * s - q * r = 1 →
      (p * g 0 0 + q * g 1 0) % 2 = 1 →
      (p * g 0 1 + q * g 1 1) % 2 = 0 →
      (r * g 0 0 + s * g 1 0) % 2 = 0 →
      (r * g 0 1 + s * g 1 1) % 2 = 1 →
      ((p : ℂ) * z + (q : ℂ)) / ((r : ℂ) * z + (s : ℂ)) = u →
      u ∈ Gamma2FundamentalDomain ∪ Gamma2FundamentalDomainReflected →
      ∃ γ ∈ CongruenceSubgroup.Gamma 2,
        ((γ • τ : UpperHalfPlane) : ℂ) ∈
          Gamma2FundamentalDomain ∪ Gamma2FundamentalDomainReflected := by
    intro p q r s u hpqrs h1 h2 h3 h4 hu hmem
    have hdet_h : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      rw [Matrix.det_fin_two_of]; exact hpqrs
    obtain ⟨hM, hM_val⟩ : ∃ hM : SL(2, ℤ), (hM : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, s] :=
      ⟨⟨!![p, q; r, s], hdet_h⟩, rfl⟩
    have e00 : (hM * g) 0 0 = p * g 0 0 + q * g 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e01 : (hM * g) 0 1 = p * g 0 1 + q * g 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e10 : (hM * g) 1 0 = r * g 0 0 + s * g 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e11 : (hM * g) 1 1 = r * g 0 1 + s * g 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨hM * g, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma_mem]
      exact ⟨by rw [e00]; exact cast1 _ h1, by rw [e01]; exact cast0 _ h2,
        by rw [e10]; exact cast0 _ h3, by rw [e11]; exact cast1 _ h4⟩
    · rw [mul_smul, sl2z_smul_coe, ← hz_def, hM_val]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hu]
      exact hmem
  -- parity obstruction: `det ≡ 1 (mod 2)` rules out ten parity patterns
  have hparity : (g 0 0 % 2) * (g 1 1 % 2) % 2 ≠ (g 0 1 % 2) * (g 1 0 % 2) % 2 := by
    rw [← Int.mul_emod, ← Int.mul_emod]
    intro hEq
    have hsub : (g 0 0 * g 1 1 - g 0 1 * g 1 0) % 2 = 0 := by
      rw [Int.sub_emod, hEq, sub_self, Int.zero_emod]
    rw [hdet] at hsub
    norm_num at hsub
  rcases Int.emod_two_eq (g 0 0) with ha | ha <;>
    rcases Int.emod_two_eq (g 0 1) with hb | hb <;>
      rcases Int.emod_two_eq (g 1 0) with hc | hc <;>
        rcases Int.emod_two_eq (g 1 1) with hd | hd
  -- (0,0,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,0,0,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,0,1,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,0,1,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,1,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,1,0,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,1,1,0): `S`-class, h = [[0,-1],[1,0]], image -1/z
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 0 (-1) 1 0 (-1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_S_F hz_im hz_norm hz_re hsign))
    · exact main 0 (-1) 1 0 (-1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_S_Fsigma hz_im hz_norm hz_re hsign.le))
  -- (0,1,1,1): `TS`-class, h = [[∓1,-1],[1,0]], image ∓1 - 1/z
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main (-1) (-1) 1 0 (-1 - 1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega)
        (by push_cast
            rw [neg_one_mul, one_mul, add_zero, ← sub_eq_add_neg, sub_div, neg_div,
              div_self hz_ne])
        (Set.mem_union_right _ (gamma2_tile_TS_Fsigma hz_im hz_norm hz_re hsign))
    · exact main 1 (-1) 1 0 (1 - 1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega)
        (by push_cast
            rw [one_mul, add_zero, ← sub_eq_add_neg, sub_div, div_self hz_ne])
        (Set.mem_union_left _ (gamma2_tile_TS_F hz_im hz_norm hz_re hsign.le))
  -- (1,0,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (1,0,0,1): identity class, γ = g itself
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 1 0 0 1 z (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_id_Fsigma hz_im hz_norm hz_re hsign))
    · exact main 1 0 0 1 z (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_id_F hz_im hz_norm hz_re hsign.le))
  -- (1,0,1,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (1,0,1,1): lower-unipotent class, h = [[1,0],[±1,1]], image z/(z+1) or z/(1-z)
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 1 0 1 1 (z / (z + 1)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_L_F hz_im hz_norm hz_re hsign))
    · exact main 1 0 (-1) 1 (z / (1 - z)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_L_Fsigma hz_im hz_norm hz_re hsign.le))
  -- (1,1,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (1,1,0,1): `T`-class, h = [[1,±1],[0,1]], image z ± 1
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 1 1 0 1 (z + 1) (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_T_F hz_im hz_norm hz_re hsign))
    · exact main 1 (-1) 0 1 (z - 1) (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_T_Fsigma hz_im hz_norm hz_re hsign.le))
  -- (1,1,1,0): `ST`-class, h = [[0,-1],[1,±1]], image -1/(z±1)
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 0 (-1) 1 1 (-1 / (z + 1)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_ST_Fsigma hz_im hz_norm hz_re hsign))
    · exact main 0 (-1) 1 (-1) (-1 / (z - 1)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_ST_F hz_im hz_norm hz_re hsign.le))
  -- (1,1,1,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity

/-- **`Im λ ≥ 0` on the closed half-fundamental domain `F`.**
Combines `modularLambdaH_F_im_pos` (strict positivity on the open
interior `F^o`) with the three boundary-arc lemmas
`modularLambdaH_pure_imag_real` (left edge, `λ ∈ ℝ`),
`modularLambdaH_one_add_imag_real` (right edge), and
`modularLambdaH_semicircle_real` (semicircular bottom arc). -/
theorem modularLambdaH_im_nonneg_on_closed_F
    {τ : ℂ} (hτ_F : τ ∈ Gamma2FundamentalDomain) :
    0 ≤ (modularLambdaH τ).im := by
  obtain ⟨hτ_im_pos, hτ_re_nonneg, hτ_re_le_one, hτ_semicircle⟩ := hτ_F
  -- Case split on left/right edges and semicircle vs interior.
  by_cases h_re_zero : τ.re = 0
  · -- Left edge: τ = i·y for some y > 0.
    have h_τ_eq : τ = Complex.I * τ.im := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [h_τ_eq]
    rw [modularLambdaH_pure_imag_real hτ_im_pos]
  · by_cases h_re_one : τ.re = 1
    · -- Right edge: τ = 1 + i·y for some y > 0.
      have h_τ_eq : τ = 1 + Complex.I * τ.im := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h_τ_eq]
      rw [modularLambdaH_one_add_imag_real hτ_im_pos]
    · by_cases h_semicircle : ‖2 * τ - 1‖ = 1
      · -- Semicircle: λ ∈ ℝ.
        rw [modularLambdaH_semicircle_real hτ_im_pos h_semicircle]
      · -- Strict interior: use Step A.
        have hτ_interior : τ ∈ Gamma2FundamentalDomainInterior := by
          refine ⟨hτ_im_pos, ?_, ?_, ?_⟩
          · rcases lt_or_eq_of_le hτ_re_nonneg with h | h
            · exact h
            · exact absurd h.symm h_re_zero
          · rcases lt_or_eq_of_le hτ_re_le_one with h | h
            · exact h
            · exact absurd h h_re_one
          · rcases lt_or_eq_of_le hτ_semicircle with h | h
            · exact h
            · exact absurd h.symm h_semicircle
        exact (modularLambdaH_F_im_pos τ hτ_interior).le

/-- **Half-FD existence (upper branch).** Every `τ ∈ ℍ` with
`Im(λ τ) > 0` has a `Γ(2)`-translate in the half-fundamental domain
`F`. Proof: use the strict fundamental-domain property
`gamma2_translate_in_F_union_F_sigma` to obtain `γ ∈ Γ(2)` with
`γ • τ ∈ F ∪ F^σ`. If `γ • τ ∈ F^σ`, then `-conj(γ • τ) ∈ F`
(by definition of `F^σ` as the reflection of `F`); by
`modularLambdaH_conj_symmetry` and `modularLambdaH_im_nonneg_on_closed_F`,
`Im(λ(γ • τ)) ≤ 0`; but by `Γ(2)`-invariance of `λ`,
`Im(λ(γ • τ)) = Im(λ τ) > 0` — contradiction. So `γ • τ ∈ F`. -/
theorem gamma2_orbit_meets_F_when_im_lambda_pos (τ : UpperHalfPlane)
    (hτ_pos : 0 < (modularLambdaH (τ : ℂ)).im) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2,
      ((γ • τ : UpperHalfPlane) : ℂ) ∈ Gamma2FundamentalDomain := by
  obtain ⟨γ, hγ_in, h_in_union⟩ := gamma2_translate_in_F_union_F_sigma τ
  -- λ-invariance: λ(γ•τ) = λ(τ).
  have h_lam_inv : modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) = modularLambdaH (τ : ℂ) :=
    modularLambdaH_gamma2_invariant γ hγ_in τ
  -- Im(λ γτ) = Im(λ τ) > 0.
  have h_im_lam_γτ : 0 < (modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ)).im := by
    rw [h_lam_inv]; exact hτ_pos
  rcases h_in_union with h_F | h_Fσ
  · exact ⟨γ, hγ_in, h_F⟩
  · -- γ • τ ∈ F^σ: derive contradiction via conjugation.
    exfalso
    -- Extract F^σ membership data.
    obtain ⟨hγτ_im, hγτ_re_ge, hγτ_re_le, hγτ_semicircle⟩ := h_Fσ
    -- -conj(γ • τ) ∈ F.
    set γτ_c : ℂ := ((γ • τ : UpperHalfPlane) : ℂ) with hγτ_c_def
    have h_neg_conj_in_F : -(starRingEnd ℂ γτ_c) ∈ Gamma2FundamentalDomain := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Im(-conj γτ) = Im(γτ) > 0.
        simp only [Complex.neg_im, Complex.conj_im, neg_neg]
        exact hγτ_im
      · -- Re(-conj γτ) = -Re(γτ) ≥ 0 (since Re(γτ) ≤ 0).
        simp only [Complex.neg_re, Complex.conj_re]
        linarith
      · -- Re(-conj γτ) = -Re(γτ) ≤ 1 (since Re(γτ) ≥ -1).
        simp only [Complex.neg_re, Complex.conj_re]
        linarith
      · -- |2(-conj γτ) - 1| = |2γτ + 1| ≥ 1.
        have h_eq_neg_conj : (2 * (-(starRingEnd ℂ γτ_c)) - 1 : ℂ) =
            -(starRingEnd ℂ (2 * γτ_c + 1)) := by
          simp only [map_add, map_mul, Complex.conj_ofNat, map_one]
          ring
        have h_norm_eq : ‖2 * (-(starRingEnd ℂ γτ_c)) - 1‖ = ‖2 * γτ_c + 1‖ := by
          rw [h_eq_neg_conj, norm_neg, Complex.norm_conj]
        rw [h_norm_eq]
        exact hγτ_semicircle
    -- λ(-conj γτ) = conj(λ γτ) by conjugation symmetry.
    have h_lam_neg_conj : modularLambdaH (-(starRingEnd ℂ γτ_c)) =
        starRingEnd ℂ (modularLambdaH γτ_c) :=
      modularLambdaH_conj_symmetry hγτ_im
    -- Im(λ(-conj γτ)) ≥ 0 (from closed F).
    have h_im_neg_conj_nonneg : 0 ≤ (modularLambdaH (-(starRingEnd ℂ γτ_c))).im :=
      modularLambdaH_im_nonneg_on_closed_F h_neg_conj_in_F
    -- Im(conj(λ γτ)) = -Im(λ γτ).
    have h_im_conj_eq : (starRingEnd ℂ (modularLambdaH γτ_c)).im =
        -(modularLambdaH γτ_c).im := by
      simp [Complex.conj_im]
    -- Combine: Im(λ γτ) ≤ 0.
    rw [h_lam_neg_conj, h_im_conj_eq] at h_im_neg_conj_nonneg
    -- h_im_neg_conj_nonneg : 0 ≤ -(modularLambdaH γτ_c).im
    have h_im_γτ_le : (modularLambdaH γτ_c).im ≤ 0 := by linarith
    -- But h_im_lam_γτ : 0 < (modularLambdaH γτ_c).im. Contradiction.
    linarith

/-! ## Half-fundamental-domain injectivity (architectural helper)

The closure of `modularLambdaH_existsUnique_in_F_interior_of_im_pos`
rests on the F_Y argument principle
`cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`.
The non-vanishing boundary conditions required by the AP decompose into
the four boundary helpers below (left edge, right edge, semicircle, top
edge). Uniqueness itself is delivered by the degree-argument bootstrap
`modularLambdaH_F_interior_preimage_unique`, which combines the AP's
divisor-count form with a δ-thickening argument bridging the AP's
shifted-disk geometry (centered at `1/2 + δ·i`) to F's actual semicircle
geometry (centered at `1/2`). -/

/-- **Boundary helper (left edge).** For `w` with `Im w > 0` and `y > 0`,
`λ(i·y) ≠ w`. Direct consequence of `modularLambdaH_pure_imag_real`
(`Im λ(i·y) = 0`) and `Im w > 0`. -/
theorem modularLambdaH_left_edge_ne_of_im_pos
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH (Complex.I * y) ≠ w := by
  intro h_eq
  have h_im_lam_zero : (modularLambdaH (Complex.I * y)).im = 0 :=
    modularLambdaH_pure_imag_real hy
  rw [h_eq] at h_im_lam_zero
  linarith

/-- **Boundary helper (right edge).** For `w` with `Im w > 0` and `y > 0`,
`λ(1 + i·y) ≠ w`. Direct consequence of
`modularLambdaH_one_add_imag_real`. -/
theorem modularLambdaH_right_edge_ne_of_im_pos
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH (1 + Complex.I * y) ≠ w := by
  intro h_eq
  have h_im_lam_zero : (modularLambdaH (1 + Complex.I * y)).im = 0 :=
    modularLambdaH_one_add_imag_real hy
  rw [h_eq] at h_im_lam_zero
  linarith

/-- **Boundary helper (bottom semicircle).** For `w` with `Im w > 0` and
`τ` on the upper semicircle `|2τ − 1| = 1, Im τ > 0`, `λ(τ) ≠ w`. Direct
consequence of `modularLambdaH_semicircle_real`. -/
theorem modularLambdaH_semicircle_ne_of_im_pos
    {w : ℂ} (hw : 0 < w.im) {τ : ℂ}
    (hτ_im : 0 < τ.im) (hτ_semi : ‖2 * τ - 1‖ = 1) :
    modularLambdaH τ ≠ w := by
  intro h_eq
  have h_im_lam_zero : (modularLambdaH τ).im = 0 :=
    modularLambdaH_semicircle_real hτ_im hτ_semi
  rw [h_eq] at h_im_lam_zero
  linarith

/-- **Boundary helper (top edge).** For `w` with `Im w > 0`, there exists
`Y₀` such that for all `Y ≥ Y₀` and all `x ∈ [0, 1]`,
`λ(x + Y·i) ≠ w`. Proof: `‖θ₂(τ)‖ ≤ 10·exp(−π·Im τ/4)` (from
`theta2_norm_le_of_im_ge_one`) and `‖jacobiTheta τ − 1‖ ≤ C·exp(−π·Im τ)`
(from `isBigO_at_im_infty_jacobiTheta_sub_one`) — both bounds depend
only on `Im τ`, hence uniform in `Re τ`. Combined,
`‖λ(τ)‖ ≤ 160000·exp(−π·Im τ)` for `Im τ` large, which is `< ‖w‖` for
`Im τ` large enough. -/
theorem modularLambdaH_top_edge_far_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) ≠ w := by
  have hw_ne : w ≠ 0 := fun h_eq => by rw [h_eq] at hw; simp at hw
  have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  -- Get the uniform bound on jacobiTheta - 1 (depends only on Im τ).
  obtain ⟨C, hC⟩ := isBigO_at_im_infty_jacobiTheta_sub_one.bound
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hC
  obtain ⟨Y_start, hY_start⟩ := hC
  -- Exponential decay of exp(-π·Y).
  have h_exp_decay : Filter.Tendsto (fun Y : ℝ => Real.exp (-Real.pi * Y))
      Filter.atTop (nhds 0) := by
    have h_arg : Filter.Tendsto (fun Y : ℝ => -Real.pi * Y) Filter.atTop Filter.atBot := by
      have h1 : Filter.Tendsto (fun Y : ℝ => Real.pi * Y) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop Real.pi_pos Filter.tendsto_id
      have h2 := Filter.tendsto_neg_atTop_atBot.comp h1
      refine h2.congr ?_
      intro Y
      simp only [Function.comp_apply]
      ring
    exact Real.tendsto_exp_atBot.comp h_arg
  -- C·exp(-π·Y) ≤ 1/2 eventually.
  have h_C_evt : ∀ᶠ Y in Filter.atTop, C * Real.exp (-Real.pi * Y) ≤ 1/2 := by
    have h_lim : Filter.Tendsto (fun Y : ℝ => C * Real.exp (-Real.pi * Y))
        Filter.atTop (nhds 0) := by
      have := h_exp_decay.const_mul C
      simpa using this
    have h_lt : ∀ᶠ Y in Filter.atTop, C * Real.exp (-Real.pi * Y) < 1/2 :=
      h_lim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
    filter_upwards [h_lt] with Y hY using hY.le
  -- 160000·exp(-π·Y) < ‖w‖ eventually.
  have h_lambda_norm_evt :
      ∀ᶠ Y in Filter.atTop, 160000 * Real.exp (-Real.pi * Y) < ‖w‖ := by
    have h_lim : Filter.Tendsto (fun Y : ℝ => 160000 * Real.exp (-Real.pi * Y))
        Filter.atTop (nhds 0) := by
      have := h_exp_decay.const_mul 160000
      simpa using this
    exact h_lim.eventually (eventually_lt_nhds hw_norm_pos)
  -- Combine.
  have h_combined : ∀ᶠ Y in Filter.atTop,
      max 1 Y_start ≤ Y ∧
      C * Real.exp (-Real.pi * Y) ≤ 1/2 ∧
      160000 * Real.exp (-Real.pi * Y) < ‖w‖ := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨max 1 Y_start, fun Y hY => hY⟩,
      h_C_evt, h_lambda_norm_evt] with Y h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  rw [Filter.eventually_atTop] at h_combined
  obtain ⟨Y₀, hY₀⟩ := h_combined
  refine ⟨Y₀, ?_⟩
  intro Y hY_ge x hx_nn hx_le
  obtain ⟨hY_max_le, hC_half, h_lam_bound⟩ := hY₀ Y hY_ge
  have hY_start_le : Y_start ≤ Y := le_trans (le_max_right _ _) hY_max_le
  have hY_one_le : 1 ≤ Y := le_trans (le_max_left _ _) hY_max_le
  set τ : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I with hτ_def
  have hτ_im : τ.im = Y := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_θ₂_bound : ‖theta2 τ‖ ≤ 10 * Real.exp (-Real.pi * Y / 4) := by
    have h_τ_im_ge : 1 ≤ τ.im := by rw [hτ_im]; exact hY_one_le
    have h := theta2_norm_le_of_im_ge_one h_τ_im_ge
    rw [hτ_im] at h
    exact h
  have h_jt_bound : ‖jacobiTheta τ - 1‖ ≤ C * Real.exp (-Real.pi * Y) := by
    have h_apply := hY_start Y hY_start_le τ hτ_im
    rw [hτ_im, Real.norm_of_nonneg (Real.exp_pos _).le] at h_apply
    exact h_apply
  have h_θ₃_lb : 1/2 ≤ ‖theta3 τ‖ := by
    unfold theta3
    have h1 : ‖jacobiTheta τ - 1‖ ≤ 1/2 := le_trans h_jt_bound hC_half
    have h_norm_diff :
        ‖(1 : ℂ)‖ - ‖jacobiTheta τ‖ ≤ ‖(1 : ℂ) - jacobiTheta τ‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, norm_sub_rev] at h_norm_diff
    linarith
  -- Conclude λ(τ) ≠ w by norm comparison.
  intro h_eq
  -- λ(τ) = θ₂⁴ / θ₃⁴ = w, so ‖θ₂‖⁴/‖θ₃‖⁴ = ‖w‖.
  have h_θ₃_ne : theta3 τ ≠ 0 := by
    intro h_eq_zero
    rw [h_eq_zero, norm_zero] at h_θ₃_lb
    linarith
  have h_θ₃_pow_ne : theta3 τ ^ 4 ≠ 0 := pow_ne_zero _ h_θ₃_ne
  have h_lam_def : modularLambdaH τ = theta2 τ ^ 4 / theta3 τ ^ 4 := rfl
  rw [h_lam_def] at h_eq
  have h_lam_norm : ‖theta2 τ ^ 4 / theta3 τ ^ 4‖ = ‖w‖ := by rw [h_eq]
  rw [norm_div, norm_pow, norm_pow] at h_lam_norm
  have h_θ₂_nn : 0 ≤ ‖theta2 τ‖ := norm_nonneg _
  have h_θ₂_pow_le : ‖theta2 τ‖^4 ≤ (10 * Real.exp (-Real.pi * Y / 4))^4 :=
    pow_le_pow_left₀ h_θ₂_nn h_θ₂_bound 4
  have h_θ₂_pow_simp :
      (10 * Real.exp (-Real.pi * Y / 4))^4 = 10000 * Real.exp (-Real.pi * Y) := by
    rw [mul_pow]
    have h1 : (10 : ℝ)^4 = 10000 := by norm_num
    have h2 : (Real.exp (-Real.pi * Y / 4))^4 = Real.exp (-Real.pi * Y) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [h1, h2]
  have h_θ₂_pow_le_2 : ‖theta2 τ‖^4 ≤ 10000 * Real.exp (-Real.pi * Y) :=
    h_θ₂_pow_le.trans (le_of_eq h_θ₂_pow_simp)
  have h_θ₃_lb_pow : (1/16 : ℝ) ≤ ‖theta3 τ‖^4 := by
    have h_one_sixteenth : (1/2 : ℝ)^4 = 1/16 := by norm_num
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h_θ₃_lb 4
    rw [h_one_sixteenth] at h
    exact h
  have h_θ₃_pow_pos : 0 < ‖theta3 τ‖^4 :=
    pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_θ₃_lb) 4
  have h_lam_norm_le :
      ‖theta2 τ‖^4 / ‖theta3 τ‖^4 ≤ 160000 * Real.exp (-Real.pi * Y) := by
    calc ‖theta2 τ‖^4 / ‖theta3 τ‖^4
        ≤ (10000 * Real.exp (-Real.pi * Y)) / ‖theta3 τ‖^4 :=
          div_le_div_of_nonneg_right h_θ₂_pow_le_2 h_θ₃_pow_pos.le
      _ ≤ (10000 * Real.exp (-Real.pi * Y)) / (1/16) := by
          apply div_le_div_of_nonneg_left _ (by norm_num : (0:ℝ) < 1/16) h_θ₃_lb_pow
          have h_exp_nn : 0 ≤ Real.exp (-Real.pi * Y) := (Real.exp_pos _).le
          positivity
      _ = 160000 * Real.exp (-Real.pi * Y) := by ring
  linarith [h_lam_norm_le, h_lam_bound, h_lam_norm]

/-! ## Path-(a) F_Y AP application scaffold

The F_Y argument principle
`cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`
from `WindingNumber.lean` drives both the winding-index theorem
`modularLambdaH_F_Y_image_curve_winding_index_eq_one` and the
degree-argument bootstrap `modularLambdaH_F_interior_preimage_unique`
(uniqueness of the `λ`-preimage in `F^o`). The scaffold below
decomposes the application into sub-lemmas with explicit statements.

The F_Y region is a rectangle minus an upper half-disk on its bottom edge,
shaped to approximate the closure of `F^o ∩ {δ ≤ Im ≤ Y}` for small `δ`
and large `Y`. The chosen parameters are
`a = 0, b = 1, e = 1/2 + δ·i, R₀ = R₀'`, where `δ > 0` and `R₀' ∈ (0, 1/2)`
are picked to satisfy the strict AP hypothesis `a < e.re − R₀` (giving
`R₀' < 1/2`) while keeping `τ₁, τ₂` inside the F_Y interior. -/

/-- **Sub-lemma 1 — F_Y geometric setup.** For `w ∈ ℍ` and any
`τ₁, τ₂ ∈ F^o`, there exists a parameter triple `(δ, Y, R₀)` with:
* `0 < δ ≤ δ_max ≤ 1/4` (rectangle bottom above the real axis);
* `δ < τᵢ.im < Y` (rectangle covers both `τᵢ`);
* `0 < R₀ < 1/2` (strict AP hypothesis `0 < 1/2 − R₀`);
* `‖τᵢ − (1/2 + δ·i)‖ > R₀` for each `τᵢ` (both `τᵢ` strictly outside
  the disk, hence in F_Y interior).

The proof picks `δ := min(τ₁.im/2, τ₂.im/2, δ_max)`,
`Y := max(τ₁.im + 1, τ₂.im + 1, 1)`, and `R₀ := 1/2 − δ`. The norm
condition follows from `|τᵢ − 1/2| > 1/2` (from `F^o`) via the reverse
triangle inequality. -/
theorem modularLambdaH_F_Y_params_exist
    {w : ℂ} (_hw : 0 < w.im)
    {τ₁ τ₂ : ℂ}
    (h₁_in : τ₁ ∈ Gamma2FundamentalDomainInterior)
    (h₂_in : τ₂ ∈ Gamma2FundamentalDomainInterior)
    {δ_max : ℝ} (hδ_max_pos : 0 < δ_max) (hδ_max_lt_quarter : δ_max ≤ 1 / 4) :
    ∃ δ Y R₀ : ℝ,
      0 < δ ∧ δ ≤ δ_max ∧ δ < τ₁.im ∧ δ < τ₂.im ∧
      δ < Y ∧ τ₁.im < Y ∧ τ₂.im < Y ∧
      0 < R₀ ∧ R₀ < 1 / 2 ∧ δ + R₀ < Y ∧
      ‖τ₁ - (1/2 + δ * Complex.I)‖ > R₀ ∧
      ‖τ₂ - (1/2 + δ * Complex.I)‖ > R₀ := by
  obtain ⟨h₁_im, _, _, h₁_semi⟩ := h₁_in
  obtain ⟨h₂_im, _, _, h₂_semi⟩ := h₂_in
  -- δ := min(τ₁.im / 2, τ₂.im / 2, δ_max).
  set δ : ℝ := min (min (τ₁.im / 2) (τ₂.im / 2)) δ_max with hδ_def
  have hδ_pos : 0 < δ := by
    refine lt_min (lt_min ?_ ?_) hδ_max_pos
    · linarith
    · linarith
  have hδ_le_δ_max : δ ≤ δ_max := min_le_right _ _
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le_δ_max hδ_max_lt_quarter
  have hδ_lt_half : δ < 1/2 := by linarith
  have hδ_lt_τ₁_im : δ < τ₁.im := by
    have h₁ : δ ≤ τ₁.im / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδ_lt_τ₂_im : δ < τ₂.im := by
    have h₂ : δ ≤ τ₂.im / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  -- Y := max(τ₁.im + 1, τ₂.im + 1, 1).
  set Y : ℝ := max (max (τ₁.im + 1) (τ₂.im + 1)) 1 with hY_def
  have hY_ge_one : (1 : ℝ) ≤ Y := le_max_right _ _
  have hY_gt_τ₁_im : τ₁.im < Y := by
    have h₁ : τ₁.im + 1 ≤ Y := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hY_gt_τ₂_im : τ₂.im < Y := by
    have h₂ : τ₂.im + 1 ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hY_gt_δ : δ < Y := lt_of_lt_of_le hδ_lt_half (by linarith)
  -- R₀ := 1/2 - δ.
  set R₀ : ℝ := 1/2 - δ with hR₀_def
  have hR₀_pos : 0 < R₀ := by linarith
  have hR₀_lt_half : R₀ < 1/2 := by linarith
  have h_δ_plus_R₀_eq : δ + R₀ = 1/2 := by rw [hR₀_def]; ring
  have hY_gt_δ_plus_R₀ : δ + R₀ < Y := by rw [h_δ_plus_R₀_eq]; linarith
  refine ⟨δ, Y, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ₁_im, hδ_lt_τ₂_im, hY_gt_δ,
    hY_gt_τ₁_im, hY_gt_τ₂_im, hR₀_pos, hR₀_lt_half, hY_gt_δ_plus_R₀, ?_, ?_⟩
  · -- ‖τ₁ - (1/2 + δi)‖ > R₀.
    have h_semi_real : 1 < ‖2 * τ₁ - 1‖ := h₁_semi
    have h_eq : 2 * τ₁ - 1 = 2 * (τ₁ - 1/2) := by ring
    rw [h_eq, norm_mul] at h_semi_real
    have h_norm_2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h_norm_2] at h_semi_real
    have h_norm_τ₁_minus : 1/2 < ‖τ₁ - 1/2‖ := by linarith
    have h_norm_δ : ‖((δ : ℂ) * Complex.I)‖ = δ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ_pos]
    have h_sub_eq : τ₁ - (1/2 + δ * Complex.I) = (τ₁ - 1/2) - δ * Complex.I := by ring
    rw [h_sub_eq]
    have h_rtri := norm_sub_norm_le (τ₁ - 1/2) ((δ : ℂ) * Complex.I)
    rw [h_norm_δ] at h_rtri
    linarith
  · -- ‖τ₂ - (1/2 + δi)‖ > R₀.
    have h_semi_real : 1 < ‖2 * τ₂ - 1‖ := h₂_semi
    have h_eq : 2 * τ₂ - 1 = 2 * (τ₂ - 1/2) := by ring
    rw [h_eq, norm_mul] at h_semi_real
    have h_norm_2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h_norm_2] at h_semi_real
    have h_norm_τ₂_minus : 1/2 < ‖τ₂ - 1/2‖ := by linarith
    have h_norm_δ : ‖((δ : ℂ) * Complex.I)‖ = δ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ_pos]
    have h_sub_eq : τ₂ - (1/2 + δ * Complex.I) = (τ₂ - 1/2) - δ * Complex.I := by ring
    rw [h_sub_eq]
    have h_rtri := norm_sub_norm_le (τ₂ - 1/2) ((δ : ℂ) * Complex.I)
    rw [h_norm_δ] at h_rtri
    linarith

/-- **Sub-lemma 1' — F_Y geometric setup adapted for sub-lemma 8.**
A stronger variant of `modularLambdaH_F_Y_params_exist` that additionally
ensures `R₀ > √(1/4 − δ²)`, so the shifted-disk arc lies strictly inside
F^o (where each arc point satisfies `|τ − 1/2| > 1/2`).

This variant picks `δ` small enough relative to the buffer
`εᵢ := ‖τᵢ − 1/2‖² − 1/4 > 0` (from F^o) and the imaginary parts. The
choice `R₀ := 1/2 − δ²/4` lies in the narrow interval
`(√(1/4 − δ²), 1/2)` and admits `‖τᵢ − (1/2 + δ·i)‖ > R₀` provided
`δ ≤ εᵢ/(4 · τᵢ.im)`. -/
theorem modularLambdaH_F_Y_params_exist_arc
    {w : ℂ} (_hw : 0 < w.im)
    {τ₁ τ₂ : ℂ}
    (h₁_in : τ₁ ∈ Gamma2FundamentalDomainInterior)
    (h₂_in : τ₂ ∈ Gamma2FundamentalDomainInterior)
    {δ_max : ℝ} (hδ_max_pos : 0 < δ_max) (hδ_max_lt_quarter : δ_max ≤ 1 / 4) :
    ∃ δ Y R₀ : ℝ,
      0 < δ ∧ δ ≤ δ_max ∧ δ < τ₁.im ∧ δ < τ₂.im ∧
      δ < Y ∧ τ₁.im < Y ∧ τ₂.im < Y ∧
      0 < R₀ ∧ R₀ < 1 / 2 ∧ δ + R₀ < Y ∧
      Real.sqrt (1/4 - δ^2) < R₀ ∧
      ‖τ₁ - (1/2 + δ * Complex.I)‖ > R₀ ∧
      ‖τ₂ - (1/2 + δ * Complex.I)‖ > R₀ := by
  obtain ⟨h₁_im, _, _, h₁_semi⟩ := h₁_in
  obtain ⟨h₂_im, _, _, h₂_semi⟩ := h₂_in
  -- F^o gives ‖τᵢ - 1/2‖ > 1/2.
  have h_norm_τ₁_sub_gt : 1/2 < ‖τ₁ - 1/2‖ := by
    have h_semi : 1 < ‖2 * τ₁ - 1‖ := h₁_semi
    have h_eq : 2 * τ₁ - 1 = 2 * (τ₁ - 1/2) := by ring
    rw [h_eq, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num] at h_semi
    linarith
  have h_norm_τ₂_sub_gt : 1/2 < ‖τ₂ - 1/2‖ := by
    have h_semi : 1 < ‖2 * τ₂ - 1‖ := h₂_semi
    have h_eq : 2 * τ₂ - 1 = 2 * (τ₂ - 1/2) := by ring
    rw [h_eq, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num] at h_semi
    linarith
  have h_ε₁_pos : 0 < ‖τ₁ - 1/2‖^2 - 1/4 := by nlinarith [h_norm_τ₁_sub_gt]
  have h_ε₂_pos : 0 < ‖τ₂ - 1/2‖^2 - 1/4 := by nlinarith [h_norm_τ₂_sub_gt]
  -- Step 2: obtain δ as opaque value, with all needed bounds proven inside.
  have h_δ_exists : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ_max ∧ δ ≤ 1/4 ∧
      δ < τ₁.im ∧ δ < τ₂.im ∧
      2 * δ * τ₁.im ≤ (‖τ₁ - 1/2‖^2 - 1/4) / 2 ∧
      2 * δ * τ₂.im ≤ (‖τ₂ - 1/2‖^2 - 1/4) / 2 := by
    -- Pick the candidate δ as the min of five bounds.
    set b₁ : ℝ := τ₁.im / 2 with hb₁_def
    set b₂ : ℝ := τ₂.im / 2 with hb₂_def
    set bε₁ : ℝ := (‖τ₁ - 1/2‖^2 - 1/4) / (4 * τ₁.im) with hbε₁_def
    set bε₂ : ℝ := (‖τ₂ - 1/2‖^2 - 1/4) / (4 * τ₂.im) with hbε₂_def
    have hb₁_pos : 0 < b₁ := by rw [hb₁_def]; linarith
    have hb₂_pos : 0 < b₂ := by rw [hb₂_def]; linarith
    have hbε₁_pos : 0 < bε₁ := by rw [hbε₁_def]; positivity
    have hbε₂_pos : 0 < bε₂ := by rw [hbε₂_def]; positivity
    refine ⟨min (min (min b₁ b₂) δ_max) (min bε₁ bε₂), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 < δ.
      exact lt_min (lt_min (lt_min hb₁_pos hb₂_pos) hδ_max_pos) (lt_min hbε₁_pos hbε₂_pos)
    · -- δ ≤ δ_max.
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    · -- δ ≤ 1/4.
      exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) hδ_max_lt_quarter
    · -- δ < τ₁.im.
      have : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ b₁ :=
        le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
      rw [hb₁_def] at this
      linarith
    · -- δ < τ₂.im.
      have : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ b₂ :=
        le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
      rw [hb₂_def] at this
      linarith
    · -- 2δ·τ₁.im ≤ (‖τ₁-1/2‖²-1/4)/2.
      have h_δ_le_bε₁ : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ bε₁ :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      rw [hbε₁_def] at h_δ_le_bε₁
      have h_4τ₁_pos : 0 < 4 * τ₁.im := by linarith
      have h_mul : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) * (4 * τ₁.im) ≤
          ((‖τ₁ - 1/2‖^2 - 1/4) / (4 * τ₁.im)) * (4 * τ₁.im) :=
        mul_le_mul_of_nonneg_right h_δ_le_bε₁ (le_of_lt h_4τ₁_pos)
      rw [div_mul_cancel₀ _ (ne_of_gt h_4τ₁_pos)] at h_mul
      linarith
    · -- 2δ·τ₂.im ≤ (‖τ₂-1/2‖²-1/4)/2.
      have h_δ_le_bε₂ : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ bε₂ :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      rw [hbε₂_def] at h_δ_le_bε₂
      have h_4τ₂_pos : 0 < 4 * τ₂.im := by linarith
      have h_mul : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) * (4 * τ₂.im) ≤
          ((‖τ₂ - 1/2‖^2 - 1/4) / (4 * τ₂.im)) * (4 * τ₂.im) :=
        mul_le_mul_of_nonneg_right h_δ_le_bε₂ (le_of_lt h_4τ₂_pos)
      rw [div_mul_cancel₀ _ (ne_of_gt h_4τ₂_pos)] at h_mul
      linarith
  -- Now obtain δ as opaque.
  obtain ⟨δ, hδ_pos, hδ_le_δ_max, hδ_le_quarter, hδ_lt_τ₁_im, hδ_lt_τ₂_im,
    h_2δ_τ₁_le, h_2δ_τ₂_le⟩ := h_δ_exists
  -- Step 3: compute Y and R₀.
  set Y : ℝ := max (max (τ₁.im + 1) (τ₂.im + 1)) 1 with hY_def
  have hY_ge_one : (1 : ℝ) ≤ Y := le_max_right _ _
  have hY_gt_τ₁_im : τ₁.im < Y := by
    have : τ₁.im + 1 ≤ Y := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hY_gt_τ₂_im : τ₂.im < Y := by
    have : τ₂.im + 1 ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hY_gt_δ : δ < Y := by linarith
  set R₀ : ℝ := 1/2 - δ^2/4 with hR₀_def
  have h_δ_sq_pos : 0 < δ^2 := by positivity
  have h_δ_sq_le_inv16 : δ^2 ≤ 1/16 := by nlinarith
  have hR₀_pos : 0 < R₀ := by rw [hR₀_def]; linarith
  have hR₀_lt_half : R₀ < 1/2 := by rw [hR₀_def]; linarith
  have h_δ_plus_R₀_lt_Y : δ + R₀ < Y := by
    rw [hR₀_def]
    have h_δ_sq_nn : (0:ℝ) ≤ δ^2/4 := by positivity
    linarith
  -- R₀ > √(1/4 - δ²).
  have h_arg_nn : (0:ℝ) ≤ 1/4 - δ^2 := by linarith
  have h_R₀_sq_eq : R₀^2 = 1/4 - δ^2/4 + δ^4/16 := by rw [hR₀_def]; ring
  have h_R₀_sq_gt : 1/4 - δ^2 < R₀^2 := by
    rw [h_R₀_sq_eq]
    have h_3δ_sq_pos : 0 < 3 * δ^2 / 4 := by positivity
    have h_δ_4_nn : (0:ℝ) ≤ δ^4 / 16 := by positivity
    linarith
  have h_sqrt_lt_R₀ : Real.sqrt (1/4 - δ^2) < R₀ := by
    have h_sqrt_lt_sqrt : Real.sqrt (1/4 - δ^2) < Real.sqrt (R₀^2) :=
      Real.sqrt_lt_sqrt h_arg_nn h_R₀_sq_gt
    rw [Real.sqrt_sq hR₀_pos.le] at h_sqrt_lt_sqrt
    exact h_sqrt_lt_sqrt
  -- Pre-compute the shared inequality δ⁴/16 ≤ δ²/4.
  have h_δ4_le_δ2 : δ^4 / 16 ≤ δ^2 / 4 := by nlinarith [h_δ_sq_pos, h_δ_sq_le_inv16]
  -- Helper: compute the squared norm of `τ - (1/2 + δi)` for any τ : ℂ.
  -- Cast `1/2 : ℂ` as `((1/2 : ℝ) : ℂ)` so `Complex.ofReal_re`/`Complex.ofReal_im`
  -- can reduce the complex arithmetic uniformly.
  have h_half_cast : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
  have h_normSq : ∀ (z : ℂ),
      ‖z - (1/2 + (δ : ℂ) * Complex.I)‖^2 = ‖z - 1/2‖^2 - 2*δ*z.im + δ^2 := by
    intro z
    rw [h_half_cast, Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
      Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- Pre-compute the squared norm bounds for τ₁ and τ₂.
  have h_τ₁_normSq_gt : R₀^2 < ‖τ₁ - (1/2 + (δ : ℂ) * Complex.I)‖^2 := by
    rw [h_normSq τ₁, h_R₀_sq_eq]
    linarith [h_2δ_τ₁_le, h_ε₁_pos, h_δ_sq_pos, h_δ4_le_δ2]
  have h_τ₂_normSq_gt : R₀^2 < ‖τ₂ - (1/2 + (δ : ℂ) * Complex.I)‖^2 := by
    rw [h_normSq τ₂, h_R₀_sq_eq]
    linarith [h_2δ_τ₂_le, h_ε₂_pos, h_δ_sq_pos, h_δ4_le_δ2]
  -- Take square roots.
  have h_τ₁_norm_gt : R₀ < ‖τ₁ - (1/2 + (δ : ℂ) * Complex.I)‖ := by
    have h_sqrt_lt : Real.sqrt (R₀^2) <
        Real.sqrt (‖τ₁ - (1/2 + (δ : ℂ) * Complex.I)‖^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_τ₁_normSq_gt
    rw [Real.sqrt_sq hR₀_pos.le, Real.sqrt_sq (norm_nonneg _)] at h_sqrt_lt
    exact h_sqrt_lt
  have h_τ₂_norm_gt : R₀ < ‖τ₂ - (1/2 + (δ : ℂ) * Complex.I)‖ := by
    have h_sqrt_lt : Real.sqrt (R₀^2) <
        Real.sqrt (‖τ₂ - (1/2 + (δ : ℂ) * Complex.I)‖^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_τ₂_normSq_gt
    rw [Real.sqrt_sq hR₀_pos.le, Real.sqrt_sq (norm_nonneg _)] at h_sqrt_lt
    exact h_sqrt_lt
  exact ⟨δ, Y, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ₁_im, hδ_lt_τ₂_im, hY_gt_δ,
    hY_gt_τ₁_im, hY_gt_τ₂_im, hR₀_pos, hR₀_lt_half, h_δ_plus_R₀_lt_Y, h_sqrt_lt_R₀,
    h_τ₁_norm_gt, h_τ₂_norm_gt⟩

/-- **Sub-lemma 2 — analyticity on the closed F_Y region.** Given F_Y
parameters with `δ > 0`, the function `g(τ) := λ(τ) − w` is analytic on
an open neighbourhood of the closed F_Y region
`(Set.Icc 0 1 ×ℂ Set.Icc δ Y) \ Metric.ball (1/2 + δ·i) R₀`.

Proof: the F_Y region is contained in the open upper half-plane (since
its bottom edge sits at `Im τ = δ > 0`), where `λ` is analytic by
`modularLambdaH_differentiableOn`. Subtracting the constant `w`
preserves analyticity. -/
theorem modularLambdaH_F_Y_analytic
    (w : ℂ) {δ Y R₀ : ℝ} (hδ : 0 < δ) (_hδY : δ < Y) (_hR₀ : 0 < R₀) :
    AnalyticOnNhd ℂ (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀) := by
  intro τ hτ
  obtain ⟨h_box, _⟩ := hτ
  rw [Complex.mem_reProdIm] at h_box
  obtain ⟨_, h_im⟩ := h_box
  rw [Set.mem_Icc] at h_im
  have hτ_im_pos : 0 < τ.im := lt_of_lt_of_le hδ h_im.1
  have h_open_H : IsOpen ({z : ℂ | 0 < z.im} : Set ℂ) := by
    have h_set_eq : ({z : ℂ | 0 < z.im} : Set ℂ) = Complex.im ⁻¹' Set.Ioi 0 := by
      ext; simp
    rw [h_set_eq]
    exact isOpen_Ioi.preimage Complex.continuous_im
  have h_lam_an : AnalyticAt ℂ modularLambdaH τ :=
    (modularLambdaH_differentiableOn.analyticOnNhd h_open_H) τ hτ_im_pos
  exact h_lam_an.sub analyticAt_const

/-- **Sub-lemma 3 — left edge non-vanishing.** For `w ∈ ℍ` and any
`y > 0`, `λ(0 + i·y) − w ≠ 0`. Direct from
`modularLambdaH_left_edge_ne_of_im_pos`. -/
theorem modularLambdaH_F_Y_left_edge_ne
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0 := by
  intro h_eq
  have h_lam_eq : modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) = w := by
    linear_combination h_eq
  have h_z_eq : ((0 : ℂ) + (y : ℂ) * Complex.I) = Complex.I * y := by ring
  rw [h_z_eq] at h_lam_eq
  exact modularLambdaH_left_edge_ne_of_im_pos hw hy h_lam_eq

/-- **Sub-lemma 4 — right edge non-vanishing.** For `w ∈ ℍ` and any
`y > 0`, `λ(1 + i·y) − w ≠ 0`. Direct from
`modularLambdaH_right_edge_ne_of_im_pos`. -/
theorem modularLambdaH_F_Y_right_edge_ne
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0 := by
  intro h_eq
  have h_lam_eq : modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) = w := by
    linear_combination h_eq
  have h_z_eq : ((1 : ℂ) + (y : ℂ) * Complex.I) = 1 + Complex.I * y := by ring
  rw [h_z_eq] at h_lam_eq
  exact modularLambdaH_right_edge_ne_of_im_pos hw hy h_lam_eq

/-- **Sub-lemma 5 — top edge non-vanishing for `Y` sufficiently large.**
For `w ∈ ℍ`, there exists `Y₀` such that for all `Y ≥ Y₀` and
`x ∈ [0, 1]`, `λ(x + i·Y) − w ≠ 0`. Direct from
`modularLambdaH_top_edge_far_of_im_pos`. -/
theorem modularLambdaH_F_Y_top_edge_ne {w : ℂ} (hw : 0 < w.im) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0 := by
  obtain ⟨Y₀, hY₀⟩ := modularLambdaH_top_edge_far_of_im_pos hw
  refine ⟨Y₀, fun Y hY x hx_nn hx_le h_eq => ?_⟩
  have h_lam_eq : modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) = w := by
    linear_combination h_eq
  exact hY₀ Y hY x hx_nn hx_le h_lam_eq

/-- **Sub-lemma 6 — bot_left coupled strip non-vanishing.** For
`w ∈ ℍ`, there exists `δ_w ∈ (0, 1/2)` such that for all
`δ ∈ (0, δ_w]` and `x ∈ [0, δ]`, `λ(x + i·δ) − w ≠ 0`.

The strip width is coupled to `δ` (matching the bot_left segment of
the F_Y region when `R₀ = 1/2 − δ`). For `τ = x + δi` with `x ≤ δ`,
`|τ| ≤ δ√2`, so `Im(−1/τ) = δ/(x² + δ²) ≥ 1/(2δ)`. For `δ ≤ 1/2`,
this gives `Im(−1/τ) ≥ 1`, and
`modularLambdaH_norm_le_exp_of_im_ge_one` yields
`‖λ(−1/τ)‖ ≤ 160000·exp(−π/(2δ))`. By the S-action identity
`modularLambdaH_add_S_smul_eq_one` (`λ(τ) + λ(−1/τ) = 1`),
`‖λ(τ) − 1‖ ≤ 160000·exp(−π/(2δ))`. Since `w ∈ ℍ`, `w ≠ 1` and
`‖w − 1‖ > 0`. For `δ` sufficiently small, the exponential bound
beats `‖w − 1‖`, forcing `λ(τ) ≠ w`. -/
theorem modularLambdaH_F_Y_bot_left_strip_ne
    {w : ℂ} (hw : 0 < w.im) :
    ∃ δ_w : ℝ, 0 < δ_w ∧ δ_w < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_w → ∀ x : ℝ,
      0 ≤ x → x ≤ δ →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0 := by
  have hw_ne_one : w ≠ 1 := fun h_eq => by rw [h_eq] at hw; simp at hw
  have hw_one_norm_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne_one)
  set L : ℝ := Real.log (160000 / ‖w - 1‖) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_nn hx_le h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  have h_x_sq_le_δ_sq : x^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < x^2 + δ^2 := by nlinarith
  have h_normSq : Complex.normSq τ = x^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ_re, hτ_im]; ring
  -- Im(-1/τ) = δ/(x² + δ²).
  have h_im_inv : (-(τ : ℂ)⁻¹).im = δ / (x^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ_im, h_normSq]; ring
  -- 1/(2δ) ≤ Im(-1/τ): equivalent to x² + δ² ≤ 2δ² (i.e., x² ≤ δ²).
  have h_im_inv_ge : 1/(2*δ) ≤ (-(τ : ℂ)⁻¹).im := by
    rw [h_im_inv, div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  -- 1/(2δ) ≥ 2 (since δ ≤ 1/4).
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_ge_one : 1 ≤ (-(τ : ℂ)⁻¹).im := by linarith
  -- Apply norm bound to -1/τ.
  have h_norm_lam_inv : ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_ge_one
  -- Apply S-action identity: λ(τ) + λ(-1/τ) = 1.
  have h_S : modularLambdaH τ + modularLambdaH (-1/τ) = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ_im_pos
  have h_neg_eq : -1/τ = -τ⁻¹ := by field_simp
  rw [h_neg_eq] at h_S
  -- ‖λ(τ) - 1‖ = ‖λ(-τ⁻¹)‖.
  have h_diff_eq : modularLambdaH τ - 1 = -modularLambdaH (-(τ : ℂ)⁻¹) := by
    linear_combination h_S
  have h_norm_diff : ‖modularLambdaH τ - 1‖ = ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ := by
    rw [h_diff_eq, norm_neg]
  -- ‖λ(τ) - 1‖ ≤ 160000 · exp(-π · 1/(2δ)).
  have h_exp_mono : Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_ge]
  have h_bound : ‖modularLambdaH τ - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff]
    refine le_trans h_norm_lam_inv ?_
    exact mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
  -- M ≤ 1/(2δ): δ ≤ 1/(2M) means 2δM ≤ 1.
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  -- π * (1/(2δ)) > L since π > 1 and M ≥ L: π · M > M ≥ L, and π/(2δ) ≥ π·M.
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_M_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := by exact mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_M_ge_pi_M
  -- exp(-π·(1/(2δ))) < exp(-L) = ‖w-1‖/160000.
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have h_quot_pos : (0 : ℝ) < 160000 / ‖w - 1‖ := by positivity
  have h_exp_neg_L : Real.exp (-L) = ‖w - 1‖ / 160000 := by
    rw [hL_def]
    rw [show -Real.log (160000 / ‖w - 1‖) = Real.log ((160000 / ‖w - 1‖)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 / ‖w - 1‖)⁻¹)]
    rw [inv_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < ‖w - 1‖ := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := by
          exact mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (‖w - 1‖ / 160000) := by rw [h_exp_neg_L]
      _ = ‖w - 1‖ := by field_simp
  have h_strict : ‖modularLambdaH τ - 1‖ < ‖w - 1‖ := lt_of_le_of_lt h_bound h_final_bound
  rw [h_lam_eq] at h_strict
  exact lt_irrefl _ h_strict

/-- **Sub-lemma 7 — bot_right coupled strip non-vanishing.** For
`w ∈ ℍ`, there exists `δ_w ∈ (0, 1/2)` such that for all
`δ ∈ (0, δ_w]` and `x ∈ [1 − δ, 1]`, `λ(x + i·δ) − w ≠ 0`.

The strip width is coupled to `δ` (matching the bot_right segment of
the F_Y region when `R₀ = 1/2 − δ`). For `τ = x + δi` with
`x ∈ [1 − δ, 1]`, write `τ − 1 = (x − 1) + δi` and use conjugation
symmetry `modularLambdaH_conj_symmetry` to relate to the bot_left
strip point `(1 − x) + δi`. By sub-lemma 6 applied to `(1 − x) + δi`,
`‖λ((1 − x) + δi) − 1‖` is small for `δ` small; hence
`‖λ(τ − 1) − 1‖` is small (conjugation preserves the bound).
The T-action identity `modularLambdaH_add_one_eq_div_sub_one`
(`λ(τ) = λ(τ − 1)/(λ(τ − 1) − 1)`) then gives `|λ(τ)|` large for
`λ(τ − 1)` close to 1, forcing `λ(τ) ≠ w`. -/
theorem modularLambdaH_F_Y_bot_right_strip_ne
    {w : ℂ} (_hw : 0 < w.im) :
    ∃ δ_w : ℝ, 0 < δ_w ∧ δ_w < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_w → ∀ x : ℝ,
      1 - δ ≤ x → x ≤ 1 →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0 := by
  -- Target: ‖λ(τ - 1) - 1‖ < 1/(‖w‖ + 2). Then |λ(τ)| ≥ ‖w‖ + 1 > ‖w‖, so λ(τ) ≠ w.
  set L : ℝ := Real.log (160000 * (‖w‖ + 2)) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_ge hx_le h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  -- Define τ' := (1 - x) + δi (in bot_left strip).
  set τ' : ℂ := ((1 - x : ℝ) : ℂ) + (δ : ℂ) * Complex.I with hτ'_def
  have hτ'_re : τ'.re = 1 - x := by
    simp [hτ'_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im : τ'.im = δ := by
    simp [hτ'_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im_pos : 0 < τ'.im := hτ'_im ▸ hδ_pos
  have hτ'_re_nn : 0 ≤ τ'.re := by rw [hτ'_re]; linarith
  have hτ'_re_le_δ : τ'.re ≤ δ := by rw [hτ'_re]; linarith
  -- σ := τ - 1.
  set σ : ℂ := τ - 1 with hσ_def
  have hσ_im : σ.im = δ := by simp [hσ_def, hτ_im]
  have hσ_im_pos : 0 < σ.im := hσ_im ▸ hδ_pos
  -- -conj σ = τ', so λ(τ') = conj(λ(σ)).
  have h_neg_conj_σ : -(starRingEnd ℂ σ) = τ' := by
    apply Complex.ext
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_re,
        Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_im,
        Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have h_conj_lam : modularLambdaH τ' = starRingEnd ℂ (modularLambdaH σ) := by
    rw [← h_neg_conj_σ]
    exact modularLambdaH_conj_symmetry hσ_im_pos
  -- Cusp-0 bound on τ' (in bot_left strip):
  -- For τ' = (1-x) + δi with (1-x) ∈ [0, δ] and δ ∈ (0, 1/4]:
  -- Compute Im(-1/τ'), apply norm bound, apply S-action identity.
  have h_x_sq_le_δ_sq : (1 - x)^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < (1 - x)^2 + δ^2 := by nlinarith
  have h_normSq_τ' : Complex.normSq τ' = (1 - x)^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ'_re, hτ'_im]; ring
  have h_im_inv_τ' : (-(τ' : ℂ)⁻¹).im = δ / ((1 - x)^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ'_im, h_normSq_τ']; ring
  have h_im_inv_τ'_ge : 1/(2*δ) ≤ (-(τ' : ℂ)⁻¹).im := by
    rw [h_im_inv_τ', div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_τ'_ge_one : 1 ≤ (-(τ' : ℂ)⁻¹).im := by linarith
  have h_norm_lam_inv_τ' : ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_τ'_ge_one
  have h_S_τ' : modularLambdaH τ' + modularLambdaH (-1/τ') = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ'_im_pos
  have h_neg_eq_τ' : -1/τ' = -τ'⁻¹ := by field_simp
  rw [h_neg_eq_τ'] at h_S_τ'
  have h_diff_τ' : modularLambdaH τ' - 1 = -modularLambdaH (-(τ' : ℂ)⁻¹) := by
    linear_combination h_S_τ'
  have h_norm_diff_τ' : ‖modularLambdaH τ' - 1‖ = ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ := by
    rw [h_diff_τ', norm_neg]
  have h_exp_mono_τ' : Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_τ'_ge]
  have h_bound_τ' : ‖modularLambdaH τ' - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff_τ']
    exact le_trans h_norm_lam_inv_τ' (mul_le_mul_of_nonneg_left h_exp_mono_τ' (by norm_num))
  -- M ≤ 1/(2δ), so π·M ≤ π/(2δ).
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_inv_2δ_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_inv_2δ_ge_pi_M
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  have h_w_norm_plus_two_pos : (0 : ℝ) < ‖w‖ + 2 := by
    have : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    linarith
  have h_exp_neg_L : Real.exp (-L) = 1 / (160000 * (‖w‖ + 2)) := by
    rw [hL_def]
    rw [show -Real.log (160000 * (‖w‖ + 2)) = Real.log ((160000 * (‖w‖ + 2))⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 * (‖w‖ + 2))⁻¹)]
    rw [one_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < 1 / (‖w‖ + 2) := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (1 / (160000 * (‖w‖ + 2))) := by rw [h_exp_neg_L]
      _ = 1 / (‖w‖ + 2) := by field_simp
  have h_strict_τ' : ‖modularLambdaH τ' - 1‖ < 1 / (‖w‖ + 2) :=
    lt_of_le_of_lt h_bound_τ' h_final_bound
  -- Transfer to σ via conjugation.
  have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH τ' - 1‖ := by
    rw [h_conj_lam]
    rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
      rw [map_sub, map_one]]
    rw [norm_conj]
  have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (‖w‖ + 2) := by
    rw [h_norm_diff_σ]; exact h_strict_τ'
  -- T-action: λ(τ) = λ(σ + 1) = λ(σ)/(λ(σ) - 1).
  have h_T : modularLambdaH (σ + 1) = modularLambdaH σ / (modularLambdaH σ - 1) :=
    modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
  have h_σ_plus_one : σ + 1 = τ := by simp [hσ_def]
  rw [h_σ_plus_one] at h_T
  -- λ(σ) - 1 ≠ 0 from λ(σ) ≠ 1.
  have h_lam_σ_sub_one_ne : modularLambdaH σ - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hσ_im_pos)
  -- |λ(σ)| ≥ 1 - ‖λ(σ) - 1‖.
  have h_lam_σ_norm_ge : 1 - ‖modularLambdaH σ - 1‖ ≤ ‖modularLambdaH σ‖ := by
    have h_rtri : ‖(1 : ℂ)‖ - ‖modularLambdaH σ‖ ≤ ‖(1 : ℂ) - modularLambdaH σ‖ :=
      norm_sub_norm_le (1 : ℂ) (modularLambdaH σ)
    have h_simp : (1 : ℂ) - modularLambdaH σ = -(modularLambdaH σ - 1) := by ring
    rw [norm_one, h_simp, norm_neg] at h_rtri
    linarith
  -- Now: |λ(τ)| = |λ(σ)| / |λ(σ) - 1|.
  have h_norm_lam_τ : ‖modularLambdaH τ‖ = ‖modularLambdaH σ‖ / ‖modularLambdaH σ - 1‖ := by
    rw [h_T, norm_div]
  -- We want |λ(τ)| > ‖w‖.
  -- |λ(σ)| ≥ 1 - c, |λ(σ) - 1| < 1/(‖w‖ + 2) where c = ‖λ(σ) - 1‖.
  -- |λ(σ)| / |λ(σ) - 1| ≥ (1 - c)/c > ‖w‖ + 1 > ‖w‖.
  set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
  have hc_lt : c < 1 / (‖w‖ + 2) := h_strict_σ
  have hc_pos : 0 < c := by
    rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
  have h_one_minus_c_pos : 0 < 1 - c := by
    have : c < 1 := by
      have h_inv_pos : (0 : ℝ) < 1 / (‖w‖ + 2) := by positivity
      have h_inv_lt_one : 1 / (‖w‖ + 2) ≤ 1 := by
        rw [div_le_iff₀ h_w_norm_plus_two_pos]; linarith [norm_nonneg w]
      linarith
    linarith
  have h_lam_σ_norm_pos : 0 < ‖modularLambdaH σ‖ := by linarith [h_lam_σ_norm_ge]
  -- (1 - c)/c > ‖w‖: equiv to (1 - c) > c·‖w‖, i.e., 1 > c·(‖w‖ + 1), i.e., c < 1/(‖w‖ + 1).
  have h_w_plus_one_pos : (0 : ℝ) < ‖w‖ + 1 := by linarith [norm_nonneg w]
  have hc_lt_inv : c < 1 / (‖w‖ + 1) := by
    calc c < 1 / (‖w‖ + 2) := hc_lt
      _ ≤ 1 / (‖w‖ + 1) := by
        apply one_div_le_one_div_of_le h_w_plus_one_pos
        linarith
  have h_c_w_plus_one_lt_one : c * (‖w‖ + 1) < 1 := by
    have := hc_lt_inv
    rw [lt_div_iff₀ h_w_plus_one_pos] at this
    linarith
  have h_norm_lam_τ_gt : ‖w‖ < ‖modularLambdaH τ‖ := by
    rw [h_norm_lam_τ]
    rw [lt_div_iff₀ hc_pos]
    calc ‖w‖ * c = c * ‖w‖ := by ring
      _ < c * ‖w‖ + (1 - c * (‖w‖ + 1)) := by linarith [h_c_w_plus_one_lt_one]
      _ = 1 - c := by ring
      _ ≤ ‖modularLambdaH σ‖ := h_lam_σ_norm_ge
  -- λ(τ) = w would give ‖λ(τ)‖ = ‖w‖. Contradiction.
  rw [h_lam_eq] at h_norm_lam_τ_gt
  exact lt_irrefl _ h_norm_lam_τ_gt

/-! ### Lipschitz infrastructure for sub-lemma 8

The shifted arc `|τ − (1/2 + δ·i)| = R₀` (for `R₀ > √(1/4 − δ²)`) lies
inside `F^o`, and is close to the F^o semicircle `|τ − 1/2| = 1/2` with
distance bounded by `O(δ)`. On the F^o semicircle, `λ` takes real
values. By continuity of `λ` on the open upper half-plane,
`|Im(λ(arc point))| ≤ M · O(δ)` where `M` is a Lipschitz constant for
`Im λ` on a compact neighborhood of the arc + semicircle.

The infrastructure below packages these helpers as separate lemmas. -/

/-- **Helper 8.1 — Arc-to-semicircle distance.** For arc point
`τ_arc(θ) = (1/2 + δ·i) + R₀·exp(iθ)` and `θ ∈ [0, π]`, there exists
a corresponding F^o semicircle point `τ_sc(θ) = 1/2 + (1/2)·exp(iθ)`
with `|τ_arc(θ) − τ_sc(θ)| ≤ δ + |R₀ − 1/2|`.

Proof: direct triangle inequality:
`τ_arc(θ) − τ_sc(θ) = δ·i + (R₀ − 1/2)·exp(iθ)`,
so `|τ_arc − τ_sc| ≤ δ + |R₀ − 1/2|`. -/
theorem modularLambdaH_arc_to_semicircle_dist
    {δ R₀ : ℝ} (hδ : 0 < δ) (_hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (θ : ℝ) :
    ‖_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
        - _root_.circleMap (1/2 : ℂ) (1/2) θ‖ ≤ δ + (1/2 - R₀) := by
  -- circleMap c r θ = c + r * exp(θ·I).
  have h_diff_eq : _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
        - _root_.circleMap (1/2 : ℂ) (1/2) θ
      = (δ : ℂ) * Complex.I + (R₀ - 1/2 : ℝ) * Complex.exp (θ * Complex.I) := by
    unfold circleMap
    push_cast
    ring
  rw [h_diff_eq]
  refine le_trans (norm_add_le _ _) ?_
  have h_norm_δi : ‖(δ : ℂ) * Complex.I‖ = δ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
  have h_norm_R₀_exp : ‖((R₀ - 1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖
      = 1/2 - R₀ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith : (R₀ - 1/2 : ℝ) < 0)]
    linarith
  rw [h_norm_δi, h_norm_R₀_exp]

/-- **Helper 8.2 — Im(λ) is locally Lipschitz on the upper half-plane.**
On any closed ball `closedBall τ₀ r` contained in `{Im > 0}`, `Im ∘ λ`
satisfies a Lipschitz bound with constant `M_τ₀_r` (computable from
the supremum of `‖λ'‖` over the ball, which is finite by analyticity
of `λ` on the open upper half-plane).

This is a standard analytic fact (analytic function on a compact
subset of its domain has bounded derivative, hence is Lipschitz). -/
theorem modularLambdaH_im_lipschitz_on_compact
    {τ₀ : ℂ} (_hτ₀ : 0 < τ₀.im) {r : ℝ} (hr : 0 < r)
    (h_ball_in : Metric.closedBall τ₀ r ⊆ {z : ℂ | 0 < z.im}) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ τ' : ℂ,
      τ ∈ Metric.closedBall τ₀ r → τ' ∈ Metric.closedBall τ₀ r →
      |(modularLambdaH τ).im - (modularLambdaH τ').im| ≤ M * ‖τ - τ'‖ := by
  -- Step 1: Open upper half-plane is open.
  have h_open_H : IsOpen ({z : ℂ | 0 < z.im} : Set ℂ) := by
    have h_set_eq : ({z : ℂ | 0 < z.im} : Set ℂ) = Complex.im ⁻¹' Set.Ioi 0 := by
      ext; simp
    rw [h_set_eq]
    exact isOpen_Ioi.preimage Complex.continuous_im
  -- Step 2: From `closedBall τ₀ r ⊆ {Im > 0}`, the minimum imaginary part is
  -- `τ₀.im - r`. Take a slightly larger open ball that still lies in `{Im > 0}`.
  have h_τ₀_minus_r_pos : 0 < τ₀.im - r := by
    have h_min : ((τ₀ - (r : ℂ) * Complex.I)).im = τ₀.im - r := by
      simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have h_in : τ₀ - (r : ℂ) * Complex.I ∈ Metric.closedBall τ₀ r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h_diff : τ₀ - (r : ℂ) * Complex.I - τ₀ = -((r : ℂ) * Complex.I) := by ring
      rw [h_diff, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
    have h_im_pos : 0 < (τ₀ - (r : ℂ) * Complex.I).im := h_ball_in h_in
    rw [h_min] at h_im_pos
    exact h_im_pos
  set r' : ℝ := (r + τ₀.im) / 2 with hr'_def
  have hr'_pos : 0 < r' := by rw [hr'_def]; linarith
  have hr_lt_r' : r < r' := by rw [hr'_def]; linarith
  have hr'_lt_τ₀_im : r' < τ₀.im := by rw [hr'_def]; linarith
  -- Both `ball τ₀ r'` and `closedBall τ₀ r'` are contained in `{Im > 0}`,
  -- since for any x in either, `|τ₀.im − x.im| ≤ r' < τ₀.im`, so `x.im > 0`.
  have h_ball'_closed_in : Metric.closedBall τ₀ r' ⊆ ({z : ℂ | 0 < z.im} : Set ℂ) := by
    intro x hx_ball
    rw [Metric.mem_closedBall, dist_eq_norm] at hx_ball
    have h_im_diff : |x.im - τ₀.im| ≤ ‖x - τ₀‖ := by
      have := abs_im_le_norm (x - τ₀)
      rwa [Complex.sub_im] at this
    have h_lower : τ₀.im - x.im ≤ |x.im - τ₀.im| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have : τ₀.im - x.im ≤ r' := le_trans (le_trans h_lower h_im_diff) hx_ball
    change 0 < x.im
    linarith
  have h_ball'_in : Metric.ball τ₀ r' ⊆ ({z : ℂ | 0 < z.im} : Set ℂ) :=
    (Metric.ball_subset_closedBall).trans h_ball'_closed_in
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH {z : ℂ | 0 < z.im} :=
    modularLambdaH_differentiableOn.analyticOnNhd h_open_H
  have h_deriv_cont_uhp : ContinuousOn (deriv modularLambdaH) {z : ℂ | 0 < z.im} :=
    h_lam_an.deriv.continuousOn
  -- Step 4: Bound `‖deriv λ‖` on closedBall τ₀ r' via compactness.
  have h_compact' : IsCompact (Metric.closedBall τ₀ r') := isCompact_closedBall τ₀ r'
  have h_ne' : (Metric.closedBall τ₀ r').Nonempty :=
    ⟨τ₀, Metric.mem_closedBall_self hr'_pos.le⟩
  have h_deriv_cont' : ContinuousOn (deriv modularLambdaH) (Metric.closedBall τ₀ r') :=
    h_deriv_cont_uhp.mono h_ball'_closed_in
  obtain ⟨τ_max, _hτ_max_in, hτ_max_le⟩ :=
    h_compact'.exists_isMaxOn h_ne' h_deriv_cont'.norm
  set M : ℝ := ‖deriv modularLambdaH τ_max‖ + 1 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; positivity
  have h_deriv_bound : ∀ x ∈ Metric.closedBall τ₀ r', ‖deriv modularLambdaH x‖ ≤ M := by
    intro x hx
    have h_max : ‖deriv modularLambdaH x‖ ≤ ‖deriv modularLambdaH τ_max‖ :=
      hτ_max_le hx
    rw [hM_def]; linarith
  refine ⟨M, hM_pos, ?_⟩
  intro τ τ' hτ_in hτ'_in
  -- τ, τ' ∈ closedBall τ₀ r ⊆ ball τ₀ r'.
  have hτ_in' : τ ∈ Metric.ball τ₀ r' := by
    rw [Metric.mem_closedBall] at hτ_in
    rw [Metric.mem_ball]
    linarith
  have hτ'_in' : τ' ∈ Metric.ball τ₀ r' := by
    rw [Metric.mem_closedBall] at hτ'_in
    rw [Metric.mem_ball]
    linarith
  -- Step 5: λ is ℂ-differentiable on `ball τ₀ r'` (open ⊆ UHP).
  have h_ball'_open : IsOpen (Metric.ball τ₀ r') := Metric.isOpen_ball
  have h_diff_ℂ_on_ball' : DifferentiableOn ℂ modularLambdaH (Metric.ball τ₀ r') :=
    modularLambdaH_differentiableOn.mono (h_ball'_in.trans (fun _ h => h))
  -- Step 6: UniqueDiffOn ℂ for the open ball.
  have h_unique_diff_ℂ : UniqueDiffOn ℂ (Metric.ball τ₀ r') :=
    h_ball'_open.uniqueDiffOn
  -- Step 7: Bound `‖fderivWithin ℂ λ s x‖` on the open ball, via
  --   `fderivWithin = fderiv` (open set), then `‖fderiv ℂ λ‖ = ‖deriv λ‖`.
  have h_convex_ball' : Convex ℝ (Metric.ball τ₀ r') := convex_ball _ _
  have h_fderiv_bound_ball' : ∀ x ∈ Metric.ball τ₀ r',
      ‖fderivWithin ℂ modularLambdaH (Metric.ball τ₀ r') x‖ ≤ M := by
    intro x hx
    have hx_uhp : x ∈ ({z : ℂ | 0 < z.im} : Set ℂ) := h_ball'_in hx
    have h_diff_ℂ_at : DifferentiableAt ℂ modularLambdaH x :=
      (h_lam_an x hx_uhp).differentiableAt
    rw [h_diff_ℂ_at.fderivWithin (h_unique_diff_ℂ x hx), ← norm_deriv_eq_norm_fderiv]
    have hx_closed : x ∈ Metric.closedBall τ₀ r' := Metric.ball_subset_closedBall hx
    exact h_deriv_bound x hx_closed
  -- Step 8: Apply MVT (𝕜 = ℂ) on the open ball.
  have h_mvt : ‖modularLambdaH τ - modularLambdaH τ'‖ ≤ M * ‖τ - τ'‖ :=
    h_convex_ball'.norm_image_sub_le_of_norm_fderivWithin_le
      h_diff_ℂ_on_ball' h_fderiv_bound_ball' hτ'_in' hτ_in'
  -- Step 9: |Im (a - b)| ≤ ‖a - b‖.
  have h_im_bound : |(modularLambdaH τ).im - (modularLambdaH τ').im| ≤
      ‖modularLambdaH τ - modularLambdaH τ'‖ := by
    have h_le := abs_im_le_norm (modularLambdaH τ - modularLambdaH τ')
    rwa [Complex.sub_im] at h_le
  linarith

/-- **Helper 8.3.a — Lipschitz ball lies in the upper half-plane.**
The closed ball `closedBall ((1/2 : ℂ) + i/(2 sin θ_0)) ((1 + cos θ_0)/
(4 sin θ_0))` (used in Helper 8.3) is contained in `{Im > 0}`. -/
theorem modularLambdaH_arc_lipschitz_ball_in_uhp
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2) :
    Metric.closedBall ((1/2 : ℂ) +
        Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))
        ((1 + Real.cos θ_0) / (4 * Real.sin θ_0)) ⊆
      ({z : ℂ | 0 < z.im} : Set ℂ) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have hc_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt⟩
  have hs_le_one : Real.sin θ_0 ≤ 1 := Real.sin_le_one θ_0
  have hc_le_one : Real.cos θ_0 ≤ 1 := Real.cos_le_one θ_0
  have hsc_sq : Real.sin θ_0 ^ 2 + Real.cos θ_0 ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq θ_0
  have hc_lt_one : Real.cos θ_0 < 1 := by
    nlinarith [hsc_sq, sq_nonneg (Real.sin θ_0), hs_pos]
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  -- The center has Im = 1/(2 sin θ_0).
  have hτ_K_im : ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im =
      1 / (2 * Real.sin θ_0) := by
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by
      rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  -- The radius is < center's Im, so the ball is in UHP.
  have hr_K_lt : (1 + Real.cos θ_0) / (4 * Real.sin θ_0) <
      1 / (2 * Real.sin θ_0) := by
    rw [div_lt_div_iff₀ h_4s_pos h_2s_pos]
    nlinarith [hc_lt_one, hs_pos]
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h_im_le : |x.im -
      ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im| ≤
      ‖x - ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))‖ := by
    have := abs_im_le_norm (x -
      ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)))
    rwa [Complex.sub_im] at this
  have h_lower : ((1/2 : ℂ) +
      Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im - x.im ≤
      |x.im - ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have h_diff_le : ((1/2 : ℂ) +
      Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im - x.im ≤
      (1 + Real.cos θ_0) / (4 * Real.sin θ_0) :=
    le_trans (le_trans h_lower h_im_le) hx
  change 0 < x.im
  rw [hτ_K_im] at h_diff_le
  linarith [hr_K_lt]

/-- **Helper 8.3.b — Semicircle point lies in the Lipschitz ball.**
For `θ ∈ [θ_0, π − θ_0]`, the F^o semicircle point
`circleMap (1/2) (1/2) θ` is contained in the closed ball used by
Helper 8.3. -/
theorem modularLambdaH_arc_lipschitz_semi_in_ball
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2)
    {θ : ℝ} (hθ_lo : θ_0 ≤ θ) (hθ_hi : θ ≤ Real.pi - θ_0) :
    _root_.circleMap (1/2 : ℂ) (1/2) θ ∈
      Metric.closedBall ((1/2 : ℂ) +
        Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))
        ((1 + Real.cos θ_0) / (4 * Real.sin θ_0)) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have hc_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt⟩
  have hs_le_one : Real.sin θ_0 ≤ 1 := Real.sin_le_one θ_0
  have hc_le_one : Real.cos θ_0 ≤ 1 := Real.cos_le_one θ_0
  have hsc_sq : Real.sin θ_0 ^ 2 + Real.cos θ_0 ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq θ_0
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  have h_16s2_pos : 0 < 16 * Real.sin θ_0 ^ 2 := by positivity
  have h_4s2_pos : 0 < 4 * Real.sin θ_0 ^ 2 := by positivity
  -- sin θ ≥ sin θ_0 for θ ∈ [θ_0, π - θ_0].
  have hθ_pos : 0 < θ := lt_of_lt_of_le hθ_0_pos hθ_lo
  have hθ_lt_pi : θ < Real.pi := by linarith
  have hθ_sin_lo : Real.sin θ_0 ≤ Real.sin θ := by
    by_cases h : θ ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hθ_lo
    · push Not at h
      have h_pi_sub_lo : θ_0 ≤ Real.pi - θ := by linarith
      have h_pi_sub_hi : Real.pi - θ ≤ Real.pi / 2 := by linarith
      have h_sym : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
      rw [h_sym]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h_pi_sub_hi h_pi_sub_lo
  have hθ_sq_sum : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  -- Compute distance² = (cos θ / 2)² + (sin θ / 2 - 1/(2s))².
  rw [Metric.mem_closedBall, dist_eq_norm]
  -- Use sq_le_sq' or sqrt_le_sqrt argument.
  set semi : ℂ := _root_.circleMap (1/2 : ℂ) (1/2) θ with hsemi_def
  set τ_K : ℂ := (1/2 : ℂ) +
    Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ) with hτ_K_def
  set r_K : ℝ := (1 + Real.cos θ_0) / (4 * Real.sin θ_0) with hr_K_def
  have hr_K_nn : 0 ≤ r_K := by
    rw [hr_K_def]; positivity
  -- semi.re and semi.im.
  have hsemi_re : semi.re = 1/2 + (1/2) * Real.cos θ := by
    rw [hsemi_def, _root_.circleMap]
    simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  have hsemi_im : semi.im = (1/2) * Real.sin θ := by
    rw [hsemi_def, _root_.circleMap]
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  -- τ_K.re and τ_K.im.
  have hτ_K_re : τ_K.re = 1/2 := by
    rw [hτ_K_def]
    have h_half_re : ((1 : ℂ) / 2).re = 1/2 := by rw [Complex.div_re]; simp
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_re]
    ring
  have hτ_K_im : τ_K.im = 1 / (2 * Real.sin θ_0) := by
    rw [hτ_K_def]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  -- Difference.
  have h_sub_re : (semi - τ_K).re = (1/2) * Real.cos θ := by
    rw [Complex.sub_re, hsemi_re, hτ_K_re]; ring
  have h_sub_im : (semi - τ_K).im = (1/2) * Real.sin θ - 1 / (2 * Real.sin θ_0) := by
    rw [Complex.sub_im, hsemi_im, hτ_K_im]
  -- Squared norm.
  have h_normSq_eq : ‖semi - τ_K‖ ^ 2 = ((1/2) * Real.cos θ) ^ 2 +
      ((1/2) * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h_sub_re, h_sub_im]
    ring
  -- The bound: ((1/2) cos θ)² + ((1/2) sin θ - 1/(2 sin θ_0))² ≤ r_K².
  have h_bound : ‖semi - τ_K‖ ^ 2 ≤ r_K ^ 2 := by
    rw [h_normSq_eq, hr_K_def, div_pow]
    have h_denom : (4 * Real.sin θ_0) ^ 2 = 16 * Real.sin θ_0 ^ 2 := by ring
    rw [h_denom]
    rw [le_div_iff₀ h_16s2_pos]
    -- Goal: (cos²θ/4 + (sin θ/2 - 1/(2 s))²) * (16 s²) ≤ (1+c)²
    have h_expand : (((1/2) * Real.cos θ) ^ 2 +
        ((1/2) * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2) *
        (16 * Real.sin θ_0 ^ 2) =
        4 * Real.sin θ_0 ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) -
        8 * Real.sin θ_0 * Real.sin θ + 4 := by
      field_simp
      ring
    rw [h_expand, add_comm (Real.cos θ ^ 2) _, hθ_sq_sum, mul_one]
    -- Goal: 4 s² - 8 s sin θ + 4 ≤ (1+c)²
    -- Using sin θ ≥ s: 8 s sin θ ≥ 8 s².
    -- 4 s² - 8 s² + 4 = -4 s² + 4 = 4(1 - s²) = 4 c².
    -- Need 4 c² ≤ (1+c)² i.e., (1-c)(1+3c) ≥ 0.
    have h_step1 : 4 * Real.sin θ_0 ^ 2 - 8 * Real.sin θ_0 * Real.sin θ + 4 ≤
        4 * Real.sin θ_0 ^ 2 - 8 * Real.sin θ_0 * Real.sin θ_0 + 4 := by
      have h_mul_le : 8 * Real.sin θ_0 * Real.sin θ_0 ≤
          8 * Real.sin θ_0 * Real.sin θ := by
        have h_8s_pos : 0 < 8 * Real.sin θ_0 := by linarith
        exact mul_le_mul_of_nonneg_left hθ_sin_lo h_8s_pos.le
      linarith
    apply le_trans h_step1
    -- Goal: 4 s² - 8 s² + 4 ≤ (1+c)²
    -- = -4 s² + 4 = 4(1 - s²) = 4 c². Need 4 c² ≤ (1+c)².
    nlinarith [hsc_sq, hc_pos, hc_le_one, sq_nonneg (1 - Real.cos θ_0),
               sq_nonneg (Real.cos θ_0)]
  -- Take square roots.
  have h_sqrt := Real.sqrt_le_sqrt h_bound
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hr_K_nn] at h_sqrt
  exact h_sqrt

/-- **Helper 8.3.c.aux — Pure polynomial inequality used by Helper 8.3.c.**
For `s, c ∈ [0, 1]` with `s² + c² = 1` and `δ ∈ (0, s/4]`:
`16 s⁴ δ² + 4 c² (1 − 2sδ)² ≤ (1 + c)²`. The proof reduces to two
bounds (`16 s⁴ δ² ≤ s⁶ = (1-c²)³` and `4 c² (1-2sδ)² ≤ 4c²`) and the
polynomial inequality `(1-c²)³ + 4c² ≤ (1+c)²`. -/
theorem modularLambdaH_arc_lipschitz_poly_ineq
    {s c δ : ℝ} (hs_pos : 0 < s) (hs_le_one : s ≤ 1)
    (hc_pos : 0 < c) (hc_le_one : c ≤ 1) (hsc_sq : s ^ 2 + c ^ 2 = 1)
    (hδ : 0 < δ) (hδ_small : δ ≤ s / 4) :
    16 * s ^ 4 * δ ^ 2 + 4 * c ^ 2 * (1 - 2 * s * δ) ^ 2 ≤ (1 + c) ^ 2 := by
  -- 16 s⁴ δ² ≤ s⁶ (since δ ≤ s/4 gives δ² ≤ s²/16).
  have h_first_le : 16 * s ^ 4 * δ ^ 2 ≤ s ^ 6 := by
    have h_4δ_le_s : 4 * δ ≤ s := by linarith [hδ_small]
    have h_sq_bound : 16 * δ ^ 2 ≤ s ^ 2 := by
      nlinarith [h_4δ_le_s, hδ, hs_pos]
    have h_s6_eq : s ^ 6 = s ^ 4 * s ^ 2 := by ring
    rw [h_s6_eq]
    have h_s4_nn : 0 ≤ s ^ 4 := by positivity
    nlinarith [h_sq_bound, h_s4_nn]
  -- 4 c² (1 - 2sδ)² ≤ 4 c² (since 0 ≤ 1 - 2sδ ≤ 1, so (1-2sδ)² ≤ 1).
  have h_2sδ_nn : 0 ≤ 1 - 2 * s * δ := by
    nlinarith [hs_le_one, hδ_small, hs_pos]
  have h_2sδ_le_one : 1 - 2 * s * δ ≤ 1 := by nlinarith [hs_pos, hδ]
  have h_sq_le_one : (1 - 2 * s * δ) ^ 2 ≤ 1 := by
    nlinarith [h_2sδ_nn, h_2sδ_le_one]
  have h_second_le : 4 * c ^ 2 * (1 - 2 * s * δ) ^ 2 ≤ 4 * c ^ 2 := by
    nlinarith [sq_nonneg c, h_sq_le_one, hc_pos]
  -- s⁶ = (1 - c²)³.
  have h_s6_eq : s ^ 6 = (1 - c ^ 2) ^ 3 := by
    have hs_sq_eq : s ^ 2 = 1 - c ^ 2 := by linarith [hsc_sq]
    have : s ^ 6 = (s ^ 2) ^ 3 := by ring
    rw [this, hs_sq_eq]
  have h_LHS_le : 16 * s ^ 4 * δ ^ 2 + 4 * c ^ 2 * (1 - 2 * s * δ) ^ 2 ≤
      (1 - c ^ 2) ^ 3 + 4 * c ^ 2 := by
    linarith [h_first_le, h_second_le, h_s6_eq]
  apply le_trans h_LHS_le
  -- Polynomial inequality: (1 - c²)³ + 4 c² ≤ (1+c)² for c ∈ [0, 1].
  -- Reduces to (1-c)²(1+c)³ ≤ 1 + 3c, i.e., c(2 + 2c + 2c² - c³ - c⁴) ≥ 0.
  nlinarith [hc_pos, hc_le_one, sq_nonneg c, sq_nonneg (1 - c),
             sq_nonneg (1 + c), mul_nonneg hc_pos.le hc_pos.le,
             mul_nonneg (sq_nonneg c) (sq_nonneg (1 - c)),
             mul_nonneg (sq_nonneg (1 - c)) (sq_nonneg (1 - c))]

set_option maxHeartbeats 400000 in
-- nlinarith chain over the arc-ball geometry exceeds the default 200000 budget.
/-- **Helper 8.3.c — Arc point lies in the Lipschitz ball.**
For F^o arc parameters with `R₀ > √(1/4 − δ²)`, `R₀ < 1/2`, and
`δ ≤ sin θ_0 / 4`, the arc point
`circleMap (1/2 + δi) R₀ θ` lies in the closed ball used by Helper 8.3
for any `θ ∈ [θ_0, π − θ_0]`. The lower bound on `R₀` is essential:
the geometric argument shows
`|arc(θ) − τ_K|² ≤ (sδ)² + (1/(2s) − δ)² cos² θ_0`, which is sharp
because `R₀ > 1/2 − s δ` (a strict consequence of `R₀ > √(1/4 − δ²)`
when `δ ≤ s/4`). -/
theorem modularLambdaH_arc_lipschitz_arc_in_ball
    {δ R₀ : ℝ} (hδ : 0 < δ)
    (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀) (hR₀_lt : R₀ < 1 / 2)
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2)
    (hδ_small : δ ≤ Real.sin θ_0 / 4)
    {θ : ℝ} (hθ_lo : θ_0 ≤ θ) (hθ_hi : θ ≤ Real.pi - θ_0) :
    _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ ∈
      Metric.closedBall ((1/2 : ℂ) +
        Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))
        ((1 + Real.cos θ_0) / (4 * Real.sin θ_0)) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have hc_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt⟩
  have hs_le_one : Real.sin θ_0 ≤ 1 := Real.sin_le_one θ_0
  have hc_le_one : Real.cos θ_0 ≤ 1 := Real.cos_le_one θ_0
  have hsc_sq : Real.sin θ_0 ^ 2 + Real.cos θ_0 ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq θ_0
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  have h_16s2_pos : 0 < 16 * Real.sin θ_0 ^ 2 := by positivity
  -- Useful arithmetic: δ ≤ 1/4 (since δ ≤ s/4 ≤ 1/4).
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    have : δ ≤ Real.sin θ_0 / 4 := hδ_small
    linarith [hs_le_one]
  -- 2 s δ ≤ 1/2, so 1 - 2 s δ ≥ 1/2 > 0.
  have h_2sδ_le_half : 2 * Real.sin θ_0 * δ ≤ 1 / 2 := by
    nlinarith [hs_le_one, hδ_le_quarter]
  -- R₀ > 1/2 - s δ. Key reduction via R₀ > √(1/4 - δ²).
  have h_half_sub_sδ_pos : 0 < 1 / 2 - Real.sin θ_0 * δ := by
    nlinarith [hs_le_one, hδ_le_quarter]
  have h_arg_nn : (0 : ℝ) ≤ 1 / 4 - δ ^ 2 := by nlinarith [hδ_le_quarter]
  have h_sqrt_gt_us : 1 / 2 - Real.sin θ_0 * δ < Real.sqrt (1 / 4 - δ ^ 2) := by
    have h_diff_pos : (1 / 2 - Real.sin θ_0 * δ) ^ 2 < 1 / 4 - δ ^ 2 := by
      nlinarith [hδ_small, hs_pos, hs_le_one, sq_nonneg (Real.sin θ_0),
                 sq_nonneg δ, mul_pos hs_pos hδ]
    calc 1 / 2 - Real.sin θ_0 * δ
        = Real.sqrt ((1 / 2 - Real.sin θ_0 * δ) ^ 2) := by
          rw [Real.sqrt_sq h_half_sub_sδ_pos.le]
      _ < Real.sqrt (1 / 4 - δ ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) h_diff_pos
  have hR₀_gt_us : 1 / 2 - Real.sin θ_0 * δ < R₀ :=
    lt_trans h_sqrt_gt_us hR₀_lo
  -- sin θ ≥ sin θ_0 for θ ∈ [θ_0, π - θ_0].
  have hθ_pos : 0 < θ := lt_of_lt_of_le hθ_0_pos hθ_lo
  have hθ_lt_pi : θ < Real.pi := by linarith
  have hθ_sin_lo : Real.sin θ_0 ≤ Real.sin θ := by
    by_cases h : θ ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hθ_lo
    · push Not at h
      have h_sym : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
      rw [h_sym]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
        (by linarith)
  have hθ_sq_sum : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  -- Set up.
  rw [Metric.mem_closedBall, dist_eq_norm]
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  set τ_K : ℂ := (1/2 : ℂ) +
    Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ) with hτ_K_def
  set r_K : ℝ := (1 + Real.cos θ_0) / (4 * Real.sin θ_0) with hr_K_def
  have hr_K_nn : 0 ≤ r_K := by rw [hr_K_def]; positivity
  -- arc.re and arc.im.
  have harc_re : arc.re = 1/2 + R₀ * Real.cos θ := by
    rw [harc_def, _root_.circleMap]
    simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have harc_im : arc.im = δ + R₀ * Real.sin θ := by
    rw [harc_def, _root_.circleMap]
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  -- τ_K.re and τ_K.im.
  have hτ_K_re : τ_K.re = 1/2 := by
    rw [hτ_K_def]
    have h_half_re : ((1 : ℂ) / 2).re = 1/2 := by rw [Complex.div_re]; simp
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_re]
    ring
  have hτ_K_im : τ_K.im = 1 / (2 * Real.sin θ_0) := by
    rw [hτ_K_def]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  -- Difference.
  have h_sub_re : (arc - τ_K).re = R₀ * Real.cos θ := by
    rw [Complex.sub_re, harc_re, hτ_K_re]; ring
  have h_sub_im : (arc - τ_K).im = δ + R₀ * Real.sin θ - 1 / (2 * Real.sin θ_0) := by
    rw [Complex.sub_im, harc_im, hτ_K_im]
  -- Squared norm.
  have h_normSq_eq : ‖arc - τ_K‖ ^ 2 = (R₀ * Real.cos θ) ^ 2 +
      (δ + R₀ * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h_sub_re, h_sub_im]
    ring
  -- Bound: |arc - τ_K|² ≤ r_K².
  -- Strategy: use the algebraic identity
  --   (R₀ cos θ)² + (δ + R₀ sin θ - 1/(2s))²
  --   ≤ (R₀ - (1/2 - sδ))² + (1/(2s) - δ)² c²    (using sin θ ≥ s)
  --   ≤ (sδ)² + (1/(2s) - δ)² c²                  (using R₀ - (1/2-sδ) < sδ)
  --   ≤ ((1+c)/(4s))² = r_K²                       (polynomial inequality)
  have h_bound : ‖arc - τ_K‖ ^ 2 ≤ r_K ^ 2 := by
    rw [h_normSq_eq]
    -- Step A: LHS = R₀² - 2 R₀ (1/(2s) - δ) sin θ + (1/(2s) - δ)²
    have h_step_A_eq : (R₀ * Real.cos θ) ^ 2 +
        (δ + R₀ * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2 =
        R₀ ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) -
        2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ +
        (1 / (2 * Real.sin θ_0) - δ) ^ 2 := by ring
    rw [h_step_A_eq, add_comm (Real.cos θ ^ 2) _, hθ_sq_sum, mul_one]
    -- Now goal: R₀² - 2 R₀ u sin θ + u² ≤ r_K²  where u := 1/(2s) - δ.
    -- Step B: replace sin θ by s (since coefficient of sin θ is negative).
    have h_u_pos : 0 < 1 / (2 * Real.sin θ_0) - δ := by
      have h_one_2s_ge : 1 / (2 * Real.sin θ_0) ≥ 1 / 2 := by
        rw [ge_iff_le, le_div_iff₀ h_2s_pos]
        nlinarith [hs_le_one, hs_pos]
      linarith [hs_le_one, hs_pos, hδ_small,
                show Real.sin θ_0 / 4 ≤ 1 / 4 from by linarith]
    have hR₀_pos : 0 < R₀ := by
      have h_sqrt_nn : 0 ≤ Real.sqrt (1 / 4 - δ ^ 2) := Real.sqrt_nonneg _
      linarith
    have h_factor_pos : 0 < 2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) := by positivity
    have h_step_B :
        R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 ≤
        R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 := by
      have h_mul_le :
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 ≤
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ :=
        mul_le_mul_of_nonneg_left hθ_sin_lo h_factor_pos.le
      linarith
    apply le_trans h_step_B
    -- Step C: identity R₀² - 2 R₀ u s + u² = (R₀ - us)² + u² c²
    have h_step_C_eq :
        R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 =
        (R₀ - Real.sin θ_0 * (1 / (2 * Real.sin θ_0) - δ)) ^ 2 +
        (1 / (2 * Real.sin θ_0) - δ) ^ 2 * Real.cos θ_0 ^ 2 := by
      have hs_sq_sub : 1 - Real.sin θ_0 ^ 2 = Real.cos θ_0 ^ 2 := by linarith [hsc_sq]
      have h_eq : R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 =
          (R₀ - Real.sin θ_0 * (1 / (2 * Real.sin θ_0) - δ)) ^ 2 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 * (1 - Real.sin θ_0 ^ 2) := by ring
      rw [h_eq, hs_sq_sub]
    rw [h_step_C_eq]
    -- Step D: simplify s·(1/(2s) - δ) = 1/2 - sδ.
    have h_us_eq : Real.sin θ_0 * (1 / (2 * Real.sin θ_0) - δ) =
        1 / 2 - Real.sin θ_0 * δ := by
      field_simp
    rw [h_us_eq]
    -- Step E: (R₀ - (1/2 - sδ))² ≤ (sδ)² (key R₀ bound).
    have h_R₀_diff_pos : 0 < R₀ - (1 / 2 - Real.sin θ_0 * δ) := by linarith
    have h_R₀_diff_lt : R₀ - (1 / 2 - Real.sin θ_0 * δ) < Real.sin θ_0 * δ := by linarith
    have h_R₀_sq_le : (R₀ - (1 / 2 - Real.sin θ_0 * δ)) ^ 2 ≤
        (Real.sin θ_0 * δ) ^ 2 := by
      nlinarith [h_R₀_diff_pos, h_R₀_diff_lt, sq_nonneg (Real.sin θ_0 * δ)]
    have h_step_D :
        (R₀ - (1 / 2 - Real.sin θ_0 * δ)) ^ 2 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 * Real.cos θ_0 ^ 2 ≤
        (Real.sin θ_0 * δ) ^ 2 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 * Real.cos θ_0 ^ 2 := by
      linarith [h_R₀_sq_le]
    apply le_trans h_step_D
    -- Step F: (sδ)² + (1/(2s) - δ)² c² ≤ r_K² = ((1+c)/(4s))².
    -- Reformulate the bound using `1/(2s) - δ = (1 - 2sδ)/(2s)`.
    have h_u_rewrite : 1 / (2 * Real.sin θ_0) - δ =
        (1 - 2 * Real.sin θ_0 * δ) / (2 * Real.sin θ_0) := by
      field_simp
    rw [h_u_rewrite, hr_K_def]
    simp only [div_pow]
    have h_denom : (4 * Real.sin θ_0) ^ 2 = 16 * Real.sin θ_0 ^ 2 := by ring
    rw [h_denom, le_div_iff₀ h_16s2_pos]
    -- After substitution: ((sδ)² + (1 - 2sδ)²/(2s)² · c²) · 16 s² ≤ (1+c)²
    have h_normalize :
        ((Real.sin θ_0 * δ) ^ 2 +
          (1 - 2 * Real.sin θ_0 * δ) ^ 2 / (2 * Real.sin θ_0) ^ 2 *
            Real.cos θ_0 ^ 2) * (16 * Real.sin θ_0 ^ 2) =
        16 * Real.sin θ_0 ^ 4 * δ ^ 2 +
        4 * Real.cos θ_0 ^ 2 * (1 - 2 * Real.sin θ_0 * δ) ^ 2 := by
      field_simp
      ring
    rw [h_normalize]
    -- Apply the pure polynomial helper.
    exact modularLambdaH_arc_lipschitz_poly_ineq hs_pos hs_le_one hc_pos hc_le_one
      hsc_sq hδ hδ_small
  -- Take square roots.
  have h_sqrt := Real.sqrt_le_sqrt h_bound
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hr_K_nn] at h_sqrt
  exact h_sqrt

/-- **Helper 8.3 — Compact-set Lipschitz bound on the arc.**
For F^o arc parameters `(δ, R₀)` with `R₀ > √(1/4 − δ²)`, `R₀ < 1/2`,
`δ ≤ sin θ_0 / 4`, and `θ ∈ [θ_0, π − θ_0]` (away from the two cusps
by `θ_0`), the arc point `circleMap (1/2 + δi) R₀ θ` and the F^o
semicircle point `circleMap (1/2) (1/2) θ` both lie in the fixed
compact ball `closedBall (1/2 + i/(2 sin θ_0)) ((1 + cos θ_0)/
(4 sin θ_0))` contained in the upper half-plane (Helpers 8.3.a/b/c).
Apply Helper 8.2 to obtain a Lipschitz constant `M`, then chain with
Helper 8.1's distance bound to conclude.

The cusp endpoints (`θ ∈ [0, θ_0) ∪ (π − θ_0, π]`) are handled
separately in Sub-lemma 8 via cusp asymptotics. -/
theorem modularLambdaH_arc_lipschitz_away_from_cusps
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀_pos : 0 < R₀)
    (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀) (hR₀_lt : R₀ < 1 / 2)
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2)
    (hδ_small : δ ≤ Real.sin θ_0 / 4) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ : ℝ, θ_0 ≤ θ → θ ≤ Real.pi - θ_0 →
      |(modularLambdaH (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)).im|
        ≤ M * (δ + (1/2 - R₀)) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  -- The center τ_K = (1/2 : ℂ) + i/(2 sin θ_0) has positive Im.
  have hτ_K_im_pos : 0 < ((1/2 : ℂ) +
      Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im := by
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    have h_pos : 0 < 1 / (2 * Real.sin θ_0) := by positivity
    linarith
  have hr_K_pos : 0 < (1 + Real.cos θ_0) / (4 * Real.sin θ_0) := by
    have hc_nn : 0 ≤ Real.cos θ_0 :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ_0_lt.le⟩
    have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
    positivity
  -- Apply Helper 8.3.a: ball is in UHP.
  have h_ball_in := modularLambdaH_arc_lipschitz_ball_in_uhp hθ_0_pos hθ_0_lt
  -- Apply Helper 8.2: Lipschitz constant M.
  obtain ⟨M, hM_pos, hM_lipschitz⟩ :=
    modularLambdaH_im_lipschitz_on_compact hτ_K_im_pos hr_K_pos h_ball_in
  refine ⟨M, hM_pos, ?_⟩
  intro θ hθ_lo hθ_hi
  -- Apply Helpers 8.3.b and 8.3.c.
  have h_semi_in := modularLambdaH_arc_lipschitz_semi_in_ball hθ_0_pos hθ_0_lt hθ_lo hθ_hi
  have h_arc_in := modularLambdaH_arc_lipschitz_arc_in_ball hδ hR₀_lo hR₀_lt
    hθ_0_pos hθ_0_lt hδ_small hθ_lo hθ_hi
  -- semicircle point has positive Im (sin θ > 0).
  have hθ_pos : 0 < θ := lt_of_lt_of_le hθ_0_pos hθ_lo
  have hθ_lt_pi : θ < Real.pi := by linarith
  have hθ_sin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have h_semi_im_pos : 0 < (_root_.circleMap (1/2 : ℂ) (1/2) θ).im := by
    rw [_root_.circleMap]
    show 0 < ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)).im
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]
    have h_pos : 0 < (1 / 2 : ℝ) * Real.sin θ := by positivity
    linarith
  -- The point is on the semicircle: ‖2 · semi - 1‖ = 1.
  have h_semi_circle : ‖2 * (_root_.circleMap (1/2 : ℂ) (1/2) θ) - 1‖ = 1 := by
    rw [_root_.circleMap]
    have h_simplify : 2 * ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) *
        Complex.exp (θ * Complex.I)) - 1 = Complex.exp (θ * Complex.I) := by
      push_cast; ring
    rw [h_simplify, Complex.norm_exp]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  -- Im λ(semi) = 0 (semicircle real-valued).
  have h_semi_im_zero : (modularLambdaH (_root_.circleMap (1/2 : ℂ) (1/2) θ)).im = 0 :=
    modularLambdaH_semicircle_real h_semi_im_pos h_semi_circle
  -- Apply Helper 8.2 Lipschitz to arc and semicircle points.
  have h_lip := hM_lipschitz
    (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)
    (_root_.circleMap (1/2 : ℂ) (1/2) θ) h_arc_in h_semi_in
  rw [h_semi_im_zero, sub_zero] at h_lip
  -- Apply Helper 8.1: distance bound `δ + (1/2 - R₀)`.
  have h_dist := modularLambdaH_arc_to_semicircle_dist hδ hR₀_pos hR₀_lt θ
  -- Combine: |Im λ(arc)| ≤ M · ‖arc - semi‖ ≤ M · (δ + (1/2 - R₀)).
  calc |(modularLambdaH (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)).im|
      ≤ M * ‖_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ -
              _root_.circleMap (1/2 : ℂ) (1/2) θ‖ := h_lip
    _ ≤ M * (δ + (1/2 - R₀)) := by
        apply mul_le_mul_of_nonneg_left _ hM_pos.le
        convert h_dist using 1

/-- **Sub-lemma 8.aux — arc has positive imaginary part.** For
`δ > 0` and `θ ∈ [0, π]`, the arc point `circleMap (1/2 + δi) R₀ θ`
has `Im > 0`. -/
theorem modularLambdaH_F_Y_arc_im_pos
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀_nn : 0 ≤ R₀)
    {θ : ℝ} (hθ_lo : 0 ≤ θ) (hθ_hi : θ ≤ Real.pi) :
    0 < (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im := by
  rw [_root_.circleMap]
  simp only [Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, mul_zero,
    mul_one, zero_mul]
  have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
  rw [h_half_im]
  have h_sin_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ_lo, hθ_hi⟩
  have h_term : 0 ≤ R₀ * Real.sin θ := mul_nonneg hR₀_nn h_sin_nn
  linarith [hδ, h_term]

/-- **Sub-lemma 8.aux — squared norm of the arc.** Convenience lemma. -/
theorem modularLambdaH_F_Y_arc_normSq_eq
    (δ R₀ : ℝ) (θ : ℝ) :
    Complex.normSq (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) =
      (1/2 + R₀ * Real.cos θ)^2 + (δ + R₀ * Real.sin θ)^2 := by
  rw [_root_.circleMap, Complex.normSq_apply]
  have h_re : ((1/2 : ℂ) + (δ : ℂ) * Complex.I +
      (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re =
      1/2 + R₀ * Real.cos θ := by
    simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_im : ((1/2 : ℂ) + (δ : ℂ) * Complex.I +
      (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im =
      δ + R₀ * Real.sin θ := by
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [h_re, h_im]; ring

/-- **Sub-lemma 8.aux.aux — `η²/4 ≤ R₀ sin η` for the cusp range.**
Used to prove `arc.Re ≤ arc.Im` in the cusp 0 region. Combines Jordan's
inequality `sin η ≥ 2η/π` with `R₀ > 1/3` and `η ≤ 1/π`. -/
theorem modularLambdaH_F_Y_arc_eta_sq_le_R₀_sin
    {R₀ η : ℝ} (hR₀_gt : (1 : ℝ) / 3 < R₀) (hη_nn : 0 ≤ η)
    (hη_le_inv_pi : η ≤ 1 / Real.pi) (hη_le_pi_2 : η ≤ Real.pi / 2) :
    η ^ 2 / 4 ≤ R₀ * Real.sin η := by
  -- sin η ≥ 2η/π (Jordan's inequality on [0, π/2]).
  have h_sin_lower : (2 / Real.pi) * η ≤ Real.sin η :=
    Real.mul_le_sin hη_nn hη_le_pi_2
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_gt_three : 3 < Real.pi := Real.pi_gt_three
  -- R₀ sin η ≥ R₀ · (2η/π) ≥ (1/3) · (2η/π) = 2η/(3π).
  have h_R₀_sin_lower : (2 * η) / (3 * Real.pi) ≤ R₀ * Real.sin η := by
    have h1 : R₀ * ((2/Real.pi) * η) ≤ R₀ * Real.sin η := by
      have hR₀_pos : 0 < R₀ := by linarith
      exact mul_le_mul_of_nonneg_left h_sin_lower hR₀_pos.le
    have h2 : (1:ℝ)/3 * ((2/Real.pi) * η) ≤ R₀ * ((2/Real.pi) * η) := by
      have : 0 ≤ (2/Real.pi) * η := by positivity
      nlinarith [hR₀_gt, this]
    have h_eq : (1:ℝ)/3 * ((2/Real.pi) * η) = (2 * η) / (3 * Real.pi) := by
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
      ring
    linarith [h1, h2, h_eq]
  -- η²/4 ≤ 2η/(3π).
  -- Equivalent: η ≤ 8/(3π) (after dividing by η/4 for η > 0).
  -- We have η ≤ 1/π. And 1/π ≤ 8/(3π) iff 1 ≤ 8/3 iff 3 ≤ 8. ✓.
  have h_η_sq_le_target : η^2 / 4 ≤ (2 * η) / (3 * Real.pi) := by
    -- Show η/4 ≤ 2/(3π) via 3πη ≤ 3 ≤ 8.
    have h_πη_le_one : Real.pi * η ≤ 1 := by
      have h2 : Real.pi * η ≤ Real.pi * (1/Real.pi) :=
        mul_le_mul_of_nonneg_left hη_le_inv_pi h_pi_pos.le
      have h3 : Real.pi * (1/Real.pi) = 1 := by field_simp
      linarith
    have h_quart_le : η / 4 ≤ 2 / (3 * Real.pi) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by positivity : (0:ℝ) < 3 * Real.pi)]
      nlinarith [h_πη_le_one]
    have h_mul : η * (η/4) ≤ η * (2/(3 * Real.pi)) :=
      mul_le_mul_of_nonneg_left h_quart_le hη_nn
    have h_lhs : η * (η/4) = η^2 / 4 := by ring
    have h_rhs : η * (2/(3 * Real.pi)) = (2 * η) / (3 * Real.pi) := by ring
    linarith [h_mul, h_lhs, h_rhs]
  linarith [h_η_sq_le_target, h_R₀_sin_lower]

/-- **Sub-lemma 8.aux.aux — pure polynomial inequality.**
For `u ≥ 0`, `v > 0` with `u ≤ v` and `v ≤ 1/(2K)`, we have
`K · (u² + v²) ≤ v` (i.e., `K ≤ v/(u² + v²)`). Used to derive
`K ≤ Im(−1/arc)` from `arc.Re ≤ arc.Im` and `arc.Im ≤ 1/(2K)`. -/
theorem modularLambdaH_F_Y_arc_cusp_0_poly_bound
    {u v K : ℝ} (hu_nn : 0 ≤ u) (hv_pos : 0 < v)
    (hu_le_v : u ≤ v) (hv_upper : v ≤ 1 / (2 * K)) (hK_pos : 0 < K) :
    K * (u ^ 2 + v ^ 2) ≤ v := by
  -- u² ≤ v² (from u ≤ v and both ≥ 0).
  have hu_sq_le : u^2 ≤ v^2 := by nlinarith [hu_le_v, hu_nn, hv_pos.le]
  -- u² + v² ≤ 2v².
  have h_uv_sum : u^2 + v^2 ≤ 2 * v^2 := by linarith
  -- 2 K v ≤ 1.
  have h_2K_pos : 0 < 2 * K := by linarith
  have h_2Kv_le : 2 * K * v ≤ 1 := by
    have h1 : 2 * K * v ≤ 2 * K * (1/(2*K)) :=
      mul_le_mul_of_nonneg_left hv_upper (by linarith)
    have h2 : 2 * K * (1/(2*K)) = 1 := by
      field_simp
    linarith
  -- K · (u² + v²) ≤ K · 2v² = 2Kv · v ≤ 1 · v = v.
  nlinarith [h_uv_sum, hv_pos, h_2Kv_le, hK_pos, sq_nonneg v]

/-- **Sub-lemma 8.aux.aux — v ≤ 1/(2K) bound.**
For δ + R₀ sin η bounded above by `1/(2K)` when `δ, η ≤ 1/(4K)`. -/
theorem modularLambdaH_F_Y_arc_cusp_0_v_bound
    {δ R₀ η K : ℝ} (_hδ_nn : 0 ≤ δ) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hη_nn : 0 ≤ η) (h_sin_η_le_η : Real.sin η ≤ η)
    (hδ_le : δ ≤ 1 / (4 * K)) (hη_le : η ≤ 1 / (4 * K))
    (hK_pos : 0 < K) :
    δ + R₀ * Real.sin η ≤ 1 / (2 * K) := by
  have h_4K_pos : 0 < 4 * K := by linarith
  have h_2K_pos : 0 < 2 * K := by linarith
  have h_8K_pos : 0 < 8 * K := by linarith
  -- R₀ sin η ≤ (1/2) η.
  have h_R₀_sin_le : R₀ * Real.sin η ≤ (1/2) * η := by
    have h1 : R₀ * Real.sin η ≤ R₀ * η :=
      mul_le_mul_of_nonneg_left h_sin_η_le_η hR₀_pos.le
    nlinarith [h1, hR₀_lt.le, hη_nn]
  -- (1/2) · η ≤ (1/2) · 1/(4K) = 1/(8K).
  have h_η_half_le : (1/2) * η ≤ 1/(8*K) := by
    have h1 : (1/2) * η ≤ (1/2) * (1/(4*K)) :=
      mul_le_mul_of_nonneg_left hη_le (by norm_num)
    have h2 : (1:ℝ)/2 * (1/(4*K)) = 1/(8*K) := by
      have hK_ne : K ≠ 0 := ne_of_gt hK_pos
      field_simp
      ring
    linarith
  -- δ + R₀ sin η ≤ 1/(4K) + 1/(8K) = 3/(8K) ≤ 1/(2K).
  have h_sum : δ + R₀ * Real.sin η ≤ 1/(4*K) + 1/(8*K) := by
    linarith
  -- 1/(4K) + 1/(8K) ≤ 1/(2K). Equivalent to 1/(4K) ≤ 3/(8K), i.e., 2 ≤ 3 ✓.
  -- Or direct: 8K · (1/(4K)) + 8K · (1/(8K)) = 2 + 1 = 3 ≤ 4 = 8K · (1/(2K)).
  have h_chain : (1:ℝ)/(4*K) + 1/(8*K) ≤ 1/(2*K) := by
    rw [div_add_div _ _ (ne_of_gt h_4K_pos) (ne_of_gt h_8K_pos)]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (4*K) * (8*K)) h_2K_pos]
    ring_nf
    nlinarith [sq_nonneg K, hK_pos]
  linarith

set_option maxHeartbeats 400000 in
-- Cusp-0 helper combines five polynomial sub-helpers and arc-point
-- complex-arithmetic simp chains; exceeds the default 200000 budget.
/-- **Sub-lemma 8.aux — lower bound on `Im(−1/arc(θ))` in cusp region.**
Given any target `K > 0`, there exist parameters `δ_K, θ_K` (depending
on `K`) such that for `δ ≤ δ_K`, `R₀ ∈ (√(1/4 − δ²), 1/2)`, and
`θ ∈ [π − θ_K, π]`: `Im(−1/arc(θ)) ≥ K`. The cusp width `θ_K` shrinks
as `K` grows. Used to apply
`modularLambdaH_norm_le_exp_of_im_ge_one`.

Proof: take `δ_K := min(1/4, 1/(4K))`, `θ_K := min(1/π, 1/(4K))`.
Setting `η := π − θ ∈ [0, θ_K]` and `u := arc.Re, v := arc.Im`:
* `u ≤ 2δ² + η²/4` (from `R₀ > √(1/4 − δ²) > 1/2 − 2δ²` and
  `1 − cos η ≤ η²/2`).
* `R₀ > √(3/16) > 1/3` (from `δ ≤ 1/4`).
* `u ≤ v` (from `2δ² ≤ δ` for `δ ≤ 1/2` and `η²/4 ≤ R₀ sin η`
  via Jordan's `sin η ≥ 2η/π`, `R₀ > 1/3`, and `η ≤ 1/π < 8/(3π)`).
* `v ≤ 1/(2K)` (from `δ ≤ 1/(4K)`, `η ≤ 1/(4K)`).
* Then `u² + v² ≤ 2v²` so `Im(−1/arc) = v/(u² + v²) ≥ 1/(2v) ≥ K`. -/
theorem modularLambdaH_F_Y_arc_im_inv_lower_cusp_0
    (K : ℝ) (hK_pos : 0 < K) :
    ∃ δ_K θ_K : ℝ, 0 < δ_K ∧ δ_K ≤ 1 / 4 ∧
      0 < θ_K ∧ θ_K ≤ Real.pi / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_K →
    Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, Real.pi - θ_K ≤ θ → θ ≤ Real.pi →
      K ≤
        (-(_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)⁻¹).im := by
  -- Strategy: δ_K := min(1/4, 1/(4K)), θ_K := min(1/π, 1/(4K)).
  -- Show arc.Re ≤ arc.Im, hence |arc|² ≤ 2·arc.Im², hence Im(-1/arc) ≥ 1/(2·arc.Im).
  -- Combined with arc.Im ≤ 1/(2K), get Im(-1/arc) ≥ K.
  have h_4K_pos : 0 < 4 * K := by linarith
  have h_2K_pos : 0 < 2 * K := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_inv_pi_pos : 0 < (1:ℝ)/Real.pi := by positivity
  have h_pi_gt_three : 3 < Real.pi := Real.pi_gt_three
  have h_inv_pi_le_pi_4 : (1:ℝ)/Real.pi ≤ Real.pi/4 := by
    rw [div_le_div_iff₀ h_pi_pos (by norm_num : (0:ℝ) < 4)]
    nlinarith [h_pi_gt_three]
  refine ⟨min (1/4) (1/(4*K)), min (1/Real.pi) (1/(4*K)),
    lt_min (by norm_num) (by positivity),
    min_le_left _ _,
    lt_min h_inv_pi_pos (by positivity),
    le_trans (min_le_left _ _) h_inv_pi_le_pi_4, ?_⟩
  intro δ R₀ hδ hδ_le hR₀_lo hR₀_lt θ hθ_lo hθ_hi
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_4K : δ ≤ 1/(4*K) := le_trans hδ_le (min_le_right _ _)
  have hR₀_pos : 0 < R₀ := by
    have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  -- Set up η.
  set η : ℝ := Real.pi - θ with hη_def
  have hη_nn : 0 ≤ η := by rw [hη_def]; linarith
  have h_θ_K_le_min : Real.pi - θ ≤ min (1/Real.pi) (1/(4*K)) := by
    rw [hη_def] at hη_def; linarith
  have hη_le_inv_pi : η ≤ 1/Real.pi := by
    have h1 : η ≤ min (1/Real.pi) (1/(4*K)) := by rw [hη_def]; linarith
    exact le_trans h1 (min_le_left _ _)
  have hη_le_inv_4K : η ≤ 1/(4*K) := by
    have h1 : η ≤ min (1/Real.pi) (1/(4*K)) := by rw [hη_def]; linarith
    exact le_trans h1 (min_le_right _ _)
  have hη_le_pi_2 : η ≤ Real.pi / 2 := by
    have h1 : η ≤ Real.pi / 4 := le_trans hη_le_inv_pi h_inv_pi_le_pi_4
    linarith
  have hη_lt_pi : η < Real.pi := by linarith
  -- Trig values.
  have h_sin_η_nn : 0 ≤ Real.sin η := Real.sin_nonneg_of_mem_Icc ⟨hη_nn, by linarith⟩
  have h_sin_η_le_η : Real.sin η ≤ η := Real.sin_le hη_nn
  have h_one_minus_cos : 1 - Real.cos η ≤ η^2 / 2 := by
    have := @Real.one_sub_sq_div_two_le_cos η; linarith
  have h_sin_θ_eq : Real.sin θ = Real.sin η := by
    rw [hη_def, Real.sin_pi_sub]
  have h_cos_θ_eq : Real.cos θ = -Real.cos η := by
    rw [hη_def, Real.cos_pi_sub]; ring
  -- R₀ > √(3/16) > 1/3.
  have hR₀_gt_sqrt_3_16 : Real.sqrt (3/16) < R₀ := by
    have h_sqrt_mono : Real.sqrt (1/4 - (1/4)^2) ≤ Real.sqrt (1/4 - δ^2) := by
      apply Real.sqrt_le_sqrt; nlinarith [hδ_le_quarter, hδ.le]
    have h_3_16 : 1/4 - (1/4:ℝ)^2 = 3/16 := by ring
    rw [h_3_16] at h_sqrt_mono
    linarith [hR₀_lo, h_sqrt_mono]
  have hR₀_gt_one_third : (1:ℝ)/3 < R₀ := by
    have h_sqrt_3_16_pos : (0:ℝ) ≤ Real.sqrt (3/16) := Real.sqrt_nonneg _
    have h_sqrt_3_16_gt : (1:ℝ)/3 < Real.sqrt (3/16) := by
      have h_sq_lt : ((1:ℝ)/3)^2 < 3/16 := by norm_num
      have h_third_nn : (0:ℝ) ≤ 1/3 := by norm_num
      have h_sqrt_mono : Real.sqrt ((1/3:ℝ)^2) < Real.sqrt (3/16) :=
        Real.sqrt_lt_sqrt (by norm_num) h_sq_lt
      rw [Real.sqrt_sq h_third_nn] at h_sqrt_mono
      exact h_sqrt_mono
    linarith
  -- Names for arc.Re and arc.Im.
  set u : ℝ := 1/2 + R₀ * Real.cos θ with hu_def
  set v : ℝ := δ + R₀ * Real.sin θ with hv_def
  have hu_eq : u = 1/2 - R₀ * Real.cos η := by rw [hu_def, h_cos_θ_eq]; ring
  have hv_eq : v = δ + R₀ * Real.sin η := by rw [hv_def, h_sin_θ_eq]
  -- v > 0 (since δ > 0, sin η ≥ 0, R₀ > 0).
  have hv_pos : 0 < v := by rw [hv_eq]; positivity
  -- u ≥ 0 (since R₀ < 1/2 and cos η ≤ 1).
  have h_cos_η_le_one : Real.cos η ≤ 1 := Real.cos_le_one η
  have hu_nn : 0 ≤ u := by
    rw [hu_eq]
    nlinarith [hR₀_lt, hR₀_pos, h_cos_η_le_one,
               Real.cos_nonneg_of_mem_Icc (⟨by linarith, by linarith⟩ :
                 η ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))]
  -- u ≤ 2δ² + η²/4.
  have h_half_minus_R₀ : 1/2 - R₀ ≤ 2 * δ^2 := by
    have hR₀_sq_gt : 1/4 - δ^2 < R₀^2 := by
      have h2 : 0 ≤ 1/4 - δ^2 := by nlinarith [hδ_le_quarter]
      have h3 : Real.sqrt (1/4 - δ^2)^2 = 1/4 - δ^2 := Real.sq_sqrt h2
      nlinarith [hR₀_lo, Real.sqrt_nonneg (1/4 - δ^2), sq_nonneg R₀, h3]
    nlinarith [hR₀_sq_gt, hR₀_lt, hR₀_pos]
  have hu_upper : u ≤ 2 * δ^2 + η^2 / 4 := by
    rw [hu_eq]
    have h1 : 1/2 - R₀ * Real.cos η = (1/2 - R₀) + R₀ * (1 - Real.cos η) := by ring
    rw [h1]
    have h2 : R₀ * (1 - Real.cos η) ≤ R₀ * (η^2 / 2) :=
      mul_le_mul_of_nonneg_left h_one_minus_cos hR₀_pos.le
    have h3 : R₀ * (η^2 / 2) ≤ (1/2) * (η^2 / 2) := by
      nlinarith [hR₀_lt, sq_nonneg η, hR₀_pos]
    linarith
  -- Key: u ≤ v (i.e., arc.Re ≤ arc.Im).
  -- u ≤ 2δ² + η²/4 ≤ δ + R₀ sin η = v.
  --   2δ² ≤ δ (using δ ≤ 1/2)
  --   η²/4 ≤ R₀ sin η (using R₀ > 1/3 > 0 and sin η ≥ (2/π) η)
  have h_η_sq_le_R₀_sin : η^2 / 4 ≤ R₀ * Real.sin η :=
    modularLambdaH_F_Y_arc_eta_sq_le_R₀_sin hR₀_gt_one_third hη_nn
      hη_le_inv_pi hη_le_pi_2
  have hu_le_v : u ≤ v := by
    rw [hv_eq]
    calc u ≤ 2 * δ^2 + η^2 / 4 := hu_upper
      _ = (2 * δ^2) + (η^2 / 4) := by ring
      _ ≤ δ + R₀ * Real.sin η := by
        have h_2δ_sq : 2 * δ^2 ≤ δ := by nlinarith [hδ.le, hδ_le_quarter]
        linarith [h_η_sq_le_R₀_sin]
  -- v ≤ 1/(2K) (via sub-helper).
  have hv_upper : v ≤ 1/(2*K) := by
    rw [hv_eq]
    exact modularLambdaH_F_Y_arc_cusp_0_v_bound hδ.le hR₀_pos hR₀_lt hη_nn
      h_sin_η_le_η hδ_le_inv_4K hη_le_inv_4K hK_pos
  -- Im(-1/arc) computation.
  have h_normSq_eq := modularLambdaH_F_Y_arc_normSq_eq δ R₀ θ
  have hθ_nn : 0 ≤ θ := by
    have h_pi_4_pos : 0 < Real.pi / 4 := by positivity
    have h_min_le : min (1/Real.pi) (1/(4*K)) ≤ 1/Real.pi := min_le_left _ _
    have h1 : Real.pi - min (1/Real.pi) (1/(4*K)) ≥ 0 := by
      linarith [h_inv_pi_pos]
    linarith
  have harc_im_pos := modularLambdaH_F_Y_arc_im_pos hδ hR₀_pos.le hθ_nn hθ_hi
  have harc_ne_zero :
      _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ ≠ 0 := by
    intro h_eq
    have : (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im = 0 := by
      rw [h_eq]; rfl
    linarith [harc_im_pos]
  have h_normSq_pos : 0 < Complex.normSq
      (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) :=
    Complex.normSq_pos.mpr harc_ne_zero
  have h_im_inv :
      (-(_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)⁻¹).im =
      (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im /
      Complex.normSq (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) := by
    rw [Complex.neg_im, Complex.inv_im]; ring
  rw [h_im_inv, le_div_iff₀ h_normSq_pos, h_normSq_eq]
  -- Express arc.Im in terms of θ.
  have harc_im_eq : (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im = v := by
    rw [_root_.circleMap]
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hv_def]
  rw [harc_im_eq]
  -- Goal: K * ((1/2 + R₀ cos θ)² + (δ + R₀ sin θ)²) ≤ v
  -- = K * (u² + v²) ≤ v
  -- Show: K * (u² + v²) ≤ K * (2 * v²) ≤ v.
  have h_normSq_uv : (1/2 + R₀ * Real.cos θ)^2 + (δ + R₀ * Real.sin θ)^2 = u^2 + v^2 := by
    rw [hu_def, hv_def]
  rw [h_normSq_uv]
  exact modularLambdaH_F_Y_arc_cusp_0_poly_bound hu_nn hv_pos hu_le_v hv_upper hK_pos


/-- **Sub-lemma 8.aux — `1/2 - R₀ ≤ 2δ²` from `R₀ > √(1/4 - δ²)`.** -/
theorem modularLambdaH_F_Y_arc_half_minus_R₀_bound
    {δ R₀ : ℝ} (hδ_pos : 0 < δ) (hδ_le_quarter : δ ≤ 1 / 4)
    (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hR₀_pos : 0 < R₀) :
    1 / 2 - R₀ ≤ 2 * δ ^ 2 := by
  have hR₀_sq_gt : 1 / 4 - δ ^ 2 < R₀ ^ 2 := by
    have h2 : 0 ≤ 1 / 4 - δ ^ 2 := by nlinarith
    have h3 : Real.sqrt (1 / 4 - δ ^ 2) ^ 2 = 1 / 4 - δ ^ 2 := Real.sq_sqrt h2
    nlinarith [hR₀_lo, Real.sqrt_nonneg (1 / 4 - δ ^ 2), sq_nonneg R₀, h3]
  nlinarith [hR₀_sq_gt, hR₀_lt, hR₀_pos]

/-- **Sub-lemma 8.aux — middle-case polynomial bound.**
Given `M, δ, R₀, w_im` with the appropriate hypotheses (`δ ≤ 1/4`,
`δ ≤ w_im/(4M)`, `1/2 − R₀ ≤ 2δ²`, `w_im > 0`), `M · (δ + (1/2 − R₀)) < w_im`. -/
theorem modularLambdaH_F_Y_arc_middle_poly_bound
    {M δ R₀ w_im : ℝ} (hM_pos : 0 < M) (hδ_pos : 0 < δ)
    (hδ_le_quarter : δ ≤ 1 / 4) (hδ_le_M : δ ≤ w_im / (4 * M))
    (h_half_minus_R₀ : 1 / 2 - R₀ ≤ 2 * δ ^ 2) (hw_im_pos : 0 < w_im) :
    M * (δ + (1 / 2 - R₀)) < w_im := by
  -- δ + 1/2 - R₀ ≤ δ + 2δ² ≤ (3/2) δ (using δ ≤ 1/4 ⟹ 2δ² ≤ δ/2).
  have h_2δ_sq_le : 2 * δ^2 ≤ δ/2 := by nlinarith [hδ_pos.le, hδ_le_quarter]
  have h_sum_le : δ + (1/2 - R₀) ≤ (3/2) * δ := by linarith
  -- M · (3/2)δ ≤ M · (3/2) · w_im/(4M) = 3 w_im / 8 < w_im.
  have hM_δ_le : M * δ ≤ M * (w_im / (4*M)) :=
    mul_le_mul_of_nonneg_left hδ_le_M hM_pos.le
  have h_M_inv : M * (w_im / (4*M)) = w_im / 4 := by
    field_simp
  have h_M_sum : M * (δ + (1/2 - R₀)) ≤ M * ((3/2) * δ) :=
    mul_le_mul_of_nonneg_left h_sum_le hM_pos.le
  have h_M_3_2_δ : M * ((3/2) * δ) = (3/2) * (M * δ) := by ring
  have h_3_2_le : (3/2 : ℝ) * (M * δ) ≤ (3/2) * (w_im / 4) := by
    have h_M_δ_le' : M * δ ≤ w_im / 4 := by rw [← h_M_inv]; exact hM_δ_le
    linarith
  have h_final : (3/2 : ℝ) * (w_im / 4) < w_im := by linarith
  linarith

/-- **Sub-lemma 8.aux — cusp-1 norm inequality.**
Given `0 ≤ w_norm`, `0 < c`, `c < 1/(w_norm + 2)`, `1 - c ≤ X`,
we have `w_norm < X / c`. -/
theorem modularLambdaH_F_Y_arc_cusp_1_norm_bound
    {w_norm c X : ℝ} (hw_nn : 0 ≤ w_norm) (hc_pos : 0 < c)
    (hc_lt : c < 1 / (w_norm + 2)) (h_one_minus_c_le_X : 1 - c ≤ X) :
    w_norm < X / c := by
  have h_w_plus_two_pos : 0 < w_norm + 2 := by linarith
  have h_c_w_plus_two_lt_one : c * (w_norm + 2) < 1 := by
    rw [lt_div_iff₀ h_w_plus_two_pos] at hc_lt; linarith
  rw [lt_div_iff₀ hc_pos]
  nlinarith [h_one_minus_c_le_X, h_c_w_plus_two_lt_one, hc_pos, hw_nn]

/-- **Sub-lemma 8.aux — exponential bound (mul form).** Given `C > 0`,
with `L := log(160000 · C)` and `K := max L 1 + 1`, we have
`160000 · exp(-π · K) < 1/C`. Used for cusp 1 where `C = ‖w‖ + 2`. -/
theorem modularLambdaH_F_Y_arc_ne_exp_bound_mul (C : ℝ) (hC_pos : 0 < C) :
    160000 * Real.exp (-Real.pi * (max (Real.log (160000 * C)) 1 + 1)) < 1 / C := by
  set L : ℝ := Real.log (160000 * C) with hL_def
  set K : ℝ := max L 1 + 1 with hK_def
  have hK_pos : 0 < K := by
    have : 1 ≤ max L 1 := le_max_right _ _
    rw [hK_def]; linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hL_lt_πK : L < Real.pi * K := by
    have h1 : L ≤ max L 1 := le_max_left _ _
    have h2 : max L 1 < K := by rw [hK_def]; linarith
    have h3 : L < K := lt_of_le_of_lt h1 h2
    nlinarith [h3, h_pi_gt_one, hK_pos]
  have h_exp_neg_L : Real.exp (-L) = 1 / (160000 * C) := by
    rw [hL_def]
    rw [show -Real.log (160000 * C) = Real.log ((160000 * C)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 * C)⁻¹), one_div]
  have h_exp_lt : Real.exp (-Real.pi * K) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  calc 160000 * Real.exp (-Real.pi * K)
      < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
    _ = 160000 * (1 / (160000 * C)) := by rw [h_exp_neg_L]
    _ = 1 / C := by field_simp

/-- **Sub-lemma 8.aux — exponential bound (div form).** Given `C > 0`,
with `L := log(160000 / C)` and `K := max L 1 + 1`, we have
`160000 · exp(-π · K) < C`. Used for cusp 0 where `C = ‖w − 1‖`. -/
theorem modularLambdaH_F_Y_arc_ne_exp_bound_div (C : ℝ) (hC_pos : 0 < C) :
    160000 * Real.exp (-Real.pi * (max (Real.log (160000 / C)) 1 + 1)) < C := by
  set L : ℝ := Real.log (160000 / C) with hL_def
  set K : ℝ := max L 1 + 1 with hK_def
  have hK_pos : 0 < K := by
    have : 1 ≤ max L 1 := le_max_right _ _
    rw [hK_def]; linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hL_lt_πK : L < Real.pi * K := by
    have h1 : L ≤ max L 1 := le_max_left _ _
    have h2 : max L 1 < K := by rw [hK_def]; linarith
    have h3 : L < K := lt_of_le_of_lt h1 h2
    nlinarith [h3, h_pi_gt_one, hK_pos]
  have h_exp_neg_L : Real.exp (-L) = C / 160000 := by
    rw [hL_def]
    rw [show -Real.log (160000 / C) = Real.log ((160000 / C)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 / C)⁻¹), inv_div]
  have h_exp_lt : Real.exp (-Real.pi * K) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  calc 160000 * Real.exp (-Real.pi * K)
      < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
    _ = 160000 * (C / 160000) := by rw [h_exp_neg_L]
    _ = C := by field_simp

set_option maxHeartbeats 400000 in
-- Three-case Sub-lemma 8 (middle Lipschitz + cusp-0 + cusp-1 conjugation)
-- with extensive complex-arithmetic and bound chaining; exceeds the default
-- 200000 budget even after extracting many sub-helpers.
/-- **Sub-lemma 8 — shifted arc non-vanishing (existential δ_w form).**
For `w ∈ ℍ`, there exists `δ_w ∈ (0, 1/2)` such that for all `δ ∈ (0, δ_w]`,
`R₀ ∈ (√(1/4 − δ²), 1/2)`, and `θ ∈ [0, π]`:
`λ(circleMap (1/2 + δ·i) R₀ θ) − w ≠ 0`.

The existential form (matching sub-lemmas 6, 7) replaces the previous
universal statement, since the proof genuinely requires `δ` small enough
relative to `w` to control the arc's `Im λ` against `Im w > 0`. In the
main F_Y theorem, this `δ_w` is passed to sub-lemma 1' as `δ_max`.

Proof structure: `θ_0 := min(θ_K_0, θ_K_1)` where `K_0, K_1` are derived
from `‖w − 1‖` and `‖w‖ + 2`. Middle of arc handled by extracting
uniform Lipschitz constant `M` directly via Helper 8.2 on the fixed
ball used by Helper 8.3, combined with the geometry of Helpers
8.3.a/b/c. Cusp 0 (`θ ∈ [π − θ_0, π]`): S-action + cusp helper.
Cusp 1 (`θ ∈ [0, θ_0]`): conjugation symmetry + T-action chain
reduces to cusp-0 analysis of `1 - conj(arc(θ)) = arc(π − θ)`. -/
theorem modularLambdaH_F_Y_arc_ne
    {w : ℂ} (hw : 0 < w.im) :
    ∃ δ_w : ℝ, 0 < δ_w ∧ δ_w < 1 / 2 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_w →
    Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      modularLambdaH (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w
        ≠ 0 := by
  -- Three-case proof:
  -- (a) Middle θ ∈ [θ_0, π - θ_0]: Helper 8.3-style bound on |Im λ|.
  -- (b) Cusp 0 θ ∈ (π - θ_K_0, π]: S-action + norm bound; ‖λ - 1‖ < ‖w - 1‖.
  -- (c) Cusp 1 θ ∈ [0, θ_K_1): conjugation + T; |λ| > ‖w‖.
  -- The three pieces of `δ_w` come from these three regimes.
  have hw_ne_one : w ≠ 1 := by
    intro h_eq
    rw [h_eq] at hw
    simp at hw
  have hw_one_norm_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne_one)
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  -- K_0 for cusp 0: 160000·exp(-π·K_0) < ‖w - 1‖.
  set L_0 : ℝ := Real.log (160000 / ‖w - 1‖) with hL_0_def
  set K_0 : ℝ := max L_0 1 + 1 with hK_0_def
  have hK_0_pos : 0 < K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  have hK_0_ge_one : 1 ≤ K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  -- K_1 for cusp 1: 160000·exp(-π·K_1) < 1/(‖w‖ + 2).
  set L_1 : ℝ := Real.log (160000 * (‖w‖ + 2)) with hL_1_def
  set K_1 : ℝ := max L_1 1 + 1 with hK_1_def
  have hK_1_pos : 0 < K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  have hK_1_ge_one : 1 ≤ K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  -- Cusp helpers.
  obtain ⟨δ_K_0, θ_K_0, hδ_K_0_pos, hδ_K_0_le_quarter, hθ_K_0_pos, hθ_K_0_le_pi_4,
    h_cusp_0_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_0 hK_0_pos
  obtain ⟨δ_K_1, θ_K_1, hδ_K_1_pos, hδ_K_1_le_quarter, hθ_K_1_pos, hθ_K_1_le_pi_4,
    h_cusp_1_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_1 hK_1_pos
  -- θ_0 := min(θ_K_0, θ_K_1). Then sin θ_0 > 0.
  set θ_0 : ℝ := min θ_K_0 θ_K_1 with hθ_0_def
  have hθ_0_pos : 0 < θ_0 := lt_min hθ_K_0_pos hθ_K_1_pos
  have hθ_0_le_θ_K_0 : θ_0 ≤ θ_K_0 := min_le_left _ _
  have hθ_0_le_θ_K_1 : θ_0 ≤ θ_K_1 := min_le_right _ _
  have hθ_0_lt_pi_2 : θ_0 < Real.pi / 2 := by
    have : θ_0 ≤ Real.pi / 4 := le_trans hθ_0_le_θ_K_0 hθ_K_0_le_pi_4
    linarith
  have hθ_0_lt_pi : θ_0 < Real.pi := by linarith
  have h_sin_θ_0_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  -- Setup the ball for Lipschitz extraction (Helper 8.3's internal setup).
  set τ_K : ℂ := (1/2 : ℂ) +
    Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ) with hτ_K_def
  set r_K : ℝ := (1 + Real.cos θ_0) / (4 * Real.sin θ_0) with hr_K_def
  have h_cos_θ_0_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt_pi_2⟩
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  have hr_K_pos : 0 < r_K := by
    rw [hr_K_def]; exact div_pos (by linarith) h_4s_pos
  -- τ_K.im = 1/(2 sin θ_0) > 0.
  have hτ_K_im_eq : τ_K.im = 1/(2*Real.sin θ_0) := by
    rw [hτ_K_def]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  have hτ_K_im_pos : 0 < τ_K.im := by rw [hτ_K_im_eq]; positivity
  -- Apply Helper 8.3.a (ball in UHP) and Helper 8.2 to get M.
  have h_ball_in :=
    modularLambdaH_arc_lipschitz_ball_in_uhp hθ_0_pos hθ_0_lt_pi_2
  obtain ⟨M, hM_pos, hM_lipschitz⟩ :=
    modularLambdaH_im_lipschitz_on_compact hτ_K_im_pos hr_K_pos h_ball_in
  -- δ_w := min of constraints.
  set δ_M : ℝ := w.im / (4 * M) with hδ_M_def
  have hδ_M_pos : 0 < δ_M := by rw [hδ_M_def]; positivity
  set δ_w : ℝ := min (min δ_K_0 δ_K_1)
    (min (Real.sin θ_0 / 4) (min δ_M (1/4))) with hδ_w_def
  have hδ_w_pos : 0 < δ_w :=
    lt_min (lt_min hδ_K_0_pos hδ_K_1_pos)
      (lt_min (by positivity) (lt_min hδ_M_pos (by norm_num)))
  have hδ_w_lt_half : δ_w < 1/2 := by
    have h1 : δ_w ≤ 1/4 := by
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      rfl
    linarith
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ R₀ hδ_pos hδ_le hR₀_lo hR₀_lt θ hθ_lo hθ_hi
  -- Extract individual constraints on δ.
  have hδ_le_δ_K_0 : δ ≤ δ_K_0 := le_trans hδ_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_le_δ_K_1 : δ ≤ δ_K_1 := le_trans hδ_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ_le_sin_θ_0_quarter : δ ≤ Real.sin θ_0 / 4 :=
    le_trans hδ_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_δ_M : δ ≤ δ_M :=
    le_trans hδ_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδ_le_quarter : δ ≤ 1/4 :=
    le_trans hδ_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- The arc point and basic facts.
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w := by
    linear_combination h_lam_eq_w
  have harc_im_pos : 0 < arc.im :=
    modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le hθ_lo hθ_hi
  -- Case split on θ position.
  by_cases h_θ_le_θ_0 : θ ≤ θ_0
  · -- Cusp 1 case: θ ∈ [0, θ_0] ⊆ [0, θ_K_1].
    -- arc(π - θ) is in [π - θ_K_1, π] (cusp 0 of arc).
    have hπθ_le : Real.pi - θ ≤ Real.pi := by linarith [hθ_lo]
    have hπθ_ge_θ_K_1 : Real.pi - θ_K_1 ≤ Real.pi - θ := by
      linarith [hθ_0_le_θ_K_1, h_θ_le_θ_0]
    -- Im(-1/arc(π - θ)) ≥ K_1.
    have h_im_inv_πθ_ge :
        K_1 ≤ (-(_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀
          (Real.pi - θ))⁻¹).im :=
      h_cusp_1_bound δ R₀ hδ_pos hδ_le_δ_K_1 hR₀_lo hR₀_lt (Real.pi - θ)
        hπθ_ge_θ_K_1 hπθ_le
    -- Define σ = arc - 1 and τ' = -conj σ = arc(π - θ).
    set σ : ℂ := arc - 1 with hσ_def
    set arcπθ : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi - θ) with harcπθ_def
    -- arc.Im > 0 already established.
    have hσ_im : σ.im = arc.im := by rw [hσ_def]; simp
    have hσ_im_pos : 0 < σ.im := by rw [hσ_im]; exact harc_im_pos
    -- arc(π - θ) = (1/2 - R₀ cos θ) + i(δ + R₀ sin θ) = 1 - conj(arc).
    -- Compute arc.re, arc.im, arcπθ.re, arcπθ.im, σ.re separately.
    have harc_re : arc.re = 1/2 + R₀ * Real.cos θ := by
      rw [harc_def, _root_.circleMap]
      simp [Complex.add_re, Complex.mul_re,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have harc_im_eq : arc.im = δ + R₀ * Real.sin θ := by
      rw [harc_def, _root_.circleMap]
      simp [Complex.add_im, Complex.mul_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have harcπθ_re : arcπθ.re = 1/2 - R₀ * Real.cos θ := by
      have h_eq : arcπθ.re = 1/2 + R₀ * Real.cos (Real.pi - θ) := by
        rw [harcπθ_def, _root_.circleMap]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, mul_zero, zero_mul, sub_zero, mul_one,
          add_zero]
        have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
        rw [h_half_re]
      rw [h_eq, Real.cos_pi_sub]; ring
    have harcπθ_im : arcπθ.im = δ + R₀ * Real.sin θ := by
      have h_eq : arcπθ.im = δ + R₀ * Real.sin (Real.pi - θ) := by
        rw [harcπθ_def, _root_.circleMap]
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, mul_zero, zero_mul, mul_one]
        have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
        rw [h_half_im]; ring
      rw [h_eq, Real.sin_pi_sub]
    have hσ_re : σ.re = -1/2 + R₀ * Real.cos θ := by
      rw [hσ_def, Complex.sub_re, harc_re, Complex.one_re]; ring
    have hσ_im_eq : σ.im = δ + R₀ * Real.sin θ := by
      rw [hσ_def, Complex.sub_im, harc_im_eq, Complex.one_im]; ring
    -- Equivalently, -conj σ = arc(π - θ).
    have h_neg_conj_σ_eq : -(starRingEnd ℂ σ) = arcπθ := by
      apply Complex.ext
      · rw [Complex.neg_re, Complex.conj_re, hσ_re, harcπθ_re]; ring
      · rw [Complex.neg_im, Complex.conj_im, hσ_im_eq, harcπθ_im]; ring
    -- λ(arc(π - θ)) = conj(λ σ).
    have h_conj_lam : modularLambdaH arcπθ = starRingEnd ℂ (modularLambdaH σ) := by
      rw [← h_neg_conj_σ_eq]
      exact modularLambdaH_conj_symmetry hσ_im_pos
    -- Norm bound on arc(π - θ).
    have h_im_inv_πθ_ge_one : 1 ≤ (-(arcπθ)⁻¹).im := by
      rw [harcπθ_def] at h_im_inv_πθ_ge ⊢
      exact le_trans hK_1_ge_one h_im_inv_πθ_ge
    have h_norm_lam_inv_πθ : ‖modularLambdaH (-(arcπθ : ℂ)⁻¹)‖ ≤
        160000 * Real.exp (-Real.pi * (-(arcπθ : ℂ)⁻¹).im) :=
      modularLambdaH_norm_le_exp_of_im_ge_one h_im_inv_πθ_ge_one
    -- S-action on arc(π - θ): λ(arc(π-θ)) + λ(-1/arc(π-θ)) = 1.
    have h_arcπθ_im_pos : 0 < arcπθ.im := by
      rw [harcπθ_def]
      exact modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le
        (by linarith [hθ_hi]) hπθ_le
    have h_S_πθ : modularLambdaH arcπθ + modularLambdaH (-1/arcπθ) = 1 :=
      modularLambdaH_add_S_smul_eq_one h_arcπθ_im_pos
    have h_neg_eq_πθ : -1/arcπθ = -arcπθ⁻¹ := by field_simp
    rw [h_neg_eq_πθ] at h_S_πθ
    have h_diff_πθ : modularLambdaH arcπθ - 1 = -modularLambdaH (-(arcπθ : ℂ)⁻¹) := by
      linear_combination h_S_πθ
    have h_norm_diff_πθ : ‖modularLambdaH arcπθ - 1‖ = ‖modularLambdaH (-(arcπθ : ℂ)⁻¹)‖ := by
      rw [h_diff_πθ, norm_neg]
    -- ‖λ(arc(π-θ)) - 1‖ ≤ 160000 · exp(-π · K_1) < 1/(‖w‖ + 2).
    have h_exp_mono_πθ : Real.exp (-Real.pi * (-(arcπθ : ℂ)⁻¹).im) ≤
        Real.exp (-Real.pi * K_1) := by
      apply Real.exp_le_exp.mpr
      have := h_im_inv_πθ_ge
      rw [harcπθ_def] at this
      nlinarith [Real.pi_pos, this]
    have h_bound_πθ : ‖modularLambdaH arcπθ - 1‖ ≤ 160000 * Real.exp (-Real.pi * K_1) := by
      rw [h_norm_diff_πθ]
      exact le_trans h_norm_lam_inv_πθ (mul_le_mul_of_nonneg_left h_exp_mono_πθ (by norm_num))
    have h_w_norm_plus_two_pos : (0 : ℝ) < ‖w‖ + 2 := by
      have : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
      linarith
    have h_inv_pos : (0 : ℝ) < 1 / (‖w‖ + 2) := by positivity
    -- 160000 · exp(-π K_1) < 1/(‖w‖+2) via exp_bound helper.
    have h_final_πθ : 160000 * Real.exp (-Real.pi * K_1) < 1 / (‖w‖ + 2) := by
      have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_mul (‖w‖ + 2) h_w_norm_plus_two_pos
      have hK_1_eq : K_1 = max (Real.log (160000 * (‖w‖ + 2))) 1 + 1 := by
        rw [hK_1_def, hL_1_def]
      rw [hK_1_eq]; exact h_helper
    have h_strict_πθ : ‖modularLambdaH arcπθ - 1‖ < 1 / (‖w‖ + 2) :=
      lt_of_le_of_lt h_bound_πθ h_final_πθ
    -- Transfer to σ via conjugation.
    have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH arcπθ - 1‖ := by
      rw [h_conj_lam]
      rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
        rw [map_sub, map_one]]
      rw [norm_conj]
    have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (‖w‖ + 2) := by
      rw [h_norm_diff_σ]; exact h_strict_πθ
    -- T-action: λ(σ + 1) = λ σ / (λ σ - 1).
    have h_T : modularLambdaH (σ + 1) = modularLambdaH σ / (modularLambdaH σ - 1) :=
      modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
    have h_σ_plus_one : σ + 1 = arc := by simp [hσ_def]
    rw [h_σ_plus_one] at h_T
    -- λ(σ) - 1 ≠ 0.
    have h_lam_σ_sub_one_ne : modularLambdaH σ - 1 ≠ 0 :=
      sub_ne_zero.mpr (modularLambdaH_ne_one hσ_im_pos)
    -- |λ(σ)| ≥ 1 - ‖λ(σ) - 1‖.
    have h_lam_σ_norm_ge : 1 - ‖modularLambdaH σ - 1‖ ≤ ‖modularLambdaH σ‖ := by
      have h_rtri : ‖(1 : ℂ)‖ - ‖modularLambdaH σ‖ ≤ ‖(1 : ℂ) - modularLambdaH σ‖ :=
        norm_sub_norm_le (1 : ℂ) (modularLambdaH σ)
      have h_simp : (1 : ℂ) - modularLambdaH σ = -(modularLambdaH σ - 1) := by ring
      rw [norm_one, h_simp, norm_neg] at h_rtri
      linarith
    -- |λ(arc)| = |λ σ| / |λ σ - 1|.
    have h_norm_lam_arc : ‖modularLambdaH arc‖ = ‖modularLambdaH σ‖ / ‖modularLambdaH σ - 1‖ := by
      rw [h_T, norm_div]
    -- Show |λ(arc)| > ‖w‖.
    set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
    have hc_lt : c < 1 / (‖w‖ + 2) := h_strict_σ
    have hc_pos : 0 < c := by
      rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
    have h_lam_σ_ge : 1 - c ≤ ‖modularLambdaH σ‖ := by
      rw [hc_def]; exact h_lam_σ_norm_ge
    have h_norm_lam_arc_gt : ‖w‖ < ‖modularLambdaH arc‖ := by
      rw [h_norm_lam_arc]
      exact modularLambdaH_F_Y_arc_cusp_1_norm_bound (norm_nonneg w) hc_pos hc_lt h_lam_σ_ge
    rw [h_lam_arc_eq] at h_norm_lam_arc_gt
    exact lt_irrefl _ h_norm_lam_arc_gt
  · push Not at h_θ_le_θ_0
    -- θ > θ_0. Check if θ ≥ π - θ_0.
    by_cases h_θ_ge : Real.pi - θ_0 ≤ θ
    · -- Cusp 0 case: θ ∈ [π - θ_0, π] ⊆ [π - θ_K_0, π].
      have hθ_in_cusp_0 : Real.pi - θ_K_0 ≤ θ := by linarith [hθ_0_le_θ_K_0]
      have h_im_inv_ge : K_0 ≤ (-(arc)⁻¹).im := by
        have := h_cusp_0_bound δ R₀ hδ_pos hδ_le_δ_K_0 hR₀_lo hR₀_lt θ hθ_in_cusp_0 hθ_hi
        rw [harc_def]; exact this
      have h_im_inv_ge_one : 1 ≤ (-(arc)⁻¹).im := le_trans hK_0_ge_one h_im_inv_ge
      -- Norm bound: ‖λ(-arc⁻¹)‖ ≤ 160000 · exp(-π · Im(-arc⁻¹)) ≤ 160000 · exp(-π K_0).
      have h_norm_lam_inv : ‖modularLambdaH (-(arc : ℂ)⁻¹)‖ ≤
          160000 * Real.exp (-Real.pi * (-(arc : ℂ)⁻¹).im) :=
        modularLambdaH_norm_le_exp_of_im_ge_one h_im_inv_ge_one
      -- S-action: λ(τ) + λ(-1/τ) = 1.
      have h_S : modularLambdaH arc + modularLambdaH (-1/arc) = 1 :=
        modularLambdaH_add_S_smul_eq_one harc_im_pos
      have h_neg_eq : -1/arc = -arc⁻¹ := by field_simp
      rw [h_neg_eq] at h_S
      have h_diff_eq : modularLambdaH arc - 1 = -modularLambdaH (-(arc : ℂ)⁻¹) := by
        linear_combination h_S
      have h_norm_diff : ‖modularLambdaH arc - 1‖ = ‖modularLambdaH (-(arc : ℂ)⁻¹)‖ := by
        rw [h_diff_eq, norm_neg]
      -- exp(-π · Im(-arc⁻¹)) ≤ exp(-π · K_0).
      have h_exp_mono : Real.exp (-Real.pi * (-(arc : ℂ)⁻¹).im) ≤
          Real.exp (-Real.pi * K_0) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos, h_im_inv_ge]
      have h_bound : ‖modularLambdaH arc - 1‖ ≤ 160000 * Real.exp (-Real.pi * K_0) := by
        rw [h_norm_diff]
        refine le_trans h_norm_lam_inv ?_
        exact mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
      -- 160000 · exp(-π · K_0) < ‖w - 1‖ via exp_bound helper.
      have h_final_bound : 160000 * Real.exp (-Real.pi * K_0) < ‖w - 1‖ := by
        have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_div ‖w - 1‖ hw_one_norm_pos
        have hK_0_eq : K_0 = max (Real.log (160000 / ‖w - 1‖)) 1 + 1 := by
          rw [hK_0_def, hL_0_def]
        rw [hK_0_eq]; exact h_helper
      have h_strict : ‖modularLambdaH arc - 1‖ < ‖w - 1‖ :=
        lt_of_le_of_lt h_bound h_final_bound
      rw [h_lam_arc_eq] at h_strict
      exact lt_irrefl _ h_strict
    · -- Middle case: θ ∈ (θ_0, π - θ_0).
      push Not at h_θ_ge
      have hθ_in_middle_lo : θ_0 ≤ θ := le_of_lt h_θ_le_θ_0
      have hθ_in_middle_hi : θ ≤ Real.pi - θ_0 := le_of_lt h_θ_ge
      -- arc ∈ closedBall τ_K r_K (Helper 8.3.c).
      have h_arc_in_ball := modularLambdaH_arc_lipschitz_arc_in_ball
        hδ_pos hR₀_lo hR₀_lt hθ_0_pos hθ_0_lt_pi_2 hδ_le_sin_θ_0_quarter
        hθ_in_middle_lo hθ_in_middle_hi
      -- semi ∈ closedBall τ_K r_K (Helper 8.3.b).
      have h_semi_in_ball := modularLambdaH_arc_lipschitz_semi_in_ball
        hθ_0_pos hθ_0_lt_pi_2 hθ_in_middle_lo hθ_in_middle_hi
      -- Apply Lipschitz bound M.
      have h_lipschitz_bd := hM_lipschitz arc
        (_root_.circleMap (1/2 : ℂ) (1/2) θ)
        (by rw [harc_def]; exact h_arc_in_ball) h_semi_in_ball
      -- semicircle real-valued: Im λ(semi) = 0.
      have hθ_pos : 0 < θ := by linarith [hθ_0_pos]
      have hθ_lt_pi : θ < Real.pi := by linarith [hθ_0_pos]
      have hθ_sin_pos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
      have h_semi_im_pos : 0 < (_root_.circleMap (1/2 : ℂ) (1/2) θ).im := by
        rw [_root_.circleMap]
        show 0 < ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)).im
        rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
        have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
        rw [h_half_im]
        have h_pos : 0 < (1 / 2 : ℝ) * Real.sin θ := by positivity
        linarith
      have h_semi_circle : ‖2 * (_root_.circleMap (1/2 : ℂ) (1/2) θ) - 1‖ = 1 := by
        rw [_root_.circleMap]
        have : 2 * ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) - 1 =
            Complex.exp (θ * Complex.I) := by push_cast; ring
        rw [this, Complex.norm_exp]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      have h_semi_im_zero : (modularLambdaH (_root_.circleMap (1/2 : ℂ) (1/2) θ)).im = 0 :=
        modularLambdaH_semicircle_real h_semi_im_pos h_semi_circle
      rw [h_semi_im_zero, sub_zero] at h_lipschitz_bd
      -- Helper 8.1: distance bound.
      have h_arc_to_semi := modularLambdaH_arc_to_semicircle_dist hδ_pos hR₀_pos hR₀_lt θ
      -- |Im λ(arc)| ≤ M · ‖arc - semi‖ ≤ M · (δ + 1/2 - R₀).
      have h_im_bound : |(modularLambdaH arc).im| ≤ M * (δ + (1/2 - R₀)) := by
        calc |(modularLambdaH arc).im|
            ≤ M * ‖arc - _root_.circleMap (1/2 : ℂ) (1/2) θ‖ := by
              rw [harc_def] at h_lipschitz_bd ⊢; exact h_lipschitz_bd
          _ ≤ M * (δ + (1/2 - R₀)) := by
              apply mul_le_mul_of_nonneg_left _ hM_pos.le
              rw [harc_def]
              exact h_arc_to_semi
      -- 1/2 - R₀ ≤ 2δ² (from R₀ > √(1/4 - δ²)).
      have h_half_minus_R₀ : 1/2 - R₀ ≤ 2 * δ^2 :=
        modularLambdaH_F_Y_arc_half_minus_R₀_bound hδ_pos hδ_le_quarter
          hR₀_lo hR₀_lt hR₀_pos
      -- δ ≤ w.im/(4M) (from hδ_le_δ_M and δ_M definition).
      have hδ_le_wim_4M : δ ≤ w.im / (4*M) := by
        have h_δ_M_eq : δ_M = w.im / (4*M) := hδ_M_def
        linarith [hδ_le_δ_M, h_δ_M_eq]
      -- Apply the pure polynomial helper.
      have h_M_bound : M * (δ + (1/2 - R₀)) < w.im :=
        modularLambdaH_F_Y_arc_middle_poly_bound hM_pos hδ_pos hδ_le_quarter
          hδ_le_wim_4M h_half_minus_R₀ hw
      -- λ(arc) = w gives Im λ(arc) = w.im. |Im λ(arc)| = w.im (since w.im > 0).
      -- But |Im λ(arc)| ≤ M · (δ + 1/2 - R₀) < w.im. Contradiction.
      rw [h_lam_arc_eq] at h_im_bound
      have h_abs_w_im : |w.im| = w.im := abs_of_pos hw
      rw [h_abs_w_im] at h_im_bound
      linarith [h_M_bound, h_im_bound]

/-- **Sub-lemma 9.aux.B1 — AP application packager.** Direct wrapper
around `cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk`
applied to `g(τ) = λ(τ) − w` over the F_Y region. Returns the existence
of a natural number `n` such that `(2πi)⁻¹ · (boundary integral) = n`.

The hypotheses include all six boundary non-vanishing conditions
(the four rectangle edges + bot_left/bot_right strips + arc), which
the caller supplies via the existing `_F_Y_left_edge_ne`,
`_F_Y_right_edge_ne`, `_F_Y_top_edge_ne` (+ a `Y ≥ Y₀` cascade),
`_F_Y_bot_left_strip_ne`, `_F_Y_bot_right_strip_ne`, and `_F_Y_arc_ne`
helpers in the path-(a) chain. -/
theorem modularLambdaH_F_Y_AP_integral_eq_nat_form
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (_hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ) := by
  -- Apply cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk to
  -- g = fun τ => modularLambdaH τ - w, e = 1/2 + δi, a = 0, b = 1, d = Y.
  set g : ℂ → ℂ := fun τ => modularLambdaH τ - w with hg_def
  set e : ℂ := (1 / 2 : ℂ) + (δ : ℂ) * Complex.I with he_def
  have he_re : e.re = 1 / 2 := by
    rw [he_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : e.im = δ := by
    rw [he_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  -- AP theorem prerequisites.
  have hab : (0 : ℝ) < 1 := by norm_num
  have h_a_lt : (0 : ℝ) < e.re - R₀ := by rw [he_re]; linarith
  have h_lt_b : e.re + R₀ < 1 := by rw [he_re]; linarith
  have h_e_im_R0_lt_d : e.im + R₀ < Y := by rw [he_im]; exact h_δR_lt_Y
  -- Analyticity of g on F_Y.
  have hg_an : AnalyticOnNhd ℂ g
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc e.im Y) \ Metric.ball e R₀) := by
    rw [he_im, he_def]
    exact modularLambdaH_F_Y_analytic w hδ _hδY hR₀_pos
  -- Boundary non-vanishing for g (= λ − w).
  have hg_bot_left' : ∀ x ∈ Set.Icc (0 : ℝ) (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_left x hx
  have hg_bot_right' : ∀ x ∈ Set.Icc (e.re + R₀) 1,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_right x hx
  have hg_top' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      g ((x : ℂ) + (Y : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; exact hg_top x hx
  have hg_right' : ∀ y ∈ Set.Icc e.im Y,
      g ((1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_right y hy
  have hg_left' : ∀ y ∈ Set.Icc e.im Y,
      g ((0 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_left y hy
  have hg_arc' : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0 := by
    rw [he_def]; intro θ hθ; exact hg_arc θ hθ
  -- Apply the AP theorem.
  obtain ⟨n, hn⟩ := cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk
    g 0 1 Y e R₀ hab hR₀_pos h_a_lt h_lt_b h_e_im_R0_lt_d
    hg_an hg_bot_left' hg_bot_right' hg_top' hg_right' hg_left' hg_arc'
  refine ⟨n, ?_⟩
  -- Convert deriv g to deriv modularLambdaH.
  have h_deriv : ∀ τ : ℂ, deriv g τ = deriv modularLambdaH τ := fun τ => by
    rw [hg_def]; exact deriv_sub_const w
  -- Rewrite hn to match the goal: substitute e.re = 1/2, e.im = δ,
  -- unfold e, unfold g, replace deriv g with deriv modularLambdaH.
  rw [he_re, he_im] at hn
  simp_rw [h_deriv, hg_def, he_def] at hn
  convert hn using 2

/-- **F_Y argument principle, divisor-sum form.** The `(2πi)⁻¹`-normalized
six-term boundary integral of `λ'/(λ − w)` over `∂F_Y` equals the total
divisor sum (the zero count with multiplicity) of `λ − w` on the
truncated region. Wrapper around
`Complex.cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`
specialized to `g := λ − w`, with `deriv g` converted to `deriv λ`. -/
theorem modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
    ((∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) := by
  set g : ℂ → ℂ := fun τ => modularLambdaH τ - w with hg_def
  set e : ℂ := (1 / 2 : ℂ) + (δ : ℂ) * Complex.I with he_def
  have he_re : e.re = 1 / 2 := by
    rw [he_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : e.im = δ := by
    rw [he_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  have hab : (0 : ℝ) < 1 := by norm_num
  have h_a_lt : (0 : ℝ) < e.re - R₀ := by rw [he_re]; linarith
  have h_lt_b : e.re + R₀ < 1 := by rw [he_re]; linarith
  have h_e_im_R0_lt_d : e.im + R₀ < Y := by rw [he_im]; exact h_δR_lt_Y
  have hg_an : AnalyticOnNhd ℂ g
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc e.im Y) \ Metric.ball e R₀) := by
    rw [he_im, he_def]
    exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos
  have hg_bot_left' : ∀ x ∈ Set.Icc (0 : ℝ) (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_left x hx
  have hg_bot_right' : ∀ x ∈ Set.Icc (e.re + R₀) 1,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_right x hx
  have hg_top' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      g ((x : ℂ) + (Y : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; exact hg_top x hx
  have hg_right' : ∀ y ∈ Set.Icc e.im Y,
      g ((1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_right y hy
  have hg_left' : ∀ y ∈ Set.Icc e.im Y,
      g ((0 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_left y hy
  have hg_arc' : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0 := by
    rw [he_def]; intro θ hθ; exact hg_arc θ hθ
  have hn := Complex.cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk
    g 0 1 Y e R₀ hab hR₀_pos h_a_lt h_lt_b h_e_im_R0_lt_d
    hg_an hg_bot_left' hg_bot_right' hg_top' hg_right' hg_left' hg_arc'
  have h_deriv : ∀ τ : ℂ, deriv g τ = deriv modularLambdaH τ := fun τ => by
    rw [hg_def]; exact deriv_sub_const w
  rw [he_re, he_im] at hn
  simp_rw [h_deriv, hg_def, he_def] at hn
  convert hn using 2


set_option maxHeartbeats 400000 in
-- The quantitative cusp-chart estimates make this declaration elaboration-heavy.
/-- **Deep-cusp reference value.** There is a value `w₀ ∈ ℍ` whose full
set of `λ`-preimages in the open fundamental domain `F°` is the single
point `τ₀ = 1/2 + T·i`, at which `λ' ≠ 0`. Deep in the cusp the
`q = exp(iπτ)`-chart is injective (`λ̃'(0) = 16 ≠ 0`, mean-value
estimate), the strip makes `q` itself injective, and away from the
cusp `‖λ‖` is bounded below by a compact-band minimum, which `‖w₀‖`
undercuts for `T` large. -/
theorem modularLambdaH_cusp_reference_value :
    ∃ (w₀ : ℂ) (τ₀ : ℂ), 0 < w₀.im ∧
      τ₀ ∈ Gamma2FundamentalDomainInterior ∧
      modularLambdaH τ₀ = w₀ ∧
      deriv modularLambdaH τ₀ ≠ 0 ∧
      ∀ τ ∈ Gamma2FundamentalDomainInterior, modularLambdaH τ = w₀ → τ = τ₀ := by
  -- ====================================================================
  -- Step 0a: pure arithmetic helpers, proved first (in an empty
  -- context) so that the nonlinear-arithmetic searches stay cheap.
  -- ====================================================================
  -- square-root comparison
  have h_sq_lt : ∀ a b : ℝ, 0 ≤ a → 0 < b → a ^ 2 < b ^ 2 → a < b := by
    intro a b ha hb h
    nlinarith
  -- squaring `1 < a`
  have h_one_lt_sq : ∀ a : ℝ, 1 < a → 1 < a ^ 2 := by
    intro a h
    nlinarith
  -- the semicircle constraint in coordinates
  have h_semi_helper : ∀ x y : ℝ, 1 < (2 * x - 1) ^ 2 + (2 * y) ^ 2 →
      x * (1 - x) < y ^ 2 := by
    intro x y h
    nlinarith
  -- cusp-0 band geometry: small `Im` and `Re ≤ 1/2` force `|σ| < 2·Im σ`
  have h_band0 : ∀ x y : ℝ, 0 < x → x ≤ 1/2 → 0 < y → y < 1/4 →
      x * (1 - x) < y ^ 2 → x * x + y * y < (2 * y) ^ 2 := by
    intro x y hx hx2 hy hy4 hs
    have h1 : x < 2 * y ^ 2 := by
      nlinarith [mul_nonneg hx.le (show (0:ℝ) ≤ 1/2 - x by linarith)]
    have h2 : 2 * y ^ 2 < y / 2 := by
      nlinarith [mul_pos hy (show (0:ℝ) < 1/4 - y by linarith)]
    nlinarith [mul_pos (show (0:ℝ) < y/2 - x by linarith)
      (show (0:ℝ) < y/2 + x by linarith), mul_pos hy hy]
  -- cusp-1 band geometry: small `Im` and `Re > 1/2` force `|σ−1| < 2·Im σ`
  have h_band1 : ∀ x y : ℝ, x < 1 → 1/2 < x → 0 < y → y < 1/4 →
      x * (1 - x) < y ^ 2 → (x - 1) * (x - 1) + y * y < (2 * y) ^ 2 := by
    intro x y hx1 hx2 hy hy4 hs
    have h1 : 1 - x < 2 * y ^ 2 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ x - 1/2 by linarith)
        (show (0:ℝ) ≤ 1 - x by linarith)]
    have h2 : 2 * y ^ 2 < y / 2 := by
      nlinarith [mul_pos hy (show (0:ℝ) < 1/4 - y by linarith)]
    nlinarith [mul_pos (show (0:ℝ) < y/2 - (1 - x) by linarith)
      (show (0:ℝ) < y/2 + (1 - x) by linarith), mul_pos hy hy]
  -- positivity of the deep-cusp derivative lower bound
  have h_deep_pos : ∀ p v : ℝ, 3 < p → p < 4 → 0 < v → v < 1/10000 →
      0 < 16 * p * v - 256 * p * v ^ 2 - 2112 * p * v ^ 3 - 100000 * v ^ 4 := by
    intro p v hp3 hp4 hv hv4
    have hv1 : v ≤ 1 := by linarith
    have h2 : v ^ 2 ≤ (1/10000) * v := by nlinarith
    have h3 : v ^ 3 ≤ v ^ 2 := by nlinarith [sq_nonneg v]
    have h21 : v ^ 2 ≤ 1 := by nlinarith
    have h4 : v ^ 4 ≤ v ^ 2 := by nlinarith [sq_nonneg v, sq_nonneg (v ^ 2)]
    have t1 : 256 * p * v ^ 2 ≤ 1024 * v ^ 2 := by nlinarith [sq_nonneg v]
    have t2 : 2112 * p * v ^ 3 ≤ 8448 * v ^ 3 := by nlinarith [pow_nonneg hv.le 3]
    have t3 : 48 * v ≤ 16 * p * v := by nlinarith
    have h3nn : (0:ℝ) ≤ v ^ 3 := pow_nonneg hv.le 3
    linarith
  -- smallness of the cusp-derivative error terms on `‖q‖ ≤ 1/100`
  have h_small_bound : ∀ t : ℝ, 0 ≤ t → t ≤ 1/100 →
      31000 * t ^ 3 + (2112 * t ^ 2 + 256 * t) ≤ 8 := by
    intro t h0 h1
    have hsq : t ^ 2 ≤ (1/100) * t := by nlinarith
    have hcb : t ^ 3 ≤ (1/100) * t ^ 2 := by nlinarith [sq_nonneg t]
    linarith
  -- ====================================================================
  -- Step 0b: numerical constants.
  -- ====================================================================
  have hπ_pos : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ_gt3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hπ_lt4 : Real.pi < 4 := Real.pi_lt_four
  have h_exp_pi_gt : (22:ℝ) < Real.exp Real.pi := exp_pi_gt_22
  have h_exp_pi_pos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  -- `exp π < 100`
  have h_exp_pi_lt : Real.exp Real.pi < 100 := by
    have h1 : Real.exp Real.pi < Real.exp 4 := Real.exp_lt_exp.mpr hπ_lt4
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
    have he := Real.exp_one_lt_d9
    have he_pos := Real.exp_pos 1
    have he2 : Real.exp 1 * Real.exp 1 < 7.389057 := by nlinarith [he, he_pos]
    have he4 : (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) < 60 := by
      nlinarith [he2, mul_pos he_pos he_pos]
    nlinarith [he4, h1, h4]
  -- `1/100 ≤ exp(−π)`
  have h_inv100_le : (1/100 : ℝ) ≤ Real.exp (-Real.pi) := by
    have h2 : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
      rw [← Real.exp_add]; simp
    have h_mul := mul_lt_mul_of_pos_left h_exp_pi_lt (Real.exp_pos (-Real.pi))
    rw [h2] at h_mul
    linarith only [h_mul]
  -- `484 < (exp π)²` and `10000 < (exp π)³`
  have h484 : (484:ℝ) < Real.exp Real.pi ^ 2 := by
    nlinarith [sq_nonneg (Real.exp Real.pi - 22), h_exp_pi_gt]
  have h10000 : (10000:ℝ) < Real.exp Real.pi ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h484.le) (sub_nonneg.mpr h_exp_pi_gt.le),
      h484, h_exp_pi_gt]
  -- `exp(−2π) < 1/100`
  have h_exp_2pi_lt : Real.exp (-(Real.pi * 2)) < 1/100 := by
    have h2 : Real.exp (-(Real.pi * 2)) * Real.exp Real.pi ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show -(Real.pi * 2) + (2:ℕ) * Real.pi = 0 by push_cast; ring]
      exact Real.exp_zero
    have h_mul := mul_lt_mul_of_pos_left h484 (Real.exp_pos (-(Real.pi * 2)))
    rw [h2] at h_mul
    linarith only [h_mul, Real.exp_pos (-(Real.pi * 2))]
  -- ====================================================================
  -- Step 1: the cusp chart `λ̃` is quantitatively injective on
  -- `closedBall 0 (1/100)`, via `‖λ̃' − 16‖ ≤ 8` there and the MVT.
  -- ====================================================================
  have h_diff_cusp : ∀ z : ℂ, ‖z‖ ≤ 1/100 → DifferentiableAt ℂ modularLambdaH_cusp z := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz_ne
    · exact modularLambdaH_cusp_differentiableAt_zero
    · exact modularLambdaH_cusp_differentiableAt_of_norm_lt_one hz_ne
        (lt_of_le_of_lt hz (by norm_num))
  have h_deriv_cusp_bound : ∀ z : ℂ, ‖z‖ ≤ 1/100 →
      ‖deriv modularLambdaH_cusp z - 16‖ ≤ 8 := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz_ne
    · rw [modularLambdaH_cusp_deriv_zero]
      simp
    · have hz_le : ‖z‖ ≤ Real.exp (-Real.pi) := le_trans hz h_inv100_le
      have h_w := modularLambdaH_cusp_deriv_sub_two_term_le_widened hz_le hz_ne
      have h_split : deriv modularLambdaH_cusp z - 16 =
          (deriv modularLambdaH_cusp z - 16 + 256 * z - 2112 * z ^ 2) +
            (2112 * z ^ 2 - 256 * z) := by ring
      rw [h_split]
      refine le_trans (norm_add_le _ _) ?_
      have h_t2 : ‖(2112:ℂ) * z ^ 2 - 256 * z‖ ≤ 2112 * ‖z‖ ^ 2 + 256 * ‖z‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_mul, norm_pow]
        have h1 : ‖(2112:ℂ)‖ = 2112 := by simp
        have h2 : ‖(256:ℂ)‖ = 256 := by simp
        rw [h1, h2]
      linarith only [h_w, h_t2, h_small_bound ‖z‖ (norm_nonneg z) hz]
  have h_cusp_injOn : ∀ x ∈ Metric.closedBall (0:ℂ) (1/100),
      ∀ y ∈ Metric.closedBall (0:ℂ) (1/100),
      modularLambdaH_cusp x = modularLambdaH_cusp y → x = y := by
    intro x hx y hy h_val_eq
    have h_ball_norm : ∀ z : ℂ, z ∈ Metric.closedBall (0:ℂ) (1/100) → ‖z‖ ≤ 1/100 := by
      intro z hz
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have h_hasDeriv : ∀ z : ℂ, ‖z‖ ≤ 1/100 →
        HasDerivAt (fun w : ℂ => modularLambdaH_cusp w - 16 * w)
          (deriv modularLambdaH_cusp z - 16) z := by
      intro z hz
      have h1 : HasDerivAt modularLambdaH_cusp (deriv modularLambdaH_cusp z) z :=
        (h_diff_cusp z hz).hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => (16:ℂ) * w) 16 z := by
        simpa using (hasDerivAt_id z).const_mul (16:ℂ)
      exact h1.sub h2
    have h_diff_f : ∀ z ∈ Metric.closedBall (0:ℂ) (1/100),
        DifferentiableAt ℂ (fun w : ℂ => modularLambdaH_cusp w - 16 * w) z := by
      intro z hz
      exact (h_hasDeriv z (h_ball_norm z hz)).differentiableAt
    have h_deriv_f_le : ∀ z ∈ Metric.closedBall (0:ℂ) (1/100),
        ‖deriv (fun w : ℂ => modularLambdaH_cusp w - 16 * w) z‖ ≤ 8 := by
      intro z hz
      rw [(h_hasDeriv z (h_ball_norm z hz)).deriv]
      exact h_deriv_cusp_bound z (h_ball_norm z hz)
    have h_mvt : ‖(modularLambdaH_cusp x - 16 * x) - (modularLambdaH_cusp y - 16 * y)‖ ≤
        8 * ‖x - y‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le h_diff_f h_deriv_f_le
        (convex_closedBall _ _) hy hx
    have h_diff_eq : (modularLambdaH_cusp x - 16 * x) - (modularLambdaH_cusp y - 16 * y) =
        -(16 * (x - y)) := by
      rw [h_val_eq]; ring
    rw [h_diff_eq, norm_neg, norm_mul] at h_mvt
    have h16 : ‖(16:ℂ)‖ = 16 := by simp
    rw [h16] at h_mvt
    have h_zero : ‖x - y‖ = 0 := by
      linarith only [h_mvt, norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h_zero)
  -- ====================================================================
  -- Step 2: cusp-0 and cusp-1 control, extracted from the tendsto lemmas.
  -- ====================================================================
  obtain ⟨δ₀, hδ₀_pos, h_cusp0⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp modularLambdaH_cusp_zero_tendsto_one_in_F
      (1/2) (by norm_num)
  have h_cusp1_ev : ∀ᶠ σ in nhdsWithin (1:ℂ) Gamma2FundamentalDomainInterior,
      (1:ℝ) ≤ ‖modularLambdaH σ‖ :=
    modularLambdaH_cusp_one_tendsto_norm_atTop_in_F.eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨δ₁, hδ₁_pos, h_cusp1⟩ := Metric.mem_nhdsWithin_iff.mp h_cusp1_ev
  -- the cusp-cutoff height ε₀
  set ε₀ : ℝ := min (min δ₀ δ₁ / 2) (1/4) with hε₀_def
  have hε₀_pos : 0 < ε₀ := lt_min (half_pos (lt_min hδ₀_pos hδ₁_pos)) (by norm_num)
  have hε₀_le_quarter : ε₀ ≤ 1/4 := min_le_right _ _
  have h_2ε₀_le_δ₀ : 2 * ε₀ ≤ δ₀ := by
    have h1 : ε₀ ≤ min δ₀ δ₁ / 2 := min_le_left _ _
    have h2 : min δ₀ δ₁ ≤ δ₀ := min_le_left _ _
    linarith only [h1, h2]
  have h_2ε₀_le_δ₁ : 2 * ε₀ ≤ δ₁ := by
    have h1 : ε₀ ≤ min δ₀ δ₁ / 2 := min_le_left _ _
    have h2 : min δ₀ δ₁ ≤ δ₁ := min_le_right _ _
    linarith only [h1, h2]
  -- ====================================================================
  -- Step 3: compactness minimum on the middle band, and the lower bound
  -- `c` for `‖λ‖` on all of `F^o ∩ {Im ≤ 2}`.
  -- ====================================================================
  set K : Set ℂ := Metric.closedBall (0:ℂ) 3 ∩ {z : ℂ | ε₀ ≤ z.im} with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0:ℂ) 3).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  have hK_pos_im : ∀ z ∈ K, 0 < z.im := fun z hz => lt_of_lt_of_le hε₀_pos hz.2
  have hK_ne : K.Nonempty := by
    refine ⟨(ε₀ : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, abs_of_pos hε₀_pos, mul_one]
      linarith only [hε₀_le_quarter]
    · change ε₀ ≤ ((ε₀ : ℂ) * Complex.I).im
      simp
  have h_cont : ContinuousOn (fun z => ‖modularLambdaH z‖) K := by
    intro z hz
    exact ((modularLambdaH_differentiableAt_of_im_pos
      (hK_pos_im z hz)).continuousAt.continuousWithinAt).norm
  obtain ⟨zmin, hzmin_mem, hzmin_min⟩ := hK_compact.exists_isMinOn hK_ne h_cont
  set c : ℝ := min (‖modularLambdaH zmin‖) (1/2) with hc_def
  have hc_pos : 0 < c :=
    lt_min (norm_pos_iff.mpr (modularLambdaH_ne_zero (hK_pos_im zmin hzmin_mem)))
      (by norm_num)
  have hc_le_half : c ≤ 1/2 := min_le_right _ _
  -- The lower bound on the sub-height-2 part of `F^o`.
  have h_lower : ∀ σ ∈ Gamma2FundamentalDomainInterior,
      σ.im ≤ 2 → c ≤ ‖modularLambdaH σ‖ := by
    intro σ hσ hσ_im_le
    obtain ⟨hσ_im_pos, hσ_re_pos, hσ_re_lt, hσ_semi⟩ := hσ
    by_cases h_im_case : ε₀ ≤ σ.im
    · -- middle band: compactness minimum
      have hσ_norm_le : ‖σ‖ ≤ 3 := by
        have h := Complex.norm_le_abs_re_add_abs_im σ
        rw [abs_of_pos hσ_re_pos, abs_of_pos hσ_im_pos] at h
        linarith only [h, hσ_re_lt, hσ_im_le]
      have hσK : σ ∈ K := by
        constructor
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hσ_norm_le
        · exact h_im_case
      calc c ≤ ‖modularLambdaH zmin‖ := min_le_left _ _
        _ ≤ ‖modularLambdaH σ‖ := hzmin_min hσK
    · rw [not_le] at h_im_case
      -- the semicircle constraint forces `Re·(1−Re) < Im²`
      have h_sq_gt : 1 < ‖2 * σ - 1‖ ^ 2 := h_one_lt_sq _ hσ_semi
      have h_norm_sq_eq : ‖2 * σ - 1‖ ^ 2 = (2 * σ.re - 1) ^ 2 + (2 * σ.im) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
          Complex.mul_im]
        ring
      rw [h_norm_sq_eq] at h_sq_gt
      have h_semi_sq : σ.re * (1 - σ.re) < σ.im ^ 2 := h_semi_helper σ.re σ.im h_sq_gt
      have hσ_im_lt_quarter : σ.im < 1/4 :=
        lt_of_lt_of_le h_im_case hε₀_le_quarter
      by_cases h_re_half : σ.re ≤ 1/2
      · -- near the cusp 0
        have h_norm_sq : ‖σ‖ ^ 2 < (2 * σ.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          exact h_band0 σ.re σ.im hσ_re_pos h_re_half hσ_im_pos hσ_im_lt_quarter h_semi_sq
        have h_norm_lt : ‖σ‖ < 2 * σ.im :=
          h_sq_lt ‖σ‖ (2 * σ.im) (norm_nonneg σ)
            (by linarith only [hσ_im_pos]) h_norm_sq
        have h_dist : dist σ 0 < δ₀ := by
          rw [dist_zero_right]
          calc ‖σ‖ < 2 * σ.im := h_norm_lt
            _ < 2 * ε₀ := by linarith only [h_im_case]
            _ ≤ δ₀ := h_2ε₀_le_δ₀
        have h_close := h_cusp0 ⟨hσ_im_pos, hσ_re_pos, hσ_re_lt, hσ_semi⟩ h_dist
        rw [dist_eq_norm] at h_close
        have h_tri : (1:ℝ) ≤ ‖modularLambdaH σ‖ + ‖modularLambdaH σ - 1‖ := by
          have h := norm_sub_le (modularLambdaH σ) (modularLambdaH σ - 1)
          have h2 : modularLambdaH σ - (modularLambdaH σ - 1) = 1 := by ring
          rw [h2, norm_one] at h
          exact h
        linarith only [h_tri, h_close, hc_le_half]
      · -- near the cusp 1
        rw [not_le] at h_re_half
        have h_norm_sq : ‖σ - 1‖ ^ 2 < (2 * σ.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
            sub_zero]
          exact h_band1 σ.re σ.im hσ_re_lt h_re_half hσ_im_pos hσ_im_lt_quarter h_semi_sq
        have h_norm_lt : ‖σ - 1‖ < 2 * σ.im :=
          h_sq_lt ‖σ - 1‖ (2 * σ.im) (norm_nonneg (σ - 1))
            (by linarith only [hσ_im_pos]) h_norm_sq
        have h_mem_ball : σ ∈ Metric.ball (1:ℂ) δ₁ := by
          rw [Metric.mem_ball, dist_eq_norm]
          calc ‖σ - 1‖ < 2 * σ.im := h_norm_lt
            _ < 2 * ε₀ := by linarith only [h_im_case]
            _ ≤ δ₁ := h_2ε₀_le_δ₁
        have h_ge_one : (1:ℝ) ≤ ‖modularLambdaH σ‖ :=
          h_cusp1 ⟨h_mem_ball, hσ_im_pos, hσ_re_pos, hσ_re_lt, hσ_semi⟩
        linarith only [h_ge_one, hc_le_half]
  -- ====================================================================
  -- Step 4: choice of the height `T` and the reference point `τ₀`.
  -- ====================================================================
  set T : ℝ := max 3 (Real.log (160000 / c) / Real.pi + 1) with hT_def
  have hT_ge_3 : (3:ℝ) ≤ T := le_max_left _ _
  have hT_ge_log : Real.log (160000 / c) / Real.pi + 1 ≤ T := le_max_right _ _
  set τ₀ : ℂ := ((1/2 : ℝ) : ℂ) + (T : ℂ) * Complex.I with hτ₀_def
  have hτ₀_re : τ₀.re = 1/2 := by
    rw [hτ₀_def]; simp
  have hτ₀_im : τ₀.im = T := by
    rw [hτ₀_def]; simp
  have hτ₀_mem : τ₀ ∈ Gamma2FundamentalDomainInterior := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hτ₀_im]; linarith only [hT_ge_3]
    · rw [hτ₀_re]; norm_num
    · rw [hτ₀_re]; norm_num
    · have h_eq : 2 * τ₀ - 1 = ((2 * T : ℝ) : ℂ) * Complex.I := by
        rw [hτ₀_def]; push_cast; ring
      rw [h_eq, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith only [hT_ge_3] : (0:ℝ) < 2 * T), mul_one]
      linarith only [hT_ge_3]
  -- the q-coordinate size at height T
  set u : ℝ := Real.exp (-(Real.pi * T)) with hu_def
  have hu_pos : 0 < u := Real.exp_pos _
  have h_u_lt : u < 1/10000 := by
    have hmul3 : Real.pi * 3 ≤ Real.pi * T := mul_le_mul_of_nonneg_left hT_ge_3 hπ_pos.le
    have h1 : u ≤ Real.exp (-(Real.pi * 3)) := by
      rw [hu_def]
      exact Real.exp_le_exp.mpr (by linarith only [hmul3])
    have h2 : Real.exp (-(Real.pi * 3)) * Real.exp Real.pi ^ 3 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show -(Real.pi * 3) + (3:ℕ) * Real.pi = 0 by push_cast; ring]
      exact Real.exp_zero
    have h_mul := mul_lt_mul_of_pos_left h10000 (Real.exp_pos (-(Real.pi * 3)))
    rw [h2] at h_mul
    linarith only [h1, h_mul, Real.exp_pos (-(Real.pi * 3))]
  -- real part of the exponent, and the chart norm identities
  have h_re_pi : ∀ σ : ℂ, ((Real.pi : ℂ) * Complex.I * σ).re = -(Real.pi * σ.im) := by
    intro σ
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_norm_E1 : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ = u := by
    rw [Complex.norm_exp, h_re_pi τ₀, hτ₀_im, hu_def]
  have h_E2_eq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h_E3_eq : Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) ^ 3 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h_norm_E2 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = u ^ 2 := by
    rw [h_E2_eq, norm_pow, h_norm_E1]
  have h_norm_E3 : ‖Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = u ^ 3 := by
    rw [h_E3_eq, norm_pow, h_norm_E1]
  have h_u4 : Real.exp (-4 * Real.pi * T) = u ^ 4 := by
    rw [hu_def, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- ====================================================================
  -- Step 5: nonvanishing of the derivative at `τ₀`.
  -- ====================================================================
  have h_deriv_ne : deriv modularLambdaH τ₀ ≠ 0 := by
    have h_im_ge_one : 1 ≤ τ₀.im := by rw [hτ₀_im]; linarith only [hT_ge_3]
    have h_bound := modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one h_im_ge_one
    rw [hτ₀_im, h_u4] at h_bound
    -- norms of the three leading terms
    have hA_norm : ‖(16:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ = 16 * Real.pi * u := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hπ_pos, h_norm_E1]
      norm_num
    have hB_norm : ‖(256:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = 256 * Real.pi * u ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hπ_pos, h_norm_E2]
      norm_num
    have hC_norm : ‖(2112:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = 2112 * Real.pi * u ^ 3 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hπ_pos, h_norm_E3]
      norm_num
    -- reverse triangle inequality
    have h_tri : ‖(16:ℂ) * (Real.pi : ℂ) * Complex.I *
          Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ ≤
        ‖deriv modularLambdaH τ₀ -
            16 * (Real.pi : ℂ) * Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) +
            256 * (Real.pi : ℂ) * Complex.I *
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀) -
            2112 * (Real.pi : ℂ) * Complex.I *
              Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ +
          ‖(256:ℂ) * (Real.pi : ℂ) * Complex.I *
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀)‖ +
          ‖(2112:ℂ) * (Real.pi : ℂ) * Complex.I *
              Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ +
          ‖deriv modularLambdaH τ₀‖ := by
      set D := deriv modularLambdaH τ₀ with hD_def
      set A := (16:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) with hA_def
      set B := (256:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀) with hB_def
      set C := (2112:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀) with hC_def
      have h_eq : A = -(D - A + B - C) + B + (-C) + D := by ring
      calc ‖A‖ = ‖-(D - A + B - C) + B + (-C) + D‖ := by rw [← h_eq]
        _ ≤ ‖-(D - A + B - C) + B + (-C)‖ + ‖D‖ := norm_add_le _ _
        _ ≤ ‖-(D - A + B - C) + B‖ + ‖-C‖ + ‖D‖ := by
            have h := norm_add_le (-(D - A + B - C) + B) (-C)
            linarith only [h]
        _ ≤ ‖-(D - A + B - C)‖ + ‖B‖ + ‖-C‖ + ‖D‖ := by
            have h := norm_add_le (-(D - A + B - C)) B
            linarith only [h]
        _ = ‖D - A + B - C‖ + ‖B‖ + ‖C‖ + ‖D‖ := by rw [norm_neg, norm_neg]
    rw [hA_norm, hB_norm, hC_norm] at h_tri
    have h_norm_lower : 16 * Real.pi * u - 256 * Real.pi * u ^ 2 -
        2112 * Real.pi * u ^ 3 - 100000 * u ^ 4 ≤ ‖deriv modularLambdaH τ₀‖ := by
      linarith only [h_bound, h_tri]
    have h_pos := h_deep_pos Real.pi u hπ_gt3 hπ_lt4 hu_pos h_u_lt
    exact norm_pos_iff.mp (lt_of_lt_of_le h_pos h_norm_lower)
  -- ====================================================================
  -- Step 6: smallness of the reference value: `‖λ(τ₀)‖ < c`.
  -- ====================================================================
  have h_w₀_lt_c : ‖modularLambdaH τ₀‖ < c := by
    have h_im_ge_one : 1 ≤ τ₀.im := by rw [hτ₀_im]; linarith only [hT_ge_3]
    have h_le := modularLambdaH_norm_le_exp_of_im_ge_one h_im_ge_one
    rw [hτ₀_im] at h_le
    have h_exp_eq : Real.exp (-Real.pi * T) = u := by
      rw [hu_def]; congr 1; ring
    rw [h_exp_eq] at h_le
    -- `160000·u < c` from the choice of `T`
    have h_ratio_pos : (0:ℝ) < 160000 / c := div_pos (by norm_num) hc_pos
    have h_log_lt : Real.log (160000 / c) < Real.pi * T := by
      have h1 : Real.log (160000 / c) / Real.pi ≤ T - 1 := by
        linarith only [hT_ge_log]
      have h2 : Real.log (160000 / c) ≤ (T - 1) * Real.pi := (div_le_iff₀ hπ_pos).mp h1
      have h3 : (T - 1) * Real.pi < T * Real.pi :=
        mul_lt_mul_of_pos_right (by linarith only []) hπ_pos
      linarith only [h2, h3]
    have h_lt_exp : 160000 / c < Real.exp (Real.pi * T) :=
      (Real.log_lt_iff_lt_exp h_ratio_pos).mp h_log_lt
    have h_uE : u * Real.exp (Real.pi * T) = 1 := by
      rw [hu_def, ← Real.exp_add,
        show -(Real.pi * T) + Real.pi * T = 0 by ring]
      exact Real.exp_zero
    have h3 : (160000 / c) * u < Real.exp (Real.pi * T) * u :=
      mul_lt_mul_of_pos_right h_lt_exp hu_pos
    rw [mul_comm (Real.exp (Real.pi * T)) u, h_uE] at h3
    have h4 := mul_lt_mul_of_pos_left h3 hc_pos
    rw [mul_one] at h4
    have h5 : c * (160000 / c * u) = 160000 * u := by
      field_simp
    rw [h5] at h4
    linarith only [h_le, h4]
  -- ====================================================================
  -- Step 7: the chart bridging identity.
  -- ====================================================================
  have h_bridge : ∀ σ : ℂ,
      modularLambdaH_cusp (Complex.exp ((Real.pi : ℂ) * Complex.I * σ)) =
        modularLambdaH σ := by
    intro σ
    have h_qe : Function.Periodic.qParam 2 σ =
        Complex.exp ((Real.pi : ℂ) * Complex.I * σ) := by
      unfold Function.Periodic.qParam
      congr 1
      push_cast
      ring
    rw [← h_qe]
    exact modularLambdaH_cusp_qParam σ
  have h_q₀_le : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ ≤ 1/100 := by
    rw [h_norm_E1]
    linarith only [h_u_lt]
  have h_q₀_mem : Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) ∈
      Metric.closedBall (0:ℂ) (1/100) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact h_q₀_le
  -- ====================================================================
  -- Step 8: assemble the five conjuncts.
  -- ====================================================================
  refine ⟨modularLambdaH τ₀, τ₀, modularLambdaH_F_im_pos τ₀ hτ₀_mem, hτ₀_mem, rfl,
    h_deriv_ne, ?_⟩
  intro τ hτ_mem hτ_eq
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt, hτ_semi⟩ := hτ_mem
  -- every `F^o`-preimage of `w₀` lives above height 2
  have hτ_im_gt : 2 < τ.im := by
    by_contra h_con
    rw [not_lt] at h_con
    have h_low := h_lower τ ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt, hτ_semi⟩ h_con
    rw [hτ_eq] at h_low
    linarith only [h_low, h_w₀_lt_c]
  -- its q-coordinate lies in the small disk
  have h_qτ_norm : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ)‖ =
      Real.exp (-(Real.pi * τ.im)) := by
    rw [Complex.norm_exp, h_re_pi τ]
  have h_qτ_le : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ)‖ ≤ 1/100 := by
    rw [h_qτ_norm]
    have hmul2 : Real.pi * 2 ≤ Real.pi * τ.im :=
      mul_le_mul_of_nonneg_left hτ_im_gt.le hπ_pos.le
    have h1 : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-(Real.pi * 2)) :=
      Real.exp_le_exp.mpr (by linarith only [hmul2])
    linarith only [h1, h_exp_2pi_lt]
  have h_qτ_mem : Complex.exp ((Real.pi : ℂ) * Complex.I * τ) ∈
      Metric.closedBall (0:ℂ) (1/100) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact h_qτ_le
  -- equal chart values, hence equal q-coordinates
  have h_vals : modularLambdaH_cusp (Complex.exp ((Real.pi : ℂ) * Complex.I * τ)) =
      modularLambdaH_cusp (Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)) := by
    rw [h_bridge τ, h_bridge τ₀, hτ_eq]
  have h_q_eq : Complex.exp ((Real.pi : ℂ) * Complex.I * τ) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) :=
    h_cusp_injOn _ h_qτ_mem _ h_q₀_mem h_vals
  -- unwind the exponential equality
  rw [Complex.exp_eq_exp_iff_exists_int] at h_q_eq
  obtain ⟨n, hn⟩ := h_q_eq
  have hπI_ne : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hπ_pos)) Complex.I_ne_zero
  have h_τ_eq : τ = τ₀ + 2 * (n : ℂ) := by
    apply mul_left_cancel₀ hπI_ne
    rw [hn]
    ring
  have h_re_eq : τ.re = 1/2 + 2 * (n:ℝ) := by
    rw [h_τ_eq, Complex.add_re, hτ₀_re]
    simp
  rw [h_re_eq] at hτ_re_pos hτ_re_lt
  have h1 : (n:ℝ) < 1 := by linarith only [hτ_re_lt]
  have h2 : (-1:ℝ) < (n:ℝ) := by linarith only [hτ_re_pos]
  have h1' : n < 1 := by exact_mod_cast h1
  have h2' : (-1:ℤ) < n := by exact_mod_cast h2
  have hn0 : n = 0 := by omega
  rw [h_τ_eq, hn0]
  simp


set_option maxHeartbeats 400000 in
-- The six-piece chain-rule/substitution conversion is elaboration-heavy.
/-- **Bridge: F_Y boundary integral expression equals image-curve
contour integral.** For valid F_Y parameters with `λ ≠ w` on each of
the six boundary pieces, the six-term AP-derived boundary integral
expression (with the standard CCW orientation signs) coincides with
`Complex.pathContourIntegral (λ ∘ F_Y_boundary_parameterization δ Y R₀)`
of `(z − w)⁻¹` over `[0, 6]`.

Proof: split the `[0, 6]` integral into six segments `[k, k+1]` for
`k = 0, …, 5`. On each segment `F_Y_boundary_parameterization`
restricts to one of the six smooth piece formulas (linear edges or
the semicircle arc). For each piece, apply the chain rule (with the
piece's affine/circle derivative) and substitute the natural parameter
(`x` for horizontal edges, `y` for vertical edges, `θ` for the arc) to
match the corresponding term in the boundary integral. The signs
match: edges traversed in the parameter's positive direction get a
`+`, those in the reverse direction get a `−`, the arc with parameter
`π(2 − t)` reversal gets a `−`. -/
theorem modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    (∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w)⁻¹) := by
  -- The γ_full integrand.
  set u : ℝ → ℂ := fun t =>
    (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w)⁻¹ *
      deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) t
  -- λ facts on ℍ.
  have hH_open : IsOpen {τ : ℂ | 0 < τ.im} :=
    Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  have h_lam_deriv_cont : ContinuousOn (deriv modularLambdaH) {τ : ℂ | 0 < τ.im} :=
    (modularLambdaH_differentiableOn.analyticOnNhd hH_open).deriv.continuousOn
  have hst : IsScalarTower ℝ ℂ ℂ := IsScalarTower.right
  have hY_pos : 0 < Y := lt_trans hδ hδY
  -- Per-piece engine: a globally differentiable formula matching the boundary
  -- parameterization on `[a, b]`, mapping `[a, b]` into `ℍ`, and avoiding `w`
  -- yields the chain-rule identity for the piece, plus interval-integrability
  -- of the γ_full integrand on the piece.
  have h_piece : ∀ (a b : ℝ) (formula formula' : ℝ → ℂ),
      a ≤ b →
      (∀ t : ℝ, HasDerivAt formula (formula' t) t) →
      Continuous formula' →
      (∀ t ∈ Set.Icc a b, 0 < (formula t).im) →
      (∀ t ∈ Set.Icc a b, F_Y_boundary_parameterization δ Y R₀ t = formula t) →
      (∀ t ∈ Set.Icc a b, modularLambdaH (formula t) - w ≠ 0) →
      ((∫ t in a..b, u t) =
          ∫ t in a..b, (modularLambdaH (formula t) - w)⁻¹ *
            (formula' t • deriv modularLambdaH (formula t))) ∧
        IntervalIntegrable u MeasureTheory.volume a b := by
    intro a b formula formula' hab h_form_d h_form'_cont h_im_pos h_F_eq h_ne
    have h_form_cont : Continuous formula :=
      continuous_iff_continuousAt.mpr fun t => (h_form_d t).continuousAt
    set V : Set ℝ := {t : ℝ | 0 < (formula t).im}
    have hV_open : IsOpen V :=
      (Complex.continuous_im.comp h_form_cont).isOpen_preimage _ isOpen_Ioi
    have h_Icc_V : Set.Icc a b ⊆ V := h_im_pos
    -- Chain rule on V via scomp with explicit scalar-tower instance.
    have h_chain : ∀ t ∈ V, HasDerivAt (fun s => modularLambdaH (formula s))
        (formula' t • deriv modularLambdaH (formula t)) t := by
      intro t ht
      have h_im : 0 < (formula t).im := ht
      have h_lam_d : HasDerivAt modularLambdaH
          (deriv modularLambdaH (formula t)) (formula t) :=
        (modularLambdaH_differentiableAt_of_im_pos h_im).hasDerivAt
      exact @HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ hst _ _ _ _ h_lam_d (h_form_d t)
    have h_g_cont : ContinuousOn
        (fun t => formula' t • deriv modularLambdaH (formula t)) V := by
      refine ContinuousOn.smul h_form'_cont.continuousOn ?_
      refine h_lam_deriv_cont.comp h_form_cont.continuousOn ?_
      intro t ht; exact ht
    have h_deriv_eqOn : Set.EqOn (deriv (fun s => modularLambdaH (formula s)))
        (fun t => formula' t • deriv modularLambdaH (formula t)) V :=
      fun t ht => (h_chain t ht).deriv
    have h_deriv_cont : ContinuousOn
        (deriv (fun s => modularLambdaH (formula s))) V :=
      h_g_cont.congr h_deriv_eqOn
    -- The formula integrand.
    set v : ℝ → ℂ := fun t =>
      (modularLambdaH (formula t) - w)⁻¹ *
        deriv (fun s => modularLambdaH (formula s)) t
    -- v is continuous on the closed piece, hence interval-integrable.
    have h_v_cont : ContinuousOn v (Set.Icc a b) := by
      intro t ht
      have htV : t ∈ V := h_Icc_V ht
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt (fun s => modularLambdaH (formula s)) t :=
        (h_chain t htV).continuousAt
      have h2 : ContinuousAt (deriv (fun s => modularLambdaH (formula s))) t :=
        h_deriv_cont.continuousAt (hV_open.mem_nhds htV)
      refine ContinuousAt.mul ?_ h2
      refine ContinuousAt.inv₀ (h1.sub continuousAt_const) ?_
      exact h_ne t ht
    have h_v_ii : IntervalIntegrable v MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]; exact h_v_cont
    -- u = v a.e. on uIoc a b: they can differ only at the corner b.
    have h_ae_imp : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        x ∈ Set.uIoc a b → u x = v x := by
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null (t := {b}) ?_
        (MeasureTheory.measure_singleton b)
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      push Not at hx
      obtain ⟨hx_ioc, hx_ne⟩ := hx
      rw [Set.uIoc_of_le hab] at hx_ioc
      rw [Set.mem_singleton_iff]
      by_contra h_xb
      apply hx_ne
      have hx_oo : x ∈ Set.Ioo a b := ⟨hx_ioc.1, lt_of_le_of_ne hx_ioc.2 h_xb⟩
      have hx_icc : x ∈ Set.Icc a b := ⟨le_of_lt hx_oo.1, le_of_lt hx_oo.2⟩
      have h_eq_nbhd :
          (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) =ᶠ[nhds x]
          (fun s => modularLambdaH (formula s)) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.Ioo a b, isOpen_Ioo.mem_nhds hx_oo, fun y hy => ?_⟩
        change modularLambdaH (F_Y_boundary_parameterization δ Y R₀ y) =
          modularLambdaH (formula y)
        rw [h_F_eq y ⟨le_of_lt hy.1, le_of_lt hy.2⟩]
      have h_deriv_eq :
          deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) x =
          deriv (fun s => modularLambdaH (formula s)) x := h_eq_nbhd.deriv_eq
      change (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ x) - w)⁻¹ *
          deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) x =
        (modularLambdaH (formula x) - w)⁻¹ *
          deriv (fun s => modularLambdaH (formula s)) x
      rw [h_F_eq x hx_icc, h_deriv_eq]
    have h_int_eq : (∫ t in a..b, u t) = ∫ t in a..b, v t :=
      intervalIntegral.integral_congr_ae h_ae_imp
    have h_uv_ae : u =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] v :=
      (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr h_ae_imp
    have h_u_ii : IntervalIntegrable u MeasureTheory.volume a b :=
      h_v_ii.congr_ae h_uv_ae.symm
    -- Rewrite the deriv of the composition via the chain rule on all of [a, b].
    have h_v_to_chain : (∫ t in a..b, v t) =
        ∫ t in a..b, (modularLambdaH (formula t) - w)⁻¹ *
          (formula' t • deriv modularLambdaH (formula t)) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have htV : t ∈ V := h_Icc_V ht
      change (modularLambdaH (formula t) - w)⁻¹ *
          deriv (fun s => modularLambdaH (formula s)) t =
        (modularLambdaH (formula t) - w)⁻¹ *
          (formula' t • deriv modularLambdaH (formula t))
      rw [(h_chain t htV).deriv]
    exact ⟨h_int_eq.trans h_v_to_chain, h_u_ii⟩
  -- Continuity of the horizontal-edge target integrand.
  have h_g_cont_horiz : ∀ (c A B : ℝ), 0 < c →
      (∀ x ∈ Set.Icc A B, modularLambdaH ((x : ℂ) + (c : ℂ) * Complex.I) - w ≠ 0) →
      ContinuousOn (fun s : ℝ => deriv modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I) /
        (modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I) - w)) (Set.Icc A B) := by
    intro c A B hc h_ne_c
    have hφ : Continuous (fun s : ℝ => (s : ℂ) + (c : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    have h_maps : ∀ s ∈ Set.Icc A B,
        ((s : ℂ) + (c : ℂ) * Complex.I) ∈ {τ : ℂ | 0 < τ.im} := by
      intro s _
      change 0 < ((s : ℂ) + (c : ℂ) * Complex.I).im
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re] using hc
    have h_num : ContinuousOn
        (fun s : ℝ => deriv modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I))
        (Set.Icc A B) := h_lam_deriv_cont.comp hφ.continuousOn h_maps
    have h_den : ContinuousOn
        (fun s : ℝ => modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I) - w)
        (Set.Icc A B) :=
      (modularLambdaH_differentiableOn.continuousOn.comp hφ.continuousOn h_maps).sub
        continuousOn_const
    exact h_num.div h_den h_ne_c
  -- Continuity of the vertical-edge target integrand.
  have h_g_cont_vert : ∀ (e : ℂ), e.im = 0 →
      (∀ y ∈ Set.Icc δ Y, modularLambdaH (e + (y : ℂ) * Complex.I) - w ≠ 0) →
      ContinuousOn (fun s : ℝ => deriv modularLambdaH (e + (s : ℂ) * Complex.I) /
        (modularLambdaH (e + (s : ℂ) * Complex.I) - w)) (Set.Icc δ Y) := by
    intro e he_im h_ne_e
    have hφ : Continuous (fun s : ℝ => e + (s : ℂ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_maps : ∀ s ∈ Set.Icc δ Y,
        (e + (s : ℂ) * Complex.I) ∈ {τ : ℂ | 0 < τ.im} := by
      intro s hs
      change 0 < (e + (s : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, he_im]
      have hs1 : δ ≤ s := hs.1
      nlinarith
    have h_num : ContinuousOn
        (fun s : ℝ => deriv modularLambdaH (e + (s : ℂ) * Complex.I))
        (Set.Icc δ Y) := h_lam_deriv_cont.comp hφ.continuousOn h_maps
    have h_den : ContinuousOn
        (fun s : ℝ => modularLambdaH (e + (s : ℂ) * Complex.I) - w)
        (Set.Icc δ Y) :=
      (modularLambdaH_differentiableOn.continuousOn.comp hφ.continuousOn h_maps).sub
        continuousOn_const
    exact h_num.div h_den h_ne_e
  -- Continuity of the arc target integrand.
  have h_g_arc_cont : ContinuousOn (fun θ : ℝ =>
      deriv modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
      (modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) (Set.Icc 0 Real.pi) := by
    have hφ : Continuous (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) :=
      continuous_circleMap _ _
    have h_maps : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
        _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ ∈
          {τ : ℂ | 0 < τ.im} := by
      intro θ hθ
      have h_cm_im : ∀ (c : ℂ) (R θ' : ℝ),
          (_root_.circleMap c R θ').im = c.im + R * Real.sin θ' := by
        intro c R θ'
        unfold _root_.circleMap
        rw [Complex.exp_mul_I]
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
      change 0 < (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im
      rw [h_cm_im]
      have h_c_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re]
      rw [h_c_im]
      have h_sin_nn : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      nlinarith [mul_nonneg hR₀_pos.le h_sin_nn]
    have h_num : ContinuousOn (fun θ : ℝ =>
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ))
        (Set.Icc 0 Real.pi) := h_lam_deriv_cont.comp hφ.continuousOn h_maps
    have h_den : ContinuousOn (fun θ : ℝ =>
        modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w)
        (Set.Icc 0 Real.pi) :=
      (modularLambdaH_differentiableOn.continuousOn.comp hφ.continuousOn h_maps).sub
        continuousOn_const
    have h_exp_cont : Continuous
        (fun θ : ℝ => Complex.I * R₀ * Complex.exp (Complex.I * θ)) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))
    exact (h_num.div h_den hg_arc).mul h_exp_cont.continuousOn
  -- Piece 0: bottom-left edge.
  have h0_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)
      ((1 / 2 - R₀ : ℂ)) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    simpa using (h1.mul_const ((1 / 2 - R₀ : ℂ))).add_const ((δ : ℂ) * Complex.I)
  have h0_im : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re] using hδ
  have h0_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F_Y_boundary_parameterization δ Y R₀ t =
      (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I := by
    intro t ht
    unfold F_Y_boundary_parameterization
    rw [if_pos ht.2]
  have h0_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h_pt : (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I =
        ((t * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_pt]
    exact hg_bot_left (t * (1 / 2 - R₀)) ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hI0, hII0⟩ := h_piece 0 1
    (fun t : ℝ => (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)
    (fun _ : ℝ => (1 / 2 - R₀ : ℂ))
    (by norm_num) h0_d continuous_const h0_im h0_eq h0_ne
  have h0_conv : (∫ t in (0 : ℝ)..1, u t) =
      ∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
    have h_f_d : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => t * (1 / 2 - R₀)) ((fun _ : ℝ => 1 / 2 - R₀) x) x :=
      fun x _ => hasDerivAt_mul_const _
    have h_img : (fun t : ℝ => t * (1 / 2 - R₀)) '' Set.uIcc (0 : ℝ) 1 ⊆
        Set.Icc (0 : ℝ) (1 / 2 - R₀) := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have h_eq' : t * (1 / 2 - R₀) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (0 : ℝ)..1, (fun _ : ℝ => 1 / 2 - R₀) t •
          ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => t * (1 / 2 - R₀))) t) =
        ∫ x in ((0 : ℝ) * (1 / 2 - R₀))..((1 : ℝ) * (1 / 2 - R₀)),
          deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
          (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_horiz δ 0 (1 / 2 - R₀) hδ hg_bot_left).mono h_img)
    calc (∫ t in (0 : ℝ)..1, u t)
        = ∫ t in (0 : ℝ)..1,
            (modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)) := hI0
      _ = ∫ t in (0 : ℝ)..1, (fun _ : ℝ => 1 / 2 - R₀) t •
            ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
              (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
              (fun t : ℝ => t * (1 / 2 - R₀))) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)) =
            (1 / 2 - R₀ : ℝ) •
              (deriv modularLambdaH (((t * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I) /
                (modularLambdaH (((t * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = ∫ x in ((0 : ℝ) * (1 / 2 - R₀))..((1 : ℝ) * (1 / 2 - R₀)),
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := h_subst
      _ = ∫ x in (0 : ℝ)..(1 / 2 - R₀),
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
          rw [zero_mul, one_mul]
  -- Piece 1: semicircular arc.
  have h1_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t)))
      ((Real.pi * -1 : ℝ) •
        (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => Real.pi * (2 - s)) (Real.pi * -1) t := by
      have h := ((hasDerivAt_id t).const_sub (2 : ℝ)).const_mul Real.pi
      simpa using h
    have h_outer := hasDerivAt_circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi * (2 - t))
    have h_comp := h_outer.scomp t h_inner
    simpa [Function.comp] using h_comp
  have h1_cont : Continuous (fun t : ℝ => (Real.pi * -1 : ℝ) •
      (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) := by
    refine Continuous.const_smul ?_ _
    refine Continuous.mul ?_ continuous_const
    exact (continuous_circleMap 0 R₀).comp (by fun_prop)
  have h1_im : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      0 < (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t))).im := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have h_cm_im : ∀ (c : ℂ) (R θ : ℝ),
        (_root_.circleMap c R θ).im = c.im + R * Real.sin θ := by
      intro c R θ
      unfold _root_.circleMap
      rw [Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
    rw [h_cm_im]
    have h_c_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
    rw [h_c_im]
    have h_sin_nn : 0 ≤ Real.sin (Real.pi * (2 - t)) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · have h2t : (0 : ℝ) ≤ 2 - t := by linarith
        positivity
      · nlinarith [Real.pi_pos]
    nlinarith [mul_nonneg hR₀_pos.le h_sin_nn]
  have h1_eq : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      F_Y_boundary_parameterization δ Y R₀ t =
      _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t)) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    unfold F_Y_boundary_parameterization
    rcases eq_or_lt_of_le ht1 with h_eq | h_lt
    · -- t = 1: junction with piece 0.
      rw [← h_eq]
      rw [if_pos (le_refl 1)]
      unfold _root_.circleMap
      have h_angle : ((Real.pi * (2 - 1) : ℝ) : ℂ) * Complex.I =
          (Real.pi : ℂ) * Complex.I := by push_cast; ring
      rw [h_angle, Complex.exp_pi_mul_I]
      push_cast; ring
    · rw [if_neg (not_le.mpr h_lt), if_pos ht2]
  have h1_ne : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t))) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    refine hg_arc (Real.pi * (2 - t)) ⟨?_, ?_⟩
    · exact mul_nonneg Real.pi_pos.le (by linarith)
    · nlinarith [Real.pi_pos]
  obtain ⟨hI1, hII1⟩ := h_piece 1 2
    (fun t : ℝ => _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi * (2 - t)))
    (fun t : ℝ => (Real.pi * -1 : ℝ) •
      (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I))
    (by norm_num) h1_d h1_cont h1_im h1_eq h1_ne
  have h1_conv : (∫ t in (1 : ℝ)..2, u t) =
      -∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := by
    have h_f_d : ∀ x ∈ Set.uIcc (1 : ℝ) 2,
        HasDerivAt (fun t : ℝ => Real.pi * (2 - t)) ((fun _ : ℝ => Real.pi * -1) x) x := by
      intro x _
      simpa using ((hasDerivAt_id x).const_sub (2 : ℝ)).const_mul Real.pi
    have h_img : (fun t : ℝ => Real.pi * (2 - t)) '' Set.uIcc (1 : ℝ) 2 ⊆
        Set.Icc (0 : ℝ) Real.pi := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      have h_eq' : Real.pi * (2 - t) = p := h_eq
      rw [← h_eq']
      constructor
      · exact mul_nonneg Real.pi_pos.le (by linarith)
      · nlinarith [Real.pi_pos]
    have h_cm : ∀ θ : ℝ, _root_.circleMap 0 R₀ θ * Complex.I =
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      intro θ
      unfold _root_.circleMap
      rw [mul_comm ((θ : ℝ) : ℂ) Complex.I]
      ring
    have h_subst : (∫ t in (1 : ℝ)..2, (fun _ : ℝ => Real.pi * -1) t •
          ((fun θ : ℝ =>
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ))) ∘
            (fun t : ℝ => Real.pi * (2 - t))) t) =
        ∫ θ in (Real.pi * (2 - 1))..(Real.pi * (2 - 2)),
          deriv modularLambdaH
            (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
          (modularLambdaH
            (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        (h_g_arc_cont.mono h_img)
    calc (∫ t in (1 : ℝ)..2, u t)
        = ∫ t in (1 : ℝ)..2,
            (modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
              (Real.pi * (2 - t))) - w)⁻¹ *
              (((Real.pi * -1 : ℝ) •
                (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) *
                deriv modularLambdaH (_root_.circleMap
                  ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t)))) := hI1
      _ = ∫ t in (1 : ℝ)..2, (fun _ : ℝ => Real.pi * -1) t •
            ((fun θ : ℝ =>
              deriv modularLambdaH
                (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
              (modularLambdaH
                (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
              (Complex.I * R₀ * Complex.exp (Complex.I * θ))) ∘
              (fun t : ℝ => Real.pi * (2 - t))) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
              (Real.pi * (2 - t))) - w)⁻¹ *
              (((Real.pi * -1 : ℝ) •
                (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) *
                deriv modularLambdaH (_root_.circleMap
                  ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t)))) =
            (Real.pi * -1 : ℝ) •
              (deriv modularLambdaH (_root_.circleMap
                ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t))) /
              (modularLambdaH (_root_.circleMap
                ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t))) - w) *
              (Complex.I * R₀ * Complex.exp (Complex.I * ((Real.pi * (2 - t) : ℝ) : ℂ))))
          rw [h_cm (Real.pi * (2 - t)), Complex.real_smul, Complex.real_smul]
          push_cast
          ring
      _ = ∫ θ in (Real.pi * (2 - 1))..(Real.pi * (2 - 2)),
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := h_subst
      _ = ∫ θ in Real.pi..(0 : ℝ),
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := by
          rw [show Real.pi * (2 - 1) = Real.pi from by ring,
            show Real.pi * (2 - 2) = 0 from by ring]
      _ = -∫ θ in (0 : ℝ)..Real.pi,
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ)) :=
          intervalIntegral.integral_symm 0 Real.pi
  -- Piece 2: bottom-right edge.
  have h2_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I)
      ((1 / 2 - R₀ : ℂ)) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 := (((h1.sub_const (2 : ℂ)).mul_const ((1 / 2 - R₀ : ℂ))).const_add
      ((1 / 2 + R₀ : ℂ))).add_const ((δ : ℂ) * Complex.I)
    simpa using h2
  have h2_im : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      0 < ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.sub_re, Complex.I_im, Complex.I_re] using hδ
  have h2_eq : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      F_Y_boundary_parameterization δ Y R₀ t =
      (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht2, ht3⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    rcases eq_or_lt_of_le ht2 with h_eq | h_lt
    · -- t = 2: junction with the arc piece.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (2 : ℝ) ≤ 1), if_pos (le_refl (2 : ℝ))]
      unfold _root_.circleMap
      have h_angle : ((Real.pi * (2 - 2) : ℝ) : ℂ) * Complex.I = 0 := by
        push_cast; ring
      rw [h_angle, Complex.exp_zero]
      push_cast; ring
    · rw [if_neg h_not1, if_neg (not_le.mpr h_lt), if_pos ht3]
  have h2_ne : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
        (δ : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht2, ht3⟩ := ht
    have h_pt : (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I =
        ((1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_pt]
    exact hg_bot_right (1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀)) ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hI2, hII2⟩ := h_piece 2 3
    (fun t : ℝ => (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I)
    (fun _ : ℝ => (1 / 2 - R₀ : ℂ))
    (by norm_num) h2_d continuous_const h2_im h2_eq h2_ne
  have h2_conv : (∫ t in (2 : ℝ)..3, u t) =
      ∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
    have h_f_d : ∀ x ∈ Set.uIcc (2 : ℝ) 3,
        HasDerivAt (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀))
          ((fun _ : ℝ => 1 / 2 - R₀) x) x := by
      intro x _
      simpa using (((hasDerivAt_id x).sub_const (2 : ℝ)).mul_const
        (1 / 2 - R₀)).const_add (1 / 2 + R₀)
    have h_img : (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀)) ''
        Set.uIcc (2 : ℝ) 3 ⊆ Set.Icc (1 / 2 + R₀ : ℝ) 1 := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
      obtain ⟨ht2, ht3⟩ := ht
      have h_eq' : 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (2 : ℝ)..3, (fun _ : ℝ => 1 / 2 - R₀) t •
          ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀))) t) =
        ∫ x in (1 / 2 + R₀ + ((2 : ℝ) - 2) * (1 / 2 - R₀))..(1 / 2 + R₀ +
            ((3 : ℝ) - 2) * (1 / 2 - R₀)),
          deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
          (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_horiz δ (1 / 2 + R₀) 1 hδ hg_bot_right).mono h_img)
    calc (∫ t in (2 : ℝ)..3, u t)
        = ∫ t in (2 : ℝ)..3,
            (modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
              (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
                  (δ : ℂ) * Complex.I)) := hI2
      _ = ∫ t in (2 : ℝ)..3, (fun _ : ℝ => 1 / 2 - R₀) t •
            ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
              (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
              (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀))) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
              (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
                  (δ : ℂ) * Complex.I)) =
            (1 / 2 - R₀ : ℝ) •
              (deriv modularLambdaH
                (((1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I) /
                (modularLambdaH
                  (((1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) : ℝ) : ℂ) +
                    (δ : ℂ) * Complex.I) - w))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = ∫ x in (1 / 2 + R₀ + ((2 : ℝ) - 2) * (1 / 2 - R₀))..(1 / 2 + R₀ +
            ((3 : ℝ) - 2) * (1 / 2 - R₀)),
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := h_subst
      _ = ∫ x in (1 / 2 + R₀ : ℝ)..1,
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
          rw [show 1 / 2 + R₀ + ((2 : ℝ) - 2) * (1 / 2 - R₀) = 1 / 2 + R₀ from by ring,
            show 1 / 2 + R₀ + ((3 : ℝ) - 2) * (1 / 2 - R₀) = 1 from by ring]
  -- Piece 3: right edge.
  have h3_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)
      (((Y - δ : ℂ)) * Complex.I) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 := ((((h1.sub_const (3 : ℂ)).mul_const ((Y - δ : ℂ))).const_add
      ((δ : ℂ))).mul_const Complex.I).const_add (1 : ℂ)
    simpa using h2
  have h3_im : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      0 < ((1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I).im := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.sub_re, Complex.I_im, Complex.I_re]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - 3) (by linarith : (0:ℝ) ≤ Y - δ)]
  have h3_eq : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      F_Y_boundary_parameterization δ Y R₀ t =
      (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    rcases eq_or_lt_of_le ht3 with h_eq | h_lt
    · -- t = 3: junction with the bottom-right edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (3 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (3 : ℝ) ≤ 2),
        if_pos (le_refl (3 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg (not_le.mpr h_lt), if_pos ht4]
  have h3_ne : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      modularLambdaH ((1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    have h_pt : (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I =
        (1 : ℂ) + ((δ + (t - 3) * (Y - δ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_pt]
    exact hg_right (δ + (t - 3) * (Y - δ)) ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hI3, hII3⟩ := h_piece 3 4
    (fun t : ℝ => (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)
    (fun _ : ℝ => ((Y - δ : ℂ)) * Complex.I)
    (by norm_num) h3_d continuous_const h3_im h3_eq h3_ne
  have h3_conv : (∫ t in (3 : ℝ)..4, u t) =
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
    have h_f_d : ∀ x ∈ Set.uIcc (3 : ℝ) 4,
        HasDerivAt (fun t : ℝ => δ + (t - 3) * (Y - δ)) ((fun _ : ℝ => Y - δ) x) x := by
      intro x _
      simpa using (((hasDerivAt_id x).sub_const (3 : ℝ)).mul_const (Y - δ)).const_add δ
    have h_img : (fun t : ℝ => δ + (t - 3) * (Y - δ)) '' Set.uIcc (3 : ℝ) 4 ⊆
        Set.Icc δ Y := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at ht
      obtain ⟨ht3, ht4⟩ := ht
      have h_eq' : δ + (t - 3) * (Y - δ) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (3 : ℝ)..4, (fun _ : ℝ => Y - δ) t •
          ((fun y : ℝ => deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => δ + (t - 3) * (Y - δ))) t) =
        ∫ y in (δ + ((3 : ℝ) - 3) * (Y - δ))..(δ + ((4 : ℝ) - 3) * (Y - δ)),
          deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
          (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_vert 1 Complex.one_im hg_right).mono h_img)
    calc (∫ t in (3 : ℝ)..4, u t)
        = ∫ t in (3 : ℝ)..4,
            (modularLambdaH ((1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I) - w)⁻¹ *
              ((Y - δ : ℂ) * Complex.I *
                deriv modularLambdaH ((1 : ℂ) +
                  ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)) := hI3
      _ = ∫ t in (3 : ℝ)..4, Complex.I *
            ((fun _ : ℝ => Y - δ) t •
              ((fun y : ℝ => deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => δ + (t - 3) * (Y - δ))) t) := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH ((1 : ℂ) +
              ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I) - w)⁻¹ *
              ((Y - δ : ℂ) * Complex.I *
                deriv modularLambdaH ((1 : ℂ) +
                  ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)) =
            Complex.I * ((Y - δ : ℝ) •
              (deriv modularLambdaH ((1 : ℂ) +
                ((δ + (t - 3) * (Y - δ) : ℝ) : ℂ) * Complex.I) /
              (modularLambdaH ((1 : ℂ) +
                ((δ + (t - 3) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = Complex.I * ∫ t in (3 : ℝ)..4,
            (fun _ : ℝ => Y - δ) t •
              ((fun y : ℝ => deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => δ + (t - 3) * (Y - δ))) t :=
          intervalIntegral.integral_const_mul Complex.I _
      _ = Complex.I * ∫ y in (δ + ((3 : ℝ) - 3) * (Y - δ))..(δ + ((4 : ℝ) - 3) * (Y - δ)),
            deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w) := by
          rw [h_subst]
      _ = Complex.I * (∫ y in (δ : ℝ)..Y,
            deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
          rw [show δ + ((3 : ℝ) - 3) * (Y - δ) = δ from by ring,
            show δ + ((4 : ℝ) - 3) * (Y - δ) = Y from by ring]
  -- Piece 4: top edge.
  have h4_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)
      (((-1 : ℝ) : ℂ)) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => 5 - s) (-1) t :=
      (hasDerivAt_id t).const_sub 5
    exact (h_inner.ofReal_comp).add_const ((Y : ℂ) * Complex.I)
  have h4_im : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      0 < (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re] using hY_pos
  have h4_eq : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      F_Y_boundary_parameterization δ Y R₀ t =
      ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht4, ht5⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    have h_not3 : ¬ t ≤ 3 := by linarith
    rcases eq_or_lt_of_le ht4 with h_eq | h_lt
    · -- t = 4: junction with the right edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (4 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (4 : ℝ) ≤ 2),
        if_neg (by norm_num : ¬ (4 : ℝ) ≤ 3), if_pos (le_refl (4 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg h_not3, if_neg (not_le.mpr h_lt),
        if_pos ht5]
  have h4_ne : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht4, ht5⟩ := ht
    exact hg_top (5 - t) ⟨by linarith, by linarith⟩
  obtain ⟨hI4, hII4⟩ := h_piece 4 5
    (fun t : ℝ => ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)
    (fun _ : ℝ => ((-1 : ℝ) : ℂ))
    (by norm_num) h4_d continuous_const h4_im h4_eq h4_ne
  have h4_conv : (∫ t in (4 : ℝ)..5, u t) =
      -∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) := by
    have h_f_d : ∀ x ∈ Set.uIcc (4 : ℝ) 5,
        HasDerivAt (fun t : ℝ => 5 - t) ((fun _ : ℝ => (-1 : ℝ)) x) x := by
      intro x _
      simpa using (hasDerivAt_id x).const_sub (5 : ℝ)
    have h_img : (fun t : ℝ => 5 - t) '' Set.uIcc (4 : ℝ) 5 ⊆
        Set.Icc (0 : ℝ) 1 := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)] at ht
      obtain ⟨ht4, ht5⟩ := ht
      have h_eq' : 5 - t = p := h_eq
      rw [← h_eq']
      exact ⟨by linarith, by linarith⟩
    have h_subst : (∫ t in (4 : ℝ)..5, (fun _ : ℝ => (-1 : ℝ)) t •
          ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => 5 - t)) t) =
        ∫ x in ((5 : ℝ) - 4)..((5 : ℝ) - 5),
          deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
          (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_horiz Y 0 1 hY_pos hg_top).mono h_img)
    calc (∫ t in (4 : ℝ)..5, u t)
        = ∫ t in (4 : ℝ)..5,
            (modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w)⁻¹ *
              (((-1 : ℝ) : ℂ) *
                deriv modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)) := hI4
      _ = ∫ t in (4 : ℝ)..5, (fun _ : ℝ => (-1 : ℝ)) t •
            ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
              (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) ∘
              (fun t : ℝ => 5 - t)) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w)⁻¹ *
              (((-1 : ℝ) : ℂ) *
                deriv modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)) =
            (-1 : ℝ) •
              (deriv modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) /
                (modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = ∫ x in ((5 : ℝ) - 4)..((5 : ℝ) - 5),
            deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) := h_subst
      _ = ∫ x in (1 : ℝ)..(0 : ℝ),
            deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) := by
          rw [show (5 : ℝ) - 4 = 1 from by norm_num,
            show (5 : ℝ) - 5 = 0 from by norm_num]
      _ = -∫ x in (0 : ℝ)..1,
            deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) :=
          intervalIntegral.integral_symm 0 1
  -- Piece 5: left edge.
  have h5_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)
      (((-(Y - δ) : ℝ) : ℂ) * Complex.I) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => Y - (s - 5) * (Y - δ)) (-(Y - δ)) t := by
      have h := (((hasDerivAt_id t).sub_const (5 : ℝ)).mul_const (Y - δ)).const_sub Y
      simpa using h
    exact (h_inner.ofReal_comp).mul_const Complex.I
  have h5_im : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      0 < (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I).im := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    have h_le_one : t - 5 ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h_le_one (by linarith : (0:ℝ) ≤ Y - δ)]
  have h5_eq : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      F_Y_boundary_parameterization δ Y R₀ t =
      ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    have h_not3 : ¬ t ≤ 3 := by linarith
    have h_not4 : ¬ t ≤ 4 := by linarith
    rcases eq_or_lt_of_le ht5 with h_eq | h_lt
    · -- t = 5: junction with the top edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (5 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (5 : ℝ) ≤ 2),
        if_neg (by norm_num : ¬ (5 : ℝ) ≤ 3), if_neg (by norm_num : ¬ (5 : ℝ) ≤ 4),
        if_pos (le_refl (5 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg h_not3, if_neg h_not4,
        if_neg (not_le.mpr h_lt), if_pos ht6]
  have h5_ne : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      modularLambdaH (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    have h := hg_left (Y - (t - 5) * (Y - δ)) ⟨by nlinarith, by nlinarith⟩
    rwa [zero_add] at h
  obtain ⟨hI5, hII5⟩ := h_piece 5 6
    (fun t : ℝ => ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)
    (fun _ : ℝ => ((-(Y - δ) : ℝ) : ℂ) * Complex.I)
    (by norm_num) h5_d continuous_const h5_im h5_eq h5_ne
  have h5_conv : (∫ t in (5 : ℝ)..6, u t) =
      Complex.I * -(∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
    have h_f_d : ∀ x ∈ Set.uIcc (5 : ℝ) 6,
        HasDerivAt (fun t : ℝ => Y - (t - 5) * (Y - δ))
          ((fun _ : ℝ => -(Y - δ)) x) x := by
      intro x _
      simpa using (((hasDerivAt_id x).sub_const (5 : ℝ)).mul_const (Y - δ)).const_sub Y
    have h_img : (fun t : ℝ => Y - (t - 5) * (Y - δ)) '' Set.uIcc (5 : ℝ) 6 ⊆
        Set.Icc δ Y := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 6)] at ht
      obtain ⟨ht5, ht6⟩ := ht
      have h_eq' : Y - (t - 5) * (Y - δ) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (5 : ℝ)..6, (fun _ : ℝ => -(Y - δ)) t •
          ((fun y : ℝ => deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => Y - (t - 5) * (Y - δ))) t) =
        ∫ y in (Y - ((5 : ℝ) - 5) * (Y - δ))..(Y - ((6 : ℝ) - 5) * (Y - δ)),
          deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
          (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_vert 0 Complex.zero_im hg_left).mono h_img)
    calc (∫ t in (5 : ℝ)..6, u t)
        = ∫ t in (5 : ℝ)..6,
            (modularLambdaH (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)⁻¹ *
              ((((-(Y - δ) : ℝ) : ℂ) * Complex.I) *
                deriv modularLambdaH
                  (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)) := hI5
      _ = ∫ t in (5 : ℝ)..6, Complex.I *
            ((fun _ : ℝ => -(Y - δ)) t •
              ((fun y : ℝ => deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => Y - (t - 5) * (Y - δ))) t) := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)⁻¹ *
              ((((-(Y - δ) : ℝ) : ℂ) * Complex.I) *
                deriv modularLambdaH
                  (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)) =
            Complex.I * ((-(Y - δ) : ℝ) •
              (deriv modularLambdaH ((0 : ℂ) +
                ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) /
              (modularLambdaH ((0 : ℂ) +
                ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)))
          rw [zero_add (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I),
            Complex.real_smul]
          push_cast
          ring
      _ = Complex.I * ∫ t in (5 : ℝ)..6,
            (fun _ : ℝ => -(Y - δ)) t •
              ((fun y : ℝ => deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => Y - (t - 5) * (Y - δ))) t :=
          intervalIntegral.integral_const_mul Complex.I _
      _ = Complex.I * ∫ y in (Y - ((5 : ℝ) - 5) * (Y - δ))..(Y - ((6 : ℝ) - 5) * (Y - δ)),
            deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w) := by
          rw [h_subst]
      _ = Complex.I * ∫ y in Y..(δ : ℝ),
            deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w) := by
          rw [show Y - ((5 : ℝ) - 5) * (Y - δ) = Y from by ring,
            show Y - ((6 : ℝ) - 5) * (Y - δ) = δ from by ring]
      _ = Complex.I * -(∫ y in (δ : ℝ)..Y,
            deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
          rw [intervalIntegral.integral_symm δ Y]
  -- Telescope the six pieces.
  have e01 := intervalIntegral.integral_add_adjacent_intervals hII0 hII1
  have hII02 := hII0.trans hII1
  have e02 := intervalIntegral.integral_add_adjacent_intervals hII02 hII2
  have hII03 := hII02.trans hII2
  have e03 := intervalIntegral.integral_add_adjacent_intervals hII03 hII3
  have hII04 := hII03.trans hII3
  have e04 := intervalIntegral.integral_add_adjacent_intervals hII04 hII4
  have hII05 := hII04.trans hII4
  have e05 := intervalIntegral.integral_add_adjacent_intervals hII05 hII5
  unfold Complex.pathContourIntegral
  change _ = ∫ t in (0 : ℝ)..6, u t
  rw [← e05, ← e04, ← e03, ← e02, ← e01,
    h0_conv, h1_conv, h2_conv, h3_conv, h4_conv, h5_conv]
  ring


/-- **Continuous-homotopy invariance of the boundary contour integral.**
Given a continuous closed homotopy `H : [0, 1] × [0, 6] → ℂ \ {w}`
(in the sense of `image_curve_lambda_F_Y_homotopic_to_circle`) between
the image curve `λ ∘ F_Y_boundary_parameterization δ Y R₀` at `s = 0`
and the parameterized CCW circle `circleMap w ε (· · π/3)` at `s = 1`,
the pathContourIntegrals of `(z − w)⁻¹` along the two endpoints are
equal.

This is the load-bearing topological sub-claim. The proof factors
through three pieces:

1. `continuous_log_lift_param_of_continuous_ne_zero` (PathWinding.lean):
   a jointly continuous log lift `L` of `H − w` over the homotopy
   rectangle `[0, 1] × [0, 6]`.

2. The integer-continuity argument: the cross-section boundary
   difference `τ s := L s 6 − L s 0` is continuous in `s` and satisfies
   `exp (τ s) = 1` by closedness of `H s`, hence takes values in
   `2πi · ℤ`; by the intermediate value theorem applied to
   `s ↦ (τ s).im / (2π)`, the endpoint values agree: `τ 0 = τ 1`.

3. The FTC bridges (PathWinding.lean): at `s = 0`, the piecewise-C¹
   bridge `pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve`
   identifies the image-curve contour integral with `τ 0`; at `s = 1`,
   the C¹ bridge `pathContourIntegral_inv_eq_log_lift_diff_of_contDiff`
   identifies the circle contour integral with `τ 1`. -/
theorem modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_circle_via_homotopy
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (ε : ℝ) (_hε_pos : 0 < ε) (H : ℝ → ℝ → ℂ)
    (hH_cont : ContinuousOn (Function.uncurry H)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6))
    (hH_0 : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      H 0 t = modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
    (hH_1 : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      H 1 t = _root_.circleMap w ε (t * Real.pi / 3))
    (hH_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6, H s t ≠ w)
    (hH_closed : ∀ s ∈ Set.Icc (0 : ℝ) 1, H s 0 = H s 6) :
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w)⁻¹) =
    Complex.pathContourIntegral
      (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3))
      0 6 (fun z => (z - w)⁻¹) := by
  -- The shifted homotopy u := H − w is jointly continuous and nonvanishing
  -- on the rectangle, so it admits a jointly continuous log lift.
  have h_u_cont : ContinuousOn (Function.uncurry (fun s t => H s t - w))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6) := by
    have h_eq : Function.uncurry (fun s t => H s t - w) =
        fun p : ℝ × ℝ => Function.uncurry H p - w := rfl
    rw [h_eq]
    exact hH_cont.sub continuousOn_const
  obtain ⟨L, hL_cont, hL_exp₀⟩ :=
    continuous_log_lift_param_of_continuous_ne_zero
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)
      (fun s t => H s t - w) h_u_cont
      (fun s hs t ht => sub_ne_zero.mpr (hH_avoid s hs t ht))
  have hL_exp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L s t) = H s t - w := hL_exp₀
  -- Membership facts used throughout.
  have h0_mem6 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h6_mem6 : (6 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h0_mem1 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1_mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  -- The cross-section boundary difference τ s := L s 6 − L s 0 is continuous
  -- and lies in 2πi·ℤ for every s ∈ [0, 1] (closedness of H s).
  have h_τ_cont : Continuous (fun s => L s 6 - L s 0) := by
    have h6 : Continuous (fun s => L s 6) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    have h0 : Continuous (fun s => L s 0) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    exact h6.sub h0
  have h_τ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, L s 6 - L s 0 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    have h_exp_eq : Complex.exp (L s 6 - L s 0) = 1 := by
      rw [Complex.exp_sub, hL_exp s hs 6 h6_mem6, hL_exp s hs 0 h0_mem6,
        ← hH_closed s hs]
      exact div_self (sub_ne_zero.mpr (hH_avoid s hs 0 h0_mem6))
    exact Complex.exp_eq_one_iff.mp h_exp_eq
  -- Integer continuity: τ 0 = τ 1.
  have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hψ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, (L s 6 - L s 0).im / (2 * Real.pi) = (n : ℝ) := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    refine ⟨n, ?_⟩
    have h_im : (L s 6 - L s 0).im = (n : ℝ) * (2 * Real.pi) := by
      rw [hn]
      simp [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    rw [h_im]
    field_simp
  have hψ_re : ∀ s ∈ Set.Icc (0 : ℝ) 1, (L s 6 - L s 0).re = 0 := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    rw [hn]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have h_τ_eq : L 0 6 - L 0 0 = L 1 6 - L 1 0 := by
    have hψ_cont : Continuous (fun s => (L s 6 - L s 0).im / (2 * Real.pi)) :=
      (Complex.continuous_im.comp h_τ_cont).div_const _
    obtain ⟨n₀, hn₀⟩ := hψ_int 0 h0_mem1
    obtain ⟨n₁, hn₁⟩ := hψ_int 1 h1_mem1
    have h_n_eq : n₀ = n₁ := by
      by_contra h_ne
      rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
      · -- n₀ < n₁: hit the half-integer n₀ + 1/2 by IVT.
        have h_le : (n₀ : ℝ) + 1 ≤ n₁ := by exact_mod_cast h_lt
        have h_mem : ((n₀ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi))
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₀ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₀ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₀ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₀ + 1 := by exact_mod_cast h_cast
        omega
      · -- n₁ < n₀: symmetric, with the decreasing-form IVT.
        have h_le : (n₁ : ℝ) + 1 ≤ n₀ := by exact_mod_cast h_gt
        have h_mem : ((n₁ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi))
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₁ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₁ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₁ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₁ + 1 := by exact_mod_cast h_cast
        omega
    -- Equal imaginary parts and zero real parts force τ 0 = τ 1.
    have h_im0 : (L (0 : ℝ) 6 - L 0 0).im = (n₀ : ℝ) * (2 * Real.pi) := by
      have h := hn₀
      field_simp at h
      linarith
    have h_im1 : (L (1 : ℝ) 6 - L 1 0).im = (n₁ : ℝ) * (2 * Real.pi) := by
      have h := hn₁
      field_simp at h
      linarith
    refine Complex.ext ?_ ?_
    · rw [hψ_re 0 h0_mem1, hψ_re 1 h1_mem1]
    · rw [h_im0, h_im1, h_n_eq]
  -- Left FTC bridge: the image-curve integral equals τ 0.
  have h_γ_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w ≠ 0 := by
    intro t ht
    rw [← hH_0 t ht]
    exact sub_ne_zero.mpr (hH_avoid 0 h0_mem1 t ht)
  have h_L0_cont : Continuous (fun t => L 0 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L0_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 0 t) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w := by
    intro t ht
    rw [hL_exp 0 h0_mem1 t ht, hH_0 t ht]
  have h_left := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
    hδ hδY hR₀_pos hR₀_lt h_γ_ne (fun t => L 0 t) h_L0_cont h_L0_exp
  -- Right FTC bridge: the circle integral equals τ 1.
  have h_circle_C1 : ContDiff ℝ 1
      (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3)) :=
    (contDiff_circleMap w ε).comp (by fun_prop)
  have h_circle_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      _root_.circleMap w ε (t * Real.pi / 3) ≠ w := by
    intro t ht
    rw [← hH_1 t ht]
    exact hH_avoid 1 h1_mem1 t ht
  have h_L1_cont : Continuous (fun t => L 1 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L1_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 1 t) = _root_.circleMap w ε (t * Real.pi / 3) - w := by
    intro t ht
    rw [hL_exp 1 h1_mem1 t ht, hH_1 t ht]
  have h_right := pathContourIntegral_inv_eq_log_lift_diff_of_contDiff
    (by norm_num : (0 : ℝ) ≤ 6)
    (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3))
    h_circle_C1 h_circle_ne (fun t => L 1 t) h_L1_cont h_L1_exp
  -- Chain the three identities.
  rw [h_left, h_right]
  exact h_τ_eq


/-- **The truncated region avoids the unit semicircle.** Under the arc
bound `√(1/4 − δ²) < R₀`, every point `τ` with `δ < Im τ` lying outside
the closed ball `B(1/2 + δi, R₀)` satisfies `1 < ‖2τ − 1‖`.

Together with the strip bounds `0 < Re τ < 1` this places the interior
of the truncated region F_Y inside the open fundamental domain `F°`:
the algebra `‖τ − (1/2 + δi)‖² = ‖τ − 1/2‖² − 2δ·Im τ + δ²` combined
with `‖τ − (1/2 + δi)‖² > R₀² > 1/4 − δ²` and `Im τ > δ > 0` yields
`‖τ − 1/2‖² > 1/4 + 2δ(Im τ − δ) > 1/4`. Consequently the zeros of
`λ − w` counted by the F_Y argument principle are exactly the
`F°`-preimages of `w` lying in F_Y. -/
theorem F_Y_point_in_gamma2_semicircle_exterior
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    {τ : ℂ} (h_im : δ < τ.im)
    (h_arc : R₀ < ‖τ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖) :
    1 < ‖2 * τ - 1‖ := by
  have hR₀_pos : 0 < R₀ := lt_of_le_of_lt (Real.sqrt_nonneg _) hR₀_lo
  -- Square the arc bound: 1/4 − δ² < R₀².
  have h_sq_lo : 1 / 4 - δ ^ 2 < R₀ ^ 2 := (Real.sqrt_lt' hR₀_pos).mp hR₀_lo
  -- Square the distance bound: R₀² < ‖τ − (1/2 + δi)‖².
  have h_sq_arc : R₀ ^ 2 < ‖τ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ ^ 2 := by
    have h := mul_self_lt_mul_self hR₀_pos.le h_arc
    nlinarith [h]
  -- Coordinates.
  have h_norm_arc : ‖τ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ ^ 2 =
      (τ.re - 1 / 2) ^ 2 + (τ.im - δ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_norm_semi : ‖2 * τ - 1‖ ^ 2 = (2 * τ.re - 1) ^ 2 + (2 * τ.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  -- Conclude via the squares.
  have h_one_lt_sq : 1 < ‖2 * τ - 1‖ ^ 2 := by
    rw [h_norm_semi]
    rw [h_norm_arc] at h_sq_arc
    nlinarith [h_sq_lo, h_sq_arc, h_im, hδ]
  by_contra h_le
  push Not at h_le
  nlinarith [norm_nonneg (2 * τ - 1), h_le, h_one_lt_sq]

/-- **Contour-integral invariance along a `w`-segment avoided by the
image curve.** If the image curve `λ ∘ ∂F_Y` avoids every point of the
segment `[w₀, w₁]`, the contour integrals of `(z − w₀)⁻¹` and
`(z − w₁)⁻¹` along it coincide.

Proof: the moving difference `u(s, t) := λ(γ(t)) − ((1 − s)w₀ + s·w₁)`
admits a jointly continuous log lift `L` over `[0, 1] × [0, 6]`
(`continuous_log_lift_param_of_continuous_ne_zero`); the cross-section
boundary difference `τ(s) := L s 6 − L s 0` is continuous and lies in
`2πi·ℤ` (the curve closes up), so by the intermediate value theorem
`τ(0) = τ(1)`; the piecewise FTC bridge identifies the two contour
integrals with `τ(0)` and `τ(1)`. -/
theorem modularLambdaH_F_Y_pathContourIntegral_eq_of_segment_avoids
    {δ Y R₀ : ℝ} (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    {w₀ w₁ : ℂ}
    (h_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) ≠
        (1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁) :
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w₀)⁻¹) =
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w₁)⁻¹) := by
  -- The moving difference u(s, t) := λ(γ t) − w(s) along the segment
  -- w(s) := (1 − s)·w₀ + s·w₁ is jointly continuous and nonvanishing.
  have h_image_cont : ContinuousOn
      (fun t : ℝ => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      (Set.Icc (0 : ℝ) 6) := by
    have h := F_Y_image_curve_continuousOn w₀ hδ hδY hR₀_pos hR₀_lt
    have h_eq : (fun t : ℝ =>
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t)) =
        fun t => (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₀) + w₀ := by
      funext t; ring
    rw [h_eq]
    exact h.add continuousOn_const
  have h_u_cont : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (t : ℝ) =>
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) -
          ((1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6) := by
    have h1 : ContinuousOn
        (fun p : ℝ × ℝ =>
          modularLambdaH (F_Y_boundary_parameterization δ Y R₀ p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6) := by
      refine ContinuousOn.comp h_image_cont continuousOn_snd ?_
      intro p hp
      exact hp.2
    have h2 : Continuous (fun p : ℝ × ℝ =>
        (1 - ((p.1 : ℝ) : ℂ)) * w₀ + ((p.1 : ℝ) : ℂ) * w₁) := by
      fun_prop
    exact h1.sub h2.continuousOn
  obtain ⟨L, hL_cont, hL_exp₀⟩ :=
    continuous_log_lift_param_of_continuous_ne_zero
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)
      (fun (s : ℝ) (t : ℝ) =>
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) -
        ((1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁)) h_u_cont
      (fun s hs t ht => sub_ne_zero.mpr (h_avoid s hs t ht))
  have hL_exp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L s t) =
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) -
          ((1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁) := hL_exp₀
  have h0_mem6 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h6_mem6 : (6 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h0_mem1 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1_mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  -- The F_Y boundary curve closes up.
  have hγ_closed : F_Y_boundary_parameterization δ Y R₀ 0 =
      F_Y_boundary_parameterization δ Y R₀ 6 := by
    unfold F_Y_boundary_parameterization
    have h0_le_1 : (0 : ℝ) ≤ 1 := by norm_num
    have h6_not_le_1 : ¬((6 : ℝ) ≤ 1) := by norm_num
    have h6_not_le_2 : ¬((6 : ℝ) ≤ 2) := by norm_num
    have h6_not_le_3 : ¬((6 : ℝ) ≤ 3) := by norm_num
    have h6_not_le_4 : ¬((6 : ℝ) ≤ 4) := by norm_num
    have h6_not_le_5 : ¬((6 : ℝ) ≤ 5) := by norm_num
    have h6_le_6 : (6 : ℝ) ≤ 6 := by norm_num
    rw [if_pos h0_le_1, if_neg h6_not_le_1, if_neg h6_not_le_2,
        if_neg h6_not_le_3, if_neg h6_not_le_4, if_neg h6_not_le_5, if_pos h6_le_6]
    push_cast; ring
  -- Cross-section boundary difference: continuous, valued in 2πi·ℤ.
  have h_τ_cont : Continuous (fun s => L s 6 - L s 0) := by
    have h6 : Continuous (fun s => L s 6) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    have h0 : Continuous (fun s => L s 0) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    exact h6.sub h0
  have h_τ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, L s 6 - L s 0 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    have h_exp_eq : Complex.exp (L s 6 - L s 0) = 1 := by
      rw [Complex.exp_sub, hL_exp s hs 6 h6_mem6, hL_exp s hs 0 h0_mem6,
        hγ_closed]
      exact div_self (sub_ne_zero.mpr (by rw [← hγ_closed]; exact h_avoid s hs 0 h0_mem6))
    exact Complex.exp_eq_one_iff.mp h_exp_eq
  have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hψ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, (L s 6 - L s 0).im / (2 * Real.pi) = (n : ℝ) := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    refine ⟨n, ?_⟩
    have h_im : (L s 6 - L s 0).im = (n : ℝ) * (2 * Real.pi) := by
      rw [hn]
      simp [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    rw [h_im]
    field_simp
  have hψ_re : ∀ s ∈ Set.Icc (0 : ℝ) 1, (L s 6 - L s 0).re = 0 := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    rw [hn]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have h_τ_eq : L 0 6 - L 0 0 = L 1 6 - L 1 0 := by
    have hψ_cont : Continuous (fun s => (L s 6 - L s 0).im / (2 * Real.pi)) :=
      (Complex.continuous_im.comp h_τ_cont).div_const _
    obtain ⟨n₀, hn₀⟩ := hψ_int 0 h0_mem1
    obtain ⟨n₁, hn₁⟩ := hψ_int 1 h1_mem1
    have h_n_eq : n₀ = n₁ := by
      by_contra h_ne
      rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
      · have h_le : (n₀ : ℝ) + 1 ≤ n₁ := by exact_mod_cast h_lt
        have h_mem : ((n₀ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi))
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₀ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₀ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₀ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₀ + 1 := by exact_mod_cast h_cast
        omega
      · have h_le : (n₁ : ℝ) + 1 ≤ n₀ := by exact_mod_cast h_gt
        have h_mem : ((n₁ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi))
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₁ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₁ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₁ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₁ + 1 := by exact_mod_cast h_cast
        omega
    have h_im0 : (L (0 : ℝ) 6 - L 0 0).im = (n₀ : ℝ) * (2 * Real.pi) := by
      have h := hn₀
      field_simp at h
      linarith
    have h_im1 : (L (1 : ℝ) 6 - L 1 0).im = (n₁ : ℝ) * (2 * Real.pi) := by
      have h := hn₁
      field_simp at h
      linarith
    refine Complex.ext ?_ ?_
    · rw [hψ_re 0 h0_mem1, hψ_re 1 h1_mem1]
    · rw [h_im0, h_im1, h_n_eq]
  -- FTC at the two endpoints of the segment.
  have h_γ_ne₀ : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₀ ≠ 0 := by
    intro t ht
    have h := h_avoid 0 h0_mem1 t ht
    rw [show (1 - ((0 : ℝ) : ℂ)) * w₀ + ((0 : ℝ) : ℂ) * w₁ = w₀ by push_cast; ring] at h
    exact sub_ne_zero.mpr h
  have h_γ_ne₁ : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₁ ≠ 0 := by
    intro t ht
    have h := h_avoid 1 h1_mem1 t ht
    rw [show (1 - ((1 : ℝ) : ℂ)) * w₀ + ((1 : ℝ) : ℂ) * w₁ = w₁ by push_cast; ring] at h
    exact sub_ne_zero.mpr h
  have h_L0_cont : Continuous (fun t => L 0 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L1_cont : Continuous (fun t => L 1 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L0_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 0 t) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₀ := by
    intro t ht
    rw [hL_exp 0 h0_mem1 t ht]
    rw [show (1 - ((0 : ℝ) : ℂ)) * w₀ + ((0 : ℝ) : ℂ) * w₁ = w₀ by push_cast; ring]
  have h_L1_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 1 t) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₁ := by
    intro t ht
    rw [hL_exp 1 h1_mem1 t ht]
    rw [show (1 - ((1 : ℝ) : ℂ)) * w₀ + ((1 : ℝ) : ℂ) * w₁ = w₁ by push_cast; ring]
  have h_left := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
    hδ hδY hR₀_pos hR₀_lt h_γ_ne₀ (fun t => L 0 t) h_L0_cont h_L0_exp
  have h_right := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
    hδ hδY hR₀_pos hR₀_lt h_γ_ne₁ (fun t => L 1 t) h_L1_cont h_L1_exp
  rw [h_left, h_right]
  exact h_τ_eq


/-- **Uniform smallness of `λ` on high horizontal edges.** For any
`ν > 0` there is a height `Y₀ ≥ 1` beyond which `‖λ‖ < ν` on the whole
horizontal segment `[0, 1] × {Y}`. Quantitative form of the cusp-`∞`
decay, from `modularLambdaH_norm_le_exp_of_im_ge_one`. -/
theorem modularLambdaH_top_edge_norm_lt_uniform {ν : ℝ} (hν : 0 < ν) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ‖modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I)‖ < ν := by
  -- Choose Y₀ with 160000·exp(−π·Y₀) < ν.
  set Y₀ : ℝ := max 1 (Real.log (320000 / ν) / Real.pi) with hY₀_def
  refine ⟨Y₀, le_max_left _ _, ?_⟩
  intro Y hY x hx_nn hx_le
  have hY_ge_one : 1 ≤ Y := le_trans (le_max_left _ _) hY
  set τ : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I with hτ_def
  have hτ_im : τ.im = Y := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_decay := modularLambdaH_norm_le_exp_of_im_ge_one (τ := τ) (by rw [hτ_im]; exact hY_ge_one)
  rw [hτ_im] at h_decay
  refine lt_of_le_of_lt h_decay ?_
  -- 160000·exp(−π·Y) < ν since Y ≥ log(320000/ν)/π.
  have h_log_le : Real.log (320000 / ν) / Real.pi ≤ Y :=
    le_trans (le_max_right _ _) hY
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_log_le' : Real.log (320000 / ν) ≤ Real.pi * Y := by
    rw [div_le_iff₀ h_pi_pos] at h_log_le
    linarith
  have h_ratio_pos : (0 : ℝ) < 320000 / ν := by positivity
  have h_exp_bound : 320000 / ν ≤ Real.exp (Real.pi * Y) := by
    calc 320000 / ν = Real.exp (Real.log (320000 / ν)) := (Real.exp_log h_ratio_pos).symm
      _ ≤ Real.exp (Real.pi * Y) := Real.exp_le_exp.mpr h_log_le'
  have h_exp_pos : (0 : ℝ) < Real.exp (Real.pi * Y) := Real.exp_pos _
  have h_neg_exp : Real.exp (-Real.pi * Y) = (Real.exp (Real.pi * Y))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [h_neg_exp]
  rw [show (160000 : ℝ) * (Real.exp (Real.pi * Y))⁻¹ =
    160000 / Real.exp (Real.pi * Y) from by ring]
  rw [div_lt_iff₀ h_exp_pos]
  have h_from_bound : 320000 / ν * ν ≤ Real.exp (Real.pi * Y) * ν := by
    exact mul_le_mul_of_nonneg_right h_exp_bound hν.le
  rw [div_mul_cancel₀ (320000 : ℝ) (ne_of_gt hν)] at h_from_bound
  linarith


/-- **Segment-uniform bottom-left strip bound.** Quantitative variant
of `modularLambdaH_F_Y_bot_left_strip_ne`: a single strip width works
simultaneously for every `w'` at distance at least `ρ` from `1`
(near the cusp `0` the boundary values approach `1`). -/
theorem modularLambdaH_F_Y_bot_left_strip_ne_uniform {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ_u : ℝ, 0 < δ_u ∧ δ_u < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_u → ∀ x : ℝ, 0 ≤ x → x ≤ δ →
      ∀ w' : ℂ, ρ ≤ ‖w' - 1‖ →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
  set L : ℝ := Real.log (160000 / ρ) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_nn hx_le w' hw'_ρ h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w' := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  have h_x_sq_le_δ_sq : x^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < x^2 + δ^2 := by nlinarith
  have h_normSq : Complex.normSq τ = x^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ_re, hτ_im]; ring
  -- Im(-1/τ) = δ/(x² + δ²).
  have h_im_inv : (-(τ : ℂ)⁻¹).im = δ / (x^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ_im, h_normSq]; ring
  -- 1/(2δ) ≤ Im(-1/τ): equivalent to x² + δ² ≤ 2δ² (i.e., x² ≤ δ²).
  have h_im_inv_ge : 1/(2*δ) ≤ (-(τ : ℂ)⁻¹).im := by
    rw [h_im_inv, div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  -- 1/(2δ) ≥ 2 (since δ ≤ 1/4).
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_ge_one : 1 ≤ (-(τ : ℂ)⁻¹).im := by linarith
  -- Apply norm bound to -1/τ.
  have h_norm_lam_inv : ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_ge_one
  -- Apply S-action identity: λ(τ) + λ(-1/τ) = 1.
  have h_S : modularLambdaH τ + modularLambdaH (-1/τ) = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ_im_pos
  have h_neg_eq : -1/τ = -τ⁻¹ := by field_simp
  rw [h_neg_eq] at h_S
  -- ‖λ(τ) - 1‖ = ‖λ(-τ⁻¹)‖.
  have h_diff_eq : modularLambdaH τ - 1 = -modularLambdaH (-(τ : ℂ)⁻¹) := by
    linear_combination h_S
  have h_norm_diff : ‖modularLambdaH τ - 1‖ = ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ := by
    rw [h_diff_eq, norm_neg]
  -- ‖λ(τ) - 1‖ ≤ 160000 · exp(-π · 1/(2δ)).
  have h_exp_mono : Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_ge]
  have h_bound : ‖modularLambdaH τ - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff]
    refine le_trans h_norm_lam_inv ?_
    exact mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
  -- M ≤ 1/(2δ): δ ≤ 1/(2M) means 2δM ≤ 1.
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  -- π * (1/(2δ)) > L since π > 1 and M ≥ L: π · M > M ≥ L, and π/(2δ) ≥ π·M.
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_M_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := by exact mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_M_ge_pi_M
  -- exp(-π·(1/(2δ))) < exp(-L) = ρ/160000.
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have h_quot_pos : (0 : ℝ) < 160000 / ρ := by positivity
  have h_exp_neg_L : Real.exp (-L) = ρ / 160000 := by
    rw [hL_def]
    rw [show -Real.log (160000 / ρ) = Real.log ((160000 / ρ)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 / ρ)⁻¹)]
    rw [inv_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < ρ := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := by
          exact mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (ρ / 160000) := by rw [h_exp_neg_L]
      _ = ρ := by field_simp
  have h_strict : ‖modularLambdaH τ - 1‖ < ρ := lt_of_le_of_lt h_bound h_final_bound
  have h_strict' : ‖modularLambdaH τ - 1‖ < ‖w' - 1‖ := lt_of_lt_of_le h_strict hw'_ρ
  rw [h_lam_eq] at h_strict'
  exact lt_irrefl _ h_strict'

/-- Segment-uniform variant of `modularLambdaH_F_Y_bot_right_strip_ne`:
the threshold `δ_u` depends only on an upper bound `‖w'‖ ≤ B`. -/
theorem modularLambdaH_F_Y_bot_right_strip_ne_uniform {B : ℝ} (hB : 0 < B) :
    ∃ δ_u : ℝ, 0 < δ_u ∧ δ_u < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_u → ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
      ∀ w' : ℂ, ‖w'‖ ≤ B →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
  -- Target: ‖λ(τ - 1) - 1‖ < 1/(B + 2). Then |λ(τ)| ≥ ‖w'‖ + 1 > ‖w'‖, so λ(τ) ≠ w'.
  set L : ℝ := Real.log (160000 * (B + 2)) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_ge hx_le w' hw'_B h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w' := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  -- Define τ' := (1 - x) + δi (in bot_left strip).
  set τ' : ℂ := ((1 - x : ℝ) : ℂ) + (δ : ℂ) * Complex.I with hτ'_def
  have hτ'_re : τ'.re = 1 - x := by
    simp [hτ'_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im : τ'.im = δ := by
    simp [hτ'_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im_pos : 0 < τ'.im := hτ'_im ▸ hδ_pos
  have hτ'_re_nn : 0 ≤ τ'.re := by rw [hτ'_re]; linarith
  have hτ'_re_le_δ : τ'.re ≤ δ := by rw [hτ'_re]; linarith
  -- σ := τ - 1.
  set σ : ℂ := τ - 1 with hσ_def
  have hσ_im : σ.im = δ := by simp [hσ_def, hτ_im]
  have hσ_im_pos : 0 < σ.im := hσ_im ▸ hδ_pos
  -- -conj σ = τ', so λ(τ') = conj(λ(σ)).
  have h_neg_conj_σ : -(starRingEnd ℂ σ) = τ' := by
    apply Complex.ext
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_re,
        Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_im,
        Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have h_conj_lam : modularLambdaH τ' = starRingEnd ℂ (modularLambdaH σ) := by
    rw [← h_neg_conj_σ]
    exact modularLambdaH_conj_symmetry hσ_im_pos
  -- Cusp-0 bound on τ' (in bot_left strip):
  -- For τ' = (1-x) + δi with (1-x) ∈ [0, δ] and δ ∈ (0, 1/4]:
  -- Compute Im(-1/τ'), apply norm bound, apply S-action identity.
  have h_x_sq_le_δ_sq : (1 - x)^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < (1 - x)^2 + δ^2 := by nlinarith
  have h_normSq_τ' : Complex.normSq τ' = (1 - x)^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ'_re, hτ'_im]; ring
  have h_im_inv_τ' : (-(τ' : ℂ)⁻¹).im = δ / ((1 - x)^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ'_im, h_normSq_τ']; ring
  have h_im_inv_τ'_ge : 1/(2*δ) ≤ (-(τ' : ℂ)⁻¹).im := by
    rw [h_im_inv_τ', div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_τ'_ge_one : 1 ≤ (-(τ' : ℂ)⁻¹).im := by linarith
  have h_norm_lam_inv_τ' : ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_τ'_ge_one
  have h_S_τ' : modularLambdaH τ' + modularLambdaH (-1/τ') = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ'_im_pos
  have h_neg_eq_τ' : -1/τ' = -τ'⁻¹ := by field_simp
  rw [h_neg_eq_τ'] at h_S_τ'
  have h_diff_τ' : modularLambdaH τ' - 1 = -modularLambdaH (-(τ' : ℂ)⁻¹) := by
    linear_combination h_S_τ'
  have h_norm_diff_τ' : ‖modularLambdaH τ' - 1‖ = ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ := by
    rw [h_diff_τ', norm_neg]
  have h_exp_mono_τ' : Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_τ'_ge]
  have h_bound_τ' : ‖modularLambdaH τ' - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff_τ']
    exact le_trans h_norm_lam_inv_τ' (mul_le_mul_of_nonneg_left h_exp_mono_τ' (by norm_num))
  -- M ≤ 1/(2δ), so π·M ≤ π/(2δ).
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_inv_2δ_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_inv_2δ_ge_pi_M
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  have h_B_plus_two_pos : (0 : ℝ) < B + 2 := by linarith
  have h_exp_neg_L : Real.exp (-L) = 1 / (160000 * (B + 2)) := by
    rw [hL_def]
    rw [show -Real.log (160000 * (B + 2)) = Real.log ((160000 * (B + 2))⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 * (B + 2))⁻¹)]
    rw [one_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < 1 / (B + 2) := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (1 / (160000 * (B + 2))) := by rw [h_exp_neg_L]
      _ = 1 / (B + 2) := by field_simp
  have h_strict_τ' : ‖modularLambdaH τ' - 1‖ < 1 / (B + 2) :=
    lt_of_le_of_lt h_bound_τ' h_final_bound
  -- Transfer to σ via conjugation.
  have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH τ' - 1‖ := by
    rw [h_conj_lam]
    rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
      rw [map_sub, map_one]]
    rw [norm_conj]
  have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (B + 2) := by
    rw [h_norm_diff_σ]; exact h_strict_τ'
  -- T-action: λ(τ) = λ(σ + 1) = λ(σ)/(λ(σ) - 1).
  have h_T : modularLambdaH (σ + 1) = modularLambdaH σ / (modularLambdaH σ - 1) :=
    modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
  have h_σ_plus_one : σ + 1 = τ := by simp [hσ_def]
  rw [h_σ_plus_one] at h_T
  -- λ(σ) - 1 ≠ 0 from λ(σ) ≠ 1.
  have h_lam_σ_sub_one_ne : modularLambdaH σ - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hσ_im_pos)
  -- |λ(σ)| ≥ 1 - ‖λ(σ) - 1‖.
  have h_lam_σ_norm_ge : 1 - ‖modularLambdaH σ - 1‖ ≤ ‖modularLambdaH σ‖ := by
    have h_rtri : ‖(1 : ℂ)‖ - ‖modularLambdaH σ‖ ≤ ‖(1 : ℂ) - modularLambdaH σ‖ :=
      norm_sub_norm_le (1 : ℂ) (modularLambdaH σ)
    have h_simp : (1 : ℂ) - modularLambdaH σ = -(modularLambdaH σ - 1) := by ring
    rw [norm_one, h_simp, norm_neg] at h_rtri
    linarith
  -- Now: |λ(τ)| = |λ(σ)| / |λ(σ) - 1|.
  have h_norm_lam_τ : ‖modularLambdaH τ‖ = ‖modularLambdaH σ‖ / ‖modularLambdaH σ - 1‖ := by
    rw [h_T, norm_div]
  -- We want |λ(τ)| > ‖w'‖.
  -- |λ(σ)| ≥ 1 - c, |λ(σ) - 1| < 1/(‖w'‖ + 2) where c = ‖λ(σ) - 1‖.
  -- |λ(σ)| / |λ(σ) - 1| ≥ (1 - c)/c > ‖w'‖ + 1 > ‖w'‖.
  set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
  have hc_lt_B : c < 1 / (B + 2) := h_strict_σ
  have h_w'_plus_two_pos : (0 : ℝ) < ‖w'‖ + 2 := by
    have : (0 : ℝ) ≤ ‖w'‖ := norm_nonneg _
    linarith
  have h_div_le : 1 / (B + 2) ≤ 1 / (‖w'‖ + 2) :=
    one_div_le_one_div_of_le h_w'_plus_two_pos (by linarith)
  have hc_lt : c < 1 / (‖w'‖ + 2) := lt_of_lt_of_le hc_lt_B h_div_le
  have hc_pos : 0 < c := by
    rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
  have h_one_minus_c_pos : 0 < 1 - c := by
    have : c < 1 := by
      have h_inv_pos : (0 : ℝ) < 1 / (‖w'‖ + 2) := by positivity
      have h_inv_lt_one : 1 / (‖w'‖ + 2) ≤ 1 := by
        rw [div_le_iff₀ h_w'_plus_two_pos]; linarith [norm_nonneg w']
      linarith
    linarith
  have h_lam_σ_norm_pos : 0 < ‖modularLambdaH σ‖ := by linarith [h_lam_σ_norm_ge]
  -- (1 - c)/c > ‖w'‖: equiv to (1 - c) > c·‖w'‖, i.e., 1 > c·(‖w'‖ + 1), i.e., c < 1/(‖w'‖ + 1).
  have h_w_plus_one_pos : (0 : ℝ) < ‖w'‖ + 1 := by linarith [norm_nonneg w']
  have hc_lt_inv : c < 1 / (‖w'‖ + 1) := by
    calc c < 1 / (‖w'‖ + 2) := hc_lt
      _ ≤ 1 / (‖w'‖ + 1) := by
        apply one_div_le_one_div_of_le h_w_plus_one_pos
        linarith
  have h_c_w_plus_one_lt_one : c * (‖w'‖ + 1) < 1 := by
    have := hc_lt_inv
    rw [lt_div_iff₀ h_w_plus_one_pos] at this
    linarith
  have h_norm_lam_τ_gt : ‖w'‖ < ‖modularLambdaH τ‖ := by
    rw [h_norm_lam_τ]
    rw [lt_div_iff₀ hc_pos]
    calc ‖w'‖ * c = c * ‖w'‖ := by ring
      _ < c * ‖w'‖ + (1 - c * (‖w'‖ + 1)) := by linarith [h_c_w_plus_one_lt_one]
      _ = 1 - c := by ring
      _ ≤ ‖modularLambdaH σ‖ := h_lam_σ_norm_ge
  -- λ(τ) = w' would give ‖λ(τ)‖ = ‖w'‖. Contradiction.
  rw [h_lam_eq] at h_norm_lam_τ_gt
  exact lt_irrefl _ h_norm_lam_τ_gt

set_option maxHeartbeats 400000 in
-- Cusp-1 case of three-case Sub-lemma 8 (uniform version): the
-- reflection/conjugation machinery plus T-action elaborate slowly.
/-- Cusp-1 branch of `modularLambdaH_F_Y_arc_ne_uniform`: for `θ` near `0`
(below the returned threshold `θ_c`), conjugation symmetry plus the
`T`-action give `‖λ(arc)‖ > B ≥ ‖w'‖`. Thresholds depend only on `B`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform_cusp_one_case {B : ℝ} (hB : 0 < B) :
    ∃ δ_c θ_c : ℝ, 0 < δ_c ∧ 0 < θ_c ∧ θ_c ≤ Real.pi / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_c → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ_c → θ ≤ Real.pi →
      ∀ w' : ℂ, ‖w'‖ ≤ B →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  -- K_1 for cusp 1: 160000·exp(-π·K_1) < 1/(B + 2).
  set L_1 : ℝ := Real.log (160000 * (B + 2)) with hL_1_def
  set K_1 : ℝ := max L_1 1 + 1 with hK_1_def
  have hK_1_pos : 0 < K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  have hK_1_ge_one : 1 ≤ K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  obtain ⟨δ_K_1, θ_K_1, hδ_K_1_pos, _hδ_K_1_le_quarter, hθ_K_1_pos, hθ_K_1_le_pi_4,
    h_cusp_1_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_1 hK_1_pos
  refine ⟨δ_K_1, θ_K_1, hδ_K_1_pos, hθ_K_1_pos, hθ_K_1_le_pi_4, ?_⟩
  intro δ R₀ hδ_pos hδ_le_δ_K_1 hR₀_lo hR₀_lt θ hθ_lo hθ_le hθ_hi w' hw'_B
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w' for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w' := by
    linear_combination h_lam_eq_w
  have harc_im_pos : 0 < arc.im :=
    modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le hθ_lo hθ_hi
  -- arc(π - θ) is in [π - θ_K_1, π] (cusp 0 of arc).
  have hπθ_le : Real.pi - θ ≤ Real.pi := by linarith [hθ_lo]
  have hπθ_ge_θ_K_1 : Real.pi - θ_K_1 ≤ Real.pi - θ := by
    linarith [hθ_le]
  -- Im(-1/arc(π - θ)) ≥ K_1.
  have h_im_inv_πθ_ge :
      K_1 ≤ (-(_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi - θ))⁻¹).im :=
    h_cusp_1_bound δ R₀ hδ_pos hδ_le_δ_K_1 hR₀_lo hR₀_lt (Real.pi - θ)
      hπθ_ge_θ_K_1 hπθ_le
  -- Define σ = arc - 1 and τ' = -conj σ = arc(π - θ).
  set σ : ℂ := arc - 1 with hσ_def
  set arcπθ : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀
    (Real.pi - θ) with harcπθ_def
  -- arc.Im > 0 already established.
  have hσ_im : σ.im = arc.im := by rw [hσ_def]; simp
  have hσ_im_pos : 0 < σ.im := by rw [hσ_im]; exact harc_im_pos
  -- arc(π - θ) = (1/2 - R₀ cos θ) + i(δ + R₀ sin θ) = 1 - conj(arc).
  -- Compute arc.re, arc.im, arcπθ.re, arcπθ.im, σ.re separately.
  have harc_re : arc.re = 1/2 + R₀ * Real.cos θ := by
    rw [harc_def, _root_.circleMap]
    simp [Complex.add_re, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have harc_im_eq : arc.im = δ + R₀ * Real.sin θ := by
    rw [harc_def, _root_.circleMap]
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have harcπθ_re : arcπθ.re = 1/2 - R₀ * Real.cos θ := by
    have h_eq : arcπθ.re = 1/2 + R₀ * Real.cos (Real.pi - θ) := by
      rw [harcπθ_def, _root_.circleMap]
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, mul_zero, zero_mul, sub_zero, mul_one,
        add_zero]
      have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
      rw [h_half_re]
    rw [h_eq, Real.cos_pi_sub]; ring
  have harcπθ_im : arcπθ.im = δ + R₀ * Real.sin θ := by
    have h_eq : arcπθ.im = δ + R₀ * Real.sin (Real.pi - θ) := by
      rw [harcπθ_def, _root_.circleMap]
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, mul_zero, zero_mul, mul_one]
      have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
      rw [h_half_im]; ring
    rw [h_eq, Real.sin_pi_sub]
  have hσ_re : σ.re = -1/2 + R₀ * Real.cos θ := by
    rw [hσ_def, Complex.sub_re, harc_re, Complex.one_re]; ring
  have hσ_im_eq : σ.im = δ + R₀ * Real.sin θ := by
    rw [hσ_def, Complex.sub_im, harc_im_eq, Complex.one_im]; ring
  -- Equivalently, -conj σ = arc(π - θ).
  have h_neg_conj_σ_eq : -(starRingEnd ℂ σ) = arcπθ := by
    apply Complex.ext
    · rw [Complex.neg_re, Complex.conj_re, hσ_re, harcπθ_re]; ring
    · rw [Complex.neg_im, Complex.conj_im, hσ_im_eq, harcπθ_im]; ring
  -- λ(arc(π - θ)) = conj(λ σ).
  have h_conj_lam : modularLambdaH arcπθ = starRingEnd ℂ (modularLambdaH σ) := by
    rw [← h_neg_conj_σ_eq]
    exact modularLambdaH_conj_symmetry hσ_im_pos
  -- Norm bound on arc(π - θ).
  have h_im_inv_πθ_ge_one : 1 ≤ (-(arcπθ)⁻¹).im := by
    rw [harcπθ_def] at h_im_inv_πθ_ge ⊢
    exact le_trans hK_1_ge_one h_im_inv_πθ_ge
  have h_norm_lam_inv_πθ : ‖modularLambdaH (-(arcπθ : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(arcπθ : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_im_inv_πθ_ge_one
  -- S-action on arc(π - θ): λ(arc(π-θ)) + λ(-1/arc(π-θ)) = 1.
  have h_arcπθ_im_pos : 0 < arcπθ.im := by
    rw [harcπθ_def]
    exact modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le
      (by linarith [hθ_hi]) hπθ_le
  have h_S_πθ : modularLambdaH arcπθ + modularLambdaH (-1/arcπθ) = 1 :=
    modularLambdaH_add_S_smul_eq_one h_arcπθ_im_pos
  have h_neg_eq_πθ : -1/arcπθ = -arcπθ⁻¹ := by field_simp
  rw [h_neg_eq_πθ] at h_S_πθ
  have h_diff_πθ : modularLambdaH arcπθ - 1 = -modularLambdaH (-(arcπθ : ℂ)⁻¹) := by
    linear_combination h_S_πθ
  have h_norm_diff_πθ : ‖modularLambdaH arcπθ - 1‖ = ‖modularLambdaH (-(arcπθ : ℂ)⁻¹)‖ := by
    rw [h_diff_πθ, norm_neg]
  -- ‖λ(arc(π-θ)) - 1‖ ≤ 160000 · exp(-π · K_1) < 1/(B + 2).
  have h_exp_mono_πθ : Real.exp (-Real.pi * (-(arcπθ : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * K_1) := by
    apply Real.exp_le_exp.mpr
    have := h_im_inv_πθ_ge
    rw [harcπθ_def] at this
    nlinarith [Real.pi_pos, this]
  have h_bound_πθ : ‖modularLambdaH arcπθ - 1‖ ≤ 160000 * Real.exp (-Real.pi * K_1) := by
    rw [h_norm_diff_πθ]
    exact le_trans h_norm_lam_inv_πθ (mul_le_mul_of_nonneg_left h_exp_mono_πθ (by norm_num))
  have h_B_plus_two_pos : (0 : ℝ) < B + 2 := by linarith
  have h_inv_pos : (0 : ℝ) < 1 / (B + 2) := by positivity
  -- 160000 · exp(-π K_1) < 1/(B+2) via exp_bound helper.
  have h_final_πθ : 160000 * Real.exp (-Real.pi * K_1) < 1 / (B + 2) := by
    have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_mul (B + 2) h_B_plus_two_pos
    have hK_1_eq : K_1 = max (Real.log (160000 * (B + 2))) 1 + 1 := by
      rw [hK_1_def, hL_1_def]
    rw [hK_1_eq]; exact h_helper
  have h_strict_πθ : ‖modularLambdaH arcπθ - 1‖ < 1 / (B + 2) :=
    lt_of_le_of_lt h_bound_πθ h_final_πθ
  -- Transfer to σ via conjugation.
  have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH arcπθ - 1‖ := by
    rw [h_conj_lam]
    rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
      rw [map_sub, map_one]]
    rw [norm_conj]
  have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (B + 2) := by
    rw [h_norm_diff_σ]; exact h_strict_πθ
  -- T-action: λ(σ + 1) = λ σ / (λ σ - 1).
  have h_T : modularLambdaH (σ + 1) = modularLambdaH σ / (modularLambdaH σ - 1) :=
    modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
  have h_σ_plus_one : σ + 1 = arc := by simp [hσ_def]
  rw [h_σ_plus_one] at h_T
  -- λ(σ) - 1 ≠ 0.
  have h_lam_σ_sub_one_ne : modularLambdaH σ - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hσ_im_pos)
  -- |λ(σ)| ≥ 1 - ‖λ(σ) - 1‖.
  have h_lam_σ_norm_ge : 1 - ‖modularLambdaH σ - 1‖ ≤ ‖modularLambdaH σ‖ := by
    have h_rtri : ‖(1 : ℂ)‖ - ‖modularLambdaH σ‖ ≤ ‖(1 : ℂ) - modularLambdaH σ‖ :=
      norm_sub_norm_le (1 : ℂ) (modularLambdaH σ)
    have h_simp : (1 : ℂ) - modularLambdaH σ = -(modularLambdaH σ - 1) := by ring
    rw [norm_one, h_simp, norm_neg] at h_rtri
    linarith
  -- |λ(arc)| = |λ σ| / |λ σ - 1|.
  have h_norm_lam_arc : ‖modularLambdaH arc‖ = ‖modularLambdaH σ‖ / ‖modularLambdaH σ - 1‖ := by
    rw [h_T, norm_div]
  -- Show |λ(arc)| > ‖w'‖.
  set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
  have hc_lt_B : c < 1 / (B + 2) := h_strict_σ
  have hc_pos : 0 < c := by
    rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
  have h_w'_plus_two_pos : (0 : ℝ) < ‖w'‖ + 2 := by
    have : (0 : ℝ) ≤ ‖w'‖ := norm_nonneg _
    linarith
  have h_div_le : 1 / (B + 2) ≤ 1 / (‖w'‖ + 2) :=
    one_div_le_one_div_of_le h_w'_plus_two_pos (by linarith)
  have hc_lt : c < 1 / (‖w'‖ + 2) := lt_of_lt_of_le hc_lt_B h_div_le
  have h_lam_σ_ge : 1 - c ≤ ‖modularLambdaH σ‖ := by
    rw [hc_def]; exact h_lam_σ_norm_ge
  have h_norm_lam_arc_gt : ‖w'‖ < ‖modularLambdaH arc‖ := by
    rw [h_norm_lam_arc]
    exact modularLambdaH_F_Y_arc_cusp_1_norm_bound (norm_nonneg w') hc_pos hc_lt h_lam_σ_ge
  rw [h_lam_arc_eq] at h_norm_lam_arc_gt
  exact lt_irrefl _ h_norm_lam_arc_gt

set_option maxHeartbeats 400000 in
-- Cusp-0 case of three-case Sub-lemma 8 (uniform version): the
-- S-action and exponential norm bounds elaborate slowly.
/-- Cusp-0 branch of `modularLambdaH_F_Y_arc_ne_uniform`: for `θ` near `π`
(above `π` minus the returned threshold `θ_c`), the `S`-action gives
`‖λ(arc) - 1‖ < ρ ≤ ‖w' - 1‖`. Thresholds depend only on `ρ`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform_cusp_zero_case {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ_c θ_c : ℝ, 0 < δ_c ∧ 0 < θ_c ∧ θ_c ≤ Real.pi / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_c → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → Real.pi - θ_c ≤ θ → θ ≤ Real.pi →
      ∀ w' : ℂ, ρ ≤ ‖w' - 1‖ →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  -- K_0 for cusp 0: 160000·exp(-π·K_0) < ρ.
  set L_0 : ℝ := Real.log (160000 / ρ) with hL_0_def
  set K_0 : ℝ := max L_0 1 + 1 with hK_0_def
  have hK_0_pos : 0 < K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  have hK_0_ge_one : 1 ≤ K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  obtain ⟨δ_K_0, θ_K_0, hδ_K_0_pos, _hδ_K_0_le_quarter, hθ_K_0_pos, hθ_K_0_le_pi_4,
    h_cusp_0_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_0 hK_0_pos
  refine ⟨δ_K_0, θ_K_0, hδ_K_0_pos, hθ_K_0_pos, hθ_K_0_le_pi_4, ?_⟩
  intro δ R₀ hδ_pos hδ_le_δ_K_0 hR₀_lo hR₀_lt θ hθ_lo hθ_in_cusp_0 hθ_hi w' hw'_ρ
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w' for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w' := by
    linear_combination h_lam_eq_w
  have harc_im_pos : 0 < arc.im :=
    modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le hθ_lo hθ_hi
  have h_im_inv_ge : K_0 ≤ (-(arc)⁻¹).im := by
    have := h_cusp_0_bound δ R₀ hδ_pos hδ_le_δ_K_0 hR₀_lo hR₀_lt θ hθ_in_cusp_0 hθ_hi
    rw [harc_def]; exact this
  have h_im_inv_ge_one : 1 ≤ (-(arc)⁻¹).im := le_trans hK_0_ge_one h_im_inv_ge
  -- Norm bound: ‖λ(-arc⁻¹)‖ ≤ 160000 · exp(-π · Im(-arc⁻¹)) ≤ 160000 · exp(-π K_0).
  have h_norm_lam_inv : ‖modularLambdaH (-(arc : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(arc : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_im_inv_ge_one
  -- S-action: λ(τ) + λ(-1/τ) = 1.
  have h_S : modularLambdaH arc + modularLambdaH (-1/arc) = 1 :=
    modularLambdaH_add_S_smul_eq_one harc_im_pos
  have h_neg_eq : -1/arc = -arc⁻¹ := by field_simp
  rw [h_neg_eq] at h_S
  have h_diff_eq : modularLambdaH arc - 1 = -modularLambdaH (-(arc : ℂ)⁻¹) := by
    linear_combination h_S
  have h_norm_diff : ‖modularLambdaH arc - 1‖ = ‖modularLambdaH (-(arc : ℂ)⁻¹)‖ := by
    rw [h_diff_eq, norm_neg]
  -- exp(-π · Im(-arc⁻¹)) ≤ exp(-π · K_0).
  have h_exp_mono : Real.exp (-Real.pi * (-(arc : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * K_0) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_ge]
  have h_bound : ‖modularLambdaH arc - 1‖ ≤ 160000 * Real.exp (-Real.pi * K_0) := by
    rw [h_norm_diff]
    refine le_trans h_norm_lam_inv ?_
    exact mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
  -- 160000 · exp(-π · K_0) < ρ via exp_bound helper.
  have h_final_bound : 160000 * Real.exp (-Real.pi * K_0) < ρ := by
    have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_div ρ hρ
    have hK_0_eq : K_0 = max (Real.log (160000 / ρ)) 1 + 1 := by
      rw [hK_0_def, hL_0_def]
    rw [hK_0_eq]; exact h_helper
  have h_strict : ‖modularLambdaH arc - 1‖ < ρ :=
    lt_of_le_of_lt h_bound h_final_bound
  have h_strict' : ‖modularLambdaH arc - 1‖ < ‖w' - 1‖ :=
    lt_of_lt_of_le h_strict hw'_ρ
  rw [h_lam_arc_eq] at h_strict'
  exact lt_irrefl _ h_strict'

set_option maxHeartbeats 400000 in
-- Middle case of three-case Sub-lemma 8 (uniform version): the
-- Lipschitz-ball extraction and semicircle computations elaborate slowly.
/-- Middle branch of `modularLambdaH_F_Y_arc_ne_uniform`: for
`θ ∈ [θ_0, π - θ_0]`, the Lipschitz bound for `Im λ` near the unit
semicircle forces `|Im λ(arc)| < μ ≤ w'.im`. The threshold
`δ_mid ≤ 1/4` depends only on `μ` and `θ_0`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform_middle_case {μ θ_0 : ℝ} (hμ : 0 < μ)
    (hθ_0_pos : 0 < θ_0) (hθ_0_lt_pi_2 : θ_0 < Real.pi / 2) :
    ∃ δ_mid : ℝ, 0 < δ_mid ∧ δ_mid ≤ 1 / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_mid → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, θ_0 ≤ θ → θ ≤ Real.pi - θ_0 →
      ∀ w' : ℂ, μ ≤ w'.im →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  have hθ_0_lt_pi : θ_0 < Real.pi := by linarith [Real.pi_pos]
  have h_sin_θ_0_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  -- Setup the ball for Lipschitz extraction (Helper 8.3's internal setup).
  set τ_K : ℂ := (1/2 : ℂ) +
    Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ) with hτ_K_def
  set r_K : ℝ := (1 + Real.cos θ_0) / (4 * Real.sin θ_0) with hr_K_def
  have h_cos_θ_0_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt_pi_2⟩
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  have hr_K_pos : 0 < r_K := by
    rw [hr_K_def]; exact div_pos (by linarith) h_4s_pos
  -- τ_K.im = 1/(2 sin θ_0) > 0.
  have hτ_K_im_eq : τ_K.im = 1/(2*Real.sin θ_0) := by
    rw [hτ_K_def]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  have hτ_K_im_pos : 0 < τ_K.im := by rw [hτ_K_im_eq]; positivity
  -- Apply Helper 8.3.a (ball in UHP) and Helper 8.2 to get M.
  have h_ball_in :=
    modularLambdaH_arc_lipschitz_ball_in_uhp hθ_0_pos hθ_0_lt_pi_2
  obtain ⟨M, hM_pos, hM_lipschitz⟩ :=
    modularLambdaH_im_lipschitz_on_compact hτ_K_im_pos hr_K_pos h_ball_in
  set δ_M : ℝ := μ / (4 * M) with hδ_M_def
  have hδ_M_pos : 0 < δ_M := by rw [hδ_M_def]; positivity
  refine ⟨min (Real.sin θ_0 / 4) (min δ_M (1/4)),
    lt_min (by positivity) (lt_min hδ_M_pos (by norm_num)),
    le_trans (min_le_right _ _) (min_le_right _ _), ?_⟩
  intro δ R₀ hδ_pos hδ_le hR₀_lo hR₀_lt θ hθ_in_middle_lo hθ_in_middle_hi w' hw'_im
  -- Extract individual constraints on δ.
  have hδ_le_sin_θ_0_quarter : δ ≤ Real.sin θ_0 / 4 :=
    le_trans hδ_le (min_le_left _ _)
  have hδ_le_δ_M : δ ≤ δ_M :=
    le_trans hδ_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_quarter : δ ≤ 1/4 :=
    le_trans hδ_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w' for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w' := by
    linear_combination h_lam_eq_w
  -- arc ∈ closedBall τ_K r_K (Helper 8.3.c).
  have h_arc_in_ball := modularLambdaH_arc_lipschitz_arc_in_ball
    hδ_pos hR₀_lo hR₀_lt hθ_0_pos hθ_0_lt_pi_2 hδ_le_sin_θ_0_quarter
    hθ_in_middle_lo hθ_in_middle_hi
  -- semi ∈ closedBall τ_K r_K (Helper 8.3.b).
  have h_semi_in_ball := modularLambdaH_arc_lipschitz_semi_in_ball
    hθ_0_pos hθ_0_lt_pi_2 hθ_in_middle_lo hθ_in_middle_hi
  -- Apply Lipschitz bound M.
  have h_lipschitz_bd := hM_lipschitz arc
    (_root_.circleMap (1/2 : ℂ) (1/2) θ)
    (by rw [harc_def]; exact h_arc_in_ball) h_semi_in_ball
  -- semicircle real-valued: Im λ(semi) = 0.
  have hθ_pos : 0 < θ := by linarith [hθ_0_pos]
  have hθ_lt_pi : θ < Real.pi := by linarith [hθ_0_pos]
  have hθ_sin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have h_semi_im_pos : 0 < (_root_.circleMap (1/2 : ℂ) (1/2) θ).im := by
    rw [_root_.circleMap]
    show 0 < ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)).im
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]
    have h_pos : 0 < (1 / 2 : ℝ) * Real.sin θ := by positivity
    linarith
  have h_semi_circle : ‖2 * (_root_.circleMap (1/2 : ℂ) (1/2) θ) - 1‖ = 1 := by
    rw [_root_.circleMap]
    have : 2 * ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) - 1 =
        Complex.exp (θ * Complex.I) := by push_cast; ring
    rw [this, Complex.norm_exp]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have h_semi_im_zero : (modularLambdaH (_root_.circleMap (1/2 : ℂ) (1/2) θ)).im = 0 :=
    modularLambdaH_semicircle_real h_semi_im_pos h_semi_circle
  rw [h_semi_im_zero, sub_zero] at h_lipschitz_bd
  -- Helper 8.1: distance bound.
  have h_arc_to_semi := modularLambdaH_arc_to_semicircle_dist hδ_pos hR₀_pos hR₀_lt θ
  -- |Im λ(arc)| ≤ M · ‖arc - semi‖ ≤ M · (δ + 1/2 - R₀).
  have h_im_bound : |(modularLambdaH arc).im| ≤ M * (δ + (1/2 - R₀)) := by
    calc |(modularLambdaH arc).im|
        ≤ M * ‖arc - _root_.circleMap (1/2 : ℂ) (1/2) θ‖ := by
          rw [harc_def] at h_lipschitz_bd ⊢; exact h_lipschitz_bd
      _ ≤ M * (δ + (1/2 - R₀)) := by
          apply mul_le_mul_of_nonneg_left _ hM_pos.le
          rw [harc_def]
          exact h_arc_to_semi
  -- 1/2 - R₀ ≤ 2δ² (from R₀ > √(1/4 - δ²)).
  have h_half_minus_R₀ : 1/2 - R₀ ≤ 2 * δ^2 :=
    modularLambdaH_F_Y_arc_half_minus_R₀_bound hδ_pos hδ_le_quarter
      hR₀_lo hR₀_lt hR₀_pos
  -- δ ≤ μ/(4M) (from hδ_le_δ_M and δ_M definition).
  have hδ_le_wim_4M : δ ≤ μ / (4*M) := by
    have h_δ_M_eq : δ_M = μ / (4*M) := hδ_M_def
    linarith [hδ_le_δ_M, h_δ_M_eq]
  -- Apply the pure polynomial helper.
  have h_M_bound : M * (δ + (1/2 - R₀)) < μ :=
    modularLambdaH_F_Y_arc_middle_poly_bound hM_pos hδ_pos hδ_le_quarter
      hδ_le_wim_4M h_half_minus_R₀ hμ
  -- λ(arc) = w' gives Im λ(arc) = w'.im. |Im λ(arc)| = w'.im (since w'.im ≥ μ > 0).
  -- But |Im λ(arc)| ≤ M · (δ + 1/2 - R₀) < μ ≤ w'.im. Contradiction.
  rw [h_lam_arc_eq] at h_im_bound
  have h_w'_im_pos : 0 < w'.im := lt_of_lt_of_le hμ hw'_im
  have h_abs_w_im : |w'.im| = w'.im := abs_of_pos h_w'_im_pos
  rw [h_abs_w_im] at h_im_bound
  linarith [h_M_bound, h_im_bound, hw'_im]

-- Three-case Sub-lemma 8 (middle Lipschitz + cusp-0 + cusp-1 conjugation),
-- segment-uniform version: thresholds depend only on (μ, B, ρ).
/-- Segment-uniform variant of `modularLambdaH_F_Y_arc_ne`: the threshold
`δ_u` depends only on `μ ≤ w'.im`, `‖w'‖ ≤ B`, and `ρ ≤ ‖w' - 1‖`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform {μ B ρ : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hρ : 0 < ρ) :
    ∃ δ_u : ℝ, 0 < δ_u ∧ δ_u < 1 / 2 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_u → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      ∀ w' : ℂ, μ ≤ w'.im → ‖w'‖ ≤ B → ρ ≤ ‖w' - 1‖ →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  -- Three-case proof, assembled from the three case helpers above:
  -- (a) Middle θ ∈ [θ_0, π - θ_0]: Helper 8.3-style bound on |Im λ|.
  -- (b) Cusp 0 θ ∈ (π - θ_K_0, π]: S-action + norm bound; ‖λ - 1‖ < ρ ≤ ‖w' - 1‖.
  -- (c) Cusp 1 θ ∈ [0, θ_K_1): conjugation + T; |λ| > B ≥ ‖w'‖.
  -- The three pieces of `δ_u` come from these three regimes.
  obtain ⟨δ_K_0, θ_K_0, hδ_K_0_pos, hθ_K_0_pos, hθ_K_0_le_pi_4, h_cusp_0⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform_cusp_zero_case hρ
  obtain ⟨δ_K_1, θ_K_1, hδ_K_1_pos, hθ_K_1_pos, _hθ_K_1_le_pi_4, h_cusp_1⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform_cusp_one_case hB
  -- θ_0 := min(θ_K_0, θ_K_1).
  set θ_0 : ℝ := min θ_K_0 θ_K_1
  have hθ_0_pos : 0 < θ_0 := lt_min hθ_K_0_pos hθ_K_1_pos
  have hθ_0_le_θ_K_0 : θ_0 ≤ θ_K_0 := min_le_left _ _
  have hθ_0_le_θ_K_1 : θ_0 ≤ θ_K_1 := min_le_right _ _
  have hθ_0_lt_pi_2 : θ_0 < Real.pi / 2 := by
    have h1 : θ_0 ≤ Real.pi / 4 := le_trans hθ_0_le_θ_K_0 hθ_K_0_le_pi_4
    linarith [Real.pi_pos]
  obtain ⟨δ_mid, hδ_mid_pos, hδ_mid_le_quarter, h_middle⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform_middle_case hμ hθ_0_pos hθ_0_lt_pi_2
  refine ⟨min (min δ_K_0 δ_K_1) δ_mid,
    lt_min (lt_min hδ_K_0_pos hδ_K_1_pos) hδ_mid_pos, ?_, ?_⟩
  · have h1 : min (min δ_K_0 δ_K_1) δ_mid ≤ δ_mid := min_le_right _ _
    linarith
  intro δ R₀ hδ_pos hδ_le hR₀_lo hR₀_lt θ hθ_lo hθ_hi w' hw'_im hw'_B hw'_ρ
  -- Extract individual constraints on δ.
  have hδ_le_δ_K_0 : δ ≤ δ_K_0 :=
    le_trans hδ_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_le_δ_K_1 : δ ≤ δ_K_1 :=
    le_trans hδ_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ_le_δ_mid : δ ≤ δ_mid := le_trans hδ_le (min_le_right _ _)
  -- Case split on θ position.
  by_cases h_θ_le_θ_0 : θ ≤ θ_0
  · -- Cusp 1 case: θ ∈ [0, θ_0] ⊆ [0, θ_K_1].
    exact h_cusp_1 δ R₀ hδ_pos hδ_le_δ_K_1 hR₀_lo hR₀_lt θ hθ_lo
      (le_trans h_θ_le_θ_0 hθ_0_le_θ_K_1) hθ_hi w' hw'_B
  · push Not at h_θ_le_θ_0
    -- θ > θ_0. Check if θ ≥ π - θ_0.
    by_cases h_θ_ge : Real.pi - θ_0 ≤ θ
    · -- Cusp 0 case: θ ∈ [π - θ_0, π] ⊆ [π - θ_K_0, π].
      exact h_cusp_0 δ R₀ hδ_pos hδ_le_δ_K_0 hR₀_lo hR₀_lt θ hθ_lo
        (by linarith [hθ_0_le_θ_K_0]) hθ_hi w' hw'_ρ
    · -- Middle case: θ ∈ (θ_0, π - θ_0).
      push Not at h_θ_ge
      exact h_middle δ R₀ hδ_pos hδ_le_δ_mid hR₀_lo hR₀_lt θ
        (le_of_lt h_θ_le_θ_0) (le_of_lt h_θ_ge) w' hw'_im


set_option maxHeartbeats 400000 in
-- Long single-declaration assembly of the degree argument (many large integral terms).
/-- **Uniqueness of the `F°`-preimage (degree-argument bootstrap).** Proved by
transporting the F_Y zero count along a `w`-segment to the deep-cusp reference
value, where the fibre is a provably unique simple point. -/
theorem modularLambdaH_F_interior_preimage_unique
    {w : ℂ} (hw : 0 < w.im) {τ₁ τ₂ : ℂ}
    (h₁_in : τ₁ ∈ Gamma2FundamentalDomainInterior)
    (h₂_in : τ₂ ∈ Gamma2FundamentalDomainInterior)
    (h₁_eq : modularLambdaH τ₁ = w) (h₂_eq : modularLambdaH τ₂ = w) :
    τ₁ = τ₂ := by
  by_contra h_τ_ne
  -- ================== A. deep-cusp reference value ==================
  obtain ⟨w_ref, τ_ref, hw_ref_im, _hτ_ref_in, _hτ_ref_eq, hτ_ref_deriv, hτ_ref_unique⟩ :=
    modularLambdaH_cusp_reference_value
  -- ================== B. segment bounds ==================
  obtain ⟨μ, hμ_pos, hμ_le_w_im, hμ_le_wref_im⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ w.im ∧ m ≤ w_ref.im :=
    ⟨min w.im w_ref.im, lt_min hw hw_ref_im, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨B, hB_pos, hB_ge_w, hB_ge_wref⟩ :
      ∃ b : ℝ, 0 < b ∧ ‖w‖ ≤ b ∧ ‖w_ref‖ ≤ b :=
    ⟨max ‖w‖ ‖w_ref‖,
      lt_of_lt_of_le (lt_of_lt_of_le hw (Complex.im_le_norm w)) (le_max_left _ _),
      le_max_left _ _, le_max_right _ _⟩
  -- `Im z ≥ μ` forces `‖z − 1‖ ≥ μ`.
  have h_im_to_sub_one : ∀ z : ℂ, μ ≤ z.im → μ ≤ ‖z - 1‖ := by
    intro z hz
    have h1 : (z - 1).im = z.im := by rw [Complex.sub_im, Complex.one_im, sub_zero]
    calc μ ≤ (z - 1).im := by rw [h1]; exact hz
      _ ≤ ‖z - 1‖ := Complex.im_le_norm _
  have hw_sub_one : μ ≤ ‖w - 1‖ := h_im_to_sub_one w hμ_le_w_im
  have hw_ref_sub_one : μ ≤ ‖w_ref - 1‖ := h_im_to_sub_one w_ref hμ_le_wref_im
  -- Segment-point bounds (i): imaginary part.
  have h_seg_im : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im := by
    intro s hs
    have h_im : ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im
        = (1 - s) * w.im + s * w_ref.im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h_im]
    have hP : 0 ≤ (1 - s) * (w.im - μ) :=
      mul_nonneg (by linarith [hs.2]) (by linarith [hμ_le_w_im])
    have hQ : 0 ≤ s * (w_ref.im - μ) :=
      mul_nonneg hs.1 (by linarith [hμ_le_wref_im])
    nlinarith [hP, hQ]
  -- Segment-point bounds (ii): norm.
  have h_seg_norm : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖ ≤ B := by
    intro s hs
    have h_tri := norm_add_le ((1 - (s : ℂ)) * w) ((s : ℂ) * w_ref)
    have h1 : ‖(1 - (s : ℂ)) * w‖ = (1 - s) * ‖w‖ := by
      rw [norm_mul]
      congr 1
      rw [show (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    have h2 : ‖(s : ℂ) * w_ref‖ = s * ‖w_ref‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    rw [h1, h2] at h_tri
    have hA := mul_le_mul_of_nonneg_left hB_ge_w (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
    have hC := mul_le_mul_of_nonneg_left hB_ge_wref hs.1
    calc ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖
        ≤ (1 - s) * ‖w‖ + s * ‖w_ref‖ := h_tri
      _ ≤ (1 - s) * B + s * B := add_le_add hA hC
      _ = B := by ring
  -- Segment-point bounds (iii): distance to `1`.
  have h_seg_sub_one : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref - 1‖ :=
    fun s hs => h_im_to_sub_one _ (h_seg_im s hs)
  -- ================== C. thresholds and region parameters ==================
  obtain ⟨δ_bl, hδ_bl_pos, _hδ_bl_lt, h_bl_prop⟩ :=
    modularLambdaH_F_Y_bot_left_strip_ne_uniform hμ_pos
  obtain ⟨δ_br, hδ_br_pos, _hδ_br_lt, h_br_prop⟩ :=
    modularLambdaH_F_Y_bot_right_strip_ne_uniform hB_pos
  obtain ⟨δ_arc, hδ_arc_pos, _hδ_arc_lt, h_arc_prop⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform hμ_pos hB_pos hμ_pos
  obtain ⟨Y₀, _hY₀_ge_one, hY₀_prop⟩ := modularLambdaH_top_edge_norm_lt_uniform hμ_pos
  obtain ⟨δ_max, hδ_max_pos, hδ_max_le_quarter, hδ_max_le_bl, hδ_max_le_br, hδ_max_le_arc⟩ :
      ∃ δ_m : ℝ, 0 < δ_m ∧ δ_m ≤ 1 / 4 ∧ δ_m ≤ δ_bl ∧ δ_m ≤ δ_br ∧ δ_m ≤ δ_arc :=
    ⟨min (min δ_bl δ_br) (min δ_arc (1 / 4)),
      lt_min (lt_min hδ_bl_pos hδ_br_pos) (lt_min hδ_arc_pos (by norm_num)),
      le_trans (min_le_right _ _) (min_le_right _ _),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _)⟩
  obtain ⟨δ, Y_base, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ₁_im, hδ_lt_τ₂_im,
    hδ_lt_Y_base, hτ₁_im_lt_Y_base, hτ₂_im_lt_Y_base,
    hR₀_pos, hR₀_lt, h_δR_lt_Y_base, hR₀_lo, hτ₁_norm_gt, hτ₂_norm_gt⟩ :=
    modularLambdaH_F_Y_params_exist_arc hw h₁_in h₂_in hδ_max_pos hδ_max_le_quarter
  obtain ⟨Y, hY_ge_base, hY_ge_Y₀⟩ : ∃ Y : ℝ, Y_base ≤ Y ∧ Y₀ ≤ Y :=
    ⟨max Y_base Y₀, le_max_left _ _, le_max_right _ _⟩
  have hδ_lt_Y : δ < Y := lt_of_lt_of_le hδ_lt_Y_base hY_ge_base
  have hτ₁_im_lt_Y : τ₁.im < Y := lt_of_lt_of_le hτ₁_im_lt_Y_base hY_ge_base
  have hτ₂_im_lt_Y : τ₂.im < Y := lt_of_lt_of_le hτ₂_im_lt_Y_base hY_ge_base
  have h_δR_lt_Y : δ + R₀ < Y := lt_of_lt_of_le h_δR_lt_Y_base hY_ge_base
  have hδ_le_δ_bl : δ ≤ δ_bl := le_trans hδ_le_δ_max hδ_max_le_bl
  have hδ_le_δ_br : δ ≤ δ_br := le_trans hδ_le_δ_max hδ_max_le_br
  have hδ_le_δ_arc : δ ≤ δ_arc := le_trans hδ_le_δ_max hδ_max_le_arc
  have hδ_le_quarter : δ ≤ 1 / 4 := le_trans hδ_le_δ_max hδ_max_le_quarter
  -- Coverage trick: the bottom edge intervals lie inside the cascade strips.
  have h_half_minus_R₀ : 1 / 2 - R₀ ≤ 2 * δ ^ 2 :=
    modularLambdaH_F_Y_arc_half_minus_R₀_bound hδ_pos hδ_le_quarter hR₀_lo hR₀_lt hR₀_pos
  have h_2δ_sq_le_δ : 2 * δ ^ 2 ≤ δ := by nlinarith [hδ_pos.le, hδ_le_quarter]
  have h_half_minus_R₀_le_δ : 1 / 2 - R₀ ≤ δ := le_trans h_half_minus_R₀ h_2δ_sq_le_δ
  -- ================== D. segment-uniform boundary facts ==================
  have hg_bot_left_u : ∀ w' : ℂ, μ ≤ ‖w' - 1‖ → ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    exact h_bl_prop δ hδ_pos hδ_le_δ_bl x hx.1 (le_trans hx.2 h_half_minus_R₀_le_δ) w' hw'
  have hg_bot_right_u : ∀ w' : ℂ, ‖w'‖ ≤ B → ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    refine h_br_prop δ hδ_pos hδ_le_δ_br x ?_ hx.2 w' hw'
    linarith [hx.1, h_half_minus_R₀_le_δ]
  have hg_top_u : ∀ w' : ℂ, μ ≤ w'.im → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw'_im x hx h_eq0
    have h_norm_lt : ‖modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I)‖ < μ :=
      hY₀_prop Y hY_ge_Y₀ x hx.1 hx.2
    have h_lam_eq : modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) = w' := by
      linear_combination h_eq0
    rw [h_lam_eq] at h_norm_lt
    linarith [Complex.im_le_norm w', hw'_im]
  have hg_right_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_right_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_left_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_left_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_arc_u : ∀ w' : ℂ, μ ≤ w'.im → ‖w'‖ ≤ B → μ ≤ ‖w' - 1‖ →
      ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
    intro w' h1 h2 h3 θ hθ
    exact h_arc_prop δ R₀ hδ_pos hδ_le_δ_arc hR₀_lo hR₀_lt θ hθ.1 hθ.2 w' h1 h2 h3
  -- The six boundary facts at `w`.
  have hg_bot_left_w := hg_bot_left_u w hw_sub_one
  have hg_bot_right_w := hg_bot_right_u w hB_ge_w
  have hg_top_w := hg_top_u w hμ_le_w_im
  have hg_right_w := hg_right_u w hw
  have hg_left_w := hg_left_u w hw
  have hg_arc_w := hg_arc_u w hμ_le_w_im hB_ge_w hw_sub_one
  -- The six boundary facts at `w_ref`.
  have hg_bot_left_wr := hg_bot_left_u w_ref hw_ref_sub_one
  have hg_bot_right_wr := hg_bot_right_u w_ref hB_ge_wref
  have hg_top_wr := hg_top_u w_ref hμ_le_wref_im
  have hg_right_wr := hg_right_u w_ref hw_ref_im
  have hg_left_wr := hg_left_u w_ref hw_ref_im
  have hg_arc_wr := hg_arc_u w_ref hμ_le_wref_im hB_ge_wref hw_ref_sub_one
  -- Transport hypothesis: the image curve avoids the whole segment.
  have h_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) ≠
        (1 - (s : ℂ)) * w + (s : ℂ) * w_ref := by
    intro s hs t ht
    have h_ne := F_Y_image_curve_ne_zero (w := (1 - (s : ℂ)) * w + (s : ℂ) * w_ref)
      hR₀_pos hR₀_lt hδ_lt_Y.le
      (hg_bot_left_u _ (h_seg_sub_one s hs))
      (hg_bot_right_u _ (h_seg_norm s hs))
      (hg_top_u _ (h_seg_im s hs))
      (hg_right_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_left_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_arc_u _ (h_seg_im s hs) (h_seg_norm s hs) (h_seg_sub_one s hs))
      t ht
    exact sub_ne_zero.mp h_ne
  -- ================== F. identity chain N(w) = N(w_ref) ==================
  have h_div_w := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_div_wr := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_LHS_w := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_LHS_wr := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_transport := modularLambdaH_F_Y_pathContourIntegral_eq_of_segment_avoids
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_avoid
  have h_count_cast :
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) =
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) := by
    rw [← h_div_w, ← h_div_wr, h_LHS_w, h_LHS_wr, h_transport]
  have h_count_eq :
      (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat =
      (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    exact_mod_cast h_count_cast
  -- ================== G. count at w_ref is at most one ==================
  have he_re : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).re = 1 / 2 := by
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  -- Any zero of `λ − w_ref` in the truncated region is `τ_ref`.
  have h_unique_δ : ∀ z ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀,
      (fun τ => modularLambdaH τ - w_ref) z = 0 → z = τ_ref := by
    intro z hz h_gz0
    have h_gz : modularLambdaH z - w_ref = 0 := h_gz0
    have h_lam_eq : modularLambdaH z = w_ref := sub_eq_zero.mp h_gz
    obtain ⟨hz_box, hz_ball⟩ := hz
    rw [Complex.mem_reProdIm] at hz_box
    obtain ⟨hz_re, hz_im⟩ := hz_box
    have hz_dist : R₀ ≤ ‖z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ := by
      simp only [Metric.mem_ball, Complex.dist_eq, not_lt] at hz_ball
      exact hz_ball
    -- Left edge excluded.
    by_cases h_re_0 : z.re = 0
    · exfalso
      have h_z_eq : z = (0 : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_re_0]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
      exact hg_left_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
    -- Right edge excluded.
    by_cases h_re_1 : z.re = 1
    · exfalso
      have h_z_eq : z = (1 : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_re_1]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
      exact hg_right_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
    -- Bottom edge excluded.
    by_cases h_im_δ : z.im = δ
    · exfalso
      have h_z_sub : z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)
          = ((z.re - 1 / 2 : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [Complex.sub_re, he_re, Complex.ofReal_re]
        · rw [Complex.sub_im, he_im, Complex.ofReal_im, h_im_δ, sub_self]
      rw [h_z_sub, Complex.norm_real, Real.norm_eq_abs] at hz_dist
      have h_z_eq : z = (z.re : ℂ) + (δ : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_im_δ]
      rcases abs_cases (z.re - 1 / 2) with ⟨h_abs_eq, _⟩ | ⟨h_abs_eq, _⟩
      · rw [h_abs_eq] at hz_dist
        exact hg_bot_right_wr z.re (Set.mem_Icc.mpr ⟨by linarith, hz_re.2⟩)
          (by rw [← h_z_eq]; exact h_gz)
      · rw [h_abs_eq] at hz_dist
        exact hg_bot_left_wr z.re (Set.mem_Icc.mpr ⟨hz_re.1, by linarith⟩)
          (by rw [← h_z_eq]; exact h_gz)
    -- Arc excluded, or interior point.
    rcases eq_or_lt_of_le hz_dist with h_norm_eq | h_arc_gt
    · exfalso
      have h_polar := Complex.norm_mul_exp_arg_mul_I
        (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I))
      have hζ_im_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).im := by
        rw [Complex.sub_im, he_im]
        linarith [hz_im.1]
      have hθ_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg :=
        Complex.arg_nonneg_iff.mpr hζ_im_nonneg
      have hθ_le_pi : (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg ≤ Real.pi :=
        Complex.arg_le_pi _
      have h_z_eq : z = _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
          ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) := by
        have h_cm : _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
            ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) =
            ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) + (R₀ : ℂ) *
              Complex.exp (((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg : ℂ) *
                Complex.I) := rfl
        rw [h_cm, h_norm_eq, h_polar]
        ring
      exact hg_arc_wr ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg)
        (Set.mem_Icc.mpr ⟨hθ_nonneg, hθ_le_pi⟩) (by rw [← h_z_eq]; exact h_gz)
    · -- Strictly interior: `z ∈ F°`, so `z = τ_ref` by the reference uniqueness.
      have h_im_gt : δ < z.im := lt_of_le_of_ne hz_im.1 (Ne.symm h_im_δ)
      have h_re_gt : 0 < z.re := lt_of_le_of_ne hz_re.1 (Ne.symm h_re_0)
      have h_re_lt : z.re < 1 := lt_of_le_of_ne hz_re.2 h_re_1
      have h_semi : 1 < ‖2 * z - 1‖ :=
        F_Y_point_in_gamma2_semicircle_exterior hδ_pos hR₀_lo h_im_gt h_arc_gt
      exact hτ_ref_unique z ⟨lt_trans hδ_pos h_im_gt, h_re_gt, h_re_lt, h_semi⟩ h_lam_eq
  have h_simple : (fun τ => modularLambdaH τ - w_ref) τ_ref = 0 →
      deriv (fun τ => modularLambdaH τ - w_ref) τ_ref ≠ 0 := by
    intro _
    have h_d : deriv (fun τ => modularLambdaH τ - w_ref) τ_ref
        = deriv modularLambdaH τ_ref := deriv_sub_const w_ref
    rw [h_d]
    exact hτ_ref_deriv
  have h_le_one : (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w_ref)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat ≤ 1 := by
    have key := Complex.divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
      (fun τ => modularLambdaH τ - w_ref) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w_ref hδ_pos hδ_lt_Y hR₀_pos)
      (by rw [he_im]; exact h_unique_δ)
      h_simple
    rw [he_im] at key
    exact key
  -- ================== H. count at w is at least two ==================
  obtain ⟨_h₁_im_pos, h₁_re_lo, h₁_re_hi, _h₁_semi⟩ := h₁_in
  obtain ⟨_h₂_im_pos, h₂_re_lo, h₂_re_hi, _h₂_semi⟩ := h₂_in
  have hτ₁_mem : τ₁ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨h₁_re_lo.le, h₁_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hδ_lt_τ₁_im.le, hτ₁_im_lt_Y.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₁_norm_gt.le
  have hτ₂_mem : τ₂ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨h₂_re_lo.le, h₂_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hδ_lt_τ₂_im.le, hτ₂_im_lt_Y.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₂_norm_gt.le
  have hτ₁_zero : (fun τ => modularLambdaH τ - w) τ₁ = 0 := by
    change modularLambdaH τ₁ - w = 0
    rw [h₁_eq, sub_self]
  have hτ₂_zero : (fun τ => modularLambdaH τ - w) τ₂ = 0 := by
    change modularLambdaH τ₂ - w = 0
    rw [h₂_eq, sub_self]
  have h_two_le : 2 ≤ (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    have key := Complex.two_le_divisor_sum_toNat_of_two_zeros_on_rectMinusUpperHalfDisk
      (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by norm_num) hR₀_pos
      (by rw [he_re]; linarith)
      (by rw [he_re]; linarith)
      (by rw [he_im]; exact h_δR_lt_Y)
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ_pos hδ_lt_Y hR₀_pos)
      (by
        rw [he_im]
        intro h0
        have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
        rw [Complex.ofReal_zero] at h0'
        exact hg_left_w δ (Set.mem_Icc.mpr ⟨le_refl δ, hδ_lt_Y.le⟩) h0')
      h_τ_ne hτ₁_mem hτ₁_zero hτ₂_mem hτ₂_zero
    rw [he_im] at key
    exact key
  omega

set_option maxHeartbeats 400000 in
-- Long single-declaration assembly of the degree argument (many large integral terms).
/-- **Nonvanishing of `λ'` at `F°`-preimages (degree-argument bootstrap).** A
vanishing derivative would make the preimage a double zero of `λ − w`, forcing
the F_Y zero count to be at least two; transporting the count along a
`w`-segment to the deep-cusp reference value caps it at one. -/
theorem modularLambdaH_F_interior_preimage_deriv_ne_zero
    {w : ℂ} (hw : 0 < w.im) {τ : ℂ}
    (h_in : τ ∈ Gamma2FundamentalDomainInterior)
    (h_eq : modularLambdaH τ = w) :
    deriv modularLambdaH τ ≠ 0 := by
  intro h_deriv_eq
  -- ================== A. deep-cusp reference value ==================
  obtain ⟨w_ref, τ_ref, hw_ref_im, _hτ_ref_in, _hτ_ref_eq, hτ_ref_deriv, hτ_ref_unique⟩ :=
    modularLambdaH_cusp_reference_value
  -- ================== B. segment bounds ==================
  obtain ⟨μ, hμ_pos, hμ_le_w_im, hμ_le_wref_im⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ w.im ∧ m ≤ w_ref.im :=
    ⟨min w.im w_ref.im, lt_min hw hw_ref_im, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨B, hB_pos, hB_ge_w, hB_ge_wref⟩ :
      ∃ b : ℝ, 0 < b ∧ ‖w‖ ≤ b ∧ ‖w_ref‖ ≤ b :=
    ⟨max ‖w‖ ‖w_ref‖,
      lt_of_lt_of_le (lt_of_lt_of_le hw (Complex.im_le_norm w)) (le_max_left _ _),
      le_max_left _ _, le_max_right _ _⟩
  -- `Im z ≥ μ` forces `‖z − 1‖ ≥ μ`.
  have h_im_to_sub_one : ∀ z : ℂ, μ ≤ z.im → μ ≤ ‖z - 1‖ := by
    intro z hz
    have h1 : (z - 1).im = z.im := by rw [Complex.sub_im, Complex.one_im, sub_zero]
    calc μ ≤ (z - 1).im := by rw [h1]; exact hz
      _ ≤ ‖z - 1‖ := Complex.im_le_norm _
  have hw_sub_one : μ ≤ ‖w - 1‖ := h_im_to_sub_one w hμ_le_w_im
  have hw_ref_sub_one : μ ≤ ‖w_ref - 1‖ := h_im_to_sub_one w_ref hμ_le_wref_im
  -- Segment-point bounds (i): imaginary part.
  have h_seg_im : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im := by
    intro s hs
    have h_im : ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im
        = (1 - s) * w.im + s * w_ref.im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h_im]
    have hP : 0 ≤ (1 - s) * (w.im - μ) :=
      mul_nonneg (by linarith [hs.2]) (by linarith [hμ_le_w_im])
    have hQ : 0 ≤ s * (w_ref.im - μ) :=
      mul_nonneg hs.1 (by linarith [hμ_le_wref_im])
    nlinarith [hP, hQ]
  -- Segment-point bounds (ii): norm.
  have h_seg_norm : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖ ≤ B := by
    intro s hs
    have h_tri := norm_add_le ((1 - (s : ℂ)) * w) ((s : ℂ) * w_ref)
    have h1 : ‖(1 - (s : ℂ)) * w‖ = (1 - s) * ‖w‖ := by
      rw [norm_mul]
      congr 1
      rw [show (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    have h2 : ‖(s : ℂ) * w_ref‖ = s * ‖w_ref‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    rw [h1, h2] at h_tri
    have hA := mul_le_mul_of_nonneg_left hB_ge_w (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
    have hC := mul_le_mul_of_nonneg_left hB_ge_wref hs.1
    calc ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖
        ≤ (1 - s) * ‖w‖ + s * ‖w_ref‖ := h_tri
      _ ≤ (1 - s) * B + s * B := add_le_add hA hC
      _ = B := by ring
  -- Segment-point bounds (iii): distance to `1`.
  have h_seg_sub_one : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref - 1‖ :=
    fun s hs => h_im_to_sub_one _ (h_seg_im s hs)
  -- ================== C. thresholds and region parameters ==================
  obtain ⟨δ_bl, hδ_bl_pos, _hδ_bl_lt, h_bl_prop⟩ :=
    modularLambdaH_F_Y_bot_left_strip_ne_uniform hμ_pos
  obtain ⟨δ_br, hδ_br_pos, _hδ_br_lt, h_br_prop⟩ :=
    modularLambdaH_F_Y_bot_right_strip_ne_uniform hB_pos
  obtain ⟨δ_arc, hδ_arc_pos, _hδ_arc_lt, h_arc_prop⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform hμ_pos hB_pos hμ_pos
  obtain ⟨Y₀, _hY₀_ge_one, hY₀_prop⟩ := modularLambdaH_top_edge_norm_lt_uniform hμ_pos
  obtain ⟨δ_max, hδ_max_pos, hδ_max_le_quarter, hδ_max_le_bl, hδ_max_le_br, hδ_max_le_arc⟩ :
      ∃ δ_m : ℝ, 0 < δ_m ∧ δ_m ≤ 1 / 4 ∧ δ_m ≤ δ_bl ∧ δ_m ≤ δ_br ∧ δ_m ≤ δ_arc :=
    ⟨min (min δ_bl δ_br) (min δ_arc (1 / 4)),
      lt_min (lt_min hδ_bl_pos hδ_br_pos) (lt_min hδ_arc_pos (by norm_num)),
      le_trans (min_le_right _ _) (min_le_right _ _),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _)⟩
  obtain ⟨δ, Y_base, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ_im, _hδ_lt_τ_im',
    hδ_lt_Y_base, hτ_im_lt_Y_base, _hτ_im_lt_Y_base',
    hR₀_pos, hR₀_lt, h_δR_lt_Y_base, hR₀_lo, hτ_norm_gt, _hτ_norm_gt'⟩ :=
    modularLambdaH_F_Y_params_exist_arc hw h_in h_in hδ_max_pos hδ_max_le_quarter
  obtain ⟨Y, hY_ge_base, hY_ge_Y₀⟩ : ∃ Y : ℝ, Y_base ≤ Y ∧ Y₀ ≤ Y :=
    ⟨max Y_base Y₀, le_max_left _ _, le_max_right _ _⟩
  have hδ_lt_Y : δ < Y := lt_of_lt_of_le hδ_lt_Y_base hY_ge_base
  have hτ_im_lt_Y : τ.im < Y := lt_of_lt_of_le hτ_im_lt_Y_base hY_ge_base
  have h_δR_lt_Y : δ + R₀ < Y := lt_of_lt_of_le h_δR_lt_Y_base hY_ge_base
  have hδ_le_δ_bl : δ ≤ δ_bl := le_trans hδ_le_δ_max hδ_max_le_bl
  have hδ_le_δ_br : δ ≤ δ_br := le_trans hδ_le_δ_max hδ_max_le_br
  have hδ_le_δ_arc : δ ≤ δ_arc := le_trans hδ_le_δ_max hδ_max_le_arc
  have hδ_le_quarter : δ ≤ 1 / 4 := le_trans hδ_le_δ_max hδ_max_le_quarter
  -- Coverage trick: the bottom edge intervals lie inside the cascade strips.
  have h_half_minus_R₀ : 1 / 2 - R₀ ≤ 2 * δ ^ 2 :=
    modularLambdaH_F_Y_arc_half_minus_R₀_bound hδ_pos hδ_le_quarter hR₀_lo hR₀_lt hR₀_pos
  have h_2δ_sq_le_δ : 2 * δ ^ 2 ≤ δ := by nlinarith [hδ_pos.le, hδ_le_quarter]
  have h_half_minus_R₀_le_δ : 1 / 2 - R₀ ≤ δ := le_trans h_half_minus_R₀ h_2δ_sq_le_δ
  -- ================== D. segment-uniform boundary facts ==================
  have hg_bot_left_u : ∀ w' : ℂ, μ ≤ ‖w' - 1‖ → ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    exact h_bl_prop δ hδ_pos hδ_le_δ_bl x hx.1 (le_trans hx.2 h_half_minus_R₀_le_δ) w' hw'
  have hg_bot_right_u : ∀ w' : ℂ, ‖w'‖ ≤ B → ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    refine h_br_prop δ hδ_pos hδ_le_δ_br x ?_ hx.2 w' hw'
    linarith [hx.1, h_half_minus_R₀_le_δ]
  have hg_top_u : ∀ w' : ℂ, μ ≤ w'.im → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw'_im x hx h_eq0
    have h_norm_lt : ‖modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I)‖ < μ :=
      hY₀_prop Y hY_ge_Y₀ x hx.1 hx.2
    have h_lam_eq : modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) = w' := by
      linear_combination h_eq0
    rw [h_lam_eq] at h_norm_lt
    linarith [Complex.im_le_norm w', hw'_im]
  have hg_right_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_right_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_left_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_left_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_arc_u : ∀ w' : ℂ, μ ≤ w'.im → ‖w'‖ ≤ B → μ ≤ ‖w' - 1‖ →
      ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
    intro w' h1 h2 h3 θ hθ
    exact h_arc_prop δ R₀ hδ_pos hδ_le_δ_arc hR₀_lo hR₀_lt θ hθ.1 hθ.2 w' h1 h2 h3
  -- The six boundary facts at `w`.
  have hg_bot_left_w := hg_bot_left_u w hw_sub_one
  have hg_bot_right_w := hg_bot_right_u w hB_ge_w
  have hg_top_w := hg_top_u w hμ_le_w_im
  have hg_right_w := hg_right_u w hw
  have hg_left_w := hg_left_u w hw
  have hg_arc_w := hg_arc_u w hμ_le_w_im hB_ge_w hw_sub_one
  -- The six boundary facts at `w_ref`.
  have hg_bot_left_wr := hg_bot_left_u w_ref hw_ref_sub_one
  have hg_bot_right_wr := hg_bot_right_u w_ref hB_ge_wref
  have hg_top_wr := hg_top_u w_ref hμ_le_wref_im
  have hg_right_wr := hg_right_u w_ref hw_ref_im
  have hg_left_wr := hg_left_u w_ref hw_ref_im
  have hg_arc_wr := hg_arc_u w_ref hμ_le_wref_im hB_ge_wref hw_ref_sub_one
  -- Transport hypothesis: the image curve avoids the whole segment.
  have h_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) ≠
        (1 - (s : ℂ)) * w + (s : ℂ) * w_ref := by
    intro s hs t ht
    have h_ne := F_Y_image_curve_ne_zero (w := (1 - (s : ℂ)) * w + (s : ℂ) * w_ref)
      hR₀_pos hR₀_lt hδ_lt_Y.le
      (hg_bot_left_u _ (h_seg_sub_one s hs))
      (hg_bot_right_u _ (h_seg_norm s hs))
      (hg_top_u _ (h_seg_im s hs))
      (hg_right_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_left_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_arc_u _ (h_seg_im s hs) (h_seg_norm s hs) (h_seg_sub_one s hs))
      t ht
    exact sub_ne_zero.mp h_ne
  -- ================== F. identity chain N(w) = N(w_ref) ==================
  have h_div_w := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_div_wr := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_LHS_w := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_LHS_wr := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_transport := modularLambdaH_F_Y_pathContourIntegral_eq_of_segment_avoids
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_avoid
  have h_count_cast :
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) =
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) := by
    rw [← h_div_w, ← h_div_wr, h_LHS_w, h_LHS_wr, h_transport]
  have h_count_eq :
      (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat =
      (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    exact_mod_cast h_count_cast
  -- ================== G. count at w_ref is at most one ==================
  have he_re : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).re = 1 / 2 := by
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  -- Any zero of `λ − w_ref` in the truncated region is `τ_ref`.
  have h_unique_δ : ∀ z ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀,
      (fun τ' => modularLambdaH τ' - w_ref) z = 0 → z = τ_ref := by
    intro z hz h_gz0
    have h_gz : modularLambdaH z - w_ref = 0 := h_gz0
    have h_lam_eq : modularLambdaH z = w_ref := sub_eq_zero.mp h_gz
    obtain ⟨hz_box, hz_ball⟩ := hz
    rw [Complex.mem_reProdIm] at hz_box
    obtain ⟨hz_re, hz_im⟩ := hz_box
    have hz_dist : R₀ ≤ ‖z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ := by
      simp only [Metric.mem_ball, Complex.dist_eq, not_lt] at hz_ball
      exact hz_ball
    -- Left edge excluded.
    by_cases h_re_0 : z.re = 0
    · exfalso
      have h_z_eq : z = (0 : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_re_0]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
      exact hg_left_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
    -- Right edge excluded.
    by_cases h_re_1 : z.re = 1
    · exfalso
      have h_z_eq : z = (1 : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_re_1]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
      exact hg_right_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
    -- Bottom edge excluded.
    by_cases h_im_δ : z.im = δ
    · exfalso
      have h_z_sub : z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)
          = ((z.re - 1 / 2 : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [Complex.sub_re, he_re, Complex.ofReal_re]
        · rw [Complex.sub_im, he_im, Complex.ofReal_im, h_im_δ, sub_self]
      rw [h_z_sub, Complex.norm_real, Real.norm_eq_abs] at hz_dist
      have h_z_eq : z = (z.re : ℂ) + (δ : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_im_δ]
      rcases abs_cases (z.re - 1 / 2) with ⟨h_abs_eq, _⟩ | ⟨h_abs_eq, _⟩
      · rw [h_abs_eq] at hz_dist
        exact hg_bot_right_wr z.re (Set.mem_Icc.mpr ⟨by linarith, hz_re.2⟩)
          (by rw [← h_z_eq]; exact h_gz)
      · rw [h_abs_eq] at hz_dist
        exact hg_bot_left_wr z.re (Set.mem_Icc.mpr ⟨hz_re.1, by linarith⟩)
          (by rw [← h_z_eq]; exact h_gz)
    -- Arc excluded, or interior point.
    rcases eq_or_lt_of_le hz_dist with h_norm_eq | h_arc_gt
    · exfalso
      have h_polar := Complex.norm_mul_exp_arg_mul_I
        (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I))
      have hζ_im_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).im := by
        rw [Complex.sub_im, he_im]
        linarith [hz_im.1]
      have hθ_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg :=
        Complex.arg_nonneg_iff.mpr hζ_im_nonneg
      have hθ_le_pi : (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg ≤ Real.pi :=
        Complex.arg_le_pi _
      have h_z_eq : z = _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
          ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) := by
        have h_cm : _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
            ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) =
            ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) + (R₀ : ℂ) *
              Complex.exp (((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg : ℂ) *
                Complex.I) := rfl
        rw [h_cm, h_norm_eq, h_polar]
        ring
      exact hg_arc_wr ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg)
        (Set.mem_Icc.mpr ⟨hθ_nonneg, hθ_le_pi⟩) (by rw [← h_z_eq]; exact h_gz)
    · -- Strictly interior: `z ∈ F°`, so `z = τ_ref` by the reference uniqueness.
      have h_im_gt : δ < z.im := lt_of_le_of_ne hz_im.1 (Ne.symm h_im_δ)
      have h_re_gt : 0 < z.re := lt_of_le_of_ne hz_re.1 (Ne.symm h_re_0)
      have h_re_lt : z.re < 1 := lt_of_le_of_ne hz_re.2 h_re_1
      have h_semi : 1 < ‖2 * z - 1‖ :=
        F_Y_point_in_gamma2_semicircle_exterior hδ_pos hR₀_lo h_im_gt h_arc_gt
      exact hτ_ref_unique z ⟨lt_trans hδ_pos h_im_gt, h_re_gt, h_re_lt, h_semi⟩ h_lam_eq
  have h_simple : (fun τ' => modularLambdaH τ' - w_ref) τ_ref = 0 →
      deriv (fun τ' => modularLambdaH τ' - w_ref) τ_ref ≠ 0 := by
    intro _
    have h_d : deriv (fun τ' => modularLambdaH τ' - w_ref) τ_ref
        = deriv modularLambdaH τ_ref := deriv_sub_const w_ref
    rw [h_d]
    exact hτ_ref_deriv
  have h_le_one : (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w_ref)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat ≤ 1 := by
    have key := Complex.divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
      (fun τ' => modularLambdaH τ' - w_ref) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w_ref hδ_pos hδ_lt_Y hR₀_pos)
      (by rw [he_im]; exact h_unique_δ)
      h_simple
    rw [he_im] at key
    exact key
  -- ================== H. count at w is at least two (double zero) ==================
  obtain ⟨_h_im_pos, h_re_lo, h_re_hi, _h_semi⟩ := h_in
  have hτ_mem : τ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨h_re_lo.le, h_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hδ_lt_τ_im.le, hτ_im_lt_Y.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ_norm_gt.le
  have hτ_zero : (fun τ' => modularLambdaH τ' - w) τ = 0 := by
    change modularLambdaH τ - w = 0
    rw [h_eq, sub_self]
  have hτ_deriv_zero : deriv (fun τ' => modularLambdaH τ' - w) τ = 0 := by
    have h_d : deriv (fun τ' => modularLambdaH τ' - w) τ
        = deriv modularLambdaH τ := deriv_sub_const w
    rw [h_d]
    exact h_deriv_eq
  have h_two_le : 2 ≤ (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    have key := Complex.two_le_divisor_sum_toNat_of_double_zero_on_rectMinusUpperHalfDisk
      (fun τ' => modularLambdaH τ' - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by norm_num) hR₀_pos
      (by rw [he_re]; linarith)
      (by rw [he_re]; linarith)
      (by rw [he_im]; exact h_δR_lt_Y)
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ_pos hδ_lt_Y hR₀_pos)
      (by
        rw [he_im]
        intro h0
        have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
        rw [Complex.ofReal_zero] at h0'
        exact hg_left_w δ (Set.mem_Icc.mpr ⟨le_refl δ, hδ_lt_Y.le⟩) h0')
      hτ_mem hτ_zero hτ_deriv_zero
    rw [he_im] at key
    exact key
  omega

/-- **Topological-winding result: image-curve contour integral equals 2πi.**
For `w ∈ ℍ` with a `λ`-preimage `τ₀ ∈ F°` located inside the truncated
region (above the bottom edge, below the top edge, outside the excised
arc-ball), and valid F_Y parameters satisfying the cusp-excision bounds
`δ ≤ 1/4` and `√(1/4 − δ²) < R₀`, with `λ ≠ w` on each boundary piece:
the contour integral of `(z − w)⁻¹` along the image curve
`λ ∘ F_Y_boundary_parameterization δ Y R₀` over `[0, 6]` equals exactly
`2πi`.

The hypothesis set is the minimal one making the statement true:

* Without `hR₀_lo`, the region F_Y reaches into the cusp at `1/2`,
  where the Γ(2)-orbit of `τ₀` clusters just above the bottom edge,
  making the winding integer exceed `1`.
* Without the preimage-location data (`hτ₀_im_lo`, `hτ₀_im_hi`,
  `hτ₀_arc`), `w` may have no preimage in F_Y at all (e.g. when the
  unique `F°`-preimage lies below the bottom edge `Im τ = δ`), making
  the winding integer `0`.
* By `F_Y_point_in_gamma2_semicircle_exterior`, the arc bound places
  the interior of F_Y inside `F°`, so the zeros of `λ − w` in F_Y are
  exactly its `F°`-preimages there — `τ₀` is one of them (simple,
  since `λ' ≠ 0` on `{Im λ > 0}`), and the winding-1 claim is
  equivalent to `τ₀` being the only one.

Proof route: by `image_curve_lambda_F_Y_homotopic_to_circle` the image
curve is continuously homotopic to a parameterized CCW circle around
`w` with angular speed `π/3`. Applying
`_pathContourIntegral_eq_circle_via_homotopy` equates the two contour
integrals. The circle integral computes directly via chain rule:
`d/dt(circleMap w ε (t π/3)) = (π/3) · ε · exp(I(t π/3)) · I`, so the
integrand `(circleMap - w)⁻¹ · deriv = (ε exp(I t π/3))⁻¹ ·
(π ε I / 3) · exp(I t π/3) = I π / 3` is constant, giving
`∫₀⁶ I π / 3 dt = 2πI`. -/
theorem modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_two_pi_I
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (_hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖) :
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w)⁻¹) = 2 * Real.pi * Complex.I := by
  -- Extract the homotopy from image_curve_lambda_F_Y_homotopic_to_circle —
  -- now exposing the 1D log lift `L` and the explicit log-space form of `H`.
  obtain ⟨ε, L, H, hε_pos, hL_cont, hL_exp, hH_form, hH_cont, hH_0, hH_1, hH_avoid⟩ :=
    image_curve_lambda_F_Y_homotopic_to_circle hw hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
      hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  -- Architectural setup for `hH_closed`:
  -- (1) The F_Y boundary curve closes at the corners: `γ(0) = γ(6) = δ·i`.
  -- (2) Hence the log lift `L` satisfies `exp(L 0) = exp(L 6)`, so by
  --     `winding_lift_integer_coeff` there is `K : ℤ` with
  --     `L 6 − L 0 = K · 2πi` (the topological winding integer).
  -- (3) For the explicit `H s t = w + exp((1−s)·L t + s·t·π/3·i)`,
  --     `H s 0 = H s 6` reduces algebraically to the integer-valuedness of
  --     the affine real map `s ↦ K + s·(1 − K)` on `[0, 1]`.
  -- (4) `K_eq_one_of_affine_int_valued_on_unit_interval` then forces `K = 1`,
  --     and `H_explicit_closed_of_K_eq_one` recovers `hH_closed`.
  -- The remaining input — the affine integer-valuedness on `[0, 1]` — is the
  -- deep topological fact equivalent to `hH_closed`; it is proved below via
  -- the degree-argument bootstrap.
  have hγ_closed : F_Y_boundary_parameterization δ Y R₀ 0 =
      F_Y_boundary_parameterization δ Y R₀ 6 := by
    unfold F_Y_boundary_parameterization
    have h0_le_1 : (0 : ℝ) ≤ 1 := by norm_num
    have h6_not_le_1 : ¬((6 : ℝ) ≤ 1) := by norm_num
    have h6_not_le_2 : ¬((6 : ℝ) ≤ 2) := by norm_num
    have h6_not_le_3 : ¬((6 : ℝ) ≤ 3) := by norm_num
    have h6_not_le_4 : ¬((6 : ℝ) ≤ 4) := by norm_num
    have h6_not_le_5 : ¬((6 : ℝ) ≤ 5) := by norm_num
    have h6_le_6 : (6 : ℝ) ≤ 6 := by norm_num
    rw [if_pos h0_le_1, if_neg h6_not_le_1, if_neg h6_not_le_2,
        if_neg h6_not_le_3, if_neg h6_not_le_4, if_neg h6_not_le_5, if_pos h6_le_6]
    push_cast; ring
  have hL_lift_closed : Complex.exp (L 0) = Complex.exp (L 6) := by
    have h0 : Complex.exp (L 0) =
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ 0) - w :=
      hL_exp 0 ⟨by norm_num, by norm_num⟩
    have h6 : Complex.exp (L 6) =
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ 6) - w :=
      hL_exp 6 ⟨by norm_num, by norm_num⟩
    rw [h0, h6, hγ_closed]
  obtain ⟨K, hK_eq⟩ := winding_lift_integer_coeff L hL_lift_closed
  -- Deep topological fact: the affine real map `s ↦ K + s·(1 − K)` is
  -- integer-valued at every `s ∈ [0, 1]` — equivalent (via
  -- `K_eq_one_of_affine_int_valued_on_unit_interval`) to the winding
  -- integer `K` being `1`. The hypothesis set is exactly what makes
  -- this true: by `F_Y_point_in_gamma2_semicircle_exterior` (using
  -- `hR₀_lo`), the interior of F_Y lies in `F°`, so `K` equals the
  -- number of `F°`-preimages of `w` inside F_Y counted with
  -- multiplicity; `τ₀` is one such preimage (`hτ₀_im_lo`/`hτ₀_im_hi`/
  -- `hτ₀_arc` place it inside, and it is a simple zero since `λ' ≠ 0`
  -- on `{Im λ > 0}`). `K = 1` is therefore equivalent to `τ₀` being
  -- the unique `F°`-preimage of `w` in F_Y — provable either by the
  -- direct boundary-tracking argument (total argument variation of
  -- `λ − w` along the six near-real boundary pieces equals `2π`) or
  -- by the Γ(2) orbit-uniqueness property of the fundamental domain.
  -- Proved here by the degree argument: `K` equals the divisor sum `N` of
  -- `λ − w` on the truncated region (FTC + AP chain), and `N = 1` since
  -- `τ₀` is its unique simple zero there (degree-argument bootstrap
  -- `modularLambdaH_F_interior_preimage_unique` / `_deriv_ne_zero`).
  have h_tau_int_valued : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, (K : ℝ) + s * (1 - K) = n := by
    -- (a) The image curve avoids zero on `[0, 6]`.
    have hγ_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w ≠ 0 :=
      F_Y_image_curve_ne_zero hR₀_pos hR₀_lt hδY.le
        hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    -- (b) FTC along the log lift: the contour integral is `L 6 − L 0`.
    have h_ftc := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
      hδ hδY hR₀_pos hR₀_lt hγ_ne L hL_cont hL_exp
    -- (c) Bridge: six-term boundary expression = path contour integral.
    have h_lhs := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
      hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
      hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    -- (d) Argument principle: normalized expression = divisor sum `N`.
    have h_div := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
      hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
      hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    -- (e) Combine (b)–(d) with `hK_eq`: `(K : ℂ) = (N : ℂ)`.
    rw [h_lhs, h_ftc, hK_eq] at h_div
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have h_cancel : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ((K : ℂ) * (2 * Real.pi * Complex.I)) = (K : ℂ) := by
      rw [mul_comm ((K : ℂ)) (2 * Real.pi * Complex.I), ← mul_assoc,
        inv_mul_cancel₀ hpi, one_mul]
    rw [h_cancel] at h_div
    -- Coordinates of the excised-ball center.
    have he_re : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).re = 1 / 2 := by
      rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
      rw [h_half_re]; ring
    have he_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
      rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
      rw [h_half_im]; ring
    obtain ⟨hτ₀_im_pos, hτ₀_re_lo, hτ₀_re_hi, hτ₀_semi⟩ := id hτ₀_in
    have hτ₀_zero : (fun τ => modularLambdaH τ - w) τ₀ = 0 := by
      change modularLambdaH τ₀ - w = 0
      rw [hτ₀_eq, sub_self]
    -- (f) Lower bound: `τ₀` is a zero in the region, so `1 ≤ N`.
    have h_one_le : 1 ≤ (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
      have hτ₀_mem : τ₀ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
          Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
        rw [he_im]
        refine ⟨?_, ?_⟩
        · rw [Complex.mem_reProdIm]
          exact ⟨Set.mem_Icc.mpr ⟨hτ₀_re_lo.le, hτ₀_re_hi.le⟩,
            Set.mem_Icc.mpr ⟨hτ₀_im_lo.le, hτ₀_im_hi.le⟩⟩
        · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
          exact hτ₀_arc.le
      have key := Complex.one_le_divisor_sum_toNat_of_zero_on_rectMinusUpperHalfDisk
        (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (by norm_num) hR₀_pos
        (by rw [he_re]; linarith)
        (by rw [he_re]; linarith)
        (by rw [he_im]; exact h_δR_lt_Y)
        (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos)
        (by
          rw [he_im]
          intro h0
          have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
          rw [Complex.ofReal_zero] at h0'
          exact hg_left δ (Set.mem_Icc.mpr ⟨le_refl δ, hδY.le⟩) h0')
        hτ₀_mem hτ₀_zero
      rw [he_im] at key
      exact key
    -- (g) Upper bound: `τ₀` is the unique simple zero, so `N ≤ 1`.
    have h_unique_δ : ∀ z ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀,
        (fun τ => modularLambdaH τ - w) z = 0 → z = τ₀ := by
      intro z hz h_gz0
      have h_gz : modularLambdaH z - w = 0 := h_gz0
      have h_lam_eq : modularLambdaH z = w := sub_eq_zero.mp h_gz
      obtain ⟨hz_box, hz_ball⟩ := hz
      rw [Complex.mem_reProdIm] at hz_box
      obtain ⟨hz_re, hz_im⟩ := hz_box
      have hz_dist : R₀ ≤ ‖z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ := by
        simp only [Metric.mem_ball, Complex.dist_eq, not_lt] at hz_ball
        exact hz_ball
      -- Left edge excluded.
      by_cases h_re_0 : z.re = 0
      · exfalso
        have h_z_eq : z = (0 : ℂ) + (z.im : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_re_0]
          · simp [Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        exact hg_left z.im hz_im (by rw [← h_z_eq]; exact h_gz)
      -- Right edge excluded.
      by_cases h_re_1 : z.re = 1
      · exfalso
        have h_z_eq : z = (1 : ℂ) + (z.im : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_re_1]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        exact hg_right z.im hz_im (by rw [← h_z_eq]; exact h_gz)
      -- Top edge excluded.
      by_cases h_im_Y : z.im = Y
      · exfalso
        have h_z_eq : z = (z.re : ℂ) + (Y : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_im_Y]
        exact hg_top z.re hz_re (by rw [← h_z_eq]; exact h_gz)
      -- Bottom edge excluded.
      by_cases h_im_δ : z.im = δ
      · exfalso
        have h_z_sub : z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)
            = ((z.re - 1 / 2 : ℝ) : ℂ) := by
          apply Complex.ext
          · rw [Complex.sub_re, he_re, Complex.ofReal_re]
          · rw [Complex.sub_im, he_im, Complex.ofReal_im, h_im_δ, sub_self]
        rw [h_z_sub, Complex.norm_real, Real.norm_eq_abs] at hz_dist
        have h_z_eq : z = (z.re : ℂ) + (δ : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_im_δ]
        rcases abs_cases (z.re - 1 / 2) with ⟨h_abs_eq, _⟩ | ⟨h_abs_eq, _⟩
        · rw [h_abs_eq] at hz_dist
          exact hg_bot_right z.re (Set.mem_Icc.mpr ⟨by linarith, hz_re.2⟩)
            (by rw [← h_z_eq]; exact h_gz)
        · rw [h_abs_eq] at hz_dist
          exact hg_bot_left z.re (Set.mem_Icc.mpr ⟨hz_re.1, by linarith⟩)
            (by rw [← h_z_eq]; exact h_gz)
      -- Arc excluded, or interior point.
      rcases eq_or_lt_of_le hz_dist with h_norm_eq | h_arc_gt
      · exfalso
        have h_polar := Complex.norm_mul_exp_arg_mul_I
          (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I))
        have hζ_im_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).im := by
          rw [Complex.sub_im, he_im]
          linarith [hz_im.1]
        have hθ_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg :=
          Complex.arg_nonneg_iff.mpr hζ_im_nonneg
        have hθ_le_pi : (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg ≤ Real.pi :=
          Complex.arg_le_pi _
        have h_z_eq : z = _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
            ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) := by
          have h_cm : _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
              ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) =
              ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) + (R₀ : ℂ) *
                Complex.exp (((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg : ℂ) *
                  Complex.I) := rfl
          rw [h_cm, h_norm_eq, h_polar]
          ring
        exact hg_arc ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg)
          (Set.mem_Icc.mpr ⟨hθ_nonneg, hθ_le_pi⟩) (by rw [← h_z_eq]; exact h_gz)
      · -- Strictly interior: `z ∈ F°`, so `z = τ₀` by the bootstrap uniqueness.
        have h_im_gt : δ < z.im := lt_of_le_of_ne hz_im.1 (Ne.symm h_im_δ)
        have h_re_gt : 0 < z.re := lt_of_le_of_ne hz_re.1 (Ne.symm h_re_0)
        have h_re_lt : z.re < 1 := lt_of_le_of_ne hz_re.2 h_re_1
        have h_semi : 1 < ‖2 * z - 1‖ :=
          F_Y_point_in_gamma2_semicircle_exterior hδ hR₀_lo h_im_gt h_arc_gt
        exact modularLambdaH_F_interior_preimage_unique hw
          ⟨lt_trans hδ h_im_gt, h_re_gt, h_re_lt, h_semi⟩ hτ₀_in h_lam_eq hτ₀_eq
    have h_simple : (fun τ => modularLambdaH τ - w) τ₀ = 0 →
        deriv (fun τ => modularLambdaH τ - w) τ₀ ≠ 0 := by
      intro _
      have h_d : deriv (fun τ => modularLambdaH τ - w) τ₀
          = deriv modularLambdaH τ₀ := deriv_sub_const w
      rw [h_d]
      exact modularLambdaH_F_interior_preimage_deriv_ne_zero hw hτ₀_in hτ₀_eq
    have h_le_one : (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat ≤ 1 := by
      have key := Complex.divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
        (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos)
        (by rw [he_im]; exact h_unique_δ)
        h_simple
      rw [he_im] at key
      exact key
    -- (h) `N = 1`, hence `K = 1`, hence the affine map is constantly `1`.
    have hN_eq : (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat = 1 :=
      le_antisymm h_le_one h_one_le
    rw [hN_eq] at h_div
    have hK_one : K = 1 := by exact_mod_cast h_div
    exact fun s _ => ⟨1, by rw [hK_one]; push_cast; ring⟩
  have hK_one : K = 1 :=
    K_eq_one_of_affine_int_valued_on_unit_interval h_tau_int_valued
  have hL_eq : L 6 - L 0 = (2 * Real.pi * Complex.I : ℂ) := by
    rw [hK_eq, hK_one]; push_cast; ring
  have hH_explicit_closed := H_explicit_closed_of_K_eq_one w L hL_eq
  have hH_closed : ∀ s ∈ Set.Icc (0 : ℝ) 1, H s 0 = H s 6 := by
    intro s hs
    rw [hH_form s 0, hH_form s 6]
    exact hH_explicit_closed s hs
  -- Apply continuous-homotopy invariance to equate image and circle integrals.
  rw [modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_circle_via_homotopy
    hδ hδY hR₀_pos hR₀_lt ε hε_pos H hH_cont hH_0 hH_1 hH_avoid hH_closed]
  -- Compute the circle integral directly.
  unfold Complex.pathContourIntegral
  -- Goal: ∫ t in 0..6, (circleMap w ε (t * π / 3) - w)⁻¹ * deriv (.) t = 2πi.
  have h_integrand : ∀ t : ℝ,
      (fun z => (z - w)⁻¹) (_root_.circleMap w ε (t * Real.pi / 3)) *
        deriv (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3)) t =
      Complex.I * (Real.pi / 3) := by
    intro t
    -- Compute deriv via chain rule.
    have h_inner : HasDerivAt (fun s : ℝ => s * Real.pi / 3) (Real.pi / 3) t := by
      have h1 : HasDerivAt (fun y : ℝ => id y * Real.pi) (1 * Real.pi) t :=
        (hasDerivAt_id t).mul_const Real.pi
      simp only [id, one_mul] at h1
      exact h1.div_const 3
    have h_outer := hasDerivAt_circleMap w ε (t * Real.pi / 3)
    have h_comp := h_outer.scomp t h_inner
    have h_deriv_eq : deriv (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3)) t =
        (Real.pi / 3 : ℝ) • (_root_.circleMap 0 ε (t * Real.pi / 3) * Complex.I) :=
      h_comp.deriv
    rw [h_deriv_eq]
    -- circleMap w ε θ - w = circleMap 0 ε θ.
    have h_sub : _root_.circleMap w ε (t * Real.pi / 3) - w =
        _root_.circleMap 0 ε (t * Real.pi / 3) := by
      unfold _root_.circleMap; ring
    change (_root_.circleMap w ε (t * Real.pi / 3) - w)⁻¹ * _ = _
    rw [h_sub]
    -- circleMap 0 ε θ ≠ 0.
    have h_circ_ne : _root_.circleMap 0 ε (t * Real.pi / 3) ≠ 0 := by
      unfold _root_.circleMap
      simp only [zero_add]
      refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
      exact_mod_cast ne_of_gt hε_pos
    -- Simplify.
    rw [Complex.real_smul]
    field_simp
    push_cast
    ring
  -- Use the constant integrand to evaluate the integral.
  rw [intervalIntegral.integral_congr (g := fun _ => Complex.I * (Real.pi / 3))
    (fun t _ => h_integrand t)]
  rw [intervalIntegral.integral_const]
  change ((6 - 0 : ℝ) : ℂ) * (Complex.I * (Real.pi / 3)) = 2 * Real.pi * Complex.I
  push_cast
  ring

/-- **Sub-lemma 9.aux.B2.core — Image curve winding index is 1.**
The load-bearing topological/geometric core sub-helper for B2. For any
`n : ℕ` satisfying the AP-derived identity, `n` equals the winding
index of the image curve `λ ∘ ∂F_Y` around `w`, which is `1`.

Proof: bridge the 6-term boundary integral expression to
`pathContourIntegral (λ ∘ F_Y_boundary_parameterization) 0 6 ((z − w)⁻¹)`
via `_LHS_eq_pathContourIntegral`, then apply
`_pathContourIntegral_eq_two_pi_I` (the topological winding result).
Combining with the AP-derived hypothesis `(2πi)⁻¹ · expression = (n : ℂ)`
gives `(n : ℂ) = 1`, hence `n = 1`. -/
theorem modularLambdaH_F_Y_image_curve_winding_index_eq_one
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖)
    {n : ℕ}
    (hn : (2 * Real.pi * Complex.I)⁻¹ * ((∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ)) :
    n = 1 := by
  -- Bridge LHS to pathContourIntegral via the chain-rule sub-helper.
  have h_bridge := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  -- Topological winding via homotopy + circle.
  have h_topo := modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_two_pi_I
    hw hδ hδY hR₀_pos hR₀_lt hδ_le hR₀_lo h_δR_lt_Y
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    τ₀ hτ₀_in hτ₀_eq hτ₀_im_lo hτ₀_im_hi hτ₀_arc
  -- Combine: (2πi)⁻¹ · 2πi = 1 = (n : ℂ).
  rw [h_bridge, h_topo] at hn
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  rw [inv_mul_cancel₀ hpi] at hn
  exact_mod_cast hn.symm

/-- **Sub-lemma 9.aux.B2 — AP natural-count equals 1.**
For `w ∈ ℍ` and any `n : ℕ` satisfying the AP-derived identity
`(2πi)⁻¹ · (boundary integral) = (n : ℂ)`, the count `n` equals 1.
Mathematically, this asserts the winding number of `λ ∘ ∂F_Y` around `w`
equals 1.

Body: trivial wrapper around
`modularLambdaH_F_Y_image_curve_winding_index_eq_one`, which carries
the load-bearing topological argument. The split keeps B2's role in the
B1/B2/`_boundary_integral_eq_two_pi_I`/`_winding_eq_one` chain clean
while isolating the topological core for future refinement. -/
theorem modularLambdaH_F_Y_AP_count_eq_one
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖)
    {n : ℕ}
    (hn : (2 * Real.pi * Complex.I)⁻¹ * ((∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ)) :
    n = 1 :=
  modularLambdaH_F_Y_image_curve_winding_index_eq_one hw hδ hδY hR₀_pos hR₀_lt
    hδ_le hR₀_lo h_δR_lt_Y hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    τ₀ hτ₀_in hτ₀_eq hτ₀_im_lo hτ₀_im_hi hτ₀_arc hn

/-- **Sub-lemma 9.aux — F_Y boundary integral of `λ'/(λ − w)` equals `2πi`.**

For `w ∈ ℍ` and valid F_Y parameters with `λ ≠ w` on each of the six
boundary pieces, the closed-boundary integral of `λ'/(λ − w)` around
`∂F_Y` (CCW, region on the left) equals exactly `2πi`. Equivalently,
the image curve `λ ∘ ∂F_Y` has winding number `1` around `w`.

Proof: combine `modularLambdaH_F_Y_AP_integral_eq_nat_form` (returning
`(2πi)⁻¹ · integral = n` for some `n : ℕ`) with
`modularLambdaH_F_Y_AP_count_eq_one` (`n = 1`), then multiply by `2πi`. -/
theorem modularLambdaH_F_Y_boundary_integral_eq_two_pi_I
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖) :
    (∫ x in (0 : ℝ)..(1 / 2 - R₀),
      deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
      (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
    (∫ x in (1 / 2 + R₀ : ℝ)..1,
      deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
      (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
    Complex.I * (∫ y in (δ : ℝ)..Y,
      deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
      (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
    (∫ x in (0 : ℝ)..1,
      deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
      (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
    Complex.I * (∫ y in (δ : ℝ)..Y,
      deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
      (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
    (∫ θ in (0 : ℝ)..Real.pi,
      deriv modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
      (modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
    2 * Real.pi * Complex.I := by
  obtain ⟨n, hn⟩ := modularLambdaH_F_Y_AP_integral_eq_nat_form hδ hδY hR₀_pos hR₀_lt
    h_δR_lt_Y hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  have h_n_one : n = 1 := modularLambdaH_F_Y_AP_count_eq_one hw hδ hδY hR₀_pos hR₀_lt
    hδ_le hR₀_lo h_δR_lt_Y hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    τ₀ hτ₀_in hτ₀_eq hτ₀_im_lo hτ₀_im_hi hτ₀_arc hn
  rw [h_n_one, Nat.cast_one] at hn
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  have h_mul : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ * _) =
      (2 * Real.pi * Complex.I) * 1 := congrArg _ hn
  rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at h_mul
  exact h_mul

/-- **Sub-lemma 9 — winding number computation = 1.** For `w ∈ ℍ` and
valid F_Y parameters with `λ ≠ w` on each of the six boundary pieces,
the boundary integral expression from the F_Y AP — applied to
`g(τ) := λ(τ) − w` — divided by `2πi` equals `1`. Hence the natural-
number count from the F_Y AP equals `1`.

Proof: by `modularLambdaH_F_Y_boundary_integral_eq_two_pi_I`, the
boundary integral equals `2πi`. Then `(2πi)⁻¹ · (2πi) = 1`. -/
theorem modularLambdaH_F_Y_winding_eq_one
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = 1 := by
  have h_integral := modularLambdaH_F_Y_boundary_integral_eq_two_pi_I hw hδ hδY hR₀_pos
    hR₀_lt hδ_le hR₀_lo h_δR_lt_Y hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    τ₀ hτ₀_in hτ₀_eq hτ₀_im_lo hτ₀_im_hi hτ₀_arc
  rw [h_integral]
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  exact inv_mul_cancel₀ hpi

/-- **Sub-lemma 9.aux.B3 — Two distinct zeros force AP count `≥ 2`.**
A refinement of the F_Y argument principle exposing the natural-number
count as the divisor sum. For `g(τ) = λ(τ) − w` with two distinct zeros
`τ₁, τ₂` in the **open** F_Y interior, the natural number `n` returned
by the AP existential (`(2πi)⁻¹ · integral = (n : ℂ)`) satisfies `n ≥ 2`.

Combined with `_winding_eq_one` (giving `(2πi)⁻¹ · integral = 1`, hence
`n = 1`), this yields a contradiction, proving uniqueness of preimages
in F_Y interior.

Proof strategy: factor `g = r · h` via `MeromorphicOn.extract_zeros_poles`
on the F_Y region. The natural number `n` from `cIntegralLogDeriv_isNat`
equals the divisor sum of `g` over `F_Y` (this requires either reaching
inside the AP theorem's existing proof or restating with the explicit
divisor sum). Each zero `τᵢ` contributes at least `1` to the divisor
sum (multiplicity ≥ 1 since `g τᵢ = 0` and `g` analytic, distinct from
the analyticOrder-defined `0` value). Two distinct zeros ⟹ sum ≥ 2. -/
theorem modularLambdaH_F_Y_AP_count_ge_two_of_two_distinct_zeros
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    {τ₁ τ₂ : ℂ}
    (hτ₁_re_lo : 0 < τ₁.re) (hτ₁_re_hi : τ₁.re < 1)
    (hτ₁_im_lo : δ < τ₁.im) (hτ₁_im_hi : τ₁.im < Y)
    (hτ₁_outside : R₀ < ‖τ₁ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖)
    (hτ₂_re_lo : 0 < τ₂.re) (hτ₂_re_hi : τ₂.re < 1)
    (hτ₂_im_lo : δ < τ₂.im) (hτ₂_im_hi : τ₂.im < Y)
    (hτ₂_outside : R₀ < ‖τ₂ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖)
    (hτ_ne : τ₁ ≠ τ₂)
    (hlam_τ₁ : modularLambdaH τ₁ = w) (hlam_τ₂ : modularLambdaH τ₂ = w)
    {n : ℕ}
    (hn : (2 * Real.pi * Complex.I)⁻¹ * ((∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ)) :
    2 ≤ n := by
  -- (1) Argument principle: the normalized boundary expression equals the
  -- divisor sum `N` of `λ − w` on the truncated region.
  have h_div := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  -- (2) Identify `n` with the divisor sum.
  have h_cast := hn.symm.trans h_div
  have h_n_eq : n = (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    exact_mod_cast h_cast
  -- Coordinates of the excised-ball center.
  have he_re : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).re = 1 / 2 := by
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  -- (3) `τ₁`, `τ₂` are two distinct zeros of `λ − w` in the region.
  have hτ₁_zero : (fun τ => modularLambdaH τ - w) τ₁ = 0 := by
    change modularLambdaH τ₁ - w = 0
    rw [hlam_τ₁, sub_self]
  have hτ₂_zero : (fun τ => modularLambdaH τ - w) τ₂ = 0 := by
    change modularLambdaH τ₂ - w = 0
    rw [hlam_τ₂, sub_self]
  have hτ₁_mem : τ₁ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨hτ₁_re_lo.le, hτ₁_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hτ₁_im_lo.le, hτ₁_im_hi.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₁_outside.le
  have hτ₂_mem : τ₂ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨hτ₂_re_lo.le, hτ₂_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hτ₂_im_lo.le, hτ₂_im_hi.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₂_outside.le
  -- (4) Two distinct zeros force the divisor sum to be at least 2.
  have key := Complex.two_le_divisor_sum_toNat_of_two_zeros_on_rectMinusUpperHalfDisk
    (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
    (by norm_num) hR₀_pos
    (by rw [he_re]; linarith)
    (by rw [he_re]; linarith)
    (by rw [he_im]; exact h_δR_lt_Y)
    (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos)
    (by
      rw [he_im]
      intro h0
      have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
      rw [Complex.ofReal_zero] at h0'
      exact hg_left δ (Set.mem_Icc.mpr ⟨le_refl δ, hδY.le⟩) h0')
    hτ_ne hτ₁_mem hτ₁_zero hτ₂_mem hτ₂_zero
  rw [he_im] at key
  omega

/-- **Existence and uniqueness of `λ`-preimage in `F^o`.** For each
`w` with `Im w > 0`, there is a unique `τ ∈ F^o` with `λ(τ) = w`.

Existence: directly from `modularLambdaH_image_F_supset_upperHalf`
(the surjectivity half of Step D).

Uniqueness: via `modularLambdaH_F_interior_preimage_unique` (the
degree-argument bootstrap), which transports the F_Y zero count of
`g(τ) := λ(τ) − w` along a `w`-segment avoided by the boundary image
to the deep-cusp reference value, where the fibre is a provably
unique simple point. -/
theorem modularLambdaH_existsUnique_in_F_interior_of_im_pos
    {w : ℂ} (hw : 0 < w.im) :
    ∃! τ : ℂ, τ ∈ Gamma2FundamentalDomainInterior ∧ modularLambdaH τ = w := by
  obtain ⟨τ_ex, hτ_ex_in, hτ_ex_eq⟩ :=
    modularLambdaH_image_F_supset_upperHalf hw
  refine ⟨τ_ex, ⟨hτ_ex_in, hτ_ex_eq⟩, ?_⟩
  rintro τ' ⟨hτ'_in, hτ'_eq⟩
  exact modularLambdaH_F_interior_preimage_unique hw hτ'_in hτ_ex_in hτ'_eq hτ_ex_eq

/-- **Injectivity of `λ` on the open interior `F^o`.** Combined
with the surjectivity from Step D
`modularLambdaH_image_fundamentalDomainInterior`, this yields the
biholomorphism `λ : F^o ≅ {Im w > 0}`. Direct consequence of
`modularLambdaH_existsUnique_in_F_interior_of_im_pos`: the unique
preimage of `λ τ₁` in `F^o` is both `τ₁` and `τ₂`. -/
theorem modularLambdaH_injOn_F_interior :
    Set.InjOn modularLambdaH Gamma2FundamentalDomainInterior := by
  intro τ₁ h₁ τ₂ h₂ h_eq
  have hw : 0 < (modularLambdaH τ₁).im := modularLambdaH_F_im_pos τ₁ h₁
  obtain ⟨τ, _, hτ_unique⟩ :=
    modularLambdaH_existsUnique_in_F_interior_of_im_pos hw
  have h_τ₁ : τ₁ = τ := hτ_unique τ₁ ⟨h₁, rfl⟩
  have h_τ₂ : τ₂ = τ := hτ_unique τ₂ ⟨h₂, h_eq.symm⟩
  rw [h_τ₁, h_τ₂]

/-- **Injectivity of `λ` on the boundary `∂F`.** For two boundary
points `τ₁, τ₂ ∈ F \ F^o` with `λ(τ₁) = λ(τ₂)`, we have `τ₁ = τ₂`.
The proof case-splits on which of the three boundary arcs each `τᵢ`
lies on (left edge `Re τ = 0`, right edge `Re τ = 1`, upper
semicircle `|2τ − 1| = 1`). Same arc ⟹ same point by strict
monotonicity (left edge: existing `modularLambdaH_iy_strictAntitone`;
right edge: derivable from `modularLambdaH_T_smul` + left-edge
antitone, with `λ(1 + iy) = λ(iy) / (λ(iy) − 1)` after the Jacobi
identity simplification; semicircle: derivable from
`modularLambdaH_add_S_smul_eq_one` + left-edge antitone via
`−1/τ = −1 + i tan(θ/2)`). Different arcs ⟹ disjoint images in
`(0, 1)`, `(−∞, 0)`, `(1, +∞)` contradict `λ`-equality. -/
theorem modularLambdaH_injOn_F_boundary
    {τ₁ τ₂ : ℂ}
    (h₁ : τ₁ ∈ Gamma2FundamentalDomain)
    (h₁_not_int : τ₁ ∉ Gamma2FundamentalDomainInterior)
    (h₂ : τ₂ ∈ Gamma2FundamentalDomain)
    (h₂_not_int : τ₂ ∉ Gamma2FundamentalDomainInterior)
    (h_eq : modularLambdaH τ₁ = modularLambdaH τ₂) :
    τ₁ = τ₂ := by
  sorry

/-- **Injectivity of `λ` on the closed half-fundamental domain `F`.**
Case split on `F^o` vs `∂F` for each of `τ₁`, `τ₂`:

* **Both `F^o`**: `modularLambdaH_injOn_F_interior`.
* **Both `∂F`**: `modularLambdaH_injOn_F_boundary`.
* **Mixed (one `F^o`, one `∂F`)**: `Im λ > 0` on `F^o` (Step A,
  `modularLambdaH_F_im_pos`) versus `Im λ = 0` on `∂F` (from one of
  the three boundary real-value lemmas
  `modularLambdaH_pure_imag_real` / `_one_add_imag_real` /
  `_semicircle_real`) — contradicts `λ`-equality. -/
theorem modularLambdaH_injOn_F_closed :
    Set.InjOn modularLambdaH Gamma2FundamentalDomain := by
  intro τ₁ h₁ τ₂ h₂ h_eq
  obtain ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ := h₁
  obtain ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ := h₂
  -- Helper: `Im(λ τ) = 0` for `τ ∈ ∂F`.
  have h_im_zero_on_boundary : ∀ {τ : ℂ}, τ ∈ Gamma2FundamentalDomain →
      τ ∉ Gamma2FundamentalDomainInterior → (modularLambdaH τ).im = 0 := by
    intro τ hτ_F hτ_not_int
    obtain ⟨hτ_im, hτ_re_nn, hτ_re_le, hτ_semi⟩ := hτ_F
    by_cases h_re_zero : τ.re = 0
    · have h_τ_eq : τ = Complex.I * τ.im := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h_τ_eq]; exact modularLambdaH_pure_imag_real hτ_im
    · by_cases h_re_one : τ.re = 1
      · have h_τ_eq : τ = 1 + Complex.I * τ.im := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
        rw [h_τ_eq]; exact modularLambdaH_one_add_imag_real hτ_im
      · by_cases h_semi_eq : ‖2 * τ - 1‖ = 1
        · exact modularLambdaH_semicircle_real hτ_im h_semi_eq
        · -- All three boundary inequalities strict ⟹ τ ∈ F^o, contradicts.
          exfalso
          apply hτ_not_int
          refine ⟨hτ_im, ?_, ?_, ?_⟩
          · rcases lt_or_eq_of_le hτ_re_nn with h | h
            · exact h
            · exact absurd h.symm h_re_zero
          · rcases lt_or_eq_of_le hτ_re_le with h | h
            · exact h
            · exact absurd h h_re_one
          · rcases lt_or_eq_of_le hτ_semi with h | h
            · exact h
            · exact absurd h.symm h_semi_eq
  by_cases h₁_int : τ₁ ∈ Gamma2FundamentalDomainInterior
  · by_cases h₂_int : τ₂ ∈ Gamma2FundamentalDomainInterior
    · -- Both interior.
      exact modularLambdaH_injOn_F_interior h₁_int h₂_int h_eq
    · -- τ₁ interior, τ₂ boundary: contradicts via Im λ.
      exfalso
      have h_im_1 : 0 < (modularLambdaH τ₁).im := modularLambdaH_F_im_pos _ h₁_int
      have h_im_2 : (modularLambdaH τ₂).im = 0 :=
        h_im_zero_on_boundary ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ h₂_int
      rw [h_eq] at h_im_1
      linarith
  · by_cases h₂_int : τ₂ ∈ Gamma2FundamentalDomainInterior
    · -- τ₁ boundary, τ₂ interior: contradicts via Im λ.
      exfalso
      have h_im_2 : 0 < (modularLambdaH τ₂).im := modularLambdaH_F_im_pos _ h₂_int
      have h_im_1 : (modularLambdaH τ₁).im = 0 :=
        h_im_zero_on_boundary ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ h₁_int
      rw [← h_eq] at h_im_2
      linarith
    · -- Both boundary.
      exact modularLambdaH_injOn_F_boundary
        ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ h₁_int
        ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ h₂_int h_eq

/-- **Injectivity of `λ` on `F` modulo `Γ(2)`.** For
`τ₁, τ₂ ∈ F ⊂ ℍ` with `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Direct consequence of `modularLambdaH_injOn_F_closed`:
`λ` injective on `F` gives `τ₁ = τ₂` in `ℂ`, hence `τ₁ = τ₂` in `ℍ`
(by `UpperHalfPlane.ext`), and `γ = 1 ∈ Γ(2)` does the job. -/
theorem modularLambdaH_injOn_F_mod_gamma2
    {τ₁ τ₂ : UpperHalfPlane}
    (h₁ : (τ₁ : ℂ) ∈ Gamma2FundamentalDomain)
    (h₂ : (τ₂ : ℂ) ∈ Gamma2FundamentalDomain)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have h_eq_c : (τ₁ : ℂ) = (τ₂ : ℂ) :=
    modularLambdaH_injOn_F_closed h₁ h₂ h_eq
  have h_eq_h : τ₁ = τ₂ := UpperHalfPlane.ext h_eq_c
  refine ⟨1, (CongruenceSubgroup.Gamma 2).one_mem, ?_⟩
  rw [h_eq_h]; exact one_smul _ _

/-! ## Pillar-4 sub-lemmas (orbit identification, three branches) -/

/-- **Pillar-4 upper branch.** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) > 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Reduce both `τ₁`, `τ₂` to `F` via
`gamma2_orbit_meets_F_when_im_lambda_pos`, apply
`modularLambdaH_injOn_F_mod_gamma2`, transport via the
`Γ(2)`-action. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_pos : 0 < (modularLambdaH (τ₁ : ℂ)).im)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have h_im_pos_2 : 0 < (modularLambdaH (τ₂ : ℂ)).im := by rw [← h_eq]; exact h_im_pos
  obtain ⟨γ₁, hγ₁_in, hγ₁τ₁_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ₁ h_im_pos
  obtain ⟨γ₂, hγ₂_in, hγ₂τ₂_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ₂ h_im_pos_2
  have h_eq_γ : modularLambdaH ((γ₁ • τ₁ : UpperHalfPlane) : ℂ)
      = modularLambdaH ((γ₂ • τ₂ : UpperHalfPlane) : ℂ) := by
    rw [modularLambdaH_gamma2_invariant γ₁ hγ₁_in τ₁,
      modularLambdaH_gamma2_invariant γ₂ hγ₂_in τ₂]
    exact h_eq
  obtain ⟨γ, hγ_in, hγ_eq⟩ :=
    modularLambdaH_injOn_F_mod_gamma2 hγ₁τ₁_F hγ₂τ₂_F h_eq_γ
  refine ⟨γ₂⁻¹ * γ * γ₁, ?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma 2).mul_mem
      ((CongruenceSubgroup.Gamma 2).mul_mem
        ((CongruenceSubgroup.Gamma 2).inv_mem hγ₂_in) hγ_in) hγ₁_in
  · rw [mul_smul, mul_smul, hγ_eq, ← mul_smul, inv_mul_cancel, one_smul]

/-! ## Analytic non-injectivity helper -/

set_option maxHeartbeats 400000 in
-- Composes the multiplicity factorization with an analytic n-th root
-- (`Complex.log` + `Complex.exp`) and the inverse function theorem; the
-- combined elaboration pressure exceeds the default heartbeat limit.
/-- **Analytic local openness with multiplicity.** If `f : ℂ → ℂ`
is analytic at `z₀`, not eventually constant near `z₀`, and
`deriv f z₀ = 0`, then in any neighbourhood `U` of `z₀` and for any
value `w` sufficiently close (but unequal) to `f z₀`, there exist
two distinct points `z₁, z₂ ∈ U` with `f z₁ = f z₂ = w`. This is
the classical "open mapping with multiplicity ≥ 2" statement: the
factorization `f(z) - f(z₀) = (z - z₀)^n · g(z)` with `n ≥ 2`,
`g(z₀) ≠ 0`, combined with the existence of an analytic `n`-th root
of `g` near `z₀` (via `Complex.exp ∘ ((1/n) * Complex.log ∘ h)`),
yields `n` distinct preimages for each `w` in a small punctured
neighbourhood of `f(z₀)`. -/
theorem analyticAt_localOpen_with_multiplicity
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀)
    (h_nc : ¬ ∀ᶠ z in nhds z₀, f z = f z₀)
    (h_dz : deriv f z₀ = 0)
    (U : Set ℂ) (hU : U ∈ nhds z₀) :
    ∃ V ∈ nhds (f z₀), ∀ w ∈ V, w ≠ f z₀ →
      ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ ∧ f z₁ = w ∧ f z₂ = w := by
  -- Abbreviate f₀(z) := f(z) - f(z₀). Analytic at z₀ with f₀(z₀) = 0.
  set f₀ : ℂ → ℂ := fun z => f z - f z₀ with hf₀_def
  have hf₀_at : AnalyticAt ℂ f₀ z₀ := hf.sub analyticAt_const
  -- Order of f₀ is not ⊤ (else f₀ ≡ 0 near z₀, i.e. f eventually constant).
  have h_order_ne_top : analyticOrderAt f₀ z₀ ≠ ⊤ := by
    intro h_top
    rw [analyticOrderAt_eq_top] at h_top
    apply h_nc
    filter_upwards [h_top] with z hz
    exact sub_eq_zero.mp hz
  -- Use analyticOrderAt_deriv_add_one to obtain n ≥ 2.
  have h_order_chain :
      analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f₀ z₀ := by
    have h := hf.analyticOrderAt_deriv_add_one
    -- h : order(deriv f) + 1 = order (fun x_1 => f x_1 - f z₀) = order f₀.
    exact h
  -- deriv f is analytic at z₀ (from f analytic at z₀).
  have h_deriv_at : AnalyticAt ℂ (deriv f) z₀ := hf.deriv
  -- (deriv f)(z₀) = 0, and deriv f is analytic, so analyticOrderAt (deriv f) z₀ ≥ 1.
  -- Specifically: if order = 0, then (deriv f)(z₀) ≠ 0 by definition.
  have h_deriv_order_ge_one : 1 ≤ analyticOrderAt (deriv f) z₀ := by
    rw [ENat.one_le_iff_ne_zero]
    intro h_eq
    rw [h_deriv_at.analyticOrderAt_eq_zero] at h_eq
    exact h_eq h_dz
  -- Hence order(f₀) ≥ 2.
  have h_order_f₀_ge_two : 2 ≤ analyticOrderAt f₀ z₀ := by
    rw [← h_order_chain]
    calc (2 : ℕ∞) = 1 + 1 := by rfl
      _ ≤ analyticOrderAt (deriv f) z₀ + 1 := by
        gcongr
  -- Convert order to natural number n.
  obtain ⟨n, hn_coe⟩ := ENat.ne_top_iff_exists.mp h_order_ne_top
  have hn_eq : analyticOrderAt f₀ z₀ = (n : ℕ∞) := hn_coe.symm
  have hn_ge_two : 2 ≤ n := by
    have : ((2 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by rw [← hn_eq]; exact_mod_cast h_order_f₀_ge_two
    exact_mod_cast this
  have hn_pos : 0 < n := by linarith
  have hn_ne_zero : n ≠ 0 := by linarith
  -- Get the factorization.
  obtain ⟨g, hg_at, hg_ne, hg_eq⟩ :=
    (hf₀_at.analyticOrderAt_eq_natCast).mp hn_eq
  -- hg_eq : ∀ᶠ z in nhds z₀, f₀ z = (z - z₀) ^ n • g z
  -- Define c := g z₀, and h(z) := g(z) / c.
  set c : ℂ := g z₀ with hc_def
  have hc_ne : c ≠ 0 := hg_ne
  set h : ℂ → ℂ := fun z => g z / c with hh_def
  have hh_at : AnalyticAt ℂ h z₀ := (hg_at.div_const : AnalyticAt ℂ (fun z => g z / c) z₀)
  have hh_z₀_one : h z₀ = 1 := by
    change g z₀ / c = 1
    exact div_self hc_ne
  have hh_in_slit : h z₀ ∈ Complex.slitPlane := by
    rw [hh_z₀_one]; exact Complex.one_mem_slitPlane
  -- Eventually h(z) ∈ slitPlane (since slitPlane is open + h continuous).
  have h_h_slit_evt : ∀ᶠ z in nhds z₀, h z ∈ Complex.slitPlane :=
    hh_at.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hh_in_slit)
  -- log analytic at h(z₀) = 1.
  have h_log_at : AnalyticAt ℂ Complex.log (h z₀) := by
    apply DifferentiableOn.analyticAt _ (Complex.isOpen_slitPlane.mem_nhds hh_in_slit)
    intro z hz
    exact (Complex.differentiableAt_log hz).differentiableWithinAt
  -- log ∘ h analytic at z₀.
  have h_log_h_at : AnalyticAt ℂ (Complex.log ∘ h) z₀ := h_log_at.comp hh_at
  -- Define ρ(z) := exp ((1/n) * log(h z)).
  set ρ : ℂ → ℂ := fun z => Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z)) with hρ_def
  -- ρ analytic at z₀.
  have hρ_at : AnalyticAt ℂ ρ z₀ := by
    have h_mul : AnalyticAt ℂ (fun z => (n : ℂ)⁻¹ * Complex.log (h z)) z₀ :=
      (analyticAt_const).mul h_log_h_at
    exact h_mul.cexp
  -- ρ(z₀) = 1.
  have hρ_z₀ : ρ z₀ = 1 := by
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z₀)) = 1
    rw [hh_z₀_one, Complex.log_one, mul_zero, Complex.exp_zero]
  -- Eventually ρ(z)^n = h(z).
  have h_nC_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn_ne_zero
  have h_ρ_pow_eq : ∀ᶠ z in nhds z₀, ρ z ^ n = h z := by
    filter_upwards [h_h_slit_evt] with z hz_slit
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z)) ^ n = h z
    rw [← Complex.exp_nat_mul]
    have h_h_ne : h z ≠ 0 := Complex.slitPlane_ne_zero hz_slit
    have h_simp : (n : ℂ) * ((n : ℂ)⁻¹ * Complex.log (h z)) = Complex.log (h z) := by
      field_simp
    rw [h_simp]
    exact Complex.exp_log h_h_ne
  -- Define φ(z) := (z - z₀) · ρ(z).
  set φ : ℂ → ℂ := fun z => (z - z₀) * ρ z with hφ_def
  have hφ_at : AnalyticAt ℂ φ z₀ :=
    (analyticAt_id.sub analyticAt_const).mul hρ_at
  have hφ_z₀ : φ z₀ = 0 := by change (z₀ - z₀) * _ = 0; ring
  -- HasDerivAt φ 1 z₀.
  have hφ_hasDeriv : HasDerivAt φ 1 z₀ := by
    have h_a : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := by
      simpa using (hasDerivAt_id z₀).sub_const z₀
    have h_b : HasDerivAt ρ (deriv ρ z₀) z₀ := hρ_at.differentiableAt.hasDerivAt
    have h_mul := h_a.mul h_b
    have h_simpl : (1 : ℂ) * ρ z₀ + (z₀ - z₀) * deriv ρ z₀ = 1 := by
      rw [hρ_z₀]; ring
    rw [← h_simpl]
    exact h_mul
  have hφ_deriv_eq : deriv φ z₀ = 1 := hφ_hasDeriv.deriv
  -- HasStrictDerivAt φ 1 z₀.
  have hφ_strict : HasStrictDerivAt φ 1 z₀ := by
    have := hφ_at.hasStrictDerivAt
    rw [hφ_deriv_eq] at this
    exact this
  -- Local inverse ψ.
  set ψ : ℂ → ℂ := hφ_strict.localInverse φ 1 z₀ one_ne_zero with hψ_def
  -- ψ(0) = z₀ via eventually_left_inverse at z₀.
  have hψ_0 : ψ 0 = z₀ := by
    have h_ev := hφ_strict.eventually_left_inverse one_ne_zero
    have h_at_z₀ : ψ (φ z₀) = z₀ := h_ev.self_of_nhds
    rwa [hφ_z₀] at h_at_z₀
  -- ψ continuous at 0 via HasStrictFDerivAt.localInverse_continuousAt.
  have hψ_cont : ContinuousAt ψ 0 := by
    have h_cont_at : ContinuousAt ψ (φ z₀) :=
      (hφ_strict.hasStrictFDerivAt_equiv one_ne_zero).localInverse_continuousAt
    rwa [hφ_z₀] at h_cont_at
  -- Eventually φ(ψ y) = y near 0 (right inverse).
  have h_right_inv : ∀ᶠ y in nhds 0, φ (ψ y) = y := by
    have h_ev := hφ_strict.eventually_right_inverse one_ne_zero
    rwa [hφ_z₀] at h_ev
  -- Eventually f(z) = f(z₀) + c · φ(z)^n.
  have h_factor_eq : ∀ᶠ z in nhds z₀, f z = f z₀ + c * φ z ^ n := by
    filter_upwards [hg_eq, h_ρ_pow_eq] with z h_fact h_pow
    -- h_fact : f z - f z₀ = (z - z₀)^n • g z
    -- h_pow : ρ z ^ n = h z = g z / c
    change f z = f z₀ + c * ((z - z₀) * ρ z) ^ n
    have h_sub : f z - f z₀ = (z - z₀)^n • g z := h_fact
    have h_smul : (z - z₀)^n • g z = (z - z₀)^n * g z := by rw [smul_eq_mul]
    rw [h_smul] at h_sub
    have h_g_eq : g z = c * h z := by
      change g z = c * (g z / c)
      field_simp
    rw [h_g_eq] at h_sub
    have h_pow_expand : ((z - z₀) * ρ z) ^ n = (z - z₀)^n * ρ z ^ n := by
      rw [mul_pow]
    rw [h_pow_expand, h_pow]
    linear_combination h_sub
  -- Collect all eventually-conditions into a single open ball around z₀:
  -- ∃ ε > 0, ∀ z ∈ B(z₀, ε), ψ z ∈ U ∧ f(ψ z + extra) etc.
  -- Use that ψ(0) = z₀ ∈ U (since U ∈ nhds z₀).
  -- Build the witness V around f(z₀) such that w ∈ V → ζ = (w - f(z₀))/c is small enough
  -- that both ζ_0 = exp((1/n) log ζ) and ζ_1 = ζ_0 * exp(2πi/n) are in nhds 0 with all
  -- needed properties.
  -- Combine eventually facts: ψ(0) = z₀ ∈ U, ψ continuous, etc.
  -- Get a single radius δ that handles everything.
  have h_all_nhd_0 : ∀ᶠ y in nhds 0, φ (ψ y) = y ∧ ψ y ∈ U ∧ f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
    have h_ψU : ∀ᶠ y in nhds 0, ψ y ∈ U := by
      have h_ψU_filter : Filter.Tendsto ψ (nhds 0) (nhds (ψ 0)) := hψ_cont
      rw [hψ_0] at h_ψU_filter
      exact h_ψU_filter hU
    have h_fac_ψ : ∀ᶠ y in nhds 0, f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
      have h_ψ_to_z₀ : Filter.Tendsto ψ (nhds 0) (nhds z₀) := by
        rw [← hψ_0]; exact hψ_cont
      exact h_ψ_to_z₀ h_factor_eq
    filter_upwards [h_right_inv, h_ψU, h_fac_ψ] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- Extract ε > 0 such that B(0, ε) is in the eventually set.
  rcases Metric.eventually_nhds_iff.mp h_all_nhd_0 with ⟨δ, hδ_pos, hδ_prop⟩
  -- Define V = B(f z₀, |c| · δ^n).
  set η : ℝ := ‖c‖ * δ^n with hη_def
  have hη_pos : 0 < η := by
    have hδ_pow_pos : 0 < δ^n := pow_pos hδ_pos n
    have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    positivity
  refine ⟨Metric.ball (f z₀) η, Metric.ball_mem_nhds _ hη_pos, ?_⟩
  intro w hw_in_V hw_ne
  -- w ∈ B(f z₀, η), w ≠ f z₀.
  -- Define ζ = (w - f z₀) / c.
  set ζ : ℂ := (w - f z₀) / c with hζ_def
  have hζ_ne : ζ ≠ 0 := by
    intro hζ_zero
    apply hw_ne
    have h_sub_zero : w - f z₀ = 0 := by
      have h1 : (w - f z₀) / c = 0 := hζ_zero
      have h_mul : (w - f z₀) / c * c = 0 * c := by rw [h1]
      rw [div_mul_cancel₀ _ hc_ne, zero_mul] at h_mul
      exact h_mul
    linear_combination h_sub_zero
  -- Define ζ_0 = exp((1/n) * log ζ), ζ_1 = ζ_0 * exp(2πi/n).
  set ζ_0 : ℂ := Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ) with hζ_0_def
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hω_def
  set ζ_1 : ℂ := ζ_0 * ω with hζ_1_def
  -- ζ_0 ^ n = ζ.
  have hζ_0_pow : ζ_0 ^ n = ζ := by
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ) ^ n = ζ
    rw [← Complex.exp_nat_mul]
    have h_simp : (n : ℂ) * ((n : ℂ)⁻¹ * Complex.log ζ) = Complex.log ζ := by field_simp
    rw [h_simp]
    exact Complex.exp_log hζ_ne
  -- ω ^ n = 1.
  have hω_pow : ω ^ n = 1 := by
    change Complex.exp (2 * Real.pi * Complex.I / n) ^ n = 1
    rw [← Complex.exp_nat_mul]
    have h_simp : (n : ℂ) * (2 * Real.pi * Complex.I / n) = 2 * Real.pi * Complex.I := by
      field_simp
    rw [h_simp]
    exact Complex.exp_two_pi_mul_I
  -- ζ_1 ^ n = ζ.
  have hζ_1_pow : ζ_1 ^ n = ζ := by
    change (ζ_0 * ω) ^ n = ζ
    rw [mul_pow, hω_pow, mul_one, hζ_0_pow]
  -- ω ≠ 1 (since n ≥ 2).
  have hω_ne_one : ω ≠ 1 := by
    intro hω_one
    -- ω = 1 means exp(2πi/n) = 1, so 2πi/n = 2πi·k for some k ∈ ℤ.
    -- This means 1/n = k, so n | 1, so n = 1, contradicting n ≥ 2.
    have h_log_eq : Complex.log ω = 0 := by rw [hω_one]; exact Complex.log_one
    -- log(exp(z)) = z when -π < z.im ≤ π.
    have h_2pi_div_n_im : ((2 * Real.pi * Complex.I / n : ℂ)).im = 2 * Real.pi / n := by
      have h_n_re : (n : ℂ).re = n := by simp
      have h_n_im : (n : ℂ).im = 0 := by simp
      have h_n_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      simp [Complex.div_im, Complex.mul_im, Complex.mul_re,
        Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im, h_n_im]
      field_simp
    have h_2pi_div_n_lt : (2 * Real.pi * Complex.I / n : ℂ).im ≤ Real.pi := by
      rw [h_2pi_div_n_im]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn_ge_two
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have : 2 * Real.pi / n ≤ Real.pi := by
        rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (n : ℝ))]
        nlinarith
      exact this
    have h_2pi_div_n_gt : -Real.pi < (2 * Real.pi * Complex.I / n : ℂ).im := by
      rw [h_2pi_div_n_im]
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      have : 0 < 2 * Real.pi / n := by positivity
      linarith
    have h_log_omega : Complex.log ω = 2 * Real.pi * Complex.I / n := by
      change Complex.log (Complex.exp (2 * Real.pi * Complex.I / n)) = 2 * Real.pi * Complex.I / n
      exact Complex.log_exp h_2pi_div_n_gt h_2pi_div_n_lt
    rw [h_log_omega] at h_log_eq
    -- h_log_eq : 2πi/n = 0, but 2πi/n ≠ 0.
    have h_im : (2 * Real.pi * Complex.I / n : ℂ).im = 0 := by rw [h_log_eq]; simp
    rw [h_2pi_div_n_im] at h_im
    have h_pos : 0 < 2 * Real.pi / n := by
      have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      have : 0 < Real.pi := Real.pi_pos
      positivity
    linarith
  -- ζ_1 ≠ ζ_0.
  have hζ_ne_distinct : ζ_0 ≠ ζ_1 := by
    intro h_eq
    have h_ζ₀_ne : ζ_0 ≠ 0 := by
      intro h_ζ₀_zero
      have : ζ_0 ^ n = 0 := by rw [h_ζ₀_zero]; exact zero_pow hn_ne_zero
      rw [hζ_0_pow] at this
      exact hζ_ne this
    have : ω = 1 := by
      have h_eq' : ζ_0 * ω = ζ_0 * 1 := by rw [mul_one]; exact h_eq.symm
      exact mul_left_cancel₀ h_ζ₀_ne h_eq'
    exact hω_ne_one this
  -- |ζ| < δ^n.
  have h_ζ_norm : ‖ζ‖ < δ^n := by
    change ‖(w - f z₀) / c‖ < δ^n
    rw [norm_div]
    rw [Metric.mem_ball, dist_eq_norm] at hw_in_V
    have h_num_lt : ‖w - f z₀‖ < η := hw_in_V
    have h_c_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    rw [div_lt_iff₀ h_c_norm_pos]
    have h_η_def : η = ‖c‖ * δ^n := hη_def
    nlinarith
  -- ‖ζ_0‖ = |ζ|^(1/n) < δ.
  have h_ζ₀_norm_eq : ‖ζ_0‖ = ‖ζ‖^((n : ℝ)⁻¹) := by
    change ‖Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ)‖ = ‖ζ‖^((n : ℝ)⁻¹)
    rw [Complex.norm_exp]
    -- Re((n : ℂ)⁻¹ * log ζ) = (1/n) * Re(log ζ) = (1/n) * log ‖ζ‖
    have h_n_re : ((n : ℂ)⁻¹).re = (n : ℝ)⁻¹ := by
      have : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [this, ← Complex.ofReal_inv]
      simp
    have h_n_im : ((n : ℂ)⁻¹).im = 0 := by
      have : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [this, ← Complex.ofReal_inv]
      simp
    rw [Complex.mul_re, h_n_re, h_n_im, zero_mul, sub_zero]
    rw [Complex.log_re]
    have h_norm_pos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ_ne
    rw [show (n : ℝ)⁻¹ * Real.log ‖ζ‖ = Real.log ‖ζ‖ * (n : ℝ)⁻¹ from by ring]
    exact (Real.rpow_def_of_pos h_norm_pos _).symm
  have h_ζ₀_norm_lt : ‖ζ_0‖ < δ := by
    rw [h_ζ₀_norm_eq]
    have h_pos_zeta : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ_ne
    have h_n_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h_n_real_ne : (n : ℝ) ≠ 0 := ne_of_gt h_n_real_pos
    have h_n_inv_pos : 0 < ((n : ℝ))⁻¹ := inv_pos.mpr h_n_real_pos
    -- We need ‖ζ‖^(1/n) < δ.
    -- We have ‖ζ‖ < δ^n (= h_ζ_norm).
    -- Apply rpow with positive 1/n: (‖ζ‖)^(1/n) < (δ^n)^(1/n) = δ.
    have h_δ_pos : 0 < δ := hδ_pos
    have h_step1 : ‖ζ‖ ^ ((n : ℝ)⁻¹) < (δ^n) ^ ((n : ℝ)⁻¹) := by
      exact Real.rpow_lt_rpow h_pos_zeta.le h_ζ_norm h_n_inv_pos
    have h_step2 : (δ^n) ^ ((n : ℝ)⁻¹) = δ := by
      rw [show δ^n = δ ^ ((n : ℕ) : ℝ) from (Real.rpow_natCast δ n).symm]
      rw [← Real.rpow_mul h_δ_pos.le]
      rw [mul_inv_cancel₀ h_n_real_ne]
      exact Real.rpow_one _
    linarith
  -- ‖ζ_1‖ = ‖ζ_0‖ < δ.
  have h_ζ₁_norm_lt : ‖ζ_1‖ < δ := by
    change ‖ζ_0 * ω‖ < δ
    rw [norm_mul]
    have h_omega_norm : ‖ω‖ = 1 := by
      change ‖Complex.exp (2 * Real.pi * Complex.I / n)‖ = 1
      rw [Complex.norm_exp]
      -- Re(2πi/n) = 0
      have h_re_zero : ((2 * Real.pi * Complex.I / n : ℂ)).re = 0 := by
        simp [Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [h_re_zero, Real.exp_zero]
    rw [h_omega_norm, mul_one]
    exact h_ζ₀_norm_lt
  -- ζ_0, ζ_1 ∈ B(0, δ).
  have h_ζ₀_in_ball : ζ_0 ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact h_ζ₀_norm_lt
  have h_ζ₁_in_ball : ζ_1 ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact h_ζ₁_norm_lt
  -- Convert to membership in nhds 0 (for hδ_prop).
  have hδ_at_ball : ∀ y ∈ Metric.ball (0 : ℂ) δ,
      φ (ψ y) = y ∧ ψ y ∈ U ∧ f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
    intro y hy
    have : dist y 0 < δ := Metric.mem_ball.mp hy
    exact hδ_prop this
  obtain ⟨h_φψ_ζ₀, hψ_ζ₀_U, h_f_ψ_ζ₀⟩ := hδ_at_ball ζ_0 h_ζ₀_in_ball
  obtain ⟨h_φψ_ζ₁, hψ_ζ₁_U, h_f_ψ_ζ₁⟩ := hδ_at_ball ζ_1 h_ζ₁_in_ball
  -- f(ψ ζ_i) = w.
  have h_f_ψ_ζ₀_eq_w : f (ψ ζ_0) = w := by
    rw [h_f_ψ_ζ₀, h_φψ_ζ₀, hζ_0_pow]
    change f z₀ + c * ((w - f z₀) / c) = w
    rw [mul_div_cancel₀ _ hc_ne]; ring
  have h_f_ψ_ζ₁_eq_w : f (ψ ζ_1) = w := by
    rw [h_f_ψ_ζ₁, h_φψ_ζ₁, hζ_1_pow]
    change f z₀ + c * ((w - f z₀) / c) = w
    rw [mul_div_cancel₀ _ hc_ne]; ring
  -- ψ ζ_0 ≠ ψ ζ_1.
  have hψ_ne : ψ ζ_0 ≠ ψ ζ_1 := by
    intro h_eq
    -- ψ injective on its image (since ψ is local inverse).
    have h_eq' : φ (ψ ζ_0) = φ (ψ ζ_1) := by rw [h_eq]
    rw [h_φψ_ζ₀, h_φψ_ζ₁] at h_eq'
    exact hζ_ne_distinct h_eq'
  -- Wrap up.
  exact ⟨ψ ζ_0, hψ_ζ₀_U, ψ ζ_1, hψ_ζ₁_U, hψ_ne, h_f_ψ_ζ₀_eq_w, h_f_ψ_ζ₁_eq_w⟩

/-- **Pillar-3 boundary `= 0` branch.** For `τ ∈ ℍ` with
`Im(λ τ) = 0`, `deriv λ τ ≠ 0`. Suppose `deriv λ τ = 0` for
contradiction. By `analyticAt_localOpen_with_multiplicity`, for
each `k` there are distinct `z₁ᵏ, z₂ᵏ ∈ B(τ, 1/(k+1)) ⊂ ℍ` with
`λ(z₁ᵏ) = λ(z₂ᵏ)` and `Im λ(z₁ᵏ) > 0` (the witness `λ τ + (r/2)·i`
inside the helper neighbourhood `V`). By Pillar-4 upper branch,
`z₂ᵏ = γₖ • z₁ᵏ` for some `γₖ ∈ Γ(2)`. Proper discontinuity
restricts `γₖ` to a finite set on a compact ball around `τ`;
extract a constant subsequence `γₖ = γ`. Passing to the limit,
`γ • τ = τ`, so by Pillar 1 (`gamma_two_fixed_point_implies_pm_one`)
`γ ∈ {I, -I}`. But `±I` acts trivially on `ℍ`, so along the
subsequence `z₁ᵏ = z₂ᵏ`, contradicting distinctness. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_zero
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im = 0) :
    deriv modularLambdaH τ ≠ 0 := by
  intro h_dz
  -- Setup: H is the open upper half-plane in ℂ.
  set H : Set ℂ := {z | 0 < z.im} with hH_def
  have hH_open : IsOpen H := by
    have : H = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp [hH_def]
    rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH H :=
    modularLambdaH_differentiableOn.analyticOnNhd hH_open
  have h_lam_at : AnalyticAt ℂ modularLambdaH τ := h_lam_an τ hτ
  have h_H_preconn : IsPreconnected H := by
    apply Convex.isPreconnected
    intro w₁ hw₁ w₂ hw₂ s t hs ht hst
    change 0 < (s • w₁ + t • w₂).im
    rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
    rcases lt_or_eq_of_le hs with hs_pos | hs_zero
    · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
      have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
      linarith
    · have ht_pos : 0 < t := by linarith
      have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
      have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
      linarith
  -- λ is not eventually constant at τ (identity theorem + global non-constancy).
  have h_lam_not_const : ¬ ∀ᶠ z in nhds τ, modularLambdaH z = modularLambdaH τ := by
    intro h_eq
    have h_const_an : AnalyticOnNhd ℂ (fun _ : ℂ => modularLambdaH τ) H :=
      fun _ _ => analyticAt_const
    have h_eqOn : Set.EqOn modularLambdaH (fun _ => modularLambdaH τ) H :=
      h_lam_an.eqOn_of_preconnected_of_eventuallyEq h_const_an h_H_preconn hτ h_eq
    have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.im h; simp at this
    have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.re h; simp at this
    have h_lam_img : modularLambdaH '' H = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := modularLambdaH_image
    have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' H := h_lam_img ▸ h_1i_in
    have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' H := h_lam_img ▸ h_2i_in
    obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
    obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
    have h_a := h_eqOn hτ_a_H
    have h_b := h_eqOn hτ_b_H
    rw [hτ_a_eq] at h_a
    rw [hτ_b_eq] at h_b
    have h_eq_12 : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := h_a.trans h_b.symm
    have h_re := congrArg Complex.re h_eq_12
    simp at h_re
  -- Setup τ_h and proper-discontinuity instance.
  haveI := gamma_two_properlyDiscontinuousSMul
  set τ_h : UpperHalfPlane := ⟨τ, hτ⟩ with hτ_h_def
  -- For each k, helper produces distinct preimages with Im λ > 0.
  have h_seq : ∀ k : ℕ, ∃ z₁ z₂ : ℂ, 0 < z₁.im ∧ 0 < z₂.im ∧
      ‖z₁ - τ‖ < 1/(k+1) ∧ ‖z₂ - τ‖ < 1/(k+1) ∧
      z₁ ≠ z₂ ∧ modularLambdaH z₁ = modularLambdaH z₂ ∧
      0 < (modularLambdaH z₁).im := by
    intro k
    set ε : ℝ := 1/(k+1) with hε_def
    have hε_pos : 0 < ε := by positivity
    set U : Set ℂ := Metric.ball τ ε ∩ H with hU_def
    have hU_nhds : U ∈ nhds τ := Filter.inter_mem
      (Metric.ball_mem_nhds _ hε_pos) (hH_open.mem_nhds hτ)
    obtain ⟨V, hV_nhds, hV_prop⟩ :=
      analyticAt_localOpen_with_multiplicity h_lam_at h_lam_not_const h_dz U hU_nhds
    rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨r, hr_pos, hr_sub⟩
    set w : ℂ := modularLambdaH τ + (r/2 : ℝ) * Complex.I with hw_def
    have h_dist_w : dist w (modularLambdaH τ) = r/2 := by
      rw [hw_def, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr_pos)]
    have hw_in_V : w ∈ V := by
      apply hr_sub
      rw [Metric.mem_ball, h_dist_w]; linarith
    have hw_ne : w ≠ modularLambdaH τ := by
      intro h_eq
      have h_im_eq : w.im = (modularLambdaH τ).im := congrArg Complex.im h_eq
      rw [hw_def, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero, hlam_im] at h_im_eq
      linarith
    obtain ⟨z₁, hz₁_U, z₂, hz₂_U, hne, h_lam_z₁, h_lam_z₂⟩ := hV_prop w hw_in_V hw_ne
    obtain ⟨hz₁_ball, hz₁_im⟩ := hz₁_U
    obtain ⟨hz₂_ball, hz₂_im⟩ := hz₂_U
    refine ⟨z₁, z₂, hz₁_im, hz₂_im, ?_, ?_, hne, ?_, ?_⟩
    · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz₁_ball
    · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz₂_ball
    · rw [h_lam_z₁, h_lam_z₂]
    · rw [h_lam_z₁, hw_def]
      show 0 < (modularLambdaH τ + ↑(r/2) * Complex.I).im
      rw [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero, hlam_im, zero_add]
      exact half_pos hr_pos
  choose z₁ z₂ hz₁_im hz₂_im hd₁ hd₂ hne h_lam_eq h_im_pos using h_seq
  -- Sequences in ℍ.
  set z₁_h : ℕ → UpperHalfPlane := fun n => ⟨z₁ n, hz₁_im n⟩ with hz₁_h_def
  set z₂_h : ℕ → UpperHalfPlane := fun n => ⟨z₂ n, hz₂_im n⟩ with hz₂_h_def
  -- Pillar-4 upper for each n.
  have h_orbit : ∀ n, ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • z₁_h n = z₂_h n := by
    intro n
    exact gamma2_lambda_eq_implies_orbit_when_im_lambda_pos (h_im_pos n) (h_lam_eq n)
  choose γ hγ_in hγ_eq using h_orbit
  -- Tendsto z₁, z₂ → τ in ℂ via norm bounds.
  have h_z₁_tend_c : Filter.Tendsto z₁ Filter.atTop (nhds τ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h_nb : ‖z₁ n - τ‖ < 1/(n+1) := hd₁ n
    have h_le : (1 : ℝ)/(n+1) ≤ 1/(N+1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hn
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h_nb (le_of_lt (lt_of_le_of_lt h_le hN))
  have h_z₂_tend_c : Filter.Tendsto z₂ Filter.atTop (nhds τ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h_nb : ‖z₂ n - τ‖ < 1/(n+1) := hd₂ n
    have h_le : (1 : ℝ)/(n+1) ≤ 1/(N+1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hn
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h_nb (le_of_lt (lt_of_le_of_lt h_le hN))
  -- Bridge ℂ-Tendsto to ℍ-Tendsto via the open embedding.
  have h_ind : Topology.IsInducing (UpperHalfPlane.coe) :=
    UpperHalfPlane.isOpenEmbedding_coe.isInducing
  have h_z₁_tend_h : Filter.Tendsto z₁_h Filter.atTop (nhds τ_h) := by
    rw [h_ind.tendsto_nhds_iff]
    change Filter.Tendsto (fun n => (z₁_h n : ℂ)) Filter.atTop (nhds (τ_h : ℂ))
    exact h_z₁_tend_c
  have h_z₂_tend_h : Filter.Tendsto z₂_h Filter.atTop (nhds τ_h) := by
    rw [h_ind.tendsto_nhds_iff]
    change Filter.Tendsto (fun n => (z₂_h n : ℂ)) Filter.atTop (nhds (τ_h : ℂ))
    exact h_z₂_tend_c
  -- Compact ball K in ℍ.
  set K : Set UpperHalfPlane := Metric.closedBall τ_h 1 with hK_def
  have hK_compact : IsCompact K := isCompact_closedBall _ _
  -- Finite γ-set via proper discontinuity.
  set S : Set (↥(CongruenceSubgroup.Gamma 2)) :=
    { g | ((fun τ => g • τ) '' K ∩ K).Nonempty } with hS_def
  have hS_finite : S.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK_compact hK_compact
  -- For n large, z_h n ∈ K (using dist < 1/2 < 1).
  rw [Metric.tendsto_atTop] at h_z₁_tend_h h_z₂_tend_h
  obtain ⟨N₁, hN₁⟩ := h_z₁_tend_h (1/2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := h_z₂_tend_h (1/2) (by norm_num)
  set N : ℕ := max N₁ N₂ with hN_def
  have h_γ_in_S : ∀ n, N ≤ n →
      (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) ∈ S := by
    intro n hn
    have h1 := hN₁ n (le_of_max_le_left hn)
    have h2 := hN₂ n (le_of_max_le_right hn)
    refine ⟨z₂_h n, ⟨z₁_h n, ?_, hγ_eq n⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr (le_trans h1.le (by norm_num))
    · exact Metric.mem_closedBall.mpr (le_trans h2.le (by norm_num))
  -- Pigeonhole: some γ in S occurs at infinitely many n ≥ N.
  have h_pigeon : ∃ γ_lim : ↥(CongruenceSubgroup.Gamma 2), γ_lim ∈ S ∧
      {n : ℕ | N ≤ n ∧
        (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim}.Infinite := by
    by_contra h_neg
    push Not at h_neg
    have h_ici_infinite : Set.Infinite (Set.Ici N) := Set.Ici_infinite N
    apply h_ici_infinite
    have h_eq : Set.Ici N =
        ⋃ γ_lim ∈ S, {n : ℕ | N ≤ n ∧
          (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim} := by
      ext n
      simp only [Set.mem_Ici, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
      constructor
      · intro hn
        refine ⟨⟨γ n, hγ_in n⟩, h_γ_in_S n hn, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩
        exact hn
    rw [h_eq]
    apply hS_finite.biUnion
    intro γ_lim hγ_lim
    exact h_neg γ_lim hγ_lim
  obtain ⟨γ_lim, _hγ_lim_in_S, hγ_inf⟩ := h_pigeon
  -- Strictly mono subseq in the fiber {γ n = γ_lim}.
  have h_seq_idx : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, φ k ∈
      {n : ℕ | N ≤ n ∧
        (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim} := by
    apply Nat.exists_strictMono_subsequence
    intro M
    obtain ⟨b, hb_in, hb_gt⟩ := hγ_inf.exists_gt M
    exact ⟨b, hb_gt, hb_in⟩
  obtain ⟨φ, hφ_mono, hφ_in⟩ := h_seq_idx
  -- Along subseq, γ_lim.val • z₁_h (φ k) = z₂_h (φ k).
  have h_subseq_eq : ∀ k, γ_lim.val • z₁_h (φ k) = z₂_h (φ k) := by
    intro k
    have h_γ_eq_lim : γ (φ k) = γ_lim.val := by
      have := (hφ_in k).2
      exact congrArg Subtype.val this
    rw [← h_γ_eq_lim]
    exact hγ_eq (φ k)
  -- Distinct along subseq.
  have h_subseq_ne : ∀ k, z₁_h (φ k) ≠ z₂_h (φ k) := by
    intro k h_eq
    have h_z_eq : z₁ (φ k) = z₂ (φ k) := by
      have : (z₁_h (φ k) : ℂ) = (z₂_h (φ k) : ℂ) := by rw [h_eq]
      exact this
    exact hne (φ k) h_z_eq
  -- Take limit: γ_lim.val • τ_h = τ_h.
  have h_cont : Continuous (fun σ : UpperHalfPlane => γ_lim.val • σ) := by
    change Continuous (fun σ : UpperHalfPlane => ((γ_lim.val : SL(2, ℝ)) • σ))
    exact continuous_const_smul _
  have h_z₁_tend_h' : Filter.Tendsto z₁_h Filter.atTop (nhds τ_h) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    exact h_z₁_tend_h δ hδ
  have h_z₂_tend_h' : Filter.Tendsto z₂_h Filter.atTop (nhds τ_h) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    exact h_z₂_tend_h δ hδ
  have h_tend_left : Filter.Tendsto (fun k => γ_lim.val • z₁_h (φ k)) Filter.atTop
      (nhds (γ_lim.val • τ_h)) :=
    (h_cont.tendsto _).comp (h_z₁_tend_h'.comp hφ_mono.tendsto_atTop)
  have h_tend_right : Filter.Tendsto (fun k => z₂_h (φ k)) Filter.atTop (nhds τ_h) :=
    h_z₂_tend_h'.comp hφ_mono.tendsto_atTop
  have h_replace : (fun k => γ_lim.val • z₁_h (φ k)) = (fun k => z₂_h (φ k)) :=
    funext h_subseq_eq
  rw [h_replace] at h_tend_left
  have h_γ_fix : γ_lim.val • τ_h = τ_h :=
    tendsto_nhds_unique h_tend_left h_tend_right
  -- Pillar 1: γ_lim ∈ {I, -I}.
  have h_pm := gamma_two_fixed_point_implies_pm_one γ_lim.val γ_lim.property τ_h h_γ_fix
  -- ±I acts trivially: γ_lim • z = z. Contradicts h_subseq_ne for k = 0.
  have h_triv : γ_lim.val • z₁_h (φ 0) = z₁_h (φ 0) := by
    rcases h_pm with h | h
    · rw [h]; simp
    · rw [h]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp
  have h_contra : z₁_h (φ 0) = z₂_h (φ 0) := by
    rw [← h_subseq_eq 0, h_triv]
  exact h_subseq_ne 0 h_contra


/-- **Non-vanishing of `λ'` on the closed half-fundamental domain
`F`.** Case split on `F^o` vs `∂F`. For interior points, suppose
`deriv λ τ = 0`; by `analyticAt_localOpen_with_multiplicity` the
helper produces two distinct preimages `z₁ ≠ z₂` of some value
`w ≠ λ τ` inside a small ball `B(τ, ε) ⊆ F^o`, contradicting
`modularLambdaH_injOn_F_interior`. For boundary points,
`Im(λ τ) = 0` (from the three boundary real-value lemmas) so
`modularLambdaH_deriv_ne_zero_when_im_lambda_zero` applies
directly. -/
theorem modularLambdaH_deriv_ne_zero_on_F
    {τ : ℂ} (hτ_F : τ ∈ Gamma2FundamentalDomain) :
    deriv modularLambdaH τ ≠ 0 := by
  obtain ⟨hτ_im, hτ_re_nn, hτ_re_le, hτ_semicircle⟩ := hτ_F
  by_cases h_interior : τ ∈ Gamma2FundamentalDomainInterior
  · -- F^o case: use H_inj_F^o + multiplicity helper.
    intro h_dz
    -- λ analytic at τ.
    have hH_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    have h_lam_at : AnalyticAt ℂ modularLambdaH τ :=
      (modularLambdaH_differentiableOn.analyticOnNhd hH_open) τ hτ_im
    -- ℍ is preconnected (convex).
    have h_H_preconn : IsPreconnected {z : ℂ | 0 < z.im} := by
      apply Convex.isPreconnected
      intro w₁ hw₁ w₂ hw₂ s t hs ht hst
      change 0 < (s • w₁ + t • w₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
        have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
        have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
        linarith
    have h_lam_an : AnalyticOnNhd ℂ modularLambdaH {z : ℂ | 0 < z.im} :=
      modularLambdaH_differentiableOn.analyticOnNhd hH_open
    have h_lam_not_const : ¬ ∀ᶠ z in nhds τ, modularLambdaH z = modularLambdaH τ := by
      intro h_eq
      have h_const_an : AnalyticOnNhd ℂ (fun _ : ℂ => modularLambdaH τ) {z : ℂ | 0 < z.im} :=
        fun _ _ => analyticAt_const
      have h_eqOn : Set.EqOn modularLambdaH (fun _ => modularLambdaH τ) {z : ℂ | 0 < z.im} :=
        h_lam_an.eqOn_of_preconnected_of_eventuallyEq h_const_an h_H_preconn hτ_im h_eq
      have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
        refine ⟨?_, ?_⟩
        · intro h; have := congrArg Complex.im h; simp at this
        · intro h; have := congrArg Complex.im h; simp at this
      have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
        refine ⟨?_, ?_⟩
        · intro h; have := congrArg Complex.im h; simp at this
        · intro h; have := congrArg Complex.re h; simp at this
      have h_lam_img : modularLambdaH '' {z : ℂ | 0 < z.im} = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } :=
        modularLambdaH_image
      have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' {z : ℂ | 0 < z.im} :=
        h_lam_img ▸ h_1i_in
      have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' {z : ℂ | 0 < z.im} :=
        h_lam_img ▸ h_2i_in
      obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
      obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
      have h_a := h_eqOn hτ_a_H
      have h_b := h_eqOn hτ_b_H
      rw [hτ_a_eq] at h_a
      rw [hτ_b_eq] at h_b
      have h_eq_12 : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := h_a.trans h_b.symm
      have h_re := congrArg Complex.re h_eq_12
      simp at h_re
    -- F^o is nhd of τ.
    have hF_open : IsOpen Gamma2FundamentalDomainInterior :=
      Gamma2FundamentalDomainInterior_isOpen
    have hF_nhds : Gamma2FundamentalDomainInterior ∈ nhds τ :=
      hF_open.mem_nhds h_interior
    -- Apply multiplicity helper.
    obtain ⟨V, hV_nhds, hV_prop⟩ :=
      analyticAt_localOpen_with_multiplicity h_lam_at h_lam_not_const h_dz
        Gamma2FundamentalDomainInterior hF_nhds
    -- Pick w ∈ V with w ≠ λ τ.
    rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨r, hr_pos, hr_sub⟩
    set w : ℂ := modularLambdaH τ + (r/2 : ℝ) with hw_def
    have h_dist_w : dist w (modularLambdaH τ) = r/2 := by
      rw [hw_def, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr_pos)]
    have hw_in_V : w ∈ V := by
      apply hr_sub
      rw [Metric.mem_ball, h_dist_w]; linarith
    have hw_ne : w ≠ modularLambdaH τ := by
      intro h_eq
      have h_re_eq : w.re = (modularLambdaH τ).re := congrArg Complex.re h_eq
      rw [hw_def, Complex.add_re, Complex.ofReal_re] at h_re_eq
      linarith
    obtain ⟨z_1, hz_1_in, z_2, hz_2_in, h_ne, h_lam_z_1, h_lam_z_2⟩ :=
      hV_prop w hw_in_V hw_ne
    -- z_1, z_2 ∈ F^o, λ(z_1) = λ(z_2). By H_inj_F^o, z_1 = z_2.
    have h_lam_eq : modularLambdaH z_1 = modularLambdaH z_2 := h_lam_z_1.trans h_lam_z_2.symm
    have h_z_eq : z_1 = z_2 :=
      modularLambdaH_injOn_F_interior hz_1_in hz_2_in h_lam_eq
    exact h_ne h_z_eq
  · -- ∂F case: τ ∈ F but not in F^o. Hence Im(λ τ) = 0 (boundary real-value).
    have h_im_lam_zero : (modularLambdaH τ).im = 0 := by
      by_cases h_re_zero : τ.re = 0
      · have h_τ_eq : τ = Complex.I * τ.im := by
          apply Complex.ext
          · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
          · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
        rw [h_τ_eq]
        exact modularLambdaH_pure_imag_real hτ_im
      · by_cases h_re_one : τ.re = 1
        · have h_τ_eq : τ = 1 + Complex.I * τ.im := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          rw [h_τ_eq]
          exact modularLambdaH_one_add_imag_real hτ_im
        · by_cases h_semicircle : ‖2 * τ - 1‖ = 1
          · exact modularLambdaH_semicircle_real hτ_im h_semicircle
          · -- All three boundary conditions strict: τ ∈ F^o, contradicting h_interior.
            exfalso
            apply h_interior
            refine ⟨hτ_im, ?_, ?_, ?_⟩
            · rcases lt_or_eq_of_le hτ_re_nn with h | h
              · exact h
              · exact absurd h.symm h_re_zero
            · rcases lt_or_eq_of_le hτ_re_le with h | h
              · exact h
              · exact absurd h h_re_one
            · rcases lt_or_eq_of_le hτ_semicircle with h | h
              · exact h
              · exact absurd h.symm h_semicircle
    exact modularLambdaH_deriv_ne_zero_when_im_lambda_zero hτ_im h_im_lam_zero

/-- **Möbius-derivative + upper branch for Pillar 3.** For
`τ ∈ ℍ` with `Im(λ τ) > 0`, `deriv λ τ ≠ 0`. Reduce `τ` to
`γ • τ ∈ F` via the half-FD property; apply
`modularLambdaH_deriv_ne_zero_on_F`; transport back along the
`Γ(2)`-orbit via the Möbius chain rule. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_pos
    {τ : ℂ} (hτ : 0 < τ.im)
    (h_im_pos : 0 < (modularLambdaH τ).im) :
    deriv modularLambdaH τ ≠ 0 := by
  set τ_h : UpperHalfPlane := ⟨τ, hτ⟩ with hτ_h_def
  have hlam_τ_h : 0 < (modularLambdaH (τ_h : ℂ)).im := h_im_pos
  obtain ⟨γ, hγ_in, hγτ_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ_h hlam_τ_h
  have h_deriv_γτ : deriv modularLambdaH ((γ • τ_h : UpperHalfPlane) : ℂ) ≠ 0 :=
    modularLambdaH_deriv_ne_zero_on_F hγτ_F
  set a : ℂ := (γ.val 0 0 : ℂ) with ha_def
  set b : ℂ := (γ.val 0 1 : ℂ) with hb_def
  set c : ℂ := (γ.val 1 0 : ℂ) with hc_def
  set d : ℂ := (γ.val 1 1 : ℂ) with hd_def
  have h_det : a * d - b * c = 1 := by
    have hγ_det := γ.2
    have : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
      have := Matrix.det_fin_two γ.val
      rw [hγ_det] at this
      linarith
    push_cast [ha_def, hb_def, hc_def, hd_def]
    exact_mod_cast this
  set Mob : ℂ → ℂ := fun z => (a * z + b) / (c * z + d) with hMob_def
  have h_smul_coe : ((γ • τ_h : UpperHalfPlane) : ℂ) = Mob τ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change ((((algebraMap ℤ ℝ) (γ.val 0 0)) : ℂ) * (τ_h : ℂ) +
        ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ)) /
        (((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) * (τ_h : ℂ) +
          ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ)) = Mob τ
    simp [hMob_def, ha_def, hb_def, hc_def, hd_def, hτ_h_def]
  have h_denom_ne : c * τ + d ≠ 0 := by
    intro h_eq
    have h_im_pos : 0 < ((γ • τ_h : UpperHalfPlane) : ℂ).im :=
      (γ • τ_h : UpperHalfPlane).2
    rw [h_smul_coe] at h_im_pos
    have h_Mob_undef : Mob τ = (a * τ + b) / 0 := by
      change (a * τ + b) / (c * τ + d) = (a * τ + b) / 0
      rw [h_eq]
    rw [h_Mob_undef] at h_im_pos
    simp at h_im_pos
  have h_Mob_deriv : HasDerivAt Mob (1 / (c * τ + d) ^ 2) τ := by
    have h_num : HasDerivAt (fun z : ℂ => a * z + b) a τ := by
      have := (hasDerivAt_id τ).const_mul a
      simpa using this.add_const b
    have h_den : HasDerivAt (fun z : ℂ => c * z + d) c τ := by
      have := (hasDerivAt_id τ).const_mul c
      simpa using this.add_const d
    have h_div : HasDerivAt Mob
        ((a * (c * τ + d) - (a * τ + b) * c) / (c * τ + d) ^ 2) τ := h_num.div h_den h_denom_ne
    have h_simpl : (a * (c * τ + d) - (a * τ + b) * c) / (c * τ + d) ^ 2
        = 1 / (c * τ + d) ^ 2 := by
      rw [div_eq_div_iff (pow_ne_zero 2 h_denom_ne) (pow_ne_zero 2 h_denom_ne)]
      linear_combination ((c * τ + d) ^ 2) * h_det
    rw [← h_simpl]
    exact h_div
  have hγτ_im_pos : 0 < ((γ • τ_h : UpperHalfPlane) : ℂ).im := (γ • τ_h).2
  have h_inv_local :
      ∀ᶠ z in nhds τ, modularLambdaH (Mob z) = modularLambdaH z := by
    have h_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    have hτ_mem : τ ∈ {z : ℂ | 0 < z.im} := hτ
    refine Filter.eventually_of_mem (h_open.mem_nhds hτ_mem) ?_
    intro z hz
    have hz_im : 0 < z.im := hz
    set z_h : UpperHalfPlane := ⟨z, hz_im⟩ with hz_h_def
    have h_inv_z := modularLambdaH_gamma2_invariant γ hγ_in z_h
    have h_smul_z_coe : ((γ • z_h : UpperHalfPlane) : ℂ) = Mob z := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      change ((((algebraMap ℤ ℝ) (γ.val 0 0)) : ℂ) * (z_h : ℂ) +
          ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ)) /
          (((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) * (z_h : ℂ) +
            ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ)) = Mob z
      simp [hMob_def, ha_def, hb_def, hc_def, hd_def, hz_h_def]
    rw [h_smul_z_coe] at h_inv_z
    exact h_inv_z
  have h_compose_deriv :
      deriv (fun z : ℂ => modularLambdaH (Mob z)) τ
        = deriv modularLambdaH (Mob τ) * (1 / (c * τ + d) ^ 2) := by
    have h_Mob_im_pos : 0 < (Mob τ).im := by
      have hh := (γ • τ_h : UpperHalfPlane).2
      rw [h_smul_coe] at hh
      exact hh
    have h_lam_diff_at_Mobτ : DifferentiableAt ℂ modularLambdaH (Mob τ) :=
      modularLambdaH_differentiableAt_of_im_pos h_Mob_im_pos
    have h_chain : HasDerivAt (fun z : ℂ => modularLambdaH (Mob z))
        (deriv modularLambdaH (Mob τ) * (1 / (c * τ + d) ^ 2)) τ :=
      (h_lam_diff_at_Mobτ.hasDerivAt).comp τ h_Mob_deriv
    exact h_chain.deriv
  have h_deriv_eq :
      deriv (fun z : ℂ => modularLambdaH (Mob z)) τ = deriv modularLambdaH τ :=
    Filter.EventuallyEq.deriv_eq h_inv_local
  rw [h_compose_deriv] at h_deriv_eq
  rw [h_smul_coe] at h_deriv_γτ
  intro h_zero
  rw [h_zero] at h_deriv_eq
  have h_factor_ne : (1 : ℂ) / (c * τ + d) ^ 2 ≠ 0 :=
    one_div_ne_zero (pow_ne_zero 2 h_denom_ne)
  have := h_deriv_eq.symm
  rw [eq_comm, mul_eq_zero] at this
  rcases this with h | h
  · exact h_deriv_γτ h
  · exact h_factor_ne h

/-- **Pillar-3 LHP `< 0` branch.** For `τ ∈ ℍ` with `Im(λ τ) < 0`,
`deriv λ τ ≠ 0`. Proof: pass to `τ' := -conj τ ∈ ℍ`; by
`modularLambdaH_conj_symmetry`, `λ τ' = conj(λ τ)` so
`Im(λ τ') > 0` and the upper branch gives `deriv λ τ' ≠ 0`. Define
`G(z) := conj(λ(-conj z))`; by the conjugation identity `G = λ`
locally on `ℍ`. Compute `deriv G τ = -conj(deriv λ τ')` via the
Wirtinger / FDeriv composition `conj ∘ λ ∘ negConj` over `ℝ`; the
two anti-holomorphic `conj` factors cancel algebraically so the
composition is the `ℝ`-linear map `h ↦ -conj(d) · h`, identified as
`(-conj d) • id_ℝ`. Convert this `ℝ`-FDeriv to a `ℂ`-derivative via
the `isLittleO` characterisation. Combined with
`deriv G τ = deriv λ τ` (EventuallyEq), conclude
`deriv λ τ = -conj(deriv λ τ') ≠ 0`. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_neg
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im < 0) :
    deriv modularLambdaH τ ≠ 0 := by
  -- τ' := -conj τ ∈ ℍ.
  have hτ' : 0 < (-(starRingEnd ℂ τ)).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ
  have h_lam_τ' :
      modularLambdaH (-(starRingEnd ℂ τ)) = starRingEnd ℂ (modularLambdaH τ) :=
    modularLambdaH_conj_symmetry hτ
  have h_im_pos' : 0 < (modularLambdaH (-(starRingEnd ℂ τ))).im := by
    rw [h_lam_τ', Complex.conj_im]; linarith
  -- Upper branch: deriv λ at τ' is non-zero.
  have hd_ne : deriv modularLambdaH (-(starRingEnd ℂ τ)) ≠ 0 :=
    modularLambdaH_deriv_ne_zero_when_im_lambda_pos hτ' h_im_pos'
  -- G(z) := conj(λ(-conj z)); G = λ locally at τ.
  have hG_eq_lam :
      (fun z => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) =ᶠ[nhds τ] modularLambdaH := by
    have h_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    filter_upwards [h_open.mem_nhds (show τ ∈ {z : ℂ | 0 < z.im} from hτ)] with z hz_im
    show starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z))) = modularLambdaH z
    rw [show modularLambdaH (-(starRingEnd ℂ z)) = starRingEnd ℂ (modularLambdaH z) from
        modularLambdaH_conj_symmetry hz_im, Complex.conj_conj]
  -- Abbreviate d := deriv λ τ'.
  set d : ℂ := deriv modularLambdaH (-(starRingEnd ℂ τ)) with hd_def
  -- HasFDerivAt for the three pieces (all `ℝ`-linear, avoiding `restrictScalars`).
  have h_negconj_fderiv : HasFDerivAt (fun z : ℂ => -(starRingEnd ℂ z))
      (-(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)) τ :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.neg
  have h_conj_fderiv : HasFDerivAt (fun w : ℂ => starRingEnd ℂ w)
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)
      (modularLambdaH (-(starRingEnd ℂ τ))) :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  -- `λ` has `ℝ`-FDeriv `d • (id ℝ ℂ)` at `-conj τ`. Bypass the `restrictScalars`
  -- type-class issue by constructing the `ℝ`-linear FDeriv directly via
  -- `hasFDerivAt_iff_isLittleO` from the underlying `HasDerivAt`.
  have h_lam_diff_at : DifferentiableAt ℂ modularLambdaH (-(starRingEnd ℂ τ)) :=
    modularLambdaH_differentiableAt_of_im_pos hτ'
  have h_lam_hasDeriv : HasDerivAt modularLambdaH d (-(starRingEnd ℂ τ)) :=
    h_lam_diff_at.hasDerivAt
  have h_lam_fderiv : HasFDerivAt modularLambdaH
      (d • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ))
      (-(starRingEnd ℂ τ)) := by
    rw [hasFDerivAt_iff_isLittleO]
    have h_o := h_lam_hasDeriv.isLittleO
    refine h_o.congr_left ?_
    intro y
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- Inner composition: λ ∘ negConj.
  have h_inner := h_lam_fderiv.comp τ h_negconj_fderiv
  -- Outer composition: conj ∘ (λ ∘ negConj).
  have h_outer := h_conj_fderiv.comp τ h_inner
  -- The `ℝ`-linear composition equals `(-conj d) • id_ℝ` by ring after
  -- pushing `conj` through products and using `conj_conj`.
  have h_comp_eq :
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp
        ((d • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)).comp
          (-(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ))) =
        (-(starRingEnd ℂ d)) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) := by
    ext h
    have h_cle : ∀ z : ℂ, (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) z = starRingEnd ℂ z :=
      fun _ => rfl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply, h_cle, smul_eq_mul]
    rw [map_mul, map_neg, Complex.conj_conj]
    ring
  rw [h_comp_eq] at h_outer
  -- Convert the `ℝ`-FDeriv with `(-conj d) • id_ℝ` to a `ℂ`-derivative.
  have hG_hasDeriv : HasDerivAt
      (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z))))
      (-(starRingEnd ℂ d)) τ := by
    rw [hasDerivAt_iff_isLittleO]
    have h_outer_o := h_outer.isLittleO
    refine h_outer_o.congr_left ?_
    intro y
    simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- deriv G τ = -conj d via chain rule.
  have h_deriv_G_chain :
      deriv (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) τ
        = -(starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ)))) :=
    hG_hasDeriv.deriv
  -- deriv G τ = deriv λ τ via EventuallyEq.
  have h_deriv_G_local :
      deriv (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) τ
        = deriv modularLambdaH τ :=
    hG_eq_lam.deriv_eq
  -- Conclude.
  intro h_zero
  rw [h_zero] at h_deriv_G_local
  rw [h_deriv_G_chain] at h_deriv_G_local
  -- h_deriv_G_local : -(starRingEnd ℂ (deriv λ (-conj τ))) = 0.
  have h_conjd_zero : starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ))) = 0 :=
    neg_eq_zero.mp h_deriv_G_local
  have h_d_zero : deriv modularLambdaH (-(starRingEnd ℂ τ)) = 0 := by
    have h_conj_conj :
        starRingEnd ℂ (starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ)))) =
          starRingEnd ℂ 0 := congr_arg _ h_conjd_zero
    rwa [Complex.conj_conj, map_zero] at h_conj_conj
  exact hd_ne h_d_zero
/-- **Pillar-3 LHP-and-boundary branch (dispatcher).** -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_non_pos
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im ≤ 0) :
    deriv modularLambdaH τ ≠ 0 := by
  rcases lt_or_eq_of_le hlam_im with h | h
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_neg hτ h
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_zero hτ h

/-- **Pillar-4 LHP branch (Im λ < 0).** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) < 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`.

Proof: pass to `τ_i' := -conj τ_i ∈ ℍ`; by
`modularLambdaH_conj_symmetry` we have `Im(λ τ_i') > 0` and
`λ(τ₁') = λ(τ₂')`. Apply the upper branch to obtain
`γ = ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∈ Γ(2)` with `γ • τ₁' = τ₂'`. Conjugating
both sides translates to `γ' • τ₁ = τ₂` for
`γ' := ⟨⟨a, -b⟩, ⟨-c, d⟩⟩`, also in `Γ(2)`. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_neg
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_neg : (modularLambdaH (τ₁ : ℂ)).im < 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have hτ₁_im : 0 < (τ₁ : ℂ).im := τ₁.2
  have hτ₂_im : 0 < (τ₂ : ℂ).im := τ₂.2
  -- Build τ_i' := -conj τ_i ∈ ℍ.
  have hτ₁'_im : 0 < (-(starRingEnd ℂ (τ₁ : ℂ))).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ₁_im
  have hτ₂'_im : 0 < (-(starRingEnd ℂ (τ₂ : ℂ))).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ₂_im
  set τ₁' : UpperHalfPlane := ⟨-(starRingEnd ℂ (τ₁ : ℂ)), hτ₁'_im⟩ with hτ₁'_def
  set τ₂' : UpperHalfPlane := ⟨-(starRingEnd ℂ (τ₂ : ℂ)), hτ₂'_im⟩ with hτ₂'_def
  have h_lam_τ₁' : modularLambdaH (τ₁' : ℂ) = starRingEnd ℂ (modularLambdaH (τ₁ : ℂ)) :=
    modularLambdaH_conj_symmetry hτ₁_im
  have h_lam_τ₂' : modularLambdaH (τ₂' : ℂ) = starRingEnd ℂ (modularLambdaH (τ₂ : ℂ)) :=
    modularLambdaH_conj_symmetry hτ₂_im
  have h_im_pos' : 0 < (modularLambdaH (τ₁' : ℂ)).im := by
    rw [h_lam_τ₁', Complex.conj_im]
    linarith
  have h_eq' : modularLambdaH (τ₁' : ℂ) = modularLambdaH (τ₂' : ℂ) := by
    rw [h_lam_τ₁', h_lam_τ₂', h_eq]
  obtain ⟨γ, hγ_in, hγ_eq⟩ :=
    gamma2_lambda_eq_implies_orbit_when_im_lambda_pos h_im_pos' h_eq'
  -- Build γ' = [[a, -b], [-c, d]] ∈ SL(2, ℤ).
  set γ'_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![γ.val 0 0, -γ.val 0 1; -γ.val 1 0, γ.val 1 1] with hγ'_mat_def
  have hγ'_det : γ'_mat.det = 1 := by
    simp only [hγ'_mat_def, Matrix.det_fin_two_of]
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    linarith
  set γ' : SL(2, ℤ) := ⟨γ'_mat, hγ'_det⟩ with hγ'_def
  have hγ'_in : γ' ∈ CongruenceSubgroup.Gamma 2 := by
    rw [CongruenceSubgroup.Gamma_mem]
    have hγ_mem : _ ∧ _ ∧ _ ∧ _ := CongruenceSubgroup.Gamma_mem.mp hγ_in
    obtain ⟨ha, hb, hc, hd⟩ := hγ_mem
    have h00' : γ'.val 0 0 = γ.val 0 0 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    have h01' : γ'.val 0 1 = -γ.val 0 1 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    have h10' : γ'.val 1 0 = -γ.val 1 0 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    have h11' : γ'.val 1 1 = γ.val 1 1 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h00']; exact ha
    · rw [h01']; push_cast; rw [hb]; ring
    · rw [h10']; push_cast; rw [hc]; ring
    · rw [h11']; exact hd
  refine ⟨γ', hγ'_in, ?_⟩
  apply UpperHalfPlane.ext
  -- The upper-branch identity in ℂ.
  have h_γ_eq_c : ((γ • τ₁' : UpperHalfPlane) : ℂ) = (τ₂' : ℂ) := by rw [hγ_eq]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h_γ_eq_c
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  -- γ' entries match γ with sign flips on b, c.
  have h00 : γ'.val 0 0 = γ.val 0 0 := by simp [hγ'_def, hγ'_mat_def]
  have h01 : γ'.val 0 1 = -γ.val 0 1 := by simp [hγ'_def, hγ'_mat_def]
  have h10 : γ'.val 1 0 = -γ.val 1 0 := by simp [hγ'_def, hγ'_mat_def]
  have h11 : γ'.val 1 1 = γ.val 1 1 := by simp [hγ'_def, hγ'_mat_def]
  rw [h00, h01, h10, h11]
  -- Abbreviate the real-cast entries.
  set a : ℂ := ((algebraMap ℤ ℝ) (γ.val 0 0) : ℂ) with ha_def
  set b : ℂ := ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ) with hb_def
  set c : ℂ := ((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) with hc_def
  set d : ℂ := ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ) with hd_def
  -- Negation through algebraMap.
  have hb_neg : ((algebraMap ℤ ℝ) (-γ.val 0 1) : ℂ) = -b := by push_cast; ring
  have hc_neg : ((algebraMap ℤ ℝ) (-γ.val 1 0) : ℂ) = -c := by push_cast; ring
  rw [hb_neg, hc_neg]
  -- Substitute τ_i' = -conj τ_i in h_γ_eq_c.
  have h_τ₁'_c_eq : (τ₁' : ℂ) = -(starRingEnd ℂ (τ₁ : ℂ)) := rfl
  have h_τ₂'_c_eq : (τ₂' : ℂ) = -(starRingEnd ℂ (τ₂ : ℂ)) := rfl
  rw [h_τ₁'_c_eq, h_τ₂'_c_eq] at h_γ_eq_c
  -- Take conjugate of the equation.
  have h_conj := congr_arg (starRingEnd ℂ) h_γ_eq_c
  simp only [map_div₀, map_add, map_mul, map_neg, Complex.conj_conj] at h_conj
  -- Conj of real-coerced values is itself.
  have hca : starRingEnd ℂ a = a := Complex.conj_ofReal _
  have hcb : starRingEnd ℂ b = b := Complex.conj_ofReal _
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  have hcd : starRingEnd ℂ d = d := Complex.conj_ofReal _
  rw [hca, hcb, hcc, hcd] at h_conj
  -- h_conj : (a * -(τ₁) + b) / (c * -(τ₁) + d) = -(τ₂).
  -- Goal: (a * τ₁ + -b) / (-c * τ₁ + d) = τ₂.
  -- Reduce to h_conj via numerator/denominator sign manipulation.
  have h_num_eq : a * (τ₁ : ℂ) + -b = -(a * -(τ₁ : ℂ) + b) := by ring
  have h_den_eq : -c * (τ₁ : ℂ) + d = c * -(τ₁ : ℂ) + d := by ring
  rw [h_num_eq, h_den_eq, neg_div, h_conj, neg_neg]

/-- **Orbit relation is closed.** The `Γ(2)`-orbit relation
`{(τ₁, τ₂) : ∃ γ ∈ Γ(2), γ • τ₁ = τ₂}` is closed in
`ℍ × ℍ`. Proof: take a convergent sequence
`(τ₁^n, τ₂^n) → (τ₁, τ₂)` with `γₙ • τ₁^n = τ₂^n`. Locally compact
neighbourhoods of `τ₁, τ₂` and `gamma_two_properlyDiscontinuousSMul`
restrict `γₙ` to a finite set; extract a subsequence with constant
`γₙ = γ`, take the limit using continuity of `γ•`, and conclude
`γ • τ₁ = τ₂`. -/
theorem gamma2_orbitRel_isClosed :
    IsClosed { p : UpperHalfPlane × UpperHalfPlane |
      ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • p.1 = p.2 } := by
  rw [← isSeqClosed_iff_isClosed]
  intro xn x h_in_n h_tendsto
  haveI := gamma_two_properlyDiscontinuousSMul
  -- Extract γₙ for each xₙ.
  choose γn hγn_in hγn_eq using h_in_n
  -- Compact closed balls around x.1, x.2.
  set K₁ : Set UpperHalfPlane := Metric.closedBall x.1 1 with hK₁_def
  set K₂ : Set UpperHalfPlane := Metric.closedBall x.2 1 with hK₂_def
  have hK₁_compact : IsCompact K₁ := isCompact_closedBall _ _
  have hK₂_compact : IsCompact K₂ := isCompact_closedBall _ _
  -- Convergence in each coordinate.
  have h_tendsto_1 : Filter.Tendsto (fun n => (xn n).1) Filter.atTop (nhds x.1) :=
    (continuous_fst.tendsto x).comp h_tendsto
  have h_tendsto_2 : Filter.Tendsto (fun n => (xn n).2) Filter.atTop (nhds x.2) :=
    (continuous_snd.tendsto x).comp h_tendsto
  rw [Metric.tendsto_atTop] at h_tendsto_1 h_tendsto_2
  obtain ⟨N₁, hN₁⟩ := h_tendsto_1 (1/2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := h_tendsto_2 (1/2) (by norm_num)
  set N : ℕ := max N₁ N₂ with hN_def
  -- Finite γ-set from proper discontinuity.
  set S : Set (↥(CongruenceSubgroup.Gamma 2)) :=
    { g | ((fun τ => g • τ) '' K₁ ∩ K₂).Nonempty } with hS_def
  have hS_finite : S.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK₁_compact hK₂_compact
  -- For n ≥ N, the lifted γn n lives in S.
  have h_γn_in_S : ∀ n, N ≤ n →
      (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) ∈ S := by
    intro n hn
    have h1 := hN₁ n (le_of_max_le_left hn)
    have h2 := hN₂ n (le_of_max_le_right hn)
    refine ⟨(xn n).2, ⟨(xn n).1, ?_, hγn_eq n⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr (le_trans h1.le (by norm_num))
    · exact Metric.mem_closedBall.mpr (le_trans h2.le (by norm_num))
  -- Pigeonhole: some γ ∈ S is hit infinitely often in (γn n)_{n ≥ N}.
  have h_pigeon : ∃ γ : ↥(CongruenceSubgroup.Gamma 2), γ ∈ S ∧
      {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ}.Infinite := by
    by_contra h_neg
    push Not at h_neg
    have h_ici_infinite : Set.Infinite (Set.Ici N) := Set.Ici_infinite N
    apply h_ici_infinite
    have h_eq : Set.Ici N =
        ⋃ γ ∈ S, {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} := by
      ext n
      simp only [Set.mem_Ici, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
      constructor
      · intro hn
        refine ⟨⟨γn n, hγn_in n⟩, h_γn_in_S n hn, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩
        exact hn
    rw [h_eq]
    apply hS_finite.biUnion
    intro γ hγ
    exact h_neg γ hγ
  -- Extract γ and infinite subsequence.
  obtain ⟨γ, _hγ_in_S, hγ_inf⟩ := h_pigeon
  -- Build a strictly increasing index sequence in the fiber.
  have h_seq : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, φ k ∈ {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} := by
    apply Nat.exists_strictMono_subsequence
    intro M
    obtain ⟨b, hb_in, hb_gt⟩ := hγ_inf.exists_gt M
    exact ⟨b, hb_gt, hb_in⟩
  obtain ⟨φ, hφ_mono, hφ_in⟩ := h_seq
  -- For each k: γn (φ k) = γ.val, so γ.val • (xn (φ k)).1 = (xn (φ k)).2.
  -- Take limit using continuity of γ.val•.
  refine ⟨γ.val, γ.property, ?_⟩
  -- γ.val • x.1 = x.2: use continuity.
  have h_cont : Continuous (fun τ : UpperHalfPlane => γ.val • τ) := by
    change Continuous (fun τ : UpperHalfPlane => ((γ.val : SL(2, ℝ)) • τ))
    exact continuous_const_smul _
  have h_tend1 : Filter.Tendsto (fun n => (xn n).1) Filter.atTop (nhds x.1) :=
    (continuous_fst.tendsto x).comp h_tendsto
  have h_tend2 : Filter.Tendsto (fun n => (xn n).2) Filter.atTop (nhds x.2) :=
    (continuous_snd.tendsto x).comp h_tendsto
  have h_tendsto_left : Filter.Tendsto (fun k => γ.val • (xn (φ k)).1) Filter.atTop
      (nhds (γ.val • x.1)) :=
    (h_cont.tendsto _).comp (h_tend1.comp hφ_mono.tendsto_atTop)
  have h_tendsto_right : Filter.Tendsto (fun k => (xn (φ k)).2) Filter.atTop (nhds x.2) :=
    h_tend2.comp hφ_mono.tendsto_atTop
  -- For each k: γ.val • (xn (φ k)).1 = (xn (φ k)).2.
  have h_eq_seq : ∀ k, γ.val • (xn (φ k)).1 = (xn (φ k)).2 := by
    intro k
    have hk_in : φ k ∈ {n | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} :=
      hφ_in k
    have h_γ_eq : γn (φ k) = γ.val := by
      have := hk_in.2
      exact congrArg Subtype.val this
    rw [← h_γ_eq]
    exact hγn_eq (φ k)
  have h_replace : (fun k => γ.val • (xn (φ k)).1) = (fun k => (xn (φ k)).2) :=
    funext h_eq_seq
  rw [h_replace] at h_tendsto_left
  exact tendsto_nhds_unique h_tendsto_left h_tendsto_right

/-- **Density of upper `λ`-fibre at the boundary.** For
`(τ₁, τ₂) ∈ ℍ × ℍ` with `λ(τ₁) = λ(τ₂)` and `Im(λ τ₁) = 0` (the
boundary case), every neighbourhood of `(τ₁, τ₂)` in `ℍ × ℍ`
contains some `(τ₁', τ₂')` with `λ(τ₁') = λ(τ₂')` and
`Im(λ τ₁') > 0`. Proof: the open mapping theorem
(`AnalyticAt.eventually_constant_or_nhds_le_map_nhds` applied to `λ`
at `τ₁, τ₂`) gives `λ(D₁) ∩ λ(D₂)` as a neighbourhood of
`λ(τ₁) = λ(τ₂)` for any small balls `D₁, D₂`. With `Im λ τ₁ = 0`,
the open neighbourhood intersects `{Im > 0}`; pick `v` there and
pull back to `τ₁' ∈ D₁`, `τ₂' ∈ D₂`. -/
theorem modularLambdaH_eq_fibre_dense_in_im_lambda_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_zero : (modularLambdaH (τ₁ : ℂ)).im = 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ))
    (U : Set (UpperHalfPlane × UpperHalfPlane))
    (hU : U ∈ nhds (τ₁, τ₂)) :
    ∃ p ∈ U, modularLambdaH (p.1 : ℂ) = modularLambdaH (p.2 : ℂ) ∧
      0 < (modularLambdaH (p.1 : ℂ)).im := by
  -- Get product nhd V₁ ×ˢ V₂ ⊆ U.
  obtain ⟨V₁, hV₁, V₂, hV₂, hV_sub⟩ := mem_nhds_prod_iff.mp hU
  -- Set H := {z : ℂ | 0 < z.im}, open.
  set H : Set ℂ := {z : ℂ | 0 < z.im} with hH_def
  have hH_open : IsOpen H := by
    have : H = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp [hH_def]
    rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
  have hH_preconn : IsPreconnected H := by
    apply Convex.isPreconnected
    intro w₁ hw₁ w₂ hw₂ s t hs ht hst
    change 0 < (s • w₁ + t • w₂).im
    rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
    rcases lt_or_eq_of_le hs with hs_pos | hs_zero
    · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
      have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
      linarith
    · have ht_pos : 0 < t := by linarith
      have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
      have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
      linarith
  -- λ is analytic on H.
  have h_lam_analytic : AnalyticOnNhd ℂ modularLambdaH H :=
    modularLambdaH_differentiableOn.analyticOnNhd hH_open
  -- λ has different values: 1+i and 2+i are both in image (in ℂ ∖ {0, 1}).
  have h_lam_not_const : ¬ Set.EqOn modularLambdaH (fun _ => modularLambdaH (τ₁ : ℂ)) H := by
    intro h_eqOn
    -- Use modularLambdaH_image to find τ_a, τ_b with different λ-values.
    have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.im h; simp at this
    have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.re h; simp at this
    have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' H := by
      rw [modularLambdaH_image]; exact h_1i_in
    have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' H := by
      rw [modularLambdaH_image]; exact h_2i_in
    obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
    obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
    have h_eq_a : modularLambdaH τ_a = modularLambdaH (τ₁ : ℂ) := h_eqOn hτ_a_H
    have h_eq_b : modularLambdaH τ_b = modularLambdaH (τ₁ : ℂ) := h_eqOn hτ_b_H
    have : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := by
      rw [← hτ_a_eq, ← hτ_b_eq, h_eq_a, h_eq_b]
    have h_re := congrArg Complex.re this
    simp at h_re
  -- λ is not eventually constant at (τ₁ : ℂ).
  have hτ₁_in_H : (τ₁ : ℂ) ∈ H := τ₁.2
  have hτ₂_in_H : (τ₂ : ℂ) ∈ H := τ₂.2
  have h_not_evt_const_at_τ₁ : ¬ (∀ᶠ z in nhds (τ₁ : ℂ),
      modularLambdaH z = modularLambdaH (τ₁ : ℂ)) := by
    intro h_evt
    apply h_lam_not_const
    exact h_lam_analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hH_preconn
      hτ₁_in_H h_evt
  have h_not_evt_const_at_τ₂ : ¬ (∀ᶠ z in nhds (τ₂ : ℂ),
      modularLambdaH z = modularLambdaH (τ₂ : ℂ)) := by
    intro h_evt
    apply h_lam_not_const
    have h_lam_analytic_const : AnalyticOnNhd ℂ (fun _ => modularLambdaH (τ₁ : ℂ)) H :=
      analyticOnNhd_const
    -- λ =ᶠ const-at-τ₂ at τ₂, but const-at-τ₂ = const-at-τ₁ (h_eq).
    have h_evt' : ∀ᶠ z in nhds (τ₂ : ℂ), modularLambdaH z = modularLambdaH (τ₁ : ℂ) := by
      filter_upwards [h_evt] with z hz
      rw [hz]; exact h_eq.symm
    exact h_lam_analytic.eqOn_of_preconnected_of_eventuallyEq h_lam_analytic_const hH_preconn
      hτ₂_in_H h_evt'
  -- Apply open mapping at τ₁ and τ₂.
  have h_lam_at_τ₁ : AnalyticAt ℂ modularLambdaH (τ₁ : ℂ) :=
    h_lam_analytic _ hτ₁_in_H
  have h_lam_at_τ₂ : AnalyticAt ℂ modularLambdaH (τ₂ : ℂ) :=
    h_lam_analytic _ hτ₂_in_H
  have h_open_τ₁ : nhds (modularLambdaH (τ₁ : ℂ)) ≤ Filter.map modularLambdaH (nhds (τ₁ : ℂ)) :=
    (h_lam_at_τ₁.eventually_constant_or_nhds_le_map_nhds).resolve_left h_not_evt_const_at_τ₁
  have h_open_τ₂ : nhds (modularLambdaH (τ₂ : ℂ)) ≤ Filter.map modularLambdaH (nhds (τ₂ : ℂ)) :=
    (h_lam_at_τ₂.eventually_constant_or_nhds_le_map_nhds).resolve_left h_not_evt_const_at_τ₂
  -- Bridge V_i to nhd in ℂ via open embedding.
  have hW₁_nhd : ((↑) : UpperHalfPlane → ℂ) '' V₁ ∈ nhds (τ₁ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ₁).symm ▸ Filter.image_mem_map hV₁
  have hW₂_nhd : ((↑) : UpperHalfPlane → ℂ) '' V₂ ∈ nhds (τ₂ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ₂).symm ▸ Filter.image_mem_map hV₂
  -- λ(W_i) is a nhd of λ τ_i.
  have h_lamW₁_nhd : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∈
      nhds (modularLambdaH (τ₁ : ℂ)) :=
    h_open_τ₁ (Filter.image_mem_map hW₁_nhd)
  have h_lamW₂_nhd : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
      nhds (modularLambdaH (τ₂ : ℂ)) :=
    h_open_τ₂ (Filter.image_mem_map hW₂_nhd)
  -- λ(W₁) ∩ λ(W₂) is a nhd of λ τ_1 (= λ τ_2).
  have h_inter_nhd :
      modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∩
        modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
      nhds (modularLambdaH (τ₁ : ℂ)) := by
    have h_lamW₂_nhd' : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
        nhds (modularLambdaH (τ₁ : ℂ)) := h_eq ▸ h_lamW₂_nhd
    exact Filter.inter_mem h_lamW₁_nhd h_lamW₂_nhd'
  -- {Im > 0} ∩ (nhd of λ τ_1) is non-empty since Im(λ τ_1) = 0.
  have h_im_pos_nhd : ∃ v ∈ modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∩
        modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂), 0 < v.im := by
    -- Take open ball around λ τ_1 small enough inside the inter nhd; pick a point with Im > 0.
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp h_inter_nhd
    refine ⟨modularLambdaH (τ₁ : ℂ) + (ε/2 : ℝ) * Complex.I, ?_, ?_⟩
    · apply hε_ball
      rw [Metric.mem_ball, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε/2)]
      linarith
    · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, h_im_zero]
      linarith
  obtain ⟨v, hv_inter, hv_im⟩ := h_im_pos_nhd
  -- Pull back v to τ_1' ∈ V_1 and τ_2' ∈ V_2.
  obtain ⟨hv₁_in, hv₂_in⟩ := hv_inter
  obtain ⟨z₁, ⟨τ₁', hτ₁'_V, rfl⟩, h_lam_z₁⟩ := hv₁_in
  obtain ⟨z₂, ⟨τ₂', hτ₂'_V, rfl⟩, h_lam_z₂⟩ := hv₂_in
  -- The witness pair.
  refine ⟨(τ₁', τ₂'), hV_sub ⟨hτ₁'_V, hτ₂'_V⟩, ?_, ?_⟩
  · change modularLambdaH (τ₁' : ℂ) = modularLambdaH (τ₂' : ℂ)
    rw [h_lam_z₁, h_lam_z₂]
  · change 0 < (modularLambdaH (τ₁' : ℂ)).im
    rw [h_lam_z₁]; exact hv_im

/-- **Pillar-4 boundary branch (Im λ = 0).** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) = 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Closes via density (`modularLambdaH_eq_fibre_dense_in_im_lambda_pos`)
of the upper `λ`-fibre + closedness of the orbit relation
(`gamma2_orbitRel_isClosed`) + the upper branch
`gamma2_lambda_eq_implies_orbit_when_im_lambda_pos`. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_zero
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_zero : (modularLambdaH (τ₁ : ℂ)).im = 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  -- The orbit relation R, the target set of (τ₁, τ₂).
  set R : Set (UpperHalfPlane × UpperHalfPlane) :=
    { p | ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • p.1 = p.2 } with hR_def
  change (τ₁, τ₂) ∈ R
  have hR_closed : IsClosed R := gamma2_orbitRel_isClosed
  rw [← hR_closed.closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨p, hp_U, hp_eq, hp_im⟩ :=
    modularLambdaH_eq_fibre_dense_in_im_lambda_pos h_im_zero h_eq U hU
  exact ⟨p, hp_U, gamma2_lambda_eq_implies_orbit_when_im_lambda_pos hp_im hp_eq⟩

/-- **Pillar-4 LHP-and-boundary branch.** Combination of the
`Im(λ) < 0` and `Im(λ) = 0` cases. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_non_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_le : (modularLambdaH (τ₁ : ℂ)).im ≤ 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  rcases lt_or_eq_of_le h_im_le with h_lt | h_eq_zero
  · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_neg h_lt h_eq
  · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_zero h_eq_zero h_eq

/-! ## Pillar 3: non-vanishing of the derivative -/

/-- **Pillar 3: `λ'(τ) ≠ 0` for every `τ ∈ ℍ`.** Case split on the
sign of `Im(λ τ)`. -/
theorem modularLambdaH_deriv_ne_zero_on_upperHalf
    {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambdaH τ ≠ 0 := by
  rcases le_or_gt (modularLambdaH τ).im 0 with h_im_le | h_im_pos
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_non_pos hτ h_im_le
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_pos hτ h_im_pos

/-! ## Pillar 4: orbit identification -/

/-- **Pillar 4: `λ` separates `Γ(2)`-orbits.** Case split on the
sign of `Im(λ τ₁)` (which equals `Im(λ τ₂)` by hypothesis). -/
theorem modularLambdaH_eq_iff_gamma2_orbit
    {τ₁ τ₂ : UpperHalfPlane} :
    modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ) ↔
      ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  constructor
  · intro h_eq
    rcases le_or_gt (modularLambdaH (τ₁ : ℂ)).im 0 with h_im_le | h_im_pos
    · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_non_pos h_im_le h_eq
    · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_pos h_im_pos h_eq
  · rintro ⟨γ, hγ_in, h_eq⟩
    rw [← h_eq]
    exact (modularLambdaH_gamma2_invariant γ hγ_in τ₁).symm

/-! ## Main covering-map theorems -/

/-- **Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`.**

The source space here is `ℂ` (since `modularLambdaH : ℂ → ℂ`), not `ℍ`,
yet the statement is mathematically correct. Off `ℍ` the defining series
`theta3 τ = ∑' n, cexp (π·i·n²·τ)` is non-summable, so Mathlib's `tsum`
returns `0` and the division `theta2 τ ^ 4 / theta3 τ ^ 4` yields the
junk value `0`. Since the base set explicitly excludes `0`, the preimage
of any small `U` around a point `w ∈ {w | w ≠ 0 ∧ w ≠ 1}` cannot contain
any `τ ∉ ℍ`, so `f⁻¹ U ⊆ ℍ`. Because `ℍ` is open in `ℂ`, the subspace
topology on `f⁻¹ U` from `ℂ` agrees with that from `ℍ`, and the standard
covering-map property of `λ : ℍ → ℂ ∖ {0, 1}` transports verbatim. -/
theorem modularLambdaH_isCoveringMapOn :
    IsCoveringMapOn modularLambdaH { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

/-- **Covering property of `λ` on the unit disk.**

Same source-topology subtlety as `modularLambdaH_isCoveringMapOn`: the
Cayley transform composition `modularLambda := modularLambdaH ∘
cayleyToHalfPlane` is typed as `ℂ → ℂ`, but the junk value off `𝔻` lands
on the excluded point `0`, so the preimage of any open `U` around a base
point sits inside `𝔻` and the covering property transports through. -/
theorem modularLambda_isCoveringMapOn :
    IsCoveringMapOn modularLambda { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

end RiemannDynamics

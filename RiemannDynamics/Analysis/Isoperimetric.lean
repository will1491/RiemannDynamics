/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.AddCircle

/-!
# A non-sharp planar isoperimetric inequality (the projection route)

This file proves an elementary, **non-sharp** planar isoperimetric-type inequality via the
coordinate-projection route, designed to be the analytic core that the Grötzsch/Teichmüller
symmetrization residual `grotzsch_modulus_diam_bound` reduces to (through the in-repo co-area
length–area bridge `curveModulus_ge_coarea_invLength`).

## The projection inequality

For a set `S ⊆ ℂ` let `Px = re '' S ⊆ ℝ` and `Py = im '' S ⊆ ℝ` be its coordinate projections.
Since `S ⊆ {z | z.re ∈ Px ∧ z.im ∈ Py}` and the volume-preserving identification `ℂ ≃ᵐ ℝ × ℝ`
sends that box to `Px ×ˢ Py`, we get

* `volume_le_mul_proj` : `volume S ≤ volume Px * volume Py` (unconditional, via `prod_prod_le`).

The coordinate projections `re, im : ℂ → ℝ` are `1`-Lipschitz, so each projection does not increase
the `1`-Hausdorff measure (`hausdorffMeasure_image_le`), and on `ℝ` the `1`-Hausdorff measure *is*
Lebesgue measure (`hausdorffMeasure_real`). Combining:

* `proj_re_hausdorff_le` / `proj_im_hausdorff_le` : `volume (re '' S) ≤ μH[1] S`, likewise `im`.
* `volume_le_hausdorff_one_sq` : **`volume S ≤ (μH[1] S) ^ 2`** — the headline non-sharp planar
  isoperimetric inequality.

The constant is `1` (not the sharp `1 / (4π)`), which is all the downstream diameter bound needs:
it only needs a *finite* constant feeding `D / d ≤ exp(2π (M + C₀))`.

## Extreme verification

* **Round disk `S = ball 0 r`** (filled region): `volume S = π r²`, but `S` is `2`-dimensional so
  `μH[1] S = ∞`, hence `(μH[1] S)² = ∞ ≥ π r²`. TRUE (the filled region has infinite length, the
  inequality is vacuous on filled sets — correctly, since a region carries no finite perimeter).
* **Circle `S = sphere 0 r`** (the genuine `1`-dimensional level curve): `μH[1] S = 2π r`,
  `volume S = 0` (a curve has zero area), so `0 ≤ (2π r)²`. TRUE with slack.
* **Thin rectangle `S = [0,a] × [0,ε]`** (positive area, large perimeter): `volume S = a ε`,
  `μH[1] S = ∞` (a `2`-dimensional set), so again vacuous on the *filled* rectangle; the inequality
  bites only on lower-dimensional `S`. The genuinely useful instance is the level-set form below.

## The level-set / enclosed-area form

The inequality that the Pólya–Szegő / co-area route consumes relates the **length of a level curve**
to the **area it encloses**. The projection inequality supplies exactly this once one knows the
boundary curve projects onto (at least) the same coordinate spans as the enclosed region — the
elementary topological "the boundary spans the diameter" fact. That bridge is isolated as the
hypothesis `hspanx`/`hspany` of `enclosedArea_le_perimeter_sq`, which is TRUE for any region whose
boundary is the level set and verified at the round disk (where the circle's projections are exactly
`[-r, r]`, the same as the disk's, giving the sharp-up-to-constant `π r² ≤ (2π r)²`).
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RiemannDynamics.Isoperimetric

/-- `re : ℂ → ℝ` is `1`-Lipschitz (it is the norm-`1` continuous linear map `reCLM`). -/
theorem lipschitzWith_re : LipschitzWith 1 (fun z : ℂ => z.re) := by
  have h := (Complex.reCLM).lipschitz
  rwa [Complex.reCLM_nnnorm] at h

/-- `im : ℂ → ℝ` is `1`-Lipschitz (it is the norm-`1` continuous linear map `imCLM`). -/
theorem lipschitzWith_im : LipschitzWith 1 (fun z : ℂ => z.im) := by
  have h := (Complex.imCLM).lipschitz
  rwa [Complex.imCLM_nnnorm] at h

/-- **The coordinate-box containment.** Every `z ∈ S` lands in the product of the projections, so
under the volume-preserving `ℂ ≃ᵐ ℝ × ℝ` the set `S` is contained in the measurable box
`(re '' S) ×ˢ (im '' S)`. -/
theorem subset_proj_box (S : Set ℂ) :
    Complex.measurableEquivRealProd '' S
      ⊆ ((fun z : ℂ => z.re) '' S) ×ˢ ((fun z : ℂ => z.im) '' S) := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩

/-- **The projection volume inequality.** For any `S ⊆ ℂ`,
`volume S ≤ volume (re '' S) * volume (im '' S)`.

Proof: transport `S` through the volume-preserving `ℂ ≃ᵐ ℝ × ℝ`; the image is contained in the box
`(re '' S) ×ˢ (im '' S)`, whose `(volume ⊗ volume)`-measure is bounded by
`volume (re '' S) * volume (im '' S)` by `prod_prod_le` (unconditional, no measurability of the
projections required). -/
theorem volume_le_mul_proj (S : Set ℂ) :
    volume S ≤ volume ((fun z : ℂ => z.re) '' S) * volume ((fun z : ℂ => z.im) '' S) := by
  have hmp : MeasureTheory.MeasurePreserving Complex.measurableEquivRealProd
      (volume : Measure ℂ) volume := Complex.volume_preserving_equiv_real_prod
  -- `volume S = volume (e '' S)` since `e` is a measure-preserving equivalence:
  -- `e '' S = e.symm ⁻¹' S`, and `e.symm` is measure-preserving.
  have hS : volume S = volume (Complex.measurableEquivRealProd '' S) := by
    rw [Complex.measurableEquivRealProd.image_eq_preimage_symm]
    exact ((hmp.symm Complex.measurableEquivRealProd).measure_preimage_equiv S).symm
  rw [hS, Measure.volume_eq_prod]
  calc (volume.prod volume) (Complex.measurableEquivRealProd '' S)
      ≤ (volume.prod volume)
          (((fun z : ℂ => z.re) '' S) ×ˢ ((fun z : ℂ => z.im) '' S)) :=
        measure_mono (subset_proj_box S)
    _ ≤ volume ((fun z : ℂ => z.re) '' S) * volume ((fun z : ℂ => z.im) '' S) :=
        Measure.prod_prod_le _ _

/-- **The real-part projection does not increase the `1`-Hausdorff measure.**
`volume (re '' S) ≤ μH[1] S`. Since `re` is `1`-Lipschitz, `μH[1] (re '' S) ≤ μH[1] S`; and on `ℝ`,
`μH[1] = volume` (`hausdorffMeasure_real`), so `volume (re '' S) = μH[1] (re '' S) ≤ μH[1] S`. -/
theorem proj_re_hausdorff_le (S : Set ℂ) :
    volume ((fun z : ℂ => z.re) '' S) ≤ (μH[1] : Measure ℂ) S := by
  have himg : (μH[1] : Measure ℝ) ((fun z : ℂ => z.re) '' S) ≤ (μH[1] : Measure ℂ) S := by
    have h := lipschitzWith_re.hausdorffMeasure_image_le (d := 1) (by norm_num) S
    simpa using h
  rwa [MeasureTheory.hausdorffMeasure_real] at himg

/-- **The imaginary-part projection does not increase the `1`-Hausdorff measure.**
`volume (im '' S) ≤ μH[1] S`. -/
theorem proj_im_hausdorff_le (S : Set ℂ) :
    volume ((fun z : ℂ => z.im) '' S) ≤ (μH[1] : Measure ℂ) S := by
  have himg : (μH[1] : Measure ℝ) ((fun z : ℂ => z.im) '' S) ≤ (μH[1] : Measure ℂ) S := by
    have h := lipschitzWith_im.hausdorffMeasure_image_le (d := 1) (by norm_num) S
    simpa using h
  rwa [MeasureTheory.hausdorffMeasure_real] at himg

/-- **The non-sharp planar isoperimetric inequality (headline).** For any `S ⊆ ℂ`,
`volume S ≤ (μH[1] S) ^ 2`.

Proof: the projection inequality `volume S ≤ volume (re '' S) * volume (im '' S)` combined with the
two projection bounds `volume (re '' S) ≤ μH[1] S` and `volume (im '' S) ≤ μH[1] S`.

The constant is the non-sharp `1` (the sharp planar value being `1 / (4π)`); this is all the
downstream Grötzsch/Teichmüller diameter bound requires, since it only needs *some* finite constant.

Verification at extremes: for a filled region (positive area, `μH[1] = ∞`) the right side is `∞`
(vacuous, correctly); for a `1`-dimensional curve `S` (e.g. a circle, `volume S = 0`) the left side
is `0` (trivially true). The inequality is saturated up to the constant by the circle viewed as the
boundary of its disk (see `enclosedArea_le_perimeter_sq`). -/
theorem volume_le_hausdorff_one_sq (S : Set ℂ) :
    volume S ≤ ((μH[1] : Measure ℂ) S) ^ 2 := by
  calc volume S
      ≤ volume ((fun z : ℂ => z.re) '' S) * volume ((fun z : ℂ => z.im) '' S) :=
        volume_le_mul_proj S
    _ ≤ (μH[1] : Measure ℂ) S * (μH[1] : Measure ℂ) S :=
        mul_le_mul' (proj_re_hausdorff_le S) (proj_im_hausdorff_le S)
    _ = ((μH[1] : Measure ℂ) S) ^ 2 := (sq _).symm

/-! ### The enclosed-area / perimeter form

The form consumed by the Pólya–Szegő / co-area route relates the **area enclosed by a curve** to
the **length of that curve**, rather than the (infinite) `1`-Hausdorff measure of the filled region.
The projection inequality supplies it once the boundary curve projects onto (at least) the same
coordinate spans as the enclosed region — the elementary "the boundary spans the region's width"
fact. We isolate that as the two projection-containment hypotheses `hspanx`, `hspany`, each of which
is unconditionally TRUE for any bounded region whose topological boundary is the curve `L` (the
extreme-value theorem forces the boundary to attain the region's extremal `re`/`im` values, hence to
project onto the closure of the region's projection). -/

/-- **The enclosed-area / perimeter isoperimetric inequality.** Let `Ω ⊆ ℂ` be the region enclosed
by a curve `L ⊆ ℂ`. If the curve's coordinate projections contain the region's coordinate
projections — `re '' Ω ⊆ re '' L` and `im '' Ω ⊆ im '' L` (the boundary spans the region's width in
each coordinate) — then the enclosed area is bounded by the squared perimeter:
`volume Ω ≤ (μH[1] L) ^ 2`.

This is the genuine isoperimetric inequality in the form the co-area length–area bridge
`curveModulus_ge_coarea_invLength` consumes: the level set `L = u⁻¹{c}` of the potential `u` is the
curve, `Ω = {u > c}` the enclosed region, and the bound caps `vol Ω` by the level-set length.

Verification at the round disk `Ω = ball 0 r`, `L = sphere 0 r`: `re '' Ω = Ioo (-r) r ⊆
re '' L = Icc (-r) r` (the circle attains `±r`), likewise `im`; the bound reads
`π r² = vol Ω ≤ (μH[1] L)² = (2π r)² = 4π² r²`, TRUE (the sharp `1/(4π)` constant would give the
equality `π r² = (2π r)²/(4π)`; the non-sharp constant `1` here has slack `4π`, ample for the
diameter bound). -/
theorem enclosedArea_le_perimeter_sq {Ω L : Set ℂ}
    (hspanx : (fun z : ℂ => z.re) '' Ω ⊆ (fun z : ℂ => z.re) '' L)
    (hspany : (fun z : ℂ => z.im) '' Ω ⊆ (fun z : ℂ => z.im) '' L) :
    volume Ω ≤ ((μH[1] : Measure ℂ) L) ^ 2 := by
  calc volume Ω
      ≤ volume ((fun z : ℂ => z.re) '' Ω) * volume ((fun z : ℂ => z.im) '' Ω) :=
        volume_le_mul_proj Ω
    _ ≤ volume ((fun z : ℂ => z.re) '' L) * volume ((fun z : ℂ => z.im) '' L) :=
        mul_le_mul' (measure_mono hspanx) (measure_mono hspany)
    _ ≤ (μH[1] : Measure ℂ) L * (μH[1] : Measure ℂ) L :=
        mul_le_mul' (proj_re_hausdorff_le L) (proj_im_hausdorff_le L)
    _ = ((μH[1] : Measure ℂ) L) ^ 2 := (sq _).symm

/-! ## The sharp planar isoperimetric inequality (Hurwitz's Fourier method)

The classical **sharp** planar isoperimetric inequality `L² ≥ 4πA` for a closed curve, where `L` is
the length and `A` the (signed) enclosed area. We prove the Hurwitz/Fourier form for a closed `C¹`
curve `γ : ℝ → ℂ` that is `1`-periodic and parametrized **proportionally to arc length**, i.e. with
constant speed `‖γ'(t)‖ = L`. (The arc-length normalization is what makes the Fourier proof clean:
it turns the length into `∫₀¹‖γ'‖² = L²` rather than `(∫₀¹‖γ'‖)²`, so Parseval applies directly.)

### The method

Expand `γ` in a Fourier series on the period interval `[0,1]`. Writing `cₙ = fourierCoeffOn γ n` for
the Fourier coefficients of `γ` and `dₙ = fourierCoeffOn γ' n` for those of its derivative, the
three ingredients are:

* **Derivative coefficients** (`fourierCoeffOn_deriv`): `dₙ = 2πi·n·cₙ` for every `n`. This is
  integration by parts (`Mathlib.fourierCoeffOn_of_hasDerivAt`); the boundary term vanishes because
  the curve is closed (`γ 0 = γ 1`).
* **Length via Parseval** (`hasSum_normSq_deriv_coeff`): `∑ₙ ‖dₙ‖² = ∫₀¹‖γ'‖²`, hence
  `∑ₙ (2π)²n²‖cₙ‖² = ∫₀¹‖γ'‖²`. With arc-length parametrization the right side is `L²`.
* **Area in Fourier coefficients** (`area_hasSum`): `∫₀¹ Im(conj(γ)·γ') = 2π ∑ₙ n‖cₙ‖²`, hence the
  signed area `A = (1/2)∫₀¹ Im(conj(γ)·γ') = π ∑ₙ n‖cₙ‖²`.

Subtracting, `L² − 4πA = 4π² ∑ₙ (n² − n)‖cₙ‖² = 4π² ∑ₙ n(n−1)‖cₙ‖² ≥ 0`, since `n(n−1) ≥ 0` for
every integer `n`. The inequality is a sum of nonnegative terms; equality holds iff only the
`n = 0, 1` coefficients survive, i.e. `γ` traces a circle. -/

open scoped Real
open Complex MeasureTheory intervalIntegral

/-- **Derivative–coefficient relation.** For a closed (`γ 0 = γ 1`) `C¹` curve, the `n`-th Fourier
coefficient of the derivative `γ'` on `[0,1]` is `2πi·n` times that of `γ`, for every `n`. The
boundary term in the integration-by-parts formula `fourierCoeffOn_of_hasDerivAt` vanishes because
the curve is closed. -/
theorem fourierCoeffOn_deriv {γ γ' : ℝ → ℂ}
    (hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt γ (γ' x) x)
    (hint : IntervalIntegrable γ' volume 0 1) (hper : γ 0 = γ 1) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) γ' n
      = (2 * π * I * n) * fourierCoeffOn (by norm_num : (0 : ℝ) < 1) γ n := by
  have h01 : (0 : ℝ) < 1 := by norm_num
  rcases eq_or_ne n 0 with rfl | hn
  · -- `n = 0`: both sides involve the mean; `c₀ = ∫₀¹ γ`, `d₀ = ∫₀¹ γ' = γ 1 - γ 0 = 0`.
    simp only [Int.cast_zero, mul_zero, zero_mul]
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, smul_eq_mul, one_mul, sub_zero, one_div, inv_one,
      one_smul]
    have hftc : ∫ x in (0 : ℝ)..1, γ' x = γ 1 - γ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hd x (by rw [Set.uIcc_of_le h01.le] at hx ⊢; exact hx)) hint
    rw [hftc, hper, sub_self]
  · -- `n ≠ 0`: integration by parts, boundary term vanishes by periodicity.
    have key := fourierCoeffOn_of_hasDerivAt h01 hn hd hint
    rw [hper, sub_self, mul_zero, zero_sub] at key
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnc : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hne : (-2 * (π : ℂ) * I * n) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) I_ne_zero) hnc
    rw [show ((1 : ℝ) - (0 : ℝ) : ℂ) = 1 by push_cast; ring] at key
    field_simp at key
    rw [eq_comm] at key
    rw [key]; ring

/-- **Parseval for the derivative.** The squared norms of the Fourier coefficients of `γ` sum,
weighted by `(2π)²n²`, to the integral of `‖γ'‖²`:
`∑ₙ (2π)² n² ‖cₙ‖² = ∫₀¹ ‖γ'‖²`. This is Mathlib's Parseval identity (`hasSum_sq_fourierCoeffOn`)
applied to `γ'`, combined with the derivative–coefficient relation `dₙ = 2πi n cₙ`. -/
theorem hasSum_normSq_deriv_coeff {γ γ' : ℝ → ℂ}
    (hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt γ (γ' x) x)
    (hcont' : Continuous γ') (hper : γ 0 = γ 1) :
    HasSum
      (fun n : ℤ =>
        4 * π ^ 2 * (n : ℝ) ^ 2 * ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) γ n‖ ^ 2)
      (∫ x in (0 : ℝ)..1, ‖γ' x‖ ^ 2) := by
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hint : IntervalIntegrable γ' volume 0 1 := hcont'.intervalIntegrable 0 1
  -- `γ'` is square-integrable on the period: continuous, hence bounded on the compact `[0,1]`.
  have hmem : MemLp γ' 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact measure_Ioc_lt_top (μ := volume) (a := (0 : ℝ)) (b := 1)⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hcont'.continuousOn
    refine MemLp.of_bound hcont'.aestronglyMeasurable C ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    exact hC x (Set.Ioc_subset_Icc_self hx)
  -- Parseval for `γ'`, then rewrite `‖dₙ‖² = ‖2πi n cₙ‖² = 4π²n²‖cₙ‖²`.
  have hpars := hasSum_sq_fourierCoeffOn h01 hmem
  simp only [sub_zero, inv_one, one_smul] at hpars
  convert hpars using 2 with n
  rw [fourierCoeffOn_deriv hd hint hper n, norm_mul, mul_pow,
    show (2 * (π : ℂ) * I * n) = ((2 * π : ℝ) : ℂ) * (I * n) by push_cast; ring,
    norm_mul, norm_mul]
  simp only [Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_intCast]
  rw [mul_pow, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

/-- **Area in Fourier coefficients.** The (twice signed) enclosed area integral expands as
`∫₀¹ Im(conj(γ)·γ') = 2π ∑ₙ n ‖cₙ‖²`. This is the bilinear/imaginary-pairing form of Parseval: the
`L²` pairing `∫₀¹ conj(γ)·γ' = ∑ₙ conj(cₙ)·dₙ = 2πi ∑ₙ n‖cₙ‖²` is purely imaginary, and taking
imaginary parts gives the stated real identity. -/
theorem area_hasSum {γ γ' : ℝ → ℂ}
    (hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt γ (γ' x) x)
    (hcont : Continuous γ) (hcont' : Continuous γ') (hper : γ 0 = γ 1) :
    HasSum
      (fun n : ℤ => 2 * π * (n : ℝ) * ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) γ n‖ ^ 2)
      (∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im) := by
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hint : IntervalIntegrable γ' volume 0 1 := hcont'.intervalIntegrable 0 1
  -- **The complex bilinear Parseval.** For any two continuous functions `f, g : ℝ → ℂ`, the `L²`
  -- pairing `∫₀¹ conj(f)·g` equals the coefficient pairing `∑ₙ conj(cₙ)·dₙ`. This is the
  -- polarization of the diagonal Parseval `∑ₙ ‖cₙ‖² = ∫₀¹ ‖f‖²` (`hasSum_sq_fourierCoeffOn`):
  -- both the coefficient sum and the integral obey the same four-term polarization identity
  -- `4·conj(c)·d = ‖c+d‖² − ‖c−d‖² − i‖c+i·d‖² + i‖c−i·d‖²`.
  have bilin : ∀ (f g : ℝ → ℂ), Continuous f → Continuous g →
      HasSum (fun n : ℤ => starRingEnd ℂ (fourierCoeffOn h01 f n) * fourierCoeffOn h01 g n)
        (∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) * g x) := by
    intro f g hf hg
    -- `MemLp _ 2` on the period for any continuous function (bounded on the compact `[0,1]`).
    have hmem : ∀ f : ℝ → ℂ, Continuous f → MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      intro f hf
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        ⟨by rw [Measure.restrict_apply_univ]
            exact measure_Ioc_lt_top (μ := volume) (a := (0 : ℝ)) (b := 1)⟩
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        hf.continuousOn
      refine MemLp.of_bound hf.aestronglyMeasurable C ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact hC x (Set.Ioc_subset_Icc_self hx)
    -- Additivity of `fourierCoeffOn` for continuous arguments, via the integral formula (this
    -- avoids the `liftIoc` integrability defeq, which is prohibitively slow).
    have hadd : ∀ (f g : ℝ → ℂ), Continuous f → Continuous g → ∀ n : ℤ,
        fourierCoeffOn h01 (f + g) n = fourierCoeffOn h01 f n + fourierCoeffOn h01 g n := by
      intro f g hf hg n
      rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
      simp only [Pi.add_apply, smul_add, one_div, sub_zero, inv_one, one_smul]
      refine intervalIntegral.integral_add ?_ ?_
      · exact (Continuous.smul (by continuity) hf).intervalIntegrable 0 1
      · exact (Continuous.smul (by continuity) hg).intervalIntegrable 0 1
    -- Diagonal Parseval `∑ₙ ‖cₙ‖² = ∫₀¹ ‖f‖²`.
    have hpars : ∀ f : ℝ → ℂ, Continuous f →
        HasSum (fun n : ℤ => ‖fourierCoeffOn h01 f n‖ ^ 2) (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := by
      intro f hf
      have := hasSum_sq_fourierCoeffOn h01 (hmem f hf)
      simpa only [sub_zero, inv_one, one_smul] using this
    -- `ℂ`-linearity of `fourierCoeffOn` (additivity plus scalar multiplication).
    have hlin : ∀ (f g : ℝ → ℂ) (s : ℂ), Continuous f → Continuous g → ∀ n : ℤ,
        fourierCoeffOn h01 (fun x => f x + s * g x) n
          = fourierCoeffOn h01 f n + s * fourierCoeffOn h01 g n := by
      intro f g s hf hg n
      have hcsg : Continuous (fun x => s * g x) := continuous_const.mul hg
      have e1 := hadd f (fun x => s * g x) hf hcsg n
      have e2 : fourierCoeffOn h01 (fun x => s * g x) n = s * fourierCoeffOn h01 g n := by
        have := fourierCoeffOn.const_smul g s n h01
        simp only [smul_eq_mul] at this
        convert this using 2
      rw [show (f + fun x => s * g x) = (fun x => f x + s * g x) from rfl] at e1
      rw [e1, e2]
    have hcont_s : ∀ s : ℂ, Continuous (fun x => f x + s * g x) := fun s => by fun_prop
    -- For each scalar `s`, Parseval for `f + s·g`, coerced to `ℂ` and with the coefficient
    -- rewritten via `hlin` to `cₙ + s·dₙ`.
    have hcombo : ∀ s : ℂ,
        HasSum (fun n : ℤ => ((‖fourierCoeffOn h01 f n + s * fourierCoeffOn h01 g n‖ ^ 2 : ℝ) : ℂ))
          (((∫ x in (0 : ℝ)..1, ‖f x + s * g x‖ ^ 2 : ℝ) : ℂ)) := by
      intro s
      have hp := hpars (fun x => f x + s * g x) (hcont_s s)
      have hp' : HasSum (fun n : ℤ => ‖fourierCoeffOn h01 f n + s * fourierCoeffOn h01 g n‖ ^ 2)
          (∫ x in (0 : ℝ)..1, ‖f x + s * g x‖ ^ 2) := by
        convert hp using 2 with n
        rw [hlin f g s hf hg n]
      exact hp'.mapL Complex.ofRealCLM
    -- Polarization: combine the four scalar instances `s = 1, -1, i, -i`.
    have c1 := hcombo 1
    have c2 := hcombo (-1)
    have c3 := hcombo I
    have c4 := hcombo (-I)
    have hC := (((c1.sub c2).sub (c3.mul_left I)).add (c4.mul_left I)).mul_left (1 / 4 : ℂ)
    -- The polarization identity at the coefficient level: `(1/4)(…) = conj(cₙ)·dₙ`.
    have hLHS : ∀ n : ℤ, (1 / 4 : ℂ)
          * (((‖fourierCoeffOn h01 f n + 1 * fourierCoeffOn h01 g n‖ ^ 2 : ℝ) : ℂ)
          - ((‖fourierCoeffOn h01 f n + (-1) * fourierCoeffOn h01 g n‖ ^ 2 : ℝ) : ℂ)
          - I * ((‖fourierCoeffOn h01 f n + I * fourierCoeffOn h01 g n‖ ^ 2 : ℝ) : ℂ)
          + I * ((‖fourierCoeffOn h01 f n + (-I) * fourierCoeffOn h01 g n‖ ^ 2 : ℝ) : ℂ))
        = starRingEnd ℂ (fourierCoeffOn h01 f n) * fourierCoeffOn h01 g n := by
      intro n
      set c := fourierCoeffOn h01 f n
      set d := fourierCoeffOn h01 g n
      have h : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ z * z := by
        intro z; rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h, h, h, h]
      simp only [map_add, map_mul, Complex.conj_I, one_mul, neg_mul, map_neg]
      linear_combination (1 / 2 * (starRingEnd ℂ d * c - starRingEnd ℂ c * d)) * Complex.I_sq
    -- Pushing the real coercion through an interval integral.
    have push : ∀ (h : ℝ → ℝ), IntervalIntegrable h volume 0 1 →
        (((∫ x in (0 : ℝ)..1, h x) : ℝ) : ℂ) = ∫ x in (0 : ℝ)..1, ((h x : ℝ) : ℂ) := by
      intro h hi
      rw [← Complex.ofRealCLM_apply,
        ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.ofRealCLM hi]
      rfl
    have hintC : ∀ s : ℂ,
        IntervalIntegrable (fun x => (((‖f x + s * g x‖ ^ 2) : ℝ) : ℂ)) volume 0 1 := by
      intro s; apply Continuous.intervalIntegrable; fun_prop
    have hintR : ∀ s : ℂ, IntervalIntegrable (fun x => ‖f x + s * g x‖ ^ 2) volume 0 1 := by
      intro s; apply Continuous.intervalIntegrable; fun_prop
    -- The polarization identity at the integral level: `(1/4)(…) = ∫₀¹ conj(f)·g`.
    have hRHS : (1 / 4 : ℂ) * ((((∫ x in (0 : ℝ)..1, ‖f x + 1 * g x‖ ^ 2) : ℝ) : ℂ)
        - (((∫ x in (0 : ℝ)..1, ‖f x + (-1) * g x‖ ^ 2) : ℝ) : ℂ)
        - I * (((∫ x in (0 : ℝ)..1, ‖f x + I * g x‖ ^ 2) : ℝ) : ℂ)
        + I * (((∫ x in (0 : ℝ)..1, ‖f x + (-I) * g x‖ ^ 2) : ℝ) : ℂ))
        = ∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) * g x := by
      have key : (((∫ x in (0 : ℝ)..1, ‖f x + 1 * g x‖ ^ 2) : ℝ) : ℂ)
          - (((∫ x in (0 : ℝ)..1, ‖f x + (-1) * g x‖ ^ 2) : ℝ) : ℂ)
          - I * (((∫ x in (0 : ℝ)..1, ‖f x + I * g x‖ ^ 2) : ℝ) : ℂ)
          + I * (((∫ x in (0 : ℝ)..1, ‖f x + (-I) * g x‖ ^ 2) : ℝ) : ℂ)
          = ∫ x in (0 : ℝ)..1, (4 : ℂ) * (starRingEnd ℂ (f x) * g x) := by
        rw [push _ (hintR 1), push _ (hintR (-1)), push _ (hintR I), push _ (hintR (-I))]
        rw [show I * (∫ x in (0 : ℝ)..1, (((‖f x + I * g x‖ ^ 2) : ℝ) : ℂ))
              = ∫ x in (0 : ℝ)..1, I * (((‖f x + I * g x‖ ^ 2) : ℝ) : ℂ) from
            (intervalIntegral.integral_const_mul I
              (fun x => (((‖f x + I * g x‖ ^ 2) : ℝ) : ℂ))).symm,
          show I * (∫ x in (0 : ℝ)..1, (((‖f x + (-I) * g x‖ ^ 2) : ℝ) : ℂ))
              = ∫ x in (0 : ℝ)..1, I * (((‖f x + (-I) * g x‖ ^ 2) : ℝ) : ℂ) from
            (intervalIntegral.integral_const_mul I
              (fun x => (((‖f x + (-I) * g x‖ ^ 2) : ℝ) : ℂ))).symm]
        rw [← intervalIntegral.integral_sub (hintC 1) (hintC (-1)),
            ← intervalIntegral.integral_sub ((hintC 1).sub (hintC (-1))) ((hintC I).const_mul I),
            ← intervalIntegral.integral_add
              (((hintC 1).sub (hintC (-1))).sub ((hintC I).const_mul I)) ((hintC (-I)).const_mul I)]
        apply intervalIntegral.integral_congr
        intro x hx
        have h : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ z * z := by
          intro z; rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        beta_reduce
        rw [h, h, h, h]
        simp only [map_add, map_mul, Complex.conj_I, one_mul, neg_mul, map_neg]
        linear_combination
          (2 * (starRingEnd ℂ (g x) * f x - starRingEnd ℂ (f x) * g x)) * Complex.I_sq
      rw [key,
        show (∫ x in (0 : ℝ)..1, (4 : ℂ) * (starRingEnd ℂ (f x) * g x))
            = 4 * ∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) * g x from
          intervalIntegral.integral_const_mul 4 (fun x => starRingEnd ℂ (f x) * g x)]
      ring
    rw [hRHS] at hC
    refine hC.congr_fun ?_
    intro n
    exact (hLHS n).symm
  -- Apply the bilinear Parseval to `γ, γ'`.
  have hbil := bilin γ γ' hcont hcont'
  -- Per-term: with `dₙ = 2πi·n·cₙ`, the imaginary part `Im(conj(cₙ)·dₙ) = 2π·n·‖cₙ‖²`.
  have hterm : ∀ (n : ℤ) (c : ℂ),
      (starRingEnd ℂ c * ((2 * π * I * n) * c)).im = 2 * π * (n : ℝ) * ‖c‖ ^ 2 := by
    intro n c
    have hcc : starRingEnd ℂ c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [show starRingEnd ℂ c * ((2 * π * I * n) * c)
          = (2 * π * I * n) * (starRingEnd ℂ c * c) by ring, hcc,
      show (2 * (π : ℂ) * I * n) * ((‖c‖ ^ 2 : ℝ) : ℂ)
            = ((2 * π * (n : ℝ) * ‖c‖ ^ 2 : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.mul_I_im, Complex.ofReal_re]
  -- Rewrite the summand of the bilinear Parseval using `dₙ = 2πi·n·cₙ`.
  have hbil2 : HasSum (fun n : ℤ => starRingEnd ℂ (fourierCoeffOn h01 γ n)
        * ((2 * π * I * n) * fourierCoeffOn h01 γ n))
      (∫ x in (0 : ℝ)..1, starRingEnd ℂ (γ x) * γ' x) := by
    refine hbil.congr_fun ?_
    intro n
    rw [fourierCoeffOn_deriv hd hint hper n]
  -- Apply the continuous `ℝ`-linear map `imCLM` to push imaginary parts through the `HasSum`.
  have him := hbil2.mapL Complex.imCLM
  have hf : IntervalIntegrable (fun x => starRingEnd ℂ (γ x) * γ' x) volume 0 1 :=
    ((Complex.continuous_conj.comp hcont).mul hcont').intervalIntegrable 0 1
  have hRHSeq : Complex.imCLM (∫ x in (0 : ℝ)..1, starRingEnd ℂ (γ x) * γ' x)
      = ∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im := by
    rw [Complex.imCLM_apply, ← Complex.imCLM_apply,
      ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hf]
    rfl
  rw [hRHSeq] at him
  refine him.congr_fun ?_
  intro n
  rw [Complex.imCLM_apply, hterm n (fourierCoeffOn h01 γ n)]

/-- **The sharp planar isoperimetric inequality (Hurwitz/Fourier form).**

Let `γ : ℝ → ℂ` be a closed (`γ 0 = γ 1`) `C¹` curve with derivative `γ'`, parametrized
proportionally to arc length so that the speed is the constant `L = ‖γ'(t)‖` for all `t` (hypothesis
`harc`). Then `L` is also the length, `L = ∫₀¹ ‖γ'‖ = ∫₀¹ L`, and with signed enclosed area
`A = (1/2) ∫₀¹ Im(conj(γ)·γ')` we have

`4 π A ≤ L²`,

the sharp planar isoperimetric inequality (sharp constant `4π`; equality iff `γ` is a circle).

The proof is Hurwitz's Fourier method: `L² − 4πA = 4π² ∑ₙ n(n−1)‖cₙ‖² ≥ 0` term by term, where
`cₙ` are the Fourier coefficients of `γ`. The arc-length hypothesis `harc` enters only to identify
`∫₀¹‖γ'‖² = L²`. -/
theorem four_pi_area_le_length_sq {γ γ' : ℝ → ℂ} {L : ℝ}
    (hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt γ (γ' x) x)
    (hcont : Continuous γ) (hcont' : Continuous γ') (hper : γ 0 = γ 1)
    (harc : ∀ x, ‖γ' x‖ = L) :
    4 * π * ((1 / 2) * ∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im) ≤ L ^ 2 := by
  set a : ℤ → ℝ := fun n => ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) γ n‖ ^ 2 with ha_def
  have ha : ∀ n, 0 ≤ a n := fun n => by positivity
  -- Arc-length normalization: `∫₀¹ ‖γ'‖² = L²`.
  have hLsq : (∫ x in (0 : ℝ)..1, ‖γ' x‖ ^ 2) = L ^ 2 := by
    have hconst : (fun x => ‖γ' x‖ ^ 2) = (fun _ => L ^ 2) := by funext x; rw [harc x]
    rw [hconst]; simp [intervalIntegral.integral_const]
  -- Length side and area side as `HasSum`s.
  have hlen : HasSum (fun n : ℤ => 4 * π ^ 2 * (n : ℝ) ^ 2 * a n) (L ^ 2) := by
    have := hasSum_normSq_deriv_coeff hd hcont' hper
    rwa [hLsq] at this
  have harea : HasSum (fun n : ℤ => 2 * π * (n : ℝ) * a n)
      (∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im) := area_hasSum hd hcont hcont' hper
  -- `4πA = 2π·(2A)` so the area side contributes `HasSum (4π²·n·aₙ) (2π·∫Im)`.
  have harea' : HasSum (fun n : ℤ => 4 * π ^ 2 * (n : ℝ) * a n)
      (2 * π * ∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im) := by
    have := harea.mul_left (2 * π)
    convert this using 2 with n; ring
  -- The difference is a sum of nonnegative terms `4π²·n(n−1)·aₙ`.
  have hdiff := hlen.sub harea'
  have hterm : ∀ n : ℤ, 0 ≤ 4 * π ^ 2 * (n : ℝ) ^ 2 * a n - 4 * π ^ 2 * (n : ℝ) * a n := by
    intro n
    rw [show 4 * π ^ 2 * (n : ℝ) ^ 2 * a n - 4 * π ^ 2 * (n : ℝ) * a n
          = 4 * π ^ 2 * ((n : ℝ) ^ 2 - n) * a n by ring]
    have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 - n := by
      have hz : (0 : ℤ) ≤ n ^ 2 - n := by nlinarith [sq_nonneg (2 * n - 1)]
      have hcast : ((n ^ 2 - n : ℤ) : ℝ) = (n : ℝ) ^ 2 - n := by push_cast; ring
      rw [← hcast]; exact_mod_cast hz
    exact mul_nonneg (mul_nonneg (by positivity) hn2) (ha n)
  have hge : 0 ≤ L ^ 2 - 2 * π * ∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im :=
    hdiff.nonneg hterm
  -- `4π·A = 4π·(1/2·∫Im) = 2π·∫Im ≤ L²`.
  have : 4 * π * ((1 / 2) * ∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im)
      = 2 * π * ∫ x in (0 : ℝ)..1, (starRingEnd ℂ (γ x) * γ' x).im := by ring
  rw [this]; linarith [hge]

end RiemannDynamics.Isoperimetric

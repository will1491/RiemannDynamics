/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Def

/-!
# Foliation arc functionals and the pseudo-Anosov interface

The horizontal and vertical foliations of a quadratic differential `q` are carried by their
transverse arc measures: along a curve `γ` the pullback `Q(t) = q (γ t) (γ' t)²` determines
the branch-free densities `|Im √Q| = √((|Q| − Re Q)/2)` and `|Re √Q| = √((|Q| + Re Q)/2)`,
whose integrals are the transverse measures of the horizontal and vertical foliations; the
flat length `∫ |q|^{1/2} |dz|` dominates both. All three functionals are invariant under
deck transformations by the weight-4 law.

A Teichmüller `λ`-stretch of `q` is a map expanding the horizontal foliation by `λ` and
contracting the vertical one by `λ⁻¹`; in branch-free form this is the first-order pair
`q(f) (∂f)² = a² q` and `q(f) ∂f ∂̄f = a b |q|` with `a = (λ+λ⁻¹)/2`, `b = (λ−λ⁻¹)/2`. A
mapping class of the Bers model is **pseudo-Anosov** when some representative point carries
a nonzero quadratic differential and a `λ`-stretch self-map of the upper half plane, with
`λ > 1`, normalizing the marked group and inducing the re-marking on the boundary.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The transverse densities -/

/-- The **horizontal transverse density** of `q` along `γ` at time `t`: the branch-free
form of `|Im (√q dz)|`, computed from `Q = q (γ t) (γ' t)²` as `√((|Q| − Re Q)/2)`. It
vanishes along horizontal trajectories and measures their crossings. -/
noncomputable def horizontalDensity (q : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.sqrt ((‖q (γ t) * deriv γ t ^ 2‖ - (q (γ t) * deriv γ t ^ 2).re) / 2))

/-- The **vertical transverse density** of `q` along `γ` at time `t`: the branch-free form
of `|Re (√q dz)|`, computed from `Q = q (γ t) (γ' t)²` as `√((|Q| + Re Q)/2)`. -/
noncomputable def verticalDensity (q : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.sqrt ((‖q (γ t) * deriv γ t ^ 2‖ + (q (γ t) * deriv γ t ^ 2).re) / 2))

/-- The **horizontal variation** of a curve: the transverse measure of the horizontal
foliation of `q` deposited along `γ`. -/
noncomputable def horizontalVariation (q : ℂ → ℂ) (γ : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, horizontalDensity q γ t

/-- The **vertical variation** of a curve: the transverse measure of the vertical foliation
of `q` deposited along `γ`. -/
noncomputable def verticalVariation (q : ℂ → ℂ) (γ : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, verticalDensity q γ t

/-- The **flat length** of a curve in the `|q|^{1/2} |dz|` metric of `q`. -/
noncomputable def qdLength (q : ℂ → ℂ) (γ : ℝ → ℂ) : ℝ≥0∞ :=
  arcLengthLineIntegral (fun z => ENNReal.ofReal (Real.sqrt ‖q z‖)) γ

/-- `0 ≤ (‖w‖ − Re w)/2`, from `|Re w| ≤ ‖w‖`. -/
theorem norm_sub_re_div_two_nonneg (w : ℂ) : 0 ≤ (‖w‖ - w.re) / 2 := by
  have h := abs_le.mp (Complex.abs_re_le_norm w)
  linarith [h.2]

/-- `0 ≤ (‖w‖ + Re w)/2`, from `|Re w| ≤ ‖w‖`. -/
theorem norm_add_re_div_two_nonneg (w : ℂ) : 0 ≤ (‖w‖ + w.re) / 2 := by
  have h := abs_le.mp (Complex.abs_re_le_norm w)
  linarith [h.1]

/-- The flat density factorizes: `√‖q (γ t) (γ' t)²‖ = √‖q (γ t)‖ ‖γ' t‖`. -/
theorem sqrt_norm_mul_sq (q : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    Real.sqrt ‖q (γ t) * deriv γ t ^ 2‖ = Real.sqrt ‖q (γ t)‖ * ‖deriv γ t‖ := by
  rw [norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Pythagoras for the transverse densities: the squares of the horizontal and vertical
densities sum to the flat density squared `|Q| = |q (γ t)| |γ' t|²`. -/
theorem horizontalDensity_sq_add_verticalDensity_sq (q : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    horizontalDensity q γ t ^ 2 + verticalDensity q γ t ^ 2
      = ‖q (γ t) * deriv γ t ^ 2‖ₑ := by
  have h1 := norm_sub_re_div_two_nonneg (q (γ t) * deriv γ t ^ 2)
  have h2 := norm_add_re_div_two_nonneg (q (γ t) * deriv γ t ^ 2)
  unfold horizontalDensity verticalDensity
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt h1, Real.sq_sqrt h2, ← ENNReal.ofReal_add h1 h2, ← ofReal_norm_eq_enorm]
  congr 1
  ring

/-- The horizontal density is dominated by the flat length density. -/
theorem horizontalDensity_le (q : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    horizontalDensity q γ t
      ≤ ENNReal.ofReal (Real.sqrt ‖q (γ t)‖) * ‖deriv γ t‖₊ := by
  have habs := abs_le.mp (Complex.abs_re_le_norm (q (γ t) * deriv γ t ^ 2))
  have hle : (‖q (γ t) * deriv γ t ^ 2‖ - (q (γ t) * deriv γ t ^ 2).re) / 2
      ≤ ‖q (γ t) * deriv γ t ^ 2‖ := by linarith [habs.1]
  unfold horizontalDensity
  calc ENNReal.ofReal
        (Real.sqrt ((‖q (γ t) * deriv γ t ^ 2‖ - (q (γ t) * deriv γ t ^ 2).re) / 2))
      ≤ ENNReal.ofReal (Real.sqrt ‖q (γ t) * deriv γ t ^ 2‖) :=
        ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hle)
    _ = ENNReal.ofReal (Real.sqrt ‖q (γ t)‖ * ‖deriv γ t‖) := by
        rw [sqrt_norm_mul_sq]
    _ = ENNReal.ofReal (Real.sqrt ‖q (γ t)‖) * ENNReal.ofReal ‖deriv γ t‖ :=
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ = ENNReal.ofReal (Real.sqrt ‖q (γ t)‖) * ‖deriv γ t‖₊ := by
        rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]

/-- The vertical density is dominated by the flat length density. -/
theorem verticalDensity_le (q : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    verticalDensity q γ t
      ≤ ENNReal.ofReal (Real.sqrt ‖q (γ t)‖) * ‖deriv γ t‖₊ := by
  have habs := abs_le.mp (Complex.abs_re_le_norm (q (γ t) * deriv γ t ^ 2))
  have hle : (‖q (γ t) * deriv γ t ^ 2‖ + (q (γ t) * deriv γ t ^ 2).re) / 2
      ≤ ‖q (γ t) * deriv γ t ^ 2‖ := by linarith [habs.2]
  unfold verticalDensity
  calc ENNReal.ofReal
        (Real.sqrt ((‖q (γ t) * deriv γ t ^ 2‖ + (q (γ t) * deriv γ t ^ 2).re) / 2))
      ≤ ENNReal.ofReal (Real.sqrt ‖q (γ t) * deriv γ t ^ 2‖) :=
        ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hle)
    _ = ENNReal.ofReal (Real.sqrt ‖q (γ t)‖ * ‖deriv γ t‖) := by
        rw [sqrt_norm_mul_sq]
    _ = ENNReal.ofReal (Real.sqrt ‖q (γ t)‖) * ENNReal.ofReal ‖deriv γ t‖ :=
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ = ENNReal.ofReal (Real.sqrt ‖q (γ t)‖) * ‖deriv γ t‖₊ := by
        rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]

/-- The horizontal variation of a curve is at most its flat length. -/
theorem horizontalVariation_le_qdLength (q : ℂ → ℂ) (γ : ℝ → ℂ) :
    horizontalVariation q γ ≤ qdLength q γ := by
  unfold horizontalVariation qdLength arcLengthLineIntegral
  exact lintegral_mono fun t => horizontalDensity_le q γ t

/-- The vertical variation of a curve is at most its flat length. -/
theorem verticalVariation_le_qdLength (q : ℂ → ℂ) (γ : ℝ → ℂ) :
    verticalVariation q γ ≤ qdLength q γ := by
  unfold verticalVariation qdLength arcLengthLineIntegral
  exact lintegral_mono fun t => verticalDensity_le q γ t

/-- Measurability in time of the horizontal density. -/
theorem measurable_horizontalDensity {q : ℂ → ℂ} (hq : Measurable q) {γ : ℝ → ℂ}
    (hγ : Measurable γ) : Measurable (horizontalDensity q γ) := by
  have hg : Measurable fun t => q (γ t) * deriv γ t ^ 2 :=
    (hq.comp hγ).mul ((measurable_deriv γ).pow_const 2)
  unfold horizontalDensity
  exact (((hg.norm.sub (Complex.measurable_re.comp hg)).div_const 2).sqrt).ennreal_ofReal

/-- Measurability in time of the vertical density. -/
theorem measurable_verticalDensity {q : ℂ → ℂ} (hq : Measurable q) {γ : ℝ → ℂ}
    (hγ : Measurable γ) : Measurable (verticalDensity q γ) := by
  have hg : Measurable fun t => q (γ t) * deriv γ t ^ 2 :=
    (hq.comp hγ).mul ((measurable_deriv γ).pow_const 2)
  unfold verticalDensity
  exact (((hg.norm.add (Complex.measurable_re.comp hg)).div_const 2).sqrt).ennreal_ofReal

/-! ## Deck invariance -/

/-- Unconditional `deriv` chain rule for a Möbius deck transformation postcomposed with a
curve: at non-differentiability times both sides are the junk value zero. -/
theorem deriv_moebiusMap_comp (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {γ : ℝ → ℂ} (hcont : Continuous γ) {t : ℝ} (hpos : 0 < (γ t).im) :
    deriv (moebiusMap γd ∘ γ) t = (moebiusDenom γd (γ t) ^ 2)⁻¹ * deriv γ t := by
  by_cases hdiff : DifferentiableAt ℝ γ t
  · have hm : HasDerivAt (moebiusMap γd) ((moebiusDenom γd (γ t) ^ 2)⁻¹) (γ t) :=
      hasDerivAt_moebiusMap_of_im_pos γd hpos
    have hcomp := HasDerivAt.comp (h := γ) t hm hdiff.hasDerivAt
    exact hcomp.deriv
  · have hden : moebiusDenom γd (γ t) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero γd hpos.ne'
    have h2 : ¬ DifferentiableAt ℝ (moebiusMap γd ∘ γ) t := by
      intro hc
      apply hdiff
      have hev : ∀ᶠ s in nhds t, 0 < (γ s).im :=
        (isOpen_lt continuous_const (Complex.continuous_im.comp hcont)).mem_nhds hpos
      have hden' : moebiusDenom γd⁻¹ (moebiusMap γd (γ t)) ≠ 0 := by
        intro h0
        have hmul := moebiusDenom_mul γd⁻¹ γd (γ t) hden
        rw [h0, zero_mul, inv_mul_cancel, moebiusDenom_one] at hmul
        exact zero_ne_one hmul
      have hminv : DifferentiableAt ℝ (moebiusMap γd⁻¹) ((moebiusMap γd ∘ γ) t) :=
        (differentiableAt_complex_iff_differentiableAt_real.mp
          (hasDerivAt_moebiusMap γd⁻¹ hden').differentiableAt).1
      have hcomp2 : DifferentiableAt ℝ (moebiusMap γd⁻¹ ∘ (moebiusMap γd ∘ γ)) t :=
        hminv.comp t hc
      have heq : γ =ᶠ[nhds t] moebiusMap γd⁻¹ ∘ (moebiusMap γd ∘ γ) := by
        filter_upwards [hev] with s hs
        have hdens : moebiusDenom γd (γ s) ≠ 0 :=
          moebiusDenom_ne_zero_of_im_ne_zero γd hs.ne'
        simp only [Function.comp_apply]
        rw [moebiusMap_mul γd⁻¹ γd (γ s) hdens, inv_mul_cancel, moebiusMap_one]
      exact hcomp2.congr_of_eventuallyEq heq
    rw [deriv_zero_of_not_differentiableAt hdiff, deriv_zero_of_not_differentiableAt h2,
      mul_zero]

/-- The pullback `Q(t) = q (γ t) (γ' t)²` is exactly invariant under postcomposition of the
curve with a deck transformation obeying the weight-4 law. -/
theorem pullback_moebiusMap_comp {q : ℂ → ℂ} (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γd z) = moebiusDenom γd z ^ 4 * q z)
    {γ : ℝ → ℂ} (hcont : Continuous γ) {t : ℝ} (hpos : 0 < (γ t).im) :
    q ((moebiusMap γd ∘ γ) t) * deriv (moebiusMap γd ∘ γ) t ^ 2
      = q (γ t) * deriv γ t ^ 2 := by
  have hden : moebiusDenom γd (γ t) ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γd hpos.ne'
  have hd := deriv_moebiusMap_comp γd hcont hpos
  have happ : (moebiusMap γd ∘ γ) t = moebiusMap γd (γ t) := rfl
  rw [happ, hq (γ t) hpos, hd]
  field_simp

/-- **Deck invariance of the flat length**: precomposition with a Möbius deck
transformation preserves `qdLength` for continuous absolutely continuous curves whose track
lies in the upper half plane — the density transforms by `|denom|²` and the derivative by
`|denom|⁻²`. -/
theorem qdLength_moebiusMap_comp {q : ℂ → ℂ} (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γd z) = moebiusDenom γd z ^ 4 * q z)
    {γ : ℝ → ℂ} (hcont : Continuous γ) (_hAC : AbsolutelyContinuousOnInterval γ 0 1)
    (him : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (γ t).im) :
    qdLength q (moebiusMap γd ∘ γ) = qdLength q γ := by
  simp only [qdLength, arcLengthLineIntegral]
  refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  have hpos := him t ht
  have hden : moebiusDenom γd (γ t) ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γd hpos.ne'
  have hd := deriv_moebiusMap_comp γd hcont hpos
  have happ : (moebiusMap γd ∘ γ) t = moebiusMap γd (γ t) := rfl
  have hnormpos : 0 < ‖moebiusDenom γd (γ t)‖ := norm_pos_iff.mpr hden
  have hreal : Real.sqrt ‖q (moebiusMap γd (γ t))‖ * ‖deriv (moebiusMap γd ∘ γ) t‖
      = Real.sqrt ‖q (γ t)‖ * ‖deriv γ t‖ := by
    rw [hq (γ t) hpos, hd, norm_mul, norm_pow, norm_mul, norm_inv, norm_pow,
      Real.sqrt_mul (by positivity), show ‖moebiusDenom γd (γ t)‖ ^ 4
        = (‖moebiusDenom γd (γ t)‖ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    field_simp
  rw [happ, ← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hreal,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]

/-- **Deck invariance of the horizontal variation**: the pullback `Q = q (γ t) (γ' t)²` is
exactly invariant under precomposition with a Möbius deck transformation. -/
theorem horizontalVariation_moebiusMap_comp {q : ℂ → ℂ}
    (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γd z) = moebiusDenom γd z ^ 4 * q z)
    {γ : ℝ → ℂ} (hcont : Continuous γ) (_hAC : AbsolutelyContinuousOnInterval γ 0 1)
    (him : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (γ t).im) :
    horizontalVariation q (moebiusMap γd ∘ γ) = horizontalVariation q γ := by
  simp only [horizontalVariation]
  refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  simp only [horizontalDensity]
  rw [pullback_moebiusMap_comp γd hq hcont (him t ht)]

/-- **Deck invariance of the vertical variation**. -/
theorem verticalVariation_moebiusMap_comp {q : ℂ → ℂ}
    (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γd z) = moebiusDenom γd z ^ 4 * q z)
    {γ : ℝ → ℂ} (hcont : Continuous γ) (_hAC : AbsolutelyContinuousOnInterval γ 0 1)
    (him : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (γ t).im) :
    verticalVariation q (moebiusMap γd ∘ γ) = verticalVariation q γ := by
  simp only [verticalVariation]
  refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  simp only [verticalDensity]
  rw [pullback_moebiusMap_comp γd hq hcont (him t ht)]

/-! ## The Teichmüller stretch -/

/-- `f` is a **Teichmüller `λ`-stretch** of the quadratic differential `q` on the upper
half plane: in the natural coordinates of `q`, `f` expands horizontally by `λ` and
contracts vertically by `λ⁻¹`. With `a = (λ+λ⁻¹)/2` and `b = (λ−λ⁻¹)/2`, the branch-free
encoding of `√q(f) ∂f = a √q` and `√q(f) ∂̄f = b conj √q` is the displayed pair; the
squared equation loses only the relative sign, which the mixed product recovers. -/
def IsTeichmullerStretch (q : ℂ → ℂ) (lam : ℝ) (f : ℂ → ℂ) : Prop :=
  (∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      q (f z) * dz f z ^ 2 = (((lam + lam⁻¹) / 2 : ℝ) : ℂ) ^ 2 * q z) ∧
  (∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      q (f z) * dz f z * dzbar f z
        = ((((lam + lam⁻¹) / 2) * ((lam - lam⁻¹) / 2) : ℝ) : ℂ) * (‖q z‖ : ℂ))

/-- At almost every point where `q ≠ 0`, a stretch has nonvanishing complex-linear
derivative part and its image point carries a nonzero value of `q`. -/
theorem IsTeichmullerStretch.dz_ne_zero {q : ℂ → ℂ} {lam : ℝ} {f : ℂ → ℂ}
    (hs : IsTeichmullerStretch q lam f) (hlam : 0 < lam)
    (hae : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), q z ≠ 0) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), dz f z ≠ 0 ∧ q (f z) ≠ 0 := by
  filter_upwards [hs.1, hae] with z h1 hq
  have hinv : 0 < lam⁻¹ := inv_pos.mpr hlam
  have ha : ((lam + lam⁻¹) / 2 : ℝ) ≠ 0 := by positivity
  have hne : q (f z) * dz f z ^ 2 ≠ 0 := by
    rw [h1]
    exact mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ha)) hq
  obtain ⟨hqf, hdz2⟩ := mul_ne_zero_iff.mp hne
  exact ⟨(pow_ne_zero_iff two_ne_zero).mp hdz2, hqf⟩

/-- **The Beltrami coefficient of a stretch**: dividing the two stretch equations yields
`∂̄f = k (conj q / |q|) ∂f` almost everywhere, with `k = (λ² − 1)/(λ² + 1)` — the
Teichmüller coefficient of modulus `k` in the direction of `q`. -/
theorem IsTeichmullerStretch.beltrami_eq {q : ℂ → ℂ} {lam : ℝ} {f : ℂ → ℂ}
    (hs : IsTeichmullerStretch q lam f) (hlam : 0 < lam)
    (hae : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), q z ≠ 0) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar f z
        = teichmullerCoeffFun q ((lam ^ 2 - 1) / (lam ^ 2 + 1)) z * dz f z := by
  filter_upwards [hs.1, hs.2, hs.dz_ne_zero hlam hae, hae] with z h1 h2 hnz hq
  obtain ⟨hdz, hqf⟩ := hnz
  have hNC : ((‖q z‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq)
  have hab : ((lam + lam⁻¹) / 2) * ((lam - lam⁻¹) / 2)
      = (lam ^ 2 - 1) / (lam ^ 2 + 1) * ((lam + lam⁻¹) / 2) ^ 2 := by
    have h2p : (lam ^ 2 + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  have habC : ((((lam + lam⁻¹) / 2) * ((lam - lam⁻¹) / 2) : ℝ) : ℂ)
      = (((lam ^ 2 - 1) / (lam ^ 2 + 1) : ℝ) : ℂ) * (((lam + lam⁻¹) / 2 : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast congrArg Complex.ofReal hab
  have hconj : q z * starRingEnd ℂ (q z) = ((‖q z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow]
  refine mul_left_cancel₀ (mul_ne_zero hqf hdz) ?_
  rw [h2]
  simp only [teichmullerCoeffFun]
  rw [Complex.ofReal_inv]
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have h3C : (((lam ^ 2 + 1) * (lam ^ 2 - 1) / (lam ^ 2 * 2 ^ 2) : ℝ) : ℂ)
      = (((lam + lam⁻¹) / 2 * ((lam - lam⁻¹) / 2) : ℝ) : ℂ) := by
    norm_cast
    field_simp
    ring
  field_simp
  linear_combination
    (-(((lam ^ 2 - 1) / (lam ^ 2 + 1) : ℝ) : ℂ) * starRingEnd ℂ (q z)) * h1
    - ((((lam + lam⁻¹) / 2) * ((lam - lam⁻¹) / 2) : ℝ) : ℂ) * hconj
    + (q z * starRingEnd ℂ (q z)) * habC
    + ((‖q z‖ : ℝ) : ℂ) ^ 2 * h3C

/-- A stretch has almost-everywhere constant absolute Beltrami ratio:
`‖∂̄f‖ = ((λ² − 1)/(λ² + 1)) ‖∂f‖`. -/
theorem IsTeichmullerStretch.norm_dzbar_eq {q : ℂ → ℂ} {lam : ℝ} {f : ℂ → ℂ}
    (hs : IsTeichmullerStretch q lam f) (hlam : 1 ≤ lam)
    (hae : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), q z ≠ 0) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ‖dzbar f z‖ = (lam ^ 2 - 1) / (lam ^ 2 + 1) * ‖dz f z‖ := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hk0 : 0 ≤ (lam ^ 2 - 1) / (lam ^ 2 + 1) :=
    div_nonneg (by nlinarith) (by positivity)
  filter_upwards [hs.beltrami_eq hlam0 hae, hae] with z hb hq
  rw [hb, norm_mul]
  congr 1
  simp only [teichmullerCoeffFun]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk0,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hq), mul_one]

/-! ## The pseudo-Anosov interface -/

/-- **Pseudo-Anosov data** for the re-marking `P`: a representative point `x`, a nonzero
quadratic differential on its surface, a stretch factor `λ > 1`, and a `λ`-stretch self-map
of the upper half plane normalizing `x.group` and inducing the re-marking `P` on the
boundary through the markings. -/
structure PseudoAnosovData (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (P : ModGroupUpper Γ₀) where
  /-- The representative point of the Bers model. -/
  x : TeichRep Γ₀
  /-- A quadratic differential on the surface of `x`. -/
  q : QuadraticDifferential x.group
  /-- The differential is somewhere nonzero on the upper half plane. -/
  hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0
  /-- The stretch factor. -/
  lam : ℝ
  /-- The stretch factor exceeds `1`. -/
  hlam : 1 < lam
  /-- The stretch self-map of the upper half plane. -/
  f : ℂ → ℂ
  /-- A two-sided inverse of the stretch on the upper half plane. -/
  finv : ℂ → ℂ
  /-- The stretch is quasiconformal on the upper half plane with the Teichmüller bound. -/
  hf : IsQCUpper f finv ((lam ^ 2 - 1) / (lam ^ 2 + 1))
  /-- Forward `x.group`-compatibility on the upper half plane. -/
  compat : ∀ γ ∈ x.group, ∃ γ' ∈ x.group, ∀ z : ℂ, 0 < z.im →
    f (moebiusMap γ z) = moebiusMap γ' (f z)
  /-- Backward `x.group`-compatibility on the upper half plane. -/
  compat' : ∀ γ' ∈ x.group, ∃ γ ∈ x.group, ∀ z : ℂ, 0 < z.im →
    f (moebiusMap γ z) = moebiusMap γ' (f z)
  /-- The map is a Teichmüller `λ`-stretch of the differential. -/
  stretch : IsTeichmullerStretch q lam f
  /-- `f` induces `P`: through the markings, `f` has the boundary trace of the re-marking,
  up to the Möbius renormalization of the normalized solutions. -/
  represents : ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ t : ℝ,
    moebiusDenom R ((x.smulUpper P).w t) ≠ 0 →
    Filter.Tendsto f (nhdsWithin (x.w (t : ℂ)) {z : ℂ | 0 < z.im})
      (nhds (moebiusMap R ((x.smulUpper P).w (t : ℂ))))

/-- A re-marking of the Bers model is **pseudo-Anosov** when it carries pseudo-Anosov
data: a representative with a nonzero quadratic differential, a stretch factor `λ > 1`,
and a `λ`-stretch self-map inducing it. -/
def IsPseudoAnosov (P : ModGroupUpper Γ₀) : Prop := Nonempty (PseudoAnosovData Γ₀ P)

namespace PseudoAnosovData

variable {P : ModGroupUpper Γ₀}

/-- The Teichmüller Beltrami bound of pseudo-Anosov data is nonnegative. -/
theorem kappa_nonneg (d : PseudoAnosovData Γ₀ P) :
    0 ≤ (d.lam ^ 2 - 1) / (d.lam ^ 2 + 1) := by
  have h := d.hlam
  exact div_nonneg (by nlinarith) (by positivity)

/-- The Teichmüller Beltrami bound of pseudo-Anosov data is below `1`. -/
theorem kappa_lt_one (d : PseudoAnosovData Γ₀ P) :
    (d.lam ^ 2 - 1) / (d.lam ^ 2 + 1) < 1 := by
  have h := d.hlam
  rw [div_lt_one (by positivity)]
  linarith

/-- The stretch map of pseudo-Anosov data has the Teichmüller Beltrami coefficient of its
differential almost everywhere on the upper half plane. -/
theorem beltrami_eq (d : PseudoAnosovData Γ₀ P) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar d.f z
        = teichmullerCoeffFun d.q ((d.lam ^ 2 - 1) / (d.lam ^ 2 + 1)) z * dz d.f z :=
  d.stretch.beltrami_eq (lt_trans one_pos d.hlam) (d.q.ae_ne_zero d.hq0)

end PseudoAnosovData

end RiemannDynamics

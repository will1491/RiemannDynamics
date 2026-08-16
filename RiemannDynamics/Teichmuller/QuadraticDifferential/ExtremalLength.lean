/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Foliations
import RiemannDynamics.QC.Regularity.SeparatingModulus
import RiemannDynamics.QC.LengthArea.ReverseLengthAreaForward
import RiemannDynamics.QC.LengthArea.CurveModulus

/-!
# Extremal length

The extremal length of a curve family is the reciprocal of its conformal modulus. The file
records its antitonicity, its exact values on round annuli and axis rectangles, the
reciprocity of the connecting and separating families of a round annulus, quasi-invariance
under geometrically quasiconformal maps, and the length–area inequality in the flat metric
`|q|^{1/2} |dz|` of a quadratic differential — the estimate underlying Teichmüller
uniqueness.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- The **extremal length** of a curve family: the reciprocal of its conformal modulus. -/
noncomputable def extremalLength (F : Set (ℝ → ℂ)) : ℝ≥0∞ := (curveModulus F)⁻¹

/-- Extremal length is antitone: a larger family is easier to cross, hence shorter. -/
theorem extremalLength_anti {F₁ F₂ : Set (ℝ → ℂ)} (h : F₁ ⊆ F₂) :
    extremalLength F₂ ≤ extremalLength F₁ :=
  ENNReal.inv_le_inv.mpr (curveModulus_mono h)

/-- **Extremal length of a round annulus** (connecting family): the reciprocal of the
modulus `2π / log (R/r)` is `log (R/r) / (2π)`. -/
theorem extremalLength_connectingCurveFamily_roundAnnulus {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    extremalLength (connectingCurveFamily (innerCircle z₀ r) (outerCircle z₀ R)
        (RoundAnnulus z₀ r R))
      = ENNReal.ofReal (Real.log (R / r) / (2 * Real.pi)) := by
  have hL : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hpos : 0 < 2 * Real.pi / Real.log (R / r) := by positivity
  change (ringModulus z₀ r R)⁻¹ = _
  rw [ringModulus_roundAnnulus hr hrR, ← ENNReal.ofReal_inv_of_pos hpos, inv_div]

/-- **Extremal length of an axis rectangle**: the reciprocal of the modulus
`(t − s)/(b − a)` of `[a, b] × [s, t]` is `(b − a)/(t − s)`. -/
theorem extremalLength_axisRect {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    extremalLength (axisRectQuadrilateral a b s t hab hst).curveFamily
      = ENNReal.ofReal ((b - a) / (t - s)) := by
  have hpos : 0 < (t - s) / (b - a) := div_pos (by linarith) (by linarith)
  change ((axisRectQuadrilateral a b s t hab hst).modulus)⁻¹ = _
  rw [axisRect_modulus hab hst, ← ENNReal.ofReal_inv_of_pos hpos, inv_div]

/-- **Reciprocity on a round annulus**: the extremal length of the separating family equals
the modulus of the connecting family. -/
theorem extremalLength_separatingCurveFamily_roundAnnulus {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    extremalLength (separatingCurveFamily z₀ (RoundAnnulus z₀ r R))
      = ringModulus z₀ r R := by
  have hL : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hpos : 0 < Real.log (R / r) / (2 * Real.pi) := by positivity
  change (separatingModulus z₀ r R)⁻¹ = _
  rw [separatingModulus_roundAnnulus hr hrR, ringModulus_roundAnnulus hr hrR,
    ← ENNReal.ofReal_inv_of_pos hpos, inv_div]

/-- **Quasi-invariance of extremal length**: a geometrically `K`-quasiconformal map
distorts the extremal length of a quadrilateral's curve family by at most `K`. -/
theorem extremalLength_le_of_isQCGeometric {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (Q : Quadrilateral) :
    extremalLength Q.curveFamily
      ≤ ENNReal.ofReal K * extremalLength (Q.imageCurveFamily f) := by
  have hK0 : ENNReal.ofReal K ≠ 0 := by
    have h1 : (1 : ℝ) ≤ K := hf.1
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hKtop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinv : (ENNReal.ofReal K)⁻¹ * (curveModulus Q.curveFamily)⁻¹
      ≤ (curveModulus (Q.imageCurveFamily f))⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl hK0) (Or.inl hKtop)]
    exact ENNReal.inv_le_inv.mpr (hf.2.2 Q)
  change (curveModulus Q.curveFamily)⁻¹
      ≤ ENNReal.ofReal K * (curveModulus (Q.imageCurveFamily f))⁻¹
  calc (curveModulus Q.curveFamily)⁻¹
      = ENNReal.ofReal K * ((ENNReal.ofReal K)⁻¹ * (curveModulus Q.curveFamily)⁻¹) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hK0 hKtop, one_mul]
    _ ≤ ENNReal.ofReal K * (curveModulus (Q.imageCurveFamily f))⁻¹ := by gcongr

/-! ## The length–area inequality in the flat metric of a quadratic differential -/

/-- **Length–area in the `|q|^{1/2} |dz|` metric**: if every curve of `Δ` stays in `S` and
has flat length at least `L`, then the modulus of `Δ` is at most the flat area of `S`
divided by `L²` — the test density is `|q|^{1/2}` cut off to `S`. -/
theorem curveModulus_le_qdArea_div_sq {q : ℂ → ℂ} (hq : Measurable q) {S : Set ℂ}
    (hS : MeasurableSet S) {Δ : Set (ℝ → ℂ)} {L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (hΔ : ∀ γ ∈ Δ, (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ S) ∧ L ≤ qdLength q γ) :
    curveModulus Δ ≤ (∫⁻ z in S, ‖q z‖ₑ) / L ^ 2 := by
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt ‖q z‖) with hf
  set ρ₀ : ℂ → ℝ≥0∞ := S.indicator f with hρ₀
  have hfmeas : Measurable f :=
    ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hq.norm)
  have hρ₀meas : Measurable ρ₀ := hfmeas.indicator hS
  -- The cut-off density has the same line integral as the flat length along curves of `Δ`.
  have hline : ∀ γ ∈ Δ, L ≤ arcLengthLineIntegral ρ₀ γ := by
    intro γ hγ
    have heq : arcLengthLineIntegral ρ₀ γ = qdLength q γ := by
      change arcLengthLineIntegral ρ₀ γ = arcLengthLineIntegral f γ
      unfold arcLengthLineIntegral
      refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
      rw [hρ₀, Set.indicator_of_mem ((hΔ γ hγ).1 t ht)]
    rw [heq]; exact (hΔ γ hγ).2
  -- The energy of the cut-off density is exactly the flat area of `S`.
  have henergy : (∫⁻ z, (ρ₀ z) ^ 2) = ∫⁻ z in S, ‖q z‖ₑ := by
    have hpt : (fun z => (ρ₀ z) ^ 2) = S.indicator fun z => ‖q z‖ₑ := by
      funext z
      by_cases hz : z ∈ S
      · rw [hρ₀, Set.indicator_of_mem hz, Set.indicator_of_mem hz, hf,
          ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _),
          ofReal_norm]
      · rw [hρ₀, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        exact zero_pow two_ne_zero
    rw [hpt, lintegral_indicator hS]
  calc curveModulus Δ
      ≤ (∫⁻ z, (ρ₀ z) ^ 2) / L ^ 2 :=
        curveModulus_le_of_lintegralSq_finite_of_lineIntegral_ge hρ₀meas hL hLtop hline
    _ = (∫⁻ z in S, ‖q z‖ₑ) / L ^ 2 := by rw [henergy]

/-- Reciprocal form of `curveModulus_le_qdArea_div_sq`: the extremal length of `Δ` is at
least the squared flat length divided by the flat area. -/
theorem le_extremalLength_of_qdLength {q : ℂ → ℂ} (hq : Measurable q) {S : Set ℂ}
    (hS : MeasurableSet S) {Δ : Set (ℝ → ℂ)} {L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (hΔ : ∀ γ ∈ Δ, (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ S) ∧ L ≤ qdLength q γ) :
    L ^ 2 / ∫⁻ z in S, ‖q z‖ₑ ≤ extremalLength Δ := by
  have h := curveModulus_le_qdArea_div_sq hq hS hL hLtop hΔ
  have hL2ne : L ^ 2 ≠ 0 := pow_ne_zero 2 hL.ne'
  have hL2top : L ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hLtop
  calc L ^ 2 / ∫⁻ z in S, ‖q z‖ₑ
      = ((∫⁻ z in S, ‖q z‖ₑ) / L ^ 2)⁻¹ :=
        (ENNReal.inv_div (Or.inl hL2top) (Or.inl hL2ne)).symm
    _ ≤ (curveModulus Δ)⁻¹ := ENNReal.inv_le_inv.mpr h
    _ = extremalLength Δ := rfl

end RiemannDynamics

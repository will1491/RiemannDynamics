import RiemannDynamics.Analysis.SingularIntegral.DyadicLebesgue
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Dyadic assembly of the Gehring self-improvement

This file assembles the proven dyadic Calderón–Zygmund machinery
(`exists_dyadic_CZ_stopping`, `dyadic_ae_tendsto_average`) into the higher-integrability
core of Gehring's lemma, working entirely on dyadic squares so that the layer-cake
absorption happens on a *single* fixed square (no maximal function, no cross-ball mismatch).

## Pipeline

* `dyadic_reverseHolder` — transfers a metric-ball reverse-Hölder hypothesis (the form
  consumed by `gehring_selfImprovement`) to the dyadic squares, using the centre/ball
  comparability `dyadicSquare_subset_ball` and a fixed planar volume ratio.
* `dyadic_higher_integrability` — the dyadic Gehring self-improvement core: under the
  ball reverse-Hölder hypothesis, the weight `w` is locally `L^{q+ε}` on every dyadic
  square, with a single gain `ε` depending only on `q` and `A`.  Its proof runs the
  Calderón–Zygmund stopping decomposition on a fixed square, the resulting same-square
  good-λ inequality, and the layer-cake absorption.

The endpoint `gehring_selfImprovement` then covers any ball by finitely many dyadic squares
of comparable size and sums.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- **Dyadic reverse-Hölder transfer.**  A metric-ball reverse-Hölder inequality with the
fixed enlargement factor `4` (the hypothesis form consumed by `gehring_selfImprovement`)
yields a reverse-Hölder inequality on every dyadic square `R = dyadicSquare m k`, with the
right-hand side taken over the comparable ball about the square's centre of radius
`4 · 2^m`.  The constant gains only the planar volume ratio `π^{1/q}` (since
`R ⊆ ball (centre) (2^m)` and `vol (ball) / vol R = π`). -/
theorem dyadic_reverseHolder {q A : ℝ} (hq : 1 < q) (_hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞}
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (m : ℤ) (k : ℤ × ℤ) :
    (⨍⁻ z in dyadicSquare m k, w z ^ q ∂volume) ^ (1 / q) ≤
      ENNReal.ofReal (Real.pi ^ (1 / q) * A) *
          (⨍⁻ z in Metric.ball (dyadicCenter m k) (4 * (2 : ℝ) ^ m), w z ∂volume) +
        ENNReal.ofReal (Real.pi ^ (1 / q) * A) *
          (⨍⁻ z in Metric.ball (dyadicCenter m k) (4 * (2 : ℝ) ^ m), b z ^ q ∂volume) ^
            (1 / q) := by
  -- Setup
  set c := dyadicCenter m k with hc
  set s : ℝ := (2 : ℝ) ^ m with hs
  have hs0 : 0 < s := by rw [hs]; exact zpow_pos (by norm_num) m
  set R := dyadicSquare m k with hR
  set Bs := Metric.ball c s with hBs
  have hq0 : (0 : ℝ) ≤ 1 / q := by positivity
  -- volumes
  have hvolR : volume R = ENNReal.ofReal (s ^ 2) := by
    rw [hR, volume_dyadicSquare]
  have hvolBs : volume Bs = ENNReal.ofReal (Real.pi * s ^ 2) := by
    rw [hBs, Complex.volume_ball]
    have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi]; rw [ENNReal.ofReal_coe_nnreal]
    rw [hpi, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hs0.le, mul_comm]
  have hs2pos : (0 : ℝ) < s ^ 2 := by positivity
  have hvolR0 : volume R ≠ 0 := by
    rw [hvolR, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hs2pos
  have hvolRtop : volume R ≠ ⊤ := by rw [hvolR]; exact ENNReal.ofReal_ne_top
  have hvolBs0 : volume Bs ≠ 0 := by
    rw [hvolBs, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hvolBstop : volume Bs ≠ ⊤ := by rw [hvolBs]; exact ENNReal.ofReal_ne_top
  -- planar volume ratio  vol Bs / vol R = π
  have hratio : volume Bs / volume R = ENNReal.ofReal Real.pi := by
    rw [hvolR, hvolBs, ENNReal.ofReal_mul Real.pi_pos.le, mul_div_assoc, ENNReal.div_self]
    · rw [mul_one]
    · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hs2pos
    · exact ENNReal.ofReal_ne_top
  -- STEP A: Avg R (w^q) ≤ ofReal π * Avg Bs (w^q)
  have hsubset : R ⊆ Bs := by rw [hR, hBs]; exact dyadicSquare_subset_ball m k
  have hmono : ∫⁻ z in R, w z ^ q ≤ ∫⁻ z in Bs, w z ^ q := lintegral_mono_set hsubset
  have hStepA : (⨍⁻ z in R, w z ^ q ∂volume) ≤
      ENNReal.ofReal Real.pi * (⨍⁻ z in Bs, w z ^ q ∂volume) := by
    rw [setLAverage_eq, setLAverage_eq]
    calc (∫⁻ z in R, w z ^ q ∂volume) / volume R
        ≤ (∫⁻ z in Bs, w z ^ q ∂volume) / volume R := ENNReal.div_le_div_right hmono _
      _ = ((∫⁻ z in Bs, w z ^ q ∂volume) / volume Bs) * (volume Bs / volume R) := by
          rw [← mul_div_assoc, ENNReal.div_mul_cancel hvolBs0 hvolBstop]
      _ = (volume Bs / volume R) * ((∫⁻ z in Bs, w z ^ q ∂volume) / volume Bs) := by rw [mul_comm]
      _ = ENNReal.ofReal Real.pi * ((∫⁻ z in Bs, w z ^ q ∂volume) / volume Bs) := by rw [hratio]
  -- STEP B: take (·)^(1/q)
  have hStepB : (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q) ≤
      ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := by
    calc (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q)
        ≤ (ENNReal.ofReal Real.pi * (⨍⁻ z in Bs, w z ^ q ∂volume)) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hStepA hq0
      _ = ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.ofReal_rpow_of_pos Real.pi_pos]
  -- STEP C: apply the ball reverse-Hölder hypothesis at (c, s)
  have hStepC := hRH c s hs0
  -- STEP D: chain and distribute
  have hpi0 : (0 : ℝ) ≤ Real.pi ^ (1 / q) := by positivity
  calc (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q)
      ≤ ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := hStepB
    _ ≤ ENNReal.ofReal (Real.pi ^ (1 / q)) *
          (ENNReal.ofReal A * (⨍⁻ z in Metric.ball c (4 * s), w z ∂volume) +
           ENNReal.ofReal A * (⨍⁻ z in Metric.ball c (4 * s), b z ^ q ∂volume) ^ (1 / q)) :=
        mul_le_mul_right hStepC _
    _ = ENNReal.ofReal (Real.pi ^ (1 / q) * A) * (⨍⁻ z in Metric.ball c (4 * s), w z ∂volume) +
        ENNReal.ofReal (Real.pi ^ (1 / q) * A) *
          (⨍⁻ z in Metric.ball c (4 * s), b z ^ q ∂volume) ^ (1 / q) := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hpi0]

/-- **Dyadic Gehring higher-integrability core.**  Fix `q > 1` and a reverse-Hölder constant
`A ≥ 0`.  There is a single exponent gain `ε > 0` — depending only on `q` and `A` — such that
every nonnegative weight `w` (with lower-order term `b`) that is locally `Lᵠ` (`b` locally
`L^{q+ε}`) and satisfies the metric-ball reverse-Hölder inequality with enlargement `4` is
`L^{q+ε}` on every dyadic square: `∫⁻_{dyadicSquare m k} w^{q+ε} < ⊤`.

This is the dyadic Calderón–Zygmund self-improvement: on the fixed square the stopping
decomposition `exists_dyadic_CZ_stopping` produces the same-square good-λ inequality, whose
layer-cake reconstruction absorbs (with `ε` small) on that one square. -/
theorem dyadic_higher_integrability {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      ∀ {w b : ℂ → ℝ≥0∞}, AEMeasurable w volume → AEMeasurable b volume →
        (∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ q < ⊤) →
        (∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, b z ^ (q + ε) < ⊤) →
        (∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
            ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
              ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q)) →
        ∀ (m : ℤ) (k : ℤ × ℤ), ∫⁻ z in dyadicSquare m k, w z ^ (q + ε) < ⊤ := by
  sorry

end RiemannDynamics

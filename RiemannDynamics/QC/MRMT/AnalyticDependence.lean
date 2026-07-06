/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.MRMT.NeumannSeries

/-!
# Holomorphic dependence of the principal solution on the coefficient

Along the complex one-parameter family `t ↦ t·μ` of Beltrami coefficients, the
principal solutions depend holomorphically on `t`: for each point `z`, the map
`t ↦ f^{t·μ}(z)` is analytic on the parameter region `{t | ‖t‖·‖μ‖∞ < 1}`.

This is read off the Neumann series: the fixed point of `u ↦ t·μ·S u + t·μ` is the
power series `h_t = ∑ₙ t^{n+1}·(μ·S)^n μ` in `Lᵖ`, and pairing with the Cauchy
kernel at `z` — a bounded functional on the compactly vanishing fields — produces a
convergent power series for `f^{t·μ}(z) − z`. Around a parameter `t₀` with
`‖t₀‖·‖μ‖∞ < 1` an exponent `p(t₀)` with a contraction margin covers a neighborhood,
and the local series glue by uniqueness of principal solutions.

This is the interface consumed (through the normalized-solution wrapper of the
uniqueness file) by the no-wandering-domains argument and the Teichmüller theory:
holomorphic motions of solutions along holomorphic families of coefficients.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- **Scaling a Beltrami coefficient** along the complex parameter `t`, on the
region `‖t‖·‖μ‖∞ < 1` where the scaled coefficient is again admissible. -/
noncomputable def BeltramiCoeff.scale (b : BeltramiCoeff) (t : ℂ)
    (ht : ‖t‖ * b.normInf < 1) : BeltramiCoeff where
  μ := fun z => t * b.μ z
  measurable := measurable_const.mul b.measurable
  bound := by
    have hne : eLpNormEssSup b.μ volume ≠ ⊤ := b.bound.trans_le le_top |>.ne
    have hself : eLpNormEssSup b.μ volume = ENNReal.ofReal b.normInf := by
      rw [BeltramiCoeff.normInf, ENNReal.ofReal_toReal hne]
    have hsmul : (fun z => t * b.μ z) = fun z => t • b.μ z := by
      funext z; simp [smul_eq_mul]
    calc eLpNormEssSup (fun z => t * b.μ z) volume
        = eLpNormEssSup (fun z => t • b.μ z) volume := by rw [hsmul]
      _ = ‖t‖ₑ * eLpNormEssSup b.μ volume := by
          rw [show (fun z => t • b.μ z) = t • b.μ from rfl,
            MeasureTheory.eLpNormEssSup_const_smul]
      _ = ENNReal.ofReal ‖t‖ * ENNReal.ofReal b.normInf := by
          rw [hself, ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal (‖t‖ * b.normInf) :=
          (ENNReal.ofReal_mul (norm_nonneg t)).symm
      _ < 1 := ENNReal.ofReal_lt_one.mpr ht

/-- The coefficient of `BeltramiCoeff.scale` is the pointwise scaling. -/
theorem BeltramiCoeff.scale_μ (b : BeltramiCoeff) (t : ℂ) (ht : ‖t‖ * b.normInf < 1) :
    (b.scale t ht).μ = fun z => t * b.μ z := rfl

/-- **Holomorphic dependence of the principal solution on the parameter.** For a
compactly vanishing coefficient `b`, there is a family `F` of principal solutions
of the scaled coefficients `t·μ`, defined on the region `‖t‖·‖μ‖∞ < 1`, such that
for every point `z` the evaluation `t ↦ F t z` is analytic on that region. -/
theorem mrmt_holomorphic_dependence_principal (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ F : ℂ → ℂ → ℂ,
      (∀ (t : ℂ) (ht : ‖t‖ * b.normInf < 1),
        IsPrincipalSolution (b.scale t ht) (F t)) ∧
      ∀ z : ℂ, AnalyticOnNhd ℂ (fun t => F t z) {t : ℂ | ‖t‖ * b.normInf < 1} := by
  sorry

end RiemannDynamics

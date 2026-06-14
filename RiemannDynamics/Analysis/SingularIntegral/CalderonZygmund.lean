/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Carleson.ToMathlib.RealInterpolation.Main

/-!
# Calderón–Zygmund `Lᵖ` bounds

The predicate `IsCalderonZygmundBound T p C` records that a singular-integral
operator `T : (ℂ → ℂ) → (ℂ → ℂ)` is bounded `Lᵖ(ℂ) → Lᵖ(ℂ)` with constant `C`:

`‖T f‖_p ≤ C · ‖f‖_p`   for every `f`.

The file's substantive content is the **Marcinkiewicz interpolation bridge**
`isCalderonZygmundBound_of_hasWeakType`: a subadditive operator that is weak-(1,1)
and weak-(2,2) is bounded on `Lᵖ` for every `1 < p < 2`. It is the abstract,
kernel-free node through which the Beurling transform's `Lᵖ` bound factors — the
Beurling-specific input (the kernel satisfies the Calderón–Zygmund hypotheses,
giving weak-(1,1) via the Carleson project's `czOperator_weak_1_1`, together with
the `L²` isometry) feeds this bridge in `Analysis/SingularIntegral/Beurling.lean`.
The proof routes through the Carleson real-interpolation theorem
`MeasureTheory.exists_hasStrongType_real_interpolation`.

This is the qualitative form the measurable Riemann mapping theorem consumes for
the Beurling transform: a constant `C_p` for every `1 < p < ∞`, continuous in
`p`, with `C_2 = 1`, so that the Neumann series `∑ (μ T)ⁿ μ` converges in `Lᵖ`
for `‖μ‖∞ < 1` and `p` near `2`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- A singular-integral operator `T` on `ℂ` satisfies a **Calderón–Zygmund `Lᵖ`
bound** with constant `C` if `‖T f‖_p ≤ C ‖f‖_p` for every `Lᵖ` function `f`
(the bound is asserted on `MemLp f p volume`, the class the Neumann series
consumes; an unrestricted `∀ f` would overreach to non-measurable functions). -/
def IsCalderonZygmundBound (T : (ℂ → ℂ) → ℂ → ℂ) (p : ℝ≥0∞) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f : ℂ → ℂ, MemLp f p volume →
    eLpNorm (T f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume

/-- **Marcinkiewicz interpolation bridge.** A subadditive operator on `ℂ` that is
weak-(1,1) and weak-(2,2) is bounded on `Lᵖ(ℂ)` for every `1 < p < 2` — the
abstract Calderón–Zygmund `Lᵖ` step, obtained from the two endpoint weak-type
bounds by real interpolation (`MeasureTheory.exists_hasStrongType_real_interpolation`).
The Beurling transform feeds its kernel-derived weak-(1,1) bound and `L²` isometry
into this node; the range `p > 2` then follows by duality. -/
theorem isCalderonZygmundBound_of_hasWeakType
    {T : (ℂ → ℂ) → ℂ → ℂ} {p : ℝ≥0∞} (hp₁ : 1 < p) (hp₂ : p < 2)
    {A C₁ C₂ : ℝ≥0} (hA : 1 ≤ A) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hmeas : ∀ f : ℂ → ℂ, MemLp f p volume → AEStronglyMeasurable (T f) volume)
    (hsub : AESubadditiveOn T (fun f : ℂ → ℂ => MemLp f 1 volume ∨ MemLp f 2 volume) A volume)
    (hweak₁ : HasWeakType T 1 1 volume volume C₁)
    (hweak₂ : HasWeakType T 2 2 volume volume C₂) :
    ∃ C : ℝ, IsCalderonZygmundBound T p C := by
  -- interpolation parameter
  set t : ℝ≥0∞ := 2 * (1 - p⁻¹) with ht_def
  -- basic facts about p
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp₁ (by simp)
  have hpinv_lt1 : p⁻¹ < 1 := by rw [ENNReal.inv_lt_one]; exact hp₁
  have hhalf_lt : (2:ℝ≥0∞)⁻¹ < p⁻¹ := by rw [ENNReal.inv_lt_inv]; exact hp₂
  have hpinv_ne_top : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hp0
  have h2mulinv : (2:ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  -- 1 - p⁻¹ < 2⁻¹, proved by adding p⁻¹ to both sides
  have h2 : (1:ℝ≥0∞) - p⁻¹ < 2⁻¹ := by
    have htwo_inv_ne : (2:ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    have hadd : (1:ℝ≥0∞) - p⁻¹ + p⁻¹ < 2⁻¹ + p⁻¹ := by
      rw [tsub_add_cancel_of_le hpinv_lt1.le]
      calc (1:ℝ≥0∞) = 2⁻¹ + 2⁻¹ := (ENNReal.inv_two_add_inv_two).symm
        _ < 2⁻¹ + p⁻¹ := by
          rw [ENNReal.add_lt_add_iff_left htwo_inv_ne]; exact hhalf_lt
    exact lt_of_add_lt_add_right hadd
  -- ht : t ∈ Ioo 0 1
  have ht : t ∈ Ioo (0:ℝ≥0∞) 1 := by
    constructor
    · have : 0 < 1 - p⁻¹ := tsub_pos_of_lt hpinv_lt1
      rw [ht_def]; positivity
    · rw [ht_def]
      calc 2 * (1 - p⁻¹) < 2 * 2⁻¹ := by gcongr; simp
        _ = 1 := h2mulinv
  -- hp : p⁻¹ = (1 - t)/1 + t/2
  have h2pinv : (1:ℝ≥0∞) ≤ 2 * p⁻¹ := by
    calc (1:ℝ≥0∞) = 2 * 2⁻¹ := h2mulinv.symm
      _ ≤ 2 * p⁻¹ := by gcongr
  have hp : p⁻¹ = (1 - t) / 1 + t / 2 := by
    rw [ht_def, div_one]
    -- goal: p⁻¹ = (1 - 2*(1 - p⁻¹)) + (2*(1 - p⁻¹)) / 2
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
  -- side conditions for the interpolation endpoints
  have hp0' : (1:ℝ≥0∞) ∈ Ioc 0 1 := by constructor <;> simp
  have hp1' : (2:ℝ≥0∞) ∈ Ioc 0 2 := by constructor <;> simp
  have hq0q1 : (1:ℝ≥0∞) ≠ 2 := by norm_num
  -- apply the Carleson real-interpolation theorem
  have hST : HasStrongType T p p volume volume
      (C_realInterpolation 1 2 1 2 p C₁ C₂ A t) :=
    exists_hasStrongType_real_interpolation hp0' hp1' hq0q1 hA ht hC₁ hC₂ hp hp
      hmeas hsub hweak₁ hweak₂
  set c : ℝ≥0 := C_realInterpolation 1 2 1 2 p C₁ C₂ A t with hc_def
  refine ⟨(c : ℝ), NNReal.coe_nonneg c, fun f hf => ?_⟩
  have hbound := (hST f hf).2
  -- hbound : eLpNorm (T f) p volume ≤ ↑c * eLpNorm f p volume
  rw [show ENNReal.ofReal (c : ℝ) = (c : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal]
  exact hbound

end RiemannDynamics

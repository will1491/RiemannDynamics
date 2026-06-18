/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import RiemannDynamics.Analysis.Sobolev.Mollification
import RiemannDynamics.Analysis.SingularIntegral.CalderonZygmund
import RiemannDynamics.Analysis.SingularIntegral.Beurling.Kernel
import RiemannDynamics.Analysis.SingularIntegral.Beurling.Convolution
import Carleson.ToMathlib.HardyLittlewood
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.UniformIntegrable
import RiemannDynamics.Analysis.SingularIntegral.DyadicLebesgue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The Gehring reverse-Hölder self-improvement

This file proves the **higher-integrability residual** of Bojarski's theorem: an
`L²` Beltrami fixed point `G = h + T(μ·G)` with `‖μ‖∞ < 1` is automatically locally
`Lᵠ` for some `q > 2`, with *no* `Lᵖ` hypothesis on the inhomogeneity `h`. Classically
this is the **Gehring reverse-Hölder / Caccioppoli self-improvement lemma**.

## The f-level reverse-Hölder

The reverse-Hölder gain cannot be derived from the bare fixed-point equation
`G = h + T(μ·G)` alone: the `L² ⟹ L¹` reverse-Hölder gain is a *Sobolev–Poincaré*
phenomenon on the **primitive** `F` of which `G` is the weak holomorphic gradient
(`G = ∂F`). The reverse-Hölder node is therefore stated at the **`f`-level**: it takes the
primitive bundle `(F, Gx, Gy)` (which L5 `dz_cutoff_eq_beurling_repr` constructs and hands
back), and reduces to two analytic nodes — a Sobolev–Poincaré inequality on balls and an
`f`-level Caccioppoli inequality obtained by weak integration by parts against the test
function `χ²(F − F_B)`.

The development is decomposed into the following dependency-ordered nodes:

* **S0** `memLpLocOn_two_of_memLp_two` — trivial packaging `L² ⟹ L²_loc`.
* **N1** `sobolevPoincare_ball` — Sobolev–Poincaré on a ball for a `W^{1,2}` primitive
  `F` with weak gradient `(Gx, Gy)`: the `L²`-oscillation of `F` on a ball is bounded by
  `r` times the `L¹`-average of `‖∇F‖`.
* **N2** `weakIBP_against_W12` — weak integration by parts admitting a `W^{1,2}` compactly
  supported test function (not just `C^∞`), e.g. `φ = χ²(F − c)`.
* **N3** `caccioppoli_of_beltrami` — the `f`-level Caccioppoli inequality: the gradient
  energy `⨍⁻_B ‖G‖²` is bounded by `r⁻²·⨍⁻_{2B}‖F − F_B‖² + ‖h‖`-terms, by testing the
  Beltrami structure against `χ²(F − F_B)` via N2.
* **S1** `reverseHolder_of_weakGradient` — the **`f`-level reverse-Hölder** inequality on
  every ball, derived from N3 (Caccioppoli) + N1 (Sobolev–Poincaré): the `r⁻¹` from
  Caccioppoli cancels the `r` from Sobolev–Poincaré, yielding a scale-invariant constant
  `A`.
* **S2** `gehring_selfImprovement` — the **general, equation-agnostic** Gehring lemma:
  a nonnegative locally-`Lᵠ` weight satisfying a reverse-Hölder inequality on all balls
  (with a controlled lower-order term) is locally `L^{q+ε}` for some `ε > 0`.
* **S3** `beltrami_fixedPoint_memLpLocOn` — the restated residual: assemble S0 + S1 + S2
  to upgrade an `L²` Beltrami fixed point (carrying its primitive bundle) to `Lᵠ_loc`,
  `q > 2`.

## Infrastructure consumed by N1 (the Sobolev–Poincaré proof)

The Sobolev–Poincaré node `sobolevPoincare_ball` is discharged by mollifying
the primitive `F` to `C¹` (`RiemannDynamics.exists_contDiff_hasCompactSupport_eLpNorm_sub_le`,
`Analysis/Sobolev/Mollification.lean`) and applying Mathlib's Gagliardo–Nirenberg–Sobolev
inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`
(`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`) at `n = finrank ℝ ℂ = 2`,
`p = 2` (the Hölder conjugate of `2`), to the mean-subtracted localized function, then
passing the weak gradient `(Gx, Gy)` to the Fréchet derivative in the `L¹` limit.

## Infrastructure consumed by S2 (the Gehring proof)

The general self-improvement node `gehring_selfImprovement` is discharged
using the **Hardy–Littlewood maximal function stack from the Carleson library**
(`Carleson.ToMathlib.HardyLittlewood`):

* `MeasureTheory.maximalFunction` / `MeasureTheory.MB` — the (centered, ball-averaged)
  maximal operator over a countable family of balls.
* `MeasureTheory.HasWeakType.MB_one` — the weak-(1,1) endpoint of `MB`.
* `MeasureTheory.hasStrongType_MB` — the strong-(p,p) bound for `1 < p`.
* the Vitali covering `Vitali.exists_disjoint_subfamily_covering_enlargement_ball` and
  `Set.Countable.measure_biUnion_le_lintegral` for the good-λ / stopping-time decomposition,

together with Mathlib's **layer-cake** representation
(`MeasureTheory.lintegral_eq_lintegral_meas_lt`, `Mathlib.MeasureTheory.Integral.Layercake`)
and the average notation `⨍⁻` (`MeasureTheory.laverage`,
`Mathlib.MeasureTheory.Integral.Average`). All of these are importable from this file
(the Carleson maximal stack is already a dependency, see `Beurling/Kernel.lean`).

All nodes (N1, N2, N3, S0, S1, S2, S3) are proved here, so the downstream consumer
`beltrami_fixedPoint_memLpLocOn_of_memLp_two` (in `Beurling/Beltrami.lean`) is fully
discharged.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace RiemannDynamics

/-! ## S0 — `L²` ⟹ `L²_loc` -/

/-- **S0.** A globally-`L²` function is locally `L²` on `Set.univ`: restrict to every
compact `K`. Trivial packaging used as the base case of the Gehring iteration. -/
theorem memLpLocOn_two_of_memLp_two {G : ℂ → ℂ} (hG : MemLp G 2 volume) :
    MemLpLocOn G 2 Set.univ :=
  fun K _ _ => hG.restrict K

/-! ## N1 sub-stack — gradient comparison and the superseded Riesz auxiliaries

The honest source of the `L² → L¹` reverse-Hölder gain. The averages are the `ℝ≥0∞`-valued
lower-integral averages `⨍⁻ … = (vol B)⁻¹ ∫⁻ …`. We write the gradient norm of the
primitive `F` (whose weak partials are `Gx, Gy`) directly via the weak holomorphic Wirtinger
derivative `G = ½(Gx − I·Gy)`: classically `‖∇F‖` is comparable to `‖G‖` for a `W^{1,2}`
primitive whose `∂̄`-part is controlled, and the Sobolev–Poincaré constant absorbs the
comparison constant.

`sobolevPoincare_ball` (N1) is proved via the genuine planar endpoint Sobolev embedding
`W^{1,1}(ℝ²) ↪ L²(ℝ²)` (Mathlib `eLpNorm_le_eLpNorm_fderiv_one`) through a cutoff and
`W^{1,1}` mollification — the **P-stack** developed below. The Riesz-potential / fractional
-integration auxiliaries that follow (`rieszPotential_pointwise_le_maximal`,
`hasWeakType_rieszPotential_one_two`) are true planar facts about the order-`1` Riesz
potential `I₁`, but they are not on the N1 path: the strong `I₁ : L¹ → L²` endpoint they
would feed is the EXCLUDED Hardy–Littlewood–Sobolev endpoint and is false, so the P-stack
replaces it. -/

/-- **R2 (`eLpNorm_rieszPotential_one_le`).** The **Hardy–Littlewood–Sobolev fractional
integration bound** `I₁ : L¹(ℝ²) → L²(ℝ²)` for the planar Riesz potential, in lower-integral
form.

There is a *dimensional* constant `C_H ≥ 0` such that for every nonnegative measurable
density `g : ℂ → ℝ≥0∞` and every ball `B = ball x ρ`, the `L²`-norm over `B` of the Riesz
potential `I₁ g := ∫⁻_B g y / ‖· − y‖` is controlled by the `L¹`-norm of `g` over `B`:
`(∫⁻ z in B, (∫⁻ y in B, g y / ‖z − y‖ ∂volume)² ∂volume)^(1/2) ≤ C_H · ∫⁻ y in B, g y ∂volume`.

This is the genuine `L¹ → L²` *strong*-type bound for the fractional integral `I₁` of order
`1` in dimension `n = 2` (so `1/2 = 1/1 − 1/n`, the HLS exponent at the `L¹` endpoint). The
constant `C_H` is **independent of `g`, `x`, and `ρ`**.

*Derivation.* The kernel `1/‖·‖ ∉ L²(ℝ²)`, so Young's inequality fails and one
argues by **real (Marcinkiewicz) interpolation**: split the kernel at radius `δ` into a
local part (bounded by `δ · MB g`, the Hardy–Littlewood maximal function
`MeasureTheory.MB` of `g`) and a tail part (bounded pointwise by `δ⁻¹ · ‖g‖₁`).
Optimizing in `δ` gives the *weak*-(1,2) bound `‖I₁ g‖_{2,∞} ≲ ‖g‖₁`; the strong `L¹ → L²`
bound on a ball then follows from this weak-(1,2) endpoint together with the trivial
`L^∞`-localization, via the Marcinkiewicz bridge
(`RiemannDynamics.isCalderonZygmundBound_of_hasWeakType` /
`MeasureTheory.exists_hasStrongType_real_interpolation`) and the maximal-function endpoints
`MeasureTheory.HasWeakType.MB_one`, `MeasureTheory.hasStrongType_MB`. -/
-- The `ℂ = ℝ²` doubling datum (`defaultA 4`) consumed by the Hardy–Littlewood maximal
-- function `globalMaximalFunction volume 1`. This is the `IsDoubling` projection of the
-- `DoublingMeasure ℂ (defaultA 4)` instance from `Beurling/Kernel.lean`; instance
-- resolution does not register the `extends`-projection automatically, so we expose it.
private instance instIsDoublingComplexDefaultA4 :
    (volume : Measure ℂ).IsDoubling ((defaultA 4 : ℕ) : ℝ≥0) :=
  doublingMeasure_complex_defaultA4.toIsDoubling

/-- The Hardy–Littlewood maximal function of an `ℝ≥0∞`-valued density `g`, *localized to the
ball* `ball x ρ`, realized through the Carleson `globalMaximalFunction` applied to the real
representative `((ball x ρ).indicator g ·).toReal`. The localization is essential: the
weak-(1,1) bound for the maximal function controls the *global* `L¹` mass of its argument, and
restricting to the ball makes that mass equal to the ball mass `∫_B g`. When `g` is
finite-valued the enorm of this representative is `(ball x ρ).indicator g` itself, so the local
averages of `g` over sub-balls are dominated by `rieszMaximal g x ρ`. -/
private noncomputable def rieszMaximal (g : ℂ → ℝ≥0∞) (x : ℂ) (ρ : ℝ) (z : ℂ) : ℝ≥0∞ :=
  globalMaximalFunction (X := ℂ) (E := ℝ) (A := ((defaultA 4 : ℕ) : ℝ≥0)) volume 1
    (fun y => ((Metric.ball x ρ).indicator g y).toReal) z

/-- The **weak-(1,1) level-set bound** for the localized maximal function `rieszMaximal g x ρ`,
with the `L¹` mass expressed as the ball mass `∫_B g`. This is the projection of the Carleson
maximal-function weak-(1,1) endpoint `hasWeakType_globalMaximalFunction` to the `distribution`
(super-level-set) formulation, with the global `L¹` norm of the indicator representative
identified with `∫_B g` (using that `g` is finite-valued on `B`). -/
private theorem rieszMaximal_weak_1_1 (g : ℂ → ℝ≥0∞) (hgfin : ∀ y, g y ≠ ⊤)
    (hgmeas : AEMeasurable g volume) (x : ℂ) (ρ : ℝ)
    (hIfin : (∫⁻ y in Metric.ball x ρ, g y ∂volume) ≠ ⊤) (s : ℝ≥0) :
    (s : ℝ≥0∞) * volume {z | (s : ℝ≥0∞) < rieszMaximal g x ρ z}
      ≤ (C_weakType_globalMaximalFunction ((defaultA 4 : ℕ) : ℝ≥0) 1 1)
          * ∫⁻ y in Metric.ball x ρ, g y ∂volume := by
  set u : ℂ → ℝ := fun y => ((Metric.ball x ρ).indicator g y).toReal with hu_def
  -- The global `L¹` norm of `u` is the ball mass of `g`.
  have hL1 : eLpNorm u 1 volume = ∫⁻ y in Metric.ball x ρ, g y ∂volume := by
    rw [hu_def, eLpNorm_one_eq_lintegral_enorm, ← lintegral_indicator measurableSet_ball]
    congr 1; ext y; simp only [Set.indicator]; split_ifs with h
    · rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (hgfin y)]
    · simp
  have humem : MemLp u 1 volume :=
    ⟨(hgmeas.indicator measurableSet_ball).ennreal_toReal.aestronglyMeasurable,
      hL1 ▸ lt_of_le_of_ne le_top hIfin⟩
  -- Unfold the weak-(1,1) endpoint of the global maximal function into a level-set bound.
  have hwt := (hasWeakType_globalMaximalFunction (μ := volume) (E := ℝ)
    (A := ((defaultA 4 : ℕ) : ℝ≥0)) (p₁ := 1) (p₂ := 1) (by norm_num) le_rfl u humem).2
  rw [wnorm, if_neg (by norm_num), wnorm', iSup_le_iff] at hwt
  have hkey := hwt s
  rw [distribution] at hkey
  simp only [enorm_eq_self] at hkey
  norm_num at hkey
  rw [hL1] at hkey
  exact hkey

-- Helper: integral of the indicator over ball z r is at most  π r² · M.
private theorem ball_indicator_le (g : ℂ → ℝ≥0∞) (x : ℂ) (ρ : ℝ) (hgfin : ∀ y, g y ≠ ⊤)
    (z : ℂ) (r : ℝ) (hr : 0 < r) :
    ∫⁻ y in (Metric.ball z r), (Metric.ball x ρ).indicator g y ∂volume ≤
      ENNReal.ofReal r ^ 2 * NNReal.pi * rieszMaximal g x ρ z := by
  have hpt : ∀ y, (Metric.ball x ρ).indicator g y
      = ‖((Metric.ball x ρ).indicator g y).toReal‖ₑ := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
    by_cases hy : y ∈ Metric.ball x ρ
    · rw [Set.indicator_of_mem hy]; exact hgfin y
    · rw [Set.indicator_of_notMem hy]; exact ENNReal.zero_ne_top
  calc ∫⁻ y in (Metric.ball z r), (Metric.ball x ρ).indicator g y ∂volume
      = ∫⁻ y in (Metric.ball z r), ‖((Metric.ball x ρ).indicator g y).toReal‖ₑ ∂volume := by
        simp_rw [← hpt]
    _ ≤ volume (Metric.ball z r) * rieszMaximal g x ρ z := by
        rw [rieszMaximal]
        exact lintegral_ball_le_volume_globalMaximalFunction (by simpa using hr)
    _ = ENNReal.ofReal r ^ 2 * NNReal.pi * rieszMaximal g x ρ z := by
        rw [Complex.volume_ball]

-- INNER bound:  ∫_{ball z δ} gB/‖z-y‖ ≤ 16π · δ · M.
private theorem inner_le (g : ℂ → ℝ≥0∞) (x : ℂ) (ρ : ℝ) (hgfin : ∀ y, g y ≠ ⊤)
    (hgmeas : AEMeasurable g volume) (z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∫⁻ y in (Metric.ball z δ), (Metric.ball x ρ).indicator g y / (‖z - y‖₊ : ℝ≥0∞) ∂volume ≤
      ENNReal.ofReal (16 * Real.pi) * ENNReal.ofReal δ * rieszMaximal g x ρ z := by
  set gB := (Metric.ball x ρ).indicator g with hgB
  set M := rieszMaximal g x ρ z with hM
  -- the dyadic term function
  set F : ℕ → ℂ → ℝ≥0∞ := fun n y =>
    ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
      (Metric.ball z ((2 : ℝ) ^ (1 - (n : ℤ)) * δ)).indicator gB y with hF
  -- radius positivity
  have hrad : ∀ n : ℕ, 0 < (2 : ℝ) ^ (1 - (n : ℤ)) * δ := by
    intro n; positivity
  -- POINTWISE bound on ball z δ \ {z}
  have hpw : ∀ y ∈ Metric.ball z δ, y ≠ z →
      gB y / (‖z - y‖₊ : ℝ≥0∞) ≤ ∑' n : ℕ, F n y := by
    intro y hy hyz
    simp only [hF]
    -- inline the off-z bound (proved standalone above)
    set s := dist y z with hs
    have hspos : 0 < s := dist_pos.mpr hyz
    have hsδ : s < δ := by rw [Metric.mem_ball] at hy; exact hy
    have hns : (‖z - y‖₊ : ℝ) = s := by
      rw [hs, dist_comm, dist_eq_norm, coe_nnnorm]
    have hnse : (‖z - y‖₊ : ℝ≥0∞) = ENNReal.ofReal s := by
      rw [← hns, ENNReal.ofReal_coe_nnreal]
    have hge1 : (1:ℝ) ≤ δ / s := (one_le_div hspos).mpr hsδ.le
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hge1 (by norm_num : (1:ℝ) < 2)
    have hsle : s ≤ (2:ℝ)^(-(n:ℤ)) * δ := by
      rw [zpow_neg, zpow_natCast, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      have := (le_div_iff₀ hspos).mp hn1
      nlinarith [this]
    have hmem : y ∈ Metric.ball z ((2:ℝ)^(1-(n:ℤ)) * δ) := by
      rw [Metric.mem_ball, ← hs]
      calc s ≤ (2:ℝ)^(-(n:ℤ)) * δ := hsle
        _ < (2:ℝ)^(1-(n:ℤ)) * δ := by
            apply mul_lt_mul_of_pos_right _ hδ
            rw [show (1:ℤ)-(n:ℤ) = 1 + (-(n:ℤ)) by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
            nlinarith [zpow_pos (by norm_num : (0:ℝ) < 2) (-(n:ℤ))]
    have hinv : (ENNReal.ofReal s)⁻¹ ≤ (2:ℝ≥0∞)^(n+1) / ENNReal.ofReal δ := by
      have hr1 : (1:ℝ)/s ≤ (2:ℝ)^(n+1) / δ := by
        rw [div_le_div_iff₀ hspos hδ, one_mul]
        have := (div_lt_iff₀ hspos).mp hn2
        nlinarith [this]
      rw [← ENNReal.ofReal_inv_of_pos hspos]
      have e2pow : (2 : ℝ≥0∞) ^ (n + 1) = ENNReal.ofReal ((2:ℝ) ^ (n + 1)) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num)]
      rw [e2pow, ← ENNReal.ofReal_div_of_pos hδ]
      apply ENNReal.ofReal_le_ofReal
      rwa [inv_eq_one_div]
    have hFn : ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
        (Metric.ball z ((2 : ℝ) ^ (1 - (n : ℤ)) * δ)).indicator gB y
        = ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) * gB y := by
      rw [Set.indicator_of_mem hmem]
    calc gB y / (‖z - y‖₊ : ℝ≥0∞)
        = gB y * (ENNReal.ofReal s)⁻¹ := by rw [hnse, ENNReal.div_eq_inv_mul, mul_comm]
      _ ≤ gB y * ((2:ℝ≥0∞)^(n+1) / ENNReal.ofReal δ) := mul_le_mul_right hinv _
      _ = ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
            (Metric.ball z ((2 : ℝ) ^ (1 - (n : ℤ)) * δ)).indicator gB y := by
          rw [hFn, mul_comm]
      _ ≤ ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
            (Metric.ball z ((2 : ℝ) ^ (1 - (n : ℤ)) * δ)).indicator gB y :=
          ENNReal.le_tsum n
  -- per-term integral bound
  have hterm : ∀ n : ℕ, ∫⁻ y in (Metric.ball z δ), F n y ∂volume ≤
      ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * M * (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    simp only [hF]
    set r := (2 : ℝ) ^ (1 - (n : ℤ)) * δ with hr
    have hrpos : 0 < r := by rw [hr]; positivity
    have hconst_ne_top : (2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ ≠ ⊤ :=
      ENNReal.div_ne_top (by simp) (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ)
    rw [lintegral_const_mul' _ _ hconst_ne_top]
    have hball : ∫⁻ y in (Metric.ball z δ),
        (Metric.ball z r).indicator gB y ∂volume ≤
        ENNReal.ofReal r ^ 2 * NNReal.pi * M := by
      calc ∫⁻ y in (Metric.ball z δ), (Metric.ball z r).indicator gB y ∂volume
          ≤ ∫⁻ y, (Metric.ball z r).indicator gB y ∂volume :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ y in (Metric.ball z r), gB y ∂volume := by
            rw [lintegral_indicator measurableSet_ball]
        _ ≤ ENNReal.ofReal r ^ 2 * NNReal.pi * M :=
            ball_indicator_le g x ρ hgfin z r hrpos
    calc ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
          ∫⁻ y in (Metric.ball z δ), (Metric.ball z r).indicator gB y ∂volume
        ≤ ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) * (ENNReal.ofReal r ^ 2 * NNReal.pi * M) :=
          mul_le_mul_right hball _
      _ = ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * M * (2 : ℝ≥0∞)⁻¹ ^ n := by
          have e2pow : (2 : ℝ≥0∞) ^ (n + 1) = ENNReal.ofReal ((2:ℝ) ^ (n + 1)) := by
            rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num)]
          have e2inv : (2 : ℝ≥0∞)⁻¹ ^ n = ENNReal.ofReal (((2:ℝ))⁻¹ ^ n) := by
            rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num),
              ENNReal.ofReal_ofNat]
          have epi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
            rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
          have er2 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r ^ 2) :=
            (ENNReal.ofReal_pow hrpos.le 2).symm
          have hLHS_eq : ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
              (ENNReal.ofReal r ^ 2 * NNReal.pi)
              = ENNReal.ofReal ((2:ℝ)^(n+1) / δ * (r^2 * Real.pi)) := by
            rw [e2pow, er2, epi]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_div_of_pos hδ]
          have hRHS_eq : ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * (2 : ℝ≥0∞)⁻¹ ^ n
              = ENNReal.ofReal (8 * Real.pi * δ * ((2:ℝ))⁻¹ ^ n) := by
            rw [e2inv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          have hscal : (2:ℝ)^(n+1) / δ * (r^2 * Real.pi)
              = 8 * Real.pi * δ * ((2:ℝ))⁻¹ ^ n := by
            rw [hr]
            have h1 : (2:ℝ)^(n+1) = (2:ℝ)^((n:ℤ)+1) := by
              rw [← zpow_natCast]; push_cast; ring_nf
            have h2 : ((2:ℝ))⁻¹ ^ n = (2:ℝ)^(-(n:ℤ)) := by
              rw [inv_pow, ← zpow_natCast (2:ℝ) n, ← zpow_neg]
            have h3 : ((2:ℝ)^(1-(n:ℤ)))^2 = (2:ℝ)^((2:ℤ)-2*(n:ℤ)) := by
              rw [← zpow_natCast ((2:ℝ)^(1-(n:ℤ))) 2, ← zpow_mul]; ring_nf
            rw [h1, h2, mul_pow, h3]
            have hpow : (2:ℝ)^((n:ℤ)+1) * (2:ℝ)^((2:ℤ)-2*(n:ℤ))
                = (8:ℝ) * (2:ℝ)^(-(n:ℤ)) := by
              rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
              rw [show ((n:ℤ)+1) + ((2:ℤ)-2*(n:ℤ)) = 3 + (-(n:ℤ)) by ring]
              rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
              norm_num
            have hδ' : δ ≠ 0 := hδ.ne'
            field_simp
            nlinarith [hpow, sq_nonneg δ, hδ, zpow_pos (by norm_num : (0:ℝ) < 2) (-(n:ℤ))]
          calc ((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
                (ENNReal.ofReal r ^ 2 * NNReal.pi * M)
              = (((2 : ℝ≥0∞) ^ (n + 1) / ENNReal.ofReal δ) *
                  (ENNReal.ofReal r ^ 2 * NNReal.pi)) * M := by ring
            _ = ENNReal.ofReal ((2:ℝ)^(n+1) / δ * (r^2 * Real.pi)) * M := by rw [hLHS_eq]
            _ = ENNReal.ofReal (8 * Real.pi * δ * ((2:ℝ))⁻¹ ^ n) * M := by rw [hscal]
            _ = (ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * (2 : ℝ≥0∞)⁻¹ ^ n) * M := by
                  rw [hRHS_eq]
            _ = ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * M * (2 : ℝ≥0∞)⁻¹ ^ n := by ring
  -- assemble inner bound
  -- a.e. version of pointwise
  have hae : ∀ᵐ y ∂volume, y ∈ Metric.ball z δ → gB y / (‖z - y‖₊ : ℝ≥0∞) ≤ ∑' n : ℕ, F n y := by
    have hnull : (volume : Measure ℂ) {z} = 0 := measure_singleton z
    filter_upwards [ (MeasureTheory.compl_mem_ae_iff.mpr hnull) ] with y hy hymem
    have hyz : y ≠ z := by
      intro h; subst h; exact hy rfl
    exact hpw y hymem hyz
  calc ∫⁻ y in (Metric.ball z δ), gB y / (‖z - y‖₊ : ℝ≥0∞) ∂volume
      ≤ ∫⁻ y in (Metric.ball z δ), (∑' n : ℕ, F n y) ∂volume :=
        setLIntegral_mono_ae' measurableSet_ball hae
    _ = ∑' n : ℕ, ∫⁻ y in (Metric.ball z δ), F n y ∂volume := by
        rw [lintegral_tsum]
        intro n
        simp only [hF]
        apply AEMeasurable.const_mul
        apply AEMeasurable.indicator _ measurableSet_ball
        exact (hgmeas.indicator measurableSet_ball).restrict
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * M * (2 : ℝ≥0∞)⁻¹ ^ n :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * M * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n := by
        rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * M * 2 := by
        rw [ENNReal.tsum_geometric_two]
    _ = ENNReal.ofReal (16 * Real.pi) * ENNReal.ofReal δ * M := by
        have hc : ENNReal.ofReal (8 * Real.pi) * 2 = ENNReal.ofReal (16 * Real.pi) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by rw [ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
        calc ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal δ * M * 2
            = (ENNReal.ofReal (8 * Real.pi) * 2) * (ENNReal.ofReal δ * M) := by ring
          _ = ENNReal.ofReal (16 * Real.pi) * (ENNReal.ofReal δ * M) := by rw [hc]
          _ = ENNReal.ofReal (16 * Real.pi) * ENNReal.ofReal δ * M := by ring

-- TAIL bound and the "for all δ" combined bound.
private theorem combined_le (g : ℂ → ℝ≥0∞) (x : ℂ) (ρ : ℝ) (hgfin : ∀ y, g y ≠ ⊤)
    (hgmeas : AEMeasurable g volume) (z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∫⁻ y in (Metric.ball x ρ), g y / (‖z - y‖₊ : ℝ≥0∞) ∂volume ≤
      (ENNReal.ofReal δ)⁻¹ * (∫⁻ y in (Metric.ball x ρ), g y ∂volume)
        + ENNReal.ofReal (16 * Real.pi) * ENNReal.ofReal δ * rieszMaximal g x ρ z := by
  set gB := (Metric.ball x ρ).indicator g with hgB
  -- rewrite goal integral as whole-space integral of gB/‖z-y‖
  have hker : ∀ y, gB y / (‖z - y‖₊ : ℝ≥0∞)
      = (Metric.ball x ρ).indicator (fun w => g w / (‖z - w‖₊ : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ Metric.ball x ρ
    · rw [hgB, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [hgB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.zero_div]
  have hI : ∫⁻ y in (Metric.ball x ρ), g y / (‖z - y‖₊ : ℝ≥0∞) ∂volume
      = ∫⁻ y, gB y / (‖z - y‖₊ : ℝ≥0∞) ∂volume := by
    simp_rw [hker]
    rw [lintegral_indicator measurableSet_ball]
  have hII : ∫⁻ y in (Metric.ball x ρ), g y ∂volume = ∫⁻ y, gB y ∂volume := by
    rw [hgB, lintegral_indicator measurableSet_ball]
  rw [hI, hII]
  -- split whole = ball z δ + complement
  rw [← lintegral_add_compl (fun y => gB y / (‖z - y‖₊ : ℝ≥0∞))
    (measurableSet_ball (x := z) (ε := δ))]
  rw [add_comm]
  refine add_le_add ?_ ?_
  · -- TAIL : on (ball z δ)ᶜ, ‖z-y‖ ≥ δ, so gB/‖z-y‖ ≤ δ⁻¹ gB
    have htail : ∀ y ∈ (Metric.ball z δ)ᶜ,
        gB y / (‖z - y‖₊ : ℝ≥0∞) ≤ (ENNReal.ofReal δ)⁻¹ * gB y := by
      intro y hy
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt] at hy  -- δ ≤ dist y z
      have hns : (‖z - y‖₊ : ℝ≥0∞) = ENNReal.ofReal (dist y z) := by
        rw [show (dist y z) = ((‖z - y‖₊ : ℝ)) by rw [dist_comm, dist_eq_norm, coe_nnnorm],
          ENNReal.ofReal_coe_nnreal]
      rw [hns, ENNReal.div_eq_inv_mul]
      apply mul_le_mul_left
      apply ENNReal.inv_le_inv'
      exact ENNReal.ofReal_le_ofReal hy
    calc ∫⁻ y in (Metric.ball z δ)ᶜ, gB y / (‖z - y‖₊ : ℝ≥0∞) ∂volume
        ≤ ∫⁻ y in (Metric.ball z δ)ᶜ, (ENNReal.ofReal δ)⁻¹ * gB y ∂volume :=
          setLIntegral_mono_ae' measurableSet_ball.compl (ae_of_all _ htail)
      _ = (ENNReal.ofReal δ)⁻¹ * ∫⁻ y in (Metric.ball z δ)ᶜ, gB y ∂volume := by
          rw [lintegral_const_mul' _ _ (by
            simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero, not_le]; exact hδ)]
      _ ≤ (ENNReal.ofReal δ)⁻¹ * ∫⁻ y, gB y ∂volume := by
          apply mul_le_mul_right
          exact setLIntegral_le_lintegral _ _
  · -- INNER
    exact inner_le g x ρ hgfin hgmeas z δ hδ

/-- **R2a (`rieszPotential_pointwise_le_maximal`).** The **pointwise geometric-mean / split
bound** for the planar Riesz potential. Splitting the kernel `1/‖z − ·‖` at an optimized
radius into a local part — dominated by `δ · M g(z)` through the dyadic-annulus estimate and
`laverage_le_globalMaximalFunction` — and a tail part — dominated by `δ⁻¹ · ‖g‖₁` — and
optimizing the cut `δ := (‖g‖₁ / M g(z))^(1/2)` yields, for every finite-valued density `g`,
the geometric-mean bound
`I₁ g(z) ≤ C · (M g z)^(1/2) · (∫_B g)^(1/2)`,
with `M g = rieszMaximal g` the Hardy–Littlewood maximal function and `C` a dimensional
constant independent of `g`, `x`, `ρ`, `z`. This is the engine of the weak-(1,2) endpoint
R2b. -/
private theorem rieszPotential_pointwise_le_maximal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℂ → ℝ≥0∞), (∀ y, g y ≠ ⊤) → AEMeasurable g volume →
      ∀ (x : ℂ) (ρ : ℝ), 0 < ρ → ∀ z : ℂ,
        (∫⁻ y in Metric.ball x ρ, g y / (‖z - y‖₊ : ℝ≥0∞) ∂volume) ≤
          ENNReal.ofReal C * (rieszMaximal g x ρ z) ^ (1 / (2 : ℝ)) *
            (∫⁻ y in Metric.ball x ρ, g y ∂volume) ^ (1 / (2 : ℝ)) := by
  refine ⟨1 + 16 * Real.pi, by positivity, ?_⟩
  intro g hgfin hgmeas x ρ hρ z
  set M := rieszMaximal g x ρ z with hM
  set I := ∫⁻ y in Metric.ball x ρ, g y ∂volume with hIdef
  set I₁ := ∫⁻ y in Metric.ball x ρ, g y / (‖z - y‖₊ : ℝ≥0∞) ∂volume with hI₁def
  -- Case I = 0
  rcases eq_or_ne I 0 with hI0 | hIne
  · -- show I₁ = 0
    have hgae : g =ᵐ[volume.restrict (Metric.ball x ρ)] 0 := by
      rw [← lintegral_eq_zero_iff' (hgmeas.restrict)]
      exact hI0
    have : I₁ = 0 := by
      rw [hI₁def]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hgae] with y hy
      simp only [Pi.zero_apply] at hy ⊢
      rw [hy, ENNReal.zero_div]
    rw [this]; exact zero_le _
  · -- I ≠ 0, so 0 < I
    have hIpos : 0 < I := pos_iff_ne_zero.mpr hIne
    -- Case M = ⊤
    rcases eq_or_ne M ⊤ with hMtop | hMne
    · -- RHS = ⊤
      have hMrpow : M ^ (1/(2:ℝ)) = ⊤ := by rw [hMtop]; exact ENNReal.top_rpow_of_pos (by norm_num)
      have hIrpow : 0 < I ^ (1/(2:ℝ)) := ENNReal.rpow_pos_of_nonneg hIpos (by norm_num)
      have : ENNReal.ofReal (1 + 16 * Real.pi) * M ^ (1/(2:ℝ)) * I ^ (1/(2:ℝ)) = ⊤ := by
        rw [hMrpow]
        rw [ENNReal.mul_top (by positivity), ENNReal.top_mul (by positivity)]
      rw [this]; exact le_top
    · -- M ≠ ⊤
      -- M = 0 contradicts I > 0 :  M = 0 ⟹ I = 0
      have hMpos : 0 < M := by
        rcases eq_or_ne M 0 with hM0 | hMpos
        · exfalso
          -- ball x ρ ⊆ ball z R for R large; ∫_{ball xρ} g ≤ ∫_{ball z R} gB ≤ π R² M = 0
          obtain ⟨R, hRpos, hsub⟩ : ∃ R, 0 < R ∧ Metric.ball x ρ ⊆ Metric.ball z R := by
            refine ⟨dist x z + ρ + 1, by positivity, ?_⟩
            intro y hy
            rw [Metric.mem_ball] at hy ⊢
            calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
              _ < ρ + dist x z := by linarith [hy]
              _ < dist x z + ρ + 1 := by linarith
          have hball : ∫⁻ y in Metric.ball z R, (Metric.ball x ρ).indicator g y ∂volume ≤
              ENNReal.ofReal R ^ 2 * NNReal.pi * M := ball_indicator_le g x ρ hgfin z R hRpos
          rw [hM0, mul_zero] at hball
          have hIeq : I = ∫⁻ y in Metric.ball z R, (Metric.ball x ρ).indicator g y ∂volume := by
            rw [hIdef, lintegral_indicator measurableSet_ball,
              Measure.restrict_restrict measurableSet_ball,
              Set.inter_eq_self_of_subset_left hsub]
          rw [hIeq] at hIpos
          exact absurd (le_antisymm hball (zero_le _)) hIpos.ne'
        · exact pos_iff_ne_zero.mpr hMpos
      -- Case I = ⊤
      rcases eq_or_ne I ⊤ with hItop | hIne2
      · have hIrpow : I ^ (1/(2:ℝ)) = ⊤ := by
          rw [hItop]; exact ENNReal.top_rpow_of_pos (by norm_num)
        have hMrpow : 0 < M ^ (1/(2:ℝ)) := ENNReal.rpow_pos_of_nonneg hMpos (by norm_num)
        have : ENNReal.ofReal (1 + 16 * Real.pi) * M ^ (1/(2:ℝ)) * I ^ (1/(2:ℝ)) = ⊤ := by
          rw [hIrpow, ENNReal.mul_top (by positivity)]
        rw [this]; exact le_top
      · -- finite positive I, M.  The real optimization.
        set Mr := M.toReal with hMr
        set Ir := I.toReal with hIr
        have hMrpos : 0 < Mr := ENNReal.toReal_pos hMpos.ne' hMne
        have hIrpos : 0 < Ir := ENNReal.toReal_pos hIpos.ne' hIne2
        have hMeq : M = ENNReal.ofReal Mr := (ENNReal.ofReal_toReal hMne).symm
        have hIeq : I = ENNReal.ofReal Ir := (ENNReal.ofReal_toReal hIne2).symm
        -- choose δ
        set δ := Real.sqrt (Ir / Mr) with hδdef
        have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
        -- combined bound
        have hcomb := combined_le g x ρ hgfin hgmeas z δ hδpos
        rw [← hI₁def, ← hIdef, ← hM] at hcomb
        -- rewrite RHS of hcomb into ofReal of a single real
        have hRHScomb : (ENNReal.ofReal δ)⁻¹ * I
            + ENNReal.ofReal (16 * Real.pi) * ENNReal.ofReal δ * M
            = ENNReal.ofReal (δ⁻¹ * Ir + 16 * Real.pi * δ * Mr) := by
          rw [hIeq, hMeq, ← ENNReal.ofReal_inv_of_pos hδpos]
          rw [← ENNReal.ofReal_mul (by positivity)]
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        -- the real arithmetic identity:  the bound = (1+16π) √Mr √Ir
        have hreal : δ⁻¹ * Ir + 16 * Real.pi * δ * Mr
            = (1 + 16 * Real.pi) * (Real.sqrt Mr * Real.sqrt Ir) := by
          rw [hδdef]
          have hsM : 0 < Real.sqrt Mr := Real.sqrt_pos.mpr hMrpos
          have hsI : 0 < Real.sqrt Ir := Real.sqrt_pos.mpr hIrpos
          rw [Real.sqrt_div hIrpos.le]
          have hMrr : Real.sqrt Mr * Real.sqrt Mr = Mr := Real.mul_self_sqrt hMrpos.le
          have hIrr : Real.sqrt Ir * Real.sqrt Ir = Ir := Real.mul_self_sqrt hIrpos.le
          set a := Real.sqrt Mr with ha
          set b := Real.sqrt Ir with hb
          rw [← hMrr, ← hIrr]
          have ha' : a ≠ 0 := hsM.ne'
          have hb' : b ≠ 0 := hsI.ne'
          field_simp
        -- RHS of the goal in ofReal form
        have hgoalRHS : ENNReal.ofReal (1 + 16 * Real.pi) * M ^ (1/(2:ℝ)) * I ^ (1/(2:ℝ))
            = ENNReal.ofReal ((1 + 16 * Real.pi) * (Real.sqrt Mr * Real.sqrt Ir)) := by
          rw [hMeq, hIeq, ENNReal.ofReal_rpow_of_pos hMrpos, ENNReal.ofReal_rpow_of_pos hIrpos,
            ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            mul_assoc]
        rw [hgoalRHS]
        calc I₁ ≤ (ENNReal.ofReal δ)⁻¹ * I
                  + ENNReal.ofReal (16 * Real.pi) * ENNReal.ofReal δ * M := hcomb
          _ = ENNReal.ofReal (δ⁻¹ * Ir + 16 * Real.pi * δ * Mr) := hRHScomb
          _ = ENNReal.ofReal ((1 + 16 * Real.pi) * (Real.sqrt Mr * Real.sqrt Ir)) := by
                rw [hreal]

/-- **R2b (`hasWeakType_rieszPotential_one_two`).** The **weak-(1,2) endpoint** of the planar
Riesz potential `I₁` on a ball, in level-set form. For every finite-valued density `g` and
every height `λ > 0`,
`volume {z ∈ B | λ < I₁ g(z)} ≤ C · (‖g‖₁ / λ)²`,
the constant `C` independent of `g`, `x`, `ρ`. *Proof.* The R2a geometric-mean bound turns
`I₁ g(z) > λ` into `M g(z) > λ² / (C₀² · ‖g‖₁)`, so the level set is contained in a
super-level set of the maximal function, on which the weak-(1,1) maximal bound
(`hasWeakType_globalMaximalFunction`) applies. -/
private theorem hasWeakType_rieszPotential_one_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℂ → ℝ≥0∞), (∀ y, g y ≠ ⊤) → AEMeasurable g volume →
      ∀ (x : ℂ) (ρ : ℝ), 0 < ρ → ∀ lam : ℝ≥0∞, 0 < lam → lam ≠ ⊤ →
        volume {z ∈ Metric.ball x ρ |
            lam < ∫⁻ y in Metric.ball x ρ, g y / (‖z - y‖₊ : ℝ≥0∞) ∂volume} ≤
          ENNReal.ofReal C * ((∫⁻ y in Metric.ball x ρ, g y ∂volume) / lam) ^ (2 : ℕ) := by
  classical
  -- R2a: the pointwise geometric-mean bound (constant `C₀`).
  obtain ⟨C₀, hC₀, hR2a⟩ := rieszPotential_pointwise_le_maximal
  -- The weak-(1,1) constant of the maximal function (a finite `ℝ≥0∞`, nonzero).
  set Cw' : ℝ≥0∞ := C_weakType_globalMaximalFunction ((defaultA 4 : ℕ) : ℝ≥0) 1 1 with hCw'_def
  have hCw'fin : Cw' ≠ ⊤ := C_weakType_globalMaximalFunction_lt_top.ne
  have hCw'0 : Cw' ≠ 0 := by
    rw [hCw'_def, C_weakType_globalMaximalFunction, C_weakType_maximalFunction, if_pos rfl,
      ne_eq, mul_eq_zero, not_or]
    refine ⟨pow_ne_zero _ (by simp [defaultA]), ?_⟩
    intro h
    rw [ENNReal.rpow_eq_zero_iff] at h
    rcases h with h | h
    · exact absurd h.1 (by simp [defaultA])
    · simp [defaultA] at h
  -- The weak-(1,2) constant: `C := Cw'.toReal · C₀²`.
  refine ⟨Cw'.toReal * C₀ ^ 2, by positivity, ?_⟩
  intro g hgfin hgmeas x ρ hρ lam hlam hlamtop
  set I : ℝ≥0∞ := ∫⁻ y in Metric.ball x ρ, g y ∂volume with hI_def
  set a : ℝ≥0∞ := ENNReal.ofReal C₀ with ha_def
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  -- The level set (abbreviation `LS`).
  set LS : Set ℂ := {z ∈ Metric.ball x ρ |
      lam < ∫⁻ y in Metric.ball x ρ, g y / (‖z - y‖₊ : ℝ≥0∞) ∂volume} with hLS_def
  -- Degenerate case `a = 0` (i.e. `C₀ = 0`): R2a forces `I₁ g(z) ≤ 0`, so `LS = ∅`.
  by_cases ha0 : a = 0
  · have hempty : LS = ∅ := by
      rw [hLS_def, Set.eq_empty_iff_forall_notMem]
      rintro z ⟨_, hz⟩
      have hpt := hR2a g hgfin hgmeas x ρ hρ z
      rw [ha0, zero_mul, zero_mul] at hpt
      exact absurd (lt_of_lt_of_le hz hpt) (by simp)
    rw [hempty]; simp
  · -- `a ≠ 0`, so `C₀ > 0`.
    have hC₀pos : 0 < C₀ := by
      rcases hC₀.lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [ha_def, ← h, ENNReal.ofReal_zero]) ha0
    by_cases hItop : I = ⊤
    · -- `I = ⊤`: RHS `= ofReal(Cw'.toReal·C₀²) · (⊤/lam)² = ⊤`.
      rw [hItop, ENNReal.top_div_of_ne_top hlamtop, ENNReal.top_pow (by norm_num),
          ENNReal.mul_top (by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
            have : 0 < Cw'.toReal := ENNReal.toReal_pos hCw'0 hCw'fin
            positivity)]
      exact le_top
    · -- Main case: `0 < a`, `I ≠ ⊤`.
      have hIhalf_top : I ^ (1 / (2 : ℝ)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hItop
      set aI : ℝ≥0∞ := a * I ^ (1 / (2 : ℝ)) with haI_def
      have haItop : aI ≠ ⊤ := ENNReal.mul_ne_top hatop hIhalf_top
      by_cases hI0 : I = 0
      · -- `I = 0`: R2a RHS `= 0`, so `LS = ∅`.
        have hempty : LS = ∅ := by
          rw [hLS_def, Set.eq_empty_iff_forall_notMem]
          rintro z ⟨_, hz⟩
          have hpt := hR2a g hgfin hgmeas x ρ hρ z
          rw [← hI_def, hI0, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero] at hpt
          exact absurd (lt_of_lt_of_le hz hpt) (by simp)
        rw [hempty]; simp
      · -- `0 < I < ⊤`, `0 < a < ⊤`, so `aI ≠ 0`.
        have hIhalf0 : I ^ (1 / (2 : ℝ)) ≠ 0 :=
          (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hI0) hItop).ne'
        have haI0 : aI ≠ 0 := mul_ne_zero ha0 hIhalf0
        -- The threshold `t := (lam / aI)²` and its `ℝ≥0` truncation `s`.
        set t : ℝ≥0∞ := (lam / aI) ^ (2 : ℝ) with ht_def
        have htfin : t ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.div_ne_top hlamtop haI0)
        have hlamdiv0 : lam / aI ≠ 0 := by
          rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
          exact ⟨hlam.ne', haItop⟩
        have ht0 : t ≠ 0 := by
          rw [ht_def]
          exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hlamdiv0)
            (ENNReal.div_ne_top hlamtop haI0)).ne'
        set s : ℝ≥0 := t.toNNReal with hs_def
        have hs_coe : (s : ℝ≥0∞) = t := by rw [hs_def, ENNReal.coe_toNNReal htfin]
        -- `t · (a²·I) = lam²`, the key relation balancing the threshold.
        have htrel : t * (a ^ 2 * I) = lam ^ 2 := by
          have hsq : t = lam ^ 2 / (a ^ 2 * I) := by
            rw [ht_def, ENNReal.div_rpow_of_nonneg _ _ (by norm_num), haI_def,
                ENNReal.mul_rpow_of_ne_top hatop hIhalf_top,
                ← ENNReal.rpow_natCast lam 2, ← ENNReal.rpow_natCast a 2, ← ENNReal.rpow_mul I]
            norm_num
          rw [hsq, ENNReal.div_mul_cancel (mul_ne_zero (pow_ne_zero _ ha0) hI0)
            (ENNReal.mul_ne_top (ENNReal.pow_ne_top hatop) hItop)]
        -- Level-set inclusion: `LS ⊆ {z | t < rieszMaximal g x ρ z}`.
        have hsub : LS ⊆ {z | t < rieszMaximal g x ρ z} := by
          rintro z ⟨_, hz⟩
          have hpt := hR2a g hgfin hgmeas x ρ hρ z
          rw [← hI_def] at hpt
          have hlt : lam < a * (rieszMaximal g x ρ z) ^ (1 / (2 : ℝ)) * I ^ (1 / (2 : ℝ)) :=
            lt_of_lt_of_le hz hpt
          -- Algebraic core: `lam < a·M^½·I^½ ⟹ (lam/aI)² < M`.
          change t < rieszMaximal g x ρ z
          rw [ht_def, haI_def]
          have h' : lam < (rieszMaximal g x ρ z) ^ (1 / (2 : ℝ)) * (a * I ^ (1 / (2 : ℝ))) := by
            rw [show (rieszMaximal g x ρ z) ^ (1 / (2 : ℝ)) * (a * I ^ (1 / (2 : ℝ)))
                  = a * (rieszMaximal g x ρ z) ^ (1 / (2 : ℝ)) * I ^ (1 / (2 : ℝ)) by ring]
            exact hlt
          have hkey : lam / (a * I ^ (1 / (2 : ℝ))) < (rieszMaximal g x ρ z) ^ (1 / (2 : ℝ)) :=
            (ENNReal.div_lt_iff (Or.inl haI0) (Or.inl haItop)).2 h'
          calc (lam / (a * I ^ (1 / (2 : ℝ)))) ^ (2 : ℝ)
              < ((rieszMaximal g x ρ z) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
                ENNReal.rpow_lt_rpow hkey (by norm_num)
            _ = rieszMaximal g x ρ z := by rw [← ENNReal.rpow_mul]; norm_num
        -- The weak-(1,1) bound applied at `s`, then transported through the inclusion.
        have hweak := rieszMaximal_weak_1_1 g hgfin hgmeas x ρ (by rw [← hI_def]; exact hItop) s
        rw [hs_coe, ← hI_def] at hweak
        -- `t · volume LS ≤ Cw' · I`, hence `volume LS ≤ Cw' · I / t`.
        have hLSbound : volume LS ≤ Cw' * I / t := by
          have hmono : t * volume LS ≤ Cw' * I :=
            le_trans (by gcongr) hweak
          rwa [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl htfin), mul_comm]
        -- Conclude by rewriting `Cw' · I / t = ofReal C · (I/lam)²`.
        refine le_trans hLSbound (le_of_eq ?_)
        have hofRC : ENNReal.ofReal (Cw'.toReal * C₀ ^ 2) = Cw' * a ^ 2 := by
          rw [ha_def, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hCw'fin,
              ENNReal.ofReal_pow hC₀]
        rw [hofRC]
        -- `Cw' · I / t = Cw' · a² · (I/lam)²`, via `div_eq_div_iff` and `htrel`.
        have hlam0 : lam ≠ 0 := hlam.ne'
        have hlam2_ne0 : lam ^ 2 ≠ 0 := pow_ne_zero _ hlam0
        have hlam2_top : lam ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hlamtop
        have hdp : ((I / lam) ^ (2 : ℕ)) = I ^ 2 / lam ^ 2 := by
          rw [← ENNReal.rpow_two, ENNReal.div_rpow_of_nonneg _ _ (by norm_num),
              ENNReal.rpow_two, ENNReal.rpow_two]
        rw [show Cw' * a ^ 2 * (I / lam) ^ (2 : ℕ) = (Cw' * a ^ 2 * I ^ 2) / lam ^ 2 by
              rw [hdp, ← mul_div_assoc],
            ENNReal.div_eq_div_iff hlam2_ne0 hlam2_top ht0 htfin, ← htrel]
        ring

/-! ## P-stack — sound endpoint Sobolev (replaces the unsound `I₁` Riesz/HLS route)

The strong `I₁ : L¹ → L²` Riesz bound (the former `R2c` / `eLpNorm_rieszPotential_one_le`) is
the EXCLUDED Hardy–Littlewood–Sobolev endpoint and is mathematically FALSE: the localized
density `g = 1_{ball(x,ε)}` gives `(∫_B (I₁ g)²)^{1/2} / ‖g‖₁ ≈ √(ln(1/ε)) → ∞`. Those two
false nodes were removed. The Sobolev–Poincaré target `N1` is nevertheless TRUE and is
re-derived from the genuine endpoint Sobolev embedding `W^{1,1}(ℝ²) ↪ L²(ℝ²)` (Mathlib
`eLpNorm_le_eLpNorm_fderiv_one`) via a cutoff and `W^{1,1}` mollification. The pointwise /
weak-type nodes `R2a` (`rieszPotential_pointwise_le_maximal`) and `R2b`
(`hasWeakType_rieszPotential_one_two`) above remain true but are now orphaned by this route. -/

/-- **P1 (`eLpNorm_two_le_eLpNorm_fderiv_one`).** The genuine planar endpoint Sobolev
inequality `‖u‖_{L²} ≤ C·‖∇u‖_{L¹}` for a `C¹` compactly-supported `u` — the true
`W^{1,1}(ℝ²) ↪ L²(ℝ²)` embedding. A thin wrapper over Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one` at `finrank ℝ ℂ = 2`, `p = 2` (the
Hölder-conjugate hypothesis `((2 : ℝ≥0)).HolderConjugate 2` is discharged by
`NNReal.holderConjugate_iff`). The SOUND replacement for the false strong `I₁ : L¹ → L²`
bound. -/
theorem eLpNorm_two_le_eLpNorm_fderiv_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℂ → ℂ}, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u 2 volume ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ u) 1 volume := by
  -- The witness is Mathlib's endpoint Sobolev constant at the exponent `2`.
  refine ⟨(eLpNormLESNormFDerivOneConst (volume : Measure ℂ) ((2 : NNReal) : ℝ) : ℝ),
    NNReal.coe_nonneg _, ?_⟩
  intro u hu hucs
  -- The Hölder-conjugate side condition: at `finrank ℝ ℂ = 2`, the conjugate of `2` is `2`.
  have hhc : ((2 : NNReal)).HolderConjugate (2 : NNReal) := by
    rw [NNReal.holderConjugate_iff]; exact ⟨by norm_num, by norm_num⟩
  have hfin : (((Module.finrank ℝ ℂ : ℕ) : NNReal)).HolderConjugate (2 : NNReal) := by
    rw [Complex.finrank_real_complex]; exact_mod_cast hhc
  have key := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure ℂ) hu hucs hfin
  rw [ENNReal.ofReal_coe_nnreal]
  -- Reconcile `(↑(2 : NNReal) : ℝ≥0∞)` with the literal `(2 : ℝ≥0∞)` in the goal.
  have h2 : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by norm_num
  rw [h2] at key
  convert key using 2

/-- **P2 (`eLpNorm_fderiv_one_le_partials`).** The operator norm of the Fréchet derivative is
controlled in `L¹` by its two directional components in the `{1, I}` basis:
`‖∇u‖_{L¹} ≤ ‖∂₁u‖_{L¹} + ‖∂_I u‖_{L¹}`. Elementary: pointwise
`‖fderiv ℝ u z‖ ≤ ‖(fderiv ℝ u z) 1‖ + ‖(fderiv ℝ u z) I‖` (any unit `w = a·1 + b·I` has
`|a|, |b| ≤ 1`), then the `L¹` triangle inequality. -/
theorem eLpNorm_fderiv_one_le_partials {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u) :
    eLpNorm (fderiv ℝ u) 1 volume ≤
      eLpNorm (fun z => (fderiv ℝ u z) 1) 1 volume
        + eLpNorm (fun z => (fderiv ℝ u z) Complex.I) 1 volume := by
  -- Abbreviations for the two directional partials.
  set a : ℂ → ℂ := fun z => (fderiv ℝ u z) 1 with ha
  set b : ℂ → ℂ := fun z => (fderiv ℝ u z) Complex.I with hb
  -- Pointwise operator-norm bound `‖∇u z‖ ≤ ‖a z‖ + ‖b z‖`.
  have hptw : ∀ z : ℂ, ‖fderiv ℝ u z‖ ≤ ‖a z‖ + ‖b z‖ := by
    intro z
    apply ContinuousLinearMap.opNorm_le_bound
    · positivity
    · intro w
      -- Decompose `w = w.re • 1 + w.im • I` in `ℂ`.
      have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      have hmap : (fderiv ℝ u z) w = w.re • a z + w.im • b z := by
        conv_lhs => rw [hdecomp]
        rw [map_add, map_smul, map_smul]
      rw [hmap]
      calc ‖w.re • a z + w.im • b z‖
          ≤ ‖w.re • a z‖ + ‖w.im • b z‖ := norm_add_le _ _
        _ = |w.re| * ‖a z‖ + |w.im| * ‖b z‖ := by
            rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖a z‖ + ‖w‖ * ‖b z‖ := by
            gcongr
            · exact abs_re_le_norm w
            · exact abs_im_le_norm w
        _ = (‖a z‖ + ‖b z‖) * ‖w‖ := by ring
  -- `eLpNorm (∇u) 1 ≤ eLpNorm (z ↦ ‖a z‖ + ‖b z‖) 1` by monotonicity, then the `L¹`
  -- triangle inequality splits the majorant into the two directional `L¹` norms.
  have hcont : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hma : AEStronglyMeasurable a volume :=
    (hcont.clm_apply continuous_const).aestronglyMeasurable
  have hmb : AEStronglyMeasurable b volume :=
    (hcont.clm_apply continuous_const).aestronglyMeasurable
  calc eLpNorm (fderiv ℝ u) 1 volume
      ≤ eLpNorm (fun z => ‖a z‖ + ‖b z‖) 1 volume := eLpNorm_mono_real hptw
    _ = eLpNorm ((fun z => ‖a z‖) + (fun z => ‖b z‖)) 1 volume := by rfl
    _ ≤ eLpNorm (fun z => ‖a z‖) 1 volume + eLpNorm (fun z => ‖b z‖) 1 volume :=
        eLpNorm_add_le hma.norm hmb.norm le_rfl
    _ = eLpNorm a 1 volume + eLpNorm b 1 volume := by
        rw [eLpNorm_norm, eLpNorm_norm]

/-- **P3 (`exists_contDiff_approx_W11`).** The one genuinely new analytic node: a
compactly-supported `W^{1,2}` function `u` (given through its weak directional derivatives
`gx` (direction `1`), `gy` (direction `I`), assumed `L¹`) is approximated by a `C¹`
compactly-supported `w` simultaneously in `L²` of the function and with gradient-`L¹` norm
not exceeding `‖gx‖₁ + ‖gy‖₁` (up to `ε`). Proof by `ContDiffBump` mollification `w = η_δ ⋆ u`:
`‖w − u‖_{L²} → 0`; the directional derivatives commute with mollification
(`fderiv_convolution_normed_apply_eq`, `(fderiv w) v = η_δ ⋆ gᵥ`), so by Young
`‖η_δ ⋆ gᵥ‖₁ ≤ ‖gᵥ‖₁`, and `P2` gives `‖∇w‖₁ ≤ ‖gx‖₁ + ‖gy‖₁`. This replaces the entire
`I₁` Riesz / HLS sub-stack. -/
theorem exists_contDiff_approx_W11 {u gx gy : ℂ → ℂ}
    (hu2 : MemLp u 2 volume) (hucs : HasCompactSupport u)
    (hgx : HasWeakDirDeriv 1 gx u Set.univ) (hgy : HasWeakDirDeriv Complex.I gy u Set.univ)
    (hgx1 : MemLp gx 1 volume) (hgy1 : MemLp gy 1 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ → ℂ, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
      eLpNorm (fun z => w z - u z) 2 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (fderiv ℝ w) 1 volume ≤
        eLpNorm gx 1 volume + eLpNorm gy 1 volume + ENNReal.ofReal ε := by
  classical
  -- ====================================================================
  -- (Y) General `L¹` Young inequality `‖ρ ⋆ g‖₁ ≤ ‖ρ‖₁ · ‖g‖₁`.
  -- ====================================================================
  have young : ∀ (ρ : ℂ → ℝ) (g : ℂ → ℂ), MemLp ρ 1 volume → MemLp g 1 volume →
      eLpNorm (MeasureTheory.convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
        ≤ eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
    intro ρ g hρmem hgmem
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hpt : ∀ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ
        ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume := by
      intro z
      rw [MeasureTheory.convolution_def]
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine lintegral_mono (fun t => ?_)
      rw [hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    have hgsm : AEStronglyMeasurable g volume := hgmem.1
    have hρsm : AEStronglyMeasurable ρ volume := hρmem.1
    have hjoint : AEMeasurable (Function.uncurry
        (fun z t => ‖ρ t‖ₑ * ‖g (z - t)‖ₑ)) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable
          (fun p : ℂ × ℂ => (L (ρ p.2)) (g (p.1 - p.2))) (volume.prod volume) :=
        AEStronglyMeasurable.convolution_integrand L hρsm hgsm
      have h2 : AEMeasurable (fun p : ℂ × ℂ => ‖(L (ρ p.2)) (g (p.1 - p.2))‖ₑ)
          (volume.prod volume) := h1.enorm
      refine h2.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Function.uncurry, hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    calc ∫⁻ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ ∂volume
        ≤ ∫⁻ z, ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ z, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume :=
          lintegral_lintegral_swap hjoint
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g (z - t)‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          rw [lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g z‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          congr 1
          exact lintegral_sub_right_eq_self (fun z => ‖g z‖ₑ) t
      _ = (∫⁻ t, ‖ρ t‖ₑ ∂volume) * ∫⁻ z, ‖g z‖ₑ ∂volume := by
          rw [lintegral_mul_const'' _ hρsm.enorm]
      _ = eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  -- ====================================================================
  -- (F) Mollification commutes with the weak directional derivative.
  -- ====================================================================
  have fderiv_conv : ∀ {f gv : ℂ → ℂ} {v : ℂ},
      HasWeakDirDeriv v gv f Set.univ →
      MeasureTheory.LocallyIntegrable f → MeasureTheory.LocallyIntegrable gv →
      ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      HasCompactSupport ρ → ∀ (z : ℂ),
        (fderiv ℝ (MeasureTheory.convolution ρ f
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
          = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro f gv v hv hf hgv ρ hρ_smooth hρ_supp z
    have _hgv := hgv
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
    have hρ_diff : Differentiable ℝ ρ :=
      hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
    have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
    have hderiv :
        HasFDerivAt (MeasureTheory.convolution ρ f L volume)
          (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
    rw [hderiv.fderiv]
    have hconvexists :
        MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) volume :=
      (hdρ_supp.convolutionExists_left (L.precompL ℂ)
        (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
    rw [MeasureTheory.convolution_def,
        ContinuousLinearMap.integral_apply hconvexists.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
    have hcv :
        (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂volume)
          = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume := by
      have hself := MeasureTheory.integral_sub_left_eq_self
        (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) volume z
      simp only [sub_sub_cancel] at hself
      exact hself.symm
    refine hcv.trans ?_
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
        (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume)
          = -∫ u, ((fderiv ℝ φz u) v) • f u ∂volume := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
      rw [hφz_fderiv u]
      rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
        from neg_smul _ _, neg_neg]
    rw [hint_eq]
    have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
      hρ_smooth.comp (contDiff_const.sub contDiff_id)
    have hφz_supp : HasCompactSupport φz :=
      hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
    have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
    rw [hwd, neg_neg]
    rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
        (fun t => (L (ρ t)) (gv (z - t))) volume z]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
    rfl
  -- ====================================================================
  -- (C) `L²` mollification convergence `‖ρ_n ⋆ g - g‖₂ → 0` for `g ∈ L²`.
  -- ====================================================================
  have conv_tendsto : ∀ {g : ℂ → ℂ},
      MemLp g 2 volume → ∀ (φ : ℕ → ContDiffBump (0 : ℂ)),
      Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - g) 2 volume)
        Filter.atTop (nhds 0) := by
    intro g hg φ hφrout
    set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
      g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
    have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
        Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) h
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
          Filter.atTop (nhds 0) := by
      intro h hh_supp hh_smooth
      obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
      have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
      set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
      have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
      have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
      have hKfin : volume Kset < ⊤ := hKcompact.measure_lt_top
      have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
      set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
        h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
      have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
        HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
        ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
      have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
        intro n x
        set ρ := (φ n).normed volume with hρ
        have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
        rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
        calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
            ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t, ρ t * M ∂volume := by
              have hint : Integrable ρ volume :=
                ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                  ((φ n).hasCompactSupport_normed)
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
              refine Filter.Eventually.of_forall (fun t => ?_)
              simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
              exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
          _ = (∫ t, ρ t ∂volume) * M := by rw [integral_mul_const]
          _ = M := by rw [(φ n).integral_normed]; ring
      have hMh : ∀ y, ‖h y‖ ≤ M := hM
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
        have hsub := MeasureTheory.support_convolution_subset (μ := volume)
          (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
          (f := (φ n).normed volume) (g := h)
        refine hsub.trans (le_trans ?_ haddsub)
        apply Set.add_subset_add _ (subset_tsupport h)
        intro z hz
        have h1 : z ∈ tsupport ((φ n).normed volume) := subset_tsupport _ hz
        rwa [(φ n).tsupport_normed_eq] at h1
      haveI : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
        constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
      set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
      have hrestrict : ∀ᶠ n in Filter.atTop,
          eLpNorm (D n) 2 volume = eLpNorm (D n) 2 (volume.restrict Kset) := by
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
      have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Kset))
          Filter.atTop (nhds 0) := by
        have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
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
        have hhmem : MemLp h 2 (volume.restrict Kset) :=
          MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
            (Filter.Eventually.of_forall hMh)
        exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
          (Filter.Eventually.of_forall hptwise)
      exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
    have hP2 : ∀ (u : ℂ → ℂ), MemLp u 2 volume → ∀ (ε : ℝ),
        eLpNorm u 2 volume ≤ ENNReal.ofReal ε → ∀ n,
          eLpNorm (MeasureTheory.convolution ((φ n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
      intro u hu ε hclose n
      set ρc : ℂ → ℂ := fun z => (((φ n).normed volume z : ℝ) : ℂ) with hρc
      have hconv_eq : MeasureTheory.convolution ((φ n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          = MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ) volume := by
        funext x
        rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
        exact (Complex.real_smul).symm
      rw [hconv_eq]
      have hρc_memLp : MemLp ρc 1 volume := by
        have hcont : Continuous ρc :=
          Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
        have hsupp : HasCompactSupport ρc :=
          ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
        exact hcont.memLp_of_hasCompactSupport hsupp
      have hρc_norm : eLpNorm ρc 1 volume = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hint : Integrable ((φ n).normed volume) volume :=
          ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
            ((φ n).hasCompactSupport_normed)
        have hnn : 0 ≤ᵐ[volume] (φ n).normed volume :=
          Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
        calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
            = ∫⁻ z, ENNReal.ofReal ((φ n).normed volume z) ∂volume := by
              refine lintegral_congr (fun z => ?_)
              rw [hρc,
                show ‖(((φ n).normed volume z : ℝ) : ℂ)‖ₑ
                    = ‖(φ n).normed volume z‖ₑ from by
                  rw [← enorm_norm, Complex.norm_real, enorm_norm],
                Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
          _ = ENNReal.ofReal (∫ z, (φ n).normed volume z ∂volume) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ = 1 := by rw [(φ n).integral_normed]; simp
      calc eLpNorm (MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ)
              volume) 2 volume
          ≤ eLpNorm ρc 1 volume * eLpNorm u 2 volume :=
            eLpNorm_convolution_le hρc_memLp hu
        _ = eLpNorm u 2 volume := by rw [hρc_norm, one_mul]
        _ ≤ ENNReal.ofReal ε := hclose
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [htop]; exact le_top
    set δ : ℝ := ε.toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
    have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
    obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ε := δ / 3) (by positivity)
    have hh_memLp : MemLp hh 2 volume :=
      hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
    have hgh_memLp : MemLp (g - hh) 2 volume := hg.sub hh_memLp
    have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      hP2 (g - hh) hgh_memLp (δ / 3) hh_close
    have hP3ev : ∀ᶠ n in Filter.atTop,
        eLpNorm (MeasureTheory.convolution ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
        (ENNReal.ofReal_pos.mpr (by positivity)))
    have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g) := by
      intro n
      have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed volume) (g - hh)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous ?_
        exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
      have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        rw [hCg]; simp only
        rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
        congr 1; abel
      rw [hsplit]; abel
    filter_upwards [hP3ev] with n hn3
    rw [hdecomp n]
    have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) volume :=
      (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        ((hg.locallyIntegrable (by norm_num)).sub
          hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
        volume - hh) volume :=
      ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (hh - g) volume :=
      (hh_memLp.sub hg).1
    have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g)) 2
          volume
        ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
      refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
      refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
      · exact add_le_add (hP2gh n) hn3
      · rw [eLpNorm_sub_comm]; exact hh_close
    refine le_trans hkey ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
    apply le_of_eq; congr 1; ring
  -- ====================================================================
  -- Assembly: pick one mollifier of small enough radius.
  -- ====================================================================
  -- A canonical mollifier sequence with `rOut = 2/(n+2) → 0`.
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- The `L²` convergence of the mollification of `u`, extract one good index `N`.
  have hconvu := conv_tendsto hu2 φ₀ hφ₀rout
  have hev : ∀ᶠ n in Filter.atTop,
      eLpNorm (MeasureTheory.convolution ((φ₀ n).normed volume) u
        (ContinuousLinearMap.lsmul ℝ ℝ) volume - u) 2 volume ≤ ENNReal.ofReal ε :=
    ENNReal.tendsto_nhds_zero.mp hconvu (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨N, hN⟩ := hev.exists
  -- The chosen mollifier `ρ := (φ₀ N).normed volume` and `w := ρ ⋆ u`.
  set ρ : ℂ → ℝ := (φ₀ N).normed volume with hρdef
  set w : ℂ → ℂ := MeasureTheory.convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hwdef
  have hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := (φ₀ N).contDiff_normed
  have hρ_cs : HasCompactSupport ρ := (φ₀ N).hasCompactSupport_normed
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  have hρ_memLp : MemLp ρ 1 volume := hρ_cont.memLp_of_hasCompactSupport hρ_cs
  -- local integrability of `u`, `gx`, `gy`.
  have hu_li : MeasureTheory.LocallyIntegrable u := hu2.locallyIntegrable (by norm_num)
  have hgx_li : MeasureTheory.LocallyIntegrable gx := hgx1.locallyIntegrable le_rfl
  have hgy_li : MeasureTheory.LocallyIntegrable gy := hgy1.locallyIntegrable le_rfl
  -- (1) `w` is `C¹` and (2) compactly supported.
  have hw_contDiff : ContDiff ℝ 1 w := by
    refine HasCompactSupport.contDiff_convolution_left _ hρ_cs ?_ hu_li
    exact hρ_smooth.of_le (by exact_mod_cast le_top)
  have hw_cs : HasCompactSupport w :=
    HasCompactSupport.convolution _ hρ_cs hucs
  refine ⟨w, hw_contDiff, hw_cs, ?_, ?_⟩
  · -- (3) `L²` distance.
    have : (fun z => w z - u z) = w - u := rfl
    rw [this]; exact hN
  · -- (4) gradient `L¹` bound.
    -- `ρ`'s `L¹` mass is `1`.
    have hρ_norm1 : eLpNorm ρ 1 volume = 1 := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      have hint : Integrable ρ volume :=
        hρ_cont.integrable_of_hasCompactSupport hρ_cs
      have hnn : 0 ≤ᵐ[volume] ρ :=
        Filter.Eventually.of_forall (fun z => (φ₀ N).nonneg_normed z)
      calc ∫⁻ z, ‖ρ z‖ₑ ∂volume
          = ∫⁻ z, ENNReal.ofReal (ρ z) ∂volume := by
            refine lintegral_congr (fun z => ?_)
            rw [Real.enorm_of_nonneg ((φ₀ N).nonneg_normed z)]
        _ = ENNReal.ofReal (∫ z, ρ z ∂volume) :=
            (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
        _ = 1 := by rw [hρdef, (φ₀ N).integral_normed]; simp
    -- Identify the two directional derivatives of `w` with mollifications.
    have hdx : (fun z => (fderiv ℝ w z) 1)
        = MeasureTheory.convolution ρ gx (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext z
      exact fderiv_conv hgx hu_li hgx_li hρ_smooth hρ_cs z
    have hdy : (fun z => (fderiv ℝ w z) Complex.I)
        = MeasureTheory.convolution ρ gy (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext z
      exact fderiv_conv hgy hu_li hgy_li hρ_smooth hρ_cs z
    -- Young `L¹` bounds: `‖ρ ⋆ gx‖₁ ≤ ‖gx‖₁`, `‖ρ ⋆ gy‖₁ ≤ ‖gy‖₁`.
    have hyx : eLpNorm (fun z => (fderiv ℝ w z) 1) 1 volume ≤ eLpNorm gx 1 volume := by
      rw [hdx]
      calc eLpNorm (MeasureTheory.convolution ρ gx (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
          ≤ eLpNorm ρ 1 volume * eLpNorm gx 1 volume := young ρ gx hρ_memLp hgx1
        _ = eLpNorm gx 1 volume := by rw [hρ_norm1, one_mul]
    have hyy : eLpNorm (fun z => (fderiv ℝ w z) Complex.I) 1 volume ≤ eLpNorm gy 1 volume := by
      rw [hdy]
      calc eLpNorm (MeasureTheory.convolution ρ gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
          ≤ eLpNorm ρ 1 volume * eLpNorm gy 1 volume := young ρ gy hρ_memLp hgy1
        _ = eLpNorm gy 1 volume := by rw [hρ_norm1, one_mul]
    -- Combine with P2 and add the `ε` slack.
    calc eLpNorm (fderiv ℝ w) 1 volume
        ≤ eLpNorm (fun z => (fderiv ℝ w z) 1) 1 volume
            + eLpNorm (fun z => (fderiv ℝ w z) Complex.I) 1 volume :=
          eLpNorm_fderiv_one_le_partials hw_contDiff
      _ ≤ eLpNorm gx 1 volume + eLpNorm gy 1 volume := add_le_add hyx hyy
      _ ≤ eLpNorm gx 1 volume + eLpNorm gy 1 volume + ENNReal.ofReal ε := le_self_add


/-! ## P-cut — an adapted smooth cutoff with the `1/r` gradient bound -/

/-- **P-cut (`exists_cutoff_ball`).** A smooth cutoff `χ` adapted to the ball `ball x r`:
`χ ≡ 1` on `ball x r`, `0 ≤ χ ≤ 1`, support inside `closedBall x (3r/2)`, and the
**scale-correct gradient bound** `‖fderiv ℝ χ z‖ ≤ C / r` for a dimensional constant `C`
(independent of `x, r`). This is the cutoff both N1 (Sobolev–Poincaré) and N3 (Caccioppoli)
test against; Mathlib's `ContDiffBump` provides the plateau/support/smoothness but exposes no
derivative bound, so the `C/r` control is obtained here by rescaling a fixed reference bump
`ψ` (whose continuous compactly-supported `fderiv` is bounded by some `C₀`) along
`z ↦ r⁻¹ • (z − x)`, the chain rule supplying the `r⁻¹` factor. -/
theorem exists_cutoff_ball (x : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧
      (∀ z ∈ Metric.ball x r, χ z = 1) ∧
      tsupport χ ⊆ Metric.closedBall x (3 * r / 2) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖fderiv ℝ χ z‖ ≤ C / r := by
  -- Reference bump centred at `0` with `rIn = 1`, `rOut = 3/2`.
  set ψ : ContDiffBump (0 : ℂ) := ⟨1, 3 / 2, by norm_num, by norm_num⟩ with hψdef
  -- The affine rescaling `g z = r⁻¹ • (z - x)` and the cutoff `χ = ψ ∘ g`.
  set g : ℂ → ℂ := fun z => r⁻¹ • (z - x) with hgdef
  set χ : ℂ → ℝ := fun z => ψ (g z) with hχdef
  -- Norm identity for the real rescaling, valid since `r > 0`.
  have hnorm : ∀ w : ℂ, ‖r⁻¹ • w‖ = r⁻¹ * ‖w‖ := by
    intro w
    rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Membership translation: `g z ∈ ball 0 s ↔ z ∈ ball x (r*s)` (for `s ≥ 0`).
  have hball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.ball (0 : ℂ) s ↔ z ∈ Metric.ball x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_lt_iff₀ hr]
  -- Membership translation for closed balls (used for the plateau).
  have hcball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.closedBall (0 : ℂ) s ↔ z ∈ Metric.closedBall x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_closedBall, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_le_iff₀ hr]
  -- `g` is smooth.
  have hg_cd : ContDiff ℝ (⊤ : ℕ∞) g :=
    (contDiff_id.sub contDiff_const).const_smul r⁻¹
  -- `χ` is smooth.
  have hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ := ψ.contDiff.comp hg_cd
  -- `g` is differentiable, with constant derivative `r⁻¹ • id`.
  have hg_diff : ∀ z, DifferentiableAt ℝ g z :=
    fun z => (hg_cd.differentiable (by simp)).differentiableAt
  have hfd_g : ∀ z, fderiv ℝ g z = r⁻¹ • (ContinuousLinearMap.id ℝ ℂ) := by
    intro z
    have h1 : HasFDerivAt (fun z : ℂ => z - x) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const x
    exact (h1.const_smul (r⁻¹)).fderiv
  refine ⟨χ, hχ_cd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Compact support: `χ` is supported where `g z ∈ support ψ = ball 0 (3/2)`,
    -- a bounded preimage under `g`.
    apply HasCompactSupport.intro (K := Metric.closedBall x (3 * r / 2))
      (isCompact_closedBall _ _)
    intro z hz
    -- If `z ∉ closedBall x (3r/2)` then `g z ∉ closedBall 0 (3/2) ⊇ ball 0 (3/2)`.
    have hznot : z ∉ Metric.closedBall x (r * (3 / 2)) := by
      intro hmem
      exact hz (by simpa [mul_div_assoc, mul_comm] using hmem)
    have hgz : g z ∉ Metric.closedBall (0 : ℂ) (3 / 2) := by
      rw [hcball (3 / 2) (by norm_num)]; exact hznot
    have hgz' : g z ∉ Function.support (⇑ψ) := by
      rw [ψ.support_eq]
      intro hmem
      exact hgz (Metric.ball_subset_closedBall hmem)
    change χ z = 0
    rw [hχdef]
    exact Function.notMem_support.mp hgz'
  · -- `0 ≤ χ`.
    intro z; exact ψ.nonneg
  · -- `χ ≤ 1`.
    intro z; exact ψ.le_one
  · -- Plateau: on `ball x r`, `g z ∈ closedBall 0 1 = closedBall 0 rIn`, so `ψ (g z) = 1`.
    intro z hz
    have hzc : z ∈ Metric.closedBall x (r * 1) := by
      rw [mul_one]; exact Metric.ball_subset_closedBall hz
    have hgz : g z ∈ Metric.closedBall (0 : ℂ) 1 := (hcball 1 (by norm_num) z).mpr hzc
    simpa [hχdef] using ψ.one_of_mem_closedBall (by simpa [hψdef] using hgz)
  · -- Support is inside `closedBall x (3r/2)`: `support χ ⊆ ball x (3r/2)`, and `tsupport`
    -- is its closure, hence inside the closed ball.
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    -- `z ∈ support χ` means `ψ (g z) ≠ 0`, i.e. `g z ∈ support ψ = ball 0 (3/2)`.
    have hχz : χ z ≠ 0 := Function.mem_support.mp hz
    have hgz : g z ∈ Function.support (⇑ψ) := Function.mem_support.mpr hχz
    rw [ψ.support_eq, hball (3 / 2) (by norm_num) z] at hgz
    refine Metric.ball_subset_closedBall ?_
    simpa [mul_div_assoc, mul_comm] using hgz
  · -- Gradient bound `‖fderiv χ z‖ ≤ C₀ / r`.
    -- `fderiv ψ` is continuous (smoothness ≥ 1) with compact support, hence bounded by `C₀`.
    have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) (⇑ψ) := ψ.contDiff
    have hfd_cont : Continuous (fderiv ℝ (⇑ψ)) := hψ_cd.continuous_fderiv (by simp)
    have hfd_cs : HasCompactSupport (fderiv ℝ (⇑ψ)) :=
      HasCompactSupport.fderiv ℝ ψ.hasCompactSupport
    obtain ⟨C₀, hC₀⟩ := hfd_cs.exists_bound_of_continuous hfd_cont
    refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
    intro z
    -- Chain rule and operator-norm submultiplicativity supply the `r⁻¹` factor.
    have hψ_diff : DifferentiableAt ℝ (⇑ψ) (g z) :=
      (hψ_cd.differentiable (by simp)).differentiableAt
    have hcomp : fderiv ℝ χ z = (fderiv ℝ (⇑ψ) (g z)).comp (fderiv ℝ g z) := by
      have hχeq : χ = (⇑ψ) ∘ g := rfl
      rw [hχeq, fderiv_comp z hψ_diff (hg_diff z)]
    rw [hcomp, hfd_g z]
    calc ‖(fderiv ℝ (⇑ψ) (g z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖
        ≤ ‖fderiv ℝ (⇑ψ) (g z)‖ * ‖r⁻¹ • (ContinuousLinearMap.id ℝ ℂ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ (⇑ψ) (g z)‖ * r⁻¹ := by
          rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hr)]
      _ ≤ max C₀ 0 * r⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hr))
          exact le_trans (hC₀ (g z)) (le_max_left _ _)
      _ = max C₀ 0 / r := by rw [div_eq_mul_inv]

/-- **P-cut, uniform-constant form (`exists_cutoff_ball_uniform`).** The gradient bound
constant of `exists_cutoff_ball` is in fact **independent of the ball** `(x, r)`: it is the
bound on the Fréchet derivative of a single fixed reference bump. This uniform form hoists
that constant `Cχ` *outside* the `∀ x r` quantifier, which is what the Sobolev–Poincaré node
N1 needs in order to choose its ball-independent constant. -/
theorem exists_cutoff_ball_uniform :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
        (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧
        (∀ z ∈ Metric.ball x r, χ z = 1) ∧
        tsupport χ ⊆ Metric.closedBall x (3 * r / 2) ∧
        ∀ z, ‖fderiv ℝ χ z‖ ≤ Cχ / r := by
  -- Reference bump centred at `0` with `rIn = 1`, `rOut = 3/2`, fixed once.
  set ψ : ContDiffBump (0 : ℂ) := ⟨1, 3 / 2, by norm_num, by norm_num⟩ with hψdef
  have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) (⇑ψ) := ψ.contDiff
  have hfd_cont : Continuous (fderiv ℝ (⇑ψ)) := hψ_cd.continuous_fderiv (by simp)
  have hfd_cs : HasCompactSupport (fderiv ℝ (⇑ψ)) :=
    HasCompactSupport.fderiv ℝ ψ.hasCompactSupport
  obtain ⟨C₀, hC₀⟩ := hfd_cs.exists_bound_of_continuous hfd_cont
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x r hr
  -- The affine rescaling `g z = r⁻¹ • (z - x)` and the cutoff `χ = ψ ∘ g`.
  set g : ℂ → ℂ := fun z => r⁻¹ • (z - x) with hgdef
  set χ : ℂ → ℝ := fun z => ψ (g z) with hχdef
  have hnorm : ∀ w : ℂ, ‖r⁻¹ • w‖ = r⁻¹ * ‖w‖ := by
    intro w
    rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  have hball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.ball (0 : ℂ) s ↔ z ∈ Metric.ball x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_lt_iff₀ hr]
  have hcball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.closedBall (0 : ℂ) s ↔ z ∈ Metric.closedBall x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_closedBall, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_le_iff₀ hr]
  have hg_cd : ContDiff ℝ (⊤ : ℕ∞) g :=
    (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ := ψ.contDiff.comp hg_cd
  have hg_diff : ∀ z, DifferentiableAt ℝ g z :=
    fun z => (hg_cd.differentiable (by simp)).differentiableAt
  have hfd_g : ∀ z, fderiv ℝ g z = r⁻¹ • (ContinuousLinearMap.id ℝ ℂ) := by
    intro z
    have h1 : HasFDerivAt (fun z : ℂ => z - x) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const x
    exact (h1.const_smul (r⁻¹)).fderiv
  refine ⟨χ, hχ_cd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.intro (K := Metric.closedBall x (3 * r / 2))
      (isCompact_closedBall _ _)
    intro z hz
    have hznot : z ∉ Metric.closedBall x (r * (3 / 2)) := by
      intro hmem
      exact hz (by simpa [mul_div_assoc, mul_comm] using hmem)
    have hgz : g z ∉ Metric.closedBall (0 : ℂ) (3 / 2) := by
      rw [hcball (3 / 2) (by norm_num)]; exact hznot
    have hgz' : g z ∉ Function.support (⇑ψ) := by
      rw [ψ.support_eq]
      intro hmem
      exact hgz (Metric.ball_subset_closedBall hmem)
    change χ z = 0
    rw [hχdef]
    exact Function.notMem_support.mp hgz'
  · intro z; exact ψ.nonneg
  · intro z; exact ψ.le_one
  · intro z hz
    have hzc : z ∈ Metric.closedBall x (r * 1) := by
      rw [mul_one]; exact Metric.ball_subset_closedBall hz
    have hgz : g z ∈ Metric.closedBall (0 : ℂ) 1 := (hcball 1 (by norm_num) z).mpr hzc
    simpa [hχdef] using ψ.one_of_mem_closedBall (by simpa [hψdef] using hgz)
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    have hχz : χ z ≠ 0 := Function.mem_support.mp hz
    have hgz : g z ∈ Function.support (⇑ψ) := Function.mem_support.mpr hχz
    rw [ψ.support_eq, hball (3 / 2) (by norm_num) z] at hgz
    refine Metric.ball_subset_closedBall ?_
    simpa [mul_div_assoc, mul_comm] using hgz
  · intro z
    have hψ_diff : DifferentiableAt ℝ (⇑ψ) (g z) :=
      (hψ_cd.differentiable (by simp)).differentiableAt
    have hcomp : fderiv ℝ χ z = (fderiv ℝ (⇑ψ) (g z)).comp (fderiv ℝ g z) := by
      have hχeq : χ = (⇑ψ) ∘ g := rfl
      rw [hχeq, fderiv_comp z hψ_diff (hg_diff z)]
    rw [hcomp, hfd_g z]
    calc ‖(fderiv ℝ (⇑ψ) (g z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖
        ≤ ‖fderiv ℝ (⇑ψ) (g z)‖ * ‖r⁻¹ • (ContinuousLinearMap.id ℝ ℂ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ (⇑ψ) (g z)‖ * r⁻¹ := by
          rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hr)]
      _ ≤ max C₀ 0 * r⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hr))
          exact le_trans (hC₀ (g z)) (le_max_left _ _)
      _ = max C₀ 0 / r := by rw [div_eq_mul_inv]

/-! ## (1,1)-Poincaré on a ball for the `W^{1,2}` primitive -/

set_option maxHeartbeats 400000 in
-- The mollification proof inlines the smooth segment-FTC Poincaré, the `conv_tendsto`
-- L²-mollification convergence and the `fderiv_conv` Leibniz identity as local `have`s,
-- so the single self-contained elaboration needs a modestly raised heartbeat budget.
open Metric in
/-- **(`poincare_one_one_ball`).** The **`(1,1)`-Poincaré inequality on a ball** for a
`W^{1,2}` primitive `F` with weak directional derivatives `Gx` (direction `1`) and `Gy`
(direction `I`). On every ball `B = ball x r` the `L¹`-mass of the oscillation of `F`
about its average is controlled by `r` times the `L¹`-mass of the **full gradient**
`‖Gx‖ + ‖Gy‖`:
`∫⁻_{B} ‖F − F_B‖ ≤ C · r · ∫⁻_{B} (‖Gx‖ + ‖Gy‖)`.

This is the lower-order companion needed in the cutoff proof of the Sobolev–Poincaré
node N1: it absorbs the cutoff-annulus commutator `(∇χ)·(F − F_B)` whose `L¹` mass is
controlled by the gradient.

**Proof (mollification route).** The witness constant is `C = 8`. We mollify `F` to a
sequence of `C¹` functions `Fₙ = ρₙ ⋆ F` (`ρₙ` a normed `ContDiffBump`), prove the
`(1,1)`-Poincaré for each smooth `Fₙ` by the all-direction segment FTC `Fₙ(z) − Fₙ(w) =
∫₀¹ ∇Fₙ(w+t(z−w))·(z−w) dt`, average over `w`, and collapse the double integral by the
affine change of variables `y = (1−t)w + tz` (Jacobian `(1−t)²` resp. `t²`) split at
`t = 1/2`, giving the scale-invariant constant `8`. We then pass `n → ∞` on the fixed ball:
the directional derivatives commute with mollification (`fderiv_conv`), `Fₙ → F` and
`ρₙ ⋆ Gᵥ → Gᵥ` in `L²(B)` (the proven `conv_tendsto`), whence both the oscillation `L¹`-mass
and the gradient `L¹`-mass converge, and the per-`n` inequality passes to the limit. -/
theorem poincare_one_one_ball :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F Gx Gy : ℂ → ℂ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          ∫⁻ z in Metric.ball x r, (‖F z - (⨍ w in Metric.ball x r, F w)‖₊ : ℝ≥0∞) ∂volume ≤
            ENNReal.ofReal (C * r) *
              ∫⁻ z in Metric.ball x r, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume := by
  refine ⟨8, by norm_num, ?_⟩
  intro F Gx Gy hF hGx hGy hGxw hGyw x r hr
  have smooth_poincare : ∀ (u : ℂ → ℂ), ContDiff ℝ 1 u → ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∫⁻ z in ball x r, (‖u z - (⨍ w in ball x r, u w ∂volume)‖ₑ) ∂volume ≤
        ENNReal.ofReal (8 * r) * ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ ∂volume := by
    intro u hu x r hr
    set B := ball x r with hB
    have hBmeas : MeasurableSet B := measurableSet_ball
    have hBfin : volume B ≠ ⊤ := (measure_ball_lt_top).ne
    have hBpos : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
    have hBrpos : 0 < volume.real B := by
      rw [Measure.real, ENNReal.toReal_pos_iff]; exact ⟨pos_iff_ne_zero.mpr hBpos, hBfin.lt_top⟩
    set g : ℂ → ℝ≥0∞ := fun y => ‖fderiv ℝ u y‖ₑ with hg
    have hgmeas : Measurable g := ((hu.continuous_fderiv (by norm_num)).enorm).measurable
    set G := ∫⁻ y in B, g y ∂volume with hG
    have hudiff : Differentiable ℝ u := hu.differentiable (by norm_num)
    have hucont : Continuous u := hudiff.continuous
    have hfdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    have hconv : Convex ℝ B := convex_ball x r
    -- (1) Pointwise segment-FTC bound.
    have hpoint : ∀ z w : ℂ, (‖u z - u w‖ₑ) ≤
        ∫⁻ t in Set.Ioc (0:ℝ) 1, g (w + t • (z - w)) * ‖z - w‖ₑ ∂volume := by
      intro z w
      have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + s • (z - w)) (z - w) t := by
        intro t; have := ((hasDerivAt_id t).smul_const (z - w)).const_add w; simpa using this
      have hgderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u (w + s • (z - w)))
          ((fderiv ℝ u (w + t • (z - w))) (z - w)) t := fun t =>
        ((hudiff (w + t • (z - w))).hasFDerivAt).comp_hasDerivAt t (hline t)
      have hlinec : Continuous (fun t : ℝ => w + t • (z - w)) := by
        have h : (fun t : ℝ => w + t • (z - w)) = fun t : ℝ => w + (t : ℂ) * (z - w) := by
          funext t; rw [Complex.real_smul]
        rw [h]; fun_prop
      have hcont : Continuous (fun t : ℝ => (fderiv ℝ u (w + t • (z - w))) (z - w)) :=
        (hfdc.comp hlinec).clm_apply continuous_const
      have hftc : u z - u w = ∫ t in (0:ℝ)..1, (fderiv ℝ u (w + t • (z - w))) (z - w) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hgderiv t)
          (hcont.intervalIntegrable _ _)]; simp
      rw [hftc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      refine le_trans (enorm_integral_le_lintegral_enorm _) (lintegral_mono (fun t => ?_))
      calc ‖(fderiv ℝ u (w + t • (z - w))) (z - w)‖ₑ
          ≤ ‖fderiv ℝ u (w + t • (z - w))‖ₑ * ‖z - w‖ₑ := by
            rw [← ofReal_norm_eq_enorm (((fderiv ℝ u (w + t • (z - w))) (z - w))),
              ← ofReal_norm_eq_enorm (z - w),
              show ‖fderiv ℝ u (w + t • (z - w))‖ₑ
                = ENNReal.ofReal ‖fderiv ℝ u (w + t • (z - w))‖ from
                (ofReal_norm_eq_enorm _).symm,
              ← ENNReal.ofReal_mul (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal ((fderiv ℝ u (w + t • (z - w))).le_opNorm (z - w))
        _ = g (w + t • (z - w)) * ‖z - w‖ₑ := rfl
    -- (2) Substitution-on-ball lemmas (both directions).
    have subW : ∀ (z : ℂ), z ∈ B → ∀ (t : ℝ), 0 < 1 - t → t ∈ Set.Icc (0:ℝ) 1 →
        ∫⁻ w in B, g ((1 - t) • w + t • z) ∂volume ≤
          ENNReal.ofReal ((1 - t) ^ 2)⁻¹ * G := by
      intro z hz t ht0 ht1
      rw [← lintegral_indicator hBmeas]
      have hmono : ∀ w : ℂ, B.indicator (fun w => g ((1 - t) • w + t • z)) w ≤
          (fun w => B.indicator g ((1 - t) • w + t • z)) w := by
        intro w
        by_cases hw : w ∈ B
        · simp only []
          have hin : (1 - t) • w + t • z ∈ B := by
            have := hconv hw hz (by linarith [ht1.1] : (0:ℝ) ≤ 1 - t) ht1.1 (by ring)
            simpa using this
          rw [Set.indicator_of_mem hw, Set.indicator_of_mem hin]
        · simp only []; rw [Set.indicator_of_notMem hw]; exact zero_le _
      refine (lintegral_mono hmono).trans_eq ?_
      set h : ℂ → ℝ≥0∞ := B.indicator g with hh
      have hhmeas : Measurable h := hgmeas.indicator hBmeas
      have hfr : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
      have hmap : Measure.map (fun w : ℂ => (1 - t) • w) volume
          = ENNReal.ofReal (|((1 - t) ^ (Module.finrank ℝ ℂ))⁻¹|) • (volume : Measure ℂ) :=
        Measure.map_addHaar_smul volume ht0.ne'
      have hfmeas : Measurable (fun y : ℂ => h (y + t • z)) := hhmeas.comp (by fun_prop)
      have hgmm : Measurable (fun w : ℂ => (1 - t) • w) := by fun_prop
      calc ∫⁻ w, h ((1 - t) • w + t • z) ∂volume
          = ∫⁻ w, (fun y => h (y + t • z)) ((fun w : ℂ => (1 - t) • w) w) ∂volume := rfl
        _ = ∫⁻ w, (fun y => h (y + t • z)) w ∂(Measure.map (fun w : ℂ => (1 - t) • w) volume) :=
            (lintegral_map hfmeas hgmm).symm
        _ = ENNReal.ofReal (|((1 - t) ^ (Module.finrank ℝ ℂ))⁻¹|)
              * ∫⁻ w, h (w + t • z) ∂volume := by rw [hmap, lintegral_smul_measure, smul_eq_mul]
        _ = ENNReal.ofReal ((1 - t) ^ 2)⁻¹ * ∫⁻ y, h y ∂volume := by
            rw [lintegral_add_right_eq_self h (t • z), hfr, abs_of_nonneg (by positivity)]
        _ = ENNReal.ofReal ((1 - t) ^ 2)⁻¹ * G := by
            rw [hG, lintegral_indicator hBmeas]
    have subZ : ∀ (w : ℂ), w ∈ B → ∀ (t : ℝ), 0 < t → t ∈ Set.Icc (0:ℝ) 1 →
        ∫⁻ z in B, g ((1 - t) • w + t • z) ∂volume ≤
          ENNReal.ofReal (t ^ 2)⁻¹ * G := by
      intro w hw t ht0 ht1
      rw [← lintegral_indicator hBmeas]
      have hmono : ∀ z : ℂ, B.indicator (fun z => g ((1 - t) • w + t • z)) z ≤
          (fun z => B.indicator g ((1 - t) • w + t • z)) z := by
        intro z
        by_cases hz : z ∈ B
        · simp only []
          have hin : (1 - t) • w + t • z ∈ B := by
            have := hconv hw hz (by linarith [ht1.2] : (0:ℝ) ≤ 1 - t) ht1.1 (by ring)
            simpa using this
          rw [Set.indicator_of_mem hz, Set.indicator_of_mem hin]
        · simp only []; rw [Set.indicator_of_notMem hz]; exact zero_le _
      refine (lintegral_mono hmono).trans_eq ?_
      set h : ℂ → ℝ≥0∞ := B.indicator g with hh
      have hhmeas : Measurable h := hgmeas.indicator hBmeas
      have hfr : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
      have hmap : Measure.map (fun z : ℂ => t • z) volume
          = ENNReal.ofReal (|(t ^ (Module.finrank ℝ ℂ))⁻¹|) • (volume : Measure ℂ) :=
        Measure.map_addHaar_smul volume ht0.ne'
      have hfmeas : Measurable (fun y : ℂ => h ((1 - t) • w + y)) := hhmeas.comp (by fun_prop)
      have hgmm : Measurable (fun z : ℂ => t • z) := by fun_prop
      calc ∫⁻ z, h ((1 - t) • w + t • z) ∂volume
          = ∫⁻ z, (fun y => h ((1 - t) • w + y)) ((fun z : ℂ => t • z) z) ∂volume := rfl
        _ = ∫⁻ z, (fun y => h ((1 - t) • w + y)) z ∂(Measure.map (fun z : ℂ => t • z) volume) :=
            (lintegral_map hfmeas hgmm).symm
        _ = ENNReal.ofReal (|(t ^ (Module.finrank ℝ ℂ))⁻¹|)
              * ∫⁻ z, h ((1 - t) • w + z) ∂volume := by
            rw [hmap, lintegral_smul_measure, smul_eq_mul]
        _ = ENNReal.ofReal (t ^ 2)⁻¹ * ∫⁻ y, h y ∂volume := by
            rw [lintegral_add_left_eq_self h ((1 - t) • w), hfr, abs_of_nonneg (by positivity)]
        _ = ENNReal.ofReal (t ^ 2)⁻¹ * G := by rw [hG, lintegral_indicator hBmeas]
    -- ============================================================
    -- (3) Averaging reduction: ‖u z - u_B‖ₑ ≤ ofReal((vol.real B)⁻¹) * ∫⁻_w∈B ‖u z - u w‖ₑ.
    -- ============================================================
    have hUintB : IntegrableOn u B volume :=
      (hucont.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
        ball_subset_closedBall
    have havg : ∀ z, u z - (⨍ w in B, u w ∂volume) = ⨍ w in B, (u z - u w) ∂volume := by
      intro z
      have hconstI : IntegrableOn (fun _ => u z) B volume := integrableOn_const hBfin
      rw [setAverage_eq, setAverage_eq, integral_sub hconstI hUintB, setIntegral_const,
        smul_sub, smul_smul, mul_comm, mul_inv_cancel₀, one_smul]
      rw [Measure.real]; simp only [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hBpos, hBfin⟩
    -- ============================================================
    -- (4) The double-integral bound.  Let D := ∫⁻_z∈B ∫⁻_w∈B ‖u z - u w‖ₑ.
    -- We bound  LHS ≤ ofReal((vol.real B)⁻¹) * D  and  D ≤ ofReal(8 r) * (vol B) * G,
    -- so the (vol.real B)⁻¹ cancels (vol B).
    -- ============================================================
    set D := ∫⁻ z in B, ∫⁻ w in B, ‖u z - u w‖ₑ ∂volume ∂volume with hD
    -- LHS ≤ ofReal((vol.real B)⁻¹) * D.
    have hLHS : ∫⁻ z in B, (‖u z - (⨍ w in B, u w ∂volume)‖ₑ) ∂volume ≤
        ENNReal.ofReal (volume.real B)⁻¹ * D := by
      rw [hD, ← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_mono_ae ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [havg z, setAverage_eq, enorm_smul]
      refine mul_le_mul' ?_ (enorm_integral_le_lintegral_enorm _)
      rw [Real.enorm_of_nonneg (by positivity)]
    -- ============================================================
    -- (5) Triple-integral bound for D.
    -- ============================================================
    -- joint measurability used repeatedly.
    have hjm : ∀ z : ℂ, Measurable (fun p : ℂ × ℝ => g (p.1 + p.2 • (z - p.1))) := by
      intro z; apply hgmeas.comp
      have heq : (fun p : ℂ × ℝ => p.1 + p.2 • (z - p.1))
          = fun p : ℂ × ℝ => p.1 + (p.2 : ℂ) * (z - p.1) := by
        funext p; rw [Complex.real_smul]
      rw [heq]; fun_prop
    -- D ≤ ofReal(2r) * T, where T is the triple integral.
    have hzw_le : ∀ z ∈ B, ∀ w ∈ B, ‖z - w‖ₑ ≤ ENNReal.ofReal (2 * r) := by
      intro z hz w hw
      rw [← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      have htri : ‖z - w‖ ≤ ‖z - x‖ + ‖x - w‖ := by
        calc ‖z - w‖ = ‖(z - x) + (x - w)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - x‖ + ‖x - w‖ := norm_add_le _ _
      rw [hB, mem_ball, dist_eq_norm] at hz hw
      rw [norm_sub_rev x w] at htri
      linarith [hz, hw]
    set T := ∫⁻ z in B, ∫⁻ w in B,
        (∫⁻ t in Set.Ioc (0:ℝ) 1, g (w + t • (z - w)) ∂volume) ∂volume ∂volume with hT
    have hDT : D ≤ ENNReal.ofReal (2 * r) * T := by
      rw [hD, hT, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' hBmeas]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' hBmeas]
      refine Filter.Eventually.of_forall (fun w hw => ?_)
      refine le_trans (hpoint z w) ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun s hs => ?_)
      rw [mul_comm (ENNReal.ofReal (2 * r))]
      exact mul_le_mul' (le_refl _) (hzw_le z hz w hw)
    -- T ≤ 4 * (vol B) * G.
    -- rewrite g(w+t(z-w)) = g((1-t)•w + t•z).
    have hrw : ∀ (z w : ℂ) (t : ℝ), g (w + t • (z - w)) = g ((1 - t) • w + t • z) := by
      intro z w t; congr 1; module
    -- T₁ over Ioc 0 (1/2): bound via swap (w ↔ t) and subW.
    have hT1 : (∫⁻ z in B, ∫⁻ w in B,
          (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
        ≤ 2 * G * volume B := by
      have hmeasJ : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • q.1 + q.2 • (0:ℂ))) := by
        apply hgmeas.comp
        have heq : (fun q : ℂ × ℝ => (1 - q.2) • q.1 + q.2 • (0:ℂ))
            = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1 := by
          funext q; rw [Complex.real_smul]; simp
        rw [heq]; fun_prop
      have hinner : ∀ z ∈ B, (∫⁻ w in B,
          (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume) ≤ 2 * G := by
        intro z hz
        have hJz : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • q.1 + q.2 • z)) := by
          apply hgmeas.comp
          have heq : (fun q : ℂ × ℝ => (1 - q.2) • q.1 + q.2 • z)
              = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1 + ((q.2 : ℝ) : ℂ) * z := by
            funext q; rw [Complex.real_smul, Complex.real_smul]
          rw [heq]; fun_prop
        have hswap : (∫⁻ w in B, (∫⁻ t in Set.Ioc (0:ℝ) (1/2),
              g ((1 - t) • w + t • z) ∂volume) ∂volume)
            = ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
                (∫⁻ w in B, g ((1 - t) • w + t • z) ∂volume) ∂volume := by
          rw [lintegral_lintegral_swap]
          exact (hJz.aemeasurable.comp_measurable
            (by fun_prop : Measurable (fun p : ℂ × ℝ => ((p.1, p.2) : ℂ × ℝ))))
        rw [hswap]
        calc ∫⁻ t in Set.Ioc (0:ℝ) (1/2), (∫⁻ w in B, g ((1 - t) • w + t • z) ∂volume) ∂volume
            ≤ ∫⁻ t in Set.Ioc (0:ℝ) (1/2), ENNReal.ofReal 4 * G ∂volume := by
              refine lintegral_mono_ae ?_
              rw [ae_restrict_iff' measurableSet_Ioc]
              refine Filter.Eventually.of_forall (fun t ht => ?_)
              simp only [Set.mem_Ioc] at ht
              have ht0 : 0 < 1 - t := by linarith [ht.2]
              have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, by linarith [ht.2]⟩
              refine le_trans (subW z hz t ht0 htIcc) ?_
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (le_refl _)
              have hb : (1/2 : ℝ) ≤ 1 - t := by linarith [ht.2]
              rw [inv_le_iff_one_le_mul₀ (by positivity)]
              nlinarith [hb]
          _ = ENNReal.ofReal 4 * G * volume (Set.Ioc (0:ℝ) (1/2)) := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ = 2 * G := by
              rw [Real.volume_Ioc, show ENNReal.ofReal 4 = (4:ℝ≥0∞) by norm_num,
                show ENNReal.ofReal ((1:ℝ)/2 - 0) = (1/2 : ℝ≥0∞) by
                  rw [show (1:ℝ)/2 - 0 = (2:ℝ)⁻¹ by norm_num,
                    ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
                mul_right_comm, show (4:ℝ≥0∞) * (1/2) = 2 from by
                  rw [one_div, show (4:ℝ≥0∞) = 2 * 2 from by norm_num, mul_assoc,
                    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]]
      calc (∫⁻ z in B, ∫⁻ w in B,
              (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          ≤ ∫⁻ z in B, 2 * G ∂volume := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' hBmeas]
            exact Filter.Eventually.of_forall hinner
        _ = 2 * G * volume B := by rw [lintegral_const, Measure.restrict_apply_univ]
    -- T₂ over Ioc (1/2) 1: bound via swap (z ↔ t) and subZ.
    have hT2 : (∫⁻ z in B, ∫⁻ w in B,
          (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
        ≤ 2 * G * volume B := by
      -- swap z and w outermost first (Tonelli), then proceed symmetrically.
      have hswapOuter : (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          = (∫⁻ w in B, ∫⁻ z in B,
            (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume) := by
        have hf : Measurable (Function.uncurry (fun z w : ℂ => ∫⁻ t in Set.Ioc (1/2) (1:ℝ),
            g ((1 - t) • w + t • z) ∂volume)) := by
          have hf2 : Measurable (fun q : (ℂ × ℂ) × ℝ => g ((1 - q.2) • q.1.2 + q.2 • q.1.1)) := by
            apply hgmeas.comp
            have heq : (fun q : (ℂ × ℂ) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1)
                = fun q : (ℂ × ℂ) × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1.2 + ((q.2 : ℝ) : ℂ) * q.1.1 := by
              funext q; rw [Complex.real_smul, Complex.real_smul]
            rw [heq]; fun_prop
          exact hf2.lintegral_prod_right'
        exact lintegral_lintegral_swap hf.aemeasurable
      rw [hswapOuter]
      have hinner : ∀ w ∈ B, (∫⁻ z in B,
          (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume) ≤ 2 * G := by
        intro w hw
        have hJw : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • w + q.2 • q.1)) := by
          apply hgmeas.comp
          have heq : (fun q : ℂ × ℝ => (1 - q.2) • w + q.2 • q.1)
              = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * w + ((q.2 : ℝ) : ℂ) * q.1 := by
            funext q; rw [Complex.real_smul, Complex.real_smul]
          rw [heq]; fun_prop
        have hswap : (∫⁻ z in B, (∫⁻ t in Set.Ioc (1/2) (1:ℝ),
              g ((1 - t) • w + t • z) ∂volume) ∂volume)
            = ∫⁻ t in Set.Ioc (1/2) (1:ℝ),
                (∫⁻ z in B, g ((1 - t) • w + t • z) ∂volume) ∂volume := by
          rw [lintegral_lintegral_swap]
          exact (hJw.aemeasurable.comp_measurable
            (by fun_prop : Measurable (fun p : ℂ × ℝ => ((p.1, p.2) : ℂ × ℝ))))
        rw [hswap]
        calc ∫⁻ t in Set.Ioc (1/2) (1:ℝ), (∫⁻ z in B, g ((1 - t) • w + t • z) ∂volume) ∂volume
            ≤ ∫⁻ t in Set.Ioc (1/2) (1:ℝ), ENNReal.ofReal 4 * G ∂volume := by
              refine lintegral_mono_ae ?_
              rw [ae_restrict_iff' measurableSet_Ioc]
              refine Filter.Eventually.of_forall (fun t ht => ?_)
              simp only [Set.mem_Ioc] at ht
              have ht0 : 0 < t := by linarith [ht.1]
              have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht.2⟩
              refine le_trans (subZ w hw t ht0 htIcc) ?_
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (le_refl _)
              have hb : (1/2 : ℝ) ≤ t := by linarith [ht.1]
              rw [inv_le_iff_one_le_mul₀ (by positivity)]
              nlinarith [hb]
          _ = ENNReal.ofReal 4 * G * volume (Set.Ioc (1/2) (1:ℝ)) := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ = 2 * G := by
              rw [Real.volume_Ioc, show ENNReal.ofReal 4 = (4:ℝ≥0∞) by norm_num,
                show ENNReal.ofReal ((1:ℝ) - 1/2) = (1/2 : ℝ≥0∞) by
                  rw [show (1:ℝ) - 1/2 = (2:ℝ)⁻¹ by norm_num,
                    ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
                mul_right_comm, show (4:ℝ≥0∞) * (1/2) = 2 from by
                  rw [one_div, show (4:ℝ≥0∞) = 2 * 2 from by norm_num, mul_assoc,
                    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]]
      calc (∫⁻ w in B, ∫⁻ z in B,
              (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          ≤ ∫⁻ w in B, 2 * G ∂volume := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' hBmeas]
            exact Filter.Eventually.of_forall hinner
        _ = 2 * G * volume B := by rw [lintegral_const, Measure.restrict_apply_univ]
    -- assemble T ≤ 4 vol B G via the t-split.
    have hT4 : T ≤ 4 * volume B * G := by
      have hTconv : T = ∫⁻ z in B, ∫⁻ w in B,
          (∫⁻ t in Set.Ioc (0:ℝ) 1, g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume := by
        rw [hT]; simp only [hrw]
      rw [hTconv]
      have hsplit : ∀ z w : ℂ,
          (∫⁻ t in Set.Ioc (0:ℝ) 1, g ((1 - t) • w + t • z) ∂volume)
            = (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume)
              + (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) := by
        intro z w
        have hdisj : Disjoint (Set.Ioc (0:ℝ) (1/2)) (Set.Ioc (1/2) 1) := by
          simp only [Set.disjoint_left]
          intro a h1 h2
          simp only [Set.mem_Ioc] at h1 h2
          linarith [h1.2, h2.1]
        rw [← lintegral_union measurableSet_Ioc hdisj,
          Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)]
      have hTeq : (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (0:ℝ) 1, g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          = (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          + (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume) := by
        have hmeasA : Measurable (fun z : ℂ => ∫⁻ w in B, ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
            g ((1 - t) • w + t • z) ∂volume ∂volume) := by
          have hf2 : Measurable (fun q : (ℂ × ℂ) × ℝ => g ((1 - q.2) • q.1.2 + q.2 • q.1.1)) := by
            apply hgmeas.comp
            have heq : (fun q : (ℂ × ℂ) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1)
                = fun q : (ℂ × ℂ) × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1.2 + ((q.2 : ℝ) : ℂ) * q.1.1 := by
              funext q; rw [Complex.real_smul, Complex.real_smul]
            rw [heq]; fun_prop
          have hf3 : Measurable (fun p : ℂ × ℂ => ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
              g ((1 - t) • p.2 + t • p.1) ∂volume) := hf2.lintegral_prod_right'
          exact hf3.lintegral_prod_right'
        rw [← lintegral_add_left' hmeasA.aemeasurable.restrict]
        refine lintegral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        have hmeasAw : Measurable (fun w : ℂ => ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
            g ((1 - t) • w + t • z) ∂volume) := by
          have hf2 : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • q.1 + q.2 • z)) := by
            apply hgmeas.comp
            have heq : (fun q : ℂ × ℝ => (1 - q.2) • q.1 + q.2 • z)
                = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1 + ((q.2 : ℝ) : ℂ) * z := by
              funext q; rw [Complex.real_smul, Complex.real_smul]
            rw [heq]; fun_prop
          exact hf2.lintegral_prod_right'
        simp only []
        rw [← lintegral_add_left' hmeasAw.aemeasurable.restrict]
        refine lintegral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        exact hsplit z w
      rw [hTeq]
      calc _ ≤ 2 * G * volume B + 2 * G * volume B := add_le_add hT1 hT2
        _ = 4 * volume B * G := by ring
    -- ============================================================
    -- (6) Assemble:  LHS ≤ ofReal((vol.real B)⁻¹) * D ≤ ofReal((vol.real B)⁻¹) * ofReal(2r) * T
    --             ≤ ofReal((vol.real B)⁻¹) * ofReal(2r) * 4 * vol B * G = ofReal(8r) * G.
    -- ============================================================
    have hvoleq : volume B = ENNReal.ofReal (volume.real B) := by
      rw [Measure.real, ENNReal.ofReal_toReal hBfin]
    calc ∫⁻ z in B, (‖u z - (⨍ w in B, u w ∂volume)‖ₑ) ∂volume
        ≤ ENNReal.ofReal (volume.real B)⁻¹ * D := hLHS
      _ ≤ ENNReal.ofReal (volume.real B)⁻¹ * (ENNReal.ofReal (2 * r) * T) :=
          mul_le_mul' (le_refl _) hDT
      _ ≤ ENNReal.ofReal (volume.real B)⁻¹ * (ENNReal.ofReal (2 * r) * (4 * volume B * G)) :=
          mul_le_mul' (le_refl _) (mul_le_mul' (le_refl _) hT4)
      _ = ENNReal.ofReal (8 * r) * G := by
          rw [hvoleq]
          rw [show ENNReal.ofReal (volume.real B)⁻¹ *
              (ENNReal.ofReal (2 * r) * (4 * ENNReal.ofReal (volume.real B) * G))
            = (ENNReal.ofReal (volume.real B)⁻¹ * ENNReal.ofReal (volume.real B))
              * (ENNReal.ofReal (2 * r) * 4 * G) from by ring]
          rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (ne_of_gt hBrpos),
            ENNReal.ofReal_one, one_mul]
          rw [show ENNReal.ofReal (2 * r) * 4 = ENNReal.ofReal (8 * r) from by
            rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num,
              ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring]
  have conv_tendsto : ∀ {g : ℂ → ℂ},
      MemLp g 2 volume → ∀ (φ : ℕ → ContDiffBump (0 : ℂ)),
      Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - g) 2 volume)
        Filter.atTop (nhds 0) := by
    intro g hg φ hφrout
    set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
      g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
    have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
        Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) h
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
          Filter.atTop (nhds 0) := by
      intro h hh_supp hh_smooth
      obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
      have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
      set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
      have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
      have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
      have hKfin : volume Kset < ⊤ := hKcompact.measure_lt_top
      have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
      set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
        h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
      have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
        HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
        ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
      have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
        intro n x
        set ρ := (φ n).normed volume with hρ
        have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
        rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
        calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
            ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t, ρ t * M ∂volume := by
              have hint : Integrable ρ volume :=
                ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                  ((φ n).hasCompactSupport_normed)
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
              refine Filter.Eventually.of_forall (fun t => ?_)
              simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
              exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
          _ = (∫ t, ρ t ∂volume) * M := by rw [integral_mul_const]
          _ = M := by rw [(φ n).integral_normed]; ring
      have hMh : ∀ y, ‖h y‖ ≤ M := hM
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
        have hsub := MeasureTheory.support_convolution_subset (μ := volume)
          (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
          (f := (φ n).normed volume) (g := h)
        refine hsub.trans (le_trans ?_ haddsub)
        apply Set.add_subset_add _ (subset_tsupport h)
        intro z hz
        have h1 : z ∈ tsupport ((φ n).normed volume) := subset_tsupport _ hz
        rwa [(φ n).tsupport_normed_eq] at h1
      haveI : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
        constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
      set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
      have hrestrict : ∀ᶠ n in Filter.atTop,
          eLpNorm (D n) 2 volume = eLpNorm (D n) 2 (volume.restrict Kset) := by
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
      have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Kset))
          Filter.atTop (nhds 0) := by
        have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
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
        have hhmem : MemLp h 2 (volume.restrict Kset) :=
          MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
            (Filter.Eventually.of_forall hMh)
        exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
          (Filter.Eventually.of_forall hptwise)
      exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
    have hP2 : ∀ (u : ℂ → ℂ), MemLp u 2 volume → ∀ (ε : ℝ),
        eLpNorm u 2 volume ≤ ENNReal.ofReal ε → ∀ n,
          eLpNorm (MeasureTheory.convolution ((φ n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
      intro u hu ε hclose n
      set ρc : ℂ → ℂ := fun z => (((φ n).normed volume z : ℝ) : ℂ) with hρc
      have hconv_eq : MeasureTheory.convolution ((φ n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          = MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ) volume := by
        funext x
        rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
        exact (Complex.real_smul).symm
      rw [hconv_eq]
      have hρc_memLp : MemLp ρc 1 volume := by
        have hcont : Continuous ρc :=
          Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
        have hsupp : HasCompactSupport ρc :=
          ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
        exact hcont.memLp_of_hasCompactSupport hsupp
      have hρc_norm : eLpNorm ρc 1 volume = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hint : Integrable ((φ n).normed volume) volume :=
          ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
            ((φ n).hasCompactSupport_normed)
        have hnn : 0 ≤ᵐ[volume] (φ n).normed volume :=
          Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
        calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
            = ∫⁻ z, ENNReal.ofReal ((φ n).normed volume z) ∂volume := by
              refine lintegral_congr (fun z => ?_)
              rw [hρc,
                show ‖(((φ n).normed volume z : ℝ) : ℂ)‖ₑ
                    = ‖(φ n).normed volume z‖ₑ from by
                  rw [← enorm_norm, Complex.norm_real, enorm_norm],
                Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
          _ = ENNReal.ofReal (∫ z, (φ n).normed volume z ∂volume) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ = 1 := by rw [(φ n).integral_normed]; simp
      calc eLpNorm (MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ)
              volume) 2 volume
          ≤ eLpNorm ρc 1 volume * eLpNorm u 2 volume :=
            eLpNorm_convolution_le hρc_memLp hu
        _ = eLpNorm u 2 volume := by rw [hρc_norm, one_mul]
        _ ≤ ENNReal.ofReal ε := hclose
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [htop]; exact le_top
    set δ : ℝ := ε.toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
    have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
    obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ε := δ / 3) (by positivity)
    have hh_memLp : MemLp hh 2 volume :=
      hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
    have hgh_memLp : MemLp (g - hh) 2 volume := hg.sub hh_memLp
    have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      hP2 (g - hh) hgh_memLp (δ / 3) hh_close
    have hP3ev : ∀ᶠ n in Filter.atTop,
        eLpNorm (MeasureTheory.convolution ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
        (ENNReal.ofReal_pos.mpr (by positivity)))
    have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g) := by
      intro n
      have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed volume) (g - hh)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous ?_
        exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
      have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        rw [hCg]; simp only
        rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
        congr 1; abel
      rw [hsplit]; abel
    filter_upwards [hP3ev] with n hn3
    rw [hdecomp n]
    have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) volume :=
      (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        ((hg.locallyIntegrable (by norm_num)).sub
          hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
        volume - hh) volume :=
      ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (hh - g) volume :=
      (hh_memLp.sub hg).1
    have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g)) 2
          volume
        ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
      refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
      refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
      · exact add_le_add (hP2gh n) hn3
      · rw [eLpNorm_sub_comm]; exact hh_close
    refine le_trans hkey ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
    apply le_of_eq; congr 1; ring
  have fderiv_conv : ∀ {f gv : ℂ → ℂ} {v : ℂ},
      HasWeakDirDeriv v gv f Set.univ →
      MeasureTheory.LocallyIntegrable f → MeasureTheory.LocallyIntegrable gv →
      ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      HasCompactSupport ρ → ∀ (z : ℂ),
        (fderiv ℝ (MeasureTheory.convolution ρ f
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
          = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro f gv v hv hf hgv ρ hρ_smooth hρ_supp z
    have _hgv := hgv
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
    have hρ_diff : Differentiable ℝ ρ :=
      hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
    have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
    have hderiv :
        HasFDerivAt (MeasureTheory.convolution ρ f L volume)
          (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
    rw [hderiv.fderiv]
    have hconvexists :
        MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) volume :=
      (hdρ_supp.convolutionExists_left (L.precompL ℂ)
        (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
    rw [MeasureTheory.convolution_def,
        ContinuousLinearMap.integral_apply hconvexists.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
    have hcv :
        (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂volume)
          = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume := by
      have hself := MeasureTheory.integral_sub_left_eq_self
        (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) volume z
      simp only [sub_sub_cancel] at hself
      exact hself.symm
    refine hcv.trans ?_
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
        (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume)
          = -∫ u, ((fderiv ℝ φz u) v) • f u ∂volume := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
      rw [hφz_fderiv u]
      rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
        from neg_smul _ _, neg_neg]
    rw [hint_eq]
    have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
      hρ_smooth.comp (contDiff_const.sub contDiff_id)
    have hφz_supp : HasCompactSupport φz :=
      hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
    have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
    rw [hwd, neg_neg]
    rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
        (fun t => (L (ρ t)) (gv (z - t))) volume z]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
    rfl
  -- L¹(B) integral convergence helper (from L²(B) convergence). 
  have limconv : ∀ (B : Set ℂ), MeasurableSet B → volume B ≠ ⊤ →
      ∀ (fF : ℂ → ℂ) (fnF : ℕ → ℂ → ℂ),
      (∀ n, AEStronglyMeasurable (fnF n) volume) → AEStronglyMeasurable fF volume →
      (∫⁻ z in B, ‖fF z‖ₑ ∂volume) ≠ ⊤ →
      Tendsto (fun n => eLpNorm (fun z => fnF n z - fF z) 2 (volume.restrict B)) atTop (𝓝 0) →
      Tendsto (fun n => ∫⁻ z in B, ‖fnF n z‖ₑ ∂volume) atTop
        (𝓝 (∫⁻ z in B, ‖fF z‖ₑ ∂volume)) := by
    intro B hBmeas hBfin f fn hfm hfm0 hIffin hconv
    have hdist : Tendsto (fun n => ∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume) atTop (𝓝 0) := by
      have hbound : ∀ n, (∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume)
          ≤ eLpNorm (fun z => fn n z - f z) 2 (volume.restrict B) * (volume B) ^ (1/2 : ℝ) := by
        intro n
        have h1 : (∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume)
            = eLpNorm (fun z => fn n z - f z) 1 (volume.restrict B) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
        rw [h1]
        have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B)
          (p := 1) (q := 2) (f := fun z => fn n z - f z) (by norm_num)
          ((hfm n).sub hfm0).restrict
        rw [Measure.restrict_apply_univ,
          show (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2) = (1/2 : ℝ) by norm_num] at hle
        exact hle
      have hVBfin : ((volume B) ^ (1/2 : ℝ)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
      have hrhs : Tendsto (fun n => eLpNorm (fun z => fn n z - f z) 2 (volume.restrict B)
          * (volume B) ^ (1/2 : ℝ)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hconv (Or.inr hVBfin); simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞)) tendsto_const_nhds
        hrhs (fun n => zero_le _) hbound
    set If := ∫⁻ z in B, ‖f z‖ₑ ∂volume with hIf
    set dn := fun n => ∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume with hdn
    have hae : ∀ n, AEMeasurable (fun z => ‖fn n z - f z‖ₑ) (volume.restrict B) :=
      fun n => (((hfm n).sub hfm0).restrict).aemeasurable.enorm
    have key1 : ∀ n, (∫⁻ z in B, ‖fn n z‖ₑ ∂volume) ≤ If + dn n := by
      intro n
      have : If + dn n = ∫⁻ z in B, (‖f z‖ₑ + ‖fn n z - f z‖ₑ) ∂volume := by
        rw [hIf, hdn]; simp only []; rw [lintegral_add_right' _ (hae n)]
      rw [this]
      refine lintegral_mono (fun z => ?_)
      calc ‖fn n z‖ₑ = ‖f z + (fn n z - f z)‖ₑ := by congr 1; ring
        _ ≤ ‖f z‖ₑ + ‖fn n z - f z‖ₑ := enorm_add_le _ _
    have key2 : ∀ n, If ≤ (∫⁻ z in B, ‖fn n z‖ₑ ∂volume) + dn n := by
      intro n
      have : (∫⁻ z in B, ‖fn n z‖ₑ ∂volume) + dn n
          = ∫⁻ z in B, (‖fn n z‖ₑ + ‖fn n z - f z‖ₑ) ∂volume := by
        rw [hdn]; simp only []; rw [lintegral_add_right' _ (hae n)]
      rw [this, hIf]
      refine lintegral_mono (fun z => ?_)
      calc ‖f z‖ₑ = ‖fn n z + (f z - fn n z)‖ₑ := by congr 1; ring
        _ ≤ ‖fn n z‖ₑ + ‖f z - fn n z‖ₑ := enorm_add_le _ _
        _ = ‖fn n z‖ₑ + ‖fn n z - f z‖ₑ := by rw [← enorm_neg (fn n z - f z), neg_sub]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun n => If - dn n) (h := fun n => If + dn n) ?_ ?_ ?_ key1
    · have : Tendsto (fun n => If - dn n) atTop (𝓝 (If - 0)) :=
        ENNReal.Tendsto.sub tendsto_const_nhds hdist (Or.inr (by simp))
      simpa using this
    · have : Tendsto (fun n => If + dn n) atTop (𝓝 (If + 0)) :=
        Tendsto.add tendsto_const_nhds hdist
      simpa using this
    · intro n; exact tsub_le_iff_right.mpr (key2 n)
  -- average convergence helper.
  have avgconv : ∀ (B : Set ℂ), volume B ≠ ⊤ → volume B ≠ 0 →
      ∀ (fF : ℂ → ℂ) (fnF : ℕ → ℂ → ℂ),
      (∀ n, IntegrableOn (fnF n) B volume) → IntegrableOn fF B volume →
      Tendsto (fun n => eLpNorm (fun z => fnF n z - fF z) 1 (volume.restrict B)) atTop (𝓝 0) →
      Tendsto (fun n => ⨍ w in B, fnF n w ∂volume) atTop (𝓝 (⨍ w in B, fF w ∂volume)) := by
    intro B hBfin hBpos F Fn hFn_int hF_int hconvF
    haveI : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖(⨍ w in B, Fn n w ∂volume) - (⨍ w in B, F w ∂volume)‖
        ≤ (volume.real B)⁻¹ * (eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)).toReal := by
      intro n
      set g : ℂ → ℂ := fun z => Fn n z - F z with hgdef
      have hgint : IntegrableOn g B volume := (hFn_int n).sub hF_int
      rw [setAverage_eq, setAverage_eq, ← smul_sub,
        show (∫ x in B, Fn n x ∂volume) - ∫ x in B, F x ∂volume = ∫ x in B, g x ∂volume from
          (integral_sub (hFn_int n) hF_int).symm,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      rw [eLpNorm_one_eq_lintegral_enorm]
      calc ‖∫ z in B, g z ∂volume‖
          ≤ ∫ z in B, ‖g z‖ ∂volume := norm_integral_le_integral_norm _
        _ = (∫⁻ z in B, ‖g z‖ₑ ∂volume).toReal := by
            rw [integral_norm_eq_lintegral_enorm hgint.aestronglyMeasurable]
    have hrhs : Tendsto (fun n => (volume.real B)⁻¹ *
        (eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)).toReal) atTop (𝓝 0) := by
      have htoreal : Tendsto
          (fun n => (eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)).toReal)
          atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal (by norm_num)).comp hconvF; simpa using this
      have := htoreal.const_mul ((volume.real B)⁻¹); simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) hbound hrhs
  -- LHS oscillation L²(B) convergence helper.
  have lhsconv : ∀ (B : Set ℂ), volume B ≠ ⊤ → volume B ≠ 0 →
      ∀ (fF : ℂ → ℂ) (fnF : ℕ → ℂ → ℂ),
      (∀ n, Continuous (fnF n)) → MemLp fF 2 volume →
      Tendsto (fun n => eLpNorm (fun z => fnF n z - fF z) 2 (volume.restrict B)) atTop (𝓝 0) →
      Tendsto (fun n => (⨍ w in B, fnF n w ∂volume) - (⨍ w in B, fF w ∂volume)) atTop (𝓝 0) →
      Tendsto (fun n => eLpNorm (fun z => (fnF n z - (⨍ w in B, fnF n w ∂volume))
          - (fF z - (⨍ w in B, fF w ∂volume))) 2 (volume.restrict B)) atTop (𝓝 0) := by
    intro B hBfin hBpos F Fn hFn_cont hFmem hconvF hcn
    haveI : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
    have hμne : (volume.restrict B) ≠ 0 := by
      rw [← Measure.measure_univ_ne_zero, Measure.restrict_apply_univ]; exact hBpos
    set cn : ℕ → ℂ := fun n => (⨍ w in B, Fn n w ∂volume) - (⨍ w in B, F w ∂volume) with hcndef
    have hbound : ∀ n, eLpNorm (fun z => (Fn n z - (⨍ w in B, Fn n w ∂volume))
          - (F z - (⨍ w in B, F w ∂volume))) 2 (volume.restrict B)
        ≤ eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B)
          + ‖cn n‖ₑ * (volume B) ^ (1 / (2:ℝ)) := by
      intro n
      have heq : (fun z => (Fn n z - (⨍ w in B, Fn n w ∂volume))
            - (F z - (⨍ w in B, F w ∂volume)))
          = (fun z => (Fn n z - F z) + (fun _ : ℂ => -cn n) z) := by
        funext z; simp only [hcndef]; ring
      rw [heq]
      refine le_trans (eLpNorm_add_le (((hFn_cont n).aestronglyMeasurable.sub hFmem.1).restrict)
        aestronglyMeasurable_const (by norm_num)) ?_
      gcongr
      rw [eLpNorm_const (-cn n) (by norm_num) hμne, Measure.restrict_apply_univ, enorm_neg,
        show (1 / ENNReal.toReal 2) = (1/2 : ℝ) by norm_num]
    have hrhs : Tendsto (fun n => eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B)
        + ‖cn n‖ₑ * (volume B) ^ (1 / (2:ℝ))) atTop (𝓝 0) := by
      have hc : Tendsto (fun n => ‖cn n‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0:ℂ)).comp hcn; simpa using this
      have hVBfin : ((volume B) ^ (1/2 : ℝ)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
      have hc2 : Tendsto (fun n => ‖cn n‖ₑ * (volume B) ^ (1 / (2:ℝ))) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hc (Or.inr hVBfin); simpa using this
      have := hconvF.add hc2; simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds hrhs (fun n => zero_le _) hbound
  -- ============================================================
  -- WIRING: mollify F, apply the smooth Poincaré, pass to the limit.
  -- ============================================================
  set B := ball x r with hB
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hBpos : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hF_li : MeasureTheory.LocallyIntegrable F := hF.locallyIntegrable (by norm_num)
  have hGx_li : MeasureTheory.LocallyIntegrable Gx := hGx.locallyIntegrable (by norm_num)
  have hGy_li : MeasureTheory.LocallyIntegrable Gy := hGy.locallyIntegrable (by norm_num)
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Tendsto (fun n => (φ₀ n).rOut) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set ρ : ℕ → ℂ → ℝ := fun n => (φ₀ n).normed volume with hρ
  have hρ_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n => (φ₀ n).contDiff_normed
  have hρ_cs : ∀ n, HasCompactSupport (ρ n) := fun n => (φ₀ n).hasCompactSupport_normed
  have hρ_cont : ∀ n, Continuous (ρ n) := fun n => (hρ_smooth n).continuous
  set Fn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) F (ContinuousLinearMap.lsmul ℝ ℝ) volume with hFn
  set Gxn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume with hGxn
  set Gyn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume with hGyn
  have hFn_cd : ∀ n, ContDiff ℝ 1 (Fn n) := fun n =>
    HasCompactSupport.contDiff_convolution_left _ (hρ_cs n)
      ((hρ_smooth n).of_le (by exact_mod_cast le_top)) hF_li
  have hdx : ∀ n z, (fderiv ℝ (Fn n) z) 1 = Gxn n z := fun n z =>
    fderiv_conv hGxw hF_li hGx_li (hρ_smooth n) (hρ_cs n) z
  have hdy : ∀ n z, (fderiv ℝ (Fn n) z) Complex.I = Gyn n z := fun n z =>
    fderiv_conv hGyw hF_li hGy_li (hρ_smooth n) (hρ_cs n) z
  have hGxn_cont : ∀ n, Continuous (Gxn n) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρ_cs n) (hρ_cont n) hGx_li
  have hGyn_cont : ∀ n, Continuous (Gyn n) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρ_cs n) (hρ_cont n) hGy_li
  haveI hBfinm : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
  -- L²(B) and L¹(B) convergence of Fn, Gxn, Gyn.
  have hconvF2 : Tendsto (fun n => eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds (conv_tendsto hF φ₀ hφ₀rout) (fun n => zero_le _)
      (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hconvGx : Tendsto (fun n => eLpNorm (fun z => Gxn n z - Gx z) 2 (volume.restrict B))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds (conv_tendsto hGx φ₀ hφ₀rout) (fun n => zero_le _)
      (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hconvGy : Tendsto (fun n => eLpNorm (fun z => Gyn n z - Gy z) 2 (volume.restrict B))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds (conv_tendsto hGy φ₀ hφ₀rout) (fun n => zero_le _)
      (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hconvF1 : Tendsto (fun n => eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B))
      atTop (𝓝 0) := by
    have hb : ∀ n, eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)
        ≤ eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B) * (volume B) ^ (1/2 : ℝ) := by
      intro n
      have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B)
        (p := 1) (q := 2) (f := fun z => Fn n z - F z) (by norm_num)
        (((hFn_cd n).continuous.aestronglyMeasurable.sub hF.1).restrict)
      rwa [Measure.restrict_apply_univ,
        show (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2) = (1/2 : ℝ) by norm_num] at hle
    have hVBfin : ((volume B) ^ (1/2 : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds ?_ (fun n => zero_le _) hb
    have := ENNReal.Tendsto.mul_const hconvF2 (Or.inr hVBfin); simpa using this
  have hFn_intB : ∀ n, IntegrableOn (Fn n) B volume := fun n =>
    ((hFn_cd n).continuous.locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hF_intB : IntegrableOn F B volume :=
    (hF_li.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have havgconv : Tendsto (fun n => (⨍ w in B, Fn n w ∂volume) - (⨍ w in B, F w ∂volume))
      atTop (𝓝 0) := by
    have h0 := avgconv B hBfin hBpos F Fn hFn_intB hF_intB hconvF1
    have := h0.sub (tendsto_const_nhds (x := ⨍ w in B, F w ∂volume)); simpa using this
  have hLHSconv : Tendsto (fun n => eLpNorm (fun z => (Fn n z - (⨍ w in B, Fn n w ∂volume))
        - (F z - (⨍ w in B, F w ∂volume))) 2 (volume.restrict B)) atTop (𝓝 0) :=
    lhsconv B hBfin hBpos F Fn (fun n => (hFn_cd n).continuous) hF hconvF2 havgconv
  -- finiteness of the L¹(B) norms of F-F_B, Gx, Gy.
  have hGxfin : (∫⁻ z in B, ‖Gx z‖ₑ ∂volume) ≠ ⊤ := by
    have h1 : MemLp Gx 1 (volume.restrict B) := (hGx.restrict B).mono_exponent (by norm_num)
    have := h1.eLpNorm_lt_top; rw [eLpNorm_one_eq_lintegral_enorm] at this; exact this.ne
  have hGyfin : (∫⁻ z in B, ‖Gy z‖ₑ ∂volume) ≠ ⊤ := by
    have h1 : MemLp Gy 1 (volume.restrict B) := (hGy.restrict B).mono_exponent (by norm_num)
    have := h1.eLpNorm_lt_top; rw [eLpNorm_one_eq_lintegral_enorm] at this; exact this.ne
  have hOscfin : (∫⁻ z in B, ‖F z - (⨍ w in B, F w ∂volume)‖ₑ ∂volume) ≠ ⊤ := by
    have hmem : MemLp (fun z => F z - (⨍ w in B, F w ∂volume)) 1 (volume.restrict B) := by
      refine MemLp.sub ((hF.restrict B).mono_exponent (by norm_num)) ?_
      exact memLp_const _
    have := hmem.eLpNorm_lt_top; rw [eLpNorm_one_eq_lintegral_enorm] at this; exact this.ne
  -- Integral-convergence of LHS and RHS.
  have hRGx : Tendsto (fun n => ∫⁻ z in B, ‖Gxn n z‖ₑ ∂volume) atTop
      (𝓝 (∫⁻ z in B, ‖Gx z‖ₑ ∂volume)) :=
    limconv B hBmeas hBfin Gx Gxn (fun n => (hGxn_cont n).aestronglyMeasurable) hGx.1 hGxfin hconvGx
  have hRGy : Tendsto (fun n => ∫⁻ z in B, ‖Gyn n z‖ₑ ∂volume) atTop
      (𝓝 (∫⁻ z in B, ‖Gy z‖ₑ ∂volume)) :=
    limconv B hBmeas hBfin Gy Gyn (fun n => (hGyn_cont n).aestronglyMeasurable) hGy.1 hGyfin hconvGy
  have hLHSlim : Tendsto (fun n => ∫⁻ z in B, ‖(Fn n z - (⨍ w in B, Fn n w ∂volume))
        - (F z - (⨍ w in B, F w ∂volume)) + (F z - (⨍ w in B, F w ∂volume))‖ₑ ∂volume) atTop
      (𝓝 (∫⁻ z in B, ‖F z - (⨍ w in B, F w ∂volume)‖ₑ ∂volume)) := by
    refine limconv B hBmeas hBfin (fun z => F z - (⨍ w in B, F w ∂volume))
      (fun n z => (Fn n z - (⨍ w in B, Fn n w ∂volume)) - (F z - (⨍ w in B, F w ∂volume))
        + (F z - (⨍ w in B, F w ∂volume))) ?_ ?_ hOscfin ?_
    · intro n
      exact ((((hFn_cd n).continuous.aestronglyMeasurable.sub aestronglyMeasurable_const).sub
        (hF.1.sub aestronglyMeasurable_const)).add (hF.1.sub aestronglyMeasurable_const))
    · exact hF.1.sub aestronglyMeasurable_const
    · simpa using hLHSconv
  -- The per-n smooth Poincaré inequality.
  have hper : ∀ n, ∫⁻ z in B, ‖Fn n z - (⨍ w in B, Fn n w ∂volume)‖ₑ ∂volume
      ≤ ENNReal.ofReal (8 * r) *
        ((∫⁻ z in B, ‖Gxn n z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gyn n z‖ₑ ∂volume) := by
    intro n
    refine le_trans (smooth_poincare (Fn n) (hFn_cd n) x r hr) ?_
    refine mul_le_mul' (le_refl _) ?_
    -- ∫⁻_B ‖∇Fn‖ₑ ≤ ∫⁻_B (‖Gxn‖ₑ + ‖Gyn‖ₑ).
    rw [← lintegral_add_left' ((hGxn_cont n).aestronglyMeasurable.aemeasurable.enorm.restrict)]
    refine lintegral_mono (fun z => ?_)
    -- pointwise ‖fderiv (Fn n) z‖ₑ ≤ ‖(fderiv (Fn n) z) 1‖ₑ + ‖(fderiv (Fn n) z) I‖ₑ
    have hptw : ‖fderiv ℝ (Fn n) z‖ ≤
        ‖(fderiv ℝ (Fn n) z) 1‖ + ‖(fderiv ℝ (Fn n) z) Complex.I‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro w
      have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      have hmap : (fderiv ℝ (Fn n) z) w
          = w.re • (fderiv ℝ (Fn n) z) 1 + w.im • (fderiv ℝ (Fn n) z) Complex.I := by
        conv_lhs => rw [hdecomp]; rw [map_add, map_smul, map_smul]
      rw [hmap]
      calc ‖w.re • (fderiv ℝ (Fn n) z) 1 + w.im • (fderiv ℝ (Fn n) z) Complex.I‖
          ≤ ‖w.re • (fderiv ℝ (Fn n) z) 1‖ + ‖w.im • (fderiv ℝ (Fn n) z) Complex.I‖ :=
            norm_add_le _ _
        _ = |w.re| * ‖(fderiv ℝ (Fn n) z) 1‖ + |w.im| * ‖(fderiv ℝ (Fn n) z) Complex.I‖ := by
            rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖(fderiv ℝ (Fn n) z) 1‖ + ‖w‖ * ‖(fderiv ℝ (Fn n) z) Complex.I‖ := by
            gcongr
            · exact abs_re_le_norm w
            · exact abs_im_le_norm w
        _ = (‖(fderiv ℝ (Fn n) z) 1‖ + ‖(fderiv ℝ (Fn n) z) Complex.I‖) * ‖w‖ := by ring
    calc ‖fderiv ℝ (Fn n) z‖ₑ
        ≤ ‖(fderiv ℝ (Fn n) z) 1‖ₑ + ‖(fderiv ℝ (Fn n) z) Complex.I‖ₑ := by
          rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
            ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hptw
      _ = ‖Gxn n z‖ₑ + ‖Gyn n z‖ₑ := by rw [hdx n z, hdy n z]
  -- Pass to the limit.
  have hLHSeq : (fun n => ∫⁻ z in B, ‖(Fn n z - (⨍ w in B, Fn n w ∂volume))
        - (F z - (⨍ w in B, F w ∂volume)) + (F z - (⨍ w in B, F w ∂volume))‖ₑ ∂volume)
      = fun n => ∫⁻ z in B, ‖Fn n z - (⨍ w in B, Fn n w ∂volume)‖ₑ ∂volume := by
    funext n
    refine lintegral_congr (fun z => ?_)
    congr 1; ring
  rw [hLHSeq] at hLHSlim
  -- RHS limit.
  have hRHSlim : Tendsto (fun n => ENNReal.ofReal (8 * r) *
      ((∫⁻ z in B, ‖Gxn n z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gyn n z‖ₑ ∂volume)) atTop
      (𝓝 (ENNReal.ofReal (8 * r) *
        ((∫⁻ z in B, ‖Gx z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gy z‖ₑ ∂volume))) :=
    ENNReal.Tendsto.const_mul (hRGx.add hRGy)
      (Or.inr ENNReal.ofReal_ne_top)
  have hfinal : ∫⁻ z in B, ‖F z - (⨍ w in B, F w ∂volume)‖ₑ ∂volume
      ≤ ENNReal.ofReal (8 * r) *
        ((∫⁻ z in B, ‖Gx z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gy z‖ₑ ∂volume) :=
    le_of_tendsto_of_tendsto' hLHSlim hRHSlim hper
  -- Reconcile ‖·‖₊-coercions and the averaging notation with the goal.
  have hcoeL : (fun z => (‖F z - (⨍ w in B, F w)‖₊ : ℝ≥0∞))
      = fun z => ‖F z - (⨍ w in B, F w ∂volume)‖ₑ := by funext z; rw [← enorm_eq_nnnorm]
  have hcoeR : (fun z => (‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞))
      = fun z => ‖Gx z‖ₑ + ‖Gy z‖ₑ := by funext z; rw [← enorm_eq_nnnorm, ← enorm_eq_nnnorm]
  rw [show (⨍ w in B, F w) = (⨍ w in B, F w ∂volume) from rfl]
  rw [hcoeL]
  rw [show (∫⁻ z in B, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume)
      = ∫⁻ z in B, (‖Gx z‖ₑ + ‖Gy z‖ₑ) ∂volume from by rw [hcoeR]]
  rw [lintegral_add_left' (hGx.1.aemeasurable.enorm.restrict)]
  exact hfinal

/-- **Auxiliary: the constant function has weak directional derivative `0`.** A constant `c`
is `C¹` with vanishing Fréchet derivative, so the weak directional derivative supplied by
`HasWeakDirDeriv.of_contDiffOn` is the zero function. Used to subtract the centring constant
from the cutoff product in the Sobolev–Poincaré node N1. -/
private theorem hasWeakDirDeriv_const (v : ℂ) (c : ℂ) :
    HasWeakDirDeriv v (fun _ => (0 : ℂ)) (fun _ => c) (Set.univ : Set ℂ) := by
  have hcd : ContDiffOn ℝ 1 (fun _ : ℂ => c) (Set.univ : Set ℂ) :=
    (contDiff_const).contDiffOn
  have h := HasWeakDirDeriv.of_contDiffOn (v := v) isOpen_univ hcd
  -- `fderiv ℝ (const) = 0`, so the supplied weak derivative is the zero function.
  have hfd : (fun z => (fderiv ℝ (fun _ : ℂ => c) z) v) = (fun _ => (0 : ℂ)) := by
    funext z
    rw [show (fun _ : ℂ => c) = Function.const ℂ c from rfl, fderiv_const]
    rfl
  rwa [hfd] at h

/-- **Auxiliary: the compactly-supported `W^{1,1}→L²` Sobolev embedding.** A compactly
supported `MemLp 2` function `u` whose weak directional partials `gx` (direction `1`) and
`gy` (direction `I`) are `MemLp 1` satisfies the genuine planar endpoint Sobolev bound
`‖u‖_{L²} ≤ C·(‖gx‖_{L¹} + ‖gy‖_{L¹})` with the dimensional constant `C` of P1
(`eLpNorm_two_le_eLpNorm_fderiv_one`). Proof: mollify `u` to a `C¹` compactly-supported `w`
with `‖w − u‖_{L²} ≤ ε` and `‖∇w‖_{L¹} ≤ ‖gx‖₁ + ‖gy‖₁ + ε` (P3
`exists_contDiff_approx_W11`), apply P1 to `w`, and let `ε → 0`. This is the cutoff route's
only use of the P-stack; it returns the constant `C` of P1 unchanged. -/
private theorem sobolev_compactSupport_W11 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u gx gy : ℂ → ℂ},
      MemLp u 2 volume → HasCompactSupport u →
      HasWeakDirDeriv 1 gx u Set.univ → HasWeakDirDeriv Complex.I gy u Set.univ →
      MemLp gx 1 volume → MemLp gy 1 volume →
        eLpNorm u 2 volume ≤
          ENNReal.ofReal C * (eLpNorm gx 1 volume + eLpNorm gy 1 volume) := by
  obtain ⟨C, hC0, hP1⟩ := eLpNorm_two_le_eLpNorm_fderiv_one
  refine ⟨C, hC0, ?_⟩
  intro u gx gy hu2 hucs hgx hgy hgx1 hgy1
  -- The target bound holds with any positive slack `ε`; pass `ε → 0`.
  set RHS₀ : ℝ≥0∞ := ENNReal.ofReal C * (eLpNorm gx 1 volume + eLpNorm gy 1 volume) with hRHS₀
  have hslack : ∀ ε : ℝ, 0 < ε →
      eLpNorm u 2 volume ≤ RHS₀ + ENNReal.ofReal ((C + 1) * ε) := by
    intro ε hε
    obtain ⟨w, hwcd, hwcs, hwdist, hwgrad⟩ :=
      exists_contDiff_approx_W11 hu2 hucs hgx hgy hgx1 hgy1 hε
    -- P1 on the `C¹` compactly-supported approximant `w`.
    have hP1w : eLpNorm w 2 volume ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ w) 1 volume :=
      hP1 hwcd hwcs
    -- `‖u‖₂ ≤ ‖w‖₂ + ‖w − u‖₂`.
    have htri : eLpNorm u 2 volume
        ≤ eLpNorm w 2 volume + eLpNorm (fun z => w z - u z) 2 volume := by
      have hsub : eLpNorm (fun z => u z) 2 volume
          ≤ eLpNorm (fun z => w z) 2 volume + eLpNorm (fun z => u z - w z) 2 volume := by
        have hadd := eLpNorm_add_le (f := fun z => w z) (g := fun z => u z - w z)
          hwcd.continuous.aestronglyMeasurable (hu2.1.sub hwcd.continuous.aestronglyMeasurable)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have hfun : ((fun z => w z) + fun z => u z - w z) = (fun z => u z) := by
          funext z; simp
        rwa [hfun] at hadd
      -- `‖u − w‖₂ = ‖w − u‖₂`.
      have hflip : eLpNorm (fun z => u z - w z) 2 volume
          = eLpNorm (fun z => w z - u z) 2 volume := by
        rw [← eLpNorm_neg]; congr 1; funext z; simp
      rwa [hflip] at hsub
    -- Assemble: `‖u‖₂ ≤ ofReal C·(‖gx‖₁ + ‖gy‖₁ + ofReal ε) + ofReal ε`.
    refine le_trans htri ?_
    refine le_trans (add_le_add hP1w hwdist) ?_
    refine le_trans (add_le_add (by gcongr : ENNReal.ofReal C * eLpNorm (fderiv ℝ w) 1 volume
      ≤ ENNReal.ofReal C * (eLpNorm gx 1 volume + eLpNorm gy 1 volume + ENNReal.ofReal ε))
      le_rfl) ?_
    -- Distribute and collect into `RHS₀ + ofReal((C+1)·ε)`.
    rw [mul_add, mul_add]
    -- `ofReal C · ofReal ε = ofReal (C·ε)`; `ofReal ε = ofReal ε`.
    have hCe : ENNReal.ofReal C * ENNReal.ofReal ε = ENNReal.ofReal (C * ε) :=
      (ENNReal.ofReal_mul hC0).symm
    rw [hCe]
    have hsplit : ENNReal.ofReal ((C + 1) * ε)
        = ENNReal.ofReal (C * ε) + ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) hε.le]; congr 1; ring
    rw [hRHS₀, hsplit]
    -- Rearrange `(ofReal C·‖gx‖₁ + ofReal C·‖gy‖₁ + ofReal(C·ε)) + ofReal ε`.
    rw [mul_add]
    ring_nf
    -- After `ring_nf` both sides are sums of the same five `ℝ≥0∞` terms.
    rfl
  -- Pass to the limit `ε → 0⁺`: the slack `ofReal((C+1)·ε) → 0`.
  have hlim : Tendsto (fun ε : ℝ => RHS₀ + ENNReal.ofReal ((C + 1) * ε)) (𝓝[>] 0)
      (𝓝 (RHS₀ + 0)) := by
    refine Filter.Tendsto.const_add RHS₀ ?_
    have : Tendsto (fun ε : ℝ => ENNReal.ofReal ((C + 1) * ε)) (𝓝 0) (𝓝 (ENNReal.ofReal 0)) := by
      refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
      have : Tendsto (fun ε : ℝ => (C + 1) * ε) (𝓝 0) (𝓝 ((C + 1) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this
    rw [ENNReal.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hslack ε hε

/-! ## N1 — Sobolev–Poincaré on a ball for the `W^{1,2}` primitive -/

set_option maxHeartbeats 400000 in
-- Extracted Leibniz weak-derivative algebra for the N1 cutoff product, isolated so its
-- single self-contained elaboration stays within the heartbeat budget.
/-- **Auxiliary for N1: the cutoff weak partials.** The cutoff product `u = χ·(F − c)`
has Leibniz weak directional partials `χ·Gx + (∂₁χ)(F − c)` (direction `1`) and
`χ·Gy + (∂_I χ)(F − c)` (direction `I`). Proof: `HasWeakDirDeriv.smul_smooth` on `F` and
on the centring constant (`hasWeakDirDeriv_const`), combined by `HasWeakDirDeriv.sub`. -/
private theorem cutoff_weak_partials {F Gx Gy : ℂ → ℂ} {c : ℂ} {χ : ℂ → ℝ}
    (hFmem : MemLp F 2 volume) (hGxmem : MemLp Gx 2 volume) (hGymem : MemLp Gy 2 volume)
    (hGxweak : HasWeakDirDeriv 1 Gx F Set.univ)
    (hGyweak : HasWeakDirDeriv Complex.I Gy F Set.univ)
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) :
    HasWeakDirDeriv 1 (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c))
        (fun z => χ z • (F z - c)) Set.univ ∧
      HasWeakDirDeriv Complex.I (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c))
        (fun z => χ z • (F z - c)) Set.univ := by
  have hχcont : Continuous χ := hχcd.continuous
  set u : ℂ → ℂ := fun z => χ z • (F z - c) with hu_def
  -- Local integrability of `F` and the constant `c`.
  have hFloc : LocallyIntegrableOn F (Set.univ : Set ℂ) :=
    (hFmem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hGxloc : LocallyIntegrableOn Gx (Set.univ : Set ℂ) :=
    (hGxmem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hGyloc : LocallyIntegrableOn Gy (Set.univ : Set ℂ) :=
    (hGymem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hcloc : LocallyIntegrableOn (fun _ : ℂ => c) (Set.univ : Set ℂ) :=
    (locallyIntegrable_const c).locallyIntegrableOn _
  have hχsmoothTop : ContDiff ℝ (⊤ : ℕ∞) χ := hχcd
  -- Weak partials of `χ•F` and `χ•(const c)` via the Leibniz rule, then subtract.
  have hwF1 : HasWeakDirDeriv 1
      (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • F z) (fun z => χ z • F z) Set.univ :=
    hGxweak.smul_smooth hχsmoothTop hFloc hGxloc
  have hwc1 : HasWeakDirDeriv 1
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c) (fun z => χ z • c) Set.univ :=
    (hasWeakDirDeriv_const 1 c).smul_smooth hχsmoothTop hcloc
      ((locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _)
  have hwF2 : HasWeakDirDeriv Complex.I
      (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z) (fun z => χ z • F z) Set.univ :=
    hGyweak.smul_smooth hχsmoothTop hFloc hGyloc
  have hwc2 : HasWeakDirDeriv Complex.I
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c) (fun z => χ z • c) Set.univ :=
    (hasWeakDirDeriv_const Complex.I c).smul_smooth hχsmoothTop hcloc
      ((locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _)
  have hdχcont : Continuous (fun z => (fderiv ℝ χ z) 1) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχIcont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hzeroloc : LocallyIntegrableOn (fun _ : ℂ => (0 : ℂ)) (Set.univ : Set ℂ) :=
    (locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _
  have hχFloc : LocallyIntegrableOn (fun z => χ z • F z) (Set.univ : Set ℂ) :=
    MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hFloc
      hχcont.continuousOn
  have hχcloc : LocallyIntegrableOn (fun z => χ z • c) (Set.univ : Set ℂ) :=
    MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hcloc
      hχcont.continuousOn
  have hg1F_loc : LocallyIntegrableOn
      (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • F z) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hGxloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hFloc
        hdχcont.continuousOn)
  have hg2F_loc : LocallyIntegrableOn
      (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hGyloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hFloc
        hdχIcont.continuousOn)
  have hg1c_loc : LocallyIntegrableOn
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hzeroloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hcloc
        hdχcont.continuousOn)
  have hg2c_loc : LocallyIntegrableOn
      (fun z => χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c) (Set.univ : Set ℂ) :=
    (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hzeroloc
      hχcont.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_univ.isLocallyClosed hcloc
        hdχIcont.continuousOn)
  set gxu : ℂ → ℂ := fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c) with hgxu_def
  set gyu : ℂ → ℂ := fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c) with hgyu_def
  have hu_eq : u = fun z => χ z • F z - χ z • c := by
    funext z
    change χ z • (F z - c) = χ z • F z - χ z • c
    module
  have hgxu_eq : gxu = fun z => (χ z • Gx z + ((fderiv ℝ χ z) 1) • F z)
      - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c) := by
    funext z
    change χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)
      = (χ z • Gx z + ((fderiv ℝ χ z) 1) • F z) - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c)
    module
  have hgyu_eq : gyu = fun z => (χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z)
      - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c) := by
    funext z
    change χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)
      = (χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z)
        - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c)
    module
  have hxweak : HasWeakDirDeriv 1 gxu u Set.univ := by
    rw [hu_eq, hgxu_eq]
    exact hwF1.sub hwc1 hχFloc hχcloc hg1F_loc hg1c_loc
  have hyweak : HasWeakDirDeriv Complex.I gyu u Set.univ := by
    rw [hu_eq, hgyu_eq]
    exact hwF2.sub hwc2 hχFloc hχcloc hg2F_loc hg2c_loc
  exact ⟨hxweak, hyweak⟩

set_option maxHeartbeats 400000 in
-- The Leibniz weak-derivative algebra + `MemLp`-membership + Sobolev-embedding chain is a
-- single self-contained elaboration, so it needs a modestly raised heartbeat budget.
/-- **Auxiliary for N1: the cutoff Sobolev oscillation bound.** For a `W^{1,2}` primitive
`F` (weak partials `Gx, Gy`), a centring constant `c`, and a smooth compactly-supported
cutoff `χ`, the cutoff product `u = χ·(F − c)` satisfies the compactly-supported Sobolev
embedding `‖u‖_{L²} ≤ C₁·(‖gxu‖_{L¹} + ‖gyu‖_{L¹})` where `gxu = χ·Gx + (∂₁χ)(F − c)` and
`gyu = χ·Gy + (∂_I χ)(F − c)` are the Leibniz weak partials of `u`. The constant `C₁` is the
endpoint Sobolev constant of `sobolev_compactSupport_W11`. This packages the entire
weak-derivative-algebra + `MemLp` + Sobolev portion of the N1 proof into one lemma so the
main node only does the (lighter) integral bookkeeping. -/
private theorem cutoff_sobolev_oscL2 :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ {F Gx Gy : ℂ → ℂ} {c : ℂ} {χ : ℂ → ℝ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        eLpNorm (fun z => χ z • (F z - c)) 2 volume ≤
          ENNReal.ofReal C₁ *
            (eLpNorm (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)) 1 volume +
             eLpNorm (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)) 1 volume) := by
  obtain ⟨C₁, hC₁0, hSob⟩ := sobolev_compactSupport_W11
  refine ⟨C₁, hC₁0, ?_⟩
  intro F Gx Gy c χ hFmem hGxmem hGymem hGxweak hGyweak hχcd hχcs
  have hχcont : Continuous χ := hχcd.continuous
  have hdχcont : Continuous (fun z => (fderiv ℝ χ z) 1) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχIcont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨hxweak, hyweak⟩ :=
    cutoff_weak_partials (c := c) hFmem hGxmem hGymem hGxweak hGyweak hχcd
  haveI hHT221 : ENNReal.HolderTriple 2 2 1 := ⟨by
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
    rw [ENNReal.inv_two_add_inv_two]⟩
  -- `MemLp` membership of the cutoff product `u` and its two partials, via Hölder products
  -- of the (compactly-supported, bounded) cutoff factors with the `L²` data `F, Gx, Gy`.
  have hχmemTop : MemLp χ ∞ volume := hχcont.memLp_top_of_hasCompactSupport hχcs volume
  have hχmem2 : MemLp χ 2 volume := hχcont.memLp_of_hasCompactSupport hχcs
  have hdχcs : HasCompactSupport (fun z => (fderiv ℝ χ z) 1) :=
    HasCompactSupport.fderiv_apply ℝ hχcs 1
  have hdχIcs : HasCompactSupport (fun z => (fderiv ℝ χ z) Complex.I) :=
    HasCompactSupport.fderiv_apply ℝ hχcs Complex.I
  have hdχmem2 : MemLp (fun z => (fderiv ℝ χ z) 1) 2 volume :=
    hdχcont.memLp_of_hasCompactSupport hdχcs
  have hdχImem2 : MemLp (fun z => (fderiv ℝ χ z) Complex.I) 2 volume :=
    hdχIcont.memLp_of_hasCompactSupport hdχIcs
  -- `c`-scaled cutoff factors are continuous, compactly supported, hence `MemLp` at any exponent.
  have hχc_mem2 : MemLp (fun z => χ z • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]; fun_prop
  have hdχc_mem1 : MemLp (fun z => ((fderiv ℝ χ z) 1) • c) 1 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχcont).mul continuous_const
  have hdχIc_mem1 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • c) 1 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχIcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχIcont).mul continuous_const
  -- The Hölder smul products at the explicit exponents (exponents pinned to avoid the
  -- `HolderTriple` semi-out-param unification blowup).
  have hχF2 : MemLp (fun z => χ z • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hχmemTop
  have hχGx1 : MemLp (fun z => χ z • Gx z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hGxmem hχmem2
  have hχGy1 : MemLp (fun z => χ z • Gy z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hGymem hχmem2
  have hdχF1 : MemLp (fun z => ((fderiv ℝ χ z) 1) • F z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hFmem hdχmem2
  have hdχIF1 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • F z) 1 volume :=
    MemLp.smul (r := 1) (p := 2) (q := 2) hFmem hdχImem2
  -- `u = χ•F − χ•c ∈ L²` with compact support.
  have humem : MemLp (fun z => χ z • (F z - c)) 2 volume := by
    refine MemLp.ae_eq ?_ (hχF2.sub hχc_mem2)
    filter_upwards with z
    change χ z • F z - χ z • c = χ z • (F z - c)
    module
  have hucs : HasCompactSupport (fun z => χ z • (F z - c)) :=
    hχcs.smul_right (f' := fun z => F z - c)
  -- `gxu = χ•Gx + (∂₁χ)•F − (∂₁χ)•c ∈ L¹`.
  have hgxumem : MemLp (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)) 1 volume := by
    refine MemLp.ae_eq ?_ (hχGx1.add (hdχF1.sub hdχc_mem1))
    filter_upwards with z
    change χ z • Gx z + (((fderiv ℝ χ z) 1) • F z - ((fderiv ℝ χ z) 1) • c)
      = χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)
    module
  -- `gyu = χ•Gy + (∂_Iχ)•F − (∂_Iχ)•c ∈ L¹`.
  have hgyumem : MemLp (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)) 1 volume := by
    refine MemLp.ae_eq ?_ (hχGy1.add (hdχIF1.sub hdχIc_mem1))
    filter_upwards with z
    change χ z • Gy z + (((fderiv ℝ χ z) Complex.I) • F z - ((fderiv ℝ χ z) Complex.I) • c)
      = χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)
    module
  exact hSob humem hucs hxweak hyweak hgxumem hgyumem

set_option maxHeartbeats 400000 in
-- The recentring average-Jensen + `(1,1)`-Poincaré chain is a single self-contained
-- elaboration, so it needs a modestly raised heartbeat budget.
/-- **Auxiliary for N1: the cutoff commutator bound.** The `L¹`-mass over the doubled ball
`2B = ball x (2r)` of the oscillation of `F` about its **inner** average `c = ⨍_B F` is
controlled by `r` times the full-gradient `L¹`-mass over `2B`:
`∫⁻_{2B} ‖F − c‖ ≤ 5·Cp·(2r)·∫⁻_{2B}(‖Gx‖+‖Gy‖)`, where `Cp` is the `(1,1)`-Poincaré constant.
Proof: the `(1,1)`-Poincaré (`poincare_one_one_ball`) at radius `2r` bounds the oscillation
about the **outer** average `c₂ = ⨍_{2B} F`; the inner/outer recentring costs the factor `5`
via the average-Jensen bound `‖c − c₂‖·|B| ≤ ∫⁻_{2B}‖F − c₂‖` and the planar ratio
`|2B|/|B| = 4`. This is the commutator the N1 cutoff proof must absorb. -/
private theorem cutoff_commutator_bound :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ {F Gx Gy : ℂ → ℂ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          ∫⁻ z in Metric.ball x (2 * r),
              (‖F z - (⨍ w in Metric.ball x r, F w)‖₊ : ℝ≥0∞) ∂volume ≤
            ENNReal.ofReal (5 * Cp * (2 * r)) *
              ∫⁻ z in Metric.ball x (2 * r),
                ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume := by
  obtain ⟨Cp, hCp0, hPoin⟩ := poincare_one_one_ball
  refine ⟨Cp, hCp0, ?_⟩
  intro F Gx Gy hFmem hGxmem hGymem hGxweak hGyweak x r hr
  set B : Set ℂ := Metric.ball x r with hB_def
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hVolB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVolBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hVolB2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  set c : ℂ := ⨍ w in B, F w ∂volume with hc_def
  set c2 : ℂ := ⨍ w in B2, F w ∂volume with hc2_def
  set gradInt : ℝ≥0∞ := ∫⁻ z in B2, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume
    with hgradInt_def
  -- Integrability of `F` (hence of `F − c₂`) on the finite-measure ball `B2`.
  haveI : IsFiniteMeasure (volume.restrict B2) := isFiniteMeasure_restrict.2 hVolB2top
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hVolBtop
  have hF_intB2 : IntegrableOn F B2 volume := (hFmem.restrict B2).integrable (by norm_num)
  have hF_intB : IntegrableOn F B volume := (hFmem.restrict B).integrable (by norm_num)
  have hconst_intB : IntegrableOn (fun _ : ℂ => c2) B volume :=
    integrableOn_const (C := c2) (by rw [hB_def]; exact measure_ball_lt_top.ne)
  have hFc2_intB : IntegrableOn (fun z => F z - c2) B volume := hF_intB.sub hconst_intB
  -- (P) Poincaré at radius `2r`: oscillation about the outer average `c₂`.
  have hOuter : ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume
      ≤ ENNReal.ofReal (Cp * (2 * r)) * gradInt := by
    have := hPoin hFmem hGxmem hGymem hGxweak hGyweak x (2 * r) h2r
    -- `hPoin` gives the oscillation about `⨍_{ball x (2r)} F = c₂`.
    rwa [← hc2_def, ← hB2_def, ← hgradInt_def] at this
  -- (J) Average-Jensen recentring: `‖c − c₂‖·|B| ≤ ∫⁻_{2B} ‖F − c₂‖`.
  -- `c − c₂ = ⨍_B (F − c₂)`, so `‖c − c₂‖·|B| = ‖∫_B (F − c₂)‖ ≤ ∫_B ‖F − c₂‖ ≤ ∫_{2B} ‖F − c₂‖`.
  have hB_sub_B2 : B ⊆ B2 := by
    intro z hz; rw [hB_def, Metric.mem_ball] at hz; rw [hB2_def, Metric.mem_ball]; linarith
  have hBrealpos : 0 < volume.real B :=
    ENNReal.toReal_pos hVolB0 hVolBtop
  -- `c − c₂ = ⨍_B (F − c₂)` by linearity of the set average over `B`.
  have hcdiff : c - c2 = ⨍ w in B, (F w - c2) ∂volume := by
    have hlin : (⨍ w in B, (F w - c2) ∂volume) = (⨍ w in B, F w ∂volume) - c2 := by
      rw [setAverage_eq, setAverage_eq, integral_sub hF_intB hconst_intB,
        setIntegral_const, smul_sub, smul_smul, inv_mul_cancel₀ hBrealpos.ne', one_smul]
    rw [hlin, ← hc_def]
  -- `‖c − c₂‖·|B| ≤ ∫_B ‖F − c₂‖` (Jensen / norm of integral).
  have hJensenReal : ‖c - c2‖ * volume.real B ≤ ∫ w in B, ‖F w - c2‖ ∂volume := by
    rw [hcdiff, setAverage_eq, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg measureReal_nonneg]
    calc (volume.real B)⁻¹ * ‖∫ w in B, (F w - c2) ∂volume‖ * volume.real B
        = ‖∫ w in B, (F w - c2) ∂volume‖ := by
          field_simp
      _ ≤ ∫ w in B, ‖F w - c2‖ ∂volume := norm_integral_le_integral_norm _
  -- Enorm form of Jensen: `‖c − c₂‖ₑ · |B| ≤ ∫⁻_B ‖F − c₂‖ₑ`.
  have hintE_eq : ∫ w in B, ‖F w - c2‖ ∂volume
      = (∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume).toReal := by
    rw [integral_norm_eq_lintegral_enorm hFc2_intB.aestronglyMeasurable]
    simp only [enorm_eq_nnnorm]
  have hintE_lt : ∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume < ⊤ := by
    have := hFc2_intB.2
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [enorm_eq_nnnorm] using this
  have hJensenE : (‖c - c2‖₊ : ℝ≥0∞) * volume B ≤ ∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume := by
    have hreal : ‖c - c2‖ * volume.real B ≤
        (∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume).toReal := by rw [← hintE_eq]; exact hJensenReal
    -- Lift the real inequality to `ℝ≥0∞` using `ENNReal.ofReal` and `toReal` round-trips.
    have hlhs_eq : (‖c - c2‖₊ : ℝ≥0∞) * volume B
        = ENNReal.ofReal (‖c - c2‖ * volume.real B) := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm,
        Measure.real, ENNReal.ofReal_toReal hVolBtop]
    rw [hlhs_eq, ← ENNReal.ofReal_toReal hintE_lt.ne]
    exact ENNReal.ofReal_le_ofReal hreal
  -- `|2B| = 4·|B|` (planar volume scaling).
  have hvol_ratio : volume B2 = 4 * volume B := by
    rw [hB_def, hB2_def, Complex.volume_ball, Complex.volume_ball]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [mul_pow]
    rw [show ENNReal.ofReal 2 ^ 2 = (4 : ℝ≥0∞) from by
      rw [show (2 : ℝ) = ((2 : ℝ≥0∞).toReal) from by norm_num, ENNReal.ofReal_toReal (by norm_num)]
      norm_num]
    ring
  -- (Assemble) `∫⁻_{2B} ‖F − c‖ ≤ 5·∫⁻_{2B} ‖F − c₂‖ ≤ ofReal(5·Cp·2r)·gradInt`.
  have hFc2_intB2 : ∫⁻ w in B, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume
      ≤ ∫⁻ w in B2, (‖F w - c2‖₊ : ℝ≥0∞) ∂volume :=
    lintegral_mono_set hB_sub_B2
  -- Triangle split of the inner-centred oscillation.
  have htriE : ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume
      ≤ (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume) + (‖c2 - c‖₊ : ℝ≥0∞) * volume B2 := by
    have hpt : ∀ z, (‖F z - c‖₊ : ℝ≥0∞) ≤ (‖F z - c2‖₊ : ℝ≥0∞) + (‖c2 - c‖₊ : ℝ≥0∞) := by
      intro z
      rw [← enorm_eq_nnnorm, ← enorm_eq_nnnorm, ← enorm_eq_nnnorm]
      have : F z - c = (F z - c2) + (c2 - c) := by ring
      rw [this]; exact enorm_add_le _ _
    calc ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume
        ≤ ∫⁻ z in B2, ((‖F z - c2‖₊ : ℝ≥0∞) + (‖c2 - c‖₊ : ℝ≥0∞)) ∂volume :=
          lintegral_mono (fun z => hpt z)
      _ = (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume)
            + ∫⁻ _ in B2, (‖c2 - c‖₊ : ℝ≥0∞) ∂volume := by
          rw [lintegral_add_right _ measurable_const]
      _ = (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume) + (‖c2 - c‖₊ : ℝ≥0∞) * volume B2 := by
          rw [setLIntegral_const]
  -- `‖c₂ − c‖ₑ · |2B| ≤ 4·∫⁻_{2B} ‖F − c₂‖`.
  have hcomm2 : (‖c2 - c‖₊ : ℝ≥0∞) * volume B2 ≤ 4 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by
    have hsymm : (‖c2 - c‖₊ : ℝ≥0∞) = (‖c - c2‖₊ : ℝ≥0∞) := by
      rw [show c2 - c = -(c - c2) from by ring, nnnorm_neg]
    rw [hsymm, hvol_ratio]
    calc (‖c - c2‖₊ : ℝ≥0∞) * (4 * volume B)
        = 4 * ((‖c - c2‖₊ : ℝ≥0∞) * volume B) := by ring
      _ ≤ 4 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by
          gcongr; exact le_trans hJensenE hFc2_intB2
  -- Combine: total factor `5`, then Poincaré.
  calc ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume
      ≤ (∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume)
          + 4 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by
        refine le_trans htriE ?_; gcongr
    _ = 5 * ∫⁻ z in B2, (‖F z - c2‖₊ : ℝ≥0∞) ∂volume := by ring
    _ ≤ 5 * (ENNReal.ofReal (Cp * (2 * r)) * gradInt) := by gcongr
    _ = ENNReal.ofReal (5 * Cp * (2 * r)) * gradInt := by
        rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 from by simp [ENNReal.ofReal_ofNat],
          ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), mul_assoc 5 Cp (2 * r)]

/-- **Auxiliary for N1: the cutoff-partial `L¹` bound.** A single Leibniz partial
`χ·G + (∂_v χ)·(F − c)` (supported in the doubled ball `B2 = ball x (2r)`) has `L¹`-mass
controlled by the `L¹`-mass of `G` over `B2` plus the commutator `(Cχ/r)·∫_{B2}‖F − c‖`:
`∫⁻ ‖χ·G + (∂_v χ)·(F − c)‖ ≤ ∫⁻_{B2} ‖G‖ + (Cχ/r)·∫⁻_{B2} ‖F − c‖`. Proof: pointwise
`‖·‖ₑ ≤ B2.indicator (‖G‖ₑ + (Cχ/r)·‖F − c‖ₑ)` using `|χ| ≤ 1`, `‖∂_v χ‖ ≤ ‖∇χ‖ ≤ Cχ/r`, and
the support containments (off `B2` both `χ` and `∂_v χ` vanish). -/
private theorem cutoff_partial_l1_le {F G : ℂ → ℂ} {c : ℂ} {χ : ℂ → ℝ} {v : ℂ}
    {x : ℂ} {r Cχ : ℝ} (hv : ‖v‖ ≤ 1)
    (hGmeas : AEMeasurable G volume)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hχsupp : Function.support χ ⊆ Metric.ball x (2 * r))
    (hdχsupp : Function.support (fun z => (fderiv ℝ χ z) v) ⊆ Metric.ball x (2 * r))
    (hχgrad : ∀ z, ‖fderiv ℝ χ z‖ ≤ Cχ / r) :
    eLpNorm (fun z => χ z • G z + ((fderiv ℝ χ z) v) • (F z - c)) 1 volume ≤
      (∫⁻ z in Metric.ball x (2 * r), (‖G z‖₊ : ℝ≥0∞) ∂volume)
        + ENNReal.ofReal (Cχ / r)
            * ∫⁻ z in Metric.ball x (2 * r), (‖F z - c‖₊ : ℝ≥0∞) ∂volume := by
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  rw [eLpNorm_one_eq_lintegral_enorm]
  -- Pointwise bound by the `B2`-indicator of `‖G‖ₑ + (Cχ/r)·‖F − c‖ₑ`.
  have hpt : ∀ z, ‖χ z • G z + ((fderiv ℝ χ z) v) • (F z - c)‖ₑ ≤
      B2.indicator (fun z => (‖G z‖ₑ + ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ)) z := by
    intro z
    by_cases hz : z ∈ B2
    · rw [Set.indicator_of_mem hz]
      refine le_trans (enorm_add_le _ _) (add_le_add ?_ ?_)
      · -- `‖χ z • G z‖ₑ = ‖χ z‖ₑ · ‖G z‖ₑ ≤ ‖G z‖ₑ`.
        rw [Complex.real_smul, enorm_mul]
        calc (‖(χ z : ℂ)‖ₑ) * ‖G z‖ₑ ≤ 1 * ‖G z‖ₑ := by
              gcongr
              rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (hχ0 z)]
              exact ENNReal.ofReal_le_one.2 (hχ1 z)
          _ = ‖G z‖ₑ := one_mul _
      · -- `‖(∂_v χ z) • (F z − c)‖ₑ ≤ (Cχ/r)·‖F z − c‖ₑ`.
        rw [Complex.real_smul, enorm_mul,
          show ‖((fderiv ℝ χ z) v : ℂ)‖ₑ = ENNReal.ofReal |(fderiv ℝ χ z) v| from by
            rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]]
        gcongr
        calc |(fderiv ℝ χ z) v| = ‖(fderiv ℝ χ z) v‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ χ z‖ * ‖v‖ := (fderiv ℝ χ z).le_opNorm v
          _ ≤ (Cχ / r) * 1 := by
              refine mul_le_mul (hχgrad z) hv (norm_nonneg _) ?_
              exact le_trans (norm_nonneg _) (hχgrad z)
          _ = Cχ / r := mul_one _
    · -- Off `B2`: `χ z = 0` and `(∂_v χ z) = 0`, so the integrand vanishes.
      rw [Set.indicator_of_notMem hz]
      have hχz : χ z = 0 := Function.notMem_support.1 (fun h => hz (hχsupp h))
      have hdχz : (fderiv ℝ χ z) v = 0 := Function.notMem_support.1 (fun h => hz (hdχsupp h))
      simp [hχz, hdχz]
  calc ∫⁻ z, ‖χ z • G z + ((fderiv ℝ χ z) v) • (F z - c)‖ₑ ∂volume
      ≤ ∫⁻ z, B2.indicator (fun z => ‖G z‖ₑ + ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z ∂volume :=
        lintegral_mono hpt
    _ = ∫⁻ z in B2, (‖G z‖ₑ + ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) ∂volume := by
        rw [lintegral_indicator hB2meas]
    _ = (∫⁻ z in B2, ‖G z‖ₑ ∂volume)
          + ENNReal.ofReal (Cχ / r) * ∫⁻ z in B2, ‖F z - c‖ₑ ∂volume := by
        rw [lintegral_add_left' (hGmeas.enorm.restrict)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = (∫⁻ z in B2, (‖G z‖₊ : ℝ≥0∞) ∂volume)
          + ENNReal.ofReal (Cχ / r) * ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume := by
        simp only [enorm_eq_nnnorm]

/-- **N1 (`sobolevPoincare_ball`).** The **Sobolev–Poincaré inequality on a ball** for a
`W^{1,2}` primitive `F` with weak directional derivatives `Gx` (direction `1`) and `Gy`
(direction `I`).

There is a dimensional constant `C ≥ 0` such that on every ball `B = ball x r` the
`L²`-oscillation of `F` about its average `F_B := ⨍_B F` is controlled by `r` times the
`L¹`-average of the **full gradient** `‖Gx‖ + ‖Gy‖` over the **doubled ball** `2B =
ball x (2r)`:
`(⨍⁻_{B} ‖F − F_B‖²)^(1/2) ≤ C · r · ⨍⁻_{2B} (‖Gx‖ + ‖Gy‖)`.

This is the genuine `L² → L¹` gain. The constant `C` is **independent of the ball**
`(x, r)` and of `F`; it is the endpoint Sobolev constant. The inequality is **asymmetric**
(oscillation over `B`, gradient over the larger `2B`): the cutoff route is the only
Riesz-free derivation available in this development, and it produces exactly this enlarged
form (the same-ball statement would require a `W^{1,1}` extension operator, absent from
Mathlib).

**Why the full gradient.** The naive weight `‖G‖ = ‖½(Gx − I·Gy)‖` (the holomorphic
`∂`-part alone) is **false**: it is blind to the antiholomorphic part `∂̄F = ½(Gx + I·Gy)`.
A localized `F = conj` has `Gx = 1`, `Gy = −I`, so `G ≡ 0` while `∂̄F ≡ 1`, making the
naive RHS vanish below a positive LHS. The genuine `(2,1)` Sobolev–Poincaré inequality
uses the full gradient `‖Gx‖ + ‖Gy‖`, which sees both parts.

*Derivation (via the sound P-stack — the `I₁` Riesz route was unsound).* Form the cutoff
product `u = χ·(F − F_B)` with `χ` adapted to `B` (`χ ≡ 1` on `B`, supported in a fixed
dilate `closedBall x (3r/2) ⊆ 2B`, `|∇χ| ≲ r⁻¹`); its weak partials are
`χ·Gx + (∂₁χ)(F − F_B)` and `χ·Gy + (∂_I χ)(F − F_B)` by the Leibniz rule
`HasWeakDirDeriv.smul_smooth` (with `hasWeakDirDeriv_const` for the centring constant).
Mollify `u` to a `C¹` compactly-supported `w` (P3 `exists_contDiff_approx_W11`), apply the
genuine endpoint Sobolev inequality P1 (`eLpNorm_two_le_eLpNorm_fderiv_one`,
`‖w‖_{L²} ≤ C·‖∇w‖_{L¹}`), and pass `ε → 0` in the `L²` distance
(`sobolev_compactSupport_W11`). Since `χ ≡ 1` on `B`, this bounds `‖F − F_B‖_{L²(B)}` by
`∫_{2B}(‖Gx‖+‖Gy‖)` plus the lower-order commutator `(C/r)·∫_{2B}‖F − F_B‖`. The commutator
is absorbed by the `(1,1)`-Poincaré `poincare_one_one_ball` applied at radius `2r`
(`∫_{2B}‖F − F_{2B}‖ ≤ 8·(2r)·∫_{2B}(‖Gx‖+‖Gy‖)`) after recentering `F_B → F_{2B}` via the
average-Jensen bound `‖F_B − F_{2B}‖ ≤ ⨍_B‖F − F_{2B}‖` (giving the harmless factor `5`).
Converting to `⨍⁻`-averages via the planar `volume_ball = ofReal r² · π` produces the factor
`r`, giving the scale-invariant constant. *Dependency:* P1, P3, `poincare_one_one_ball`,
`sobolev_compactSupport_W11`, `hasWeakDirDeriv_const`. -/
theorem sobolevPoincare_ball :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F Gx Gy : ℂ → ℂ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r,
              (‖F z - (⨍ w in Metric.ball x r, F w)‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
              ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal (C * r) *
              (⨍⁻ z in Metric.ball x (2 * r),
                ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume) := by
  classical
  -- The cutoff Sobolev oscillation constant `C₁` (P1, via `cutoff_sobolev_oscL2`), the uniform
  -- cutoff gradient constant `Cχ` (ball-independent), and the commutator constant `Cp`
  -- (`cutoff_commutator_bound`, packaging the `(1,1)`-Poincaré + recentring).
  obtain ⟨C₁, hC₁0, hSob⟩ := cutoff_sobolev_oscL2
  obtain ⟨Cχ, hCχ0, hCut⟩ := exists_cutoff_ball_uniform
  obtain ⟨Cp, hCp0, hComm⟩ := cutoff_commutator_bound
  -- The ball-independent constant. The factor `4·√π` is the planar volume-ratio conversion
  -- `|2B| / |B|^{1/2} = 4·r·√π`; the bracket `1 + Cχ·(2·(5·Cp·2))` collects the gradient term
  -- and the absorbed commutator (`(2·Cχ/r)·(5·Cp·2r)·gradInt`).
  refine ⟨4 * Real.sqrt Real.pi * C₁ * (1 + Cχ * (2 * (5 * Cp * 2))), by positivity, ?_⟩
  intro F Gx Gy hFmem hGxmem hGymem hGxweak hGyweak x r hr
  -- Abbreviations for the two balls and basic measure facts.
  set B : Set ℂ := Metric.ball x r with hB_def
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hVolB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVolBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hVolB20 : volume B2 ≠ 0 := (Metric.measure_ball_pos volume x h2r).ne'
  have hVolB2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  -- The centring constant `c := F_B = ⨍_B F`.
  set c : ℂ := ⨍ w in B, F w ∂volume with hc_def
  -- Local integrability facts on the (finite-measure) ball `B2`, needed throughout.
  have hF_intB2 : IntegrableOn F B2 volume := by
    haveI : IsFiniteMeasure (volume.restrict B2) :=
      isFiniteMeasure_restrict.2 hVolB2top
    exact (hFmem.restrict B2).integrable (by norm_num)
  have hF_intB : IntegrableOn F B volume := by
    haveI : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2 hVolBtop
    exact (hFmem.restrict B).integrable (by norm_num)
  -- ====================================================================
  -- (Cut) The cutoff `χ` adapted to `B`, with uniform gradient bound `‖∇χ‖ ≤ Cχ/r`.
  -- ====================================================================
  obtain ⟨χ, hχcd, hχcs, hχ0, hχ1, hχB, hχsupp, hχgrad⟩ := hCut x r hr
  have hχcont : Continuous χ := hχcd.continuous
  -- `tsupport χ ⊆ closedBall x (3r/2) ⊆ B2 = ball x (2r)`.
  have hsupp_sub_B2 : tsupport χ ⊆ B2 := by
    refine hχsupp.trans ?_
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [hB2_def, Metric.mem_ball]
    exact lt_of_le_of_lt hz (by linarith)
  -- ====================================================================
  -- (u) The cutoff product `u = χ·(F − c)`, its weak partials `gxu, gyu`, and the
  -- compactly-supported Sobolev oscillation bound (factored into `cutoff_sobolev_oscL2`).
  -- ====================================================================
  set u : ℂ → ℂ := fun z => χ z • (F z - c) with hu_def
  set gxu : ℂ → ℂ := fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c) with hgxu_def
  set gyu : ℂ → ℂ := fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c) with hgyu_def
  have hSobu : eLpNorm u 2 volume ≤
      ENNReal.ofReal C₁ * (eLpNorm gxu 1 volume + eLpNorm gyu 1 volume) :=
    hSob hFmem hGxmem hGymem hGxweak hGyweak hχcd hχcs
  -- Abbreviation: the full-gradient `L¹`-mass over `2B`.
  set gradInt : ℝ≥0∞ := ∫⁻ z in B2, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume
    with hgradInt_def
  -- ====================================================================
  -- (A) `(∫⁻_B ‖F − c‖²)^{1/2} ≤ eLpNorm u 2`  (since `χ ≡ 1` on `B`).
  -- ====================================================================
  have hu_on_B : ∀ z ∈ B, u z = F z - c := by
    intro z hz
    change χ z • (F z - c) = F z - c
    rw [hχB z (by rw [hB_def] at hz; exact hz)]
    module
  have hLHS_le_u : (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
      ≤ eLpNorm u 2 volume := by
    have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top]
    rw [show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
        = ∫⁻ z in B, (‖u z‖ₑ) ^ (2 : ℝ) ∂volume := by
          refine setLIntegral_congr_fun hBmeas (fun z hz => ?_)
          rw [hu_on_B z hz, ← enorm_eq_nnnorm]
      _ ≤ ∫⁻ z, (‖u z‖ₑ) ^ (2 : ℝ) ∂volume := setLIntegral_le_lintegral _ _
  -- ====================================================================
  -- (B) Gradient + commutator bound:
  --   `eLpNorm gxu 1 + eLpNorm gyu 1 ≤ (1 + Cχ·(5·(2·Cp·2)))·gradInt`.
  -- ====================================================================
  -- (B0) `tsupport (∂_v χ) ⊆ tsupport χ ⊆ B2`, so the cutoff partials are supported in `2B`.
  have hdχ_supp1 : Function.support (fun z => (fderiv ℝ χ z) 1) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) 1).trans hsupp_sub_B2)
  have hdχ_suppI : Function.support (fun z => (fderiv ℝ χ z) Complex.I) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) Complex.I).trans hsupp_sub_B2)
  have hχ_supp : Function.support χ ⊆ B2 := (subset_tsupport χ).trans hsupp_sub_B2
  -- Abbreviation: the commutator `L¹`-mass over `2B`.
  set commInt : ℝ≥0∞ := ∫⁻ z in B2, (‖F z - c‖₊ : ℝ≥0∞) ∂volume with hcommInt_def
  -- (B1) Per-direction `L¹` bounds for the two cutoff partials, via `cutoff_partial_l1_le`.
  have hgxu_le : eLpNorm gxu 1 volume ≤
      (∫⁻ z in B2, (‖Gx z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt :=
    cutoff_partial_l1_le (by simp) hGxmem.1.aemeasurable hχ0 hχ1 hχ_supp hdχ_supp1 hχgrad
  have hgyu_le : eLpNorm gyu 1 volume ≤
      (∫⁻ z in B2, (‖Gy z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt :=
    cutoff_partial_l1_le (by simp) hGymem.1.aemeasurable hχ0 hχ1 hχ_supp hdχ_suppI hχgrad
  -- (B2) The commutator bound (Poincaré + recentring).
  have hCommBound : commInt ≤ ENNReal.ofReal (5 * Cp * (2 * r)) * gradInt :=
    hComm hFmem hGxmem hGymem hGxweak hGyweak x r hr
  -- (B3) `∫⁻_{2B} ‖Gx‖ + ∫⁻_{2B} ‖Gy‖ = gradInt`.
  have hsplit_grad : (∫⁻ z in B2, (‖Gx z‖₊ : ℝ≥0∞) ∂volume)
      + ∫⁻ z in B2, (‖Gy z‖₊ : ℝ≥0∞) ∂volume = gradInt := by
    rw [hgradInt_def, ← lintegral_add_left' (hGxmem.1.aemeasurable.enorm.restrict.congr
      (by filter_upwards with z; simp [enorm_eq_nnnorm]))]
  -- (B-assemble) `eLpNorm gxu 1 + eLpNorm gyu 1 ≤ (1 + Cχ·(2·(5·Cp·2)))·gradInt`.
  have hGradTot : eLpNorm gxu 1 volume + eLpNorm gyu 1 volume ≤
      ENNReal.ofReal (1 + Cχ * (2 * (5 * Cp * 2))) * gradInt := by
    have hsum : eLpNorm gxu 1 volume + eLpNorm gyu 1 volume ≤
        gradInt + 2 * (ENNReal.ofReal (Cχ / r) * commInt) := by
      calc eLpNorm gxu 1 volume + eLpNorm gyu 1 volume
          ≤ ((∫⁻ z in B2, (‖Gx z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt)
              + ((∫⁻ z in B2, (‖Gy z‖₊ : ℝ≥0∞) ∂volume) + ENNReal.ofReal (Cχ / r) * commInt) :=
            add_le_add hgxu_le hgyu_le
        _ = gradInt + 2 * (ENNReal.ofReal (Cχ / r) * commInt) := by
            rw [← hsplit_grad]; ring
    refine le_trans hsum ?_
    -- Absorb the commutator: `2·(Cχ/r)·commInt ≤ 2·(Cχ/r)·ofReal(5Cp·2r)·gradInt`, and the
    -- `r` cancels to give `Cχ·(2·(5·Cp·2))·gradInt`.
    have hrne : r ≠ 0 := hr.ne'
    have hcomm_abs : 2 * (ENNReal.ofReal (Cχ / r) * commInt)
        ≤ ENNReal.ofReal (Cχ * (2 * (5 * Cp * 2))) * gradInt := by
      calc 2 * (ENNReal.ofReal (Cχ / r) * commInt)
          ≤ 2 * (ENNReal.ofReal (Cχ / r) * (ENNReal.ofReal (5 * Cp * (2 * r)) * gradInt)) := by
            gcongr
        _ = ENNReal.ofReal (Cχ * (2 * (5 * Cp * 2))) * gradInt := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
              ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            field_simp
    calc gradInt + 2 * (ENNReal.ofReal (Cχ / r) * commInt)
        ≤ gradInt + ENNReal.ofReal (Cχ * (2 * (5 * Cp * 2))) * gradInt := by
          gcongr
      _ = ENNReal.ofReal (1 + Cχ * (2 * (5 * Cp * 2))) * gradInt := by
          rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
            add_mul, one_mul]
  -- ====================================================================
  -- (C) Chain `LHSint ≤ ofReal(C₁·bracket)·gradInt`, then convert to `⨍⁻`-averages.
  -- ====================================================================
  set bracket : ℝ := 1 + Cχ * (2 * (5 * Cp * 2)) with hbracket_def
  have hbracket0 : 0 ≤ bracket := by rw [hbracket_def]; positivity
  -- `LHSint ≤ ofReal(C₁·bracket)·gradInt`.
  have hLHSint_le : (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal (C₁ * bracket) * gradInt := by
    calc (∫⁻ z in B, (‖F z - c‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
        ≤ eLpNorm u 2 volume := hLHS_le_u
      _ ≤ ENNReal.ofReal C₁ * (eLpNorm gxu 1 volume + eLpNorm gyu 1 volume) := hSobu
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal bracket * gradInt) := by gcongr
      _ = ENNReal.ofReal (C₁ * bracket) * gradInt := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₁0]
  -- Volume identities, all as `ENNReal.ofReal` of positive reals.
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_eq : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hvolB : volume B = ENNReal.ofReal (r ^ 2 * Real.pi) := by
    rw [hB_def, Complex.volume_ball, hpi_eq, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity)]
  have hvolB2 : volume B2 = ENNReal.ofReal (4 * r ^ 2 * Real.pi) := by
    rw [hB2_def, Complex.volume_ball, hpi_eq, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  -- `(volume B)^{1/2} = ofReal(r·√π)`.
  have hVB_half : (volume B) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (r * Real.sqrt Real.pi) := by
    rw [hvolB, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.mul_rpow (by positivity) hpi0.le, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  have hVB_half_ne0 : (volume B) ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hVolB0, Or.inr (by norm_num)⟩
  have hVB_half_top : (volume B) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVolBtop
  -- The constant/volume identity: `ofReal(C₁·bracket)·|2B| = ofReal(C·r)·|B|^{1/2}` with
  -- `C = 4√π·C₁·bracket` (the planar volume-ratio conversion).
  set Cfull : ℝ := 4 * Real.sqrt Real.pi * C₁ * bracket with hCfull_def
  have hkey : ENNReal.ofReal (C₁ * bracket) * volume B2
      = ENNReal.ofReal (Cfull * r) * (volume B) ^ (1 / (2 : ℝ)) := by
    rw [hvolB2, hVB_half, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    -- Real identity: `C₁·bracket·(4r²π) = (4√π·C₁·bracket·r)·(r·√π)`.
    have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi0.le
    rw [hCfull_def]
    linear_combination (-(4 : ℝ) * C₁ * bracket * r ^ 2) * hsqrt
  -- Convert the goal's `⨍⁻`-averages to `∫⁻ / volume` and finish.
  rw [setLAverage_eq, setLAverage_eq, ← hgradInt_def,
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    ENNReal.div_le_iff hVB_half_ne0 hVB_half_top]
  -- The RHS equals `ofReal(C₁·bracket)·gradInt`, dominating `LHSint` by `hLHSint_le`.
  refine le_trans hLHSint_le (le_of_eq ?_)
  rw [mul_comm (ENNReal.ofReal (Cfull * r)) (gradInt / volume B2), mul_assoc, ← hkey,
    ← mul_assoc, mul_comm (gradInt / volume B2), mul_assoc,
    ENNReal.div_mul_cancel hVolB20 hVolB2top]

/-! ## N2 — weak integration by parts against a `W^{1,2}` test function -/

/-- **N2 (`weakIBP_against_W12`).** **Weak integration by parts / weak Leibniz against a
`W^{1,2}` test function.** The weak-derivative identity `∫ (∂ᵥφ)·F = −∫ φ·(∂ᵥF)` extends
from smooth compactly supported `φ` (the definition of `HasWeakDirDeriv`) to a compactly
supported `W^{1,2}` test function `φ` with weak directional derivative `φ'` in direction `v`.

This is what lets the Caccioppoli step (N3) test the Beltrami structure against the
non-smooth test function `φ = χ²·(F − c)` (which is only `W^{1,2}`, not `C^∞`).

*Derivation.* `φ` is the `W^{1,2}` limit of smooth compactly supported `φₙ`
(`exists_contDiff_hasCompactSupport_eLpNorm_sub_le` applied to `φ` and `φ'`); the
identity for each `φₙ` (the `HasWeakDirDeriv` definition / `smul_smooth`) passes to the
limit by the `L²`-`L²` Cauchy–Schwarz pairing with `F` and its weak derivative `G`. -/
theorem weakIBP_against_W12 {v : ℂ} {F G φ φ' : ℂ → ℂ}
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hφ : MemLp φ 2 volume) (hφ' : MemLp φ' 2 volume)
    (hφcs : HasCompactSupport φ)
    (hGweak : HasWeakDirDeriv v G F Set.univ)
    (hφweak : HasWeakDirDeriv v φ' φ Set.univ) :
    ∫ z, φ' z * F z = - ∫ z, φ z * G z := by
  classical
  -- `2` and `2` are Hölder conjugates (`1/2 + 1/2 = 1`), so the product of two
  -- `L²` functions is `L¹` and the pairing is bounded by the product of the `L²` norms.
  haveI hHolder : ENNReal.HolderTriple 2 2 1 := ⟨by
    rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  -- ====================================================================
  -- (L) `L²`-`L²` Hölder pairing continuity: `‖∫ a·H‖ ≤ ‖a‖₂·‖H‖₂` for `a, H ∈ L²`.
  -- ====================================================================
  have pairing_le : ∀ {a H : ℂ → ℂ}, MemLp a 2 volume → MemLp H 2 volume →
      ‖∫ z, a z * H z‖ ≤ (eLpNorm a 2 volume * eLpNorm H 2 volume).toReal := by
    intro a H ha hH
    -- `‖∫ a·H‖ ≤ ∫⁻ ‖a·H‖ₑ = eLpNorm (a·H) 1`, then Hölder bounds the `L¹` norm.
    have h1 : ‖∫ z, a z * H z‖ₑ ≤ ∫⁻ z, ‖a z * H z‖ₑ ∂volume :=
      enorm_integral_le_lintegral_enorm _
    have h2 : (∫⁻ z, ‖a z * H z‖ₑ ∂volume) = eLpNorm (fun z => a z * H z) 1 volume :=
      eLpNorm_one_eq_lintegral_enorm.symm
    have h3 : eLpNorm (fun z => a z * H z) 1 volume
        ≤ eLpNorm a 2 volume * eLpNorm H 2 volume := by
      have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hH.1 ha.1
      simpa only [smul_eq_mul] using this
    have h4 : ‖∫ z, a z * H z‖ₑ ≤ eLpNorm a 2 volume * eLpNorm H 2 volume :=
      le_trans h1 (le_trans (le_of_eq h2) h3)
    -- Pass from `‖·‖ₑ` to `‖·‖` (real).
    have hfin : eLpNorm a 2 volume * eLpNorm H 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top ha.eLpNorm_lt_top.ne hH.eLpNorm_lt_top.ne
    have := (ENNReal.toReal_le_toReal (by simp [enorm]) hfin).mpr h4
    simpa [enorm, ENNReal.toReal_ofReal, norm_nonneg] using this
  -- ====================================================================
  -- (ℂ) Complex-test-function lift of `hGweak`: the weak IBP identity holds against
  -- every SMOOTH compactly supported COMPLEX-valued test function `ψ`, with `*`.
  -- ====================================================================
  have hGweakℂ : ∀ ψ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      ∫ z, ((fderiv ℝ ψ z) v) * F z = - ∫ z, ψ z * G z := by
    intro ψ hψ hψcs
    -- Real and imaginary coordinate test functions.
    set χ₁ : ℂ → ℝ := fun z => (ψ z).re with hχ₁
    set χ₂ : ℂ → ℝ := fun z => (ψ z).im with hχ₂
    have hχ₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₁ := Complex.reCLM.contDiff.comp hψ
    have hχ₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₂ := Complex.imCLM.contDiff.comp hψ
    have hχ₁cs : HasCompactSupport χ₁ :=
      hψcs.comp_left (g := Complex.reCLM) (by simp)
    have hχ₂cs : HasCompactSupport χ₂ :=
      hψcs.comp_left (g := Complex.imCLM) (by simp)
    have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by
      exact_mod_cast (by norm_num : ((⊤ : ℕ∞)) ≠ 0))
    -- The directional derivative of `ψ` splits along real/imaginary parts.
    have hreim : ∀ z, (fderiv ℝ ψ z) v
        = (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) + (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * Complex.I := by
      intro z
      have hdψ : HasFDerivAt ψ (fderiv ℝ ψ z) z := hψdiff.differentiableAt.hasFDerivAt
      have hd1 : HasFDerivAt χ₁ (Complex.reCLM.comp (fderiv ℝ ψ z)) z :=
        Complex.reCLM.hasFDerivAt.comp z hdψ
      have hd2 : HasFDerivAt χ₂ (Complex.imCLM.comp (fderiv ℝ ψ z)) z :=
        Complex.imCLM.hasFDerivAt.comp z hdψ
      rw [hd1.fderiv, hd2.fderiv]
      simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
      exact (Complex.re_add_im _).symm
    -- Pointwise rewrite of the LHS integrand.
    have hLHSpt : ∀ z, ((fderiv ℝ ψ z) v) * F z
        = (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z
            + Complex.I * ((((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z) := by
      intro z; rw [hreim z]; ring
    have hRHSpt : ∀ z, ψ z * G z
        = ((χ₁ z : ℝ) : ℂ) * G z + Complex.I * (((χ₂ z : ℝ) : ℂ) * G z) := by
      intro z
      have : ψ z = ((χ₁ z : ℝ) : ℂ) + ((χ₂ z : ℝ) : ℂ) * Complex.I := (Complex.re_add_im _).symm
      rw [this]; ring
    -- The two real test functions give the IBP identity (with `•` = real scalar `*`).
    have hG1 := hGweak χ₁ hχ₁sm hχ₁cs (Set.subset_univ _)
    have hG2 := hGweak χ₂ hχ₂sm hχ₂cs (Set.subset_univ _)
    -- Recast the `•` pairings as complex `*` pairings.
    have smul_to_mul : ∀ (c : ℝ) (w : ℂ), c • w = ((c : ℝ) : ℂ) * w :=
      fun c w => (Complex.real_smul).symm ▸ rfl
    -- Integrability of the four pieces (continuous compactly supported × `L²` is integrable).
    have integ_real : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m →
        ∀ {h : ℂ → ℂ}, MemLp h 2 volume →
        Integrable (fun z => ((m z : ℝ) : ℂ) * h z) volume := by
      intro m hm hmcs h hh
      have hmcsℂ : HasCompactSupport (fun z => ((m z : ℝ) : ℂ)) :=
        hmcs.comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
      have hmcont : Continuous (fun z => ((m z : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp hm
      have hmmem : MemLp (fun z => ((m z : ℝ) : ℂ)) 2 volume :=
        hmcont.memLp_of_hasCompactSupport hmcsℂ
      exact hmmem.integrable_mul hh
    have hcont_dχ₁ : Continuous (fun z => (fderiv ℝ χ₁ z) v) :=
      (hχ₁sm.continuous_fderiv (by exact_mod_cast (by norm_num : ((⊤ : ℕ∞)) ≠ 0))).clm_apply
        continuous_const
    have hcont_dχ₂ : Continuous (fun z => (fderiv ℝ χ₂ z) v) :=
      (hχ₂sm.continuous_fderiv (by exact_mod_cast (by norm_num : ((⊤ : ℕ∞)) ≠ 0))).clm_apply
        continuous_const
    have hcs_dχ₁ : HasCompactSupport (fun z => (fderiv ℝ χ₁ z) v) :=
      HasCompactSupport.fderiv_apply ℝ hχ₁cs v
    have hcs_dχ₂ : HasCompactSupport (fun z => (fderiv ℝ χ₂ z) v) :=
      HasCompactSupport.fderiv_apply ℝ hχ₂cs v
    -- LHS pieces.
    have iLHS1 : Integrable (fun z => (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z) volume :=
      integ_real _ hcont_dχ₁ hcs_dχ₁ hF
    have iLHS2 : Integrable (fun z => (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z) volume :=
      integ_real _ hcont_dχ₂ hcs_dχ₂ hF
    have iRHS1 : Integrable (fun z => ((χ₁ z : ℝ) : ℂ) * G z) volume :=
      integ_real _ hχ₁sm.continuous hχ₁cs hG
    have iRHS2 : Integrable (fun z => ((χ₂ z : ℝ) : ℂ) * G z) volume :=
      integ_real _ hχ₂sm.continuous hχ₂cs hG
    -- The two real identities, rephrased with complex `*`.
    have hG1' : (∫ z, (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z)
        = -∫ z, ((χ₁ z : ℝ) : ℂ) * G z := by
      have e1 : (∫ z, ((fderiv ℝ χ₁ z) v) • F z)
          = ∫ z, (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      have e2 : (∫ z, χ₁ z • G z) = ∫ z, ((χ₁ z : ℝ) : ℂ) * G z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      rw [← e1, ← e2, hG1]
    have hG2' : (∫ z, (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z)
        = -∫ z, ((χ₂ z : ℝ) : ℂ) * G z := by
      have e1 : (∫ z, ((fderiv ℝ χ₂ z) v) • F z)
          = ∫ z, (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      have e2 : (∫ z, χ₂ z • G z) = ∫ z, ((χ₂ z : ℝ) : ℂ) * G z := by
        apply integral_congr_ae; filter_upwards with z; exact smul_to_mul _ _
      rw [← e1, ← e2, hG2]
    -- Assemble.
    calc ∫ z, ((fderiv ℝ ψ z) v) * F z
        = ∫ z, ((((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z
            + Complex.I * ((((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z)) := by
          apply integral_congr_ae; filter_upwards with z; exact hLHSpt z
      _ = (∫ z, (((fderiv ℝ χ₁ z) v : ℝ) : ℂ) * F z)
            + Complex.I * ∫ z, (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z := by
          rw [integral_add iLHS1 (iLHS2.const_mul Complex.I)]
          congr 1
          exact integral_const_mul Complex.I (fun z => (((fderiv ℝ χ₂ z) v : ℝ) : ℂ) * F z)
      _ = (-∫ z, ((χ₁ z : ℝ) : ℂ) * G z)
            + Complex.I * (-∫ z, ((χ₂ z : ℝ) : ℂ) * G z) := by rw [hG1', hG2']
      _ = -((∫ z, ((χ₁ z : ℝ) : ℂ) * G z)
            + Complex.I * ∫ z, ((χ₂ z : ℝ) : ℂ) * G z) := by ring
      _ = -∫ z, (((χ₁ z : ℝ) : ℂ) * G z + Complex.I * (((χ₂ z : ℝ) : ℂ) * G z)) := by
          rw [integral_add iRHS1 (iRHS2.const_mul Complex.I)]
          congr 2
          exact (integral_const_mul Complex.I (fun z => ((χ₂ z : ℝ) : ℂ) * G z)).symm
      _ = -∫ z, ψ z * G z := by
          congr 1; apply integral_congr_ae; filter_upwards with z; exact (hRHSpt z).symm
  -- ====================================================================
  -- (F) Mollification commutes with the weak directional derivative (P3 technique).
  -- ====================================================================
  have fderiv_conv : ∀ {f gv : ℂ → ℂ},
      HasWeakDirDeriv v gv f Set.univ →
      MeasureTheory.LocallyIntegrable f → MeasureTheory.LocallyIntegrable gv →
      ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      HasCompactSupport ρ → ∀ (z : ℂ),
        (fderiv ℝ (MeasureTheory.convolution ρ f
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
          = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro f gv hv hf hgv ρ hρ_smooth hρ_supp z
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
    have hρ_diff : Differentiable ℝ ρ :=
      hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
    have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
    have hderiv :
        HasFDerivAt (MeasureTheory.convolution ρ f L volume)
          (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
    rw [hderiv.fderiv]
    have hconvexists :
        MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) volume :=
      (hdρ_supp.convolutionExists_left (L.precompL ℂ)
        (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
    rw [MeasureTheory.convolution_def,
        ContinuousLinearMap.integral_apply hconvexists.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
    have hcv :
        (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂volume)
          = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume := by
      have hself := MeasureTheory.integral_sub_left_eq_self
        (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) volume z
      simp only [sub_sub_cancel] at hself
      exact hself.symm
    refine hcv.trans ?_
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
        (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume)
          = -∫ u, ((fderiv ℝ φz u) v) • f u ∂volume := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
      rw [hφz_fderiv u]
      rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
        from neg_smul _ _, neg_neg]
    rw [hint_eq]
    have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
      hρ_smooth.comp (contDiff_const.sub contDiff_id)
    have hφz_supp : HasCompactSupport φz :=
      hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
    have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
    rw [hwd, neg_neg]
    rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
        (fun t => (L (ρ t)) (gv (z - t))) volume z]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
    rfl
  -- ====================================================================
  -- (C) `L²` mollification convergence `‖ρ_n ⋆ g - g‖₂ → 0` for `g ∈ L²`.
  -- ====================================================================
  have conv_tendsto : ∀ {g : ℂ → ℂ},
      MemLp g 2 volume → ∀ (φb : ℕ → ContDiffBump (0 : ℂ)),
      Filter.Tendsto (fun n => (φb n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φb n).normed volume) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - g) 2 volume)
        Filter.atTop (nhds 0) := by
    intro g hg φb hφrout
    set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φb n).normed volume)
      g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
    have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
        Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φb n).normed volume) h
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
          Filter.atTop (nhds 0) := by
      intro h hh_supp hh_smooth
      obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
      have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
      set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
      have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
      have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
      have hKfin : volume Kset < ⊤ := hKcompact.measure_lt_top
      have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
      set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φb n).normed volume)
        h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
      have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
        HasCompactSupport.continuous_convolution_left _ ((φb n).hasCompactSupport_normed)
          ((φb n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
        ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
      have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
        intro n x
        set ρ := (φb n).normed volume with hρ
        have hρnn : ∀ t, 0 ≤ ρ t := (φb n).nonneg_normed
        rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
        calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
            ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t, ρ t * M ∂volume := by
              have hint : Integrable ρ volume :=
                ((φb n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                  ((φb n).hasCompactSupport_normed)
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
              refine Filter.Eventually.of_forall (fun t => ?_)
              simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
              exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
          _ = (∫ t, ρ t ∂volume) * M := by rw [integral_mul_const]
          _ = M := by rw [(φb n).integral_normed]; ring
      have hMh : ∀ y, ‖h y‖ ≤ M := hM
      have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
        have hev : ∀ᶠ n in Filter.atTop, (φb n).rOut ≤ 1 := by
          have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
          filter_upwards [this] with n hn using hn
        filter_upwards [hev] with n hrout1
        have haddsub : Metric.closedBall (0 : ℂ) (φb n).rOut + tsupport h ⊆ Kset := by
          intro w hw
          obtain ⟨a, ha, b, hb, rfl⟩ := hw
          rw [Metric.mem_closedBall, dist_zero_right] at ha
          refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
          rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
        have hsub := MeasureTheory.support_convolution_subset (μ := volume)
          (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
          (f := (φb n).normed volume) (g := h)
        refine hsub.trans (le_trans ?_ haddsub)
        apply Set.add_subset_add _ (subset_tsupport h)
        intro w hw
        have h1 : w ∈ tsupport ((φb n).normed volume) := subset_tsupport _ hw
        rwa [(φb n).tsupport_normed_eq] at h1
      haveI : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
        constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
      set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
      have hrestrict : ∀ᶠ n in Filter.atTop,
          eLpNorm (D n) 2 volume = eLpNorm (D n) 2 (volume.restrict Kset) := by
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
      have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Kset))
          Filter.atTop (nhds 0) := by
        have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
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
        have hhmem : MemLp h 2 (volume.restrict Kset) :=
          MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
            (Filter.Eventually.of_forall hMh)
        exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
          (Filter.Eventually.of_forall hptwise)
      exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
    have hP2 : ∀ (u : ℂ → ℂ), MemLp u 2 volume → ∀ (ε : ℝ),
        eLpNorm u 2 volume ≤ ENNReal.ofReal ε → ∀ n,
          eLpNorm (MeasureTheory.convolution ((φb n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
      intro u hu ε hclose n
      set ρc : ℂ → ℂ := fun z => (((φb n).normed volume z : ℝ) : ℂ) with hρc
      have hconv_eq : MeasureTheory.convolution ((φb n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          = MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ) volume := by
        funext x
        rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
        exact (Complex.real_smul).symm
      rw [hconv_eq]
      have hρc_memLp : MemLp ρc 1 volume := by
        have hcont : Continuous ρc :=
          Complex.continuous_ofReal.comp ((φb n).contDiff_normed (n := 0)).continuous
        have hsupp : HasCompactSupport ρc :=
          ((φb n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
        exact hcont.memLp_of_hasCompactSupport hsupp
      have hρc_norm : eLpNorm ρc 1 volume = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hint : Integrable ((φb n).normed volume) volume :=
          ((φb n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
            ((φb n).hasCompactSupport_normed)
        have hnn : 0 ≤ᵐ[volume] (φb n).normed volume :=
          Filter.Eventually.of_forall (fun z => (φb n).nonneg_normed z)
        calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
            = ∫⁻ z, ENNReal.ofReal ((φb n).normed volume z) ∂volume := by
              refine lintegral_congr (fun z => ?_)
              rw [hρc,
                show ‖(((φb n).normed volume z : ℝ) : ℂ)‖ₑ
                    = ‖(φb n).normed volume z‖ₑ from by
                  rw [← enorm_norm, Complex.norm_real, enorm_norm],
                Real.enorm_of_nonneg ((φb n).nonneg_normed z)]
          _ = ENNReal.ofReal (∫ z, (φb n).normed volume z ∂volume) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ = 1 := by rw [(φb n).integral_normed]; simp
      calc eLpNorm (MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ)
              volume) 2 volume
          ≤ eLpNorm ρc 1 volume * eLpNorm u 2 volume :=
            eLpNorm_convolution_le hρc_memLp hu
        _ = eLpNorm u 2 volume := by rw [hρc_norm, one_mul]
        _ ≤ ENNReal.ofReal ε := hclose
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [htop]; exact le_top
    set δ : ℝ := ε.toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
    have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
    obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ε := δ / 3) (by positivity)
    have hh_memLp : MemLp hh 2 volume :=
      hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
    have hgh_memLp : MemLp (g - hh) 2 volume := hg.sub hh_memLp
    have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φb n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      hP2 (g - hh) hgh_memLp (δ / 3) hh_close
    have hP3ev : ∀ᶠ n in Filter.atTop,
        eLpNorm (MeasureTheory.convolution ((φb n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
        (ENNReal.ofReal_pos.mpr (by positivity)))
    have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φb n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φb n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g) := by
      intro n
      have hce1 : MeasureTheory.ConvolutionExists ((φb n).normed volume) (g - hh)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        refine HasCompactSupport.convolutionExists_left _ ((φb n).hasCompactSupport_normed)
          ((φb n).contDiff_normed (n := 0)).continuous ?_
        exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
      have hce2 : MeasureTheory.ConvolutionExists ((φb n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        HasCompactSupport.convolutionExists_left _ ((φb n).hasCompactSupport_normed)
          ((φb n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hsplit : Cg n = MeasureTheory.convolution ((φb n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + MeasureTheory.convolution ((φb n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        rw [hCg]; simp only
        rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
        congr 1; abel
      rw [hsplit]; abel
    filter_upwards [hP3ev] with n hn3
    rw [hdecomp n]
    have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φb n).normed volume) (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) volume :=
      (HasCompactSupport.continuous_convolution_left _ ((φb n).hasCompactSupport_normed)
        ((φb n).contDiff_normed (n := 0)).continuous
        ((hg.locallyIntegrable (by norm_num)).sub
          hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φb n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
        volume - hh) volume :=
      ((HasCompactSupport.continuous_convolution_left _ ((φb n).hasCompactSupport_normed)
        ((φb n).contDiff_normed (n := 0)).continuous
        hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (hh - g) volume :=
      (hh_memLp.sub hg).1
    have hkey : eLpNorm (MeasureTheory.convolution ((φb n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φb n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g)) 2
          volume
        ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
      refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
      refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
      · exact add_le_add (hP2gh n) hn3
      · rw [eLpNorm_sub_comm]; exact hh_close
    refine le_trans hkey ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
    apply le_of_eq; congr 1; ring
  -- ====================================================================
  -- Assembly: build the mollified sequence and pass to the limit.
  -- ====================================================================
  -- Local integrability of `φ`, `φ'` (both `L²`, hence locally integrable).
  have hφ_li : MeasureTheory.LocallyIntegrable φ := hφ.locallyIntegrable (by norm_num)
  have hφ'_li : MeasureTheory.LocallyIntegrable φ' := hφ'.locallyIntegrable (by norm_num)
  -- A canonical mollifier sequence with `rOut = 2/(n+2) → 0`.
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- The mollified test functions and their directional derivatives.
  set ρn : ℕ → ℂ → ℝ := fun n => (φ₀ n).normed volume with hρn
  set φn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρn n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume with hφn
  set φ'n : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρn n) φ' (ContinuousLinearMap.lsmul ℝ ℝ) volume with hφ'n
  have hρn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρn n) := fun n =>
    (φ₀ n).contDiff_normed
  have hρn_cs : ∀ n, HasCompactSupport (ρn n) := fun n => (φ₀ n).hasCompactSupport_normed
  -- (1) Each `φn` is `C^∞`, compactly supported (a valid smooth test function).
  have hφn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φn n) := by
    intro n
    refine HasCompactSupport.contDiff_convolution_left _ (hρn_cs n) ?_ hφ_li
    exact hρn_smooth n
  have hφn_cs : ∀ n, HasCompactSupport (φn n) := fun n =>
    HasCompactSupport.convolution _ (hρn_cs n) hφcs
  -- (2) The directional derivative of `φn` is `ρn ⋆ φ'`.
  have hφn_deriv : ∀ n z, (fderiv ℝ (φn n) z) v = φ'n n z := by
    intro n z
    exact fderiv_conv hφweak hφ_li hφ'_li (hρn_smooth n) (hρn_cs n) z
  -- (3) For each `n`, the smooth IBP identity from `hGweakℂ`.
  have hident : ∀ n, ∫ z, φ'n n z * F z = - ∫ z, φn n z * G z := by
    intro n
    have h := hGweakℂ (φn n) (hφn_smooth n) (hφn_cs n)
    rw [← h]
    apply integral_congr_ae; filter_upwards with z; rw [hφn_deriv n z]
  -- (4) `φn` is `L²` (continuous, compactly supported); `φ'n = ρn ⋆ φ'` is `L²` by Young.
  have hφn_memLp : ∀ n, MemLp (φn n) 2 volume := fun n =>
    (hφn_smooth n).continuous.memLp_of_hasCompactSupport (hφn_cs n)
  -- `‖ρn‖₁ = 1`, hence `‖ρn ⋆ φ'‖₂ ≤ ‖φ'‖₂ < ⊤`, giving `φ'n ∈ L²`.
  have hρn_memLp : ∀ n, MemLp (ρn n) 1 volume := fun n =>
    (hρn_smooth n).continuous.memLp_of_hasCompactSupport (hρn_cs n)
  have hρn_memLpℂ : ∀ n, MemLp (fun z => (((ρn n) z : ℝ) : ℂ)) 1 volume := by
    intro n
    have hcont : Continuous (fun z => (((ρn n) z : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hρn_smooth n).continuous
    have hsupp : HasCompactSupport (fun z => (((ρn n) z : ℝ) : ℂ)) :=
      (hρn_cs n).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
    exact hcont.memLp_of_hasCompactSupport hsupp
  have hφ'n_conv_eq : ∀ n, φ'n n
      = MeasureTheory.convolution (fun z => (((ρn n) z : ℝ) : ℂ)) φ'
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
    intro n
    funext x
    rw [hφ'n]; simp only
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
    exact (Complex.real_smul).symm
  have hφ'n_memLp : ∀ n, MemLp (φ'n n) 2 volume := by
    intro n
    -- Measurability: `φ'n n` is a continuous `lsmul`-convolution.
    have hmeas : AEStronglyMeasurable (φ'n n) volume :=
      (HasCompactSupport.continuous_convolution_left _ (hρn_cs n)
        (hρn_smooth n).continuous hφ'_li).aestronglyMeasurable
    -- Finiteness: rewrite to the `mul`-convolution and apply Young `‖ρ ⋆ φ'‖₂ ≤ ‖ρ‖₁·‖φ'‖₂`.
    have hfin : eLpNorm (fun z => (((ρn n) z : ℝ) : ℂ)) 1 volume * eLpNorm φ' 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top (hρn_memLpℂ n).eLpNorm_lt_top.ne hφ'.eLpNorm_lt_top.ne
    have hlt : eLpNorm (φ'n n) 2 volume < ⊤ := by
      rw [hφ'n_conv_eq n]
      exact lt_of_le_of_lt (eLpNorm_convolution_le (hρn_memLpℂ n) hφ')
        (lt_of_le_of_ne le_top hfin)
    exact ⟨hmeas, hlt⟩
  -- (5) `L²` convergence of the two mollified sequences to `φ`, `φ'`.
  have hconvφ : Filter.Tendsto (fun n => eLpNorm (φn n - φ) 2 volume)
      Filter.atTop (nhds 0) := conv_tendsto hφ φ₀ hφ₀rout
  have hconvφ' : Filter.Tendsto (fun n => eLpNorm (φ'n n - φ') 2 volume)
      Filter.atTop (nhds 0) := conv_tendsto hφ' φ₀ hφ₀rout
  -- ====================================================================
  -- (Limit) Pass `n → ∞` in `∫ φ'n·F = -∫ φn·G`, using the Hölder pairing.
  -- ====================================================================
  -- Generic lemma: an `L²`-convergent sequence pairs continuously against a fixed `L²`
  -- function. From `‖aₙ − a‖₂ → 0` we get `∫ aₙ·H → ∫ a·H`.
  have pair_tendsto : ∀ {an : ℕ → ℂ → ℂ} {a H : ℂ → ℂ},
      (∀ n, MemLp (an n) 2 volume) → MemLp a 2 volume → MemLp H 2 volume →
      Filter.Tendsto (fun n => eLpNorm (an n - a) 2 volume) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => ∫ z, an n z * H z) Filter.atTop (nhds (∫ z, a z * H z)) := by
    intro an a H han ha hH hconv
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- `‖∫ aₙ·H − ∫ a·H‖ = ‖∫ (aₙ − a)·H‖ ≤ ‖aₙ − a‖₂·‖H‖₂`.
    have hbound : ∀ n, ‖(∫ z, an n z * H z) - ∫ z, a z * H z‖
        ≤ (eLpNorm (an n - a) 2 volume * eLpNorm H 2 volume).toReal := by
      intro n
      have hint1 : Integrable (fun z => an n z * H z) volume := (han n).integrable_mul hH
      have hint2 : Integrable (fun z => a z * H z) volume := ha.integrable_mul hH
      have hsub : (∫ z, an n z * H z) - ∫ z, a z * H z
          = ∫ z, (an n z - a z) * H z := by
        rw [← integral_sub hint1 hint2]
        apply integral_congr_ae; filter_upwards with z; ring
      rw [hsub]
      have hpe := pairing_le ((han n).sub ha) hH
      refine le_trans (le_of_eq ?_) hpe
      simp only [Pi.sub_apply]
    -- The bound `→ 0`, so eventually `< ε`.
    have htend0 : Filter.Tendsto
        (fun n => (eLpNorm (an n - a) 2 volume * eLpNorm H 2 volume).toReal)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => eLpNorm (an n - a) 2 volume * eLpNorm H 2 volume)
          Filter.atTop (nhds (0 * eLpNorm H 2 volume)) :=
        ENNReal.Tendsto.mul_const hconv (Or.inr hH.eLpNorm_lt_top.ne)
      rw [zero_mul] at h1
      have h2 := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp h1
      simpa only [Function.comp, ENNReal.toReal_zero] using h2
    rw [Metric.tendsto_atTop] at htend0
    obtain ⟨N, hN⟩ := htend0 ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hbound n) ?_
    have hNn := hN n hn
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg ENNReal.toReal_nonneg] at hNn
    exact hNn
  -- LHS `∫ φ'n·F → ∫ φ'·F`, RHS `-∫ φn·G → -∫ φ·G`.
  have hLHS_tendsto : Filter.Tendsto (fun n => ∫ z, φ'n n z * F z)
      Filter.atTop (nhds (∫ z, φ' z * F z)) :=
    pair_tendsto hφ'n_memLp hφ' hF hconvφ'
  have hRHS_tendsto : Filter.Tendsto (fun n => -∫ z, φn n z * G z)
      Filter.atTop (nhds (-∫ z, φ z * G z)) :=
    (pair_tendsto hφn_memLp hφ hG hconvφ).neg
  -- The two sequences are equal for each `n`, so their limits agree.
  exact tendsto_nhds_unique (hLHS_tendsto.congr (fun n => (hident n))) hRHS_tendsto

/-! ## N3 — the `f`-level Caccioppoli inequality -/

set_option maxHeartbeats 400000 in
-- The proof bundles the full Beurling-`L²`-energy mollification argument (the `∂`/`∂̄`
-- isometry on the smooth approximants) together with the commutator absorption and the
-- planar `⨍⁻`-average conversion in a single elaboration, so it needs a raised budget.
/-- **N3 (`caccioppoli_of_beltrami`).** The **`f`-level Caccioppoli (reverse-Poincaré)
inequality** for a weak holomorphic gradient `G = ½(Gx − I·Gy)` of a primitive `F` (weak
partials `Gx, Gy`) that solves the **differential** Beltrami relation `∂̄F = μ·∂F + R`, i.e.
`½(Gx + I·Gy) = μ·G + R` a.e., with inhomogeneity `R ∈ L²`.

There is a constant `A ≥ 0`, depending only on `‖μ‖∞` (hence **independent of the ball**
`x, r` and of the solution), such that on every ball `B = ball x r` the gradient energy is
bounded by the oscillation of `F` on the doubled ball `2B = ball x (2r)` (scaled by `r⁻²`)
plus the inhomogeneity:
`(⨍⁻_{B} ‖G‖²)^(1/2) ≤ A · r⁻¹ · (⨍⁻_{2B} ‖F − F_{2B}‖²)^(1/2)
    + A · (⨍⁻_{2B} ‖R‖²)^(1/2)`.

The localized relation is consumed as a hypothesis; the caller `reverseHolder_of_weakGradient`
(S1) supplies it (with `R = ½(Gx + I·Gy) − μ·G`, automatically `L²`), so no `L²`-Beurling
machinery enters here.

*Derivation.* Test the differential relation against `φ = χ²·(F − F_{2B})` for a cutoff `χ`
adapted to `B` (with `|∇χ| ≲ r⁻¹`), using the weak IBP node N2 (the test function is only
`W^{1,2}`). The cross term and the `∇χ`-commutator are absorbed by the ellipticity `‖μ‖∞ < 1`,
converting the gradient energy on `B` into the lower-order oscillation
`r⁻²·⨍⁻_{2B}‖F − F_{2B}‖²` plus the forcing `‖R‖`, the classical Caccioppoli step.
*Dependency:* N2. -/
theorem caccioppoli_of_beltrami {μ : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {F G Gx Gy R : ℂ → ℂ},
      MemLp F 2 volume → MemLp G 2 volume → MemLp R 2 volume →
      MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
      (∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z) →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, (‖G z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal (A / r) *
              (⨍⁻ z in Metric.ball x (2 * r),
                (‖F z - (⨍ w in Metric.ball x (2 * r), F w)‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
                ^ (1 / (2 : ℝ)) +
            ENNReal.ofReal A *
              (⨍⁻ z in Metric.ball x (2 * r), (‖R z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
                ^ (1 / (2 : ℝ)) := by
  classical
  -- The uniform cutoff gradient constant `Cχ` (ball-independent).
  obtain ⟨Cχ, hCχ0, hCut⟩ := exists_cutoff_ball_uniform
  -- `M := ‖μ‖∞.toReal < 1`.
  set M : ℝ := (eLpNormEssSup μ volume).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hμessSup_eq : eLpNormEssSup μ volume = ENNReal.ofReal M := by
    rw [hM_def, ENNReal.ofReal_toReal hμfin]
  have hM1 : M < 1 := by
    rw [hM_def]
    have : (1 : ℝ≥0∞).toReal = 1 := by norm_num
    rw [← this]
    exact (ENNReal.toReal_lt_toReal hμfin (by norm_num)).mpr hμbound
  have h1M0 : (0 : ℝ) < 1 - M := by linarith
  -- The combined Caccioppoli constant.
  refine ⟨(4 * Cχ + 2) / (1 - M), by positivity, ?_⟩
  intro F G Gx Gy R hFmem hGmem hRmem hGxmem hGymem hGxweak hGyweak hGdef hRrel x r hr
  set A : ℝ := (4 * Cχ + 2) / (1 - M) with hA_def
  have hA0 : 0 ≤ A := by rw [hA_def]; positivity
  -- ====================================================================
  -- (Setup) The cutoff `χ`, the centring constant `c = ⨍_{2B} F`, the balls.
  -- ====================================================================
  set B : Set ℂ := Metric.ball x r with hB_def
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hVolB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVolBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hVolB20 : volume B2 ≠ 0 := (Metric.measure_ball_pos volume x h2r).ne'
  have hVolB2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  set c : ℂ := ⨍ w in B2, F w ∂volume with hc_def
  -- The cutoff adapted to `B`.
  obtain ⟨χ, hχcd, hχcs, hχ0, hχ1, hχB, hχsupp, hχgrad⟩ := hCut x r hr
  have hχcont : Continuous χ := hχcd.continuous
  have hsupp_sub_B2 : tsupport χ ⊆ B2 := by
    refine hχsupp.trans ?_
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [hB2_def, Metric.mem_ball]
    exact lt_of_le_of_lt hz (by linarith)
  -- ====================================================================
  -- (u, gxu, gyu) the cutoff product and its weak partials.
  -- ====================================================================
  set u : ℂ → ℂ := fun z => χ z • (F z - c) with hu_def
  set gxu : ℂ → ℂ := fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c) with hgxu_def
  set gyu : ℂ → ℂ := fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c) with hgyu_def
  obtain ⟨hxweak, hyweak⟩ :=
    cutoff_weak_partials (c := c) hFmem hGxmem hGymem hGxweak hGyweak hχcd
  -- `MemLp` of `u`, `gxu`, `gyu` at `L²`, with compact support.
  haveI hHT221 : ENNReal.HolderTriple 2 2 1 := ⟨by
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one, ENNReal.inv_two_add_inv_two]⟩
  have hdχcont : Continuous (fun z => (fderiv ℝ χ z) 1) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχIcont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    (hχcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hχmemTop : MemLp χ ∞ volume := hχcont.memLp_top_of_hasCompactSupport hχcs volume
  have hdχcs : HasCompactSupport (fun z => (fderiv ℝ χ z) 1) :=
    HasCompactSupport.fderiv_apply ℝ hχcs 1
  have hdχIcs : HasCompactSupport (fun z => (fderiv ℝ χ z) Complex.I) :=
    HasCompactSupport.fderiv_apply ℝ hχcs Complex.I
  have hdχmemTop : MemLp (fun z => (fderiv ℝ χ z) 1) ∞ volume :=
    hdχcont.memLp_top_of_hasCompactSupport hdχcs volume
  have hdχImemTop : MemLp (fun z => (fderiv ℝ χ z) Complex.I) ∞ volume :=
    hdχIcont.memLp_top_of_hasCompactSupport hdχIcs volume
  have hχc_mem2 : MemLp (fun z => χ z • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]; fun_prop
  have hdχc_mem2 : MemLp (fun z => ((fderiv ℝ χ z) 1) • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχcont).mul continuous_const
  have hdχIc_mem2 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • c) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_
      (hdχIcs.smul_right (f' := fun _ : ℂ => c))
    simp_rw [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp hdχIcont).mul continuous_const
  have hχF2 : MemLp (fun z => χ z • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hχmemTop
  have hχGx2 : MemLp (fun z => χ z • Gx z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hGxmem hχmemTop
  have hχGy2 : MemLp (fun z => χ z • Gy z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hGymem hχmemTop
  have hdχF2 : MemLp (fun z => ((fderiv ℝ χ z) 1) • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hdχmemTop
  have hdχIF2 : MemLp (fun z => ((fderiv ℝ χ z) Complex.I) • F z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hFmem hdχImemTop
  have humem : MemLp u 2 volume := by
    refine MemLp.ae_eq ?_ (hχF2.sub hχc_mem2)
    filter_upwards with z
    simp only [hu_def, Pi.sub_apply]
    module
  have hucs : HasCompactSupport u :=
    hχcs.smul_right (f' := fun z => F z - c)
  have hgxumem : MemLp gxu 2 volume := by
    refine MemLp.ae_eq ?_ (hχGx2.add (hdχF2.sub hdχc_mem2))
    filter_upwards with z
    simp only [hgxu_def, Pi.sub_apply, Pi.add_apply]
    module
  have hgyumem : MemLp gyu 2 volume := by
    refine MemLp.ae_eq ?_ (hχGy2.add (hdχIF2.sub hdχIc_mem2))
    filter_upwards with z
    simp only [hgyu_def, Pi.sub_apply, Pi.add_apply]
    module
  -- The weak `∂` and `∂̄` of `u`.
  set Du : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gxu z - Complex.I * gyu z) with hDu_def
  set Dbaru : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gxu z + Complex.I * gyu z) with hDbaru_def
  have hDumem : MemLp Du 2 volume := by
    have hmem := (hgxumem.sub (hgyumem.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
    refine MemLp.ae_eq ?_ hmem
    filter_upwards with z
    simp only [hDu_def, Pi.sub_apply]
  have hDbarumem : MemLp Dbaru 2 volume := by
    have hmem := (hgxumem.add (hgyumem.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
    refine MemLp.ae_eq ?_ hmem
    filter_upwards with z
    simp only [hDbaru_def, Pi.add_apply]
  -- ====================================================================
  -- (E) KEY ENERGY EQUALITY: `eLpNorm Du 2 = eLpNorm Dbaru 2`.
  -- ====================================================================
  have hEnergy : eLpNorm Du 2 volume = eLpNorm Dbaru 2 volume := by
    -- Local integrability of `u`, `gxu`, `gyu` (from `L²` membership).
    have hu_li : MeasureTheory.LocallyIntegrable u := humem.locallyIntegrable (by norm_num)
    have hgxu_li : MeasureTheory.LocallyIntegrable gxu := hgxumem.locallyIntegrable (by norm_num)
    have hgyu_li : MeasureTheory.LocallyIntegrable gyu := hgyumem.locallyIntegrable (by norm_num)
    -- ================================================================
    -- (F) Mollification commutes with the weak directional derivative.
    -- ================================================================
    have fderiv_conv : ∀ {f gv : ℂ → ℂ} {v : ℂ},
        HasWeakDirDeriv v gv f Set.univ →
        MeasureTheory.LocallyIntegrable f → MeasureTheory.LocallyIntegrable gv →
        ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
        HasCompactSupport ρ → ∀ (z : ℂ),
          (fderiv ℝ (MeasureTheory.convolution ρ f
              (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
            = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
      intro f gv v hv hf hgv ρ hρ_smooth hρ_supp z
      set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
      have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ :=
        hρ_smooth.of_le (by exact_mod_cast le_top)
      have hρ_diff : Differentiable ℝ ρ :=
        hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
      have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
      have hderiv :
          HasFDerivAt (MeasureTheory.convolution ρ f L volume)
            (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) volume z) z :=
        HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
      rw [hderiv.fderiv]
      have hconvexists :
          MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) volume :=
        (hdρ_supp.convolutionExists_left (L.precompL ℂ)
          (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
      rw [MeasureTheory.convolution_def,
          ContinuousLinearMap.integral_apply hconvexists.integrable]
      simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
      have hcv :
          (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂volume)
            = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume := by
        have hself := MeasureTheory.integral_sub_left_eq_self
          (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) volume z
        simp only [sub_sub_cancel] at hself
        exact hself.symm
      refine hcv.trans ?_
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
          (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume)
            = -∫ u, ((fderiv ℝ φz u) v) • f u ∂volume := by
        rw [← MeasureTheory.integral_neg]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
        rw [hφz_fderiv u]
        rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
          from neg_smul _ _, neg_neg]
      rw [hint_eq]
      have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
        hρ_smooth.comp (contDiff_const.sub contDiff_id)
      have hφz_supp : HasCompactSupport φz :=
        hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
      have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
      rw [hwd, neg_neg]
      rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
          (fun t => (L (ρ t)) (gv (z - t))) volume z]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
      rfl
    -- ================================================================
    -- (C) `L²` mollification convergence `‖ρ_n ⋆ g - g‖₂ → 0` for `g ∈ L²`.
    -- ================================================================
    have conv_tendsto : ∀ {g : ℂ → ℂ},
        MemLp g 2 volume → ∀ (φ : ℕ → ContDiffBump (0 : ℂ)),
        Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => eLpNorm
            (MeasureTheory.convolution ((φ n).normed volume) g
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - g) 2 volume)
          Filter.atTop (nhds 0) := by
      intro g hg φ hφrout
      set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
        g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
      have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
          Filter.Tendsto (fun n => eLpNorm
            (MeasureTheory.convolution ((φ n).normed volume) h
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
            Filter.atTop (nhds 0) := by
        intro h hh_supp hh_smooth
        obtain ⟨Mbd, hMbd⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
        have hMbd0 : 0 ≤ Mbd := le_trans (norm_nonneg (h 0)) (hMbd 0)
        set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
        have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
        have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
        have hKfin : volume Kset < ⊤ := hKcompact.measure_lt_top
        have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
        set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
          h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
        have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
          HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
            ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
        have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
          ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
        have hCnbd : ∀ n x, ‖Cn n x‖ ≤ Mbd := by
          intro n x
          set ρ := (φ n).normed volume with hρ
          have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
          rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
          calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
              ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
                norm_integral_le_integral_norm _
            _ ≤ ∫ t, ρ t * Mbd ∂volume := by
                have hint : Integrable ρ volume :=
                  ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                    ((φ n).hasCompactSupport_normed)
                apply integral_mono_of_nonneg
                  (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const Mbd)
                refine Filter.Eventually.of_forall (fun t => ?_)
                simp only [ContinuousLinearMap.lsmul_apply, norm_smul,
                  Real.norm_of_nonneg (hρnn t)]
                exact mul_le_mul_of_nonneg_left (hMbd _) (hρnn t)
            _ = (∫ t, ρ t ∂volume) * Mbd := by rw [integral_mul_const]
            _ = Mbd := by rw [(φ n).integral_normed]; ring
        have hMh : ∀ y, ‖h y‖ ≤ Mbd := hMbd
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
          have hsub := MeasureTheory.support_convolution_subset (μ := volume)
            (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
            (f := (φ n).normed volume) (g := h)
          refine hsub.trans (le_trans ?_ haddsub)
          apply Set.add_subset_add _ (subset_tsupport h)
          intro z hz
          have h1 : z ∈ tsupport ((φ n).normed volume) := subset_tsupport _ hz
          rwa [(φ n).tsupport_normed_eq] at h1
        haveI : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
          constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
        set Dn : ℕ → ℂ → ℂ := fun n => Cn n - h with hDn
        have hrestrict : ∀ᶠ n in Filter.atTop,
            eLpNorm (Dn n) 2 volume = eLpNorm (Dn n) 2 (volume.restrict Kset) := by
          filter_upwards [hsupp_in_K] with n hn
          have hDsupp : Function.support (Dn n) ⊆ Kset := by
            intro x hx
            simp only [hDn, Pi.sub_apply, Function.mem_support, ne_eq] at hx
            by_contra hxK
            have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
            have h2 : h x = 0 := Function.notMem_support.mp
              (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
            rw [h1, h2, sub_zero] at hx; exact hx rfl
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
        have hgoal : Filter.Tendsto (fun n => eLpNorm (Dn n) 2 (volume.restrict Kset))
            Filter.atTop (nhds 0) := by
          have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
            refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
              (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
            refine ⟨(Mbd.toNNReal + 1), fun n => ?_⟩
            have hempty : {x | (Mbd.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
              ext x
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
              have hb' : ‖Cn n x‖₊ ≤ Mbd.toNNReal := by
                rw [← NNReal.coe_le_coe, Real.coe_toNNReal Mbd hMbd0]; exact hCnbd n x
              exact lt_of_le_of_lt hb' (by simp)
            rw [hempty, Set.indicator_empty]; simp
          have hhmem : MemLp h 2 (volume.restrict Kset) :=
            MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable Mbd
              (Filter.Eventually.of_forall hMh)
          exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
            (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
            (Filter.Eventually.of_forall hptwise)
        exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
      have hP2 : ∀ (uu : ℂ → ℂ), MemLp uu 2 volume → ∀ (ε : ℝ),
          eLpNorm uu 2 volume ≤ ENNReal.ofReal ε → ∀ n,
            eLpNorm (MeasureTheory.convolution ((φ n).normed volume) uu
              (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
        intro uu hu ε hclose n
        set ρc : ℂ → ℂ := fun z => (((φ n).normed volume z : ℝ) : ℂ) with hρc
        have hconv_eq : MeasureTheory.convolution ((φ n).normed volume) uu
              (ContinuousLinearMap.lsmul ℝ ℝ) volume
            = MeasureTheory.convolution ρc uu (ContinuousLinearMap.mul ℂ ℂ) volume := by
          funext x
          rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
          simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
          exact (Complex.real_smul).symm
        rw [hconv_eq]
        have hρc_memLp : MemLp ρc 1 volume := by
          have hcont : Continuous ρc :=
            Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
          have hsupp : HasCompactSupport ρc :=
            ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
          exact hcont.memLp_of_hasCompactSupport hsupp
        have hρc_norm : eLpNorm ρc 1 volume = 1 := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          have hint : Integrable ((φ n).normed volume) volume :=
            ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
              ((φ n).hasCompactSupport_normed)
          have hnn : 0 ≤ᵐ[volume] (φ n).normed volume :=
            Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
          calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
              = ∫⁻ z, ENNReal.ofReal ((φ n).normed volume z) ∂volume := by
                refine lintegral_congr (fun z => ?_)
                rw [hρc,
                  show ‖(((φ n).normed volume z : ℝ) : ℂ)‖ₑ
                      = ‖(φ n).normed volume z‖ₑ from by
                    rw [← enorm_norm, Complex.norm_real, enorm_norm],
                  Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
            _ = ENNReal.ofReal (∫ z, (φ n).normed volume z ∂volume) :=
                (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
            _ = 1 := by rw [(φ n).integral_normed]; simp
        calc eLpNorm (MeasureTheory.convolution ρc uu (ContinuousLinearMap.mul ℂ ℂ)
                volume) 2 volume
            ≤ eLpNorm ρc 1 volume * eLpNorm uu 2 volume :=
              eLpNorm_convolution_le hρc_memLp hu
          _ = eLpNorm uu 2 volume := by rw [hρc_norm, one_mul]
          _ ≤ ENNReal.ofReal ε := hclose
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      by_cases htop : ε = ⊤
      · refine Filter.Eventually.of_forall (fun n => ?_)
        rw [htop]; exact le_top
      set δ : ℝ := ε.toReal with hδ
      have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
      have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
      obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (ε := δ / 3) (by positivity)
      have hh_memLp : MemLp hh 2 volume :=
        hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
      have hgh_memLp : MemLp (g - hh) 2 volume := hg.sub hh_memLp
      have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
            ≤ ENNReal.ofReal (δ / 3) :=
        hP2 (g - hh) hgh_memLp (δ / 3) hh_close
      have hP3ev : ∀ᶠ n in Filter.atTop,
          eLpNorm (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
            ≤ ENNReal.ofReal (δ / 3) :=
        (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
          (ENNReal.ofReal_pos.mpr (by positivity)))
      have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + (MeasureTheory.convolution ((φ n).normed volume) hh
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g) := by
        intro n
        have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed volume) (g - hh)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
          refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
            ((φ n).contDiff_normed (n := 0)).continuous ?_
          exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
        have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
          HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
            ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
        have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed volume)
              (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
            + MeasureTheory.convolution ((φ n).normed volume) hh
              (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
          rw [hCg]; simp only
          rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
          congr 1; abel
        rw [hsplit]; abel
      filter_upwards [hP3ev] with n hn3
      rw [hdecomp n]
      have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
          ((φ n).normed volume) (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
          volume) volume :=
        (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous
          ((hg.locallyIntegrable (by norm_num)).sub
            hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
          ((φ n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
          volume - hh) volume :=
        ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous
          hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (hh - g) volume :=
        (hh_memLp.sub hg).1
      have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + (MeasureTheory.convolution ((φ n).normed volume) hh
              (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g)) 2
            volume
          ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
        refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
        refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
        · exact add_le_add (hP2gh n) hn3
        · rw [eLpNorm_sub_comm]; exact hh_close
      refine le_trans hkey ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
      apply le_of_eq; congr 1; ring
    -- ================================================================
    -- The canonical mollifier sequence and the mollified sequences.
    -- ================================================================
    set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
    have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
      have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
      rw [heq]
      exact Filter.Tendsto.div_atTop tendsto_const_nhds
        (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    set ρN : ℕ → ℂ → ℝ := fun n => (φ₀ n).normed volume with hρN
    have hρN_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρN n) :=
      fun n => (φ₀ n).contDiff_normed
    have hρN_cs : ∀ n, HasCompactSupport (ρN n) := fun n => (φ₀ n).hasCompactSupport_normed
    set un : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρN n) u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hun
    set Pn : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρN n) gxu (ContinuousLinearMap.lsmul ℝ ℝ) volume with hPn
    set Qn : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρN n) gyu (ContinuousLinearMap.lsmul ℝ ℝ) volume with hQn
    -- `un` is `C^∞` and compactly supported.
    have hun_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (un n) := fun n =>
      HasCompactSupport.contDiff_convolution_left _ (hρN_cs n) (hρN_smooth n) hu_li
    have hun_cs : ∀ n, HasCompactSupport (un n) := fun n =>
      HasCompactSupport.convolution _ (hρN_cs n) hucs
    -- `(fderiv un) 1 = Pn`, `(fderiv un) I = Qn`.
    have hfd1 : ∀ n z, (fderiv ℝ (un n) z) 1 = Pn n z := fun n z =>
      fderiv_conv hxweak hu_li hgxu_li (hρN_smooth n) (hρN_cs n) z
    have hfdI : ∀ n z, (fderiv ℝ (un n) z) Complex.I = Qn n z := fun n z =>
      fderiv_conv hyweak hu_li hgyu_li (hρN_smooth n) (hρN_cs n) z
    -- `dz un = (1/2)(Pn - I Qn)`, `dzbar un = (1/2)(Pn + I Qn)`.
    have hdz_un : ∀ n z, dz (un n) z = (1 / 2 : ℂ) * (Pn n z - Complex.I * Qn n z) := by
      intro n z; rw [dz, hfd1 n z, hfdI n z]
    have hdzbar_un : ∀ n z, dzbar (un n) z = (1 / 2 : ℂ) * (Pn n z + Complex.I * Qn n z) := by
      intro n z; rw [dzbar, hfd1 n z, hfdI n z]
    -- ================================================================
    -- (Iso) `eLpNorm (dz un) 2 = eLpNorm (dzbar un) 2` for each `n`.
    -- ================================================================
    have hiso : ∀ n, eLpNorm (dz (un n)) 2 volume = eLpNorm (dzbar (un n)) 2 volume := by
      intro n
      have hun2 : ContDiff ℝ (2 : ℕ∞) (un n) :=
        HasCompactSupport.contDiff_convolution_left _ (hρN_cs n)
          ((hρN_smooth n).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))) hu_li
      have hun1 : ContDiff ℝ (1 : ℕ∞) (un n) :=
        hun2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ∞) ≤ 2))
      -- `dzbar un` is `C^∞` and compactly supported (the smooth `Φ` applied to `fderiv un`).
      set Φ : (ℂ →L[ℝ] ℂ) → ℂ := fun D => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I) with hΦ
      have hdzbar_eq : (fun ζ => dzbar (un n) ζ) = Φ ∘ (fun ζ => fderiv ℝ (un n) ζ) := by
        funext ζ; rfl
      have hfderiv_cinf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => fderiv ℝ (un n) ζ) :=
        (hun_smooth n).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by
          simp)
      have hfderiv_c1 : ContDiff ℝ 1 (fun ζ => fderiv ℝ (un n) ζ) :=
        hun2.fderiv_right (m := 1) (by norm_num)
      have hΦ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
        have hΦ_lin : Φ = (fun D : ℂ →L[ℝ] ℂ =>
            (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
              + Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
          funext D; simp [hΦ, ContinuousLinearMap.apply_apply, smul_eq_mul]
        rw [hΦ_lin]
        exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).add
          ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
      have hdzbar_cinf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => dzbar (un n) ζ) := by
        rw [hdzbar_eq]; exact hΦ_cd.comp hfderiv_cinf
      have hdzbar_c1 : ContDiff ℝ 1 (fun ζ => dzbar (un n) ζ) :=
        hdzbar_cinf.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
      have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ (un n) ζ) :=
        (hun_cs n).fderiv (𝕜 := ℝ)
      have hdzbar_cs : HasCompactSupport (fun ζ => dzbar (un n) ζ) := by
        rw [hdzbar_eq]; refine hfderiv_cs.comp_left ?_; simp [hΦ]
      -- `dz un = beurling (dzbar un)` (inlined `dz_eq_beurling_dzbar`, via Cauchy–Pompeiu).
      have hP : cauchyTransform (fun ζ => dzbar (un n) ζ) = un n := by
        funext z; exact cauchyTransform_dzbar hun1 (hun_cs n) z
      have hbeur : ∀ z, dz (un n) z = beurling (fun ζ => dzbar (un n) ζ) z := by
        intro z
        calc dz (un n) z = dz (cauchyTransform (fun ζ => dzbar (un n) ζ)) z := by rw [hP]
          _ = beurling (fun ζ => dzbar (un n) ζ) z :=
              beurling_eq_dz_cauchyTransform hdzbar_c1 hdzbar_cs z
      -- The isometry.
      have hiso0 : eLpNorm (beurling (fun ζ => dzbar (un n) ζ)) 2 volume
          = eLpNorm (fun ζ => dzbar (un n) ζ) 2 volume :=
        beurling_l2_isometry_smooth hdzbar_cinf hdzbar_cs
      calc eLpNorm (dz (un n)) 2 volume
          = eLpNorm (fun z => beurling (fun ζ => dzbar (un n) ζ) z) 2 volume := by
            refine congrArg (fun f => eLpNorm f 2 volume) ?_; funext z; exact hbeur z
        _ = eLpNorm (fun ζ => dzbar (un n) ζ) 2 volume := hiso0
    -- ================================================================
    -- (Conv) `dz un → Du` and `dzbar un → Dbaru` in `L²`.
    -- ================================================================
    have hPconv : Filter.Tendsto (fun n => eLpNorm (fun z => Pn n z - gxu z) 2 volume)
        Filter.atTop (nhds 0) := conv_tendsto hgxumem φ₀ hφ₀rout
    have hQconv : Filter.Tendsto (fun n => eLpNorm (fun z => Qn n z - gyu z) 2 volume)
        Filter.atTop (nhds 0) := conv_tendsto hgyumem φ₀ hφ₀rout
    -- AE-strong-measurability facts.
    have hPn_aesm : ∀ n, AEStronglyMeasurable (Pn n) volume := fun n =>
      (HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgxu_li).aestronglyMeasurable
    have hQn_aesm : ∀ n, AEStronglyMeasurable (Qn n) volume := fun n =>
      (HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgyu_li).aestronglyMeasurable
    have hPn_cont : ∀ n, Continuous (Pn n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgxu_li
    have hQn_cont : ∀ n, Continuous (Qn n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρN_cs n)
        (hρN_smooth n).continuous hgyu_li
    have hdz_aesm : ∀ n, AEStronglyMeasurable (dz (un n)) volume := fun n => by
      have hc : Continuous (dz (un n)) := by
        rw [show dz (un n) = fun z => (1 / 2 : ℂ) * (Pn n z - Complex.I * Qn n z)
          from funext (hdz_un n)]
        exact continuous_const.mul ((hPn_cont n).sub (continuous_const.mul (hQn_cont n)))
      exact hc.aestronglyMeasurable
    have hdzbar_aesm : ∀ n, AEStronglyMeasurable (dzbar (un n)) volume := fun n => by
      have hc : Continuous (dzbar (un n)) := by
        rw [show dzbar (un n) = fun z => (1 / 2 : ℂ) * (Pn n z + Complex.I * Qn n z)
          from funext (hdzbar_un n)]
        exact continuous_const.mul ((hPn_cont n).add (continuous_const.mul (hQn_cont n)))
      exact hc.aestronglyMeasurable
    -- Half-norm and `I`-norm as `ENNReal` constants.
    have hhalf_e : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2) := by
      rw [← ofReal_norm_eq_enorm]; norm_num
    have hI_e : ‖(Complex.I : ℂ)‖ₑ = 1 := by
      rw [← ofReal_norm_eq_enorm, Complex.norm_I, ENNReal.ofReal_one]
    -- A generic const-smul `eLpNorm` bound for the relevant lambdas.
    have hcsmul : ∀ (c : ℂ) (f : ℂ → ℂ),
        eLpNorm (fun z => c • f z) 2 volume = ‖c‖ₑ * eLpNorm f 2 volume := fun c f => by
      have := eLpNorm_const_smul (μ := volume) (p := 2) c f
      simpa using this
    -- `eLpNorm (dz un - Du) ≤ (1/2)(eLpNorm (Pn-gxu) + eLpNorm (Qn-gyu))`, and similarly for ∂̄.
    have htri_dz : ∀ n, eLpNorm (fun z => dz (un n) z - Du z) 2 volume ≤
        ENNReal.ofReal (1 / 2) *
          (eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume) := by
      intro n
      have heq : (fun z => dz (un n) z - Du z)
          = fun z => (1 / 2 : ℂ) • ((Pn n z - gxu z) - Complex.I • (Qn n z - gyu z)) := by
        funext z
        rw [hdz_un n z, hDu_def]
        simp only [smul_eq_mul]; ring
      rw [heq, hcsmul, hhalf_e]
      gcongr
      refine le_trans (eLpNorm_sub_le ((hPn_aesm n).sub hgxumem.1)
        (((hQn_aesm n).sub hgyumem.1).const_smul Complex.I) (by norm_num)) ?_
      gcongr
      rw [show (fun z => Complex.I • (Qn n z - gyu z))
          = (fun z => Complex.I • ((fun w => Qn n w - gyu w) z)) from rfl, hcsmul, hI_e, one_mul]
    have htri_dzbar : ∀ n, eLpNorm (fun z => dzbar (un n) z - Dbaru z) 2 volume ≤
        ENNReal.ofReal (1 / 2) *
          (eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume) := by
      intro n
      have heq : (fun z => dzbar (un n) z - Dbaru z)
          = fun z => (1 / 2 : ℂ) • ((Pn n z - gxu z) + Complex.I • (Qn n z - gyu z)) := by
        funext z
        rw [hdzbar_un n z, hDbaru_def]
        simp only [smul_eq_mul]; ring
      rw [heq, hcsmul, hhalf_e]
      gcongr
      refine le_trans (eLpNorm_add_le ((hPn_aesm n).sub hgxumem.1)
        (((hQn_aesm n).sub hgyumem.1).const_smul Complex.I) (by norm_num)) ?_
      gcongr
      rw [show (fun z => Complex.I • (Qn n z - gyu z))
          = (fun z => Complex.I • ((fun w => Qn n w - gyu w) z)) from rfl, hcsmul, hI_e, one_mul]
    -- The `L²`-distances `dz un → Du`, `dzbar un → Dbaru` tend to `0`.
    have hRHStendsto : Filter.Tendsto
        (fun n => ENNReal.ofReal (1 / 2) *
          (eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume))
        Filter.atTop (nhds 0) := by
      have hsum : Filter.Tendsto
          (fun n => eLpNorm (fun z => Pn n z - gxu z) 2 volume
            + eLpNorm (fun z => Qn n z - gyu z) 2 volume) Filter.atTop (nhds 0) := by
        have := hPconv.add hQconv; simpa using this
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (1 / 2)) hsum
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    have hdzdist : Filter.Tendsto (fun n => eLpNorm (fun z => dz (un n) z - Du z) 2 volume)
        Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHStendsto
        (fun n => zero_le _) htri_dz
    have hdzbardist : Filter.Tendsto
        (fun n => eLpNorm (fun z => dzbar (un n) z - Dbaru z) 2 volume)
        Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHStendsto
        (fun n => zero_le _) htri_dzbar
    -- eLpNorm continuity: `eLpNorm (a_n) → eLpNorm a` when `eLpNorm (a_n - a) → 0`.
    have eLpNorm_tendsto : ∀ {a : ℂ → ℂ} {an : ℕ → ℂ → ℂ},
        (∀ n, AEStronglyMeasurable (an n) volume) → AEStronglyMeasurable a volume →
        eLpNorm a 2 volume ≠ ⊤ →
        Filter.Tendsto (fun n => eLpNorm (fun z => an n z - a z) 2 volume)
          Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => eLpNorm (an n) 2 volume) Filter.atTop
          (nhds (eLpNorm a 2 volume)) := by
      intro a an han ha hafin hdist
      set en : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun z => an n z - a z) 2 volume with hen
      have hupper : ∀ n, eLpNorm (an n) 2 volume ≤ eLpNorm a 2 volume + en n := by
        intro n
        have hsplit : (an n) = (fun z => (an n z - a z) + a z) := by funext z; ring
        calc eLpNorm (an n) 2 volume
            = eLpNorm (fun z => (an n z - a z) + a z) 2 volume := by rw [← hsplit]
          _ ≤ eLpNorm (fun z => an n z - a z) 2 volume + eLpNorm a 2 volume :=
              eLpNorm_add_le ((han n).sub ha) ha (by norm_num)
          _ = eLpNorm a 2 volume + en n := by rw [hen]; ring
      have hlower : ∀ n, eLpNorm a 2 volume ≤ eLpNorm (an n) 2 volume + en n := by
        intro n
        have hsplit : a = (fun z => a z - an n z + an n z) := by funext z; ring
        have hcomm : en n = eLpNorm (fun z => a z - an n z) 2 volume := by
          rw [hen]; exact eLpNorm_sub_comm (an n) a 2 volume
        calc eLpNorm a 2 volume
            = eLpNorm (fun z => (a z - an n z) + an n z) 2 volume := by rw [← hsplit]
          _ ≤ eLpNorm (fun z => a z - an n z) 2 volume + eLpNorm (an n) 2 volume :=
              eLpNorm_add_le (ha.sub (han n)) (han n) (by norm_num)
          _ = eLpNorm (an n) 2 volume + en n := by rw [hcomm]; ring
      -- Squeeze: `eLpNorm a - en ≤ eLpNorm (an n) ≤ eLpNorm a + en`.
      have hupper_t : Filter.Tendsto (fun n => eLpNorm a 2 volume + en n) Filter.atTop
          (nhds (eLpNorm a 2 volume)) := by
        have := Filter.Tendsto.const_add (eLpNorm a 2 volume) hdist
        simpa using this
      have hlower_t : Filter.Tendsto (fun n => eLpNorm a 2 volume - en n) Filter.atTop
          (nhds (eLpNorm a 2 volume)) := by
        have hsub := ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm a 2 volume))
          hdist (Or.inl hafin)
        simpa using hsub
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower_t hupper_t (fun n => ?_)
        (fun n => hupper n)
      exact tsub_le_iff_right.mpr (hlower n)
    have hdzlim : Filter.Tendsto (fun n => eLpNorm (dz (un n)) 2 volume) Filter.atTop
        (nhds (eLpNorm Du 2 volume)) :=
      eLpNorm_tendsto hdz_aesm hDumem.1 hDumem.eLpNorm_lt_top.ne hdzdist
    have hdzbarlim : Filter.Tendsto (fun n => eLpNorm (dzbar (un n)) 2 volume) Filter.atTop
        (nhds (eLpNorm Dbaru 2 volume)) :=
      eLpNorm_tendsto hdzbar_aesm hDbarumem.1 hDbarumem.eLpNorm_lt_top.ne hdzbardist
    -- The two limits coincide by the per-`n` isometry.
    have hdzbarlim' : Filter.Tendsto (fun n => eLpNorm (dz (un n)) 2 volume) Filter.atTop
        (nhds (eLpNorm Dbaru 2 volume)) := by
      refine hdzbarlim.congr (fun n => ?_)
      exact (hiso n).symm
    exact tendsto_nhds_unique hdzlim hdzbarlim'
  -- ====================================================================
  -- (Cacc) The Caccioppoli bound from the energy equality.
  -- ====================================================================
  -- Abbreviations for the gradient-norm constant `Cχ/r` and the half-balls' supports.
  have hCr0 : (0 : ℝ) ≤ Cχ / r := by positivity
  have hdχ_supp1 : Function.support (fun z => (fderiv ℝ χ z) 1) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) 1).trans hsupp_sub_B2)
  have hdχ_suppI : Function.support (fun z => (fderiv ℝ χ z) Complex.I) ⊆ B2 :=
    (subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset (𝕜 := ℝ) Complex.I).trans hsupp_sub_B2)
  have hχ_supp : Function.support χ ⊆ B2 := (subset_tsupport χ).trans hsupp_sub_B2
  -- `χ•G` is in `L²` (`MemLp.smul`), with the convenient enorm identity `‖χ•G‖ₑ = ‖χ‖ₑ·‖G‖ₑ`.
  have hχG2 : MemLp (fun z => χ z • G z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hGmem hχmemTop
  have hχR2 : MemLp (fun z => χ z • R z) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hRmem hχmemTop
  -- `μ·G` is in `L²` (`‖μ‖∞ < ∞`), hence so is `χ•(μ·G)`.
  have hμG2 : MemLp (fun z => μ z * G z) 2 volume := by
    have := MemLp.smul (r := 2) (p := ∞) (q := 2) hGmem
      (μ := volume) (f := G) (φ := μ) ?_
    · refine MemLp.ae_eq ?_ this
      filter_upwards with z; simp [smul_eq_mul]
    · refine ⟨hμmeas.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_exponent_top, hμessSup_eq]; exact ENNReal.ofReal_lt_top
  have hχμG2 : MemLp (fun z => χ z • (μ z * G z)) 2 volume :=
    MemLp.smul (r := 2) (p := ∞) (q := 2) hμG2 hχmemTop
  -- ‖μ z‖ₑ ≤ ofReal M a.e.
  have hμae : ∀ᵐ z ∂(volume : Measure ℂ), (‖μ z‖ₑ) ≤ ENNReal.ofReal M := by
    filter_upwards [ae_le_eLpNormEssSup (f := μ) (μ := volume)] with z hz
    rwa [hμessSup_eq] at hz
  -- ================================================================
  -- (D-split) `Du = χ•G + Eχ`, `Dbaru =ᵐ χ•(μG) + χ•R + Eχbar`,  with the commutator bound.
  -- ================================================================
  -- `Du z - χ z • G z` and `Dbaru z - χ z•(μG z) - χ z•R z` are commutators `≲ (Cχ/r)‖F-c‖`.
  set Eχ : ℂ → ℂ := fun z => Du z - χ z • G z with hEχ_def
  set Eχbar : ℂ → ℂ := fun z => Dbaru z - χ z • (μ z * G z) - χ z • R z with hEχbar_def
  -- Pointwise formulas for the commutators (purely algebraic, using `hGdef`/`hRrel`).
  have hEχ_eq : ∀ z, Eχ z = (1 / 2 : ℂ) * ((((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
      - Complex.I * ((((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c))) := by
    intro z
    simp only [hEχ_def, hDu_def, hgxu_def, hgyu_def, Complex.real_smul]
    rw [hGdef z]; ring
  have hEχbar_eq : ∀ᵐ z, Eχbar z = (1 / 2 : ℂ) * ((((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
      + Complex.I * ((((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c))) := by
    filter_upwards [hRrel] with z hz
    simp only [hEχbar_def, hDbaru_def, hgxu_def, hgyu_def, Complex.real_smul]
    have hrel : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z := hz
    -- `(1/2)(χGx + (∂χ)(F-c) + I(χGy + (∂χ)(F-c))) = χ((1/2)(Gx+IGy)) + commutator`
    have hkey : (1 / 2 : ℂ) * (((χ z : ℝ) : ℂ) * Gx z + (((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
        + Complex.I * (((χ z : ℝ) : ℂ) * Gy z
          + (((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c)))
        = ((χ z : ℝ) : ℂ) * ((1 / 2 : ℂ) * (Gx z + Complex.I * Gy z))
          + (1 / 2 : ℂ) * ((((fderiv ℝ χ z) 1 : ℝ) : ℂ) * (F z - c)
            + Complex.I * ((((fderiv ℝ χ z) Complex.I : ℝ) : ℂ) * (F z - c))) := by ring
    rw [hkey, hrel]; ring
  -- The pointwise commutator enorm bound `‖E z‖ₑ ≤ (Cχ/r)‖F z - c‖ₑ` (for `E ∈ {Eχ, Eχbar}`).
  have hcomm_bd : ∀ (a b : ℝ), |a| ≤ Cχ / r → |b| ≤ Cχ / r → ∀ (w : ℂ),
      ‖(1 / 2 : ℂ) * (((a : ℝ) : ℂ) * w + Complex.I * (((b : ℝ) : ℂ) * w))‖ₑ
        ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ ∧
      ‖(1 / 2 : ℂ) * (((a : ℝ) : ℂ) * w - Complex.I * (((b : ℝ) : ℂ) * w))‖ₑ
        ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
    intro a b ha hb w
    have hbound : ∀ (s : ℂ), s = (((a : ℝ) : ℂ) * w + Complex.I * (((b : ℝ) : ℂ) * w))
        ∨ s = (((a : ℝ) : ℂ) * w - Complex.I * (((b : ℝ) : ℂ) * w)) →
        ‖(1 / 2 : ℂ) * s‖ₑ ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
      intro s hs
      -- The two enorm building blocks: `‖a•w‖ₑ ≤ ofReal(Cχ/r)·‖w‖ₑ` and likewise for `b`.
      have hae : ‖((a : ℝ) : ℂ) * w‖ₑ ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
        rw [enorm_mul]
        gcongr
        rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal ha
      have hI_e : ‖(Complex.I : ℂ)‖ₑ = 1 := by
        rw [← ofReal_norm_eq_enorm, Complex.norm_I, ENNReal.ofReal_one]
      have hbe : ‖Complex.I * (((b : ℝ) : ℂ) * w)‖ₑ ≤ ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
        rw [enorm_mul, hI_e, one_mul, enorm_mul]
        gcongr
        rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal hb
      have hsbd : ‖s‖ₑ ≤ ENNReal.ofReal (2 * (Cχ / r)) * ‖w‖ₑ := by
        have htwo : ENNReal.ofReal (2 * (Cχ / r)) * ‖w‖ₑ
            = ENNReal.ofReal (Cχ / r) * ‖w‖ₑ + ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
          rw [← add_mul, ← ENNReal.ofReal_add hCr0 hCr0]; congr 2; ring
        rw [htwo]
        rcases hs with hs | hs
        · rw [hs]; exact le_trans (enorm_add_le _ _) (add_le_add hae hbe)
        · rw [hs]; exact le_trans enorm_sub_le (add_le_add hae hbe)
      calc ‖(1 / 2 : ℂ) * s‖ₑ = ‖(1 / 2 : ℂ)‖ₑ * ‖s‖ₑ := by rw [enorm_mul]
        _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * (Cχ / r)) * ‖w‖ₑ) := by
            refine mul_le_mul' ?_ hsbd
            rw [← ofReal_norm_eq_enorm]; norm_num
        _ = ENNReal.ofReal (Cχ / r) * ‖w‖ₑ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; congr 2; ring
    constructor
    · exact hbound _ (Or.inl rfl)
    · exact hbound _ (Or.inr rfl)
  -- The half-norms over `2B` and the gradient energy over `B`.
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  set oscHalf : ℝ≥0∞ := (∫⁻ z in B2, ‖F z - c‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
    with hoscHalf_def
  set RHalf : ℝ≥0∞ := (∫⁻ z in B2, ‖R z‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hRHalf_def
  -- |∂_v χ| ≤ Cχ/r for `v ∈ {1, I}` (operator-norm bound).
  have hdχ1_bd : ∀ z, |(fderiv ℝ χ z) 1| ≤ Cχ / r := by
    intro z
    calc |(fderiv ℝ χ z) 1| = ‖(fderiv ℝ χ z) 1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ χ z‖ * ‖(1 : ℂ)‖ := (fderiv ℝ χ z).le_opNorm 1
      _ ≤ (Cχ / r) * 1 := by
          refine mul_le_mul (hχgrad z) ?_ (norm_nonneg _) (by positivity)
          simp
      _ = Cχ / r := mul_one _
  have hdχI_bd : ∀ z, |(fderiv ℝ χ z) Complex.I| ≤ Cχ / r := by
    intro z
    calc |(fderiv ℝ χ z) Complex.I| = ‖(fderiv ℝ χ z) Complex.I‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ χ z‖ * ‖Complex.I‖ := (fderiv ℝ χ z).le_opNorm Complex.I
      _ ≤ (Cχ / r) * 1 := by
          refine mul_le_mul (hχgrad z) ?_ (norm_nonneg _) (by positivity)
          rw [Complex.norm_I]
      _ = Cχ / r := mul_one _
  -- Off `2B`, both `∂_v χ` vanish.
  have hd1_zero : ∀ z, z ∉ B2 → (fderiv ℝ χ z) 1 = 0 := by
    intro z hz
    by_contra hne
    exact hz (hdχ_supp1 hne)
  have hdI_zero : ∀ z, z ∉ B2 → (fderiv ℝ χ z) Complex.I = 0 := by
    intro z hz
    by_contra hne
    exact hz (hdχ_suppI hne)
  -- Pointwise commutator enorm bounds with the `2B`-support.
  have hEχ_pt : ∀ z, ‖Eχ z‖ₑ ≤ B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z := by
    intro z
    by_cases hz : z ∈ B2
    · rw [Set.indicator_of_mem hz, hEχ_eq z]
      exact (hcomm_bd _ _ (hdχ1_bd z) (hdχI_bd z) (F z - c)).2
    · rw [Set.indicator_of_notMem hz, hEχ_eq z, hd1_zero z hz, hdI_zero z hz]; simp
  have hEχbar_pt : ∀ᵐ z, ‖Eχbar z‖ₑ
      ≤ B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z := by
    filter_upwards [hEχbar_eq] with z hz
    by_cases hzm : z ∈ B2
    · rw [Set.indicator_of_mem hzm, hz]
      exact (hcomm_bd _ _ (hdχ1_bd z) (hdχI_bd z) (F z - c)).1
    · rw [Set.indicator_of_notMem hzm, hz, hd1_zero z hzm, hdI_zero z hzm]; simp
  have hχR_pt : ∀ z, ‖χ z • R z‖ₑ ≤ B2.indicator (fun z => ‖R z‖ₑ) z := by
    intro z
    by_cases hz : z ∈ B2
    · rw [Set.indicator_of_mem hz, Complex.real_smul, enorm_mul]
      calc ‖((χ z : ℝ) : ℂ)‖ₑ * ‖R z‖ₑ ≤ 1 * ‖R z‖ₑ := by
            gcongr
            rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (hχ0 z)]
            exact ENNReal.ofReal_le_one.2 (hχ1 z)
        _ = ‖R z‖ₑ := one_mul _
    · rw [Set.indicator_of_notMem hz]
      have hχz : χ z = 0 := Function.notMem_support.1 (fun h => hz (hχ_supp h))
      rw [hχz]; simp
  -- The `L²`-mass bounds: `eLpNorm E ≤ ofReal(Cχ/r)·oscHalf` and `eLpNorm (χ•R) ≤ RHalf`.
  -- `eLpNorm E 2 = (∫⁻ ‖E‖²)^{1/2}`, for any `E`.
  have heLp_sq : ∀ (E : ℂ → ℂ), eLpNorm E 2 volume
      = (∫⁻ z, ‖E z‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    intro E
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top,
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
  -- Helper: `(K² · J)^{1/2} = ofReal K · J^{1/2}` for `K ≥ 0`.
  have hsqrt_const : ∀ (K : ℝ) (J : ℝ≥0∞), 0 ≤ K →
      ((ENNReal.ofReal K) ^ (2 : ℝ) * J) ^ (1 / (2 : ℝ))
        = ENNReal.ofReal K * J ^ (1 / (2 : ℝ)) := by
    intro K J hK
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  have hcomm_eLp : ∀ (E : ℂ → ℂ),
      (∀ᵐ z, ‖E z‖ₑ ≤ B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z) →
      eLpNorm E 2 volume ≤ ENNReal.ofReal (Cχ / r) * oscHalf := by
    intro E hpt
    rw [heLp_sq, hoscHalf_def, ← hsqrt_const (Cχ / r) _ hCr0]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ z, ‖E z‖ₑ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ z, (B2.indicator (fun z => ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) z) ^ (2 : ℝ)
            ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with z hz
          exact ENNReal.rpow_le_rpow hz (by norm_num)
      _ = ∫⁻ z in B2, (ENNReal.ofReal (Cχ / r) * ‖F z - c‖ₑ) ^ (2 : ℝ) ∂volume := by
          rw [← lintegral_indicator hB2meas]
          refine lintegral_congr (fun z => ?_)
          by_cases hz : z ∈ B2
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
            rw [ENNReal.zero_rpow_of_pos (by norm_num)]
      _ = (ENNReal.ofReal (Cχ / r)) ^ (2 : ℝ)
            * ∫⁻ z in B2, ‖F z - c‖ₑ ^ (2 : ℝ) ∂volume := by
          rw [← lintegral_const_mul' _ _ (by
            exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
          refine lintegral_congr (fun z => ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  have hχR_eLp : eLpNorm (fun z => χ z • R z) 2 volume ≤ RHalf := by
    rw [heLp_sq, hRHalf_def]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ z, ‖χ z • R z‖ₑ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ z, (B2.indicator (fun z => ‖R z‖ₑ) z) ^ (2 : ℝ) ∂volume := by
          refine lintegral_mono (fun z => ?_)
          exact ENNReal.rpow_le_rpow (hχR_pt z) (by norm_num)
      _ = ∫⁻ z in B2, ‖R z‖ₑ ^ (2 : ℝ) ∂volume := by
          rw [← lintegral_indicator hB2meas]
          refine lintegral_congr (fun z => ?_)
          by_cases hz : z ∈ B2
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
              ENNReal.zero_rpow_of_pos (by norm_num)]
  -- `eLpNorm (χ•(μG)) ≤ ofReal M · eLpNorm (χ•G)`.
  have hχμG_eLp : eLpNorm (fun z => χ z • (μ z * G z)) 2 volume
      ≤ ENNReal.ofReal M * eLpNorm (fun z => χ z • G z) 2 volume := by
    rw [heLp_sq, heLp_sq, ← hsqrt_const M _ hM0]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← lintegral_const_mul' _ _ (by
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
    refine lintegral_mono_ae ?_
    filter_upwards [hμae] with z hz
    rw [Complex.real_smul, Complex.real_smul, enorm_mul, enorm_mul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (ENNReal.ofReal M) ^ (2 : ℝ) * (‖((χ z : ℝ) : ℂ)‖ₑ ^ (2:ℝ) * ‖G z‖ₑ ^ (2:ℝ))
        = ‖((χ z : ℝ) : ℂ)‖ₑ ^ (2:ℝ) * ((ENNReal.ofReal M) ^ (2:ℝ) * ‖G z‖ₑ ^ (2:ℝ)) from by
      ring]
    have hmono : (‖μ z‖ₑ) ^ (2:ℝ) ≤ (ENNReal.ofReal M) ^ (2:ℝ) :=
      ENNReal.rpow_le_rpow hz (by norm_num)
    gcongr
  -- ================================================================
  -- (Absorb) The energy equality + the mass bounds yield `(1-M)·X ≤ Y`.
  -- ================================================================
  set X : ℝ≥0∞ := eLpNorm (fun z => χ z • G z) 2 volume with hX_def
  have hXfin : X ≠ ⊤ := hχG2.eLpNorm_lt_top.ne
  -- AESM facts.
  have hEχ_aesm : AEStronglyMeasurable Eχ volume := hDumem.1.sub hχG2.1
  have hEχbar_aesm : AEStronglyMeasurable Eχbar volume :=
    (hDbarumem.1.sub hχμG2.1).sub hχR2.1
  -- Commutator `L²` bounds.
  have hEχ_le : eLpNorm Eχ 2 volume ≤ ENNReal.ofReal (Cχ / r) * oscHalf :=
    hcomm_eLp Eχ (Filter.Eventually.of_forall hEχ_pt)
  have hEχbar_le : eLpNorm Eχbar 2 volume ≤ ENNReal.ofReal (Cχ / r) * oscHalf :=
    hcomm_eLp Eχbar hEχbar_pt
  -- `X ≤ eLpNorm Du + eLpNorm Eχ`.
  have hX_upper : X ≤ eLpNorm Du 2 volume + eLpNorm Eχ 2 volume := by
    have heq : (fun z => χ z • G z) = fun z => Du z - Eχ z := by
      funext z; rw [hEχ_def]; ring
    rw [hX_def, heq]
    exact eLpNorm_sub_le hDumem.1 hEχ_aesm (by norm_num)
  -- `eLpNorm Dbaru ≤ eLpNorm (χμG) + eLpNorm (χR) + eLpNorm Eχbar`.
  have hDbar_upper : eLpNorm Dbaru 2 volume ≤
      eLpNorm (fun z => χ z • (μ z * G z)) 2 volume
        + eLpNorm (fun z => χ z • R z) 2 volume + eLpNorm Eχbar 2 volume := by
    have heq : Dbaru = fun z => (χ z • (μ z * G z) + χ z • R z) + Eχbar z := by
      funext z; rw [hEχbar_def]; ring
    rw [heq]
    refine le_trans (eLpNorm_add_le (hχμG2.1.add hχR2.1) hEχbar_aesm (by norm_num)) ?_
    gcongr
    exact eLpNorm_add_le hχμG2.1 hχR2.1 (by norm_num)
  -- Combine: `X ≤ ofReal M · X + Y` with `Y = RHalf + 2·ofReal(Cχ/r)·oscHalf`.
  set Y : ℝ≥0∞ := RHalf + 2 * (ENNReal.ofReal (Cχ / r) * oscHalf) with hY_def
  have hself : X ≤ ENNReal.ofReal M * X + Y := by
    calc X ≤ eLpNorm Du 2 volume + eLpNorm Eχ 2 volume := hX_upper
      _ = eLpNorm Dbaru 2 volume + eLpNorm Eχ 2 volume := by rw [hEnergy]
      _ ≤ (eLpNorm (fun z => χ z • (μ z * G z)) 2 volume
            + eLpNorm (fun z => χ z • R z) 2 volume + eLpNorm Eχbar 2 volume)
            + eLpNorm Eχ 2 volume := by gcongr
      _ ≤ (ENNReal.ofReal M * X + RHalf + ENNReal.ofReal (Cχ / r) * oscHalf)
            + ENNReal.ofReal (Cχ / r) * oscHalf := by
          gcongr
      _ = ENNReal.ofReal M * X + Y := by rw [hY_def]; ring
  -- Absorb `ofReal M · X`: `ofReal (1-M) · X ≤ Y`, hence `X ≤ ofReal ((1-M)⁻¹) · Y`.
  have hMabs : ENNReal.ofReal (1 - M) * X ≤ Y := by
    have hsub : X - ENNReal.ofReal M * X ≤ Y := tsub_le_iff_left.mpr hself
    have hfac : ENNReal.ofReal (1 - M) * X = X - ENNReal.ofReal M * X := by
      rw [ENNReal.ofReal_sub _ hM0, ENNReal.ofReal_one, ENNReal.sub_mul (fun _ _ => hXfin),
        one_mul]
    rwa [hfac]
  have h1M_pos : (0 : ℝ) < 1 - M := h1M0
  have hX_le : X ≤ ENNReal.ofReal ((1 - M)⁻¹) * Y := by
    calc X = ENNReal.ofReal ((1 - M)⁻¹) * (ENNReal.ofReal (1 - M) * X) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            inv_mul_cancel₀ h1M_pos.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal ((1 - M)⁻¹) * Y := by gcongr
  -- The gradient half-energy over `B`, dominated by `X` (χ ≡ 1 on `B`).
  set LHShalf : ℝ≥0∞ := (∫⁻ z in B, ‖G z‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hLHShalf_def
  have hLHS_le_X : LHShalf ≤ X := by
    rw [hLHShalf_def, hX_def, eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top,
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc (∫⁻ z in B, ‖G z‖ₑ ^ (2 : ℝ) ∂volume)
        = ∫⁻ z in B, ‖χ z • G z‖ₑ ^ (2 : ℝ) ∂volume := by
          refine setLIntegral_congr_fun hBmeas (fun z hz => ?_)
          have hχz : χ z = 1 := hχB z (by rw [hB_def] at hz; exact hz)
          rw [Complex.real_smul, hχz]; simp
      _ ≤ ∫⁻ z, ‖χ z • G z‖ₑ ^ (2 : ℝ) ∂volume := setLIntegral_le_lintegral _ _
  -- Master half-energy inequality (the commutator-absorbed Caccioppoli).
  have hMaster : LHShalf ≤ ENNReal.ofReal (2 * Cχ / ((1 - M) * r)) * oscHalf
      + ENNReal.ofReal ((1 - M)⁻¹) * RHalf := by
    refine le_trans hLHS_le_X (le_trans hX_le (le_of_eq ?_))
    rw [hY_def, mul_add]
    rw [show ENNReal.ofReal ((1 - M)⁻¹) * (2 * (ENNReal.ofReal (Cχ / r) * oscHalf))
        = ENNReal.ofReal (2 * Cχ / ((1 - M) * r)) * oscHalf from by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
        ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp]
    rw [add_comm]
  -- ================================================================
  -- (Convert) Pass to `⨍⁻`-averages via the planar volume ratio.
  -- ================================================================
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_eq : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hvolB : volume B = ENNReal.ofReal (r ^ 2 * Real.pi) := by
    rw [hB_def, Complex.volume_ball, hpi_eq, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity)]
  have hvolB2 : volume B2 = ENNReal.ofReal (4 * r ^ 2 * Real.pi) := by
    rw [hB2_def, Complex.volume_ball, hpi_eq, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  have hVB_half : (volume B) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (r * Real.sqrt Real.pi) := by
    rw [hvolB, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.mul_rpow (by positivity) hpi0.le, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  have hvol_ratio : volume B2 = 4 * volume B := by
    rw [hvolB, hvolB2, show (4 : ℝ) * r ^ 2 * Real.pi = (4 : ℝ) * (r ^ 2 * Real.pi) from by ring,
      ENNReal.ofReal_mul (by norm_num), show ENNReal.ofReal 4 = (4 : ℝ≥0∞) from by
        simp [ENNReal.ofReal_ofNat]]
  have hVB2_half : (volume B2) ^ (1 / (2 : ℝ)) = 2 * (volume B) ^ (1 / (2 : ℝ)) := by
    rw [hvol_ratio, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by simp [ENNReal.ofReal_ofNat],
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
      show (4 : ℝ) ^ (1 / (2:ℝ)) = 2 from by
        rw [show (4:ℝ) = 2 ^ (2:ℝ) from by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num,
      show ENNReal.ofReal 2 = (2 : ℝ≥0∞) from by simp [ENNReal.ofReal_ofNat]]
  have hVB_half_ne0 : (volume B) ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hVolB0, Or.inr (by norm_num)⟩
  have hVB_half_top : (volume B) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVolBtop
  have hVB2_half_ne0 : (volume B2) ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hVolB20, Or.inr (by norm_num)⟩
  have hVB2_half_top : (volume B2) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVolB2top
  -- Rewrite the goal's `⨍⁻`-averages as `half / volume^{1/2}` and reduce to `hMaster`.
  simp only [← enorm_eq_nnnorm]
  rw [setLAverage_eq, setLAverage_eq, setLAverage_eq,
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  rw [← hLHShalf_def, ← hoscHalf_def, ← hRHalf_def]
  rw [ENNReal.div_le_iff hVB_half_ne0 hVB_half_top]
  -- `RHS_goal * (volB)^{1/2}`: cancel the volume ratio (`(volB2)^{1/2} = 2·(volB)^{1/2}`).
  have hofReal_half : ENNReal.ofReal (1 / 2) = (1 : ℝ≥0∞) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (ENNReal.ofReal 1) / (ENNReal.ofReal 2) from by
      simp [ENNReal.ofReal_one, ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
  have hhalf_ratio : (volume B) ^ (1 / (2:ℝ)) / (volume B2) ^ (1 / (2:ℝ))
      = ENNReal.ofReal (1 / 2) := by
    rw [hofReal_half, hVB2_half,
      show (volume B) ^ (1 / (2:ℝ)) / (2 * (volume B) ^ (1 / (2:ℝ)))
        = 1 * (volume B) ^ (1 / (2:ℝ)) / (2 * (volume B) ^ (1 / (2:ℝ))) from by rw [one_mul],
      ENNReal.mul_div_mul_right 1 2 hVB_half_ne0 hVB_half_top]
  have hosc_cancel : oscHalf / (volume B2) ^ (1 / (2 : ℝ)) * (volume B) ^ (1 / (2 : ℝ))
      = ENNReal.ofReal (1 / 2) * oscHalf := by
    rw [ENNReal.mul_comm_div, hhalf_ratio, mul_comm]
  have hR_cancel : RHalf / (volume B2) ^ (1 / (2 : ℝ)) * (volume B) ^ (1 / (2 : ℝ))
      = ENNReal.ofReal (1 / 2) * RHalf := by
    rw [ENNReal.mul_comm_div, hhalf_ratio, mul_comm]
  rw [add_mul, mul_assoc, mul_assoc, hosc_cancel, hR_cancel]
  -- Final term-by-term comparison, both coefficients dominated.
  refine le_trans hMaster (add_le_add ?_ ?_)
  · -- oscHalf coefficient: `2Cχ/((1-M)r) ≤ A/r · (1/2)`.
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ A / r)]
    gcongr
    rw [hA_def,
      show (4 * Cχ + 2) / (1 - M) / r * (1 / 2) = (2 * Cχ + 1) / ((1 - M) * r) from by
        field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hCχ0, h1M_pos, hr]
  · -- RHalf coefficient: `(1-M)⁻¹ ≤ A · (1/2)`.
    rw [← mul_assoc, ← ENNReal.ofReal_mul hA0]
    gcongr
    rw [hA_def,
      show (4 * Cχ + 2) / (1 - M) * (1 / 2) = (2 * Cχ + 1) / (1 - M) from by field_simp; ring,
      inv_eq_one_div]
    rw [div_le_div_iff₀ h1M_pos h1M_pos]
    nlinarith [hCχ0, h1M_pos]

/-! ## S1 sub-stack — `setLAverage` arithmetic for the Wirtinger conversion

The corrected Sobolev–Poincaré node N1 carries the **full gradient** `‖Gx‖ + ‖Gy‖`, so the
reverse-Hölder node S1 must convert it back to the holomorphic gradient `‖G‖` (plus an `L²`
forcing). The Wirtinger identities give, a.e., `‖Gx z‖ + ‖Gy z‖ ≤ A'·‖G z‖ + 2·‖R z‖`; the
two small lemmas below turn the pointwise bound and the `L¹ ≤ L²` Jensen step into statements
about the lower-integral set averages `⨍⁻_s` over the doubled ball. -/

/-- **Aux: `setLAverage` monotone under an a.e. pointwise bound and a constant-multiple-plus
split.** For `s` with `0 < volume s` and `volume s < ⊤`, if a.e. on `s` we have
`f z ≤ ENNReal.ofReal c · g z + d z`, then `⨍⁻_s f ≤ ENNReal.ofReal c · ⨍⁻_s g + ⨍⁻_s d`. -/
private theorem setLAverage_le_const_mul_add {s : Set ℂ}
    {f g d : ℂ → ℝ≥0∞} {c : ℝ}
    (hd : AEMeasurable d (volume.restrict s))
    (hpt : ∀ᵐ z ∂(volume.restrict s), f z ≤ ENNReal.ofReal c * g z + d z) :
    (⨍⁻ z in s, f z ∂volume) ≤
      ENNReal.ofReal c * (⨍⁻ z in s, g z ∂volume) + (⨍⁻ z in s, d z ∂volume) := by
  rw [setLAverage_eq, setLAverage_eq, setLAverage_eq]
  -- Reduce to the `∫⁻`-level inequality, then divide by the common volume `V := volume s`.
  set V : ℝ≥0∞ := volume s with hV_def
  have hint : (∫⁻ z in s, f z ∂volume) ≤
      ENNReal.ofReal c * (∫⁻ z in s, g z ∂volume) + (∫⁻ z in s, d z ∂volume) := by
    calc (∫⁻ z in s, f z ∂volume)
        ≤ ∫⁻ z in s, (ENNReal.ofReal c * g z + d z) ∂volume := lintegral_mono_ae hpt
      _ = (∫⁻ z in s, ENNReal.ofReal c * g z ∂volume) + (∫⁻ z in s, d z ∂volume) :=
          lintegral_add_right' _ hd
      _ = ENNReal.ofReal c * (∫⁻ z in s, g z ∂volume) + (∫⁻ z in s, d z ∂volume) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc (∫⁻ z in s, f z ∂volume) / V
      ≤ (ENNReal.ofReal c * (∫⁻ z in s, g z ∂volume) + (∫⁻ z in s, d z ∂volume)) / V := by
        gcongr
    _ = ENNReal.ofReal c * ((∫⁻ z in s, g z ∂volume) / V) + (∫⁻ z in s, d z ∂volume) / V := by
        rw [ENNReal.add_div, mul_div_assoc]

/-- **Aux: Jensen `⨍⁻_s f ≤ (⨍⁻_s f²)^(1/2)`** for a finite, positive-measure set `s`. The
`L¹`-average is dominated by the `L²`-average; the proof is Cauchy–Schwarz `∫⁻ f·1 ≤
(∫⁻ f²)^½·(∫⁻ 1)^½ = (∫⁻ f²)^½·V^½` divided by `V`. -/
private theorem setLAverage_le_rpow_setLAverage_sq {s : Set ℂ}
    (hs0 : volume s ≠ 0) (hstop : volume s ≠ ⊤) {f : ℂ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict s)) :
    (⨍⁻ z in s, f z ∂volume) ≤
      (⨍⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
  set V : ℝ≥0∞ := volume s with hV_def
  -- Cauchy–Schwarz: `∫⁻_s f = ∫⁻_s f·1 ≤ (∫⁻_s f²)^½·(∫⁻_s 1²)^½`.
  have hcs : (∫⁻ z in s, f z ∂volume) ≤
      (∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ)) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]; constructor <;> norm_num
    have hmul := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict s) hpq
      (f := f) (g := fun _ => (1 : ℝ≥0∞)) hf aemeasurable_const
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
      Measure.restrict_apply_univ] at hmul
    -- `(∫⁻_s 1)^{1/2} = V^{1/2}`; `hmul` now is exactly the target.
    exact hmul
  rw [setLAverage_eq, setLAverage_eq]
  -- Divide by `V`: `(∫f)/V ≤ ((∫f²)^½·V^½)/V = ((∫f²)/V)^½`.
  have hVpow : V ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hs0, Or.inr (by norm_num)⟩
  have hVpowtop : V ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hstop
  -- `V^½·V^½ = V`.
  have hVsplit : V ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ)) = V := by
    rw [← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
    norm_num
  -- `V^½/V = (V^½)⁻¹`, hence `(a·V^½)/V = a/V^½`.
  have hkey : ∀ a : ℝ≥0∞, a * V ^ (1 / (2 : ℝ)) / V = a / V ^ (1 / (2 : ℝ)) := by
    intro a
    rw [ENNReal.div_eq_div_iff hVpow hVpowtop hs0 hstop]
    -- `V^½ · (a · V^½) = V · a`, using `V^½ · V^½ = V`.
    calc V ^ (1 / (2 : ℝ)) * (a * V ^ (1 / (2 : ℝ)))
        = a * (V ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ))) := by ring
      _ = a * V := by rw [hVsplit]
      _ = V * a := by ring
  calc (∫⁻ z in s, f z ∂volume) / V
      ≤ ((∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ))) / V := by
        gcongr
    _ = (∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) / V ^ (1 / (2 : ℝ)) := hkey _
    _ = ((∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) / V) ^ (1 / (2 : ℝ)) :=
        (ENNReal.div_rpow_of_nonneg (∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) V
          (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm

/-! ## S1 — the `f`-level reverse-Hölder inequality from the primitive -/

/-- **S1 (`reverseHolder_of_weakGradient`).** The **`f`-level reverse-Hölder / Caccioppoli
inequality** for an `L²` Beltrami fixed point `G = h + T(μ·G)` that is the weak holomorphic
gradient `G = ½(Gx − I·Gy)` of a primitive `F` (with weak partials `Gx, Gy`), carrying the
**antiholomorphic relation** `½(Gx + I·Gy) =ᵐ μ·G + R` (`R` an `L²` cutoff remainder).

There is a constant `A ≥ 0`, depending only on `‖μ‖∞` and the Beurling/dimensional
constants (hence **independent of the ball** `x, r`), such that for every centre `x` and
radius `r > 0` the `L²`-average of `‖G‖` over the ball `B = ball x r` is controlled by the
`L¹`-average of `‖G‖` over the doubled ball `2B = ball x (2r)` plus the `L²`-average of the
**combined forcing** `‖h‖ + ‖R‖`:
`(⨍⁻_{B} ‖G‖²)^(1/2) ≤ A · ⨍⁻_{2B} ‖G‖ + A · (⨍⁻_{2B} (‖h‖ + ‖R‖)²)^(1/2)`.

This is the hypothesis the general Gehring lemma `gehring_selfImprovement` consumes
(with `q = 2`, weight `w = ‖G‖`, lower-order term `b = ‖h‖ + ‖R‖`). The averages are the
`ℝ≥0∞`-valued lower-integral averages `⨍⁻ … = (vol B)⁻¹ ∫⁻ …`, which avoid any Bochner
integrability side-condition.

**Uniformity.** The constant `A` is quantified *outside* the fixed-point bundle
`(F, G, h, R)`: classically it depends only on the ellipticity `‖μ‖∞` and the
Beurling/dimensional constants, never on the particular solution. This uniformity is what
lets the downstream consumer upgrade *all* cutoff fixed points with a single exponent.

*Derivation (PROVEN modulo N1/N3).* Chain the `f`-level Caccioppoli inequality N3
(`caccioppoli_of_beltrami`, the `r⁻¹·(oscillation of F)` bound) with the corrected
Sobolev–Poincaré inequality N1 (`sobolevPoincare_ball`,
`(oscillation of F) ≤ r·⨍(‖Gx‖+‖Gy‖)`): the `r⁻¹` from Caccioppoli cancels the `r` from
Sobolev–Poincaré. The **full gradient** `‖Gx‖+‖Gy‖` is converted back to the holomorphic
gradient `‖G‖` (plus the `L²` forcing `‖R‖`) by the **Wirtinger identities**
`Gx = (1+μ)G + R`, `Gy = -I((1−μ)G − R)` (from `G = ½(Gx−I·Gy)` and the antiholomorphic
relation), so `‖Gx z‖ + ‖Gy z‖ ≤ 2(1+‖μ‖∞)·‖G z‖ + 2·‖R z‖` a.e. Averaging and a Jensen
`L¹ ≤ L²` step on `‖R‖` fold `‖R‖` together with the N3 inhomogeneity `‖h‖` into the single
`L²`-forcing `‖h‖ + ‖R‖`, giving a scale-invariant constant `A`. -/
theorem reverseHolder_of_weakGradient {μ : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {F G Gx Gy h R : ℂ → ℂ},
      HasCompactSupport F → MemLp F 2 volume → MemLp G 2 volume → MemLp h 2 volume →
      MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
      G =ᵐ[volume] h + beurling (fun z => μ z * G z) →
      MemLp R 2 volume →
      (∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z) →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, (‖G z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), (‖G z‖₊ : ℝ≥0∞) ∂volume) +
              ENNReal.ofReal A *
                (⨍⁻ z in Metric.ball x (4 * r),
                  ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ) ∂volume)
                  ^ (1 / (2 : ℝ)) := by
  classical
  -- N3: the `f`-level Caccioppoli constant `A₃` (depending only on `μ`).
  obtain ⟨A₃, hA₃, hCacc⟩ := caccioppoli_of_beltrami hμmeas hμfin hμbound
  -- N1: the dimensional Sobolev–Poincaré constant `C₁`.
  obtain ⟨C₁, hC₁, hSob⟩ := sobolevPoincare_ball
  -- `M := ‖μ‖∞.toReal < 1`; the Wirtinger comparison constant `A' := 2(1 + M)`.
  set M : ℝ := (eLpNormEssSup μ volume).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  set A' : ℝ := 2 * (1 + M) with hA'_def
  have hA'0 : 0 ≤ A' := by positivity
  -- `‖μ z‖ₑ ≤ ofReal M` a.e. (from `ae_le_eLpNormEssSup` and `‖μ‖∞ = ofReal M`).
  have hμessSup_eq : eLpNormEssSup μ volume = ENNReal.ofReal M := by
    rw [hM_def, ENNReal.ofReal_toReal hμfin]
  -- The combined reverse-Hölder constant. The `r⁻¹` of Caccioppoli cancels the `r` of the
  -- Sobolev–Poincaré applied at radius `2r` (giving the factor `2`), so the gradient
  -- coefficient is `2·A₃·C₁·A'`; the forcing absorbs the Wirtinger remainder `4·A₃·C₁·normB`
  -- (via Jensen) and the N3 inhomogeneity `2·A₃·normB` (after the `2B → 4B` ball-transfer).
  refine ⟨2 * (A₃ * C₁ * A') + 4 * (A₃ * C₁) + 2 * A₃, by positivity, ?_⟩
  intro F G Gx Gy h R hFcs hFmem hGmem hhmem hGxmem hGymem hGxweak hGyweak hGdef hGeq hRmem hRrel
    x r hr
  set Afin : ℝ := 2 * (A₃ * C₁ * A') + 4 * (A₃ * C₁) + 2 * A₃ with hAfin_def
  have hAfin0 : 0 ≤ Afin := by positivity
  -- Caccioppoli (N3): `(⨍_B ‖G‖²)^½ ≤ (A₃/r)·oscF + A₃·(⨍_{2B}‖h‖²)^½`.
  have hC := hCacc hFmem hGmem hRmem hGxmem hGymem hGxweak hGyweak hGdef hRrel x r hr
  -- Sobolev–Poincaré (N1, asymmetric) applied at radius `2r`: the oscillation of `F` over
  -- `2B = ball x (2r)` (centered at `⨍_{2B} F`) is bounded by the full-gradient `L¹`-average
  -- over the DOUBLED ball `4B = ball x (4r)`: `oscF ≤ (C₁·(2r))·⨍_{4B}(‖Gx‖+‖Gy‖)`.
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hS := hSob hFmem hGxmem hGymem hGxweak hGyweak x (2 * r) h2r
  -- ====================================================================
  -- The balls `2B`, `4B`, their volumes, and basic measurability.
  -- ====================================================================
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  set B4 : Set ℂ := Metric.ball x (4 * r) with hB4_def
  have h4r : (0 : ℝ) < 4 * r := by linarith
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hB4meas : MeasurableSet B4 := measurableSet_ball
  have hVol2_0 : volume B2 ≠ 0 := (Metric.measure_ball_pos volume x h2r).ne'
  have hVol2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  have hVol0 : volume B4 ≠ 0 := (Metric.measure_ball_pos volume x h4r).ne'
  have hVoltop : volume B4 ≠ ⊤ := measure_ball_lt_top.ne
  -- `2B ⊆ 4B`, and the planar volume ratio `|4B| = 4·|2B|`.
  have hB2_sub_B4 : B2 ⊆ B4 := by
    intro z hz; rw [hB2_def, Metric.mem_ball] at hz; rw [hB4_def, Metric.mem_ball]; linarith
  have hvol_ratio : volume B4 = 4 * volume B2 := by
    rw [hB2_def, hB4_def, Complex.volume_ball, Complex.volume_ball,
      show (4 : ℝ) * r = 2 * (2 * r) from by ring, ENNReal.ofReal_mul (by norm_num), mul_pow,
      show ENNReal.ofReal 2 ^ 2 = (4 : ℝ≥0∞) from by
        rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num]
    ring
  -- Abbreviations: `oscF` and N3's `normH` over `2B`; the Wirtinger/gradient averages over `4B`.
  set oscF : ℝ≥0∞ :=
    (⨍⁻ z in B2, (‖F z - (⨍ w in B2, F w)‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
    with hoscF_def
  -- `normH` now holds the N3 forcing in its corrected `‖R‖`-form (the differential
  -- inhomogeneity `R = ∂̄F − μ·∂F`), still over `2B`.
  set normH : ℝ≥0∞ :=
    (⨍⁻ z in B2, (‖R z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hnormH_def
  set avgG : ℝ≥0∞ := ⨍⁻ z in B4, (‖G z‖₊ : ℝ≥0∞) ∂volume with havgG_def
  set avgR : ℝ≥0∞ := ⨍⁻ z in B4, (‖R z‖₊ : ℝ≥0∞) ∂volume with havgR_def
  set normR : ℝ≥0∞ :=
    (⨍⁻ z in B4, (‖R z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hnormR_def
  set normB : ℝ≥0∞ :=
    (⨍⁻ z in B4, ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
    with hnormB_def
  set avgGxGy : ℝ≥0∞ := ⨍⁻ z in B4, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume
    with havgGxGy_def
  -- ====================================================================
  -- (W) The pointwise Wirtinger bound, a.e. on `4B`:
  --     `‖Gx z‖ₑ + ‖Gy z‖ₑ ≤ ofReal A' · ‖G z‖ₑ + 2·‖R z‖ₑ`.
  -- ====================================================================
  have hWirt : ∀ᵐ z ∂(volume.restrict B4),
      (‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)
        ≤ ENNReal.ofReal A' * (‖G z‖₊ : ℝ≥0∞) + 2 * (‖R z‖₊ : ℝ≥0∞) := by
    have hμae : ∀ᵐ z ∂(volume : Measure ℂ), (‖μ z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      filter_upwards [ae_le_eLpNormEssSup (f := μ) (μ := volume)] with z hz
      rw [hμessSup_eq] at hz
      rwa [← enorm_eq_nnnorm]
    rw [ae_restrict_iff' hB4meas]
    filter_upwards [hRrel, hμae] with z hrelz hμz _
    -- Algebra: `Gx z = (1 + μ z)·G z + R z`, `Gy z = -I·((1 − μ z)·G z − R z)`.
    have hGxeq : Gx z = (1 + μ z) * G z + R z := by
      have hbar : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z := hrelz
      have hg : G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z) := hGdef z
      -- `Gx = ½(Gx − I·Gy) + ½(Gx + I·Gy) = G + (μ·G + R)`.
      have : G z + (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = Gx z := by rw [hg]; ring
      rw [hbar] at this; rw [← this]; ring
    have hGyeq : Complex.I * Gy z = (μ z - 1) * G z + R z := by
      have hbar : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z := hrelz
      have hg : G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z) := hGdef z
      -- `I·Gy = ½(Gx + I·Gy) − ½(Gx − I·Gy) = (μ·G + R) − G`.
      have : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) - G z = Complex.I * Gy z := by
        rw [hg]; ring
      rw [hbar] at this; rw [← this]; ring
    -- Enorm bounds. `‖1 + μ z‖ₑ ≤ ofReal(1 + M)` and `‖μ z − 1‖ₑ ≤ ofReal(1 + M)`.
    have hofReal1M : (1 : ℝ≥0∞) + ENNReal.ofReal M = ENNReal.ofReal (1 + M) := by
      rw [ENNReal.ofReal_add (by norm_num) hM0, ENNReal.ofReal_one]
    have hμze : ‖(μ z : ℂ)‖ₑ ≤ ENNReal.ofReal M := by rwa [enorm_eq_nnnorm]
    have hone : ‖(1 : ℂ)‖ₑ ≤ (1 : ℝ≥0∞) := by simp [enorm_eq_nnnorm]
    have hc1 : ‖(1 + μ z : ℂ)‖ₑ ≤ ENNReal.ofReal (1 + M) := by
      refine le_trans (enorm_add_le _ _) ?_
      rw [← hofReal1M]
      exact add_le_add hone hμze
    have hofRealM1 : ENNReal.ofReal M + 1 = ENNReal.ofReal (1 + M) := by
      rw [add_comm]; exact hofReal1M
    have hc2 : ‖(μ z - 1 : ℂ)‖ₑ ≤ ENNReal.ofReal (1 + M) := by
      refine le_trans enorm_sub_le ?_
      rw [← hofRealM1]
      exact add_le_add hμze hone
    -- `‖Gx z‖ₑ ≤ ofReal(1+M)·‖G z‖ₑ + ‖R z‖ₑ`.
    have hGxbd : (‖Gx z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞)
        + (‖R z‖₊ : ℝ≥0∞) := by
      rw [← enorm_eq_nnnorm, hGxeq, ← enorm_eq_nnnorm, ← enorm_eq_nnnorm]
      refine le_trans (enorm_add_le _ _) ?_
      gcongr
      rw [enorm_mul]; gcongr
    -- `‖Gy z‖ₑ = ‖I·Gy z‖ₑ ≤ ofReal(1+M)·‖G z‖ₑ + ‖R z‖ₑ`.
    have hGybd : (‖Gy z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞)
        + (‖R z‖₊ : ℝ≥0∞) := by
      have hI : (‖Gy z‖₊ : ℝ≥0∞) = ‖Complex.I * Gy z‖ₑ := by
        rw [enorm_mul]; simp [enorm_eq_nnnorm]
      rw [hI, hGyeq]
      refine le_trans (enorm_add_le _ _) ?_
      gcongr
      · rw [enorm_mul]; gcongr; rw [enorm_eq_nnnorm]
      · rw [enorm_eq_nnnorm]
    -- Sum and collect: coefficient `2·ofReal(1+M) = ofReal A'`, remainder `2·‖R‖ₑ`.
    calc (‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)
        ≤ (ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞))
            + (ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) :=
          add_le_add hGxbd hGybd
      _ = ENNReal.ofReal A' * (‖G z‖₊ : ℝ≥0∞) + 2 * (‖R z‖₊ : ℝ≥0∞) := by
          have hA'split : ENNReal.ofReal A' = ENNReal.ofReal (1 + M) + ENNReal.ofReal (1 + M) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), hA'_def]
            congr 1; ring
          rw [hA'split]
          ring
  -- ====================================================================
  -- (C) The averaged Wirtinger conversion:
  --     `avgGxGy ≤ ofReal A' · avgG + 2 · avgR`.
  -- ====================================================================
  have hGmeasR : AEMeasurable (fun z => (‖G z‖₊ : ℝ≥0∞)) (volume.restrict B4) := by
    refine (hGmem.1.enorm.restrict).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
  have hRmeasR : AEMeasurable (fun z => (‖R z‖₊ : ℝ≥0∞)) (volume.restrict B4) := by
    refine (hRmem.1.enorm.restrict).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
  have hConv : avgGxGy ≤ ENNReal.ofReal A' * avgG + 2 * avgR := by
    have hd : AEMeasurable (fun z => 2 * (‖R z‖₊ : ℝ≥0∞)) (volume.restrict B4) :=
      hRmeasR.const_mul _
    have := setLAverage_le_const_mul_add (s := B4) (c := A') (g := fun z => (‖G z‖₊ : ℝ≥0∞))
      (d := fun z => 2 * (‖R z‖₊ : ℝ≥0∞)) hd hWirt
    -- `⨍_{4B}(2·‖R‖) = 2·avgR`.
    have hlinR : (⨍⁻ z in B4, 2 * (‖R z‖₊ : ℝ≥0∞) ∂volume) = 2 * avgR := by
      rw [havgR_def, setLAverage_eq, setLAverage_eq, lintegral_const_mul' _ _ (by norm_num),
        ← mul_div_assoc]
    rwa [hlinR] at this
  -- ====================================================================
  -- (J) Jensen: `avgR ≤ normR` and the forcing comparisons `normH, normR ≤ normB`.
  -- ====================================================================
  have hRJensen : avgR ≤ normR :=
    setLAverage_le_rpow_setLAverage_sq hVol0 hVoltop hRmeasR
  -- `‖R‖ ≤ ‖h‖ + ‖R‖` pointwise (same ball `4B`), so `normR ≤ normB`.
  have hnormR_le : normR ≤ normB := by
    rw [hnormR_def, hnormB_def]; gcongr with z
    filter_upwards with z; gcongr; exact le_add_self
  -- Ball-transfer for nonnegative integrands: `⨍⁻_{2B} g ≤ 4·⨍⁻_{4B} g`, since
  -- `∫⁻_{2B} ≤ ∫⁻_{4B}` (subset) and `|4B| = 4·|2B|`.
  have htransfer : ∀ g : ℂ → ℝ≥0∞, (⨍⁻ z in B2, g z ∂volume) ≤ 4 * ⨍⁻ z in B4, g z ∂volume := by
    intro g
    rw [setLAverage_eq, setLAverage_eq, hvol_ratio, mul_div_assoc',
      ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
    gcongr
  -- `normH ≤ 2·normB`: pointwise `‖R‖² ≤ (‖h‖+‖R‖)²` on `2B`, then transfer `2B → 4B`
  -- (factor `4` under the root becomes `2`).
  have hnormH_le2 : normH ≤ 2 * normB := by
    have hstep : normH ≤ (⨍⁻ z in B2, ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ) ∂volume)
        ^ (1 / (2 : ℝ)) := by
      rw [hnormH_def]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [setLAverage_eq, setLAverage_eq]
      gcongr
      exact le_add_self
    refine le_trans hstep ?_
    refine le_trans (ENNReal.rpow_le_rpow
      (htransfer (fun z => ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ)))
      (by norm_num : (0:ℝ) ≤ 1/2)) ?_
    rw [hnormB_def, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      show (4 : ℝ≥0∞) ^ (1 / (2:ℝ)) = 2 from by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by simp [ENNReal.ofReal_ofNat],
          ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
          show (4 : ℝ) ^ (1 / (2:ℝ)) = 2 from by
            rw [show (4:ℝ) = 2^(2:ℝ) from by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
        simp [ENNReal.ofReal_ofNat]]
  -- ====================================================================
  -- (Assemble) Substitute N1, the conversion, Jensen, and collect constants.
  -- ====================================================================
  -- `hS`'s gradient ball `ball x (2·(2r))` is `B4 = ball x (4r)`.
  rw [show (2 : ℝ) * (2 * r) = 4 * r from by ring, ← hB4_def, ← havgGxGy_def] at hS
  refine le_trans hC ?_
  have hrne : r ≠ 0 := hr.ne'
  -- `A₃/r · (C₁·2r) = 2·A₃·C₁` (the `r⁻¹` cancels the `r`, leaving the N1@2r factor `2`).
  have hreal : A₃ / r * (C₁ * (2 * r)) = 2 * (A₃ * C₁) := by
    field_simp
  have hofRealA'C :
      ENNReal.ofReal (2 * (A₃ * C₁)) * ENNReal.ofReal A' = ENNReal.ofReal (2 * (A₃ * C₁ * A')) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  -- First term: `(A₃/r)·oscF ≤ ofReal(2·A₃·C₁·A')·avgG + ofReal(4·A₃·C₁)·normB`.
  have hterm1 : ENNReal.ofReal (A₃ / r) * oscF ≤
      ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * normB := by
    calc ENNReal.ofReal (A₃ / r) * oscF
        ≤ ENNReal.ofReal (A₃ / r) * (ENNReal.ofReal (C₁ * (2 * r)) * avgGxGy) := by
          gcongr
      _ = ENNReal.ofReal (2 * (A₃ * C₁)) * avgGxGy := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hreal]
      _ ≤ ENNReal.ofReal (2 * (A₃ * C₁)) * (ENNReal.ofReal A' * avgG + 2 * avgR) := by gcongr
      _ = ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * avgR := by
          have hgrad : ENNReal.ofReal (2 * (A₃ * C₁)) * (ENNReal.ofReal A' * avgG)
              = ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG := by
            rw [← mul_assoc, hofRealA'C]
          have hforc : ENNReal.ofReal (2 * (A₃ * C₁)) * (2 * avgR)
              = ENNReal.ofReal (4 * (A₃ * C₁)) * avgR := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
              ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2; ring
          rw [mul_add, hgrad, hforc]
      _ ≤ ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * normB := by
          gcongr
          exact le_trans hRJensen hnormR_le
  -- Second term: `A₃·normH ≤ A₃·(2·normB) = ofReal(2·A₃)·normB` (via the `2B → 4B` transfer).
  have hterm2 : ENNReal.ofReal A₃ * normH ≤ ENNReal.ofReal (2 * A₃) * normB := by
    calc ENNReal.ofReal A₃ * normH
        ≤ ENNReal.ofReal A₃ * (2 * normB) := by gcongr
      _ = ENNReal.ofReal (2 * A₃) * normB := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
            ← mul_assoc, ← ENNReal.ofReal_mul hA₃, mul_comm A₃ 2]
  -- Combine: the two `normB` coefficients add to `4·A₃·C₁ + 2·A₃`; both they and the
  -- gradient coefficient `2·A₃·C₁·A'` are `≤ Afin`.
  have hAC0 : 0 ≤ A₃ * C₁ := mul_nonneg hA₃ hC₁
  have hACA'0 : 0 ≤ A₃ * C₁ * A' := mul_nonneg hAC0 hA'0
  have hAfin_grad : ENNReal.ofReal (2 * (A₃ * C₁ * A')) ≤ ENNReal.ofReal Afin :=
    ENNReal.ofReal_le_ofReal (by rw [hAfin_def]; nlinarith [hACA'0, hAC0, hA₃])
  have hAfin_forc :
      ENNReal.ofReal (4 * (A₃ * C₁)) + ENNReal.ofReal (2 * A₃) ≤ ENNReal.ofReal Afin := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by rw [hAfin_def]; nlinarith [hACA'0, hAC0, hA₃])
  calc ENNReal.ofReal (A₃ / r) * oscF + ENNReal.ofReal A₃ * normH
      ≤ (ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * normB)
          + ENNReal.ofReal (2 * A₃) * normB := add_le_add hterm1 hterm2
    _ = ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG
          + (ENNReal.ofReal (4 * (A₃ * C₁)) + ENNReal.ofReal (2 * A₃)) * normB := by
        rw [add_assoc, add_mul]
    _ ≤ ENNReal.ofReal Afin * avgG + ENNReal.ofReal Afin * normB := by
        gcongr

/-! ## S2 — the general Gehring self-improvement lemma -/

/-- **Giaquinta–Giusti iteration lemma.** A nonnegative function `Z` that is bounded
on `[r, R]` and satisfies the hole-filling inequality
`Z t ≤ θ · Z s + A / (s - t)^α + B` for every `r ≤ t < s ≤ R` (with `0 ≤ θ < 1`,
`α > 0`, `A, B ≥ 0`) is controlled at the inner endpoint by the data at scale `R - r`:
`Z r ≤ c(α, θ) · (A / (R - r)^α + B)`, with `c` depending only on `α` and `θ`.

This is the standard absorption device (Giusti, *Direct Methods in the Calculus of
Variations*, Lemma 6.1): the smallness `θ < 1` is iterated along a geometric chain of
radii `r = ρ₀ < ρ₁ < ⋯ → R` (with ratio `τ ∈ (θ^{1/α}, 1)`, so `θ·τ^{-α} < 1`), summing
the geometric series; the boundedness `Z ≤ M` makes the tail `θ^k · Z(ρ_k) → 0`.  It is
what closes the G2 layer-cake of `gehring_selfImprovement`, absorbing the reconstructed
`w^{q+ε}`-mass over the enlargement `16B₀` back onto the inner ball `4B₀`. -/
theorem giaquinta_iteration {α θ : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ {Z : ℝ → ℝ} {r R A B M : ℝ}, r < R → 0 ≤ A → 0 ≤ B →
        (∀ t ∈ Set.Icc r R, 0 ≤ Z t) →
        (∀ t ∈ Set.Icc r R, Z t ≤ M) →
        (∀ t s, r ≤ t → t < s → s ≤ R → Z t ≤ θ * Z s + A / (s - t) ^ α + B) →
        Z r ≤ c * (A / (R - r) ^ α + B) := by
  -- STEP 1: choose the ratio τ.
  have hθα0 : (0:ℝ) ≤ θ ^ (1/α) := Real.rpow_nonneg hθ0 _
  have hinvα : (0:ℝ) < 1/α := by positivity
  have hθα1 : θ ^ (1/α) < 1 := Real.rpow_lt_one hθ0 hθ1 hinvα
  set τ : ℝ := (θ ^ (1/α) + 1) / 2 with hτdef
  have hτ_gt : θ ^ (1/α) < τ := by rw [hτdef]; linarith
  have hτ1 : τ < 1 := by rw [hτdef]; linarith
  have hτ0 : 0 < τ := by rw [hτdef]; linarith
  -- τ^α > θ
  have hτα_pos : 0 < τ ^ α := Real.rpow_pos_of_pos hτ0 α
  have hθlt : θ < τ ^ α := by
    have h := Real.rpow_lt_rpow hθα0 hτ_gt hα
    rwa [← Real.rpow_mul hθ0, one_div_mul_cancel hα.ne', Real.rpow_one] at h
  -- q₀ := θ / τ^α
  set q₀ : ℝ := θ / τ ^ α with hq0def
  have hq0_nonneg : 0 ≤ q₀ := by rw [hq0def]; positivity
  have hq0_lt : q₀ < 1 := by
    rw [hq0def, div_lt_one hτα_pos]; exact hθlt
  -- STEP 2: the constant.
  have h1τ : 0 < 1 - τ := by linarith
  have h1q0 : 0 < 1 - q₀ := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have h1τα_pos : 0 < (1 - τ) ^ (-α) := Real.rpow_pos_of_pos h1τ _
  set c : ℝ := max ((1 - τ) ^ (-α) / (1 - q₀)) (1 / (1 - θ)) with hcdef
  have hc_nonneg : 0 ≤ c := by
    rw [hcdef]; apply le_max_of_le_right; positivity
  refine ⟨c, hc_nonneg, ?_⟩
  -- STEP 3: the ∀-body.
  intro Z r R A B M hrR hA hB hZpos hZbdd hstep
  have hRr : 0 < R - r := by linarith
  have hM0 : 0 ≤ M := le_trans (hZpos r ⟨le_refl r, hrR.le⟩) (hZbdd r ⟨le_refl r, hrR.le⟩)
  -- radius chain
  set ρ : ℕ → ℝ := fun i => r + (1 - τ ^ i) * (R - r) with hρdef
  have hρ0 : ρ 0 = r := by simp [hρdef]
  have hτi_nonneg : ∀ i, (0:ℝ) ≤ τ ^ i := fun i => pow_nonneg hτ0.le i
  have hτi_le_one : ∀ i, τ ^ i ≤ 1 := fun i => pow_le_one₀ hτ0.le hτ1.le
  have hρ_mem : ∀ i, ρ i ∈ Set.Icc r R := by
    intro i
    constructor
    · simp only [hρdef]; nlinarith [hτi_le_one i, hRr, hτi_nonneg i]
    · simp only [hρdef]; nlinarith [hτi_nonneg i, hRr, hτi_le_one i]
  have hρ_ge_r : ∀ i, r ≤ ρ i := fun i => (hρ_mem i).1
  have hρ_le_R : ∀ i, ρ i ≤ R := fun i => (hρ_mem i).2
  -- the gap
  have hgap : ∀ i, ρ (i+1) - ρ i = (τ ^ i) * (1 - τ) * (R - r) := by
    intro i
    simp only [hρdef, pow_succ]
    ring
  have hgap_pos : ∀ i, 0 < ρ (i+1) - ρ i := by
    intro i
    rw [hgap i]
    have : 0 < τ ^ i := pow_pos hτ0 i
    positivity
  have hρ_mono : ∀ i, ρ i < ρ (i+1) := fun i => by linarith [hgap_pos i]
  -- gap rpow
  have hgap_rpow : ∀ i, (ρ (i+1) - ρ i) ^ α = (τ ^ α) ^ i * (1 - τ) ^ α * (R - r) ^ α := by
    intro i
    rw [hgap i, Real.mul_rpow (by positivity) hRr.le, Real.mul_rpow (hτi_nonneg i) h1τ.le]
    congr 2
    rw [← Real.rpow_natCast τ i, ← Real.rpow_natCast (τ ^ α) i, ← Real.rpow_mul hτ0.le,
        ← Real.rpow_mul hτ0.le, mul_comm]
  -- D and Dstep
  set D : ℝ := A * (1 - τ) ^ (-α) * (R - r) ^ (-α) with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set Dstep : ℕ → ℝ := fun i => A / (ρ (i+1) - ρ i) ^ α with hDstepdef
  have hDstep_val : ∀ i, Dstep i = D * ((τ ^ α) ^ i)⁻¹ := by
    intro i
    simp only [hDstepdef, hgap_rpow i, hDdef]
    rw [Real.rpow_neg h1τ.le, Real.rpow_neg hRr.le]
    field_simp
  have hDstep_nonneg : ∀ i, 0 ≤ Dstep i := by
    intro i
    simp only [hDstepdef]
    exact div_nonneg hA (Real.rpow_nonneg (hgap_pos i).le α)
  -- per-step bound: θ^i * Dstep i = D * q₀^i
  have hstep_geom : ∀ i, θ ^ i * Dstep i = D * q₀ ^ i := by
    intro i
    rw [hDstep_val i, hq0def, div_pow]
    have : (τ ^ α) ^ i ≠ 0 := by positivity
    field_simp
  -- the per-step inequality from hstep
  have hper : ∀ i, Z (ρ i) ≤ θ * Z (ρ (i+1)) + Dstep i + B := by
    intro i
    have h := hstep (ρ i) (ρ (i+1)) (hρ_ge_r i) (hρ_mono i) (hρ_le_R (i+1))
    simpa only [hDstepdef] using h
  -- TELESCOPE
  have htele : ∀ k, Z (ρ 0) ≤ θ ^ k * Z (ρ k) + ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hθk : (0:ℝ) ≤ θ ^ k := pow_nonneg hθ0 k
        have hstepk := hper k
        have hmul : θ ^ k * Z (ρ k) ≤ θ ^ k * (θ * Z (ρ (k+1)) + Dstep k + B) :=
          mul_le_mul_of_nonneg_left hstepk hθk
        have hexp : θ ^ k * (θ * Z (ρ (k+1)) + Dstep k + B)
            = θ ^ (k+1) * Z (ρ (k+1)) + θ ^ k * (Dstep k + B) := by
          rw [pow_succ]; ring
        rw [Finset.sum_range_succ]
        calc Z (ρ 0) ≤ θ ^ k * Z (ρ k) + ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) := ih
          _ ≤ θ ^ k * (θ * Z (ρ (k+1)) + Dstep k + B)
                + ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) := by linarith
          _ = θ ^ (k+1) * Z (ρ (k+1))
                + (∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) + θ ^ k * (Dstep k + B)) := by
              rw [hexp]; ring
  -- bound the sum uniformly
  -- geometric partial sums
  have hgeom_bound : ∀ (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ),
      ∑ i ∈ Finset.range k, x ^ i ≤ 1 / (1 - x) := by
    intro x hx0 hx1 k
    rw [geom_sum_eq (by linarith : x ≠ 1)]
    have hxk : (0:ℝ) ≤ x ^ k := pow_nonneg hx0 k
    have hh1x : (0:ℝ) < 1 - x := by linarith
    have heq : (x ^ k - 1) / (x - 1) = (1 - x ^ k) / (1 - x) := by
      rw [← neg_div_neg_eq]; congr 1 <;> ring
    rw [heq]; gcongr; linarith
  have hsum_bound : ∀ k, ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B)
      ≤ D / (1 - q₀) + B / (1 - θ) := by
    intro k
    have hsplit : ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B)
        = (∑ i ∈ Finset.range k, θ ^ i * Dstep i) + B * ∑ i ∈ Finset.range k, θ ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [hsplit]
    have hA1 : (∑ i ∈ Finset.range k, θ ^ i * Dstep i)
        = D * ∑ i ∈ Finset.range k, q₀ ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; exact hstep_geom i
    rw [hA1]
    have hb1 : D * ∑ i ∈ Finset.range k, q₀ ^ i ≤ D / (1 - q₀) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left (hgeom_bound q₀ hq0_nonneg hq0_lt k) hD0
    have hb2 : B * ∑ i ∈ Finset.range k, θ ^ i ≤ B / (1 - θ) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left (hgeom_bound θ hθ0 hθ1 k) hB
    linarith
  -- combine: ∀ k, Z r ≤ θ^k * Z(ρ k) + (D/(1-q₀) + B/(1-θ))
  set C : ℝ := D / (1 - q₀) + B / (1 - θ) with hCdef
  have hbound_k : ∀ k, Z r ≤ θ ^ k * Z (ρ k) + C := by
    intro k
    have h1 := htele k
    have h2 := hsum_bound k
    rw [hρ0] at h1
    linarith
  -- LIMIT k→∞
  have htend_left : Tendsto (fun k : ℕ => θ ^ k * Z (ρ k)) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun k : ℕ => θ ^ k * M)
    · intro k
      have hZk := hZpos (ρ k) (hρ_mem k)
      have hθk : (0:ℝ) ≤ θ ^ k := pow_nonneg hθ0 k
      positivity
    · intro k
      have hZk := hZbdd (ρ k) (hρ_mem k)
      have hθk : (0:ℝ) ≤ θ ^ k := pow_nonneg hθ0 k
      exact mul_le_mul_of_nonneg_left hZk hθk
    · have : Tendsto (fun k : ℕ => θ ^ k * M) atTop (𝓝 (0 * M)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const M
      simpa using this
  have hZr_le_C : Z r ≤ C := by
    have htend_rhs : Tendsto (fun k : ℕ => θ ^ k * Z (ρ k) + C) atTop (𝓝 (0 + C)) :=
      htend_left.add_const C
    have htend_lhs : Tendsto (fun _ : ℕ => Z r) atTop (𝓝 (Z r)) := tendsto_const_nhds
    have := le_of_tendsto_of_tendsto' htend_lhs htend_rhs hbound_k
    simpa using this
  -- FINISH: C = (1-τ)^(-α)/(1-q₀) * (A/(R-r)^α) + (1/(1-θ)) * B ≤ c*(A/(R-r)^α + B)
  have hRrα_pos : 0 < (R - r) ^ α := Real.rpow_pos_of_pos hRr α
  have hAdiv_nonneg : 0 ≤ A / (R - r) ^ α := by positivity
  -- rewrite C
  have hCval : C = ((1 - τ) ^ (-α) / (1 - q₀)) * (A / (R - r) ^ α) + (1 / (1 - θ)) * B := by
    rw [hCdef, hDdef]
    rw [Real.rpow_neg hRr.le]
    field_simp
  rw [hCval] at hZr_le_C
  -- bound coefficients by c
  have hcoef1 : (1 - τ) ^ (-α) / (1 - q₀) ≤ c := by rw [hcdef]; exact le_max_left _ _
  have hcoef2 : 1 / (1 - θ) ≤ c := by rw [hcdef]; exact le_max_right _ _
  calc Z r ≤ ((1 - τ) ^ (-α) / (1 - q₀)) * (A / (R - r) ^ α) + (1 / (1 - θ)) * B := hZr_le_C
    _ ≤ c * (A / (R - r) ^ α) + c * B := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hcoef1 hAdiv_nonneg
        · exact mul_le_mul_of_nonneg_right hcoef2 hB
    _ = c * (A / (R - r) ^ α + B) := by ring

/-- **Dyadic reverse-Hölder transfer** (private copy for `gehring_selfImprovement`).  A
metric-ball reverse-Hölder inequality with the fixed enlargement factor `4` (the hypothesis
form consumed by `gehring_selfImprovement`) yields a reverse-Hölder inequality on every dyadic
square `R = dyadicSquare m k`, with the right-hand side over the comparable ball about the
square's centre of radius `4 · 2^m`.  Reproduced here because `DyadicGehring` (which states the
public version) would create an import cycle. -/
private theorem dyadic_reverseHolder' {q A : ℝ} (hq : 1 < q) (_hA : 0 ≤ A)
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
  set c := dyadicCenter m k with hc
  set s : ℝ := (2 : ℝ) ^ m with hs
  have hs0 : 0 < s := by rw [hs]; exact zpow_pos (by norm_num) m
  set R := dyadicSquare m k with hR
  set Bs := Metric.ball c s with hBs
  have hq0 : (0 : ℝ) ≤ 1 / q := by positivity
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
  have hratio : volume Bs / volume R = ENNReal.ofReal Real.pi := by
    rw [hvolR, hvolBs, ENNReal.ofReal_mul Real.pi_pos.le, mul_div_assoc, ENNReal.div_self]
    · rw [mul_one]
    · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hs2pos
    · exact ENNReal.ofReal_ne_top
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
  have hStepB : (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q) ≤
      ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := by
    calc (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q)
        ≤ (ENNReal.ofReal Real.pi * (⨍⁻ z in Bs, w z ^ q ∂volume)) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hStepA hq0
      _ = ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.ofReal_rpow_of_pos Real.pi_pos]
  have hStepC := hRH c s hs0
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

/-- **Layer-cake (Cavalieri) for a truncated weight over a ball** (helper for the
hole-filling step of `gehring_selfImprovement`).  For the bounded truncation
`min w N` and any exponent `p > 0`, the `(p)`-mass over a ball is the Cavalieri
integral of the super-level measures of the real-valued truncation `(min w N).toReal`
against the radial weight `λ^{p-1}`.  This is `lintegral_rpow_eq_lintegral_meas_lt_mul`
transported from the real layer (`(min w N).toReal`) to the `ℝ≥0∞` weight, using that
`min w N ≤ N < ⊤` so that `min w N = ofReal ((min w N).toReal)` pointwise. -/
private theorem holeFill_layerCake {p : ℝ} (hp : 0 < p) {w : ℂ → ℝ≥0∞}
    (hwmeas : AEMeasurable w volume) (N : ℕ) (x₀ : ℂ) (t : ℝ) :
    ∫⁻ z in Metric.ball x₀ t, (min (w z) (N : ℝ≥0∞)) ^ p
      = ENNReal.ofReal p * ∫⁻ lam in Set.Ioi (0 : ℝ),
          (volume.restrict (Metric.ball x₀ t)) {z | lam < (min (w z) (N : ℝ≥0∞)).toReal}
            * ENNReal.ofReal (lam ^ (p - 1)) := by
  set μ := volume.restrict (Metric.ball x₀ t) with hμ
  set f : ℂ → ℝ := fun z => (min (w z) (N : ℝ≥0∞)).toReal with hf
  have hfnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall (fun z => ENNReal.toReal_nonneg)
  have hfmeas : AEMeasurable f μ :=
    ((hwmeas.min aemeasurable_const).ennreal_toReal).restrict
  have key := lintegral_rpow_eq_lintegral_meas_lt_mul μ hfnn hfmeas hp
  rw [← key]
  have hpt : ∀ z, (min (w z) (N : ℝ≥0∞)) ^ p = ENNReal.ofReal (f z ^ p) := by
    intro z
    have hfin : min (w z) (N : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
    rw [hf, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal hfin]
  calc ∫⁻ z in Metric.ball x₀ t, (min (w z) (N : ℝ≥0∞)) ^ p
      = ∫⁻ z, (min (w z) (N : ℝ≥0∞)) ^ p ∂μ := rfl
    _ = ∫⁻ z, ENNReal.ofReal (f z ^ p) ∂μ := by
        apply lintegral_congr; intro z; rw [hpt z]

/-- A closed ball in `ℂ` is `volume`-a.e. equal to the corresponding open ball (the sphere
is null). -/
private theorem closedBall_aeEq_ball' (c : ℂ) (ρ : ℝ) :
    Metric.closedBall c ρ =ᵐ[volume] Metric.ball c ρ := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · -- `closedBall \ ball ⊆ sphere`, null.
    refine measure_mono_null ?_ (Measure.addHaar_sphere volume c ρ)
    intro z hz
    rw [Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball, not_lt] at hz
    rw [Metric.mem_sphere]; linarith [hz.1, hz.2]
  · -- `ball \ closedBall = ∅`.
    convert measure_empty (μ := (volume : Measure ℂ)) using 2
    rw [Set.diff_eq_empty]
    exact Metric.ball_subset_closedBall

/-- **Per-point density witness ball** (helper for the good-λ measure bound).  For a
`volume`-globally-integrable nonnegative weight `g : ℂ → ℝ≥0∞` (`∫⁻ g < ⊤`), at a.e. point
`c` the ball averages `(∫⁻_{ball c ρ} g)/vol(ball c ρ)` converge to `g c` as `ρ → 0⁺`;
consequently, for a.e. `c`, any height `Λ < g c`, and any cap `ρ₀ > 0`, there is a radius
`0 < ρ ≤ ρ₀` with `Λ < (∫⁻_{ball c ρ} g)/vol(ball c ρ)`.  Proven from Mathlib's Lebesgue
differentiation (`VitaliFamily.ae_tendsto_lintegral_div` on the uniformly-locally-doubling
Vitali family, transported to closed balls via `tendsto_closedBall_filterAt`) plus the planar
fact that closed and open balls have equal volume and integral. -/
private theorem gehring_density_ball {g : ℂ → ℝ≥0∞}
    (hgmeas : AEMeasurable g volume) (hgfin : ∫⁻ z, g z < ⊤) :
    ∀ᵐ c ∂volume, ∀ Λ : ℝ≥0∞, Λ < g c → ∀ ρ₀ : ℝ, 0 < ρ₀ →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
        Λ < (∫⁻ z in Metric.ball c ρ, g z) / volume (Metric.ball c ρ) := by
  -- The uniformly-locally-doubling Vitali family for `volume` on `ℂ`.
  set v : VitaliFamily (volume : Measure ℂ) := IsUnifLocDoublingMeasure.vitaliFamily volume 1
    with hv
  -- Lebesgue differentiation: for a.e. `c`, `(∫⁻_a g)/vol a → g c` along `v.filterAt c`.
  filter_upwards [v.ae_tendsto_lintegral_div hgmeas hgfin.ne] with c hc
  intro Λ hΛ ρ₀ hρ₀
  -- A radius sequence `δ n = ρ₀ / (n+1) → 0⁺`.
  set δ : ℕ → ℝ := fun n => ρ₀ / (n + 1) with hδ
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos hρ₀ (by positivity)
  have hδto : Tendsto δ atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall (fun n => hδpos n)⟩
    rw [hδ]
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := ρ₀)).div_atTop h1
  -- Convergence over the closed balls `closedBall c (δ n)`.
  have hclosed : Tendsto
      (fun n : ℕ => (∫⁻ z in Metric.closedBall c (δ n), g z) / volume (Metric.closedBall c (δ n)))
      atTop (𝓝 (g c)) := by
    have htf : Tendsto (fun n : ℕ => Metric.closedBall c (δ n)) atTop (v.filterAt c) := by
      refine IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt
        (μ := (volume : Measure ℂ)) (fun _ => c) δ hδto ?_
      exact Eventually.of_forall (fun n => by
        rw [one_mul]; exact Metric.mem_closedBall_self (hδpos n).le)
    exact hc.comp htf
  -- Switch closed balls to open balls (equal volume and integral in the plane).
  have hcb_eq : ∀ n,
      (∫⁻ z in Metric.closedBall c (δ n), g z) / volume (Metric.closedBall c (δ n))
        = (∫⁻ z in Metric.ball c (δ n), g z) / volume (Metric.ball c (δ n)) := by
    intro n
    have hae := closedBall_aeEq_ball' c (δ n)
    rw [setLIntegral_congr hae, measure_congr hae]
  rw [Filter.tendsto_congr hcb_eq] at hclosed
  -- Eventually the open-ball averages exceed `Λ`.
  have hev : ∀ᶠ n in atTop,
      Λ < (∫⁻ z in Metric.ball c (δ n), g z) / volume (Metric.ball c (δ n)) :=
    hclosed.eventually_const_lt hΛ
  -- Also `δ n ≤ ρ₀` (always).
  have hev2 : ∀ᶠ n in atTop, δ n ≤ ρ₀ := Eventually.of_forall (fun n => by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith [hρ₀.le, (Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  obtain ⟨n, hn1, hn2⟩ := (hev.and hev2).exists
  exact ⟨δ n, hδpos n, hn2, hn1⟩

/-- **Carleson covering bound** (helper for the good-λ measure bound).  Given a level
`l ≠ 0, ⊤`, a weight `u`, a (possibly uncountable) center set `T`, a radius function
`R : ℂ → ℝ` bounded by `Rbd`, with the per-ball averaging property
`l·vol(ball c (R c)) ≤ ∫_{ball c (R c)} u` on `T`, the union of the balls has
`l·vol(⋃_{c∈T} ball c (R c)) ≤ 16·∫⁻ u`.  Lindelöf (`isOpen_biUnion_countable`) extracts a
countable subfamily that preserves the union, then the Carleson Vitali engine
`Set.Countable.measure_biUnion_le_lintegral` (planar doubling `A_dbl = 4`, `A_dbl² = 16`)
internalizes the overlap. -/
private theorem gehring_engine_bound (l : ℝ≥0∞) (u : ℂ → ℝ≥0∞) (T : Set ℂ) (R : ℂ → ℝ)
    (Rbd : ℝ) (hRbd : ∀ c ∈ T, R c ≤ Rbd)
    (h2u : ∀ c ∈ T, l * volume (Metric.ball c (R c)) ≤ ∫⁻ z in Metric.ball c (R c), u z) :
    l * volume (⋃ c ∈ T, Metric.ball c (R c)) ≤ (16 : ℝ≥0∞) * ∫⁻ z, u z := by
  haveI hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  -- Extract a countable subfamily preserving the union.
  obtain ⟨Tc, hTcsub, hTccount, hTcU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable (ι := ℂ) T (fun c => Metric.ball c (R c))
      (fun c _ => Metric.isOpen_ball)
  rw [← hTcU]
  -- Engine on the countable family `Tc ⊆ T`.
  have hengine := hTccount.measure_biUnion_le_lintegral (μ := (volume : Measure ℂ))
    (A := 2 ^ Module.finrank ℝ ℂ) (c := id) (r := R) l u Rbd
    (fun c hc => hRbd c (hTcsub hc)) (fun c hc => h2u c (hTcsub hc))
  -- `A_dbl² = 16`.
  have hA2 : ((2 ^ Module.finrank ℝ ℂ : ℝ≥0) : ℝ≥0∞) ^ 2 = (16 : ℝ≥0∞) := by
    rw [Complex.finrank_real_complex]; norm_num
  simpa only [id, hA2] using hengine

/-- **Good-λ super-level measure bound** (the Calderón–Zygmund covering core of the
hole-filling step of `gehring_selfImprovement`).  For concentric radii
`4R₀ ≤ t < s ≤ 16R₀`, every truncation `N`, and every height `lam > 0`, the volume of the
super-level set of the truncation `min w N` inside `ball x₀ t` is controlled by a
`(1/lam)`-weighted `w`-mass plus a `(1/lam)^q`-weighted `bᵠ`-mass over the larger ball
`ball x₀ s`:
`vol {z ∈ ball x₀ t | lam < (min w N) z} ≤ ofReal(Cw/lam)·∫_{ball x₀ s} w
    + ofReal((Cb/lam)^q · 16)·∫_{ball x₀ s} bᵠ`
with `Cw = 2(A+1)·16`, `Cb = 2(A+1)`.  Construction: each super-level point has, by Lebesgue
differentiation (`gehring_density_ball`), a small ball `ball c ρ_c` (radius capped at
`(s-t)/8`) with `⨍_{ball c ρ_c} wᵠ > lamᵠ`; the per-ball reverse-Hölder hypothesis `hRH`
splits it into a `w`-dominated and a `b`-dominated alternative; the two subfamilies of
enlarged balls `ball c (4ρ_c) ⊆ ball x₀ s` are fed to the Carleson Vitali engine
`Set.Countable.measure_biUnion_le_lintegral` (planar doubling constant `A_dbl = 2² = 4`,
`A_dbl² = 16`), which internalizes the bounded overlap.  This is `w,b`-uniform. -/
private theorem gehring_goodLambda_measure {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (_hbmeas : AEMeasurable b volume)
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (x₀ : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (hWfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (N : ℕ) (t s : ℝ) (_ht : 4 * R₀ ≤ t) (hts : t < s) (hs : s ≤ 16 * R₀)
    (lam : ℝ) (hlam : 0 < lam) :
    volume {z : ℂ | z ∈ Metric.ball x₀ t ∧ lam < (min (w z) (N : ℝ≥0∞)).toReal}
      ≤ ENNReal.ofReal ((2 * (A + 1) / lam) * 16) * (∫⁻ z in Metric.ball x₀ s, w z)
        + ENNReal.ofReal ((2 * (A + 1) / lam) ^ q * 16) *
            (∫⁻ z in Metric.ball x₀ s, b z ^ q) := by
  classical
  -- The planar doubling instance (`A_dbl = 2^finrank ℝ ℂ = 4`) for the Carleson engine.
  haveI hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  have hAdbl : (2 ^ Module.finrank ℝ ℂ : ℝ≥0) = 4 := by
    rw [Complex.finrank_real_complex]; norm_num
  -- Notation.
  have hq0 : 0 < q := lt_trans one_pos hq
  set Ã : ℝ := A + 1 with hÃdef
  have hÃpos : 0 < Ã := by rw [hÃdef]; linarith
  have hÃ0 : 0 ≤ Ã := hÃpos.le
  -- `hRH` upgraded to the larger constant `Ã = A + 1` (RHS only grows).
  have hRHÃ : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q) := by
    intro x r hr
    refine le_trans (hRH x r hr) (add_le_add ?_ ?_) <;>
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by rw [hÃdef]; linarith)) _
  -- The localized weight `g = wᵠ · 1_{ball x₀ 16R₀}` (globally integrable).
  set B16 : Set ℂ := Metric.ball x₀ (16 * R₀) with hB16
  set g : ℂ → ℝ≥0∞ := B16.indicator (fun z => w z ^ q) with hgdef
  have hgmeas : AEMeasurable g volume :=
    (hwmeas.pow_const q).indicator measurableSet_ball
  have hgfin : ∫⁻ z, g z < ⊤ := by
    rw [hgdef, lintegral_indicator measurableSet_ball]; exact hWfin
  -- The super-level set.
  set S : Set ℂ := {z : ℂ | z ∈ Metric.ball x₀ t ∧ lam < (min (w z) (N : ℝ≥0∞)).toReal}
    with hSdef
  -- Heights for the density witness: `Λ = (ofReal lam)^q`.
  set Λ : ℝ≥0∞ := ENNReal.ofReal lam ^ q with hΛdef
  -- Capping radius and geometry.
  set ρ₀ : ℝ := (s - t) / 8 with hρ₀def
  have hst : 0 < s - t := by linarith
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; positivity
  -- Step bound from `hWfin`: localize-to-`ball x₀ s` integrals are over a sub-ball of 16R₀.
  have hsubs16 : Metric.ball x₀ s ⊆ B16 := by
    rw [hB16]; exact Metric.ball_subset_ball (by linarith)
  -- =========================================================================
  -- PER-POINT WITNESS.  For a.e. `c ∈ S`, there is a capped ball `ball c ρ` with
  -- `⨍_{ball c ρ} wᵠ > lamᵠ`, and `hRH` yields the `w`/`b` dichotomy.
  -- =========================================================================
  -- The good set: the full-measure set on which the density witness holds.
  set Good : Set ℂ := {c : ℂ | ∀ Λ' : ℝ≥0∞, Λ' < g c → ∀ ρ₀' : ℝ, 0 < ρ₀' →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀' ∧
        Λ' < (∫⁻ z in Metric.ball c ρ, g z) / volume (Metric.ball c ρ)} with hGooddef
  have hGoodae : volume (Goodᶜ) = 0 := by
    have hae := gehring_density_ball hgmeas hgfin
    rw [MeasureTheory.ae_iff] at hae
    exact hae
  have hDdens : ∀ c ∈ Good, ∀ Λ' : ℝ≥0∞, Λ' < g c → ∀ ρ₀' : ℝ, 0 < ρ₀' →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀' ∧
        Λ' < (∫⁻ z in Metric.ball c ρ, g z) / volume (Metric.ball c ρ) := fun c hc => hc
  -- For `c ∈ S ∩ D` (a.e. all of `S`), the dichotomy: a capped enlarged ball that is
  -- either `w`-good or `b`-good.
  -- The two scalar levels.
  set lw : ℝ≥0∞ := ENNReal.ofReal (lam / (2 * Ã)) with hlwdef
  set lb : ℝ≥0∞ := ENNReal.ofReal ((lam / (2 * Ã)) ^ q) with hlbdef
  -- Per-point dichotomy.  For `c ∈ S ∩ Good`: a capped radius `ρ` whose enlarged ball
  -- `ball c (4ρ) ⊆ ball x₀ s` is either `w`-good (`lw·vol ≤ ∫ w`) or `b`-good
  -- (`lb·vol ≤ ∫ bᵠ`).
  have hdich : ∀ c ∈ S ∩ Good, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball c (4 * ρ) ⊆ Metric.ball x₀ s ∧
      (lw * volume (Metric.ball c (4 * ρ)) ≤ ∫⁻ z in Metric.ball c (4 * ρ), w z ∨
       lb * volume (Metric.ball c (4 * ρ)) ≤ ∫⁻ z in Metric.ball c (4 * ρ), b z ^ q) ∧
      4 * ρ ≤ (s - t) / 2 := by
    rintro c ⟨hcS, hcGood⟩
    obtain ⟨hct, hclam⟩ := hcS
    -- `c ∈ B16`.
    have hcB16 : c ∈ B16 := hsubs16 (Metric.ball_subset_ball (by linarith) hct)
    -- `g c = w c ^ q`.
    have hgc : g c = w c ^ q := by rw [hgdef, Set.indicator_of_mem hcB16]
    -- `ofReal lam < w c`.
    have hlam_wc : ENNReal.ofReal lam < w c := by
      have h1 : ENNReal.ofReal lam < min (w c) (N : ℝ≥0∞) := by
        have hfin : min (w c) (N : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
        rw [← ENNReal.ofReal_toReal hfin]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le |>.mpr hclam
      exact lt_of_lt_of_le h1 (min_le_left _ _)
    -- `Λ < g c`.
    have hΛlt : Λ < g c := by
      rw [hgc, hΛdef]; exact ENNReal.rpow_lt_rpow hlam_wc hq0
    -- Density witness ball.
    obtain ⟨ρ, hρpos, hρcap, hρavg⟩ := hDdens c hcGood Λ hΛlt ρ₀ hρ₀pos
    -- `ball c ρ ⊆ ball x₀ s` (capped).
    have hballρ_sub : Metric.ball c ρ ⊆ Metric.ball x₀ s := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_ball] at hct
      have : dist z x₀ ≤ dist z c + dist c x₀ := dist_triangle z c x₀
      have hρle : ρ ≤ (s - t) / 8 := hρcap
      nlinarith [this, hz, hct, hρle, hst]
    have hball4ρ_sub : Metric.ball c (4 * ρ) ⊆ Metric.ball x₀ s := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_ball] at hct
      have htri : dist z x₀ ≤ dist z c + dist c x₀ := dist_triangle z c x₀
      have hρle : ρ ≤ (s - t) / 8 := hρcap
      nlinarith [htri, hz, hct, hρle, hst]
    refine ⟨ρ, hρpos, hball4ρ_sub, ?_, by linarith [hρcap, hst]⟩
    -- On `ball c ρ ⊆ B16`, `g = wᵠ`, so the density average is the `wᵠ`-average.
    have hballρ_B16 : Metric.ball c ρ ⊆ B16 := hballρ_sub.trans hsubs16
    have hgint : ∫⁻ z in Metric.ball c ρ, g z = ∫⁻ z in Metric.ball c ρ, w z ^ q := by
      refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
      rw [hgdef, Set.indicator_of_mem (hballρ_B16 hz)]
    rw [hgint] at hρavg
    -- `(ofReal lam)^q < ⨍⁻_{ball c ρ} wᵠ`.
    have hvolρ_pos : 0 < volume (Metric.ball c ρ) := Metric.measure_ball_pos _ _ hρpos
    have havg : Λ < ⨍⁻ z in Metric.ball c ρ, w z ^ q ∂volume := by
      rw [setLAverage_eq]; exact hρavg
    -- Take `^{1/q}`: `ofReal lam < (⨍⁻ wᵠ)^{1/q}`.
    have h1q : (0:ℝ) < 1 / q := by positivity
    have hroot : ENNReal.ofReal lam < (⨍⁻ z in Metric.ball c ρ, w z ^ q ∂volume) ^ (1 / q) := by
      rw [hΛdef] at havg
      have h := ENNReal.rpow_lt_rpow havg h1q
      have hid : (ENNReal.ofReal lam ^ q) ^ (1 / q) = ENNReal.ofReal lam := by
        rw [one_div, ENNReal.rpow_rpow_inv hq0.ne']
      rwa [hid] at h
    -- Reverse-Hölder dichotomy at `ball c ρ`.
    have hRHc := hRHÃ c ρ hρpos
    have hsum : ENNReal.ofReal lam <
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q) :=
      lt_of_lt_of_le hroot hRHc
    -- One of the two terms is `≥ ofReal lam / 2`.
    have hhalf : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume)
          ≥ ENNReal.ofReal lam / 2 ∨
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q)
          ≥ ENNReal.ofReal lam / 2 := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [not_le] at h1 h2
      have : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q)
          < ENNReal.ofReal lam / 2 + ENNReal.ofReal lam / 2 := ENNReal.add_lt_add h1 h2
      rw [ENNReal.add_halves] at this
      exact absurd (lt_trans hsum this) (lt_irrefl _)
    -- Volume facts for `4ρ`-ball (positive, finite).
    have hvol4_pos : 0 < volume (Metric.ball c (4 * ρ)) :=
      Metric.measure_ball_pos _ _ (by positivity)
    have hvol4_ne : volume (Metric.ball c (4 * ρ)) ≠ 0 := hvol4_pos.ne'
    have hvol4_top : volume (Metric.ball c (4 * ρ)) ≠ ⊤ := measure_ball_lt_top.ne
    have hÃne : ENNReal.ofReal Ã ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hÃpos
    have hÃtop : ENNReal.ofReal Ã ≠ ⊤ := ENNReal.ofReal_ne_top
    -- The clean key: `lw * ofReal Ã = ofReal lam / 2` (and similarly for the `q`-power).
    have hlw_mul : lw * ENNReal.ofReal Ã = ENNReal.ofReal lam / 2 := by
      rw [hlwdef, ← ENNReal.ofReal_mul (by positivity)]
      have hreal : lam / (2 * Ã) * Ã = lam / 2 := by
        field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1; norm_num
    rcases hhalf with hw | hb
    · -- `w`-good: `lw·vol(4B) ≤ ∫_{4B} w`.
      left
      -- `lw ≤ ⨍ w` by cancelling `ofReal Ã` from `lw·ofReal Ã = ofReal lam/2 ≤ ofReal Ã·⨍ w`.
      have hge : lw ≤ ⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume := by
        have hchain : lw * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume) * ENNReal.ofReal Ã := by
          rw [hlw_mul, mul_comm]; exact hw
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      rw [setLAverage_eq] at hge
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hge
    · -- `b`-good: `lb·vol(4B) ≤ ∫_{4B} bᵠ`.
      right
      -- `lb = lw^q`, and from `lw ≤ (⨍ bᵠ)^{1/q}` raise to `q`.
      have hlb_eq : lb = lw ^ q := by
        rw [hlbdef, hlwdef, ← ENNReal.ofReal_rpow_of_pos (by positivity)]
      have hgew : lw ≤ (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q) := by
        have hchain : lw * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q) * ENNReal.ofReal Ã := by
          rw [hlw_mul, mul_comm]; exact hb
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      have hgeq : lb ≤ ⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume := by
        rw [hlb_eq]
        have hpow := ENNReal.rpow_le_rpow hgew hq0.le
        rwa [one_div, ENNReal.rpow_inv_rpow hq0.ne'] at hpow
      rw [setLAverage_eq] at hgeq
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hgeq
  -- =========================================================================
  -- ASSEMBLY.  Choose, for each `c ∈ S ∩ Good`, the enlarged radius `R c = 4ρ_c`;
  -- partition into `w`-good and `b`-good centers; feed each subfamily to the engine.
  -- =========================================================================
  -- Total enlarged-radius function (`0` off `S ∩ Good`).
  set Rfun : ℂ → ℝ := fun c => if h : c ∈ S ∩ Good then 4 * (hdich c h).choose else 0
    with hRfundef
  -- Spec of the choice on `S ∩ Good`.
  have hRspec : ∀ c (h : c ∈ S ∩ Good), 0 < Rfun c ∧
      Metric.ball c (Rfun c) ⊆ Metric.ball x₀ s ∧
      (lw * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), w z ∨
       lb * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), b z ^ q) ∧
      Rfun c ≤ (s - t) / 2 := by
    intro c h
    have hch := (hdich c h).choose_spec
    obtain ⟨hρpos, hsub, hdisj, hcap⟩ := hch
    have hRfval : Rfun c = 4 * (hdich c h).choose := by rw [hRfundef]; simp [h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hRfval]; positivity
    · rw [hRfval]; exact hsub
    · rw [hRfval]; exact hdisj
    · rw [hRfval]; exact hcap
  -- The `w`-good and `b`-good center subsets.
  set Sw : Set ℂ := {c | ∃ h : c ∈ S ∩ Good,
      lw * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), w z} with hSwdef
  set Sb : Set ℂ := {c | ∃ h : c ∈ S ∩ Good,
      lb * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), b z ^ q} with hSbdef
  -- Every `c ∈ S ∩ Good` lies in `Sw ∪ Sb`, and inside its own ball.
  have hcover : S ∩ Good ⊆ (⋃ c ∈ Sw, Metric.ball c (Rfun c))
      ∪ (⋃ c ∈ Sb, Metric.ball c (Rfun c)) := by
    intro c hc
    obtain ⟨hRpos, _, hdisj, _⟩ := hRspec c hc
    have hcmem : c ∈ Metric.ball c (Rfun c) := Metric.mem_ball_self hRpos
    rcases hdisj with hw | hb
    · exact Or.inl (Set.mem_biUnion (⟨hc, hw⟩) hcmem)
    · exact Or.inr (Set.mem_biUnion (⟨hc, hb⟩) hcmem)
  -- Uniform radius bound and averaging hypotheses for the two engine calls.
  have hRbd_w : ∀ c ∈ Sw, Rfun c ≤ (s - t) / 2 := by
    rintro c ⟨h, _⟩; exact (hRspec c h).2.2.2
  have hRbd_b : ∀ c ∈ Sb, Rfun c ≤ (s - t) / 2 := by
    rintro c ⟨h, _⟩; exact (hRspec c h).2.2.2
  -- `u`-weights localized to `ball x₀ s`.
  have h2u_w : ∀ c ∈ Sw, lw * volume (Metric.ball c (Rfun c))
      ≤ ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator w z := by
    rintro c ⟨h, hle⟩
    have hsub : Metric.ball c (Rfun c) ⊆ Metric.ball x₀ s := (hRspec c h).2.1
    have heq : ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator w z
        = ∫⁻ z in Metric.ball c (Rfun c), w z := by
      refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
      rw [Set.indicator_of_mem (hsub hz)]
    rw [heq]; exact hle
  have h2u_b : ∀ c ∈ Sb, lb * volume (Metric.ball c (Rfun c))
      ≤ ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator (fun z => b z ^ q) z := by
    rintro c ⟨h, hle⟩
    have hsub : Metric.ball c (Rfun c) ⊆ Metric.ball x₀ s := (hRspec c h).2.1
    have heq : ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator (fun z => b z ^ q) z
        = ∫⁻ z in Metric.ball c (Rfun c), b z ^ q := by
      refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
      rw [Set.indicator_of_mem (hsub hz)]
    rw [heq]; exact hle
  -- Engine bounds.
  have hEw := gehring_engine_bound lw ((Metric.ball x₀ s).indicator w) Sw Rfun ((s - t) / 2)
    hRbd_w h2u_w
  have hEb := gehring_engine_bound lb ((Metric.ball x₀ s).indicator (fun z => b z ^ q)) Sb Rfun
    ((s - t) / 2) hRbd_b h2u_b
  -- The localized global integrals are the `ball x₀ s` integrals.
  have hIw : ∫⁻ z, (Metric.ball x₀ s).indicator w z = ∫⁻ z in Metric.ball x₀ s, w z := by
    rw [lintegral_indicator measurableSet_ball]
  have hIb : ∫⁻ z, (Metric.ball x₀ s).indicator (fun z => b z ^ q) z
      = ∫⁻ z in Metric.ball x₀ s, b z ^ q := by
    rw [lintegral_indicator measurableSet_ball]
  rw [hIw] at hEw
  rw [hIb] at hEb
  -- Positivity/finiteness of `lw, lb`.
  have hlw_pos : 0 < lw := by rw [hlwdef, ENNReal.ofReal_pos]; positivity
  have hlb_pos : 0 < lb := by rw [hlbdef, ENNReal.ofReal_pos]; positivity
  have hlw_ne : lw ≠ 0 := hlw_pos.ne'
  have hlb_ne : lb ≠ 0 := hlb_pos.ne'
  have hlw_top : lw ≠ ⊤ := by rw [hlwdef]; exact ENNReal.ofReal_ne_top
  have hlb_top : lb ≠ ⊤ := by rw [hlbdef]; exact ENNReal.ofReal_ne_top
  -- The coefficients and the key cancellation identities `coefw · lw = 16`, `coefb · lb = 16`.
  have h2Ãpos : 0 < 2 * Ã := by positivity
  set coefw : ℝ≥0∞ := ENNReal.ofReal ((2 * (A + 1) / lam) * 16) with hcoefwdef
  set coefb : ℝ≥0∞ := ENNReal.ofReal ((2 * (A + 1) / lam) ^ q * 16) with hcoefbdef
  have hcw_mul : coefw * lw = (16 : ℝ≥0∞) := by
    rw [hcoefwdef, hlwdef, ← ENNReal.ofReal_mul (by positivity), ← hÃdef]
    rw [show (2 * Ã / lam) * 16 * (lam / (2 * Ã)) = 16 by field_simp]
    rw [ENNReal.ofReal_ofNat]
  have hcb_mul : coefb * lb = (16 : ℝ≥0∞) := by
    rw [hcoefbdef, hlbdef, ← ENNReal.ofReal_mul (by positivity), ← hÃdef]
    rw [show (2 * Ã / lam) ^ q * 16 * (lam / (2 * Ã)) ^ q = 16 by
      rw [mul_right_comm, ← Real.mul_rpow (by positivity) (by positivity),
        show (2 * Ã / lam) * (lam / (2 * Ã)) = 1 by field_simp, Real.one_rpow, one_mul]]
    rw [ENNReal.ofReal_ofNat]
  -- Convert the engine bounds to volume bounds: `vol(⋃) ≤ coef·∫`.
  have hVw : volume (⋃ c ∈ Sw, Metric.ball c (Rfun c))
      ≤ coefw * (∫⁻ z in Metric.ball x₀ s, w z) := by
    have hcw_pos : 0 < coefw := by rw [hcoefwdef, ENNReal.ofReal_pos]; positivity
    have hkey : lw * volume (⋃ c ∈ Sw, Metric.ball c (Rfun c))
        ≤ lw * (coefw * (∫⁻ z in Metric.ball x₀ s, w z)) := by
      calc lw * volume (⋃ c ∈ Sw, Metric.ball c (Rfun c))
          ≤ (16 : ℝ≥0∞) * ∫⁻ z in Metric.ball x₀ s, w z := hEw
        _ = (coefw * lw) * ∫⁻ z in Metric.ball x₀ s, w z := by rw [hcw_mul]
        _ = lw * (coefw * (∫⁻ z in Metric.ball x₀ s, w z)) := by ring
    exact (ENNReal.mul_le_mul_iff_right hlw_ne hlw_top).mp hkey
  have hVb : volume (⋃ c ∈ Sb, Metric.ball c (Rfun c))
      ≤ coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q) := by
    have hkey : lb * volume (⋃ c ∈ Sb, Metric.ball c (Rfun c))
        ≤ lb * (coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q)) := by
      calc lb * volume (⋃ c ∈ Sb, Metric.ball c (Rfun c))
          ≤ (16 : ℝ≥0∞) * ∫⁻ z in Metric.ball x₀ s, b z ^ q := hEb
        _ = (coefb * lb) * ∫⁻ z in Metric.ball x₀ s, b z ^ q := by rw [hcb_mul]
        _ = lb * (coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q)) := by ring
    exact (ENNReal.mul_le_mul_iff_right hlb_ne hlb_top).mp hkey
  -- Final: `vol S = vol(S ∩ Good) ≤ vol(⋃Sw) + vol(⋃Sb)`.
  have hSeq : volume S = volume (S ∩ Good) := by
    refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
    calc volume S ≤ volume ((S ∩ Good) ∪ Goodᶜ) := by
          refine measure_mono (fun z hz => ?_)
          by_cases hg : z ∈ Good
          · exact Or.inl ⟨hz, hg⟩
          · exact Or.inr hg
      _ ≤ volume (S ∩ Good) + volume (Goodᶜ) := measure_union_le _ _
      _ = volume (S ∩ Good) := by rw [hGoodae, add_zero]
  rw [hSdef] at hSeq ⊢
  rw [← hSdef, hSeq]
  calc volume (S ∩ Good)
      ≤ volume ((⋃ c ∈ Sw, Metric.ball c (Rfun c)) ∪ (⋃ c ∈ Sb, Metric.ball c (Rfun c))) :=
        measure_mono hcover
    _ ≤ volume (⋃ c ∈ Sw, Metric.ball c (Rfun c)) + volume (⋃ c ∈ Sb, Metric.ball c (Rfun c)) :=
        measure_union_le _ _
    _ ≤ coefw * (∫⁻ z in Metric.ball x₀ s, w z)
          + coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q) := add_le_add hVw hVb

/-- **Global dyadic Calderón–Zygmund cover** (helper for `gehring_goodLambda_integral`).
Run the two-sided dyadic stopping `exists_dyadic_CZ_stopping` simultaneously on the (countably
many) generation-`M` dyadic squares, applied to the localized weight `f = (ball x₀ s).indicator wᵠ`
at height `Λ = (ofReal lam)^q`.  When `2s ≤ 2^M` each generation-`M` square has area
`(2^M)² ≥ 4s² ≥ vol(ball x₀ s)` (since `4 > π`), so the ambient average of `f` over every such
square is `≤ ⨍_{ball s} wᵠ ≤ Λ`: the ambient square never stops.  The stopping cubes of the various
ambient squares assemble into a single countable, pairwise-disjoint family that a.e.-covers the
super-level set `{lam < w} ∩ ball x₀ t` (for any `t ≤ s`), with each cube nested in `ball x₀ s` and
satisfying the two-sided bound `Λ < ⨍_{Qᵢ} f ≤ 4Λ`, where the average is of the LOCALIZED `f`, so
`∫_{Qᵢ} f = ∫_{Qᵢ ∩ ball s} wᵠ ≤ ∫_{Qᵢ} wᵠ` and the lower bound forces `Qᵢ ∩ ball s ≠ ∅`. -/
private theorem gehring_dyadic_global_cover {q : ℝ} (hq0 : 0 < q) {w : ℂ → ℝ≥0∞}
    (hwmeas : AEMeasurable w volume) (x₀ : ℂ) (s : ℝ) (hs : 0 < s)
    (M : ℤ) (hM : 2 * s ≤ (2 : ℝ) ^ M)
    (lam : ℝ) (hlam : 0 < lam)
    (hlam0cond : (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q) :
    ∃ (B : Set (ℤ × (ℤ × ℤ))),
      B.Countable ∧
      (B.Pairwise (fun i j => Disjoint (dyadicSquare i.1 i.2) (dyadicSquare j.1 j.2))) ∧
      -- every cube has scale `≤ M` (so `2^{i.1} ≤ 2^M`) and meets `ball x₀ s`:
      (∀ i ∈ B, i.1 ≤ M) ∧
      (∀ i ∈ B, (dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s).Nonempty) ∧
      -- a.e.-cover of `{lam < w} ∩ ball x₀ s`:
      (volume ((Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal}) \
        ⋃ i ∈ B, dyadicSquare i.1 i.2) = 0) ∧
      -- two-sided dyadic average bounds for the localized weight:
      (∀ i ∈ B,
        (∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q)
          ≤ ENNReal.ofReal (4 * lam ^ q) * volume (dyadicSquare i.1 i.2)) ∧
      (∀ i ∈ B, (ENNReal.ofReal lam) ^ q <
        (∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q) /
          volume (dyadicSquare i.1 i.2)) := by
  classical
  -- The localized weight `f = (ball x₀ s).indicator wᵠ`.
  set Bs : Set ℂ := Metric.ball x₀ s with hBsdef
  set f : ℂ → ℝ≥0∞ := Bs.indicator (fun z => w z ^ q) with hfdef
  have hfmeas : AEMeasurable f volume := (hwmeas.pow_const q).indicator measurableSet_ball
  -- The height `Λ = ofReal(lam^q) = (ofReal lam)^q`.
  set Λ : ℝ≥0∞ := ENNReal.ofReal (lam ^ q) with hΛdef
  have hΛeq : (ENNReal.ofReal lam) ^ q = Λ := by
    rw [hΛdef, ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le]
  have hΛfin : Λ ≠ ⊤ := by rw [hΛdef]; exact ENNReal.ofReal_ne_top
  have hΛpos : 0 < Λ := by rw [hΛdef, ENNReal.ofReal_pos]; positivity
  -- Volume facts.
  have h2Mpos : (0:ℝ) < (2:ℝ) ^ M := zpow_pos (by norm_num) M
  have hvolBs : volume Bs = ENNReal.ofReal (Real.pi * s ^ 2) := by
    rw [hBsdef, Complex.volume_ball]
    have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hs.le, mul_comm]
  -- `vol(ball s) < (2^M)^2 = vol(dyadicSquare M j)` (since `4 > π` and `2s ≤ 2^M`).
  have hvolBs_lt : volume Bs < ENNReal.ofReal (((2:ℝ) ^ M) ^ 2) := by
    rw [hvolBs]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have h4s : 4 * s ^ 2 ≤ ((2:ℝ) ^ M) ^ 2 := by nlinarith [hM, hs.le, h2Mpos]
    nlinarith [Real.pi_lt_d2, hs, h4s]
  -- AMBIENT NON-STOP: for every gen-`M` index `j`, the localized average is `< Λ`.
  have hambient : ∀ j : ℤ × ℤ, (⨍⁻ z in dyadicSquare M j, f z ∂volume) < Λ := by
    intro j
    set Q : Set ℂ := dyadicSquare M j with hQdef
    have hvolQ : volume Q = ENNReal.ofReal (((2:ℝ) ^ M) ^ 2) := by
      rw [hQdef, volume_dyadicSquare]
    have hvolQ0 : volume Q ≠ 0 := by
      rw [hvolQ, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hvolQtop : volume Q ≠ ⊤ := by rw [hvolQ]; exact ENNReal.ofReal_ne_top
    -- `∫_Q f = ∫_{Q ∩ ball s} wᵠ ≤ ∫_{ball s} wᵠ`.
    have hintf : ∫⁻ z in Q, f z = ∫⁻ z in Q ∩ Bs, w z ^ q := by
      rw [hfdef, setLIntegral_indicator (measurableSet_ball), Set.inter_comm Bs Q]
    have hintf_le : ∫⁻ z in Q, f z ≤ ∫⁻ z in Bs, w z ^ q := by
      rw [hintf]; exact lintegral_mono_set Set.inter_subset_right
    -- The average over `Bs`.
    have hAvBs : ⨍⁻ z in Bs, w z ^ q ∂volume ≤ Λ := by rw [hΛeq] at hlam0cond; exact hlam0cond
    -- `∫_{Bs} wᵠ ≤ Λ · vol(Bs) < ⊤`.
    have hIfin : ∫⁻ z in Bs, w z ^ q ≠ ⊤ := by
      rw [setLAverage_eq] at hAvBs
      have hvolBstop : volume Bs ≠ ⊤ := by rw [hvolBs]; exact ENNReal.ofReal_ne_top
      have hvolBs0 : volume Bs ≠ 0 := by
        rw [hvolBs, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      have := (ENNReal.div_le_iff_le_mul (Or.inl hvolBs0) (Or.inl hvolBstop)).mp hAvBs
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hΛfin hvolBstop) this
    -- `⨍_Q f = (∫_Q f)/vol Q ≤ (∫_{Bs} wᵠ)/vol Q < (∫_{Bs} wᵠ)/vol Bs = ⨍_{Bs} wᵠ ≤ Λ`,
    -- using `vol Q > vol Bs`.  Handle `∫_{Bs} wᵠ = 0` separately.
    rw [setLAverage_eq]
    rcases eq_or_ne (∫⁻ z in Bs, w z ^ q) 0 with hI0 | hIpos
    · -- numerator `0`: average `= 0 < Λ`.
      have : ∫⁻ z in Q, f z = 0 := le_antisymm (le_trans hintf_le (le_of_eq hI0)) (zero_le _)
      rw [this, ENNReal.zero_div]; exact hΛpos
    · -- positive numerator: strict via `vol Q > vol Bs`.
      have hvolBs0 : volume Bs ≠ 0 := by
        rw [hvolBs, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      have hvolBstop : volume Bs ≠ ⊤ := by rw [hvolBs]; exact ENNReal.ofReal_ne_top
      have hvolQgtBs : volume Bs < volume Q := by rw [hvolQ]; exact hvolBs_lt
      calc (∫⁻ z in Q, f z) / volume Q
          ≤ (∫⁻ z in Bs, w z ^ q) / volume Q := ENNReal.div_le_div_right hintf_le _
        _ < (∫⁻ z in Bs, w z ^ q) / volume Bs :=
            ENNReal.div_lt_div_left hIpos hIfin hvolQgtBs
        _ = ⨍⁻ z in Bs, w z ^ q ∂volume := by rw [setLAverage_eq]
        _ ≤ Λ := hAvBs
  -- Per-ambient stopping data, chosen via `Exists.choose`.
  have hstop : ∀ j : ℤ × ℤ, ∃ (ι : Type) (B : Set ι) (n : ι → ℤ) (k : ι → ℤ × ℤ),
      B.Countable ∧
      (∀ i ∈ B, dyadicSquare (n i) (k i) ⊆ dyadicSquare M j) ∧
      (Pairwise (fun i₁ i₂ => Disjoint (dyadicSquare (n i₁) (k i₁)) (dyadicSquare (n i₂) (k i₂)))) ∧
      (volume ({z ∈ dyadicSquare M j | Λ < f z} \
        ⋃ i ∈ B, dyadicSquare (n i) (k i)) = 0) ∧
      (∀ i ∈ B, Λ < ⨍⁻ z in dyadicSquare (n i) (k i), f z ∂volume ∧
        (⨍⁻ z in dyadicSquare (n i) (k i), f z ∂volume) ≤ 4 * Λ) :=
    fun j => exists_dyadic_CZ_stopping hfmeas M j (hambient j) hΛfin
  choose ιj Bj nj kj hBjct hBjsub hBjdisj hBjcov hBjavg using hstop
  -- The cube-identifier map for ambient `j`.
  set gj : (j : ℤ × ℤ) → ιj j → ℤ × (ℤ × ℤ) := fun j i => (nj j i, kj j i) with hgjdef
  -- The combined family of cube identifiers.
  set B : Set (ℤ × (ℤ × ℤ)) := ⋃ j : ℤ × ℤ, gj j '' (Bj j) with hBdef
  -- Membership unfolding: `p ∈ B ↔ ∃ j, ∃ i ∈ Bj j, gj j i = p`.
  have hBmem : ∀ p : ℤ × (ℤ × ℤ), p ∈ B ↔ ∃ j, ∃ i ∈ Bj j, gj j i = p := by
    intro p
    simp only [hBdef, Set.mem_iUnion, Set.mem_image]
  -- For `i' ∈ Bj j`, the cube identified by `gj j i'` equals `dyadicSquare (nj j i') (kj j i')`.
  have hcubeEq : ∀ (j : ℤ × ℤ) (i : ιj j),
      dyadicSquare (gj j i).1 (gj j i).2 = dyadicSquare (nj j i) (kj j i) := fun j i => rfl
  -- The localized-integral identity `∫_{cube} f = ∫_{cube ∩ ball s} wᵠ` for any dyadic cube.
  have hfint : ∀ (m : ℤ) (idx : ℤ × ℤ),
      ∫⁻ z in dyadicSquare m idx, f z
        = ∫⁻ z in dyadicSquare m idx ∩ Bs, w z ^ q := by
    intro m idx
    rw [hfdef, setLIntegral_indicator (measurableSet_ball), Set.inter_comm Bs _]
  -- Volume positivity/finiteness of any dyadic cube.
  have hvolcube : ∀ (m : ℤ) (idx : ℤ × ℤ),
      volume (dyadicSquare m idx) ≠ 0 ∧ volume (dyadicSquare m idx) ≠ ⊤ := by
    intro m idx
    rw [volume_dyadicSquare]
    refine ⟨?_, ENNReal.ofReal_ne_top⟩
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  refine ⟨B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Countability.
    rw [hBdef]
    exact Set.countable_iUnion (fun j => (hBjct j).image _)
  · -- Pairwise disjointness on `B`.
    intro p hp p' hp' hpp'
    rw [hBmem] at hp hp'
    obtain ⟨j, i, hi, hgi⟩ := hp
    obtain ⟨j', i', hi', hgi'⟩ := hp'
    -- The cubes.
    have hcp : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    have hcp' : dyadicSquare p'.1 p'.2 = dyadicSquare (nj j' i') (kj j' i') := by rw [← hgi']
    rw [hcp, hcp']
    by_cases hjj : j = j'
    · -- Same ambient: use per-ambient pairwise disjointness; `i ≠ i'`.
      subst hjj
      have hii : i ≠ i' := by
        rintro rfl
        exact hpp' (by rw [← hgi, ← hgi'])
      exact hBjdisj j hii
    · -- Different ambients: cubes nested in disjoint gen-`M` squares.
      have hsub1 : dyadicSquare (nj j i) (kj j i) ⊆ dyadicSquare M j := hBjsub j i hi
      have hsub2 : dyadicSquare (nj j' i') (kj j' i') ⊆ dyadicSquare M j' := hBjsub j' i' hi'
      have hQdisj : Disjoint (dyadicSquare M j) (dyadicSquare M j') :=
        dyadicSquare_pairwise_disjoint M hjj
      exact hQdisj.mono hsub1 hsub2
  · -- Scale bound `i.1 ≤ M`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hsub : dyadicSquare (nj j i) (kj j i) ⊆ dyadicSquare M j := hBjsub j i hi
    have hp1 : p.1 = nj j i := by rw [← hgi, hgjdef]
    rw [hp1]
    -- volume monotonicity ⟹ `(2^{nj})² ≤ (2^M)²` ⟹ `nj ≤ M`.
    have hvmono : volume (dyadicSquare (nj j i) (kj j i)) ≤ volume (dyadicSquare M j) :=
      measure_mono hsub
    rw [volume_dyadicSquare, volume_dyadicSquare,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvmono
    have h2n : (0:ℝ) < (2:ℝ) ^ (nj j i) := zpow_pos (by norm_num) _
    have h2M : (0:ℝ) < (2:ℝ) ^ M := zpow_pos (by norm_num) _
    have hle : (2:ℝ) ^ (nj j i) ≤ (2:ℝ) ^ M := by nlinarith [hvmono, h2n, h2M]
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hle
  · -- Nonempty intersection with `ball s`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hp12 : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    rw [hp12]
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    -- `f = 0` on the cube ⟹ `⨍ f = 0`, contradicting `Λ < ⨍ f`.
    have havg := (hBjavg j i hi).1
    have hf0 : ∫⁻ z in dyadicSquare (nj j i) (kj j i), f z = 0 := by
      rw [hfint, hempty]; simp
    rw [setLAverage_eq, hf0, ENNReal.zero_div] at havg
    exact absurd havg (not_lt.mpr (zero_le _))
  · -- a.e.-cover of `{lam < w.toReal} ∩ ball s`.
    have hbad_sub : (Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal}) \
        ⋃ i ∈ B, dyadicSquare i.1 i.2
        ⊆ ⋃ j : ℤ × ℤ, ({z ∈ dyadicSquare M j | Λ < f z} \
            ⋃ i ∈ Bj j, dyadicSquare (nj j i) (kj j i)) := by
      rintro z ⟨⟨hzs, hzlam⟩, hznotcov⟩
      simp only [Set.mem_setOf_eq] at hzlam
      -- `z` lies in its gen-`M` ambient square.
      set j₀ : ℤ × ℤ := dyadicIndexAt M z with hj₀
      have hzj₀ : z ∈ dyadicSquare M j₀ := mem_dyadicSquare_dyadicIndexAt M z
      -- `f z > Λ`.
      have hwfin : w z ≠ ⊤ := by
        intro htop; rw [htop, ENNReal.toReal_top] at hzlam; linarith
      have hfz : f z = w z ^ q := by
        rw [hfdef, Set.indicator_of_mem (by rw [hBsdef]; exact hzs)]
      have hΛlt : Λ < f z := by
        rw [hfz, hΛdef, ← ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le]
        apply ENNReal.rpow_lt_rpow _ hq0
        rw [← ENNReal.ofReal_toReal hwfin]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le |>.mpr hzlam
      refine Set.mem_iUnion.mpr ⟨j₀, ⟨hzj₀, hΛlt⟩, ?_⟩
      -- `z` not covered by `Bj j₀` cubes (else it would be in `⋃ B`).
      intro hzcov
      apply hznotcov
      rw [Set.mem_iUnion₂] at hzcov ⊢
      obtain ⟨i, hi, hzi⟩ := hzcov
      refine ⟨gj j₀ i, (hBmem _).mpr ⟨j₀, i, hi, rfl⟩, ?_⟩
      rw [hcubeEq j₀ i]; exact hzi
    refine measure_mono_null hbad_sub ?_
    rw [measure_iUnion_null_iff]
    exact fun j => hBjcov j
  · -- Upper average bound: `∫_{cube ∩ ball s} wᵠ ≤ ofReal(4 lam^q) · vol(cube)`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hp12 : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    rw [hp12]
    have havg := (hBjavg j i hi).2
    rw [setLAverage_eq, hfint] at havg
    obtain ⟨hv0, hvtop⟩ := hvolcube (nj j i) (kj j i)
    rw [ENNReal.div_le_iff_le_mul (Or.inl hv0) (Or.inl hvtop)] at havg
    refine le_trans havg ?_
    rw [show (4 : ℝ≥0∞) * Λ = ENNReal.ofReal (4 * lam ^ q) by
      rw [hΛdef, show (4:ℝ≥0∞) = ENNReal.ofReal 4 by rw [ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by norm_num)]]
  · -- Lower average bound: `(ofReal lam)^q < ∫_{cube ∩ ball s} wᵠ / vol(cube)`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hp12 : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    rw [hp12]
    have havg := (hBjavg j i hi).1
    rw [setLAverage_eq, hfint] at havg
    rw [hΛeq]; exact havg

/-- **Indexed Carleson covering bound** (helper for `gehring_goodLambda_integral`).  The
cube-identifier-indexed analogue of `gehring_engine_bound`: a countable family of balls
`ball (c i) (r i)` (`i ∈ 𝓑`), each with the per-ball averaging property
`l·vol ≤ ∫ u`, has `l·vol(⋃) ≤ 16·∫⁻ u` (planar doubling `A_dbl = 4`, `A_dbl² = 16`). -/
private theorem gehring_engine_idx {ι : Type} (𝓑 : Set ι) (hct : 𝓑.Countable)
    (c : ι → ℂ) (r : ι → ℝ) (l : ℝ≥0∞) (u : ℂ → ℝ≥0∞) (Rbd : ℝ)
    (hRbd : ∀ i ∈ 𝓑, r i ≤ Rbd)
    (h2u : ∀ i ∈ 𝓑, l * volume (Metric.ball (c i) (r i)) ≤ ∫⁻ z in Metric.ball (c i) (r i), u z) :
    l * volume (⋃ i ∈ 𝓑, Metric.ball (c i) (r i)) ≤ (16 : ℝ≥0∞) * ∫⁻ z, u z := by
  haveI hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  have hengine := hct.measure_biUnion_le_lintegral (μ := (volume : Measure ℂ))
    (A := 2 ^ Module.finrank ℝ ℂ) (c := c) (r := r) l u Rbd hRbd h2u
  have hA2 : ((2 ^ Module.finrank ℝ ℂ : ℝ≥0) : ℝ≥0∞) ^ 2 = (16 : ℝ≥0∞) := by
    rw [Complex.finrank_real_complex]; norm_num
  simpa only [hA2] using hengine

/-- **Honest exponent-1 good-λ in INTEGRAL (`w^q`-mass) form, on the HIGH range `λ ≥ λ₀`** — the
analytic core of STEP B of `gehring_selfImprovement`.
For concentric radii `4R₀ ≤ t < s ≤ 16R₀` and a height `lam > 0` on the HIGH range characterized by
`⨍⁻_{ball s} wᵠ ≤ (ofReal lam)^q` (i.e. `lam ≥ λ₀ := (⨍_{ball s} wᵠ)^{1/q}`), the FULL
(a-priori-integrable) `w^q`-mass over the super-level set `{w > lam} ∩ ball t` is controlled by the
`lam^{q-1}`-weighted FULL `w`-mass (exponent ONE) over the SUPER-LEVEL set `{w > β·lam} ∩ ball s`,
plus a super-level `bᵠ`-forcing:
`∫_{ball t ∩ {lam < w}} wᵠ  ≤  Cw·lam^{q-1}·∫_{ball s ∩ {β·lam < w}} w`
`  + Cb·∫_{ball s ∩ {β·lam < b}} bᵠ`
with (here) `β = 1/2`, `Cw = 4(2·π^{1/q}·A)ᵠ`, `Cb = 256(2·π^{1/q}·(A+1))ᵠ`.

The THRESHOLD-RESTRICTED hypothesis `hlam0cond` is what makes the statement hold: it is the
Giaquinta–Modica threshold split, consumed downstream in `gehring_assembly`/`gehring_holeFill`
ONLY on the high range `λ ≥ λ₀`, while `0 < λ < λ₀` is handled there by the trivial
`∫_{ball t ∩ {λ<w}} wᵠ ≤ ∫_{16B₀} wᵠ` bound folded into the `C₁·Wmaster/(s-t)²` collar.
The proof is the classical Calderón–Zygmund stopping-time / reverse-Hölder dichotomy core:
two-sided stopping of `g := 1_{ball s}·wᵠ` at height `lamᵠ`
(`exists_dyadic_CZ_stopping`: cubes `Qᵢ ⊆ Q` with `lamᵠ < ⨍_{Qᵢ}g ≤ 4lamᵠ`, the `≤ 4lamᵠ` from
doubling against the non-stopping parent; `λ ≥ λ₀` is what makes
`⨍_Q g ≤ ⨍_{ball s}wᵠ ≤ lamᵠ` so the ambient does not stop) bounding the LHS by `Σ 4lamᵠ·vol(Qᵢ)`;
per-cube reverse-Hölder dichotomy `dyadic_reverseHolder'` into `w`-good / `b`-good cubes
(`⨍_{Eᵢ}w > γ·lam` or `⨍_{Eᵢ}bᵠ > (γlam)ᵠ`, `γ = 1/(2π^{1/q}A)`, `Eᵢ = ball(centre,4·2^{mᵢ})`);
super-level concentration (`β < γ`: `∫_{Eᵢ}w ≤ βlam·vol(Eᵢ) + ∫_{Eᵢ∩{w>βλ}}w` ⟹
`lam·vol(Eᵢ) ≤ (γ-β)⁻¹∫_{Eᵢ∩{w>βλ}}w`); and the Carleson sum via `gehring_engine_bound` on
`u := 1_{ball s ∩ {w>βλ}}·w`.  The boundary-collar term handles the geometric capping
`Eᵢ ⊆ ball s` (the `4×` enlargement of the at-most-`vol(ball s)`-sized stopping cubes need not, in
general, fit inside `ball s`), via the metric capped covering shared with the companion
super-level MEASURE bound `gehring_goodLambda_measure`. -/
private theorem gehring_goodLambda_integral_core {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (x₀ : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hWfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (hBfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q < ⊤)
    (t s : ℝ) (ht : 4 * R₀ ≤ t) (hts : t < s) (hs : s ≤ 16 * R₀)
    (lam : ℝ) (hlam : 0 < lam)
    (hlam0cond : (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q) :
    ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (w z).toReal}, w z ^ q
      ≤ ENNReal.ofReal (256 * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1))
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (w z).toReal}, w z)
        + ENNReal.ofReal (64 * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q)
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (b z).toReal}, b z ^ q)
        -- BOUNDARY COLLAR: the contribution of the (few, large) stopping cubes whose `4×`
        -- enlargement spills outside `ball x₀ s`; bounded by `4·lamᵠ·vol(ball s)`.  This term
        -- vanishes for `lam` above the structural threshold `λ₁` (any boundary cube would force
        -- `lamᵠ·((s-t)/10)² < ∫_{ball s}wᵠ ≤ Wmaster`), making its λ-integral finite; the
        -- consumer integrates this good-λ on `(λ₀, λ₁)` and uses the collar-free form above.
        + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) := by
  classical
  have hq0 : 0 < q := lt_trans one_pos hq
  have hst : 0 < s - t := by linarith
  have hspos : 0 < s := by linarith
  -- Planar doubling instance for the Carleson engine.
  haveI hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  -- Abbreviation `Ã = π^{1/q}·A + 1 > 0` (the reverse-Hölder constant, padded by 1).
  set P : ℝ := Real.pi ^ (1 / q) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  set Ã : ℝ := P * A + 1 with hÃdef
  have hÃpos : 0 < Ã := by rw [hÃdef]; nlinarith [hPpos, hA]
  -- The collar/level constants: `β = 1/(4Ã)`, w-level `lw = ofReal(βlam)`,
  -- b-level `lb = ofReal((βlam)^q)`.
  set β : ℝ := 1 / (4 * Ã) with hβdef
  have hβpos : 0 < β := by rw [hβdef]; positivity
  set lw : ℝ≥0∞ := ENNReal.ofReal (β * lam) with hlwdef
  set lb : ℝ≥0∞ := ENNReal.ofReal ((β * lam) ^ q) with hlbdef
  -- Choose `M` minimal-ish with `2s ≤ 2^M` (any large enough `M` works for the cover).
  obtain ⟨M, hM⟩ : ∃ M : ℤ, 2 * s ≤ (2 : ℝ) ^ M := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * s) (by norm_num : (1:ℝ) < 2)
    exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hn.le⟩
  -- Run the global dyadic cover.
  obtain ⟨B, hBct, hBdisj, hBscale, hBmeet, hBcov, hBup, hBlow⟩ :=
    gehring_dyadic_global_cover hq0 hwmeas x₀ s hspos M hM lam hlam hlam0cond
  -- Geometry of a cube `i ∈ B`: centre, scale, enlarged ball `Eᵢ = ball cᵢ (4·2^{nᵢ})`.
  set cI : ℤ × (ℤ × ℤ) → ℂ := fun i => dyadicCenter i.1 i.2 with hcIdef
  set ρI : ℤ × (ℤ × ℤ) → ℝ := fun i => (2 : ℝ) ^ i.1 with hρIdef
  have hρIpos : ∀ i, 0 < ρI i := fun i => by rw [hρIdef]; exact zpow_pos (by norm_num) _
  -- The cube is inside its circumscribed ball `ball cᵢ (2^{nᵢ})`.
  have hQsubball : ∀ i, dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (ρI i) := by
    intro i; rw [hcIdef, hρIdef]; exact dyadicSquare_subset_ball i.1 i.2
  -- ============================================================================
  -- PER-CUBE REVERSE-HÖLDER DICHOTOMY (super-level concentrated).
  -- For `i ∈ B`: either `w`-good (`lw·vol(Eᵢ) ≤ ∫_{Eᵢ∩{w>βλ}} w`) or `b`-good
  -- (`lb·vol(Eᵢ) ≤ ∫_{Eᵢ∩{b>βλ}} bᵠ`), where `Eᵢ = ball cᵢ (4ρᵢ)`.
  -- ============================================================================
  set Esub : Set ℂ := {z : ℂ | β * lam < (w z).toReal} with hEsubdef
  set Fsub : Set ℂ := {z : ℂ | β * lam < (b z).toReal} with hFsubdef
  -- Full (un-restricted) reverse-Hölder levels `lwf = lam/(2Ã)`, `lbf = (lam/(2Ã))^q`.
  set lwf : ℝ≥0∞ := ENNReal.ofReal (lam / (2 * Ã)) with hlwfdef
  set lbf : ℝ≥0∞ := ENNReal.ofReal ((lam / (2 * Ã)) ^ q) with hlbfdef
  have hdich : ∀ i ∈ B,
      (lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z) ∨
      (lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q) := by
    intro i hi
    -- `lam < (⨍_{Qᵢ} wᵠ)^{1/q}`.
    have hQpos : 0 < volume (dyadicSquare i.1 i.2) := by
      rw [volume_dyadicSquare, ENNReal.ofReal_pos]; positivity
    have hQtop : volume (dyadicSquare i.1 i.2) ≠ ⊤ := by
      rw [volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
    have hlowfull : (ENNReal.ofReal lam) ^ q < ⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume := by
      refine lt_of_lt_of_le (hBlow i hi) ?_
      rw [setLAverage_eq]
      exact ENNReal.div_le_div_right (lintegral_mono_set Set.inter_subset_left) _
    have h1q : (0:ℝ) < 1 / q := by positivity
    have hroot : ENNReal.ofReal lam <
        (⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume) ^ (1 / q) := by
      have h := ENNReal.rpow_lt_rpow hlowfull h1q
      have hid : (ENNReal.ofReal lam ^ q) ^ (1 / q) = ENNReal.ofReal lam := by
        rw [one_div, ENNReal.rpow_rpow_inv hq0.ne']
      rwa [hid] at h
    -- Reverse-Hölder on the cube, with constant `P·A ≤ Ã`.
    have hRHc := dyadic_reverseHolder' hq hA hRH i.1 i.2
    have hPA_le : ENNReal.ofReal (P * A) ≤ ENNReal.ofReal Ã :=
      ENNReal.ofReal_le_ofReal (by rw [hÃdef, hPdef]; nlinarith [hPpos, hA])
    have hRHc' : ENNReal.ofReal lam <
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã *
            (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
      have hceq : Metric.ball (dyadicCenter i.1 i.2) (4 * (2:ℝ) ^ i.1)
          = Metric.ball (cI i) (4 * ρI i) := by rw [hcIdef, hρIdef]
      rw [hceq] at hRHc
      refine lt_of_lt_of_le hroot (le_trans hRHc (add_le_add ?_ ?_)) <;>
        exact mul_le_mul_left hPA_le _
    -- One of the two terms is `≥ ofReal lam / 2`.
    have hvol4_pos : 0 < volume (Metric.ball (cI i) (4 * ρI i)) :=
      Metric.measure_ball_pos _ _ (by positivity [hρIpos i])
    have hvol4_ne : volume (Metric.ball (cI i) (4 * ρI i)) ≠ 0 := hvol4_pos.ne'
    have hvol4_top : volume (Metric.ball (cI i) (4 * ρI i)) ≠ ⊤ := measure_ball_lt_top.ne
    have hÃne : ENNReal.ofReal Ã ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hÃpos
    have hÃtop : ENNReal.ofReal Ã ≠ ⊤ := ENNReal.ofReal_ne_top
    have hhalf : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume)
          ≥ ENNReal.ofReal lam / 2 ∨
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          ≥ ENNReal.ofReal lam / 2 := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [not_le] at h1 h2
      have hsum2 : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          < ENNReal.ofReal lam / 2 + ENNReal.ofReal lam / 2 := ENNReal.add_lt_add h1 h2
      rw [ENNReal.add_halves] at hsum2
      exact absurd (lt_trans hRHc' hsum2) (lt_irrefl _)
    -- `lwf · ofReal Ã = ofReal lam / 2`.
    have hlwf_mul : lwf * ENNReal.ofReal Ã = ENNReal.ofReal lam / 2 := by
      rw [hlwfdef, ← ENNReal.ofReal_mul (by positivity)]
      have hreal : lam / (2 * Ã) * Ã = lam / 2 := by field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1; norm_num
    rcases hhalf with hw | hb
    · left
      have hge : lwf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hw
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      rw [setLAverage_eq] at hge
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hge
    · right
      have hlbf_eq : lbf = lwf ^ q := by
        rw [hlbfdef, hlwfdef, ← ENNReal.ofReal_rpow_of_pos (by positivity)]
      have hgew : lwf ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
                * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hb
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      have hgeq : lbf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume := by
        rw [hlbf_eq]
        have hpow := ENNReal.rpow_le_rpow hgew hq0.le
        rwa [one_div, ENNReal.rpow_inv_rpow hq0.ne'] at hpow
      rw [setLAverage_eq] at hgeq
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hgeq
  -- ============================================================================
  -- SETUP for the assembly: containments, a.e. finiteness, the inner predicate.
  -- ============================================================================
  have hssub16 : Metric.ball x₀ s ⊆ Metric.ball x₀ (16 * R₀) :=
    Metric.ball_subset_ball (by linarith)
  -- `w < ⊤` a.e. on `ball s`.
  have hwfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), w z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ^ q ≠ ⊤ :=
      ae_lt_top' (hwmeas.pow_const q).restrict hWfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- `b < ⊤` a.e. on `ball s`.
  have hbfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), b z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ^ q ≠ ⊤ :=
      ae_lt_top' (hbmeas.pow_const q).restrict hBfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- The inner predicate: the enlargement `Eᵢ ⊆ ball x₀ s` (engine-able cubes).
  set Inn : Set (ℤ × (ℤ × ℤ)) :=
    {i ∈ B | Metric.ball (cI i) (4 * ρI i) ⊆ Metric.ball x₀ s} with hInndef
  -- The w-good and b-good inner subfamilies.
  set Sw : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z} with hSwdef
  set Sb : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q} with hSbdef
  have hSwsub : Sw ⊆ B := fun i hi => hi.1.1
  have hSbsub : Sb ⊆ B := fun i hi => hi.1.1
  have hSwct : Sw.Countable := hBct.mono hSwsub
  have hSbct : Sb.Countable := hBct.mono hSbsub
  -- The localized `u`-weights.
  set uw : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Esub).indicator w with huwdef
  set ub : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Fsub).indicator (fun z => b z ^ q) with hubdef
  -- ============================================================================
  -- PER-CUBE ENGINE HYPOTHESES (super-level concentration on inner cubes).
  -- ============================================================================
  have hEsub_nm : NullMeasurableSet Esub volume :=
    nullMeasurableSet_lt aemeasurable_const hwmeas.ennreal_toReal
  have hFsub_nm : NullMeasurableSet Fsub volume :=
    nullMeasurableSet_lt aemeasurable_const hbmeas.ennreal_toReal
  -- w-good inner: `lw·vol(Eᵢ) ≤ ∫_{Eᵢ} uw`.
  have h2uw : ∀ i ∈ Sw, lw * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), uw z := by
    rintro i ⟨⟨hiB, hEsub⟩, hwg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    -- `∫_E uw = ∫_{E ∩ Esub} w` (since `E ⊆ ball s`).
    have huwint : ∫⁻ z in E, uw z = ∫⁻ z in E ∩ Esub, w z := by
      have hpt : ∀ z ∈ E, uw z = Esub.indicator w z := by
        intro z hz
        rw [huwdef]
        by_cases hzE : z ∈ Esub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Esub := ⟨hEsubs hz, hzE⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzE]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Esub := fun h => hzE h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzE]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hEsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Pointwise a.e. on `E`: `w z ≤ Esub.indicator w z + ofReal(βlam)`.
    have hconc : ∫⁻ z in E, w z
        ≤ (∫⁻ z in E, Esub.indicator w z) + ENNReal.ofReal (β * lam) * volume E := by
      have hstep : ∫⁻ z in E, w z
          ≤ ∫⁻ z in E, (Esub.indicator w z + ENNReal.ofReal (β * lam)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), w z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hwfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzE : z ∈ Esub
        · rw [Set.indicator_of_mem hzE]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzE, zero_add]
          rw [hEsubdef, Set.mem_setOf_eq, not_lt] at hzE
          rw [← ENNReal.ofReal_toReal hzfin]
          exact ENNReal.ofReal_le_ofReal hzE
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Esub.indicator w z = ∫⁻ z in E ∩ Esub, w z := by
      rw [setLIntegral_indicator₀ _ (hEsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- Combine: `lwf·vol(E) ≤ ∫_E w`, and `lwf = lw + ofReal(βlam)`.
    have hlw_eq : lw + ENNReal.ofReal (β * lam) = lwf := by
      rw [hlwdef, hlwfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hβdef]; field_simp; ring
    rw [huwint]
    have hkey : lwf * volume E
        ≤ (∫⁻ z in E ∩ Esub, w z) + ENNReal.ofReal (β * lam) * volume E := le_trans hwg hconc
    rw [← hlw_eq, add_mul] at hkey
    refine ENNReal.le_of_add_le_add_right ?_ hkey
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- b-good inner: `lb·vol(Eᵢ) ≤ ∫_{Eᵢ} ub`.
  have h2ub : ∀ i ∈ Sb, lb * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), ub z := by
    rintro i ⟨⟨hiB, hEsub⟩, hbg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    have hubint : ∫⁻ z in E, ub z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      have hpt : ∀ z ∈ E, ub z = Fsub.indicator (fun z => b z ^ q) z := by
        intro z hz
        rw [hubdef]
        by_cases hzF : z ∈ Fsub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Fsub := ⟨hEsubs hz, hzF⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzF]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Fsub := fun h => hzF h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzF]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hFsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Super-level concentration: `bᵠ z ≤ Fsub.indicator bᵠ z + ofReal((βlam)^q)` a.e. on `E`.
    have hconc : ∫⁻ z in E, b z ^ q
        ≤ (∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z)
          + ENNReal.ofReal ((β * lam) ^ q) * volume E := by
      have hstep : ∫⁻ z in E, b z ^ q
          ≤ ∫⁻ z in E, (Fsub.indicator (fun z => b z ^ q) z + ENNReal.ofReal ((β * lam) ^ q)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), b z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hbfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzF : z ∈ Fsub
        · rw [Set.indicator_of_mem hzF]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzF, zero_add]
          rw [hFsubdef, Set.mem_setOf_eq, not_lt] at hzF
          rw [← ENNReal.ofReal_toReal hzfin,
            ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0.le]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ENNReal.toReal_nonneg hzF hq0.le)
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      rw [setLIntegral_indicator₀ _ (hFsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- `lb + ofReal((βlam)^q) ≤ lbf` (since `2 ≤ 2^q`).
    have hlb_le : lb + ENNReal.ofReal ((β * lam) ^ q) ≤ lbf := by
      rw [hlbdef, hlbfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h2q : (2:ℝ) ≤ 2 ^ q := by
        calc (2:ℝ) = 2 ^ (1:ℝ) := by rw [Real.rpow_one]
          _ ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hq)
      have hβl : (0:ℝ) ≤ β * lam := by positivity
      have hkey : 2 * (β * lam) ^ q ≤ (lam / (2 * Ã)) ^ q := by
        have heq : lam / (2 * Ã) = 2 * (β * lam) := by rw [hβdef]; field_simp; ring
        rw [heq, Real.mul_rpow (by norm_num) hβl]
        nlinarith [Real.rpow_nonneg hβl q, h2q]
      linarith [hkey]
    rw [hubint]
    have hkey : lbf * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans hbg hconc
    have hlbstep : (lb + ENNReal.ofReal ((β * lam) ^ q)) * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans (mul_le_mul_left hlb_le _) hkey
    rw [add_mul] at hlbstep
    refine ENNReal.le_of_add_le_add_right ?_ hlbstep
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- ============================================================================
  -- ENGINE CALLS: bound `vol(⋃_{Sw} Eᵢ)`, `vol(⋃_{Sb} Eᵢ)` by super-level integrals.
  -- ============================================================================
  -- Radius bound: for inner cubes, `4·ρI i ≤ s` (since `Eᵢ ⊆ ball x₀ s`).
  have hRbd : ∀ i ∈ Inn, 4 * ρI i ≤ s := by
    rintro i ⟨hiB, hEsub⟩
    by_contra hgt
    push Not at hgt
    have hvle : volume (Metric.ball (cI i) (4 * ρI i)) ≤ volume (Metric.ball x₀ s) :=
      measure_mono hEsub
    rw [Complex.volume_ball, Complex.volume_ball] at hvle
    have h4ρpos : 0 < 4 * ρI i := by have := hρIpos i; linarith
    rw [ENNReal.mul_le_mul_iff_left (by simp [NNReal.pi_pos.ne']) (by simp)] at hvle
    rw [← ENNReal.ofReal_pow h4ρpos.le, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ s),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvle
    nlinarith [hvle, hgt, h4ρpos]
  have hRbdSw : ∀ i ∈ Sw, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hRbdSb : ∀ i ∈ Sb, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hEw := gehring_engine_idx Sw hSwct cI (fun i => 4 * ρI i) lw uw s hRbdSw h2uw
  have hEb := gehring_engine_idx Sb hSbct cI (fun i => 4 * ρI i) lb ub s hRbdSb h2ub
  -- The global integrals of `uw`, `ub` are the super-level masses over `ball x₀ s`.
  have hIuw : ∫⁻ z, uw z = ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    rw [huwdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hEsub_nm)]
  have hIub : ∫⁻ z, ub z = ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    rw [hubdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hFsub_nm)]
  rw [hIuw] at hEw
  rw [hIub] at hEb
  -- ============================================================================
  -- LHS BOUND and FINAL ASSEMBLY.
  -- ============================================================================
  set S : Set ℂ := Metric.ball x₀ t ∩ {z : ℂ | lam < (w z).toReal} with hSdef
  have htsub : Metric.ball x₀ t ⊆ Metric.ball x₀ s := Metric.ball_subset_ball hts.le
  -- The cube sets `Cᵢ := Qᵢ ∩ ball s` are measurable and pairwise disjoint on `B`.
  set Cset : ℤ × (ℤ × ℤ) → Set ℂ := fun i => dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s with hCsetdef
  have hCmeas : ∀ i, MeasurableSet (Cset i) :=
    fun i => (measurableSet_dyadicSquare _ _).inter measurableSet_ball
  have hCdisj : B.PairwiseDisjoint Cset := by
    intro i hi j hj hij
    exact (hBdisj hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  -- `S` is a.e. covered by `⋃_{i∈B} Cset i`.
  have hScov : volume (S \ ⋃ i ∈ B, Cset i) = 0 := by
    refine measure_mono_null ?_ hBcov
    intro z hz
    obtain ⟨hzS, hznotcov⟩ := hz
    have hzs : z ∈ Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal} :=
      ⟨htsub hzS.1, hzS.2⟩
    refine ⟨hzs, ?_⟩
    intro hzcov
    apply hznotcov
    rw [Set.mem_iUnion₂] at hzcov ⊢
    obtain ⟨i, hi, hzi⟩ := hzcov
    exact ⟨i, hi, hzi, hzs.1⟩
  -- `∫_S wᵠ ≤ ∫_{⋃_{i∈B} Cset i} wᵠ`.
  set U : Set ℂ := ⋃ i ∈ B, Cset i with hUdef
  have hLHS1 : ∫⁻ z in S, w z ^ q ≤ ∫⁻ z in U, w z ^ q := by
    have h1 : (S \ (S \ U) : Set ℂ) =ᵐ[volume] S := diff_null_ae_eq_self hScov
    have h2 : S \ (S \ U) = S ∩ U := Set.diff_diff_right_self S U
    rw [h2] at h1
    rw [setLIntegral_congr h1.symm]
    exact lintegral_mono_set Set.inter_subset_right
  -- Split `⋃_{i∈B} Cset = (⋃_{Inn}) ∪ (⋃_{B\Inn})`, a disjoint union.
  have hInnsubB : Inn ⊆ B := fun i hi => hi.1
  have hUsplit : (⋃ i ∈ B, Cset i)
      = (⋃ i ∈ Inn, Cset i) ∪ (⋃ i ∈ B \ Inn, Cset i) := by
    rw [← Set.biUnion_union]
    congr 1
    rw [Set.union_diff_cancel hInnsubB]
  have hUdisj : Disjoint (⋃ i ∈ Inn, Cset i) (⋃ i ∈ B \ Inn, Cset i) := by
    rw [Set.disjoint_iff_forall_ne]
    rintro x hx y hy rfl
    rw [Set.mem_iUnion₂] at hx hy
    obtain ⟨i, hiI, hxi⟩ := hx
    obtain ⟨j, ⟨hjB, hjnI⟩, hxj⟩ := hy
    have hij : i ≠ j := fun h => hjnI (h ▸ hiI)
    exact (hCdisj (hInnsubB hiI) hjB hij).le_bot ⟨hxi, hxj⟩ |>.elim
  have hUmeasBd : MeasurableSet (⋃ i ∈ B \ Inn, Cset i) := by
    apply MeasurableSet.biUnion (hBct.mono (Set.diff_subset))
    exact fun i _ => hCmeas i
  -- `∫_{⋃_B} = ∫_{⋃_Inn} + ∫_{⋃_{B\Inn}}`.
  have hLHS2 : ∫⁻ z in ⋃ i ∈ B, Cset i, w z ^ q
      = (∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q) + ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q := by
    rw [hUsplit, lintegral_union hUmeasBd hUdisj]
  -- BOUNDARY BOUND: `∫_{⋃_{B\Inn} Cset} wᵠ ≤ ofReal(lamᵠ)·vol(ball s)`.
  have hUbdsubs : (⋃ i ∈ B \ Inn, Cset i) ⊆ Metric.ball x₀ s := by
    apply Set.iUnion₂_subset
    exact fun i _ => Set.inter_subset_right
  have hBoundary : ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q
      ≤ ENNReal.ofReal (lam ^ q) * volume (Metric.ball x₀ s) := by
    calc ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q
        ≤ ∫⁻ z in Metric.ball x₀ s, w z ^ q := lintegral_mono_set hUbdsubs
      _ ≤ ENNReal.ofReal (lam ^ q) * volume (Metric.ball x₀ s) := by
          have hav := hlam0cond
          rw [setLAverage_eq, ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le] at hav
          have hvol_ne : volume (Metric.ball x₀ s) ≠ 0 := (Metric.measure_ball_pos _ _ hspos).ne'
          have hvol_top : volume (Metric.ball x₀ s) ≠ ⊤ := measure_ball_lt_top.ne
          exact (ENNReal.div_le_iff_le_mul (Or.inl hvol_ne) (Or.inl hvol_top)).mp hav
  -- INNER BOUND: `∫_{⋃_{Inn} Cset} wᵠ ≤ ofReal(4lamᵠ)·(vol(⋃_{Sw}Eᵢ) + vol(⋃_{Sb}Eᵢ))`.
  -- Step (a): `∫_{⋃_{Inn} Cset} wᵠ = Σ_{i:Inn} ∫_{Cset i} wᵠ ≤ ofReal(4lamᵠ)·vol(⋃_{Inn} Qᵢ)`.
  have hInnct : Inn.Countable := hBct.mono hInnsubB
  have hInnerSum : ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q
      ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
    rw [lintegral_biUnion hInnct (fun i _ => hCmeas i)
      (hCdisj.subset hInnsubB)]
    calc ∑' i : Inn, ∫⁻ z in Cset i, w z ^ q
        ≤ ∑' i : Inn, ENNReal.ofReal (4 * lam ^ q)
            * volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) := by
          apply ENNReal.tsum_le_tsum
          rintro ⟨i, hi⟩
          exact hBup i (hInnsubB hi)
      _ = ENNReal.ofReal (4 * lam ^ q)
            * ∑' i : Inn, volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
          rw [measure_biUnion hInnct (Set.Pairwise.mono hInnsubB hBdisj)
            (fun i _ => measurableSet_dyadicSquare _ _)]
  -- Step (b): `vol(⋃_{Inn} Qᵢ) ≤ vol(⋃_{Sw} Eᵢ) + vol(⋃_{Sb} Eᵢ)`.
  have hQcover : (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ⊆ (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        ∪ (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
    apply Set.iUnion₂_subset
    intro i hi
    have hiB : i ∈ B := hInnsubB hi
    have hQE : dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (4 * ρI i) := by
      refine (hQsubball i).trans (Metric.ball_subset_ball ?_)
      have := hρIpos i; linarith
    rcases hdich i hiB with hw | hb
    · have hiSw : i ∈ Sw := ⟨hi, hw⟩
      exact hQE.trans (Set.subset_union_of_subset_left
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSw) _)
    · have hiSb : i ∈ Sb := ⟨hi, hb⟩
      exact hQE.trans (Set.subset_union_of_subset_right
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSb) _)
  have hQvol : volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ≤ volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) :=
    le_trans (measure_mono hQcover) (measure_union_le _ _)
  -- ============================================================================
  -- COEFFICIENT TRANSFER.  `ofReal(4lamᵠ)·vol(⋃_{Sw}Eᵢ) ≤ ofReal(Cw)·∫_{ball s∩Esub}w`,
  -- and similarly for `Sb`.
  -- ============================================================================
  set Cw : ℝ := 256 * Ã * lam ^ (q - 1) with hCwdef
  set Cb : ℝ := 64 * (4 * Ã) ^ q with hCbdef
  have hlw_ne : lw ≠ 0 := by rw [hlwdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlb_ne : lb ≠ 0 := by rw [hlbdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlw_top : lw ≠ ⊤ := by rw [hlwdef]; exact ENNReal.ofReal_ne_top
  have hlb_top : lb ≠ ⊤ := by rw [hlbdef]; exact ENNReal.ofReal_ne_top
  -- Real identity: `lam^{q-1}·lam = lam^q`.
  have hlamq : lam ^ (q - 1) * lam = lam ^ q := by
    have h := (Real.rpow_add hlam (q - 1) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; congr 1; ring
  -- `ofReal Cw · lw = 16 · ofReal(4lamᵠ)`.
  have hCw_mul : ENNReal.ofReal Cw * lw = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCwdef, hlwdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hβdef]
    have : 256 * Ã * lam ^ (q - 1) * (1 / (4 * Ã) * lam) = 64 * (lam ^ (q - 1) * lam) := by
      field_simp; ring
    rw [this, hlamq]; ring
  -- `ofReal Cb · lb = 16 · ofReal(4lamᵠ)`.
  have hCb_mul : ENNReal.ofReal Cb * lb = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCbdef, hlbdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    -- `64·(4Ã)^q·(βlam)^q = 64·lamᵠ`, since `(4Ã)^q·(βlam)^q = (4Ã·βlam)^q = lamᵠ`.
    have hbase : (4 * Ã) * (β * lam) = lam := by rw [hβdef]; field_simp
    have hmr : (4 * Ã) ^ q * (β * lam) ^ q = lam ^ q := by
      rw [← Real.mul_rpow (by positivity) (by positivity [hβpos]), hbase]
    rw [show (64 * (4 * Ã) ^ q * (β * lam) ^ q : ℝ) = 64 * ((4 * Ã) ^ q * (β * lam) ^ q) by ring,
      hmr]; ring
  -- Transfer the engine bounds to coefficient form.
  have hsixteen_ne : (16 : ℝ≥0∞) ≠ 0 := by norm_num
  have hsixteen_top : (16 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hTransW : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cw * lw) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCw_mul]; ring
      _ = ENNReal.ofReal Cw * (lw * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cw * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) :=
          mul_le_mul_right hEw _
      _ = 16 * (ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) := by ring
  have hTransB : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cb * lb) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCb_mul]; ring
      _ = ENNReal.ofReal Cb * (lb * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cb * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
          mul_le_mul_right hEb _
      _ = 16 * (ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) := by ring
  -- ============================================================================
  -- FINAL COMBINATION.
  -- ============================================================================
  -- The goal's super-level sets coincide with `Esub`, `Fsub` (`β = 1/(4(P·A+1))`).
  have hβeq : (1 : ℝ) / (4 * (Real.pi ^ (1 / q) * A + 1)) = β := by
    rw [hβdef, hÃdef, hPdef]
  have hCw_goal : (256 : ℝ) * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1) = Cw := by
    rw [hCwdef, hÃdef, hPdef]
  have hCb_goal : (64 : ℝ) * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q = Cb := by
    rw [hCbdef, hÃdef, hPdef]
  -- The goal coincides (definitionally + via `hβeq`/`hCw_goal`/`hCb_goal`) with the bound below.
  have hgoal : ∫⁻ z in S, w z ^ q
      ≤ (ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
          + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q))
          + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) :=
    calc ∫⁻ z in S, w z ^ q
        ≤ ∫⁻ z in ⋃ i ∈ B, Cset i, w z ^ q := hLHS1
      _ = (∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q) + ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q := hLHS2
      _ ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
            + ENNReal.ofReal (lam ^ q) * volume (Metric.ball x₀ s) :=
          add_le_add hInnerSum hBoundary
      _ ≤ ENNReal.ofReal (4 * lam ^ q)
              * (volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
                + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
            + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) := by
          apply add_le_add (mul_le_mul_right hQvol _)
          exact mul_le_mul_left
            (ENNReal.ofReal_le_ofReal (by nlinarith [Real.rpow_nonneg hlam.le q])) _
      _ = (ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
            + ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
            + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) := by rw [mul_add]
      _ ≤ (ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
            + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q))
            + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) :=
          add_le_add (add_le_add hTransW hTransB) le_rfl
  -- The goal is already (definitionally, via the `set`s) in `Cw, Cb, Esub, Fsub` form.
  exact hgoal

/-- **Collar-free honest exponent-1 good-λ** (the high-`λ₁` companion of
`gehring_goodLambda_integral_core`).  For levels `lam` above the structural threshold
`λ₁` (encoded by `hλ₁ : 5·√Wm ≤ (s−t)·lam^{q/2}`, where `Wm = (∫_{16B₀}wᵠ).toReal`), **no
boundary cube meets `ball x₀ t`**: a stopping cube `Qᵢ` meeting `ball x₀ t` has, by the
stopping lower bound `lamᵠ·vol(Qᵢ) ≤ ∫_{ball s}wᵠ ≤ Wm`, side `ρᵢ ≤ √Wm/lam^{q/2} ≤ (s−t)/5`,
so its `4×` enlargement `Eᵢ = ball cᵢ(4ρᵢ) ⊆ ball x₀(t+5ρᵢ) ⊆ ball x₀ s` is engine-able.
Hence the boundary collar of the core vanishes on the `ball t` super-level set, giving the
collar-FREE good-λ that the consumer integrates on the high range `(λ₁,∞)`. -/
private theorem gehring_goodLambda_integral_noCollar {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (x₀ : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hWfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (hBfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q < ⊤)
    (t s : ℝ) (ht : 4 * R₀ ≤ t) (hts : t < s) (hs : s ≤ 16 * R₀)
    (lam : ℝ) (hlam : 0 < lam)
    (hlam0cond : (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q)
    (hlam1 : 5 * Real.sqrt ((∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
            ≤ (s - t) * lam ^ (q / 2)) :
    ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (w z).toReal}, w z ^ q
      ≤ ENNReal.ofReal (256 * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1))
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (w z).toReal}, w z)
        + ENNReal.ofReal (64 * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q)
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (b z).toReal}, b z ^ q) := by
  classical
  have hq0 : 0 < q := lt_trans one_pos hq
  have hst : 0 < s - t := by linarith
  have hspos : 0 < s := by linarith
  -- Planar doubling instance for the Carleson engine.
  haveI hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  -- Abbreviation `Ã = π^{1/q}·A + 1 > 0` (the reverse-Hölder constant, padded by 1).
  set P : ℝ := Real.pi ^ (1 / q) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  set Ã : ℝ := P * A + 1 with hÃdef
  have hÃpos : 0 < Ã := by rw [hÃdef]; nlinarith [hPpos, hA]
  -- The collar/level constants: `β = 1/(4Ã)`, w-level `lw = ofReal(βlam)`,
  -- b-level `lb = ofReal((βlam)^q)`.
  set β : ℝ := 1 / (4 * Ã) with hβdef
  have hβpos : 0 < β := by rw [hβdef]; positivity
  set lw : ℝ≥0∞ := ENNReal.ofReal (β * lam) with hlwdef
  set lb : ℝ≥0∞ := ENNReal.ofReal ((β * lam) ^ q) with hlbdef
  -- Choose `M` minimal-ish with `2s ≤ 2^M` (any large enough `M` works for the cover).
  obtain ⟨M, hM⟩ : ∃ M : ℤ, 2 * s ≤ (2 : ℝ) ^ M := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * s) (by norm_num : (1:ℝ) < 2)
    exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hn.le⟩
  -- Run the global dyadic cover.
  obtain ⟨B, hBct, hBdisj, hBscale, hBmeet, hBcov, hBup, hBlow⟩ :=
    gehring_dyadic_global_cover hq0 hwmeas x₀ s hspos M hM lam hlam hlam0cond
  -- Geometry of a cube `i ∈ B`: centre, scale, enlarged ball `Eᵢ = ball cᵢ (4·2^{nᵢ})`.
  set cI : ℤ × (ℤ × ℤ) → ℂ := fun i => dyadicCenter i.1 i.2 with hcIdef
  set ρI : ℤ × (ℤ × ℤ) → ℝ := fun i => (2 : ℝ) ^ i.1 with hρIdef
  have hρIpos : ∀ i, 0 < ρI i := fun i => by rw [hρIdef]; exact zpow_pos (by norm_num) _
  -- The cube is inside its circumscribed ball `ball cᵢ (2^{nᵢ})`.
  have hQsubball : ∀ i, dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (ρI i) := by
    intro i; rw [hcIdef, hρIdef]; exact dyadicSquare_subset_ball i.1 i.2
  -- ============================================================================
  -- PER-CUBE REVERSE-HÖLDER DICHOTOMY (super-level concentrated).
  -- For `i ∈ B`: either `w`-good (`lw·vol(Eᵢ) ≤ ∫_{Eᵢ∩{w>βλ}} w`) or `b`-good
  -- (`lb·vol(Eᵢ) ≤ ∫_{Eᵢ∩{b>βλ}} bᵠ`), where `Eᵢ = ball cᵢ (4ρᵢ)`.
  -- ============================================================================
  set Esub : Set ℂ := {z : ℂ | β * lam < (w z).toReal} with hEsubdef
  set Fsub : Set ℂ := {z : ℂ | β * lam < (b z).toReal} with hFsubdef
  -- Full (un-restricted) reverse-Hölder levels `lwf = lam/(2Ã)`, `lbf = (lam/(2Ã))^q`.
  set lwf : ℝ≥0∞ := ENNReal.ofReal (lam / (2 * Ã)) with hlwfdef
  set lbf : ℝ≥0∞ := ENNReal.ofReal ((lam / (2 * Ã)) ^ q) with hlbfdef
  have hdich : ∀ i ∈ B,
      (lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z) ∨
      (lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q) := by
    intro i hi
    -- `lam < (⨍_{Qᵢ} wᵠ)^{1/q}`.
    have hQpos : 0 < volume (dyadicSquare i.1 i.2) := by
      rw [volume_dyadicSquare, ENNReal.ofReal_pos]; positivity
    have hQtop : volume (dyadicSquare i.1 i.2) ≠ ⊤ := by
      rw [volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
    have hlowfull : (ENNReal.ofReal lam) ^ q < ⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume := by
      refine lt_of_lt_of_le (hBlow i hi) ?_
      rw [setLAverage_eq]
      exact ENNReal.div_le_div_right (lintegral_mono_set Set.inter_subset_left) _
    have h1q : (0:ℝ) < 1 / q := by positivity
    have hroot : ENNReal.ofReal lam <
        (⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume) ^ (1 / q) := by
      have h := ENNReal.rpow_lt_rpow hlowfull h1q
      have hid : (ENNReal.ofReal lam ^ q) ^ (1 / q) = ENNReal.ofReal lam := by
        rw [one_div, ENNReal.rpow_rpow_inv hq0.ne']
      rwa [hid] at h
    -- Reverse-Hölder on the cube, with constant `P·A ≤ Ã`.
    have hRHc := dyadic_reverseHolder' hq hA hRH i.1 i.2
    have hPA_le : ENNReal.ofReal (P * A) ≤ ENNReal.ofReal Ã :=
      ENNReal.ofReal_le_ofReal (by rw [hÃdef, hPdef]; nlinarith [hPpos, hA])
    have hRHc' : ENNReal.ofReal lam <
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã *
            (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
      have hceq : Metric.ball (dyadicCenter i.1 i.2) (4 * (2:ℝ) ^ i.1)
          = Metric.ball (cI i) (4 * ρI i) := by rw [hcIdef, hρIdef]
      rw [hceq] at hRHc
      refine lt_of_lt_of_le hroot (le_trans hRHc (add_le_add ?_ ?_)) <;>
        exact mul_le_mul_left hPA_le _
    -- One of the two terms is `≥ ofReal lam / 2`.
    have hvol4_pos : 0 < volume (Metric.ball (cI i) (4 * ρI i)) :=
      Metric.measure_ball_pos _ _ (by positivity [hρIpos i])
    have hvol4_ne : volume (Metric.ball (cI i) (4 * ρI i)) ≠ 0 := hvol4_pos.ne'
    have hvol4_top : volume (Metric.ball (cI i) (4 * ρI i)) ≠ ⊤ := measure_ball_lt_top.ne
    have hÃne : ENNReal.ofReal Ã ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hÃpos
    have hÃtop : ENNReal.ofReal Ã ≠ ⊤ := ENNReal.ofReal_ne_top
    have hhalf : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume)
          ≥ ENNReal.ofReal lam / 2 ∨
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          ≥ ENNReal.ofReal lam / 2 := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [not_le] at h1 h2
      have hsum2 : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          < ENNReal.ofReal lam / 2 + ENNReal.ofReal lam / 2 := ENNReal.add_lt_add h1 h2
      rw [ENNReal.add_halves] at hsum2
      exact absurd (lt_trans hRHc' hsum2) (lt_irrefl _)
    -- `lwf · ofReal Ã = ofReal lam / 2`.
    have hlwf_mul : lwf * ENNReal.ofReal Ã = ENNReal.ofReal lam / 2 := by
      rw [hlwfdef, ← ENNReal.ofReal_mul (by positivity)]
      have hreal : lam / (2 * Ã) * Ã = lam / 2 := by field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1; norm_num
    rcases hhalf with hw | hb
    · left
      have hge : lwf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hw
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      rw [setLAverage_eq] at hge
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hge
    · right
      have hlbf_eq : lbf = lwf ^ q := by
        rw [hlbfdef, hlwfdef, ← ENNReal.ofReal_rpow_of_pos (by positivity)]
      have hgew : lwf ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
                * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hb
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      have hgeq : lbf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume := by
        rw [hlbf_eq]
        have hpow := ENNReal.rpow_le_rpow hgew hq0.le
        rwa [one_div, ENNReal.rpow_inv_rpow hq0.ne'] at hpow
      rw [setLAverage_eq] at hgeq
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hgeq
  -- ============================================================================
  -- SETUP for the assembly: containments, a.e. finiteness, the inner predicate.
  -- ============================================================================
  have hssub16 : Metric.ball x₀ s ⊆ Metric.ball x₀ (16 * R₀) :=
    Metric.ball_subset_ball (by linarith)
  -- `w < ⊤` a.e. on `ball s`.
  have hwfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), w z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ^ q ≠ ⊤ :=
      ae_lt_top' (hwmeas.pow_const q).restrict hWfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- `b < ⊤` a.e. on `ball s`.
  have hbfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), b z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ^ q ≠ ⊤ :=
      ae_lt_top' (hbmeas.pow_const q).restrict hBfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- The inner predicate: the enlargement `Eᵢ ⊆ ball x₀ s` (engine-able cubes).
  set Inn : Set (ℤ × (ℤ × ℤ)) :=
    {i ∈ B | Metric.ball (cI i) (4 * ρI i) ⊆ Metric.ball x₀ s} with hInndef
  -- The w-good and b-good inner subfamilies.
  set Sw : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z} with hSwdef
  set Sb : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q} with hSbdef
  have hSwsub : Sw ⊆ B := fun i hi => hi.1.1
  have hSbsub : Sb ⊆ B := fun i hi => hi.1.1
  have hSwct : Sw.Countable := hBct.mono hSwsub
  have hSbct : Sb.Countable := hBct.mono hSbsub
  -- The localized `u`-weights.
  set uw : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Esub).indicator w with huwdef
  set ub : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Fsub).indicator (fun z => b z ^ q) with hubdef
  -- ============================================================================
  -- PER-CUBE ENGINE HYPOTHESES (super-level concentration on inner cubes).
  -- ============================================================================
  have hEsub_nm : NullMeasurableSet Esub volume :=
    nullMeasurableSet_lt aemeasurable_const hwmeas.ennreal_toReal
  have hFsub_nm : NullMeasurableSet Fsub volume :=
    nullMeasurableSet_lt aemeasurable_const hbmeas.ennreal_toReal
  -- w-good inner: `lw·vol(Eᵢ) ≤ ∫_{Eᵢ} uw`.
  have h2uw : ∀ i ∈ Sw, lw * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), uw z := by
    rintro i ⟨⟨hiB, hEsub⟩, hwg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    -- `∫_E uw = ∫_{E ∩ Esub} w` (since `E ⊆ ball s`).
    have huwint : ∫⁻ z in E, uw z = ∫⁻ z in E ∩ Esub, w z := by
      have hpt : ∀ z ∈ E, uw z = Esub.indicator w z := by
        intro z hz
        rw [huwdef]
        by_cases hzE : z ∈ Esub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Esub := ⟨hEsubs hz, hzE⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzE]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Esub := fun h => hzE h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzE]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hEsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Pointwise a.e. on `E`: `w z ≤ Esub.indicator w z + ofReal(βlam)`.
    have hconc : ∫⁻ z in E, w z
        ≤ (∫⁻ z in E, Esub.indicator w z) + ENNReal.ofReal (β * lam) * volume E := by
      have hstep : ∫⁻ z in E, w z
          ≤ ∫⁻ z in E, (Esub.indicator w z + ENNReal.ofReal (β * lam)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), w z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hwfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzE : z ∈ Esub
        · rw [Set.indicator_of_mem hzE]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzE, zero_add]
          rw [hEsubdef, Set.mem_setOf_eq, not_lt] at hzE
          rw [← ENNReal.ofReal_toReal hzfin]
          exact ENNReal.ofReal_le_ofReal hzE
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Esub.indicator w z = ∫⁻ z in E ∩ Esub, w z := by
      rw [setLIntegral_indicator₀ _ (hEsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- Combine: `lwf·vol(E) ≤ ∫_E w`, and `lwf = lw + ofReal(βlam)`.
    have hlw_eq : lw + ENNReal.ofReal (β * lam) = lwf := by
      rw [hlwdef, hlwfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hβdef]; field_simp; ring
    rw [huwint]
    have hkey : lwf * volume E
        ≤ (∫⁻ z in E ∩ Esub, w z) + ENNReal.ofReal (β * lam) * volume E := le_trans hwg hconc
    rw [← hlw_eq, add_mul] at hkey
    refine ENNReal.le_of_add_le_add_right ?_ hkey
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- b-good inner: `lb·vol(Eᵢ) ≤ ∫_{Eᵢ} ub`.
  have h2ub : ∀ i ∈ Sb, lb * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), ub z := by
    rintro i ⟨⟨hiB, hEsub⟩, hbg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    have hubint : ∫⁻ z in E, ub z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      have hpt : ∀ z ∈ E, ub z = Fsub.indicator (fun z => b z ^ q) z := by
        intro z hz
        rw [hubdef]
        by_cases hzF : z ∈ Fsub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Fsub := ⟨hEsubs hz, hzF⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzF]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Fsub := fun h => hzF h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzF]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hFsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Super-level concentration: `bᵠ z ≤ Fsub.indicator bᵠ z + ofReal((βlam)^q)` a.e. on `E`.
    have hconc : ∫⁻ z in E, b z ^ q
        ≤ (∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z)
          + ENNReal.ofReal ((β * lam) ^ q) * volume E := by
      have hstep : ∫⁻ z in E, b z ^ q
          ≤ ∫⁻ z in E, (Fsub.indicator (fun z => b z ^ q) z + ENNReal.ofReal ((β * lam) ^ q)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), b z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hbfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzF : z ∈ Fsub
        · rw [Set.indicator_of_mem hzF]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzF, zero_add]
          rw [hFsubdef, Set.mem_setOf_eq, not_lt] at hzF
          rw [← ENNReal.ofReal_toReal hzfin,
            ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0.le]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ENNReal.toReal_nonneg hzF hq0.le)
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      rw [setLIntegral_indicator₀ _ (hFsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- `lb + ofReal((βlam)^q) ≤ lbf` (since `2 ≤ 2^q`).
    have hlb_le : lb + ENNReal.ofReal ((β * lam) ^ q) ≤ lbf := by
      rw [hlbdef, hlbfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h2q : (2:ℝ) ≤ 2 ^ q := by
        calc (2:ℝ) = 2 ^ (1:ℝ) := by rw [Real.rpow_one]
          _ ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hq)
      have hβl : (0:ℝ) ≤ β * lam := by positivity
      have hkey : 2 * (β * lam) ^ q ≤ (lam / (2 * Ã)) ^ q := by
        have heq : lam / (2 * Ã) = 2 * (β * lam) := by rw [hβdef]; field_simp; ring
        rw [heq, Real.mul_rpow (by norm_num) hβl]
        nlinarith [Real.rpow_nonneg hβl q, h2q]
      linarith [hkey]
    rw [hubint]
    have hkey : lbf * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans hbg hconc
    have hlbstep : (lb + ENNReal.ofReal ((β * lam) ^ q)) * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans (mul_le_mul_left hlb_le _) hkey
    rw [add_mul] at hlbstep
    refine ENNReal.le_of_add_le_add_right ?_ hlbstep
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- ============================================================================
  -- ENGINE CALLS: bound `vol(⋃_{Sw} Eᵢ)`, `vol(⋃_{Sb} Eᵢ)` by super-level integrals.
  -- ============================================================================
  -- Radius bound: for inner cubes, `4·ρI i ≤ s` (since `Eᵢ ⊆ ball x₀ s`).
  have hRbd : ∀ i ∈ Inn, 4 * ρI i ≤ s := by
    rintro i ⟨hiB, hEsub⟩
    by_contra hgt
    push Not at hgt
    have hvle : volume (Metric.ball (cI i) (4 * ρI i)) ≤ volume (Metric.ball x₀ s) :=
      measure_mono hEsub
    rw [Complex.volume_ball, Complex.volume_ball] at hvle
    have h4ρpos : 0 < 4 * ρI i := by have := hρIpos i; linarith
    rw [ENNReal.mul_le_mul_iff_left (by simp [NNReal.pi_pos.ne']) (by simp)] at hvle
    rw [← ENNReal.ofReal_pow h4ρpos.le, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ s),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvle
    nlinarith [hvle, hgt, h4ρpos]
  have hRbdSw : ∀ i ∈ Sw, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hRbdSb : ∀ i ∈ Sb, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hEw := gehring_engine_idx Sw hSwct cI (fun i => 4 * ρI i) lw uw s hRbdSw h2uw
  have hEb := gehring_engine_idx Sb hSbct cI (fun i => 4 * ρI i) lb ub s hRbdSb h2ub
  -- The global integrals of `uw`, `ub` are the super-level masses over `ball x₀ s`.
  have hIuw : ∫⁻ z, uw z = ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    rw [huwdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hEsub_nm)]
  have hIub : ∫⁻ z, ub z = ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    rw [hubdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hFsub_nm)]
  rw [hIuw] at hEw
  rw [hIub] at hEb
  -- ============================================================================
  -- COLLAR-FREE LHS BOUND.  For `lam ≥ λ₁` every cube `i ∈ B` whose square meets
  -- `ball x₀ t` is INNER (`Eᵢ ⊆ ball x₀ s`), so the LHS super-level mass over
  -- `ball t` is covered by the inner cubes alone: NO boundary collar.
  -- ============================================================================
  set S : Set ℂ := Metric.ball x₀ t ∩ {z : ℂ | lam < (w z).toReal} with hSdef
  have htsub : Metric.ball x₀ t ⊆ Metric.ball x₀ s := Metric.ball_subset_ball hts.le
  -- The finite master mass `Wm = (∫_{16B₀}wᵠ).toReal` and `∫_{ball s}wᵠ ≤ Wm` (ENNReal).
  set Wm : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hWmdef
  have hWm0 : 0 ≤ Wm := ENNReal.toReal_nonneg
  have hssub16 : Metric.ball x₀ s ⊆ Metric.ball x₀ (16 * R₀) :=
    Metric.ball_subset_ball (by linarith)
  have hInts_le_Wm : (∫⁻ z in Metric.ball x₀ s, w z ^ q).toReal ≤ Wm := by
    rw [hWmdef]; exact ENNReal.toReal_mono hWfin.ne (lintegral_mono_set hssub16)
  -- KEY: any cube `i ∈ B` meeting `ball x₀ t` is inner.
  have hMeetInn : ∀ i ∈ B, (dyadicSquare i.1 i.2 ∩ Metric.ball x₀ t).Nonempty →
      Metric.ball (cI i) (4 * ρI i) ⊆ Metric.ball x₀ s := by
    intro i hiB hmeet
    obtain ⟨p, hpQ, hpt⟩ := hmeet
    -- `dist x₀ (cI i) ≤ t + ρI i`.
    have hpcI : dist p (cI i) < ρI i := Metric.mem_ball.mp (hQsubball i hpQ)
    have hpx₀ : dist p x₀ < t := Metric.mem_ball.mp hpt
    have hdist : dist x₀ (cI i) ≤ t + ρI i := by
      calc dist x₀ (cI i) ≤ dist x₀ p + dist p (cI i) := dist_triangle _ _ _
        _ = dist p x₀ + dist p (cI i) := by rw [dist_comm x₀ p]
        _ ≤ t + ρI i := by linarith
    -- `ρI i ≤ (s - t)/5`, from `lamᵠ·ρᵢ² ≤ ∫_{ball s}wᵠ ≤ Wm`.
    have hρpos := hρIpos i
    -- `(ofReal lam)^q · vol(Qᵢ) ≤ ∫_{Qᵢ∩ball s}wᵠ ≤ ∫_{ball s}wᵠ`.
    have hQpos : 0 < volume (dyadicSquare i.1 i.2) := by
      rw [volume_dyadicSquare, ENNReal.ofReal_pos]; positivity
    have hQtop : volume (dyadicSquare i.1 i.2) ≠ ⊤ := by
      rw [volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
    have hstop : (ENNReal.ofReal lam) ^ q * volume (dyadicSquare i.1 i.2)
        ≤ ∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q := by
      have h := hBlow i hiB
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl hQpos.ne') (Or.inl hQtop)] at h
      exact h.le
    -- to reals: `lamᵠ · ρᵢ² ≤ Wm`.
    have hInts_fin : ∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q ≠ ⊤ :=
      ne_top_of_le_ne_top hWfin.ne (lintegral_mono_set (Set.inter_subset_right.trans hssub16))
    have hstopR : lam ^ q * (ρI i) ^ 2 ≤ Wm := by
      have hmono := ENNReal.toReal_mono hInts_fin hstop
      have hLHSeq : ((ENNReal.ofReal lam) ^ q * volume (dyadicSquare i.1 i.2)).toReal
          = lam ^ q * (ρI i) ^ 2 := by
        rw [ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le,
          ENNReal.toReal_ofReal (by positivity), volume_dyadicSquare,
          ENNReal.toReal_ofReal (by positivity), hρIdef]
      rw [hLHSeq] at hmono
      calc lam ^ q * (ρI i) ^ 2
          ≤ (∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q).toReal := hmono
        _ ≤ Wm := le_trans (ENNReal.toReal_mono hWfin.ne
              (lintegral_mono_set (Set.inter_subset_right.trans hssub16))) le_rfl
    -- `ρᵢ ≤ √Wm / lam^{q/2}`, hence `5ρᵢ ≤ s - t` from `hλ₁`.
    have hlamq2 : 0 < lam ^ (q / 2) := Real.rpow_pos_of_pos hlam _
    have hρWm : ρI i * lam ^ (q / 2) ≤ Real.sqrt Wm := by
      rw [Real.le_sqrt (by positivity) hWm0]
      have hsplit : lam ^ q = (lam ^ (q / 2)) ^ 2 := by
        rw [← Real.rpow_natCast (lam ^ (q/2)) 2, ← Real.rpow_mul hlam.le]
        congr 1; push_cast; ring
      calc (ρI i * lam ^ (q / 2)) ^ 2 = lam ^ q * (ρI i) ^ 2 := by rw [hsplit]; ring
        _ ≤ Wm := hstopR
    have h5ρ : 5 * ρI i ≤ s - t := by
      have hkey : 5 * (ρI i * lam ^ (q / 2)) ≤ (s - t) * lam ^ (q / 2) :=
        le_trans (by linarith [hρWm]) hlam1
      have : 5 * ρI i * lam ^ (q / 2) ≤ (s - t) * lam ^ (q / 2) := by linarith [hkey]
      exact le_of_mul_le_mul_right (by linarith [this]) hlamq2
    -- Conclude `Eᵢ ⊆ ball x₀ s`.
    refine Metric.ball_subset_ball' ?_
    rw [dist_comm]
    linarith [hdist, h5ρ, hρpos]
  -- The inner predicate and the w/b-good subfamilies (same as the core).
  -- `S` is a.e. covered by `⋃_{i∈B} (Qᵢ ∩ ball s)`, but we refine to inner cubes.
  set Cset : ℤ × (ℤ × ℤ) → Set ℂ := fun i => dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s with hCsetdef
  have hCmeas : ∀ i, MeasurableSet (Cset i) :=
    fun i => (measurableSet_dyadicSquare _ _).inter measurableSet_ball
  have hCdisj : B.PairwiseDisjoint Cset := by
    intro i hi j hj hij
    exact (hBdisj hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  -- a.e. cover of `S` by the INNER cubes: any covering cube meeting `ball t` is inner.
  have hScov : volume (S \ ⋃ i ∈ Inn, Cset i) = 0 := by
    refine measure_mono_null ?_ hBcov
    intro z hz
    obtain ⟨hzS, hznotcov⟩ := hz
    have hzs : z ∈ Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal} :=
      ⟨htsub hzS.1, hzS.2⟩
    refine ⟨hzs, ?_⟩
    intro hzcov
    apply hznotcov
    rw [Set.mem_iUnion₂] at hzcov ⊢
    obtain ⟨i, hi, hzi⟩ := hzcov
    -- `z ∈ Qᵢ` and `z ∈ ball t`, so `Qᵢ` meets `ball t`, hence `i ∈ Inn`.
    have hmeet : (dyadicSquare i.1 i.2 ∩ Metric.ball x₀ t).Nonempty := ⟨z, hzi, hzS.1⟩
    have hiInn : i ∈ Inn := ⟨hi, hMeetInn i hi hmeet⟩
    exact ⟨i, hiInn, hzi, hzs.1⟩
  -- `∫_S wᵠ ≤ ∫_{⋃_{Inn} Cset} wᵠ`.
  have hInnsubB : Inn ⊆ B := fun i hi => hi.1
  have hInnct : Inn.Countable := hBct.mono hInnsubB
  have hUmeasInn : MeasurableSet (⋃ i ∈ Inn, Cset i) :=
    MeasurableSet.biUnion hInnct (fun i _ => hCmeas i)
  have hLHS1 : ∫⁻ z in S, w z ^ q ≤ ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q := by
    have h1 : (S \ (S \ (⋃ i ∈ Inn, Cset i)) : Set ℂ) =ᵐ[volume] S := diff_null_ae_eq_self hScov
    have h2 : S \ (S \ (⋃ i ∈ Inn, Cset i)) = S ∩ (⋃ i ∈ Inn, Cset i) :=
      Set.diff_diff_right_self S _
    rw [h2] at h1
    rw [setLIntegral_congr h1.symm]
    exact lintegral_mono_set Set.inter_subset_right
  -- INNER BOUND: `∫_{⋃_{Inn} Cset} wᵠ ≤ ofReal(4lamᵠ)·(vol(⋃_{Sw}Eᵢ) + vol(⋃_{Sb}Eᵢ))`.
  have hInnerSum : ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q
      ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
    rw [lintegral_biUnion hInnct (fun i _ => hCmeas i) (hCdisj.subset hInnsubB)]
    calc ∑' i : Inn, ∫⁻ z in Cset i, w z ^ q
        ≤ ∑' i : Inn, ENNReal.ofReal (4 * lam ^ q)
            * volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) := by
          apply ENNReal.tsum_le_tsum
          rintro ⟨i, hi⟩
          exact hBup i (hInnsubB hi)
      _ = ENNReal.ofReal (4 * lam ^ q)
            * ∑' i : Inn, volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
          rw [measure_biUnion hInnct (Set.Pairwise.mono hInnsubB hBdisj)
            (fun i _ => measurableSet_dyadicSquare _ _)]
  -- `vol(⋃_{Inn} Qᵢ) ≤ vol(⋃_{Sw} Eᵢ) + vol(⋃_{Sb} Eᵢ)`.
  have hQcover : (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ⊆ (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        ∪ (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
    apply Set.iUnion₂_subset
    intro i hi
    have hiB : i ∈ B := hInnsubB hi
    have hQE : dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (4 * ρI i) := by
      refine (hQsubball i).trans (Metric.ball_subset_ball ?_)
      have := hρIpos i; linarith
    rcases hdich i hiB with hw | hb
    · have hiSw : i ∈ Sw := ⟨hi, hw⟩
      exact hQE.trans (Set.subset_union_of_subset_left
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSw) _)
    · have hiSb : i ∈ Sb := ⟨hi, hb⟩
      exact hQE.trans (Set.subset_union_of_subset_right
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSb) _)
  have hQvol : volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ≤ volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) :=
    le_trans (measure_mono hQcover) (measure_union_le _ _)
  -- COEFFICIENT TRANSFER (identical to the core).
  set Cw : ℝ := 256 * Ã * lam ^ (q - 1) with hCwdef
  set Cb : ℝ := 64 * (4 * Ã) ^ q with hCbdef
  have hlw_ne : lw ≠ 0 := by rw [hlwdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlb_ne : lb ≠ 0 := by rw [hlbdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlw_top : lw ≠ ⊤ := by rw [hlwdef]; exact ENNReal.ofReal_ne_top
  have hlb_top : lb ≠ ⊤ := by rw [hlbdef]; exact ENNReal.ofReal_ne_top
  have hlamq : lam ^ (q - 1) * lam = lam ^ q := by
    have h := (Real.rpow_add hlam (q - 1) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; congr 1; ring
  have hCw_mul : ENNReal.ofReal Cw * lw = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCwdef, hlwdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hβdef]
    have : 256 * Ã * lam ^ (q - 1) * (1 / (4 * Ã) * lam) = 64 * (lam ^ (q - 1) * lam) := by
      field_simp; ring
    rw [this, hlamq]; ring
  have hCb_mul : ENNReal.ofReal Cb * lb = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCbdef, hlbdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have hbase : (4 * Ã) * (β * lam) = lam := by rw [hβdef]; field_simp
    have hmr : (4 * Ã) ^ q * (β * lam) ^ q = lam ^ q := by
      rw [← Real.mul_rpow (by positivity) (by positivity [hβpos]), hbase]
    rw [show (64 * (4 * Ã) ^ q * (β * lam) ^ q : ℝ) = 64 * ((4 * Ã) ^ q * (β * lam) ^ q) by ring,
      hmr]; ring
  have hsixteen_ne : (16 : ℝ≥0∞) ≠ 0 := by norm_num
  have hsixteen_top : (16 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hTransW : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cw * lw) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCw_mul]; ring
      _ = ENNReal.ofReal Cw * (lw * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cw * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) :=
          mul_le_mul_right hEw _
      _ = 16 * (ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) := by ring
  have hTransB : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cb * lb) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCb_mul]; ring
      _ = ENNReal.ofReal Cb * (lb * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cb * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
          mul_le_mul_right hEb _
      _ = 16 * (ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) := by ring
  -- FINAL COMBINATION (collar-free).
  have hβeq : (1 : ℝ) / (4 * (Real.pi ^ (1 / q) * A + 1)) = β := by
    rw [hβdef, hÃdef, hPdef]
  have hCw_goal : (256 : ℝ) * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1) = Cw := by
    rw [hCwdef, hÃdef, hPdef]
  have hCb_goal : (64 : ℝ) * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q = Cb := by
    rw [hCbdef, hÃdef, hPdef]
  have hgoal : ∫⁻ z in S, w z ^ q
      ≤ ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
          + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
    calc ∫⁻ z in S, w z ^ q
        ≤ ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q := hLHS1
      _ ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := hInnerSum
      _ ≤ ENNReal.ofReal (4 * lam ^ q)
              * (volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
                + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))) := mul_le_mul_right hQvol _
      _ = ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
            + ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
          rw [mul_add]
      _ ≤ ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
            + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
          add_le_add hTransW hTransB
  exact hgoal


/-! ## Hole-filling pillars for `gehring_selfImprovement` (STEP B).

The `O(ε)` Gehring gain decomposes ONLY the `w^ε` factor, KEEPING the `w^q` mass:
`∫ f^{q+ε} = ε·∫_{λ>0} λ^{ε-1}·(∫_{{f>λ}} f^q) dλ`.  The leading `ε` is the gain.
These private helpers prove: the `w^ε`-mass layer-cake (`gehring_mass_layerCake`), its
Tonelli reconstruction (`gehring_recon`), the ε-absorption assembly (`gehring_assembly`),
the `.toReal` conversion (`gehring_toReal_conv`), and the hole-fill packaging
(`gehring_holeFill`) consuming the truncated super-level good-λ. -/

private theorem gehring_scalar_lc (c : ℝ) (hc : 0 ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ lam in Set.Ioo (0:ℝ) c, ENNReal.ofReal (lam ^ (ε - 1)) = ENNReal.ofReal (c ^ ε / ε) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst hc0; simp [Real.zero_rpow hε.ne']
  · have hii : IntervalIntegrable (fun lam => lam ^ (ε - 1)) volume 0 c :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < ε - 1)
    have hint : IntegrableOn (fun lam => lam ^ (ε - 1)) (Set.Ioo 0 c) volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcpos.le).mp hii
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 c)] (fun lam => lam ^ (ε - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with lam hlam
      exact Real.rpow_nonneg hlam.1.le _
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcpos.le]
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < ε - 1))]
    rw [Real.zero_rpow (by linarith : ε - 1 + 1 ≠ 0)]
    rw [show ε - 1 + 1 = ε by ring]; ring


/-- **`Ž_N`-layer-cake (`q`-mass × truncated `ε`-factor).**  The iterated quantity of
STEP B is `Ž_N(t) = ∫_{ball t} w^q · (min w N)^ε` (the FULL `q`-mass `w^q` times the
TRUNCATED `ε`-gain factor `(min w N)^ε`).  Its `(min w N).toReal`-layer-cake decomposes ONLY the
bounded `ε`-factor (`min w N ≤ N`, so the `λ`-integral lives on `(0,N)`) while keeping the full,
a-priori-integrable `w^q` mass.  This is the device that eliminates the over-truncation tail: the
inner super-level integral is the FULL `∫_{{w>λ}} w^q` (not the truncated `(min w N)^q`-mass), so
the good-λ that feeds it is the honest exponent-preserving one for the integrable `w^q`. -/
private theorem gehring_mass_layerCake {q ε : ℝ} (_hq0 : 0 < q) (hε : 0 < ε) {w : ℂ → ℝ≥0∞}
    (hwmeas : AEMeasurable w volume) (N : ℕ) (x₀ : ℂ) (t : ℝ) :
    ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
      = ENNReal.ofReal ε * ∫⁻ lam in Set.Ioi (0:ℝ),
          (∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal},
            w z ^ q) * ENNReal.ofReal (lam ^ (ε - 1)) := by
  classical
  set f : ℂ → ℝ≥0∞ := fun z => min (w z) (N : ℝ≥0∞) with hfdef
  have hfmeas : AEMeasurable f volume := hwmeas.min aemeasurable_const
  have hffin : ∀ z, f z ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  set μ : Measure ℂ :=
    (volume.restrict (Metric.ball x₀ t)).withDensity (fun z => w z ^ q) with hμdef
  have hwqmeas : AEMeasurable (fun z => w z ^ q) (volume.restrict (Metric.ball x₀ t)) :=
    (hwmeas.restrict).pow_const q
  have hLHS : ∫⁻ z in Metric.ball x₀ t, w z ^ q * f z ^ ε = ∫⁻ z, f z ^ ε ∂μ := by
    rw [hμdef, lintegral_withDensity_eq_lintegral_mul₀ hwqmeas ((hfmeas.restrict).pow_const ε)]
    apply lintegral_congr_ae
    filter_upwards with z
    simp only [Pi.mul_apply]
  rw [hLHS]
  set g : ℂ → ℝ := fun z => (f z).toReal with hgdef
  have hpt : ∀ z, f z ^ ε = ENNReal.ofReal (g z ^ ε) := by
    intro z
    rw [hgdef, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hε.le,
      ENNReal.ofReal_toReal (hffin z)]
  have hgnn : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall (fun z => ENNReal.toReal_nonneg)
  have hgmeas : AEMeasurable g μ := by
    refine (hfmeas.ennreal_toReal.restrict (s := Metric.ball x₀ t)).mono' ?_
    rw [hμdef]; exact withDensity_absolutelyContinuous _ _
  have hrpowlc := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ) hgnn hgmeas hε
  rw [show (∫⁻ z, f z ^ ε ∂μ) = ∫⁻ z, ENNReal.ofReal (g z ^ ε) ∂μ from lintegral_congr hpt]
  rw [hrpowlc]
  congr 1
  apply lintegral_congr
  intro lam
  congr 1
  have hwqvol : AEMeasurable (fun z => w z ^ q) volume := hwmeas.pow_const q
  have hgvol : AEMeasurable g volume := hfmeas.ennreal_toReal
  have hmslt : NullMeasurableSet {a : ℂ | lam < g a} (volume.restrict (Metric.ball x₀ t)) :=
    nullMeasurableSet_lt aemeasurable_const hgvol.restrict
  rw [hμdef, withDensity_apply₀ _ hmslt, Measure.restrict_restrict₀ hmslt]
  have hseteq : {a : ℂ | lam < g a} ∩ Metric.ball x₀ t
      = Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal} := by
    rw [hgdef]; ext z; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
  rw [hseteq]

private theorem gehring_recon {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) {D : ℂ → ℝ≥0∞} {θ : ℂ → ℝ}
    (hDmeas : AEMeasurable D volume) (hθmeas : AEMeasurable θ volume)
    (hθnn : ∀ z, 0 ≤ θ z) (x₀ : ℂ) (s : ℝ) :
    ∫⁻ lam in Set.Ioi (0:ℝ),
        (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < θ z}, D z)
          * ENNReal.ofReal (lam ^ (p - 1))
      = ENNReal.ofReal (1 / (p * β ^ p)) *
          ∫⁻ z in Metric.ball x₀ s, D z * ENNReal.ofReal (θ z ^ p) := by
  classical
  set ν : Measure ℂ := (volume.restrict (Metric.ball x₀ s)).withDensity D with hνdef
  have hinner : ∀ lam : ℝ, (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < θ z}, D z)
      = ν {z | β * lam < θ z} := by
    intro lam
    have hmslt : NullMeasurableSet {z : ℂ | β * lam < θ z} (volume.restrict (Metric.ball x₀ s)) :=
      nullMeasurableSet_lt aemeasurable_const hθmeas.restrict
    rw [hνdef, withDensity_apply₀ _ hmslt, Measure.restrict_restrict₀ hmslt]
    have hseteq : {z : ℂ | β * lam < θ z} ∩ Metric.ball x₀ s
        = Metric.ball x₀ s ∩ {z | β * lam < θ z} := Set.inter_comm _ _
    rw [hseteq]
  simp_rw [hinner]
  set hθ : ℂ → ℝ := fun z => θ z / β with hθdef
  have hνset : ∀ lam : ℝ, ν {z | β * lam < θ z} = ν {z | lam < hθ z} := by
    intro lam; congr 1; ext z
    simp only [Set.mem_setOf_eq, hθdef, lt_div_iff₀ hβ, mul_comm]
  simp_rw [hνset]
  have hhnn : 0 ≤ᵐ[ν] hθ := Filter.Eventually.of_forall (fun z => by
    rw [hθdef]; exact div_nonneg (hθnn z) hβ.le)
  have hhmeas : AEMeasurable hθ ν := by
    have h1 : AEMeasurable hθ (volume.restrict (Metric.ball x₀ s)) := by
      rw [hθdef]; exact hθmeas.restrict.div_const β
    refine h1.mono' ?_
    rw [hνdef]; exact withDensity_absolutelyContinuous _ _
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := ν) hhnn hhmeas hp
  have hdens : ∫⁻ z, ENNReal.ofReal (hθ z ^ p) ∂ν
      = ENNReal.ofReal (1 / β ^ p) * ∫⁻ z in Metric.ball x₀ s, D z * ENNReal.ofReal (θ z ^ p) := by
    rw [hνdef, lintegral_withDensity_eq_lintegral_mul₀ hDmeas.restrict
        (by
          refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
          have hhr : AEMeasurable hθ (volume.restrict (Metric.ball x₀ s)) := by
            rw [hθdef]; exact hθmeas.restrict.div_const β
          exact hhr.pow_const p)]
    rw [← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top : ENNReal.ofReal (1 / β ^ p) ≠ ⊤)]
    apply lintegral_congr_ae
    filter_upwards with z
    simp only [Pi.mul_apply, hθdef]
    rw [Real.div_rpow (hθnn z) hβ.le, ENNReal.ofReal_div_of_pos (by positivity)]
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < β ^ p), div_eq_mul_inv]
    ring
  rw [hdens] at hlc
  have hp0 : ENNReal.ofReal p ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eq_comm, ← ENNReal.eq_div_iff hp0 hptop] at hlc
  rw [hlc, ENNReal.div_eq_inv_mul]
  rw [show ENNReal.ofReal (1 / (p * β ^ p))
      = (ENNReal.ofReal p)⁻¹ * ENNReal.ofReal (1 / β ^ p) from ?_]
  · ring
  · rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp


/-- **The crux pointwise inequality.**  For `w : ℝ≥0∞`, `N : ℕ`, `1 < q`, `0 ≤ ε`,
`w · (min w N).toReal^{q+ε-1} ≤ w^q · (min w N)^ε`.  This is the inequality that eliminates the
over-truncation tail: on `{w ≤ N}` it is an equality (`w·w^{q+ε-1} = w^{q+ε} = w^q·w^ε`); on
`{w > N}` (`min w N = N`) it reads `w·N^{q+ε-1} ≤ w^q·N^ε`, i.e. `N^{q-1} ≤ w^{q-1}`, true since
`w > N` and `q-1 ≥ 0`.  It is what makes the reconstruction of the honest exponent-1 good-λ land
in the FINITE truncated quantity `Ž_N = ∫ w^q (min w N)^ε` rather than the untruncated energy. -/
private theorem gehring_crux_le {q ε : ℝ} (hq : 1 < q) (hε : 0 ≤ ε) (w : ℝ≥0∞) (N : ℕ) :
    w * ENNReal.ofReal ((min w (N : ℝ≥0∞)).toReal ^ (q + ε - 1))
      ≤ w ^ q * (min w (N : ℝ≥0∞)) ^ ε := by
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq
  have hqε1 : (0:ℝ) ≤ q + ε - 1 := by linarith
  have hminfin : min w (N : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  rcases le_total w (N : ℝ≥0∞) with hwN | hwN
  · -- `w ≤ N`: `min w N = w`.  Equality `w·w^{q+ε-1} = w^q·w^ε`.
    have hmin : min w (N : ℝ≥0∞) = w := min_eq_left hwN
    rw [hmin]
    rcases eq_or_ne w ⊤ with hwtop | hwfin
    · exact absurd (hwtop ▸ hwN) (by simp)
    · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hqε1, ENNReal.ofReal_toReal hwfin]
      rw [show w * w ^ (q + ε - 1) = w ^ (1:ℝ) * w ^ (q + ε - 1) by rw [ENNReal.rpow_one]]
      rw [← ENNReal.rpow_add_of_nonneg (1:ℝ) (q + ε - 1) zero_le_one hqε1]
      rw [← ENNReal.rpow_add_of_nonneg q ε hq0.le hε]
      rw [show (1:ℝ) + (q + ε - 1) = q + ε by ring]
  · -- `w ≥ N`: `min w N = N`.  Need `w·N^{q+ε-1} ≤ w^q·N^ε`, i.e. `w·N^{q-1} ≤ w^q`.
    have hmin : min w (N : ℝ≥0∞) = (N : ℝ≥0∞) := min_eq_right hwN
    rw [hmin]
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- `N = 0`: `min = 0`, `(0).toReal = 0`, LHS = `w·ofReal(0^{q+ε-1}) = 0` (since `q+ε-1>0`).
      subst hN0
      simp only [Nat.cast_zero, ENNReal.toReal_zero]
      rw [Real.zero_rpow (by linarith : q + ε - 1 ≠ 0), ENNReal.ofReal_zero, mul_zero]
      exact zero_le _
    · have hNreal : ((N:ℝ≥0∞)).toReal = (N:ℝ) := by simp
      rw [hNreal]
      -- RHS factor `(N:ℝ≥0∞)^ε = ofReal((N:ℝ)^ε)`.
      have hNε : (N:ℝ≥0∞) ^ ε = ENNReal.ofReal ((N:ℝ) ^ ε) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg N) hε]
      rw [hNε]
      -- LHS = w·ofReal(N^{q+ε-1}) = w·ofReal(N^{q-1})·ofReal(N^ε).
      rw [show (N:ℝ) ^ (q + ε - 1) = (N:ℝ) ^ (q - 1) * (N:ℝ) ^ ε by
        rw [← Real.rpow_add (by exact_mod_cast hNpos)]; ring_nf]
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [show w * (ENNReal.ofReal ((N:ℝ)^(q-1)) * ENNReal.ofReal ((N:ℝ)^ε))
        = (w * ENNReal.ofReal ((N:ℝ)^(q-1))) * ENNReal.ofReal ((N:ℝ)^ε) by ring]
      apply mul_le_mul_left
      -- `w·N^{q-1} ≤ w^q`.  Since `N ≤ w`: `N^{q-1} ≤ w^{q-1}`, and `w·w^{q-1}=w^q`.
      have hNlew : (ENNReal.ofReal ((N:ℝ)^(q-1))) ≤ w ^ (q - 1) := by
        rw [← ENNReal.ofReal_natCast (n := N)] at hwN
        calc ENNReal.ofReal ((N:ℝ)^(q-1))
            = (ENNReal.ofReal (N:ℝ)) ^ (q - 1) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg N) (by linarith)]
          _ ≤ w ^ (q - 1) := ENNReal.rpow_le_rpow hwN (by linarith)
      calc w * ENNReal.ofReal ((N:ℝ)^(q-1)) ≤ w * w ^ (q - 1) := mul_le_mul_right hNlew _
        _ = w ^ (1:ℝ) * w ^ (q - 1) := by rw [ENNReal.rpow_one]
        _ = w ^ (q:ℝ) := by
            rw [← ENNReal.rpow_add_of_nonneg (1:ℝ) (q-1) zero_le_one (by linarith),
              show (1:ℝ) + (q - 1) = q by ring]

private theorem gehring_assembly {q A ε : ℝ} (hq : 1 < q) (_hA : 0 ≤ A) (hεpos : 0 < ε)
    (_hεle : ε ≤ 1)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (x₀ : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (Cw Cb β : ℝ) (hCw : 0 ≤ Cw) (hCb : 0 ≤ Cb) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (N : ℕ) (t s : ℝ) (_ht : 4 * R₀ ≤ t) (_hts : t < s) (_hs : s ≤ 16 * R₀)
    -- THRESHOLD SPLIT.  The good-λ is consumed only on the HIGH range `lam ≥ lam₀`; on the LOW
    -- range `0 < lam < lam₀` the super-level `w^q`-mass is bounded by the master mass `Wlow`.
    (lam₀ : ℝ) (hlam₀0 : 0 ≤ lam₀) (Wlow : ℝ≥0∞) (hWlowtop : Wlow ≠ ⊤)
    (hWlow : ∀ lam : ℝ, 0 < lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q ≤ Wlow)
    -- The honest exponent-1 good-λ (TRUNCATED super-level on the RHS w-mass, FULL `w^q` on LHS),
    -- valid on the HIGH range `lam ≥ lam₀`:
    (hGL : ∀ lam : ℝ, 0 < lam → lam₀ ≤ lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
          + ENNReal.ofReal Cb
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q)) :
    ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
      ≤ ENNReal.ofReal (lam₀ ^ ε) * Wlow
        + (ENNReal.ofReal (Cw / ((q + ε - 1) * β ^ (q + ε - 1)) * ε)
          * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
        + ENNReal.ofReal (Cb / β ^ ε) * (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε))) := by
  classical
  have hq0 : 0 < q := lt_trans one_pos hq
  have hqε1 : 0 < q + ε - 1 := by linarith
  -- Step 1: layer-cake LHS.
  rw [gehring_mass_layerCake hq0 hεpos hwmeas N x₀ t]
  -- Step 2: THRESHOLD SPLIT of the λ-integral `Ioi 0 = Ioo 0 lam₀ ∪ Ici lam₀`.
  -- Abbreviations for the inner super-level integral and the good-λ RHS integrand.
  set Inner : ℝ → ℝ≥0∞ := fun lam =>
    ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q with hInnerdef
  set GLrhs : ℝ → ℝ≥0∞ := fun lam =>
    ENNReal.ofReal (Cw * lam ^ (q - 1))
        * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
      + ENNReal.ofReal Cb
        * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q) with hGLrhsdef
  -- Measurability of `Inner` (antitone level integral) for the set-split lemma.
  have hInner_meas : Measurable Inner := by
    have hanti : Antitone Inner := by
      intro a c hac; apply lintegral_mono_set; intro z hz
      exact ⟨hz.1, lt_of_le_of_lt hac hz.2⟩
    exact hanti.measurable
  have hgw_meas : Measurable (fun lam : ℝ => ENNReal.ofReal (lam ^ (ε - 1))) := by
    apply ENNReal.measurable_ofReal.comp; fun_prop
  -- The split bound: `∫_{Ioi 0} Inner·g ≤ LOW + HIGH` where LOW = `Wlow·lam₀^ε/ε` (as a λ-integral
  -- over `Ioo 0 lam₀`) and HIGH = `∫_{Ioi 0} GLrhs·g` (the good-λ RHS over all of `Ioi 0`,
  -- which dominates the `Ici lam₀` part by nonnegativity).
  have hsplit : ∫⁻ lam in Set.Ioi (0:ℝ), Inner lam * ENNReal.ofReal (lam ^ (ε - 1))
      ≤ (∫⁻ lam in Set.Ioo (0:ℝ) lam₀, Wlow * ENNReal.ofReal (lam ^ (ε - 1)))
        + ∫⁻ lam in Set.Ioi (0:ℝ), GLrhs lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
    rcases eq_or_lt_of_le hlam₀0 with hlam₀eq | hlam₀pos
    · -- `lam₀ = 0`: the LOW range `Ioo 0 0` is empty; HIGH covers everything.
      subst hlam₀eq
      simp only [Set.Ioo_self, Measure.restrict_empty, lintegral_zero_measure, zero_add]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lam hlam
      exact mul_le_mul_left (hGL lam hlam (le_of_lt hlam)) _
    · -- `lam₀ > 0`: split `Ioi 0 = Ioo 0 lam₀ ∪ Ici lam₀`.
      have hunion : Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) lam₀ ∪ Set.Ici lam₀ :=
        (Set.Ioo_union_Ici_eq_Ioi hlam₀pos).symm
      have hLHSsplit : ∫⁻ lam in Set.Ioi (0:ℝ), Inner lam * ENNReal.ofReal (lam ^ (ε - 1))
          = (∫⁻ lam in Set.Ioo (0:ℝ) lam₀, Inner lam * ENNReal.ofReal (lam ^ (ε - 1)))
            + ∫⁻ lam in Set.Ici lam₀, Inner lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
        rw [hunion, lintegral_union measurableSet_Ici
          (Set.disjoint_left.mpr (fun lam h1 h2 => absurd h2 (not_le.mpr h1.2)))]
      rw [hLHSsplit]
      apply add_le_add
      · -- LOW: `Inner lam ≤ Wlow` on `Ioo 0 lam₀`.
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with lam hlam
        exact mul_le_mul_left (hWlow lam hlam.1) _
      · -- HIGH: `Inner lam ≤ GLrhs lam` on `Ici lam₀ ⊆ {lam ≥ lam₀, lam > 0}`, then extend to
        -- `Ioi 0`.
        calc ∫⁻ lam in Set.Ici lam₀, Inner lam * ENNReal.ofReal (lam ^ (ε - 1))
            ≤ ∫⁻ lam in Set.Ici lam₀, GLrhs lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ici] with lam hlam
              exact mul_le_mul_left (hGL lam (lt_of_lt_of_le hlam₀pos hlam) hlam) _
          _ ≤ ∫⁻ lam in Set.Ioi (0:ℝ), GLrhs lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
              apply lintegral_mono_set
              exact fun lam hlam => lt_of_lt_of_le hlam₀pos hlam
  -- Bound the LOW λ-integral via `gehring_scalar_lc`.
  have hlow_eval : ∫⁻ lam in Set.Ioo (0:ℝ) lam₀, Wlow * ENNReal.ofReal (lam ^ (ε - 1))
      = Wlow * ENNReal.ofReal (lam₀ ^ ε / ε) := by
    rw [lintegral_const_mul' _ _ hWlowtop, gehring_scalar_lc lam₀ hlam₀0 ε hεpos]
  rw [hlow_eval] at hsplit
  -- Assemble: `Ž_N(t) = ε·∫_{Ioi 0} Inner·g ≤ ε·(LOW + HIGH)`.
  rw [show (∫⁻ lam in Set.Ioi (0:ℝ), Inner lam * ENNReal.ofReal (lam ^ (ε - 1)))
      = ∫⁻ lam in Set.Ioi (0:ℝ),
        (∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q)
          * ENNReal.ofReal (lam ^ (ε - 1)) from rfl]
  refine le_trans (mul_le_mul_right hsplit _) ?_
  rw [mul_add]
  apply add_le_add
  · -- `ε·(Wlow·lam₀^ε/ε) = ofReal(lam₀^ε)·Wlow`.
    rw [← mul_assoc, mul_comm (ENNReal.ofReal ε) Wlow, mul_assoc]
    apply le_of_eq
    rw [show ENNReal.ofReal ε * ENNReal.ofReal (lam₀ ^ ε / ε) = ENNReal.ofReal (lam₀ ^ ε) from by
      rw [← ENNReal.ofReal_mul hεpos.le]
      congr 1; field_simp]
    ring
  -- HIGH part: the existing reconstruction (identical to the previous assembly proof).
  simp only [hGLrhsdef]
  -- Distribute (A+B)*g into A*g + B*g pointwise on Ioi 0, then split the integral.
  have hpw : ∀ lam : ℝ, lam ∈ Set.Ioi (0:ℝ) →
      (ENNReal.ofReal (Cw * lam ^ (q - 1))
          * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
        + ENNReal.ofReal Cb
          * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q))
        * ENNReal.ofReal (lam ^ (ε - 1))
      = ENNReal.ofReal Cw *
            ((∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
              * ENNReal.ofReal (lam ^ ((q + ε - 1) - 1)))
        + ENNReal.ofReal Cb *
            ((∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q)
              * ENNReal.ofReal (lam ^ (ε - 1))) := by
    intro lam hlam
    have hlampos : 0 < lam := hlam
    rw [add_mul]
    congr 1
    · rw [show ENNReal.ofReal (Cw * lam ^ (q - 1))
              = ENNReal.ofReal Cw * ENNReal.ofReal (lam ^ (q - 1)) from by
            rw [← ENNReal.ofReal_mul hCw]]
      rw [show (q + ε - 1) - 1 = (q - 1) + (ε - 1) by ring]
      rw [Real.rpow_add hlampos, ENNReal.ofReal_mul (Real.rpow_nonneg hlampos.le _)]
      ring
    · ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpw]
  -- Split the integral.
  rw [lintegral_add_left' ?_]
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- w-term reconstruction: `θ := (min w N).toReal` (TRUNCATED level), `D := w` (FULL integrand).
    rw [gehring_recon hqε1 hβ0 hwmeas (hwmeas.min aemeasurable_const).ennreal_toReal
          (fun z => ENNReal.toReal_nonneg) x₀ s]
    rw [gehring_recon hεpos hβ0 (hbmeas.pow_const q) hbmeas.ennreal_toReal
          (fun z => ENNReal.toReal_nonneg) x₀ s]
    -- The crux comparison: `∫ w·ofReal((min w N).toReal^{q+ε-1}) ≤ ∫ w^q·(min w N)^ε = Ž_N(s)`.
    have hwid : ∫⁻ z in Metric.ball x₀ s,
          w z * ENNReal.ofReal ((min (w z) (N:ℝ≥0∞)).toReal ^ (q + ε - 1))
        ≤ ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε := by
      apply lintegral_mono
      intro z
      exact gehring_crux_le hq hεpos.le (w z) N
    have hbid : ∫⁻ z in Metric.ball x₀ s, b z ^ q * ENNReal.ofReal ((b z).toReal ^ ε)
        ≤ ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) := by
      apply lintegral_mono_ae
      filter_upwards with z
      rcases eq_or_ne (b z) ⊤ with hbtop | hbfin
      · rw [hbtop]
        simp only [ENNReal.toReal_top, Real.zero_rpow hεpos.ne', ENNReal.ofReal_zero, mul_zero]
        exact zero_le _
      · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hεpos.le,
          ENNReal.ofReal_toReal hbfin]
        rw [← ENNReal.rpow_add_of_nonneg q ε hq0.le hεpos.le]
    calc ENNReal.ofReal ε *
            (ENNReal.ofReal Cw * (ENNReal.ofReal (1 / ((q + ε - 1) * β ^ (q + ε - 1)))
                * ∫⁻ z in Metric.ball x₀ s,
                    w z * ENNReal.ofReal ((min (w z) (N:ℝ≥0∞)).toReal ^ (q + ε - 1)))
              + ENNReal.ofReal Cb * (ENNReal.ofReal (1 / (ε * β ^ ε))
                * ∫⁻ z in Metric.ball x₀ s, b z ^ q * ENNReal.ofReal ((b z).toReal ^ ε)))
        ≤ ENNReal.ofReal ε *
            (ENNReal.ofReal Cw * (ENNReal.ofReal (1 / ((q + ε - 1) * β ^ (q + ε - 1)))
                * ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
              + ENNReal.ofReal Cb * (ENNReal.ofReal (1 / (ε * β ^ ε))
                * ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε))) := by gcongr
      _ = ENNReal.ofReal (Cw / ((q + ε - 1) * β ^ (q + ε - 1)) * ε)
              * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
            + ENNReal.ofReal (Cb / β ^ ε) * (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε)) := by
          have triple : ∀ (a bb c : ℝ) (I : ℝ≥0∞), 0 ≤ a → 0 ≤ bb →
              ENNReal.ofReal a * (ENNReal.ofReal bb * (ENNReal.ofReal c * I))
                = ENNReal.ofReal (a * bb * c) * I := by
            intro a bb c I ha hb
            rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul ha,
              ← ENNReal.ofReal_mul (by positivity)]
          rw [mul_add, triple ε Cw _ _ hεpos.le hCw, triple ε Cb _ _ hεpos.le hCb]
          have e1 : ε * Cw * (1 / ((q + ε - 1) * β ^ (q + ε - 1)))
              = Cw / ((q + ε - 1) * β ^ (q + ε - 1)) * ε := by ring
          have e2 : ε * Cb * (1 / (ε * β ^ ε)) = Cb / β ^ ε := by
            rw [eq_div_iff (by positivity : β ^ ε ≠ 0)]; field_simp
          rw [e1, e2]
  · -- AEMeasurable of the w-summand: (antitone level-integral) * ofReal(λ^{p-1}).
    have hanti : Antitone (fun lam : ℝ =>
        ∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z) := by
      intro a c hac
      apply lintegral_mono_set
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hmul : β * a ≤ β * c := mul_le_mul_of_nonneg_left hac hβ0.le
      exact lt_of_le_of_lt hmul hz.2
    have hmeas1 : Measurable (fun lam : ℝ =>
        ∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z) :=
      hanti.measurable
    have hmeasrpow : Measurable (fun lam : ℝ => ENNReal.ofReal (lam ^ ((q + ε - 1) - 1))) := by
      apply ENNReal.measurable_ofReal.comp; fun_prop
    exact ((measurable_const.mul (hmeas1.mul hmeasrpow)).aemeasurable).restrict

private theorem gehring_toReal_conv {q κ κ' ε Cb β : ℝ} {w b : ℂ → ℝ≥0∞} {x₀ : ℂ}
    {Wmaster Bmaster t s : ℝ}
    (N : ℕ)
    (hκ'κ : κ' ≤ κ) (hκ'0 : 0 ≤ κ') (hε0 : 0 ≤ ε) (hCbβ0 : 0 ≤ Cb / β ^ ε)
    (_hWmaster0 : 0 ≤ Wmaster)
    (_hst : 0 < s - t)
    -- THRESHOLD-SPLIT low collar term `Low = ofReal(lam₀^ε)·Wlow`:
    (Low : ℝ≥0∞) (hLowfin : Low ≠ ⊤)
    -- finiteness:
    (_hXfin : ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε ≠ ⊤)
    (hYfin : ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε ≠ ⊤)
    (hZbfin : ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) ≠ ⊤)
    -- Bmaster bound: Zb.toReal ≤ Bmaster
    (hZbBm : (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε)).toReal ≤ Bmaster)
    -- the ENNReal inequality (from the THRESHOLD-SPLIT assembly):
    (hENN : ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
      ≤ Low + (ENNReal.ofReal (κ' * ε)
          * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
        + ENNReal.ofReal (Cb / β ^ ε) * (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε))))
    -- C₁ chosen large: covers both the `b`-forcing AND the low collar.
    (C₁ : ℝ) (hC₁ : Cb / β ^ ε ≤ C₁) (hC₁0 : 0 ≤ C₁)
    (hLowbd : Low.toReal ≤ C₁ * Wmaster / (s - t) ^ (2 : ℝ)) :
    (∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
      ≤ (κ * ε) * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
        + C₁ * Wmaster / (s - t) ^ (2 : ℝ) + C₁ * Bmaster := by
  set X := ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N:ℝ≥0∞)) ^ ε with hXdef
  set Y := ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N:ℝ≥0∞)) ^ ε with hYdef
  set Zb := ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) with hZbdef
  -- toReal-monotone applied to hENN.
  have hmono := ENNReal.toReal_mono ?_ hENN
  · -- bound RHS toReal
    rw [ENNReal.toReal_add hLowfin (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)] at hmono
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal hCbβ0] at hmono
    -- hmono : X.toReal ≤ Low.toReal + (κ'ε * Y.toReal + (Cb/βε) * Zb.toReal)
    have hYnn : 0 ≤ Y.toReal := ENNReal.toReal_nonneg
    have hwterm : (κ' * ε) * Y.toReal ≤ (κ * ε) * Y.toReal :=
      mul_le_mul_of_nonneg_right (by nlinarith [hκ'κ, hε0]) hYnn
    have hbterm : (Cb / β ^ ε) * Zb.toReal ≤ C₁ * Bmaster :=
      mul_le_mul hC₁ hZbBm ENNReal.toReal_nonneg hC₁0
    calc X.toReal ≤ Low.toReal + ((κ' * ε) * Y.toReal + (Cb / β ^ ε) * Zb.toReal) := hmono
      _ ≤ (κ * ε) * Y.toReal + C₁ * Wmaster / (s - t) ^ (2 : ℝ) + C₁ * Bmaster := by linarith
  · -- finiteness of RHS for toReal_mono
    exact ENNReal.add_ne_top.mpr ⟨hLowfin, ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYfin,
       ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZbfin⟩⟩

-- The hole-fill lemma: assembles pillars + good-λ + toReal into the ∃ C₁ shape.
set_option maxHeartbeats 400000 in
-- Large but elementary threshold/collar bookkeeping; a modest heartbeat bump avoids spurious
-- `whnf` timeouts on the heavy `(∫⁻…).toReal` master-mass terms.
private theorem gehring_holeFill {q A ε : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    (hεpos : 0 < ε) (hεle : ε ≤ 1)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (x₀ : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (κ Cw Cb β : ℝ) (hCw : 0 ≤ Cw) (hCb : 0 ≤ Cb) (hβ0 : 0 < β) (hβ1 : β < 1)
    -- the κ'≤κ constant fit:
    (hκfit : Cw / ((q + ε - 1) * β ^ (q + ε - 1)) ≤ κ) (_hκ0 : 0 ≤ κ)
    -- master finiteness:
    (hWmaster0 : 0 ≤ (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
    (hWfin16 : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (hbfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) < ⊤)
    -- the honest, COLLAR-FREE exponent-1 good-λ (FULL `w^q` LHS, TRUNCATED super-level RHS w-mass),
    -- valid on the HIGH range `⨍_{ball s} w^q ≤ (ofReal lam)^q` (i.e. `lam ≥ lam₀`) AND above the
    -- structural collar-killing threshold `5·√Wmaster ≤ (s−t)·lam^{q/2}` (i.e. `lam ≥ lam₁`):
    (hGL : ∀ (N : ℕ) (t s : ℝ), 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ → ∀ lam : ℝ, 0 < lam →
      (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q →
      5 * Real.sqrt ((∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
          ≤ (s - t) * lam ^ (q / 2) →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
          + ENNReal.ofReal Cb
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q)) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ N : ℕ, ∀ t s : ℝ, 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ →
      (∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
        ≤ (κ * ε) * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
          + C₁ * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal / (s - t) ^ (2 : ℝ)
          + C₁ * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)).toReal := by
  have hq0 : 0 < q := lt_trans one_pos hq
  have hqε0 : 0 < q + ε := by linarith
  have hqε1 : 0 < q + ε - 1 := by linarith
  set Wmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hWmasterdef
  set Bmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)).toReal with hBmasterdef
  -- The volume of `ball (4R₀)` is the smallest among `ball s` for `s ≥ 4R₀`; it gives the
  -- structural lower bound on `vol(ball s)` that bounds the threshold `lam₀^ε`.
  have hvolB4 : (0:ℝ) < Real.pi * (4 * R₀) ^ 2 := by positivity
  -- The collar constant `C₁`: covers the `b`-forcing `Cb/βε`, the low (`lam₀`) collar
  -- `lam₀^ε·Wmaster ≤ Cthr·Wmaster/(s-t)²` (using `lam₀^ε ≤ (Wmaster/vol(ball 4R₀))^{ε/q}` and
  -- `(s-t) ≤ 12R₀`), AND the collar-killing (`lam₁`) collar
  -- `lam₁^ε·(s-t)² ≤ (12R₀)² + 25·Wmaster =: Cthr1` (since `lam₁^q = 25Wmaster/(s-t)²` and
  -- `lam₁^ε ≤ 1 + lam₁^q`).  `C₁ := max (Cb/βε) (max Cthr Cthr1)`.
  set Cthr : ℝ :=
    (12 * R₀) ^ (2:ℝ) * (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) with hCthrdef
  have hCthr0 : 0 ≤ Cthr := by rw [hCthrdef]; positivity
  set Cthr1 : ℝ := (12 * R₀) ^ 2 + 25 * Wmaster with hCthr1def
  have hCthr10 : 0 ≤ Cthr1 := by rw [hCthr1def]; positivity
  set C₁ : ℝ := max (Cb / β ^ ε) (max Cthr Cthr1) with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_trans (div_nonneg hCb (by positivity)) (le_max_left _ _)
  have hC₁ge : Cb / β ^ ε ≤ C₁ := le_max_left _ _
  have hCthrge : Cthr ≤ C₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCthr1ge : Cthr1 ≤ C₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C₁, hC₁0, ?_⟩
  intro N t s ht hts hs
  have hst : 0 < s - t := by linarith
  have hst12 : s - t ≤ 12 * R₀ := by linarith
  -- per-N finiteness of the `Ž_N`-masses (`Ž_N(r) = ∫ w^q·(min w N)^ε ≤ N^ε·∫ w^q < ⊤`).
  have hNfin : ∀ r : ℝ, r ≤ 16 * R₀ →
      ∫⁻ z in Metric.ball x₀ r, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε ≠ ⊤ := by
    intro r hr
    have hbd : ∫⁻ z in Metric.ball x₀ r, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
        ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q := by
      calc ∫⁻ z in Metric.ball x₀ r, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
          ≤ ∫⁻ z in Metric.ball x₀ r, w z ^ q * (N : ℝ≥0∞) ^ ε := by
            apply lintegral_mono; intro z
            exact mul_le_mul_right (ENNReal.rpow_le_rpow (min_le_right _ _) hεpos.le) _
        _ = (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ r, w z ^ q := by
            rw [← lintegral_const_mul' _ _ (by
              exact (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N)).ne)]
            apply lintegral_congr_ae; filter_upwards with z; rw [mul_comm]
        _ ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q :=
            mul_le_mul_right (lintegral_mono_set (Metric.ball_subset_ball hr)) _
    refine (lt_of_le_of_lt hbd ?_).ne
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N))
      hWfin16
  -- Bmaster bound: Zb(s).toReal ≤ Bmaster.
  have hZbBm : (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε)).toReal ≤ Bmaster := by
    rw [hBmasterdef]
    apply ENNReal.toReal_mono hbfin.ne
    exact lintegral_mono_set (Metric.ball_subset_ball (by linarith))
  -- finiteness of ∫_{B_s} b^{q+ε}.
  have hZbsfin : ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) ≠ ⊤ := by
    refine (lt_of_le_of_lt (lintegral_mono_set (Metric.ball_subset_ball (by linarith))) hbfin).ne
  -- ===== THRESHOLD SETUP =====
  -- The finite `w^q`-mass and average over `ball s` (a sub-ball of `16B₀`).
  have hWsfin : ∫⁻ z in Metric.ball x₀ s, w z ^ q ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono_set (Metric.ball_subset_ball (by linarith))) hWfin16).ne
  have hvolBs_pos : 0 < volume (Metric.ball x₀ s) := Metric.measure_ball_pos _ _ (by linarith)
  have hvolBs_ne : volume (Metric.ball x₀ s) ≠ 0 := hvolBs_pos.ne'
  have hvolBs_top : volume (Metric.ball x₀ s) ≠ ⊤ := measure_ball_lt_top.ne
  -- the average is finite.
  set Av : ℝ≥0∞ := ⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume with hAvdef
  have hAvfin : Av ≠ ⊤ := by
    rw [hAvdef, setLAverage_eq]
    exact ENNReal.div_ne_top hWsfin hvolBs_ne
  -- the average threshold `lamA = Av.toReal^{1/q}` (real, ≥ 0), with `(ofReal lamA)^q = Av`.
  set lamA : ℝ := Av.toReal ^ (1 / q) with hlamAdef
  have hAvnn : 0 ≤ Av.toReal := ENNReal.toReal_nonneg
  have hlamA0 : 0 ≤ lamA := by rw [hlamAdef]; positivity
  have hlamApow : lamA ^ q = Av.toReal := by
    rw [hlamAdef, ← Real.rpow_mul hAvnn, one_div, inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  have hlamAq : (ENNReal.ofReal lamA) ^ q = Av := by
    rw [ENNReal.ofReal_rpow_of_nonneg hlamA0 hq0.le, hlamApow, ENNReal.ofReal_toReal hAvfin]
  -- the collar-killing threshold `lamC = (5·√Wmaster/(s−t))^{2/q}` (real, ≥ 0), with
  -- `5·√Wmaster ≤ (s−t)·lamC^{q/2}` (with equality), so `hλ₁` holds for `lam ≥ lamC`.
  set lamC : ℝ := (5 * Real.sqrt Wmaster / (s - t)) ^ (2 / q) with hlamCdef
  have hWmsqrt0 : 0 ≤ 5 * Real.sqrt Wmaster / (s - t) := by positivity
  have hlamC0 : 0 ≤ lamC := by rw [hlamCdef]; positivity
  have hlamCq2 : lamC ^ (q / 2) = 5 * Real.sqrt Wmaster / (s - t) := by
    rw [hlamCdef, ← Real.rpow_mul hWmsqrt0]
    rw [show (2 / q) * (q / 2) = 1 by field_simp, Real.rpow_one]
  -- Make `lamC` and `lamA` opaque (their bodies are nested rpow's of heavy `.toReal`/`setLAverage`
  -- terms; downstream `nlinarith`/`positivity`/`isDefEq` only need `hlam{A,C}0`/`hlam{A,C}q2`, so
  -- keeping the bodies transparent triggers spurious `whnf` blowups).
  clear_value lamC lamA
  -- the combined assembly threshold `lam₀ = max lamA lamC ≥ 0`.
  set lam₀ : ℝ := max lamA lamC with hlam₀def
  have hlam₀0 : 0 ≤ lam₀ := le_trans hlamA0 (le_max_left _ _)
  have hlamAle : lamA ≤ lam₀ := le_max_left _ _
  have hlamCle : lamC ≤ lam₀ := le_max_right _ _
  clear_value lam₀
  -- Wlow = the master `w^q`-mass over `ball t ⊆ 16B₀`, an upper bound for every super-level mass.
  set Wlow : ℝ≥0∞ := ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q with hWlowdef
  have hWlowtop : Wlow ≠ ⊤ := hWfin16.ne
  have hWlowbound : ∀ lam : ℝ, 0 < lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q ≤ Wlow := by
    intro lam _
    rw [hWlowdef]
    calc ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ∫⁻ z in Metric.ball x₀ t, w z ^ q := lintegral_mono_set Set.inter_subset_left
      _ ≤ ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q :=
          lintegral_mono_set (Metric.ball_subset_ball (by linarith))
  -- The good-λ as consumed by the assembly: valid for `lam ≥ lam₀`.
  have hGLhigh : ∀ lam : ℝ, 0 < lam → lam₀ ≤ lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
          + ENNReal.ofReal Cb
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q) := by
    intro lam hlam hlamge
    refine hGL N t s ht hts hs lam hlam ?_ ?_
    · -- average condition: `lam ≥ lamA`.
      rw [← hAvdef, ← hlamAq]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_trans hlamAle hlamge)) hq0.le
    · -- collar-killing condition: `5√Wmaster ≤ (s−t)·lam^{q/2}` from `lam ≥ lamC`.
      have hlamCge : lamC ≤ lam := le_trans hlamCle hlamge
      have hpowmono : lamC ^ (q / 2) ≤ lam ^ (q / 2) :=
        Real.rpow_le_rpow hlamC0 hlamCge (by positivity)
      calc 5 * Real.sqrt Wmaster = (s - t) * lamC ^ (q / 2) := by
            rw [hlamCq2]; field_simp
        _ ≤ (s - t) * lam ^ (q / 2) := by
            apply mul_le_mul_of_nonneg_left hpowmono hst.le
  -- ENNReal inequality from the THRESHOLD-SPLIT assembly.
  have hENN := gehring_assembly hq hA hεpos hεle hwmeas hbmeas x₀ R₀ hR₀ Cw Cb β hCw hCb hβ0 hβ1
    N t s ht hts hs lam₀ hlam₀0 Wlow hWlowtop hWlowbound hGLhigh
  -- toReal conversion (κ' := Cw/((q+ε-1)β^{q+ε-1})).
  have hκ'0 : (0:ℝ) ≤ Cw / ((q + ε - 1) * β ^ (q + ε - 1)) := by
    apply div_nonneg hCw; positivity
  have hCbβ0 : (0:ℝ) ≤ Cb / β ^ ε := div_nonneg hCb (by positivity)
  -- The low collar bound: `Low = ofReal(lam₀^ε)·Wlow`, and `Low.toReal ≤ C₁·Wmaster/(s-t)²`.
  set Low : ℝ≥0∞ := ENNReal.ofReal (lam₀ ^ ε) * Wlow with hLowdef
  have hLowfin : Low ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWlowtop
  have hLowbd : Low.toReal ≤ C₁ * Wmaster / (s - t) ^ (2 : ℝ) := by
    -- `Low.toReal = lam₀^ε·Wmaster`, and `lam₀ = max lamA lamC`.
    have hWlowReal : Wlow.toReal = Wmaster := by rw [hWlowdef, hWmasterdef]
    have hLowtoReal : Low.toReal = lam₀ ^ ε * Wmaster := by
      rw [hLowdef, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hWlowReal]
    rw [hLowtoReal]
    -- helper: `(s-t)^{2:ℝ} = (s-t)^2` (natural-power), positive.
    have hst2pos : 0 < (s - t) ^ (2:ℝ) := Real.rpow_pos_of_pos hst 2
    have hst2eq : (s - t) ^ (2:ℝ) = (s - t) ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    -- SUFFICES: `lam₀^ε · (s-t)² ≤ C₁`.
    suffices hsuff : lam₀ ^ ε * (s - t) ^ (2:ℝ) ≤ C₁ by
      rw [le_div_iff₀ hst2pos]
      calc lam₀ ^ ε * Wmaster * (s - t) ^ (2:ℝ)
          = (lam₀ ^ ε * (s - t) ^ (2:ℝ)) * Wmaster := by ring
        _ ≤ C₁ * Wmaster := mul_le_mul_of_nonneg_right hsuff hWmaster0
    -- (A) the average part `lamA^ε·(s-t)² ≤ Cthr`.
    have hAvbd : Av.toReal ≤ Wmaster / (Real.pi * (4 * R₀) ^ 2) := by
      rw [hAvdef, setLAverage_eq, ENNReal.toReal_div]
      apply div_le_div₀ ENNReal.toReal_nonneg ?_ hvolB4 ?_
      · change (∫⁻ z in Metric.ball x₀ s, w z ^ q).toReal ≤ Wmaster
        rw [hWmasterdef]
        apply ENNReal.toReal_mono hWfin16.ne
        exact lintegral_mono_set (Metric.ball_subset_ball (by linarith))
      · rw [Complex.volume_ball]
        have hpi : (↑NNReal.pi : ℝ≥0∞).toReal = Real.pi := by
          rw [← NNReal.coe_real_pi]; simp
        have hs0 : (0:ℝ) ≤ s := by linarith
        rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow hs0, ENNReal.toReal_ofReal (by positivity),
          hpi]
        have h4Rs : 4 * R₀ ≤ s := by linarith only [ht, hst.le]
        have hsq : (4 * R₀) ^ 2 ≤ s ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) h4Rs
        rw [mul_comm (s^2) Real.pi]
        exact mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
    have hlamAε : lamA ^ ε = Av.toReal ^ (ε / q) := by
      rw [hlamAdef, ← Real.rpow_mul hAvnn]; congr 1; ring
    have hbase_le : Av.toReal ≤ Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1 :=
      le_trans hAvbd (by linarith)
    have hpow_le : Av.toReal ^ (ε / q) ≤ (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) :=
      Real.rpow_le_rpow hAvnn hbase_le (by positivity)
    have hAcollar : lamA ^ ε * (s - t) ^ (2:ℝ) ≤ Cthr := by
      rw [hlamAε, hCthrdef]
      calc Av.toReal ^ (ε / q) * (s - t) ^ (2:ℝ)
          ≤ (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) * (s - t) ^ (2:ℝ) :=
            mul_le_mul_of_nonneg_right hpow_le hst2pos.le
        _ ≤ (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) * (12 * R₀) ^ (2:ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow hst.le hst12 (by norm_num)
        _ = (12 * R₀) ^ (2:ℝ) * (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) := by ring
    -- (B) the collar-killing part `lamC^ε·(s-t)² ≤ Cthr1`.
    -- `lamC^q = (5√Wm/(s-t))²` (from `lamC^{q/2} = 5√Wm/(s-t)`).
    have hlamCqval : lamC ^ q = (5 * Real.sqrt Wmaster / (s - t)) ^ 2 := by
      have h2 : lamC ^ q = (lamC ^ (q / 2)) ^ 2 := by
        rw [← Real.rpow_natCast (lamC ^ (q/2)) 2, ← Real.rpow_mul hlamC0]
        norm_num
      rw [h2, hlamCq2]
    -- `lamC^q · (s-t)² = 25·Wmaster`.
    have hlamCq_mul : lamC ^ q * (s - t) ^ 2 = 25 * Wmaster := by
      rw [hlamCqval, div_pow, div_mul_cancel₀ _ (by positivity : ((s - t) ^ 2 : ℝ) ≠ 0),
        mul_pow, Real.sq_sqrt hWmaster0]; ring
    -- `lamC^ε ≤ 1 + lamC^q` (since `0 ≤ ε ≤ q`).
    have hlamCε_le : lamC ^ ε ≤ 1 + lamC ^ q := by
      rcases le_or_gt lamC 1 with hle | hgt
      · have hle1 : lamC ^ ε ≤ 1 := Real.rpow_le_one hlamC0 hle hεpos.le
        linarith only [Real.rpow_nonneg hlamC0 q, hle1]
      · have hle2 : lamC ^ ε ≤ lamC ^ q :=
          Real.rpow_le_rpow_of_exponent_le hgt.le (le_trans hεle (le_of_lt hq))
        linarith only [hle2]
    have hst2le : (s - t) ^ 2 ≤ (12 * R₀) ^ 2 := by
      apply pow_le_pow_left₀ hst.le hst12
    have hCcollar : lamC ^ ε * (s - t) ^ (2:ℝ) ≤ Cthr1 := by
      calc lamC ^ ε * (s - t) ^ (2:ℝ)
          ≤ (1 + lamC ^ q) * (s - t) ^ (2:ℝ) :=
            mul_le_mul_of_nonneg_right hlamCε_le hst2pos.le
        _ = (s - t) ^ 2 + lamC ^ q * (s - t) ^ 2 := by rw [hst2eq]; ring
        _ = (s - t) ^ 2 + 25 * Wmaster := by rw [hlamCq_mul]
        _ ≤ (12 * R₀) ^ 2 + 25 * Wmaster := by linarith only [hst2le]
        _ = Cthr1 := hCthr1def.symm
    -- Combine: `lam₀^ε = max(lamA^ε, lamC^ε)`, bounded by `max(Cthr,Cthr1) ≤ C₁`.
    have hmaxpow : lam₀ ^ ε = max (lamA ^ ε) (lamC ^ ε) := by
      rw [hlam₀def]
      rcases le_total lamA lamC with h | h
      · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow hlamA0 h hεpos.le)]
      · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow hlamC0 h hεpos.le)]
    rw [hmaxpow]
    rcases le_total (lamA ^ ε) (lamC ^ ε) with h | h
    · rw [max_eq_right h]; exact le_trans hCcollar hCthr1ge
    · rw [max_eq_left h]; exact le_trans hAcollar hCthrge
  exact gehring_toReal_conv (κ' := Cw / ((q + ε - 1) * β ^ (q + ε - 1)))
    (Wmaster := Wmaster) (Bmaster := Bmaster) N hκfit hκ'0
    hεpos.le hCbβ0 hWmaster0 hst Low hLowfin (hNfin t (by linarith)) (hNfin s hs) hZbsfin hZbBm hENN
    C₁ hC₁ge hC₁0 hLowbd


/-- **S2 (`gehring_selfImprovement`).** The **abstract Gehring reverse-Hölder
self-improvement lemma**, stated equation-agnostically so it is reusable.

Fix an exponent `q > 1` and a reverse-Hölder constant `A ≥ 0`. Then there is a *single*
exponent gain `ε > 0` — depending only on `q` and `A` (and the ambient dimension `2`) —
such that **every** nonnegative weight `w : ℂ → ℝ≥0∞` that is locally `Lᵠ` (together with a
lower-order term `b` locally `Lᵠ`) and satisfies the **reverse-Hölder inequality** on every
ball `B = ball x r` with the **fixed enlargement factor `4`** (`4B = ball x (4r)`),
`(⨍⁻_{B} wᵠ)^(1/q) ≤ A · ⨍⁻_{4B} w + (⨍⁻_{4B} bᵠ)^(1/q)`,
is self-improved to `w ∈ L^{q+ε}_loc`, quantitatively on every compact `K`:
`∫⁻_{K} w^{q+ε} < ⊤`. (Gehring's lemma is robust to any fixed enlargement `> 1`; the factor
`4` is the one produced by the asymmetric Sobolev–Poincaré chain in S1.)

**Uniformity of `ε`.** The gain is quantified *outside* the weight `w` (and `b`): it
depends only on the structural constants `q, A`. This is the precise classical statement
of Gehring's lemma, and is exactly what the Beltrami consumer needs (the cutoff fixed
points share one `A`, hence one `ε`).

This is the content underlying Gehring's lemma; the proof runs the good-λ /
stopping-time / Calderón–Zygmund decomposition through the Hardy–Littlewood maximal
function (`MeasureTheory.MB`, `HasWeakType.MB_one`, `hasStrongType_MB`), a Vitali
covering (`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`), and the
layer-cake formula (`lintegral_eq_lintegral_meas_lt`). -/
theorem gehring_selfImprovement {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      ∀ {w b : ℂ → ℝ≥0∞}, AEMeasurable w volume → AEMeasurable b volume →
        (∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ q < ⊤) →
        (∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, b z ^ (q + ε) < ⊤) →
        (∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
            ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
              ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q)) →
        ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ (q + ε) < ⊤ := by
  -- ===========================================================================
  -- DECOMPOSITION of the abstract Gehring self-improvement lemma into the four
  -- dependency-ordered nodes G0 (localization), G1 (good-λ / Calderón–Zygmund),
  -- G2 (layer-cake + ε-absorption) and G3 (glue), following the standard proof.
  --
  -- The structure is exactly the classical one: G1 is the genuine good-λ
  -- inequality produced by the maximal-function stopping decomposition + the
  -- Vitali covering + the per-ball reverse-Hölder hypothesis; G2 integrates G1
  -- against `λ^{ε-1}` via the layer-cake formula and absorbs the resulting
  -- `∫ w^{q+ε}` term on the left using `ε` small. G0 reduces the compact-set
  -- conclusion to a fixed enclosing ball, and G3 is the trivial glue. The output
  -- exponent gain `ε₀` is the one extracted by the absorption in G2: it is read off
  -- from the absorbed coefficient (the rate `κ`, fixed by `q, A`) as `ε₀ = 1/(2κ+1)`.
  -- ===========================================================================
  classical
  -- =========================================================================
  -- HONEST GAIN `ε₀`.  The absorption in G2 produces an absorbed coefficient
  -- `θ(ε) = κ·ε` (the hole-filling `θ` fed to `giaquinta_iteration`), where the
  -- absorption RATE `κ` depends ONLY on the structural data `q, A` (it is read off
  -- the good-λ covering constant, which is `w,b`-independent), NOT on `ε`.  So we
  -- can extract `κ` here — before `ε`, `w`, `b` enter — and set
  --   `ε₀ := 1 / (2κ + 1)`,
  -- which forces `θ = κ·ε ≤ κ·ε₀ = κ/(2κ+1) < 1/2 < 1` for every `ε ≤ ε₀`, so the
  -- Giaquinta absorption succeeds.  (The gain must scale with `1/κ`: for `ε` large the
  -- absorbed coefficient would exceed `1` and the absorption would fail.)  `κ` is a
  -- concrete closed form in `q, A`: with the
  -- collar-free good-λ constants `Cw = 256·Ã·lam^{q-1}`, `β = 1/(4Ã)` (`Ã = π^{1/q}A+1`),
  -- the absorbed rate `Cw/((q+ε−1)·β^{q+ε−1}) = 256·Ã·(4Ã)^{q+ε−1}/(q+ε−1)` is `≤`
  -- the ε-uniform `C₀/(q−1)` with `C₀ := 256·Ã·(4Ã)^q` (since `4Ã ≥ 4 > 1` makes
  -- `(4Ã)^{ε−1} ≤ 1` and `1/(q+ε−1) ≤ 1/(q−1)` for `ε ≤ 1`).
  -- =========================================================================
  have hq0' : 0 < q := lt_trans one_pos hq
  have hq1 : 0 < q - 1 := by linarith
  set Ãκ : ℝ := Real.pi ^ (1 / q) * A + 1 with hÃκdef
  have hÃκpos : 0 < Ãκ := by rw [hÃκdef]; positivity
  set C₀ : ℝ := 256 * Ãκ * (4 * Ãκ) ^ q with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; positivity
  set κ : ℝ := C₀ / (q - 1) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; exact div_pos hC₀pos hq1
  have hκ0 : 0 ≤ κ := hκpos.le
  set ε₀ : ℝ := 1 / (2 * κ + 1) with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; positivity
  -- For every `ε ≤ ε₀`, the absorbed coefficient `θ = κ·ε` is `< 1`.
  have hθlt1 : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → κ * ε < 1 := by
    intro ε hεpos hεle
    have h1 : κ * ε ≤ κ * ε₀ := mul_le_mul_of_nonneg_left hεle hκ0
    have h2 : κ * ε₀ = κ / (2 * κ + 1) := by rw [hε₀def]; ring
    have h3 : κ / (2 * κ + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hεpos hεle w b hwmeas hbmeas hwloc hbloc hRH
  -- The honest absorbed coefficient for this `ε`.
  have hθε : κ * ε < 1 := hθlt1 ε hεpos hεle
  have hκε0 : 0 ≤ κ * ε := by positivity
  -- ---------------------------------------------------------------------------
  -- G0 + G3 (localization + glue) — CLOSED.
  -- It suffices to prove the fixed-ball finiteness `∫⁻_{ball x₀ R₀} w^{q+ε} < ⊤`
  -- for every centre `x₀` and radius `R₀ > 0`: a compact `K` is bounded, hence
  -- contained in some ball `ball 0 R₀`, and `∫⁻_K ≤ ∫⁻_{ball 0 R₀}` by monotonicity.
  -- ---------------------------------------------------------------------------
  suffices hball : ∀ (x₀ : ℂ) (R₀ : ℝ), 0 < R₀ →
      ∫⁻ z in Metric.ball x₀ R₀, w z ^ (q + ε) < ⊤ by
    intro K hK
    obtain ⟨R₀, hR₀sub⟩ := hK.isBounded.subset_ball 0
    rcases le_or_gt R₀ 0 with hR₀ | hR₀
    · -- `R₀ ≤ 0` ⟹ `ball 0 R₀ = ∅` ⟹ `K = ∅`.
      have hKsub : K ⊆ (∅ : Set ℂ) := by
        intro z hz
        have := hR₀sub hz
        rwa [Metric.ball_eq_empty.mpr hR₀] at this
      rw [Set.subset_empty_iff.mp hKsub]; simp
    · calc ∫⁻ z in K, w z ^ (q + ε)
          ≤ ∫⁻ z in Metric.ball 0 R₀, w z ^ (q + ε) := lintegral_mono_set hR₀sub
        _ < ⊤ := hball 0 R₀ hR₀
  -- ---------------------------------------------------------------------------
  -- Fix the enclosing ball `B₀ = ball x₀ R₀` (`R₀ > 0`).
  -- ---------------------------------------------------------------------------
  intro x₀ R₀ hR₀
  -- Basic positivity facts about `q` and `ε` reused below.
  have hq0 : 0 < q := lt_trans one_pos hq
  have hqε0 : 0 < q + ε := by linarith
  -- ===========================================================================
  -- G1 (good-λ / Calderón–Zygmund) — the FIRST hard node.
  --
  -- The Giaquinta–Modica good-λ inequality at the heart of Gehring's lemma.  For
  -- a level `λ ≥ λ₀` the super-level `wᵠ`-mass over the master ball `4B₀` is
  -- controlled by a `λ^{q-1}`-weighted mass of `w` at EXPONENT ONE over a smaller
  -- super-level set, plus a super-level `bᵠ`-forcing:
  --   `∫_{{w>λ}∩4B₀} wᵠ  ≤  C · λ^{q-1} · ∫_{{w>βλ}∩16B₀} w
  --                           + C · ∫_{{b>βλ}∩16B₀} bᵠ`,
  -- with `0 < β < 1` and a FIXED constant `C` (depending only on `q`, `A` and the
  -- planar doubling/overlap constant).  Three features are load-bearing:
  --  * the exponent `1` on the right `w`-mass together with the `λ^{q-1}` factor
  --    make the G2 layer-cake absorbed coefficient `K(ε) = C·ε/((q+ε−1)·β^{q+ε−1})`
  --    tend to `0` as `ε → 0` (the ε-prefactor survives because the radial inner
  --    integral over `λ^{q+ε−2}` stays bounded, `q+ε−2 > −1`), so a FIXED `C` is
  --    absorbed for small `ε` — the constant need NOT shrink;
  --  * the forcing is a SUPER-LEVEL set of `b` at exponent `q`, not a λ-independent
  --    constant (which would make `∫_{λ₀}^∞ λ^{ε−1} dλ` diverge);
  --  * the threshold `λ₀ ~ (⨍_{4B₀} wᵠ)^{1/q}` is genuine: for `λ < λ₀` the
  --    inequality fails (as `λ → 0` the left side → `∫_{4B₀} wᵠ > 0` while the
  --    `λ^{q-1}`-weighted right `w`-term → `0`).
  --
  -- Mathematically this is the Calderón–Zygmund stopping decomposition of `wᵠ` at
  -- height `λ^q` on `4B₀` (`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`,
  -- `Set.Countable.measure_biUnion_le_lintegral`): each stopping ball `Bᵢ ⊆ 4B₀`
  -- has `⨍_{Bᵢ} wᵠ > λ^q`, and the per-ball reverse-Hölder inequality `hRH` on the
  -- enlargement `4Bᵢ ⊆ 16B₀` splits `Bᵢ` into `w`-dominated balls (`⨍_{4Bᵢ} w > cλ`,
  -- contributing the `λ^{q-1}·∫_{{w>βλ}} w` term) and `b`-dominated balls
  -- (`⨍_{4Bᵢ} bᵠ > c'λ^q`, contributing `∫_{{b>βλ}} bᵠ`).
  -- ===========================================================================
  -- The two finite forcing masses over the master super-ball `16B₀`, available from
  -- the loc-`Lᵠ` / loc-`L^{q+ε}` hypotheses; we expose their `.toReal` (real, finite)
  -- as the data `A`-/`B`-constants of the hole-filling inequality.
  have hWmaster : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall)
      (hwloc _ (isCompact_closedBall x₀ (16 * R₀)))
  have hBmaster : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall)
      (hbloc _ (isCompact_closedBall x₀ (16 * R₀)))
  set Wmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hWmasterdef
  set Bmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)).toReal with hBmasterdef
  have hWmaster0 : 0 ≤ Wmaster := ENNReal.toReal_nonneg
  have hBmaster0 : 0 ≤ Bmaster := ENNReal.toReal_nonneg
  -- =========================================================================
  -- G1 (good-λ / Calderón–Zygmund), in its HOLE-FILLING form.  The classical
  -- good-λ inequality, run over a chain of concentric
  -- radii `4R₀ ≤ t < s ≤ 16R₀` (the good-λ holds for every such pair because
  -- every ball satisfies `hRH`) and integrated against `λ^{ε-1}` via the
  -- layer-cake / Cavalieri formula, produces directly the hole-filling
  -- inequality that the Giaquinta–Giusti iteration lemma `giaquinta_iteration`
  -- consumes:  with the absorbed coefficient `θ = κ·ε < 1` (κ fixed by
  -- `q, A`), for every truncation level `N` and every `4R₀ ≤ t < s ≤ 16R₀`,
  --   `Z_N(t) ≤ (κ·ε)·Z_N(s) + C₁·Wmaster/(s−t)² + C₁·Bmaster`,
  -- where `Z_N(t) := (∫_{ball x₀ t}(min w N)^{q+ε}).toReal` is the truncated
  -- `(q+ε)`-mass, `C₁ ≥ 0` is a FIXED constant (independent of `N`, `t`, `s`),
  -- and `Wmaster, Bmaster` are the finite master forcing masses.  The exponent-1
  -- structure of the right `w`-mass is what makes `θ = κ·ε`, hence `< 1` for
  -- `ε ≤ ε₀`.
  --
  -- The Calderón–Zygmund COVERING CORE is `gehring_goodLambda_measure` (good-λ super-level
  -- measure bound via the Vitali/Carleson engine + Lebesgue differentiation
  -- `gehring_density_ball` + the planar doubling engine `gehring_engine_bound`):
  --   `vol {z∈ball x₀ t | lam < (min w N) z}
  --       ≤ ofReal((2(A+1)/lam)·16)·∫_{ball x₀ s} w
  --         + ofReal((2(A+1)/lam)^q·16)·∫_{ball x₀ s} bᵠ`.
  -- The layer-cake λ-integration of that
  -- bound (`holeFill_layerCake`) plus the ε-absorption upgrades the
  -- good-λ RHS from the FULL `∫_{ball s} w` to the SUPER-LEVEL-restricted
  -- `∫_{{w>βλ}∩ball s} (min w N)` so that the Tonelli reconstruction returns
  -- `Z_N(s)` (not the unbounded `∫_s w^p`); that upgrade uses the TWO-SIDED dyadic
  -- stopping `exists_dyadic_CZ_stopping` (`lam < ⨍_Q wᵠ ≤ 4 lam`, in
  -- `DyadicLebesgue`) to force `w ≈ min w N` on the selected cubes.
  -- The full-RHS good-λ alone is insufficient (its
  -- λ-integral over `(0,∞)` diverges, and the cap at `N` is not `N`-uniform).
  -- =========================================================================
  obtain ⟨C₁, hC₁0, holeFill⟩ :
      ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ N : ℕ, ∀ t s : ℝ, 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ →
        (∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
          ≤ (κ * ε) * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
            + C₁ * Wmaster / (s - t) ^ (2 : ℝ) + C₁ * Bmaster := by
    -- ε ≤ 1 (since ε ≤ ε₀ = 1/(2κ+1) ≤ 1).
    have hεle1 : ε ≤ 1 := le_trans hεle (by rw [hε₀def, div_le_one (by positivity)]; linarith)
    -- The honest COLLAR-FREE good-λ constants (depend only on q, A); `Ã = π^{1/q}A+1`,
    -- `Cw = 256Ã`, `Cb = 64(4Ã)^q`, `β = 1/(4Ã)` (exactly `gehring_goodLambda_integral_noCollar`).
    set P : ℝ := Real.pi ^ (1 / q) with hPdef
    have hPpos : 0 < P := by rw [hPdef]; positivity
    set Ã : ℝ := P * A + 1 with hÃdef
    have hÃpos : 0 < Ã := by rw [hÃdef]; positivity
    set Cw : ℝ := 256 * Ã with hCwdef
    set Cb : ℝ := 64 * (4 * Ã) ^ q with hCbdef
    set β : ℝ := 1 / (4 * Ã) with hβdef
    have hCwpos : 0 ≤ Cw := by rw [hCwdef]; positivity
    have hCbpos : 0 ≤ Cb := by rw [hCbdef]; positivity
    have hβpos : 0 < β := by rw [hβdef]; positivity
    have h4Ãgt1 : (1:ℝ) < 4 * Ã := by rw [hÃdef]; nlinarith [hPpos, hA]
    have h4Ãge1 : (1:ℝ) ≤ 4 * Ã := h4Ãgt1.le
    have hβ1 : β < 1 := by
      rw [hβdef, div_lt_one (by positivity)]; linarith [h4Ãgt1]
    -- The constant fit `κ' ≤ κ`.  `Cw/((q+ε−1)·β^{q+ε−1}) = 256Ã·(4Ã)^{q+ε−1}/(q+ε−1)`,
    -- and `(4Ã)^{ε−1} ≤ 1` (base `≥ 1`, exponent `≤ 0`), `1/(q+ε−1) ≤ 1/(q−1)`, so this is
    -- `≤ 256Ã·(4Ã)^q/(q−1) = C₀/(q−1) = κ`.
    have hκfit : Cw / ((q + ε - 1) * β ^ (q + ε - 1)) ≤ κ := by
      have hq1' : 0 < q - 1 := by linarith
      have hqε1' : 0 < q + ε - 1 := by linarith
      have hÃ4pos : (0:ℝ) < 4 * Ã := by positivity
      -- `β^{q+ε-1} = (4Ã)^{-(q+ε-1)}`, so `1/β^{q+ε-1} = (4Ã)^{q+ε-1}`.
      have hβpow : β ^ (q + ε - 1) = (4 * Ã) ^ (-(q + ε - 1)) := by
        rw [hβdef, Real.div_rpow (by norm_num) (by positivity), Real.one_rpow,
          Real.rpow_neg (by positivity), one_div]
      have hden_pos : 0 < (q + ε - 1) * β ^ (q + ε - 1) := by
        rw [hβpow]; positivity
      rw [hκdef, hC₀def, hCwdef, div_le_div_iff₀ hden_pos hq1', hβpow]
      -- LHS = 256Ã·(q-1), RHS = 256Ã(4Ã)^q·((q+ε-1)·(4Ã)^{-(q+ε-1)}).
      rw [Real.rpow_neg (by positivity)]
      have h4Ãqpos : (0:ℝ) < (4 * Ã) ^ q := Real.rpow_pos_of_pos hÃ4pos q
      have h4Ãqεpos : (0:ℝ) < (4 * Ã) ^ (q + ε - 1) := Real.rpow_pos_of_pos hÃ4pos _
      -- `(4Ã)^{ε-1} ≤ 1` (base ≥ 1, exponent ≤ 0), hence `(4Ã)^{q+ε-1} ≤ (4Ã)^q`.
      have hle1 : (4 * Ã) ^ (ε - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h4Ãge1 (by linarith [hεle1])
      have hqεle : (4 * Ã) ^ (q + ε - 1) ≤ (4 * Ã) ^ q := by
        rw [show q + ε - 1 = q + (ε - 1) by ring, Real.rpow_add hÃ4pos]
        calc (4 * Ã) ^ q * (4 * Ã) ^ (ε - 1) ≤ (4 * Ã) ^ q * 1 :=
              mul_le_mul_of_nonneg_left hle1 h4Ãqpos.le
          _ = (4 * Ã) ^ q := mul_one _
      -- RHS = 256Ã(4Ã)^q·(q+ε-1)/(4Ã)^{q+ε-1} ≥ 256Ã·(q+ε-1) ≥ 256Ã·(q-1).
      rw [show 256 * Ã * (4 * Ã) ^ q * ((q + ε - 1) * ((4 * Ã) ^ (q + ε - 1))⁻¹)
            = (256 * Ã * (q + ε - 1)) * ((4 * Ã) ^ q / (4 * Ã) ^ (q + ε - 1)) by
          rw [div_eq_mul_inv]; ring]
      have hfrac_ge1 : (1:ℝ) ≤ (4 * Ã) ^ q / (4 * Ã) ^ (q + ε - 1) :=
        (one_le_div₀ h4Ãqεpos).mpr hqεle
      have hstep : 256 * Ã * (q - 1) ≤ 256 * Ã * (q + ε - 1) := by nlinarith [hÃpos, hεpos]
      calc 256 * Ã * (q - 1) ≤ 256 * Ã * (q + ε - 1) := hstep
        _ = (256 * Ã * (q + ε - 1)) * 1 := by ring
        _ ≤ (256 * Ã * (q + ε - 1)) * ((4 * Ã) ^ q / (4 * Ã) ^ (q + ε - 1)) :=
            mul_le_mul_of_nonneg_left hfrac_ge1 (by positivity)
    -- The honest exponent-1 good-λ (STEP B).  It is assembled from the
    -- `Ž_N = ∫ w^q·(min w N)^ε`-layer-cake `gehring_mass_layerCake`, its
    -- reconstruction `gehring_recon` + the tail-killing pointwise comparison `gehring_crux_le`, the
    -- ε-absorption assembly `gehring_assembly`, the `.toReal` conversion `gehring_toReal_conv`, the
    -- hole-fill packaging `gehring_holeFill`, and the constant fit `hκfit`.  This `hGL` is the
    -- good-λ: the FULL (a-priori-integrable) `w^q`
    -- mass on the super-level set `{min w N > lam} ∩ ball t` is controlled by the
    -- `lam^{q-1}`-weighted
    -- FULL `w`-mass (exponent one) on the SUPER-LEVEL set `{min w N > β·lam} ∩ ball s`, plus a
    -- super-level `bᵠ`-forcing.  Crucially the RHS w-mass is the FULL `w` (no `min w N` truncation
    -- of the integrand) — this is exactly what the dyadic-CZ stopping + reverse-Hölder dichotomy +
    -- Carleson engine produce (no enlarged-ball maximal upper bound on `⨍ w` is required).
    -- The truncation `min w N` lives ONLY in the level set (truncated super-level), which on the
    -- active range `lam < N` agrees with `{w > β·lam}`; for `lam ≥ N` the LHS super-level set is
    -- empty so the inequality is trivial.  The over-truncation tail is handled
    -- by `gehring_crux_le` (the iterated quantity is `Ž_N = ∫ w^q·(min w N)^ε`, FINITE,
    -- with the truncation on the `ε`-factor only), NOT by truncating the good-λ RHS integrand.
    have hGL : ∀ (N : ℕ) (t s : ℝ), 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ → ∀ lam : ℝ, 0 < lam →
        (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q →
        5 * Real.sqrt ((∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
            ≤ (s - t) * lam ^ (q / 2) →
        ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
          ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
              * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
            + ENNReal.ofReal Cb
              * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q) := by
      intro N t' s' ht' hts' hs' lam hlampos hlam0cond hlam1cond
      -- The `min w N` level sets reduce to the FULL `w` level sets up to the null set `{w = ⊤}`
      -- exactly when `lam < N` (and `β·lam < lam < N`); the integral good-λ pillar then closes it.
      -- For `lam ≥ N` the LHS super-level set `{lam < (min w N).toReal}` is empty.
      have hWfin16 : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ := hWmaster
      classical
      -- `{w = ⊤} ∩ ball x₀ (16R₀)` is `volume`-null (`w^q` integrable there ⟹ `w < ⊤` a.e.).
      have hwtop_null : volume ({z : ℂ | w z = ⊤} ∩ Metric.ball x₀ (16 * R₀)) = 0 := by
        have htop :
            volume {z : ℂ | (Metric.ball x₀ (16 * R₀)).indicator (fun z => w z ^ q) z = ⊤} = 0 := by
          apply measure_eq_top_of_lintegral_ne_top
            ((hwmeas.pow_const q).indicator measurableSet_ball)
          rw [lintegral_indicator measurableSet_ball]; exact hWfin16.ne
        refine measure_mono_null ?_ htop
        intro z hz; simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hz ⊢
        rw [Set.indicator_of_mem hz.2, hz.1, ENNReal.top_rpow_of_pos (by linarith : (0:ℝ) < q)]
      -- The level-set equality up to `{w = ⊤}` (null on the ball), via symmetric-difference
      -- nullity.
      have hset_eq : ∀ (r c : ℝ), r ≤ 16 * R₀ → c < (N:ℝ) →
          (Metric.ball x₀ r ∩ {z : ℂ | c < (min (w z) (N:ℝ≥0∞)).toReal} : Set ℂ)
            =ᵐ[volume] (Metric.ball x₀ r ∩ {z : ℂ | c < (w z).toReal} : Set ℂ) := by
        intro r c hr hcN
        have hnull : volume ({z : ℂ | w z = ⊤} ∩ Metric.ball x₀ r) = 0 :=
          measure_mono_null (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hr)) hwtop_null
        rw [Filter.eventuallyEq_set, ae_iff]
        refine measure_mono_null
          (show {z : ℂ | ¬ (z ∈ Metric.ball x₀ r ∩ {z | c < (min (w z) (N:ℝ≥0∞)).toReal}
              ↔ z ∈ Metric.ball x₀ r ∩ {z | c < (w z).toReal})}
            ⊆ {z : ℂ | w z = ⊤} ∩ Metric.ball x₀ r from ?_) hnull
        intro z hz
        simp only [Set.mem_setOf_eq] at hz
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        by_cases hzr : z ∈ Metric.ball x₀ r
        · refine ⟨?_, hzr⟩
          by_contra hwtop
          apply hz
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hzr, true_and]
          rw [ENNReal.toReal_min hwtop (ENNReal.natCast_ne_top N), ENNReal.toReal_natCast]
          constructor
          · intro h2; exact lt_of_lt_of_le h2 (min_le_left _ _)
          · intro h2; exact lt_min h2 hcN
        · exact absurd (by simp only [Set.mem_inter_iff, hzr, false_and, iff_self]) hz
      -- `∫_{16B₀} b^q < ⊤` from the loc-`L^{q+ε}` master mass `hBmaster` (`b^q ≤ 1 + b^{q+ε}`).
      have hBfinq : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q < ⊤ := by
        have hbd : ∀ z, b z ^ q ≤ 1 + b z ^ (q + ε) := by
          intro z
          rcases le_total (b z) 1 with hle | hge
          · have : b z ^ q ≤ 1 := by
              rw [← ENNReal.one_rpow q]; exact ENNReal.rpow_le_rpow hle hq0.le
            exact le_trans this (le_add_right le_rfl)
          · have : b z ^ q ≤ b z ^ (q + ε) :=
              ENNReal.rpow_le_rpow_of_exponent_le hge (by linarith)
            exact le_trans this (le_add_left le_rfl)
        calc ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q
            ≤ ∫⁻ z in Metric.ball x₀ (16 * R₀), (1 + b z ^ (q + ε)) := lintegral_mono hbd
          _ = volume (Metric.ball x₀ (16 * R₀))
                + ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) := by
              rw [lintegral_add_left' aemeasurable_const, setLIntegral_const, one_mul]
          _ < ⊤ := ENNReal.add_lt_top.mpr ⟨measure_ball_lt_top, hBmaster⟩
      rcases lt_or_ge lam (N : ℝ) with hlamN | hlamN
      · -- `lam < N`: a.e. rewrite both `min w N` level sets to full `w` level sets.
        have hβlamN : β * lam < (N:ℝ) := by
          have : β * lam < lam := by
            rw [hβdef]
            calc 1 / (4 * Ã) * lam < 1 * lam := by
                  apply mul_lt_mul_of_pos_right _ hlampos
                  rw [div_lt_one (by positivity)]; linarith [h4Ãge1]
              _ = lam := one_mul lam
          linarith
        rw [setLIntegral_congr (hset_eq t' lam (by linarith) hlamN),
            setLIntegral_congr (hset_eq s' (β * lam) hs' hβlamN)]
        have hcall := gehring_goodLambda_integral_noCollar hq hA hwmeas hbmeas hRH x₀ R₀ hR₀
          hWfin16 hBfinq t' s' ht' hts' hs' lam hlampos hlam0cond hlam1cond
        -- The noCollar bound's constants/level match `Cw, Cb, β` (via `hÃdef`, `hβdef`, `hCwdef`,
        -- `hCbdef`); rewrite to identify them.
        rw [show (256 : ℝ) * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1) = Cw * lam ^ (q - 1) by
              rw [hCwdef, hÃdef, hPdef],
            show (64 : ℝ) * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q = Cb by rw [hCbdef, hÃdef, hPdef],
            show (1 : ℝ) / (4 * (Real.pi ^ (1 / q) * A + 1)) = β by
              rw [hβdef, hÃdef, hPdef]] at hcall
        exact hcall
      · -- `lam ≥ N`: the LHS super-level set is empty, so the LHS is `0`.
        have hempty :
            Metric.ball x₀ t' ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal} = (∅ : Set ℂ) := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨_, hlt⟩
          simp only [Set.mem_setOf_eq] at hlt
          have hle : (min (w z) (N:ℝ≥0∞)).toReal ≤ (N:ℝ) := by
            rcases eq_or_ne (w z) ⊤ with hwt | hwf
            · rw [hwt]; simp
            · rw [ENNReal.toReal_min hwf (ENNReal.natCast_ne_top N), ENNReal.toReal_natCast]
              exact min_le_right _ _
          linarith
        rw [hempty]; simp
    exact gehring_holeFill hq hA hεpos hεle1 hwmeas hbmeas x₀ R₀ hR₀ κ Cw Cb β
      hCwpos hCbpos hβpos hβ1 hκfit hκ0 hWmaster0 hWmaster hBmaster hGL
  -- ===========================================================================
  -- G2 (layer-cake + ε-absorption) — the SECOND hard node.
  --
  -- Multiply the MASTER-BALL good-λ inequality `goodLambda` by `λ^{ε-1}` and
  -- integrate in `λ ∈ (0,∞)`. By the layer-cake / Cavalieri representation
  -- (`lintegral_rpow_eq_lintegral_meas_lt_mul`) the left side reconstructs
  -- `∫_{4B₀} w^{q+ε}`, and — now that the good-λ RHS `wᵠ`-mass lives over the SAME
  -- master ball `4B₀` — the first right-hand term reconstructs into a term over
  -- `∫_{4B₀} w^{q+ε}` as well (Giaquinta–Modica iteration lemma); the absorbed
  -- coefficient is `< 1` for `ε ≤ ε₀` small, so the `∫_{4B₀} w^{q+ε}` term moves
  -- to the left, leaving
  --   `∫_{4B₀} w^{q+ε} ≲ ∫_{16B₀} wᵠ + ∫_{16B₀} b^{q+ε} < ⊤`,
  -- finite by the loc-`Lᵠ` hypothesis `hwloc` on `wᵠ` and the loc-`L^{q+ε}`
  -- hypothesis `hbloc` on `b`, both evaluated on the compact `closedBall x₀ (16 R₀)`.
  --
  -- The absorption is the only place the smallness of `ε` is used; it is what
  -- fixes the gain `ε₀`. This node consumes the master-ball `goodLambda`; the
  -- layer-cake bookkeeping and the absorption inequality live here.
  -- ===========================================================================
  have absorb : ∫⁻ z in Metric.ball x₀ R₀, w z ^ (q + ε) < ⊤ := by
    -- The forcing terms G2 produces on the right are finite, from the
    -- loc-`Lᵠ`/loc-`L^{q+ε}` hypotheses, evaluated on the
    -- compact super-ball `closedBall x₀ (16 R₀)` (which contains `16B₀`).
    -- `∫_{16B₀} wᵠ < ⊤` from `hwloc`.
    have hRHS_w : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ := by
      have hKc : IsCompact (Metric.closedBall x₀ (16 * R₀)) :=
        isCompact_closedBall x₀ (16 * R₀)
      exact lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall) (hwloc _ hKc)
    -- `∫_{16B₀} b^{q+ε} < ⊤` from `hbloc`.
    have hRHS_b : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) < ⊤ := by
      have hKc : IsCompact (Metric.closedBall x₀ (16 * R₀)) :=
        isCompact_closedBall x₀ (16 * R₀)
      exact lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall) (hbloc _ hKc)
    -- `B₀ ⊆ 4B₀`, so it suffices to bound `∫_{4B₀} w^{q+ε}`.
    have hsub : Metric.ball x₀ R₀ ⊆ Metric.ball x₀ (4 * R₀) :=
      Metric.ball_subset_ball (by linarith)
    refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
    -- =======================================================================
    -- CORE of G2: the layer-cake reconstruction + ε-absorption.
    --
    -- The node is a SINGLE absorbed linear bound of the target
    -- `∫_{4B₀} w^{q+ε}` by the two finite forcing masses `∫_{16B₀} wᵠ` and
    -- `∫_{16B₀} b^{q+ε}` (both `< ⊤`, supplied above as `hRHS_w`, `hRHS_b`) with
    -- a FINITE coefficient `K`, packaged as `hbound`; the finiteness wrapper around
    -- it (below) follows from `hRHS_w`, `hRHS_b`, `ENNReal.add_lt_top` and
    -- `ENNReal.mul_lt_top`.
    -- =======================================================================
    obtain ⟨K, hKfin, hbound⟩ :
        ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
          ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ (q + ε)
            ≤ K * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
              + K * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
      -- G2 — the Giaquinta–Giusti absorption, consuming the hole-filling
      -- inequality `holeFill` of the G1 node above through the iteration
      -- lemma `giaquinta_iteration`.
      -- =====================================================================
      -- RIGOROUS REDUCTION (fully discharged below): truncation + monotone
      -- convergence.  We reduce the target `hbound` for the genuine weight `w`
      -- to the SAME bound for the bounded truncations `w_N := min w N`,
      -- UNIFORMLY in `N`, via the monotone-convergence theorem.  Concretely:
      --   * `(min (w z) N)^{q+ε} ↑ (w z)^{q+ε}` pointwise as `N → ∞`
      --     (`min (w z) N ↑ w z`, and `·^{q+ε}` is monotone and continuous on
      --     `ℝ≥0∞`, so `iSup_eq_of_tendsto` gives the pointwise sup);
      --   * `lintegral_iSup'` exchanges the sup with `∫_{4B₀}`, identifying
      --     `∫_{4B₀} w^{q+ε} = ⨆ N, ∫_{4B₀} (min w N)^{q+ε}`;
      --   * with a single finite `K` for which every truncation obeys the
      --     bound (RHS independent of `N`), `iSup_le` collapses the sup.
      -- This isolates the analytic
      -- content into the per-`N` bounded absorbed bound `hboundN` below.
      -- =====================================================================
      -- Positivity of the reconstruction exponent (reused).
      have hqε0' : 0 ≤ q + ε := hqε0.le
      -- POINTWISE truncation sup of `Ž_N`: `⨆ N, w^q·(min (w z) N)^ε = w^{q+ε}`.
      have hptsup : ∀ z, ⨆ N : ℕ, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
          = w z ^ (q + ε) := by
        intro z
        -- `min (w z) ·` is monotone in the `ℕ`-truncation level.
        have hmin_mono : Monotone (fun n : ℕ => min (w z) (n : ℝ≥0∞)) := by
          intro a c hac; exact min_le_min_left _ (by exact_mod_cast hac)
        -- and its `ℕ`-sup is `w z` (the truncations exhaust `w z`).
        have hsup : ⨆ n : ℕ, min (w z) (n : ℝ≥0∞) = w z := by
          apply le_antisymm (iSup_le fun n => min_le_left _ _)
          apply le_of_forall_lt_imp_le_of_dense
          intro c hc
          obtain ⟨n, hn⟩ := exists_nat_gt c.toReal
          refine le_iSup_of_le n (le_min (le_of_lt hc) ?_)
          calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal (ne_top_of_lt hc)).symm
            _ ≤ ENNReal.ofReal n := ENNReal.ofReal_le_ofReal hn.le
            _ = (n : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast]
        -- `w^q · (·)^ε` is monotone (exponent `≥ 0`) and continuous in the truncation.
        have hmono : Monotone (fun n : ℕ => w z ^ q * (min (w z) (n : ℝ≥0∞)) ^ ε) :=
          fun a c hac => mul_le_mul_right (ENNReal.rpow_le_rpow (hmin_mono hac) hεpos.le) _
        have htend : Tendsto (fun n : ℕ => min (w z) (n : ℝ≥0∞)) atTop (𝓝 (w z)) := by
          have h := tendsto_atTop_iSup hmin_mono; rwa [hsup] at h
        have hcompε : Tendsto (fun n : ℕ => (min (w z) (n : ℝ≥0∞)) ^ ε) atTop
            (𝓝 ((w z) ^ ε)) :=
          (ENNReal.continuous_rpow_const.tendsto (w z)).comp htend
        have hside : (w z) ^ ε ≠ 0 ∨ w z ^ q ≠ ⊤ := by
          rcases eq_or_ne (w z) 0 with hw0 | hw0
          · right; rw [hw0, ENNReal.zero_rpow_of_pos hq0']; simp
          · left; rw [ne_eq, ENNReal.rpow_eq_zero_iff]; push Not
            exact ⟨fun h => absurd h hw0, fun _ => hεpos.le⟩
        have hcomp : Tendsto (fun n : ℕ => w z ^ q * (min (w z) (n : ℝ≥0∞)) ^ ε) atTop
            (𝓝 (w z ^ q * (w z) ^ ε)) :=
          ENNReal.Tendsto.const_mul hcompε hside
        rw [show w z ^ q * w z ^ ε = w z ^ (q + ε) from
          (ENNReal.rpow_add_of_nonneg q ε hq0'.le hεpos.le).symm] at hcomp
        exact iSup_eq_of_tendsto hmono hcomp
      -- Per-truncation measurability and monotonicity for `lintegral_iSup'`.
      have hmeasN : ∀ N : ℕ,
          AEMeasurable (fun z => w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
            (volume.restrict (Metric.ball x₀ (4 * R₀))) :=
        fun N => (hwmeas.restrict.pow_const _).mul
          ((hwmeas.restrict.min aemeasurable_const).pow_const _)
      have hmonoN : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (4 * R₀))),
          Monotone (fun N : ℕ => w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε) := by
        filter_upwards with z a c hac
        exact mul_le_mul_right
          (ENNReal.rpow_le_rpow (min_le_min_left _ (by exact_mod_cast hac)) hεpos.le) _
      -- MONOTONE CONVERGENCE: identify the target LHS with the sup of truncations.
      have hMCT : ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ (q + ε)
          = ⨆ N : ℕ, ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε := by
        rw [← lintegral_iSup' hmeasN hmonoN]
        exact lintegral_congr_ae (by filter_upwards with z using (hptsup z).symm)
      -- =====================================================================
      -- G2 absorption — the per-`N` bounded bound, UNIFORM in `N`, PROVEN here
      -- from the hole-filling residual `holeFill` via the PROVEN Giaquinta–Giusti
      -- iteration lemma `giaquinta_iteration`.
      --
      -- For each truncation level `N`, the truncated mass `Z_N(t) =
      -- (∫_{ball x₀ t}(min w N)^{q+ε}).toReal` is finite (bounded by `N^{q+ε}·vol`),
      -- nonnegative, and bounded by `M_N` on `[4R₀,16R₀]`, and `holeFill` supplies
      -- the hole-filling inequality `Z_N(t) ≤ (κ·ε)·Z_N(s) + C₁·Wmaster/(s−t)² +
      -- C₁·Bmaster` for every `4R₀ ≤ t < s ≤ 16R₀`, with the absorbed
      -- coefficient `θ = κ·ε < 1`.  The iteration lemma then collapses the chain,
      -- giving `Z_N(4R₀) ≤ cIter·(C₁·Wmaster/(12R₀)² + C₁·Bmaster)`, which is a
      -- single FIXED `N`-independent ENNReal bound `K·∫_{16B₀}wᵠ + K·∫_{16B₀}b^{q+ε}`
      -- after converting `Wmaster, Bmaster` back to their (finite) lintegrals.  The
      -- monotone-convergence collapse `hMCT` then removes the truncation.
      --
      -- The PROVEN Giaquinta–Giusti iteration constant `c = c(α, θ)` for `α = 2`,
      -- `θ = κ·ε < 1` (honest by `hθε`).  It depends only on `α, θ`, i.e. on `q, A, ε`.
      obtain ⟨cIter, hcIter0, hcIter⟩ := giaquinta_iteration (α := (2 : ℝ)) (θ := κ * ε)
        (by norm_num) hκε0 hθε
      -- Geometry: `12 R₀ = 16R₀ − 4R₀ > 0` and `(12R₀)² > 0`.
      have h12R₀ : (0 : ℝ) < 12 * R₀ := by linarith
      have hgapα : (0 : ℝ) < (16 * R₀ - 4 * R₀) ^ (2 : ℝ) := by
        have : (16 * R₀ - 4 * R₀) = 12 * R₀ := by ring
        rw [this]; exact Real.rpow_pos_of_pos h12R₀ 2
      -- The single finite, `N`-independent coefficient `K`.
      set K : ℝ≥0∞ := ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ)) +
                ENNReal.ofReal (cIter * C₁) with hKdef
      have hKfin : K ≠ ⊤ := by
        rw [hKdef]
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
      have hboundN : ∀ N : ℕ,
          ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
            ≤ K * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
              + K * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
        intro N
        -- `∫_{16B₀} w^q < ⊤` (master finiteness, from `hWmaster`).
        have hW16fin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ := hWmaster
        -- Per-`N` bound: `Ž_N(s) = ∫_{B_s} w^q·(min w N)^ε ≤ N^ε·∫_{16B₀} w^q` (`s ≤ 16R₀`).
        have hNbound : ∀ s : ℝ, s ≤ 16 * R₀ →
            ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
              ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q := by
          intro s hs16
          calc ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
              ≤ ∫⁻ z in Metric.ball x₀ s, w z ^ q * (N : ℝ≥0∞) ^ ε := by
                apply lintegral_mono; intro z
                exact mul_le_mul_right (ENNReal.rpow_le_rpow (min_le_right _ _) hεpos.le) _
            _ = (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ s, w z ^ q := by
                rw [← lintegral_const_mul' _ _ (by
                  exact (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N)).ne)]
                apply lintegral_congr_ae; filter_upwards with z; rw [mul_comm]
            _ ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q :=
                mul_le_mul_right (lintegral_mono_set (Metric.ball_subset_ball hs16)) _
        have hNfin : ∀ s : ℝ, s ≤ 16 * R₀ →
            ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε < ⊤ := by
          intro s hs16
          refine lt_of_le_of_lt (hNbound s hs16) ?_
          exact ENNReal.mul_lt_top
            (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N)) hW16fin
        -- The real-valued `Ž_N`.
        set ZN : ℝ → ℝ := fun t => (∫⁻ z in Metric.ball x₀ t,
          w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal with hZNdef
        have hZN0 : ∀ t ∈ Set.Icc (4 * R₀) (16 * R₀), 0 ≤ ZN t :=
          fun t _ => ENNReal.toReal_nonneg
        -- The uniform bound `M_N` on `[4R₀, 16R₀]` (`Ž_N(t) ≤ N^ε·∫_{16B₀}w^q` for `t ≤ 16R₀`).
        set MN : ℝ :=
          ((N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hMNdef
        have hZNbdd : ∀ t ∈ Set.Icc (4 * R₀) (16 * R₀), ZN t ≤ MN := by
          intro t ht
          rw [hZNdef, hMNdef]
          apply ENNReal.toReal_mono
          · exact ENNReal.mul_ne_top (ENNReal.rpow_lt_top_of_nonneg hεpos.le
              (ENNReal.natCast_ne_top N)).ne hW16fin.ne
          · exact hNbound t ht.2
        -- Apply the iteration lemma.
        have hZNiter := hcIter (Z := ZN) (r := 4 * R₀) (R := 16 * R₀)
          (A := C₁ * Wmaster) (B := C₁ * Bmaster) (M := MN)
          (by linarith) (mul_nonneg hC₁0 hWmaster0) (mul_nonneg hC₁0 hBmaster0)
          hZN0 hZNbdd
          (fun t s ht hts hs => by
            have := holeFill N t s ht hts hs
            simpa only [hZNdef] using this)
        -- `hZNiter : ZN (4R₀) ≤ cIter * (C₁ * Wmaster / (16R₀ - 4R₀)^2 + C₁ * Bmaster)`.
        -- Convert the LHS `ZN (4R₀)` back to the ENNReal target.
        have hround : ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
            = ENNReal.ofReal (ZN (4 * R₀)) := by
          rw [hZNdef, ENNReal.ofReal_toReal (hNfin (4 * R₀) (by linarith)).ne]
        rw [hround]
        -- RHS bound in ℝ.
        have hRHSreal : ZN (4 * R₀)
            ≤ cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster + cIter * C₁ * Bmaster := by
          calc ZN (4 * R₀)
              ≤ cIter * (C₁ * Wmaster / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) + C₁ * Bmaster) := hZNiter
            _ = cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster + cIter * C₁ * Bmaster := by
                rw [mul_add, mul_div_assoc']; ring
        -- The two master masses as ENNReal `ofReal` of their `.toReal`.
        have hWeq : ENNReal.ofReal Wmaster = ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q := by
          rw [hWmasterdef, ENNReal.ofReal_toReal hWmaster.ne]
        have hBeq : ENNReal.ofReal Bmaster = ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) := by
          rw [hBmasterdef, ENNReal.ofReal_toReal hBmaster.ne]
        -- Assemble the ENNReal bound.
        calc ENNReal.ofReal (ZN (4 * R₀))
            ≤ ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster
                + cIter * C₁ * Bmaster) := ENNReal.ofReal_le_ofReal hRHSreal
          _ = ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster)
                + ENNReal.ofReal (cIter * C₁ * Bmaster) := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          _ = ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ)) * ENNReal.ofReal Wmaster
                + ENNReal.ofReal (cIter * C₁) * ENNReal.ofReal Bmaster := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ))
                * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
                + ENNReal.ofReal (cIter * C₁)
                    * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
                rw [hWeq, hBeq]
          _ ≤ (ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ))
                  + ENNReal.ofReal (cIter * C₁))
                * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
                + (ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ))
                    + ENNReal.ofReal (cIter * C₁))
                * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
                gcongr <;> simp
      -- Collapse the monotone sup against the `N`-uniform bound.
      exact ⟨K, hKfin, by rw [hMCT]; exact iSup_le hboundN⟩
    refine lt_of_le_of_lt hbound (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hKfin) hRHS_w
    · exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hKfin) hRHS_b
  exact absorb

/-! ## S3 — the restated Beltrami higher-integrability residual -/

/-- **Auxiliary: local-`L²` ⟹ local lintegral finiteness of `‖·‖²`.** From `MemLp F 2`
the squared `ℝ≥0∞`-enorm has finite lower integral on every compact set — the
loc-`Lᵠ` hypothesis (with `q = 2`) that the Gehring lemma S2 consumes. -/
private theorem lintegral_enorm_sq_lt_top_of_memLp {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (K : Set ℂ) : ∫⁻ z in K, (‖F z‖₊ : ℝ≥0∞) ^ (2 : ℝ) < ⊤ := by
  have hFK : MemLp F 2 (volume.restrict K) := hF.restrict K
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hlt := hFK.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top] at hlt
  have htoReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [htoReal] at hlt
  have hbase : (∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂volume.restrict K) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop] at hlt
    simp only [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at hlt
    exact (lt_irrefl _ hlt)
  simpa only [enorm_eq_nnnorm] using hbase

/-- **Auxiliary: `MemLp F (ofReal s)` ⟹ local lintegral finiteness of `‖·‖^t` for
`0 < t ≤ s`.** From `MemLp F (ofReal s)`, on every compact `K` the `t`-th `ℝ≥0∞`-enorm
power has finite lower integral whenever `0 < t ≤ s`: restrict to `K` (a finite
measure on a compact set), drop the exponent to `ofReal t ≤ ofReal s` by
`MemLp.mono_exponent`, and unfold `eLpNorm`. This is the forcing-term finiteness the
corrected Gehring lemma S2 consumes at the higher integrability exponent `t = 2 + ε`,
supplied by the `δ = 1` datum `MemLp h 3` (`s = 3`). -/
private theorem lintegral_enorm_rpow_lt_top_of_memLp {F : ℂ → ℂ} {s t : ℝ}
    (ht0 : 0 < t) (hts : t ≤ s) (hF : MemLp F (ENNReal.ofReal s) volume)
    (K : Set ℂ) (hK : IsCompact K) : ∫⁻ z in K, (‖F z‖₊ : ℝ≥0∞) ^ t < ⊤ := by
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hFKs : MemLp F (ENNReal.ofReal s) (volume.restrict K) := hF.restrict K
  have hFKt : MemLp F (ENNReal.ofReal t) (volume.restrict K) :=
    hFKs.mono_exponent (ENNReal.ofReal_le_ofReal hts)
  have htne : ENNReal.ofReal t ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, ht0]
  have httop : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlt := hFKt.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal htne httop] at hlt
  have htoReal : (ENNReal.ofReal t).toReal = t := ENNReal.toReal_ofReal ht0.le
  rw [htoReal] at hlt
  have hbase : (∫⁻ z, ‖F z‖ₑ ^ t ∂volume.restrict K) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop] at hlt
    simp only [ENNReal.top_rpow_of_pos (by positivity : (0:ℝ) < 1 / t)] at hlt
    exact (lt_irrefl _ hlt)
  simpa only [enorm_eq_nnnorm] using hbase

/-- **Auxiliary: local lintegral finiteness of `‖G‖^q` ⟹ `MemLpLocOn G (ofReal q)`.**
Repackages the Gehring conclusion (`∫⁻_K ‖G‖^q < ⊤` for every compact `K`) as
`MemLpLocOn`. -/
private theorem memLpLocOn_of_lintegral_lt_top {G : ℂ → ℂ} {q : ℝ} (hq0 : 0 < q)
    (hGae : AEStronglyMeasurable G volume)
    (hfin : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, (‖G z‖₊ : ℝ≥0∞) ^ q < ⊤) :
    MemLpLocOn G (ENNReal.ofReal q) Set.univ := by
  intro K _ hK
  have hofReal_ne0 : ENNReal.ofReal q ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hq0]
  have hofReal_ne_top : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨hGae.restrict, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hofReal_ne0 hofReal_ne_top]
  have htoReal : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  rw [htoReal]
  have hfinK : (∫⁻ z, ‖G z‖ₑ ^ q ∂volume.restrict K) < ⊤ := by
    have hgK := hfin K hK
    have heq : (∫⁻ z in K, (‖G z‖₊ : ℝ≥0∞) ^ q) = (∫⁻ z, ‖G z‖ₑ ^ q ∂volume.restrict K) := by
      simp [enorm_eq_nnnorm]
    rwa [heq] at hgK
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  exact hfinK.ne

/-- **S3 (`beltrami_fixedPoint_memLpLocOn`).** The restated (decoupled) higher-
integrability residual, in **uniform-exponent** form. With `μ` fixed (`‖μ‖∞ < 1`), there
is a single exponent `q > 2` — depending only on `μ` — such that **every** `L²` Beltrami
fixed point `G = h + T(μ·G)` that is the weak holomorphic gradient `G = ½(Gx − I·Gy)` of a
compactly-supported `W^{1,2}` primitive `F` is locally `Lᵠ`, with no `Lᵖ` hypothesis on `h`.

The exponent is quantified *outside* the fixed-point bundle `(F, G, Gx, Gy, h)`: this
records the classical fact that Gehring's gain `ε` depends only on `‖μ‖∞` (via the
reverse-Hölder constant `A` from S1 and the dimension), not on the particular solution. The
downstream consumer L6 (`dz_memLpLocOn_of_beltrami`) needs exactly this uniformity, since it
applies the residual to a cutoff fixed point whose data varies with the compact set; L5
(`dz_cutoff_eq_beurling_repr`) supplies the primitive bundle for each such fixed point.

*Proof.* `reverseHolder_of_weakGradient` (S1) gives a reverse-Hölder constant `A` depending
only on `μ`; `gehring_selfImprovement` (S2) turns the pair `(q = 2, A)` into a uniform gain
`ε > 0`. Set `q := 2 + ε`. For each fixed point, the primitive bundle `(F, Gx, Gy)` feeds
S1's reverse-Hölder inequality for `(‖G‖, ‖h‖)`, the `MemLp _ 2` data supplies the loc-`L²`
hypotheses (`lintegral_enorm_sq_lt_top_of_memLp`), so S2 yields `∫⁻_K ‖G‖^{2+ε} < ⊤` on
every compact `K`, which `memLpLocOn_of_lintegral_lt_top` repackages as
`MemLpLocOn G (ofReal (2+ε)) univ`. -/
theorem beltrami_fixedPoint_memLpLocOn {μ : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ q : ℝ, 2 < q ∧ ∀ {F G Gx Gy h R : ℂ → ℂ},
      HasCompactSupport F → MemLp F 2 volume → MemLp G 2 volume →
      MemLp h 2 volume → MemLp h 3 volume →
      MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
      G =ᵐ[volume] h + beurling (fun z => μ z * G z) →
      MemLp R 2 volume → MemLp R 3 volume →
      (∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z) →
        MemLpLocOn G (ENNReal.ofReal q) Set.univ := by
  classical
  -- S1: the uniform reverse-Hölder constant `A` (depending only on `μ`).
  obtain ⟨A, hA, hRH⟩ := reverseHolder_of_weakGradient hμmeas hμfin hμbound
  -- S2: the uniform exponent gain `ε₀` (depending only on `q = 2`
  -- and `A`). The gain is achievable at any `ε ≤ ε₀`; we take `ε := min ε₀ 1` so that the
  -- higher-integrability exponent `2 + ε ≤ 3` is supplied by the `δ = 1` datum `MemLp h 3`.
  obtain ⟨ε₀, hε₀, hgain⟩ := gehring_selfImprovement (q := 2) (A := A) (by norm_num) hA
  set ε : ℝ := min ε₀ 1 with hε_def
  have hεpos : 0 < ε := lt_min hε₀ (by norm_num)
  have hεle₀ : ε ≤ ε₀ := min_le_left _ _
  have hεle1 : ε ≤ 1 := min_le_right _ _
  refine ⟨2 + ε, by linarith, ?_⟩
  -- Fix an arbitrary `L²` Beltrami fixed point bundle `(F, G, Gx, Gy, h, R)`, now also
  -- equipped with the `δ = 1` higher integrability `MemLp h 3`, `MemLp R 3`, and the
  -- antiholomorphic relation `½(Gx + I·Gy) =ᵐ μ·G + R`.
  intro F G Gx Gy h R hFcs hFmem hGmem hhmem hhmem3 hGxmem hGymem hGxweak hGyweak hGdef hGeq
    hRmem hRmem3 hRrel
  have hq0 : (0 : ℝ) < 2 + ε := by linarith
  -- The weights for the abstract Gehring lemma. The forcing `b` is the **combined** `L²`/`L³`
  -- inhomogeneity `‖h‖ + ‖R‖`: S1 (the corrected reverse-Hölder) converts the full gradient
  -- `‖Gx‖ + ‖Gy‖` back to `‖G‖` plus a `‖R‖` term (Wirtinger), and folds it together with the
  -- N3 inhomogeneity `‖h‖` into this single forcing.
  set w : ℂ → ℝ≥0∞ := fun z => (‖G z‖₊ : ℝ≥0∞) with hw_def
  set b : ℂ → ℝ≥0∞ := fun z => (‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞) with hb_def
  have hGae : AEStronglyMeasurable G volume := hGmem.1
  have hhae : AEStronglyMeasurable h volume := hhmem.1
  have hRae : AEStronglyMeasurable R volume := hRmem.1
  have hwmeas : AEMeasurable w volume := by
    refine (hGae.enorm).congr ?_; filter_upwards with z; simp [hw_def, enorm_eq_nnnorm]
  have hbmeas : AEMeasurable b volume := by
    have hh' : AEMeasurable (fun z => (‖h z‖₊ : ℝ≥0∞)) volume := by
      refine (hhae.enorm).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
    have hR' : AEMeasurable (fun z => (‖R z‖₊ : ℝ≥0∞)) volume := by
      refine (hRae.enorm).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
    simpa only [hb_def] using hh'.add hR'
  -- Loc-`L²` of `w = ‖G‖` (the weight at the base exponent `q = 2`).
  have hwloc : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ (2 : ℝ) < ⊤ :=
    fun K _ => by simpa only [hw_def] using lintegral_enorm_sq_lt_top_of_memLp hGmem K
  -- The forcing `b = ‖h‖ + ‖R‖` at the STRICTLY HIGHER exponent `2 + ε`: this is what the
  -- corrected Gehring lemma consumes. Supplied by `MemLp h 3` and `MemLp R 3` (`2 + ε ≤ 3`):
  -- `(‖h‖ + ‖R‖)^p ≤ 2^{p-1}(‖h‖^p + ‖R‖^p)` and both pieces have finite local lintegral.
  have hhmem3' : MemLp h (ENNReal.ofReal 3) volume := by
    rw [show (ENNReal.ofReal 3 : ℝ≥0∞) = 3 from by norm_num]; exact hhmem3
  have hRmem3' : MemLp R (ENNReal.ofReal 3) volume := by
    rw [show (ENNReal.ofReal 3 : ℝ≥0∞) = 3 from by norm_num]; exact hRmem3
  have hbloc : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, b z ^ (2 + ε) < ⊤ := by
    intro K hK
    -- `b^{2+ε} ≤ 2^{1+ε}(‖h‖^{2+ε} + ‖R‖^{2+ε})` pointwise.
    have hpt : ∀ z, b z ^ (2 + ε) ≤ (2 : ℝ≥0∞) ^ (1 + ε) *
        ((‖h z‖₊ : ℝ≥0∞) ^ (2 + ε) + (‖R z‖₊ : ℝ≥0∞) ^ (2 + ε)) := by
      intro z
      have h2e : (2 + ε) - 1 = 1 + ε := by ring
      have hbnd := ENNReal.rpow_add_le_mul_rpow_add_rpow (‖h z‖₊ : ℝ≥0∞) (‖R z‖₊ : ℝ≥0∞)
        (p := 2 + ε) (by linarith)
      rw [h2e] at hbnd
      simpa only [hb_def] using hbnd
    -- Measurability of the first summand `z ↦ ‖h z‖ₑ^{2+ε}` (restricted to `K`).
    have hmeas_h : AEMeasurable (fun z => (‖h z‖₊ : ℝ≥0∞) ^ (2 + ε))
        (volume.restrict K) := by
      have : AEMeasurable (fun z => (‖h z‖₊ : ℝ≥0∞)) (volume.restrict K) := by
        refine (hhae.enorm.restrict).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
      exact this.pow_const _
    refine lt_of_le_of_lt (setLIntegral_mono' hK.measurableSet (fun z _ => hpt z)) ?_
    rw [lintegral_const_mul' _ _ (by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)),
      lintegral_add_left' hmeas_h]
    refine ENNReal.mul_lt_top (by
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)) ?_
    exact ENNReal.add_lt_top.2
      ⟨lintegral_enorm_rpow_lt_top_of_memLp (by linarith) (by linarith) hhmem3' K hK,
       lintegral_enorm_rpow_lt_top_of_memLp (by linarith) (by linarith) hRmem3' K hK⟩
  -- The reverse-Hölder inequality for this fixed point, from S1 (fed the primitive bundle and
  -- the antiholomorphic relation): it now carries the COMBINED forcing `b² = (‖h‖ + ‖R‖)²`.
  have hRHGh :=
    hRH hFcs hFmem hGmem hhmem hGxmem hGymem hGxweak hGyweak hGdef hGeq hRmem hRrel
  -- S2's conclusion: `∫⁻_K ‖G‖^{2+ε} < ⊤` on every compact `K`.
  have hfin : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ (2 + ε) < ⊤ :=
    hgain hεpos hεle₀ hwmeas hbmeas hwloc hbloc hRHGh
  -- Repackage as `MemLpLocOn`.
  refine memLpLocOn_of_lintegral_lt_top hq0 hGae ?_
  intro K hK
  simpa only [hw_def] using hfin K hK

end RiemannDynamics

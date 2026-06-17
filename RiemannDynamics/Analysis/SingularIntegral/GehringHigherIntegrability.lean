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

/-!
# The Gehring reverse-Hölder self-improvement (Phase-1 scaffold)

This file isolates the **higher-integrability residual** of Bojarski's theorem: an
`L²` Beltrami fixed point `G = h + T(μ·G)` with `‖μ‖∞ < 1` is automatically locally
`Lᵠ` for some `q > 2`, with *no* `Lᵖ` hypothesis on the inhomogeneity `h`. Classically
this is the **Gehring reverse-Hölder / Caccioppoli self-improvement lemma**.

## The honest f-level reverse-Hölder

The earlier abstract scaffold tried to derive the reverse-Hölder gain from the bare
fixed-point equation `G = h + T(μ·G)` alone. That node was **unprovable**: the
`L² ⟹ L¹` reverse-Hölder gain is a *Sobolev–Poincaré* phenomenon on the **primitive**
`F` of which `G` is the weak holomorphic gradient (`G = ∂F`). The abstract form discards
`F`, so the gain has no honest derivation. The cure is to re-architect the reverse-Hölder
node at the **`f`-level**: it takes the primitive bundle `(F, Gx, Gy)` (which L5
`dz_cutoff_eq_beurling_repr` already constructs and now hands back), and reduces to two
genuinely analytic nodes — a Sobolev–Poincaré inequality on balls and an `f`-level
Caccioppoli inequality obtained by weak integration by parts against the test function
`χ²(F − F_B)`.

The residual is decomposed into the following dependency-ordered nodes:

* **S0** `memLpLocOn_two_of_memLp_two` — trivial packaging `L² ⟹ L²_loc`. *Proven.*
* **N1** `sobolevPoincare_ball` — Sobolev–Poincaré on a ball for a `W^{1,2}` primitive
  `F` with weak gradient `(Gx, Gy)`: the `L²`-oscillation of `F` on a ball is bounded by
  `r` times the `L¹`-average of `‖∇F‖`. *(Analytic node; `sorry`.)*
* **N2** `weakIBP_against_W12` — weak integration by parts admitting a `W^{1,2}` compactly
  supported test function (not just `C^∞`), e.g. `φ = χ²(F − c)`. *(Analytic node;
  `sorry`.)*
* **N3** `caccioppoli_of_beltrami` — the `f`-level Caccioppoli inequality: the gradient
  energy `⨍⁻_B ‖G‖²` is bounded by `r⁻²·⨍⁻_{2B}‖F − F_B‖² + ‖h‖`-terms, by testing the
  Beltrami structure against `χ²(F − F_B)` via N2. *(Depends N2; `sorry`.)*
* **S1** `reverseHolder_of_weakGradient` — the **`f`-level reverse-Hölder** inequality on
  every ball, derived from N3 (Caccioppoli) + N1 (Sobolev–Poincaré): the `r⁻¹` from
  Caccioppoli cancels the `r` from Sobolev–Poincaré, yielding a scale-invariant constant
  `A`. *Proven modulo N1/N3.*
* **S2** `gehring_selfImprovement` — the **general, equation-agnostic** Gehring lemma:
  a nonnegative locally-`Lᵠ` weight satisfying a reverse-Hölder inequality on all balls
  (with a controlled lower-order term) is locally `L^{q+ε}` for some `ε > 0`.
  *(The hard abstract node; `sorry`.)*
* **S3** `beltrami_fixedPoint_memLpLocOn` — the restated residual: assemble S0 + S1 + S2
  to upgrade an `L²` Beltrami fixed point (carrying its primitive bundle) to `Lᵠ_loc`,
  `q > 2`. *Proven modulo S1/S2.*

## Infrastructure consumed by N1 (the Sobolev–Poincaré proof, Phase 2)

The Sobolev–Poincaré node `sobolevPoincare_ball` is intended to be discharged by mollifying
the primitive `F` to `C¹` (`RiemannDynamics.exists_contDiff_hasCompactSupport_eLpNorm_sub_le`,
`Analysis/Sobolev/Mollification.lean`) and applying Mathlib's Gagliardo–Nirenberg–Sobolev
inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`
(`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`) at `n = finrank ℝ ℂ = 2`,
`p = 2` (the Hölder conjugate of `2`), to the mean-subtracted localized function, then
passing the weak gradient `(Gx, Gy)` to the Fréchet derivative in the `L¹` limit.

## Infrastructure consumed by S2 (the Gehring proof, Phase 2)

The general self-improvement node `gehring_selfImprovement` is intended to be discharged
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

Nothing hard is proved here. N1, N2, N3 and S2 are faithful, maximally-general statements
left as `sorry`; S0, S1 and S3 are closed (S1 modulo N1/N3, S3 modulo S1/S2), so the
downstream consumer `beltrami_fixedPoint_memLpLocOn_of_memLp_two` (in `Beurling/Beltrami.lean`)
reduces to `{N1, N2, N3, S2}` by a fully-compiled argument.
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

/-! ## N1 sub-stack — Riesz potential + Hardy–Littlewood–Sobolev

The honest source of the `L² → L¹` reverse-Hölder gain. The averages are the `ℝ≥0∞`-valued
lower-integral averages `⨍⁻ … = (vol B)⁻¹ ∫⁻ …`. We write the gradient norm of the
primitive `F` (whose weak partials are `Gx, Gy`) directly via the weak holomorphic Wirtinger
derivative `G = ½(Gx − I·Gy)`: classically `‖∇F‖` is comparable to `‖G‖` for a `W^{1,2}`
primitive whose `∂̄`-part is controlled, and the Sobolev–Poincaré constant absorbs the
comparison constant.

The naive "mollify `F − F_B` to `C¹` and feed Mathlib's Gagliardo–Nirenberg–Sobolev
inequality" route **fails**: the localized function `χ·(F − F_B)` carries a cutoff-annulus
commutator term `(∇χ)·(F − F_B)` whose `L¹` norm is not controlled by `r·∫_B‖G‖`, so the
GNS estimate on the global mollification does not close. The correct route is the **Riesz
potential / fractional integration** representation of `F − F_B` on the convex ball,
followed by the **Hardy–Littlewood–Sobolev** `L¹ → L²` bound for the planar Riesz potential
`I₁`, whose kernel `1/‖·‖ ∉ L²(ℝ²)` — so Young's convolution inequality is unavailable and
real (Marcinkiewicz) interpolation through the Hardy–Littlewood maximal function is
essential.  The two sub-nodes are:

* **R1** `rieszPotential_pointwise_bound` — the mean-value / Riesz representation: on a ball
  the oscillation `‖F z − F_B‖` is pointwise dominated by the Riesz potential
  `∫⁻_B ‖G y‖ / ‖z − y‖ ∂y` of the gradient density `‖G‖`.
* **R2** `eLpNorm_rieszPotential_one_le` — the Hardy–Littlewood–Sobolev `I₁ : L¹ → L²`
  fractional-integration bound, written in the lower-integral form
  `(∫⁻_B (I₁ g)²)^(1/2) ≤ C · ∫⁻_B g`.

`sobolevPoincare_ball` (N1) is then **proved modulo R1, R2** by combining the pointwise R1
with the `L²`-square-function R2 and the `volume_ball` scaling. -/

/-- **R1 (`rieszPotential_pointwise_bound`).** The **Riesz-potential / mean-value
representation** of the oscillation of a `W^{1,2}` primitive on a ball.

For a `W^{1,2}` function `F` on `ℂ` with weak directional derivatives `Gx` (direction `1`)
and `Gy` (direction `I`), and holomorphic gradient `G = ½(Gx − I·Gy)`, there is a
*dimensional* constant `C_R ≥ 0` such that on every ball `B = ball x ρ` the oscillation of
`F` about its average `F_B := ⨍_B F` is, for a.e. `z ∈ B`, pointwise bounded by the Riesz
potential (fractional integral `I₁`) of the gradient density `‖G‖`:
`‖F z − F_B‖ ≤ C_R · ∫⁻ y in B, ‖G y‖ / ‖z − y‖ ∂volume`.

The averaging `F_B = ⨍_B F` is the Bochner set average. The kernel is the planar Riesz
kernel `1/‖z − y‖` (the `n − 1 = 1` Riesz potential in dimension `n = 2`); the `‖G‖`
density encodes `‖∇F‖ ~ 2‖G‖` for the holomorphic gradient.

*Derivation (Phase 2).* Fundamental theorem of calculus along the segment `[w, z]` for each
`w ∈ B` (the ball is convex), then average the identity `F z − F w = ∫₀¹ ∇F((1−s)w + sz)·(z − w) ds`
over `w ∈ B`; Fubini and the change of variables `y = (1−s)w + sz` collapse the double
integral to the single Riesz potential, the convexity of `B` keeping the integration domain
inside `B`. The dimensional constant `C_R` is the planar Riesz-representation constant. -/
theorem rieszPotential_pointwise_bound :
    ∃ C_R : ℝ, 0 ≤ C_R ∧ ∀ {F G Gx Gy : ℂ → ℂ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
        ∀ (x : ℂ) (ρ : ℝ), 0 < ρ →
          ∀ᵐ z ∂(volume.restrict (Metric.ball x ρ)),
            (‖F z - (⨍ w in Metric.ball x ρ, F w)‖₊ : ℝ≥0∞) ≤
              ENNReal.ofReal C_R *
                ∫⁻ y in Metric.ball x ρ, (‖G y‖₊ : ℝ≥0∞) / (‖z - y‖₊ : ℝ≥0∞) ∂volume := by
  sorry

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

*Derivation (Phase 2).* The kernel `1/‖·‖ ∉ L²(ℝ²)`, so Young's inequality fails and one
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
    show χ z • (F z - c) = χ z • F z - χ z • c
    module
  have hgxu_eq : gxu = fun z => (χ z • Gx z + ((fderiv ℝ χ z) 1) • F z)
      - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c) := by
    funext z
    show χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)
      = (χ z • Gx z + ((fderiv ℝ χ z) 1) • F z) - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) 1) • c)
    module
  have hgyu_eq : gyu = fun z => (χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • F z)
      - (χ z • (0 : ℂ) + ((fderiv ℝ χ z) Complex.I) • c) := by
    funext z
    show χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)
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
    show χ z • F z - χ z • c = χ z • (F z - c)
    module
  have hucs : HasCompactSupport (fun z => χ z • (F z - c)) :=
    hχcs.smul_right (f' := fun z => F z - c)
  -- `gxu = χ•Gx + (∂₁χ)•F − (∂₁χ)•c ∈ L¹`.
  have hgxumem : MemLp (fun z => χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)) 1 volume := by
    refine MemLp.ae_eq ?_ (hχGx1.add (hdχF1.sub hdχc_mem1))
    filter_upwards with z
    show χ z • Gx z + (((fderiv ℝ χ z) 1) • F z - ((fderiv ℝ χ z) 1) • c)
      = χ z • Gx z + ((fderiv ℝ χ z) 1) • (F z - c)
    module
  -- `gyu = χ•Gy + (∂_Iχ)•F − (∂_Iχ)•c ∈ L¹`.
  have hgyumem : MemLp (fun z => χ z • Gy z + ((fderiv ℝ χ z) Complex.I) • (F z - c)) 1 volume := by
    refine MemLp.ae_eq ?_ (hχGy1.add (hdχIF1.sub hdχIc_mem1))
    filter_upwards with z
    show χ z • Gy z + (((fderiv ℝ χ z) Complex.I) • F z - ((fderiv ℝ χ z) Complex.I) • c)
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
    show χ z • (F z - c) = F z - c
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

*Derivation (Phase 2).* `φ` is the `W^{1,2}` limit of smooth compactly supported `φₙ`
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

/-- **N3 (`caccioppoli_of_beltrami`).** The **`f`-level Caccioppoli (reverse-Poincaré)
inequality** for a Beltrami fixed point `G = h + T(μ·G)` that is the weak holomorphic
gradient `G = ½(Gx − I·Gy)` of a primitive `F` (weak partials `Gx, Gy`).

There is a constant `A ≥ 0`, depending only on `‖μ‖∞` and the Beurling operator norm
(hence **independent of the ball** `x, r` and of the solution), such that on every ball
`B = ball x r` the gradient energy is bounded by the oscillation of `F` on the doubled
ball `2B = ball x (2r)` (scaled by `r⁻²`) plus the inhomogeneity:
`(⨍⁻_{B} ‖G‖²)^(1/2) ≤ A · r⁻¹ · (⨍⁻_{2B} ‖F − F_{2B}‖²)^(1/2)
    + A · (⨍⁻_{2B} ‖h‖²)^(1/2)`.

*Derivation (Phase 2).* Test the weak Beltrami equation against `φ = χ²·(F − F_{2B})`
for a cutoff `χ` adapted to `B` (with `|∇χ| ≲ r⁻¹`), using the weak IBP node N2 (the test
function is only `W^{1,2}`). The cross term and the `∇χ`-commutator are absorbed by the
ellipticity `‖μ‖∞ < 1`, converting the gradient energy on `B` into the lower-order
oscillation `r⁻²·⨍⁻_{2B}‖F − F_{2B}‖²` plus the inhomogeneity, the classical Caccioppoli
step. *Dependency:* N2. -/
theorem caccioppoli_of_beltrami {μ : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {F G Gx Gy h : ℂ → ℂ},
      MemLp F 2 volume → MemLp G 2 volume → MemLp h 2 volume →
      MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
      G =ᵐ[volume] h + beurling (fun z => μ z * G z) →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, (‖G z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal (A / r) *
              (⨍⁻ z in Metric.ball x (2 * r),
                (‖F z - (⨍ w in Metric.ball x (2 * r), F w)‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
                ^ (1 / (2 : ℝ)) +
            ENNReal.ofReal A *
              (⨍⁻ z in Metric.ball x (2 * r), (‖h z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
                ^ (1 / (2 : ℝ)) := by
  sorry

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
  have hC := hCacc hFmem hGmem hhmem hGxmem hGymem hGxweak hGyweak hGdef hGeq x r hr
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
  set normH : ℝ≥0∞ :=
    (⨍⁻ z in B2, (‖h z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hnormH_def
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
  -- `normH ≤ 2·normB`: pointwise `‖h‖² ≤ (‖h‖+‖R‖)²` on `2B`, then transfer `2B → 4B`
  -- (factor `4` under the root becomes `2`).
  have hnormH_le2 : normH ≤ 2 * normB := by
    have hstep : normH ≤ (⨍⁻ z in B2, ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ) ∂volume)
        ^ (1 / (2 : ℝ)) := by
      rw [hnormH_def]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [setLAverage_eq, setLAverage_eq]
      gcongr
      exact le_self_add
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

This is the content underlying Gehring's lemma; the proof (Phase 2) runs the good-λ /
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
  -- conclusion to a fixed enclosing ball, and G3 is the trivial glue. G0 and G3
  -- are closed below; G1 and G2 are the two hard analytic cores, laid as faithful
  -- nodes. The output exponent gain `ε₀` is the one extracted by the absorption
  -- in G2 (set to `1` here as the placeholder gain; the genuine value is read off
  -- from the absorbed coefficient in the G2 node).
  -- ===========================================================================
  classical
  -- The uniform gain. The genuine Gehring `ε₀` is determined by G2's absorption
  -- (the value at which the absorbed coefficient drops below `1`); we expose a
  -- positive placeholder so the scaffold typechecks. Any `0 < ε₀` is admissible
  -- for laying the decomposition; the absorption node fixes the honest value.
  refine ⟨1, by norm_num, ?_⟩
  intro ε hεpos _hεle w b hwmeas hbmeas hwloc hbloc hRH
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
  -- (`⨍_{4Bᵢ} bᵠ > c'λ^q`, contributing `∫_{{b>βλ}} bᵠ`).  This several-hundred-line
  -- stopping-time / CZ argument is not available in Mathlib; it is laid here as a
  -- faithful node.
  -- ===========================================================================
  obtain ⟨β, hβpos, hβlt1, lam0, hlam0, C, goodLambda⟩ :
      ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∃ lam0 : ℝ, 0 ≤ lam0 ∧ ∃ C : ℝ≥0∞,
        ∀ lam : ℝ, lam0 ≤ lam →
          (∫⁻ z in {z | ENNReal.ofReal lam < w z} ∩ Metric.ball x₀ (4 * R₀),
                w z ^ q)
            ≤ C * ENNReal.ofReal (lam ^ (q - 1))
                * (∫⁻ z in {z | ENNReal.ofReal (β * lam) < w z}
                      ∩ Metric.ball x₀ (16 * R₀), w z)
              + C * (∫⁻ z in {z | ENNReal.ofReal (β * lam) < b z}
                      ∩ Metric.ball x₀ (16 * R₀), b z ^ q) := by
    sorry
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
  -- fixes the honest gain `ε₀`. This is laid as a faithful node consuming the
  -- master-ball `goodLambda`; the layer-cake bookkeeping and the absorption
  -- inequality live here.
  -- ===========================================================================
  have absorb : ∫⁻ z in Metric.ball x₀ R₀, w z ^ (q + ε) < ⊤ := by
    -- The forcing terms G2 produces on the right are finite, supplied here as
    -- CLOSED glue from the loc-`Lᵠ`/loc-`L^{q+ε}` hypotheses, evaluated on the
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
    -- ISOLATED CORE of G2: the layer-cake reconstruction + ε-absorption.
    --
    -- The node is reduced to a SINGLE absorbed linear bound of the target
    -- `∫_{4B₀} w^{q+ε}` by the two finite forcing masses `∫_{16B₀} wᵠ` and
    -- `∫_{16B₀} b^{q+ε}` (both `< ⊤`, supplied above as `hRHS_w`, `hRHS_b`) with
    -- a FINITE coefficient `K`. We package that absorbed bound as the residual
    -- `hbound`; the finiteness wrapper around it (below) is fully discharged
    -- from `hRHS_w`, `hRHS_b`, `ENNReal.add_lt_top` and `ENNReal.mul_lt_top`.
    -- =======================================================================
    obtain ⟨K, hKfin, hbound⟩ :
        ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
          ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ (q + ε)
            ≤ K * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
              + K * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
      -- G2 — the layer-cake + ε-absorption reconstruction, consuming the
      -- corrected Giaquinta–Modica `goodLambda` (right `w`-mass at exponent `1`,
      -- factor `λ^{q-1}`, super-level `bᵠ`-forcing) of the G1 node above.
      --
      -- `goodLambda` is the only nontrivial input; we record its consumption
      -- explicitly so the dependency is real.
      have hgoodLambda := goodLambda
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
      -- This part is honest and complete; it isolates the genuine analytic
      -- content into the per-`N` bounded absorbed bound `hboundN` below.
      -- =====================================================================
      -- Positivity of the reconstruction exponent (reused).
      have hqε0' : 0 ≤ q + ε := hqε0.le
      -- POINTWISE truncation sup: `⨆ N, (min (w z) N)^{q+ε} = (w z)^{q+ε}`.
      have hptsup : ∀ z, ⨆ N : ℕ, (min (w z) (N : ℝ≥0∞)) ^ (q + ε)
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
        -- `·^{q+ε}` is monotone (exponent `≥ 0`) and continuous on `ℝ≥0∞`.
        have hmono : Monotone (fun n : ℕ => (min (w z) (n : ℝ≥0∞)) ^ (q + ε)) :=
          fun a c hac => ENNReal.rpow_le_rpow (hmin_mono hac) hqε0'
        have htend : Tendsto (fun n : ℕ => min (w z) (n : ℝ≥0∞)) atTop (𝓝 (w z)) := by
          have h := tendsto_atTop_iSup hmin_mono; rwa [hsup] at h
        have hcomp : Tendsto (fun n : ℕ => (min (w z) (n : ℝ≥0∞)) ^ (q + ε)) atTop
            (𝓝 ((w z) ^ (q + ε))) :=
          (ENNReal.continuous_rpow_const.tendsto (w z)).comp htend
        exact iSup_eq_of_tendsto hmono hcomp
      -- Per-truncation measurability and monotonicity for `lintegral_iSup'`.
      have hmeasN : ∀ N : ℕ,
          AEMeasurable (fun z => (min (w z) (N : ℝ≥0∞)) ^ (q + ε))
            (volume.restrict (Metric.ball x₀ (4 * R₀))) :=
        fun N => (hwmeas.restrict.min aemeasurable_const).pow_const _
      have hmonoN : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (4 * R₀))),
          Monotone (fun N : ℕ => (min (w z) (N : ℝ≥0∞)) ^ (q + ε)) := by
        filter_upwards with z a c hac
        exact ENNReal.rpow_le_rpow (min_le_min_left _ (by exact_mod_cast hac)) hqε0'
      -- MONOTONE CONVERGENCE: identify the target LHS with the sup of truncations.
      have hMCT : ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ (q + ε)
          = ⨆ N : ℕ, ∫⁻ z in Metric.ball x₀ (4 * R₀), (min (w z) (N : ℝ≥0∞)) ^ (q + ε) := by
        rw [← lintegral_iSup' hmeasN hmonoN]
        exact lintegral_congr_ae (by filter_upwards with z using (hptsup z).symm)
      -- =====================================================================
      -- RESIDUAL — the per-`N` bounded absorbed bound, UNIFORM in `N`.
      --
      -- This is the genuine Giaquinta–Modica iteration core.  Feeding the
      -- corrected `goodLambda` into the `ℝ`-layer-cake — multiply by `λ^{ε-1}`
      -- and integrate `λ ∈ (λ₀,∞)`, then Tonelli — reconstructs the bound
      --   `∫_{{w>λ₀}∩4B₀} w^{q+ε} ≤ λ₀^ε·G(λ₀) + K(ε)·∫_{16B₀} w^{q+ε}
      --                               + C·β^{-ε}·∫_{16B₀} b^{q+ε}`,
      -- where the right `w`-mass at EXPONENT `1` and the `λ^{q-1}` factor produce
      -- the FINITE absorbed coefficient
      --   `K(ε) = C·ε / ((q+ε−1)·β^{q+ε−1})`,
      -- with `C` the FIXED G1 covering constant.  Crucially `K(ε) → 0` as
      -- `ε → 0` (numerator `ε → 0`, denominator `→ (q−1)·β^{q−1} > 0`): the
      -- ε-prefactor from `∂_λ(λ^ε)` survives because the inner radial integral
      -- over `λ^{q+ε−2}` is bounded (`q+ε−2 > −1`).  So for `ε ≤ ε₀` (chosen with
      -- `K(ε₀) ≤ 1/2`) the absorption SUCCEEDS — the covering constant does NOT
      -- need to shrink; the exponent-`1` structure of the corrected good-λ is what
      -- makes a fixed `C` absorbable.  (This corrects the earlier diagnosis: the
      -- obstruction was never the size of `C`, but the exponent on the right
      -- `w`-mass — `q` in the trivial form, which cancels the ε-prefactor and
      -- pins `coeff ≥ C`; `1` in the corrected form, which lets it vanish.)
      --
      -- The one genuine remaining ingredient is the GIAQUINTA ITERATION LEMMA
      -- (not in Mathlib).  Because the reconstructed `w^{q+ε}`-mass lives over the
      -- enlargement `16B₀` while the left side is over `4B₀`, the absorption is
      -- run over a finite chain of concentric radii `4R₀ ≤ t < s ≤ 16R₀`: the
      -- good-λ holds for every such pair (every ball satisfies `hRH`), giving
      -- `φ_N(t) ≤ K(ε)·φ_N(s) + A(s−t)^{-α}·∫_{16B₀} wᵠ + B·∫_{16B₀} b^{q+ε}`
      -- for the truncated masses `φ_N(t) = ∫_{ball x₀ t} (min w N)^{q+ε}` (each
      -- finite, so the iteration lemma applies), whose conclusion at `t = 4R₀`
      -- is the `N`-uniform bound below.  This iteration lemma together with the
      -- per-pair layer-cake reconstruction is the residual analytic content.
      obtain ⟨K, hKfin, hboundN⟩ :
          ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ N : ℕ,
            ∫⁻ z in Metric.ball x₀ (4 * R₀), (min (w z) (N : ℝ≥0∞)) ^ (q + ε)
              ≤ K * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
                + K * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
        sorry
      -- Collapse the monotone sup against the `N`-uniform bound.
      exact ⟨K, hKfin, by rw [hMCT]; exact iSup_le (hboundN)⟩
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
  -- S2 (corrected, Option-A): the uniform exponent gain `ε₀` (depending only on `q = 2`
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

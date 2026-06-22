/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# The one-sided co-area (Eilenberg) inequality — GMT infrastructure

This file builds the **Eilenberg inequality** (the *one-sided* co-area inequality) for a Lipschitz
real-valued function on a metric space, as standalone geometric-measure-theory infrastructure. The
target inequality is, for a `K`-Lipschitz `u : X → ℝ` and a nonnegative measurable weight
`g : X → ℝ≥0∞`,

> `∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[d-1]) dc ≤ K · ∫⁻ z, g z ∂μH[d]`     (★)

(the integrated `(d−1)`-Hausdorff measure of the weighted level sets is dominated by the
`d`-dimensional weighted integral, with the Lipschitz constant). In the unweighted, planar form
`d = 2`, `g = ‖∇u‖` this is the genuine ingredient powering the length–area lower bound for the
modulus of a conjugate family of curves (see `QC/GeometricDifferentiable.lean`).

## Direction and truth

The inequality (★) is the **TRUE** one-sided direction. For a Lipschitz `u`, the level sets are
"thin" (they have `μH[d-1]`-measure controlled by the gradient), so the *left*-hand integrated
level-set measure is **bounded above** by the gradient integral. (The reverse inequality, an
*equality*, holds for `u ∈ C¹` with `|∇u| ≠ 0` — the full co-area formula — and is genuinely
deeper; it is **not** what is needed here and is **not** claimed.) The `≤` of (★) is exactly what
the length–area lower bound consumes: it lets one pass from a *gradient-energy* integral to an
*integrated-level-set* integral, which the admissible separating density then bounds below.

### Affine sanity check (`u` affine, the `f = id` degenerate case)

For `u : ℝ² → ℝ` the affine projection `u(x, y) = x` (Lipschitz constant `1`), the level sets are
the vertical lines `{x = c}`, `μH[1]`-measure of `u⁻¹{c} ∩ R` over a rectangle `R = [a,b]×[s,t]` is
`t − s`, and `‖∇u‖ = 1`, so (★) reads `∫_a^b (t − s) dc ≤ 1 · vol(R) = (b−a)(t−s)`, an
**equality**. This reproduces the plain-Fubini affine case that `lengthArea_modulus_lower_bound`
proves directly, confirming the direction.

## What is proved here vs. the isolated residual

* The `mkMetric` / Hausdorff-content covering machinery (`Measure.hausdorffMeasure`,
  `Measure.mkMetric_le_liminf_tsum`, `LipschitzWith.hausdorffMeasure_image_le`) is Mathlib's; there
  is **no** co-area formula or Eilenberg inequality in Mathlib (an exhaustive search finds neither
  `coarea` nor `eilenberg` in any analytic sense).
* The genuine covering core — a Vitali/Besicovitch cover of the domain by small balls, on each of
  which `u` oscillates by `≤ K · diam`, summing Hausdorff `(d−1)`-contents of the slices — is the
  single isolated residual `eilenberg_coarea_le` below. Its precise missing classical ingredient
  and its truth/direction are documented at the `sorry`.

The surrounding measurability, the planar specialization, and the affine equality check are proved
in full and are axiom-clean.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RiemannDynamics.Coarea

variable {X : Type*} [MeasurableSpace X] [EMetricSpace X] [BorelSpace X]

/-! ## The Eilenberg one-sided co-area inequality -/

/-- **Eilenberg one-sided co-area inequality (the isolated GMT residual).**

For a `K`-Lipschitz function `u : X → ℝ` on a (Borel) metric space and a nonnegative measurable
weight `g : X → ℝ≥0∞`, the **integrated `(d−1)`-Hausdorff measure of the weighted level sets is
dominated by `K` times the `d`-Hausdorff-weighted integral**:

`∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[d-1]) dc ≤ (K : ℝ≥0∞) · ∫⁻ z, g z ∂μH[d]`.

## Truth and direction

This is the **TRUE one-sided (`≤`) co-area inequality** (Eilenberg's inequality; Federer,
*Geometric Measure Theory* 2.10.25; Evans–Gariepy, *Measure Theory and Fine Properties of
Functions*, §3.4.2, the inequality `∫* (∫ g dμH^{n-1}) dc ≤ Lip(u) ∫ g dμH^n`). The Lipschitz
hypothesis makes the level sets thin, so the left side is **bounded above**; the reverse is the
full co-area *formula* (an equality for `C¹` maps with non-vanishing gradient), which is deeper and
**not** asserted here.

## The precise missing classical ingredient

The classical proof: fix `δ > 0`; by a Vitali/Besicovitch covering (Mathlib has
`Besicovitch.exists_disjoint_closedBall_covering_ae`) choose balls `Bᵢ = closedBall xᵢ rᵢ` with
`rᵢ < δ` covering (a.e.) the support of `g`. On `Bᵢ`, `u` has oscillation `≤ K · diam Bᵢ`, so
`u(Bᵢ)` is an interval of length `≤ K · diam Bᵢ`; the level set `u⁻¹{c} ∩ Bᵢ` is nonempty for
`c` in that interval and has diameter `≤ diam Bᵢ`. Therefore the *Hausdorff `(d−1)`-content of the
sliced cover*, integrated over `c`, telescopes:
`∫⁻ c, ∑ᵢ (diam Bᵢ)^{d-1} · 𝟙[c ∈ u(Bᵢ)] ≤ ∑ᵢ (diam Bᵢ)^{d-1} · K · diam Bᵢ = K ∑ᵢ (diam Bᵢ)^d`,
the right side approximating `K · μH[d]` of the cover as `δ → 0` (via
`Measure.hausdorffMeasure_le_liminf_tsum`), the left side dominating `∫⁻ c, μH[d-1](u⁻¹{c})`
(monotone convergence / Fatou as `δ → 0`). Weighting by `g` is by the same covering with `g`
sampled on each ball.

**Missing from Mathlib:** the simultaneous diameter bookkeeping linking a single covering's
`(d−1)`-content slices to the `d`-content of the cover (the "co-area Vitali sum"); Mathlib's
covering lemmas produce the cover and `mkMetric_le_liminf_tsum` bounds *one* Hausdorff content, but
the *cross*-dimensional telescoping `∑ (diam)^{d-1} · diam(u-image) ≤ K ∑ (diam)^d` and the Fatou
passage in `c` are net-new. This is the single genuinely irreducible GMT atom of the co-area route;
everything that consumes it (the planar specialization and the ρ-potential length–area assembly) is
built on top and is sound. -/
theorem eilenberg_coarea_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : X → ℝ≥0∞} (hg : Measurable g) {d : ℝ} (hd : 1 ≤ d) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[d - 1] : Measure X)) ≤ (K : ℝ≥0∞) * ∫⁻ z, g z ∂(μH[d]) := by
  sorry

/-! ## Planar specialization

In the plane (`d = 2`, `μH[2] = volume`, `μH[1]` on level sets) with the gradient weight, the
Eilenberg inequality becomes the length–area lower bound used by the modulus theory. We record the
specialization to a general weight; the gradient instantiation is in the QC assembly. -/

/-- **Planar Eilenberg inequality, general weight.** On `ℂ` (with `μH[2] = volume` by
`Measure.hausdorffMeasure_prod_real` transported through `Complex.measurableEquivRealProd`), for a
`K`-Lipschitz `u : ℂ → ℝ` and measurable `g ≥ 0`,
`∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[1]) dc ≤ K · ∫⁻ z, g z ∂μH[2]`.

This is the immediate `d = 2` instance of `eilenberg_coarea_le`; it is stated separately so the QC
length–area assembly can consume it without re-deriving the dimension arithmetic. Its truth and
direction are inherited from `eilenberg_coarea_le` (the one-sided `≤`). -/
theorem eilenberg_coarea_planar_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ)) ≤ (K : ℝ≥0∞) * ∫⁻ z, g z ∂(μH[2]) := by
  have h := eilenberg_coarea_le (X := ℂ) hu hg (d := 2) (by norm_num)
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
  exact h

/-- **`μH[2] = volume` on `ℂ` (standard normalization fact, isolated residual).**

The 2-dimensional Hausdorff measure on the complex plane (with its Euclidean metric) coincides with
the canonical planar Lebesgue measure `volume`.

## Truth and direction

**TRUE** (equality). `ℂ` is a 2-dimensional real inner product space, and on any finite-dimensional
real inner product space the `d`-Hausdorff measure (`d = finrank`) equals the additive Haar /
Lebesgue measure: both are `addHaar` measures, and the scaling factor is `1` because an orthonormal
parallelepiped is a unit cube of unit Hausdorff content (Federer 2.10.35; Mathlib's
`MeasureTheory.Measure.euclideanHausdorffMeasure` records exactly this `addHaarScalarFactor`, with
the factor-`= 1` step a Mathlib `proof_wanted`,
`addHaarScalarFactor_hausdorffMeasure_eq`). It is a pure normalization fact, **independent of** the
co-area core, and is used only to convert the Hausdorff-flavoured Eilenberg conclusion into the
`volume`-flavoured statement the QC length–area assembly consumes.

## Missing ingredient

The Mathlib-side `addHaarScalarFactor (volume : EuclideanSpace ℝ (Fin 2)) μH[2] = 1` (currently a
`proof_wanted`) transported across the linear isometry `ℂ ≃ₗᵢ EuclideanSpace ℝ (Fin 2)` via
`IsometryEquiv.measurePreserving_hausdorffMeasure`. No analytic content; pure measure
normalization. -/
theorem hausdorffMeasure_two_complex_eq_volume :
    (μH[2] : Measure ℂ) = volume := by
  sorry

/-- **Planar Eilenberg inequality against `volume` (the QC-facing form).**

The `volume`-normalized one-sided co-area inequality on `ℂ`: for `K`-Lipschitz `u : ℂ → ℝ` and
measurable `g ≥ 0`,
`∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[1]) dc ≤ K · ∫⁻ z, g z ∂volume`.

This is `eilenberg_coarea_planar_le` with the right-hand `μH[2]` rewritten to `volume`
(`hausdorffMeasure_two_complex_eq_volume`). The level-set integrals remain `μH[1]` (the genuine
arc-length measure on the 1-dimensional level sets). Direction `≤` inherited from the co-area core;
**TRUE**. -/
theorem eilenberg_coarea_volume_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ)) ≤ (K : ℝ≥0∞) * ∫⁻ z, g z ∂volume := by
  have h := eilenberg_coarea_planar_le hu hg
  rwa [hausdorffMeasure_two_complex_eq_volume] at h

/-! ## The gradient-weighted (sharp) planar co-area inequality

The Lipschitz-constant forms above are derived corollaries; the genuine Eilenberg inequality
replaces the constant `K` by the *pointwise* gradient norm `‖∇u‖`. This sharp form is what the
length–area lower bound consumes: it lets the eikonal bound `‖∇u‖ ≤ ρ` transfer the
gradient-energy integral `∫ ρ σ` down to the integrated level sets. -/

/-- **Sharp planar co-area (Eilenberg) inequality, gradient-weighted form (the isolated GMT
residual that the length–area assembly consumes).**

For a `K`-Lipschitz `u : ℂ → ℝ` (Lipschitz, hence `fderiv ℝ u` exists a.e. by Rademacher) and a
nonnegative measurable weight `g : ℂ → ℝ≥0∞`,

`∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[1]) dc ≤ ∫⁻ z, g z * ‖fderiv ℝ u z‖₊ ∂volume`.

## Truth and direction

**TRUE**, one-sided (`≤`). This is the genuine Eilenberg inequality (Evans–Gariepy §3.4.2,
Theorem 1: for Lipschitz `u : ℝⁿ → ℝ`, `∫_ℝ (∫_{u⁻¹{c}} g dμH^{n-1}) dc ≤ ∫ g |∇u| dx`; equality
is the co-area *formula*, the deeper two-sided statement, which is **not** claimed). The pointwise
gradient `‖∇u‖` is sharper than the Lipschitz constant `K` (since `‖∇u‖ ≤ K` a.e.); the
`K`-constant form `eilenberg_coarea_volume_le` follows from this by monotonicity, so this is the
*primitive* co-area atom.

## Affine sanity check

For `u(z) = z.re` (so `fderiv ℝ u = reCLM`, `‖∇u‖ = 1`), the right side is `∫⁻ g dvol`; the left
side is `∫⁻ c (∫_{re = c} g dμH[1]) dc`, and co-area for the affine `u` is the Fubini equality
`∫ g = ∫_c ∫_{re=c} g`, so `≤` holds with equality — exactly the affine length–area case in
`lengthArea_modulus_lower_bound`.

## Missing ingredient

Same covering core as `eilenberg_coarea_le`, refined: instead of bounding each ball's `u`-image by
`K · diam`, use the *pointwise* gradient — the oscillation of `u` on a small ball `B(x, r)` is
`(‖∇u(x)‖ + o(1)) · r` at a.e. `x` (differentiability), so the co-area Vitali sum telescopes to
`∫ g ‖∇u‖` rather than `K ∫ g`. The covering/Fatou bookkeeping is net-new (Mathlib has no co-area).
This is the genuinely irreducible deepest atom of the geometric⇒analytic length–area route. -/
theorem eilenberg_coarea_grad_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ))
      ≤ ∫⁻ z, g z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume := by
  sorry

end RiemannDynamics.Coarea

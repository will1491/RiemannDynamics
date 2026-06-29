/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.LengthArea.ReverseLengthAreaForward

/-!
# Loewner planar reciprocity — the image cross-bound residual

This file states the single planar Loewner / Beurling–Ahlfors reciprocity residual consumed by
`imageConjugate_cross_bound` (`QC/GeometricToAnalytic/GeometricDifferentiable/`) on the geometric ⇒
analytic
critical path: for a geometric `K`-quasiconformal homeomorphism `f` and densities `ρ`, `σ`
admissible for the image crossing family and the image separating (swap) family of an axis
rectangle, the cross-product integrates to at least `1`,

  `1 ≤ ∫⁻ z, ρ z · σ z`.

This is the headline reciprocity inequality. Through `imageConjugate_cross_bound` it feeds
`conjugateImageModulus_reciprocity` (`1 ≤ M(Γ) · M(Γ*)`), then
`square_imageCurveFamily_modulus_ge` (`M(image square) ≥ 1/K`), the modulus blow-up
`squareQuad_imageModulus_ge`, and ultimately the infinitesimal dilatation bound
`IsQCGeometric.infinitesimal_dilatation`.

## Why it is Mathlib-absent

A serious Phase-3 investigation (summarized in `imageConjugate_cross_bound`'s docstring) confirmed
that the proved Sobolev co-area engine (`Analysis/Sobolev/Coarea/Assembly.lean`'s
`eilenberg_coarea_grad_le`) plus the proved planar Sperner / Poincaré–Miranda crossing
(`Analysis/RectangleCrossing.lean`'s `rectangle_crossing`) are **insufficient** to close the
cross-bound directly:

* a Lipschitz scalar `u : ℂ → ℝ` whose level sets are the image foliation does not exist from a
  mere homeomorphism `f`;
* the source-plane co-area route needs a change-of-variables for `f` (a known `fderiv`), which the
  geometric ⇒ analytic direction is precisely constructing on top of this lemma;
* the natural foliation `c ↦ f({c} × [s,t])` consists of continuous but not necessarily absolutely
  continuous curves, so σ-admissibility does not apply along the foliation leaves.

The classical Beurling ρ-potential route is ruled out by a planar Kakeya / Nikodym counterexample.
The genuine closure runs through the **Loewner condition** for the planar Jordan domain
(Heinonen 2001, *Lectures on Analysis on Metric Spaces*; Heinonen–Koskela 1998; Hesse 1975), which
equates extremal length and capacity for conjugate families — Mathlib-absent.

## Closeability roadmap

Reduce the image case to the affine case via `rectangle_crossing` (every image crossing curve meets
every image separating curve) together with a measure-preserving topological parametrization of the
image quadrilateral by the source axis rectangle. The affine atom — full AC-curve-family
admissibility, *not* slice admissibility (a 2026-06-26 audit found the slice-only hypotheses
insufficient: `ρ(x,y) = 1 + sin(2πx)sin(2πy)`, `σ` symmetric, on `[0,1]²` gives `∫∫ ρσ = 3/4 < 1`)
— is then the classical Beurling argument:

1. **Truncate to bounded densities** `ρ_n = min(ρ, n)` (with an admissibility-preserving
   renormalization by a factor `→ 1`).
2. **Bounded case via the Beurling ρ-potential** `u_n(z) = inf_γ ∫_γ ρ_n ds`: Lipschitz, eikonal
   `‖∇u_n‖ ≤ ρ_n` a.e., level sets separate left from right, so by σ-admissibility and the proved
   co-area `eilenberg_coarea_grad_le`, `1 ≤ ∫_0^1 (∫_{u_n=c} σ dμH¹) dc ≤ ∫ ρ_n · σ`.
3. **Pass to the limit** by monotone convergence.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- **Loewner image cross-bound — the reciprocity residual for `imageConjugate_cross_bound`.**

For a geometric `K`-quasiconformal homeomorphism `f : ℂ → ℂ` and admissible densities
`ρ, σ : ℂ → ℝ≥0∞` for the image crossing family and the image separating (swap) family of an axis
rectangle, the cross-product integrates to at least `1`:

  `1 ≤ ∫⁻ z, ρ z * σ z`.

This has the **identical signature** to `imageConjugate_cross_bound`
(`QC/GeometricToAnalytic/GeometricDifferentiable/`); it discharges that lemma by a one-line call.
See the file
docstring for why it is Mathlib-absent and for the closeability roadmap. -/
theorem loewner_image_cross_bound_axisRect {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {K : ℝ} (hfqc : IsQCGeometric f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t)
    {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)) :
    1 ≤ ∫⁻ z, ρ z * σ z := by
  sorry

end RiemannDynamics

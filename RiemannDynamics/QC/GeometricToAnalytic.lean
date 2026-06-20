/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.Analytic
import RiemannDynamics.QC.SensePreserving
import RiemannDynamics.Analysis.Sobolev.AbsolutelyContinuousLines

/-!
# Geometric ⇒ analytic: the Gehring–Lehto stages

This file decomposes the hard direction of the quasiconformal equivalence —
`isQCAnalytic_of_isQCGeometric` in `QC/Equivalence.lean` — into its classical
Gehring–Lehto stages, stated here as separate lemmas. A geometric `K`-quasiconformal map
(a sense-preserving homeomorphism whose image-family modulus is `≤ K · M(Q)` for every
quadrilateral) is absolutely continuous on lines, lies in `W^{1,2}_loc`, is differentiable
almost everywhere, and satisfies a Beltrami equation with dilatation bound
`‖μ‖∞ ≤ (K − 1)/(K + 1)`.

## Stages

* `IsQCGeometric.exists_acl_weakGradient` — **reverse length–area**: the modulus bound forces
  absolute continuity on almost every horizontal and vertical line, with `L²_loc` partials.
  *(research-scale; the converse of the length–area inequality)*
* `IsQCGeometric.ae_differentiableAt` — **Stepanov / Gehring–Lehto a.e. differentiability**:
  an ACL map with `L²_loc` partials is (totally) differentiable almost everywhere. Rademacher
  does not apply (the map is not Lipschitz); this is the Stepanov refinement.
  *(research-scale; approximate differentiability is absent from Mathlib)*
* `IsQCGeometric.exists_beltrami` — **dilatation bound**: at almost every point the pointwise
  dilatation `‖∂̄f / ∂f‖` is `≤ (K − 1)/(K + 1)`, packaged as a `BeltramiCoeff`.

These stages assemble (with `SensePreserving.isHomeomorph`, `memWklocP_one_of_acl`,
`SensePreserving.ae_det_pos`) into `isQCAnalytic_of_isQCGeometric`.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- **Reverse length–area (geometric ⇒ ACL).** A geometric `K`-quasiconformal map is
absolutely continuous on almost every horizontal and vertical line, with `x`- and
`y`-partials that are locally `L²`. This is the converse of the length–area inequality: the
modulus bound `M(f(Q)) ≤ K · M(Q)` on rectangles forces, by a Fubini/length–area argument,
absolute continuity of the line slices together with the square-integrable energy bound. -/
theorem IsQCGeometric.exists_acl_weakGradient {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ gx gy : ℂ → ℂ, ACLHorizontal f gx ∧ ACLVertical f gy ∧
      MemLpLocOn gx (2 : ℝ≥0∞) Set.univ ∧ MemLpLocOn gy (2 : ℝ≥0∞) Set.univ := by
  sorry

/-- **Stepanov / Gehring–Lehto a.e. differentiability.** A geometric `K`-quasiconformal map
is (totally, real-)differentiable at almost every point. The map is absolutely continuous on
lines with `L²_loc` partials (`exists_acl_weakGradient`); the Stepanov theorem upgrades this
to total differentiability a.e. (Rademacher is inapplicable — the map need not be Lipschitz). -/
theorem IsQCGeometric.ae_differentiableAt {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ f z := by
  sorry

/-- **Dilatation bound (geometric ⇒ Beltrami).** A geometric `K`-quasiconformal map satisfies
a Beltrami equation `∂̄f = b.μ · ∂f` almost everywhere with a coefficient of essential norm at
most `(K − 1)/(K + 1)`. At almost every point of differentiability the infinitesimal modulus
distortion is `≤ K`, which is exactly the pointwise dilatation bound
`‖∂̄f / ∂f‖ ≤ (K − 1)/(K + 1)`; measurability and the essential-norm bound package it as a
`BeltramiCoeff`. -/
theorem IsQCGeometric.exists_beltrami {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hf : IsQCGeometric f K) :
    ∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧
      ∀ᵐ z : ℂ, dzbar f z = b.μ z * dz f z := by
  sorry

end RiemannDynamics

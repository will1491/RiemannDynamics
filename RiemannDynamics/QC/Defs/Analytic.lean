/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Defs.BeltramiCoeff

/-!
# Quasiconformal maps: the analytic definition

This file gives the **analytic** definition of a quasiconformal map, the one the
measurable Riemann mapping theorem and Sullivan's deformation argument consume.
A map `f : ℂ → ℂ` is quasiconformal with Beltrami coefficient `b` when:

* `f` is an **orientation-preserving homeomorphism** of the plane
  (`OrientationPreservingHomeo`): a homeomorphism whose almost-everywhere
  Jacobian `det (Df)` is positive;
* `f` lies in `W^{1,2}_loc(ℂ)` (`MemW12loc`, from the Sobolev layer), so its weak
  Wirtinger derivatives `∂f`, `∂̄f` exist; and
* `f` satisfies the **Beltrami equation** `∂̄f = b.μ · ∂f` almost everywhere.

The two standard definitions of quasiconformality — this analytic one and the
geometric `K`-quasiconformal one via the modulus of quadrilaterals — are proved
equivalent in `QC/Equivalence.lean`; analytic signatures carry the Beltrami
coefficient `(b : BeltramiCoeff)`, geometric ones carry the dilatation
`(K : ℝ)`, and the equivalence is the only place the two tracks meet.

The Wirtinger derivatives `dz`, `dzbar` are the pointwise ones from
`Analysis/Sobolev/Wirtinger.lean`; since `f ∈ W^{1,2}_loc` is differentiable
almost everywhere, they agree almost everywhere with the weak derivatives, so the
almost-everywhere Beltrami equation is the intended one.
-/

open MeasureTheory Complex
open scoped ENNReal

namespace RiemannDynamics

/-- An **orientation-preserving homeomorphism** of the plane: a homeomorphism
`f : ℂ → ℂ` whose real Jacobian determinant `det (Df z)` is positive for almost
every `z`. (For a quasiconformal map the differential `Df` exists almost
everywhere; where `f` is not differentiable `fderiv ℝ f z` is `0`, so the
almost-everywhere positivity is the substantive sense-preserving condition.) This
is the orientation condition of the analytic definition `IsQCAnalytic` below; the
geometric definition `IsQCGeometric` instead uses the purely topological
`SensePreserving` (in `QC/Defs/SensePreserving.lean`), so that a.e. differentiability and
positivity of the Jacobian remain conclusions of the geometric ⇒ analytic direction
rather than hypotheses. The two are reconciled by the translation bridges
`SensePreserving.of_orientationPreservingHomeo` and `SensePreserving.ae_det_pos`. -/
def OrientationPreservingHomeo (f : ℂ → ℂ) : Prop :=
  IsHomeomorph f ∧ ∀ᵐ z, 0 < (fderiv ℝ f z).det

/-- The **analytic definition of a quasiconformal map**. `f : ℂ → ℂ` is
quasiconformal with Beltrami coefficient `b` when it is an orientation-preserving
homeomorphism, lies in `W^{1,2}_loc(ℂ)`, and satisfies the Beltrami equation
`∂̄f = b.μ · ∂f` almost everywhere. -/
def IsQCAnalytic (f : ℂ → ℂ) (b : BeltramiCoeff) : Prop :=
  OrientationPreservingHomeo f ∧ MemW12loc f ∧ ∀ᵐ z, dzbar f z = b.μ z * dz f z

end RiemannDynamics

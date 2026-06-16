/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Modulus
import RiemannDynamics.QC.Analytic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Quasiconformal maps: the geometric definition

This file gives the **geometric** definition of a quasiconformal map, via the
quasi-invariance of the **modulus of quadrilaterals**. A quadrilateral is a
topological embedding of the closed unit square `[0, 1]²` into `ℂ`; its modulus is
the conformal modulus (`curveModulus`) of the family of curves joining the left
side `{0} × [0, 1]` to the right side `{1} × [0, 1]` inside the embedded square.
Taking the square as data sidesteps the Jordan curve theorem (which Mathlib does
not have): the four sides are the images of the four sides of the standard square.

A homeomorphism `f : ℂ → ℂ` is **`K`-quasiconformal** when it distorts the modulus
of every quadrilateral by at most the factor `K`:

`modulus (f Q) ≤ K · modulus Q` for every quadrilateral `Q`.

For a homeomorphism this single inequality (applied also to `f⁻¹`) is equivalent to
the two-sided bound `K⁻¹ · modulus Q ≤ modulus (f Q) ≤ K · modulus Q`.

This is the geometric track of the two quasiconformal definitions; the analytic
track (`IsQCAnalytic`, via the Beltrami equation) lives in `QC/Analytic.lean`, and
the two are proved equivalent in `QC/Equivalence.lean`. The geometric track owns the
compactness, removability, and Weyl (`1`-quasiconformal ⇒ conformal) lemmas.

## Main definitions

* `Quadrilateral` — a continuous embedding of the closed unit square into `ℂ`;
* `Quadrilateral.curveFamily Q` — the family of curves in the embedded square
  joining the left side to the right side;
* `Quadrilateral.modulus Q` — the conformal modulus of that curve family;
* `IsQCGeometric f K` — `f` is an orientation-preserving homeomorphism distorting
  every quadrilateral's modulus by at most `K`.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- The closed unit square `[0, 1] × [0, 1] ⊆ ℝ × ℝ`. -/
def unitSquare : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 1

/-- A **quadrilateral**: a continuous map `ℝ × ℝ → ℂ` injective on the closed unit
square. Its image is a topological square whose four sides are the images of the
four sides of `[0, 1]²`; taking the parametrization as data avoids the Jordan curve
theorem. -/
structure Quadrilateral where
  /-- The parametrizing map; only its values on `unitSquare` matter. -/
  toFun : ℝ × ℝ → ℂ
  /-- The parametrization is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The parametrization is injective on the closed unit square. -/
  injOn_unitSquare : Set.InjOn toFun unitSquare

namespace Quadrilateral

/-- The image of the closed unit square under the quadrilateral. -/
def image (Q : Quadrilateral) : Set ℂ := Q.toFun '' unitSquare

/-- The **left side** of the quadrilateral: the image of `{0} × [0, 1]`. -/
def leftSide (Q : Quadrilateral) : Set ℂ := Q.toFun '' (({0} : Set ℝ) ×ˢ Set.Icc 0 1)

/-- The **right side** of the quadrilateral: the image of `{1} × [0, 1]`. -/
def rightSide (Q : Quadrilateral) : Set ℂ := Q.toFun '' (({1} : Set ℝ) ×ˢ Set.Icc 0 1)

/-- The **connecting curve family** of the quadrilateral: absolutely continuous
curves in the embedded square that start on the left side and end on the right side.
Restricting to absolutely continuous curves is the mathematically correct domain for
the modulus: the arc-length line integral uses `deriv γ`, which is meaningful only
when `γ` is differentiable a.e. (as it is for absolutely continuous curves), and
non-rectifiable curves never lower the modulus, so the value is unchanged. -/
def curveFamily (Q : Quadrilateral) : Set (ℝ → ℂ) :=
  {γ | Continuous γ ∧ (∀ a c : ℝ, AbsolutelyContinuousOnInterval γ a c) ∧
    γ 0 ∈ Q.leftSide ∧ γ 1 ∈ Q.rightSide ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Q.image}

/-- The **modulus** of the quadrilateral: the conformal modulus of its connecting
curve family. -/
noncomputable def modulus (Q : Quadrilateral) : ℝ≥0∞ := curveModulus Q.curveFamily

/-- The **image connecting curve family** of the quadrilateral under a map `f`: the
absolutely continuous curves that join the image left side `f '' leftSide` to the
image right side `f '' rightSide` while staying inside the image region
`f '' image`. When `f` is a homeomorphism this is exactly the connecting family of
the image quadrilateral `f ∘ Q` (since `f '' (Q.toFun '' S) = (f ∘ Q.toFun) '' S`),
so its modulus is the genuine modulus `M(f(Q))`.

This is the mathematically correct object for the geometric definition: it ranges
over *all* AC curves in the image quadrilateral, not only those of the form `f ∘ γ`
with `γ` absolutely continuous. A quasiconformal map is ACL but need not send every
AC curve to an AC curve, so the pushforward `(f ∘ ·) '' Q.curveFamily` is in general
a proper subfamily with strictly smaller modulus — using it would state a condition
strictly weaker than `M(f(Q)) ≤ K · M(Q)`. -/
def imageCurveFamily (Q : Quadrilateral) (f : ℂ → ℂ) : Set (ℝ → ℂ) :=
  {δ | Continuous δ ∧ (∀ a c : ℝ, AbsolutelyContinuousOnInterval δ a c) ∧
    δ 0 ∈ f '' Q.leftSide ∧ δ 1 ∈ f '' Q.rightSide ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ f '' Q.image}

end Quadrilateral

/-- The **geometric definition of a `K`-quasiconformal map**: an
orientation-preserving homeomorphism `f : ℂ → ℂ` that distorts the modulus of every
quadrilateral by at most the factor `K`, i.e. `M(f(Q)) ≤ K · M(Q)`. Here `M(f(Q))`
is the modulus of `Q.imageCurveFamily f`, the connecting family of the image
quadrilateral `f ∘ Q` — *all* absolutely continuous curves joining the two image
sides inside the image region. (It must be this family rather than the pushforward
`(f ∘ ·) '' Q.curveFamily`: a quasiconformal map need not carry every AC curve to an
AC curve, so the pushforward is a proper subfamily of strictly smaller modulus and
would yield a strictly weaker condition.) -/
def IsQCGeometric (f : ℂ → ℂ) (K : ℝ) : Prop :=
  OrientationPreservingHomeo f ∧ ∀ Q : Quadrilateral,
    curveModulus (Q.imageCurveFamily f) ≤ ENNReal.ofReal K * Q.modulus

end RiemannDynamics

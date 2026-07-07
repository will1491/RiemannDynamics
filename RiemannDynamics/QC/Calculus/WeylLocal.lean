/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.WeakDeriv

/-!
# Weyl's lemma on an open set

The local (open-set) form of Weyl's lemma: a continuous function on an open
set `V ⊆ ℂ` whose weak `∂̄`-derivative vanishes on `V` is holomorphic on `V`.

Two interchangeable formulations are provided, matching the two ways the rest
of the development produces the weak hypothesis:

* `weyl_lemma_on` — via explicit weak-gradient witnesses `gx`, `gy` on `V`
  (the shape produced by the Cauchy-transform calculus, e.g.
  `hasWeakGradient_cauchyTransform`), with the Wirtinger combination
  `gx + I·gy` vanishing almost everywhere on `V`;
* `weyl_lemma_on_of_test` — via the distributional formulation: the
  integral of `f` against `∂̄φ` vanishes for every smooth compactly
  supported complex test function `φ` with support in `V`.

The proof route (mollification) is the one inlined for `V = univ` in
`weyl_lemma` (`QC/Calculus/Weyl.lean`): convolve `f` with a shrinking bump
family; each mollification is smooth with vanishing `∂̄` on a shrunken set,
hence holomorphic there; the mollifications converge locally uniformly to `f`
on compact subsets of `V`, so `f` is holomorphic on `V` by Weierstrass
convergence. The only new ingredient relative to the global case is the
shrinking: mollification at scale `ε` is controlled only at points whose
`ε`-neighborhood lies in `V`, and `V` is exhausted by such points.
-/

open MeasureTheory Complex
open scoped ContDiff

namespace RiemannDynamics

/-- **Weyl's lemma on an open set, weak-gradient form.** If `f` is continuous
on an open set `V ⊆ ℂ`, has weak partial derivatives `gx` (direction `1`) and
`gy` (direction `I`) on `V` that are locally integrable on `V`, and the weak
`∂̄`-combination `gx + I·gy` vanishes almost everywhere on `V`, then `f` is
holomorphic on `V`. -/
theorem weyl_lemma_on {V : Set ℂ} {f gx gy : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V)
    (hgrad : HasWeakGradient gx gy f V)
    (hgx : LocallyIntegrableOn gx V)
    (hgy : LocallyIntegrableOn gy V)
    (hcomb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ V → gx z + Complex.I * gy z = 0) :
    DifferentiableOn ℂ f V := by
  sorry

/-- **Weyl's lemma on an open set, test-function form.** If `f` is continuous
on an open set `V ⊆ ℂ` and the distributional `∂̄`-derivative of `f` vanishes
on `V` — the integral of `f` against `∂̄φ` is zero for every smooth compactly
supported complex test function `φ` with support in `V` — then `f` is
holomorphic on `V`. -/
theorem weyl_lemma_on_of_test {V : Set ℂ} {f : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V)
    (htest : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ z, dzbar φ z * f z = 0) :
    DifferentiableOn ℂ f V := by
  sorry

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.NormalFamilies.Basic
import RMT4.Montel

/-!
# Classical Montel theorem

A locally uniformly bounded family of holomorphic functions on an open set
`U ⊆ ℂ` is normal. The substance is in RMT4's `montel`; here we re-package its
total-boundedness conclusion in the `IsNormal` sequential-subsequence form
used by the dynamics line.
-/

namespace RiemannDynamics

open Set Filter Topology

/-- **Classical Montel theorem.** A locally uniformly bounded family of
holomorphic functions on an open set is normal.

The substance — equicontinuity from Cauchy estimates and total boundedness of
the family in the locally-uniform topology — is `RMT4.Montel.montel`. What
remains is repackaging that `TotallyBounded (range F)` conclusion as a
sequential subsequence-extraction statement, which requires sequential
compactness in the space `ℂ →ᵤ[compacts U] ℂ`. -/
theorem montel_locallyBounded {𝓕 : Set (ℂ → ℂ)} {U : Set ℂ}
    (hU : IsOpen U) (h : LocallyUniformlyBounded 𝓕 U)
    (hol : ∀ f ∈ 𝓕, DifferentiableOn ℂ f U) : IsNormal 𝓕 U := by
  sorry

end RiemannDynamics

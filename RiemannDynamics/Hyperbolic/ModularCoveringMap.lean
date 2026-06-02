/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.Gamma2FundamentalDomain

/-!
# Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`

The level-2 modular function `λ` is a holomorphic covering map of the
triply-punctured plane by the upper half-plane. The proof factors
through four classical statements:

* **Freeness mod `±I`** (`gamma_two_fixed_point_implies_pm_one`):
  any `γ ∈ Γ(2)` with a fixed point in `ℍ` is `±I`.
* **Proper discontinuity** (`gamma_two_properlyDiscontinuousSMul`):
  `Γ(2)` acts properly discontinuously on `ℍ`.
* **Non-vanishing derivative** (`modularLambdaH_deriv_ne_zero_on_upperHalf`):
  `λ' ≠ 0` on `ℍ`.
* **Orbit identification** (`modularLambdaH_eq_iff_gamma2_orbit`):
  `λ(τ₁) = λ(τ₂) ↔ ∃ γ ∈ Γ(2), γ • τ₁ = τ₂`.

The first two pillars depend only on the `SL₂(ℤ)`-action and live in
`Hyperbolic/ModularFunction.lean`. The last two pillars use the Step-D
biholomorphism `λ : F^o → {Im w > 0}`
(`modularLambdaH_image_fundamentalDomainInterior`) and the
fundamental-domain property of `F`, both of which are established in
`Hyperbolic/Gamma2FundamentalDomain.lean`. This file imports both and
houses pillars 3, 4, the main covering-map theorem, and its disk
companion `modularLambda_isCoveringMapOn` (transported via the Cayley
homeomorphism `𝔻 ≃ₜ ℍ`).
-/

namespace RiemannDynamics

open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## Pillar 3: non-vanishing of the derivative -/

/-- **Pillar 3: `λ'(τ) ≠ 0` for every `τ ∈ ℍ`.** Step D gives a
biholomorphism `λ : F^o → {Im w > 0}`, which by the open-mapping /
inverse-function theorem has nowhere-vanishing derivative on `F^o`.
By Γ(2)-equivariance (chain rule applied to
`modularLambdaH_gamma2_invariant`) the non-vanishing transports along
each `Γ(2)`-orbit; the fundamental-domain property of `F` ensures
every `τ ∈ ℍ` is `Γ(2)`-conjugate to a point in `F`. The boundary
arcs of `F^o` are handled by the Schwarz-reflection extension. -/
theorem modularLambdaH_deriv_ne_zero_on_upperHalf
    {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambdaH τ ≠ 0 := by
  sorry

/-! ## Pillar 4: orbit identification -/

/-- **Pillar 4: `λ` separates `Γ(2)`-orbits.** For `τ₁, τ₂ ∈ ℍ`,
`λ(τ₁) = λ(τ₂)` iff `τ₂` is in the `Γ(2)`-orbit of `τ₁`. The
forward direction is `modularLambdaH_gamma2_invariant`; the reverse
uses Step D (injectivity of `λ` on `F^o`) together with the
fundamental-domain property of `F`. -/
theorem modularLambdaH_eq_iff_gamma2_orbit
    {τ₁ τ₂ : UpperHalfPlane} :
    modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ) ↔
      ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  sorry

/-! ## Main covering-map theorems -/

/-- **Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`.** `λ` is a
holomorphic covering map. The assembly combines the four pillars:
pillar 3 (`λ' ≠ 0`) gives local biholomorphism around any preimage;
pillar 4 (orbit identification) identifies the fibre over each
`w ∈ ℂ ∖ {0, 1}` as a `Γ(2)`-orbit; pillar 1 (freeness mod `±I`)
plus pillar 2 (proper discontinuity) provide a `Γ(2)`-invariant
neighbourhood of each preimage whose translates are pairwise
disjoint, yielding the trivialisation. -/
theorem modularLambdaH_isCoveringMapOn :
    IsCoveringMapOn modularLambdaH { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

/-- **Covering property of `λ` on the unit disk.**
`modularLambda : 𝔻 → ℂ ∖ {0, 1}` is a covering map of the
triply-punctured plane by the disk. Conditional on
`modularLambdaH_isCoveringMapOn`: the Cayley transform restricts to a
homeomorphism `𝔻 ≃ₜ ℍ` (using `cayleyToHalfPlane_image_ball`,
`halfPlaneToCayley_mem_ball`, `cayleyToHalfPlane_halfPlaneToCayley`,
`halfPlaneToCayley_cayleyToHalfPlane`). For each `w ∈ ℂ ∖ {0, 1}`,
the evenly-covered neighbourhood `U` of `w` under `modularLambdaH`
(and its trivialisation `modularLambdaH ⁻¹' U ≃ₜ U × Γ(2)`) transports
through Cayley: `modularLambda ⁻¹' U` lives inside `𝔻` (since
`modularLambda` is Lean-junk `0` outside `𝔻`), Cayley-restricted gives
a homeomorphism `modularLambda ⁻¹' U ≃ₜ modularLambdaH ⁻¹' U`, then
chains with the trivialisation and the fibre Cayley to obtain the
disk-side trivialisation. -/
theorem modularLambda_isCoveringMapOn :
    IsCoveringMapOn modularLambda { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

end RiemannDynamics

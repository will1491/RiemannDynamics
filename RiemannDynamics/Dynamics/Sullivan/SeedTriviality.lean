/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.Deformation.SphereVectorField
import RiemannDynamics.QC.Calculus.WeylLocal

/-!
# The explicit seed family and its triviality criterion

The infinite-dimensional input to Sullivan's finiteness argument: an explicit
family of Beltrami *seeds* carried by a round disk, together with explicit
solutions of the corresponding `∂̄`-equations, and the **triviality
criterion**: if a sphere vector field whose `∂̄` restricts on an open set
`U'` to a linear combination of the seeds vanishes on the frontier of `U'`,
then the combination is zero.

For a disk `D = ball a ρ` the `k`-th seed (`seedBasis`, `k = 0, 1, …`) is

`σₖ(z) = (k+1)·conj(z−a)^k · 1_D`,

with the explicit solution (`seedSolution`)

`uₖ(z) = conj(z−a)^{k+1}` on `D`, `uₖ(z) = ρ^{2(k+1)}·(z−a)^{−(k+1)}` off `D`

— continuous across the circle `|z−a| = ρ` (where `conj(w)^{k+1}` equals
`(ρ²/w)^{k+1}`), with `∂̄uₖ = σₖ` weakly, holomorphic off the closed disk,
and vanishing at infinity. Off the disk the solutions assemble into the
negative-power tail `negPowerCombo`, a rational function whose only pole is
at `a`.

The triviality criterion (`seed_vanish_of_sphereField_vanish_on_frontier`)
is stated for an open `U' ⊆ ℂ` (the endgame passes the finite part of a
Fatou component and transfers frontier data through the charts): given a
sphere field `v` with `∂̄v = Σ cₖ·σₖ` a.e. on `U'` and `v = 0` on the
frontier of `U'`, the function `h := v − Σ cₖ·uₖ` is weakly holomorphic on
`U'`, hence holomorphic (open-set Weyl); damping by
`M(z) = (z−a)^K/(z−b)^{K+3}` — where `b` avoids the closure of `U'` and `K`
dominates the pole order of the tail — makes `F := (h + negPowerCombo)·M`
holomorphic on `U'` (the zero of `M` at `a` absorbs the pole), vanishing on
the frontier (there `h + negPowerCombo = v = 0`) and at infinity (`M` decays
like `|z|^{−3}` against the `O(|z|²)` growth of a sphere field). The
maximum principle for holomorphic functions with vanishing boundary and
infinity data (`eqOn_zero_of_forall_frontier_tendsto_zero`, built on
Mathlib's `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` /
`Complex.norm_le_of_forall_mem_frontier_norm_le` via compact exhaustion of
`{‖F‖ ≥ ε}`) forces `F ≡ 0`, so the negative-power tail extends
holomorphically across `a`, which kills every coefficient
(`coeffs_eq_zero_of_negPowerCombo_extends`).
-/

open MeasureTheory Complex Metric Filter Topology

namespace RiemannDynamics

/-! ## The seed family and its explicit solutions -/

/-- The `k`-th **seed coefficient** on the disk `ball a ρ`:
`(k+1)·conj(z−a)^k` inside the disk, `0` outside. The index `k` starts at
`0`; the normalizing factor `k+1` makes `seedSolution` a `∂̄`-primitive with
coefficient exactly `1`. -/
noncomputable def seedBasis (a : ℂ) (ρ : ℝ) (k : ℕ) : ℂ → ℂ := fun z =>
  open Classical in
  if z ∈ Metric.ball a ρ
    then ((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k else 0

/-- The explicit solution of `∂̄u = seedBasis a ρ k`: the anti-holomorphic
power `conj(z−a)^{k+1}` inside the disk, matched across the circle to the
holomorphic negative power `ρ^{2(k+1)}·(z−a)^{−(k+1)}` outside. Total; the
center `z = a` lies inside the disk (for `ρ > 0`), so the negative power is
only evaluated away from its pole. -/
noncomputable def seedSolution (a : ℂ) (ρ : ℝ) (k : ℕ) : ℂ → ℂ := fun z =>
  open Classical in
  if z ∈ Metric.ball a ρ
    then (starRingEnd ℂ (z - a)) ^ (k + 1)
    else ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ))

/-- A linear combination of the first `K` seeds — the general element of the
`K`-dimensional seed family. -/
noncomputable def seedCombo (a : ℂ) (ρ : ℝ) (K : ℕ) (c : Fin K → ℂ) :
    ℂ → ℂ := fun z =>
  ∑ k : Fin K, c k * seedBasis a ρ k z

/-- The **negative-power tail**: the rational function
`Σ cₖ·ρ^{2(k+1)}·(z−a)^{−(k+1)}`, holomorphic on `ℂ ∖ {a}` with its only
pole at `a`. Off the disk it is the corresponding combination of the
explicit solutions. -/
noncomputable def negPowerCombo (a : ℂ) (ρ : ℝ) (K : ℕ) (c : Fin K → ℂ) :
    ℂ → ℂ := fun z =>
  ∑ k : Fin K, c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k.1 + 1 : ℤ))

/-- Off the disk, the seed solutions assemble into the negative-power
tail. -/
theorem sum_seedSolution_eq_negPowerCombo (a : ℂ) (ρ : ℝ) (K : ℕ)
    (c : Fin K → ℂ) {z : ℂ} (hz : z ∉ Metric.ball a ρ) :
    ∑ k : Fin K, c k * seedSolution a ρ k z = negPowerCombo a ρ K c z := by
  sorry

/-- The explicit solution is continuous: inside and outside pieces are
continuous on their open domains, and they match on the circle
`|z−a| = ρ`, where `conj(w)^{k+1} = (ρ²/w)^{k+1} = ρ^{2(k+1)}·w^{−(k+1)}`
for `w = z−a`. -/
theorem seedSolution_continuous (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    Continuous (seedSolution a ρ k) := by
  sorry

/-- The explicit solution solves its `∂̄`-equation weakly, with locally
square-integrable gradient: `∂̄(seedSolution) = seedBasis` on `ℂ`. Inside
and outside the disk this is the classical Wirtinger calculus of the
explicit formulas; the pieces glue across the (null) circle because the
function is continuous there — integration by parts against a test function
picks up no boundary term. -/
theorem hasL2WeakDzbar_seedSolution (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    HasL2WeakDzbar (seedSolution a ρ k) (seedBasis a ρ k) Set.univ := by
  sorry

/-- The explicit solution is holomorphic outside the closed disk. -/
theorem differentiableOn_seedSolution (a : ℂ) (ρ : ℝ) (k : ℕ) :
    DifferentiableOn ℂ (seedSolution a ρ k) (Metric.closedBall a ρ)ᶜ := by
  sorry

/-- The explicit solution vanishes at infinity. -/
theorem seedSolution_tendsto_cocompact (a : ℂ) (ρ : ℝ) (k : ℕ) :
    Tendsto (seedSolution a ρ k) (cocompact ℂ) (nhds 0) := by
  sorry

/-! ## The maximum-modulus kill -/

/-- **Maximum principle with vanishing boundary and infinity data.** A
function holomorphic on an open set `V ⊆ ℂ`, tending to `0` at every
frontier point of `V` (from within `V`) and tending to `0` at infinity
within `V` (vacuous for bounded `V`), vanishes identically on `V`. Proof
route: for `ε > 0` the set `{z ∈ V | ε ≤ ‖F z‖}` is compact (closed in `V`
by the frontier data, bounded by the infinity data), so `‖F‖` attains a
maximum `≥ ε` at an interior point of `V`; Mathlib's maximum-modulus
principle (`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`, applied on a
ball around the maximum, or the frontier-norm bound
`Complex.norm_le_of_forall_mem_frontier_norm_le` on the compact piece)
propagates the maximum to the frontier, contradicting the boundary data. -/
theorem eqOn_zero_of_forall_frontier_tendsto_zero {V : Set ℂ} (hV : IsOpen V)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F V)
    (hfront : ∀ p ∈ frontier V, Tendsto F (nhdsWithin p V) (nhds 0))
    (hinfty : Tendsto F (cocompact ℂ ⊓ Filter.principal V) (nhds 0)) :
    ∀ z ∈ V, F z = 0 := by
  sorry

/-! ## The triviality criterion -/

/-- **Weak holomorphy of the corrected field.** If `v` has weak
`∂̄`-derivative `μ` on `ℂ` and `μ` agrees a.e. on the open set `U'` with the
seed combination, then subtracting the explicit solutions kills the weak
`∂̄` on `U'`, and the open-set Weyl lemma makes the difference holomorphic
on `U'`. -/
theorem differentiableOn_sub_seedSolutions {U' : Set ℂ} (hU' : IsOpen U')
    {v μ : ℂ → ℂ} (hv : Continuous v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {K : ℕ} {c : Fin K → ℂ}
    (hloc : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U' → μ z = seedCombo a ρ K c z) :
    DifferentiableOn ℂ
      (fun z => v z - ∑ k : Fin K, c k * seedSolution a ρ k z) U' := by
  sorry

/-- **The pole-cancellation endgame** (elementary Laurent algebra). If the
negative-power tail agrees, away from `a`, with a function holomorphic in a
neighborhood of `a`, then every coefficient vanishes: multiplying by
`(z−a)^K` and evaluating derivatives at `a` (or comparing Laurent
coefficients through Cauchy integrals over small circles) isolates each
`cₖ·ρ^{2(k+1)} ≠ 0`-candidate in turn. -/
theorem coeffs_eq_zero_of_negPowerCombo_extends {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {K : ℕ} {c : Fin K → ℂ} {h : ℂ → ℂ} {W : Set ℂ}
    (hW : IsOpen W) (ha : a ∈ W) (hh : DifferentiableOn ℂ h W)
    (heq : ∀ z ∈ W, z ≠ a → h z = negPowerCombo a ρ K c z) :
    c = 0 := by
  sorry

/-- **The seed-triviality criterion.** Let `U' ⊆ ℂ` be open, carrying a
closed disk `closedBall a ρ ⊆ U'`, with some point `b ∉ closure U'`
available for damping. If a sphere vector field `v` has weak `∂̄`-derivative
`μ` on `ℂ` that agrees a.e. on `U'` with the seed combination `Σ cₖ·σₖ`, and
`v` vanishes on the frontier of `U'`, then `c = 0`.

Proof route: `h := v − Σ cₖ·uₖ` is holomorphic on `U'`
(`differentiableOn_sub_seedSolutions`) and equals `v − negPowerCombo`
outside the disk; with `M(z) := (z−a)^K/(z−b)^{K+3}`, the product
`F := (h + negPowerCombo)·M` is holomorphic on `U'` (removable singularity
at `a`: the zero of `M` dominates the pole of the tail), tends to `0` at
every frontier point (there `h + negPowerCombo = v → 0`) and at infinity
within `U'` (sphere-field growth `O(|z|²)` against `M = O(|z|^{−3})`), so
`F ≡ 0` by the maximum principle; since `M ≠ 0` off `{a, b}`, the tail
`negPowerCombo = −h` extends holomorphically across `a`, and
`coeffs_eq_zero_of_negPowerCombo_extends` gives `c = 0`. -/
theorem seed_vanish_of_sphereField_vanish_on_frontier
    {U' : Set ℂ} (hU' : IsOpen U')
    {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall a ρ ⊆ U')
    (hb : ∃ b : ℂ, b ∉ closure U')
    {K : ℕ} {c : Fin K → ℂ} {v μ : ℂ → ℂ}
    (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hloc : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U' → μ z = seedCombo a ρ K c z)
    (hfront : ∀ p ∈ frontier U', v p = 0) :
    c = 0 := by
  sorry

end RiemannDynamics

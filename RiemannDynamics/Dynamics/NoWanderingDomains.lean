/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.Sullivan.EventualInjectivity
import RiemannDynamics.Dynamics.Sullivan.Spreading
import RiemannDynamics.Dynamics.Sullivan.SeedTriviality

/-!
# Sullivan's No Wandering Domains theorem

Every Fatou component of a rational map of degree at least two is eventually
periodic; equivalently, no component wanders. The proof is the infinitesimal
deformation argument:

1. *Normalization* (`exists_wandering_injective_package`): replace a
   wandering component by a later orbit component `U` on which every iterate
   is injective and whose orbit avoids `∞` and the critical points.
2. *Seeds and spreading*: fix a closed disk in the finite part of `U`
   (`IsFatouComponent.exists_closedBall_subset`); each seed combination
   `σ_c` (`seedCombo`, `K = 2d+2` seeds) spreads to an `f`-invariant
   coefficient `μ_c` on `ℂ` (`spreadCoeff`), agreeing with `σ_c` on `U` and
   with `‖μ_c‖∞ ≤ ‖σ_c‖∞`.
3. *Solve and project*: `v_c := dbarSolver μ_c` is a sphere vector field
   with `∂̄v_c = μ_c`; invariance places its deformation field
   `δv_c = f′·v_c − v_c∘f` in the `(2d+1)`-dimensional section space
   (`exists_sectionSpace_rep_deltaField`). The assignment `c ↦ [δv_c]` is
   linear — every stage (seed, spread, solver, delta, carrier
   representative) is linear — from a `(2d+2)`-dimensional space into a
   `(2d+1)`-dimensional one, so some `c ≠ 0` has `δv_c = 0` off the poles
   (`exists_nonzero_seed_with_deltaField_eq_zero`).
4. *Contradiction*: a trivial deformation vanishes on the Julia set
   (`sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero`), hence on the
   frontier of `U` (which lies in the Julia set); the seed-triviality
   criterion (`seed_vanish_of_sphereField_vanish_on_frontier`, with a
   damping point outside the closure of `U` supplied by the disjoint next
   orbit component) then forces `c = 0` — a contradiction
   (`not_isWandering_of_injective_package`).

The eventually-periodic form follows through the wandering dichotomy
`isWandering_iff_not_isEventuallyPeriodic`.
-/

open MeasureTheory Complex Metric Filter Topology Function OnePoint

namespace RiemannDynamics

/-! ## Assembly nodes -/

/-- A Fatou component contains a closed disk in its finite part: the
component is open and nonempty, and it cannot reduce to `{∞}` since the
sphere has no isolated points, so it contains a finite point together with
a chart ball around it. -/
theorem IsFatouComponent.exists_closedBall_subset {f : ℂ̂ → ℂ̂} {U : Set ℂ̂}
    (hU : IsFatouComponent f U) :
    ∃ (a : ℂ) (ρ : ℝ), 0 < ρ ∧
      ∀ z ∈ Metric.closedBall a ρ, ((z : ℂ̂) ∈ U) := by
  sorry

/-- The frontier of the finite part transfers to the frontier upstairs: the
coercion `ℂ → ℂ̂` is an open embedding, so a finite-chart frontier point of
`{z | ↑z ∈ U}` maps to a frontier point of `U`. -/
theorem frontier_finitePart_subset (U : Set ℂ̂) :
    frontier {z : ℂ | ((z : ℂ̂) ∈ U)}
      ⊆ {z : ℂ | ((z : ℂ̂) ∈ frontier U)} := by
  sorry

/-- **A damping point exists** for a wandering component: some finite point
avoids the closure of the finite part of `U`. The next orbit component
`fcOrbit f U 1` is open, nonempty, and disjoint from `U`; were it contained
in the closure of `U` it would lie in the frontier of `U`, hence in the
Julia set — contradicting that it consists of Fatou points. A finite point
of it works. -/
theorem exists_damping_point {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U) :
    ∃ b : ℂ, b ∉ closure {z : ℂ | ((z : ℂ̂) ∈ U)} := by
  sorry

/-- **Bridging critical-avoidance formats**: from stepwise nonvanishing of
the finite-chart derivative of `f` on every orbit component (the format
produced by `exists_wandering_injective_package`) to nonvanishing of the
orbit derivative cocycle `iterDeriv` on `U` (the format consumed by the
spreading theorems): the orbit of a point of `U` visits the successive orbit
components, stays finite, and each factor of the product is a nonzero
step derivative. -/
theorem iterDeriv_ne_zero_of_orbit_noncritical
    {r : RationalData} (hd : 1 ≤ r.degree) {U : Set ℂ̂}
    (hU : IsFatouComponent r.toSphereMap U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit r.toSphereMap U n) →
      deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) z ≠ 0) :
    ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0 := by
  sorry

/-- **The rank–nullity extraction.** Under the injectivity package and with
a seed disk in the finite part of `U`, some nonzero seed combination has
vanishing deformation field: the assignment

`c ↦ (carrier representative of) δ(dbarSolver (spreadCoeff (σ_c)))`

is a linear map from the `(2d+2)`-dimensional seed space into the
`(2d+1)`-dimensional section space — linearity composes from
`spreadCoeff_add`/`spreadCoeff_smul`, `dbarSolver_add`/`dbarSolver_smul`
(fed by `spreadCoeff_aemeasurable` and `spreadCoeff_eLpNormEssSup_le`),
pointwise linearity of `deltaField` in the field, and uniqueness of the
carrier representative (`sectionSpaceCarrier_eqOn_nonpoles_eq`) — so its
kernel is nontrivial by `finrank_sectionSpaceCarrier` and dimension
counting. A kernel element `c ≠ 0` has `δ(dbarSolver μ_c) = 0` at every
non-pole. -/
theorem exists_nonzero_seed_with_deltaField_eq_zero
    {r : RationalData} (hd : 2 ≤ r.degree)
    {U : Set ℂ̂} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hball : ∀ z ∈ Metric.closedBall a ρ, ((z : ℂ̂) ∈ U)) :
    ∃ c : Fin (2 * r.degree + 2) → ℂ, c ≠ 0 ∧
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
        deltaField r
          (dbarSolver (spreadCoeff r (Metric.closedBall a ρ)
            (seedCombo a ρ (2 * r.degree + 2) c))) z = 0 := by
  sorry

/-- **The contradiction core.** A Fatou component carrying the full
injectivity package cannot wander: a nonzero seed `c` with trivial
deformation field exists by rank–nullity; the associated sphere field
`v_c = dbarSolver μ_c` vanishes on the (finite) Julia set, hence on the
frontier of the finite part of `U`; the seed-triviality criterion — with a
damping point from `exists_damping_point` and the restriction law
`spreadCoeff_restrict` identifying `∂̄v_c` with `σ_c` on `U` — forces
`c = 0`. -/
theorem not_isWandering_of_injective_package
    {r : RationalData} (hd : 2 ≤ r.degree) {U : Set ℂ̂}
    (hU : IsFatouComponent r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0) :
    ¬ IsWandering r.toSphereMap U := by
  sorry

/-! ## The theorem -/

/-- **Sullivan's No Wandering Domains theorem.** No Fatou component of a
rational map of degree at least two wanders: normalize by the eventual
injectivity package, bridge the map to a `RationalData` witness, and apply
the contradiction core — noting that if the relabeled component
`fcOrbit f U N` were shown non-wandering while `U` wandered, the orbit
disjointness of `U` would be violated. -/
theorem sullivan_no_wandering_domains {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f) :
    ∀ U : Set ℂ̂, IsFatouComponent f U → ¬ IsWandering f U := by
  sorry

/-- **Every Fatou component is eventually periodic** — the positive form of
Sullivan's theorem, through the wandering / eventually-periodic
dichotomy. -/
theorem fatouComponent_isEventuallyPeriodic {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) :
    IsEventuallyPeriodic f U := by
  sorry

end RiemannDynamics

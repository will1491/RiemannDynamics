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
  have hopen : IsOpen U := hU.isOpen
  have hne : U.Nonempty := hU.nonempty
  have hdense : Dense (Set.range ((↑) : ℂ → ℂ̂)) := OnePoint.denseRange_coe
  obtain ⟨x, hxU, hxr⟩ := hdense.inter_open_nonempty U hopen hne
  obtain ⟨a, rfl⟩ := hxr
  have hpre : IsOpen {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    hopen.preimage OnePoint.continuous_coe
  have haU : a ∈ {z : ℂ | ((z : ℂ̂) ∈ U)} := hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre a haU
  refine ⟨a, ε / 2, by positivity, fun z hz => ?_⟩
  exact hball (Metric.mem_ball.mpr
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))

/-- The frontier of the finite part transfers to the frontier upstairs: the
coercion `ℂ → ℂ̂` is an open embedding, so a finite-chart frontier point of
`{z | ↑z ∈ U}` maps to a frontier point of `U`. -/
theorem frontier_finitePart_subset (U : Set ℂ̂) :
    frontier {z : ℂ | ((z : ℂ̂) ∈ U)}
      ⊆ {z : ℂ | ((z : ℂ̂) ∈ frontier U)} := by
  intro z hz
  have hc : Continuous ((↑) : ℂ → ℂ̂) := OnePoint.continuous_coe
  have hclU : ((z : ℂ̂)) ∈ closure U :=
    hc.closure_preimage_subset U hz.1
  have hintU : ((z : ℂ̂)) ∉ interior U := by
    intro hmem
    exact hz.2 (preimage_interior_subset_interior_preimage hc hmem)
  exact ⟨hclU, hintU⟩

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
  have hU₁ : IsFatouComponent f (fcOrbit f U 1) :=
    isFatouComponent_fcOrbit 1 hf hd hU
  have hdisj : Disjoint U (fcOrbit f U 1) := by
    have h01 := isWandering_iff.mp hW 0 1 (by norm_num)
    rwa [fcOrbit_zero hU] at h01
  have hdense : Dense (Set.range ((↑) : ℂ → ℂ̂)) := OnePoint.denseRange_coe
  obtain ⟨x, hxU₁, hxr⟩ := hdense.inter_open_nonempty _ hU₁.isOpen hU₁.nonempty
  obtain ⟨b, rfl⟩ := hxr
  refine ⟨b, fun hbcl => ?_⟩
  have hbU : b ∉ {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    fun h => Set.disjoint_left.mp hdisj h hxU₁
  have hbfr : b ∈ frontier {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    ⟨hbcl, fun h => hbU (interior_subset h)⟩
  have hfrU : ((b : ℂ̂)) ∈ frontier U := frontier_finitePart_subset U hbfr
  have hjul : ((b : ℂ̂)) ∈ JuliaSet f := hU.frontier_subset_juliaSet hfrU
  exact Set.disjoint_left.mp (disjoint_fatouSet_juliaSet f)
    (hU₁.subset_fatouSet hxU₁) hjul

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
  intro z hz n
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 1 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  have hfo : IsOpenMap r.toSphereMap := hfr.isOpenMap (hfr.ne_const hdeg)
  have hfwd : ∀ k : ℕ,
      r.toSphereMap^[k] ((z : ℂ̂)) ∈ FatouSet r.toSphereMap := by
    intro k
    induction k with
    | zero => simpa using hU.subset_fatouSet hz
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo ih
  have hmem : ∀ k : ℕ,
      r.toSphereMap^[k] ((z : ℂ̂)) ∈ fcOrbit r.toSphereMap U k :=
    fun k => Set.mem_biUnion hz (mem_connectedComponentIn (hfwd k))
  unfold iterDeriv
  rw [Finset.prod_ne_zero_iff]
  intro j _hj
  have hjfin : r.toSphereMap^[j] ((z : ℂ̂)) ≠ ∞ := fun h => hinf j (h ▸ hmem j)
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hjfin
  have hwmem : ((w : ℂ̂)) ∈ fcOrbit r.toSphereMap U j := by
    rw [hw]; exact hmem j
  have hden : r.denReduced.eval w ≠ 0 := by
    intro h0
    have hnext : r.toSphereMap^[j + 1] ((z : ℂ̂)) = ∞ := by
      rw [Function.iterate_succ_apply', ← hw]
      show r.toSphereMap ((w : ℂ̂)) = ∞
      simp only [RationalData.toSphereMap]
      rw [if_pos h0]
    exact hinf (j + 1) (hnext ▸ hmem (j + 1))
  rw [← hw]
  have hread : chartFiniteMap ((w : ℂ̂)) = w := rfl
  rw [hread, fderivRational_eq_deriv_reading r hden]
  exact hcrit j w hwmem

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
  intro U hU hW
  -- Bridge the map to a `RationalData` witness.
  obtain ⟨r, rfl⟩ := hf
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdr : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  -- Normalize: pass to a later orbit component carrying the full package.
  obtain ⟨N, hUC, hWC, hinj, hinf, hcrit⟩ :=
    exists_wandering_injective_package hfr hd hU hW
  -- Convert stepwise critical-avoidance to the `iterDeriv` cocycle format.
  have hcrit' : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit r.toSphereMap U N) →
      ∀ n : ℕ, iterDeriv r n z ≠ 0 :=
    iterDeriv_ne_zero_of_orbit_noncritical (le_trans one_le_two hdr)
      hUC hinf hcrit
  -- The contradiction core refutes the wandering of the relabeled component.
  exact not_isWandering_of_injective_package hdr hUC hinj hinf hcrit' hWC

/-- **Every Fatou component is eventually periodic** — the positive form of
Sullivan's theorem, through the wandering / eventually-periodic
dichotomy. -/
theorem fatouComponent_isEventuallyPeriodic {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) :
    IsEventuallyPeriodic f U := by
  by_contra hnep
  have hW : IsWandering f U :=
    (isWandering_iff_not_isEventuallyPeriodic hf
      (le_trans one_le_two hd) hU).mpr hnep
  exact sullivan_no_wandering_domains hf hd U hU hW

end RiemannDynamics

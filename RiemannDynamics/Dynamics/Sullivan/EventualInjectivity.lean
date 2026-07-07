/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.FatouComponents.Periodic
import RiemannDynamics.Dynamics.JuliaFatou.RepellingDensity

/-!
# Eventual injectivity on a wandering component (interface)

The normalization wall of the No Wandering Domains theorem: a wandering Fatou
component may be relabeled along its forward orbit so that, from some time
on, every iterate is injective on the component and the orbit components
avoid `∞` and the critical points of the map.

This file states the *interface only*. The two soft normalizations are
finiteness pigeonholing: the orbit components are pairwise disjoint, `∞`
lies in at most one of them, and the finitely many critical points of a
rational map meet only finitely many of them. The injectivity clause is the
hard dichotomy: each component step `f : Uₙ → Uₙ₊₁` is proper and eventually
critical-point-free, hence a covering of some degree `≥ 1`; if infinitely
many steps had degree `≥ 2`, the moduli of a suitable separating curve
family would grow without bound through the orbit, producing essential
annuli of arbitrarily large modulus separating the (uniformly perfect) Julia
set — a contradiction. The internal development of this dichotomy is a later
sub-architecture; downstream files consume only the statement below.

The file also hosts the small shared lemma that the frontier of a Fatou
component lies in the Julia set, consumed by several parts of the endgame.
-/

open Function OnePoint

namespace RiemannDynamics

/-- The frontier of a Fatou component is contained in the Julia set: the
Fatou set is open, so a frontier point of the component that were in the
Fatou set would lie in the interior of some component meeting `U`, hence in
`U` itself — contradicting that an open set is disjoint from its own
frontier. -/
theorem IsFatouComponent.frontier_subset_juliaSet {f : ℂ̂ → ℂ̂} {U : Set ℂ̂}
    (hU : IsFatouComponent f U) :
    frontier U ⊆ JuliaSet f := by
  intro x hx
  rw [hU.isOpen.frontier_eq] at hx
  obtain ⟨hxcl, hxU⟩ := hx
  by_contra hxJ
  have hxF : x ∈ FatouSet f := by
    by_contra h
    exact hxJ h
  set W := connectedComponentIn (FatouSet f) x with hW
  have hWfc : IsFatouComponent f W := isFatouComponent_connectedComponentIn hxF
  have hxW : x ∈ W := mem_connectedComponentIn hxF
  obtain ⟨y, hyW, hyU⟩ := mem_closure_iff.mp hxcl W hWfc.isOpen hxW
  have hWU : W = U := hWfc.eq_of_mem hU hyW hyU
  exact hxU (hWU ▸ hxW)

/-- **Avoidance pigeonhole.** Along a wandering orbit the components are
pairwise disjoint, so `∞` (one point) and the critical points of `f`
(finitely many, as zeros of the wronskian reading together with the finitely
many `∞`-chart criticalities) meet only finitely many orbit components: from
some index on, every orbit component avoids `∞` and contains no critical
point of `f`. -/
theorem exists_avoidance_index {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U) :
    ∃ N : ℕ, ∀ n : ℕ,
      ∞ ∉ fcOrbit f U (N + n) ∧
      ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U (N + n)) →
        deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0 := by
  sorry

/-- **Component maps are surjective**: a rational map of degree at least one
sends each orbit component onto the next. The image is open (rational maps
are open) and relatively closed in the connected target component (a
boundary point of the image inside the target would be the image of a
boundary point of the source, but frontiers of Fatou components map into the
Julia set), hence clopen and nonempty. -/
theorem fcOrbit_image_eq {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ) :
    f '' fcOrbit f U n = fcOrbit f U (n + 1) := by
  sorry

/-- **Properness of the component restriction, fiber form**: the fiber of
the component map over an interior point of the target component is compact
— it is the intersection of the compact global fiber with the source
component, and no boundary point of the source can map into the (Fatou)
target since frontiers map into the Julia set. -/
theorem isCompact_fiber_inter {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    {w : ℂ̂} (hw : w ∈ fcOrbit f U (n + 1)) :
    IsCompact (f ⁻¹' {w} ∩ fcOrbit f U n) := by
  sorry

/-- **Constant fiber count**: when the source component contains neither `∞`
nor critical points, the component map is a proper local homeomorphism onto
the connected target, so its fiber cardinality is finite, positive, and the
same over every target point (stack of records: finitely many disjoint local
sheets plus the properness exclusion of stray preimages). -/
theorem exists_fiberCount {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k := by
  sorry

/-- A component step with constant fiber count one is injective on the
source component. -/
theorem injOn_of_fiberCount_one {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (h1 : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = 1) :
    Set.InjOn f (fcOrbit f U n) := by
  sorry

/-- **Injectivity telescopes**: if every single component step from index
`N` on is injective, then every iterate is injective on the `N`-th
component (finite induction along the orbit, using that iterates stay in
the orbit components). -/
theorem injOn_iterate_of_tail_injective {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (N : ℕ)
    (hstep : ∀ m : ℕ, N ≤ m → Set.InjOn f (fcOrbit f U m)) :
    ∀ n : ℕ, Set.InjOn (f^[n]) (fcOrbit f U N) := by
  sorry

/-- **The hard branch of the dichotomy**: a wandering orbit cannot have
covering steps of fiber count at least two cofinally often. Each such step
multiplies the modulus of a separating curve family of the (multiply
connected) target component by the fiber count, and homeomorphic steps
preserve it, so cofinally many multiple steps drive the modulus of an
essential separating configuration in the Fatou set beyond every bound —
producing essential annuli of arbitrarily large modulus separating the
Julia set, which contradicts the uniform-perfectness-type bound obtained
from the definite-size Montel expansion at Julia points. -/
theorem not_cofinal_multiple_steps {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    (hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ k : ℕ, 2 ≤ k ∧
      ∀ w ∈ fcOrbit f U (n + 1),
        (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    False := by
  sorry

/-- **Eventual injectivity package** for a wandering component. A wandering
Fatou component of a rational map of degree at least two may be replaced by
a later component of its own orbit (`fcOrbit f U N`, again a wandering Fatou
component) on which

* every iterate of `f` is injective,
* no orbit component contains `∞`, and
* no orbit component contains a critical point of `f` (phrased through the
  finite-chart derivative at finite points — orbit components avoid `∞`, so
  this is the full critical-avoidance statement).

This is exactly the hypothesis package consumed by the spreading
construction (`Spreading.lean`) and the endgame
(`NoWanderingDomains.lean`). -/
theorem exists_wandering_injective_package {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U) :
    ∃ N : ℕ,
      IsFatouComponent f (fcOrbit f U N) ∧
      IsWandering f (fcOrbit f U N) ∧
      (∀ n : ℕ, Set.InjOn (f^[n]) (fcOrbit f U N)) ∧
      (∀ n : ℕ, ∞ ∉ fcOrbit f (fcOrbit f U N) n) ∧
      (∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f (fcOrbit f U N) n) →
        deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0) := by
  sorry

end RiemannDynamics

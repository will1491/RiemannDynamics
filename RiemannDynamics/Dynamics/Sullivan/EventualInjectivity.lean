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

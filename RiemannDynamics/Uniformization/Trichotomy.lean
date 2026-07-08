/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.HolomorphicEquiv
import RiemannDynamics.Analysis.Winding.GridPrimitives
import RMT4.Main

/-!
# The uniformization trichotomy

Every nonempty, connected, simply connected domain of the Riemann sphere is
biholomorphic to exactly one of the unit disc, the plane, or the sphere
(`sphere_domain_trichotomy`), and — through a holomorphic embedding into the
sphere — the same holds for every abstract simply connected Riemann surface
(`uniformization_trichotomy`).

The route to the disc case is the Riemann mapping theorem for plane domains:
simple connectivity forces every connected component of the complement to be
unbounded (`unbounded_connectedComponentIn_compl_of_simplyConnectedSpace`),
which yields holomorphic primitives on the domain and hence the hypotheses of
the mapping theorem. The sphere case is Möbius normalization; the plane case
is the complement-of-one-point reading in the finite chart. The three models
are mutually non-biholomorphic: compactness separates `ℂ̂` from the other two,
and Liouville's theorem separates `ℂ` from the disc.

## Main statements

* `sphere_domain_trichotomy` — the trichotomy for domains `U : Opens ℂ̂`;
* `planar_dichotomy` — a simply connected plane domain is biholomorphic to
  the disc or to `ℂ`;
* `uniformization_trichotomy` — the trichotomy for abstract simply connected
  Riemann surfaces, reduced through
  `exists_diffeomorph_opens_sphere_of_simplyConnected`.
-/

open OnePoint Topology TopologicalSpace Metric
open scoped Manifold ContDiff

namespace RiemannDynamics

/-- The open unit disc as a plane domain, the disc model of the trichotomy. -/
def unitDiscOpens : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-! ## From simple connectivity to holomorphic primitives -/

/-- In a simply connected open plane set, every connected component of the
complement is unbounded: a bounded complementary component would be enclosed
by an essential loop of the domain. -/
theorem unbounded_connectedComponentIn_compl_of_simplyConnectedSpace
    {U : Set ℂ} (hU : IsOpen U) (hsc : SimplyConnectedSpace ↥U) :
    ∀ z ∉ U, ¬Bornology.IsBounded (connectedComponentIn Uᶜ z) := by
  sorry

/-- A simply connected open plane set admits holomorphic primitives for all
holomorphic functions. -/
theorem has_primitives_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    (hsc : SimplyConnectedSpace ↥U) : has_primitives U := by
  exact has_primitives_of_unbounded_components hU
    (unbounded_connectedComponentIn_compl_of_simplyConnectedSpace hU hsc)

/-- **The Riemann mapping theorem** for simply connected plane domains: a
nonempty, connected, simply connected open proper subset of `ℂ` maps
holomorphically and injectively onto the unit disc. -/
theorem exists_riemannMap_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsConnected U) (hne : U ≠ Set.univ)
    (hsc : SimplyConnectedSpace ↥U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ Set.InjOn f U ∧
      f '' U = Metric.ball 0 1 := by
  exact RMT hU hUc hne (has_primitives_of_simplyConnectedSpace hU hsc)

/-! ## The trichotomy for plane and sphere domains -/

/-- **Planar dichotomy**: a nonempty, connected, simply connected plane domain
is biholomorphic to the unit disc or to the plane. -/
theorem planar_dichotomy (U : Opens ℂ) (hUc : IsConnected (U : Set ℂ))
    (hsc : SimplyConnectedSpace ↥U) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  by_cases hne : (U : Set ℂ) = Set.univ
  · right
    have hU : U = ⊤ := Opens.ext (by simpa using hne)
    subst hU
    exact nonempty_diffeomorph_top ℂ
  · left
    obtain ⟨f, hf, hinj, himg⟩ :=
      exists_riemannMap_of_simplyConnectedSpace U.isOpen hUc hne hsc
    exact nonempty_diffeomorph_of_injOn_differentiableOn U unitDiscOpens f hf hinj himg

/-- **The uniformization trichotomy for sphere domains**: a nonempty,
connected, simply connected domain of the Riemann sphere is biholomorphic to
the unit disc, the plane, or the whole sphere. -/
theorem sphere_domain_trichotomy (U : Opens ℂ̂)
    (hUc : IsConnected (U : Set ℂ̂)) (hsc : SimplyConnectedSpace ↥U) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
        Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  sorry

/-! ## Separation of the three models -/

/-- Liouville separation: the plane is not biholomorphic to the unit disc. -/
theorem not_nonempty_diffeomorph_complex_unitDisc :
    ¬ Nonempty (ℂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) := by
  rintro ⟨e⟩
  -- The composite `F = Subtype.val ∘ e : ℂ → ℂ` is an entire function.
  have hFsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ e : ℂ → ℂ) :=
    contMDiff_subtype_val.comp e.contMDiff
  have hFdiff : Differentiable ℂ (Subtype.val ∘ e : ℂ → ℂ) :=
    hFsmooth.contDiff.differentiable (by simp)
  -- Its range lies in the unit ball, hence is bounded.
  have hFbdd : Bornology.IsBounded (Set.range (Subtype.val ∘ e : ℂ → ℂ)) :=
    (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
      (Set.range_subset_iff.mpr fun z => (e z).2)
  -- Liouville: `F` takes the same value at `0` and `1`, contradicting injectivity.
  have h01 : (e 0 : ℂ) = (e 1 : ℂ) := hFdiff.apply_eq_apply_of_bounded hFbdd 0 1
  exact zero_ne_one (e.toEquiv.injective (Subtype.ext h01))

/-- Compactness separation: the sphere is not biholomorphic to the plane. -/
theorem not_nonempty_diffeomorph_sphere_complex :
    ¬ Nonempty (ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  rintro ⟨e⟩
  have hcs : CompactSpace ℂ := e.toHomeomorph.compactSpace
  exact not_compactSpace_iff.mpr inferInstance hcs

/-- Compactness separation: the sphere is not biholomorphic to the unit
disc. -/
theorem not_nonempty_diffeomorph_sphere_unitDisc :
    ¬ Nonempty (ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) := by
  rintro ⟨e⟩
  have hcs : CompactSpace ↥unitDiscOpens := e.toHomeomorph.compactSpace
  have hc : IsCompact (Metric.ball (0 : ℂ) 1) := isCompact_iff_compactSpace.mpr hcs
  have hcl : closure (Metric.ball (0 : ℂ) 1) = Metric.ball (0 : ℂ) 1 :=
    hc.isClosed.closure_eq
  rw [closure_ball (0 : ℂ) one_ne_zero] at hcl
  have h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hcl] at h1
  simp [Metric.mem_ball, dist_eq_norm] at h1

/-! ## The abstract trichotomy -/

/-- **Planarity of simply connected Riemann surfaces**: every connected,
simply connected one-dimensional complex manifold embeds biholomorphically
onto a domain of the Riemann sphere. -/
theorem exists_diffeomorph_opens_sphere_of_simplyConnected (M : Type*)
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    [T2Space M] [ConnectedSpace M] [SimplyConnectedSpace M]
    [SecondCountableTopology M] :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  sorry

/-- **The uniformization trichotomy**: every connected, simply connected
Riemann surface is biholomorphic to the unit disc, the plane, or the Riemann
sphere. -/
theorem uniformization_trichotomy (M : Type*) [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [T2Space M] [ConnectedSpace M]
    [SimplyConnectedSpace M] [SecondCountableTopology M] :
    Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
        Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  sorry

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.SphereManifold
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Biholomorphic equivalences of one-dimensional complex manifolds

Shared infrastructure for the uniformization trichotomy: a biholomorphism
between one-dimensional complex-analytic manifolds is an analytic
`Diffeomorph` over the model `𝓘(ℂ)`, written `M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ N`. This
file provides the production and transport lemmas that every case of the
trichotomy consumes:

* an injective holomorphic map between plane domains is biholomorphic onto its
  image (`nonempty_diffeomorph_of_injOn_differentiableOn`);
* the full space `M` is biholomorphic to the open set `⊤ : Opens M`
  (`nonempty_diffeomorph_top`);
* every Möbius transformation of `ℂ̂` is a biholomorphism
  (`exists_glSMul_diffeomorph`);
* a biholomorphism restricts to a biholomorphism between an open set and its
  image (`exists_diffeomorph_opens_image`);
* a domain in `ℂ̂` avoiding `∞` reads as a plane domain through the finite
  chart (`exists_diffeomorph_opens_planar`);
* simple connectivity transfers along homeomorphisms
  (`simplyConnectedSpace_of_homeomorph`).
-/

open OnePoint Topology TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

/-! ## Topological transfer -/

/-- Simple connectivity is a topological invariant: it transfers along any
homeomorphism. -/
theorem simplyConnectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (h : SimplyConnectedSpace X) :
    SimplyConnectedSpace Y := by
  haveI := h
  exact e.toHomotopyEquiv.symm.simplyConnectedSpace

/-! ## Producing biholomorphisms -/

/-- The open set `⊤ : Opens M` of a one-dimensional complex manifold is
biholomorphic to `M` itself. -/
theorem nonempty_diffeomorph_top (M : Type*) [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] :
    Nonempty (↥(⊤ : Opens M) ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ M) := by
  refine ⟨{
    toFun := Subtype.val
    invFun := fun x => ⟨x, trivial⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl
    contMDiff_toFun := contMDiff_subtype_val
    contMDiff_invFun := fun x => ?_ }⟩
  have h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y : ↥(⊤ : Opens M) => ((⟨y, trivial⟩ : ↥(⊤ : Opens M))))
      (⟨x, trivial⟩ : ↥(⊤ : Opens M)) := by
    have hid : (fun y : ↥(⊤ : Opens M) => ((⟨y, trivial⟩ : ↥(⊤ : Opens M)))) = id := rfl
    rw [hid]
    exact contMDiffAt_id
  exact (contMDiffAt_subtype_iff
    (f := fun z : M => (⟨z, trivial⟩ : ↥(⊤ : Opens M)))
    (x := (⟨x, trivial⟩ : ↥(⊤ : Opens M)))).mp h

/-- An injective holomorphic map between plane domains is a biholomorphism
onto its image: the inverse is automatically holomorphic. -/
theorem nonempty_diffeomorph_of_injOn_differentiableOn (U V : Opens ℂ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    (himg : f '' U = V) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥V) := by
  sorry

/-- Every Möbius transformation acts on the Riemann sphere as a
biholomorphism. -/
theorem exists_glSMul_diffeomorph (g : GL (Fin 2) ℂ) :
    ∃ e : ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂, ⇑e = (g • ·) := by
  sorry

/-! ## Transporting biholomorphisms -/

/-- A biholomorphism restricts to a biholomorphism from any open set onto its
image. -/
theorem exists_diffeomorph_opens_image {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]
    (e : M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ N) (U : Opens M) :
    ∃ V : Opens N, (V : Set N) = ⇑e '' U ∧
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥V) := by
  sorry

/-- A domain in the Riemann sphere avoiding `∞` is biholomorphic, through the
finite chart, to a plane domain whose points are the finite points of the
domain. -/
theorem exists_diffeomorph_opens_planar (U : Opens ℂ̂)
    (hU : (∞ : ℂ̂) ∉ (U : Set ℂ̂)) :
    ∃ V : Opens ℂ, ((↑) : ℂ → ℂ̂) '' V = U ∧
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥V) := by
  sorry

end RiemannDynamics

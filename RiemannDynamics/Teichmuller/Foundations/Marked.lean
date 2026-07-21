import RiemannDynamics.Teichmuller.Foundations.Def
import RiemannDynamics.Surface.GenusSurface
import RiemannDynamics.Uniformization.Fuchsian
import RiemannDynamics.Uniformization.GenusHyperbolic

/-!
# The Fuchsian base of a compact hyperbolic surface

`fuchsianBase_of_isHyperbolic` packages the Fuchsian uniformization of a compact connected
hyperbolic Riemann surface into the hypothesis triple over which the Teichmüller theory is
developed: a Fuchsian group `Γ₀ ≤ SL(2, ℝ)` whose elements with a fixed point act trivially
on the upper half plane and whose orbit space is compact.

Instantiating the theory at the genus-`g` surface reduces to the single statement
`IsHyperbolic (GenusSurface g)` for `2 ≤ g`: with it, `fuchsianBase_of_isHyperbolic` produces
the base `(Γ₀, hΓ₀, hfree, hcc)`, and `Teich Γ₀` is the Teichmüller space of the genus-`g`
surface. That statement amounts to excluding the plane and sphere branches of the
uniformization trichotomy through the fundamental group of `GenusSurface g`.
-/

open scoped Manifold ContDiff

namespace RiemannDynamics

/-- The Fuchsian uniformization of a compact connected hyperbolic Riemann surface, packaged
as an abstract base: a Fuchsian group whose elements with a fixed point act trivially on the
upper half plane, with compact orbit space. -/
theorem fuchsianBase_of_isHyperbolic (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [ConnectedSpace X] [CompactSpace X]
    (hX : IsHyperbolic X) :
    ∃ Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      IsFuchsianGroup Γ₀ ∧
      (∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
        ∀ τ' : UpperHalfPlane, γ • τ' = τ') ∧
      CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)) := by
  obtain ⟨Γ, π, hΓ, hfree, -, -, -, -, ⟨e⟩⟩ := exists_fuchsian_model hX
  exact ⟨Γ, hΓ, hfree, e.compactSpace⟩

/-- The Fuchsian base of the genus-`g` surface, `2 ≤ g`: a Fuchsian group whose elements
with a fixed point act trivially on the upper half plane, with compact orbit space, so
that `Teich Γ₀` is the Teichmüller space of the genus-`g` surface. -/
theorem exists_fuchsianBase_genusSurface (g : ℕ) [NeZero g] (hg : 2 ≤ g) :
    ∃ Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      IsFuchsianGroup Γ₀ ∧
      (∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) → ∀ τ' : UpperHalfPlane, γ • τ' = τ') ∧
      CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)) := by
  exact fuchsianBase_of_isHyperbolic (GenusSurface g) (isHyperbolic_genusSurface g hg)

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Bergman
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Symmetrize
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Invariant
import RiemannDynamics.Analysis.SingularIntegral.L1Duality

/-!
# Hamilton–Krushkal necessity

An extremal marked candidate has a Hamilton maximizer: the real part of the pairing of
its Beltrami coefficient with the unit ball of automorphic quadratic differentials of the
domain group attains the coefficient norm. The contrapositive is the variational step —
a gap between the pairing supremum and the coefficient norm produces, through the
Hahn–Banach extension of the pairing functional, its essentially bounded representative,
and the deformation of the candidate along the resulting infinitesimally trivial
direction, a competing marked candidate of strictly smaller dilatation.

* `exists_lt_dilatation_of_pairing_gap` — the variational step: a pairing gap defeats
  extremality.
* `hamilton_krushkal_necessity` — the attained Hamilton maximizer of an extremal
  candidate.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **The variational step**: a symmetric marked candidate whose coefficient pairs with
the unit ball of automorphic quadratic differentials of the domain group strictly below
its norm is not extremal — some marked candidate for the pair has strictly smaller
dilatation. -/
theorem exists_lt_dilatation_of_pairing_gap (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {F : ℂ → ℂ} {b : BeltramiCoeff}
    (hmc : IsMarkedCandidate x y F) (hqa : IsQCAnalytic F b)
    (hsym : b.μ = symmExtension b.μ)
    (hFsym : ∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : QuadraticDifferential y.group, q.l1Norm ≤ 1 →
      (qdPairing b.μ q).re ≤ b.normInf - δ) :
    ∃ (G : ℂ → ℂ) (K : ℝ), IsQCGeometric G K ∧ IsMarkedCandidate x y G ∧ K < b.K := by
  sorry

/-- **Hamilton–Krushkal necessity**: the coefficient of a symmetric extremal marked
candidate attains its norm as the real part of its pairing with a unit-mass automorphic
quadratic differential of the domain group. -/
theorem hamilton_krushkal_necessity (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {F : ℂ → ℂ} {b : BeltramiCoeff}
    (hmc : IsMarkedCandidate x y F) (hqa : IsQCAnalytic F b)
    (hsym : b.μ = symmExtension b.μ)
    (hFsym : ∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    (hext : b.K = sInf (gDilatationSet x y)) :
    ∃ q₀ : QuadraticDifferential y.group, q₀.l1Norm ≤ 1 ∧
      (qdPairing b.μ q₀).re = b.normInf := by
  -- transport the Fuchsian triple to the range group
  have hΓy := TeichRep.isFuchsian_group hΓ₀ hfree y
  have hfy := y.group_free hfree
  have hccy := y.group_cocompact hcc
  -- the coefficient is a.e. bounded by its norm on the upper half plane
  have hne : eLpNormEssSup b.μ volume ≠ ⊤ := b.bound.ne_top
  have hbd : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖b.μ z‖ ≤ b.normInf := by
    refine ae_restrict_of_ae ?_
    filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with z hz
    have h := ENNReal.toReal_mono hne hz
    rwa [toReal_enorm] at h
  -- the Hamilton maximizer over the unit ball
  obtain ⟨q₀, hq01, hq0max⟩ := exists_qdPairing_maximizer hΓy hfy hccy b.measurable hbd
  refine ⟨q₀, hq01, ?_⟩
  have hfin : q₀.l1Norm ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq01
  -- upper bound: the pairing never exceeds the coefficient norm
  have hub : (qdPairing b.μ q₀).re ≤ b.normInf := by
    have h1 : (qdPairing b.μ q₀).re ≤ ‖qdPairing b.μ q₀‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have h2 := norm_qdPairing_le b.normInf_nonneg hbd q₀ hfin
    have h3 : q₀.l1Norm.toReal ≤ 1 := by
      have h4 := ENNReal.toReal_mono ENNReal.one_ne_top hq01
      simpa using h4
    have h5 : b.normInf * q₀.l1Norm.toReal ≤ b.normInf * 1 :=
      mul_le_mul_of_nonneg_left h3 b.normInf_nonneg
    linarith
  -- lower bound: a strict gap would defeat extremality
  by_contra hv
  have hlt : (qdPairing b.μ q₀).re < b.normInf := lt_of_le_of_ne hub hv
  have hδ : 0 < b.normInf - (qdPairing b.μ q₀).re := sub_pos.mpr hlt
  have hgap : ∀ q : QuadraticDifferential y.group, q.l1Norm ≤ 1 →
      (qdPairing b.μ q).re ≤ b.normInf - (b.normInf - (qdPairing b.μ q₀).re) := by
    intro q hq
    have h := hq0max q hq
    linarith
  obtain ⟨G, K', hGgeo, hGmc, hK'⟩ :=
    exists_lt_dilatation_of_pairing_gap hΓ₀ hfree hcc hmc hqa hsym hFsym hδ hgap
  have hmem : K' ∈ gDilatationSet x y := ⟨G, hGgeo, hGmc⟩
  have hle : sInf (gDilatationSet x y) ≤ K' :=
    csInf_le (bddBelow_gDilatationSet x y) hmem
  rw [← hext] at hle
  linarith

end RiemannDynamics

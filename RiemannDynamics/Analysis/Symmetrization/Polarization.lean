/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Atomic polarization Dirichlet-energy inequality

Polarization (two-point rearrangement) of a real function `u : ℂ → ℝ` about the real axis, with
the reflection `σ z = conj z` and the upper half-plane `{z | 0 ≤ z.im}`, is
`polarize u z = max (u z) (u (conj z))` on the closed upper half-plane and
`polarize u z = min (u z) (u (conj z))` on the open lower half-plane.

The main result `dirichletEnergy_polarize_le` states that for a differentiable `u`, polarization
does not increase the Dirichlet energy:
`∫⁻ z, ‖fderiv ℝ (polarize u) z‖₊ ^ 2 ≤ ∫⁻ z, ‖fderiv ℝ u z‖₊ ^ 2`.

## Proof outline

The plane is split into the two open half-planes; the real axis is a proper `ℝ`-submodule and hence
Lebesgue-null. On the open upper half-plane `polarize u` agrees locally with `w ↦ max (u w)
(u (conj w))`, and on the open lower half-plane with `w ↦ min (u w) (u (conj w))`, so the two
gradients coincide there. Since `conj` is a linear isometry that preserves planar Lebesgue measure
and fixes each of the two functions `w ↦ max (u w) (u (conj w))` and `w ↦ min (u w) (u (conj w))`,
the lower-half energy equals the upper-half energy, so the whole polarized energy equals the
upper-half integral of `‖∇ max‖² + ‖∇ min‖²`. The corresponding decomposition of the energy of `u`
turns the whole integral of `‖∇u‖²` into the upper-half integral of `‖∇u‖² + ‖∇(u ∘ conj)‖²`. The
conclusion then follows from the pointwise two-point inequality
`‖∇ max (f, g)‖² + ‖∇ min (f, g)‖² ≤ ‖∇f‖² + ‖∇g‖²`, valid for functions differentiable at the
point: off the coincidence set `{f = g}` the pair `(∇ max, ∇ min)` is `(∇f, ∇g)` up to a swap, and
on `{f = g}` the nonnegative function `max - min` attains a minimum, so `∇ max = ∇ min` and the
triangle inequality gives `‖∇ max‖² + ‖∇ min‖² = ½‖∇f + ∇g‖² ≤ ‖∇f‖² + ‖∇g‖²`.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal

namespace RiemannDynamics

variable {V : Type*} [NormedAddCommGroup V]

theorem nnnorm_sq_eq (v : V) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h1 : (‖v‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖v‖ := by
    rw [← enorm_eq_nnnorm]; exact (ofReal_norm v).symm
  rw [h1, ENNReal.ofReal_pow (norm_nonneg v)]

theorem enn_sq_add_le {a b c d : V} (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖c‖ ^ 2 + ‖d‖ ^ 2) :
    (‖a‖₊ : ℝ≥0∞) ^ 2 + (‖b‖₊ : ℝ≥0∞) ^ 2 ≤ (‖c‖₊ : ℝ≥0∞) ^ 2 + (‖d‖₊ : ℝ≥0∞) ^ 2 := by
  rw [nnnorm_sq_eq a, nnnorm_sq_eq b, nnnorm_sq_eq c, nnnorm_sq_eq d,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

section MasterPointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem master_pointwise (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => max (f y) (g y)) x‖ ^ 2 + ‖fderiv ℝ (fun y => min (f y) (g y)) x‖ ^ 2
      ≤ ‖fderiv ℝ f x‖ ^ 2 + ‖fderiv ℝ g x‖ ^ 2 := by
  rcases lt_trichotomy (f x) (g x) with hlt | heq | hgt
  · have hmaxeq : (fun y => max (f y) (g y)) =ᶠ[𝓝 x] g := by
      filter_upwards [hf.continuousAt.eventually_lt hg.continuousAt hlt] with y hy
        using max_eq_right hy.le
    have hmineq : (fun y => min (f y) (g y)) =ᶠ[𝓝 x] f := by
      filter_upwards [hf.continuousAt.eventually_lt hg.continuousAt hlt] with y hy
        using min_eq_left hy.le
    rw [hmaxeq.fderiv_eq, hmineq.fderiv_eq]; linarith
  · by_cases hmax : DifferentiableAt ℝ (fun y => max (f y) (g y)) x
    · have hmin : DifferentiableAt ℝ (fun y => min (f y) (g y)) x := by
        have : (fun y => min (f y) (g y)) = (fun y => f y + g y - max (f y) (g y)) := by
          funext y; rw [← max_add_min (f y) (g y)]; ring
        rw [this]; exact (hf.add hg).sub hmax
      have hmaxmin : fderiv ℝ (fun y => max (f y) (g y)) x
          = fderiv ℝ (fun y => min (f y) (g y)) x := by
        set φ := fun y => max (f y) (g y) - min (f y) (g y) with hφ
        have hφnn : ∀ y, 0 ≤ φ y := by intro y; simp [hφ, sub_nonneg]
        have hφx : φ x = 0 := by simp [hφ, heq]
        have hlm : IsLocalMin φ x := by filter_upwards with y; rw [hφx]; exact hφnn y
        have hz : fderiv ℝ φ x = 0 := hlm.fderiv_eq_zero
        have hsub : fderiv ℝ φ x = fderiv ℝ (fun y => max (f y) (g y)) x
            - fderiv ℝ (fun y => min (f y) (g y)) x := fderiv_sub hmax hmin
        rw [hz] at hsub
        exact (eq_of_sub_eq_zero hsub.symm)
      have hsum : fderiv ℝ (fun y => max (f y) (g y)) x
          + fderiv ℝ (fun y => min (f y) (g y)) x = fderiv ℝ f x + fderiv ℝ g x := by
        have he : (fun y => max (f y) (g y) + min (f y) (g y)) = (fun y => f y + g y) := by
          funext y; exact max_add_min (f y) (g y)
        have h1 : fderiv ℝ (fun y => max (f y) (g y) + min (f y) (g y)) x
            = fderiv ℝ (fun y => max (f y) (g y)) x
              + fderiv ℝ (fun y => min (f y) (g y)) x := fderiv_add hmax hmin
        have h2 : fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x :=
          fderiv_add hf hg
        rw [← h1, he, h2]
      have htwo : (2 : ℝ) • fderiv ℝ (fun y => max (f y) (g y)) x
          = fderiv ℝ f x + fderiv ℝ g x := by
        rw [two_smul]; nth_rewrite 2 [hmaxmin]; exact hsum
      have hLHS : ‖fderiv ℝ (fun y => max (f y) (g y)) x‖ ^ 2
          + ‖fderiv ℝ (fun y => min (f y) (g y)) x‖ ^ 2
          = 2 * ‖fderiv ℝ (fun y => max (f y) (g y)) x‖ ^ 2 := by
        rw [← hmaxmin]; ring
      rw [hLHS]
      have hnorm : (2:ℝ) * ‖fderiv ℝ (fun y => max (f y) (g y)) x‖
          = ‖fderiv ℝ f x + fderiv ℝ g x‖ := by
        rw [← htwo, norm_smul]; simp
      have htri : ‖fderiv ℝ f x + fderiv ℝ g x‖ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ g x‖ :=
        norm_add_le _ _
      nlinarith [sq_nonneg (‖fderiv ℝ f x‖ - ‖fderiv ℝ g x‖),
        norm_nonneg (fderiv ℝ f x), norm_nonneg (fderiv ℝ g x),
        norm_nonneg (fderiv ℝ (fun y => max (f y) (g y)) x), hnorm, htri,
        mul_le_mul_of_nonneg_left htri (by norm_num : (0:ℝ) ≤ 2)]
    · have hmin : ¬ DifferentiableAt ℝ (fun y => min (f y) (g y)) x := by
        intro hmin
        apply hmax
        have : (fun y => max (f y) (g y)) = (fun y => f y + g y - min (f y) (g y)) := by
          funext y; rw [← max_add_min (f y) (g y)]; ring
        rw [this]; exact (hf.add hg).sub hmin
      rw [fderiv_zero_of_not_differentiableAt hmax, fderiv_zero_of_not_differentiableAt hmin,
        norm_zero]
      nlinarith [sq_nonneg ‖fderiv ℝ f x‖, sq_nonneg ‖fderiv ℝ g x‖]
  · have hmaxeq : (fun y => max (f y) (g y)) =ᶠ[𝓝 x] f := by
      filter_upwards [hg.continuousAt.eventually_lt hf.continuousAt hgt] with y hy
        using max_eq_left hy.le
    have hmineq : (fun y => min (f y) (g y)) =ᶠ[𝓝 x] g := by
      filter_upwards [hg.continuousAt.eventually_lt hf.continuousAt hgt] with y hy
        using min_eq_right hy.le
    rw [hmaxeq.fderiv_eq, hmineq.fderiv_eq]

end MasterPointwise

theorem axis_null : volume {z : ℂ | z.im = 0} = 0 := by
  have he : {z : ℂ | z.im = 0} = (LinearMap.ker Complex.imLm : Submodule ℝ ℂ) := by
    ext z; simp [Complex.imLm, LinearMap.mem_ker]
  rw [he]
  apply Measure.addHaar_submodule
  intro h
  have : (Complex.I : ℂ) ∈ (LinearMap.ker Complex.imLm : Submodule ℝ ℂ) := by rw [h]; trivial
  simp [LinearMap.mem_ker, Complex.imLm] at this

theorem lower_ae : ({z : ℂ | z.im ≤ 0} : Set ℂ) =ᵐ[volume] {z : ℂ | z.im < 0} := by
  refine (MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩)
  · have hdiff : {z : ℂ | z.im ≤ 0} \ {z : ℂ | z.im < 0} ⊆ {z : ℂ | z.im = 0} := by
      intro z hz
      simp only [Set.mem_diff, Set.mem_setOf_eq, not_lt] at hz
      exact le_antisymm hz.1 hz.2
    exact measure_mono_null hdiff axis_null
  · have : {z : ℂ | z.im < 0} \ {z : ℂ | z.im ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_diff, Set.mem_setOf_eq, not_le, Set.mem_empty_iff_false, iff_false,
        not_and, not_lt]
      intro h; linarith
    rw [this]; simp

theorem split_plane (f : ℂ → ℝ≥0∞) :
    ∫⁻ w, f w = (∫⁻ w in {z : ℂ | 0 < z.im}, f w) + (∫⁻ w in {z : ℂ | z.im < 0}, f w) := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  rw [← lintegral_add_compl f hU]
  congr 1
  apply setLIntegral_congr
  have hc : ({z : ℂ | 0 < z.im}ᶜ : Set ℂ) = {z : ℂ | z.im ≤ 0} := by
    ext z; simp [not_lt]
  rw [hc]; exact lower_ae

theorem conj_mp : MeasurePreserving (starRingEnd ℂ) volume volume := by
  have : (starRingEnd ℂ : ℂ → ℂ) = (Complex.conjLIE : ℂ → ℂ) := by
    funext z; exact (Complex.conjLIE_apply z).symm
  rw [this]
  exact LinearIsometryEquiv.measurePreserving Complex.conjLIE

theorem conj_emb : MeasurableEmbedding (starRingEnd ℂ) := by
  have : (starRingEnd ℂ : ℂ → ℂ) = (Complex.conjLIE : ℂ → ℂ) := by
    funext z; exact (Complex.conjLIE_apply z).symm
  rw [this]
  exact Complex.conjLIE.toHomeomorph.measurableEmbedding

theorem lower_sub_upper (f : ℂ → ℝ≥0∞) :
    ∫⁻ a in {z : ℂ | 0 < z.im}, f ((starRingEnd ℂ) a)
      = ∫⁻ b in {z : ℂ | z.im < 0}, f b := by
  have hpre : (starRingEnd ℂ) ⁻¹' {z : ℂ | z.im < 0} = {z : ℂ | 0 < z.im} := by
    ext z; simp only [Set.mem_preimage, Set.mem_setOf_eq, Complex.conj_im]
    constructor <;> intro h <;> linarith
  rw [← hpre]
  exact conj_mp.setLIntegral_comp_preimage_emb conj_emb f {z : ℂ | z.im < 0}

/-- norm of the derivative of a function precomposed with conjugation. -/
theorem norm_fderiv_comp_conj (u : ℂ → ℝ) (z : ℂ) :
    ‖fderiv ℝ (fun w => u ((starRingEnd ℂ) w)) z‖ = ‖fderiv ℝ u ((starRingEnd ℂ) z)‖ := by
  have hfun : (fun w => u ((starRingEnd ℂ) w))
      = u ∘ (Complex.conjLIE.toContinuousLinearEquiv : ℂ → ℂ) := by
    funext w; simp only [Function.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      Complex.conjLIE_apply]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  have h : (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ)
      = Complex.conjLIE.toLinearIsometry.toContinuousLinearMap := rfl
  rw [h, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, Complex.conjLIE_apply]

/-- Polarization of `u : ℂ → ℝ` about the real axis. -/
noncomputable def polarize (u : ℂ → ℝ) : ℂ → ℝ :=
  fun z => if 0 ≤ z.im then max (u z) (u ((starRingEnd ℂ) z))
    else min (u z) (u ((starRingEnd ℂ) z))

/-- The upper-half energy of the polarization is the upper-half energy of the pointwise `max`. -/
theorem setLIntegral_upper_polarize (u : ℂ → ℝ) :
    ∫⁻ z in {z : ℂ | 0 < z.im}, (‖fderiv ℝ (polarize u) z‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          (‖fderiv ℝ (fun w => max (u w) (u ((starRingEnd ℂ) w))) z‖₊ : ℝ≥0∞) ^ 2 := by
  apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
  intro z hz
  have hzU : z ∈ {z : ℂ | 0 < z.im} := hz
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have heq : fderiv ℝ (polarize u) z
      = fderiv ℝ (fun w => max (u w) (u ((starRingEnd ℂ) w))) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hopen.mem_nhds hzU] with w hw
    simp only [polarize, if_pos (le_of_lt hw)]
  simp only [heq]

/-- The lower-half energy of the polarization is the lower-half energy of the pointwise `min`. -/
theorem setLIntegral_lower_polarize (u : ℂ → ℝ) :
    ∫⁻ z in {z : ℂ | z.im < 0}, (‖fderiv ℝ (polarize u) z‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z in {z : ℂ | z.im < 0},
          (‖fderiv ℝ (fun w => min (u w) (u ((starRingEnd ℂ) w))) z‖₊ : ℝ≥0∞) ^ 2 := by
  apply setLIntegral_congr_fun (measurableSet_lt Complex.measurable_im measurable_const)
  intro z hz
  have hzL : z ∈ {z : ℂ | z.im < 0} := hz
  have hopen : IsOpen {z : ℂ | z.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  have heq : fderiv ℝ (polarize u) z
      = fderiv ℝ (fun w => min (u w) (u ((starRingEnd ℂ) w))) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hopen.mem_nhds hzL] with w hw
    simp only [polarize, if_neg (not_le.mpr hw)]
  simp only [heq]

/-- Conjugation symmetry of the norm of the derivative of `min (u ·) (u (conj ·))`. -/
theorem norm_fderiv_min_conj (u : ℂ → ℝ) (a : ℂ) :
    ‖fderiv ℝ (fun w => min (u w) (u ((starRingEnd ℂ) w))) ((starRingEnd ℂ) a)‖
      = ‖fderiv ℝ (fun w => min (u w) (u ((starRingEnd ℂ) w))) a‖ := by
  set m := fun w => min (u w) (u ((starRingEnd ℂ) w)) with hm
  have hsym : (fun w => m ((starRingEnd ℂ) w)) = m := by
    funext w; simp only [hm, Complex.conj_conj]; rw [min_comm]
  have hchain : ‖fderiv ℝ (fun w => m ((starRingEnd ℂ) w)) a‖
      = ‖fderiv ℝ m ((starRingEnd ℂ) a)‖ := by
    have hfun : (fun w => m ((starRingEnd ℂ) w))
        = m ∘ (Complex.conjLIE.toContinuousLinearEquiv : ℂ → ℂ) := by
      funext w; simp only [Function.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        Complex.conjLIE_apply]
    rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
    have h : (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ)
        = Complex.conjLIE.toLinearIsometry.toContinuousLinearMap := rfl
    rw [h, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, Complex.conjLIE_apply]
  rw [← hchain, hsym]

/-- **Atomic polarization Dirichlet-energy inequality.** For a differentiable `u : ℂ → ℝ`,
polarization about the real axis does not increase the Dirichlet energy. -/
theorem dirichletEnergy_polarize_le (u : ℂ → ℝ) (hu : Differentiable ℝ u) :
    ∫⁻ z, (‖fderiv ℝ (polarize u) z‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 := by
  -- abbreviations
  set g := fun w => u ((starRingEnd ℂ) w) with hg
  -- differentiability of the conjugate composite
  have hgdiff : ∀ z, DifferentiableAt ℝ g z := by
    intro z
    have hc : DifferentiableAt ℝ (fun w : ℂ => (starRingEnd ℂ) w) z :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt
    exact (hu ((starRingEnd ℂ) z)).comp z hc
  -- LHS = ∫_U ‖∇max‖² + ∫_L ‖∇min‖²
  rw [split_plane (fun z => (‖fderiv ℝ (polarize u) z‖₊ : ℝ≥0∞) ^ 2),
    setLIntegral_upper_polarize u, setLIntegral_lower_polarize u]
  -- ∫_L ‖∇min‖² = ∫_U ‖∇min‖²  (conjugation symmetry)
  have hLm : ∫⁻ z in {z : ℂ | z.im < 0},
      (‖fderiv ℝ (fun w => min (u w) (u ((starRingEnd ℂ) w))) z‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          (‖fderiv ℝ (fun w => min (u w) (u ((starRingEnd ℂ) w))) z‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← lower_sub_upper (fun z => (‖fderiv ℝ
      (fun w => min (u w) (u ((starRingEnd ℂ) w))) z‖₊ : ℝ≥0∞) ^ 2)]
    apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
    intro a _
    simp only
    congr 2
    exact NNReal.coe_injective (norm_fderiv_min_conj u a)
  rw [hLm, ← lintegral_add_left]
  · -- RHS = ∫_U ‖∇u‖² + ∫_L ‖∇u‖²  and turn ∫_L ‖∇u‖² into ∫_U ‖∇g‖²
    rw [split_plane (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2)]
    have hRg : ∫⁻ z in {z : ℂ | z.im < 0}, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
        = ∫⁻ z in {z : ℂ | 0 < z.im}, (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2 := by
      rw [← lower_sub_upper (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2)]
      apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
      intro a _
      simp only [hg]
      congr 2
      exact NNReal.coe_injective (norm_fderiv_comp_conj u a).symm
    rw [hRg, ← lintegral_add_left]
    · -- pointwise inequality on U
      apply setLIntegral_mono
      · apply Measurable.add
        · exact ((measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp
            (measurable_fderiv ℝ u))).pow_const 2)
        · exact ((measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp
            (measurable_fderiv ℝ g))).pow_const 2)
      · intro z _
        have hpt := master_pointwise u g z (hu z) (hgdiff z)
        exact enn_sq_add_le hpt
    · exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp
        (measurable_fderiv ℝ u))).pow_const 2
  · exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp
      (measurable_fderiv ℝ (fun w => max (u w) (u ((starRingEnd ℂ) w)))))).pow_const 2

/-- The super-level volume as a Lebesgue integral of the `0/1` threshold indicator. -/
theorem volume_superlevel_eq_lintegral (f : ℂ → ℝ) (hf : Measurable f) (c : ℝ) :
    volume (f ⁻¹' Set.Ioi c) = ∫⁻ z, (if c < f z then (1 : ℝ≥0∞) else 0) := by
  classical
  have hmeas : MeasurableSet (f ⁻¹' Set.Ioi c) := hf measurableSet_Ioi
  rw [← lintegral_indicator_one hmeas]
  apply lintegral_congr
  intro z
  rw [Set.indicator_apply]
  simp only [Set.mem_preimage, Set.mem_Ioi, Pi.one_apply]

/-- Two-point rearrangement of the threshold indicator: the number of the two values exceeding
`c` is unchanged by replacing `(a, b)` with `(max a b, min a b)`. -/
theorem twoPoint_indicator (a b c : ℝ) :
    (if c < max a b then (1 : ℝ≥0∞) else 0) + (if c < min a b then 1 else 0)
      = (if c < a then 1 else 0) + (if c < b then 1 else 0) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm]
  · rw [max_eq_left h, min_eq_right h]

/-- **Polarization preserves the super-level volume.** Two-point rearrangement about the real axis
is equimeasurable: the volume of each super-level set of `polarize u` equals that of `u`. -/
theorem volume_polarize_superlevel_eq (u : ℂ → ℝ) (hu : Measurable u) (c : ℝ) :
    volume ((polarize u) ⁻¹' Set.Ioi c) = volume (u ⁻¹' Set.Ioi c) := by
  -- conjugation is measurable, so all threshold indicators below are measurable
  have hconj : Measurable (starRingEnd ℂ) := conj_emb.measurable
  have hg : Measurable (fun w => u ((starRingEnd ℂ) w)) := hu.comp hconj
  -- `polarize u` is measurable
  have hpol : Measurable (polarize u) := by
    unfold polarize
    exact Measurable.ite (measurableSet_le measurable_const Complex.measurable_im)
      (hu.max hg) (hu.min hg)
  -- rewrite both super-level volumes as integrals of threshold indicators
  rw [volume_superlevel_eq_lintegral (polarize u) hpol c,
    volume_superlevel_eq_lintegral u hu c]
  -- split the plane into the two open half-planes (the axis is null)
  rw [split_plane (fun z => if c < polarize u z then (1 : ℝ≥0∞) else 0),
    split_plane (fun z => if c < u z then (1 : ℝ≥0∞) else 0)]
  -- on the upper half `polarize u = max`, on the lower half `polarize u = min`
  have hUpol : ∫⁻ z in {z : ℂ | 0 < z.im}, (if c < polarize u z then (1 : ℝ≥0∞) else 0)
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          (if c < max (u z) (u ((starRingEnd ℂ) z)) then (1 : ℝ≥0∞) else 0) := by
    apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
    intro z hz
    rw [Set.mem_setOf_eq] at hz
    simp only [polarize, if_pos (le_of_lt hz)]
  have hLpol : ∫⁻ z in {z : ℂ | z.im < 0}, (if c < polarize u z then (1 : ℝ≥0∞) else 0)
      = ∫⁻ z in {z : ℂ | z.im < 0},
          (if c < min (u z) (u ((starRingEnd ℂ) z)) then (1 : ℝ≥0∞) else 0) := by
    apply setLIntegral_congr_fun (measurableSet_lt Complex.measurable_im measurable_const)
    intro z hz
    rw [Set.mem_setOf_eq] at hz
    simp only [polarize, if_neg (not_le.mpr hz)]
  rw [hUpol, hLpol]
  -- fold the lower `min`-integral onto the upper half via conjugation (`min_comm` under `conj`)
  have hLmin : ∫⁻ z in {z : ℂ | z.im < 0},
      (if c < min (u z) (u ((starRingEnd ℂ) z)) then (1 : ℝ≥0∞) else 0)
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          (if c < min (u z) (u ((starRingEnd ℂ) z)) then (1 : ℝ≥0∞) else 0) := by
    rw [← lower_sub_upper
      (fun z => if c < min (u z) (u ((starRingEnd ℂ) z)) then (1 : ℝ≥0∞) else 0)]
    apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
    intro a _
    simp only [Complex.conj_conj, min_comm]
  -- fold the lower `u`-integral onto the upper half via conjugation
  have hLu : ∫⁻ z in {z : ℂ | z.im < 0}, (if c < u z then (1 : ℝ≥0∞) else 0)
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          (if c < u ((starRingEnd ℂ) z) then (1 : ℝ≥0∞) else 0) := by
    rw [← lower_sub_upper (fun z => if c < u z then (1 : ℝ≥0∞) else 0)]
  rw [hLmin, hLu]
  -- both sides are now upper-half integrals; apply the two-point identity pointwise
  rw [← lintegral_add_left, ← lintegral_add_left]
  · apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
    intro z _
    exact twoPoint_indicator (u z) (u ((starRingEnd ℂ) z)) c
  · exact Measurable.ite (measurableSet_lt measurable_const hu)
      measurable_const measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_const (hu.max hg))
      measurable_const measurable_const

/-- Two-point rearrangement of a weighted pairing: for reals with `q ≤ p`, moving the larger of
`a, b` to the heavier weight `p` does not decrease the pairing. -/
theorem twoPoint_pairing_le (a b p q : ℝ) (h : q ≤ p) :
    a * p + b * q ≤ max a b * p + min a b * q := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, min_eq_left hab]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h)]
  · rw [max_eq_left hab, min_eq_right hab]

/-- **Baernstein–Van Schaftingen master inequality.** For nonnegative measurable `u, w : ℂ → ℝ`
with a weight `w` that is at least as large on the upper (polarization) half-plane as at its
reflection (`w (conj z) ≤ w z` whenever `0 ≤ z.im`), polarization about the real axis does not
decrease the weighted pairing `∫ u · w`. -/
theorem lintegral_mul_weight_polarize_ge (u w : ℂ → ℝ)
    (hu : Measurable u) (hw : Measurable w) (hunn : 0 ≤ u) (hwnn : 0 ≤ w)
    (hwsym : ∀ z : ℂ, 0 ≤ z.im → w ((starRingEnd ℂ) z) ≤ w z) :
    ∫⁻ z, ENNReal.ofReal (u z * w z) ≤ ∫⁻ z, ENNReal.ofReal (polarize u z * w z) := by
  -- conjugation is measurable, so the composites below are measurable
  have hconj : Measurable (starRingEnd ℂ) := conj_emb.measurable
  have hg : Measurable (fun z => u ((starRingEnd ℂ) z)) := hu.comp hconj
  have hwg : Measurable (fun z => w ((starRingEnd ℂ) z)) := hw.comp hconj
  have hpol : Measurable (polarize u) := by
    unfold polarize
    exact Measurable.ite (measurableSet_le measurable_const Complex.measurable_im)
      (hu.max hg) (hu.min hg)
  -- split each side into the two open half-planes (the axis is null)
  rw [split_plane (fun z => ENNReal.ofReal (u z * w z)),
    split_plane (fun z => ENNReal.ofReal (polarize u z * w z))]
  -- on the upper half `polarize u = max`
  have hUpol : ∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal (polarize u z * w z)
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          ENNReal.ofReal (max (u z) (u ((starRingEnd ℂ) z)) * w z) := by
    apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
    intro z hz
    rw [Set.mem_setOf_eq] at hz
    simp only [polarize, if_pos (le_of_lt hz)]
  -- fold the lower `u`-integral onto the upper half via conjugation
  have hLu : ∫⁻ z in {z : ℂ | z.im < 0}, ENNReal.ofReal (u z * w z)
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          ENNReal.ofReal (u ((starRingEnd ℂ) z) * w ((starRingEnd ℂ) z)) := by
    rw [← lower_sub_upper (fun z => ENNReal.ofReal (u z * w z))]
  -- fold the lower `min`-integral onto the upper half via conjugation (`min_comm` under `conj`)
  have hLpol : ∫⁻ z in {z : ℂ | z.im < 0}, ENNReal.ofReal (polarize u z * w z)
      = ∫⁻ z in {z : ℂ | 0 < z.im},
          ENNReal.ofReal (min (u ((starRingEnd ℂ) z)) (u z) * w ((starRingEnd ℂ) z)) := by
    have hLmin : ∫⁻ z in {z : ℂ | z.im < 0}, ENNReal.ofReal (polarize u z * w z)
        = ∫⁻ z in {z : ℂ | z.im < 0},
            ENNReal.ofReal (min (u z) (u ((starRingEnd ℂ) z)) * w z) := by
      apply setLIntegral_congr_fun (measurableSet_lt Complex.measurable_im measurable_const)
      intro z hz
      rw [Set.mem_setOf_eq] at hz
      simp only [polarize, if_neg (not_le.mpr hz)]
    rw [hLmin, ← lower_sub_upper
      (fun z => ENNReal.ofReal (min (u z) (u ((starRingEnd ℂ) z)) * w z))]
    apply setLIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
    intro a _
    simp only [Complex.conj_conj]
  rw [hUpol, hLu, hLpol]
  -- combine each side into a single upper-half integral
  rw [← lintegral_add_left, ← lintegral_add_left]
  · -- pointwise two-point inequality on the upper half
    apply setLIntegral_mono
    · refine Measurable.add ?_ ?_
      · exact ENNReal.measurable_ofReal.comp ((hu.max hg).mul hw)
      · exact ENNReal.measurable_ofReal.comp ((hg.min hu).mul hwg)
    · intro z hz
      rw [Set.mem_setOf_eq] at hz
      have hpq : w ((starRingEnd ℂ) z) ≤ w z := hwsym z hz.le
      rw [← ENNReal.ofReal_add (mul_nonneg (hunn _) (hwnn _))
          (mul_nonneg (hunn _) (hwnn _)),
        ← ENNReal.ofReal_add
          (mul_nonneg (le_max_of_le_left (hunn _)) (hwnn _))
          (mul_nonneg (le_min (hunn _) (hunn _)) (hwnn _))]
      apply ENNReal.ofReal_le_ofReal
      have h2 := twoPoint_pairing_le (u z) (u ((starRingEnd ℂ) z)) (w z)
        (w ((starRingEnd ℂ) z)) hpq
      rw [min_comm] at h2
      linarith
  · exact ENNReal.measurable_ofReal.comp ((hu.max hg).mul hw)
  · exact ENNReal.measurable_ofReal.comp (hu.mul hw)

/-- Polarization of a nonnegative function is nonnegative: on the upper half it is a maximum of
nonnegatives and on the lower half a minimum of nonnegatives. -/
theorem polarize_nonneg (u : ℂ → ℝ) (hunn : 0 ≤ u) : 0 ≤ polarize u := by
  intro z
  unfold polarize
  split_ifs
  · exact le_max_of_le_left (hunn z)
  · exact le_min (hunn z) (hunn ((starRingEnd ℂ) z))

/-- **Polarization preserves the `Lᵖ` energy.** For a nonnegative measurable `u : ℂ → ℝ` and any
real exponent `p > 0`, two-point rearrangement about the real axis leaves `∫ uᵖ` unchanged. This is
the layer-cake consequence of super-level equimeasurability `volume_polarize_superlevel_eq`: both
sides equal `p · ∫₀^∞ tᵖ⁻¹ · volume {z | t < ·} dt`, and the two distribution functions agree.
Specializing to `p = 2` gives the `L²` (Dirichlet) energy identity used for `W¹²` boundedness. -/
theorem lintegral_rpow_polarize_eq (u : ℂ → ℝ) (hu : Measurable u) (hunn : 0 ≤ u)
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ z, ENNReal.ofReal (polarize u z ^ p) = ∫⁻ z, ENNReal.ofReal (u z ^ p) := by
  have hconj : Measurable (starRingEnd ℂ) := conj_emb.measurable
  have hg : Measurable (fun w => u ((starRingEnd ℂ) w)) := hu.comp hconj
  have hpol : Measurable (polarize u) := by
    unfold polarize
    exact Measurable.ite (measurableSet_le measurable_const Complex.measurable_im)
      (hu.max hg) (hu.min hg)
  have hpolnn : 0 ≤ polarize u := polarize_nonneg u hunn
  rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul volume
        (Eventually.of_forall hpolnn) hpol.aemeasurable hp,
      MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul volume
        (Eventually.of_forall hunn) hu.aemeasurable hp]
  congr 1
  apply lintegral_congr
  intro t
  congr 1
  have h1 : {a : ℂ | t < polarize u a} = (polarize u) ⁻¹' Set.Ioi t := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]
  have h2 : {a : ℂ | t < u a} = u ⁻¹' Set.Ioi t := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]
  rw [h1, h2]
  exact volume_polarize_superlevel_eq u hu t

end RiemannDynamics

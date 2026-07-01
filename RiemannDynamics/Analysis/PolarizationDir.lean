/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Polarization

/-!
# Directional polarization Dirichlet-energy inequality

Polarization (two-point rearrangement) of a real function `u : ℂ → ℝ` about the line through the
origin at angle `θ`, with reflection `σ_θ z = exp (2θ I) * conj z` across that line. It is obtained
from the real-axis polarization `polarize` by rotation-conjugation with the rotation `R z =
exp (θ I) * z` (an `ℝ`-linear isometry of `ℂ` that preserves planar Lebesgue measure):
`polarizeDir θ u = (fun w => polarize (u ∘ R) w) ∘ R⁻¹`, so `polarizeDir θ u z = max (u z)
(u (σ_θ z))` on the closed half-plane on the positive side of the line and the corresponding `min`
on the open half-plane on the negative side.

The main result `dirichletEnergy_polarizeDir_le` states that for a differentiable `u`, directional
polarization does not increase the Dirichlet energy, and `volume_polarizeDir_superlevel_eq` states
that it is equimeasurable (each super-level set keeps its planar measure).

## Proof outline

Both facts are transported from the real-axis toolkit `dirichletEnergy_polarize_le` and
`volume_polarize_superlevel_eq` by conjugating with the rotation `R z = exp (θ I) * z`, realised as
a linear isometry equivalence `rotLIE θ`. Precomposition with a linear isometry equivalence leaves
the norm of the derivative invariant (chain rule together with `opNorm_comp_linearIsometryEquiv`),
and a linear isometry equivalence of `ℂ` preserves planar Lebesgue measure; chaining these across
the identity `polarizeDir θ u = polarize (u ∘ R) ∘ R⁻¹` reduces each statement to the real-axis one
applied to `u ∘ R`.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- Rotation of `ℂ` by angle `θ`, i.e. multiplication by `exp (θ I)`, as an `ℝ`-linear isometry
equivalence. Its inverse is multiplication by `exp (-(θ I))`. -/
noncomputable def rotLIE (θ : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun := fun z => Complex.exp (θ * Complex.I) * z
  invFun := fun z => Complex.exp (-(θ * Complex.I)) * z
  map_add' := by intro x y; change _ * (x + y) = _ * x + _ * y; ring
  map_smul' := by
    intro r x
    change Complex.exp (θ * Complex.I) * (RingHom.id ℝ) r • x
      = r • (Complex.exp (θ * Complex.I) * x)
    simp only [RingHom.id_apply]
    rw [Complex.real_smul, Complex.real_smul]; ring
  left_inv := by
    intro z
    change Complex.exp (-(θ * Complex.I)) * (Complex.exp (θ * Complex.I) * z) = z
    rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  right_inv := by
    intro z
    change Complex.exp (θ * Complex.I) * (Complex.exp (-(θ * Complex.I)) * z) = z
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  norm_map' := by
    intro z
    change ‖Complex.exp (θ * Complex.I) * z‖ = ‖z‖
    rw [norm_mul, Complex.norm_exp]; simp

@[simp] theorem rotLIE_apply (θ : ℝ) (z : ℂ) :
    rotLIE θ z = Complex.exp (θ * Complex.I) * z := rfl

@[simp] theorem rotLIE_symm_apply (θ : ℝ) (z : ℂ) :
    (rotLIE θ).symm z = Complex.exp (-(θ * Complex.I)) * z := rfl

/-- The rotation `rotLIE θ` preserves planar Lebesgue measure. -/
theorem rotLIE_measurePreserving (θ : ℝ) : MeasurePreserving (rotLIE θ) volume volume :=
  LinearIsometryEquiv.measurePreserving (rotLIE θ)

/-- The inverse rotation `(rotLIE θ).symm` preserves planar Lebesgue measure. -/
theorem rotLIE_symm_measurePreserving (θ : ℝ) :
    MeasurePreserving ((rotLIE θ).symm) volume volume :=
  LinearIsometryEquiv.measurePreserving (rotLIE θ).symm

/-- The norm of the derivative is invariant under right-composition with a linear isometry
equivalence: `‖fderiv (g ∘ R) z‖ = ‖fderiv g (R z)‖`. -/
theorem norm_fderiv_comp_lie (g : ℂ → ℝ) (R : ℂ ≃ₗᵢ[ℝ] ℂ) (z : ℂ) :
    ‖fderiv ℝ (fun w => g (R w)) z‖ = ‖fderiv ℝ g (R z)‖ := by
  have hfun : (fun w => g (R w)) = g ∘ (R.toContinuousLinearEquiv : ℂ → ℂ) := by
    funext w; simp only [Function.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  have h : (R.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ)
      = R.toLinearIsometry.toContinuousLinearMap := rfl
  rw [h, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The Dirichlet energy of `g ∘ R⁻¹` equals that of `g`, since `R⁻¹` is a measure-preserving
linear isometry: the norm of the derivative is unchanged pointwise up to the change of variables. -/
theorem lintegral_nnnorm_fderiv_comp_lie_symm (g : ℂ → ℝ) (R : ℂ ≃ₗᵢ[ℝ] ℂ)
    (hR : MeasurePreserving (R.symm) volume volume) :
    ∫⁻ z, (‖fderiv ℝ (fun w => g (R.symm w)) z‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z, (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2 := by
  have hmeas : Measurable (fun z => (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2) :=
    (measurable_coe_nnreal_ennreal.comp
      (measurable_nnnorm.comp (measurable_fderiv ℝ g))).pow_const 2
  rw [← hR.lintegral_comp hmeas]
  apply lintegral_congr
  intro z
  congr 1
  exact congrArg _ (NNReal.coe_injective (norm_fderiv_comp_lie g R.symm z))

/-- Polarization of `u : ℂ → ℝ` about the line through the origin at angle `θ`, obtained from the
real-axis polarization by rotation-conjugation with the rotation `R z = exp (θ I) * z`. -/
noncomputable def polarizeDir (θ : ℝ) (u : ℂ → ℝ) : ℂ → ℝ :=
  fun z => polarize (fun w => u (Complex.exp (θ * Complex.I) * w))
    (Complex.exp (-(θ * Complex.I)) * z)

/-- `polarizeDir θ u` is the real-axis polarization of `u ∘ R` post-composed with `R⁻¹`. -/
theorem polarizeDir_eq (θ : ℝ) (u : ℂ → ℝ) :
    polarizeDir θ u = fun z => polarize (fun w => u (rotLIE θ w)) ((rotLIE θ).symm z) := rfl

/-- **Directional polarization Dirichlet-energy inequality.** For a differentiable `u : ℂ → ℝ`,
polarization about the line through the origin at angle `θ` does not increase the Dirichlet
energy. -/
theorem dirichletEnergy_polarizeDir_le (θ : ℝ) (u : ℂ → ℝ) (hu : Differentiable ℝ u) :
    ∫⁻ z, (‖fderiv ℝ (polarizeDir θ u) z‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 := by
  set v := fun w => u (rotLIE θ w) with hv
  have hvdiff : Differentiable ℝ v := by
    have hR : Differentiable ℝ (fun w : ℂ => rotLIE θ w) := by
      simp only [rotLIE_apply]; exact (differentiable_const _).mul differentiable_id
    exact hu.comp hR
  -- energy of polarizeDir = energy of polarize v (invariance under R⁻¹)
  have h1 : ∫⁻ z, (‖fderiv ℝ (polarizeDir θ u) z‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z, (‖fderiv ℝ (polarize v) z‖₊ : ℝ≥0∞) ^ 2 := by
    rw [polarizeDir_eq]
    exact lintegral_nnnorm_fderiv_comp_lie_symm (polarize v) (rotLIE θ)
      (rotLIE_symm_measurePreserving θ)
  -- energy of u = energy of v (invariance under R)
  have h2 : ∫⁻ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 = ∫⁻ z, (‖fderiv ℝ v z‖₊ : ℝ≥0∞) ^ 2 := by
    have hmeas : Measurable (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2) :=
      (measurable_coe_nnreal_ennreal.comp
        (measurable_nnnorm.comp (measurable_fderiv ℝ u))).pow_const 2
    rw [← (rotLIE_measurePreserving θ).lintegral_comp hmeas]
    apply lintegral_congr
    intro z
    congr 1
    exact congrArg _ (NNReal.coe_injective (norm_fderiv_comp_lie u (rotLIE θ) z).symm)
  rw [h1, h2]
  exact dirichletEnergy_polarize_le v hvdiff

/-- **Directional polarization preserves the super-level volume.** Two-point rearrangement about
the line through the origin at angle `θ` is equimeasurable: the volume of each super-level set of
`polarizeDir θ u` equals that of `u`. -/
theorem volume_polarizeDir_superlevel_eq (θ : ℝ) (u : ℂ → ℝ) (hu : Measurable u) (c : ℝ) :
    volume ((polarizeDir θ u) ⁻¹' Set.Ioi c) = volume (u ⁻¹' Set.Ioi c) := by
  set v := fun w => u (rotLIE θ w) with hv
  have hvmeas : Measurable v := by
    have hR : Measurable (fun w : ℂ => rotLIE θ w) := by
      simp only [rotLIE_apply]; exact measurable_const.mul measurable_id
    exact hu.comp hR
  -- transfer through R⁻¹
  have hpre : (polarizeDir θ u) ⁻¹' Set.Ioi c
      = (rotLIE θ).symm ⁻¹' ((polarize v) ⁻¹' Set.Ioi c) := by
    rw [polarizeDir_eq]; rfl
  have hpolv : Measurable (polarize v) := by
    unfold polarize
    have hconj : Measurable (starRingEnd ℂ) := conj_emb.measurable
    exact Measurable.ite (measurableSet_le measurable_const Complex.measurable_im)
      (hvmeas.max (hvmeas.comp hconj)) (hvmeas.min (hvmeas.comp hconj))
  rw [hpre, (rotLIE_symm_measurePreserving θ).measure_preimage
    (hpolv measurableSet_Ioi).nullMeasurableSet]
  -- real-axis equimeasurability for v
  rw [volume_polarize_superlevel_eq v hvmeas c]
  -- transfer u through R
  have hpreu : v ⁻¹' Set.Ioi c = (rotLIE θ) ⁻¹' (u ⁻¹' Set.Ioi c) := rfl
  rw [hpreu, (rotLIE_measurePreserving θ).measure_preimage
    (hu measurableSet_Ioi).nullMeasurableSet]

end RiemannDynamics

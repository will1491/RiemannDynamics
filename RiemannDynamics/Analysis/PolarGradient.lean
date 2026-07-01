import Mathlib
import RiemannDynamics.QC.Regularity.ModulusEnergy

/-!
# Polar orthonormal decomposition of the gradient norm

For a point `z ≠ 0` in the complex plane, the pair
`er := z / ‖z‖` (unit radial direction) and `eθ := I * z / ‖z‖` (unit tangential direction)
forms a real orthonormal basis of `ℂ`.  Consequently, the squared operator norm of any
continuous `ℝ`-linear functional `L : ℂ →L[ℝ] ℝ` splits as the sum of the squares of its
values on `er` and `eθ`.

Specialising `L` to the Fréchet derivative `fderiv ℝ u z` of a real-valued function `u`
gives the pointwise polar (radial/angular) split of the gradient norm, the analytic
foundation of the circular-symmetrization energy identity
`D(u) = ∫∫ (∂_r u)² + (∂_θ u / r)² r dr dθ`.
-/

namespace RiemannDynamics

open Complex MeasureTheory
open scoped ENNReal NNReal

/-- The unit-modulus rotation `z / ‖z‖` as an element of the circle group. -/
noncomputable def polarRotation {z : ℂ} (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    change z / (‖z‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_of_nonneg (norm_nonneg z)]
    exact div_self (by simpa using hz)⟩

@[simp]
theorem coe_polarRotation {z : ℂ} (hz : z ≠ 0) :
    (polarRotation hz : ℂ) = z / (‖z‖ : ℂ) := rfl

/-- The polar orthonormal basis `{z/‖z‖, I·z/‖z‖}` of `ℂ`, obtained by rotating the
standard basis `{1, I}` by the unit `z/‖z‖`. -/
noncomputable def polarBasis {z : ℂ} (hz : z ≠ 0) : OrthonormalBasis (Fin 2) ℝ ℂ :=
  Complex.orthonormalBasisOneI.map (rotation (polarRotation hz))

@[simp]
theorem polarBasis_zero {z : ℂ} (hz : z ≠ 0) :
    polarBasis hz 0 = z / (‖z‖ : ℂ) := by
  simp [polarBasis, rotation_apply]

@[simp]
theorem polarBasis_one {z : ℂ} (hz : z ≠ 0) :
    polarBasis hz 1 = Complex.I * z / (‖z‖ : ℂ) := by
  simp only [polarBasis, OrthonormalBasis.map_apply, coe_orthonormalBasisOneI]
  rw [rotation_apply, coe_polarRotation, Matrix.cons_val_one, Matrix.cons_val_zero,
    mul_div_assoc, mul_comm]

/-- **Polar decomposition of the norm of a linear functional.**
For any continuous `ℝ`-linear functional `L : ℂ →L[ℝ] ℝ` and any `z ≠ 0`, the squared
operator norm of `L` equals the sum of squares of its values on the unit radial direction
`z/‖z‖` and the unit tangential direction `I·z/‖z‖`. -/
theorem norm_sq_eq_polar (L : ℂ →L[ℝ] ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖L‖ ^ 2
      = (L (z / (‖z‖ : ℂ))) ^ 2 + (L (Complex.I * z / (‖z‖ : ℂ))) ^ 2 := by
  have h := (polarBasis hz).norm_dual L
  rw [Fin.sum_univ_two, polarBasis_zero, polarBasis_one] at h
  exact h

/-- **Polar decomposition of the gradient norm.**
For `u : ℂ → ℝ` and `z ≠ 0`, the squared operator norm of the Fréchet derivative splits
into its squared radial and tangential components. -/
theorem norm_fderiv_sq_eq_polar {u : ℂ → ℝ} {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ u z‖ ^ 2
      = (fderiv ℝ u z (z / (‖z‖ : ℂ))) ^ 2
        + (fderiv ℝ u z (Complex.I * z / (‖z‖ : ℂ))) ^ 2 :=
  norm_sq_eq_polar (fderiv ℝ u z) hz

/-- **Radial/angular split of the Dirichlet energy.**
On a region `U` avoiding the origin, the Dirichlet energy `∫_U ‖∇u‖²` splits as the sum of the
integrals of the squared radial component `(∂_r u)²` and the squared tangential component
`(∂_θ u / r)²` of the gradient, obtained by integrating the pointwise polar decomposition
`norm_fderiv_sq_eq_polar`. -/
theorem dirichletEnergy_eq_radial_add_angular {u : ℂ → ℝ} {U : Set ℂ}
    (_hU0 : (0 : ℂ) ∉ U) :
    dirichletEnergy u U
      = (∫⁻ z in U, ENNReal.ofReal ((fderiv ℝ u z (z / (‖z‖ : ℂ))) ^ 2))
        + (∫⁻ z in U, ENNReal.ofReal ((fderiv ℝ u z (Complex.I * z / (‖z‖ : ℂ))) ^ 2)) := by
  -- The evaluation map `(L, v) ↦ L v` is continuous, hence measurable.
  have hbil : Continuous (fun q : (ℂ →L[ℝ] ℝ) × ℂ => q.1 q.2) :=
    isBoundedBilinearMap_apply.continuous
  have hfder : Measurable (fun z : ℂ => fderiv ℝ u z) := measurable_fderiv ℝ u
  have hrad : Measurable (fun z : ℂ => fderiv ℝ u z (z / (‖z‖ : ℂ))) := by
    have hv : Measurable (fun z : ℂ => (z / (‖z‖ : ℂ))) := by fun_prop
    exact hbil.measurable.comp (hfder.prodMk hv)
  have hmrad : Measurable
      (fun z : ℂ => ENNReal.ofReal ((fderiv ℝ u z (z / (‖z‖ : ℂ))) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hrad.pow_const 2)
  -- The origin is null, so `z ≠ 0` almost everywhere on the restricted measure.
  have hne : ∀ᵐ z : ℂ ∂(volume.restrict U), z ≠ 0 := by
    apply ae_restrict_of_ae
    rw [ae_iff]; simp only [not_not]
    have hset : {z : ℂ | z = 0} = {(0 : ℂ)} := by ext z; simp
    rw [hset]; exact measure_singleton _
  -- Pointwise, the squared gradient norm splits into squared radial and tangential parts.
  have hpt : (fun z : ℂ => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[volume.restrict U]
      (fun z : ℂ => ENNReal.ofReal ((fderiv ℝ u z (z / (‖z‖ : ℂ))) ^ 2)
        + ENNReal.ofReal ((fderiv ℝ u z (Complex.I * z / (‖z‖ : ℂ))) ^ 2)) := by
    filter_upwards [hne] with z hz
    have hpolar := norm_fderiv_sq_eq_polar (u := u) hz
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← hpolar,
      ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    congr 1
  calc
    dirichletEnergy u U
        = ∫⁻ z in U, ((‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2) := rfl
    _ = ∫⁻ z in U, (ENNReal.ofReal ((fderiv ℝ u z (z / (‖z‖ : ℂ))) ^ 2)
          + ENNReal.ofReal ((fderiv ℝ u z (Complex.I * z / (‖z‖ : ℂ))) ^ 2)) :=
        lintegral_congr_ae hpt
    _ = (∫⁻ z in U, ENNReal.ofReal ((fderiv ℝ u z (z / (‖z‖ : ℂ))) ^ 2))
          + (∫⁻ z in U, ENNReal.ofReal ((fderiv ℝ u z (Complex.I * z / (‖z‖ : ℂ))) ^ 2)) :=
        lintegral_add_left hmrad _

/-- **Tangential (angular) derivative identity.**
For `u : ℂ → ℝ` differentiable at `z`, the derivative of `u` along the circle
`θ ↦ exp(iθ)·z` at `θ = 0` equals the Fréchet derivative of `u` at `z` applied to the tangent
vector `i·z`.  This is the pointwise foundation for the angular gradient component. -/
theorem deriv_circle_eq_fderiv_tangent {u : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    deriv (fun θ : ℝ => u (Complex.exp (Complex.I * (θ : ℂ)) * z)) 0
      = fderiv ℝ u z (Complex.I * z) := by
  -- The coercion `θ ↦ (θ : ℂ)` has derivative `1` at every point.
  have hofReal : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 0 :=
    Complex.ofRealCLM.hasDerivAt
  -- Hence `θ ↦ I * θ` has derivative `I` at `0`.
  have hlin : HasDerivAt (fun θ : ℝ => Complex.I * (θ : ℂ)) Complex.I 0 := by
    simpa using hofReal.const_mul Complex.I
  -- Compose with `exp`: at `0` the base point is `I * 0 = 0`, and `exp 0 = 1`.
  have hexp : HasDerivAt (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) Complex.I 0 := by
    have h : HasDerivAt (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) * Complex.I) 0 :=
      (Complex.hasDerivAt_exp _).comp 0 hlin
    simpa [Complex.exp_zero] using h
  -- Multiply by the constant `z` to obtain the tangent curve `γ θ = exp(Iθ) · z`.
  have hγ : HasDerivAt (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ)) * z)
      (Complex.I * z) 0 := by
    simpa using hexp.mul_const z
  -- The curve passes through `z` at `θ = 0`, so the chain rule gives the claim.
  have hcomp : HasDerivAt (u ∘ fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ)) * z)
      (fderiv ℝ u z (Complex.I * z)) 0 :=
    hu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  exact hcomp.deriv

/-- **Scaled tangential derivative identity.**
For `u : ℂ → ℝ` differentiable at `z ≠ 0`, the value of the Fréchet derivative on the unit
tangential direction `I·z/‖z‖` equals `(1/‖z‖)` times the circular derivative of `u`. -/
theorem fderiv_unit_tangent_eq {u : ℂ → ℝ} {z : ℂ} (_hz : z ≠ 0)
    (hu : DifferentiableAt ℝ u z) :
    fderiv ℝ u z (Complex.I * z / (‖z‖ : ℂ))
      = (1 / ‖z‖) * deriv (fun θ : ℝ => u (Complex.exp (Complex.I * (θ : ℂ)) * z)) 0 := by
  rw [deriv_circle_eq_fderiv_tangent hu]
  have harg : Complex.I * z / (‖z‖ : ℂ) = (1 / ‖z‖ : ℝ) • (Complex.I * z) := by
    rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, div_eq_mul_inv,
      div_eq_mul_inv, one_mul, mul_comm ((‖z‖ : ℂ))⁻¹ _, mul_assoc]
  rw [harg, map_smul, smul_eq_mul]

end RiemannDynamics

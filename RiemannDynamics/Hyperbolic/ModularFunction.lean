/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.DiskMetric
import RiemannDynamics.Hyperbolic.ModularFormsBridge
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Topology.Covering.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Ring.Int.Parity

/-!
# The elliptic modular function λ

The level-2 modular function `λ : ℍ → ℂ ∖ {0, 1}` is the holomorphic
universal-covering map of the triply-punctured sphere by the upper
half-plane. We construct it as

  `λ(τ) = (θ₂(τ) / θ₃(τ))⁴`

where the theta nullwerte are built from Mathlib's `jacobiTheta₂`:

  `θ₂(τ) := exp(πi τ / 4) · jacobiTheta₂(τ / 2, τ)
          = ∑_{n ∈ ℤ} exp(πi (n + ½)² τ)`,
  `θ₃(τ) := jacobiTheta τ = jacobiTheta₂(0, τ)
          = ∑_{n ∈ ℤ} exp(πi n² τ)`.

Composing with the Cayley transform `cayleyToHalfPlane : 𝔻 → ℍ` from
`DiskMetric.lean`, we obtain `modularLambda : 𝔻 → ℂ ∖ {0, 1}`, the
covering map used in the proof of the Montel–Carathéodory theorem
(`StrongMontel`).

This file is currently architecture only: all properties (omitting
`{0, 1}`, Γ(2)-invariance, covering-map property) are stated as
`sorry`-stubbed theorems pending the full modular-forms / theta
identity development.
-/

namespace RiemannDynamics

open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

/-- The half-integer theta nullwert
`θ₂(τ) = exp(πi τ / 4) · jacobiTheta₂(τ / 2, τ) = ∑ exp(πi (n + ½)² τ)`. -/
noncomputable def theta2 (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- The standard theta nullwert `θ₃(τ) = jacobiTheta τ`. -/
noncomputable def theta3 (τ : ℂ) : ℂ := jacobiTheta τ

/-- The alternating-sign theta nullwert
`θ₄(τ) = ∑_{n ∈ ℤ} (-1)ⁿ exp(πi n² τ) = jacobiTheta(τ + 1)`. We take the
right-hand expression as the definition; the alternating-sign series form
is established as `theta4_eq_jacobiTheta_add_one` below. -/
noncomputable def theta4 (τ : ℂ) : ℂ := jacobiTheta (τ + 1)

/-- The modular function on the upper half-plane, as a map `ℂ → ℂ`. The
formula gives the correct value for `τ ∈ ℍ`; off `ℍ` the value is the
Lean junk for `0 / 0` and not mathematically meaningful. -/
noncomputable def modularLambdaH (τ : ℂ) : ℂ :=
  (theta2 τ) ^ 4 / (theta3 τ) ^ 4

/-- The modular function on the unit disk, obtained by composing
`modularLambdaH` with the Cayley transform `𝔻 → ℍ` from
`DiskMetric.lean`. -/
noncomputable def modularLambda (z : ℂ) : ℂ :=
  modularLambdaH (cayleyToHalfPlane z)

/-! ## Modular transformations under `T : τ ↦ τ + 1`

`θ₂`, `θ₃`, `θ₄` transform under `T` as follows:
- `θ₃(τ + 1) = θ₄(τ)` (immediate from the definition `θ₄(τ) := θ₃(τ + 1)`).
- `θ₄(τ + 1) = θ₃(τ)` (uses `jacobiTheta_two_add` for the period-2 invariance of `θ₃`).
- `θ₂(τ + 1) = exp(πi/4) · θ₂(τ)` (uses `jacobiTheta₂_add_half_T` below). -/

/-- Auxiliary identity for the two-variable Jacobi theta:
`jacobiTheta₂(z + ½, τ + 1) = jacobiTheta₂(z, τ)`. This follows because the
extra factor `exp(πi · n(n+1))` is `1` for every integer `n`. -/
lemma jacobiTheta₂_add_half_T (z τ : ℂ) :
    jacobiTheta₂ (z + 1 / 2) (τ + 1) = jacobiTheta₂ z τ := by
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term]
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have h_int : (n : ℤ) * (n + 1) = 2 * k := by linarith
  have h_cast : (n : ℂ) * ((n : ℂ) + 1) = 2 * (k : ℂ) := by exact_mod_cast h_int
  have h_eq :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z + 1 / 2)
        + (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ + 1)
      = (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z
          + (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)
        + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination (Real.pi : ℂ) * Complex.I * h_cast
  rw [h_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I k, mul_one]

/-- Identity `jacobiTheta₂(1/2, τ) = θ₄(τ)`. Both sides equal
`∑_n (−1)ⁿ exp(πi n² τ)`. -/
lemma jacobiTheta₂_one_half_eq_theta4 (τ : ℂ) :
    jacobiTheta₂ (1 / 2) τ = theta4 τ := by
  unfold theta4 jacobiTheta
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term]
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
  have h_int : (n - 1 : ℤ) * n = 2 * k := by
    have h1 : (n - 1 : ℤ) * n = (n - 1) * (n - 1 + 1) := by ring
    rw [h1]; linarith
  have h_cast : ((n : ℂ) - 1) * (n : ℂ) = 2 * (k : ℂ) := by exact_mod_cast h_int
  have h_eq :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2)
        + (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ
      = (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ + 1)
        + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    linear_combination -((Real.pi : ℂ) * Complex.I) * h_cast
  rw [h_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I (-k), mul_one]

/-- `θ₃(τ + 1) = θ₄(τ)`. Definitional. -/
theorem theta3_add_one (τ : ℂ) : theta3 (τ + 1) = theta4 τ := rfl

/-- `θ₄(τ + 1) = θ₃(τ)`. Uses `jacobiTheta` is period-2 in its argument. -/
theorem theta4_add_one (τ : ℂ) : theta4 (τ + 1) = theta3 τ := by
  unfold theta4 theta3
  rw [show (τ + 1 + 1 : ℂ) = 2 + τ from by ring]
  exact jacobiTheta_two_add τ

/-- `θ₂(τ + 1) = exp(πi/4) · θ₂(τ)`. Uses `jacobiTheta₂_add_half_T`. -/
theorem theta2_add_one (τ : ℂ) :
    theta2 (τ + 1) = Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * theta2 τ := by
  unfold theta2
  rw [show (τ + 1) / 2 = τ / 2 + 1 / 2 from by ring]
  rw [jacobiTheta₂_add_half_T (τ / 2) τ]
  rw [show (Real.pi : ℂ) * Complex.I * (τ + 1) / 4
        = (Real.pi : ℂ) * Complex.I * τ / 4 + (Real.pi : ℂ) * Complex.I / 4 from by ring]
  rw [Complex.exp_add]
  ring

/-- `θ₂(τ + 2) = i · θ₂(τ)`. Applying `theta2_add_one` twice gives the
factor `(exp(πi/4))² = exp(πi/2) = i`. -/
theorem theta2_two_add (τ : ℂ) : theta2 (τ + 2) = Complex.I * theta2 τ := by
  rw [show (τ + 2 : ℂ) = (τ + 1) + 1 from by ring]
  rw [theta2_add_one, theta2_add_one]
  rw [show Complex.exp ((Real.pi : ℂ) * Complex.I / 4)
        * (Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * theta2 τ)
      = Complex.exp ((Real.pi : ℂ) * Complex.I / 4
                     + (Real.pi : ℂ) * Complex.I / 4) * theta2 τ from by
    rw [Complex.exp_add]; ring]
  rw [show ((Real.pi : ℂ) * Complex.I / 4 + (Real.pi : ℂ) * Complex.I / 4)
        = (Real.pi : ℂ) * Complex.I / 2 from by ring]
  rw [show (Real.pi : ℂ) * Complex.I / 2 = (Real.pi / 2 : ℂ) * Complex.I from by ring]
  rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

/-- `θ₃(τ + 2) = θ₃(τ)`. Restates `jacobiTheta_two_add` in terms of `theta3`. -/
theorem theta3_two_add (τ : ℂ) : theta3 (τ + 2) = theta3 τ := by
  unfold theta3
  rw [show (τ + 2 : ℂ) = 2 + τ from by ring]
  exact jacobiTheta_two_add τ

/-- `θ₄(τ + 2) = θ₄(τ)`. Follows from `theta4 τ = theta3(τ + 1)`
+ `theta3_two_add`. -/
theorem theta4_two_add (τ : ℂ) : theta4 (τ + 2) = theta4 τ := by
  unfold theta4
  rw [show (τ + 2 + 1 : ℂ) = (τ + 1) + 2 from by ring]
  exact theta3_two_add (τ + 1)

/-! ## Holomorphy of `θ₂`, `θ₃`, `θ₄` on `ℍ`

`jacobiTheta` is differentiable on the upper half-plane (Mathlib's
`differentiableAt_jacobiTheta`); `jacobiTheta₂` is jointly differentiable
on `ℂ × {τ : ℂ | 0 < τ.im}` (`hasFDerivAt_jacobiTheta₂`). The theta
nullwerte `θ₂`, `θ₃`, `θ₄` inherit pointwise differentiability on `ℍ`. -/

/-- `θ₃ = jacobiTheta` is differentiable at every point of `ℍ`. -/
theorem theta3_differentiableAt {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ theta3 τ := differentiableAt_jacobiTheta hτ

/-- `θ₂(τ) = exp(πi τ / 4) · jacobiTheta₂(τ / 2, τ)` is differentiable at
every point of `ℍ`. -/
theorem theta2_differentiableAt {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ theta2 τ := by
  unfold theta2
  refine DifferentiableAt.mul ?_ ?_
  · -- exp((π·I)·τ/4) is entire
    have h_inner : DifferentiableAt ℂ (fun σ : ℂ => (Real.pi : ℂ) * Complex.I * σ / 4) τ :=
      ((differentiable_id.differentiableAt).const_mul ((Real.pi : ℂ) * Complex.I)).div_const 4
    exact Complex.differentiable_exp.differentiableAt.comp τ h_inner
  · -- jacobiTheta₂(τ/2, τ) via composition
    let g : ℂ → ℂ × ℂ := fun σ => (σ / 2, σ)
    let f : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
    have h_pair : DifferentiableAt ℂ g τ := by
      refine DifferentiableAt.prodMk ?_ differentiable_id.differentiableAt
      exact differentiable_id.differentiableAt.div_const 2
    have h_jt₂ : DifferentiableAt ℂ f (g τ) :=
      (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
    exact h_jt₂.comp τ h_pair

/-- `θ₄(τ) = jacobiTheta(τ + 1)` is differentiable at every point of `ℍ`. -/
theorem theta4_differentiableAt {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ theta4 τ := by
  unfold theta4
  have h_shift : DifferentiableAt ℂ (fun σ : ℂ => σ + 1) τ :=
    differentiable_id.differentiableAt.add_const 1
  have h_shift_im : 0 < (τ + 1).im := by simpa [Complex.add_im] using hτ
  have h_jt : DifferentiableAt ℂ jacobiTheta (τ + 1) :=
    differentiableAt_jacobiTheta h_shift_im
  exact h_jt.comp τ h_shift

/-- **`T²`-invariance of `λ`** on the upper half-plane:
`λ(τ + 2) = λ(τ)`. The proof combines `θ₂(τ+2) = i·θ₂(τ)` with
`θ₃(τ+2) = θ₃(τ)`; raising the `θ₂/θ₃` ratio to the fourth power kills
the `i` factor since `i⁴ = 1`. -/
theorem modularLambdaH_two_add (τ : ℂ) :
    modularLambdaH (τ + 2) = modularLambdaH τ := by
  unfold modularLambdaH
  rw [theta2_two_add, theta3_two_add]
  rw [mul_pow]
  rw [show Complex.I ^ 4 = 1 from by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; ring]
  ring

/-- Subtraction-by-2 also leaves `λ` invariant (the inverse of `T²`-invariance,
needed for the `ST⁻²S` generator below). -/
theorem modularLambdaH_sub_two (τ : ℂ) :
    modularLambdaH (τ - 2) = modularLambdaH τ := by
  have h := modularLambdaH_two_add (τ - 2)
  rw [show (τ - 2 + 2 : ℂ) = τ from by ring] at h
  exact h.symm

/-- **`T`-shift formula for `λ`.** `λ(τ + 1) = −(θ₂(τ)⁴ / θ₄(τ)⁴)`.
The proof applies the T-suite: `θ₂(τ+1) = e^{iπ/4}·θ₂(τ)`, `θ₃(τ+1) = θ₄(τ)`,
then raises to the fourth power and uses `(e^{iπ/4})⁴ = e^{iπ} = -1`. -/
theorem modularLambdaH_T_smul (τ : ℂ) :
    modularLambdaH (τ + 1) = -(theta2 τ ^ 4 / theta4 τ ^ 4) := by
  unfold modularLambdaH
  rw [theta2_add_one, theta3_add_one]
  rw [mul_pow]
  rw [show (Complex.exp ((Real.pi : ℂ) * Complex.I / 4)) ^ 4 = (-1 : ℂ) from by
    have h4 : ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4) = (Real.pi : ℂ) * Complex.I := by
      ring
    calc Complex.exp ((Real.pi : ℂ) * Complex.I / 4) ^ 4
        = Complex.exp (((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4)) := by
          rw [← Complex.exp_nat_mul]
      _ = Complex.exp ((Real.pi : ℂ) * Complex.I) := by rw [h4]
      _ = -1 := Complex.exp_pi_mul_I]
  ring

/-! ## Modular transformations under `S : τ ↦ −1/τ`

Mathlib provides `θ₃` under `S` as `jacobiTheta_S_smul`. The corresponding
`S`-transformations for `θ₂` and `θ₄` follow from the functional equation of
`jacobiTheta₂`, but require shifting the argument `z` and tracking signs;
they are recorded here as `sorry`-stubbed statements. -/

/-- `θ₂(−1/τ) = √(−iτ) · θ₄(τ)` for `τ ∈ ℍ`. Combines the
`jacobiTheta₂_functional_equation` evaluated at `z = -1/(2τ), τ = -1/τ`
with `jacobiTheta₂_one_half_eq_theta4`. -/
theorem theta2_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta2 (-1 / τ) = ((-Complex.I * τ) ^ (1 / 2 : ℂ)) * theta4 τ := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hmIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  -- Key identity: I/τ = (-Iτ)⁻¹, since (-Iτ)·(I/τ) = -I²·(τ/τ) = 1.
  have h_inv_relation : Complex.I / τ = (-Complex.I * τ)⁻¹ := by
    have h_prod : (-Complex.I * τ) * (Complex.I / τ) = 1 := by
      rw [show (Complex.I / τ) = Complex.I * τ⁻¹ from div_eq_mul_inv _ _]
      rw [show (-Complex.I * τ) * (Complex.I * τ⁻¹)
            = -(Complex.I ^ 2) * (τ * τ⁻¹) from by ring]
      rw [mul_inv_cancel₀ hτ_ne, mul_one, Complex.I_sq]; norm_num
    exact eq_inv_of_mul_eq_one_right h_prod
  -- arg(-Iτ) ≠ π since Re(-Iτ) = τ.im > 0.
  have h_arg : (-Complex.I * τ).arg ≠ Real.pi := by
    intro h_arg_eq
    have h_eq := Complex.arg_eq_pi_iff.mp h_arg_eq
    have h_re : (-Complex.I * τ).re = τ.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [h_re] at h_eq
    linarith [h_eq.1]
  unfold theta2
  -- Simplify (-1/τ)/2 = -1/(2τ) in the inner jacobiTheta₂ argument.
  rw [show ((-1 / τ : ℂ)) / 2 = -1 / (2 * τ) from by ring]
  -- Apply the functional equation at z = -1/(2τ), τ_param = -1/τ.
  rw [jacobiTheta₂_functional_equation (-1 / (2 * τ)) (-1 / τ)]
  -- Simplify the substituted arguments and exponents.
  rw [show (-Complex.I * (-1 / τ) : ℂ) = Complex.I / τ from by ring]
  rw [show (-1 / (2 * τ) : ℂ) / (-1 / τ) = 1 / 2 from by field_simp]
  rw [show (-1 / (-1 / τ) : ℂ) = τ from by field_simp]
  rw [show -(Real.pi : ℂ) * Complex.I * (-1 / (2 * τ)) ^ 2 / (-1 / τ)
        = (Real.pi : ℂ) * Complex.I / (4 * τ) from by field_simp; ring]
  rw [jacobiTheta₂_one_half_eq_theta4]
  -- The outer exp argument equals the negation of the inner one.
  rw [show (Real.pi : ℂ) * Complex.I * (-1 / τ) / 4
        = -((Real.pi : ℂ) * Complex.I / (4 * τ)) from by field_simp]
  -- Combine the two exp factors: exp(-x) · exp(x) = exp(0) = 1.
  rw [show ∀ a b c d : ℂ, a * (b * c * d) = (a * c) * (b * d)
        from fun a b c d => by ring]
  rw [← Complex.exp_add]
  rw [show -((Real.pi : ℂ) * Complex.I / (4 * τ))
        + (Real.pi : ℂ) * Complex.I / (4 * τ) = 0 from by ring]
  rw [Complex.exp_zero, one_mul]
  -- Goal: 1 / (I/τ)^{1/2} · theta4 τ = (-Iτ)^{1/2} · theta4 τ.
  congr 1
  rw [h_inv_relation, Complex.inv_cpow _ _ h_arg, one_div, inv_inv]

/-- `θ₃(−1/τ) = √(−iτ) · θ₃(τ)` for `τ ∈ ℍ`. (`jacobiTheta_S_smul` ported to
the bare-`ℂ` form used in this file.) -/
theorem theta3_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta3 (-1 / τ) = ((-Complex.I * τ) ^ (1 / 2 : ℂ)) * theta3 τ := by
  unfold theta3
  set τH : UpperHalfPlane := ⟨τ, hτ⟩ with hτH_def
  have h_τH_coe : (τH : ℂ) = τ := rfl
  have hS_coe : ((ModularGroup.S • τH : UpperHalfPlane) : ℂ) = -1 / τ := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(τH : ℂ))⁻¹ = -1 / τ
    rw [h_τH_coe]; field_simp
  have step := jacobiTheta_S_smul τH
  rw [h_τH_coe, hS_coe] at step
  exact step

/-- `θ₄(−1/τ) = √(−iτ) · θ₂(τ)` for `τ ∈ ℍ`. Same strategy as
`theta2_S_smul` but applied at `z = 1/2` rather than `z = -1/(2τ)`. -/
theorem theta4_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta4 (-1 / τ) = ((-Complex.I * τ) ^ (1 / 2 : ℂ)) * theta2 τ := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hmIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  have h_inv_relation : Complex.I / τ = (-Complex.I * τ)⁻¹ := by
    have h_prod : (-Complex.I * τ) * (Complex.I / τ) = 1 := by
      rw [show (Complex.I / τ) = Complex.I * τ⁻¹ from div_eq_mul_inv _ _]
      rw [show (-Complex.I * τ) * (Complex.I * τ⁻¹)
            = -(Complex.I ^ 2) * (τ * τ⁻¹) from by ring]
      rw [mul_inv_cancel₀ hτ_ne, mul_one, Complex.I_sq]; norm_num
    exact eq_inv_of_mul_eq_one_right h_prod
  have h_arg : (-Complex.I * τ).arg ≠ Real.pi := by
    intro h_arg_eq
    have h_eq := Complex.arg_eq_pi_iff.mp h_arg_eq
    have h_re : (-Complex.I * τ).re = τ.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [h_re] at h_eq
    linarith [h_eq.1]
  -- Rewrite θ₄(-1/τ) as jacobiTheta₂(1/2, -1/τ).
  rw [← jacobiTheta₂_one_half_eq_theta4]
  -- Apply the functional equation at z = 1/2, τ_param = -1/τ.
  rw [jacobiTheta₂_functional_equation (1 / 2) (-1 / τ)]
  rw [show (-Complex.I * (-1 / τ) : ℂ) = Complex.I / τ from by ring]
  rw [show (1 / 2 : ℂ) / (-1 / τ) = -(τ / 2) from by field_simp]
  rw [show (-1 / (-1 / τ) : ℂ) = τ from by field_simp]
  rw [show -(Real.pi : ℂ) * Complex.I * (1 / 2) ^ 2 / (-1 / τ)
        = (Real.pi : ℂ) * Complex.I * τ / 4 from by field_simp; ring]
  rw [jacobiTheta₂_neg_left]
  -- Now goal: (1/(I/τ)^{1/2}) · exp(πIτ/4) · jacobiTheta₂(τ/2, τ)
  --        = (-Iτ)^{1/2} · theta2 τ
  -- where theta2 τ = exp(πIτ/4) · jacobiTheta₂(τ/2, τ).
  unfold theta2
  rw [h_inv_relation, Complex.inv_cpow _ _ h_arg, one_div, inv_inv]
  ring

/-- **`S`-quotient form of `λ`.** For `τ ∈ ℍ`,
`λ(−1/τ) = (θ₄(τ)/θ₃(τ))⁴`. The proof cancels the common `√(−iτ)` factor
that the S-suite introduces in both numerator and denominator. -/
theorem modularLambdaH_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (-1 / τ) = (theta4 τ / theta3 τ) ^ 4 := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have h_root_ne : (-Complex.I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne)
  unfold modularLambdaH
  rw [theta2_S_smul hτ, theta3_S_smul hτ, mul_pow, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 4 h_root_ne), div_pow]

/-! ## `Γ(2)`-invariance generators

`Γ(2)` is generated by `T² = [[1, 2], [0, 1]]` (which is `τ ↦ τ + 2`) and
`[[1, 0], [2, 1]] = S · T⁻² · S` (which is `τ ↦ τ / (2τ + 1)`). The first
generator is `modularLambdaH_two_add`. The second is below. -/

/-- **Second `Γ(2)` generator.** `λ(τ / (2τ + 1)) = λ(τ)` for `τ ∈ ℍ`.
The matrix `[[1, 0], [2, 1]]` acts as `τ ↦ τ / (2τ + 1) = S(T⁻²(S(τ)))`,
so we chain S-, T⁻²-, S-invariances of the `θ_i` ratios. -/
theorem modularLambdaH_div_two_tau_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (τ / (2 * τ + 1)) = modularLambdaH τ := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have h2τp1_im : (2 * τ + 1 : ℂ).im = 2 * τ.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.one_im]
  have h2τp1_ne : (2 * τ + 1 : ℂ) ≠ 0 := by
    intro h
    have h_im : (2 * τ + 1 : ℂ).im = 0 := by rw [h]; rfl
    rw [h2τp1_im] at h_im
    linarith
  -- `Im(-1/τ) = τ.im / |τ|² > 0`.
  have h_neg_inv_im : (-1 / τ : ℂ).im = τ.im / Complex.normSq τ := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by field_simp]
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  have h_neg_inv_im_pos : 0 < (-1 / τ : ℂ).im := by
    rw [h_neg_inv_im]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ_ne)
  -- `Im(-1/τ - 2) = Im(-1/τ) > 0`.
  have h_σ_im_pos : 0 < (-1/τ - 2 : ℂ).im := by
    have h_eq : (-1/τ - 2 : ℂ).im = (-1/τ : ℂ).im := by
      simp [Complex.sub_im]
    rw [h_eq]; exact h_neg_inv_im_pos
  -- `-1/τ - 2 ≠ 0` (from positive imaginary part).
  have h_σ_ne : (-1/τ - 2 : ℂ) ≠ 0 := by
    intro h
    have : (-1/τ - 2 : ℂ).im = 0 := by rw [h]; rfl
    linarith
  -- `τ / (2τ + 1) = -1 / (-1/τ - 2)` via cross-multiplication.
  have h_rewrite : (τ / (2 * τ + 1) : ℂ) = -1 / (-1/τ - 2) := by
    rw [div_eq_div_iff h2τp1_ne h_σ_ne]
    field_simp
    ring
  rw [h_rewrite]
  -- Apply S-quotient form at σ = -1/τ - 2.
  rw [modularLambdaH_S_smul h_σ_im_pos]
  -- Use T²-invariance to step σ = -1/τ - 2 back to -1/τ.
  have h_t4 : theta4 (-1/τ - 2) = theta4 (-1/τ) := by
    have := theta4_two_add (-1/τ - 2)
    rwa [show (-1/τ - 2 + 2 : ℂ) = -1/τ from by ring, eq_comm] at this
  have h_t3 : theta3 (-1/τ - 2) = theta3 (-1/τ) := by
    have := theta3_two_add (-1/τ - 2)
    rwa [show (-1/τ - 2 + 2 : ℂ) = -1/τ from by ring, eq_comm] at this
  rw [h_t4, h_t3]
  -- Apply the S-suite at τ to convert θ_i(-1/τ) to factors times θ_j(τ).
  rw [theta4_S_smul hτ, theta3_S_smul hτ]
  -- Cancel the common `√(-iτ)`.
  have h_root_ne : (-Complex.I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne)
  rw [mul_div_mul_left _ _ h_root_ne]
  -- Goal reduced to `(θ₂(τ)/θ₃(τ))⁴ = λ(τ)`; unfold the definition.
  unfold modularLambdaH
  rw [div_pow]

/-! ## Jacobi's identity: setup via the difference's modular transformations

Define `f(τ) := θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴`. Jacobi's identity asserts
`f ≡ 0` on `ℍ`. The classical proof shows that `f` transforms as a
specific modular form for `Γ_θ = ⟨S, T²⟩` of weight 2, has q-expansion
starting at `O(q²)` (the leading `q⁰` and `q¹` coefficients all cancel),
and then concludes by the uniqueness of holomorphic functions with that
transformation behaviour vanishing at the cusp.

This file proves the two transformation properties of `f` (which together
fix its weight-2 character on `Γ_θ`). The remaining work — q-expansion +
holomorphic uniqueness — requires modular-form infrastructure beyond the
current development. -/

/-- Under the T-shift `τ ↦ τ + 1`, the Jacobi difference negates:
`θ₂(τ+1)⁴ + θ₄(τ+1)⁴ − θ₃(τ+1)⁴ = −(θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴)`. -/
theorem jacobi_diff_T_smul (τ : ℂ) :
    theta2 (τ + 1) ^ 4 + theta4 (τ + 1) ^ 4 - theta3 (τ + 1) ^ 4
      = -(theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) := by
  rw [theta2_add_one, theta3_add_one, theta4_add_one]
  rw [mul_pow]
  rw [show (Complex.exp ((Real.pi : ℂ) * Complex.I / 4)) ^ 4 = (-1 : ℂ) from by
    have h4 : ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4) = (Real.pi : ℂ) * Complex.I := by
      ring
    calc Complex.exp ((Real.pi : ℂ) * Complex.I / 4) ^ 4
        = Complex.exp (((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4)) := by
          rw [← Complex.exp_nat_mul]
      _ = Complex.exp ((Real.pi : ℂ) * Complex.I) := by rw [h4]
      _ = -1 := Complex.exp_pi_mul_I]
  ring

/-- Under the S-action `τ ↦ −1/τ`, the Jacobi difference picks up a `−τ²`
factor: `θ₂(−1/τ)⁴ + θ₄(−1/τ)⁴ − θ₃(−1/τ)⁴ = −τ² · (θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴)`.
Each `θ_i(−1/τ)⁴` collects `(√(−iτ))⁴ = −τ²` from the S-suite. -/
theorem jacobi_diff_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta2 (-1 / τ) ^ 4 + theta4 (-1 / τ) ^ 4 - theta3 (-1 / τ) ^ 4
      = -τ ^ 2 * (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hmIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  -- `(√(-iτ))⁴ = (-iτ)² = -τ²`.
  have h_sq : ((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 2 = -Complex.I * τ := by
    rw [sq, ← Complex.cpow_add _ _ hmIτ_ne]
    norm_num
  have h_pow4 : ((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 4 = -τ ^ 2 := by
    have h_expand : ((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 4
        = (((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 2) ^ 2 := by ring
    rw [h_expand, h_sq, mul_pow, neg_sq, Complex.I_sq]
    ring
  rw [theta2_S_smul hτ, theta3_S_smul hτ, theta4_S_smul hτ]
  rw [mul_pow, mul_pow, mul_pow]
  rw [h_pow4]
  ring

/-- **`T²`-invariance of the Jacobi difference.** Applying
`jacobi_diff_T_smul` twice composes the sign factor `-1 · -1 = 1`,
showing `f(τ + 2) = f(τ)` where `f := θ₂⁴ + θ₄⁴ − θ₃⁴`. -/
theorem jacobi_diff_two_add (τ : ℂ) :
    theta2 (τ + 2) ^ 4 + theta4 (τ + 2) ^ 4 - theta3 (τ + 2) ^ 4
      = theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4 := by
  have h1 := jacobi_diff_T_smul τ
  have h2 := jacobi_diff_T_smul (τ + 1)
  rw [show (τ + 1 + 1 : ℂ) = τ + 2 from by ring] at h2
  rw [h2, h1]; ring

/-- The **squared Jacobi difference** `f² = (θ₂⁴ + θ₄⁴ − θ₃⁴)²` is
`T`-invariant: the sign from `jacobi_diff_T_smul` squares away. -/
theorem jacobi_diff_sq_T_smul (τ : ℂ) :
    (theta2 (τ + 1) ^ 4 + theta4 (τ + 1) ^ 4 - theta3 (τ + 1) ^ 4) ^ 2
      = (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2 := by
  rw [jacobi_diff_T_smul]; ring

/-- The **squared Jacobi difference** `f²` transforms with weight 4
under `S : τ ↦ −1/τ`. The `(−τ²)` factor from `jacobi_diff_S_smul`
squares to `τ⁴`. -/
theorem jacobi_diff_sq_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    (theta2 (-1 / τ) ^ 4 + theta4 (-1 / τ) ^ 4 - theta3 (-1 / τ) ^ 4) ^ 2
      = τ ^ 4 * (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2 := by
  rw [jacobi_diff_S_smul hτ]; ring

/-- The squared Jacobi difference is holomorphic on the upper
half-plane. Follows from holomorphy of `θ₂`, `θ₃`, `θ₄` together with
ring closure under products, sums, and powers. -/
theorem jacobi_diff_sq_differentiableOn :
    DifferentiableOn ℂ
      (fun τ : ℂ => (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2)
      { τ : ℂ | 0 < τ.im } := by
  intro τ hτ
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((((theta2_differentiableAt hτ).pow 4).add
    ((theta4_differentiableAt hτ).pow 4)).sub
    ((theta3_differentiableAt hτ).pow 4)).pow 2

/-! ### Analytic norm bounds at the cusp

The cusp bound for `f²` is reduced to four pointwise bounds on the
individual theta nullwerte for `τ.im ≥ 1`: `θ₂` has the leading
exponential factor `exp(−π·τ.im/4)`, `θ₃` and `θ₄` are bounded
constants close to 1, and `θ₃ − θ₄` has full `exp(−π·τ.im)` decay
because the constant terms cancel. The first bound is the analytic
content of the q-expansion of `θ₂` at the cusp; the other three
follow from `norm_jacobiTheta_sub_one_le`. -/

/-- `‖θ₂(τ)‖ ≤ 10 · exp(−π·τ.im/4)` for `τ.im ≥ 1`. Encodes the
leading factor `q^{1/4}` in `θ₂(τ) = 2 q^{1/4}(1 + q² + q⁶ + …)`,
`q = exp(πiτ)`. Bounds the integer sum
`∑_{n ∈ ℤ} ‖jacobiTheta₂_term n (τ/2) τ‖` by `2·(1−R)⁻¹` where
`R = exp(−π·τ.im)`, using that each term equals
`exp(−π·τ.im·n(n+1))` and `n(n+1) ≥ |n|` (split through `Int.rec`). -/
theorem theta2_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ‖ ≤ 10 * Real.exp (-Real.pi * τ.im / 4) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- `R = exp(−π·τ.im)` and its useful bounds.
  set R : ℝ := Real.exp (-Real.pi * τ.im) with hR_def
  have hR_pos : 0 < R := Real.exp_pos _
  have hR_le_exp_neg_pi : R ≤ Real.exp (-Real.pi) := by
    rw [hR_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have hR_lt_one : R < 1 := lt_of_le_of_lt hR_le_exp_neg_pi (by linarith)
  have h_one_sub_pos : 0 < 1 - R := by linarith
  have h_one_sub_ge_half : 1/2 ≤ 1 - R := by
    have hR_le_half : R ≤ 1/2 := le_trans hR_le_exp_neg_pi (le_of_lt h_exp_neg_pi_lt_half)
    linarith
  -- Geometric series HasSum and its ℤ-extension via Int.rec.
  have h_geo : HasSum (fun n : ℕ => R ^ n) ((1 - R)⁻¹) :=
    hasSum_geometric_of_lt_one hR_pos.le hR_lt_one
  have h_int_rec_hasSum :
      HasSum (fun n : ℤ => Int.rec (fun m : ℕ => R ^ m) (fun m : ℕ => R ^ m) n)
             ((1 - R)⁻¹ + (1 - R)⁻¹) :=
    HasSum.int_rec h_geo h_geo
  -- `(τ/2).im = τ.im / 2`.
  have h_zim : (τ / 2 : ℂ).im = τ.im / 2 := by
    simp
  -- Per-term bound: `‖jacobiTheta₂_term n (τ/2) τ‖ ≤ Int.rec R^· R^· n`.
  have h_term_bound : ∀ n : ℤ,
      ‖jacobiTheta₂_term n (τ / 2) τ‖
        ≤ Int.rec (fun m : ℕ => R ^ m) (fun m : ℕ => R ^ m) n := by
    intro n
    rw [norm_jacobiTheta₂_term, h_zim]
    cases n with
    | ofNat m =>
      change Real.exp _ ≤ R ^ m
      rw [hR_def, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h_cast : ((Int.ofNat m : ℤ) : ℝ) = (m : ℝ) := by simp
      rw [h_cast]
      have h_prod_nn : 0 ≤ Real.pi * τ.im * (m : ℝ) ^ 2 := by positivity
      nlinarith
    | negSucc m =>
      change Real.exp _ ≤ R ^ m
      rw [hR_def, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h_cast : ((Int.negSucc m : ℤ) : ℝ) = -((m : ℝ) + 1) := by
        rw [Int.cast_negSucc]; push_cast; ring
      rw [h_cast]
      have h_prod_nn : 0 ≤ Real.pi * τ.im * (m : ℝ) ^ 2 := by positivity
      nlinarith
  -- Apply `tsum_of_norm_bounded`.
  have h_hsum := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_tsum_le :
      ‖∑' n : ℤ, jacobiTheta₂_term n (τ / 2) τ‖ ≤ (1 - R)⁻¹ + (1 - R)⁻¹ :=
    tsum_of_norm_bounded h_int_rec_hasSum h_term_bound
  have h_jt₂_le : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ (1 - R)⁻¹ + (1 - R)⁻¹ := by
    rw [← h_hsum.tsum_eq]; exact h_tsum_le
  -- `(1 - R)⁻¹ ≤ 2`.
  have h_quot_le : (1 - R)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h_one_sub_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have h_jt₂_le_4 : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ 4 := by linarith
  -- Reassemble `‖θ₂(τ)‖ = ‖exp(πi τ/4)‖ · ‖jacobiTheta₂(τ/2, τ)‖`.
  unfold theta2
  rw [norm_mul]
  have h_exp_re : ((Real.pi : ℂ) * Complex.I * τ / 4).re = -Real.pi * τ.im / 4 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h_exp_norm : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4)‖
                  = Real.exp (-Real.pi * τ.im / 4) := by
    rw [Complex.norm_exp, h_exp_re]
  rw [h_exp_norm]
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im / 4) := Real.exp_pos _
  calc Real.exp (-Real.pi * τ.im / 4) * ‖jacobiTheta₂ (τ / 2) τ‖
      ≤ Real.exp (-Real.pi * τ.im / 4) * 4 :=
        mul_le_mul_of_nonneg_left h_jt₂_le_4 h_exp_pos.le
    _ ≤ 10 * Real.exp (-Real.pi * τ.im / 4) := by linarith

/-- `‖θ₃(τ)‖ ≤ 10` for `τ.im ≥ 1`. The actual value is close to 1;
the loose bound `10` is chosen for convenience. -/
theorem theta3_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ‖ ≤ 10 := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- Use the Mathlib bound on ‖jacobiTheta τ - 1‖.
  have h_mathlib : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτim_pos
  -- Bound exp(-π·τ.im) ≤ exp(-π) and exp(-π) < 1/2.
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have h_exp_lt_half : Real.exp (-Real.pi * τ.im) < 1/2 :=
    lt_of_le_of_lt h_exp_at_one h_exp_neg_pi_lt_half
  have h_one_sub_ge : 1/2 ≤ 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_one_sub_pos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_exp_le_one : Real.exp (-Real.pi * τ.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  -- 2/(1 - e^{-π·τ.im}) ≤ 4.
  have h_quot_le : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 4 := by
    rw [div_le_iff₀ h_one_sub_pos]; linarith
  -- Hence ‖θ₃ - 1‖ ≤ 4 · 1 = 4.
  have h_sub_one_le : ‖jacobiTheta τ - 1‖ ≤ 4 := by
    refine h_mathlib.trans ?_
    have := mul_le_mul h_quot_le h_exp_le_one (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 4)
    linarith
  -- ‖θ₃‖ = ‖(θ₃ - 1) + 1‖ ≤ ‖θ₃ - 1‖ + 1 ≤ 5 ≤ 10.
  unfold theta3
  calc ‖jacobiTheta τ‖
      = ‖(jacobiTheta τ - 1) + 1‖ := by congr 1; ring
    _ ≤ ‖jacobiTheta τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 4 + 1 := by rw [norm_one]; linarith
    _ ≤ 10 := by norm_num

/-- `‖θ₄(τ)‖ ≤ 10` for `τ.im ≥ 1`. Same bound as `θ₃` since
`θ₄(τ) = θ₃(τ + 1)` and `(τ + 1).im = τ.im`. -/
theorem theta4_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta4 τ‖ ≤ 10 := by
  have h_eq : theta4 τ = theta3 (τ + 1) := (theta3_add_one τ).symm
  have h_im : 1 ≤ (τ + 1).im := by simpa [Complex.add_im] using hτ
  rw [h_eq]
  exact theta3_norm_le_of_im_ge_one h_im

/-- **Extracted bound `‖θ₃(τ) − 1‖ ≤ 4·exp(−π·τ.im)` for `τ.im ≥ 1`.**
This is the per-τ specialization of Mathlib's
`norm_jacobiTheta_sub_one_le`: at `τ.im ≥ 1`, the quotient
`2/(1 − exp(−π·τ.im))` is bounded by `4`. -/
theorem theta3_sub_one_norm_le_exp_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - 1‖ ≤ 4 * Real.exp (-Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  have h_mathlib : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτim_pos
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have h_exp_lt_half : Real.exp (-Real.pi * τ.im) < 1/2 :=
    lt_of_le_of_lt h_exp_at_one h_exp_neg_pi_lt_half
  have h_one_sub_pos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_quot_le : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 4 := by
    rw [div_le_iff₀ h_one_sub_pos]; linarith
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im) := Real.exp_pos _
  unfold theta3
  exact h_mathlib.trans (mul_le_mul_of_nonneg_right h_quot_le h_exp_pos.le)

/-- **Lower bound `1/2 ≤ ‖θ₃(τ)‖` for `τ.im ≥ 1`.** Follows from
`theta3_sub_one_norm_le_exp_of_im_ge_one` since
`4·exp(−π·τ.im) ≤ 4·exp(−π) < 1/2`. -/
theorem theta3_norm_ge_half_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    (1 : ℝ)/2 ≤ ‖theta3 τ‖ := by
  have h_sub_one := theta3_sub_one_norm_le_exp_of_im_ge_one hτ
  -- 4 exp(-π τ.im) ≤ 4 exp(-π) < 1/2. Need exp(π) > 8.
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
  -- exp(π) > 8 via exp(π) ≥ exp(3) > 2.7^3 > 8.
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_8 : (8 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]
    nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_pi_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h_exp_pi_gt_8 : (8 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_8.trans_le (Real.exp_le_exp.mpr h_pi_gt_3.le)
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/8 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/8),
        show (1/8 : ℝ)⁻¹ = 8 from by norm_num]
    exact h_exp_pi_gt_8
  have h_four_exp_lt : 4 * Real.exp (-Real.pi * τ.im) < 1/2 := by
    have h1 : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := h_exp_at_one
    have h2 : Real.exp (-Real.pi) < 1/8 := h_exp_neg_pi_lt
    linarith
  have h_norm_sub_one_lt : ‖theta3 τ - 1‖ < 1/2 := lt_of_le_of_lt h_sub_one h_four_exp_lt
  -- ‖θ₃‖ ≥ 1 - ‖θ₃ - 1‖ > 1/2.
  have h_rev := norm_sub_norm_le (1 : ℂ) (1 - theta3 τ)
  have h_eq1 : (1 : ℂ) - (1 - theta3 τ) = theta3 τ := by ring
  have h_eq2 : ‖(1 : ℂ) - theta3 τ‖ = ‖theta3 τ - 1‖ := by
    rw [show (1 : ℂ) - theta3 τ = -(theta3 τ - 1) from by ring, norm_neg]
  rw [h_eq1, h_eq2, norm_one] at h_rev
  linarith

/-- **Uniform cusp `i∞` bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ)‖ ≤ 160000·exp(−π·τ.im)`. Chains `‖θ₂(τ)‖⁴ ≤ 10⁴·exp(−π·τ.im)`
(from `theta2_norm_le_of_im_ge_one`) with the lower bound
`‖θ₃(τ)‖ ≥ 1/2` from `theta3_norm_ge_half_of_im_ge_one`. The bound is
not sharp; the actual leading term is `16·exp(−π·τ.im)`. -/
theorem modularLambdaH_norm_le_exp_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ‖ ≤ 160000 * Real.exp (-Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have h2 := theta2_norm_le_of_im_ge_one hτ
  have h3_ge_half := theta3_norm_ge_half_of_im_ge_one hτ
  -- θ₃(τ) ≠ 0 because ‖θ₃(τ)‖ ≥ 1/2 > 0.
  have h3_ne : theta3 τ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h3_ge_half
    linarith
  have h3_pow_ne : (theta3 τ)^4 ≠ 0 := pow_ne_zero 4 h3_ne
  have h2_nn : 0 ≤ ‖theta2 τ‖ := norm_nonneg _
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im / 4) := Real.exp_pos _
  have h2_pow4 : ‖theta2 τ‖^4 ≤ 10000 * Real.exp (-Real.pi * τ.im) := by
    have h_pow_le : ‖theta2 τ‖^4 ≤ (10 * Real.exp (-Real.pi * τ.im / 4))^4 :=
      pow_le_pow_left₀ h2_nn h2 4
    have h_simp : (10 * Real.exp (-Real.pi * τ.im / 4))^4 =
        10000 * Real.exp (-Real.pi * τ.im) := by
      rw [mul_pow]
      ring_nf
      rw [← Real.exp_nat_mul]
      ring_nf
    linarith [h_pow_le, h_simp.symm.le]
  have h3_pow4 : (1 : ℝ)/16 ≤ ‖theta3 τ‖^4 := by
    have h_half_nn : (0 : ℝ) ≤ 1/2 := by norm_num
    have := pow_le_pow_left₀ h_half_nn h3_ge_half 4
    have h_simp : ((1 : ℝ)/2)^4 = 1/16 := by norm_num
    linarith
  unfold modularLambdaH
  rw [norm_div, norm_pow, norm_pow]
  -- ‖θ₂⁴‖ / ‖θ₃⁴‖ = ‖θ₂‖⁴ / ‖θ₃‖⁴ ≤ (10⁴ exp) / (1/16) = 16 · 10⁴ exp.
  have h_denom_pos : 0 < ‖theta3 τ‖^4 := by
    have : 0 < ‖theta3 τ‖ := norm_pos_iff.mpr h3_ne
    positivity
  rw [div_le_iff₀ h_denom_pos]
  -- Goal: ‖θ₂‖⁴ ≤ 160000 e^(-π τ.im) · ‖θ₃‖⁴.
  -- Use ‖θ₃‖⁴ ≥ 1/16 to get RHS ≥ 160000 e^(-π τ.im) · (1/16) = 10000 e^(-π τ.im) ≥ ‖θ₂‖⁴.
  have h_exp_nn : 0 ≤ Real.exp (-Real.pi * τ.im) := (Real.exp_pos _).le
  have h_factor_nn : 0 ≤ 160000 * Real.exp (-Real.pi * τ.im) := by positivity
  have h_lower : 10000 * Real.exp (-Real.pi * τ.im) ≤
      160000 * Real.exp (-Real.pi * τ.im) * ‖theta3 τ‖^4 := by
    have h_rewrite : 10000 * Real.exp (-Real.pi * τ.im) =
        160000 * Real.exp (-Real.pi * τ.im) * (1/16) := by ring
    rw [h_rewrite]
    exact mul_le_mul_of_nonneg_left h3_pow4 h_factor_nn
  linarith

/-- **Norm of a `jacobiTheta₂_term` at `z = τ/2`.** For each integer `n`,
`‖jacobiTheta₂_term n (τ/2) τ‖ = exp(-π · n·(n+1) · τ.im)`. The argument
of the exponential simplifies via `2π i n · (τ/2) + π i n² τ = π i n(n+1) τ`. -/
theorem jacobiTheta₂_term_half_norm (n : ℤ) (τ : ℂ) :
    ‖jacobiTheta₂_term n (τ / 2) τ‖ =
      Real.exp (-(Real.pi * (n : ℝ) * ((n : ℝ) + 1) * τ.im)) := by
  unfold jacobiTheta₂_term
  rw [Complex.norm_exp]
  -- Rewrite argument as πi · (n*(n+1) : ℝ) · τ.
  have h_arg :
      (2 : ℂ) * Real.pi * Complex.I * (n : ℂ) * (τ / 2) +
        Real.pi * Complex.I * (n : ℂ) ^ 2 * τ =
      ((Real.pi * (n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [h_arg, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]

/-- **Tail bound for `jacobiTheta₂(τ/2, τ)`.** For `τ.im ≥ 1`,
`‖jacobiTheta₂(τ/2, τ) - 2‖ ≤ 8·exp(-2π·τ.im)`.

This is the leading-term estimate. The series
`jacobiTheta₂(τ/2, τ) = Σ_n jacobiTheta₂_term n (τ/2) τ` has each term
of norm `exp(-π · n·(n+1) · τ.im)` (by `jacobiTheta₂_term_half_norm`).
At `n ∈ {0, -1}`, `n(n+1) = 0` and the term is `exp(0) = 1`, so the
finite portion `∑_{n ∈ {0,-1}} term n = 2`.

**Proof outline:**

1. Set `s := {-2, -1, 0, 1} : Finset ℤ`. Then
   `∑ n ∈ s, term n = 2 + 2 · exp(2πi τ)` (since `term ±1 = term (-2) = exp(2πi τ)`).
2. By `Summable.sum_add_tsum_subtype_compl`:
   `∑'_{n ∉ s} term n = jacobiTheta₂(τ/2, τ) - (2 + 2·exp(2πi τ))`.
3. By `norm_tsum_le_tsum_norm` and `norm_jacobiTheta₂_term_le` (with
   `T = τ.im`, `S = τ.im/2`):
   `‖∑'_{n ∉ s} term n‖ ≤ ∑'_{n ∉ s} exp(-π τ.im (n² - |n|))`.
4. For `n ∉ s` (i.e., `|n| ≥ 2`): `n² - |n| ≥ |n|`. So
   `‖term n‖ ≤ exp(-π τ.im |n|)`, summing geometrically gives
   `Σ_{|n|≥2} exp(-π|n|·τ.im) ≤ 3·exp(-2π·τ.im)` for `τ.im ≥ 1`.
5. Triangle inequality:
   `‖jacobiTheta₂(τ/2, τ) - 2‖ = ‖(j₂ - 2 - 2 e^(2πi τ)) + 2 e^(2πi τ)‖`
   `≤ ‖j₂ - 2 - 2 e^(2πi τ)‖ + ‖2 e^(2πi τ)‖`
   `≤ 3·exp(-2π·τ.im) + 2·exp(-2π·τ.im) = 5·exp(-2π·τ.im) ≤ 8·exp(-2π·τ.im)`.

The key sub-step is the geometric tail bound (#4), which uses the
exponential decay of the loose Mathlib bound on `‖jacobiTheta₂_term n‖`.
-/
theorem jacobiTheta₂_half_sub_two_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 8 * Real.exp (-2 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  -- Need r < 1/2 for the geometric bound (1-r)⁻¹ < 2.
  have hr_lt_half : r < 1 / 2 := by
    have h_arg : -2 * Real.pi * τ.im ≤ -2 * Real.pi := by nlinarith
    have h_le : r ≤ Real.exp (-2 * Real.pi) := Real.exp_le_exp.mpr h_arg
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_2pi_gt_1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h_exp_2pi_gt_2 : (2 : ℝ) < Real.exp (2 * Real.pi) := by
      have h_mono : Real.exp 1 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h_2pi_gt_1.le
      linarith
    have h_exp_neg_pos : 0 < Real.exp (2 * Real.pi) := Real.exp_pos _
    have h_exp_neg_lt : Real.exp (-2 * Real.pi) < 1 / 2 := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
      exact inv_strictAnti₀ (by norm_num : (0:ℝ) < 2) h_exp_2pi_gt_2
    linarith
  have hr_lt_one : r < 1 := by linarith
  have h_one_sub_r_pos : 0 < 1 - r := by linarith
  have h_inv_one_sub_r_le : (1 - r)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1 / 2)⁻¹ from by norm_num]
    exact inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- Setup the HasSum on ℤ.
  have h_hasSum_int := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  -- Special term values.
  have h_term_zero : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term; simp
  have h_term_one : jacobiTheta₂_term 1 (τ / 2) τ = Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term
    congr 1; push_cast; ring
  have h_term_neg_one : jacobiTheta₂_term (-1 : ℤ) (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term
    have h_arg : (2 : ℂ) * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * (τ / 2) +
        Real.pi * Complex.I * ((-1 : ℤ) : ℂ)^2 * τ = 0 := by push_cast; ring
    rw [h_arg, Complex.exp_zero]
  -- ‖exp(2πi τ)‖ = r.
  have h_norm_exp_eq : ‖Complex.exp (2 * Real.pi * Complex.I * τ)‖ = r := by
    rw [Complex.norm_exp, hr_def]
    congr 1
    have h_eq : (2 * Real.pi * Complex.I * τ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  -- Apply HasSum.nat_add_neg.
  have h_pair_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (n : ℤ) (τ/2) τ + jacobiTheta₂_term (-(n : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ + 1) := by
    have := h_hasSum_int.nat_add_neg
    rw [h_term_zero] at this
    exact this
  -- Sum of first two terms (n = 0, 1) equals 3 + exp(2πi τ).
  have h_sum_two :
      ∑ i ∈ Finset.range 2, (jacobiTheta₂_term ((i : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-((i : ℕ) : ℤ)) (τ/2) τ) =
      3 + Complex.exp (2 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [Nat.cast_zero, neg_zero, Nat.cast_one]
    rw [h_term_zero, h_term_one, h_term_neg_one]
    ring
  -- Shift by 2: HasSum of the tail starting at n = 2.
  -- We'll use the version (h_pair_hasSum.sum_nat_of_sum_int)-style by manipulating directly.
  -- Use: h_pair_hasSum has total S; subtracting the first 2 terms gives the tail.
  have h_pair_tsum : ∑' n : ℕ, (jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) =
      jacobiTheta₂ (τ/2) τ + 1 := h_pair_hasSum.tsum_eq
  have h_pair_summable : Summable (fun n : ℕ => jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) := h_pair_hasSum.summable
  have h_tail_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ - 2 - Complex.exp (2 * Real.pi * Complex.I * τ)) := by
    have h_shift_summable : Summable (fun n : ℕ =>
        jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ) := by
      have := (summable_nat_add_iff (k := 2)).mpr h_pair_summable
      exact this
    rw [Summable.hasSum_iff h_shift_summable]
    have h_eq := (Summable.sum_add_tsum_nat_add 2 h_pair_summable).symm
    rw [h_pair_tsum] at h_eq
    rw [h_sum_two] at h_eq
    linear_combination -h_eq
  -- Rearrange.
  have h_eq : jacobiTheta₂ (τ/2) τ - 2 =
      Complex.exp (2 * Real.pi * Complex.I * τ) +
      ∑' n : ℕ, (jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ) := by
    rw [h_tail_hasSum.tsum_eq]; ring
  rw [h_eq]
  -- Triangle inequality.
  refine (norm_add_le _ _).trans ?_
  rw [h_norm_exp_eq]
  -- Termwise bound: ‖term(n+2) + term(-(n+2))‖ ≤ 2·r^(n+1).
  have h_termwise : ∀ n : ℕ,
      ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖ ≤ 2 * r^(n + 1) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    -- Compute r^(n+1) = exp(-2π·(n+1)·τ.im).
    have hr_pow : r^(n + 1) = Real.exp (((n : ℝ) + 1) * (-2 * Real.pi * τ.im)) := by
      rw [hr_def, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    have hN_pos : ((((n + 2) : ℕ) : ℤ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hN_neg : (((-(((n + 2) : ℕ) : ℤ)) : ℤ) : ℝ) = -((n : ℝ) + 2) := by push_cast; ring
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg Real.pi_pos.le hτim_pos.le
    have h_pos_norm : ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ‖ ≤ r^(n + 1) := by
      rw [jacobiTheta₂_term_half_norm, hN_pos, hr_pow]
      apply Real.exp_le_exp.mpr
      have h_ineq : 2 * ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) * ((n : ℝ) + 3) := by nlinarith
      have h_mul : Real.pi * τ.im * (2 * ((n : ℝ) + 1)) ≤
          Real.pi * τ.im * (((n : ℝ) + 2) * ((n : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    have h_neg_norm : ‖jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖ ≤ r^(n + 1) := by
      rw [jacobiTheta₂_term_half_norm]
      have hN' : ((-(((n + 2) : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 2) := by push_cast; ring
      rw [hN', hr_pow]
      apply Real.exp_le_exp.mpr
      have h_ineq : 2 * ((n : ℝ) + 1) ≤ (-((n : ℝ) + 2)) * (-((n : ℝ) + 2) + 1) := by nlinarith
      have h_mul : Real.pi * τ.im * (2 * ((n : ℝ) + 1)) ≤
          Real.pi * τ.im * ((-((n : ℝ) + 2)) * (-((n : ℝ) + 2) + 1)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    linarith
  -- Summability of the bound: ∑' (2·r^(n+1)) is summable (geometric).
  have h_bound_summable : Summable (fun n : ℕ => 2 * r^(n + 1)) := by
    have : Summable (fun n : ℕ => r^n) := summable_geometric_of_lt_one hr_nn hr_lt_one
    have h_shifted : Summable (fun n : ℕ => r * r^n) :=
      (summable_geometric_of_lt_one hr_nn hr_lt_one).mul_left r
    have h_eq : (fun n : ℕ => 2 * r^(n + 1)) = (fun n : ℕ => 2 * (r * r^n)) := by
      ext n; rw [pow_succ']
    rw [h_eq]
    exact h_shifted.mul_left 2
  -- Sum of bound: 2 · r · (1-r)⁻¹.
  have h_bound_tsum : ∑' n : ℕ, 2 * r^(n + 1) = 2 * r * (1 - r)⁻¹ := by
    have h_geo := tsum_geometric_of_lt_one hr_nn hr_lt_one
    -- ∑'_n r^(n+1) = r · ∑'_n r^n = r · (1-r)⁻¹.
    have h_shift : ∑' n : ℕ, r^(n + 1) = r * (1 - r)⁻¹ := by
      have h_eq : (fun n : ℕ => r^(n + 1)) = (fun n : ℕ => r * r^n) := by
        ext n; rw [pow_succ']
      rw [h_eq, tsum_mul_left, h_geo]
    rw [show (fun n : ℕ => 2 * r^(n + 1)) = fun n : ℕ => 2 * r^(n+1) from rfl]
    rw [tsum_mul_left, h_shift, ← mul_assoc]
  -- Norm-summability of the original sequence.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_termwise
  -- Triangle inequality on the tsum.
  have h_norm_tsum_le := norm_tsum_le_tsum_norm h_norm_summable
  -- Compare: tsum norm ≤ tsum bound.
  have h_tsum_le : (∑' n : ℕ,
      ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖) ≤
      2 * r * (1 - r)⁻¹ := by
    rw [← h_bound_tsum]
    exact h_norm_summable.tsum_le_tsum h_termwise h_bound_summable
  -- Final calculation.
  have h_step : ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ)‖ ≤ 2 * r * (1 - r)⁻¹ :=
    h_norm_tsum_le.trans h_tsum_le
  -- r + 2r·(1-r)⁻¹ ≤ r + 2r·2 = 5r ≤ 8r.
  have h_final : r + 2 * r * (1 - r)⁻¹ ≤ 8 * r := by
    have h1 : 2 * r * (1 - r)⁻¹ ≤ 2 * r * 2 := by
      apply mul_le_mul_of_nonneg_left h_inv_one_sub_r_le
      positivity
    linarith
  linarith

/-- **Leading-term bound for `θ₂`.** For `τ.im ≥ 1`,
`‖θ₂(τ) - 2 · exp(πi τ/4)‖ ≤ 8·exp(-9π τ.im/4)`. Follows from
`jacobiTheta₂_half_sub_two_norm_le_of_im_ge_one` and
`θ₂(τ) = exp(πi τ/4) · jacobiTheta₂(τ/2, τ)`, factoring out
`exp(πi τ/4)` with `|exp(πi τ/4)| = exp(-π τ.im/4)`. -/
theorem theta2_norm_sub_lead_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ - 2 * Complex.exp (Real.pi * Complex.I * τ / 4)‖ ≤
      8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := by
  unfold theta2
  -- theta2 τ - 2 exp(πi τ/4) = exp(πi τ/4) · (jacobiTheta₂(τ/2, τ) - 2).
  have h_factor :
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ -
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) =
      Complex.exp (Real.pi * Complex.I * τ / 4) * (jacobiTheta₂ (τ / 2) τ - 2) := by
    ring
  rw [h_factor, norm_mul]
  -- |exp(πi τ/4)| = exp(-π τ.im/4).
  have h_norm_exp :
      ‖Complex.exp (Real.pi * Complex.I * τ / 4)‖ = Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
        ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp]
  -- Tail bound on jacobiTheta₂(τ/2, τ) - 2.
  have h_tail := jacobiTheta₂_half_sub_two_norm_le_of_im_ge_one hτ
  have h_exp_nn : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := (Real.exp_pos _).le
  -- Combine: exp(-π τ.im/4) * 8 exp(-2π τ.im) = 8 exp(-9π τ.im/4).
  have h_combine :
      Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-2 * Real.pi * τ.im)) =
      8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := by
    rw [show (8 * Real.exp (-2 * Real.pi * τ.im) : ℝ) =
        8 * Real.exp (-2 * Real.pi * τ.im) from rfl]
    rw [show Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-2 * Real.pi * τ.im)) =
        8 * (Real.exp (-(Real.pi * τ.im / 4)) * Real.exp (-2 * Real.pi * τ.im)) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 8 * Real.exp x) (by ring)
  calc Real.exp (-(Real.pi * τ.im / 4)) * ‖jacobiTheta₂ (τ / 2) τ - 2‖
      ≤ Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-2 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_left h_tail h_exp_nn
    _ = 8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := h_combine

/-- **Leading-term bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ) - 16 · exp(πi τ)‖ ≤ 4096 · exp(-2π τ.im)`.

Combines `theta2_norm_sub_lead_le_of_im_ge_one` (`|θ₂ - 2 e^(πi τ/4)|`
bound) with `theta3_sub_one_norm_le_exp_of_im_ge_one` and
`theta3_norm_ge_half_of_im_ge_one`, then expands `(a/b)⁴` algebraically.

**Proof outline:**
* Set `r₂ := (θ₂ - 2 e^(πi τ/4))/(2 e^(πi τ/4))` so `|r₂| ≤ 4·exp(-2π τ.im)`.
* Set `r₃ := θ₃ - 1` so `|r₃| ≤ 4·exp(-π τ.im)`.
* `λ = (θ₂)⁴/(θ₃)⁴ = (2 e^(πi τ/4))⁴ · (1+r₂)⁴/(1+r₃)⁴ = 16 e^(πi τ) · ((1+r₂)/(1+r₃))⁴`.
* Let `s := (1+r₂)/(1+r₃) - 1 = (r₂ - r₃)/(1+r₃)`. For `τ.im ≥ 1`,
  `|1+r₃| ≥ 1/2` (from `theta3_norm_ge_half`), so `|s| ≤ 2(|r₂|+|r₃|) ≤ 16·exp(-π τ.im)`.
* `((1+r₂)/(1+r₃))⁴ - 1 = (1+s)⁴ - 1 = s(4 + 6s + 4s² + s³)`, with
  `|4 + 6s + 4s² + s³| ≤ 4 + 6|s| + 4|s|² + |s|³ ≤ 16` for `|s| ≤ 1`.
* So `|((1+r₂)/(1+r₃))⁴ - 1| ≤ 16|s| ≤ 256·exp(-π τ.im)`.
* Hence `‖λ - 16 e^(πi τ)‖ = 16·|e^(πi τ)|·|((1+r₂)/(1+r₃))⁴ - 1|`
  `≤ 16·exp(-π τ.im)·256·exp(-π τ.im) = 4096·exp(-2π τ.im)`.

This bound is loose; the actual leading correction is `-128 q²`. The
constant `4096 = 2^12` is chosen as a safety margin around the actual
coefficient. The bound suffices for the witness at `τ = (1+4i)/2`
(`τ.im = 2`): `Im(16 e^(πi τ)) = 16·exp(-2π) ≈ 0.030`,
`error ≤ 4096·exp(-4π) ≈ 0.014`, so `Im(λ) ≥ 0.016 > 0`. -/
theorem modularLambdaH_norm_sub_lead_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)‖ ≤
      4096 * Real.exp (-2 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- A := 2·exp(πi τ/4); A^4 = 16·exp(πi τ).
  set A : ℂ := 2 * Complex.exp (Real.pi * Complex.I * τ / 4) with hA_def
  have hA_pow : A^4 = 16 * Complex.exp (Real.pi * Complex.I * τ) := by
    rw [hA_def, mul_pow]
    rw [show (Complex.exp (Real.pi * Complex.I * τ / 4))^4 =
        Complex.exp (4 * (Real.pi * Complex.I * τ / 4)) from by
      rw [← Complex.exp_nat_mul]; norm_cast]
    rw [show (4 : ℂ) * (Real.pi * Complex.I * τ / 4) = Real.pi * Complex.I * τ from by ring]
    norm_num
  rw [← hA_pow]
  -- ‖A‖ = 2·exp(-π τ.im/4).
  have hA_norm : ‖A‖ = 2 * Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [hA_def, norm_mul, Complex.norm_exp]
    have h_re : (Real.pi * Complex.I * τ / 4 : ℂ).re = -(Real.pi * τ.im / 4) := by
      have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
          ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
      rw [h_eq, Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [h_re]
    simp
  have hA_norm_pos : 0 < ‖A‖ := by rw [hA_norm]; positivity
  have hA_ne : A ≠ 0 := norm_ne_zero_iff.mp hA_norm_pos.ne'
  -- ‖A‖^4 = 16·exp(-π τ.im).
  have hA_pow_norm : ‖A^4‖ = 16 * Real.exp (-(Real.pi * τ.im)) := by
    rw [norm_pow, hA_norm, mul_pow]
    have h_2_pow : (2 : ℝ)^4 = 16 := by norm_num
    have h_exp_pow : Real.exp (-(Real.pi * τ.im / 4)) ^ 4 = Real.exp (-(Real.pi * τ.im)) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [h_2_pow, h_exp_pow]
  -- r₂ := (θ₂ - A)/A; |r₂| ≤ 4·exp(-2π τ.im).
  set r₂ : ℂ := (theta2 τ - A) / A with hr2_def
  have h_th2_sub_A := theta2_norm_sub_lead_le_of_im_ge_one hτ
  have hr2_bound : ‖r₂‖ ≤ 4 * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hr2_def, norm_div, hA_norm]
    have h_denom_pos : 0 < 2 * Real.exp (-(Real.pi * τ.im / 4)) := by positivity
    rw [div_le_iff₀ h_denom_pos]
    have h_target_eq :
        4 * Real.exp (-(2 * Real.pi * τ.im)) * (2 * Real.exp (-(Real.pi * τ.im / 4))) =
        8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := by
      rw [show (4 * Real.exp (-(2 * Real.pi * τ.im)) * (2 * Real.exp (-(Real.pi * τ.im / 4))) : ℝ) =
          8 * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * τ.im / 4))) from by ring]
      rw [← Real.exp_add]
      exact congr_arg (fun x => 8 * Real.exp x) (by ring)
    rw [h_target_eq]; exact h_th2_sub_A
  -- r₃ := θ₃ - 1; |r₃| ≤ 4·exp(-π τ.im).
  set r₃ : ℂ := theta3 τ - 1 with hr3_def
  have hr3_bound : ‖r₃‖ ≤ 4 * Real.exp (-Real.pi * τ.im) :=
    theta3_sub_one_norm_le_exp_of_im_ge_one hτ
  -- θ₂ = A·(1 + r₂); θ₃ = 1 + r₃.
  have h_th2_eq : theta2 τ = A * (1 + r₂) := by
    rw [hr2_def]; field_simp; ring
  have h_th3_eq : theta3 τ = 1 + r₃ := by rw [hr3_def]; ring
  -- ‖θ₃‖ ≥ 1/2, so 1+r₃ ≠ 0 and ‖1+r₃‖ ≥ 1/2.
  have h_th3_norm_ge := theta3_norm_ge_half_of_im_ge_one hτ
  have h_1pr3_norm_ge : (1/2 : ℝ) ≤ ‖(1 + r₃ : ℂ)‖ := by rw [← h_th3_eq]; exact h_th3_norm_ge
  have h_1pr3_pos : 0 < ‖(1 + r₃ : ℂ)‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_1pr3_norm_ge
  have h_1pr3_ne : (1 + r₃ : ℂ) ≠ 0 := norm_ne_zero_iff.mp h_1pr3_pos.ne'
  -- λ = A^4 · ((1+r₂)/(1+r₃))^4.
  have h_lambda_eq : modularLambdaH τ = A^4 * ((1 + r₂)/(1 + r₃))^4 := by
    unfold modularLambdaH
    rw [h_th2_eq, h_th3_eq, mul_pow, div_pow]
    ring
  rw [h_lambda_eq]
  -- Factor out A^4.
  rw [show (A^4 * ((1 + r₂)/(1 + r₃))^4 - A^4 : ℂ) =
      A^4 * (((1 + r₂)/(1 + r₃))^4 - 1) from by ring]
  rw [norm_mul, hA_pow_norm]
  -- Let v := (1+r₂)/(1+r₃) - 1.
  set v : ℂ := (1 + r₂)/(1 + r₃) - 1 with hv_def
  have hv_add : (1 + r₂)/(1 + r₃) = 1 + v := by rw [hv_def]; ring
  -- v = (r₂ - r₃)/(1 + r₃).
  have hv_alt : v = (r₂ - r₃)/(1 + r₃) := by
    rw [hv_def]; field_simp; ring
  -- |v| ≤ 16·exp(-π τ.im).
  have hv_bound : ‖v‖ ≤ 16 * Real.exp (-(Real.pi * τ.im)) := by
    rw [hv_alt, norm_div]
    -- ‖r₂ - r₃‖ ≤ ‖r₂‖ + ‖r₃‖ ≤ 4·exp(-2π τ.im) + 4·exp(-π τ.im) ≤ 8·exp(-π τ.im).
    have h_r3_pos : (Real.exp (-Real.pi * τ.im) : ℝ) = Real.exp (-(Real.pi * τ.im)) := by
      congr 1; ring
    have h_r3_bound' : ‖r₃‖ ≤ 4 * Real.exp (-(Real.pi * τ.im)) := by
      rw [← h_r3_pos]; exact hr3_bound
    have h_r2_relax : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(Real.pi * τ.im)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have h_r2_bound' : ‖r₂‖ ≤ 4 * Real.exp (-(Real.pi * τ.im)) := by
      refine hr2_bound.trans ?_
      have : (0 : ℝ) ≤ 4 := by norm_num
      nlinarith
    have h_num_le : ‖r₂ - r₃‖ ≤ 8 * Real.exp (-(Real.pi * τ.im)) := by
      calc ‖r₂ - r₃‖ ≤ ‖r₂‖ + ‖r₃‖ := norm_sub_le _ _
        _ ≤ 4 * Real.exp (-(Real.pi * τ.im)) + 4 * Real.exp (-(Real.pi * τ.im)) := by
            linarith
        _ = 8 * Real.exp (-(Real.pi * τ.im)) := by ring
    -- ‖r₂ - r₃‖/‖1+r₃‖ ≤ 8 exp(-π τ.im)/(1/2) = 16 exp(-π τ.im).
    rw [div_le_iff₀ h_1pr3_pos]
    have h_calc : 16 * Real.exp (-(Real.pi * τ.im)) * ‖(1 + r₃ : ℂ)‖ ≥
        16 * Real.exp (-(Real.pi * τ.im)) * (1/2) := by
      apply mul_le_mul_of_nonneg_left h_1pr3_norm_ge
      positivity
    linarith
  -- |v| ≤ 1 (since 16·exp(-π) < 1 because exp(π) > 16).
  have hv_le_one : ‖v‖ ≤ 1 := by
    refine hv_bound.trans ?_
    -- 16 · exp(-π τ.im) ≤ 16 · exp(-π) ≤ 1.
    have h_exp_le : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-Real.pi) := by
      apply Real.exp_le_exp.mpr; nlinarith
    -- exp(π) > exp(3) > 16: exp(1) > 2.71828, exp(3) > 2.71828^3 > 20 > 16.
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
      have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
      rw [h_eq]
      nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
    have h_pi_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
      h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr h_pi_gt_3.le)
    have h_16_exp_neg_pi : 16 * Real.exp (-Real.pi) ≤ 1 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    have h_mul := mul_le_mul_of_nonneg_left h_exp_le (by norm_num : (0:ℝ) ≤ 16)
    linarith [h_exp_le, h_16_exp_neg_pi, h_mul]
  -- (1+v)^4 - 1 = v · (4 + 6v + 4v² + v³).
  rw [hv_add]
  rw [show ((1 + v)^4 - 1 : ℂ) = v * (4 + 6*v + 4*v^2 + v^3) from by ring]
  rw [norm_mul]
  -- ‖4 + 6v + 4v² + v³‖ ≤ 4 + 6 + 4 + 1 = 15.
  have h_poly_bound : ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖ ≤ 15 := by
    have h_v_sq : ‖v‖^2 ≤ 1 := by
      have := pow_le_pow_left₀ (norm_nonneg v) hv_le_one 2
      simpa using this
    have h_v_cube : ‖v‖^3 ≤ 1 := by
      have := pow_le_pow_left₀ (norm_nonneg v) hv_le_one 3
      simpa using this
    have h_4_eq : ‖((4 : ℂ))‖ = 4 := by norm_num
    have h_6v_eq : ‖((6 * v : ℂ))‖ = 6 * ‖v‖ := by
      rw [show ((6 * v : ℂ)) = (((6 : ℝ) : ℂ)) * v from by push_cast; ring]
      rw [norm_mul, Complex.norm_real]
      simp
    have h_4v2_eq : ‖((4 * v^2 : ℂ))‖ = 4 * ‖v‖^2 := by
      rw [show ((4 * v^2 : ℂ)) = (((4 : ℝ) : ℂ)) * v^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, norm_pow]
      simp
    have h_v3_eq : ‖(v^3)‖ = ‖v‖^3 := norm_pow v 3
    have h_chain :
        ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖ ≤
          ‖((4 : ℂ))‖ + ‖((6*v : ℂ))‖ + ‖((4*v^2 : ℂ))‖ + ‖(v^3 : ℂ)‖ := by
      have h1 := norm_add_le ((4 + 6*v + 4*v^2 : ℂ)) ((v^3 : ℂ))
      have h2 := norm_add_le ((4 + 6*v : ℂ)) ((4*v^2 : ℂ))
      have h3 := norm_add_le ((4 : ℂ)) ((6*v : ℂ))
      linarith
    rw [h_4_eq, h_6v_eq, h_4v2_eq, h_v3_eq] at h_chain
    linarith [hv_le_one, h_v_sq, h_v_cube]
  -- ‖v‖ · ‖4 + 6v + 4v² + v³‖ ≤ 16·exp(-π τ.im) · 15 = 240·exp(-π τ.im).
  -- And 16·exp(-π τ.im) · 240·exp(-π τ.im) = 3840·exp(-2π τ.im) ≤ 4096·exp(-2π τ.im).
  have h_step1 : ‖v‖ * ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖ ≤
      (16 * Real.exp (-(Real.pi * τ.im))) * 15 :=
    mul_le_mul hv_bound h_poly_bound (norm_nonneg _) (by positivity)
  have h_step2 : 16 * Real.exp (-(Real.pi * τ.im)) *
      ((16 * Real.exp (-(Real.pi * τ.im))) * 15) =
      3840 * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show (16 * Real.exp (-(Real.pi * τ.im)) *
        (16 * Real.exp (-(Real.pi * τ.im)) * 15) : ℝ) =
        3840 * (Real.exp (-(Real.pi * τ.im)) * Real.exp (-(Real.pi * τ.im))) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 3840 * Real.exp x) (by ring)
  have h_exp_eq : Real.exp (-(2 * Real.pi * τ.im)) = Real.exp (-2 * Real.pi * τ.im) :=
    congr_arg Real.exp (by ring)
  have h_target_le : 3840 * Real.exp (-(2 * Real.pi * τ.im)) ≤
      4096 * Real.exp (-2 * Real.pi * τ.im) := by
    rw [h_exp_eq]
    have h_exp_nn : 0 ≤ Real.exp (-2 * Real.pi * τ.im) := (Real.exp_pos _).le
    nlinarith
  calc 16 * Real.exp (-(Real.pi * τ.im)) * (‖v‖ * ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖)
      ≤ 16 * Real.exp (-(Real.pi * τ.im)) *
        ((16 * Real.exp (-(Real.pi * τ.im))) * 15) :=
        mul_le_mul_of_nonneg_left h_step1 (by positivity)
    _ = 3840 * Real.exp (-(2 * Real.pi * τ.im)) := h_step2
    _ ≤ 4096 * Real.exp (-2 * Real.pi * τ.im) := h_target_le

/-! ## Two-term q-expansion infrastructure

The leading-term bounds `θ₃ − 1 ≈ 2q`, `θ₂ ≈ 2 q^{1/4}`,
`λ ≈ 16q` (each with `O(q²)` error) are tight to leading order, but
their `O(q²)` error coefficients carry signs that matter for the
cusp-1 analysis of `λ` in `F^o`. The two-term expansions
`θ₃ = 1 + 2q + O(q⁴)`, `θ₂ = 2 q^{1/4}(1 + q² + O(q⁶))`,
`λ = 16q − 128q² + O(q³)` resolve the sign control needed for the
Phragmén–Lindelöf closure of Step A. -/

/-- **Two-term q-expansion of `θ₃`.** For `τ.im ≥ 1`,
`‖θ₃(τ) − 1 − 2·exp(πi τ)‖ ≤ 4·exp(−4π·τ.im)`. The first two
non-zero terms of the q-series `θ₃ = 1 + 2q + 2q⁴ + 2q⁹ + …` are
subtracted; the remaining tail starts at `2q⁴` and is bounded
geometrically. -/
theorem theta3_sub_one_minus_2q_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ)‖ ≤
      4 * Real.exp (-4 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- Set r := exp(-π τ.im). For τ.im ≥ 1, r ≤ exp(-π) < 1/16.
  set r : ℝ := Real.exp (-Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_le_exp_neg_pi : r ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  -- exp(-π) < 1/16 via exp(π) > 16.
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]; nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_pi_gt_16
  have hr_lt : r < 1/16 := lt_of_le_of_lt hr_le_exp_neg_pi h_exp_neg_pi_lt
  have hr_lt_one : r < 1 := by linarith
  -- r⁴ < 1/2.
  have hr4_lt_half : r^4 < 1/2 := by
    have h1 : r^4 < (1/16)^4 :=
      pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : (1/16 : ℝ)^4 < 1/2 := by norm_num
    linarith
  have hr4_pos : 0 < r^4 := by positivity
  have h_1_sub_r4_pos : 0 < 1 - r^4 := by linarith
  have h_inv_le_2 : (1 - r^4)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    apply inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- hasSum_nat_jacobiTheta gives HasSum over ℕ.
  have h_hasSum := hasSum_nat_jacobiTheta hτim_pos
  have h_summable := h_hasSum.summable
  -- Sum of first term = q.
  have h_sum_one : ∑ i ∈ Finset.range 1,
      Complex.exp (Real.pi * Complex.I * ((i : ℂ) + 1)^2 * τ) =
      Complex.exp (Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_one]
    congr 1; push_cast; ring
  -- Split: HasSum (fun n => f(n+1)) ((jacobiTheta - 1)/2 - q).
  have h_shifted : Summable (fun n : ℕ =>
      Complex.exp (Real.pi * Complex.I * ((n + 1 : ℕ) + 1 : ℂ)^2 * τ)) :=
    (summable_nat_add_iff (k := 1)).mpr h_summable
  have h_split := h_summable.sum_add_tsum_nat_add 1
  rw [h_sum_one, h_hasSum.tsum_eq] at h_split
  -- h_split : q + ∑'_{n} f(n+1) = (jacobiTheta - 1)/2.
  -- Hence 2(∑' f(n+1)) = jacobiTheta - 1 - 2q.
  unfold theta3
  have h_id : jacobiTheta τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) =
      2 * ∑' n : ℕ, Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ) := by
    linear_combination -2 * h_split
  rw [h_id, norm_mul, Complex.norm_two]
  -- ‖2 · tsum‖ = 2 · ‖tsum‖. We bound 2 · ‖tsum‖ ≤ 2 · 2 r⁴ = 4 r⁴.
  -- Termwise: ‖f(n+1)‖ = exp(-π (n+2)² τ.im) ≤ r⁴ · (r⁴)^n.
  -- Tail bound: ∑ ‖f(n+1)‖ ≤ r⁴/(1 - r⁴) ≤ 2 r⁴.
  have hr4_lt_one : r^4 < 1 := by linarith
  have h_term_norm : ∀ n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^4 * (r^4)^n := by
    intro n
    rw [Complex.norm_exp]
    -- Re argument: Re(π i (n+2)² τ) = -π (n+2)² τ.im.
    have h_re : (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ).re =
        -(Real.pi * ((n : ℝ) + 2)^2 * τ.im) := by
      have h_factor : Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ =
          ((Real.pi * ((n : ℝ) + 2)^2 : ℝ) : ℂ) * (Complex.I * τ) := by
        push_cast; ring
      rw [h_factor, Complex.re_ofReal_mul]
      rw [show (Complex.I * τ).re = -τ.im from by
        rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring]
      ring
    rw [h_re]
    -- Goal: exp(-π (n+2)² τ.im) ≤ r⁴ · (r⁴)^n.
    have h_bound_eq : r^4 * (r^4)^n = Real.exp ((1 + (n : ℝ)) * (-4 * Real.pi * τ.im)) := by
      have h_r4_eq : r^4 = Real.exp (-4 * Real.pi * τ.im) := by
        rw [hr_def, ← Real.exp_nat_mul]; congr 1; ring
      rw [h_r4_eq, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    rw [h_bound_eq]
    apply Real.exp_le_exp.mpr
    -- Goal: -(π (n+2)² τ.im) ≤ (1 + n) · (-4π τ.im).
    have h_ineq : ((n : ℝ) + 2)^2 ≥ 4 * ((n : ℝ) + 1) := by nlinarith [sq_nonneg ((n : ℝ))]
    have h_pi_tau_pos : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    nlinarith
  -- Summability of bound.
  have h_bound_summable : Summable (fun n : ℕ => r^4 * (r^4)^n) :=
    (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ r^4) hr4_lt_one).mul_left _
  -- Bound the tsum of norms.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_norm
  have h_tsum_norm_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_bound : (∑' n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖) ≤
      r^4 * (1 - r^4)⁻¹ := by
    refine (h_norm_summable.tsum_le_tsum h_term_norm h_bound_summable).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr4_lt_one]
  -- Conclude.
  have h_chain : ‖∑' n : ℕ,
      Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^4 * (1 - r^4)⁻¹ := h_tsum_norm_le.trans h_tsum_bound
  have h_inv_bound : r^4 * (1 - r^4)⁻¹ ≤ 2 * r^4 := by
    have : r^4 * (1 - r^4)⁻¹ ≤ r^4 * 2 :=
      mul_le_mul_of_nonneg_left h_inv_le_2 hr4_pos.le
    linarith
  -- Now ‖2 · tsum‖ = 2 · ‖tsum‖. With ‖tsum‖ ≤ 2 r⁴, get 4 r⁴.
  -- r⁴ = exp(-4π τ.im).
  have hr4_eq : r^4 = Real.exp (-4 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]
    congr 1; ring
  calc (2 : ℝ) * ‖∑' n : ℕ,
        Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖
      ≤ 2 * (r^4 * (1 - r^4)⁻¹) := by
        apply mul_le_mul_of_nonneg_left h_chain (by norm_num)
    _ ≤ 2 * (2 * r^4) := by
        apply mul_le_mul_of_nonneg_left h_inv_bound (by norm_num)
    _ = 4 * r^4 := by ring
    _ = 4 * Real.exp (-4 * Real.pi * τ.im) := by rw [hr4_eq]

/-- **Three-term q-expansion of `θ₃`.** For `τ.im ≥ 1`,
`‖θ₃(τ) − 1 − 2·exp(πi τ) − 2·exp(4πi τ)‖ ≤ 4·exp(−9π·τ.im)`. The
first three non-zero terms of `θ₃ = 1 + 2q + 2q⁴ + 2q⁹ + …` are
subtracted; the remaining tail starts at `2q⁹`. This is the building
block (together with three-term θ₂ and the algebraic combination
yielding three-term λ) for the cusp-1 sign control in
`modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`. -/
theorem theta3_sub_one_minus_2q_minus_2q4_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) -
        2 * Complex.exp (4 * Real.pi * Complex.I * τ)‖ ≤
      4 * Real.exp (-9 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- r := exp(-π τ.im). For τ.im ≥ 1, r ≤ exp(-π) < 1/16.
  set r : ℝ := Real.exp (-Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_le_exp_neg_pi : r ≤ Real.exp (-Real.pi) := by
    rw [hr_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]; nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_pi_gt_16
  have hr_lt : r < 1/16 := lt_of_le_of_lt hr_le_exp_neg_pi h_exp_neg_pi_lt
  have hr_lt_one : r < 1 := by linarith
  -- r⁵ < 1.
  have hr5_lt_one : r^5 < 1 := by
    have h1 : r^5 < (1/16)^5 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^5 < 1 := by norm_num
    linarith
  -- r⁵ < 1/2 for the (1-r⁵)⁻¹ ≤ 2 bound.
  have hr5_lt_half : r^5 < 1/2 := by
    have h1 : r^5 < (1/16)^5 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^5 ≤ 1/2 := by norm_num
    linarith
  have h_one_sub_r5_pos : 0 < 1 - r^5 := by linarith
  have h_inv_le_2 : (1 - r^5)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    apply inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- HasSum on ℕ for jacobiTheta.
  have h_hasSum := hasSum_nat_jacobiTheta hτim_pos
  have h_summable := h_hasSum.summable
  -- Sum of first two terms: q + q⁴.
  have h_sum_two : ∑ i ∈ Finset.range 2,
      Complex.exp (Real.pi * Complex.I * ((i : ℂ) + 1)^2 * τ) =
      Complex.exp (Real.pi * Complex.I * τ) +
      Complex.exp (4 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    push_cast
    congr 1
    · congr 1; ring
    · congr 1; ring
  -- Split off n=0,1.
  have h_shifted : Summable (fun n : ℕ =>
      Complex.exp (Real.pi * Complex.I * ((n + 2 : ℕ) + 1 : ℂ)^2 * τ)) :=
    (summable_nat_add_iff (k := 2)).mpr h_summable
  have h_split := h_summable.sum_add_tsum_nat_add 2
  rw [h_sum_two, h_hasSum.tsum_eq] at h_split
  -- h_split : (q + q⁴) + ∑'_{n} f(n+2) = (jacobiTheta - 1)/2.
  -- ⟹ 2 (q + q⁴) + 2 ∑' = jacobiTheta - 1.
  -- ⟹ jacobiTheta - 1 - 2q - 2q⁴ = 2 ∑'.
  unfold theta3
  have h_id : jacobiTheta τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) -
      2 * Complex.exp (4 * Real.pi * Complex.I * τ) =
      2 * ∑' n : ℕ, Complex.exp (Real.pi * Complex.I *
        (((n + 2 : ℕ) : ℂ) + 1)^2 * τ) := by
    linear_combination -2 * h_split
  rw [h_id, norm_mul, Complex.norm_two]
  -- Termwise: ‖exp(πi (n+3)² τ)‖ ≤ exp(-π · (n+3)² · τ.im) ≤ r^9 · (r^5)^n.
  have hr5_lt_one' : r^5 < 1 := hr5_lt_one
  have h_term_norm : ∀ n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^9 * (r^5)^n := by
    intro n
    rw [Complex.norm_exp]
    -- Re argument: -π · (n+3)² · τ.im.
    have h_re : (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ).re =
        -(Real.pi * ((n : ℝ) + 3)^2 * τ.im) := by
      have h_factor : Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ =
          ((Real.pi * ((n : ℝ) + 3)^2 : ℝ) : ℂ) * (Complex.I * τ) := by
        push_cast; ring
      rw [h_factor, Complex.re_ofReal_mul]
      rw [show (Complex.I * τ).re = -τ.im from by
        rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring]
      ring
    rw [h_re]
    -- Goal: exp(-π (n+3)² τ.im) ≤ r^9 · (r^5)^n.
    -- r^9 · (r^5)^n = exp(-π τ.im · (9 + 5n)).
    have h_bound_eq : r^9 * (r^5)^n = Real.exp ((9 + 5 * (n : ℝ)) * (-Real.pi * τ.im)) := by
      have h_r9_eq : r^9 = Real.exp (9 * (-Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r5_pow_eq : (r^5)^n = Real.exp ((5 * (n : ℝ)) * (-Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r9_eq, h_r5_pow_eq, ← Real.exp_add]
      congr 1; ring
    rw [h_bound_eq]
    apply Real.exp_le_exp.mpr
    -- -(π (n+3)² τ.im) ≤ (9 + 5n)(-π τ.im) ⟺ (n+3)² ≥ 9 + 5n.
    have h_ineq : ((n : ℝ) + 3)^2 ≥ 9 + 5 * (n : ℝ) := by nlinarith [sq_nonneg ((n : ℝ))]
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    nlinarith
  -- Summability of bound.
  have h_bound_summable : Summable (fun n : ℕ => r^9 * (r^5)^n) :=
    (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ r^5) hr5_lt_one).mul_left _
  -- Norm-summability of tail.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_norm
  have h_tsum_norm_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_bound : (∑' n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖) ≤
      r^9 * (1 - r^5)⁻¹ := by
    refine (h_norm_summable.tsum_le_tsum h_term_norm h_bound_summable).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr5_lt_one]
  have h_chain : ‖∑' n : ℕ,
      Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^9 * (1 - r^5)⁻¹ := h_tsum_norm_le.trans h_tsum_bound
  -- r^9 · (1 - r^5)⁻¹ ≤ 2 r^9.
  have hr9_pos : 0 < r^9 := by positivity
  have h_inv_bound : r^9 * (1 - r^5)⁻¹ ≤ 2 * r^9 := by
    have : r^9 * (1 - r^5)⁻¹ ≤ r^9 * 2 :=
      mul_le_mul_of_nonneg_left h_inv_le_2 hr9_pos.le
    linarith
  have hr9_eq : r^9 = Real.exp (-9 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]; congr 1; ring
  calc (2 : ℝ) * ‖∑' n : ℕ,
        Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖
      ≤ 2 * (r^9 * (1 - r^5)⁻¹) := by
        apply mul_le_mul_of_nonneg_left h_chain (by norm_num)
    _ ≤ 2 * (2 * r^9) := by
        apply mul_le_mul_of_nonneg_left h_inv_bound (by norm_num)
    _ = 4 * r^9 := by ring
    _ = 4 * Real.exp (-9 * Real.pi * τ.im) := by rw [hr9_eq]

/-- **Two-term q-expansion of `jacobiTheta₂(τ/2, τ)`.** For `τ.im ≥ 1`,
`‖jacobiTheta₂(τ/2, τ) − 2 − 2·exp(2πi τ)‖ ≤ 4·exp(−6π·τ.im)`.
By the symmetric pairing `n ↔ −n−1` and
`jacobiTheta₂_term_half_norm`, the series splits as
`jacobiTheta₂(τ/2, τ) = 2 ∑_{k≥0} exp(πi·k(k+1)·τ) = 2 + 2q² + 2q⁶ + …`;
subtracting the first two terms leaves a tail starting at `2q⁶`. -/
theorem jacobiTheta₂_half_sub_two_minus_two_q2_norm_le_of_im_ge_one
    {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ)‖ ≤
      8 * Real.exp (-6 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- r := exp(-2π τ.im). Need r < 1/2.
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_half : r < 1 / 2 := by
    have h_arg : -2 * Real.pi * τ.im ≤ -2 * Real.pi := by nlinarith
    have h_le : r ≤ Real.exp (-2 * Real.pi) := Real.exp_le_exp.mpr h_arg
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_2pi_gt_1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h_exp_2pi_gt_2 : (2 : ℝ) < Real.exp (2 * Real.pi) := by
      have h_mono : Real.exp 1 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h_2pi_gt_1.le
      linarith
    have h_exp_neg_lt : Real.exp (-2 * Real.pi) < 1 / 2 := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
      exact inv_strictAnti₀ (by norm_num : (0:ℝ) < 2) h_exp_2pi_gt_2
    linarith
  have hr_lt_one : r < 1 := by linarith
  have hr2_lt_one : r^2 < 1 := by
    have : r^2 < (1/2)^2 := pow_lt_pow_left₀ hr_lt_half hr_nn (by norm_num)
    nlinarith
  have h_one_sub_r2_pos : 0 < 1 - r^2 := by linarith
  have h_inv_one_sub_r2_le : (1 - r^2)⁻¹ ≤ 2 := by
    have h_r2_le : r^2 ≤ 1/2 := by
      have : r^2 < (1/2)^2 := pow_lt_pow_left₀ hr_lt_half hr_nn (by norm_num)
      nlinarith
    rw [show (2 : ℝ) = (1 / 2)⁻¹ from by norm_num]
    exact inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- HasSum on ℤ, then nat_add_neg.
  have h_hasSum_int := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_term_zero : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term; simp
  have h_term_one : jacobiTheta₂_term 1 (τ / 2) τ = Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_one : jacobiTheta₂_term (-1 : ℤ) (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term
    have h_arg : (2 : ℂ) * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * (τ / 2) +
        Real.pi * Complex.I * ((-1 : ℤ) : ℂ)^2 * τ = 0 := by push_cast; ring
    rw [h_arg, Complex.exp_zero]
  have h_term_two : jacobiTheta₂_term 2 (τ / 2) τ =
      Complex.exp (6 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_two : jacobiTheta₂_term (-2 : ℤ) (τ / 2) τ =
      Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  -- ‖exp(2πi τ)‖ = r, ‖exp(6πi τ)‖ = r³.
  have h_norm_exp_2 : ‖Complex.exp (2 * Real.pi * Complex.I * τ)‖ = r := by
    rw [Complex.norm_exp, hr_def]
    congr 1
    have h_eq : (2 * Real.pi * Complex.I * τ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  have h_norm_exp_6 : ‖Complex.exp (6 * Real.pi * Complex.I * τ)‖ = r^3 := by
    rw [Complex.norm_exp, hr_def, ← Real.exp_nat_mul]
    congr 1
    have h_eq : (6 * Real.pi * Complex.I * τ : ℂ) =
        ((6 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  -- Apply HasSum.nat_add_neg.
  have h_pair_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (n : ℤ) (τ/2) τ + jacobiTheta₂_term (-(n : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ + 1) := by
    have := h_hasSum_int.nat_add_neg
    rw [h_term_zero] at this
    exact this
  have h_pair_summable : Summable (fun n : ℕ =>
      jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) := h_pair_hasSum.summable
  -- Sum of first 3 terms: 3 + 2 exp(2πi τ) + exp(6πi τ).
  have h_sum_three :
      ∑ i ∈ Finset.range 3, (jacobiTheta₂_term ((i : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-((i : ℕ) : ℤ)) (τ/2) τ) =
      3 + 2 * Complex.exp (2 * Real.pi * Complex.I * τ) +
      Complex.exp (6 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    simp only [Nat.cast_zero, neg_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [h_term_zero, h_term_one, h_term_neg_one, h_term_two, h_term_neg_two]
    ring
  -- Shift by 3: HasSum tail.
  have h_pair_tsum : ∑' n : ℕ, (jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) =
      jacobiTheta₂ (τ/2) τ + 1 := h_pair_hasSum.tsum_eq
  have h_tail_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ - 2 -
        2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        Complex.exp (6 * Real.pi * Complex.I * τ)) := by
    have h_shift_summable : Summable (fun n : ℕ =>
        jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ) := by
      have := (summable_nat_add_iff (k := 3)).mpr h_pair_summable
      exact this
    rw [Summable.hasSum_iff h_shift_summable]
    have h_eq := (Summable.sum_add_tsum_nat_add 3 h_pair_summable).symm
    rw [h_pair_tsum] at h_eq
    rw [h_sum_three] at h_eq
    linear_combination -h_eq
  -- Rearrange.
  have h_eq : jacobiTheta₂ (τ/2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ) =
      Complex.exp (6 * Real.pi * Complex.I * τ) +
      ∑' n : ℕ, (jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ) := by
    rw [h_tail_hasSum.tsum_eq]; ring
  rw [h_eq]
  -- Triangle inequality.
  refine (norm_add_le _ _).trans ?_
  rw [h_norm_exp_6]
  -- Termwise bound: ‖term((n+3)) + term(-(n+3))‖ ≤ 2 · r³ · (r²)^n.
  have h_termwise : ∀ n : ℕ,
      ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖ ≤ 2 * (r^3 * (r^2)^n) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    -- Compute r³ · (r²)^n = exp(-2π τ.im · (3 + 2n)).
    have h_bound_eq : r^3 * (r^2)^n = Real.exp ((3 + 2 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
      have h_r3_eq : r^3 = Real.exp (3 * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r2_pow_eq : (r^2)^n = Real.exp ((2 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r3_eq, h_r2_pow_eq, ← Real.exp_add]
      congr 1; ring
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    have hN_pos : ((((n + 3) : ℕ) : ℤ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    -- ‖term((n+3))‖ ≤ r³ · (r²)^n.
    have h_pos_norm : ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ‖ ≤ r^3 * (r^2)^n := by
      rw [jacobiTheta₂_term_half_norm, hN_pos, h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (n+3) · (n+4) · τ.im) ≤ (3 + 2n) · (-2π τ.im).
      -- ⟺ (n+3)(n+4) ≥ 2(3 + 2n) = 6 + 4n.
      have h_ineq : 6 + 4 * (n : ℝ) ≤ ((n : ℝ) + 3) * ((n : ℝ) + 4) := by nlinarith
      have h_mul : Real.pi * τ.im * (6 + 4 * (n : ℝ)) ≤
          Real.pi * τ.im * (((n : ℝ) + 3) * ((n : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    -- ‖term(-(n+3))‖ ≤ r³ · (r²)^n.
    have h_neg_norm : ‖jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖ ≤
        r^3 * (r^2)^n := by
      rw [jacobiTheta₂_term_half_norm]
      have hN' : ((-(((n + 3) : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 3) := by push_cast; ring
      rw [hN', h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (-(n+3)) · (-(n+3)+1) · τ.im) = -(π · (n+3)(n+2) · τ.im) ≤ (3 + 2n) · (-2π τ.im).
      -- ⟺ (n+3)(n+2) ≥ 6 + 4n.
      have h_ineq : 6 + 4 * (n : ℝ) ≤ (-((n : ℝ) + 3)) * (-((n : ℝ) + 3) + 1) := by nlinarith
      have h_mul : Real.pi * τ.im * (6 + 4 * (n : ℝ)) ≤
          Real.pi * τ.im * ((-((n : ℝ) + 3)) * (-((n : ℝ) + 3) + 1)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    linarith
  -- Summability of bound: ∑ 2 r³ (r²)^n.
  have hr3_pos : 0 < r^3 := by positivity
  have hr2_nn : 0 ≤ r^2 := by positivity
  have h_bound_summable : Summable (fun n : ℕ => 2 * (r^3 * (r^2)^n)) := by
    have h_geo : Summable (fun n : ℕ => (r^2)^n) :=
      summable_geometric_of_lt_one hr2_nn hr2_lt_one
    have : Summable (fun n : ℕ => r^3 * (r^2)^n) := h_geo.mul_left _
    exact this.mul_left _
  -- Tsum of bound: 2 r³ / (1 - r²).
  have h_bound_tsum : ∑' n : ℕ, 2 * (r^3 * (r^2)^n) =
      2 * r^3 * (1 - r^2)⁻¹ := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr2_nn hr2_lt_one]
    ring
  -- norm-summability of tail.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_termwise
  have h_norm_tsum_le := norm_tsum_le_tsum_norm h_norm_summable
  -- ∑ ‖term + term‖ ≤ 2 r³ / (1 - r²).
  have h_tsum_le : (∑' n : ℕ,
      ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖) ≤
      2 * r^3 * (1 - r^2)⁻¹ := by
    rw [← h_bound_tsum]
    exact h_norm_summable.tsum_le_tsum h_termwise h_bound_summable
  have h_step : ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ)‖ ≤ 2 * r^3 * (1 - r^2)⁻¹ :=
    h_norm_tsum_le.trans h_tsum_le
  -- Final: r³ + 2 r³ · (1 - r²)⁻¹ ≤ r³ + 4 r³ = 5 r³ ≤ 8 r³.
  have h_final : r^3 + 2 * r^3 * (1 - r^2)⁻¹ ≤ 8 * r^3 := by
    have h1 : 2 * r^3 * (1 - r^2)⁻¹ ≤ 2 * r^3 * 2 := by
      apply mul_le_mul_of_nonneg_left h_inv_one_sub_r2_le
      positivity
    linarith
  -- r³ = exp(-6π τ.im).
  have hr3_eq : r^3 = Real.exp (-6 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  calc r^3 + ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ)‖
      ≤ r^3 + 2 * r^3 * (1 - r^2)⁻¹ := by linarith [h_step]
    _ ≤ 8 * r^3 := h_final
    _ = 8 * Real.exp (-6 * Real.pi * τ.im) := by rw [hr3_eq]

/-- **Three-term q-expansion of `jacobiTheta₂(τ/2, τ)`.** For `τ.im ≥ 1`,
`‖jacobiTheta₂(τ/2, τ) − 2 − 2·exp(2πi τ) − 2·exp(6πi τ)‖ ≤ 8·exp(−12π·τ.im)`.
Subtracts three pairs `(k = 0, 1, 2)` from
`jacobiTheta₂(τ/2, τ) = 2 ∑_{k≥0} exp(πi·k(k+1)·τ)`; the tail starts
at `2 exp(12πi τ)` from `k = 3`. -/
theorem jacobiTheta₂_half_sub_three_term_norm_le_of_im_ge_one
    {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (6 * Real.pi * Complex.I * τ)‖ ≤
      8 * Real.exp (-12 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- r := exp(-2π τ.im).
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  -- r < 1/256 (since rq < 1/16 implies rq² < 1/256, and r = rq²).
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_2pi_gt_1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h_exp_2pi_gt_2 : (2 : ℝ) < Real.exp (2 * Real.pi) := by
    have h_mono : Real.exp 1 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h_2pi_gt_1.le
    linarith
  have hr_lt : r < 1 / 2 := by
    have h_arg : -2 * Real.pi * τ.im ≤ -2 * Real.pi := by nlinarith
    have h_le : r ≤ Real.exp (-2 * Real.pi) := Real.exp_le_exp.mpr h_arg
    have h_exp_neg_lt : Real.exp (-2 * Real.pi) < 1/2 := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
      rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
      exact inv_strictAnti₀ (by norm_num : (0:ℝ) < 2) h_exp_2pi_gt_2
    linarith
  have hr_lt_one : r < 1 := by linarith
  have hr4_lt_one : r^4 < 1 := by
    have : r^4 < (1/2)^4 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    nlinarith
  -- r⁴ < 1/16.
  have hr4_lt_half : r^4 < 1/2 := by
    have h1 : r^4 < (1/2)^4 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/2 : ℝ))^4 ≤ 1/2 := by norm_num
    linarith
  have h_one_sub_r4_pos : 0 < 1 - r^4 := by linarith
  have h_inv_one_sub_r4_le : (1 - r^4)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    exact inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- HasSum setup.
  have h_hasSum_int := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_term_zero : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term; simp
  have h_term_one : jacobiTheta₂_term 1 (τ / 2) τ = Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_one : jacobiTheta₂_term (-1 : ℤ) (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term
    have h_arg : (2 : ℂ) * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * (τ / 2) +
        Real.pi * Complex.I * ((-1 : ℤ) : ℂ)^2 * τ = 0 := by push_cast; ring
    rw [h_arg, Complex.exp_zero]
  have h_term_two : jacobiTheta₂_term 2 (τ / 2) τ =
      Complex.exp (6 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_two : jacobiTheta₂_term (-2 : ℤ) (τ / 2) τ =
      Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_three : jacobiTheta₂_term 3 (τ / 2) τ =
      Complex.exp (12 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_three : jacobiTheta₂_term (-3 : ℤ) (τ / 2) τ =
      Complex.exp (6 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  -- Pair HasSum.
  have h_pair_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (n : ℤ) (τ/2) τ + jacobiTheta₂_term (-(n : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ + 1) := by
    have := h_hasSum_int.nat_add_neg
    rw [h_term_zero] at this
    exact this
  have h_pair_summable : Summable (fun n : ℕ =>
      jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) := h_pair_hasSum.summable
  -- Sum of first 4 nats (n=0,1,2,3):
  -- 2 + (Q² + 1) + (Q^6 + Q²) + (Q^12 + Q^6) = 3 + 2Q² + 2Q^6 + Q^12.
  have h_sum_four :
      ∑ i ∈ Finset.range 4, (jacobiTheta₂_term ((i : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-((i : ℕ) : ℤ)) (τ/2) τ) =
      3 + 2 * Complex.exp (2 * Real.pi * Complex.I * τ) +
      2 * Complex.exp (6 * Real.pi * Complex.I * τ) +
      Complex.exp (12 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [Nat.cast_zero, neg_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [h_term_zero, h_term_one, h_term_neg_one, h_term_two, h_term_neg_two,
        h_term_three, h_term_neg_three]
    ring
  have h_pair_tsum : ∑' n : ℕ, (jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) =
      jacobiTheta₂ (τ/2) τ + 1 := h_pair_hasSum.tsum_eq
  -- HasSum tail starting at n=4.
  have h_tail_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ - 2 -
        2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
        Complex.exp (12 * Real.pi * Complex.I * τ)) := by
    have h_shift_summable : Summable (fun n : ℕ =>
        jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ) := by
      have := (summable_nat_add_iff (k := 4)).mpr h_pair_summable
      exact this
    rw [Summable.hasSum_iff h_shift_summable]
    have h_eq := (Summable.sum_add_tsum_nat_add 4 h_pair_summable).symm
    rw [h_pair_tsum] at h_eq
    rw [h_sum_four] at h_eq
    linear_combination -h_eq
  -- Express target as exp(12πi τ) + tail.
  have h_eq : jacobiTheta₂ (τ/2) τ - 2 -
      2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
      2 * Complex.exp (6 * Real.pi * Complex.I * τ) =
      Complex.exp (12 * Real.pi * Complex.I * τ) +
      ∑' n : ℕ, (jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ) := by
    rw [h_tail_hasSum.tsum_eq]; ring
  rw [h_eq]
  refine (norm_add_le _ _).trans ?_
  -- ‖exp(12πi τ)‖ = r⁶.
  have h_norm_exp_12 : ‖Complex.exp (12 * Real.pi * Complex.I * τ)‖ = r^6 := by
    rw [Complex.norm_exp, hr_def, ← Real.exp_nat_mul]
    congr 1
    have h_eq : (12 * Real.pi * Complex.I * τ : ℂ) =
        ((12 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp_12]
  -- Termwise bound: for n : ℕ, ‖term(n+4) + term(-(n+4))‖ ≤ 2 r⁶ (r⁴)^n.
  -- For k = n+4 ≥ 4: k(k+1) ≥ 20, k(k-1) ≥ 12. With r = exp(-2π τ.im),
  -- ‖term(n)‖ = r^{n(n+1)/2}.
  -- So ‖term(n+4)‖ ≤ r^{(n+4)(n+5)/2}, ‖term(-(n+4))‖ ≤ r^{(n+4)(n+3)/2}.
  -- (n+4)(n+3)/2 ≥ 6 + 4n: verify (n+4)(n+3)/2 - 6 - 4n = (n²-n)/2 ≥ 0.
  -- (n+4)(n+5)/2 ≥ (n+4)(n+3)/2 ≥ 6 + 4n.
  have h_termwise : ∀ n : ℕ,
      ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖ ≤ 2 * (r^6 * (r^4)^n) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    have h_bound_eq : r^6 * (r^4)^n = Real.exp ((6 + 4 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
      have h_r6_eq : r^6 = Real.exp (6 * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r4_pow_eq : (r^4)^n = Real.exp ((4 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r6_eq, h_r4_pow_eq, ← Real.exp_add]
      congr 1; ring
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    have hN_pos : ((((n + 4) : ℕ) : ℤ) : ℝ) = (n : ℝ) + 4 := by push_cast; ring
    have h_pos_norm : ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ‖ ≤ r^6 * (r^4)^n := by
      rw [jacobiTheta₂_term_half_norm, hN_pos, h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (n+4) · (n+5) · τ.im) ≤ (6 + 4n)·(-2π τ.im) ⟺ (n+4)(n+5) ≥ 2·(6 + 4n) = 12 + 8n.
      have h_ineq : 12 + 8 * (n : ℝ) ≤ ((n : ℝ) + 4) * ((n : ℝ) + 5) := by nlinarith
      have h_mul : Real.pi * τ.im * (12 + 8 * (n : ℝ)) ≤
          Real.pi * τ.im * (((n : ℝ) + 4) * ((n : ℝ) + 5)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    have h_neg_norm : ‖jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖ ≤
        r^6 * (r^4)^n := by
      rw [jacobiTheta₂_term_half_norm]
      have hN' : ((-(((n + 4) : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 4) := by push_cast; ring
      rw [hN', h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (-(n+4)) · (-(n+4)+1) · τ.im) = -(π · (n+4)(n+3) · τ.im) ≤ (6 + 4n)(-2π τ.im).
      -- ⟺ (n+4)(n+3) ≥ 12 + 8n, i.e. n² + 7n + 12 ≥ 12 + 8n, i.e. n² ≥ n.
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h_n_sq_ge : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith
      have h_ineq : 12 + 8 * (n : ℝ) ≤ (-((n : ℝ) + 4)) * (-((n : ℝ) + 4) + 1) := by nlinarith
      have h_mul : Real.pi * τ.im * (12 + 8 * (n : ℝ)) ≤
          Real.pi * τ.im * ((-((n : ℝ) + 4)) * (-((n : ℝ) + 4) + 1)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    linarith
  -- Summability of bound.
  have h_bound_summable : Summable (fun n : ℕ => 2 * (r^6 * (r^4)^n)) := by
    have h_geo : Summable (fun n : ℕ => (r^4)^n) :=
      summable_geometric_of_lt_one (by positivity) hr4_lt_one
    have : Summable (fun n : ℕ => r^6 * (r^4)^n) := h_geo.mul_left _
    exact this.mul_left _
  -- Tsum of bound = 2 r⁶ / (1 - r⁴).
  have h_bound_tsum : ∑' n : ℕ, 2 * (r^6 * (r^4)^n) =
      2 * r^6 * (1 - r^4)⁻¹ := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr4_lt_one]
    ring
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_termwise
  have h_norm_tsum_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_le : (∑' n : ℕ,
      ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖) ≤
      2 * r^6 * (1 - r^4)⁻¹ := by
    rw [← h_bound_tsum]
    exact h_norm_summable.tsum_le_tsum h_termwise h_bound_summable
  have h_step : ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ)‖ ≤ 2 * r^6 * (1 - r^4)⁻¹ :=
    h_norm_tsum_le.trans h_tsum_le
  have hr6_pos : 0 < r^6 := by positivity
  have h_final : r^6 + 2 * r^6 * (1 - r^4)⁻¹ ≤ 8 * r^6 := by
    have h1 : 2 * r^6 * (1 - r^4)⁻¹ ≤ 2 * r^6 * 2 := by
      apply mul_le_mul_of_nonneg_left h_inv_one_sub_r4_le
      positivity
    linarith
  have hr6_eq : r^6 = Real.exp (-12 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc r^6 + ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ)‖
      ≤ r^6 + 2 * r^6 * (1 - r^4)⁻¹ := by linarith [h_step]
    _ ≤ 8 * r^6 := h_final
    _ = 8 * Real.exp (-12 * Real.pi * τ.im) := by rw [hr6_eq]

/-- **Two-term leading bound for `θ₂`.** For `τ.im ≥ 1`,
`‖θ₂(τ) − 2·exp(πi τ/4)·(1 + exp(2πi τ))‖ ≤ 4·exp(−25π·τ.im/4)`.
Follows from `jacobiTheta₂_half_sub_two_minus_two_q2_norm_le_of_im_ge_one`
and `θ₂(τ) = exp(πi τ/4) · jacobiTheta₂(τ/2, τ)`, factoring out
`exp(πi τ/4)` with `|exp(πi τ/4)| = exp(−π τ.im/4)`. -/
theorem theta2_norm_sub_two_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ - 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
        (1 + Complex.exp (2 * Real.pi * Complex.I * τ))‖ ≤
      8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := by
  unfold theta2
  -- theta2 τ - 2 exp(πi τ/4)(1 + exp(2πi τ)) =
  --   exp(πi τ/4) · (jacobiTheta₂(τ/2, τ) - 2 - 2 exp(2πi τ)).
  have h_factor :
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ -
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ)) =
      Complex.exp (Real.pi * Complex.I * τ / 4) *
        (jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ)) := by
    ring
  rw [h_factor, norm_mul]
  -- |exp(πi τ/4)| = exp(-π τ.im/4).
  have h_norm_exp :
      ‖Complex.exp (Real.pi * Complex.I * τ / 4)‖ = Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
        ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp]
  have h_tail := jacobiTheta₂_half_sub_two_minus_two_q2_norm_le_of_im_ge_one hτ
  have h_exp_nn : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := (Real.exp_pos _).le
  have h_combine :
      Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-6 * Real.pi * τ.im)) =
      8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := by
    rw [show (Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-6 * Real.pi * τ.im)) : ℝ) =
        8 * (Real.exp (-(Real.pi * τ.im / 4)) * Real.exp (-6 * Real.pi * τ.im)) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 8 * Real.exp x) (by ring)
  calc Real.exp (-(Real.pi * τ.im / 4)) *
        ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ)‖
      ≤ Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-6 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_left h_tail h_exp_nn
    _ = 8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := h_combine

/-- **Three-term leading bound for `θ₂`.** For `τ.im ≥ 1`,
`‖θ₂(τ) − 2·exp(πi τ/4)·(1 + exp(2πi τ) + exp(6πi τ))‖ ≤ 8·exp(−49π·τ.im/4)`.
Follows from `jacobiTheta₂_half_sub_three_term_norm_le_of_im_ge_one`
and `θ₂(τ) = exp(πi τ/4) · jacobiTheta₂(τ/2, τ)`. -/
theorem theta2_norm_sub_three_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ - 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
        (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
          Complex.exp (6 * Real.pi * Complex.I * τ))‖ ≤
      8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := by
  unfold theta2
  have h_factor :
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ -
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
            Complex.exp (6 * Real.pi * Complex.I * τ)) =
      Complex.exp (Real.pi * Complex.I * τ / 4) *
        (jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (6 * Real.pi * Complex.I * τ)) := by
    ring
  rw [h_factor, norm_mul]
  have h_norm_exp :
      ‖Complex.exp (Real.pi * Complex.I * τ / 4)‖ = Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
        ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp]
  have h_tail := jacobiTheta₂_half_sub_three_term_norm_le_of_im_ge_one hτ
  have h_exp_nn : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := (Real.exp_pos _).le
  have h_combine :
      Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-12 * Real.pi * τ.im)) =
      8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := by
    rw [show (Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-12 * Real.pi * τ.im)) : ℝ) =
        8 * (Real.exp (-(Real.pi * τ.im / 4)) * Real.exp (-12 * Real.pi * τ.im)) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 8 * Real.exp x) (by ring)
  calc Real.exp (-(Real.pi * τ.im / 4)) *
        ‖jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (6 * Real.pi * Complex.I * τ)‖
      ≤ Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-12 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_left h_tail h_exp_nn
    _ = 8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := h_combine

/-- **Two-term leading bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ) − 16·exp(πi τ) + 128·exp(2πi τ)‖ ≤ K·exp(−3π·τ.im)` with
explicit constant `K = 8192`. Derives from
`theta2_norm_sub_two_term_le_of_im_ge_one` and
`theta3_sub_one_minus_2q_norm_le_of_im_ge_one` via the algebraic
expansion `(θ₂/θ₃)⁴ = 16q · (1 + r₂)⁴ · (1 + r₃)⁻⁴` (where
`r₂, r₃` are the second-order corrections of `θ₂, θ₃`), with two
applications of the geometric-series expansion `(1 + x)⁻¹ = 1 − x + O(x²)`.

This is the load-bearing q²-correction lemma needed for the
cusp-1 sign control in `modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`:
the `−128q²` coefficient is what makes `Im(δ_λ)` strictly
non-positive uniformly on `F^o`-shifted neighbourhoods of `0`. -/
theorem modularLambdaH_norm_sub_two_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ) +
        128 * Complex.exp (2 * Real.pi * Complex.I * τ)‖ ≤
      8192 * Real.exp (-3 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- Setup: q := exp(πi τ), Q2 := exp(2πi τ).
  set q : ℂ := Complex.exp (Real.pi * Complex.I * τ) with hq_def
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ) with hQ2_def
  -- rq := exp(-π τ.im). ‖q‖ = rq, ‖Q2‖ = rq² ≤ rq.
  set rq : ℝ := Real.exp (-Real.pi * τ.im) with hrq_def
  have hrq_pos : 0 < rq := Real.exp_pos _
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hq_norm : ‖q‖ = rq := by
    rw [hq_def, Complex.norm_exp, hrq_def]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ : ℂ) = ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by
      ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  have hQ2_eq_q_sq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hQ2_norm : ‖Q2‖ = rq^2 := by rw [hQ2_eq_q_sq, norm_pow, hq_norm]
  -- exp(π) > 16, so rq < 1/16.
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]; nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have hrq_le : rq ≤ Real.exp (-Real.pi) := by
    rw [hrq_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_pi_gt_16
  have hrq_lt : rq < 1/16 := lt_of_le_of_lt hrq_le h_exp_neg_pi_lt
  have hrq_lt_one : rq < 1 := by linarith
  have hrq3_eq : rq^3 = Real.exp (-3 * Real.pi * τ.im) := by
    rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- A := 2 exp(πi τ/4); A⁴ = 16 q; ‖A⁴‖ = 16 rq.
  set A : ℂ := 2 * Complex.exp (Real.pi * Complex.I * τ / 4) with hA_def
  have hA_pow : A^4 = 16 * q := by
    rw [hA_def, hq_def, mul_pow]
    rw [show (Complex.exp (Real.pi * Complex.I * τ / 4))^4 =
        Complex.exp (4 * (Real.pi * Complex.I * τ / 4)) from by
      rw [← Complex.exp_nat_mul]; norm_cast]
    rw [show (4 : ℂ) * (Real.pi * Complex.I * τ / 4) = Real.pi * Complex.I * τ from by ring]
    norm_num
  have hA_norm : ‖A‖ = 2 * Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [hA_def, norm_mul, Complex.norm_exp]
    have h_re : (Real.pi * Complex.I * τ / 4 : ℂ).re = -(Real.pi * τ.im / 4) := by
      have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
          ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
      rw [h_eq, Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [h_re]
    simp
  have hA_pow_norm : ‖A^4‖ = 16 * rq := by
    rw [hA_pow, norm_mul, hq_norm]; simp
  have hA_norm_pos : 0 < ‖A‖ := by rw [hA_norm]; positivity
  have hA_ne : A ≠ 0 := norm_ne_zero_iff.mp hA_norm_pos.ne'
  -- r₂' and r₃' bounds via two-term theta lemmas.
  set r₂' : ℂ := (theta2 τ - A * (1 + Q2)) / A with hr2_def
  set r₃' : ℂ := theta3 τ - 1 - 2 * q with hr3_def
  have h_th2_sub := theta2_norm_sub_two_term_le_of_im_ge_one hτ
  have h_unfold_A1Q2 : 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
      (1 + Complex.exp (2 * Real.pi * Complex.I * τ)) = A * (1 + Q2) := by
    rw [hA_def, hQ2_def]
  have hr2_bound : ‖r₂'‖ ≤ 4 * rq^6 := by
    rw [hr2_def, norm_div, hA_norm]
    have h_denom_pos : 0 < 2 * Real.exp (-(Real.pi * τ.im / 4)) := by positivity
    rw [div_le_iff₀ h_denom_pos]
    have hrq6_eq : rq^6 = Real.exp (-(6 * Real.pi * τ.im)) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h_target_eq : 4 * rq^6 * (2 * Real.exp (-(Real.pi * τ.im / 4))) =
        8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := by
      rw [hrq6_eq]
      rw [show (4 * Real.exp (-(6 * Real.pi * τ.im)) *
          (2 * Real.exp (-(Real.pi * τ.im / 4))) : ℝ) =
          8 * (Real.exp (-(6 * Real.pi * τ.im)) * Real.exp (-(Real.pi * τ.im / 4))) from by ring]
      rw [← Real.exp_add]
      exact congr_arg (fun x => 8 * Real.exp x) (by ring)
    rw [h_target_eq, ← h_unfold_A1Q2]
    exact h_th2_sub
  have hr3_bound : ‖r₃'‖ ≤ 4 * rq^4 := by
    rw [hr3_def, hq_def]
    have hrq4_eq : rq^4 = Real.exp (-4 * Real.pi * τ.im) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hrq4_eq]
    exact theta3_sub_one_minus_2q_norm_le_of_im_ge_one hτ
  -- Loose bounds: ‖r₂'‖ ≤ rq², ‖r₃'‖ ≤ rq (using rq < 1/16).
  -- 4 rq^6 ≤ rq²: need 4 rq^4 ≤ 1, i.e., rq ≤ (1/4)^{1/4} ≈ 0.707. We have rq < 1/16. ✓
  have hrq2_pos : 0 < rq^2 := by positivity
  have hr2_bound_loose : ‖r₂'‖ ≤ rq^2 := by
    refine hr2_bound.trans ?_
    -- 4 rq^6 ≤ rq^2 ⟺ 4 rq^4 ≤ 1. We have rq < 1/16, so rq^4 < 1/65536 < 1/4.
    have h_rq4_lt : rq^4 < 1/4 := by
      have : rq^4 < (1/16)^4 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16)^4 : ℝ) ≤ 1/4 := by norm_num
      linarith
    have : 4 * rq^6 ≤ rq^2 := by
      have h_rq6 : rq^6 = rq^4 * rq^2 := by ring
      rw [h_rq6]
      have h_ineq : 4 * rq^4 ≤ 1 := by linarith
      calc 4 * (rq^4 * rq^2) = (4 * rq^4) * rq^2 := by ring
        _ ≤ 1 * rq^2 := mul_le_mul_of_nonneg_right h_ineq hrq2_pos.le
        _ = rq^2 := by ring
    linarith
  have hr3_bound_loose : ‖r₃'‖ ≤ rq := by
    refine hr3_bound.trans ?_
    -- 4 rq^4 ≤ rq ⟺ 4 rq^3 ≤ 1.
    have h_rq3_lt : rq^3 < 1/4 := by
      have : rq^3 < (1/16)^3 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16 : ℝ))^3 ≤ 1/4 := by norm_num
      linarith
    have : 4 * rq^4 ≤ rq := by
      have h_rq4 : rq^4 = rq^3 * rq := by ring
      rw [h_rq4]
      have h_ineq : 4 * rq^3 ≤ 1 := by linarith
      calc 4 * (rq^3 * rq) = (4 * rq^3) * rq := by ring
        _ ≤ 1 * rq := mul_le_mul_of_nonneg_right h_ineq hrq_nn
        _ = rq := by ring
    linarith
  -- θ₂ = A(1 + Q2 + r₂'); θ₃ = 1 + 2q + r₃'.
  have h_th2_eq : theta2 τ = A * (1 + Q2 + r₂') := by
    rw [hr2_def]; field_simp; ring
  have h_th3_eq : theta3 τ = 1 + 2 * q + r₃' := by rw [hr3_def]; ring
  -- ‖θ₃‖ ≥ 1/2, so 1 + 2q + r₃' ≠ 0 and ‖1+2q+r₃'‖ ≥ 1/2.
  have h_th3_norm_ge := theta3_norm_ge_half_of_im_ge_one hτ
  have h_th3_norm_ge' : (1/2 : ℝ) ≤ ‖(1 + 2*q + r₃' : ℂ)‖ := by
    rw [← h_th3_eq]; exact h_th3_norm_ge
  have h_th3_pos : 0 < ‖(1 + 2*q + r₃' : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_th3_norm_ge'
  have h_th3_ne : (1 + 2*q + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp h_th3_pos.ne'
  -- λ = A⁴ · ((1+Q2+r₂')/(1+2q+r₃'))⁴.
  have h_lambda_eq : modularLambdaH τ = A^4 * ((1 + Q2 + r₂') / (1 + 2*q + r₃'))^4 := by
    unfold modularLambdaH
    rw [h_th2_eq, h_th3_eq, mul_pow, div_pow]
    ring
  rw [h_lambda_eq]
  -- Rewrite 16 q = A^4 and 128 Q2 = 8 q · A^4.
  rw [show (16 * Complex.exp (Real.pi * Complex.I * τ) : ℂ) = A^4 from hA_pow.symm]
  have h_128_eq : (128 * Complex.exp (2 * Real.pi * Complex.I * τ) : ℂ) = 8 * q * A^4 := by
    rw [show Complex.exp (2 * Real.pi * Complex.I * τ) = Q2 from rfl]
    rw [hA_pow, hQ2_eq_q_sq]; ring
  rw [h_128_eq]
  -- Goal: ‖A^4 * ratio^4 - A^4 + 8 q · A^4‖ ≤ ...
  -- = ‖A^4 · (ratio^4 - 1 + 8 q)‖.
  rw [show (A^4 * ((1 + Q2 + r₂') / (1 + 2*q + r₃'))^4 - A^4 + 8 * q * A^4 : ℂ) =
      A^4 * (((1 + Q2 + r₂') / (1 + 2*q + r₃'))^4 - 1 + 8 * q) from by ring]
  rw [norm_mul, hA_pow_norm]
  -- Set v := (1+Q2+r₂')/(1+2q+r₃') - 1.
  set v : ℂ := (1 + Q2 + r₂') / (1 + 2*q + r₃') - 1 with hv_def
  have hv_add : (1 + Q2 + r₂') / (1 + 2*q + r₃') = 1 + v := by rw [hv_def]; ring
  rw [hv_add]
  -- (1+v)^4 - 1 + 8 q = 4 (v + 2 q) + 6 v² + 4 v³ + v⁴.
  rw [show ((1 + v)^4 - 1 + 8 * q : ℂ) = 4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 from by ring]
  -- v + 2q identity: v + 2q = (Q2 + r₂' - 2q - r₃' + 2q(1+2q+r₃'))/(1+2q+r₃')
  --                       = (Q2 + r₂' - r₃' + 4q² + 2q r₃')/(1+2q+r₃').
  -- Substituting Q2 = q²: numerator = q² + 4q² + r₂' - r₃' + 2q r₃' = 5q² + r₂' - r₃' + 2q r₃'.
  -- But this uses Q2 = q². Since we want a CLEAN identity, let's keep Q2 generic.
  have hv_plus_2q_eq : v + 2*q =
      (Q2 + r₂' - r₃' + 4*q^2 + 2*q*r₃') / (1 + 2*q + r₃') := by
    rw [hv_def]
    field_simp
    ring
  -- |Q2| ≤ rq²; |r₂'| ≤ rq²; |r₃'| ≤ rq²; |4q²| = 4 rq²; |2q r₃'| ≤ 2 rq².
  -- We have ‖r₃'‖ ≤ 4 rq^4 ≤ rq² (since 4 rq² ≤ 1 for rq ≤ 1/2).
  have hr3_bound_better : ‖r₃'‖ ≤ rq^2 := by
    refine hr3_bound.trans ?_
    -- 4 rq^4 ≤ rq² ⟺ 4 rq² ≤ 1. We have rq < 1/16, so rq² < 1/256 < 1/4.
    have h_rq2_lt : rq^2 < 1/4 := by
      have : rq^2 < (1/16)^2 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16 : ℝ))^2 ≤ 1/4 := by norm_num
      linarith
    have : 4 * rq^4 ≤ rq^2 := by
      have h_rq4 : rq^4 = rq^2 * rq^2 := by ring
      rw [h_rq4]
      have h_ineq : 4 * rq^2 ≤ 1 := by linarith
      calc 4 * (rq^2 * rq^2) = (4 * rq^2) * rq^2 := by ring
        _ ≤ 1 * rq^2 := mul_le_mul_of_nonneg_right h_ineq hrq2_pos.le
        _ = rq^2 := by ring
    linarith
  -- |2q r₃'| ≤ 2 rq · rq² ≤ rq² for rq ≤ 1/2.
  -- Actually 2 rq · rq² = 2 rq³. For rq ≤ 1/2: 2 rq³ ≤ rq² (since 2 rq ≤ 1).
  -- So |2q r₃'| ≤ 2 rq · rq² ≤ rq² (since 2 rq ≤ 2/16 = 1/8 ≤ 1).
  -- Therefore: ‖num‖ ≤ rq² + rq² + rq² + 4 rq² + rq² = 8 rq².
  have h_num_bound : ‖(Q2 + r₂' - r₃' + 4*q^2 + 2*q*r₃' : ℂ)‖ ≤ 8 * rq^2 := by
    have h1 : ‖(Q2 + r₂' - r₃' + 4*q^2 + 2*q*r₃' : ℂ)‖ ≤
        ‖Q2‖ + ‖r₂'‖ + ‖r₃'‖ + ‖(4 * q^2 : ℂ)‖ + ‖(2 * q * r₃' : ℂ)‖ := by
      have h_step1 := norm_add_le (Q2 + r₂' - r₃' + 4*q^2) (2 * q * r₃')
      have h_step2 := norm_add_le (Q2 + r₂' - r₃') (4*q^2)
      have h_step3 := norm_sub_le (Q2 + r₂') r₃'
      have h_step4 := norm_add_le Q2 r₂'
      have h_rewrite_a : Q2 + r₂' - r₃' + 4 * q^2 + 2 * q * r₃' =
          (Q2 + r₂' - r₃' + 4 * q^2) + 2 * q * r₃' := by ring
      have h_rewrite_b : Q2 + r₂' - r₃' + 4 * q^2 =
          (Q2 + r₂' - r₃') + 4 * q^2 := by ring
      have h_rewrite_c : Q2 + r₂' - r₃' = (Q2 + r₂') - r₃' := by ring
      rw [h_rewrite_a]
      refine h_step1.trans ?_
      rw [h_rewrite_b] at h_step2 ⊢
      have h_step2' := h_step2
      have h_combine : ‖Q2 + r₂' - r₃' + 4 * q^2‖ + ‖2 * q * r₃'‖ ≤
          ‖Q2 + r₂' - r₃'‖ + ‖(4 * q^2 : ℂ)‖ + ‖2 * q * r₃'‖ := by linarith
      refine h_combine.trans ?_
      rw [h_rewrite_c] at h_step3
      have h_step3' : ‖(Q2 + r₂') - r₃'‖ ≤ ‖Q2 + r₂'‖ + ‖r₃'‖ := norm_sub_le _ _
      have h_combine2 : ‖Q2 + r₂' - r₃'‖ ≤ ‖Q2 + r₂'‖ + ‖r₃'‖ := by
        rw [h_rewrite_c]; exact h_step3'
      have h_combine3 : ‖Q2 + r₂'‖ ≤ ‖Q2‖ + ‖r₂'‖ := h_step4
      linarith
    have h_4q2 : ‖(4 * q^2 : ℂ)‖ = 4 * rq^2 := by
      rw [show ((4 * q^2 : ℂ)) = (((4 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, norm_pow, hq_norm]
      simp
    have h_2qr3 : ‖(2 * q * r₃' : ℂ)‖ ≤ 2 * rq * rq^2 := by
      rw [norm_mul, norm_mul, hq_norm, Complex.norm_ofNat]
      have h_step : (2 : ℝ) * rq * ‖r₃'‖ ≤ 2 * rq * rq^2 :=
        mul_le_mul_of_nonneg_left hr3_bound_better (by positivity)
      linarith
    -- Bound 2*rq*rq^2 by rq^2 (since 2*rq ≤ 1/8 < 1).
    have h_2rq_le : (2 : ℝ) * rq ≤ 1 := by linarith
    have h_2qr3_loose : ‖(2 * q * r₃' : ℂ)‖ ≤ rq^2 := by
      refine h_2qr3.trans ?_
      have h_step : (2 : ℝ) * rq * rq^2 ≤ 1 * rq^2 :=
        mul_le_mul_of_nonneg_right h_2rq_le hrq2_pos.le
      linarith
    rw [h_4q2] at h1
    linarith [hQ2_norm.le, hr2_bound_loose, hr3_bound_better, h1, h_2qr3_loose]
  -- |1 + 2q + r₃'| ≥ 1/2 from h_th3_norm_ge'.
  -- |v + 2q| = ‖num‖/‖1+2q+r₃'‖ ≤ (8 rq²)/(1/2) = 16 rq².
  have hv_plus_2q_bound : ‖v + 2*q‖ ≤ 16 * rq^2 := by
    rw [hv_plus_2q_eq, norm_div]
    rw [div_le_iff₀ h_th3_pos]
    have h1 : 16 * rq^2 * ‖(1 + 2*q + r₃' : ℂ)‖ ≥ 16 * rq^2 * (1/2) := by
      apply mul_le_mul_of_nonneg_left h_th3_norm_ge' (by positivity)
    have h2 : 16 * rq^2 * (1/2 : ℝ) = 8 * rq^2 := by ring
    linarith [h_num_bound]
  -- |v| ≤ 6 rq (from |Q-R|/|1+R|).
  -- v = (Q2 + r₂' - 2q - r₃')/(1+2q+r₃').
  have hv_alt : v = (Q2 + r₂' - 2*q - r₃') / (1 + 2*q + r₃') := by
    rw [hv_def]; field_simp; ring
  have hv_bound : ‖v‖ ≤ 6 * rq := by
    rw [hv_alt, norm_div]
    rw [div_le_iff₀ h_th3_pos]
    -- ‖Q2 + r₂' - 2q - r₃'‖ ≤ rq² + rq² + 2 rq + rq² = 2 rq + 3 rq² ≤ 3 rq.
    have h_num : ‖(Q2 + r₂' - 2*q - r₃' : ℂ)‖ ≤ rq^2 + rq^2 + 2 * rq + rq^2 := by
      have h1 : ‖(Q2 + r₂' - 2*q - r₃' : ℂ)‖ ≤
          ‖Q2‖ + ‖r₂'‖ + ‖(2 * q : ℂ)‖ + ‖r₃'‖ := by
        have h_step1 := norm_sub_le (Q2 + r₂' - 2*q) r₃'
        have h_step2 := norm_sub_le (Q2 + r₂') (2*q)
        have h_step3 := norm_add_le Q2 r₂'
        have h_rewrite : Q2 + r₂' - 2 * q - r₃' = (Q2 + r₂' - 2 * q) - r₃' := by ring
        rw [h_rewrite]
        have h_rewrite_b : Q2 + r₂' - 2 * q = (Q2 + r₂') - 2 * q := by ring
        rw [h_rewrite_b] at h_step2
        linarith
      have h_2q : ‖(2 * q : ℂ)‖ = 2 * rq := by
        rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
        rw [norm_mul, Complex.norm_real, hq_norm]
        simp
      rw [h_2q] at h1
      linarith [hQ2_norm.le, hr2_bound_loose, hr3_bound_better]
    have h_num_simp : rq^2 + rq^2 + 2 * rq + rq^2 = 2 * rq + 3 * rq^2 := by ring
    rw [h_num_simp] at h_num
    -- 2 rq + 3 rq² ≤ 3 rq (since 3 rq² ≤ rq for rq ≤ 1/3, true).
    have h_rq2_le : 3 * rq^2 ≤ rq := by
      have : 3 * rq ≤ 1 := by linarith
      calc 3 * rq^2 = (3 * rq) * rq := by ring
        _ ≤ 1 * rq := mul_le_mul_of_nonneg_right this hrq_nn
        _ = rq := by ring
    have h_num_loose : ‖(Q2 + r₂' - 2*q - r₃' : ℂ)‖ ≤ 3 * rq := by linarith
    -- Now ‖num‖ ≤ 3 rq, ‖1+R‖ ≥ 1/2, so ‖v‖ ≤ 6 rq.
    have h1 : 6 * rq * ‖(1 + 2*q + r₃' : ℂ)‖ ≥ 6 * rq * (1/2) := by
      apply mul_le_mul_of_nonneg_left h_th3_norm_ge' (by positivity)
    linarith
  -- Now bound the bracket: ‖4(v+2q) + 6v² + 4v³ + v⁴‖.
  have hv_sq : ‖v‖^2 ≤ 36 * rq^2 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hv_bound 2
    have h_sq : (6 * rq)^2 = 36 * rq^2 := by ring
    linarith [this, h_sq.le]
  have hv_cube : ‖v‖^3 ≤ 216 * rq^3 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hv_bound 3
    have h_cube : (6 * rq)^3 = 216 * rq^3 := by ring
    linarith [this, h_cube.le]
  have hv_fourth : ‖v‖^4 ≤ 1296 * rq^4 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hv_bound 4
    have h_fourth : (6 * rq)^4 = 1296 * rq^4 := by ring
    linarith [this, h_fourth.le]
  have h_4v_bound : ‖(4 * (v + 2 * q) : ℂ)‖ ≤ 4 * (16 * rq^2) := by
    rw [norm_mul, Complex.norm_ofNat]
    have h_step : (4 : ℝ) * ‖v + 2 * q‖ ≤ 4 * (16 * rq^2) :=
      mul_le_mul_of_nonneg_left hv_plus_2q_bound (by norm_num)
    linarith
  have h_6v2_bound : ‖(6 * v^2 : ℂ)‖ ≤ 6 * (36 * rq^2) := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h_step : (6 : ℝ) * ‖v‖^2 ≤ 6 * (36 * rq^2) :=
      mul_le_mul_of_nonneg_left hv_sq (by norm_num)
    linarith
  have h_4v3_bound : ‖(4 * v^3 : ℂ)‖ ≤ 4 * (216 * rq^3) := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h_step : (4 : ℝ) * ‖v‖^3 ≤ 4 * (216 * rq^3) :=
      mul_le_mul_of_nonneg_left hv_cube (by norm_num)
    linarith
  have h_v4_bound : ‖(v^4 : ℂ)‖ ≤ 1296 * rq^4 := by
    rw [norm_pow]; exact hv_fourth
  -- Combine: ‖bracket‖ ≤ 64 rq² + 216 rq² + 864 rq³ + 1296 rq⁴.
  have h_bracket_bound : ‖(4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 : ℂ)‖ ≤
      64 * rq^2 + 216 * rq^2 + 864 * rq^3 + 1296 * rq^4 := by
    have h1 := norm_add_le ((4 * (v + 2*q) + 6 * v^2 + 4 * v^3 : ℂ)) ((v^4 : ℂ))
    have h2 := norm_add_le ((4 * (v + 2*q) + 6 * v^2 : ℂ)) ((4 * v^3 : ℂ))
    have h3 := norm_add_le ((4 * (v + 2*q) : ℂ)) ((6 * v^2 : ℂ))
    -- ‖4(v+2q) + 6v² + 4v³ + v⁴‖ ≤ ‖4(v+2q)‖ + ‖6v²‖ + ‖4v³‖ + ‖v⁴‖.
    have h_chain : ‖(4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 : ℂ)‖ ≤
        ‖(4 * (v + 2*q) : ℂ)‖ + ‖(6 * v^2 : ℂ)‖ + ‖(4 * v^3 : ℂ)‖ + ‖(v^4 : ℂ)‖ := by linarith
    linarith [h_4v_bound, h_6v2_bound, h_4v3_bound, h_v4_bound, h_chain]
  -- Now want: 16 rq · (bracket bound) ≤ 8192 · exp(-3π τ.im) = 8192 rq³.
  -- 64 rq² + 216 rq² + 864 rq³ + 1296 rq⁴
  --   ≤ 280 rq² + 864 rq³ + 1296 rq⁴
  -- For rq ≤ 1/16: rq³ ≤ rq²/16, rq⁴ ≤ rq²/256.
  -- 864 rq³ ≤ 864 rq² /16 = 54 rq². 1296 rq⁴ ≤ 1296 rq²/256 ≈ 5 rq².
  -- Sum ≤ 280 + 54 + 5 = 339 rq². Use 400 rq² for buffer.
  -- 16 rq · 400 rq² = 6400 rq³ ≤ 8192 rq³. ✓
  have hrq3_le_rq2 : rq^3 ≤ rq^2 / 16 := by
    -- rq^3 = rq^2 * rq ≤ rq^2 * (1/16)
    have h1 : rq^3 = rq^2 * rq := by ring
    rw [h1]
    have h2 : rq^2 * rq ≤ rq^2 * (1/16) :=
      mul_le_mul_of_nonneg_left (by linarith : rq ≤ 1/16) hrq2_pos.le
    linarith
  have hrq4_le_rq2 : rq^4 ≤ rq^2 / 256 := by
    -- rq^4 = rq^2 * rq^2 ≤ rq^2 * (1/256)
    have h1 : rq^4 = rq^2 * rq^2 := by ring
    rw [h1]
    have h_rq2_le : rq^2 ≤ 1/256 := by
      have : rq^2 < (1/16)^2 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16 : ℝ))^2 = 1/256 := by norm_num
      linarith
    have h2 : rq^2 * rq^2 ≤ rq^2 * (1/256) :=
      mul_le_mul_of_nonneg_left h_rq2_le hrq2_pos.le
    linarith
  have h_final_bound : 64 * rq^2 + 216 * rq^2 + 864 * rq^3 + 1296 * rq^4 ≤ 400 * rq^2 := by
    have h1 : 864 * rq^3 ≤ 864 * (rq^2 / 16) :=
      mul_le_mul_of_nonneg_left hrq3_le_rq2 (by norm_num)
    have h2 : 1296 * rq^4 ≤ 1296 * (rq^2 / 256) :=
      mul_le_mul_of_nonneg_left hrq4_le_rq2 (by norm_num)
    have h_simp1 : 864 * (rq^2 / 16) = 54 * rq^2 := by ring
    rw [h_simp1] at h1
    have h_const : (1296 : ℝ) / 256 ≤ 6 := by norm_num
    have h_step : 1296 * (rq^2 / 256) ≤ 6 * rq^2 := by
      calc 1296 * (rq^2 / 256) = (1296 / 256) * rq^2 := by ring
        _ ≤ 6 * rq^2 := mul_le_mul_of_nonneg_right h_const hrq2_pos.le
    have h2' : 1296 * rq^4 ≤ 6 * rq^2 := h2.trans h_step
    linarith
  -- Combine: 16 rq · (bracket norm) ≤ 16 rq · 400 rq² = 6400 rq³ ≤ 8192 rq³.
  have h_step : (16 * rq) * ‖(4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 : ℂ)‖ ≤
      (16 * rq) * (400 * rq^2) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [h_bracket_bound, h_final_bound]
    · positivity
  have h_simp : (16 : ℝ) * rq * (400 * rq^2) = 6400 * rq^3 := by ring
  rw [h_simp] at h_step
  have h_final : 6400 * rq^3 ≤ 8192 * Real.exp (-3 * Real.pi * τ.im) := by
    rw [← hrq3_eq]
    have h_pos : 0 ≤ rq^3 := by positivity
    linarith
  linarith

/-- Pure ring identity used in the three-term `λ` bound. With
`s := v + 2q − 5q²`, the bracket
`(1 + v)⁴ − 1 + 8q − 44q²` decomposes into a `−120q³` leading correction
plus terms quadratic and higher in `s` and `v`. -/
theorem modularLambda_three_term_bracket_identity (v q : ℂ) :
    (1 + v)^4 - 1 + 8 * q - 44 * q^2 =
      -120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
        6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 := by
  ring

/-- Norm bound on `v := (1 + q² + q⁶ + r₂') / D − 1` with
`D := 1 + 2q + 2q⁴ + r₃'`. Used in the three-term `λ` bound. -/
theorem modularLambda_three_term_v_bound (q r₂' r₃' : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (hr2_loose : ‖r₂'‖ ≤ rq ^ 3) (hr3_loose : ‖r₃'‖ ≤ rq ^ 3)
    (hD_norm : (1 / 2 : ℝ) ≤ ‖(1 + 2 * q + 2 * q ^ 4 + r₃' : ℂ)‖) :
    ‖(1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1‖ ≤ 6 * rq := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hrq2_pos : 0 < rq^2 := by positivity
  have hD_pos : 0 < ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by linarith
  have hD_ne : (1 + 2*q + 2*q^4 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp hD_pos.ne'
  -- Rewrite v as num/D.
  have h_v_eq : (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1 =
      (q^2 + q^6 + r₂' - 2*q - 2*q^4 - r₃') / (1 + 2*q + 2*q^4 + r₃') := by
    rw [div_sub_one hD_ne]
    congr 1; ring
  rw [h_v_eq, norm_div]
  rw [div_le_iff₀ hD_pos]
  -- Goal: ‖num‖ ≤ 6 * rq * ‖D‖.
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  have h_q6_norm : ‖q^6‖ = rq^6 := by rw [norm_pow, hq_norm]
  have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
    rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, hq_norm]; simp
  have h_2q4_norm : ‖((2 : ℂ) * q^4)‖ = 2 * rq^4 := by
    rw [show ((2 * q^4 : ℂ)) = (((2 : ℝ) : ℂ)) * q^4 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q4_norm]; simp
  -- Triangle inequality.
  have h_eq : q^2 + q^6 + r₂' - 2*q - 2*q^4 - r₃' =
      (((q^2 + q^6 + r₂') - 2*q) - 2*q^4) - r₃' := by ring
  rw [h_eq]
  have h_t1 := norm_sub_le (((q^2 + q^6 + r₂') - 2*q) - 2*q^4) r₃'
  have h_t2 := norm_sub_le ((q^2 + q^6 + r₂') - 2*q) (2*q^4)
  have h_t3 := norm_sub_le (q^2 + q^6 + r₂') (2*q)
  have h_t4 := norm_add_le (q^2 + q^6) r₂'
  have h_t5 := norm_add_le (q^2) (q^6)
  -- Power ladder.
  have h_rq3_le_rq2 : rq^3 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq4_le_rq2 : rq^4 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq6_le_rq2 : rq^6 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq2_le_rq16 : rq^2 ≤ rq * (1/16) := by
    have h_eq2 : rq^2 = rq * rq := by ring
    rw [h_eq2]; exact mul_le_mul_of_nonneg_left hrq_lt.le hrq_nn
  -- Bound LHS ≤ 3 rq.
  have h_lhs_le : ‖(((q^2 + q^6 + r₂') - 2*q) - 2*q^4) - r₃'‖ ≤ 3 * rq := by
    have h_chain : ‖(((q^2 + q^6 + r₂') - 2*q) - 2*q^4) - r₃'‖ ≤
        rq^2 + rq^6 + rq^3 + 2*rq + 2*rq^4 + rq^3 := by
      linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_q2_norm.le, h_q6_norm.le,
                hr2_loose, hr3_loose, h_2q_norm.le, h_2q4_norm.le]
    -- rq² + rq⁶ + 2*rq³ + 2*rq⁴ ≤ 6 rq² ≤ 6·rq/16 ≤ rq.
    linarith [h_chain, h_rq3_le_rq2, h_rq4_le_rq2, h_rq6_le_rq2, h_rq2_le_rq16]
  -- 6 rq · ‖D‖ ≥ 6 rq · (1/2) = 3 rq.
  have h_rhs_ge : 3 * rq ≤ 6 * rq * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by
    have h_step : 6 * rq * (1/2 : ℝ) ≤ 6 * rq * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hD_norm (by positivity)
    linarith
  linarith

/-- Norm bound on `s := v + 2q − 5q²` for the three-term `λ` setup. -/
theorem modularLambda_three_term_s_bound (q r₂' r₃' : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (hr2_loose : ‖r₂'‖ ≤ rq ^ 3) (hr3_loose : ‖r₃'‖ ≤ rq ^ 3)
    (hD_norm : (1 / 2 : ℝ) ≤ ‖(1 + 2 * q + 2 * q ^ 4 + r₃' : ℂ)‖) :
    ‖((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2‖ ≤ 64 * rq^3 := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hrq2_pos : 0 < rq^2 := by positivity
  have hrq3_pos : 0 < rq^3 := by positivity
  have hD_pos : 0 < ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by linarith
  have hD_ne : (1 + 2*q + 2*q^4 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp hD_pos.ne'
  -- s = num/D where num = -10q³ - 2q⁴ + 4q⁵ - 9q⁶ + r₂' - r₃'(1 - 2q + 5q²).
  have h_s_eq : ((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2 =
      (-10*q^3 - 2*q^4 + 4*q^5 - 9*q^6 + r₂' - r₃' * (1 - 2*q + 5*q^2)) /
        (1 + 2*q + 2*q^4 + r₃') := by
    have h_lhs_mul : (((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2) *
        (1 + 2*q + 2*q^4 + r₃') =
        (-10*q^3 - 2*q^4 + 4*q^5 - 9*q^6 + r₂' - r₃' * (1 - 2*q + 5*q^2)) := by
      have h_div_mul : (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') *
          (1 + 2*q + 2*q^4 + r₃') = 1 + q^2 + q^6 + r₂' := div_mul_cancel₀ _ hD_ne
      have h_expand : (((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2) *
          (1 + 2*q + 2*q^4 + r₃') =
          (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') * (1 + 2*q + 2*q^4 + r₃') -
            (1 + 2*q + 2*q^4 + r₃') + 2*q * (1 + 2*q + 2*q^4 + r₃') -
            5*q^2 * (1 + 2*q + 2*q^4 + r₃') := by ring
      rw [h_expand, h_div_mul]
      ring
    rw [eq_div_iff hD_ne]
    exact h_lhs_mul
  rw [h_s_eq, norm_div]
  rw [div_le_iff₀ hD_pos]
  -- Goal: ‖num‖ ≤ 64 rq³ · ‖D‖.
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q3_norm : ‖q^3‖ = rq^3 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  have h_q5_norm : ‖q^5‖ = rq^5 := by rw [norm_pow, hq_norm]
  have h_q6_norm : ‖q^6‖ = rq^6 := by rw [norm_pow, hq_norm]
  have h_10q3_norm : ‖((10 : ℂ) * q^3)‖ = 10 * rq^3 := by
    rw [show ((10 * q^3 : ℂ)) = (((10 : ℝ) : ℂ)) * q^3 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q3_norm]; simp
  have h_2q4_norm : ‖((2 : ℂ) * q^4)‖ = 2 * rq^4 := by
    rw [show ((2 * q^4 : ℂ)) = (((2 : ℝ) : ℂ)) * q^4 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q4_norm]; simp
  have h_4q5_norm : ‖((4 : ℂ) * q^5)‖ = 4 * rq^5 := by
    rw [show ((4 * q^5 : ℂ)) = (((4 : ℝ) : ℂ)) * q^5 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q5_norm]; simp
  have h_9q6_norm : ‖((9 : ℂ) * q^6)‖ = 9 * rq^6 := by
    rw [show ((9 * q^6 : ℂ)) = (((9 : ℝ) : ℂ)) * q^6 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q6_norm]; simp
  -- ‖1 - 2q + 5q²‖ ≤ 2.
  have h_1_2q_5q2_le : ‖((1 : ℂ) - 2*q + 5*q^2)‖ ≤ 2 := by
    have h_5q2_norm : ‖((5 : ℂ) * q^2)‖ = 5 * rq^2 := by
      rw [show ((5 * q^2 : ℂ)) = (((5 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, h_q2_norm]; simp
    have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
      rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_1_norm : ‖((1 : ℂ))‖ = 1 := norm_one
    have h_add := norm_add_le ((1 : ℂ) - 2*q) (5*q^2)
    have h_sub := norm_sub_le ((1 : ℂ)) (2*q)
    have h_5rq2 : 5 * rq^2 ≤ 1/2 := by
      have h_rq2_le : rq^2 ≤ rq * (1/16) := by
        have h_eq2 : rq^2 = rq * rq := by ring
        rw [h_eq2]; exact mul_le_mul_of_nonneg_left hrq_lt.le hrq_nn
      have h_rq16 : rq * (1/16 : ℝ) ≤ (1/16) * (1/16) := by
        apply mul_le_mul_of_nonneg_right hrq_lt.le; norm_num
      have : rq^2 ≤ (1/256 : ℝ) := by
        have h_simp : (1/16 : ℝ) * (1/16) = 1/256 := by norm_num
        linarith
      linarith
    have h_2rq : 2 * rq ≤ 1/2 := by linarith
    linarith [h_add, h_sub, h_5q2_norm.le, h_2q_norm.le, h_5rq2, h_2rq, h_1_norm]
  -- ‖r₃' · (1 - 2q + 5q²)‖ ≤ 2 rq³.
  have h_r3_mul_le : ‖r₃' * (1 - 2*q + 5*q^2)‖ ≤ 2 * rq^3 := by
    rw [norm_mul]
    have h : ‖r₃'‖ * ‖((1 : ℂ) - 2*q + 5*q^2)‖ ≤ rq^3 * 2 :=
      mul_le_mul hr3_loose h_1_2q_5q2_le (norm_nonneg _) hrq3_pos.le
    linarith
  -- Triangle inequality.
  have h_eq : -10*q^3 - 2*q^4 + 4*q^5 - 9*q^6 + r₂' - r₃' * (1 - 2*q + 5*q^2) =
      (((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6) + r₂') - r₃' * (1 - 2*q + 5*q^2) := by ring
  rw [h_eq]
  have h_t1 := norm_sub_le ((((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6) + r₂'))
    (r₃' * (1 - 2*q + 5*q^2))
  have h_t2 := norm_add_le (((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6)) r₂'
  have h_t3 := norm_sub_le ((((-(10*q^3)) - 2*q^4) + 4*q^5)) (9*q^6)
  have h_t4 := norm_add_le (((-(10*q^3)) - 2*q^4)) (4*q^5)
  have h_t5 := norm_sub_le (-(10*q^3)) (2*q^4)
  have h_neg10q3 : ‖(-((10 : ℂ) * q^3))‖ = 10 * rq^3 := by
    rw [norm_neg]; exact h_10q3_norm
  -- Power bounds.
  have h_rq4_le : rq^4 ≤ rq^3 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq5_le : rq^5 ≤ rq^3 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq6_le : rq^6 ≤ rq^3 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  -- Numerator bound: 10 + 2 + 4 + 9 + 1 + 2 = 28 rq³.
  have h_num_le : ‖(((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6) + r₂') -
      r₃' * (1 - 2*q + 5*q^2)‖ ≤ 28 * rq^3 := by
    linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_neg10q3, h_2q4_norm.le, h_4q5_norm.le,
              h_9q6_norm.le, hr2_loose, h_r3_mul_le, h_rq4_le, h_rq5_le, h_rq6_le]
  -- 64 rq³ · ‖D‖ ≥ 64 rq³ · 1/2 = 32 rq³ ≥ 28 rq³.
  have h_rhs_ge : 28 * rq^3 ≤ 64 * rq^3 * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by
    have h_step : 64 * rq^3 * (1/2 : ℝ) ≤ 64 * rq^3 * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hD_norm (by positivity)
    linarith
  linarith

/-- **Three-term leading bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ) − 16·exp(πi τ) + 128·exp(2πi τ) − 704·exp(3πi τ)‖
   ≤ 32768·exp(−4π·τ.im)`. Combines the three-term `θ₂` and `θ₃` bounds
via the algebraic identity `(1 + v)⁴ − 1 + 8q − 44q² = −120q³ +
(4 − 24q + 60q²)·s + 6s² + 150q⁴ + 4v³ + v⁴` where `s := v + 2q − 5q²`
captures the next-order correction beyond the two-term bound. -/
theorem modularLambdaH_norm_sub_three_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ) +
        128 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        704 * Complex.exp (3 * Real.pi * Complex.I * τ)‖ ≤
      32768 * Real.exp (-4 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  set q : ℂ := Complex.exp (Real.pi * Complex.I * τ) with hq_def
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ) with hQ2_def
  set Q3 : ℂ := Complex.exp (3 * Real.pi * Complex.I * τ) with hQ3_def
  set Q4 : ℂ := Complex.exp (4 * Real.pi * Complex.I * τ) with hQ4_def
  set Q6 : ℂ := Complex.exp (6 * Real.pi * Complex.I * τ) with hQ6_def
  set rq : ℝ := Real.exp (-Real.pi * τ.im) with hrq_def
  have hrq_pos : 0 < rq := Real.exp_pos _
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hq_norm : ‖q‖ = rq := by
    rw [hq_def, Complex.norm_exp, hrq_def]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ : ℂ) = ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by
      ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  have hQ2_eq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ3_eq : Q3 = q^3 := by
    rw [hQ3_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ4_eq : Q4 = q^4 := by
    rw [hQ4_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ6_eq : Q6 = q^6 := by
    rw [hQ6_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- exp(π) > 16, so rq < 1/16.
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]; nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have hrq_le_eneg : rq ≤ Real.exp (-Real.pi) := by
    rw [hrq_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_pi_gt_16
  have hrq_lt : rq < 1/16 := lt_of_le_of_lt hrq_le_eneg h_exp_neg_pi_lt
  have hrq_lt_one : rq < 1 := by linarith
  have hrq_le_one : rq ≤ 1 := hrq_lt_one.le
  have hrq2_pos : 0 < rq^2 := by positivity
  have hrq3_pos : 0 < rq^3 := by positivity
  have hrq3_nn : 0 ≤ rq^3 := hrq3_pos.le
  have hrq4_pos : 0 < rq^4 := by positivity
  have hrq4_eq : rq^4 = Real.exp (-4 * Real.pi * τ.im) := by
    rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- A := 2 exp(πi τ/4); A⁴ = 16q.
  set A : ℂ := 2 * Complex.exp (Real.pi * Complex.I * τ / 4) with hA_def
  have hA_pow : A^4 = 16 * q := by
    rw [hA_def, hq_def, mul_pow]
    rw [show (Complex.exp (Real.pi * Complex.I * τ / 4))^4 =
        Complex.exp (4 * (Real.pi * Complex.I * τ / 4)) from by
      rw [← Complex.exp_nat_mul]; norm_cast]
    rw [show (4 : ℂ) * (Real.pi * Complex.I * τ / 4) = Real.pi * Complex.I * τ from by ring]
    norm_num
  have hA_norm : ‖A‖ = 2 * Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [hA_def, norm_mul, Complex.norm_exp]
    have h_re : (Real.pi * Complex.I * τ / 4 : ℂ).re = -(Real.pi * τ.im / 4) := by
      have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
          ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
      rw [h_eq, Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [h_re]; simp
  have hA_pow_norm : ‖A^4‖ = 16 * rq := by
    rw [hA_pow, norm_mul, hq_norm]; simp
  have hA_norm_pos : 0 < ‖A‖ := by rw [hA_norm]; positivity
  have hA_ne : A ≠ 0 := norm_ne_zero_iff.mp hA_norm_pos.ne'
  -- r₂', r₃' bounds.
  set r₂' : ℂ := (theta2 τ - A * (1 + Q2 + Q6)) / A with hr2_def
  set r₃' : ℂ := theta3 τ - 1 - 2 * q - 2 * Q4 with hr3_def
  have hr2_bound : ‖r₂'‖ ≤ 4 * rq^12 := by
    rw [hr2_def, norm_div, hA_norm]
    have h_denom_pos : 0 < 2 * Real.exp (-(Real.pi * τ.im / 4)) := by positivity
    rw [div_le_iff₀ h_denom_pos]
    have hrq12_eq : rq^12 = Real.exp (-(12 * Real.pi * τ.im)) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h_target_eq : 4 * rq^12 * (2 * Real.exp (-(Real.pi * τ.im / 4))) =
        8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := by
      rw [hrq12_eq]
      rw [show (4 * Real.exp (-(12 * Real.pi * τ.im)) *
          (2 * Real.exp (-(Real.pi * τ.im / 4))) : ℝ) =
          8 * (Real.exp (-(12 * Real.pi * τ.im)) *
            Real.exp (-(Real.pi * τ.im / 4))) from by ring]
      rw [← Real.exp_add]
      exact congr_arg (fun x => 8 * Real.exp x) (by ring)
    rw [h_target_eq]
    have h_eq_A : A * (1 + Q2 + Q6) =
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
            Complex.exp (6 * Real.pi * Complex.I * τ)) := by
      rw [hA_def, hQ2_def, hQ6_def]
    rw [h_eq_A]
    exact theta2_norm_sub_three_term_le_of_im_ge_one hτ
  have hr3_bound : ‖r₃'‖ ≤ 4 * rq^9 := by
    rw [hr3_def, hq_def, hQ4_def]
    have hrq9_eq : rq^9 = Real.exp (-9 * Real.pi * τ.im) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hrq9_eq]
    exact theta3_sub_one_minus_2q_minus_2q4_norm_le_of_im_ge_one hτ
  have hr2_loose : ‖r₂'‖ ≤ rq^3 := by
    refine hr2_bound.trans ?_
    have h_4rq9_le : (4 : ℝ) * rq^9 ≤ 1 := by
      have h1 : rq^9 ≤ (1/16 : ℝ)^9 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h2 : ((1/16:ℝ))^9 ≤ 1/4 := by norm_num
      linarith
    have h_eq : (4 : ℝ) * rq^12 = (4 * rq^9) * rq^3 := by ring
    rw [h_eq]
    calc (4 * rq^9) * rq^3 ≤ 1 * rq^3 := mul_le_mul_of_nonneg_right h_4rq9_le hrq3_nn
      _ = rq^3 := one_mul _
  have hr3_loose : ‖r₃'‖ ≤ rq^3 := by
    refine hr3_bound.trans ?_
    have h_4rq6_le : (4 : ℝ) * rq^6 ≤ 1 := by
      have h1 : rq^6 ≤ (1/16 : ℝ)^6 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h2 : ((1/16:ℝ))^6 ≤ 1/4 := by norm_num
      linarith
    have h_eq : (4 : ℝ) * rq^9 = (4 * rq^6) * rq^3 := by ring
    rw [h_eq]
    calc (4 * rq^6) * rq^3 ≤ 1 * rq^3 := mul_le_mul_of_nonneg_right h_4rq6_le hrq3_nn
      _ = rq^3 := one_mul _
  -- θ₂ = A(1+Q2+Q6+r₂'); θ₃ = 1+2q+2Q4+r₃'.
  have h_th2_eq : theta2 τ = A * (1 + Q2 + Q6 + r₂') := by
    rw [hr2_def]; field_simp
    ring
  have h_th3_eq : theta3 τ = 1 + 2 * q + 2 * Q4 + r₃' := by rw [hr3_def]; ring
  -- ‖D‖ ≥ 1/2 (using θ₃ norm bound).
  have h_th3_norm_ge := theta3_norm_ge_half_of_im_ge_one hτ
  have h_th3_norm_ge' : (1/2 : ℝ) ≤ ‖(1 + 2*q + 2*Q4 + r₃' : ℂ)‖ := by
    rw [← h_th3_eq]; exact h_th3_norm_ge
  have h_th3_pos : 0 < ‖(1 + 2*q + 2*Q4 + r₃' : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_th3_norm_ge'
  have h_th3_ne : (1 + 2*q + 2*Q4 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp h_th3_pos.ne'
  -- λ formula.
  have h_lambda_eq : modularLambdaH τ =
      A^4 * ((1 + Q2 + Q6 + r₂') / (1 + 2*q + 2*Q4 + r₃'))^4 := by
    unfold modularLambdaH
    rw [h_th2_eq, h_th3_eq, mul_pow, div_pow]; ring
  rw [h_lambda_eq]
  -- Substitute 16q = A^4, 128 Q2 = 8q A⁴, 704 Q3 = 44q² A⁴.
  rw [show (16 * Complex.exp (Real.pi * Complex.I * τ) : ℂ) = A^4 from hA_pow.symm]
  rw [show (128 * Complex.exp (2 * Real.pi * Complex.I * τ) : ℂ) = 8 * q * A^4 from by
    rw [show Complex.exp (2 * Real.pi * Complex.I * τ) = Q2 from rfl]
    rw [hA_pow, hQ2_eq]; ring]
  rw [show (704 * Complex.exp (3 * Real.pi * Complex.I * τ) : ℂ) = 44 * q^2 * A^4 from by
    rw [show Complex.exp (3 * Real.pi * Complex.I * τ) = Q3 from rfl]
    rw [hA_pow, hQ3_eq]; ring]
  -- Factor out A^4.
  rw [show (A^4 * ((1 + Q2 + Q6 + r₂') / (1 + 2*q + 2*Q4 + r₃'))^4 - A^4 +
      8 * q * A^4 - 44 * q^2 * A^4 : ℂ) =
      A^4 * (((1 + Q2 + Q6 + r₂') / (1 + 2*q + 2*Q4 + r₃'))^4 - 1 + 8 * q - 44 * q^2) from
        by ring]
  rw [norm_mul, hA_pow_norm]
  -- Convert Q^k to q^k in the bracket.
  rw [hQ2_eq, hQ4_eq, hQ6_eq]
  -- ‖D‖ ≥ 1/2 in q^4 form.
  have hD_norm_q : (1/2 : ℝ) ≤ ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by
    rw [show (1 + 2*q + 2*q^4 + r₃' : ℂ) = 1 + 2*q + 2*Q4 + r₃' from by rw [hQ4_eq]]
    exact h_th3_norm_ge'
  -- Set v.
  set v : ℂ := (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1 with hv_def
  rw [show ((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃')) = 1 + v from by
    rw [hv_def]; ring]
  -- Apply algebraic identity.
  rw [modularLambda_three_term_bracket_identity v q]
  -- Apply helpers.
  have hv_bound : ‖v‖ ≤ 6 * rq :=
    modularLambda_three_term_v_bound q r₂' r₃' rq hq_norm hrq_pos hrq_lt
      hr2_loose hr3_loose hD_norm_q
  have hs_bound : ‖v + 2*q - 5*q^2‖ ≤ 64 * rq^3 :=
    modularLambda_three_term_s_bound q r₂' r₃' rq hq_norm hrq_pos hrq_lt
      hr2_loose hr3_loose hD_norm_q
  -- Bound each bracket term.
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q3_norm : ‖q^3‖ = rq^3 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  -- ‖-120 q^3‖ = 120 rq^3.
  have h_120q3_norm : ‖(-120 * q^3 : ℂ)‖ = 120 * rq^3 := by
    rw [show ((-120 * q^3 : ℂ)) = (((-120 : ℝ) : ℂ)) * q^3 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q3_norm]; simp
  -- ‖(4 − 24q + 60q²)‖ ≤ 6.
  have h_coeff_norm_le : ‖((4 : ℂ) - 24*q + 60*q^2)‖ ≤ 6 := by
    have h_24q : ‖((24 : ℂ) * q)‖ = 24 * rq := by
      rw [show ((24 * q : ℂ)) = (((24 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_60q2 : ‖((60 : ℂ) * q^2)‖ = 60 * rq^2 := by
      rw [show ((60 * q^2 : ℂ)) = (((60 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, h_q2_norm]; simp
    have h_4_norm : ‖(4 : ℂ)‖ = 4 := by simp
    have h_24rq : 24 * rq ≤ 24/16 := by linarith
    have h_60rq2 : 60 * rq^2 ≤ 60/256 := by
      have h_rq2 : rq^2 ≤ 1/256 := by
        have h_step : rq^2 = rq * rq := by ring
        rw [h_step]
        calc rq * rq ≤ (1/16) * (1/16 : ℝ) :=
              mul_le_mul hrq_lt.le hrq_lt.le hrq_nn (by norm_num)
          _ = 1/256 := by norm_num
      linarith
    have h_add := norm_add_le ((4 : ℂ) - 24*q) (60*q^2)
    have h_sub := norm_sub_le ((4 : ℂ)) (24*q)
    linarith [h_add, h_sub, h_24q, h_60q2, h_4_norm, h_24rq, h_60rq2]
  -- ‖(4 − 24q + 60q²)·s‖ ≤ 6 · 64 rq³ = 384 rq³.
  have h_coeff_s_le : ‖((4 : ℂ) - 24*q + 60*q^2) * (v + 2*q - 5*q^2)‖ ≤ 384 * rq^3 := by
    rw [norm_mul]
    have h_step : ‖((4 : ℂ) - 24*q + 60*q^2)‖ * ‖v + 2*q - 5*q^2‖ ≤ 6 * (64 * rq^3) :=
      mul_le_mul h_coeff_norm_le hs_bound (norm_nonneg _) (by norm_num)
    linarith
  -- ‖6 s²‖ ≤ 6 · (64 rq³)² = 24576 rq⁶ ≤ 6 rq³.
  have h_6s2_le : ‖(6 : ℂ) * (v + 2*q - 5*q^2)^2‖ ≤ 6 * rq^3 := by
    rw [norm_mul, norm_pow]
    have h_step1 : ‖v + 2*q - 5*q^2‖^2 ≤ (64 * rq^3)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hs_bound 2
    have h_simp : ((64 : ℝ) * rq^3)^2 = 4096 * rq^6 := by ring
    have h_6 : ‖((6 : ℂ))‖ = 6 := by simp
    rw [h_6]
    have h_chain : (6 : ℝ) * ‖v + 2*q - 5*q^2‖^2 ≤ 6 * (4096 * rq^6) := by
      calc (6 : ℝ) * ‖v + 2*q - 5*q^2‖^2 ≤ 6 * (64 * rq^3)^2 :=
            mul_le_mul_of_nonneg_left h_step1 (by norm_num)
        _ = 6 * (4096 * rq^6) := by rw [h_simp]
    -- 6 · 4096 · rq⁶ ≤ 6 · rq³? 4096 rq⁶ ≤ rq³ iff 4096 rq³ ≤ 1.
    -- rq³ ≤ 1/16³ = 1/4096. So 4096 rq³ ≤ 1. ✓
    have h_4096rq3 : (4096 : ℝ) * rq^3 ≤ 1 := by
      have h_rq3 : rq^3 ≤ (1/16 : ℝ)^3 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have hh : ((1/16:ℝ))^3 = 1/4096 := by norm_num
      linarith
    have h_4096_rq6_le_rq3 : (4096 : ℝ) * rq^6 ≤ rq^3 := by
      have h_eq : (4096 : ℝ) * rq^6 = (4096 * rq^3) * rq^3 := by ring
      rw [h_eq]
      calc (4096 * rq^3) * rq^3 ≤ 1 * rq^3 :=
            mul_le_mul_of_nonneg_right h_4096rq3 hrq3_nn
        _ = rq^3 := one_mul _
    linarith
  -- ‖150 q⁴‖ ≤ 10 rq³.
  have h_150q4_le : ‖((150 : ℂ) * q^4)‖ ≤ 10 * rq^3 := by
    rw [show ((150 * q^4 : ℂ)) = (((150 : ℝ) : ℂ)) * q^4 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q4_norm]
    simp only [Real.norm_ofNat]
    have h_step : (150 : ℝ) * rq^4 = (150 * rq) * rq^3 := by ring
    have h_150rq : (150 : ℝ) * rq ≤ 10 := by linarith
    rw [h_step]
    exact mul_le_mul_of_nonneg_right h_150rq hrq3_nn
  -- ‖4 v³‖ ≤ 4 · (6 rq)³ = 864 rq³.
  have h_4v3_le : ‖((4 : ℂ) * v^3)‖ ≤ 864 * rq^3 := by
    rw [norm_mul, norm_pow]
    have h_step1 : ‖v‖^3 ≤ (6 * rq)^3 := pow_le_pow_left₀ (norm_nonneg _) hv_bound 3
    have h_simp : (6 * rq)^3 = 216 * rq^3 := by ring
    have h_4 : ‖((4 : ℂ))‖ = 4 := by simp
    rw [h_4]
    have h_chain : (4 : ℝ) * ‖v‖^3 ≤ 864 * rq^3 := by
      have h_a : (4 : ℝ) * ‖v‖^3 ≤ 4 * (6 * rq)^3 :=
        mul_le_mul_of_nonneg_left h_step1 (by norm_num)
      have h_b : (4 : ℝ) * (6 * rq)^3 = 864 * rq^3 := by rw [h_simp]; ring
      linarith
    exact h_chain
  -- ‖v⁴‖ ≤ 1296 rq⁴ ≤ 81 rq³.
  have h_v4_le : ‖v^4‖ ≤ 81 * rq^3 := by
    rw [norm_pow]
    have h_step1 : ‖v‖^4 ≤ (6 * rq)^4 := pow_le_pow_left₀ (norm_nonneg _) hv_bound 4
    have h_simp : (6 * rq)^4 = 1296 * rq^4 := by ring
    -- 1296 rq^4 ≤ 81 rq^3 iff 1296 rq ≤ 81 iff rq ≤ 81/1296 = 1/16. ✓
    have h_1296rq : (1296 : ℝ) * rq ≤ 81 := by linarith
    have h_chain : (1296 : ℝ) * rq^4 ≤ 81 * rq^3 := by
      have h_eq : (1296 : ℝ) * rq^4 = (1296 * rq) * rq^3 := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_right h_1296rq hrq3_nn
    linarith [h_step1, h_simp.le, h_chain]
  -- Combine: bracket ≤ 120 + 384 + 6 + 10 + 864 + 81 = 1465 rq³.
  have h_bracket_bound : ‖(-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
      6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ)‖ ≤ 1465 * rq^3 := by
    have h_eq : (-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
        6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ) =
        ((((((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
            6 * (v + 2*q - 5*q^2)^2) + 150 * q^4) + 4 * v^3) + v^4) := by ring
    rw [h_eq]
    have h1 := norm_add_le (((((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
        6 * (v + 2*q - 5*q^2)^2) + 150 * q^4) + 4 * v^3) (v^4)
    have h2 := norm_add_le ((((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
        6 * (v + 2*q - 5*q^2)^2) + 150 * q^4) (4 * v^3)
    have h3 := norm_add_le (((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
        6 * (v + 2*q - 5*q^2)^2) (150 * q^4)
    have h4 := norm_add_le ((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2))
        (6 * (v + 2*q - 5*q^2)^2)
    have h5 := norm_add_le (-120 * q^3) ((4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2))
    linarith [h1, h2, h3, h4, h5, h_120q3_norm.le, h_coeff_s_le, h_6s2_le,
              h_150q4_le, h_4v3_le, h_v4_le]
  -- 16 rq · ‖bracket‖ ≤ 16 rq · 1465 rq³ = 23440 rq⁴ ≤ 32768 rq⁴.
  have h_step : (16 * rq) * ‖(-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
      6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ)‖ ≤ 23440 * rq^4 := by
    have h_mul : (16 * rq) * ‖(-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
        6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ)‖ ≤
        (16 * rq) * (1465 * rq^3) :=
      mul_le_mul_of_nonneg_left h_bracket_bound (by positivity)
    have h_eq : (16 : ℝ) * rq * (1465 * rq^3) = 23440 * rq^4 := by ring
    linarith
  have h_final : 23440 * rq^4 ≤ 32768 * Real.exp (-4 * Real.pi * τ.im) := by
    rw [← hrq4_eq]
    have h_pos : 0 ≤ rq^4 := by positivity
    linarith
  linarith [h_step, h_final]

/-- `‖θ₃(τ) − θ₄(τ)‖ ≤ 100 · exp(−π·τ.im)` for `τ.im ≥ 1`. The
constant terms `1` in `θ₃` and `θ₄` cancel, leaving the leading-`q¹`
piece `4q + O(q⁹)`; this gives full `exp(−π·τ.im)` decay. -/
theorem theta3_sub_theta4_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - theta4 τ‖ ≤ 100 * Real.exp (-Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  have hτ1_im : (τ + 1).im = τ.im := by simp [Complex.add_im]
  have hτ1_im_pos : 0 < (τ + 1).im := by rw [hτ1_im]; exact hτim_pos
  -- Mathlib bound at τ and at τ + 1.
  have h_at_τ : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτim_pos
  have h_at_τ1 : ‖jacobiTheta (τ + 1) - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * (τ + 1).im)) * Real.exp (-Real.pi * (τ + 1).im) :=
    norm_jacobiTheta_sub_one_le hτ1_im_pos
  rw [hτ1_im] at h_at_τ1
  -- exp(-π·τ.im) ≤ exp(-π) < 1/2; hence (1 - exp(-π·τ.im)) ≥ 1/2.
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have h_exp_lt_half : Real.exp (-Real.pi * τ.im) < 1/2 :=
    lt_of_le_of_lt h_exp_at_one h_exp_neg_pi_lt_half
  have h_one_sub_ge : 1/2 ≤ 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_one_sub_pos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_quot_le : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 4 := by
    rw [div_le_iff₀ h_one_sub_pos]; linarith
  -- Each ‖θᵢ - 1‖ ≤ 4 · exp(-π·τ.im).
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im) := Real.exp_pos _
  have h_th3_sub_one : ‖jacobiTheta τ - 1‖ ≤ 4 * Real.exp (-Real.pi * τ.im) :=
    h_at_τ.trans (mul_le_mul_of_nonneg_right h_quot_le h_exp_pos.le)
  have h_th4_sub_one : ‖jacobiTheta (τ + 1) - 1‖ ≤ 4 * Real.exp (-Real.pi * τ.im) :=
    h_at_τ1.trans (mul_le_mul_of_nonneg_right h_quot_le h_exp_pos.le)
  -- θ₃ - θ₄ = (θ₃ - 1) - (θ₄ - 1) = (jacobiTheta τ - 1) - (jacobiTheta(τ+1) - 1).
  unfold theta3 theta4
  calc ‖jacobiTheta τ - jacobiTheta (τ + 1)‖
      = ‖(jacobiTheta τ - 1) - (jacobiTheta (τ + 1) - 1)‖ := by congr 1; ring
    _ ≤ ‖jacobiTheta τ - 1‖ + ‖jacobiTheta (τ + 1) - 1‖ := norm_sub_le _ _
    _ ≤ 4 * Real.exp (-Real.pi * τ.im) + 4 * Real.exp (-Real.pi * τ.im) := by
        linarith
    _ ≤ 100 * Real.exp (-Real.pi * τ.im) := by nlinarith

/-- **Jacobi-difference cusp bound.** The squared Jacobi difference
`f² = (θ₂⁴ + θ₄⁴ − θ₃⁴)²` decays exponentially at the cusp `+i∞`.
The proof chains the four norm bounds: `‖θ₂⁴‖ ≤ 10⁴·exp(−π·τ.im)`
from `theta2_norm_le_of_im_ge_one`, and
`‖θ₃⁴ − θ₄⁴‖ ≤ 4·10⁵·exp(−π·τ.im)` from the factorisation
`θ₃⁴ − θ₄⁴ = (θ₃ − θ₄)(θ₃³ + θ₃²θ₄ + θ₃θ₄² + θ₄³)` together with
`theta3_sub_theta4_norm_le_of_im_ge_one` and the `θ₃/θ₄` bounds. -/
theorem jacobi_diff_sq_cusp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℂ, 1 ≤ τ.im →
      ‖(theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2‖
        ≤ C * Real.exp (-Real.pi * τ.im) := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro τ hτim
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτim
  have hπ_pos := Real.pi_pos
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im) := Real.exp_pos _
  have h_exp_nn : 0 ≤ Real.exp (-Real.pi * τ.im) := h_exp_pos.le
  have h_exp_le_one : Real.exp (-Real.pi * τ.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  -- Apply the four helpers.
  have h2 := theta2_norm_le_of_im_ge_one hτim
  have h3 := theta3_norm_le_of_im_ge_one hτim
  have h4 := theta4_norm_le_of_im_ge_one hτim
  have h34 := theta3_sub_theta4_norm_le_of_im_ge_one hτim
  -- `‖θ₂⁴‖ ≤ 10000 · exp(−π·τ.im)`.
  have h2_pow4 : ‖theta2 τ ^ 4‖ ≤ 10000 * Real.exp (-Real.pi * τ.im) := by
    rw [norm_pow]
    have h_pow_le : ‖theta2 τ‖ ^ 4 ≤ (10 * Real.exp (-Real.pi * τ.im / 4)) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 4
    refine h_pow_le.trans (le_of_eq ?_)
    rw [mul_pow]
    have h_exp_pow : (Real.exp (-Real.pi * τ.im / 4)) ^ 4 = Real.exp (-Real.pi * τ.im) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h_exp_pow]
    norm_num
  -- `‖θᵢ‖ ^ k ≤ 10 ^ k` for k = 1, 2, 3.
  have hn3 : (0 : ℝ) ≤ ‖theta3 τ‖ := norm_nonneg _
  have hn4 : (0 : ℝ) ≤ ‖theta4 τ‖ := norm_nonneg _
  have h3_pow3 : ‖theta3 τ‖ ^ 3 ≤ 1000 := by
    calc ‖theta3 τ‖ ^ 3 ≤ (10 : ℝ) ^ 3 := pow_le_pow_left₀ hn3 h3 3
      _ = 1000 := by norm_num
  have h3_pow2 : ‖theta3 τ‖ ^ 2 ≤ 100 := by
    calc ‖theta3 τ‖ ^ 2 ≤ (10 : ℝ) ^ 2 := pow_le_pow_left₀ hn3 h3 2
      _ = 100 := by norm_num
  have h4_pow3 : ‖theta4 τ‖ ^ 3 ≤ 1000 := by
    calc ‖theta4 τ‖ ^ 3 ≤ (10 : ℝ) ^ 3 := pow_le_pow_left₀ hn4 h4 3
      _ = 1000 := by norm_num
  have h4_pow2 : ‖theta4 τ‖ ^ 2 ≤ 100 := by
    calc ‖theta4 τ‖ ^ 2 ≤ (10 : ℝ) ^ 2 := pow_le_pow_left₀ hn4 h4 2
      _ = 100 := by norm_num
  -- `‖θ₃³ + θ₃²θ₄ + θ₃θ₄² + θ₄³‖ ≤ 4000`.
  have h_quart_norm :
      ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2 + theta4 τ ^ 3‖
        ≤ 4000 := by
    have h_a : ‖theta3 τ ^ 3‖ ≤ 1000 := by rw [norm_pow]; exact h3_pow3
    have h_b : ‖theta3 τ ^ 2 * theta4 τ‖ ≤ 1000 := by
      rw [norm_mul, norm_pow]
      have := mul_le_mul h3_pow2 h4 hn4 (by norm_num : (0:ℝ) ≤ 100)
      linarith
    have h_c : ‖theta3 τ * theta4 τ ^ 2‖ ≤ 1000 := by
      rw [norm_mul, norm_pow]
      have := mul_le_mul h3 h4_pow2 (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 10)
      linarith
    have h_d : ‖theta4 τ ^ 3‖ ≤ 1000 := by rw [norm_pow]; exact h4_pow3
    have h_add1 :
        ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2 + theta4 τ ^ 3‖
          ≤ ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2‖
              + ‖theta4 τ ^ 3‖ := norm_add_le _ _
    have h_add2 :
        ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2‖
          ≤ ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ‖ + ‖theta3 τ * theta4 τ ^ 2‖ :=
      norm_add_le _ _
    have h_add3 :
        ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ‖
          ≤ ‖theta3 τ ^ 3‖ + ‖theta3 τ ^ 2 * theta4 τ‖ := norm_add_le _ _
    linarith
  -- `‖θ₃⁴ − θ₄⁴‖ = ‖(θ₃ − θ₄)·(θ₃³ + θ₃²θ₄ + θ₃θ₄² + θ₄³)‖ ≤ 100·exp(−π·τ.im)·4000`.
  have h_diff_eq : theta3 τ ^ 4 - theta4 τ ^ 4
      = (theta3 τ - theta4 τ)
        * (theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ
            + theta3 τ * theta4 τ ^ 2 + theta4 τ ^ 3) := by ring
  have h_diff_norm :
      ‖theta3 τ ^ 4 - theta4 τ ^ 4‖
        ≤ 100 * Real.exp (-Real.pi * τ.im) * 4000 := by
    rw [h_diff_eq, norm_mul]
    exact mul_le_mul h34 h_quart_norm (norm_nonneg _)
      (by positivity)
  -- `‖f‖ ≤ ‖θ₂⁴‖ + ‖θ₃⁴ − θ₄⁴‖ ≤ 410000·exp(−π·τ.im)`.
  have h_f_decomp : theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4
      = theta2 τ ^ 4 - (theta3 τ ^ 4 - theta4 τ ^ 4) := by ring
  have h_f_norm :
      ‖theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4‖
        ≤ 410000 * Real.exp (-Real.pi * τ.im) := by
    rw [h_f_decomp]
    have h_step : ‖theta2 τ ^ 4 - (theta3 τ ^ 4 - theta4 τ ^ 4)‖
        ≤ ‖theta2 τ ^ 4‖ + ‖theta3 τ ^ 4 - theta4 τ ^ 4‖ := norm_sub_le _ _
    have h_sum :
        10000 * Real.exp (-Real.pi * τ.im) + 100 * Real.exp (-Real.pi * τ.im) * 4000
          = 410000 * Real.exp (-Real.pi * τ.im) := by ring
    linarith
  -- `‖f²‖ = ‖f‖² ≤ (410000)²·exp(−2π·τ.im) ≤ 10¹²·exp(−π·τ.im)`.
  rw [norm_pow]
  have h_sq_le : ‖theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4‖ ^ 2
      ≤ (410000 * Real.exp (-Real.pi * τ.im)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h_f_norm 2
  refine h_sq_le.trans ?_
  rw [mul_pow]
  -- `exp(−π·τ.im)^2 = exp(−π·τ.im) · exp(−π·τ.im) ≤ exp(−π·τ.im) · 1`.
  have h_exp_sq : (Real.exp (-Real.pi * τ.im)) ^ 2
      ≤ Real.exp (-Real.pi * τ.im) := by
    rw [sq]
    nlinarith
  have h_410k_sq_pos : (0 : ℝ) ≤ (410000 : ℝ) ^ 2 := by positivity
  have h_step1 :
      (410000 : ℝ) ^ 2 * (Real.exp (-Real.pi * τ.im)) ^ 2
        ≤ (410000 : ℝ) ^ 2 * Real.exp (-Real.pi * τ.im) :=
    mul_le_mul_of_nonneg_left h_exp_sq h_410k_sq_pos
  refine h_step1.trans ?_
  -- `(410000)² ≤ 10¹²`.
  have h_const_le : (410000 : ℝ) ^ 2 ≤ 10 ^ 12 := by norm_num
  exact mul_le_mul_of_nonneg_right h_const_le h_exp_nn

/-- **Weight-4 cusp form vanishing principle** (architectural). A
holomorphic function `g` on the upper half-plane that is
`T`-invariant (`g(τ + 1) = g(τ)`), transforms under `S` with
weight 4 (`g(−1/τ) = τ⁴ · g(τ)`), and decays exponentially at the
cusp `+i∞` must be identically zero on `ℍ`.

**Mathematical content.** The space `S_4(SL(2, ℤ))` of weight-4
cusp forms for the full modular group is zero-dimensional.
A concrete proof uses the `Δ`-division route: given a weight-4
cusp form `g`, the quotient `g² / Δ` is a weight `8 − 12 = −4`
modular form (since `g²` has weight 8, vanishes to order ≥ 2 at
the cusp, while `Δ` has weight 12 and vanishes to order exactly 1
at the cusp; the quotient is holomorphic on `ℍ` because Mathlib's
`delta_ne_zero` holds, and bounded at the cusp because `2 − 1 ≥ 1`).
By Mathlib's `levelOne_neg_weight_eq_zero` (a negative-weight
modular form for `SL(2, ℤ)` is identically zero), `g² / Δ = 0`,
hence `g = 0`.

**Mathlib gaps for closing this lemma.**
1. Bridging the bare `ℂ → ℂ` hypotheses to a Mathlib
   `CuspForm Γ(1) 4`. The `T` and `S` invariance hypotheses give
   slash invariance on the two generators; the full
   `SlashInvariantForm Γ(1) 4` slash invariance is obtained via
   `SpecialLinearGroup.SL2Z_generators` + `Subgroup.closure_induction`
   (the pattern used in Mathlib's `EisensteinSeries.E2.Transform`).
2. Bridging Mathlib's `delta : ℍ → ℂ` to a packaged `CuspForm Γ(1) 12`.
   Mathlib has `delta_T_invariant`, `delta_S_invariant`,
   `delta_ne_zero`, but the bundled cusp-form instance is not yet
   exposed.
3. Constructing the quotient `g² / Δ` as a `ModularForm Γ(1) (−4)`
   from the two packaged forms (no Mathlib API for modular-form
   division; needs custom construction).
4. The endpoint `levelOne_neg_weight_eq_zero` is in Mathlib and
   directly applies once the quotient is packaged.

All four are tractable but multi-session formalization tasks. -/
theorem holomorphic_weight4_modform_cusp_vanishes
    {g : ℂ → ℂ}
    (h_holo : DifferentiableOn ℂ g { τ : ℂ | 0 < τ.im })
    (h_T : ∀ τ : ℂ, 0 < τ.im → g (τ + 1) = g τ)
    (h_S : ∀ τ : ℂ, 0 < τ.im → g (-1 / τ) = τ ^ 4 * g τ)
    (h_cusp : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℂ, 1 ≤ τ.im →
        ‖g τ‖ ≤ C * Real.exp (-Real.pi * τ.im))
    {τ : ℂ} (hτ : 0 < τ.im) :
    g τ = 0 := by
  -- The bridge constructs a `CuspForm Γ(1) 4` from the bare hypotheses
  -- and applies the weight-4 vanishing principle. Concretely:
  -- (a) `g_H := fun σ : ℍ => g σ` is `T`-, `S`-, and SL(2,ℤ)-slash-invariant
  --     of weight 4 (via the bridge `slash_T_eq_of_T_invariant`,
  --     `slash_S_eq_of_S_weight_k`, and `slashInvariant_via_S_T_in_SL2Z`);
  -- (b) `g_H` is `MDiff` (via `mdiff_of_differentiableOn_upperHalfPlane`);
  -- (c) `g_H` vanishes at `+i∞` (via `isZeroAtImInfty_of_exp_decay`);
  --     by `OnePoint.isZeroAt_iff_forall_SL2Z`, this extends to all cusps
  --     using slash invariance.
  -- Then `CuspForm.mk g_H ... : CuspForm Γ(1) 4`, and
  -- `weight4_levelOne_cuspForm_vanishes` gives `g_H = 0`, hence `g τ = 0`.
  set g_H : UpperHalfPlane → ℂ := fun σ => g (↑σ : ℂ) with hg_H_def
  -- Slash invariance under T, S, and the full SL(2, ℤ).
  have h_T_slash : g_H ∣[(4 : ℤ)] ModularGroup.T = g_H :=
    slash_T_eq_of_T_invariant h_T
  have h_S_slash : g_H ∣[(4 : ℤ)] ModularGroup.S = g_H :=
    slash_S_eq_of_S_weight_k h_S
  have h_slash_SL : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g_H ∣[(4 : ℤ)] γ = g_H := fun γ =>
    slashInvariant_via_S_T_in_SL2Z h_S_slash h_T_slash γ
  -- Manifold differentiability and cusp vanishing.
  have h_mdiff : MDiff g_H := mdiff_of_differentiableOn_upperHalfPlane h_holo
  have h_zero : IsZeroAtImInfty g_H := isZeroAtImInfty_of_exp_decay h_cusp
  -- Bundle as a CuspForm Γ(1) 4.
  let F : CuspForm Γ(1) 4 :=
  { toFun := g_H
    slash_action_eq' := by
      intro γ_GL hγ_GL
      obtain ⟨g_SL, _hg_SL_mem, h_eq⟩ := hγ_GL
      have h := h_slash_SL g_SL
      rw [ModularForm.SL_slash] at h
      rw [← h_eq]
      exact h
    holo' := h_mdiff
    zero_at_cusps' := by
      intro c hc
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
      intro γ _hγ
      rw [h_slash_SL γ]
      exact h_zero }
  -- Apply the bridge's `weight4_levelOne_cuspForm_vanishes`.
  have h_F_zero : F ⟨τ, hτ⟩ = 0 := weight4_levelOne_cuspForm_vanishes F ⟨τ, hτ⟩
  -- `F ⟨τ, hτ⟩ = g_H ⟨τ, hτ⟩ = g τ` by definition.
  exact h_F_zero

/-- **Jacobi's identity**: `θ₂(τ)⁴ + θ₄(τ)⁴ = θ₃(τ)⁴` on the upper
half-plane. Setting `g(τ) := (θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴)²`, the
proven transformations `jacobi_diff_sq_T_smul` and
`jacobi_diff_sq_S_smul` show `g` is a holomorphic, weight-4 modular
form for `SL(2, ℤ)`. The cusp bound `jacobi_diff_sq_cusp_bound`
shows `g` vanishes at `+i∞`. By the weight-4 cusp form vanishing
principle (`holomorphic_weight4_modform_cusp_vanishes`),
`g ≡ 0`; hence `f ≡ 0` and Jacobi's identity follows. -/
theorem jacobi_identity {τ : ℂ} (hτ : 0 < τ.im) :
    theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := by
  have h_zero : (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2 = 0 :=
    holomorphic_weight4_modform_cusp_vanishes
      (g := fun σ => (theta2 σ ^ 4 + theta4 σ ^ 4 - theta3 σ ^ 4) ^ 2)
      jacobi_diff_sq_differentiableOn
      (fun σ _ => jacobi_diff_sq_T_smul σ)
      (fun σ hσ => jacobi_diff_sq_S_smul hσ)
      jacobi_diff_sq_cusp_bound
      hτ
  have h_diff_zero : theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4 = 0 :=
    (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h_zero
  linear_combination h_diff_zero

/-! ## Non-vanishing of `θ₂`, `θ₃`, `θ₄` on `ℍ`

The full-ℍ non-vanishing theorems `theta2_ne_zero`, `theta3_ne_zero`,
`theta4_ne_zero` are proved later in this file (after the half-regime
lemmas and the SL(2,ℤ)-reduction infrastructure). They are obtained by
combining the easy-regime non-vanishing (`theta_i_ne_zero_of_im_ge_half`)
with the SL(2,ℤ)-invariance of the predicate `all_theta_ne_zero`. -/

/-- For `τ` with imaginary part at least one, the bound
`‖jacobiTheta τ − 1‖ ≤ 2·exp(−π·τ.im)/(1 − exp(−π·τ.im))` is strictly less
than one (since `exp(−π) < 1/3`), so `jacobiTheta τ ≠ 0`. This is the
easy regime of the general non-vanishing claim. -/
theorem theta3_ne_zero_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    theta3 τ ≠ 0 := by
  unfold theta3
  have hτ_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have h_bound : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτ_pos
  -- Let x = exp(-π · τ.im); show x < 1/3, hence 2x/(1-x) < 1.
  set x := Real.exp (-Real.pi * τ.im) with hx_def
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_x_pos : 0 < x := Real.exp_pos _
  have h_x_le : x ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_exp_neg_pi : Real.exp (-Real.pi) < 1 / 3 := by
    have h_pi : 3 < Real.pi := Real.pi_gt_three
    have h_exp_3 : (3 : ℝ) < Real.exp 3 := by
      have h1 : (3 : ℝ) + 1 ≤ Real.exp 3 := Real.add_one_le_exp 3
      linarith
    have h_exp_pi : Real.exp 3 < Real.exp Real.pi := Real.exp_lt_exp.mpr h_pi
    have h3_lt_exp_pi : (3 : ℝ) < Real.exp Real.pi := lt_trans h_exp_3 h_exp_pi
    have h_exp_pi_pos : 0 < Real.exp Real.pi := Real.exp_pos _
    rw [Real.exp_neg, inv_lt_comm₀ h_exp_pi_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    rw [show (1 / 3 : ℝ)⁻¹ = 3 from by norm_num]
    exact h3_lt_exp_pi
  have h_x_lt_third : x < 1 / 3 := lt_of_le_of_lt h_x_le h_exp_neg_pi
  have h_one_sub_x_pos : 0 < 1 - x := by linarith
  have h_bound_lt_one : 2 / (1 - x) * x < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h_one_sub_x_pos]
    linarith
  have h_norm_lt : ‖jacobiTheta τ - 1‖ < 1 := lt_of_le_of_lt h_bound h_bound_lt_one
  intro h_zero
  rw [h_zero, zero_sub, norm_neg, norm_one] at h_norm_lt
  exact lt_irrefl 1 h_norm_lt

/-- Easy-regime non-vanishing for `θ₄`. Reduces to
`theta3_ne_zero_of_im_ge_one` via `θ₄ τ = θ₃ (τ + 1)` and the fact that
`Im(τ + 1) = Im τ`. -/
theorem theta4_ne_zero_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    theta4 τ ≠ 0 := by
  rw [show theta4 τ = theta3 (τ + 1) from (theta3_add_one τ).symm]
  apply theta3_ne_zero_of_im_ge_one
  simp [Complex.add_im, hτ]

/-- **Easy-regime non-vanishing for `θ₂`.** For `τ.im ≥ 1`,
`θ₂(τ) = exp(πiτ/4) · jacobiTheta₂(τ/2, τ)`, where the leading two
terms of `jacobiTheta₂(τ/2, τ)` at `n = 0, −1` both equal `1`, giving
`jacobiTheta₂(τ/2, τ) = 2 + r(τ)`. The remainder is bounded by the
geometric series `2·s/(1 − s) ≤ 1` where `s = exp(−2π·τ.im) ≤ 1/3`
(via `Real.add_one_le_exp 2 ⇒ exp(2π) ≥ 3`), so
`‖jacobiTheta₂(τ/2, τ)‖ ≥ 2 − 1 = 1 > 0` and `θ₂ ≠ 0` since
`exp(πiτ/4) ≠ 0`. -/
theorem theta2_ne_zero_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    theta2 τ ≠ 0 := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- `s = exp(−2π·τ.im) ≤ 1/3` for τ.im ≥ 1.
  set s : ℝ := Real.exp (-2 * Real.pi * τ.im) with hs_def
  have hs_pos : 0 < s := Real.exp_pos _
  have hs_le_third : s ≤ 1/3 := by
    rw [hs_def, show (-2 * Real.pi * τ.im : ℝ) = -(2 * Real.pi * τ.im) from by ring,
        Real.exp_neg,
        inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/3),
        show (1/3 : ℝ)⁻¹ = 3 from by norm_num]
    have h_3_le_exp_2 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h_2_le_2piτ : (2 : ℝ) ≤ 2 * Real.pi * τ.im := by
      have h_pi_3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      have h_2pi_pos : 0 < 2 * Real.pi := by positivity
      nlinarith
    linarith [Real.exp_le_exp.mpr h_2_le_2piτ]
  have hs_lt_one : s < 1 := by linarith
  have h_one_sub_s_pos : 0 < 1 - s := by linarith
  -- 2·((1-s)⁻¹ - 1) ≤ 1.
  have h_int_sum_le_one : (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) ≤ 1 := by
    have h_inv_eq : (1 - s)⁻¹ - 1 = s / (1 - s) := by
      field_simp; ring
    rw [h_inv_eq]
    rw [show s/(1-s) + s/(1-s) = 2*s/(1-s) from by ring]
    rw [div_le_one h_one_sub_s_pos]; linarith
  -- HasSum for the (skipped) geometric series.
  have h_geo : HasSum (fun m : ℕ => s ^ m) ((1 - s)⁻¹) :=
    hasSum_geometric_of_lt_one hs_pos.le hs_lt_one
  have h_skip_geo : HasSum (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                          ((1 - s)⁻¹ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_geo 0
    simp only [pow_zero] at h_step
    exact h_step
  -- Sum over ℤ via Int.rec.
  have h_int_rec : HasSum
      (fun n : ℤ => Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                            (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n)
      ((1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1)) :=
    HasSum.int_rec h_skip_geo h_skip_geo
  -- HasSum for jacobiTheta₂ - 2, by skipping terms at n=0 and n=-1.
  have h_jt_hasSum := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_zim : (τ / 2 : ℂ).im = τ.im / 2 := by simp
  -- Show term_0 = 1 and term_{-1} = 1.
  have h_term_0 : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    simp [jacobiTheta₂_term]
  have h_term_neg1 : jacobiTheta₂_term (-1) (τ / 2) τ = 1 := by
    rw [jacobiTheta₂_term]
    have h_zero : 2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) * (τ/2)
        + (Real.pi : ℂ) * Complex.I * (((-1 : ℤ) : ℂ)) ^ 2 * τ = 0 := by
      push_cast; ring
    rw [h_zero]; exact Complex.exp_zero
  -- Skip n=0 from jacobiTheta₂.
  have h_skip_0 : HasSum
      (fun n : ℤ => if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_jt_hasSum 0
    rw [h_term_0] at h_step
    exact h_step
  -- Skip n=-1 from the result.
  have h_skip_both : HasSum
      (fun n : ℤ => if n = -1 then (0 : ℂ)
                    else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1 - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_skip_0 (-1)
    have h_at_neg1 :
        (if ((-1 : ℤ)) = 0 then (0 : ℂ) else jacobiTheta₂_term (-1) (τ / 2) τ) = 1 := by
      simp [h_term_neg1]
    rw [h_at_neg1] at h_step
    exact h_step
  -- Per-term norm bound.
  have h_term_bound : ∀ n : ℤ,
      ‖(if n = -1 then (0 : ℂ)
        else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)‖
        ≤ Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                  (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n := by
    intro n
    cases n with
    | ofNat m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.ofNat m : ℤ) ≠ -1 := by
          have h_nn : (0 : ℤ) ≤ Int.ofNat m := Int.natCast_nonneg m
          omega
        have hn_ne_0 : (Int.ofNat m : ℤ) ≠ 0 := by
          change ((m : ℕ) : ℤ) ≠ 0
          exact_mod_cast hm
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.ofNat m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.ofNat m : ℤ) : ℝ) = (m : ℝ) := by simp
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        -- Goal: -π·m²·τ.im - 2π·m·(τ.im/2) ≤ m·(-2π·τ.im)
        -- ⟺ π·m·τ.im·(m - 1) ≥ 0.
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
    | negSucc m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.negSucc m : ℤ) ≠ -1 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        have hn_ne_0 : (Int.negSucc m : ℤ) ≠ 0 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.negSucc m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.negSucc m : ℤ) : ℝ) = -((m : ℝ) + 1) := by
          rw [Int.cast_negSucc]; push_cast; ring
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        -- After substituting, LHS = -π·τ.im·(m+1)·m, RHS = -2π·τ.im·m.
        -- Need: -π·τ.im·m·(m+1) ≤ -2π·τ.im·m ⟺ m+1 ≥ 2 ⟺ m ≥ 1.
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
  -- Apply tsum_of_norm_bounded.
  have h_norm_le : ‖jacobiTheta₂ (τ / 2) τ - 1 - 1‖
      ≤ (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) := by
    rw [← h_skip_both.tsum_eq]
    exact tsum_of_norm_bounded h_int_rec h_term_bound
  have h_norm_diff_le_one : ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 1 := by
    have h_eq : jacobiTheta₂ (τ / 2) τ - 2 = jacobiTheta₂ (τ / 2) τ - 1 - 1 := by ring
    rw [h_eq]; linarith
  -- ‖jacobiTheta₂‖ ≥ 1 via reverse triangle.
  have h_jt_norm_ge : (1 : ℝ) ≤ ‖jacobiTheta₂ (τ / 2) τ‖ := by
    have h_rev : ‖(2 : ℂ)‖ - ‖(2 : ℂ) - jacobiTheta₂ (τ / 2) τ‖
        ≤ ‖(2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)‖ :=
      norm_sub_norm_le (2 : ℂ) ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)
    have h_simp : (2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ) = jacobiTheta₂ (τ / 2) τ := by ring
    rw [h_simp] at h_rev
    have h_two_norm : ‖(2 : ℂ)‖ = 2 := by simp
    have h_eq_neg : (2 : ℂ) - jacobiTheta₂ (τ / 2) τ = -(jacobiTheta₂ (τ / 2) τ - 2) := by ring
    rw [h_two_norm, h_eq_neg, norm_neg] at h_rev
    linarith
  -- Conclude theta2 ≠ 0.
  intro h_zero
  unfold theta2 at h_zero
  have h_exp_ne : Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) ≠ 0 :=
    Complex.exp_ne_zero _
  rcases mul_eq_zero.mp h_zero with h | h
  · exact h_exp_ne h
  · rw [h, norm_zero] at h_jt_norm_ge
    linarith

/-- **Extended-regime non-vanishing for `θ₃`** (`im ≥ 1/2`). Same
proof shape as `theta3_ne_zero_of_im_ge_one`, but the numeric bound
`exp(−π/2) < 1/3` uses `Real.quadratic_le_exp_of_nonneg` at `π/2`
to get `exp(π/2) ≥ 1 + π/2 + (π/2)²/2 > 3` from `π > 3`. The lower
threshold `1/2` is compatible with `SL(2,ℤ)`-reduction
(`ModularGroup.exists_one_half_le_im_smul`) and is needed for
bridging to the full upper half-plane via the modular action. -/
theorem theta3_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    theta3 τ ≠ 0 := by
  unfold theta3
  have hτ_pos : 0 < τ.im := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hτ
  have h_bound : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτ_pos
  set x := Real.exp (-Real.pi * τ.im) with hx_def
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_x_pos : 0 < x := Real.exp_pos _
  have h_x_le : x ≤ Real.exp (-Real.pi / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_exp_neg_pi_half : Real.exp (-Real.pi / 2) < 1 / 3 := by
    have h_pi_gt_3 : 3 < Real.pi := Real.pi_gt_three
    have h_pi_half_nn : (0 : ℝ) ≤ Real.pi / 2 := by linarith
    have h_quad : 1 + Real.pi/2 + (Real.pi/2)^2 / 2 ≤ Real.exp (Real.pi/2) :=
      Real.quadratic_le_exp_of_nonneg h_pi_half_nn
    have h_3_lt_quad : (3 : ℝ) < 1 + Real.pi/2 + (Real.pi/2)^2 / 2 := by nlinarith
    have h_3_lt_exp_pi_half : (3 : ℝ) < Real.exp (Real.pi/2) :=
      lt_of_lt_of_le h_3_lt_quad h_quad
    have h_exp_pi_half_pos : 0 < Real.exp (Real.pi/2) := Real.exp_pos _
    rw [show (-Real.pi / 2 : ℝ) = -(Real.pi/2) from by ring, Real.exp_neg,
        inv_lt_comm₀ h_exp_pi_half_pos (by norm_num : (0 : ℝ) < 1 / 3),
        show (1 / 3 : ℝ)⁻¹ = 3 from by norm_num]
    exact h_3_lt_exp_pi_half
  have h_x_lt_third : x < 1 / 3 := lt_of_le_of_lt h_x_le h_exp_neg_pi_half
  have h_one_sub_x_pos : 0 < 1 - x := by linarith
  have h_bound_lt_one : 2 / (1 - x) * x < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h_one_sub_x_pos]; linarith
  have h_norm_lt : ‖jacobiTheta τ - 1‖ < 1 := lt_of_le_of_lt h_bound h_bound_lt_one
  intro h_zero
  rw [h_zero, zero_sub, norm_neg, norm_one] at h_norm_lt
  exact lt_irrefl 1 h_norm_lt

/-- Extended-regime non-vanishing for `θ₄`. Reduces to
`theta3_ne_zero_of_im_ge_half` via `θ₄ τ = θ₃ (τ + 1)`. -/
theorem theta4_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    theta4 τ ≠ 0 := by
  rw [show theta4 τ = theta3 (τ + 1) from (theta3_add_one τ).symm]
  apply theta3_ne_zero_of_im_ge_half
  rw [Complex.add_im]; simp; linarith

/-- **Extended-regime non-vanishing for `θ₂`** (`im ≥ 1/2`). Same
series-decomposition proof as `theta2_ne_zero_of_im_ge_one`, but the
numeric bound `s ≤ 1/3` (where `s = exp(−2π·τ.im)`) uses the simpler
`Real.add_one_le_exp π` (giving `exp(π) ≥ 1 + π ≥ 4 > 3`) — for
`τ.im ≥ 1/2`, `s ≤ exp(−π) ≤ 1/3`. -/
theorem theta2_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    theta2 τ ≠ 0 := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hτ
  have hπ_pos := Real.pi_pos
  set s : ℝ := Real.exp (-2 * Real.pi * τ.im) with hs_def
  have hs_pos : 0 < s := Real.exp_pos _
  have hs_le_third : s ≤ 1/3 := by
    rw [hs_def, show (-2 * Real.pi * τ.im : ℝ) = -(2 * Real.pi * τ.im) from by ring,
        Real.exp_neg,
        inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/3),
        show (1/3 : ℝ)⁻¹ = 3 from by norm_num]
    have h_pi_gt_3 : 3 < Real.pi := Real.pi_gt_three
    have h_pi_le_2pi_tau : Real.pi ≤ 2 * Real.pi * τ.im := by nlinarith
    have h_exp_le : Real.exp Real.pi ≤ Real.exp (2 * Real.pi * τ.im) :=
      Real.exp_le_exp.mpr h_pi_le_2pi_tau
    have h_3_le_exp_pi : (3 : ℝ) ≤ Real.exp Real.pi := by
      have := Real.add_one_le_exp Real.pi; linarith
    linarith
  have hs_lt_one : s < 1 := by linarith
  have h_one_sub_s_pos : 0 < 1 - s := by linarith
  have h_int_sum_le_one : (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) ≤ 1 := by
    have h_inv_eq : (1 - s)⁻¹ - 1 = s / (1 - s) := by field_simp; ring
    rw [h_inv_eq]
    rw [show s/(1-s) + s/(1-s) = 2*s/(1-s) from by ring]
    rw [div_le_one h_one_sub_s_pos]; linarith
  have h_geo : HasSum (fun m : ℕ => s ^ m) ((1 - s)⁻¹) :=
    hasSum_geometric_of_lt_one hs_pos.le hs_lt_one
  have h_skip_geo : HasSum (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                          ((1 - s)⁻¹ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_geo 0
    simp only [pow_zero] at h_step
    exact h_step
  have h_int_rec : HasSum
      (fun n : ℤ => Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                            (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n)
      ((1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1)) :=
    HasSum.int_rec h_skip_geo h_skip_geo
  have h_jt_hasSum := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_zim : (τ / 2 : ℂ).im = τ.im / 2 := by simp
  have h_term_0 : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    simp [jacobiTheta₂_term]
  have h_term_neg1 : jacobiTheta₂_term (-1) (τ / 2) τ = 1 := by
    rw [jacobiTheta₂_term]
    have h_zero : 2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) * (τ/2)
        + (Real.pi : ℂ) * Complex.I * (((-1 : ℤ) : ℂ)) ^ 2 * τ = 0 := by
      push_cast; ring
    rw [h_zero]; exact Complex.exp_zero
  have h_skip_0 : HasSum
      (fun n : ℤ => if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_jt_hasSum 0
    rw [h_term_0] at h_step
    exact h_step
  have h_skip_both : HasSum
      (fun n : ℤ => if n = -1 then (0 : ℂ)
                    else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1 - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_skip_0 (-1)
    have h_at_neg1 :
        (if ((-1 : ℤ)) = 0 then (0 : ℂ) else jacobiTheta₂_term (-1) (τ / 2) τ) = 1 := by
      simp [h_term_neg1]
    rw [h_at_neg1] at h_step
    exact h_step
  have h_term_bound : ∀ n : ℤ,
      ‖(if n = -1 then (0 : ℂ)
        else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)‖
        ≤ Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                  (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n := by
    intro n
    cases n with
    | ofNat m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.ofNat m : ℤ) ≠ -1 := by
          have h_nn : (0 : ℤ) ≤ Int.ofNat m := Int.natCast_nonneg m
          omega
        have hn_ne_0 : (Int.ofNat m : ℤ) ≠ 0 := by
          change ((m : ℕ) : ℤ) ≠ 0
          exact_mod_cast hm
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.ofNat m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.ofNat m : ℤ) : ℝ) = (m : ℝ) := by simp
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
    | negSucc m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.negSucc m : ℤ) ≠ -1 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        have hn_ne_0 : (Int.negSucc m : ℤ) ≠ 0 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.negSucc m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.negSucc m : ℤ) : ℝ) = -((m : ℝ) + 1) := by
          rw [Int.cast_negSucc]; push_cast; ring
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
  have h_norm_le : ‖jacobiTheta₂ (τ / 2) τ - 1 - 1‖
      ≤ (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) := by
    rw [← h_skip_both.tsum_eq]
    exact tsum_of_norm_bounded h_int_rec h_term_bound
  have h_norm_diff_le_one : ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 1 := by
    have h_eq : jacobiTheta₂ (τ / 2) τ - 2 = jacobiTheta₂ (τ / 2) τ - 1 - 1 := by ring
    rw [h_eq]; linarith
  have h_jt_norm_ge : (1 : ℝ) ≤ ‖jacobiTheta₂ (τ / 2) τ‖ := by
    have h_rev : ‖(2 : ℂ)‖ - ‖(2 : ℂ) - jacobiTheta₂ (τ / 2) τ‖
        ≤ ‖(2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)‖ :=
      norm_sub_norm_le (2 : ℂ) ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)
    have h_simp : (2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ) = jacobiTheta₂ (τ / 2) τ := by ring
    rw [h_simp] at h_rev
    have h_two_norm : ‖(2 : ℂ)‖ = 2 := by simp
    have h_eq_neg : (2 : ℂ) - jacobiTheta₂ (τ / 2) τ = -(jacobiTheta₂ (τ / 2) τ - 2) := by ring
    rw [h_two_norm, h_eq_neg, norm_neg] at h_rev
    linarith
  intro h_zero
  unfold theta2 at h_zero
  have h_exp_ne : Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) ≠ 0 :=
    Complex.exp_ne_zero _
  rcases mul_eq_zero.mp h_zero with h | h
  · exact h_exp_ne h
  · rw [h, norm_zero] at h_jt_norm_ge
    linarith

/-! ### `SL(2,ℤ)`-reduction: extending non-vanishing to all of `ℍ` -/

/-- All three theta nullwerte are simultaneously nonzero at `τ`.
This is the orbit-invariant predicate under the `SL(2,ℤ)`-action,
since `SL(2,ℤ)` permutes `{θ₂, θ₃, θ₄}` modulo nonzero factors. -/
def all_theta_ne_zero (τ : ℂ) : Prop :=
  theta2 τ ≠ 0 ∧ theta3 τ ≠ 0 ∧ theta4 τ ≠ 0

/-- Easy-regime version of `all_theta_ne_zero` for `τ.im ≥ 1/2`. -/
theorem all_theta_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    all_theta_ne_zero τ :=
  ⟨theta2_ne_zero_of_im_ge_half hτ,
   theta3_ne_zero_of_im_ge_half hτ,
   theta4_ne_zero_of_im_ge_half hτ⟩

/-- T-invariance: `all_theta_ne_zero (τ + 1) ↔ all_theta_ne_zero τ`.
Uses `theta2_add_one`, `theta3_add_one`, `theta4_add_one`; the T-shift
permutes `θ₃ ↔ θ₄` and rescales `θ₂` by the nonzero `exp(πi/4)`. -/
theorem all_theta_ne_zero_T_iff (τ : ℂ) :
    all_theta_ne_zero (τ + 1) ↔ all_theta_ne_zero τ := by
  unfold all_theta_ne_zero
  rw [theta2_add_one, theta3_add_one, theta4_add_one]
  have h_exp_ne : Complex.exp ((Real.pi : ℂ) * Complex.I / 4) ≠ 0 :=
    Complex.exp_ne_zero _
  constructor
  · rintro ⟨h2, h3, h4⟩
    exact ⟨(mul_ne_zero_iff.mp h2).2, h4, h3⟩
  · rintro ⟨h2, h3, h4⟩
    exact ⟨mul_ne_zero h_exp_ne h2, h4, h3⟩

/-- S-invariance: `all_theta_ne_zero (-1/τ) ↔ all_theta_ne_zero τ`
for `τ ∈ ℍ`. Uses `theta2_S_smul`, `theta3_S_smul`, `theta4_S_smul`;
the S-action permutes `θ₂ ↔ θ₄` (fixing `θ₃`) and rescales by the
nonzero `(−iτ)^{1/2}`. -/
theorem all_theta_ne_zero_S_iff {τ : ℂ} (hτ : 0 < τ.im) :
    all_theta_ne_zero (-1 / τ) ↔ all_theta_ne_zero τ := by
  unfold all_theta_ne_zero
  rw [theta2_S_smul hτ, theta3_S_smul hτ, theta4_S_smul hτ]
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have h_mIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  have h_factor_ne : (-Complex.I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl h_mIτ_ne)
  constructor
  · rintro ⟨h2, h3, h4⟩
    refine ⟨(mul_ne_zero_iff.mp h4).2, (mul_ne_zero_iff.mp h3).2, (mul_ne_zero_iff.mp h2).2⟩
  · rintro ⟨h2, h3, h4⟩
    exact ⟨mul_ne_zero h_factor_ne h4, mul_ne_zero h_factor_ne h3, mul_ne_zero h_factor_ne h2⟩

/-- **Main SL(2,ℤ)-invariance of `all_theta_ne_zero`.** For any
`γ ∈ SL(2,ℤ)` and any `τ ∈ ℍ`,
`all_theta_ne_zero ((γ • τ) : ℂ) ↔ all_theta_ne_zero (τ : ℂ)`. Proved
by `Subgroup.closure_induction` on `SpecialLinearGroup.SL2Z_generators`,
using `all_theta_ne_zero_T_iff` and `all_theta_ne_zero_S_iff` on the
generators. -/
theorem all_theta_ne_zero_smul_iff_SL2Z (γ : SL(2, ℤ)) :
    ∀ τ : UpperHalfPlane,
      all_theta_ne_zero ((γ • τ : UpperHalfPlane) : ℂ) ↔ all_theta_ne_zero (τ : ℂ) := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | one =>
    intro τ; rw [one_smul]
  | mem g hg =>
    intro τ
    rcases hg with h | h
    · -- g = S
      subst h
      rw [UpperHalfPlane.modular_S_smul]
      change all_theta_ne_zero ((-(τ : ℂ))⁻¹) ↔ _
      rw [show (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) from by field_simp]
      exact all_theta_ne_zero_S_iff τ.2
    · -- g = T
      subst h
      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
      rw [show (((1 : ℝ) : ℂ) + (τ : ℂ)) = (τ : ℂ) + 1 from by push_cast; ring]
      exact all_theta_ne_zero_T_iff (τ : ℂ)
  | mul g h _ _ ig ih =>
    intro τ
    rw [mul_smul]
    exact (ig (h • τ)).trans (ih τ)
  | inv g _ ig =>
    intro τ
    have h_id : g • (g⁻¹ • τ : UpperHalfPlane) = τ := by
      rw [← mul_smul, mul_inv_cancel, one_smul]
    have h := ig (g⁻¹ • τ)
    rw [h_id] at h
    exact h.symm

/-- **Full-`ℍ` theta non-vanishing.** For any `τ ∈ ℍ`, all three theta
nullwerte are nonzero. Applies `SL(2,ℤ)`-reduction (Mathlib's
`ModularGroup.exists_one_half_le_im_smul`) to land in the easy regime
`im ≥ 1/2`, then transports the easy-regime non-vanishing back via
`all_theta_ne_zero_smul_iff_SL2Z`. -/
theorem all_theta_ne_zero_on_H {τ : ℂ} (hτ : 0 < τ.im) :
    all_theta_ne_zero τ := by
  set τH : UpperHalfPlane := ⟨τ, hτ⟩
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_one_half_le_im_smul τH
  have h_at_γτ : all_theta_ne_zero (((γ • τH : UpperHalfPlane)) : ℂ) :=
    all_theta_ne_zero_of_im_ge_half hγ
  exact (all_theta_ne_zero_smul_iff_SL2Z γ τH).mp h_at_γτ

/-- `θ₂` does not vanish on the upper half-plane. -/
theorem theta2_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : theta2 τ ≠ 0 :=
  (all_theta_ne_zero_on_H hτ).1

/-- `θ₃ = jacobiTheta` does not vanish on the upper half-plane. -/
theorem theta3_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : theta3 τ ≠ 0 :=
  (all_theta_ne_zero_on_H hτ).2.1

/-- `θ₄` does not vanish on the upper half-plane. -/
theorem theta4_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : theta4 τ ≠ 0 :=
  (all_theta_ne_zero_on_H hτ).2.2

/-- **Easy-regime differentiability of `λ`.** For `τ` with `1 ≤ τ.im`,
`modularLambdaH` is differentiable at `τ` (since `θ₃(τ) ≠ 0` and both
`θ₂`, `θ₃` are differentiable). -/
theorem modularLambdaH_differentiableAt_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    DifferentiableAt ℂ modularLambdaH τ := by
  have hτ_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have h3_ne : theta3 τ ≠ 0 := theta3_ne_zero_of_im_ge_one hτ
  have h3_pow_ne : theta3 τ ^ 4 ≠ 0 := pow_ne_zero 4 h3_ne
  unfold modularLambdaH
  refine DifferentiableAt.div ?_ ?_ h3_pow_ne
  · exact (theta2_differentiableAt hτ_pos).pow 4
  · exact (theta3_differentiableAt hτ_pos).pow 4

/-! ## Range and omitted values of `λ` -/

/-- `λ(τ) ≠ 0` for `τ ∈ ℍ`. Directly from `θ₂(τ) ≠ 0` and
`θ₃(τ) ≠ 0`: `λ(τ) = θ₂⁴/θ₃⁴`, and `θ₂⁴ ≠ 0`. -/
theorem modularLambdaH_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH τ ≠ 0 := by
  unfold modularLambdaH
  have h2 := theta2_ne_zero hτ
  have h3 := theta3_ne_zero hτ
  exact div_ne_zero (pow_ne_zero 4 h2) (pow_ne_zero 4 h3)

/-- `λ(τ) ≠ 1` for `τ ∈ ℍ`. Combines Jacobi's identity
`θ₂⁴ + θ₄⁴ = θ₃⁴` (giving `λ = 1 − (θ₄/θ₃)⁴`) with `θ₄(τ) ≠ 0`. -/
theorem modularLambdaH_ne_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH τ ≠ 1 := by
  unfold modularLambdaH
  have h2 := theta2_ne_zero hτ
  have h3 := theta3_ne_zero hτ
  have h4 := theta4_ne_zero hτ
  have h3_pow : (theta3 τ)^4 ≠ 0 := pow_ne_zero 4 h3
  have h_jacobi : theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := jacobi_identity hτ
  intro h_eq
  -- λ = θ₂⁴/θ₃⁴ = 1 means θ₂⁴ = θ₃⁴.
  have h_theta2_pow_eq : theta2 τ ^ 4 = theta3 τ ^ 4 := by
    have h_eq' := h_eq
    field_simp at h_eq'
    exact h_eq'
  -- Combined with Jacobi: θ₄⁴ = 0.
  have h_theta4_pow_zero : theta4 τ ^ 4 = 0 := by
    linear_combination h_jacobi - h_theta2_pow_eq
  -- Hence θ₄ = 0, contradicting theta4_ne_zero.
  have h_theta4 : theta4 τ = 0 :=
    (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp h_theta4_pow_zero
  exact h4 h_theta4

/-- **Surjectivity of `λ : ℍ → ℂ ∖ {0, 1}`.** The image of `λ` on `ℍ`
is exactly the triply-punctured plane.

The `⊆` direction is direct from `modularLambdaH_ne_zero` and
`modularLambdaH_ne_one` and is closed below. The `⊇` direction —
surjectivity — is the deep classical theorem. The intended proof
path uses the **Schwarz reflection principle**
(`schwarzReflect_differentiableOn`, now closed in
`SchwarzReflection.lean`): identify a fundamental domain `F` of
`Γ(2)` on `ℍ` whose interior is mapped biholomorphically by `λ` onto
one open half of `ℂ ∖ {0, 1}` (say the upper half), with the three
boundary arcs of `F` mapping to the three real-axis intervals
`(-∞, 0), (0, 1), (1, +∞)`. The Schwarz reflection principle then
extends `λ` across each boundary arc to a reflected fundamental
domain, with image covering the complementary lower half. Iterating
the reflections tiles all of `ℍ` and the image covers all of
`ℂ ∖ {0, 1}`. Required infrastructure (still pending):
explicit `F`, the boundary-correspondence biholomorphism
`F^o → upper half of ℂ ∖ {0, 1}`, and the Möbius-conjugated Schwarz
reflection across the two semi-circular boundary arcs. -/
theorem modularLambdaH_image :
    modularLambdaH '' { τ : ℂ | 0 < τ.im } = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · -- `⊆`: `λ(ℍ) ⊆ ℂ ∖ {0, 1}` from `modularLambdaH_ne_zero/_ne_one`.
    rintro w ⟨τ, hτ, rfl⟩
    exact ⟨modularLambdaH_ne_zero hτ, modularLambdaH_ne_one hτ⟩
  · -- `⊇`: surjectivity via Schwarz reflection across the fundamental-
    -- domain boundary arcs of `Γ(2)`. Pending the fundamental-domain
    -- infrastructure (see doc-comment above).
    sorry

/-! ## Modular invariance under `Γ(2)` -/

/-- **`Γ(2)`-invariance of `λ` on `ℍ`.**

**Deferred proof sketch.** `Γ(2) := { γ ∈ SL₂(ℤ) | γ ≡ I (mod 2) }` is
generated (in `PSL₂(ℤ)`) by `T² = [[1, 2], [0, 1]]` and
`ST⁻²S = [[1, 0], [2, 1]]`. We have already proven:
* `modularLambdaH_two_add : λ(τ + 2) = λ(τ)` (`T²`-invariance);
* `modularLambdaH_div_two_tau_add_one : λ(τ / (2τ + 1)) = λ(τ)`
  (`ST⁻²S`-invariance).

The remaining ingredient is the group-theoretic generation result:
every `γ ∈ Γ(2)` is a product of `T²`, `ST⁻²S`, their inverses, and
`±I` (with `-I` acting trivially on `λ`). Mathlib does not currently
carry this generator decomposition for `Γ(2)`; supplying it requires
either an explicit row-reduction algorithm on `SL₂(ℤ)` modulo 2 or a
Möbius geometric argument on the fundamental domain. Status: blocked. -/
theorem modularLambdaH_gamma2_invariant
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (_hγ : γ ∈ CongruenceSubgroup.Gamma 2) (τ : UpperHalfPlane) :
    modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ)
      = modularLambdaH (τ : ℂ) := by
  sorry

/-! ## Holomorphy and the covering map property -/

/-- `λ` is holomorphic on the upper half-plane. Follows from
`theta3_ne_zero` on `ℍ` together with the differentiability of the
theta nullwerte. -/
theorem modularLambdaH_differentiableOn :
    DifferentiableOn ℂ modularLambdaH { τ : ℂ | 0 < τ.im } := by
  intro τ hτ
  have hτ_pos : 0 < τ.im := hτ
  have h3 : theta3 τ ≠ 0 := theta3_ne_zero hτ_pos
  have h3_pow : (theta3 τ)^4 ≠ 0 := pow_ne_zero 4 h3
  unfold modularLambdaH
  apply DifferentiableAt.differentiableWithinAt
  refine DifferentiableAt.div ?_ ?_ h3_pow
  · exact (theta2_differentiableAt hτ_pos).pow 4
  · exact (theta3_differentiableAt hτ_pos).pow 4

/-- **Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`.**

**Deferred proof sketch.** This is the central theorem of the
modular-function track: `λ` is a holomorphic covering map of the
triply-punctured plane by the upper half-plane. The standard proof
factors `λ` through the quotient `ℍ → ℍ / Γ(2)` and the
homeomorphism `ℍ / Γ(2) ≃ ℂ ∖ {0, 1}` induced by `λ`. Required
ingredients (none currently in Mathlib for `Γ(2)` specifically):
* `Γ(2)` acts freely and properly discontinuously on `ℍ`;
* The quotient projection `ℍ → ℍ / Γ(2)` is a covering map;
* `λ` factors through this quotient as a homeomorphism onto
  `ℂ ∖ {0, 1}`.

Alternatively, via the inverse function theorem: `λ` is locally
injective on `ℍ` (its derivative `λ'` is nonzero on `ℍ`), and the
preimage `λ⁻¹{w}` is discrete (a `Γ(2)`-orbit). This gives the local
triviality at each `w`. Status: blocked on `Γ(2)` action machinery. -/
theorem modularLambdaH_isCoveringMapOn :
    IsCoveringMapOn modularLambdaH { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

/-! ## Disk version `modularLambda : 𝔻 → ℂ ∖ {0, 1}` -/

/-- The disk modular function takes values in the triply-punctured plane.
Reduces to `modularLambdaH_ne_zero` and `modularLambdaH_ne_one` via the
Cayley transform: `cayleyToHalfPlane` sends `𝔻` to `ℍ`, so
`(cayleyToHalfPlane z).im > 0`. -/
theorem modularLambda_omits {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    modularLambda z ≠ 0 ∧ modularLambda z ≠ 1 := by
  unfold modularLambda
  have hτ_pos : 0 < (cayleyToHalfPlane z).im := cayleyToHalfPlane_im_pos hz
  exact ⟨modularLambdaH_ne_zero hτ_pos, modularLambdaH_ne_one hτ_pos⟩

/-- The image of `modularLambda` on `𝔻` is exactly `ℂ ∖ {0, 1}`.
Combines `cayleyToHalfPlane_image_ball` (Cayley sends `𝔻` onto `ℍ`)
with `modularLambdaH_image` (surjectivity of `λ` onto the
triply-punctured plane). -/
theorem modularLambda_image :
    modularLambda '' ball (0 : ℂ) 1 = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  unfold modularLambda
  rw [show (fun z => modularLambdaH (cayleyToHalfPlane z))
        = modularLambdaH ∘ cayleyToHalfPlane from rfl,
      Set.image_comp, cayleyToHalfPlane_image_ball]
  exact modularLambdaH_image

/-- `modularLambda` is holomorphic on the unit disk. Composition of
`cayleyToHalfPlane : 𝔻 → ℍ` (Möbius, hence differentiable on `𝔻`) with
`modularLambdaH` (differentiable on `ℍ`). -/
theorem modularLambda_differentiableOn :
    DifferentiableOn ℂ modularLambda (ball (0 : ℂ) 1) := by
  intro z hz
  unfold modularLambda
  have h_one_sub_ne : (1 - z) ≠ 0 := by
    simp only [Metric.mem_ball, dist_zero_right] at hz
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz; simp at hz
  have h_cayley_diff : DifferentiableAt ℂ cayleyToHalfPlane z := by
    unfold cayleyToHalfPlane
    fun_prop (disch := exact h_one_sub_ne)
  have hτ_pos : 0 < (cayleyToHalfPlane z).im := cayleyToHalfPlane_im_pos hz
  have h_modH_diff : DifferentiableAt ℂ modularLambdaH (cayleyToHalfPlane z) := by
    have h3 : theta3 (cayleyToHalfPlane z) ≠ 0 := theta3_ne_zero hτ_pos
    have h3_pow : (theta3 (cayleyToHalfPlane z))^4 ≠ 0 := pow_ne_zero 4 h3
    unfold modularLambdaH
    refine DifferentiableAt.div ?_ ?_ h3_pow
    · exact (theta2_differentiableAt hτ_pos).pow 4
    · exact (theta3_differentiableAt hτ_pos).pow 4
  exact (h_modH_diff.comp z h_cayley_diff).differentiableWithinAt

/-- **Covering property of `λ` on the unit disk.**
`modularLambda : 𝔻 → ℂ ∖ {0, 1}` is a covering map of the
triply-punctured plane by the disk.

**Deferred proof sketch.** Conditional on `modularLambdaH_isCoveringMapOn`.
The Cayley transform restricts to a homeomorphism
`𝔻 ≃ₜ ℍ` (using `cayleyToHalfPlane_image_ball`,
`halfPlaneToCayley_mem_ball`, `cayleyToHalfPlane_halfPlaneToCayley`,
`halfPlaneToCayley_cayleyToHalfPlane`). For each `w ∈ ℂ ∖ {0, 1}`, the
evenly-covered neighborhood `U` of `w` under `modularLambdaH` (and its
trivialization `H_MH : modularLambdaH ⁻¹' U ≃ₜ U × I_MH`) transports
through Cayley: `modularLambda ⁻¹' U` lives inside `𝔻` (since
`modularLambda` is Lean-junk `0` outside `𝔻`), Cayley-restricted gives a
homeomorphism `modularLambda ⁻¹' U ≃ₜ modularLambdaH ⁻¹' U`, then chain
with `H_MH` and the fiber Cayley to obtain `H_ML`. Status: structurally
clear, but ~200 lines of subtype-bookkeeping; deferred for a focused
session. -/
theorem modularLambda_isCoveringMapOn :
    IsCoveringMapOn modularLambda { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

end RiemannDynamics

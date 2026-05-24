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

**Deferred proof sketch.** The `⊆` direction is direct from
`modularLambdaH_ne_zero` and `modularLambdaH_ne_one` (both proven).
The `⊇` direction — surjectivity — is the deep theorem. Two classical
proof paths:
* **Via covering theory**: `λ` is a holomorphic covering map onto its
  image (`modularLambdaH_isCoveringMapOn`); the image is open in
  `ℂ ∖ {0, 1}`, and since the latter is connected and the image is
  nonempty, the image equals the whole space.
* **Via direct construction**: lift any `w ∈ ℂ ∖ {0, 1}` by reflecting
  the fundamental domain `F` of `Γ(2)` across its boundary, using the
  Schwarz reflection principle.

Both routes require Mathlib infrastructure not currently available
(`λ` open map + covering connectedness, or Schwarz reflection on
`F`). Status: blocked. -/
theorem modularLambdaH_image :
    modularLambdaH '' { τ : ℂ | 0 < τ.im } = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
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

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.ModularFunction
import RiemannDynamics.Hyperbolic.SchwarzReflection
import RiemannDynamics.Hyperbolic.ArgumentPrinciple
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Fundamental domain of `Γ(2)` for the level-2 modular function `λ`

The level-2 principal congruence subgroup `Γ(2) ⊂ SL(2, ℤ)` acts on
the upper half-plane `ℍ`. A standard fundamental domain is the strip
of width `1` with a semi-circular notch removed:

  `F := { τ ∈ ℍ : 0 ≤ Re τ ≤ 1, |2τ − 1| ≥ 1 }`.

The boundary `∂F` consists of three arcs:
* The vertical line `Re τ = 0` (left edge), `τ ∈ {iy : y > 0}`.
* The vertical line `Re τ = 1` (right edge), `τ ∈ {1 + iy : y > 0}`.
* The upper semi-circle `|2τ − 1| = 1` of radius `1/2` centered at
  `1/2` (bottom arc), `τ ∈ {(1 + e^{iθ})/2 : 0 < θ < π}`.

The modular function `λ` restricted to the open interior `F^o` is a
biholomorphism onto the open upper half of `ℂ ∖ {0, 1}`; the three
boundary arcs map respectively to the three real-axis intervals
`(0, 1)`, `(−∞, 0)`, `(1, +∞)`. The Schwarz reflection principle
(`schwarzReflect_differentiableOn`) extends `λ` from `F^o` across the
real-axis arc into the reflected fundamental domain; the two semi-
circular boundary arcs require a Möbius-conjugated version of
Schwarz reflection.

This file sets up the fundamental domain and its basic topological
properties. The deep biholomorphism and tiling steps consumed by the
surjectivity argument for `modularLambdaH_image` are stated here as
deferred theorems.
-/

namespace RiemannDynamics

open Complex Filter Topology Set

/-- The standard fundamental domain of `Γ(2)` acting on the upper
half-plane: the strip `0 ≤ Re τ ≤ 1` with the half-disk
`|2τ − 1| < 1` removed. -/
def Gamma2FundamentalDomain : Set ℂ :=
  { τ : ℂ | 0 < τ.im ∧ 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ 1 ≤ ‖2 * τ - 1‖ }

/-- The open interior of `Gamma2FundamentalDomain`: strict
inequalities on each of the three boundary arcs. -/
def Gamma2FundamentalDomainInterior : Set ℂ :=
  { τ : ℂ | 0 < τ.im ∧ 0 < τ.re ∧ τ.re < 1 ∧ 1 < ‖2 * τ - 1‖ }

/-! ## Basic topological properties -/

/-- `F` is contained in the upper half-plane. -/
theorem Gamma2FundamentalDomain_subset_upperHalf :
    Gamma2FundamentalDomain ⊆ { τ : ℂ | 0 < τ.im } := fun _ hτ => hτ.1

/-- `F^o` is contained in `F`. -/
theorem Gamma2FundamentalDomainInterior_subset :
    Gamma2FundamentalDomainInterior ⊆ Gamma2FundamentalDomain := by
  intro τ hτ
  exact ⟨hτ.1, hτ.2.1.le, hτ.2.2.1.le, hτ.2.2.2.le⟩

/-- `F^o` is contained in the upper half-plane. -/
theorem Gamma2FundamentalDomainInterior_subset_upperHalf :
    Gamma2FundamentalDomainInterior ⊆ { τ : ℂ | 0 < τ.im } := fun _ hτ => hτ.1

/-- The open interior `F^o` is an open subset of `ℂ`. -/
theorem Gamma2FundamentalDomainInterior_isOpen :
    IsOpen Gamma2FundamentalDomainInterior := by
  have h1 : IsOpen { τ : ℂ | 0 < τ.im } :=
    isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen { τ : ℂ | 0 < τ.re } :=
    isOpen_lt continuous_const Complex.continuous_re
  have h3 : IsOpen { τ : ℂ | τ.re < 1 } :=
    isOpen_lt Complex.continuous_re continuous_const
  have h4 : IsOpen { τ : ℂ | 1 < ‖2 * τ - 1‖ } := by
    apply isOpen_lt continuous_const
    fun_prop
  have h_eq : Gamma2FundamentalDomainInterior =
      { τ : ℂ | 0 < τ.im } ∩ { τ : ℂ | 0 < τ.re } ∩
      { τ : ℂ | τ.re < 1 } ∩ { τ : ℂ | 1 < ‖2 * τ - 1‖ } := by
    ext τ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩
    · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  rw [h_eq]
  exact (((h1.inter h2).inter h3).inter h4)

/-! ## Boundary-real values of `λ`

The three boundary arcs of `F` are mapped by `λ` to real-axis arcs.
This is the boundary-correspondence half of the biholomorphism: it
makes the `schwarzReflect_differentiableOn` hypothesis (real-axis
values) directly verifiable. -/

/-- `θ₃(iy)` is real for every `y > 0`. The Jacobi theta series at
purely imaginary argument is a sum of real exponentials
`exp(−π·n²·y)`, hence real. -/
theorem theta3_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (theta3 (Complex.I * y)).im = 0 := by
  -- `theta3 (Iy) = jacobiTheta (Iy)`. From `hasSum_nat_jacobiTheta`,
  -- `(jacobiTheta(Iy) - 1)/2 = ∑ exp(π·I·(n+1)²·Iy) = ∑ exp(-π·(n+1)²·y)`.
  -- Each term is a positive real, so the sum is real and
  -- `(jacobiTheta(Iy)).im = 0`.
  unfold theta3
  have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, hy]
  have h_sum := hasSum_nat_jacobiTheta hτ_im
  -- Each term has imaginary part 0.
  have h_terms_real : ∀ n : ℕ,
      (Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ)))).im = 0 := by
    intro n
    have h_arg : (Real.pi : ℂ) * Complex.I * ((↑n : ℂ) + 1) ^ 2 *
        (Complex.I * (y : ℂ)) =
        ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_arg]
    exact Complex.exp_ofReal_im _
  -- Apply `HasSum.map Complex.imCLM`.
  have h_map := h_sum.map Complex.imCLM Complex.continuous_im
  -- Rewrite via funext to expose `(·).im` form.
  have h_funext : (fun n : ℕ => (Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ)))).im) = (fun _ : ℕ => (0 : ℝ)) := by
    funext n; exact h_terms_real n
  -- HasSum of zero is zero, so the target's `.im` is zero.
  have h_im_zero : ((jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2).im = 0 := by
    have h_lhs : (⇑Complex.imCLM ∘ fun n : ℕ =>
        Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ)))) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      change (Complex.exp _).im = 0
      exact h_terms_real n
    rw [h_lhs] at h_map
    have h_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
    -- `Complex.imCLM z = z.im` by definition.
    exact h_map.unique h_zero
  -- Extract jacobiTheta(Iy).im = 0.
  have h_div : ((jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2).im
      = (jacobiTheta (Complex.I * (y : ℂ)) - 1).im / 2 := by
    simp
  rw [h_div] at h_im_zero
  have h_sub_zero : (jacobiTheta (Complex.I * (y : ℂ)) - 1).im = 0 := by linarith
  have h_jt_im : (jacobiTheta (Complex.I * (y : ℂ))).im = 0 := by
    have h1 : (jacobiTheta (Complex.I * (y : ℂ))).im - (1 : ℂ).im = 0 := by
      rw [← Complex.sub_im]; exact h_sub_zero
    simpa using h1
  exact h_jt_im

/-- `θ₂(iy)` is real for every `y > 0`. The defining series
`exp(πiτ/4) · jacobiTheta₂(τ/2, τ)` reduces to a sum of real
exponentials at `τ = iy`. -/
theorem theta2_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (theta2 (Complex.I * y)).im = 0 := by
  unfold theta2
  have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, hy]
  -- First factor: `exp(π·I·Iy/4) = exp(-πy/4)` is real.
  have h_first_im : (Complex.exp ((Real.pi : ℂ) * Complex.I *
      (Complex.I * (y : ℂ)) / 4)).im = 0 := by
    have h_arg : (Real.pi : ℂ) * Complex.I * (Complex.I * (y : ℂ)) / 4 =
        ((-Real.pi * y / 4 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_arg]
    exact Complex.exp_ofReal_im _
  -- Second factor: `jacobiTheta₂(Iy/2, Iy)` is real.
  have h_second_im : (jacobiTheta₂ (Complex.I * (y : ℂ) / 2)
      (Complex.I * (y : ℂ))).im = 0 := by
    have h_sum := hasSum_jacobiTheta₂_term (Complex.I * (y : ℂ) / 2) hτ_im
    -- Each term `cexp(2πi n (Iy/2) + πi n² (Iy)) = cexp(-π·(n²+n)·y)` is real.
    have h_terms_real : ∀ n : ℤ,
        (jacobiTheta₂_term n (Complex.I * (y : ℂ) / 2)
          (Complex.I * (y : ℂ))).im = 0 := by
      intro n
      unfold jacobiTheta₂_term
      have h_arg : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (Complex.I * (y : ℂ) / 2) +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (y : ℂ)) =
          ((-Real.pi * ((n : ℝ) + (n : ℝ)^2) * y : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
        ring
      rw [h_arg]
      exact Complex.exp_ofReal_im _
    have h_map := h_sum.map Complex.imCLM Complex.continuous_im
    have h_lhs : (⇑Complex.imCLM ∘ fun n : ℤ =>
        jacobiTheta₂_term n (Complex.I * (y : ℂ) / 2)
          (Complex.I * (y : ℂ))) =
        (fun _ : ℤ => (0 : ℝ)) := by
      funext n
      change (jacobiTheta₂_term n _ _).im = 0
      exact h_terms_real n
    rw [h_lhs] at h_map
    have h_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0 := hasSum_zero
    exact h_map.unique h_zero
  -- Combine: `(real · real).im = 0`.
  rw [Complex.mul_im, h_first_im, h_second_im]
  ring

/-- `θ₄(iy)` is real for every `y > 0`. Follows from
`theta3_pure_imag_real` via `theta4 τ = jacobiTheta (τ + 1)` and the
real-valuedness of the corresponding series at imaginary argument. -/
theorem theta4_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (theta4 (Complex.I * y)).im = 0 := by
  unfold theta4
  have hτ_im : 0 < (Complex.I * (y : ℂ) + 1).im := by
    simp [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.I_re, Complex.I_im, hy]
  have h_sum := hasSum_nat_jacobiTheta hτ_im
  -- Each term `exp(π·I·(n+1)²·(Iy+1))` factors as `real · (±1)`, hence real.
  have h_terms_real : ∀ n : ℕ,
      (Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ) + 1))).im = 0 := by
    intro n
    have h_split : (Real.pi : ℂ) * Complex.I * ((↑n : ℂ) + 1) ^ 2 *
        (Complex.I * (y : ℂ) + 1) =
        ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ) +
        ((↑n : ℂ) + 1) ^ 2 * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_split, Complex.exp_add]
    have h1 : (Complex.exp ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ)).im = 0 :=
      Complex.exp_ofReal_im _
    have h2 : (Complex.exp (((↑n : ℂ) + 1) ^ 2 * ((Real.pi : ℂ) * Complex.I))).im = 0 := by
      rw [show ((↑n : ℂ) + 1) ^ 2 = (((n + 1)^2 : ℕ) : ℂ) from by push_cast; ring]
      rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      rcases Nat.even_or_odd ((n + 1)^2) with hev | hod
      · rw [Even.neg_one_pow hev]; simp
      · rw [Odd.neg_one_pow hod]; simp
    rw [Complex.mul_im, h1, h2]
    ring
  -- Apply HasSum.map to extract `.im` of the partial sum.
  have h_map := h_sum.map Complex.imCLM Complex.continuous_im
  have h_lhs : (⇑Complex.imCLM ∘ fun n : ℕ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ) + 1))) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    change (Complex.exp _).im = 0
    exact h_terms_real n
  rw [h_lhs] at h_map
  have h_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
  have h_im_zero : ((jacobiTheta (Complex.I * (y : ℂ) + 1) - 1) / 2).im = 0 :=
    h_map.unique h_zero
  have h_div : ((jacobiTheta (Complex.I * (y : ℂ) + 1) - 1) / 2).im
      = (jacobiTheta (Complex.I * (y : ℂ) + 1) - 1).im / 2 := by simp
  rw [h_div] at h_im_zero
  have h_sub_zero : (jacobiTheta (Complex.I * (y : ℂ) + 1) - 1).im = 0 := by linarith
  have h_jt_im : (jacobiTheta (Complex.I * (y : ℂ) + 1)).im = 0 := by
    have h1 : (jacobiTheta (Complex.I * (y : ℂ) + 1)).im - (1 : ℂ).im = 0 := by
      rw [← Complex.sub_im]; exact h_sub_zero
    simpa using h1
  exact h_jt_im

/-- **Left boundary arc of `F`: `λ(iy) ∈ ℝ`.** For every `y > 0`,
`modularLambdaH(iy)` is real. This is the boundary correspondence for
the left vertical edge `Re τ = 0` of `F`; combined with the
biholomorphism `λ : F^o ≅ {Im w > 0}`, the image of the imaginary
axis is one of the three real-axis arcs of `ℂ ∖ {0, 1}` (specifically
`(0, 1)`). -/
theorem modularLambdaH_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (modularLambdaH (Complex.I * y)).im = 0 := by
  unfold modularLambdaH
  have h2 : (theta2 (Complex.I * y)).im = 0 := theta2_pure_imag_real hy
  have h3 : (theta3 (Complex.I * y)).im = 0 := theta3_pure_imag_real hy
  -- Powers of a real-imaginary-zero complex are real-imaginary-zero.
  have hp : ∀ z : ℂ, z.im = 0 → (z^4).im = 0 := by
    intros z hz
    have : z^4 = z*z*z*z := by ring
    rw [this]
    simp [Complex.mul_im, hz]
  -- Quotient of two real-imaginary-zero complex numbers has imaginary part zero.
  have hdiv : ∀ z w : ℂ, z.im = 0 → w.im = 0 → (z / w).im = 0 := by
    intros z w hz hw
    rw [Complex.div_im, hz, hw]
    ring
  exact hdiv _ _ (hp _ h2) (hp _ h3)

/-- **Right boundary arc of `F`: `λ(1 + iy) ∈ ℝ`.** For every `y > 0`,
`modularLambdaH(1 + iy)` is real. Follows from `modularLambdaH_T_smul`
together with the reality of `θ₂(iy)` and `θ₄(iy)`. -/
theorem modularLambdaH_one_add_imag_real {y : ℝ} (hy : 0 < y) :
    (modularLambdaH (1 + Complex.I * y)).im = 0 := by
  rw [show (1 + Complex.I * y : ℂ) = Complex.I * y + 1 from by ring]
  rw [modularLambdaH_T_smul]
  have h2 : (theta2 (Complex.I * y)).im = 0 := theta2_pure_imag_real hy
  have h4 : (theta4 (Complex.I * y)).im = 0 := theta4_pure_imag_real hy
  have hp : ∀ z : ℂ, z.im = 0 → (z^4).im = 0 := by
    intros z hz
    have : z^4 = z*z*z*z := by ring
    rw [this]
    simp [Complex.mul_im, hz]
  have hdiv : ∀ z w : ℂ, z.im = 0 → w.im = 0 → (z / w).im = 0 := by
    intros z w hz hw
    rw [Complex.div_im, hz, hw]
    ring
  have hquot : (theta2 (Complex.I * y) ^ 4 / theta4 (Complex.I * y) ^ 4).im = 0 :=
    hdiv _ _ (hp _ h2) (hp _ h4)
  rw [Complex.neg_im, hquot, neg_zero]

/-- **Jacobi-derived modular identity for `λ`.** For `τ ∈ ℍ`,
`λ(τ) + λ(-1/τ) = 1`. The proof divides Jacobi's identity
`θ₂⁴ + θ₄⁴ = θ₃⁴` by `θ₃⁴` (which is non-zero on `ℍ`) and reads off
the two `λ`-quotients on the left-hand side via the definition of `λ`
and `modularLambdaH_S_smul`. -/
theorem modularLambdaH_add_S_smul_eq_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH τ + modularLambdaH (-1 / τ) = 1 := by
  rw [modularLambdaH_S_smul hτ]
  unfold modularLambdaH
  have h_jac : theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := jacobi_identity hτ
  have hne : theta3 τ ≠ 0 := theta3_ne_zero hτ
  field_simp
  linear_combination h_jac

/-- **Semicircle geometric lemma.** For any `τ ∈ ℂ` with `‖2τ − 1‖ = 1`,
the complex norm-squared `|τ|²` equals the real part `τ.re`. -/
theorem Gamma2FundamentalDomain_semicircle_normSq_eq_re {τ : ℂ}
    (h_circle : ‖2 * τ - 1‖ = 1) : Complex.normSq τ = τ.re := by
  have h_normSq : Complex.normSq (2 * τ - 1) = 1 := by
    rw [← Complex.sq_norm, h_circle]; ring
  have h_re : (2 * τ - 1).re = 2 * τ.re - 1 := by simp
  have h_im : (2 * τ - 1).im = 2 * τ.im := by simp
  have h_expand : Complex.normSq (2 * τ - 1) =
      (2 * τ.re - 1)^2 + (2 * τ.im)^2 := by
    rw [Complex.normSq_apply, h_re, h_im]; ring
  rw [h_expand] at h_normSq
  rw [Complex.normSq_apply]
  nlinarith

/-- **Semicircle boundary arc of `F`: `λ(τ) ∈ ℝ`.** For `τ ∈ ℂ` with
`τ.im > 0` and `‖2τ − 1‖ = 1` (the upper half of the boundary
semicircle of `F`), `modularLambdaH(τ)` is real. The proof uses the
geometric fact `|τ|² = τ.re` (so `-1/τ + 2` lies on the right edge
`Re = 1`), `T²`-invariance of `λ`, the right-edge reality
`modularLambdaH_one_add_imag_real`, and the Jacobi-derived sum identity
`modularLambdaH_add_S_smul_eq_one`. -/
theorem modularLambdaH_semicircle_real {τ : ℂ} (hτ_im : 0 < τ.im)
    (h_circle : ‖2 * τ - 1‖ = 1) :
    (modularLambdaH τ).im = 0 := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ_im
  -- Geometric step: |τ|² = τ.re, hence τ.re > 0.
  have h_normSq : Complex.normSq τ = τ.re :=
    Gamma2FundamentalDomain_semicircle_normSq_eq_re h_circle
  have h_re_pos : 0 < τ.re := by
    have h_pos : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ_ne
    rw [h_normSq] at h_pos; exact h_pos
  -- Compute (-1/τ).re = -1 and (-1/τ).im = τ.im / τ.re > 0.
  have h_inv_re : (-1 / τ).re = -1 := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by ring]
    rw [Complex.neg_re, Complex.inv_re, h_normSq]
    field_simp
  have h_inv_im : (-1 / τ).im = τ.im / τ.re := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by ring]
    rw [Complex.neg_im, Complex.inv_im, h_normSq]
    field_simp
  -- -1/τ + 2 has Re = 1, Im = τ.im/τ.re > 0.
  have h_shift_re : (-1 / τ + 2).re = 1 := by
    rw [Complex.add_re, h_inv_re]; norm_num
  have h_shift_im : (-1 / τ + 2).im = τ.im / τ.re := by
    rw [Complex.add_im, h_inv_im]; simp
  have h_shift_im_pos : 0 < τ.im / τ.re := div_pos hτ_im h_re_pos
  -- -1/τ + 2 = 1 + Complex.I * (τ.im/τ.re).
  have h_shift_eq : (-1 / τ + 2 : ℂ) = 1 + Complex.I * (τ.im / τ.re : ℝ) := by
    rw [Complex.ext_iff]
    refine ⟨?_, ?_⟩
    · rw [h_shift_re]; simp
    · rw [h_shift_im]; simp
  -- λ(-1/τ + 2) is real by the right-edge lemma.
  have h_right_edge : (modularLambdaH (-1 / τ + 2)).im = 0 := by
    rw [h_shift_eq]
    exact modularLambdaH_one_add_imag_real h_shift_im_pos
  -- By T²-invariance, λ(-1/τ) = λ(-1/τ + 2), hence λ(-1/τ).im = 0.
  have h_lambda_inv : (modularLambdaH (-1 / τ)).im = 0 := by
    have := modularLambdaH_two_add (-1 / τ)
    rw [← this]; exact h_right_edge
  -- Sum identity: λ(τ) = 1 - λ(-1/τ).
  have h_sum := modularLambdaH_add_S_smul_eq_one hτ_im
  have h_lambda_eq : modularLambdaH τ = 1 - modularLambdaH (-1 / τ) := by
    linear_combination h_sum
  rw [h_lambda_eq, Complex.sub_im, h_lambda_inv]
  simp

/-! ## Conjugation symmetry of `λ` and theta nullwerte

The theta series and `λ` have real coefficients, so they satisfy a
reflection identity under `τ ↦ -conj τ` (the imaginary-axis reflection,
which preserves `ℍ`). Combined with `modularLambdaH_image_fundamentalDomainInterior`,
this maps `F^o` to the right half of `F'^o` and gives `λ(F''^o) = lower half`,
which together with the upper half from `F^o` and the boundary reals
covers all of `ℂ ∖ {0, 1}`. -/

/-- **Conjugation symmetry of `θ₃`.** `θ₃(-conj τ) = conj(θ₃ τ)` for
every `τ ∈ ℍ`. Reduction to `jacobiTheta₂_conj` at `z = 0`. -/
theorem theta3_conj_symmetry (τ : ℂ) :
    theta3 (-(starRingEnd ℂ τ)) = starRingEnd ℂ (theta3 τ) := by
  unfold theta3
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂]
  have h := (jacobiTheta₂_conj 0 τ).symm
  -- h : jacobiTheta₂ (conj 0) (-conj τ) = conj (jacobiTheta₂ 0 τ)
  rwa [map_zero] at h

/-- **Conjugation symmetry of `θ₂`.** `θ₂(-conj τ) = conj(θ₂ τ)` for
every `τ ∈ ℍ`. The proof uses `jacobiTheta₂_conj` together with
`jacobiTheta₂_neg_left` to flip the `z = -τ/2` sign back. -/
theorem theta2_conj_symmetry (τ : ℂ) :
    theta2 (-(starRingEnd ℂ τ)) = starRingEnd ℂ (theta2 τ) := by
  unfold theta2
  -- Step 1: Rewrite the exp factor's argument as a conjugate.
  have h_exp : (Real.pi : ℂ) * Complex.I * (-(starRingEnd ℂ τ)) / 4 =
      starRingEnd ℂ ((Real.pi : ℂ) * Complex.I * τ / 4) := by
    rw [map_div₀, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [h_exp, Complex.exp_conj]
  -- Step 2: jacobiTheta₂(-conj τ / 2, -conj τ) = conj(jacobiTheta₂(τ/2, τ)).
  have h_arg : ((-(starRingEnd ℂ τ)) / 2 : ℂ) = starRingEnd ℂ (-(τ / 2)) := by
    rw [map_neg, map_div₀, map_ofNat]; ring
  have h_jt2 : jacobiTheta₂ ((-(starRingEnd ℂ τ)) / 2) (-(starRingEnd ℂ τ)) =
      starRingEnd ℂ (jacobiTheta₂ (τ / 2) τ) := by
    rw [h_arg]
    -- jacobiTheta₂(conj(-τ/2), -conj τ) = conj(jacobiTheta₂(-τ/2, τ))  -- by conj
    -- jacobiTheta₂(-τ/2, τ) = jacobiTheta₂(τ/2, τ)  -- by neg_left
    have h := (jacobiTheta₂_conj (-(τ/2)) τ).symm
    rw [← jacobiTheta₂_neg_left (τ/2) τ]
    exact h
  rw [h_jt2, ← map_mul]

/-- **Conjugation symmetry of `θ₄`.** `θ₄(-conj τ) = conj(θ₄ τ)` for
every `τ ∈ ℂ`. Uses `theta4 τ = jacobiTheta(τ + 1)` and the
2-periodicity of `jacobiTheta`. -/
theorem theta4_conj_symmetry (τ : ℂ) :
    theta4 (-(starRingEnd ℂ τ)) = starRingEnd ℂ (theta4 τ) := by
  unfold theta4
  -- jacobiTheta(-conj τ + 1) = jacobiTheta(-conj(τ - 1))
  --                          = conj(jacobiTheta(τ - 1))
  --                          = conj(jacobiTheta(τ + 1))  (by 2-periodicity).
  have h_neg_conj : -(starRingEnd ℂ τ) + 1 = -(starRingEnd ℂ (τ - 1)) := by
    rw [map_sub, map_one]; ring
  rw [h_neg_conj]
  -- Apply theta3_conj_symmetry at σ = τ - 1.
  have h_step := theta3_conj_symmetry (τ - 1)
  unfold theta3 at h_step
  rw [h_step]
  -- jacobiTheta(τ - 1) = jacobiTheta(τ + 1) by 2-periodicity.
  congr 1
  have h := jacobiTheta_two_add (τ - 1)
  rw [show (2 : ℂ) + (τ - 1) = τ + 1 from by ring] at h
  exact h.symm

/-- **Conjugation symmetry of `λ`.** For `τ ∈ ℍ`, `λ(-conj τ) = conj(λ τ)`.
The proof divides the `θ₂` and `θ₃` conjugation identities. -/
theorem modularLambdaH_conj_symmetry {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (-(starRingEnd ℂ τ)) = starRingEnd ℂ (modularLambdaH τ) := by
  unfold modularLambdaH
  rw [theta2_conj_symmetry τ, theta3_conj_symmetry τ]
  have h3_ne : theta3 τ ≠ 0 := theta3_ne_zero hτ
  rw [map_div₀, map_pow, map_pow]

/-- **Cusp `1`:** `Re(λ(1 + iy)) → −∞` as `y → 0⁺`. Proof via the
modular identity `λ(τ + 1) = λ(τ)/(λ(τ) − 1)` (derived from
`modularLambdaH_T_smul` and `jacobi_identity` divided through by `θ₃⁴`).
With the cusp-`0` limit `λ(iy) → 1` and the strict bound `λ(iy) < 1`
(from `1 − λ(iy) = (θ₄/θ₃)⁴(iy) > 0`), we get `λ(iy) − 1 → 0⁻`. Then
`1/(λ(iy)−1) → −∞` and `λ(iy)/(λ(iy)−1) → 1·(−∞) = −∞`. -/
theorem modularLambdaH_one_add_iy_tendsto_neg_infty_atZeroPos :
    Tendsto (fun y : ℝ => (modularLambdaH (1 + Complex.I * y)).re)
      (𝓝[>] (0 : ℝ)) atBot := by
  -- Step 1: g y := (λ(I·y)).re → 1.
  have h_g_to_one : Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h_lambda := modularLambdaH_iy_tendsto_one_atZeroPos
    have h_re : Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.re 1)) :=
      (Complex.continuous_re.tendsto _).comp h_lambda
    simpa using h_re
  -- Step 2: g y < 1 for y > 0.
  have h_g_lt_one : ∀ᶠ (y : ℝ) in 𝓝[>] (0 : ℝ),
      (modularLambdaH (Complex.I * (y : ℂ))).re < 1 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy_pos : (0 : ℝ) < y := hy
    have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
        Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
      exact hy_pos
    have h_ne_one : modularLambdaH (Complex.I * (y : ℂ)) ≠ 1 :=
      modularLambdaH_ne_one hτ_im
    have h_jacobi : theta2 (Complex.I * (y : ℂ)) ^ 4 +
        theta4 (Complex.I * (y : ℂ)) ^ 4 =
        theta3 (Complex.I * (y : ℂ)) ^ 4 := jacobi_identity hτ_im
    have hne3 : theta3 (Complex.I * (y : ℂ)) ≠ 0 := theta3_ne_zero hτ_im
    have hne4 : theta4 (Complex.I * (y : ℂ)) ≠ 0 := theta4_ne_zero hτ_im
    have h_one_sub : (1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ)) =
        theta4 (Complex.I * (y : ℂ)) ^ 4 / theta3 (Complex.I * (y : ℂ)) ^ 4 := by
      unfold modularLambdaH
      field_simp
      linear_combination -h_jacobi
    have h4_im : (theta4 (Complex.I * (y : ℂ))).im = 0 := theta4_pure_imag_real hy_pos
    have h3_im : (theta3 (Complex.I * (y : ℂ))).im = 0 := theta3_pure_imag_real hy_pos
    have h_t4_eq : theta4 (Complex.I * (y : ℂ)) =
        ((theta4 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h4_im]
    have h_t3_eq : theta3 (Complex.I * (y : ℂ)) =
        ((theta3 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h3_im]
    have ht3_re_ne : (theta3 (Complex.I * (y : ℂ))).re ≠ 0 := by
      intro h
      apply hne3
      rw [h_t3_eq, h]; simp
    have ht4_re_ne : (theta4 (Complex.I * (y : ℂ))).re ≠ 0 := by
      intro h
      apply hne4
      rw [h_t4_eq, h]; simp
    have h_quot_eq : theta4 (Complex.I * (y : ℂ)) ^ 4 /
        theta3 (Complex.I * (y : ℂ)) ^ 4 =
        ((((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) : ℂ) := by
      conv_lhs => rw [h_t4_eq, h_t3_eq]
      push_cast; ring
    rw [h_quot_eq] at h_one_sub
    have h_nonneg : (0 : ℝ) ≤ ((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 := by positivity
    have h_pos : (0 : ℝ) < ((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 := by
      refine lt_of_le_of_ne h_nonneg (fun h_zero => ?_)
      have h_quot_zero : (theta4 (Complex.I * (y : ℂ))).re /
          (theta3 (Complex.I * (y : ℂ))).re = 0 :=
        pow_eq_zero_iff (n := 4) (by norm_num : (4 : ℕ) ≠ 0) |>.mp h_zero.symm
      rw [div_eq_zero_iff] at h_quot_zero
      rcases h_quot_zero with h | h
      · exact ht4_re_ne h
      · exact ht3_re_ne h
    have h_re_eq : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        (((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) := by
      rw [h_one_sub, Complex.ofReal_re]
    have h_sub_re : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        1 - (modularLambdaH (Complex.I * (y : ℂ))).re := by simp
    rw [h_sub_re] at h_re_eq
    linarith
  -- Step 3: g y - 1 ∈ 𝓝[<] 0 (eventually).
  have h_sub_to_zero_below :
      Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re - 1)
        (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := h_g_to_one.sub_const 1
      simpa using this
    · filter_upwards [h_g_lt_one] with y hy
      change (modularLambdaH (Complex.I * (y : ℂ))).re - 1 < 0
      linarith
  -- Step 4: 1/(g y - 1) → atBot.
  have h_inv_atBot :
      Tendsto (fun y : ℝ => ((modularLambdaH (Complex.I * (y : ℂ))).re - 1)⁻¹)
        (𝓝[>] (0 : ℝ)) atBot :=
    tendsto_inv_nhdsLT_zero.comp h_sub_to_zero_below
  -- Step 5: g(y) * 1/(g(y) - 1) → 1 · atBot = atBot.
  have h_prod : Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re *
      ((modularLambdaH (Complex.I * (y : ℂ))).re - 1)⁻¹)
      (𝓝[>] (0 : ℝ)) atBot :=
    h_g_to_one.pos_mul_atBot one_pos h_inv_atBot
  -- Step 6: For y > 0, (λ(1+iy)).re = g(y) * 1/(g(y) - 1).
  have h_id : (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re *
        ((modularLambdaH (Complex.I * (y : ℂ))).re - 1)⁻¹) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun y : ℝ => (modularLambdaH (1 + Complex.I * y)).re) := by
    filter_upwards [self_mem_nhdsWithin, h_g_lt_one] with y hy h_lt
    have hy_pos : (0 : ℝ) < y := hy
    have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
        Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
      exact hy_pos
    have h_jacobi : theta2 (Complex.I * (y : ℂ)) ^ 4 +
        theta4 (Complex.I * (y : ℂ)) ^ 4 =
        theta3 (Complex.I * (y : ℂ)) ^ 4 := jacobi_identity hτ_im
    have hne3 : theta3 (Complex.I * (y : ℂ)) ≠ 0 := theta3_ne_zero hτ_im
    have hne4 : theta4 (Complex.I * (y : ℂ)) ≠ 0 := theta4_ne_zero hτ_im
    have h_im_iy : (modularLambdaH (Complex.I * (y : ℂ))).im = 0 :=
      modularLambdaH_pure_imag_real hy_pos
    have h_lam_sub_ne : modularLambdaH (Complex.I * (y : ℂ)) - 1 ≠ 0 :=
      sub_ne_zero.mpr (modularLambdaH_ne_one hτ_im)
    have h_complex_id : modularLambdaH (1 + Complex.I * (y : ℂ)) =
        modularLambdaH (Complex.I * (y : ℂ)) /
        (modularLambdaH (Complex.I * (y : ℂ)) - 1) := by
      rw [show (1 + Complex.I * (y : ℂ) : ℂ) = Complex.I * (y : ℂ) + 1 from by ring]
      rw [modularLambdaH_T_smul, eq_div_iff h_lam_sub_ne]
      unfold modularLambdaH
      field_simp
      linear_combination -(theta2 (Complex.I * (y : ℂ)) ^ 4) * h_jacobi
    have ha_eq : modularLambdaH (Complex.I * (y : ℂ)) =
        ((modularLambdaH (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h_im_iy]
    have hb_im : (modularLambdaH (Complex.I * (y : ℂ)) - 1).im = 0 := by
      simp [Complex.sub_im, h_im_iy]
    have hb_eq : modularLambdaH (Complex.I * (y : ℂ)) - 1 =
        (((modularLambdaH (Complex.I * (y : ℂ))).re - 1 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hb_im]
    have hb_re_ne : ((modularLambdaH (Complex.I * (y : ℂ))).re - 1 : ℝ) ≠ 0 := by
      intro h
      have : (modularLambdaH (Complex.I * (y : ℂ))).re = 1 := by linarith
      linarith
    -- Compute the RHS using h_complex_id and reality of numerator/denominator.
    have h_rhs_eq : (modularLambdaH (1 + Complex.I * (y : ℂ))).re =
        (modularLambdaH (Complex.I * (y : ℂ))).re /
        ((modularLambdaH (Complex.I * (y : ℂ))).re - 1) := by
      rw [h_complex_id, ha_eq]
      rw [show ((modularLambdaH (Complex.I * (y : ℂ))).re : ℂ) - 1 =
          (((modularLambdaH (Complex.I * (y : ℂ))).re - 1 : ℝ) : ℂ) from by push_cast; ring]
      rw [← Complex.ofReal_div]
      exact Complex.ofReal_re _
    rw [h_rhs_eq]
    field_simp
  exact h_prod.congr' h_id

/-! ## Biholomorphism of `λ` on `F^o`

The modular function `λ` restricted to the open fundamental domain
`F^o` maps onto the open upper half of `ℂ`. The proof is topological,
with three steps:

* `modularLambdaH_F_im_pos` (Step A): `λ(F^o) ⊆ {Im w > 0}` (the image
  lies entirely in the upper half-plane).
* `modularLambdaH_F_image_isOpen` (Step B): `λ(F^o)` is open in `ℂ`
  (open-mapping theorem for non-constant analytic functions on a
  connected open set).
* `modularLambdaH_F_image_isClosed_in_upperHalf` (Step C): `λ(F^o)` is
  closed when viewed inside the upper half-plane (properness: as
  `τ → ∂F^o`, `λ(τ) → ℝ ∪ {∞}` by the four cusp asymptotic theorems
  and the three boundary-real arc theorems).
* `modularLambdaH_image_fundamentalDomainInterior` (Step D): combining
  the above with connectedness of the upper half-plane and
  non-emptiness of `F^o`. -/

/-- **Witness for Step A.** The specific point `(1+4i)/2 ∈ F^o` has
`Im(λ((1+4i)/2)) > 0`. At `τ = 1/2 + 2i`, `Re(πi·τ) = -2π` and
`Im(πi·τ) = π/2`, so `exp(πi·τ) = i · exp(-2π)` and
`16·exp(πi·τ) = 16i·exp(-2π)` has `Im = 16·exp(-2π) ≈ 0.030`.
By `modularLambdaH_norm_sub_lead_le_of_im_ge_one`, the error is
bounded by `4096·exp(-4π) ≈ 0.014`. Hence `Im(λ) ≥ 0.030 - 0.014 > 0`. -/
theorem modularLambdaH_im_pos_at_witness :
    0 < (modularLambdaH ((1 + 4 * Complex.I) / 2)).im := by
  set τ : ℂ := (1 + 4 * Complex.I) / 2 with hτ_def
  -- τ.re = 1/2, τ.im = 2.
  have hτ_re : τ.re = 1/2 := by
    rw [hτ_def]
    simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
  have hτ_im : τ.im = 2 := by
    rw [hτ_def]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
    norm_num
  have hτ_im_ge_one : 1 ≤ τ.im := by rw [hτ_im]; norm_num
  -- (πi · τ).re = -2π, (πi · τ).im = π/2.
  have h_arg_re : (Real.pi * Complex.I * τ).re = -(2 * Real.pi) := by
    rw [show ((Real.pi : ℂ) * Complex.I * τ : ℂ) =
        ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) from by ring]
    rw [Complex.mul_re, Complex.mul_re, Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hτ_re, hτ_im]
    ring
  have h_arg_im : (Real.pi * Complex.I * τ).im = Real.pi / 2 := by
    rw [show ((Real.pi : ℂ) * Complex.I * τ : ℂ) =
        ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) from by ring]
    rw [Complex.mul_im, Complex.mul_re, Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hτ_re, hτ_im]
    ring
  -- (exp(πi · τ)).im = exp(-2π) · sin(π/2) = exp(-2π).
  have h_exp_im_compute :
      (Complex.exp (Real.pi * Complex.I * τ)).im = Real.exp (-(2 * Real.pi)) := by
    rw [Complex.exp_im, h_arg_re, h_arg_im, Real.sin_pi_div_two, mul_one]
  -- 16 · exp(πi · τ) has Im = 16 · exp(-2π).
  have h_16exp_im :
      ((16 : ℂ) * Complex.exp (Real.pi * Complex.I * τ)).im =
        16 * Real.exp (-2 * Real.pi) := by
    rw [Complex.mul_im]
    simp [h_exp_im_compute]
  -- Apply leading-term bound.
  have h_bound := modularLambdaH_norm_sub_lead_le_of_im_ge_one hτ_im_ge_one
  -- |Im(λ - 16 exp)| ≤ ‖λ - 16 exp‖ ≤ 4096 exp(-4π) (since τ.im = 2).
  have h_im_le_norm :
      |(modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)).im| ≤
        ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)‖ :=
    Complex.abs_im_le_norm _
  have h_im_ge_neg_bound :
      -(4096 * Real.exp (-2 * Real.pi * τ.im)) ≤
        (modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)).im := by
    have := abs_le.mp h_im_le_norm
    linarith [this.1, h_bound]
  -- τ.im = 2, so exp(-2π · τ.im) = exp(-4π).
  have hτ_im_eq : (-2 * Real.pi * τ.im : ℝ) = -4 * Real.pi := by rw [hτ_im]; ring
  rw [hτ_im_eq] at h_im_ge_neg_bound
  -- Im(λ) = Im(λ - 16 exp) + Im(16 exp).
  have h_lambda_im_decomp :
      (modularLambdaH τ).im =
        (modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)).im +
        ((16 : ℂ) * Complex.exp (Real.pi * Complex.I * τ)).im := by
    rw [Complex.sub_im]; ring
  rw [h_lambda_im_decomp, h_16exp_im]
  -- Im(λ) ≥ -(4096 exp(-4π)) + 16 exp(-2π).
  -- Show 16 exp(-2π) > 4096 exp(-4π), i.e., exp(2π) > 256 = exp(π)² > 16².
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi := by
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
      have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
      rw [h_eq]
      nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
    exact h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have h_exp_2pi_gt_256 : (256 : ℝ) < Real.exp (2 * Real.pi) := by
    have h_eq : Real.exp (2 * Real.pi) = Real.exp Real.pi * Real.exp Real.pi := by
      rw [show (2 * Real.pi : ℝ) = Real.pi + Real.pi from by ring, Real.exp_add]
    rw [h_eq]
    nlinarith [h_exp_pi_gt_16, Real.exp_pos Real.pi]
  -- 4096 exp(-4π) = (4096 / exp(2π)) · exp(-2π) < 16 · exp(-2π).
  have h_exp_neg_4pi : Real.exp (-4 * Real.pi) =
      Real.exp (-2 * Real.pi) * Real.exp (-2 * Real.pi) := by
    rw [show (-4 * Real.pi : ℝ) = (-2 * Real.pi) + (-2 * Real.pi) from by ring, Real.exp_add]
  have h_exp_neg_2pi_lt : Real.exp (-2 * Real.pi) < 1 / 256 := by
    have h_eq : Real.exp (-2 * Real.pi) = (Real.exp (2 * Real.pi))⁻¹ := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
    rw [h_eq, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/256),
      show (1/256 : ℝ)⁻¹ = 256 from by norm_num]
    exact h_exp_2pi_gt_256
  have h_exp_2pi_pos : 0 < Real.exp (-2 * Real.pi) := Real.exp_pos _
  -- Combine.
  have h_4096_lt : 4096 * Real.exp (-4 * Real.pi) < 16 * Real.exp (-2 * Real.pi) := by
    rw [h_exp_neg_4pi]
    -- 4096 * exp(-2π) * exp(-2π) < 16 * exp(-2π) iff 4096 * exp(-2π) < 16
    -- iff exp(-2π) < 16/4096 = 1/256.
    have h_step : 4096 * Real.exp (-2 * Real.pi) < 16 := by
      have : (4096 : ℝ) * (1/256) = 16 := by norm_num
      calc 4096 * Real.exp (-2 * Real.pi)
          < 4096 * (1/256 : ℝ) := by
            apply mul_lt_mul_of_pos_left h_exp_neg_2pi_lt
            norm_num
        _ = 16 := this
    calc 4096 * (Real.exp (-2 * Real.pi) * Real.exp (-2 * Real.pi))
        = (4096 * Real.exp (-2 * Real.pi)) * Real.exp (-2 * Real.pi) := by ring
      _ < 16 * Real.exp (-2 * Real.pi) :=
          mul_lt_mul_of_pos_right h_step h_exp_2pi_pos
  linarith

/-- **Sub-lemma for Step A: F^o is preconnected.** The open fundamental
domain is connected as a topological subspace of `ℂ`. Geometrically,
F^o is the open strip `0 < Re τ < 1, Im τ > 0` with the closed
semi-disk `|2τ − 1| ≤ 1` (which touches the strip's boundary tangentially)
removed. This is path-connected: any two points can be joined via
the "high cap" `{τ : Im τ ≥ 2}` which is convex (hence path-connected).

**Proof outline:**
* The "top" `T := {z : 0 < Re z < 1, 1 < Im z}` is convex (intersection
  of three open half-planes), hence path-connected.
* `T ⊆ F^o` because for `Im z > 1`, `|2z − 1|² ≥ (2 Im z)² > 4 > 1`.
* For any `τ ∈ F^o`, the vertical line from `τ` to `τ + 2i` stays in
  `F^o` (since `Re` is constant in `(0,1)`, `Im` increases, and
  `|2(τ + 2ti) − 1|² ≥ |2τ − 1|² > 1` because the imaginary part of
  `2(τ + 2ti) − 1 = 2τ − 1 + 4ti` is shifted up by `4t ≥ 0`, increasing
  the absolute value).
* `τ + 2i` lies in `T` (with `Im (τ + 2i) = Im τ + 2 ≥ 2 > 1`).
* Hence every `τ ∈ F^o` can be joined to `τ + 2i ∈ T` by a vertical
  line in `F^o`, and `T` is convex/path-connected.
* `JoinedIn.trans` chains these segments to give path-connectedness. -/
theorem Gamma2FundamentalDomainInterior_isPreconnected :
    IsPreconnected Gamma2FundamentalDomainInterior := by
  suffices h : IsPathConnected Gamma2FundamentalDomainInterior from
    h.isConnected.isPreconnected
  -- Base point: τ₀ = (1+4i)/2 = 1/2 + 2i.
  set τ₀ : ℂ := (1 + 4 * Complex.I) / 2 with hτ₀_def
  have hτ₀_im : τ₀.im = 2 := by
    rw [hτ₀_def]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
    norm_num
  have hτ₀_re : τ₀.re = 1/2 := by
    rw [hτ₀_def]
    simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
  -- τ₀ ∈ F^o.
  have hτ₀_in_F : τ₀ ∈ Gamma2FundamentalDomainInterior := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hτ₀_im]; norm_num
    · rw [hτ₀_re]; norm_num
    · rw [hτ₀_re]; norm_num
    · -- |2τ₀ - 1| = |1 + 4i - 1| = |4i| = 4 > 1.
      have heq : 2 * τ₀ - 1 = 4 * Complex.I := by rw [hτ₀_def]; ring
      rw [heq]
      simp
  refine ⟨τ₀, hτ₀_in_F, ?_⟩
  intro τ hτ
  -- Construct JoinedIn F^o τ₀ τ.
  -- Step 1: vertical line from τ₀ to (1/2 + i(Im τ + 3)) - stays in F^o.
  -- Step 2: horizontal line from (1/2 + i(Im τ + 3)) to (Re τ + i(Im τ + 3)) - stays in F^o.
  -- Step 3: vertical line from (Re τ + i(Im τ + 3)) to τ - stays in F^o.
  set M : ℝ := τ.im + 3 with hM_def
  have hM_ge_2 : (2 : ℝ) ≤ M := by rw [hM_def]; linarith [hτ.1]
  -- Top half-strip T := {z : 0 < Re z < 1, 1 < Im z}.
  set T : Set ℂ := { z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < z.im } with hT_def
  -- T ⊆ F^o.
  have hT_sub_F : T ⊆ Gamma2FundamentalDomainInterior := by
    intro z hz
    refine ⟨?_, hz.1, hz.2.1, ?_⟩
    · linarith [hz.2.2]
    · -- |2z - 1| > 1: (2 Re - 1)² + (2 Im)² > 1, since (2 Im)² > 4.
      have h_norm_sq : ‖2 * z - 1‖^2 = (2 * z.re - 1)^2 + (2 * z.im)^2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
          Complex.mul_im]
        ring
      have h_im_sq : 4 < (2 * z.im)^2 := by nlinarith [hz.2.2]
      have h_sum : 1 < (2 * z.re - 1)^2 + (2 * z.im)^2 := by nlinarith [sq_nonneg (2 * z.re - 1)]
      have h_norm_pos : 0 < ‖2 * z - 1‖ := by
        rcases lt_or_eq_of_le (norm_nonneg (2 * z - 1)) with h | h
        · exact h
        · exfalso
          rw [← h] at h_norm_sq
          nlinarith
      nlinarith [sq_nonneg (‖2 * z - 1‖ - 1)]
  -- T is convex.
  have hT_convex : Convex ℝ T := by
    intro z₁ hz₁ z₂ hz₂ s t hs ht hst
    rcases hz₁ with ⟨hz₁_re_pos, hz₁_re_lt, hz₁_im⟩
    rcases hz₂ with ⟨hz₂_re_pos, hz₂_re_lt, hz₂_im⟩
    refine ⟨?_, ?_, ?_⟩
    · change 0 < (s • z₁ + t • z₂).re
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · nlinarith
      · have ht_pos : 0 < t := by linarith
        nlinarith
    · change (s • z₁ + t • z₂).re < 1
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : s * z₁.re < s * 1 := mul_lt_mul_of_pos_left hz₁_re_lt hs_pos
        have h2 : t * z₂.re ≤ t * 1 := mul_le_mul_of_nonneg_left hz₂_re_lt.le ht
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : s * z₁.re ≤ s * 1 := mul_le_mul_of_nonneg_left hz₁_re_lt.le hs
        have h2 : t * z₂.re < t * 1 := mul_lt_mul_of_pos_left hz₂_re_lt ht_pos
        linarith
    · change 1 < (s • z₁ + t • z₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · nlinarith
      · have ht_pos : 0 < t := by linarith
        nlinarith
  -- T is nonempty (contains τ₀).
  have hτ₀_in_T : τ₀ ∈ T := ⟨by rw [hτ₀_re]; norm_num,
    by rw [hτ₀_re]; norm_num, by rw [hτ₀_im]; norm_num⟩
  -- T is path-connected.
  have hT_pc : IsPathConnected T := hT_convex.isPathConnected ⟨τ₀, hτ₀_in_T⟩
  -- Build intermediate points.
  set p₁ : ℂ := ⟨(1 : ℝ)/2, M⟩ with hp₁_def
  set p₂ : ℂ := ⟨τ.re, M⟩ with hp₂_def
  have hp₁_re : p₁.re = 1/2 := rfl
  have hp₁_im : p₁.im = M := rfl
  have hp₂_re : p₂.re = τ.re := rfl
  have hp₂_im : p₂.im = M := rfl
  -- p₁ ∈ T.
  have hp₁_in_T : p₁ ∈ T := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hp₁_re]; norm_num
    · rw [hp₁_re]; norm_num
    · rw [hp₁_im]; linarith
  -- p₂ ∈ T.
  have hp₂_in_T : p₂ ∈ T := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hp₂_re]; exact hτ.2.1
    · rw [hp₂_re]; exact hτ.2.2.1
    · rw [hp₂_im]; linarith
  -- Step 1: JoinedIn T τ₀ p₁.
  have h_joined_τ₀_p₁ : JoinedIn T τ₀ p₁ := hT_pc.joinedIn _ hτ₀_in_T _ hp₁_in_T
  -- Step 2: JoinedIn T p₁ p₂.
  have h_joined_p₁_p₂ : JoinedIn T p₁ p₂ := hT_pc.joinedIn _ hp₁_in_T _ hp₂_in_T
  -- Step 3: JoinedIn F^o p₂ τ via vertical line at Re = τ.re.
  -- Use Convex.isPathConnected on segment ℝ p₂ τ.
  have h_joined_p₂_τ : JoinedIn Gamma2FundamentalDomainInterior p₂ τ := by
    have h_seg_convex : Convex ℝ (segment ℝ p₂ τ) := convex_segment p₂ τ
    have h_seg_nonempty : (segment ℝ p₂ τ).Nonempty := ⟨p₂, left_mem_segment ℝ p₂ τ⟩
    have h_seg_pc : IsPathConnected (segment ℝ p₂ τ) :=
      h_seg_convex.isPathConnected h_seg_nonempty
    have h_p₂_mem : p₂ ∈ segment ℝ p₂ τ := left_mem_segment ℝ p₂ τ
    have h_τ_mem : τ ∈ segment ℝ p₂ τ := right_mem_segment ℝ p₂ τ
    have h_joined_seg : JoinedIn (segment ℝ p₂ τ) p₂ τ :=
      h_seg_pc.joinedIn _ h_p₂_mem _ h_τ_mem
    -- Show segment ⊆ F^o.
    have h_seg_sub_F : segment ℝ p₂ τ ⊆ Gamma2FundamentalDomainInterior := by
      intro z hz
      rcases hz with ⟨a, b, ha, hb, hab, h_eq⟩
      -- z = a • p₂ + b • τ.
      -- z.re = a · τ.re + b · τ.re = τ.re (since p₂.re = τ.re).
      have hz_re : z.re = τ.re := by
        rw [← h_eq, Complex.add_re, Complex.smul_re, Complex.smul_re,
          smul_eq_mul, smul_eq_mul, hp₂_re]
        linear_combination τ.re * hab
      -- z.im = a · M + b · τ.im.
      have hz_im : z.im = a * M + b * τ.im := by
        rw [← h_eq, Complex.add_im, Complex.smul_im, Complex.smul_im,
          smul_eq_mul, smul_eq_mul, hp₂_im]
      -- z.im ≥ τ.im.
      have hz_im_ge : τ.im ≤ z.im := by
        rw [hz_im, hM_def]
        nlinarith [hτ.1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith [hτ.1]
      · rw [hz_re]; exact hτ.2.1
      · rw [hz_re]; exact hτ.2.2.1
      · -- |2z - 1|² ≥ |2τ - 1|² > 1.
        have h_norm_sq_z : ‖2 * z - 1‖^2 = (2 * z.re - 1)^2 + (2 * z.im)^2 := by
          rw [Complex.sq_norm]
          simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
            Complex.mul_im]
          ring
        have h_norm_sq_τ : ‖2 * τ - 1‖^2 = (2 * τ.re - 1)^2 + (2 * τ.im)^2 := by
          rw [Complex.sq_norm]
          simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
            Complex.mul_im]
          ring
        have h_norm_τ_gt : 1 < ‖2 * τ - 1‖ := hτ.2.2.2
        have h_im_sq_ge : (2 * τ.im)^2 ≤ (2 * z.im)^2 := by
          have h_im_nn : 0 ≤ τ.im := hτ.1.le
          have h_z_im_nn : 0 ≤ z.im := h_im_nn.trans hz_im_ge
          nlinarith
        have h_re_eq : (2 * z.re - 1)^2 = (2 * τ.re - 1)^2 := by rw [hz_re]
        have h_norm_sq_ge : ‖2 * τ - 1‖^2 ≤ ‖2 * z - 1‖^2 := by
          rw [h_norm_sq_z, h_norm_sq_τ, h_re_eq]
          linarith
        have h_norm_pos_τ : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
        have h_norm_pos_z : 0 ≤ ‖2 * z - 1‖ := norm_nonneg _
        have h_z_ge_τ : ‖2 * τ - 1‖ ≤ ‖2 * z - 1‖ := by
          have h1 := sq_nonneg (‖2 * τ - 1‖ - ‖2 * z - 1‖)
          nlinarith
        linarith
    exact h_joined_seg.mono h_seg_sub_F
  -- Combine.
  have h_joined_τ₀_p₂ : JoinedIn Gamma2FundamentalDomainInterior τ₀ p₂ := by
    apply JoinedIn.trans
    · exact (h_joined_τ₀_p₁.mono hT_sub_F)
    · exact (h_joined_p₁_p₂.mono hT_sub_F)
  exact h_joined_τ₀_p₂.trans h_joined_p₂_τ

/-- **Sub-lemma for Step A: `Im(λ) ≠ 0` on `F^o`.** The modular function
`λ` takes no real values on the open fundamental domain. This is the
deep step in Step A's proof; it follows from the fundamental-domain
property (λ is injective on F^o up to Γ(2), and λ takes real values
only on the Γ(2)-orbit of the boundary arcs, which doesn't intersect
F^o). Equivalently: F^o ∩ λ⁻¹(ℝ) = ∅. -/
theorem modularLambdaH_im_ne_zero_on_F :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, (modularLambdaH τ).im ≠ 0 := by
  sorry

/-- **Step A: `λ(F^o) ⊆ {Im w > 0}`.** The image of `F^o` under `λ` lies
in the open upper half-plane. Combines the witness
`modularLambdaH_im_pos_at_witness` with the "Im(λ) ≠ 0 on F^o" claim
via preconnectedness of F^o. The set
`U := F^o ∩ {Im(λ z) > 0}` is open and non-empty (by the witness); the
set `V := F^o ∩ {Im(λ z) < 0}` is open and disjoint from `U`. By
`modularLambdaH_im_ne_zero_on_F`, the two sets cover F^o. By
`IsPreconnected.subset_left_of_subset_union`, F^o ⊆ U. -/
theorem modularLambdaH_F_im_pos :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, 0 < (modularLambdaH τ).im := by
  -- Set up the "good" set U and "bad" set V.
  set U : Set ℂ := Gamma2FundamentalDomainInterior ∩ {z : ℂ | 0 < (modularLambdaH z).im}
    with hU_def
  set V : Set ℂ := Gamma2FundamentalDomainInterior ∩ {z : ℂ | (modularLambdaH z).im < 0}
    with hV_def
  -- U and V are open in ℂ.
  have hF_open : IsOpen Gamma2FundamentalDomainInterior :=
    Gamma2FundamentalDomainInterior_isOpen
  have hF_sub_H : Gamma2FundamentalDomainInterior ⊆ { z : ℂ | 0 < z.im } :=
    Gamma2FundamentalDomainInterior_subset_upperHalf
  have h_cont_lam :
      ContinuousOn modularLambdaH Gamma2FundamentalDomainInterior :=
    modularLambdaH_differentiableOn.continuousOn.mono hF_sub_H
  have h_cont_im :
      ContinuousOn (fun z => (modularLambdaH z).im) Gamma2FundamentalDomainInterior :=
    Complex.continuous_im.continuousOn.comp h_cont_lam (Set.mapsTo_univ _ _)
  have hU_open : IsOpen U :=
    h_cont_im.isOpen_inter_preimage hF_open isOpen_Ioi
  have hV_open : IsOpen V :=
    h_cont_im.isOpen_inter_preimage hF_open isOpen_Iio
  -- U and V are disjoint.
  have hUV_disj : Disjoint U V := by
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.eq_empty_of_forall_notMem
    intro z hz
    have h1 : 0 < (modularLambdaH z).im := hz.1.2
    have h2 : (modularLambdaH z).im < 0 := hz.2.2
    linarith
  -- F^o ⊆ U ∪ V (using Im(λ) ≠ 0 on F^o).
  have hF_sub_UV : Gamma2FundamentalDomainInterior ⊆ U ∪ V := by
    intro z hz
    have h_ne := modularLambdaH_im_ne_zero_on_F z hz
    rcases lt_or_gt_of_ne h_ne with h_neg | h_pos
    · right; exact ⟨hz, h_neg⟩
    · left; exact ⟨hz, h_pos⟩
  -- F^o ∩ U is non-empty (witness (1+4i)/2 ∈ F^o with Im(λ) > 0).
  have h_witness_in_F : ((1 + 4 * Complex.I) / 2) ∈ Gamma2FundamentalDomainInterior := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
    · simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
    · change ((1 + 4 * Complex.I) / 2 : ℂ).re < 1
      rw [show ((1 + 4 * Complex.I) / 2 : ℂ) = (1 : ℂ) / 2 + 2 * Complex.I from by ring]
      simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
        Complex.normSq_ofNat]
      norm_num
    · have heq : 2 * (((1 : ℂ) + 4 * Complex.I) / 2) - 1 = 4 * Complex.I := by ring
      rw [heq]
      simp
  have hF_inter_U_nonempty : (Gamma2FundamentalDomainInterior ∩ U).Nonempty := by
    refine ⟨((1 + 4 * Complex.I) / 2), h_witness_in_F, h_witness_in_F, ?_⟩
    exact modularLambdaH_im_pos_at_witness
  -- F^o is preconnected.
  have hF_preconn := Gamma2FundamentalDomainInterior_isPreconnected
  -- By IsPreconnected.subset_left_of_subset_union, F^o ⊆ U.
  have hF_sub_U : Gamma2FundamentalDomainInterior ⊆ U :=
    hF_preconn.subset_left_of_subset_union hU_open hV_open hUV_disj hF_sub_UV
      hF_inter_U_nonempty
  -- Hence for any τ ∈ F^o, 0 < (modularLambdaH τ).im.
  intro τ hτ
  exact (hF_sub_U hτ).2

/-- **Step B: `λ(F^o)` is open.** By the open-mapping theorem for
non-constant analytic functions on the preconnected open set `F^o`. -/
theorem modularLambdaH_F_image_isOpen :
    IsOpen (modularLambdaH '' Gamma2FundamentalDomainInterior) := by
  -- Apply the open-mapping theorem globally on the upper half-plane ℍ.
  set ℍ : Set ℂ := { τ : ℂ | 0 < τ.im }
  -- λ is analytic on ℍ.
  have hℍ_open : IsOpen ℍ := by
    have : ℍ = Complex.im ⁻¹' Set.Ioi 0 := by ext τ; simp [ℍ]
    rw [this]
    exact isOpen_Ioi.preimage Complex.continuous_im
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH ℍ :=
    modularLambdaH_differentiableOn.analyticOnNhd hℍ_open
  -- ℍ is preconnected (convex).
  have hℍ_preconn : IsPreconnected ℍ := by
    have hconv : Convex ℝ ℍ := by
      intro w₁ hw₁ w₂ hw₂ s t hs ht hst
      change 0 < (s • w₁ + t • w₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
        have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
        have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
        linarith
    exact hconv.isPreconnected
  -- λ is not constant on ℍ (cusp limits force two different values).
  have h_lam_not_const : ¬ (∃ w, ∀ z ∈ ℍ, modularLambdaH z = w) := by
    rintro ⟨w, hconst⟩
    have hI_im : Complex.I.im = 1 := Complex.I_im
    -- λ(iy) → 0 as y → ∞ but λ(iy) → 1 as y → 0+. If λ ≡ w, then w = 0 = 1.
    have h_mul_in : ∀ y : ℝ, 0 < y → (Complex.I * (y : ℂ)) ∈ ℍ := by
      intro y hy_pos
      change 0 < (Complex.I * (y : ℂ)).im
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
      simpa using hy_pos
    have hlim_zero := modularLambdaH_iy_tendsto_zero_atTop
    have hlim_one := modularLambdaH_iy_tendsto_one_atZeroPos
    have hw_zero : w = 0 := by
      have hcst :
          Tendsto (fun y : ℝ => modularLambdaH (Complex.I * (y : ℂ))) atTop (𝓝 w) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy_pos
        exact (hconst (Complex.I * (y : ℂ)) (h_mul_in y hy_pos)).symm
      exact tendsto_nhds_unique hcst hlim_zero
    have hw_one : w = 1 := by
      have hcst :
          Tendsto (fun y : ℝ => modularLambdaH (Complex.I * (y : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with y hy_pos
        exact (hconst (Complex.I * (y : ℂ)) (h_mul_in y hy_pos)).symm
      exact tendsto_nhds_unique hcst hlim_one
    -- 0 = w = 1, contradiction.
    have : (0 : ℂ) = 1 := hw_zero.symm.trans hw_one
    exact one_ne_zero this.symm
  -- Apply open-mapping.
  rcases AnalyticOnNhd.is_constant_or_isOpen h_lam_an hℍ_preconn with h_const | h_open
  · exact absurd h_const h_lam_not_const
  · apply h_open
    · intro τ hτ
      exact hτ.1
    · exact Gamma2FundamentalDomainInterior_isOpen

/-- **Step C: `λ(F^o)` is closed in the upper half-plane.** Properness
of `λ|F^o → {Im w > 0}`: as `τ` approaches the boundary of `F^o`, the
image `λ(τ)` tends to `ℝ ∪ {∞}` (combined from the four cusp
asymptotic lemmas and the three boundary-real arc theorems), so the
preimage of any compact set in `{Im w > 0}` is compact in `F^o`.

**Proof strategy (sequential).** Suppose `wₙ → w` in `{Im w > 0}`,
with `wₙ = λ(τₙ)` for some `τₙ ∈ F^o`. Show `w ∈ λ(F^o)`. Case-split
on the sequence `(τₙ)`:

* **Bounded with limit in `F^o`**: by continuity, `λ(τ) = w ∈ λ(F^o)`.
* **Bounded with limit `τ* ∈ ∂F^o ∩ ℍ`** (on a boundary arc):
  `λ(τ*) ∈ ℝ` by the boundary-real lemmas; but `wₙ → w` with
  `Im w > 0`, contradicting `w = λ(τ*) ∈ ℝ`.
* **Bounded with limit `τ* = 0`** (cusp 0): need `λ(τₙ) → 1` for any
  approach to `0` in `F^o`. Uses the S-shift identity `λ(τ) + λ(-1/τ) = 1`
  plus `Im(-1/τₙ) → ∞` (which holds because the constraint
  `|2τ−1| > 1` in `F^o` forces `|τ|² > Re τ`, giving `|τ|² < 2 (Im τ)²`
  for `τ` near `0`, hence `Im(-1/τ) = Im τ / |τ|² > 1/(2 Im τ) → ∞`).
* **Bounded with limit `τ* = 1`** (cusp 1): need `|λ(τₙ)| → ∞`. Use
  the T-shift identity `λ(τ+1) = λ(τ)/(λ(τ)−1)` to reduce to cusp 0
  case (since `λ(τₙ - 1) → 1` as `τₙ → 1`, then
  `λ(τₙ) → 1/0 = ∞`); contradicts `wₙ → w ∈ ℂ` finite.
* **Unbounded** (`τₙ.im → ∞`, since `Re τₙ ∈ (0,1)` is bounded):
  need uniform cusp ∞ bound `|λ(τ)| ≤ C exp(-π τ.im)` on
  `{τ : τ.im ≥ 1}`. Follows from existing
  `theta2_norm_le_of_im_ge_one : ‖θ₂(τ)‖ ≤ 10 exp(-π τ.im/4)`
  and the implicit lower bound `‖θ₃(τ)‖ ≥ 1/2` (derivable from
  `‖θ₃ - 1‖ ≤ 4 exp(-π τ.im) ≤ 4 exp(-π) < 1/2` for `τ.im ≥ 1`).
  Gives `λ(τₙ) → 0`, contradicting `w ∈ {Im w > 0}`.

All four contradictions rule out the "limit outside `F^o`" cases,
leaving only the "limit in `F^o`" case, which gives `w ∈ λ(F^o)`.

This is held as an architectural `sorry` pending dedicated work to
establish the uniform cusp asymptotics in F^o (specifically, the
non-trivial cusp 0 limit via S-shift and the cusp ∞ norm bound via
existing theta-norm lemmas). -/
theorem modularLambdaH_F_image_isClosed_in_upperHalf :
    IsClosed (((↑) : { w : ℂ // 0 < w.im } → ℂ) ⁻¹'
      (modularLambdaH '' Gamma2FundamentalDomainInterior)) := by
  sorry

/-- **Step D — biholomorphism of `λ` on `F^o`.** Combining Steps A, B,
C and the connectedness of the upper half-plane: `λ(F^o)` is a
nonempty clopen subset of the connected upper half-plane, hence
equals the entire upper half-plane. -/
theorem modularLambdaH_image_fundamentalDomainInterior :
    modularLambdaH '' Gamma2FundamentalDomainInterior = { w : ℂ | 0 < w.im } := by
  -- Set up the subset and the connected ambient space.
  set U : Set ℂ := { w : ℂ | 0 < w.im } with hU_def
  set S : Set ℂ := modularLambdaH '' Gamma2FundamentalDomainInterior with hS_def
  -- Step A: S ⊆ U.
  have hSU : S ⊆ U := by
    rintro w ⟨τ, hτ, rfl⟩
    exact modularLambdaH_F_im_pos τ hτ
  -- Step B: S is open in ℂ.
  have hS_open : IsOpen S := modularLambdaH_F_image_isOpen
  -- Step C: S is closed in U (subspace topology).
  have hS_closed_in_U :
      IsClosed (((↑) : U → ℂ) ⁻¹' S) := modularLambdaH_F_image_isClosed_in_upperHalf
  -- S is open in U (from S open in ℂ, restrict).
  have hS_open_in_U :
      IsOpen (((↑) : U → ℂ) ⁻¹' S) := hS_open.preimage continuous_subtype_val
  -- U is preconnected (the upper half-plane is convex).
  have hU_preconn : IsPreconnected U := by
    have hconv : Convex ℝ U := by
      intro w₁ hw₁ w₂ hw₂ s t hs ht hst
      simp only [hU_def, Set.mem_setOf_eq] at hw₁ hw₂ ⊢
      change 0 < (s • w₁ + t • w₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
        have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
        have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
        linarith
    exact hconv.isPreconnected
  -- S is nonempty: pick the explicit witness (1 + 4i)/2 ∈ F^o.
  have hS_nonempty : S.Nonempty := by
    have hw_in_F : (((1 : ℂ) + 4 * Complex.I) / 2) ∈ Gamma2FundamentalDomainInterior := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
      · simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
      · change ((1 + 4 * Complex.I) / 2 : ℂ).re < 1
        rw [show ((1 + 4 * Complex.I) / 2 : ℂ) = (1 : ℂ) / 2 + 2 * Complex.I from by ring]
        simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
          Complex.normSq_ofNat]
        norm_num
      · have heq : 2 * (((1 : ℂ) + 4 * Complex.I) / 2) - 1 = 4 * Complex.I := by ring
        rw [heq]
        simp
    exact ⟨modularLambdaH _, _, hw_in_F, rfl⟩
  -- The preimage of S in U is nonempty.
  have hSU_pre_nonempty : (((↑) : U → ℂ) ⁻¹' S).Nonempty := by
    obtain ⟨w, hw⟩ := hS_nonempty
    exact ⟨⟨w, hSU hw⟩, hw⟩
  -- Extract a closed set `C` in ℂ such that `C ∩ U = S` (from `hS_closed_in_U`
  -- via the subspace topology induced by `Subtype.val`).
  rw [isClosed_induced_iff] at hS_closed_in_U
  obtain ⟨C, hC_closed, hC_eq⟩ := hS_closed_in_U
  have hCU_eq_S : ∀ w ∈ U, w ∈ C ↔ w ∈ S := by
    intro w hw
    exact iff_of_eq (congrArg (· (⟨w, hw⟩ : U)) hC_eq)
  -- The open complement `Cᶜ` together with `S` covers `U` disjointly.
  have hSC : S ⊆ C := fun w hw => (hCU_eq_S w (hSU hw)).mpr hw
  have hUSC : U ⊆ S ∪ Cᶜ := by
    intro w hwU
    by_cases hwC : w ∈ C
    · exact Or.inl ((hCU_eq_S w hwU).mp hwC)
    · exact Or.inr hwC
  have hSC_disj : Disjoint S Cᶜ := by
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.eq_empty_of_forall_notMem
    intro w hw
    exact hw.2 (hSC hw.1)
  -- Apply IsPreconnected.subset_left_of_subset_union to conclude U ⊆ S.
  have hU_sub_S : U ⊆ S :=
    hU_preconn.subset_left_of_subset_union hS_open hC_closed.isOpen_compl
      hSC_disj hUSC ((Set.inter_eq_self_of_subset_right hSU).symm ▸ hS_nonempty)
  exact Set.eq_of_subset_of_subset hSU hU_sub_S

/-- **`⊆` direction of the biholomorphism:** the image of `F^o` under
`λ` lies in the upper half-plane. Derived from
`modularLambdaH_image_fundamentalDomainInterior`. -/
theorem modularLambdaH_image_F_subset_upperHalf :
    modularLambdaH '' Gamma2FundamentalDomainInterior ⊆ { w : ℂ | 0 < w.im } :=
  modularLambdaH_image_fundamentalDomainInterior.subset

/-- **`⊇` direction of the biholomorphism:** every point `w` with
`Im w > 0` is in `λ(F^o)`. Derived from
`modularLambdaH_image_fundamentalDomainInterior`. -/
theorem modularLambdaH_image_F_supset_upperHalf :
    { w : ℂ | 0 < w.im } ⊆ modularLambdaH '' Gamma2FundamentalDomainInterior :=
  modularLambdaH_image_fundamentalDomainInterior.superset

end RiemannDynamics

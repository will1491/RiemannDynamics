/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.ModularFunction
import RiemannDynamics.Hyperbolic.SchwarzReflection
import RiemannDynamics.Hyperbolic.ArgumentPrinciple

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

/-! ## Biholomorphism (deferred)

The remaining deep step for the surjectivity of `modularLambdaH_image`.
Combined with `modularLambdaH_conj_symmetry` (giving `λ(F''^o) = lower half`)
and the three boundary-real arc theorems, this closes the surjectivity.

The biholomorphism splits into two inclusion-style sorries
(`modularLambdaH_image_F_subset_upperHalf` and
`modularLambdaH_image_F_supset_upperHalf`), each closed via the
argument-principle / winding-number infrastructure architected in
`ArgumentPrinciple.lean`. -/

/-- **Biholomorphism of `λ` on `F^o`.** The modular function `λ`
restricted to the open fundamental domain `F^o` maps bijectively
and holomorphically onto the open upper half of `ℂ ∖ {0, 1}`.

Deferred proof sketch: by the argument principle applied to the
boundary contour of `F^o` (truncated at `Im ≤ R`, then `R → ∞`).
The contour `∂F^o_R` is the piecewise concatenation of:
* Left edge `Re = 0` (vertical), image `λ(iy) ∈ (0, 1)` with
  `λ(iy) → 0` as `y → ∞` (`modularLambdaH_iy_tendsto_zero_atTop`)
  and `λ(iy) → 1` as `y → 0⁺` (`modularLambdaH_iy_tendsto_one_atZeroPos`).
* Semicircle `|2τ−1| = 1`, image `λ(τ) ∈ (1, ∞)` real
  (`modularLambdaH_semicircle_real`).
* Right edge `Re = 1` (vertical), image `λ(1 + iy) ∈ (−∞, 0)` with
  `λ(1+iy) → 0` as `y → ∞` (`modularLambdaH_one_add_iy_tendsto_zero_atTop`)
  and `Re(λ(1+iy)) → −∞` as `y → 0⁺`
  (`modularLambdaH_one_add_iy_tendsto_neg_infty_atZeroPos`).
* Top truncation `Im = R`, image near `0` (from cusp asymptotics).
The image curve `λ(∂F^o_R)` is a closed real curve traversing
`0 → (0,1) → 1 → (1,∞) → ∞ → (−∞,0) → 0`, winding exactly once
counterclockwise around any `w ∈ {Im > 0}` and zero times around any
`w ∈ {Im < 0}`. Combined with `argumentPrinciple_rectangle_preimage_finite`
(finite preimages on rectangles inside F^o), the winding-equals-count
identity gives `card(λ⁻¹{w} ∩ F^o) = 1` for `w ∈ {Im > 0}` and
`= 0` for `w ∈ {Im < 0} ∪ ℝ \ {0, 1}`, yielding the image equality.

This deep content requires winding-number / argument-principle
infrastructure (~500-700 LOC across multiple sessions) and is left
as a single focused sorry; the two inclusion directions
(`modularLambdaH_image_F_subset_upperHalf` and
`modularLambdaH_image_F_supset_upperHalf` below) derive from it. -/
theorem modularLambdaH_image_fundamentalDomainInterior :
    modularLambdaH '' Gamma2FundamentalDomainInterior = { w : ℂ | 0 < w.im } := by
  sorry

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

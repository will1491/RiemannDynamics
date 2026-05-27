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

/-- **Strict monotonicity of `θ₃(iy)`.** The function `y ↦ θ₃(iy).re`
is strictly antitone on `(0, ∞)`. Proof: the series
`θ₃(iy) = 1 + 2 · ∑ exp(−π·n²·y)` consists of positive terms, each
strictly decreasing in `y`; by termwise strict comparison
(`tsum_lt_tsum`), the sum is strictly decreasing. -/
theorem theta3_iy_strictAntitone :
    StrictAntiOn (fun y : ℝ => (theta3 (Complex.I * (y : ℂ))).re) (Set.Ioi 0) := by
  intro y1 hy1 y2 hy2 h_y12
  have hy1' : (0:ℝ) < y1 := hy1
  have hy2' : (0:ℝ) < y2 := hy2
  -- Imaginary parts of the τ's are positive.
  have hτ1_im : 0 < (Complex.I * (y1 : ℂ)).im := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]; exact hy1'
  have hτ2_im : 0 < (Complex.I * (y2 : ℂ)).im := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]; exact hy2'
  -- Each complex term equals a real-coerced real exponential.
  have h_arg : ∀ y : ℝ, ∀ n : ℕ,
      (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 * (Complex.I * (y : ℂ)) =
        ((-Real.pi * ((n : ℝ) + 1)^2 * y : ℝ) : ℂ) := by
    intro y n
    push_cast
    ring_nf
    rw [show (Complex.I : ℂ)^2 = -1 from Complex.I_sq]
    ring
  have h_term : ∀ y : ℝ, ∀ n : ℕ,
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
        (Complex.I * (y : ℂ))) =
        ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ) := by
    intro y n
    rw [h_arg y n, ← Complex.ofReal_exp]
  -- Series for jacobiTheta at τ = I·y.
  have h_sum1 := hasSum_nat_jacobiTheta hτ1_im
  have h_sum2 := hasSum_nat_jacobiTheta hτ2_im
  -- Rewrite the terms in real form.
  have h_sum1' : HasSum
      (fun n : ℕ => ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y1 : ℂ)) - 1) / 2) := by
    convert h_sum1 using 1
    funext n
    exact (h_term y1 n).symm
  have h_sum2' : HasSum
      (fun n : ℕ => ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y2 : ℂ)) - 1) / 2) := by
    convert h_sum2 using 1
    funext n
    exact (h_term y2 n).symm
  -- Take .re of the complex HasSums to get real HasSums.
  have h_sum1_re : HasSum
      (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1))
      ((jacobiTheta (Complex.I * (y1 : ℂ)) - 1).re / 2) := by
    have h_map := h_sum1'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  have h_sum2_re : HasSum
      (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2))
      ((jacobiTheta (Complex.I * (y2 : ℂ)) - 1).re / 2) := by
    have h_map := h_sum2'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  -- Each term is strictly larger for y1.
  have h_term_lt : ∀ n : ℕ,
      Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) <
        Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) := by
    intro n
    apply Real.exp_lt_exp.mpr
    have h_coeff_pos : 0 < Real.pi * ((n : ℝ) + 1)^2 := by
      have : 0 < ((n : ℝ) + 1)^2 := by positivity
      exact mul_pos Real.pi_pos this
    nlinarith
  -- Also need non-strict for tsum_lt_tsum.
  have h_term_le : ∀ n : ℕ,
      Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) ≤
        Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) := fun n => (h_term_lt n).le
  -- Strict comparison of sums.
  have h_tsum_lt : ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) <
      ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) := by
    exact Summable.tsum_lt_tsum h_term_le (h_term_lt 0) h_sum2_re.summable h_sum1_re.summable
  -- Express tsum in terms of jacobiTheta.
  have h_eq1 : ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) =
      (jacobiTheta (Complex.I * (y1 : ℂ)) - 1).re / 2 := h_sum1_re.tsum_eq
  have h_eq2 : ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) =
      (jacobiTheta (Complex.I * (y2 : ℂ)) - 1).re / 2 := h_sum2_re.tsum_eq
  -- Conclude.
  show (theta3 (Complex.I * (y2 : ℂ))).re < (theta3 (Complex.I * (y1 : ℂ))).re
  unfold theta3
  rw [h_eq1, h_eq2] at h_tsum_lt
  -- (jacobiTheta(τ_k) - 1).re/2 strict comparison gives jacobiTheta(τ_k).re comparison.
  have h_re_sub_eq : ∀ y : ℝ, (jacobiTheta (Complex.I * (y : ℂ)) - 1).re =
      (jacobiTheta (Complex.I * (y : ℂ))).re - 1 := by
    intro y; rw [Complex.sub_re, Complex.one_re]
  rw [h_re_sub_eq y1, h_re_sub_eq y2] at h_tsum_lt
  linarith

/-- **Pair-difference algebraic helper.** For `0 < y₁ < y₂` and
`1/y₁ ≤ α₁ < α₂`, the strict inequality
`exp(−α₂·y₁) − exp(−α₂·y₂) < exp(−α₁·y₁) − exp(−α₁·y₂)` holds.
Proof: factor out `exp(−α_i·y₁)`; reduces to comparing
`exp(α₁·d) > (1 − exp(−s·y₂))/(1 − exp(−s·y₁))` where
`s := α₂ − α₁ > 0`, `d := y₂ − y₁ > 0`. The RHS is bounded by `y₂/y₁`
via strict monotonicity of `x ↦ (1 − exp(−x))/x`; the LHS dominates
`exp(d/y₁) > y₂/y₁` via `Real.add_one_lt_exp` applied to
`y₂/y₁ − 1 > 0`. -/
private lemma exp_neg_diff_strict_dec {y1 y2 : ℝ} (hy1 : 0 < y1) (hy12 : y1 < y2)
    {α1 α2 : ℝ} (hα1 : 1 / y1 ≤ α1) (hα12 : α1 < α2) :
    Real.exp (-α2 * y1) - Real.exp (-α2 * y2) <
      Real.exp (-α1 * y1) - Real.exp (-α1 * y2) := by
  have hy2 : 0 < y2 := lt_trans hy1 hy12
  have hd_pos : 0 < y2 - y1 := sub_pos.mpr hy12
  have hα1_pos : 0 < α1 := lt_of_lt_of_le (one_div_pos.mpr hy1) hα1
  have hα2_pos : 0 < α2 := lt_trans hα1_pos hα12
  have hs_pos : 0 < α2 - α1 := sub_pos.mpr hα12
  set s := α2 - α1 with hs_def
  set d := y2 - y1 with hd_def
  -- Auxiliary: x ↦ (1 - exp(-x))/x strict decreasing on (0, ∞).
  -- Equivalent: x₂·(1 - exp(-x₁)) > x₁·(1 - exp(-x₂)) for 0 < x₁ < x₂.
  have key_aux : ∀ {x1 x2 : ℝ}, 0 < x1 → x1 < x2 →
      x1 * (1 - Real.exp (-x2)) < x2 * (1 - Real.exp (-x1)) := by
    intro x1 x2 hx1 h12
    have hδ : 0 < x2 - x1 := sub_pos.mpr h12
    have hx1_ne : x1 ≠ 0 := ne_of_gt hx1
    have hδ_ne : -(x2 - x1) ≠ 0 := by linarith
    -- (1 - exp(-x₁)) > x₁·exp(-x₁): from exp(x₁) > x₁ + 1.
    have h_step1 : x1 * Real.exp (-x1) < 1 - Real.exp (-x1) := by
      have h_exp_x1 : x1 + 1 < Real.exp x1 := Real.add_one_lt_exp hx1_ne
      have h_exp_neg_pos : 0 < Real.exp (-x1) := Real.exp_pos _
      have h_mul : Real.exp (-x1) * (x1 + 1) < Real.exp (-x1) * Real.exp x1 :=
        mul_lt_mul_of_pos_left h_exp_x1 h_exp_neg_pos
      rw [show Real.exp (-x1) * Real.exp x1 = 1 from by rw [← Real.exp_add]; simp] at h_mul
      nlinarith
    -- 1 - exp(-(x₂-x₁)) < x₂ - x₁: from exp(-(x₂-x₁)) > 1 - (x₂-x₁).
    have h_step2 : 1 - Real.exp (-(x2 - x1)) < x2 - x1 := by
      have := Real.add_one_lt_exp hδ_ne
      linarith
    -- Combine: (x₂-x₁)·(1 - exp(-x₁)) > (x₂-x₁)·x₁·exp(-x₁) > x₁·exp(-x₁)·(1 - exp(-(x₂-x₁))).
    have h_a : (x2 - x1) * (x1 * Real.exp (-x1)) < (x2 - x1) * (1 - Real.exp (-x1)) :=
      mul_lt_mul_of_pos_left h_step1 hδ
    have h_b : (1 - Real.exp (-(x2 - x1))) * (x1 * Real.exp (-x1)) <
        (x2 - x1) * (x1 * Real.exp (-x1)) :=
      mul_lt_mul_of_pos_right h_step2 (mul_pos hx1 (Real.exp_pos _))
    have h_combine : (x2 - x1) * (1 - Real.exp (-x1)) >
        x1 * Real.exp (-x1) * (1 - Real.exp (-(x2 - x1))) := by linarith
    -- Algebraic: x₂·(1 - exp(-x₁)) - x₁·(1 - exp(-x₂)) =
    -- (x₂-x₁)·(1 - exp(-x₁)) - x₁·exp(-x₁)·(1 - exp(-(x₂-x₁))).
    have h_expand : x2 * (1 - Real.exp (-x1)) - x1 * (1 - Real.exp (-x2)) =
        (x2 - x1) * (1 - Real.exp (-x1)) -
          x1 * Real.exp (-x1) * (1 - Real.exp (-(x2 - x1))) := by
      have hx2_eq : x2 = x1 + (x2 - x1) := by ring
      rw [show (-x2) = (-x1) + (-(x2 - x1)) from by ring]
      rw [Real.exp_add]
      ring
    linarith
  -- Apply key_aux with x₁ := s·y₁, x₂ := s·y₂.
  have hsy1_pos : 0 < s * y1 := mul_pos hs_pos hy1
  have hsy12 : s * y1 < s * y2 := mul_lt_mul_of_pos_left hy12 hs_pos
  have h_ratio_s : (s * y1) * (1 - Real.exp (-(s * y2))) <
      (s * y2) * (1 - Real.exp (-(s * y1))) := key_aux hsy1_pos hsy12
  -- Divide by s > 0: y₁·(1 - exp(-s·y₂)) < y₂·(1 - exp(-s·y₁)).
  have h_ratio : y1 * (1 - Real.exp (-(s * y2))) < y2 * (1 - Real.exp (-(s * y1))) := by
    have h_lhs_eq : (s * y1) * (1 - Real.exp (-(s * y2))) =
        s * (y1 * (1 - Real.exp (-(s * y2)))) := by ring
    have h_rhs_eq : (s * y2) * (1 - Real.exp (-(s * y1))) =
        s * (y2 * (1 - Real.exp (-(s * y1)))) := by ring
    rw [h_lhs_eq, h_rhs_eq] at h_ratio_s
    exact lt_of_mul_lt_mul_left h_ratio_s hs_pos.le
  -- exp(α₁·d) > y₂/y₁ via α₁·d ≥ y₂/y₁ - 1 (from α₁ ≥ 1/y₁) and add_one_lt_exp.
  have hτ_gt_one : 1 < y2 / y1 := by rw [lt_div_iff₀ hy1, one_mul]; exact hy12
  have hτm_ne : y2 / y1 - 1 ≠ 0 := by linarith
  have h_τ_lt : y2 / y1 < Real.exp (y2 / y1 - 1) := by
    have := Real.add_one_lt_exp hτm_ne; linarith
  have hα1d_ge : y2 / y1 - 1 ≤ α1 * d := by
    have h_eq : y2 / y1 - 1 = (y2 - y1) / y1 := by field_simp
    have h_d_unfold : d = y2 - y1 := hd_def
    rw [h_eq, h_d_unfold, div_le_iff₀ hy1]
    have h_α1_y1 : 1 ≤ α1 * y1 := by
      have h_one : (1 / y1) * y1 = 1 := by field_simp
      have := mul_le_mul_of_nonneg_right hα1 hy1.le
      linarith
    nlinarith [hd_pos]
  have h_exp_α1d_gt : y2 / y1 < Real.exp (α1 * d) :=
    lt_of_lt_of_le h_τ_lt (Real.exp_le_exp.mpr hα1d_ge)
  -- Now derive the main: exp(-α₁·y₁)·(1 - exp(-s·y₁)) > exp(-α₁·y₂)·(1 - exp(-s·y₂)).
  have hp1_pos : 0 < 1 - Real.exp (-(s * y1)) := by
    have : Real.exp (-(s * y1)) < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_strictMono (by linarith)
    linarith
  have h_step_a : y2 < Real.exp (α1 * d) * y1 := by
    have h_mul := mul_lt_mul_of_pos_right h_exp_α1d_gt hy1
    rwa [div_mul_cancel₀ y2 (ne_of_gt hy1)] at h_mul
  have h_step_b : y2 * (1 - Real.exp (-(s * y1))) <
      Real.exp (α1 * d) * y1 * (1 - Real.exp (-(s * y1))) :=
    mul_lt_mul_of_pos_right h_step_a hp1_pos
  have h_step_c : y1 * (1 - Real.exp (-(s * y2))) <
      Real.exp (α1 * d) * y1 * (1 - Real.exp (-(s * y1))) := lt_trans h_ratio h_step_b
  have h_step_d : 1 - Real.exp (-(s * y2)) <
      Real.exp (α1 * d) * (1 - Real.exp (-(s * y1))) := by
    have h_rewrite : Real.exp (α1 * d) * y1 * (1 - Real.exp (-(s * y1))) =
        y1 * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1)))) := by ring
    rw [h_rewrite] at h_step_c
    exact lt_of_mul_lt_mul_left h_step_c hy1.le
  -- Multiply by exp(-α₁·y₂) > 0 and use exp(-α₁·y₂)·exp(α₁·d) = exp(-α₁·y₁).
  have h_exp_neg_α1y2_pos : 0 < Real.exp (-α1 * y2) := Real.exp_pos _
  have h_step_e : Real.exp (-α1 * y2) * (1 - Real.exp (-(s * y2))) <
      Real.exp (-α1 * y2) * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1)))) :=
    mul_lt_mul_of_pos_left h_step_d h_exp_neg_α1y2_pos
  have h_eq_combine : Real.exp (-α1 * y2) * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1)))) =
      Real.exp (-α1 * y1) * (1 - Real.exp (-(s * y1))) := by
    rw [show Real.exp (-α1 * y2) * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1))))
          = Real.exp (-α1 * y2) * Real.exp (α1 * d) * (1 - Real.exp (-(s * y1))) from by ring,
       ← Real.exp_add]
    congr 2
    simp [d]; ring
  rw [h_eq_combine] at h_step_e
  -- Expand exp(-α₁·y) - exp(-α₂·y) = exp(-α₁·y)·(1 - exp(-s·y)).
  have h_expand_y1 : Real.exp (-α1 * y1) - Real.exp (-α2 * y1) =
      Real.exp (-α1 * y1) * (1 - Real.exp (-(s * y1))) := by
    rw [show -α2 * y1 = -α1 * y1 + -(s * y1) from by simp [s]; ring]
    rw [Real.exp_add]; ring
  have h_expand_y2 : Real.exp (-α1 * y2) - Real.exp (-α2 * y2) =
      Real.exp (-α1 * y2) * (1 - Real.exp (-(s * y2))) := by
    rw [show -α2 * y2 = -α1 * y2 + -(s * y2) from by simp [s]; ring]
    rw [Real.exp_add]; ring
  linarith [h_step_e, h_expand_y1, h_expand_y2]

/-- **Auxiliary: strict monotonicity of `θ₄(iy)` for `y ≥ 1`.**
Alternating series: `θ₄(iy) − 1 = 2·∑_{n≥0} (−1)^(n+1) exp(−π(n+1)²y)`.
Pair consecutive terms (`n=2k`, `n=2k+1`) using `HasSum.even_add_odd`
to express `(θ₄(iy) − 1)/2 = ∑_{k≥0}[exp(−π(2k+2)²y) − exp(−π(2k+1)²y)]`,
equivalently `1 − θ₄(iy) = 2·∑_{k≥0} A_k(y)` where
`A_k(y) := exp(−π(2k+1)²y) − exp(−π(2k+2)²y) > 0`. For `y ≥ 1`,
`exp_neg_diff_strict_dec` applied with `α_1 := π(2k+1)² ≥ π > 1 = 1/y`
gives `A_k(y_1) > A_k(y_2)` for `1 ≤ y_1 < y_2`. Termwise strict
comparison via `Summable.tsum_lt_tsum` finishes. -/
theorem theta4_iy_strictMono_aux_large :
    StrictMonoOn (fun y : ℝ => (theta4 (Complex.I * (y : ℂ))).re) (Set.Ici 1) := by
  sorry

/-- **Modular transformation specialized to imaginary axis.**
For `y > 0`, `θ_4(iy)·√y = θ_2(i/y)` (both sides real). Specialization
of `theta4_S_smul` at `τ = i/y`, using `√(1/y) = 1/√y`. -/
theorem theta4_iy_mul_sqrt_eq_theta2 {y : ℝ} (hy : 0 < y) :
    (theta4 (Complex.I * (y : ℂ))).re * Real.sqrt y =
      (theta2 (Complex.I / (y : ℂ))).re := by
  have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
  -- The point i/y has positive imaginary part 1/y.
  have h_inv_eq : Complex.I / (y : ℂ) = ((1 / y : ℝ) : ℂ) * Complex.I := by
    rw [show (Complex.I / (y : ℂ)) = Complex.I * ((y : ℂ))⁻¹ from div_eq_mul_inv _ _]
    push_cast
    ring
  have h_inv_im : 0 < (Complex.I / (y : ℂ)).im := by
    rw [h_inv_eq]
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    exact hy
  -- Apply theta4_S_smul at τ = I/y.
  have h_S := theta4_S_smul h_inv_im
  -- Simplify -1 / (I/y) = I·y.
  have h_neg_inv : -1 / (Complex.I / (y : ℂ)) = Complex.I * (y : ℂ) := by
    rw [div_div_eq_mul_div, Complex.div_I]
    ring
  rw [h_neg_inv] at h_S
  -- Simplify -I·(I/y) = 1/y.
  have h_factor : (-Complex.I * (Complex.I / (y : ℂ))) = ((1 / y : ℝ) : ℂ) := by
    rw [show (-Complex.I * (Complex.I / (y : ℂ))) =
        (-(Complex.I * Complex.I)) / (y : ℂ) from by ring]
    rw [show Complex.I * Complex.I = -1 from by rw [← sq]; exact Complex.I_sq]
    push_cast
    ring
  rw [h_factor] at h_S
  -- Convert (1/y)^(1/2 : ℂ) to (Real.sqrt (1/y) : ℂ) = (1/√y : ℂ).
  have hy_inv_nn : (0 : ℝ) ≤ 1 / y := by positivity
  have h_cpow : (((1 / y : ℝ) : ℂ)) ^ (1/2 : ℂ) = (((1 / y : ℝ) ^ (1/2 : ℝ) : ℝ) : ℂ) := by
    rw [show (1/2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_cpow hy_inv_nn (1/2)).symm
  rw [h_cpow] at h_S
  -- Simplify (1/y)^(1/2) = 1/√y as real.
  have h_real_pow : ((1 / y : ℝ) ^ (1/2 : ℝ) : ℝ) = 1 / Real.sqrt y := by
    rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, one_div]
  rw [h_real_pow] at h_S
  -- Now: theta4 (I*y) = (1/√y : ℂ) · theta2 (I/y).
  -- Multiply both sides by (√y : ℂ).
  have hy_sqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hy_sqrt_ne : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy_sqrt_pos)
  have h_eq : theta4 (Complex.I * (y : ℂ)) * ((Real.sqrt y : ℝ) : ℂ) =
      theta2 (Complex.I / (y : ℂ)) := by
    rw [h_S]
    have : (((1 / Real.sqrt y : ℝ)) : ℂ) = ((Real.sqrt y : ℝ) : ℂ)⁻¹ := by
      push_cast
      rw [one_div]
    rw [this]
    field_simp
  -- Take real parts.
  have h_re : (theta4 (Complex.I * (y : ℂ)) * ((Real.sqrt y : ℝ) : ℂ)).re =
      (theta2 (Complex.I / (y : ℂ))).re := by
    rw [h_eq]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h_re
  exact h_re

/-- **Auxiliary: strict monotonicity of `θ₄(iy)` for `0 < y ≤ 1`.**
Modular transformation `θ_4(iy) = θ_2(i/y)/√y` reduces to: for
`u = 1/y ≥ 1`, the function `u ↦ √u · θ_2(iu).re` is strictly antitone.
Termwise: `√u · exp(−π (n+1/2)² u)` has derivative
`exp(−α u)·(1 − 2 α u)/(2√u) < 0` for `u ≥ 1` since
`2 α u = 2 π (n+1/2)² · u ≥ π/2 · 1 > 1`. -/
theorem theta4_iy_strictMono_aux_small :
    StrictMonoOn (fun y : ℝ => (theta4 (Complex.I * (y : ℂ))).re) (Set.Ioc 0 1) := by
  sorry

/-- **Strict monotonicity of `θ₄(iy)`.** The function `y ↦ θ₄(iy).re`
is strictly monotone increasing on `(0, ∞)`. Combine the alternating-
series argument (`theta4_iy_strictMono_aux_large`, valid for `y ≥ 1`)
with the modular-transformation argument
(`theta4_iy_strictMono_aux_small`, valid for `0 < y ≤ 1`) via a case
split at the threshold `y = 1`. -/
theorem theta4_iy_strictMono :
    StrictMonoOn (fun y : ℝ => (theta4 (Complex.I * (y : ℂ))).re) (Set.Ioi 0) := by
  intro y1 hy1 y2 hy2 h12
  have hy1' : (0:ℝ) < y1 := hy1
  have hy2' : (0:ℝ) < y2 := hy2
  by_cases hy2_le : y2 ≤ 1
  · -- Both in (0, 1].
    have hy1_le : y1 ≤ 1 := le_of_lt (lt_of_lt_of_le h12 hy2_le)
    exact theta4_iy_strictMono_aux_small ⟨hy1', hy1_le⟩ ⟨hy2', hy2_le⟩ h12
  · have hy2_gt : 1 < y2 := lt_of_not_ge hy2_le
    by_cases hy1_ge : 1 ≤ y1
    · -- Both in [1, ∞).
      exact theta4_iy_strictMono_aux_large hy1_ge (le_of_lt (lt_of_le_of_lt hy1_ge h12)) h12
    · -- y1 < 1 < y2: chain through y = 1.
      have hy1_lt : y1 < 1 := lt_of_not_ge hy1_ge
      have h_one_mem_small : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_refl _⟩
      have h_one_mem_large : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.self_mem_Ici
      have h_y1_one : (theta4 (Complex.I * (y1 : ℂ))).re <
          (theta4 (Complex.I * ((1 : ℝ) : ℂ))).re :=
        theta4_iy_strictMono_aux_small ⟨hy1', le_of_lt hy1_lt⟩ h_one_mem_small hy1_lt
      have h_one_y2 : (theta4 (Complex.I * ((1 : ℝ) : ℂ))).re <
          (theta4 (Complex.I * (y2 : ℂ))).re :=
        theta4_iy_strictMono_aux_large h_one_mem_large (le_of_lt hy2_gt) hy2_gt
      exact lt_trans h_y1_one h_one_y2

/-- **Strict monotonicity of `λ(iy)`.** The function `y ↦ λ(iy).re`
is strictly antitone on `(0, ∞)`. Follows from
`theta3_iy_strictAntitone` (denominator decreasing) and
`theta4_iy_strictMono` (numerator increasing) via the Jacobi
identity `θ₂⁴ + θ₄⁴ = θ₃⁴`, equivalently
`1 − λ(iy) = (θ₄(iy)/θ₃(iy))⁴`: the ratio `θ₄/θ₃` is strictly
increasing (positive numerator increases, positive denominator
decreases), so `(θ₄/θ₃)⁴` is strictly increasing, hence
`λ(iy) = 1 − (θ₄/θ₃)⁴` is strictly decreasing. -/
theorem modularLambdaH_iy_strictAntitone :
    StrictAntiOn (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re) (Set.Ioi 0) := by
  sorry

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

/-- **Schwarz reflection identity for `λ` through the line `Re τ = 1`.**
For `τ ∈ ℍ`, `λ(2 − conj τ) = conj(λ τ)`. Composition of
`modularLambdaH_conj_symmetry` (reflection through `Re τ = 0`) and
`modularLambdaH_sub_two` (T²-invariance). -/
theorem modularLambdaH_schwarz_reflect_re_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (2 - starRingEnd ℂ τ) = starRingEnd ℂ (modularLambdaH τ) := by
  have h_eq : (2 - starRingEnd ℂ τ : ℂ) = -(starRingEnd ℂ (τ - 2)) := by
    rw [map_sub, map_ofNat]; ring
  rw [h_eq]
  have hτ_sub_2_im : 0 < (τ - 2).im := by
    rw [Complex.sub_im]; simpa using hτ
  rw [modularLambdaH_conj_symmetry hτ_sub_2_im]
  rw [modularLambdaH_sub_two]

/-- **Schwarz reflection identity for `λ` through the F^o boundary
semicircle `|τ − 1/2| = 1/2`.** For `τ ∈ ℍ`,
`λ(conj τ / (2·conj τ − 1)) = conj(λ τ)`. The Möbius `w ↦ w/(2w−1)`
fixes the semicircle pointwise; composed with conjugation it gives
the antiholomorphic inversion across the semicircle. The proof uses
`modularLambdaH_div_two_tau_add_one` (inverted to get
`λ(−τ/(2τ−1)) = λ(τ)`) and `modularLambdaH_conj_symmetry`. -/
theorem modularLambdaH_schwarz_reflect_semicircle {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (starRingEnd ℂ τ / (2 * starRingEnd ℂ τ - 1)) =
      starRingEnd ℂ (modularLambdaH τ) := by
  -- 2τ - 1 ≠ 0 since τ.im > 0 forces (2τ - 1).im > 0.
  have h_2τ_m_1_ne : (2 * τ - 1 : ℂ) ≠ 0 := by
    intro h
    have h_im : (2 * τ - 1 : ℂ).im = 0 := by rw [h]; rfl
    simp [Complex.sub_im, Complex.mul_im, Complex.one_im] at h_im
    linarith
  -- σ' := -τ/(2τ - 1). σ'.im > 0.
  set σ' : ℂ := -τ / (2 * τ - 1) with hσ'_def
  have h_denom_normSq_pos : 0 < Complex.normSq (2 * τ - 1) :=
    Complex.normSq_pos.mpr h_2τ_m_1_ne
  have hσ'_im_pos : 0 < σ'.im := by
    have h_im_eq : σ'.im = τ.im / Complex.normSq (2 * τ - 1) := by
      rw [hσ'_def]
      rw [show (-τ / (2 * τ - 1) : ℂ) = -(τ / (2 * τ - 1)) from neg_div _ _]
      rw [Complex.neg_im, Complex.div_im]
      have h_2τ_re : (2 * τ - 1 : ℂ).re = 2 * τ.re - 1 := by
        simp [Complex.sub_re, Complex.mul_re, Complex.one_re]
      have h_2τ_im : (2 * τ - 1 : ℂ).im = 2 * τ.im := by
        simp [Complex.sub_im, Complex.mul_im, Complex.one_im]
      rw [h_2τ_re, h_2τ_im]
      field_simp
      ring
    rw [h_im_eq]
    exact div_pos hτ h_denom_normSq_pos
  -- 2σ' + 1 = -1/(2τ - 1) ≠ 0.
  have h_2σ'_p_1_ne : (2 * σ' + 1 : ℂ) ≠ 0 := by
    intro h
    have h_im : (2 * σ' + 1 : ℂ).im = 0 := by rw [h]; rfl
    simp [Complex.add_im, Complex.mul_im, Complex.one_im] at h_im
    linarith
  -- σ'·(2τ - 1) = -τ (from definition of σ').
  have h_step : σ' * (2 * τ - 1) = -τ := by
    rw [hσ'_def]
    exact div_mul_cancel₀ _ h_2τ_m_1_ne
  -- σ'/(2σ' + 1) = τ.
  have h_φ_σ' : σ' / (2 * σ' + 1) = τ := by
    rw [div_eq_iff h_2σ'_p_1_ne]
    linear_combination -h_step
  -- λ(σ') = λ(τ) by Γ(2)-invariance applied to σ'.
  have h_σ'_lambda : modularLambdaH σ' = modularLambdaH τ := by
    have h := modularLambdaH_div_two_tau_add_one hσ'_im_pos
    rw [h_φ_σ'] at h
    exact h.symm
  -- conj(τ)/(2 conj(τ) - 1) = -conj(σ').
  have h_eq : (starRingEnd ℂ τ / (2 * starRingEnd ℂ τ - 1) : ℂ) =
      -(starRingEnd ℂ σ') := by
    rw [hσ'_def]
    rw [map_div₀, map_neg, map_sub, map_mul, map_ofNat, map_one]
    field_simp
  rw [h_eq, modularLambdaH_conj_symmetry hσ'_im_pos, h_σ'_lambda]

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

/-! ## Cusp asymptotics for `λ` inside `F^o`

Two cusp asymptotics needed for the Phragmén–Lindelöf-style closure of
Step A. These are stronger than the existing left-edge-only limits
(`modularLambdaH_iy_tendsto_*`) because the `F^o` constraint
`‖2τ − 1‖ > 1` forces every approach to `0` (resp. `1`) inside `F^o`
to satisfy `Im(−1/(τ − 1)) → ∞` (resp. the q'-expansion gives
`Im λ > 0` for `τ` near `1`). -/

/-- **Cusp 0 limit inside `F^o`.** As `τ → 0` along any path in `F^o`,
`λ(τ) → 1`. This is stronger than `modularLambdaH_iy_tendsto_one_atZeroPos`
(which gives the limit only along the imaginary axis): in `F^o`, the
constraint `‖2τ − 1‖ > 1` (equivalently `(Re τ)² + (Im τ)² > Re τ`)
forces `Re τ < (Im τ)²` near `0`, so `Im(−1/τ) = Im τ / |τ|² → ∞` as
`τ → 0` in `F^o`, and the S-shift identity
`λ(τ) = 1 − λ(−1/τ)` combined with the cusp `i∞` uniform bound
`modularLambdaH_norm_le_exp_of_im_ge_one` gives `λ(τ) → 1`. -/
theorem modularLambdaH_cusp_zero_tendsto_one_in_F :
    Filter.Tendsto modularLambdaH
      (nhdsWithin (0 : ℂ) Gamma2FundamentalDomainInterior) (𝓝 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε_pos
  have hπ_pos := Real.pi_pos
  -- Set K := max 1 (log(160000/ε)/π + 1), δ := 1/(3·K).
  set K : ℝ := max 1 (Real.log (160000 / ε) / Real.pi + 1) with hK_def
  have hK_ge_one : 1 ≤ K := le_max_left _ _
  have hK_pos : 0 < K := by linarith
  have hK_ge_log : Real.log (160000 / ε) / Real.pi + 1 ≤ K := le_max_right _ _
  set δ : ℝ := 1 / (3 * K) with hδ_def
  have h_3K_pos : 0 < 3 * K := by linarith
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro τ hτ_F hτ_dist
  rw [dist_zero_right] at hτ_dist
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  -- Standard bounds.
  have hτ_im_le_norm : τ.im ≤ ‖τ‖ := by
    have h_sq : τ.im ^ 2 ≤ ‖τ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg τ.re]
    have h_norm_nn : 0 ≤ ‖τ‖ := norm_nonneg _
    nlinarith [hτ_im_pos.le, sq_nonneg (τ.im - ‖τ‖)]
  have hτ_re_le_norm : τ.re ≤ ‖τ‖ := by
    have h_sq : τ.re ^ 2 ≤ ‖τ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg τ.im]
    have h_norm_nn : 0 ≤ ‖τ‖ := norm_nonneg _
    nlinarith [hτ_re_pos.le, sq_nonneg (τ.re - ‖τ‖)]
  have hτ_im_lt_δ : τ.im < δ := lt_of_le_of_lt hτ_im_le_norm hτ_dist
  have hτ_re_lt_δ : τ.re < δ := lt_of_le_of_lt hτ_re_le_norm hτ_dist
  -- δ ≤ 1/3 since K ≥ 1.
  have hδ_le_third : δ ≤ 1/3 := by
    rw [hδ_def]
    rw [div_le_div_iff₀ h_3K_pos (by norm_num : (0:ℝ) < 3)]
    linarith
  have hτ_im_lt_third : τ.im < 1/3 := lt_of_lt_of_le hτ_im_lt_δ hδ_le_third
  have hτ_re_lt_third : τ.re < 1/3 := lt_of_lt_of_le hτ_re_lt_δ hδ_le_third
  -- |τ|² > Re τ (from F^o constraint ‖2τ-1‖ > 1).
  have hτ_normSq_gt_re : τ.re ^ 2 + τ.im ^ 2 > τ.re := by
    have h_sq_lt : 1 < ‖2 * τ - 1‖ ^ 2 := by
      have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
      nlinarith
    have h_norm_sq_eq : ‖2 * τ - 1‖ ^ 2 = (2 * τ.re - 1) ^ 2 + (2 * τ.im) ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im]
      ring
    rw [h_norm_sq_eq] at h_sq_lt
    nlinarith
  -- Hence Im²τ > Re·(1-Re) ≥ Re·(2/3) for Re < 1/3.
  have h_im_sq_gt : τ.im ^ 2 > τ.re * (2/3) := by
    have h_one_sub : 2/3 < 1 - τ.re := by linarith
    nlinarith [hτ_re_pos.le, hτ_normSq_gt_re]
  -- Hence Re < (3/2)·Im²τ.
  have h_re_lt_3_2_im : τ.re < (3/2) * τ.im ^ 2 := by linarith
  -- |τ|² = Re² + Im² ≤ Re·(1/3) + Im² (since Re < 1/3, Re² ≤ Re·(1/3)).
  -- Re² ≤ Re · Re ≤ Re · (1/3).
  have h_re_sq_le : τ.re ^ 2 ≤ τ.re * (1/3) := by
    have := mul_le_mul_of_nonneg_left hτ_re_lt_third.le hτ_re_pos.le
    nlinarith [sq_nonneg τ.re]
  -- |τ|² ≤ Re·(1/3) + Im²τ ≤ (3/2·Im²τ)·(1/3) + Im²τ = (1/2)·Im²τ + Im²τ = (3/2)·Im²τ.
  -- So |τ|² ≤ (3/2)·Im²τ, hence 1/|τ|² ≥ 2/(3·Im²τ).
  -- Wait actually we want a stronger ratio. Let me redo.
  -- |τ|² = Re² + Im² ≤ (Re·1/3) + Im² ≤ ((3/2·Im²)·1/3) + Im² = (1/2)·Im² + Im² = (3/2)·Im².
  have h_normSq_le : τ.re ^ 2 + τ.im ^ 2 ≤ (3/2) * τ.im ^ 2 := by
    have h_re_sq_bound : τ.re ^ 2 ≤ (1/2) * τ.im ^ 2 := by
      calc τ.re ^ 2 ≤ τ.re * (1/3) := h_re_sq_le
        _ ≤ ((3/2) * τ.im ^ 2) * (1/3) :=
            mul_le_mul_of_nonneg_right h_re_lt_3_2_im.le (by norm_num)
        _ = (1/2) * τ.im ^ 2 := by ring
    linarith
  -- |τ|² ≤ (3/2)·Im²τ. So Im(-1/τ) = Im τ / |τ|² ≥ Im τ / ((3/2)·Im²τ) = 2/(3·Im τ).
  -- For Im τ < 1/3: 2/(3·Im τ) > 2 > 1.
  have hτ_normSq_pos : 0 < τ.re ^ 2 + τ.im ^ 2 := by positivity
  have hτ_normSq_eq : Complex.normSq τ = τ.re ^ 2 + τ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h_inv_im : (-1 / τ).im = τ.im / Complex.normSq τ := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by ring]
    rw [Complex.neg_im, Complex.inv_im]
    ring
  have h_inv_im_lower : 2 / (3 * τ.im) ≤ (-1 / τ).im := by
    rw [h_inv_im, hτ_normSq_eq]
    have h_3im_pos : 0 < 3 * τ.im := by linarith
    rw [div_le_div_iff₀ h_3im_pos hτ_normSq_pos]
    have : 2 * (τ.re ^ 2 + τ.im ^ 2) ≤ 2 * ((3/2) * τ.im ^ 2) :=
      mul_le_mul_of_nonneg_left h_normSq_le (by norm_num)
    have h_simp : 2 * ((3/2) * τ.im ^ 2) = τ.im * (3 * τ.im) := by ring
    linarith
  -- 2/(3·Im τ) ≥ 2·K when Im τ ≤ 1/(3·K).
  have h_inv_im_ge_2K : 2 * K ≤ (-1 / τ).im := by
    have h_2_K : 2 / (3 * τ.im) ≥ 2 * K := by
      rw [ge_iff_le]
      have h_3im_pos : 0 < 3 * τ.im := by linarith
      rw [le_div_iff₀ h_3im_pos]
      have h_imK : τ.im < 1 / (3 * K) := hτ_im_lt_δ
      have h_mul_lt : 2 * K * (3 * τ.im) < 2 * K * (1 / (3 * K) * 3) := by
        have : 2 * K * (3 * τ.im) < 2 * K * (3 * (1/(3*K))) := by
          have h_im_lt : 3 * τ.im < 3 * (1/(3*K)) :=
            mul_lt_mul_of_pos_left h_imK (by norm_num)
          exact mul_lt_mul_of_pos_left h_im_lt (by linarith : (0:ℝ) < 2 * K)
        linarith
      have h_simp : 2 * K * (1 / (3 * K) * 3) = 2 := by
        field_simp
      linarith
    linarith
  -- Apply cusp ∞ bound at -1/τ.
  have h_inv_im_ge_one : 1 ≤ (-1 / τ).im := le_trans (by linarith) h_inv_im_ge_2K
  have h_lam_bound : ‖modularLambdaH (-1 / τ)‖ ≤
      160000 * Real.exp (-Real.pi * (-1 / τ).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_ge_one
  -- S-shift.
  have h_S := modularLambdaH_add_S_smul_eq_one hτ_im_pos
  have h_lam_sub : modularLambdaH τ - 1 = -(modularLambdaH (-1 / τ)) := by
    linear_combination h_S
  rw [dist_eq_norm, h_lam_sub, norm_neg]
  -- We have ‖λ(-1/τ)‖ ≤ 160000·exp(-π·Im(-1/τ)) ≤ 160000·exp(-π·2K) ≤ 160000·exp(-2π·K).
  have h_exp_le : Real.exp (-Real.pi * (-1 / τ).im) ≤ Real.exp (-Real.pi * (2 * K)) := by
    apply Real.exp_le_exp.mpr
    have : -Real.pi * (-1 / τ).im ≤ -Real.pi * (2 * K) := by
      have h := h_inv_im_ge_2K
      nlinarith [Real.pi_pos]
    exact this
  -- 160000·exp(-π·2K) ≤ 160000·exp(-π·(log(160000/ε)/π + 1)·1)
  --                 ≤ 160000·exp(-(log(160000/ε) + π))
  --                 = 160000·(ε/160000)·exp(-π)
  --                 = ε·exp(-π) < ε.
  have h_K_ge : 2 * K ≥ Real.log (160000 / ε) / Real.pi + 1 := by
    have h1 : K ≥ Real.log (160000 / ε) / Real.pi + 1 := hK_ge_log
    linarith
  have h_pi_2K : -Real.pi * (2 * K) ≤ -(Real.log (160000 / ε) + Real.pi) := by
    have h_lhs_eq : -Real.pi * (2 * K) = -(Real.pi * (2 * K)) := by ring
    have h_rhs : Real.pi * (Real.log (160000 / ε) / Real.pi + 1) =
        Real.log (160000 / ε) + Real.pi := by
      field_simp
    have h_step : Real.pi * (Real.log (160000 / ε) / Real.pi + 1) ≤ Real.pi * (2 * K) :=
      mul_le_mul_of_nonneg_left h_K_ge hπ_pos.le
    rw [h_rhs] at h_step
    linarith
  have h_exp_neg_le : Real.exp (-Real.pi * (2 * K)) ≤
      ε / 160000 * Real.exp (-Real.pi) := by
    have h_exp_le' : Real.exp (-Real.pi * (2 * K)) ≤
        Real.exp (-(Real.log (160000 / ε) + Real.pi)) :=
      Real.exp_le_exp.mpr h_pi_2K
    have h_eq : Real.exp (-(Real.log (160000 / ε) + Real.pi)) =
        ε / 160000 * Real.exp (-Real.pi) := by
      rw [show (-(Real.log (160000 / ε) + Real.pi) : ℝ) =
          -Real.log (160000 / ε) + -Real.pi from by ring]
      rw [Real.exp_add]
      have h_160_div_pos : 0 < 160000 / ε := by positivity
      rw [show -Real.log (160000 / ε) = Real.log (160000 / ε)⁻¹ from
          (Real.log_inv _).symm]
      rw [Real.exp_log (by positivity : (0:ℝ) < (160000/ε)⁻¹)]
      rw [show ((160000 / ε)⁻¹ : ℝ) = ε / 160000 from by
        rw [inv_div]]
    linarith [h_exp_le', h_eq.le]
  -- exp(-π) < 1.
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1 := by
    rw [show (-Real.pi : ℝ) = -(Real.pi) from rfl]
    rw [Real.exp_neg]
    have h_exp_pi_gt : 1 < Real.exp Real.pi := by
      have h1 : (0:ℝ) < Real.pi := hπ_pos
      have h := Real.add_one_le_exp Real.pi
      linarith
    have h_inv_lt : (Real.exp Real.pi)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right; exact h_exp_pi_gt
    exact h_inv_lt
  calc ‖modularLambdaH (-1 / τ)‖
      ≤ 160000 * Real.exp (-Real.pi * (-1 / τ).im) := h_lam_bound
    _ ≤ 160000 * Real.exp (-Real.pi * (2 * K)) :=
        mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
    _ ≤ 160000 * (ε / 160000 * Real.exp (-Real.pi)) :=
        mul_le_mul_of_nonneg_left h_exp_neg_le (by norm_num)
    _ = ε * Real.exp (-Real.pi) := by field_simp
    _ < ε * 1 := mul_lt_mul_of_pos_left h_exp_neg_pi_lt hε_pos
    _ = ε := by ring

/-- **Cusp 1 asymptotic in `F^o` (the deep step).** There is a
neighbourhood of `1` in which every point of `F^o` has `Im λ ≥ 0`.

The proof uses the T-shift identity
`λ(τ) = λ(τ − 1)/(λ(τ − 1) − 1)`, the cusp-0 limit `λ(τ−1) → 1` for
`τ − 1` approaching `0` from the `F^o`-shifted region (i.e., from the
upper-left quadrant minus the reflected semicircle), and the
q'-expansion `δ := λ(τ−1) − 1 = −λ(−1/(τ−1)) ≈ −16 q'` where
`q' := exp(πi · (−1/(τ−1)))`. The `F^o`-shifted constraint
`‖2(τ−1) + 1‖ > 1` forces `arg(q') ∈ (0, π)` (equivalently,
`Re(−1/(τ−1)) ∈ (0, 1)`), so `Im(q') > 0` in the leading order.

**Available infrastructure.** Two Schwarz reflection identities for
`λ` are now closed axiom-clean:

* `modularLambdaH_schwarz_reflect_re_one`: `λ(2 − conj τ) = conj(λ τ)`,
  Schwarz reflection through the line `Re τ = 1` (composition of
  `modularLambdaH_conj_symmetry` and `modularLambdaH_sub_two`).
* `modularLambdaH_schwarz_reflect_semicircle`:
  `λ(conj τ/(2·conj τ − 1)) = conj(λ τ)`, Schwarz reflection through
  the F^o boundary semicircle `|τ − 1/2| = 1/2` (composition of
  `modularLambdaH_div_two_tau_add_one` inverted and
  `modularLambdaH_conj_symmetry`).

**Remaining work for closure.** With both Schwarz reflections in
place, the local orientation argument at each boundary point
determines the sign of `Im λ` on the F^o side via the inverse function
theorem. For `τ₀ = 1 + iy₀ ∈ Re τ = 1`: `λ` real, `λ'(τ₀) ≠ 0`, so
`λ` is locally conformal at `τ₀`, mapping the F^o side `Re < 1` to
one half-plane (the half-plane is determined by the
`modularLambdaH_im_pos_at_witness`). For `τ₀ ∈ F^o` boundary
semicircle: analogous orientation argument via the semicircle
reflection. Combined with preconnectedness of F^o near 1, this gives
`Im λ ≥ 0` on F^o ∩ B(1, δ). -/
theorem modularLambdaH_cusp_one_im_nonneg_nbhd_in_F :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Gamma2FundamentalDomainInterior,
      ‖τ - 1‖ ≤ δ → 0 ≤ (modularLambdaH τ).im := by
  sorry

/-- **Sub-lemma for Step A (Phragmén–Lindelöf statement): `Im(λ) ≥ 0`
on `F^o`.**

`Im λ` is harmonic on `F^o`, vanishes on the three boundary arcs
(`modularLambdaH_pure_imag_real`, `modularLambdaH_one_add_imag_real`,
`modularLambdaH_semicircle_real`), and tends to `0` at the cusps
`i∞` and `0` (via `modularLambdaH_iy_tendsto_zero_atTop` and
`modularLambdaH_iy_tendsto_one_atZeroPos`).

**Cusp-1 asymptotic (the deep step).** At cusp `1`, the modular
identity `λ(τ) = λ(τ−1)/(λ(τ)−1)` together with the cusp-`0`
limit `λ(τ−1) → 1` gives `|λ(τ)| → ∞`. The sign of `Im λ(τ)` as
`τ → 1` in `F^o` is determined by the q'-expansion at cusp 0:
writing `δ := λ(τ−1) − 1 = −λ(−1/(τ−1))` and `q' = exp(πi·(−1/(τ−1)))`,
one has `δ ≈ −16 q'`, so `Im λ(τ) = Im[1/δ + 1] = −Im(δ)/|δ|²`. For
`τ−1 = re^{iθ}` with `θ ∈ (π/2, π)` and `r > |cos θ|` (the
F^o constraint near cusp 1), one verifies `arg(q') ∈ (0, π)`, hence
`Im(q') > 0`, so `Im(δ) < 0` and `Im λ(τ) > 0`. Quantitatively,
`Im λ(τ) ∼ sin(arg q')/(16|q'|) → +∞` as `r → 0`.

**Phragmén–Lindelöf assembly.** With `Im λ → +∞` at cusp 1 and
`Im λ → 0` at the other cusps and on the boundary arcs, the minimum
principle for the harmonic function `Im λ` on the simply-connected
`F^o` (via the bounded function `h(τ) := exp(−i·λ(τ))` whose norm
`‖h(τ)‖ = exp(Im λ(τ))` is bounded below by `1` on all four boundary
contributions) gives `Im λ ≥ 0` throughout.

Mathlib's `PhragmenLindelof.vertical_strip` does not apply directly:
`λ` has dense singularities on `ℝ` from the `Γ(2)` action, so it
cannot be extended via Schwarz reflection to the strip
`{0 < Re < 1}` in the form PL requires. The proof must instead
proceed by truncation of `F^o` away from the cusps, max-modulus on
the bounded truncation, and a limit argument as the truncation
exhausts `F^o`. -/
theorem modularLambdaH_im_nonneg_on_F :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, 0 ≤ (modularLambdaH τ).im := by
  sorry

/-- **Sub-lemma for Step A: `Im(λ) ≠ 0` on `F^o`.** The modular
function `λ` takes no real values on the open fundamental domain.
Derived from `modularLambdaH_im_nonneg_on_F` (`Im λ ≥ 0`) together
with the open-mapping theorem: if `λ(τ_*)` were real for some
`τ_* ∈ F^o`, then `λ(F^o)` is open and `λ(τ_*) ∈ λ(F^o)` would
admit a small ball, so some interior point `τ'` would have
`Im(λ(τ')) < 0`, contradicting `Im λ ≥ 0`. -/
theorem modularLambdaH_im_ne_zero_on_F :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, (modularLambdaH τ).im ≠ 0 := by
  intro τstar hτstar h_im_zero
  -- Setup ℍ.
  set ℍ : Set ℂ := { τ : ℂ | 0 < τ.im }
  have hℍ_open : IsOpen ℍ := isOpen_lt continuous_const Complex.continuous_im
  -- λ is analytic on ℍ.
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
  -- λ is non-constant on ℍ (cusp limits give two different values).
  have h_lam_not_const : ¬ (∃ w, ∀ z ∈ ℍ, modularLambdaH z = w) := by
    rintro ⟨w, hconst⟩
    have h_mul_in : ∀ y : ℝ, 0 < y → (Complex.I * (y : ℂ)) ∈ ℍ := by
      intro y hy_pos
      change 0 < (Complex.I * (y : ℂ)).im
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
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
    have h_eq : (0 : ℂ) = 1 := hw_zero.symm.trans hw_one
    exact one_ne_zero h_eq.symm
  -- Open mapping on F^o: λ(F^o) is open.
  rcases h_lam_an.is_constant_or_isOpen hℍ_preconn with h_const | h_open
  · exact absurd h_const h_lam_not_const
  have hF_sub_ℍ : Gamma2FundamentalDomainInterior ⊆ ℍ :=
    Gamma2FundamentalDomainInterior_subset_upperHalf
  have hF_open : IsOpen Gamma2FundamentalDomainInterior :=
    Gamma2FundamentalDomainInterior_isOpen
  have h_image_open : IsOpen (modularLambdaH '' Gamma2FundamentalDomainInterior) :=
    h_open _ hF_sub_ℍ hF_open
  -- λ(τstar) ∈ image.
  have h_lam_in : modularLambdaH τstar ∈ modularLambdaH '' Gamma2FundamentalDomainInterior :=
    ⟨τstar, hτstar, rfl⟩
  -- Get a ball around λ(τstar) inside the image.
  rcases Metric.isOpen_iff.mp h_image_open _ h_lam_in with ⟨ε, hε_pos, hball⟩
  -- Choose w = λ(τstar) − i·ε/2.
  set w : ℂ := modularLambdaH τstar - Complex.I * ((ε / 2 : ℝ) : ℂ) with hw_def
  have h_eps_half_pos : (0 : ℝ) < ε / 2 := by linarith
  have hw_in_ball : w ∈ Metric.ball (modularLambdaH τstar) ε := by
    rw [Metric.mem_ball, dist_eq_norm, hw_def]
    have h_simplify :
        modularLambdaH τstar - Complex.I * ((ε / 2 : ℝ) : ℂ) - modularLambdaH τstar =
          -(Complex.I * ((ε / 2 : ℝ) : ℂ)) := by ring
    rw [h_simplify, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos h_eps_half_pos]
    linarith
  -- Get preimage τ' ∈ F^o.
  obtain ⟨τ', hτ'_F, hτ'_eq⟩ := hball hw_in_ball
  -- Compute Im(λ(τ')) = −ε/2 < 0.
  have h_im_τ' : (modularLambdaH τ').im = -(ε / 2) := by
    rw [hτ'_eq, hw_def]
    rw [Complex.sub_im, h_im_zero, zero_sub]
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- But Im(λ(τ')) ≥ 0 by modularLambdaH_im_nonneg_on_F. Contradiction.
  have h_nonneg' := modularLambdaH_im_nonneg_on_F τ' hτ'_F
  linarith

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

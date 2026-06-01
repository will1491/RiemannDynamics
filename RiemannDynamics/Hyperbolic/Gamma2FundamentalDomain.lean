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
# Fundamental domain of `Γ(2)` and surjectivity of `λ`

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
biholomorphism onto the open upper half of `ℂ ∖ {0, 1}`. The three
boundary arcs are real-valued under `λ` and parametrise the three
real-axis intervals `(0, 1)`, `(−∞, 0)`, `(1, +∞)`; the conjugation
identity `λ(−conj τ) = conj(λ τ)` plays the role of a Schwarz
reflection across the imaginary axis, covering the lower half of
`ℂ ∖ {0, 1}`.

The file develops the four-step program for `λ` on `F^o`:

* **Step A** — `modularLambdaH_F_im_pos`: `Im λ > 0` on `F^o`.
* **Step B** — `modularLambdaH_F_image_isOpen`: `λ(F^o)` is open in
  `ℂ` (open mapping theorem; `λ` is non-constant on `F^o`).
* **Step C** — `modularLambdaH_F_image_isClosed_in_upperHalf`:
  `λ(F^o)` is closed in the open upper half-plane (sequential
  compactness with cusp asymptotics ruling out limits at `{0, 1, ∞}`).
* **Step D** — `modularLambdaH_image_fundamentalDomainInterior`:
  `λ(F^o) = {Im w > 0}` (combining Steps A–C with connectedness of
  the upper half-plane).

The surjectivity `λ('') ℍ = ℂ ∖ {0, 1}` (`modularLambdaH_image`) and
its disk version (`modularLambda_image`) close the file: for `Im w < 0`
the conjugation symmetry transports a witness from `F^o`; for
`Im w ≥ 0` the same compactness extraction as Step C extends to the
real-axis target `w`, where the boundary-arc sub-cases of Step C
collapse into a single `τ* ∈ ℍ` branch since `λ(τ*) ∈ ℝ` is no
longer a contradiction.
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
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    exact hy1'
  have hτ2_im : 0 < (Complex.I * (y2 : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    exact hy2'
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
    simp only [Complex.reCLM_apply] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  have h_sum2_re : HasSum
      (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2))
      ((jacobiTheta (Complex.I * (y2 : ℂ)) - 1).re / 2) := by
    have h_map := h_sum2'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply] at h_map
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
  change (theta3 (Complex.I * (y2 : ℂ))).re < (theta3 (Complex.I * (y1 : ℂ))).re
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
  intro y1 hy1 y2 hy2 h_y12
  have hy1' : (1:ℝ) ≤ y1 := hy1
  have hy2' : (1:ℝ) ≤ y2 := hy2
  have hy1_pos : (0:ℝ) < y1 := lt_of_lt_of_le zero_lt_one hy1'
  have hy2_pos : (0:ℝ) < y2 := lt_of_lt_of_le zero_lt_one hy2'
  change (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re
  -- Translate to jacobiTheta at τ = I·y + 1.
  have hτ1_im : 0 < (Complex.I * (y1 : ℂ) + 1).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, add_zero]
    exact hy1_pos
  have hτ2_im : 0 < (Complex.I * (y2 : ℂ) + 1).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, add_zero]
    exact hy2_pos
  -- Each complex term equals `(-1)^(n+1) · exp(-π(n+1)²y)` (real).
  have h_term : ∀ y : ℝ, ∀ n : ℕ,
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
        (Complex.I * (y : ℂ) + 1)) =
        (((-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ) := by
    intro y n
    have h_split : (Real.pi : ℂ) * Complex.I * ((↑n : ℂ) + 1) ^ 2 *
        (Complex.I * (y : ℂ) + 1) =
        ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ) +
        ((↑n : ℂ) + 1) ^ 2 * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_split, Complex.exp_add]
    rw [show ((↑n : ℂ) + 1) ^ 2 = (((n + 1)^2 : ℕ) : ℂ) from by push_cast; ring]
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    rw [← Complex.ofReal_exp]
    have h_parity : ((-1 : ℂ))^((n+1)^2) = (((-1 : ℝ)^(n+1) : ℝ) : ℂ) := by
      rcases Nat.even_or_odd (n+1) with hn | hn
      · have h2 : Even ((n+1)^2) := by
          obtain ⟨k, hk⟩ := hn
          refine ⟨k * (k + k), ?_⟩
          have heq : (n + 1)^2 = (k + k)^2 := by rw [hk]
          rw [heq]; ring
        rw [Even.neg_one_pow h2, Even.neg_one_pow hn]
        simp
      · have h2 : Odd ((n+1)^2) := by
          have hsq : (n+1)^2 = (n+1) * (n+1) := sq (n+1)
          rw [hsq]
          exact hn.mul hn
        rw [Odd.neg_one_pow h2, Odd.neg_one_pow hn]
        simp
    rw [h_parity]
    push_cast
    ring
  -- Apply HasSum.
  have h_sum1 := hasSum_nat_jacobiTheta hτ1_im
  have h_sum2 := hasSum_nat_jacobiTheta hτ2_im
  have h_sum1' : HasSum
      (fun n : ℕ => (((-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1) / 2) := by
    convert h_sum1 using 1
    funext n
    exact (h_term y1 n).symm
  have h_sum2' : HasSum
      (fun n : ℕ => (((-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1) / 2) := by
    convert h_sum2 using 1
    funext n
    exact (h_term y2 n).symm
  -- Map to real HasSum.
  have h_sum1_re : HasSum
      (fun n : ℕ => (-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1))
      ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    have h_map := h_sum1'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  have h_sum2_re : HasSum
      (fun n : ℕ => (-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2))
      ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    have h_map := h_sum2'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  -- Define f y n := (-1)^(n+1) · exp(-π·(n+1)²·y).
  set f : ℝ → ℕ → ℝ := fun y n => (-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y)
    with f_def
  -- Pair sum: f y (2k) + f y (2k+1) = -A_k(y).
  have h_pair_eq : ∀ y : ℝ, ∀ k : ℕ,
      f y (2*k) + f y (2*k+1) =
        -(Real.exp (-Real.pi * ((2*k:ℝ)+1)^2 * y) -
          Real.exp (-Real.pi * ((2*k:ℝ)+2)^2 * y)) := by
    intro y k
    simp only [f_def]
    have h_2k_plus_1_odd : Odd (2*k+1) := ⟨k, rfl⟩
    have h_2k_plus_2_even : Even (2*k+2) := ⟨k+1, by ring⟩
    have h_eq1 : ((-1 : ℝ))^(2*k+1) = -1 := h_2k_plus_1_odd.neg_one_pow
    have h_eq2 : ((-1 : ℝ))^(2*k+1+1) = 1 := h_2k_plus_2_even.neg_one_pow
    rw [h_eq1, h_eq2]
    push_cast
    ring_nf
  -- Get summability of subseries.
  have h_sum_even1 : Summable (fun k => f y1 (2*k)) :=
    h_sum1_re.summable.comp_injective (fun _ _ hab => by omega)
  have h_sum_odd1 : Summable (fun k => f y1 (2*k+1)) :=
    h_sum1_re.summable.comp_injective (fun _ _ hab => by omega)
  have h_sum_even2 : Summable (fun k => f y2 (2*k)) :=
    h_sum2_re.summable.comp_injective (fun _ _ hab => by omega)
  have h_sum_odd2 : Summable (fun k => f y2 (2*k+1)) :=
    h_sum2_re.summable.comp_injective (fun _ _ hab => by omega)
  -- Combine subseries: by HasSum.even_add_odd, even + odd = full.
  have h_even_odd1 :
      HasSum (f y1)
        (∑' k, f y1 (2*k) + ∑' k, f y1 (2*k+1)) :=
    HasSum.even_add_odd h_sum_even1.hasSum h_sum_odd1.hasSum
  have h_even_odd2 :
      HasSum (f y2)
        (∑' k, f y2 (2*k) + ∑' k, f y2 (2*k+1)) :=
    HasSum.even_add_odd h_sum_even2.hasSum h_sum_odd2.hasSum
  have h_unique1 : ∑' k, f y1 (2*k) + ∑' k, f y1 (2*k+1) =
      (jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2 :=
    h_even_odd1.unique h_sum1_re
  have h_unique2 : ∑' k, f y2 (2*k) + ∑' k, f y2 (2*k+1) =
      (jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2 :=
    h_even_odd2.unique h_sum2_re
  -- HasSum of pair sums = full sum.
  have h_pair_sum1 :
      HasSum (fun k => f y1 (2*k) + f y1 (2*k+1))
        ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    have h := h_sum_even1.hasSum.add h_sum_odd1.hasSum
    rwa [h_unique1] at h
  have h_pair_sum2 :
      HasSum (fun k => f y2 (2*k) + f y2 (2*k+1))
        ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    have h := h_sum_even2.hasSum.add h_sum_odd2.hasSum
    rwa [h_unique2] at h
  -- Rewrite as -A_k(y).
  set A : ℝ → ℕ → ℝ := fun y k =>
    Real.exp (-Real.pi * ((2*k:ℝ)+1)^2 * y) - Real.exp (-Real.pi * ((2*k:ℝ)+2)^2 * y)
    with A_def
  have h_neg_A1 : HasSum (fun k => -A y1 k)
      ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    convert h_pair_sum1 using 1
    funext k
    rw [A_def, h_pair_eq y1 k]
  have h_neg_A2 : HasSum (fun k => -A y2 k)
      ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    convert h_pair_sum2 using 1
    funext k
    rw [A_def, h_pair_eq y2 k]
  -- HasSum of A_k(y) = - ((θ₄(iy) - 1).re / 2).
  have h_A1 : HasSum (A y1) (-(jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    have h := h_neg_A1.neg
    simp only [neg_neg] at h
    convert h using 1
    ring
  have h_A2 : HasSum (A y2) (-(jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    have h := h_neg_A2.neg
    simp only [neg_neg] at h
    convert h using 1
    ring
  -- Strict comparison of A's: A_k(y2) < A_k(y1).
  have h_A_lt : ∀ k : ℕ, A y2 k < A y1 k := by
    intro k
    simp only [A_def]
    -- Apply exp_neg_diff_strict_dec with α₁ = π(2k+1)², α₂ = π(2k+2)².
    set α1 := Real.pi * ((2*k:ℝ) + 1)^2 with α1_def
    set α2 := Real.pi * ((2*k:ℝ) + 2)^2 with α2_def
    have hα1_pos : 0 < α1 := by
      apply mul_pos Real.pi_pos
      positivity
    have hα12 : α1 < α2 := by
      simp only [α1_def, α2_def]
      apply mul_lt_mul_of_pos_left _ Real.pi_pos
      have h1 : (0 : ℝ) ≤ (2*k:ℝ) + 1 := by positivity
      have h2 : (2*k:ℝ) + 1 < (2*k:ℝ) + 2 := by linarith
      exact pow_lt_pow_left₀ h2 h1 (by norm_num)
    have hα1_ge : 1 / y1 ≤ α1 := by
      have h_inv_le_one : 1 / y1 ≤ 1 := by
        rw [div_le_one hy1_pos]; exact hy1'
      have h_α1_ge : (1 : ℝ) ≤ α1 := by
        simp only [α1_def]
        have h1 : (1 : ℝ) ≤ ((2*k:ℝ) + 1)^2 := by
          have h_ge_one : (1 : ℝ) ≤ (2*k:ℝ) + 1 := by
            have : (0 : ℝ) ≤ (2*k:ℝ) := by positivity
            linarith
          calc (1 : ℝ) = 1^2 := by norm_num
            _ ≤ ((2*k:ℝ) + 1)^2 := pow_le_pow_left₀ (by norm_num) h_ge_one 2
        have h2 : Real.pi * 1 ≤ Real.pi * ((2*k:ℝ) + 1)^2 :=
          mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
        have h3 : (1 : ℝ) < Real.pi := Real.pi_gt_three.trans' (by norm_num)
        linarith
      linarith
    -- Apply exp_neg_diff_strict_dec.
    have h_dec := exp_neg_diff_strict_dec hy1_pos h_y12 hα1_ge hα12
    -- h_dec : exp(-α2·y1) - exp(-α2·y2) < exp(-α1·y1) - exp(-α1·y2).
    -- We want: exp(-α1·y2) - exp(-α2·y2) < exp(-α1·y1) - exp(-α2·y1).
    -- These are equivalent after rearrangement.
    change Real.exp (-Real.pi * ((2 * (k:ℝ)) + 1)^2 * y2) -
        Real.exp (-Real.pi * ((2 * (k:ℝ)) + 2)^2 * y2) <
        Real.exp (-Real.pi * ((2 * (k:ℝ)) + 1)^2 * y1) -
        Real.exp (-Real.pi * ((2 * (k:ℝ)) + 2)^2 * y1)
    have h_α1_eq : α1 = Real.pi * ((2 * (k:ℝ)) + 1)^2 := α1_def
    have h_α2_eq : α2 = Real.pi * ((2 * (k:ℝ)) + 2)^2 := α2_def
    have h_α1_y1 : -α1 * y1 = -Real.pi * ((2 * (k:ℝ)) + 1)^2 * y1 := by
      rw [h_α1_eq]; ring
    have h_α1_y2 : -α1 * y2 = -Real.pi * ((2 * (k:ℝ)) + 1)^2 * y2 := by
      rw [h_α1_eq]; ring
    have h_α2_y1 : -α2 * y1 = -Real.pi * ((2 * (k:ℝ)) + 2)^2 * y1 := by
      rw [h_α2_eq]; ring
    have h_α2_y2 : -α2 * y2 = -Real.pi * ((2 * (k:ℝ)) + 2)^2 * y2 := by
      rw [h_α2_eq]; ring
    rw [h_α1_y1, h_α1_y2, h_α2_y1, h_α2_y2] at h_dec
    linarith
  have h_A_le : ∀ k : ℕ, A y2 k ≤ A y1 k := fun k => (h_A_lt k).le
  -- Apply Summable.tsum_lt_tsum.
  have h_tsum_lt : ∑' k, A y2 k < ∑' k, A y1 k := by
    exact Summable.tsum_lt_tsum h_A_le (h_A_lt 0) h_A2.summable h_A1.summable
  rw [h_A1.tsum_eq, h_A2.tsum_eq] at h_tsum_lt
  -- h_tsum_lt : -(θ₄(iy2) - 1)/2 < -(θ₄(iy1) - 1)/2  ⇒  (θ₄(iy1)).re < (θ₄(iy2)).re.
  change (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re
  unfold theta4
  have h_re_sub : ∀ y : ℝ, (jacobiTheta (Complex.I * (y : ℂ) + 1) - 1).re =
      (jacobiTheta (Complex.I * (y : ℂ) + 1)).re - 1 := by
    intro y; rw [Complex.sub_re, Complex.one_re]
  rw [h_re_sub y1, h_re_sub y2] at h_tsum_lt
  linarith

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
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero]
    positivity
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

/-- **Pair helper for the small-`y` regime.** For `α ≥ 1/2` and
`1 ≤ u₂ < u₁`, the strict bound
`√u₁ · exp(-α·u₁) < √u₂ · exp(-α·u₂)` holds. Derivation:
`u₁/u₂ = 1 + (u₁−u₂)/u₂ < exp((u₁−u₂)/u₂)` (from `Real.add_one_lt_exp`),
hence `√(u₁/u₂) < exp((u₁−u₂)/(2u₂))`. Since `1/(2u₂) ≤ 1/2 ≤ α`,
this gives `√(u₁/u₂) < exp(α(u₁−u₂))`, i.e., the claim. -/
private lemma sqrt_exp_strict_dec {α u1 u2 : ℝ} (hα : 1 / 2 ≤ α) (hu2 : 1 ≤ u2)
    (hu12 : u2 < u1) :
    Real.sqrt u1 * Real.exp (-α * u1) < Real.sqrt u2 * Real.exp (-α * u2) := by
  have hu2_pos : 0 < u2 := lt_of_lt_of_le zero_lt_one hu2
  have hu1_pos : 0 < u1 := lt_trans hu2_pos hu12
  have hd_pos : 0 < u1 - u2 := sub_pos.mpr hu12
  have hsu1_pos : 0 < Real.sqrt u1 := Real.sqrt_pos.mpr hu1_pos
  have hsu2_pos : 0 < Real.sqrt u2 := Real.sqrt_pos.mpr hu2_pos
  -- Key inequality: u₁/u₂ < exp((u₁−u₂)/u₂).
  have hu2_ne0 : u2 ≠ 0 := ne_of_gt hu2_pos
  have h_div_eq : u1 / u2 = 1 + (u1 - u2) / u2 := by
    field_simp; ring
  have hd_div_pos : 0 < (u1 - u2) / u2 := div_pos hd_pos hu2_pos
  have h_div_ne : (u1 - u2) / u2 ≠ 0 := ne_of_gt hd_div_pos
  have h_exp_lt_aux : (u1 - u2) / u2 + 1 < Real.exp ((u1 - u2) / u2) :=
    Real.add_one_lt_exp h_div_ne
  have h_u_ratio_lt : u1 / u2 < Real.exp ((u1 - u2) / u2) := by
    rw [h_div_eq]; linarith
  -- exp((u₁−u₂)/u₂) = (exp((u₁−u₂)/(2u₂)))².
  have h_exp_sq : Real.exp ((u1 - u2) / u2) = (Real.exp ((u1 - u2) / (2*u2)))^2 := by
    rw [show ((Real.exp ((u1 - u2) / (2*u2)))^2 : ℝ) =
        Real.exp ((u1 - u2) / (2*u2)) * Real.exp ((u1 - u2) / (2*u2)) from sq _]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  -- √(u₁/u₂) < exp((u₁−u₂)/(2u₂)).
  have h_sqrt_lt : Real.sqrt (u1/u2) < Real.exp ((u1 - u2) / (2 * u2)) := by
    have h_pos_u : 0 ≤ u1/u2 := by positivity
    have h_pos_exp : 0 ≤ Real.exp ((u1 - u2) / (2 * u2)) := (Real.exp_pos _).le
    have h_eq : Real.exp ((u1 - u2) / (2 * u2)) =
        Real.sqrt ((Real.exp ((u1 - u2) / (2 * u2)))^2) := (Real.sqrt_sq h_pos_exp).symm
    rw [h_eq, ← h_exp_sq]
    exact Real.sqrt_lt_sqrt h_pos_u h_u_ratio_lt
  -- √u₁ < √u₂ · exp((u₁−u₂)/(2u₂)).
  have hu2_ne : u2 ≠ 0 := ne_of_gt hu2_pos
  have h_sqrt_div : Real.sqrt (u1/u2) = Real.sqrt u1 / Real.sqrt u2 :=
    Real.sqrt_div' u1 hu2_pos.le
  have h_su1_lt : Real.sqrt u1 < Real.sqrt u2 * Real.exp ((u1 - u2) / (2 * u2)) := by
    have h := h_sqrt_lt
    rw [h_sqrt_div, div_lt_iff₀ hsu2_pos] at h
    linarith
  -- 1/(2u₂) ≤ α, hence (u₁−u₂)/(2u₂) ≤ α·(u₁−u₂).
  have h_inv_le_α : 1 / (2 * u2) ≤ α := by
    have h_inv_le_half : 1 / (2 * u2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * u2) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  have h_d_α : (u1 - u2) / (2 * u2) ≤ α * (u1 - u2) := by
    have h1 : (u1 - u2) / (2 * u2) = (1 / (2 * u2)) * (u1 - u2) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right h_inv_le_α hd_pos.le
  -- √u₁ < √u₂ · exp(α(u₁−u₂)).
  have h_su1_lt' : Real.sqrt u1 < Real.sqrt u2 * Real.exp (α * (u1 - u2)) := by
    apply lt_of_lt_of_le h_su1_lt
    apply mul_le_mul_of_nonneg_left _ hsu2_pos.le
    exact Real.exp_le_exp.mpr h_d_α
  -- Multiply by exp(-α u₁) > 0 (positive) to get the desired form.
  have hex1_pos : 0 < Real.exp (-α * u1) := Real.exp_pos _
  have h_mul := mul_lt_mul_of_pos_right h_su1_lt' hex1_pos
  -- LHS: √u₁ · exp(-α u₁). RHS: √u₂ · exp(α(u₁−u₂)) · exp(-α u₁) = √u₂ · exp(-α u₂).
  have h_rhs_eq : Real.sqrt u2 * Real.exp (α * (u1 - u2)) * Real.exp (-α * u1) =
      Real.sqrt u2 * Real.exp (-α * u2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h_rhs_eq] at h_mul
  exact h_mul

/-- **Auxiliary: strict monotonicity of `θ₄(iy)` for `0 < y ≤ 1`.**
Modular transformation `θ_4(iy) · √y = θ_2(i/y)` reduces the small-`y`
regime to the large-`u` regime with `u = 1/y ≥ 1`. Expanding
`θ_2(iu) = 2·exp(-πu/4)·jacobiTheta₂(iu/2, iu)` and combining the
`exp(-πu/4)` factor with the `n`-th term `exp(-π·n(n+1)·u)` of
`jacobiTheta₂` gives `√u · θ_2(iu).re = 2·∑_{n ∈ ℤ} √u·exp(-π·(n+1/2)²·u)`.
Each term `√u·exp(-α·u)` with `α := π(n+1/2)² ≥ π/4 > 1/2` is strictly
antitone on `[1, ∞)` by `sqrt_exp_strict_dec`. Termwise strict
comparison via `Summable.tsum_lt_tsum` finishes. -/
theorem theta4_iy_strictMono_aux_small :
    StrictMonoOn (fun y : ℝ => (theta4 (Complex.I * (y : ℂ))).re) (Set.Ioc 0 1) := by
  -- Step 1: Auxiliary claim — `u ↦ √u · θ_2(iu).re` is strictly antitone on `[1, ∞)`.
  -- This is the heart of the proof; everything else is bookkeeping.
  have h_aux : ∀ u1 u2 : ℝ, 1 ≤ u2 → u2 < u1 →
      Real.sqrt u1 * (theta2 (Complex.I * (u1 : ℂ))).re <
        Real.sqrt u2 * (theta2 (Complex.I * (u2 : ℂ))).re := by
    intros u1 u2 hu2 h_u12
    have hu2_pos : 0 < u2 := lt_of_lt_of_le zero_lt_one hu2
    have hu1_pos : 0 < u1 := lt_trans hu2_pos h_u12
    -- Set up the jacobiTheta₂ HasSum at τ = i·u.
    have hτ1_im : 0 < (Complex.I * (u1 : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hu1_pos
    have hτ2_im : 0 < (Complex.I * (u2 : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hu2_pos
    -- jacobiTheta₂_term n (iu/2) (iu) = exp(-π·u·n(n+1)) (real positive).
    have h_jt2_term : ∀ u : ℝ, ∀ n : ℤ,
        jacobiTheta₂_term n (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ)) =
          ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      intros u n
      unfold jacobiTheta₂_term
      have h_arg : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (Complex.I * (u : ℂ) / 2) +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (u : ℂ)) =
          ((-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
        ring
      rw [h_arg, ← Complex.ofReal_exp]
    -- jacobiTheta₂(iu/2, iu) HasSum at τ = iu.
    have h_jt2_sum : ∀ u : ℝ, 0 < u →
        HasSum (fun n : ℤ => ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ))
          (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))) := by
      intros u hu
      have hτ_im : 0 < (Complex.I * (u : ℂ)).im := by
        simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
          Complex.ofReal_re, one_mul, zero_add]
        exact hu
      have h_sum := hasSum_jacobiTheta₂_term (Complex.I * (u : ℂ) / 2) hτ_im
      convert h_sum using 1
      funext n
      exact (h_jt2_term u n).symm
    -- Real version of the HasSum.
    have h_jt2_sum_re : ∀ u : ℝ, 0 < u →
        HasSum (fun n : ℤ => Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)))
          (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      intros u hu
      have h_map := (h_jt2_sum u hu).map Complex.reCLM Complex.reCLM.continuous
      simpa only [Complex.reCLM_apply, Complex.ofReal_re, Function.comp_def] using h_map
    -- jacobiTheta₂(iu/2, iu).re = ∑ exp(-π·u·n(n+1)).
    -- Now θ_2(iu) = exp(πi·iu/4) · jacobiTheta₂(iu/2, iu) = exp(-πu/4) · (the sum).
    have h_t2_eq : ∀ u : ℝ, 0 < u →
        (theta2 (Complex.I * (u : ℂ))).re =
          Real.exp (-Real.pi * u / 4) *
            (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      intros u hu
      unfold theta2
      have h_arg : (Real.pi : ℂ) * Complex.I * (Complex.I * (u : ℂ)) / 4 =
          ((-Real.pi * u / 4 : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
        ring
      rw [h_arg, ← Complex.ofReal_exp]
      rw [Complex.re_ofReal_mul]
    -- HasSum representation: √u · θ_2(iu).re = 2 · ∑ √u · exp(-π u/4 - π u n(n+1)).
    -- Define G u n := √u · exp(-π·u/4 - π·u·n(n+1)) = √u · exp(-π·u·(n+1/2)²) (after combining).
    -- We will show G u_2 n > G u_1 n for each n using sqrt_exp_strict_dec.
    -- HasSum for √u · θ_2(iu).re / 2 = exp(-π u/4) · jacobiTheta₂(iu/2, iu).re · √u.
    -- This is a HasSum of `(fun n : ℤ => √u · exp(-π·u/4 - π·u·n(n+1)))`.
    set G : ℝ → ℤ → ℝ := fun u n =>
      Real.sqrt u * Real.exp (-Real.pi * u / 4 - Real.pi * u * (n : ℝ) * ((n : ℝ) + 1))
      with G_def
    have h_G_eq : ∀ u : ℝ, ∀ n : ℤ,
        G u n =
          Real.sqrt u * Real.exp (-(Real.pi * ((n : ℝ) + 1/2)^2) * u) := by
      intros u n
      simp only [G_def]
      congr 1
      ring_nf
    have h_G_sum : ∀ u : ℝ, 0 < u →
        HasSum (G u)
          (Real.sqrt u * (theta2 (Complex.I * (u : ℂ))).re) := by
      intros u hu
      have hsu_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
      -- HasSum of (fun n => exp(-π·u·n(n+1))) = jacobiTheta₂(iu/2, iu).re.
      have h_inner := h_jt2_sum_re u hu
      -- Multiply by √u · exp(-π u/4): HasSum of (fun n => √u · exp(-π u/4) · exp(-π·u·n(n+1))).
      have h_const := h_inner.mul_left (Real.sqrt u * Real.exp (-Real.pi * u / 4))
      -- Combine: term = √u · exp(-π u/4 - π·u·n(n+1)) = G u n.
      have h_eq : ∀ n : ℤ,
          Real.sqrt u * Real.exp (-Real.pi * u / 4) *
            Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) = G u n := by
        intro n
        simp only [G_def]
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      rw [show (fun n : ℤ => Real.sqrt u * Real.exp (-Real.pi * u / 4) *
          Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1))) = G u from by
            funext n; exact h_eq n] at h_const
      -- h_const : HasSum (G u) (√u · exp(-π u/4) · jacobiTheta₂(iu/2, iu).re)
      --         = HasSum (G u) (√u · (theta2 iu).re) by h_t2_eq.
      have h_t2 := h_t2_eq u hu
      rw [show Real.sqrt u * Real.exp (-Real.pi * u / 4) *
          (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re =
          Real.sqrt u * ((theta2 (Complex.I * (u : ℂ))).re) from by
        rw [h_t2]; ring] at h_const
      exact h_const
    -- Now use strict comparison for each n.
    have hu1_ge_one : 1 ≤ u1 := le_of_lt (lt_of_le_of_lt hu2 h_u12)
    have h_term_lt : ∀ n : ℤ, G u1 n < G u2 n := by
      intro n
      rw [h_G_eq u1 n, h_G_eq u2 n]
      set α := Real.pi * ((n : ℝ) + 1/2)^2 with α_def
      have hα_ge : 1/2 ≤ α := by
        simp only [α_def]
        have h_sq_ge : (1/4 : ℝ) ≤ ((n : ℝ) + 1/2)^2 := by
          -- ((n : ℝ) + 1/2)^2 ≥ 1/4 since (n+1/2)² ≥ 1/4 for n ∈ ℤ.
          -- We have (n + 1/2)² = n² + n + 1/4 = n(n+1) + 1/4 ≥ 0 + 1/4 = 1/4.
          have h1 : (((n : ℝ) + 1/2)^2 : ℝ) = (n : ℝ) * ((n : ℝ) + 1) + 1/4 := by ring
          rw [h1]
          -- n(n+1) ≥ 0 for n ∈ ℤ.
          have h2 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
            rcases le_or_gt (0 : ℝ) (n : ℝ) with hn | hn
            · have hn' : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
              exact mul_nonneg hn hn'
            · -- n < 0 so n ≤ -1, then n + 1 ≤ 0, so n·(n+1) ≥ 0.
              have hn_int : n ≤ -1 := by
                have h_lt : (n : ℝ) < 0 := hn
                have h_lt' : (n : ℤ) < 0 := by exact_mod_cast h_lt
                omega
              have hn'' : ((n : ℝ) + 1) ≤ 0 := by
                have h_le : (n : ℝ) ≤ -1 := by exact_mod_cast hn_int
                linarith
              exact mul_nonneg_iff.mpr (Or.inr ⟨hn.le, hn''⟩)
          linarith
        have h_pi_pos : 0 < Real.pi := Real.pi_pos
        calc (1/2 : ℝ) ≤ Real.pi * (1/4) := by
                have h1 : Real.pi * (1/4) ≥ 3/4 := by
                  have h_pi_ge : Real.pi ≥ 3 := Real.pi_gt_three.le
                  linarith
                linarith
          _ ≤ Real.pi * ((n : ℝ) + 1/2)^2 := by
                exact mul_le_mul_of_nonneg_left h_sq_ge h_pi_pos.le
      exact sqrt_exp_strict_dec hα_ge hu2 h_u12
    have h_term_le : ∀ n : ℤ, G u1 n ≤ G u2 n := fun n => (h_term_lt n).le
    -- Strict comparison of tsums.
    have h_sum1 := h_G_sum u1 hu1_pos
    have h_sum2 := h_G_sum u2 hu2_pos
    have h_tsum_lt : ∑' n : ℤ, G u1 n < ∑' n : ℤ, G u2 n :=
      Summable.tsum_lt_tsum h_term_le (h_term_lt 0) h_sum1.summable h_sum2.summable
    rw [h_sum1.tsum_eq, h_sum2.tsum_eq] at h_tsum_lt
    exact h_tsum_lt
  -- Step 2: Translate back to (0, 1] via the modular transformation.
  intro y1 hy1 y2 hy2 h_y12
  obtain ⟨hy1_pos, hy1_le⟩ := hy1
  obtain ⟨hy2_pos, hy2_le⟩ := hy2
  -- Set u_i := 1/y_i; then u_1 > u_2 ≥ 1.
  have hu2_pos : 0 < 1/y2 := one_div_pos.mpr hy2_pos
  have hu1_pos : 0 < 1/y1 := one_div_pos.mpr hy1_pos
  have hu2_ge : 1 ≤ 1/y2 := by rw [le_div_iff₀ hy2_pos]; linarith
  have hu1_ge : 1 ≤ 1/y1 := by rw [le_div_iff₀ hy1_pos]; linarith
  have h_u_swap : 1/y2 < 1/y1 := one_div_lt_one_div_of_lt hy1_pos h_y12
  -- Show θ_4(iy).re = √u · θ_2(iu).re where u = 1/y, using modular transformation.
  have h_t4 : ∀ y : ℝ, 0 < y →
      (theta4 (Complex.I * (y : ℂ))).re =
        Real.sqrt (1/y) * (theta2 (Complex.I * ((1/y : ℝ) : ℂ))).re := by
    intros y hy
    -- (theta4 (I·y)).re · √y = (theta2 (I/y)).re from theta4_iy_mul_sqrt_eq_theta2.
    have h_modular_eq : Complex.I / (y : ℂ) = Complex.I * ((1/y : ℝ) : ℂ) := by
      have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
      push_cast; field_simp
    have h_mod := theta4_iy_mul_sqrt_eq_theta2 hy
    rw [h_modular_eq] at h_mod
    have hsqy_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hsqy_ne : Real.sqrt y ≠ 0 := ne_of_gt hsqy_pos
    -- (theta4 (I·y)).re = (theta2 (I · (1/y))).re / √y.
    have h_solve : (theta4 (Complex.I * (y : ℂ))).re =
        (theta2 (Complex.I * ((1/y : ℝ) : ℂ))).re / Real.sqrt y := by
      rw [eq_div_iff hsqy_ne]; exact h_mod
    -- 1/√y = √(1/y).
    have h_sqrt_inv : Real.sqrt (1/y) = 1 / Real.sqrt y := by
      rw [Real.sqrt_div' 1 hy.le, Real.sqrt_one]
    rw [h_solve, h_sqrt_inv]; ring
  -- Apply h_aux with u_1 := 1/y_1 and u_2 := 1/y_2.
  change (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re
  rw [h_t4 y1 hy1_pos, h_t4 y2 hy2_pos]
  exact h_aux (1/y1) (1/y2) hu2_ge h_u_swap

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
  intro y1 hy1 y2 hy2 h_y12
  have hy1_pos : (0 : ℝ) < y1 := hy1
  have hy2_pos : (0 : ℝ) < y2 := hy2
  have hτ1_im : 0 < (Complex.I * (y1 : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact hy1_pos
  have hτ2_im : 0 < (Complex.I * (y2 : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact hy2_pos
  -- Positivity helper for `θ_3(iy).re`: it equals `1 + 2·∑_{n≥0} exp(-π(n+1)²·y) ≥ 1 > 0`.
  have h_theta3_pos : ∀ y : ℝ, 0 < y → 1 ≤ (theta3 (Complex.I * (y : ℂ))).re := by
    intros y hy
    have h_yim : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hy
    have h_arg : ∀ n : ℕ, (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
        (Complex.I * (y : ℂ)) = ((-Real.pi * ((n : ℝ) + 1)^2 * y : ℝ) : ℂ) := by
      intro n; push_cast; ring_nf
      rw [show (Complex.I : ℂ)^2 = -1 from Complex.I_sq]; ring
    have h_term : ∀ n : ℕ,
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
          (Complex.I * (y : ℂ))) =
          ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ) := by
      intro n; rw [h_arg n, ← Complex.ofReal_exp]
    have h_sum_c := hasSum_nat_jacobiTheta h_yim
    have h_sum_c' : HasSum
        (fun n : ℕ => ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ))
        ((jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2) := by
      convert h_sum_c using 1; funext n; exact (h_term n).symm
    have h_sum_re : HasSum
        (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y))
        ((jacobiTheta (Complex.I * (y : ℂ)) - 1).re / 2) := by
      have h_map := h_sum_c'.map Complex.reCLM Complex.reCLM.continuous
      simp only [Complex.reCLM_apply, Complex.ofReal_re, Function.comp_def] at h_map
      rwa [Complex.div_ofNat_re] at h_map
    have h_tsum_nonneg : 0 ≤ (jacobiTheta (Complex.I * (y : ℂ)) - 1).re / 2 := by
      rw [← h_sum_re.tsum_eq]
      exact tsum_nonneg (fun n => (Real.exp_pos _).le)
    have h_jt_ge : 1 ≤ (jacobiTheta (Complex.I * (y : ℂ))).re := by
      have h_eq : (jacobiTheta (Complex.I * (y : ℂ)) - 1).re =
          (jacobiTheta (Complex.I * (y : ℂ))).re - 1 := by
        rw [Complex.sub_re, Complex.one_re]
      have h_pos : 0 ≤ (jacobiTheta (Complex.I * (y : ℂ))).re - 1 := by
        rw [← h_eq]; linarith [h_tsum_nonneg]
      linarith
    change 1 ≤ (theta3 (Complex.I * (y : ℂ))).re
    unfold theta3; exact h_jt_ge
  -- Positivity helper for `θ_2(iu).re`: it equals `exp(-πu/4)·∑_{n ∈ ℤ} exp(-πu·n(n+1)) > 0`.
  have h_theta2_pos : ∀ u : ℝ, 0 < u → 0 < (theta2 (Complex.I * (u : ℂ))).re := by
    intros u hu
    have h_uim : 0 < (Complex.I * (u : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hu
    -- jacobiTheta₂_term n (iu/2) (iu) = exp(-π·u·n(n+1)) (real positive).
    have h_jt2_term : ∀ n : ℤ,
        jacobiTheta₂_term n (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ)) =
          ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      intro n
      unfold jacobiTheta₂_term
      have h_arg : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (Complex.I * (u : ℂ) / 2) +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (u : ℂ)) =
          ((-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast; ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]; ring
      rw [h_arg, ← Complex.ofReal_exp]
    have h_sum := hasSum_jacobiTheta₂_term (Complex.I * (u : ℂ) / 2) h_uim
    have h_sum' : HasSum (fun n : ℤ =>
        ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ))
        (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))) := by
      convert h_sum using 1; funext n; exact (h_jt2_term n).symm
    have h_sum_re : HasSum (fun n : ℤ => Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)))
        (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      have h_map := h_sum'.map Complex.reCLM Complex.reCLM.continuous
      simp only [Complex.reCLM_apply, Complex.ofReal_re, Function.comp_def] at h_map
      exact h_map
    -- Sum of positives > 0 (e.g., term at n=0 is exp(0) = 1).
    have h_jt2_pos : 0 < (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      rw [← h_sum_re.tsum_eq]
      have h_term_nonneg : ∀ n : ℤ,
          0 ≤ Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) := fun n => (Real.exp_pos _).le
      have h_term0_pos' : 0 < Real.exp (-Real.pi * u * ((0 : ℤ) : ℝ) * (((0 : ℤ) : ℝ) + 1)) :=
        Real.exp_pos _
      exact lt_of_lt_of_le h_term0_pos' (Summable.le_tsum h_sum_re.summable 0
        (fun n _ => h_term_nonneg n))
    -- θ_2(iu).re = exp(-πu/4) · jacobiTheta₂(iu/2, iu).re > 0.
    unfold theta2
    have h_arg : (Real.pi : ℂ) * Complex.I * (Complex.I * (u : ℂ)) / 4 =
        ((-Real.pi * u / 4 : ℝ) : ℂ) := by
      push_cast; ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]; ring
    rw [h_arg, ← Complex.ofReal_exp, Complex.re_ofReal_mul]
    exact mul_pos (Real.exp_pos _) h_jt2_pos
  -- Positivity helper for `θ_4(iy).re`: from `θ_4(iy)·√y = θ_2(i/y)` and θ_2 > 0.
  have h_theta4_pos : ∀ y : ℝ, 0 < y → 0 < (theta4 (Complex.I * (y : ℂ))).re := by
    intros y hy
    have h_mod := theta4_iy_mul_sqrt_eq_theta2 hy
    have hsy_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have h_uim_eq : Complex.I / (y : ℂ) = Complex.I * ((1/y : ℝ) : ℂ) := by
      have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
      push_cast; field_simp
    rw [h_uim_eq] at h_mod
    have hu_pos : 0 < 1/y := one_div_pos.mpr hy
    have h_t2_pos := h_theta2_pos (1/y) hu_pos
    have h_t4_re_sq_pos : 0 < (theta4 (Complex.I * (y : ℂ))).re * Real.sqrt y := by
      rw [h_mod]; exact h_t2_pos
    have h_sy_ne : Real.sqrt y ≠ 0 := ne_of_gt hsy_pos
    have h_t4_eq : (theta4 (Complex.I * (y : ℂ))).re =
        ((theta4 (Complex.I * (y : ℂ))).re * Real.sqrt y) / Real.sqrt y := by
      field_simp
    rw [h_t4_eq]
    exact div_pos h_t4_re_sq_pos hsy_pos
  -- Now combine: 1 - λ(iy).re = (θ_4(iy).re / θ_3(iy).re)^4, and the ratio is strictly increasing.
  -- Key algebraic step.
  have h_lambda_eq : ∀ y : ℝ, 0 < y →
      1 - (modularLambdaH (Complex.I * (y : ℂ))).re =
        ((theta4 (Complex.I * (y : ℂ))).re / (theta3 (Complex.I * (y : ℂ))).re)^4 := by
    intros y hy
    have h_yim : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hy
    have h_jacobi : theta2 (Complex.I * (y : ℂ)) ^ 4 +
        theta4 (Complex.I * (y : ℂ)) ^ 4 =
        theta3 (Complex.I * (y : ℂ)) ^ 4 := jacobi_identity h_yim
    have hne3 : theta3 (Complex.I * (y : ℂ)) ≠ 0 := theta3_ne_zero h_yim
    have h_one_sub : (1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ)) =
        theta4 (Complex.I * (y : ℂ)) ^ 4 / theta3 (Complex.I * (y : ℂ)) ^ 4 := by
      unfold modularLambdaH
      field_simp
      linear_combination -h_jacobi
    have h4_im : (theta4 (Complex.I * (y : ℂ))).im = 0 := theta4_pure_imag_real hy
    have h3_im : (theta3 (Complex.I * (y : ℂ))).im = 0 := theta3_pure_imag_real hy
    have h_t4_eq : theta4 (Complex.I * (y : ℂ)) =
        ((theta4 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h4_im]
    have h_t3_eq : theta3 (Complex.I * (y : ℂ)) =
        ((theta3 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h3_im]
    have h_quot_eq : theta4 (Complex.I * (y : ℂ)) ^ 4 /
        theta3 (Complex.I * (y : ℂ)) ^ 4 =
        ((((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) : ℂ) := by
      conv_lhs => rw [h_t4_eq, h_t3_eq]
      push_cast; ring
    rw [h_quot_eq] at h_one_sub
    have h_re_eq : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        (((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) := by
      rw [h_one_sub, Complex.ofReal_re]
    have h_sub_re : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        1 - (modularLambdaH (Complex.I * (y : ℂ))).re := by simp
    rw [h_sub_re] at h_re_eq
    exact h_re_eq
  -- Apply for y1, y2.
  have h_t3_1 := h_theta3_pos y1 hy1_pos
  have h_t3_2 := h_theta3_pos y2 hy2_pos
  have h_t4_1 := h_theta4_pos y1 hy1_pos
  have h_t4_2 := h_theta4_pos y2 hy2_pos
  have h_t3_1_pos : 0 < (theta3 (Complex.I * (y1 : ℂ))).re := lt_of_lt_of_le zero_lt_one h_t3_1
  have h_t3_2_pos : 0 < (theta3 (Complex.I * (y2 : ℂ))).re := lt_of_lt_of_le zero_lt_one h_t3_2
  -- θ_4(iy_1).re < θ_4(iy_2).re from `theta4_iy_strictMono`.
  have h_t4_lt : (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re :=
    theta4_iy_strictMono hy1_pos hy2_pos h_y12
  -- θ_3(iy_2).re < θ_3(iy_1).re from `theta3_iy_strictAntitone`.
  have h_t3_lt : (theta3 (Complex.I * (y2 : ℂ))).re < (theta3 (Complex.I * (y1 : ℂ))).re :=
    theta3_iy_strictAntitone hy1_pos hy2_pos h_y12
  -- Ratio θ_4/θ_3 strictly increases.
  have h_ratio_lt : (theta4 (Complex.I * (y1 : ℂ))).re / (theta3 (Complex.I * (y1 : ℂ))).re <
      (theta4 (Complex.I * (y2 : ℂ))).re / (theta3 (Complex.I * (y2 : ℂ))).re := by
    rw [div_lt_div_iff₀ h_t3_1_pos h_t3_2_pos]
    -- Goal: θ_4(iy_1) · θ_3(iy_2) < θ_4(iy_2) · θ_3(iy_1).
    -- Bound θ_4(iy_1) · θ_3(iy_2) < θ_4(iy_2) · θ_3(iy_2) ≤ θ_4(iy_2) · θ_3(iy_1).
    have h_step1 : (theta4 (Complex.I * (y1 : ℂ))).re * (theta3 (Complex.I * (y2 : ℂ))).re <
        (theta4 (Complex.I * (y2 : ℂ))).re * (theta3 (Complex.I * (y2 : ℂ))).re :=
      mul_lt_mul_of_pos_right h_t4_lt h_t3_2_pos
    have h_step2 : (theta4 (Complex.I * (y2 : ℂ))).re * (theta3 (Complex.I * (y2 : ℂ))).re <
        (theta4 (Complex.I * (y2 : ℂ))).re * (theta3 (Complex.I * (y1 : ℂ))).re :=
      mul_lt_mul_of_pos_left h_t3_lt h_t4_2
    linarith
  -- The ratios are positive.
  have h_r1_pos : 0 < (theta4 (Complex.I * (y1 : ℂ))).re / (theta3 (Complex.I * (y1 : ℂ))).re :=
    div_pos h_t4_1 h_t3_1_pos
  have h_r2_pos : 0 < (theta4 (Complex.I * (y2 : ℂ))).re / (theta3 (Complex.I * (y2 : ℂ))).re :=
    div_pos h_t4_2 h_t3_2_pos
  -- Fourth powers preserve strict order on positives.
  have h_pow_lt : ((theta4 (Complex.I * (y1 : ℂ))).re / (theta3 (Complex.I * (y1 : ℂ))).re)^4 <
      ((theta4 (Complex.I * (y2 : ℂ))).re / (theta3 (Complex.I * (y2 : ℂ))).re)^4 :=
    pow_lt_pow_left₀ h_ratio_lt h_r1_pos.le (by norm_num)
  -- Conclude.
  change (modularLambdaH (Complex.I * (y2 : ℂ))).re < (modularLambdaH (Complex.I * (y1 : ℂ))).re
  have h_eq1 := h_lambda_eq y1 hy1_pos
  have h_eq2 := h_lambda_eq y2 hy2_pos
  linarith

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

/-- Helper for `modularLambdaH_im_nonneg_strip_interior_band`: `exp π > 22`.
Used to derive `r := exp(−πY) < 1/22` when `Y ≥ 1`. -/
theorem exp_pi_gt_22 : (22 : ℝ) < Real.exp Real.pi := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he3_pow : (2.7 : ℝ)^3 < (Real.exp 1)^3 :=
    pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  have he3_eq : (Real.exp 1)^3 = Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 from by ring, Real.exp_add, Real.exp_add]
    ring
  have he3 : (19.683 : ℝ) < Real.exp 3 := by
    rw [← he3_eq]
    have : (2.7 : ℝ)^3 = 19.683 := by norm_num
    linarith
  have he014 : (1.14 : ℝ) < Real.exp 0.14 := by
    have h_add : (0.14 : ℝ) ≠ 0 := by norm_num
    have h := Real.add_one_lt_exp h_add
    linarith
  have he314_eq : Real.exp 3.14 = Real.exp 3 * Real.exp 0.14 := by
    rw [← Real.exp_add]; congr 1; norm_num
  have he314 : (22 : ℝ) < Real.exp 3.14 := by
    rw [he314_eq]
    have hpos3 : 0 < Real.exp 3 := Real.exp_pos _
    have h_prod : (19.683 : ℝ) * 1.14 ≤ Real.exp 3 * Real.exp 0.14 := by
      apply mul_le_mul he3.le he014.le (by norm_num) hpos3.le
    have h_lt : (22 : ℝ) < 19.683 * 1.14 := by norm_num
    linarith
  have h_pi : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
  exact lt_of_lt_of_le he314 (Real.exp_le_exp.mpr h_pi.le)

/-- Helper: `√2 < 1.42`. -/
theorem sqrt_two_lt_142 : Real.sqrt 2 < 1.42 := by
  have h1 : Real.sqrt 2 < Real.sqrt ((1.42 : ℝ)^2) := by
    apply Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2)
    norm_num
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.42)] at h1

/-- Helper: `1.41 < √2`. -/
theorem sqrt_two_gt_141 : (1.41 : ℝ) < Real.sqrt 2 := by
  have h1 : Real.sqrt ((1.41 : ℝ)^2) < Real.sqrt 2 := by
    apply Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (1.41 : ℝ)^2)
    norm_num
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.41)] at h1

/-- Helper: `cos(π/8) < 0.926`. Uses `cos(π/8) = √(2 + √2)/2` and `√2 < 1.42`. -/
theorem cos_pi_div_eight_lt_926 : Real.cos (Real.pi / 8) < 0.926 := by
  rw [Real.cos_pi_div_eight]
  have h_inner_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2; linarith
  have h_1852_sq : ((1.852 : ℝ))^2 = 3.429904 := by norm_num
  have h_inner_lt_pow : (2 : ℝ) + Real.sqrt 2 < (1.852 : ℝ)^2 := by
    rw [h_1852_sq]; linarith [sqrt_two_lt_142]
  have h_step : Real.sqrt (2 + Real.sqrt 2) < Real.sqrt ((1.852 : ℝ)^2) :=
    Real.sqrt_lt_sqrt h_inner_nn h_inner_lt_pow
  rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.852)] at h_step
  linarith

/-- Helper: `sin(π/8) > 0.38`. Uses `sin(π/8) = √(2 − √2)/2` and `√2 < 1.42`. -/
theorem sin_pi_div_eight_gt_38 : (0.38 : ℝ) < Real.sin (Real.pi / 8) := by
  rw [Real.sin_pi_div_eight]
  have h_inner_nn : (0 : ℝ) ≤ 2 - Real.sqrt 2 := by linarith [sqrt_two_lt_142]
  have h_076_sq : ((0.76 : ℝ))^2 = 0.5776 := by norm_num
  have h_inner_gt_pow : ((0.76 : ℝ))^2 < 2 - Real.sqrt 2 := by
    rw [h_076_sq]; linarith [sqrt_two_lt_142]
  have h_step : Real.sqrt ((0.76 : ℝ)^2) < Real.sqrt (2 - Real.sqrt 2) :=
    Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (0.76 : ℝ)^2) h_inner_gt_pow
  rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.76)] at h_step
  linarith

/-- Helper: bracket lower bound for `modularLambdaH_im_nonneg_strip_interior_band`.
For `c ≤ cπ8`, `0 < cπ8 ≤ 1`, and `r ∈ (0, 1/22)`, the bracket
`B(c, r) := 16r − 256 r² c + 704 r³ (4c² − 1)` satisfies
`B(c, r) ≥ B(cπ8, r)`.
Proof via the algebraic identity
`B(c, r) − B(cπ8, r) = 256 r² (cπ8 − c)·(1 − 11r(c + cπ8))`. -/
theorem interior_band_bracket_lower_bound (r c cπ8 : ℝ)
    (hr_pos : 0 < r) (hr_lt : r < 1 / 22)
    (hcπ8_pos : 0 < cπ8) (hcπ8_le_one : cπ8 ≤ 1)
    (h_cos_ub : c ≤ cπ8) :
    16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) ≥
      16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1) := by
  have h_cπ8_minus_c : 0 ≤ cπ8 - c := by linarith
  have h_sum_le : c + cπ8 ≤ 2 * cπ8 := by linarith
  have h_one_minus_pos : 0 ≤ 1 - 11 * r * (c + cπ8) := by
    have h_step1 : 11 * r * (c + cπ8) ≤ 11 * r * (2 * cπ8) := by
      have h_11r_pos : 0 ≤ 11 * r := by linarith
      exact mul_le_mul_of_nonneg_left h_sum_le h_11r_pos
    have h_step2 : 11 * r * (2 * cπ8) = 22 * r * cπ8 := by ring
    have h_step3 : 22 * r * cπ8 < 1 * cπ8 := by
      apply mul_lt_mul_of_pos_right _ hcπ8_pos
      linarith
    have h_step4 : 1 * cπ8 ≤ 1 := by linarith
    linarith
  have h_r_sq_pos : 0 ≤ 256 * r^2 := by positivity
  have h_diff_nn : 0 ≤ 256 * r^2 * (cπ8 - c) * (1 - 11 * r * (c + cπ8)) := by
    apply mul_nonneg
    · apply mul_nonneg h_r_sq_pos h_cπ8_minus_c
    · exact h_one_minus_pos
  have h_identity :
      (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) -
      (16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1)) =
      256 * r^2 * (cπ8 - c) * (1 - 11 * r * (c + cπ8)) := by
    ring
  linarith [h_diff_nn, h_identity]

/-- Helper polynomial inequality for `modularLambdaH_im_nonneg_strip_interior_band`.
For `r ∈ (0, 1/22)`,
`0.38 · (16r − 237.056 r² + 1696.64 r³) ≥ 32768 r⁴`.
Proof via Horner factorization `r · g(r)` where
`g(r) := 6.08 − 90.08128 r + 644.7232 r² − 32768 r³ ≥ 0.23`. -/
theorem interior_band_polynomial_inequality (r : ℝ)
    (hr_pos : 0 < r) (hr_lt : r < 1 / 22) :
    0.38 * (16 * r - 237.056 * r^2 + 1696.64 * r^3) ≥ 32768 * r^4 := by
  have hr_le : r ≤ 1/22 := le_of_lt hr_lt
  have h_r2_le : r^2 ≤ 1/484 := by
    have h_step1 : r * r ≤ r * (1/22) :=
      mul_le_mul_of_nonneg_left hr_le (le_of_lt hr_pos)
    have h_step2 : r * (1/22 : ℝ) ≤ (1/22) * (1/22) :=
      mul_le_mul_of_nonneg_right hr_le (by norm_num)
    have h_eq_sq : r^2 = r * r := sq r
    have h_eq_const : (1/22 : ℝ) * (1/22) = 1/484 := by norm_num
    linarith
  have h_inner_lb : (644.7232 : ℝ) - 32768 * r ≥ -845 := by
    have h_le : 32768 * r ≤ 32768 * (1/22 : ℝ) :=
      mul_le_mul_of_nonneg_left hr_le (by norm_num)
    have h_val : (32768 : ℝ) * (1/22) ≤ 1489.7232 := by norm_num
    linarith
  have h_90r : 90.08128 * r ≤ 4.1 := by
    have h_le : 90.08128 * r ≤ 90.08128 * (1/22 : ℝ) :=
      mul_le_mul_of_nonneg_left hr_le (by norm_num)
    have h_val : (90.08128 : ℝ) * (1/22) ≤ 4.1 := by norm_num
    linarith
  have h_845r2 : 845 * r^2 ≤ 1.75 := by
    have h_le : 845 * r^2 ≤ 845 * (1/484 : ℝ) :=
      mul_le_mul_of_nonneg_left h_r2_le (by norm_num)
    have h_val : (845 : ℝ) * (1/484) ≤ 1.75 := by norm_num
    linarith
  have h_horner_eq : (6.08 : ℝ) - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3 =
      6.08 + r * (-90.08128 + r * (644.7232 - 32768 * r)) := by ring
  have h_outer_eq : r * (-90.08128 - 845 * r) = -(90.08128 * r) - 845 * r^2 := by ring
  have h_middle : -90.08128 + r * (644.7232 - 32768 * r) ≥ -90.08128 - 845 * r := by
    have h_mul : r * (644.7232 - 32768 * r) ≥ r * (-845) :=
      mul_le_mul_of_nonneg_left h_inner_lb (le_of_lt hr_pos)
    have h_eq : r * (-845 : ℝ) = -(845 * r) := by ring
    linarith
  have h_outer : r * (-90.08128 + r * (644.7232 - 32768 * r)) ≥
      r * (-90.08128 - 845 * r) :=
    mul_le_mul_of_nonneg_left h_middle (le_of_lt hr_pos)
  have h_g_lb : (6.08 : ℝ) - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3 ≥ 0.23 := by
    linarith
  have h_f_eq : (0.38 : ℝ) * (16 * r - 237.056 * r^2 + 1696.64 * r^3) - 32768 * r^4 =
      r * (6.08 - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3) := by ring
  have h_f_ge : r * (6.08 - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3) ≥ r * 0.23 :=
    mul_le_mul_of_nonneg_left h_g_lb (le_of_lt hr_pos)
  have h_r023_nn : (0 : ℝ) ≤ r * 0.23 :=
    mul_nonneg (le_of_lt hr_pos) (by norm_num)
  linarith

/-- **Interior band of the strip claim: `Im λ ≥ 0` on
`{Re ∈ [1/8, 7/8], Im ≥ 1}`.**

The three-term q-expansion
`‖λ(w) − 16q + 128q² − 704q³‖ ≤ 32768 exp(−4π·Im w)` combined with the
algebraic identity `Im(16q − 128q² + 704q³) = sin(πX)·B(Y, X)` where
`B(Y, X) := 16 exp(−πY) − 256 exp(−2πY)·cos(πX) +
704 exp(−3πY)·(4cos²(πX) − 1)`.

At the worst case `Y = 1, X = 1/8` (or `X = 7/8` by symmetry):
* `sin(π/8) = √(2 − √2)/2 > 0.382`
* `cos(π/8) = √(2 + √2)/2 < 0.925`
* `B(1, 1/8) > 0.387` (computed via `Real.pi_lt_d6`, `Real.exp_one_gt_d9`).
* `Im(leading) > 0.382 · 0.387 ≈ 0.148`.
* Error `32768 · exp(−4π) < 0.117`.
* Margin `≈ 0.030`, formalizable via Mathlib's tight bounds.

For larger `Y`, the margin grows since the error decays as `exp(−4πY)`
while the leading decays only as `exp(−πY)`. -/
theorem modularLambdaH_im_nonneg_strip_interior_band (w : ℂ)
    (hw_re_lo : (1 : ℝ) / 8 ≤ w.re) (hw_re_hi : w.re ≤ 7 / 8)
    (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  -- Strategy: apply three-term q-expansion bound, then verify
  -- Im(16q − 128q² + 704q³) − error ≥ 0 via tight numerical bounds.
  set Y := w.im with hY_def
  set X := w.re with hX_def
  have hY_pos : 0 < Y := by linarith
  have hY_one : 1 ≤ Y := hw_im_ge
  -- The argument of `q := exp(πi·w)` decomposes as
  -- `exp(πi·w) = exp(−π·Y) · exp(πi·X)`.
  -- Hence `q.re = exp(−πY)·cos(πX)` and `q.im = exp(−πY)·sin(πX)`.
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  -- Set q := exp(π·I·w), then compute real/imaginary parts.
  set q : ℂ := Complex.exp (Real.pi * Complex.I * w) with hq_def
  have h_argq : (Real.pi * Complex.I * w).re = -Real.pi * Y := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hY_def, Complex.ofReal_re,
      Complex.ofReal_im]
  have h_argq_im : (Real.pi * Complex.I * w).im = Real.pi * X := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hX_def, Complex.ofReal_re,
      Complex.ofReal_im]
  -- |q| = exp(-πY).
  have hq_norm : ‖q‖ = Real.exp (-Real.pi * Y) := by
    rw [hq_def, Complex.norm_exp, h_argq]
  -- Apply three-term q-expansion bound.
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * w) with hQ2_def
  set Q3 : ℂ := Complex.exp (3 * Real.pi * Complex.I * w) with hQ3_def
  have h_three_term : ‖modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3‖ ≤
      32768 * Real.exp (-4 * Real.pi * Y) := by
    have := modularLambdaH_norm_sub_three_term_le_of_im_ge_one (τ := w) hY_one
    rwa [← hq_def, ← hQ2_def, ← hQ3_def] at this
  -- Q2 = q^2, Q3 = q^3.
  have hQ2_eq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hQ3_eq : Q3 = q^3 := by
    rw [hQ3_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  -- Set r := exp(-πY) and the trig values.
  set r : ℝ := Real.exp (-Real.pi * Y) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  -- q.re = r·cos(πX), q.im = r·sin(πX).
  -- The decomposition `π·I·w = (−π·Y) + (π·X)·I` (real/imag parts).
  have h_decomp : Real.pi * Complex.I * w =
      ((-Real.pi * Y : ℝ) : ℂ) + ((Real.pi * X : ℝ) : ℂ) * Complex.I := by
    have hw_decomp : w = (X : ℂ) + (Y : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hX_def]
      · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hY_def]
    rw [hw_decomp]
    push_cast
    have hI_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (Real.pi * Y) * hI_sq
  have hq_re_eq : q.re = r * Real.cos (Real.pi * X) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * Y) from hr_def]
    ring
  have hq_im_eq : q.im = r * Real.sin (Real.pi * X) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_im, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * Y) from hr_def]
    ring
  -- Q2.im = r² · sin(2πX) = 2 r² sin(πX) cos(πX).
  -- Q3.im = r³ · sin(3πX) = r³ sin(πX) (4cos²(πX) − 1).
  -- These follow from Q2 = q² and Q3 = q³.
  have hQ2_re_eq : Q2.re = r^2 * (Real.cos (Real.pi * X))^2 -
      r^2 * (Real.sin (Real.pi * X))^2 := by
    rw [hQ2_eq, sq, Complex.mul_re, hq_re_eq, hq_im_eq]; ring
  have hQ2_im_eq : Q2.im = 2 * r^2 * Real.cos (Real.pi * X) * Real.sin (Real.pi * X) := by
    rw [hQ2_eq, sq, Complex.mul_im, hq_re_eq, hq_im_eq]; ring
  have hQ3_im_eq : Q3.im = r^3 * Real.sin (Real.pi * X) *
      (4 * (Real.cos (Real.pi * X))^2 - 1) := by
    rw [hQ3_eq, show q^3 = q^2 * q from by ring, Complex.mul_im, ← hQ2_eq,
      hQ2_re_eq, hQ2_im_eq, hq_re_eq, hq_im_eq]
    have h_pyth : (Real.sin (Real.pi * X))^2 + (Real.cos (Real.pi * X))^2 = 1 :=
      Real.sin_sq_add_cos_sq (Real.pi * X)
    linear_combination -r^3 * Real.sin (Real.pi * X) * h_pyth
  -- The imaginary part of `16q − 128 Q2 + 704 Q3` factors as
  -- `sin(πX) · Bracket(Y, X)` with explicit bracket.
  set s : ℝ := Real.sin (Real.pi * X) with hs_def
  set c : ℝ := Real.cos (Real.pi * X) with hc_def
  have h_lead_im : (16 * q - 128 * Q2 + 704 * Q3).im =
      s * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im]
    simp only [show (16 : ℂ).re = 16 from rfl, show (16 : ℂ).im = 0 from rfl,
      show (128 : ℂ).re = 128 from rfl, show (128 : ℂ).im = 0 from rfl,
      show (704 : ℂ).re = 704 from rfl, show (704 : ℂ).im = 0 from rfl]
    rw [hq_re_eq, hq_im_eq, hQ2_re_eq, hQ2_im_eq, hQ3_im_eq]
    ring
  -- Lower bound on `s = sin(πX)` for `X ∈ [1/8, 7/8]`.
  -- We have πX ∈ [π/8, 7π/8], and sin attains its min on this interval at the
  -- endpoints, both equal to sin(π/8).
  have h_piX_lo : Real.pi / 8 ≤ Real.pi * X := by
    have hX_lo : (1 : ℝ) / 8 ≤ X := hw_re_lo
    have h_div : Real.pi / 8 = Real.pi * (1 / 8) := by ring
    rw [h_div]
    exact mul_le_mul_of_nonneg_left hX_lo hπ_pos.le
  have h_piX_hi : Real.pi * X ≤ 7 * Real.pi / 8 := by
    have hX_hi : X ≤ 7 / 8 := hw_re_hi
    have h_div : 7 * Real.pi / 8 = Real.pi * (7 / 8) := by ring
    rw [h_div]
    exact mul_le_mul_of_nonneg_left hX_hi hπ_pos.le
  have h_piX_pos : 0 < Real.pi * X := by
    have : 0 < Real.pi / 8 := by positivity
    linarith
  have h_piX_lt_pi : Real.pi * X < Real.pi := by
    have : 7 * Real.pi / 8 < Real.pi := by linarith
    linarith
  -- sin(πX) ≥ sin(π/8) using `Real.sin_pos_of_pos_of_lt_pi` and monotonicity on
  -- the two halves of [0, π].
  have h_sin_pos : 0 < s := by
    rw [hs_def]
    exact Real.sin_pos_of_pos_of_lt_pi h_piX_pos h_piX_lt_pi
  have h_sin_lb : Real.sin (Real.pi / 8) ≤ s := by
    rw [hs_def]
    have h_neg_pi_div_two : -(Real.pi / 2) ≤ Real.pi / 8 := by
      have : 0 < Real.pi / 2 := by positivity
      have : 0 ≤ Real.pi / 8 := by positivity
      linarith
    by_cases h_X_le_half : X ≤ 1 / 2
    · -- Case X ∈ [1/8, 1/2]: πX ∈ [π/8, π/2]. sin monotone increasing.
      have h_piX_le_half : Real.pi * X ≤ Real.pi / 2 := by
        have h_div : Real.pi / 2 = Real.pi * (1 / 2) := by ring
        rw [h_div]
        exact mul_le_mul_of_nonneg_left h_X_le_half hπ_pos.le
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        h_neg_pi_div_two h_piX_le_half h_piX_lo
    · -- Case X ∈ (1/2, 7/8]: πX ∈ (π/2, 7π/8]. Use symmetry sin(πX) = sin(π − πX).
      push Not at h_X_le_half
      have h_piX_gt_half : Real.pi / 2 < Real.pi * X := by
        have h_div : Real.pi / 2 = Real.pi * (1 / 2) := by ring
        rw [h_div]
        exact mul_lt_mul_of_pos_left h_X_le_half hπ_pos
      -- sin(πX) = sin(π − πX); π − πX ∈ [π/8, π/2).
      have h_sin_sym : Real.sin (Real.pi * X) = Real.sin (Real.pi - Real.pi * X) := by
        rw [Real.sin_pi_sub]
      rw [h_sin_sym]
      have h_pi_sub_lo : Real.pi / 8 ≤ Real.pi - Real.pi * X := by linarith
      have h_pi_sub_hi : Real.pi - Real.pi * X ≤ Real.pi / 2 := by linarith
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        h_neg_pi_div_two h_pi_sub_hi h_pi_sub_lo
  -- Upper bound on `|c| = |cos(πX)|` by `cos(π/8)` for `X ∈ [1/8, 7/8]`.
  -- cos is monotone decreasing on `[0, π]`, so cos(πX) ≤ cos(π/8) (using X ≥ 1/8)
  -- and cos(πX) ≥ cos(7π/8) = -cos(π/8) (using X ≤ 7/8).
  have h_cos_ub : c ≤ Real.cos (Real.pi / 8) := by
    rw [hc_def]
    have h_X_pos : 0 < Real.pi * X := h_piX_pos
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (le_of_lt h_piX_lt_pi) h_piX_lo
  have h_cos_lb : -Real.cos (Real.pi / 8) ≤ c := by
    rw [hc_def]
    -- cos(πX) ≥ cos(7π/8) = -cos(π/8) for πX ≤ 7π/8.
    have h_cos_at_7_pi_8 : Real.cos (7 * Real.pi / 8) = -Real.cos (Real.pi / 8) := by
      have h_eq : 7 * Real.pi / 8 = Real.pi - Real.pi / 8 := by ring
      rw [h_eq, Real.cos_pi_sub]
    rw [← h_cos_at_7_pi_8]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by linarith [Real.pi_pos] : 7 * Real.pi / 8 ≤ Real.pi) h_piX_hi
  -- Bound on r: r = exp(−πY) ≤ exp(−π) for Y ≥ 1.
  have hr_le : r ≤ Real.exp (-Real.pi) := by
    rw [hr_def]
    apply Real.exp_le_exp.mpr
    nlinarith [hπ_pos]
  -- Hence r < 1/22, using `exp(π) > 22` (helper lemma).
  have hr_lt_22 : r < 1 / 22 := by
    have h_exp_neg : Real.exp (-Real.pi) < 1 / 22 := by
      rw [Real.exp_neg]
      rw [show (Real.exp Real.pi)⁻¹ = 1 / Real.exp Real.pi from by rw [inv_eq_one_div]]
      exact one_div_lt_one_div_of_lt (by norm_num) exp_pi_gt_22
    linarith
  -- Bracket lower bound: B(c, r) ≥ B(cos(π/8), r).
  -- We use the identity B(c, r) - B(cπ8, r) = 256 r² (cπ8 - c) · (1 - 11 r (c + cπ8))
  -- and show RHS ≥ 0 for c ≤ cπ8 and r < 1/22 with cπ8 ≤ 1.
  set cπ8 : ℝ := Real.cos (Real.pi / 8) with hcπ8_def
  have hcπ8_pos : 0 < cπ8 := by
    rw [hcπ8_def]
    have : 0 < Real.pi / 8 := by positivity
    have h_lt_half : Real.pi / 8 < Real.pi / 2 := by linarith
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h_lt_half⟩
  have hcπ8_le_one : cπ8 ≤ 1 := by
    rw [hcπ8_def]; exact Real.cos_le_one _
  have h_bracket_lb : 16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) ≥
      16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1) :=
    interior_band_bracket_lower_bound r c cπ8 hr_pos hr_lt_22 hcπ8_pos
      hcπ8_le_one h_cos_ub
  -- Numerical bounds (from helper lemmas).
  have h_sqrt2_gt : (1.41 : ℝ) < Real.sqrt 2 := sqrt_two_gt_141
  have h_cπ8_lt : cπ8 < 0.926 := by rw [hcπ8_def]; exact cos_pi_div_eight_lt_926
  have h_sπ8_gt : (0.38 : ℝ) < Real.sin (Real.pi / 8) := sin_pi_div_eight_gt_38
  -- r^4 = exp(-4πY).
  have hr4_eq : r^4 = Real.exp (-4 * Real.pi * Y) := by
    have h_cast : (-4 * Real.pi * Y : ℝ) = ((4 : ℕ) : ℝ) * (-Real.pi * Y) := by
      push_cast; ring
    rw [hr_def, h_cast]
    exact (Real.exp_nat_mul _ _).symm
  -- Decompose Im λ = err.im + lead.im where lead := 16q - 128Q2 + 704Q3.
  have h_im_split : (modularLambdaH w).im =
      (modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3).im +
        (16 * q - 128 * Q2 + 704 * Q3).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im]
    ring
  -- |err.im| ≤ ‖err‖ ≤ 32768 · r^4.
  have h_err_abs : |(modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3).im| ≤
      32768 * r^4 := by
    rw [hr4_eq]
    exact le_trans (Complex.abs_im_le_norm _) h_three_term
  -- Hence err.im ≥ -32768 · r^4.
  have h_err_lb : -(32768 * r^4) ≤
      (modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3).im :=
    neg_le_of_abs_le h_err_abs
  -- 4 cπ8² - 1 = 1 + √2 (from cos²(π/8) = (2 + √2)/4).
  have h_4cπ8_sq : 4 * cπ8^2 - 1 = 1 + Real.sqrt 2 := by
    rw [hcπ8_def, Real.cos_pi_div_eight]
    have h_sqrt_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
      have := Real.sqrt_nonneg 2; linarith
    have h_div_sq : (Real.sqrt (2 + Real.sqrt 2) / 2)^2 =
        (Real.sqrt (2 + Real.sqrt 2))^2 / 4 := by ring
    rw [h_div_sq, Real.sq_sqrt h_sqrt_nn]
    ring
  -- Hence 4 cπ8² - 1 > 2.41.
  have h_4cπ8_sq_gt : (2.41 : ℝ) < 4 * cπ8^2 - 1 := by
    rw [h_4cπ8_sq]; linarith
  -- Positivity of r^2, r^3.
  have hr2_pos : 0 < r^2 := pow_pos hr_pos 2
  have hr3_pos : 0 < r^3 := pow_pos hr_pos 3
  have hr4_pos : 0 < r^4 := pow_pos hr_pos 4
  -- B(cπ8, r) > 16r - 237.056 r² + 1696.64 r³ (using cπ8 < 0.926, 4cπ8²-1 > 2.41).
  have h_B_cπ8_lb :
      16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1) >
        16 * r - 237.056 * r^2 + 1696.64 * r^3 := by
    have h_term2 : -(256 * r^2 * cπ8) > -(256 * r^2 * 0.926) := by
      have h_pos : 0 < 256 * r^2 := by linarith
      have h_mul_lt : 256 * r^2 * cπ8 < 256 * r^2 * 0.926 :=
        mul_lt_mul_of_pos_left h_cπ8_lt h_pos
      linarith
    have h_term3 : 704 * r^3 * (4 * cπ8^2 - 1) > 704 * r^3 * 2.41 := by
      have h_pos : 0 < 704 * r^3 := by linarith
      exact mul_lt_mul_of_pos_left h_4cπ8_sq_gt h_pos
    have h_eq1 : (256 : ℝ) * r^2 * 0.926 = 237.056 * r^2 := by ring
    have h_eq2 : (704 : ℝ) * r^3 * 2.41 = 1696.64 * r^3 := by ring
    linarith
  -- B(c, r) ≥ B(cπ8, r) > 16r - 237.056 r² + 1696.64 r³.
  have h_B_lb_full :
      16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) >
        16 * r - 237.056 * r^2 + 1696.64 * r^3 := by
    linarith [h_bracket_lb, h_B_cπ8_lb]
  -- B(c, r) ≥ 0.
  -- For r ≤ 1/22, 16r - 237.056 r² > 0 (since r · (16 - 237.056/22) > 0).
  have h_poly_lb_pos : 0 < 16 * r - 237.056 * r^2 + 1696.64 * r^3 := by
    have h_1 : (16 : ℝ) - 237.056 * r > 0 := by
      have : (237.056 : ℝ) * r < 237.056 * (1/22) := by
        exact mul_lt_mul_of_pos_left hr_lt_22 (by norm_num)
      linarith
    have h_2 : 16 * r - 237.056 * r^2 > 0 := by
      have h_factor : 16 * r - 237.056 * r^2 = r * (16 - 237.056 * r) := by ring
      rw [h_factor]; exact mul_pos hr_pos h_1
    linarith [mul_pos (by linarith : (0:ℝ) < 1696.64) hr3_pos]
  have h_B_pos : 0 < 16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) := by
    linarith
  -- lead.im = s · B(c, r) ≥ 0.38 · B(c, r) ≥ 0.38 · (16r - 237.056 r² + 1696.64 r³).
  have h_s_lb : (0.38 : ℝ) < s := lt_of_lt_of_le h_sπ8_gt h_sin_lb
  have h_lead_im_lb :
      (16 * q - 128 * Q2 + 704 * Q3).im >
        0.38 * (16 * r - 237.056 * r^2 + 1696.64 * r^3) := by
    rw [h_lead_im]
    have h_step1 : (0.38 : ℝ) * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) <
        s * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) :=
      mul_lt_mul_of_pos_right h_s_lb h_B_pos
    have h_step2 : (0.38 : ℝ) * (16 * r - 237.056 * r^2 + 1696.64 * r^3) <
        0.38 * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) :=
      mul_lt_mul_of_pos_left h_B_lb_full (by norm_num)
    linarith
  -- Polynomial inequality: 0.38·(16r - 237.056r² + 1696.64r³) ≥ 32768 r^4 for r ∈ (0, 1/22).
  -- Expand: 6.08 r - 90.08128 r² + 644.7232 r³ ≥ 32768 r^4.
  -- Divide by r > 0: 6.08 - 90.08128 r + 644.7232 r² ≥ 32768 r^3.
  -- For r ≤ 1/22: 90.08128/22 ≈ 4.0946, 32768/22^3 ≈ 3.0779, gap ≈ 2 with r² term help.
  have h_poly_ineq : 0.38 * (16 * r - 237.056 * r^2 + 1696.64 * r^3) ≥ 32768 * r^4 :=
    interior_band_polynomial_inequality r hr_pos hr_lt_22
  -- Now combine: lead.im > 0.38 · (...) ≥ 32768 r^4 ≥ -err.im, so lead.im + err.im > 0.
  rw [h_im_split]
  linarith

/-- **General T-shift form for `λ`.** For `τ ∈ ℍ`,
`λ(τ + 1) = λ(τ)/(λ(τ) − 1)`.
Derived from `modularLambdaH_T_smul` (`λ(τ + 1) = −θ₂(τ)⁴/θ₄(τ)⁴`)
and the Jacobi identity `θ₂⁴ + θ₄⁴ = θ₃⁴`. -/
theorem modularLambdaH_add_one_eq_div_sub_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (τ + 1) = modularLambdaH τ / (modularLambdaH τ - 1) := by
  have h_jacobi : theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := jacobi_identity hτ
  have hne3 : theta3 τ ≠ 0 := theta3_ne_zero hτ
  have hne4 : theta4 τ ≠ 0 := theta4_ne_zero hτ
  have h_lam_sub_ne : modularLambdaH τ - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hτ)
  rw [modularLambdaH_T_smul, eq_div_iff h_lam_sub_ne]
  unfold modularLambdaH
  field_simp
  linear_combination -(theta2 τ ^ 4) * h_jacobi

/-- **Cusp 1 norm limit inside `F^o`.** As `τ → 1` along any path in
`F^o`, `‖λ(τ)‖ → ∞`. Proof: `σ := τ − 1 → 0` with `Re σ < 0` and
`Im σ > 0`. Set `w := −1/σ`. Then `|w|² = 1/|σ|² → ∞`; the F^o
constraint `‖2τ − 1‖ > 1` gives `Re w < 1`, hence
`Im²w ≥ |w|² − 1 → ∞`. The cusp-∞ bound
`modularLambdaH_norm_le_exp_of_im_ge_one` then gives `λ(w) → 0`, and the
T-shift identity `λ(τ) = 1 − 1/λ(w)` yields `‖λ(τ)‖ → ∞`. -/
theorem modularLambdaH_cusp_one_tendsto_norm_atTop_in_F :
    Filter.Tendsto (fun τ => ‖modularLambdaH τ‖)
      (nhdsWithin (1 : ℂ) Gamma2FundamentalDomainInterior) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro N
  have hπ_pos : (0:ℝ) < Real.pi := Real.pi_pos
  set M : ℝ := |N| + 2 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; have := abs_nonneg N; linarith
  have hM_minus_one_ge_N : N ≤ M - 1 := by
    rw [hM_def]; have := le_abs_self N; linarith
  set K : ℝ := max 1 (Real.log (160000 * M) / Real.pi) with hK_def
  have hK_ge_one : 1 ≤ K := le_max_left _ _
  have hK_pos : 0 < K := by linarith
  have h_K_ge_log : Real.log (160000 * M) / Real.pi ≤ K := le_max_right _ _
  have h_log_pos : 0 < 160000 * M := by positivity
  have h_exp_K_pos : 0 < Real.exp (Real.pi * K) := Real.exp_pos _
  have h_exp_K_ge : 160000 * M ≤ Real.exp (Real.pi * K) := by
    have h_step : Real.log (160000 * M) ≤ Real.pi * K := by
      rw [div_le_iff₀ hπ_pos] at h_K_ge_log; linarith
    have := Real.exp_le_exp.mpr h_step
    rwa [Real.exp_log h_log_pos] at this
  have h_exp_neg_K : 160000 * Real.exp (-Real.pi * K) ≤ 1 / M := by
    rw [show -Real.pi * K = -(Real.pi * K) from by ring, Real.exp_neg, le_div_iff₀ hM_pos]
    rw [show (160000 * (Real.exp (Real.pi * K))⁻¹ * M : ℝ) =
      (160000 * M) / Real.exp (Real.pi * K) from by field_simp]
    rw [div_le_one h_exp_K_pos]
    exact h_exp_K_ge
  set δ : ℝ := 1 / (K + 1) with hδ_def
  have hK_p1_pos : 0 < K + 1 := by linarith
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (1 : ℂ) δ ∩ Gamma2FundamentalDomainInterior, ?_, ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Metric.ball (1 : ℂ) δ, Metric.isOpen_ball, Metric.mem_ball_self hδ_pos, ?_⟩
    intro y hy; exact hy
  · intro τ ⟨hτ_ball, hτ_F⟩
    obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
    rw [Metric.mem_ball, Complex.dist_eq] at hτ_ball
    set σ := τ - 1 with hσ_def
    have hσ_norm_lt : ‖σ‖ < δ := hτ_ball
    have hσ_im_pos : 0 < σ.im := by
      change 0 < (τ - 1).im
      simp only [Complex.sub_im, Complex.one_im, sub_zero]; exact hτ_im_pos
    have hσ_re_neg : σ.re < 0 := by
      change (τ - 1).re < 0
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have hσ_ne : σ ≠ 0 := fun h => by rw [h] at hσ_im_pos; simp at hσ_im_pos
    have hσ_norm_pos : 0 < ‖σ‖ := norm_pos_iff.mpr hσ_ne
    have hσ_normSq_eq : Complex.normSq σ = ‖σ‖^2 := by rw [← Complex.sq_norm]
    have hσ_normSq_pos : 0 < Complex.normSq σ := Complex.normSq_pos.mpr hσ_ne
    have hτ_F_constraint : -σ.re < Complex.normSq σ := by
      have h_sq_lt : 1 < ‖2 * τ - 1‖^2 := by
        have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
        nlinarith
      have h_eq : 2 * τ - 1 = 2 * σ + 1 := by rw [hσ_def]; ring
      have h_normSq_eq : Complex.normSq (2 * τ - 1) > 1 := by
        rw [← Complex.sq_norm]; exact h_sq_lt
      rw [h_eq] at h_normSq_eq
      have h_expand : Complex.normSq (2 * σ + 1) = 4 * Complex.normSq σ + 4 * σ.re + 1 := by
        simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.one_re, Complex.one_im]; ring
      rw [h_expand] at h_normSq_eq
      linarith
    set w := -1 / σ with hw_def
    have hw_eq_neg_inv : w = -σ⁻¹ := by rw [hw_def, neg_div, one_div]
    have hw_re : w.re = -σ.re / Complex.normSq σ := by
      rw [hw_eq_neg_inv, Complex.neg_re, Complex.inv_re]; ring
    have hw_im : w.im = σ.im / Complex.normSq σ := by
      rw [hw_eq_neg_inv, Complex.neg_im, Complex.inv_im]; ring
    have hw_im_pos : 0 < w.im := by
      rw [hw_im]; exact div_pos hσ_im_pos hσ_normSq_pos
    have hw_re_pos : 0 < w.re := by
      rw [hw_re]; apply div_pos _ hσ_normSq_pos; linarith
    have hw_re_lt_one : w.re < 1 := by
      rw [hw_re]; rw [div_lt_one hσ_normSq_pos]
      linarith
    have hw_normSq_eq : Complex.normSq w = 1 / Complex.normSq σ := by
      have h1 : ‖w‖^2 = Complex.normSq w := Complex.sq_norm _
      have h2 : ‖σ‖^2 = Complex.normSq σ := Complex.sq_norm _
      have h3 : ‖w‖ = ‖σ‖⁻¹ := by rw [hw_eq_neg_inv, norm_neg, norm_inv]
      rw [← h1, h3, inv_pow, h2, one_div]
    have h_normSq_σ_lt : Complex.normSq σ < δ^2 := by
      rw [hσ_normSq_eq]
      apply sq_lt_sq' (by linarith [norm_nonneg σ]) hσ_norm_lt
    have hw_normSq_gt : Complex.normSq w > (K + 1)^2 := by
      rw [hw_normSq_eq]
      rw [gt_iff_lt, lt_div_iff₀ hσ_normSq_pos]
      have h_pos_sq : 0 < (K + 1)^2 := by positivity
      have h_step : (K + 1)^2 * Complex.normSq σ < (K + 1)^2 * δ^2 :=
        mul_lt_mul_of_pos_left h_normSq_σ_lt h_pos_sq
      have h_δsq_inv : δ^2 = 1 / (K + 1)^2 := by
        rw [hδ_def, div_pow, one_pow]
      have h_eq : (K + 1)^2 * δ^2 = 1 := by
        rw [h_δsq_inv]; field_simp
      linarith
    have hw_re_sq_lt : w.re^2 < 1 := by nlinarith [hw_re_pos, hw_re_lt_one]
    have hw_im_sq_gt : w.im^2 > K^2 := by
      have h_normSq : Complex.normSq w = w.re^2 + w.im^2 := by
        simp [Complex.normSq_apply]; ring
      have h_sum : w.re^2 + w.im^2 > (K + 1)^2 := h_normSq ▸ hw_normSq_gt
      nlinarith
    have hw_im_gt_K : K < w.im := by
      have h_sq : K^2 < w.im^2 := hw_im_sq_gt
      nlinarith [hw_im_pos]
    have hw_im_ge_one : 1 ≤ w.im := by linarith
    have h_lamw_bound : ‖modularLambdaH w‖ ≤ 160000 * Real.exp (-Real.pi * w.im) :=
      modularLambdaH_norm_le_exp_of_im_ge_one hw_im_ge_one
    have h_exp_mono : Real.exp (-Real.pi * w.im) ≤ Real.exp (-Real.pi * K) := by
      apply Real.exp_le_exp.mpr
      have h_mul : Real.pi * K ≤ Real.pi * w.im :=
        mul_le_mul_of_nonneg_left hw_im_gt_K.le hπ_pos.le
      linarith
    have h_lamw_le : ‖modularLambdaH w‖ ≤ 1 / M := by
      calc ‖modularLambdaH w‖
          ≤ 160000 * Real.exp (-Real.pi * w.im) := h_lamw_bound
        _ ≤ 160000 * Real.exp (-Real.pi * K) :=
            mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
        _ ≤ 1 / M := h_exp_neg_K
    have hlamw_ne_zero : modularLambdaH w ≠ 0 := modularLambdaH_ne_zero hw_im_pos
    have hlamw_norm_pos : 0 < ‖modularLambdaH w‖ := norm_pos_iff.mpr hlamw_ne_zero
    have h_S : modularLambdaH σ + modularLambdaH w = 1 := by
      have := modularLambdaH_add_S_smul_eq_one hσ_im_pos
      rw [hw_def]; exact this
    have hlamσ_eq : modularLambdaH σ = 1 - modularLambdaH w := by linear_combination h_S
    have hστ_eq : σ + 1 = τ := by rw [hσ_def]; ring
    have h_T : modularLambdaH τ = modularLambdaH σ / (modularLambdaH σ - 1) := by
      rw [← hστ_eq]
      exact modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
    have hlamτ_check_eq : modularLambdaH τ = 1 - 1 / modularLambdaH w := by
      rw [h_T, hlamσ_eq]
      have h_denom_eq : (1 - modularLambdaH w) - 1 = -modularLambdaH w := by ring
      rw [h_denom_eq]
      field_simp; ring
    rw [hlamτ_check_eq]
    have h_inv_norm : ‖(1 : ℂ) / modularLambdaH w‖ = 1 / ‖modularLambdaH w‖ := by
      rw [norm_div, norm_one]
    have h_inv_lower : M ≤ ‖(1 : ℂ) / modularLambdaH w‖ := by
      rw [h_inv_norm, le_div_iff₀ hlamw_norm_pos]
      have h_step : ‖modularLambdaH w‖ * M ≤ (1 / M) * M :=
        mul_le_mul_of_nonneg_right h_lamw_le hM_pos.le
      rw [div_mul_cancel₀ 1 (ne_of_gt hM_pos)] at h_step
      linarith
    have h_tri : ‖(1 : ℂ) / modularLambdaH w‖ - ‖(1 : ℂ)‖ ≤
        ‖(1 : ℂ) / modularLambdaH w - 1‖ :=
      norm_sub_norm_le _ _
    have h_one_norm : ‖(1 : ℂ)‖ = 1 := norm_one
    have h_eq_neg : (1 : ℂ) / modularLambdaH w - 1 = -((1 : ℂ) - 1 / modularLambdaH w) := by
      ring
    rw [h_eq_neg, norm_neg] at h_tri
    linarith

/-- **Direct three-term q-expansion bound on `λ'` at `τ.im ≥ 1`.**
For `τ ∈ ℍ` with `τ.im ≥ 1`,
`‖deriv λ τ − 16πi q + 256πi q² − 2112πi q³‖ ≤ 100000 · exp(−4π·τ.im)`
where `q := exp(πi τ)`. The bound is derived from the q-expansion
power series of `λ'` directly. The tight asymptotic value of the
constant is `π · ∑_{n≥4} n |c_n| · exp(−π(n−4)) ≈ 47995`, evaluated
at the boundary `τ.im = 1` (the supremum). The chosen constant
`100000` provides a `≈ 108%` margin over this asymptotic value and
remains compatible with the closure constraint `K · r^3 < 3π` for
`r ≤ exp(−π) < 1/22` required by
`modularLambdaH_deriv_im_nonneg_on_left_edge` (since
`100000/10648 ≈ 9.391 < 3π ≈ 9.425`).

The closure path goes through the widened four-term cusp-function
infrastructure in `ModularFunction.lean`: at the boundary `τ.im = 1`,
`|q| = exp(−π)`, and Cauchy on the standard disk `|z| ≤ exp(−π)`
collapses to zero radius. The widened bound
`modularLambdaH_cusp_norm_sub_four_term_le_widened` extends the
four-term function bound to the strictly larger disk
`|z| ≤ exp(−9π/10)`, allowing Cauchy at radius
`ρ = ‖q‖/4` (sphere stays inside `|z| ≤ 5‖q‖/4 ≤ exp(−9π/10)`).
This yields `modularLambdaH_cusp_deriv_sub_two_term_le_widened`
on the full disk `‖q‖ ≤ exp(−π)`, which combines with the chain
rule `deriv λ τ = πi · q · deriv cusp(q)` to give the stated
derivative bound on `τ.im ≥ 1`. -/
theorem modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one
    {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖deriv modularLambdaH τ -
        16 * (Real.pi : ℂ) * Complex.I * Complex.exp (Real.pi * Complex.I * τ) +
        256 * (Real.pi : ℂ) * Complex.I *
          Complex.exp (2 * Real.pi * Complex.I * τ) -
        2112 * (Real.pi : ℂ) * Complex.I *
          Complex.exp (3 * Real.pi * Complex.I * τ)‖ ≤
      100000 * Real.exp (-4 * Real.pi * τ.im) := by
  set q : ℂ := Complex.exp (Real.pi * Complex.I * τ) with hq_def
  have hq_ne : q ≠ 0 := Complex.exp_ne_zero _
  have hτ_im_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  -- ‖q‖ = exp(-π τ.im).
  have h_q_norm_eq : ‖q‖ = Real.exp (-Real.pi * τ.im) := by
    rw [hq_def, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_q_norm_pos : 0 < ‖q‖ := by rw [h_q_norm_eq]; exact Real.exp_pos _
  -- ‖q‖ ≤ exp(-π).
  have h_q_norm_le : ‖q‖ ≤ Real.exp (-Real.pi) := by
    rw [h_q_norm_eq]
    apply Real.exp_le_exp.mpr
    nlinarith
  -- ‖q‖ < 1 from τ.im ≥ 1.
  have h_q_lt_1 : ‖q‖ < 1 := by
    rw [h_q_norm_eq, Real.exp_lt_one_iff]
    nlinarith
  -- ‖q‖^4 = exp(-4π τ.im).
  have h_q_norm_pow4 : ‖q‖^4 = Real.exp (-4 * Real.pi * τ.im) := by
    rw [h_q_norm_eq]
    rw [show (-4 * Real.pi * τ.im : ℝ) =
      (-Real.pi * τ.im) + (-Real.pi * τ.im) + (-Real.pi * τ.im) + (-Real.pi * τ.im) from by ring,
      Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  -- Widened cusp deriv bound at q.
  have h_widened := modularLambdaH_cusp_deriv_sub_two_term_le_widened h_q_norm_le hq_ne
  -- Chain rule for q(τ) = exp(πi τ): deriv q τ = πi · q.
  have h_lin_hasDeriv : HasDerivAt (fun z : ℂ => Real.pi * Complex.I * z)
      (Real.pi * Complex.I) τ := by
    simpa using (hasDerivAt_id τ).const_mul (Real.pi * Complex.I : ℂ)
  have h_q_fn_hasDeriv : HasDerivAt (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z))
      ((Real.pi * Complex.I) * q) τ := by
    have h_comp := (Complex.hasDerivAt_exp (Real.pi * Complex.I * τ)).comp τ h_lin_hasDeriv
    -- h_comp : HasDerivAt (exp ∘ (πi·)) (exp(πi τ) * πi) τ
    convert h_comp using 1
    rw [hq_def]; ring
  -- Cusp differentiable at q.
  have h_cusp_diff_at_q : DifferentiableAt ℂ modularLambdaH_cusp q :=
    modularLambdaH_cusp_differentiableAt_of_norm_lt_one hq_ne h_q_lt_1
  have h_cusp_hasDeriv : HasDerivAt modularLambdaH_cusp (deriv modularLambdaH_cusp q) q :=
    h_cusp_diff_at_q.hasDerivAt
  -- Composition.
  have h_comp_hasDeriv : HasDerivAt
      (modularLambdaH_cusp ∘ (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z)))
      (deriv modularLambdaH_cusp q * ((Real.pi * Complex.I) * q)) τ :=
    h_cusp_hasDeriv.comp τ h_q_fn_hasDeriv
  -- λ = cusp ∘ (z ↦ exp(πi z)).
  have h_funeq : (modularLambdaH_cusp ∘ (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z))) =
      modularLambdaH := by
    funext τ'
    change modularLambdaH_cusp (Complex.exp (Real.pi * Complex.I * τ')) = modularLambdaH τ'
    have h_qParam_eq : Function.Periodic.qParam 2 τ' = Complex.exp (Real.pi * Complex.I * τ') := by
      unfold Function.Periodic.qParam
      congr 1
      push_cast; ring
    rw [← h_qParam_eq]
    exact modularLambdaH_cusp_qParam τ'
  rw [h_funeq] at h_comp_hasDeriv
  have h_deriv_lam_eq : deriv modularLambdaH τ =
      deriv modularLambdaH_cusp q * ((Real.pi * Complex.I) * q) := h_comp_hasDeriv.deriv
  -- Identities exp(2πi τ) = q², exp(3πi τ) = q³.
  have h_qsq : Complex.exp (2 * Real.pi * Complex.I * τ) = q^2 := by
    rw [show (2 * Real.pi * Complex.I * τ : ℂ) =
      (Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) from by ring,
      Complex.exp_add, ← hq_def, sq]
  have h_qcube : Complex.exp (3 * Real.pi * Complex.I * τ) = q^3 := by
    rw [show (3 * Real.pi * Complex.I * τ : ℂ) =
      (2 * Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) from by ring,
      Complex.exp_add, h_qsq, ← hq_def]
    ring
  rw [h_qsq, h_qcube, h_deriv_lam_eq]
  -- Algebraic factoring.
  have h_factor :
      deriv modularLambdaH_cusp q * (Real.pi * Complex.I * q) -
        16 * (Real.pi : ℂ) * Complex.I * q +
        256 * (Real.pi : ℂ) * Complex.I * q^2 -
        2112 * (Real.pi : ℂ) * Complex.I * q^3 =
      (Real.pi : ℂ) * Complex.I * q *
        (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2) := by
    ring
  rw [h_factor]
  -- Norm computation.
  have h_norm_factor :
      ‖(Real.pi : ℂ) * Complex.I * q *
          (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2)‖ =
      Real.pi * ‖q‖ * ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hπ_pos]
  rw [h_norm_factor]
  -- Bound chain.
  have h_pi_q_nn : (0 : ℝ) ≤ Real.pi * ‖q‖ := by positivity
  have h_exp_nn : (0 : ℝ) ≤ Real.exp (-4 * Real.pi * τ.im) := (Real.exp_pos _).le
  calc Real.pi * ‖q‖ * ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2‖
      ≤ Real.pi * ‖q‖ * (31000 * ‖q‖^3) :=
        mul_le_mul_of_nonneg_left h_widened h_pi_q_nn
    _ = 31000 * Real.pi * ‖q‖^4 := by ring
    _ = 31000 * Real.pi * Real.exp (-4 * Real.pi * τ.im) := by rw [h_q_norm_pow4]
    _ ≤ 100000 * Real.exp (-4 * Real.pi * τ.im) := by
        have h_pi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
        have h_31000_pi_le : 31000 * Real.pi ≤ 100000 := by nlinarith
        exact mul_le_mul_of_nonneg_right h_31000_pi_le h_exp_nn

set_option maxHeartbeats 400000 in
-- The proof accumulates many local hypotheses (q, Q2, Q3 components,
-- bracket bounds, exp bounds, numerical bounds on √2, cos(π/8)) that
-- exceed the default 200000-heartbeat ceiling. Raising to 400000
-- (the project-wide allowed maximum) is the minimal accommodation.
/-- **Positivity of `Im λ'` on the closed left-edge strip.** For `w`
with `0 ≤ Re w ≤ 1/8` and `Im w ≥ 1`, `Im (deriv λ w) ≥ 0`.

The proof uses the direct three-term derivative bound
`modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one`:
`λ' = πi (16q − 256q² + 2112q³) + R` with `|R| ≤ 100000·exp(−4π·Im w)`.
Taking imaginary parts and using `cos(πx)`-bounds:
`Im λ'(w) = π·(16 cos(πx) e^{−πy} − 256 cos(2πx) e^{−2πy} +
2112 cos(3πx) e^{−3πy}) + Im R`.
For `x ∈ [0, 1/8]`, the leading bracket is bounded below by
`14.72 e^{−πy} − 256 e^{−2πy} + (nonneg) ≥ 3·e^{−πy}` when
`r = e^{−πy} ≤ 1/22` (using `cos(π/8) > 0.92`). So
`Im L = π · (bracket) ≥ 3π · r`. The error contributes
`|Im R| ≤ 100000 · r^4`. Closure: `3π · r − 100000 · r^4 = r · (3π − 100000 · r³) ≥ 0`
when `100000 · r³ ≤ 100000/10648 ≈ 9.391 < 3π ≈ 9.425`. -/
theorem modularLambdaH_deriv_im_nonneg_on_left_edge (w : ℂ)
    (hw_re_nn : 0 ≤ w.re) (hw_re_le : w.re ≤ 1 / 8) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (deriv modularLambdaH w).im := by
  set y := w.im with hy_def
  set x := w.re with hx_def
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le one_pos hw_im_ge
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Setup q, Q2, Q3.
  set q : ℂ := Complex.exp (Real.pi * Complex.I * w) with hq_def
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * w) with hQ2_def
  set Q3 : ℂ := Complex.exp (3 * Real.pi * Complex.I * w) with hQ3_def
  -- Get derivative bound.
  have h_deriv_bound := modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one
    (τ := w) hw_im_ge
  rw [← hq_def, ← hQ2_def, ← hQ3_def] at h_deriv_bound
  -- Compute real/imag parts of q, Q2, Q3.
  have h_argq_re : (Real.pi * Complex.I * w).re = -Real.pi * y := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hy_def,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_argq_im : (Real.pi * Complex.I * w).im = Real.pi * x := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hx_def,
      Complex.ofReal_re, Complex.ofReal_im]
  set r : ℝ := Real.exp (-Real.pi * y) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have h_decomp : Real.pi * Complex.I * w =
      ((-Real.pi * y : ℝ) : ℂ) + ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
    have hw_decomp : w = (x : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hx_def]
      · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hy_def]
    rw [hw_decomp]
    push_cast
    have hI_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (Real.pi * y) * hI_sq
  have hq_re_eq : q.re = r * Real.cos (Real.pi * x) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * y) from hr_def]
    ring
  have hq_im_eq : q.im = r * Real.sin (Real.pi * x) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_im, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * y) from hr_def]
    ring
  have hQ2_eq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hQ3_eq : Q3 = q^3 := by
    rw [hQ3_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  set s : ℝ := Real.sin (Real.pi * x) with hs_def
  set c : ℝ := Real.cos (Real.pi * x) with hc_def
  have h_pyth : s^2 + c^2 = 1 := Real.sin_sq_add_cos_sq (Real.pi * x)
  have hQ2_re : Q2.re = r^2 * (c^2 - s^2) := by
    rw [hQ2_eq, sq, Complex.mul_re, hq_re_eq, hq_im_eq]; ring
  have hQ2_im : Q2.im = r^2 * (2 * c * s) := by
    rw [hQ2_eq, sq, Complex.mul_im, hq_re_eq, hq_im_eq]; ring
  have hQ3_re : Q3.re = r^3 * (c * (c^2 - 3 * s^2)) := by
    rw [hQ3_eq, show q^3 = q^2 * q from by ring, Complex.mul_re, ← hQ2_eq,
      hQ2_re, hQ2_im, hq_re_eq, hq_im_eq]
    ring
  -- Compute Im(πi(16q - 256 Q2 + 2112 Q3)) = π·(16 c r - 256 r²(c² - s²) + 2112 r³ c (c² - 3s²)).
  -- That is: π·(16 c r - 256(2c² - 1) r² + 2112 c(4c² - 3) r³) using s² + c² = 1.
  set L : ℂ := 16 * (Real.pi : ℂ) * Complex.I * q -
    256 * (Real.pi : ℂ) * Complex.I * Q2 +
    2112 * (Real.pi : ℂ) * Complex.I * Q3 with hL_def
  set E : ℂ := deriv modularLambdaH w - L with hE_def
  have hE_norm : ‖E‖ ≤ 100000 * Real.exp (-4 * Real.pi * y) := by
    have h_eq : E = deriv modularLambdaH w -
        16 * (Real.pi : ℂ) * Complex.I * q +
        256 * (Real.pi : ℂ) * Complex.I * Q2 -
        2112 * (Real.pi : ℂ) * Complex.I * Q3 := by
      rw [hE_def, hL_def]; ring
    rw [h_eq]; exact h_deriv_bound
  -- Im λ' = L.im + E.im.
  have h_split : (deriv modularLambdaH w).im = L.im + E.im := by
    have : deriv modularLambdaH w = L + E := by rw [hE_def]; ring
    rw [this, Complex.add_im]
  -- L.im = π · (16 c r - 256 r² (c²-s²) + 2112 r³ c (c²-3s²)).
  have hL_im : L.im = Real.pi * (16 * c * r - 256 * r^2 * (c^2 - s^2) +
      2112 * r^3 * (c * (c^2 - 3 * s^2))) := by
    -- L = π I (16 q - 256 Q2 + 2112 Q3). Im(π I · z) = π · Re(z).
    have hL_factor : L = (Real.pi : ℂ) * Complex.I *
        (16 * q - 256 * Q2 + 2112 * Q3) := by rw [hL_def]; ring
    rw [hL_factor]
    -- Now compute Im(π I · X) where X := 16 q - 256 Q2 + 2112 Q3.
    set X : ℂ := 16 * q - 256 * Q2 + 2112 * Q3 with hX_def
    have h_im : ((Real.pi : ℂ) * Complex.I * X).im = Real.pi * X.re := by
      rw [show ((Real.pi : ℂ) * Complex.I * X : ℂ) =
          ((Real.pi : ℝ) : ℂ) * (Complex.I * X) from by ring]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    rw [h_im]
    -- Now: X.re = 16 q.re - 256 Q2.re + 2112 Q3.re.
    have hX_re : X.re = 16 * (r * c) - 256 * (r^2 * (c^2 - s^2)) +
        2112 * (r^3 * (c * (c^2 - 3 * s^2))) := by
      simp only [hX_def, Complex.add_re, Complex.sub_re, Complex.mul_re,
        show (16 : ℂ).re = 16 from rfl, show (16 : ℂ).im = 0 from rfl,
        show (256 : ℂ).re = 256 from rfl, show (256 : ℂ).im = 0 from rfl,
        show (2112 : ℂ).re = 2112 from rfl, show (2112 : ℂ).im = 0 from rfl,
        zero_mul, sub_zero]
      rw [hq_re_eq, hQ2_re, hQ3_re]
    rw [hX_re]; ring
  -- Bounds on c: c ∈ [cos(π/8), 1] for x ∈ [0, 1/8].
  have h_piX_nn : 0 ≤ Real.pi * x := by
    have : 0 ≤ x := hw_re_nn
    positivity
  have h_piX_le : Real.pi * x ≤ Real.pi / 8 := by
    have hx_le : x ≤ 1 / 8 := hw_re_le
    have h_div : Real.pi / 8 = Real.pi * (1 / 8) := by ring
    rw [h_div]
    exact mul_le_mul_of_nonneg_left hx_le hπ_pos.le
  have h_piX_lt_half : Real.pi * x < Real.pi / 2 := by
    have : Real.pi / 8 < Real.pi / 2 := by linarith
    linarith
  have hc_ge_cπ8 : Real.cos (Real.pi / 8) ≤ c := by
    rw [hc_def]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h_piX_nn (by linarith) h_piX_le
  have hc_le_one : c ≤ 1 := by rw [hc_def]; exact Real.cos_le_one _
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h_piX_lt_half⟩
  -- cos(π/8) < 0.926, so c < 0.926. And cos(π/8) > 0.924 needed; we have > 0.38 via helper.
  -- For our bound: c ≥ 0.92 (need cos(π/8) ≥ 0.92).
  -- We have cos_pi_div_eight_lt_926 : cos(π/8) < 0.926. NOT a lower bound!
  -- We need cos(π/8) ≥ some value. Let me derive.
  -- cos(π/8) = √(2 + √2)/2. With √2 > 1.41: 2 + √2 > 3.41, so √(3.41) > 1.847, cos(π/8) > 0.923.
  have h_cπ8_gt_92 : (0.92 : ℝ) < Real.cos (Real.pi / 8) := by
    rw [Real.cos_pi_div_eight]
    -- √(2 + √2)/2 > 0.92 ⟺ √(2 + √2) > 1.84 ⟺ 2 + √2 > 1.84² = 3.3856.
    have h_184_sq : ((1.84 : ℝ))^2 = 3.3856 := by norm_num
    have h_sqrt2_gt : (1.41 : ℝ) < Real.sqrt 2 := sqrt_two_gt_141
    have h_inner_gt : ((1.84 : ℝ))^2 < 2 + Real.sqrt 2 := by
      rw [h_184_sq]; linarith
    have h_inner_nn : (0 : ℝ) ≤ (1.84 : ℝ)^2 := by positivity
    have h_step : Real.sqrt ((1.84 : ℝ)^2) < Real.sqrt (2 + Real.sqrt 2) :=
      Real.sqrt_lt_sqrt h_inner_nn h_inner_gt
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.84)] at h_step
    linarith
  have hc_gt_92 : (0.92 : ℝ) < c := lt_of_lt_of_le h_cπ8_gt_92 hc_ge_cπ8
  have hc_sq_ge : (0.8464 : ℝ) ≤ c^2 := by
    have h1 : (0.92 : ℝ)^2 ≤ c^2 := by
      apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.92)
      linarith
    have h2 : (0.92 : ℝ)^2 = 0.8464 := by norm_num
    linarith
  -- r ≤ exp(-π) < 1/22.
  have hr_le : r ≤ Real.exp (-Real.pi) := by
    rw [hr_def]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hr_lt_22 : r < 1 / 22 := by
    have h_exp_neg : Real.exp (-Real.pi) < 1 / 22 := by
      rw [Real.exp_neg]
      rw [show (Real.exp Real.pi)⁻¹ = 1 / Real.exp Real.pi from by rw [inv_eq_one_div]]
      exact one_div_lt_one_div_of_lt (by norm_num) exp_pi_gt_22
    linarith
  -- Use 2c² - 1 ≤ 1 (max) and 4c² - 3 ≥ 4·0.8464 - 3 = 0.3856 (min).
  have h_2c_sq_minus_1_le : 2 * c^2 - 1 ≤ 1 := by nlinarith [h_pyth, sq_nonneg c]
  have h_4c_sq_minus_3_ge : (0.3856 : ℝ) ≤ 4 * c^2 - 3 := by linarith [hc_sq_ge]
  have h_c2_minus_s2_eq : c^2 - s^2 = 2 * c^2 - 1 := by linarith [h_pyth]
  have h_c2_minus_3s2_eq : c^2 - 3 * s^2 = 4 * c^2 - 3 := by linarith [h_pyth]
  -- Bound the bracket: B := 16 c r - 256 r² (c²-s²) + 2112 r³ c (c²-3s²).
  -- B = 16 c r - 256 (2c²-1) r² + 2112 c (4c²-3) r³.
  -- ≥ 16·0.92·r - 256·1·r² + 2112·0.92·0.3856·r³ = 14.72 r - 256 r² + 749.4 r³.
  have h_bracket : 16 * c * r - 256 * r^2 * (c^2 - s^2) +
      2112 * r^3 * (c * (c^2 - 3 * s^2)) ≥
      14.72 * r - 256 * r^2 := by
    have hr_sq_pos : 0 < r^2 := by positivity
    have hr_cube_pos : 0 < r^3 := by positivity
    -- 16 c r ≥ 16 · 0.92 · r = 14.72 r.
    have h_t1 : 14.72 * r ≤ 16 * c * r := by
      have : 14.72 * r ≤ 16 * c * r := by
        have h_step : 14.72 ≤ 16 * c := by linarith
        nlinarith [hr_pos]
      exact this
    -- -256 r² (c² - s²) ≥ -256 r² (since c² - s² ≤ 1).
    have h_t2 : -(256 * r^2 * (c^2 - s^2)) ≥ -(256 * r^2) := by
      rw [h_c2_minus_s2_eq]
      have h_step : 256 * r^2 * (2 * c^2 - 1) ≤ 256 * r^2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
    -- 2112 r³ c (c² - 3s²) ≥ 2112 r³ · 0.92 · 0.3856 = 749.4 r³ ≥ 0.
    have h_t3 : 0 ≤ 2112 * r^3 * (c * (c^2 - 3 * s^2)) := by
      rw [h_c2_minus_3s2_eq]
      have h_c_nn : 0 < c := hc_pos
      have h_4c_sq_minus_3_pos : 0 < 4 * c^2 - 3 := by linarith
      positivity
    linarith
  -- For r ≤ 1/22: 14.72 r - 256 r² ≥ 14.72 r - 256 r/22 = (14.72 - 256/22) r ≈ 3.09 r.
  have h_bracket_lb : 14.72 * r - 256 * r^2 ≥ 3 * r := by
    have h_r_sq_le : 256 * r^2 ≤ 256 * r / 22 := by
      have : 256 * r^2 = 256 * r * r := by ring
      have h_step : 256 * r * r ≤ 256 * r * (1/22) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hr_lt_22)
        positivity
      have h_eq : 256 * r * (1/22 : ℝ) = 256 * r / 22 := by ring
      linarith
    have h_step2 : 256 * r / 22 ≤ 11.64 * r := by
      have h_div : (256 : ℝ) / 22 ≤ 11.64 := by norm_num
      have : 256 * r / 22 = (256/22) * r := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h_div (le_of_lt hr_pos)
    linarith
  -- Combine: L.im = π · bracket ≥ π · 3r.
  have h_L_im_lb : L.im ≥ 3 * Real.pi * r := by
    rw [hL_im]
    have h_step1 : 16 * c * r - 256 * r^2 * (c^2 - s^2) +
        2112 * r^3 * (c * (c^2 - 3 * s^2)) ≥ 3 * r := by
      linarith
    have h_step2 : Real.pi * (16 * c * r - 256 * r^2 * (c^2 - s^2) +
        2112 * r^3 * (c * (c^2 - 3 * s^2))) ≥ Real.pi * (3 * r) :=
      mul_le_mul_of_nonneg_left h_step1 hπ_pos.le
    have h_eq : Real.pi * (3 * r) = 3 * Real.pi * r := by ring
    linarith
  -- Error: |E.im| ≤ ‖E‖ ≤ 100000 · exp(-4π y).
  have hr4_eq : r^4 = Real.exp (-4 * Real.pi * y) := by
    have h_cast : (-4 * Real.pi * y : ℝ) = ((4 : ℕ) : ℝ) * (-Real.pi * y) := by
      push_cast; ring
    rw [hr_def, h_cast]
    exact (Real.exp_nat_mul _ _).symm
  have hE_im_abs : |E.im| ≤ 100000 * r^4 := by
    rw [hr4_eq]
    exact le_trans (Complex.abs_im_le_norm _) hE_norm
  have hE_im_lb : E.im ≥ -(100000 * r^4) := neg_le_of_abs_le hE_im_abs
  -- Im λ' ≥ L.im + E.im ≥ 3π r - 100000 r^4. Need ≥ 0.
  -- 3π r - 100000 r^4 = r · (3π - 100000 r^3). Inner ≥ 3π - 100000/10648 ≈ 9.42 - 6.16 > 0.
  rw [h_split]
  have h_r3_le : r^3 ≤ (1/22 : ℝ)^3 :=
    pow_le_pow_left₀ (le_of_lt hr_pos) (le_of_lt hr_lt_22) 3
  have h_22_cube : ((1/22 : ℝ))^3 = 1/10648 := by norm_num
  have h_K_r3_le : 100000 * r^3 ≤ 100000 * ((1/22 : ℝ)^3) :=
    mul_le_mul_of_nonneg_left h_r3_le (by norm_num)
  -- 100000 · (1/22)^3 = 100000/10648 ≈ 9.391 < 9.4 < 9.42 < 3π (since π > 3.14).
  have h_K_22_le : 100000 * ((1/22 : ℝ)^3) < 9.4 := by
    rw [h_22_cube]; norm_num
  have h_inner_nn : 0 ≤ 3 * Real.pi - 100000 * r^3 := by
    have h_lt94 : 100000 * r^3 < 9.4 := lt_of_le_of_lt h_K_r3_le h_K_22_le
    have h_3pi_gt_94 : (9.4 : ℝ) < 3 * Real.pi := by
      have h_pi_gt_d2 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      linarith
    linarith
  have h_main : 3 * Real.pi * r - 100000 * r^4 ≥ 0 := by
    have h_factor : 3 * Real.pi * r - 100000 * r^4 = r * (3 * Real.pi - 100000 * r^3) := by
      ring
    rw [h_factor]
    exact mul_nonneg (le_of_lt hr_pos) h_inner_nn
  linarith

/-- **Strip left edge: `Im λ ≥ 0` on `{Re ∈ (0, 1/8), Im ≥ 1}`.**

The proof linearizes `λ` along horizontal lines `{t + i · y : t ∈ [0, x]}`
using the fundamental theorem of calculus:
`λ(x + iy) − λ(iy) = ∫_0^x λ'(t + iy) dt`.
Since `λ(iy)` is real (`modularLambdaH_pure_imag_real`), taking imaginary
parts gives
`Im λ(x + iy) = ∫_0^x Im(λ'(t + iy)) dt`.
The integrand is nonneg by
`modularLambdaH_deriv_im_nonneg_on_left_edge`, so the integral is nonneg. -/
theorem modularLambdaH_im_nonneg_strip_left_edge (w : ℂ)
    (hw_re_pos : 0 < w.re) (hw_re_lt : w.re < 1 / 8) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  set x := w.re with hx_def
  set y := w.im with hy_def
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le one_pos hw_im_ge
  have hx_pos : 0 < x := hw_re_pos
  have hx_lt : x < 1 / 8 := hw_re_lt
  -- Rewrite w = ↑x + ↑y * I.
  have hw_eq : w = (↑x : ℂ) + (↑y : ℂ) * Complex.I := by
    rw [hx_def, hy_def, Complex.re_add_im]
  -- Define the curve f(t) := λ(↑t + ↑y · I).
  -- Show f has derivative `deriv λ (↑t + ↑y · I)` at each t ∈ uIcc 0 x.
  have hf_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun s : ℝ => modularLambdaH ((↑s : ℂ) + (↑y : ℂ) * Complex.I))
        (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)) t := by
    intro t ht
    -- (↑t + ↑y · I).im = y > 0, so λ is differentiable there.
    have h_im_pos : 0 < ((↑t : ℂ) + (↑y : ℂ) * Complex.I).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
      exact hy_pos
    have h_lam_diff : DifferentiableAt ℂ modularLambdaH
        ((↑t : ℂ) + (↑y : ℂ) * Complex.I) := by
      apply (modularLambdaH_differentiableOn _ h_im_pos).differentiableAt
      exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds h_im_pos
    have h_lam_hda : HasDerivAt modularLambdaH
        (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
        ((↑t : ℂ) + (↑y : ℂ) * Complex.I) := h_lam_diff.hasDerivAt
    -- Inner: HasDerivAt (fun s => ↑s + ↑y * I) 1 t.
    have h_inner : HasDerivAt (fun s : ℝ => (↑s : ℂ) + (↑y : ℂ) * Complex.I) 1 t := by
      have := Complex.ofRealCLM.hasDerivAt (x := t)
      simpa using this.add_const ((↑y : ℂ) * Complex.I)
    -- Chain rule via scomp (explicit IsScalarTower).
    have hst : IsScalarTower ℝ ℂ ℂ := IsScalarTower.right
    have h_chain := @HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ hst _ _ _ _ h_lam_hda h_inner
    simpa using h_chain
  -- Continuity of the integrand on uIcc.
  have h_int_cont : ContinuousOn
      (fun t : ℝ => deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
      (Set.uIcc 0 x) := by
    have h_inner_cont :
        ContinuousOn (fun t : ℝ => ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
          (Set.uIcc 0 x) :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have h_inner_maps :
        Set.MapsTo (fun t : ℝ => ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
          (Set.uIcc 0 x) { z : ℂ | 0 < z.im } := by
      intro t _
      simp only [Set.mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
      exact hy_pos
    have h_deriv_cont :
        ContinuousOn (deriv modularLambdaH) { z : ℂ | 0 < z.im } := by
      have h_diff_on : DifferentiableOn ℂ modularLambdaH { z : ℂ | 0 < z.im } :=
        modularLambdaH_differentiableOn
      exact (h_diff_on.analyticOnNhd
        (isOpen_lt continuous_const Complex.continuous_im)).deriv.continuousOn
    exact h_deriv_cont.comp h_inner_cont h_inner_maps
  have h_int_integrable : IntervalIntegrable
      (fun t : ℝ => deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
      MeasureTheory.volume 0 x :=
    h_int_cont.intervalIntegrable
  -- FTC.
  have h_ftc :
      ∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I) =
      modularLambdaH ((↑x : ℂ) + (↑y : ℂ) * Complex.I) -
        modularLambdaH ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf_deriv h_int_integrable
  -- λ(iy) is real (Im = 0).
  have h_lam_iy_im : (modularLambdaH ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I)).im = 0 := by
    have h_iy_eq : ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I) = Complex.I * (↑y : ℂ) := by
      push_cast; ring
    rw [h_iy_eq]
    exact modularLambdaH_pure_imag_real hy_pos
  -- Express Im λ(w) via the integral.
  have h_lam_w_im_eq : (modularLambdaH w).im =
      (∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im := by
    have h_ftc_im : (modularLambdaH ((↑x : ℂ) + (↑y : ℂ) * Complex.I)).im -
        (modularLambdaH ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I)).im =
        (∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im := by
      rw [← Complex.sub_im, ← h_ftc]
    have h_w_eq_im : (modularLambdaH w).im =
        (modularLambdaH ((↑x : ℂ) + (↑y : ℂ) * Complex.I)).im := by
      rw [← hw_eq]
    rw [h_w_eq_im, ← h_ftc_im, h_lam_iy_im, sub_zero]
  -- Commute Im with the integral.
  have h_im_commute :
      (∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im =
      ∫ t in (0 : ℝ)..x,
        (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im :=
    (Complex.imCLM.intervalIntegral_comp_comm h_int_integrable).symm
  -- Integrand ≥ 0 by helper.
  have h_integrand_nonneg : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      0 ≤ (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im := by
    intro t ht
    apply modularLambdaH_deriv_im_nonneg_on_left_edge
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      rcases (Set.mem_uIcc.mp ht) with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith [hx_pos]
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      rcases (Set.mem_uIcc.mp ht) with ⟨_, h2⟩ | ⟨_, h2⟩
      · linarith
      · linarith [hx_lt]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
      exact hw_im_ge
  -- Integral of nonneg function is nonneg.
  rw [h_lam_w_im_eq, h_im_commute]
  -- Use intervalIntegral.integral_nonneg.
  have hx_le : (0 : ℝ) ≤ x := le_of_lt hx_pos
  apply intervalIntegral.integral_nonneg hx_le
  intro t ht
  apply h_integrand_nonneg
  rcases ht with ⟨h1, h2⟩
  exact Set.mem_uIcc.mpr (Or.inl ⟨h1, h2⟩)

/-- **Strip right edge: `Im λ ≥ 0` on `{Re ∈ (7/8, 1), Im ≥ 1}`.**

Reduces to the left edge via the T-shift identity
`λ(τ + 1) = λ(τ)/(λ(τ) − 1)` and the conjugation symmetry
`λ(−conj τ) = conj(λ τ)`.
Concretely: for `w` with `w.re ∈ (7/8, 1)`, define
`w_left := (1 − w.re) + i·w.im`, which has `Re w_left ∈ (0, 1/8)` and
`Im w_left = w.im ≥ 1`. The chain
`λ(w_left) = λ(−conj(w − 1)) = conj(λ(w − 1))`
combined with the T-shift `λ(w) = λ(w − 1)/(λ(w − 1) − 1)` gives
`λ(w) = conj(λ w_left)/(conj(λ w_left) − 1)`.
A direct computation yields
`Im λ(w) = (Im λ(w_left)) / |λ(w_left) − 1|²`,
which is nonneg since `Im λ(w_left) ≥ 0` (left edge) and
`λ(w_left) ≠ 1` on `ℍ`. -/
theorem modularLambdaH_im_nonneg_strip_right_edge (w : ℂ)
    (hw_re_gt : 7 / 8 < w.re) (hw_re_lt : w.re < 1) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  -- Build w_left := (1 - w.re) + i · w.im.
  set w_left : ℂ := ⟨1 - w.re, w.im⟩ with hw_left_def
  have hw_left_re : w_left.re = 1 - w.re := rfl
  have hw_left_im : w_left.im = w.im := rfl
  have hw_left_re_pos : 0 < w_left.re := by rw [hw_left_re]; linarith
  have hw_left_re_lt : w_left.re < 1 / 8 := by rw [hw_left_re]; linarith
  have hw_left_im_ge : 1 ≤ w_left.im := by rw [hw_left_im]; exact hw_im_ge
  have hw_left_im_pos : 0 < w_left.im := lt_of_lt_of_le one_pos hw_left_im_ge
  -- Apply left edge.
  have h_left_im : 0 ≤ (modularLambdaH w_left).im :=
    modularLambdaH_im_nonneg_strip_left_edge w_left hw_left_re_pos hw_left_re_lt
      hw_left_im_ge
  -- σ := w - 1, with Im σ = w.im ≥ 1 > 0.
  have hσ_im_pos : 0 < (w - 1).im := by
    rw [Complex.sub_im, Complex.one_im, sub_zero]; linarith
  -- Show -conj(w - 1) = w_left.
  have h_neg_conj_eq : -(starRingEnd ℂ (w - 1)) = w_left := by
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.conj_re, Complex.sub_re, Complex.one_re,
        hw_left_re]
      ring
    · simp only [Complex.neg_im, Complex.conj_im, Complex.sub_im, Complex.one_im,
        sub_zero, neg_neg, hw_left_im]
  -- Conjugation symmetry: λ(-conj(w-1)) = conj(λ(w-1)).
  have h_conj_sym :
      modularLambdaH (-(starRingEnd ℂ (w - 1))) =
        starRingEnd ℂ (modularLambdaH (w - 1)) :=
    modularLambdaH_conj_symmetry hσ_im_pos
  -- So λ(w_left) = conj(λ(w-1)), hence λ(w-1) = conj(λ(w_left)).
  rw [h_neg_conj_eq] at h_conj_sym
  have h_lam_w_sub_1 :
      modularLambdaH (w - 1) = starRingEnd ℂ (modularLambdaH w_left) := by
    have h := congrArg (starRingEnd ℂ) h_conj_sym
    rw [Complex.conj_conj] at h
    exact h.symm
  -- T-shift: λ(w) = λ((w-1) + 1) = λ(w-1)/(λ(w-1) - 1).
  have h_w_eq : w = (w - 1) + 1 := by ring
  have h_lam_w :
      modularLambdaH w = modularLambdaH (w - 1) / (modularLambdaH (w - 1) - 1) := by
    conv_lhs => rw [h_w_eq]
    exact modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
  -- Substitute to get λ(w) in terms of conj(λ(w_left)).
  rw [h_lam_w, h_lam_w_sub_1]
  set α := modularLambdaH w_left with hα_def
  -- α - 1 ≠ 0 (since λ ≠ 1 on ℍ).
  have hα_minus_one_ne : α - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hw_left_im_pos)
  -- Im(conj α / (conj α - 1)) = α.im / |α - 1|²: use conj-div, then div_im.
  have h_conj_div :
      starRingEnd ℂ α / (starRingEnd ℂ α - 1) =
        starRingEnd ℂ (α / (α - 1)) := by
    rw [map_div₀, map_sub, map_one]
  rw [h_conj_div]
  -- Goal: 0 ≤ (conj(α/(α-1))).im. Im(conj z) = -Im z.
  rw [Complex.conj_im]
  -- Goal: 0 ≤ -(α/(α-1)).im.
  rw [neg_nonneg]
  -- Compute (α/(α - 1)).im ≤ 0 using `Complex.div_im` and `← sub_div`.
  rw [Complex.div_im]
  have h_normSq_pos : 0 < Complex.normSq (α - 1) :=
    Complex.normSq_pos.mpr hα_minus_one_ne
  -- Simplify (α - 1).re and (α - 1).im.
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  -- Combine the two division terms.
  rw [← sub_div]
  -- Numerator algebraic identity.
  have h_num_eq : α.im * (α.re - 1) - α.re * α.im = -α.im := by ring
  rw [h_num_eq]
  -- Goal: -α.im / Complex.normSq (α - 1) ≤ 0.
  rw [neg_div, neg_nonpos]
  exact div_nonneg h_left_im h_normSq_pos.le

/-- **Strip claim for `λ`: `Im λ ≥ 0` on `{Re ∈ (0, 1), Im ≥ 1}`.**

The strip `{w ∈ ℂ : 0 < w.re < 1, 1 ≤ w.im}` is contained in `F^o`
(the F^o constraint `‖2w − 1‖ > 1` is automatic for `Im w ≥ 1` since
`‖2w − 1‖² = (2 Re w − 1)² + (2 Im w)² ≥ 0 + 4 > 1`), so this is a
sub-region of Step A. The closure is independent of
`modularLambdaH_im_nonneg_on_F` to avoid the cyclic dependency
strip → F^o → cusp-1 → strip.

The proof is a case split on `Re w`:
* `Re w ∈ [1/8, 7/8]`: three-term q-expansion bound
  (`modularLambdaH_im_nonneg_strip_interior_band`).
* `Re w ∈ (0, 1/8)`: linearization at `Re w = 0`
  (`modularLambdaH_im_nonneg_strip_left_edge`).
* `Re w ∈ (7/8, 1)`: reduction to the left edge via T-shift +
  conjugation symmetry (`modularLambdaH_im_nonneg_strip_right_edge`). -/
theorem modularLambdaH_im_nonneg_strip (w : ℂ) (hw_re_pos : 0 < w.re)
    (hw_re_lt : w.re < 1) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  rcases lt_or_ge w.re ((1 : ℝ) / 8) with h1 | h1
  · exact modularLambdaH_im_nonneg_strip_left_edge w hw_re_pos h1 hw_im_ge
  · rcases le_or_gt w.re ((7 : ℝ) / 8) with h2 | h2
    · exact modularLambdaH_im_nonneg_strip_interior_band w h1 h2 hw_im_ge
    · exact modularLambdaH_im_nonneg_strip_right_edge w h2 hw_re_lt hw_im_ge

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

**Reduction to the strip claim.** The combined T-shift and S-shift
give the algebraic identity `λ(τ) = 1 − 1/λ(w)` where `w := −1/(τ−1)`.
Hence `Im λ(τ) = Im λ(w)/|λ(w)|²`, so `Im λ(τ) ≥ 0 ⟺ Im λ(w) ≥ 0`.

For `τ ∈ F^o ∩ B(1, 1/3)`, the image `w = −1/(τ−1)` satisfies
`Re w ∈ (0, 1)` (F^o constraint) and `Im w > 2√2 > 1` (from
`‖w‖ ≥ 3` and `Re²w + Im²w = ‖w‖² ≥ 9` with `Re w < 1`). The cusp-1
lemma thus reduces to the strip claim
`modularLambdaH_im_nonneg_strip`. -/
theorem modularLambdaH_cusp_one_im_nonneg_nbhd_in_F :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Gamma2FundamentalDomainInterior,
      ‖τ - 1‖ ≤ δ → 0 ≤ (modularLambdaH τ).im := by
  refine ⟨1/3, by norm_num, ?_⟩
  intro τ hτ_F hτ_dist
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  -- Step 1: σ := τ - 1 has σ.im > 0 and ‖σ‖ ≤ 1/3.
  set σ := τ - 1 with hσ_def
  have hσ_im_pos : 0 < σ.im := by
    change 0 < (τ - 1).im
    simp only [Complex.sub_im, Complex.one_im, sub_zero]; exact hτ_im_pos
  have hσ_re_neg : σ.re < 0 := by
    change (τ - 1).re < 0
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hσ_re_gt_neg_one : -1 < σ.re := by
    change -1 < (τ - 1).re
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hσ_norm_le : ‖σ‖ ≤ 1/3 := hτ_dist
  -- σ ≠ 0 since σ.im > 0.
  have hσ_ne : σ ≠ 0 := by
    intro h
    rw [h] at hσ_im_pos
    simp at hσ_im_pos
  have hσ_norm_pos : 0 < ‖σ‖ := norm_pos_iff.mpr hσ_ne
  -- |σ|² = ‖σ‖² ≤ 1/9.
  have hσ_normSq_eq : Complex.normSq σ = ‖σ‖^2 := by
    rw [← Complex.sq_norm]
  have hσ_normSq_pos : 0 < Complex.normSq σ := Complex.normSq_pos.mpr hσ_ne
  have hσ_normSq_le : Complex.normSq σ ≤ 1/9 := by
    rw [hσ_normSq_eq]
    have h_sq : ‖σ‖^2 ≤ (1/3)^2 := by
      apply sq_le_sq' _ hσ_norm_le
      · linarith [norm_nonneg σ]
    nlinarith
  -- F^o constraint translates to |σ|² > -σ.re.
  have hτ_semicircle_norm : 1 < Complex.normSq (2 * τ - 1) := by
    have h := hτ_semicircle
    have h_sq : 1 < ‖2 * τ - 1‖^2 := by
      have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
      nlinarith
    have h_eq : ‖2 * τ - 1‖^2 = Complex.normSq (2 * τ - 1) := Complex.sq_norm _
    linarith [h_eq ▸ h_sq]
  have h_2tau_minus_one : (2 * τ - 1) = 2 * σ + 1 := by
    rw [hσ_def]; ring
  rw [h_2tau_minus_one] at hτ_semicircle_norm
  have hσ_F_constraint : -σ.re < Complex.normSq σ := by
    have h_eq : Complex.normSq (2 * σ + 1) = 4 * Complex.normSq σ + 4 * σ.re + 1 := by
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.one_re, Complex.one_im]
      ring
    rw [h_eq] at hτ_semicircle_norm
    linarith
  -- Step 2: Set w := -1/σ. Show w.im > 1, 0 < w.re < 1.
  set w := -1/σ with hw_def
  have hw_eq_neg_inv : w = -σ⁻¹ := by
    rw [hw_def, neg_div, one_div]
  have hw_re : w.re = -σ.re / Complex.normSq σ := by
    rw [hw_eq_neg_inv, Complex.neg_re, Complex.inv_re]
    ring
  have hw_im : w.im = σ.im / Complex.normSq σ := by
    rw [hw_eq_neg_inv, Complex.neg_im, Complex.inv_im]
    ring
  have hw_re_pos : 0 < w.re := by
    rw [hw_re]
    apply div_pos _ hσ_normSq_pos
    linarith
  have hw_re_lt_one : w.re < 1 := by
    rw [hw_re]
    rw [div_lt_one hσ_normSq_pos]
    linarith
  have hw_im_pos : 0 < w.im := by
    rw [hw_im]
    exact div_pos hσ_im_pos hσ_normSq_pos
  -- Im w ≥ 1: from |w|² ≥ 9 and Re w < 1.
  have hw_normSq_eq : Complex.normSq w = 1 / Complex.normSq σ := by
    have h1 : ‖w‖^2 = Complex.normSq w := Complex.sq_norm _
    have h2 : ‖σ‖^2 = Complex.normSq σ := Complex.sq_norm _
    have h3 : ‖w‖ = ‖σ‖⁻¹ := by
      rw [hw_eq_neg_inv, norm_neg, norm_inv]
    rw [← h1, h3]
    rw [inv_pow, h2]
    rw [one_div]
  have hw_normSq_ge : 9 ≤ Complex.normSq w := by
    rw [hw_normSq_eq]
    rw [le_div_iff₀ hσ_normSq_pos]
    nlinarith
  have hw_im_sq_ge : 1 ≤ w.im^2 := by
    have h_normSq_eq : Complex.normSq w = w.re^2 + w.im^2 := by
      simp [Complex.normSq_apply]; ring
    have h_re_sq_lt : w.re^2 < 1 := by
      have h := hw_re_lt_one
      have h_pos := hw_re_pos
      nlinarith
    have h_sum : w.re^2 + w.im^2 ≥ 9 := h_normSq_eq ▸ hw_normSq_ge
    linarith
  have hw_im_ge : 1 ≤ w.im := by
    have h_sq : (1:ℝ)^2 ≤ w.im^2 := by simpa using hw_im_sq_ge
    nlinarith [hw_im_pos]
  -- Step 3: λ ≠ 0 at w.
  have hw_im_pos' : 0 < w.im := hw_im_pos
  have hlamw_ne_zero : modularLambdaH w ≠ 0 := modularLambdaH_ne_zero hw_im_pos'
  -- Step 4: Identity λ(τ) = 1 - 1/λ(w).
  -- From T-shift: λ(σ + 1) = -(θ₂(σ)⁴/θ₄(σ)⁴) = λ(σ)/(λ(σ) - 1).
  -- From S-shift: λ(σ) + λ(w) = 1, so λ(σ) = 1 - λ(w).
  -- Combine: λ(τ) = (1 - λ(w))/((1 - λ(w)) - 1) = (1 - λ(w))/(-λ(w)) = 1 - 1/λ(w).
  have hσ_im_for_S : 0 < σ.im := hσ_im_pos
  have h_S : modularLambdaH σ + modularLambdaH w = 1 := by
    have := modularLambdaH_add_S_smul_eq_one hσ_im_for_S
    rw [hw_def]
    exact this
  have hlamσ_eq : modularLambdaH σ = 1 - modularLambdaH w := by linear_combination h_S
  -- T-shift: σ + 1 = τ.
  have hστ_eq : σ + 1 = τ := by rw [hσ_def]; ring
  have hlam_Tshift : modularLambdaH τ = -(theta2 σ ^ 4 / theta4 σ ^ 4) := by
    rw [← hστ_eq]
    exact modularLambdaH_T_smul σ
  have hθ_ne : theta3 σ ≠ 0 := theta3_ne_zero hσ_im_for_S
  have hθ4_ne : theta4 σ ≠ 0 := theta4_ne_zero hσ_im_for_S
  have h_jacobi : theta2 σ ^ 4 + theta4 σ ^ 4 = theta3 σ ^ 4 := jacobi_identity hσ_im_for_S
  have hlamσ_minus_one_ne : modularLambdaH σ - 1 ≠ 0 := by
    have hlamσ_ne_one : modularLambdaH σ ≠ 1 := modularLambdaH_ne_one hσ_im_for_S
    exact sub_ne_zero.mpr hlamσ_ne_one
  have hlam_via_lamσ : modularLambdaH τ = modularLambdaH σ / (modularLambdaH σ - 1) := by
    rw [hlam_Tshift]
    unfold modularLambdaH
    have hθ4_pow_ne : theta4 σ ^ 4 ≠ 0 := pow_ne_zero 4 hθ4_ne
    have hθ3_pow_ne : theta3 σ ^ 4 ≠ 0 := pow_ne_zero 4 hθ_ne
    -- (θ₂⁴/θ₃⁴) / (θ₂⁴/θ₃⁴ - 1) = (θ₂⁴/θ₃⁴) · θ₃⁴/(θ₂⁴ - θ₃⁴) = θ₂⁴/(θ₂⁴ - θ₃⁴)
    -- = θ₂⁴/(-θ₄⁴) = -θ₂⁴/θ₄⁴.
    have h_step : theta2 σ ^ 4 / theta3 σ ^ 4 / (theta2 σ ^ 4 / theta3 σ ^ 4 - 1) =
        theta2 σ ^ 4 / (theta2 σ ^ 4 - theta3 σ ^ 4) := by
      rw [div_sub_one hθ3_pow_ne, div_div_div_cancel_right₀]
      exact hθ3_pow_ne
    rw [h_step]
    have h_denom : theta2 σ ^ 4 - theta3 σ ^ 4 = -theta4 σ ^ 4 := by linear_combination h_jacobi
    rw [h_denom, div_neg]
  -- Substitute λ(σ) = 1 - λ(w).
  have hlamτ_via_lamw : modularLambdaH τ = (1 - modularLambdaH w) / (-modularLambdaH w) := by
    rw [hlam_via_lamσ, hlamσ_eq]
    have h_denom : (1 - modularLambdaH w) - 1 = -modularLambdaH w := by ring
    rw [h_denom]
  -- Simplify: λ(τ) = 1 - 1/λ(w).
  have hlamτ_simplified : modularLambdaH τ = 1 - 1 / modularLambdaH w := by
    rw [hlamτ_via_lamw]
    field_simp
    ring
  -- Step 5: Apply strip claim to get Im λ(w) ≥ 0.
  have h_strip : 0 ≤ (modularLambdaH w).im :=
    modularLambdaH_im_nonneg_strip w hw_re_pos hw_re_lt_one hw_im_ge
  -- Step 6: Conclude Im λ(τ) = Im λ(w)/|λ(w)|² ≥ 0.
  rw [hlamτ_simplified]
  -- Goal: 0 ≤ (1 - 1/modularLambdaH w).im.
  simp only [Complex.sub_im, Complex.one_im, zero_sub, neg_nonneg]
  -- Goal: (1/modularLambdaH w).im ≤ 0.
  -- 1/z = z̄/|z|², so Im(1/z) = -Im(z)/|z|².
  have hlamw_normSq_pos : 0 < Complex.normSq (modularLambdaH w) :=
    Complex.normSq_pos.mpr hlamw_ne_zero
  rw [show (1 : ℂ) / modularLambdaH w = (modularLambdaH w)⁻¹ from by rw [one_div]]
  rw [Complex.inv_im]
  -- Goal: -(modularLambdaH w).im / |λ(w)|² ≤ 0.
  rw [neg_div]
  rw [neg_nonpos]
  exact div_nonneg h_strip hlamw_normSq_pos.le

/-- **Cusp 0 nbhd in `F^o`.** Mirror of `modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`
under the S-shift + conjugation symmetry. For `τ ∈ F^o ∩ B(0, 1/3)`,
set `w := -1/τ`. The S-shift identity `λ(τ) + λ(w) = 1` gives
`Im λ(τ) = -Im λ(w)`. Apply conjugation symmetry
`λ(-conj w) = conj(λ w)` with `w' := -conj w`: then
`Im λ(w') = -Im λ(w)`, so `Im λ(τ) = Im λ(w')`. The `F^o`-translation
on `τ` (equivalently `‖2τ - 1‖ > 1`, equivalently `Re²τ + Im²τ > Re τ`)
gives `Re w' = Re τ / |τ|² < 1`. Combined with `|w'|² = 1/|τ|² ≥ 9`
(from `‖τ‖ ≤ 1/3`) and `Im w' > 0`, this gives `Im w' ≥ 2√2 > 1`,
placing `w'` in the strip `{0 < Re < 1, Im ≥ 1}` where the strip claim
applies. -/
theorem modularLambdaH_cusp_zero_im_nonneg_nbhd_in_F :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Gamma2FundamentalDomainInterior,
      ‖τ‖ ≤ δ → 0 ≤ (modularLambdaH τ).im := by
  refine ⟨1/3, by norm_num, ?_⟩
  intro τ hτ_F hτ_dist
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  -- τ ≠ 0.
  have hτ_ne : τ ≠ 0 := by
    intro h
    rw [h] at hτ_im_pos
    simp at hτ_im_pos
  have hτ_norm_pos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ_ne
  have hτ_normSq_eq : Complex.normSq τ = ‖τ‖^2 := by rw [← Complex.sq_norm]
  have hτ_normSq_pos : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ_ne
  have hτ_normSq_le : Complex.normSq τ ≤ 1/9 := by
    rw [hτ_normSq_eq]
    have h_sq : ‖τ‖^2 ≤ (1/3)^2 := by
      apply sq_le_sq' _ hτ_dist
      · linarith [norm_nonneg τ]
    nlinarith
  -- F^o constraint: ‖2τ - 1‖ > 1 ⟹ Re τ < |τ|².
  have hτ_F_constraint : τ.re < Complex.normSq τ := by
    have h_sq : 1 < ‖2 * τ - 1‖^2 := by
      have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
      nlinarith
    have h_normSq_eq : ‖2 * τ - 1‖^2 = Complex.normSq (2 * τ - 1) := Complex.sq_norm _
    have h_expand : Complex.normSq (2 * τ - 1) = 4 * Complex.normSq τ - 4 * τ.re + 1 := by
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.one_re, Complex.one_im]
      ring
    have h_lt : 1 < 4 * Complex.normSq τ - 4 * τ.re + 1 := by
      rw [← h_expand, ← h_normSq_eq]; exact h_sq
    linarith
  -- Set w := -1/τ.
  set w : ℂ := -1 / τ with hw_def
  have hw_eq_neg_inv : w = -τ⁻¹ := by rw [hw_def, neg_div, one_div]
  have hw_re : w.re = -τ.re / Complex.normSq τ := by
    rw [hw_eq_neg_inv, Complex.neg_re, Complex.inv_re]; ring
  have hw_im : w.im = τ.im / Complex.normSq τ := by
    rw [hw_eq_neg_inv, Complex.neg_im, Complex.inv_im]; ring
  have hw_im_pos : 0 < w.im := by
    rw [hw_im]; exact div_pos hτ_im_pos hτ_normSq_pos
  -- Set w' := -conj w (Schwarz reflection through Re = 0).
  set w' : ℂ := -(starRingEnd ℂ w) with hw'_def
  have hw'_re : w'.re = -w.re := by
    rw [hw'_def, Complex.neg_re, Complex.conj_re]
  have hw'_im : w'.im = w.im := by
    rw [hw'_def, Complex.neg_im, Complex.conj_im]; ring
  have hw'_re_pos : 0 < w'.re := by
    rw [hw'_re, hw_re, neg_div, neg_neg]
    exact div_pos hτ_re_pos hτ_normSq_pos
  have hw'_re_lt_one : w'.re < 1 := by
    rw [hw'_re, hw_re, neg_div, neg_neg]
    rw [div_lt_one hτ_normSq_pos]
    exact hτ_F_constraint
  have hw'_im_pos : 0 < w'.im := by rw [hw'_im]; exact hw_im_pos
  -- |w'|² = |w|² = 1/|τ|² ≥ 9.
  have hw_normSq_eq : Complex.normSq w = 1 / Complex.normSq τ := by
    have h1 : ‖w‖^2 = Complex.normSq w := Complex.sq_norm _
    have h2 : ‖τ‖^2 = Complex.normSq τ := Complex.sq_norm _
    have h3 : ‖w‖ = ‖τ‖⁻¹ := by rw [hw_eq_neg_inv, norm_neg, norm_inv]
    rw [← h1, h3, inv_pow, h2, one_div]
  have hw'_normSq_eq : Complex.normSq w' = Complex.normSq w := by
    rw [hw'_def, Complex.normSq_neg, Complex.normSq_conj]
  have hw'_normSq_ge : 9 ≤ Complex.normSq w' := by
    rw [hw'_normSq_eq, hw_normSq_eq]
    rw [le_div_iff₀ hτ_normSq_pos]
    nlinarith
  -- Im w' ≥ 1 from |w'|² ≥ 9 and Re w' < 1.
  have hw'_im_sq_ge : 1 ≤ w'.im^2 := by
    have h_normSq_eq : Complex.normSq w' = w'.re^2 + w'.im^2 := by
      simp [Complex.normSq_apply]; ring
    have h_re_sq_lt : w'.re^2 < 1 := by
      have h := hw'_re_lt_one
      have h_pos := hw'_re_pos
      nlinarith
    have h_sum : w'.re^2 + w'.im^2 ≥ 9 := h_normSq_eq ▸ hw'_normSq_ge
    linarith
  have hw'_im_ge : 1 ≤ w'.im := by
    have h_sq : (1:ℝ)^2 ≤ w'.im^2 := by simpa using hw'_im_sq_ge
    nlinarith [hw'_im_pos]
  -- S-shift: λ(τ) + λ(w) = 1.
  have h_S : modularLambdaH τ + modularLambdaH w = 1 := by
    have := modularLambdaH_add_S_smul_eq_one hτ_im_pos
    rw [hw_def]; exact this
  have hlamτ_eq : modularLambdaH τ = 1 - modularLambdaH w := by linear_combination h_S
  -- Conjugation symmetry: λ(w') = conj(λ(w)).
  have h_conj : modularLambdaH w' = starRingEnd ℂ (modularLambdaH w) := by
    rw [hw'_def]; exact modularLambdaH_conj_symmetry hw_im_pos
  -- Apply strip lemma to w'.
  have h_strip : 0 ≤ (modularLambdaH w').im :=
    modularLambdaH_im_nonneg_strip w' hw'_re_pos hw'_re_lt_one hw'_im_ge
  -- Im λ(w') = -Im λ(w), so Im λ(w) ≤ 0.
  have hlamw_im_eq : (modularLambdaH w').im = -(modularLambdaH w).im := by
    rw [h_conj, Complex.conj_im]
  have hlamw_im_le : (modularLambdaH w).im ≤ 0 := by linarith [hlamw_im_eq ▸ h_strip]
  -- Conclude Im λ(τ) = -Im λ(w) ≥ 0.
  rw [hlamτ_eq, Complex.sub_im, Complex.one_im, zero_sub]
  linarith

/-- **Sub-lemma for Step A (Phragmén–Lindelöf statement): `Im(λ) ≥ 0`
on `F^o`.**

`Im λ` is harmonic on `F^o`, vanishes on the three boundary arcs
(`modularLambdaH_pure_imag_real`, `modularLambdaH_one_add_imag_real`,
`modularLambdaH_semicircle_real`), and tends to `0` at the cusps
`i∞` and `0`. The four sub-regions of F^o tile it as:

* `F^o ∩ {Im τ ≥ 1}`: strip lemma `modularLambdaH_im_nonneg_strip`.
* `F^o ∩ B(0, 1/3)`: cusp-0 nbhd
  `modularLambdaH_cusp_zero_im_nonneg_nbhd_in_F`.
* `F^o ∩ B(1, 1/3)`: cusp-1 nbhd
  `modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`.
* "Middle region" `F^o ∩ {Im τ < 1, ‖τ‖ > 1/3, ‖τ - 1‖ > 1/3}`:
  bounded, with all frontier conditions giving `Im λ ≥ 0` (the F^o
  boundary arcs being real, the upper edge handled by the strip lemma,
  and the cusp-truncation arcs by the cusp nbhd lemmas). Apply the
  maximum modulus principle to `g(z) := exp(i·λ(z))` (whose norm is
  `exp(-Im λ z)`) on this bounded open set to conclude `‖g‖ ≤ 1`,
  i.e. `Im λ ≥ 0`. -/
theorem modularLambdaH_im_nonneg_on_F :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, 0 ≤ (modularLambdaH τ).im := by
  obtain ⟨δ₀, hδ₀_pos, h_cusp0⟩ := modularLambdaH_cusp_zero_im_nonneg_nbhd_in_F
  obtain ⟨δ₁, hδ₁_pos, h_cusp1⟩ := modularLambdaH_cusp_one_im_nonneg_nbhd_in_F
  intro τ hτ_F
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  by_cases h_im_case : 1 ≤ τ.im
  · exact modularLambdaH_im_nonneg_strip τ hτ_re_pos hτ_re_lt_one h_im_case
  push Not at h_im_case
  by_cases h_c0_case : ‖τ‖ ≤ δ₀
  · exact h_cusp0 τ ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ h_c0_case
  push Not at h_c0_case
  by_cases h_c1_case : ‖τ - 1‖ ≤ δ₁
  · exact h_cusp1 τ ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ h_c1_case
  push Not at h_c1_case
  -- Middle region: apply maximum modulus to g(z) := exp(i·λ(z)).
  set M : Set ℂ := { z : ℂ | 0 < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 < ‖2 * z - 1‖ ∧
    z.im < 1 ∧ δ₀ < ‖z‖ ∧ δ₁ < ‖z - 1‖ } with hM_def
  have hτ_in_M : τ ∈ M :=
    ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle, h_im_case, h_c0_case, h_c1_case⟩
  set g : ℂ → ℂ := fun z => Complex.exp (Complex.I * modularLambdaH z) with hg_def
  have h_g_norm : ∀ z : ℂ, ‖g z‖ = Real.exp (-(modularLambdaH z).im) := by
    intro z
    rw [hg_def, Complex.norm_exp]
    congr 1
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  have h2zm1_cont : Continuous (fun z : ℂ => 2 * z - 1) :=
    (continuous_const.mul continuous_id).sub continuous_const
  have hzm1_cont : Continuous (fun z : ℂ => z - 1) :=
    continuous_id.sub continuous_const
  have hM_open : IsOpen M := by
    refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    refine (isOpen_lt continuous_const Complex.continuous_re).inter ?_
    refine (isOpen_lt Complex.continuous_re continuous_const).inter ?_
    refine (isOpen_lt continuous_const h2zm1_cont.norm).inter ?_
    refine (isOpen_lt Complex.continuous_im continuous_const).inter ?_
    refine (isOpen_lt continuous_const continuous_norm).inter ?_
    exact isOpen_lt continuous_const hzm1_cont.norm
  have hM_bdd : Bornology.IsBounded M := by
    refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := (0 : ℂ)) (r := 2)) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    obtain ⟨h_im_pos, h_re_pos, h_re_lt, _, h_im_lt, _, _⟩ := hz
    have h_sq : ‖z‖ ^ 2 < 4 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith
    nlinarith [norm_nonneg z, sq_nonneg (2 - ‖z‖)]
  have h_im_nn_cl : closure M ⊆ { z : ℂ | 0 ≤ z.im } :=
    closure_minimal (fun z hz => le_of_lt hz.1)
      (isClosed_le continuous_const Complex.continuous_im)
  have h_re_nn_cl : closure M ⊆ { z : ℂ | 0 ≤ z.re } :=
    closure_minimal (fun z hz => le_of_lt hz.2.1)
      (isClosed_le continuous_const Complex.continuous_re)
  have h_re_le_cl : closure M ⊆ { z : ℂ | z.re ≤ 1 } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.1)
      (isClosed_le Complex.continuous_re continuous_const)
  have h_sc_cl : closure M ⊆ { z : ℂ | 1 ≤ ‖2 * z - 1‖ } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.1)
      (isClosed_le continuous_const h2zm1_cont.norm)
  have h_im_le_cl : closure M ⊆ { z : ℂ | z.im ≤ 1 } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.2.1)
      (isClosed_le Complex.continuous_im continuous_const)
  have h_n_ge_cl : closure M ⊆ { z : ℂ | δ₀ ≤ ‖z‖ } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.2.2.1)
      (isClosed_le continuous_const continuous_norm)
  have h_n1_ge_cl : closure M ⊆ { z : ℂ | δ₁ ≤ ‖z - 1‖ } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.2.2.2)
      (isClosed_le continuous_const hzm1_cont.norm)
  have hM_cl_in_H : ∀ z ∈ closure M, 0 < z.im := by
    intro z hz_cl
    by_contra h_neg
    push Not at h_neg
    have h_im_z_nn : 0 ≤ z.im := h_im_nn_cl hz_cl
    have h_im_zero : z.im = 0 := le_antisymm h_neg h_im_z_nn
    have h_sc : 1 ≤ ‖2 * z - 1‖ := h_sc_cl hz_cl
    have h_sc_sq : 1 ≤ ‖2 * z - 1‖ ^ 2 := by
      have h_nn : 0 ≤ ‖2 * z - 1‖ := norm_nonneg _
      nlinarith
    have h_2zm1_sq : ‖2 * z - 1‖ ^ 2 = (2 * z.re - 1) ^ 2 + (2 * z.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [h_2zm1_sq, h_im_zero] at h_sc_sq
    have h_re_sq : 1 ≤ (2 * z.re - 1) ^ 2 := by linarith
    have h_re_nn : 0 ≤ z.re := h_re_nn_cl hz_cl
    have h_re_le : z.re ≤ 1 := h_re_le_cl hz_cl
    have h_re_outside : z.re ≤ 0 ∨ 1 ≤ z.re := by
      rcases le_or_gt (2 * z.re - 1) 0 with h | h
      · left; nlinarith [sq_nonneg (2 * z.re - 1)]
      · right; nlinarith [sq_nonneg (2 * z.re - 1)]
    rcases h_re_outside with h_re_le_0 | h_re_ge_1
    · have h_re_zero : z.re = 0 := le_antisymm h_re_le_0 h_re_nn
      have h_n_ge : δ₀ ≤ ‖z‖ := h_n_ge_cl hz_cl
      have h_norm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [h_re_zero, h_im_zero] at h_norm_sq
      have h_norm_sq_zero : ‖z‖ ^ 2 = 0 := by linarith
      have h_nn : 0 ≤ ‖z‖ := norm_nonneg z
      have h_norm_zero : ‖z‖ = 0 := by nlinarith
      linarith
    · have h_re_one : z.re = 1 := le_antisymm h_re_le h_re_ge_1
      have h_n1_ge : δ₁ ≤ ‖z - 1‖ := h_n1_ge_cl hz_cl
      have h_zm1_sq : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
        ring
      rw [h_re_one, h_im_zero] at h_zm1_sq
      have h_zm1_sq_zero : ‖z - 1‖ ^ 2 = 0 := by linarith
      have h_nn : 0 ≤ ‖z - 1‖ := norm_nonneg _
      have h_zm1_zero : ‖z - 1‖ = 0 := by nlinarith
      linarith
  have hg_diff_at : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z := by
    intro z h_im_pos
    have h_lam_diff : DifferentiableAt ℂ modularLambdaH z :=
      modularLambdaH_differentiableAt_of_im_pos h_im_pos
    have h_mul : DifferentiableAt ℂ (fun w => Complex.I * modularLambdaH w) z :=
      (differentiableAt_const _).mul h_lam_diff
    exact h_mul.cexp
  have hg_DCOC : DiffContOnCl ℂ g M := by
    refine ⟨?_, ?_⟩
    · intro z hz_M
      exact (hg_diff_at z hz_M.1).differentiableWithinAt
    · intro z hz_cl
      exact (hg_diff_at z (hM_cl_in_H z hz_cl)).continuousAt.continuousWithinAt
  have hg_frontier_bound : ∀ z ∈ frontier M, ‖g z‖ ≤ 1 := by
    intro z hz_fr
    have hz_cl : z ∈ closure M := hz_fr.1
    have h_im_pos : 0 < z.im := hM_cl_in_H z hz_cl
    have h_re_nn : 0 ≤ z.re := h_re_nn_cl hz_cl
    have h_re_le : z.re ≤ 1 := h_re_le_cl hz_cl
    have h_sc_ge : 1 ≤ ‖2 * z - 1‖ := h_sc_cl hz_cl
    have h_im_le : z.im ≤ 1 := h_im_le_cl hz_cl
    have hz_not_M : z ∉ M := by
      rw [← hM_open.interior_eq]; exact hz_fr.2
    rw [h_g_norm z]
    suffices h_im_lam : 0 ≤ (modularLambdaH z).im by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_le_exp]
      linarith
    by_cases h_re_z : z.re ≤ 0
    · have h_re_z_eq : z.re = 0 := le_antisymm h_re_z h_re_nn
      have h_z_eq : z = Complex.I * ((z.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, h_re_z_eq]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im]
      rw [h_z_eq]
      exact le_of_eq (modularLambdaH_pure_imag_real h_im_pos).symm
    push Not at h_re_z
    by_cases h_re_z_1 : 1 ≤ z.re
    · have h_re_z_eq : z.re = 1 := le_antisymm h_re_le h_re_z_1
      have h_z_eq : z = 1 + Complex.I * ((z.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, h_re_z_eq]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [h_z_eq]
      exact le_of_eq (modularLambdaH_one_add_imag_real h_im_pos).symm
    push Not at h_re_z_1
    by_cases h_sc_eq : ‖2 * z - 1‖ ≤ 1
    · have h_sc_eq' : ‖2 * z - 1‖ = 1 := le_antisymm h_sc_eq h_sc_ge
      exact le_of_eq (modularLambdaH_semicircle_real h_im_pos h_sc_eq').symm
    push Not at h_sc_eq
    have hz_in_F : z ∈ Gamma2FundamentalDomainInterior :=
      ⟨h_im_pos, h_re_z, h_re_z_1, h_sc_eq⟩
    by_cases h_im_z_1 : 1 ≤ z.im
    · exact modularLambdaH_im_nonneg_strip z h_re_z h_re_z_1 h_im_z_1
    push Not at h_im_z_1
    by_cases h_norm_z : ‖z‖ ≤ δ₀
    · exact h_cusp0 z hz_in_F h_norm_z
    push Not at h_norm_z
    by_cases h_norm_z_1 : ‖z - 1‖ ≤ δ₁
    · exact h_cusp1 z hz_in_F h_norm_z_1
    push Not at h_norm_z_1
    exfalso
    exact hz_not_M ⟨h_im_pos, h_re_z, h_re_z_1, h_sc_eq, h_im_z_1, h_norm_z, h_norm_z_1⟩
  have hg_τ_bound : ‖g τ‖ ≤ 1 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hM_bdd hg_DCOC hg_frontier_bound
      (subset_closure hτ_in_M)
  rw [h_g_norm τ] at hg_τ_bound
  have h_le : -(modularLambdaH τ).im ≤ 0 := by
    rwa [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_le_exp] at hg_τ_bound
  linarith

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
leaving only the "limit in `F^o`" case, which gives `w ∈ λ(F^o)`. -/
theorem modularLambdaH_F_image_isClosed_in_upperHalf :
    IsClosed (((↑) : { w : ℂ // 0 < w.im } → ℂ) ⁻¹'
      (modularLambdaH '' Gamma2FundamentalDomainInterior)) := by
  refine IsSeqClosed.isClosed ?_
  intro xn x_target hxn_in hxn_tendsto
  -- Choose τₙ ∈ F^o with λ(τₙ) = (xn n).val.
  have h_exists : ∀ n, ∃ τ, τ ∈ Gamma2FundamentalDomainInterior ∧
      modularLambdaH τ = (xn n).val := fun n => hxn_in n
  choose τ hτ_pair using h_exists
  have hτF : ∀ n, τ n ∈ Gamma2FundamentalDomainInterior := fun n => (hτ_pair n).1
  have hτlam : ∀ n, modularLambdaH (τ n) = (xn n).val := fun n => (hτ_pair n).2
  -- λ(τₙ) → x_target.val in ℂ.
  have h_xn_C : Filter.Tendsto (fun n => (xn n).val) Filter.atTop (nhds x_target.val) :=
    (continuous_subtype_val.tendsto _).comp hxn_tendsto
  have h_lamτ_C : Filter.Tendsto (fun n => modularLambdaH (τ n)) Filter.atTop
      (nhds x_target.val) := by
    have h_eq : (fun n => modularLambdaH (τ n)) = (fun n => (xn n).val) := funext hτlam
    rw [h_eq]; exact h_xn_C
  have h_x_im_pos : 0 < x_target.val.im := x_target.property
  have h_x_norm_pos : 0 < ‖x_target.val‖ := by
    calc 0 < x_target.val.im := h_x_im_pos
      _ ≤ |x_target.val.im| := le_abs_self _
      _ ≤ ‖x_target.val‖ := Complex.abs_im_le_norm _
  -- ‖λ(τₙ)‖ → ‖x_target.val‖.
  have h_norm_lamτ : Filter.Tendsto (fun n => ‖modularLambdaH (τ n)‖) Filter.atTop
      (nhds ‖x_target.val‖) :=
    (continuous_norm.tendsto _).comp h_lamτ_C
  -- Pick Y so that for Im τ ≥ Y, ‖λ τ‖ ≤ ‖x_target.val‖/2.
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  set Y : ℝ := max 1 (Real.log (320000 / ‖x_target.val‖) / Real.pi) with hY_def
  have hY_ge_one : 1 ≤ Y := le_max_left _ _
  have hY_log_le : Real.log (320000 / ‖x_target.val‖) / Real.pi ≤ Y := le_max_right _ _
  have h_quot_pos : 0 < 320000 / ‖x_target.val‖ := by positivity
  have h_exp_Y : 320000 / ‖x_target.val‖ ≤ Real.exp (Real.pi * Y) := by
    have h_step : Real.log (320000 / ‖x_target.val‖) ≤ Real.pi * Y := by
      rw [div_le_iff₀ hπ_pos] at hY_log_le; linarith
    have := Real.exp_le_exp.mpr h_step
    rwa [Real.exp_log h_quot_pos] at this
  -- For Im τ ≥ Y: 160000 * exp(-π·Im τ) ≤ ‖x_target.val‖/2.
  have h_bound_at_Y : 160000 * Real.exp (-Real.pi * Y) ≤ ‖x_target.val‖ / 2 := by
    rw [show -Real.pi * Y = -(Real.pi * Y) from by ring, Real.exp_neg]
    have h_exp_pos : 0 < Real.exp (Real.pi * Y) := Real.exp_pos _
    have h_320 : 320000 ≤ Real.exp (Real.pi * Y) * ‖x_target.val‖ := by
      have h := h_exp_Y
      rw [div_le_iff₀ h_x_norm_pos] at h
      linarith
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show (160000 * (Real.exp (Real.pi * Y))⁻¹ * 2 : ℝ) =
      320000 / Real.exp (Real.pi * Y) from by field_simp; ring]
    rw [div_le_iff₀ h_exp_pos]
    linarith
  -- Eventually ‖λ τₙ‖ > ‖x_target.val‖ / 2.
  have h_eventually_large : ∀ᶠ n in Filter.atTop, ‖x_target.val‖ / 2 < ‖modularLambdaH (τ n)‖ := by
    have h_half_lt : ‖x_target.val‖ / 2 < ‖x_target.val‖ := by linarith
    exact h_norm_lamτ.eventually_const_lt h_half_lt
  -- Define K (eventually contains τₙ).
  set K : Set ℂ := { z : ℂ | 0 ≤ z.im ∧ z.im ≤ Y ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ ‖2 * z - 1‖ }
    with hK_def
  -- Continuity helpers.
  have h2zm1_cont : Continuous (fun z : ℂ => 2 * z - 1) :=
    (continuous_const.mul continuous_id).sub continuous_const
  -- K is closed.
  have hK_closed : IsClosed K := by
    refine (isClosed_le continuous_const Complex.continuous_im).inter ?_
    refine (isClosed_le Complex.continuous_im continuous_const).inter ?_
    refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
    refine (isClosed_le Complex.continuous_re continuous_const).inter ?_
    exact isClosed_le continuous_const h2zm1_cont.norm
  -- K is bounded.
  have hK_bdd : Bornology.IsBounded K := by
    refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := (0 : ℂ)) (r := Y + 2)) ?_
    intro z hz
    obtain ⟨h_im_nn, h_im_le, h_re_nn, h_re_le, _⟩ := hz
    rw [Metric.mem_ball, dist_zero_right]
    have h_sq : ‖z‖^2 < (Y + 2)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hY_ge_one]
    nlinarith [norm_nonneg z, sq_nonneg (Y + 2 - ‖z‖)]
  -- K is compact.
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
  -- Eventually τₙ ∈ K.
  have h_eventually_in_K : ∀ᶠ n in Filter.atTop, τ n ∈ K := by
    filter_upwards [h_eventually_large] with n hn_large
    obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτF n
    refine ⟨hτ_im_pos.le, ?_, hτ_re_pos.le, hτ_re_lt_one.le, hτ_semicircle.le⟩
    -- Im τₙ ≤ Y. Otherwise ‖λ τₙ‖ ≤ 160000 exp(-π Im τₙ) ≤ 160000 exp(-π Y) ≤ ‖x‖/2.
    by_contra h_im_gt
    push Not at h_im_gt
    have h_im_ge_Y : Y ≤ (τ n).im := h_im_gt.le
    have h_im_ge_one : 1 ≤ (τ n).im := le_trans hY_ge_one h_im_ge_Y
    have h_bound : ‖modularLambdaH (τ n)‖ ≤ 160000 * Real.exp (-Real.pi * (τ n).im) :=
      modularLambdaH_norm_le_exp_of_im_ge_one h_im_ge_one
    have h_exp_le : Real.exp (-Real.pi * (τ n).im) ≤ Real.exp (-Real.pi * Y) := by
      apply Real.exp_le_exp.mpr
      have h_pi_Y_le : Real.pi * Y ≤ Real.pi * (τ n).im :=
        mul_le_mul_of_nonneg_left h_im_ge_Y hπ_pos.le
      linarith
    have h_chain : ‖modularLambdaH (τ n)‖ ≤ ‖x_target.val‖ / 2 := by
      calc ‖modularLambdaH (τ n)‖
          ≤ 160000 * Real.exp (-Real.pi * (τ n).im) := h_bound
        _ ≤ 160000 * Real.exp (-Real.pi * Y) :=
            mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
        _ ≤ ‖x_target.val‖ / 2 := h_bound_at_Y
    linarith
  -- Extract n₀ such that τₙ ∈ K for n ≥ n₀.
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp h_eventually_in_K
  -- Shifted sequence τ' n := τ (n + n₀).
  set τ' : ℕ → ℂ := fun n => τ (n + n₀) with hτ'_def
  have hτ'_in_K : ∀ n, τ' n ∈ K := fun n => hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  -- Bolzano-Weierstrass on K.
  obtain ⟨τStar, hτStar_in_K, φ, hφ_mono, hφ_tendsto⟩ :=
    hK_compact.tendsto_subseq hτ'_in_K
  -- τStar ∈ K. λ ∘ τ' ∘ φ → x_target.val.
  have h_lamτ'_tendsto : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
      (nhds x_target.val) := by
    have h_lamτ' : Filter.Tendsto (fun n => modularLambdaH (τ' n)) Filter.atTop
        (nhds x_target.val) := by
      have h_shift : (fun n => modularLambdaH (τ' n)) =
          (fun n => modularLambdaH (τ n)) ∘ (fun n => n + n₀) := by
        funext n; rfl
      rw [h_shift]
      exact h_lamτ_C.comp (Filter.tendsto_add_atTop_nat n₀)
    exact h_lamτ'.comp hφ_mono.tendsto_atTop
  -- Extract closure constraints on τStar.
  obtain ⟨hτs_im_nn, hτs_im_le_Y, hτs_re_nn, hτs_re_le, hτs_sc⟩ := hτStar_in_K
  -- Case split on τStar.
  by_cases h_τs_im_pos : 0 < τStar.im
  · -- τStar.im > 0: cases on which boundary condition (Re, semicircle) is active.
    by_cases h_re_zero : τStar.re ≤ 0
    · -- Re τStar = 0. λ(τStar) is real. Contradicts x_target.val.im > 0.
      exfalso
      have h_re_eq : τStar.re = 0 := le_antisymm h_re_zero hτs_re_nn
      have h_z_eq : τStar = Complex.I * ((τStar.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, h_re_eq]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im]
      have h_lamτs_real : (modularLambdaH τStar).im = 0 := by
        rw [h_z_eq]; exact modularLambdaH_pure_imag_real h_τs_im_pos
      -- λ(τ'_{φ n}) → λ(τStar) by continuity.
      have h_τs_im_pos' : 0 < τStar.im := h_τs_im_pos
      have h_lam_cont : ContinuousAt modularLambdaH τStar :=
        (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos').continuousAt
      have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
      have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
        tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      have : x_target.val.im = 0 := by rw [← h_lamτs_eq]; exact h_lamτs_real
      linarith
    push Not at h_re_zero
    by_cases h_re_one : 1 ≤ τStar.re
    · -- Re τStar = 1. λ real. Contradiction.
      exfalso
      have h_re_eq : τStar.re = 1 := le_antisymm hτs_re_le h_re_one
      have h_z_eq : τStar = 1 + Complex.I * ((τStar.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, h_re_eq]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_lamτs_real : (modularLambdaH τStar).im = 0 := by
        rw [h_z_eq]; exact modularLambdaH_one_add_imag_real h_τs_im_pos
      have h_τs_im_pos' : 0 < τStar.im := h_τs_im_pos
      have h_lam_cont : ContinuousAt modularLambdaH τStar :=
        (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos').continuousAt
      have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
      have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
        tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      have : x_target.val.im = 0 := by rw [← h_lamτs_eq]; exact h_lamτs_real
      linarith
    push Not at h_re_one
    by_cases h_sc_eq : ‖2 * τStar - 1‖ ≤ 1
    · -- ‖2τStar - 1‖ = 1: semicircle. λ real. Contradiction.
      exfalso
      have h_sc_eq' : ‖2 * τStar - 1‖ = 1 := le_antisymm h_sc_eq hτs_sc
      have h_lamτs_real : (modularLambdaH τStar).im = 0 :=
        modularLambdaH_semicircle_real h_τs_im_pos h_sc_eq'
      have h_lam_cont : ContinuousAt modularLambdaH τStar :=
        (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos).continuousAt
      have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
      have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
        tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      have : x_target.val.im = 0 := by rw [← h_lamτs_eq]; exact h_lamτs_real
      linarith
    push Not at h_sc_eq
    -- τStar ∈ F^o.
    have hτStar_in_F : τStar ∈ Gamma2FundamentalDomainInterior :=
      ⟨h_τs_im_pos, h_re_zero, h_re_one, h_sc_eq⟩
    have h_lam_cont : ContinuousAt modularLambdaH τStar :=
      (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos).continuousAt
    have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
        (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
    have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
      tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
    -- x_target.val ∈ λ(F^o).
    exact ⟨τStar, hτStar_in_F, h_lamτs_eq⟩
  · -- τStar.im = 0. So τStar is on the real axis. K constraints force τStar = 0 or 1.
    push Not at h_τs_im_pos
    have h_τs_im_zero : τStar.im = 0 := le_antisymm h_τs_im_pos hτs_im_nn
    -- ‖2τStar - 1‖² ≥ 1 with Im τStar = 0 gives (2 Re τStar - 1)² ≥ 1.
    have h_sc_sq : 1 ≤ ‖2 * τStar - 1‖^2 := by
      have h_nn : 0 ≤ ‖2 * τStar - 1‖ := norm_nonneg _
      nlinarith [hτs_sc]
    have h_2zm1_sq : ‖2 * τStar - 1‖^2 = (2 * τStar.re - 1)^2 + (2 * τStar.im)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [h_2zm1_sq, h_τs_im_zero] at h_sc_sq
    have h_re_sq : 1 ≤ (2 * τStar.re - 1)^2 := by linarith
    have h_re_outside : τStar.re ≤ 0 ∨ 1 ≤ τStar.re := by
      rcases le_or_gt (2 * τStar.re - 1) 0 with h | h
      · left; nlinarith [sq_nonneg (2 * τStar.re - 1)]
      · right; nlinarith [sq_nonneg (2 * τStar.re - 1)]
    rcases h_re_outside with h_re_le_0 | h_re_ge_1
    · -- τStar = 0 (cusp 0).
      exfalso
      have h_re_zero : τStar.re = 0 := le_antisymm h_re_le_0 hτs_re_nn
      have h_τStar_eq_zero : τStar = 0 := by
        apply Complex.ext
        · simp [h_re_zero]
        · simp [h_τs_im_zero]
      -- τ' ∘ φ → 0 in F^o. So λ(τ' ∘ φ) → 1 by cusp-0 limit.
      have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (0 : ℂ)) := by
        rw [← h_τStar_eq_zero]; exact hφ_tendsto
      have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
        fun n => hτF (φ n + n₀)
      have hτ'φ_tendsto_in_F :
          Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
            (nhdsWithin (0 : ℂ) Gamma2FundamentalDomainInterior) := by
        rw [nhdsWithin, Filter.tendsto_inf]
        refine ⟨hτ'φ_tendsto, ?_⟩
        rw [Filter.tendsto_principal]
        exact Filter.Eventually.of_forall hτ'φ_in_F
      have h_cusp0 :
          Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop (nhds 1) :=
        modularLambdaH_cusp_zero_tendsto_one_in_F.comp hτ'φ_tendsto_in_F
      have h_x_eq_one : x_target.val = 1 := tendsto_nhds_unique h_lamτ'_tendsto h_cusp0
      have : x_target.val.im = 0 := by rw [h_x_eq_one]; rfl
      linarith
    · -- τStar = 1 (cusp 1).
      exfalso
      have h_re_one : τStar.re = 1 := le_antisymm hτs_re_le h_re_ge_1
      have h_τStar_eq_one : τStar = 1 := by
        apply Complex.ext
        · simp [h_re_one]
        · simp [h_τs_im_zero]
      have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (1 : ℂ)) := by
        rw [← h_τStar_eq_one]; exact hφ_tendsto
      have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
        fun n => hτF (φ n + n₀)
      have hτ'φ_tendsto_in_F :
          Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
            (nhdsWithin (1 : ℂ) Gamma2FundamentalDomainInterior) := by
        rw [nhdsWithin, Filter.tendsto_inf]
        refine ⟨hτ'φ_tendsto, ?_⟩
        rw [Filter.tendsto_principal]
        exact Filter.Eventually.of_forall hτ'φ_in_F
      have h_cusp1 :
          Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop Filter.atTop :=
        modularLambdaH_cusp_one_tendsto_norm_atTop_in_F.comp hτ'φ_tendsto_in_F
      have h_norm_lamτ'φ_tendsto :
          Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop
            (nhds ‖x_target.val‖) := (continuous_norm.tendsto _).comp h_lamτ'_tendsto
      -- Cannot tend to both atTop and to a finite value: pick conflicting witnesses.
      have h_at1 := h_cusp1
      rw [Filter.tendsto_atTop] at h_at1
      have h_at1_event := h_at1 (‖x_target.val‖ + 1)
      rw [Metric.tendsto_atTop] at h_norm_lamτ'φ_tendsto
      obtain ⟨N₂, hN₂⟩ := h_norm_lamτ'φ_tendsto 1 (by norm_num)
      obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_at1_event
      set N := max N₁ N₂
      have h_ge : ‖x_target.val‖ + 1 ≤ ‖modularLambdaH (τ' (φ N))‖ :=
        hN₁ N (le_max_left _ _)
      have h_close : dist (‖modularLambdaH (τ' (φ N))‖) (‖x_target.val‖) < 1 :=
        hN₂ N (le_max_right _ _)
      rw [Real.dist_eq] at h_close
      have h_lt : ‖modularLambdaH (τ' (φ N))‖ - ‖x_target.val‖ < 1 :=
        (abs_lt.mp h_close).2
      linarith

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

/-! ## Surjectivity of `λ` onto the triply-punctured plane -/

/-- **Surjectivity of `λ : ℍ → ℂ ∖ {0, 1}`.** The image of `λ` on `ℍ`
is exactly the triply-punctured plane.

The `⊆` direction is direct from `modularLambdaH_ne_zero` and
`modularLambdaH_ne_one`. The `⊇` direction reduces to Step D
`modularLambdaH_image_fundamentalDomainInterior`
(`λ(F^o) = {Im w > 0}`) plus the conjugation symmetry
`modularLambdaH_conj_symmetry` (which provides the Schwarz-reflection
across the imaginary axis covering `{Im w < 0}`), and a sequential
compactness extraction for `w ∈ ℝ ∖ {0, 1}` that lifts any
sequence `wₙ = w + i/n ∈ λ(F^o)` to `τₙ ∈ F^o`, then uses the cusp
asymptotics
`modularLambdaH_cusp_zero_tendsto_one_in_F`,
`modularLambdaH_cusp_one_tendsto_norm_atTop_in_F`, and
`modularLambdaH_norm_le_exp_of_im_ge_one` to rule out the three
cusps `{0, 1, ∞}` as accumulation points. -/
theorem modularLambdaH_image :
    modularLambdaH '' { τ : ℂ | 0 < τ.im } = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro w ⟨τ, hτ, rfl⟩
    exact ⟨modularLambdaH_ne_zero hτ, modularLambdaH_ne_one hτ⟩
  · rintro w ⟨hw0, hw1⟩
    by_cases h_im_neg : w.im < 0
    · -- `w.im < 0`: use conjugation symmetry `λ(-conj τ) = conj(λ τ)`.
      have hconj_im_pos : 0 < (starRingEnd ℂ w).im := by
        rw [Complex.conj_im]; linarith
      have hconj_in : starRingEnd ℂ w ∈ modularLambdaH '' Gamma2FundamentalDomainInterior := by
        rw [modularLambdaH_image_fundamentalDomainInterior]
        exact hconj_im_pos
      obtain ⟨τ', hτ'_in_F, hτ'_lambda⟩ := hconj_in
      have hτ'_im_pos : 0 < τ'.im :=
        Gamma2FundamentalDomainInterior_subset_upperHalf hτ'_in_F
      refine ⟨-(starRingEnd ℂ τ'), ?_, ?_⟩
      · change 0 < (-(starRingEnd ℂ τ')).im
        rw [Complex.neg_im, Complex.conj_im]; linarith
      · rw [modularLambdaH_conj_symmetry hτ'_im_pos, hτ'_lambda, Complex.conj_conj]
    · -- `w.im ≥ 0`: sequential compactness in F^o via Step D.
      have hw_im_nn : 0 ≤ w.im := not_lt.mp h_im_neg
      -- Sequence `wn = w + i / (n + 1)`, all in the open upper half-plane.
      set wn : ℕ → ℂ := fun n => w + Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ) with hwn_def
      have hwn_im : ∀ n, (wn n).im = w.im + 1 / (n + 1 : ℝ) := by
        intro n
        change (w + Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ)).im = w.im + 1 / (n + 1 : ℝ)
        rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hwn_im_pos : ∀ n, 0 < (wn n).im := by
        intro n
        rw [hwn_im n]
        have h_div_pos : 0 < (1 : ℝ) / (n + 1) := by positivity
        linarith
      -- `wn → w` in `ℂ`.
      have hwn_tendsto : Filter.Tendsto wn Filter.atTop (nhds w) := by
        have h_inner : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h_inner_C : Filter.Tendsto
            (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
          have h_zero : ((0 : ℝ) : ℂ) = (0 : ℂ) := Complex.ofReal_zero
          rw [← h_zero]
          exact (Complex.continuous_ofReal.tendsto _).comp h_inner
        have h_mul : Filter.Tendsto (fun n : ℕ => Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ))
            Filter.atTop (nhds (Complex.I * 0)) :=
          tendsto_const_nhds.mul h_inner_C
        rw [mul_zero] at h_mul
        have h_add : Filter.Tendsto (fun n : ℕ => w + Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ))
            Filter.atTop (nhds (w + 0)) := tendsto_const_nhds.add h_mul
        rw [add_zero] at h_add
        exact h_add
      -- Each `wn` lifts to `τn ∈ F^o` by Step D.
      have h_exists : ∀ n, ∃ τ ∈ Gamma2FundamentalDomainInterior,
          modularLambdaH τ = wn n := by
        intro n
        have h_in : wn n ∈ modularLambdaH '' Gamma2FundamentalDomainInterior := by
          rw [modularLambdaH_image_fundamentalDomainInterior]
          exact hwn_im_pos n
        obtain ⟨τ, hτ, hlamτ⟩ := h_in
        exact ⟨τ, hτ, hlamτ⟩
      choose τ hτF hτlam using h_exists
      -- `‖w‖ > 0` since `w ≠ 0`.
      have h_w_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      -- `λ(τn) → w` in `ℂ`.
      have h_lamτ_C : Filter.Tendsto (fun n => modularLambdaH (τ n)) Filter.atTop (nhds w) := by
        have h_eq : (fun n => modularLambdaH (τ n)) = wn := funext hτlam
        rw [h_eq]; exact hwn_tendsto
      have h_norm_lamτ : Filter.Tendsto (fun n => ‖modularLambdaH (τ n)‖) Filter.atTop
          (nhds ‖w‖) := (continuous_norm.tendsto _).comp h_lamτ_C
      -- Truncation `Y` of imaginary part via cusp-∞ bound.
      have hπ_pos : 0 < Real.pi := Real.pi_pos
      set Y : ℝ := max 1 (Real.log (320000 / ‖w‖) / Real.pi) with hY_def
      have hY_ge_one : 1 ≤ Y := le_max_left _ _
      have hY_log_le : Real.log (320000 / ‖w‖) / Real.pi ≤ Y := le_max_right _ _
      have h_quot_pos : 0 < 320000 / ‖w‖ := by positivity
      have h_exp_Y : 320000 / ‖w‖ ≤ Real.exp (Real.pi * Y) := by
        have h_step : Real.log (320000 / ‖w‖) ≤ Real.pi * Y := by
          rw [div_le_iff₀ hπ_pos] at hY_log_le; linarith
        have := Real.exp_le_exp.mpr h_step
        rwa [Real.exp_log h_quot_pos] at this
      have h_bound_at_Y : 160000 * Real.exp (-Real.pi * Y) ≤ ‖w‖ / 2 := by
        rw [show -Real.pi * Y = -(Real.pi * Y) from by ring, Real.exp_neg]
        have h_exp_pos : 0 < Real.exp (Real.pi * Y) := Real.exp_pos _
        have h_320 : 320000 ≤ Real.exp (Real.pi * Y) * ‖w‖ := by
          have h := h_exp_Y
          rw [div_le_iff₀ h_w_norm_pos] at h
          linarith
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        rw [show (160000 * (Real.exp (Real.pi * Y))⁻¹ * 2 : ℝ) =
          320000 / Real.exp (Real.pi * Y) from by field_simp; ring]
        rw [div_le_iff₀ h_exp_pos]
        linarith
      have h_eventually_large : ∀ᶠ n in Filter.atTop, ‖w‖ / 2 < ‖modularLambdaH (τ n)‖ := by
        have h_half_lt : ‖w‖ / 2 < ‖w‖ := by linarith
        exact h_norm_lamτ.eventually_const_lt h_half_lt
      -- Compact truncation `K` of `F^o`.
      set K : Set ℂ := { z : ℂ | 0 ≤ z.im ∧ z.im ≤ Y ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ ‖2 * z - 1‖ }
        with hK_def
      have h2zm1_cont : Continuous (fun z : ℂ => 2 * z - 1) :=
        (continuous_const.mul continuous_id).sub continuous_const
      have hK_closed : IsClosed K := by
        refine (isClosed_le continuous_const Complex.continuous_im).inter ?_
        refine (isClosed_le Complex.continuous_im continuous_const).inter ?_
        refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
        refine (isClosed_le Complex.continuous_re continuous_const).inter ?_
        exact isClosed_le continuous_const h2zm1_cont.norm
      have hK_bdd : Bornology.IsBounded K := by
        refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := (0 : ℂ)) (r := Y + 2)) ?_
        intro z hz
        obtain ⟨h_im_nn, h_im_le, h_re_nn, h_re_le, _⟩ := hz
        rw [Metric.mem_ball, dist_zero_right]
        have h_sq : ‖z‖^2 < (Y + 2)^2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          nlinarith [hY_ge_one]
        nlinarith [norm_nonneg z, sq_nonneg (Y + 2 - ‖z‖)]
      have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
      -- Eventually `τn ∈ K`.
      have h_eventually_in_K : ∀ᶠ n in Filter.atTop, τ n ∈ K := by
        filter_upwards [h_eventually_large] with n hn_large
        obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτF n
        refine ⟨hτ_im_pos.le, ?_, hτ_re_pos.le, hτ_re_lt_one.le, hτ_semicircle.le⟩
        by_contra h_im_gt
        have h_im_ge_Y : Y ≤ (τ n).im := (not_le.mp h_im_gt).le
        have h_im_ge_one : 1 ≤ (τ n).im := le_trans hY_ge_one h_im_ge_Y
        have h_bound : ‖modularLambdaH (τ n)‖ ≤ 160000 * Real.exp (-Real.pi * (τ n).im) :=
          modularLambdaH_norm_le_exp_of_im_ge_one h_im_ge_one
        have h_exp_le : Real.exp (-Real.pi * (τ n).im) ≤ Real.exp (-Real.pi * Y) := by
          apply Real.exp_le_exp.mpr
          have h_pi_Y_le : Real.pi * Y ≤ Real.pi * (τ n).im :=
            mul_le_mul_of_nonneg_left h_im_ge_Y hπ_pos.le
          linarith
        have h_chain : ‖modularLambdaH (τ n)‖ ≤ ‖w‖ / 2 := by
          calc ‖modularLambdaH (τ n)‖
              ≤ 160000 * Real.exp (-Real.pi * (τ n).im) := h_bound
            _ ≤ 160000 * Real.exp (-Real.pi * Y) :=
                mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
            _ ≤ ‖w‖ / 2 := h_bound_at_Y
        linarith
      obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp h_eventually_in_K
      set τ' : ℕ → ℂ := fun n => τ (n + n₀) with hτ'_def
      have hτ'_in_K : ∀ n, τ' n ∈ K := fun n => hn₀ (n + n₀) (Nat.le_add_left n₀ n)
      obtain ⟨τStar, hτStar_in_K, φ, hφ_mono, hφ_tendsto⟩ :=
        hK_compact.tendsto_subseq hτ'_in_K
      have h_lamτ'_tendsto : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds w) := by
        have h_lamτ' : Filter.Tendsto (fun n => modularLambdaH (τ' n)) Filter.atTop (nhds w) := by
          have h_shift : (fun n => modularLambdaH (τ' n)) =
              (fun n => modularLambdaH (τ n)) ∘ (fun n => n + n₀) := by
            funext n; rfl
          rw [h_shift]
          exact h_lamτ_C.comp (Filter.tendsto_add_atTop_nat n₀)
        exact h_lamτ'.comp hφ_mono.tendsto_atTop
      obtain ⟨hτs_im_nn, _hτs_im_le_Y, hτs_re_nn, hτs_re_le, hτs_sc⟩ := hτStar_in_K
      by_cases h_τs_im_pos : 0 < τStar.im
      · -- `τStar ∈ ℍ`. Continuity of `λ` gives `λ(τStar) = w`.
        refine ⟨τStar, h_τs_im_pos, ?_⟩
        have h_lam_cont : ContinuousAt modularLambdaH τStar :=
          (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos).continuousAt
        have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
            (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
        exact tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      · -- `τStar.im = 0`. Membership in `K` and `1 ≤ ‖2τ−1‖` forces τStar ∈ {0, 1};
        -- the cusp lemmas then contradict `w ≠ 0, w ≠ 1`.
        have h_τs_im_le : τStar.im ≤ 0 := not_lt.mp h_τs_im_pos
        have h_τs_im_zero : τStar.im = 0 := le_antisymm h_τs_im_le hτs_im_nn
        have h_sc_sq : 1 ≤ ‖2 * τStar - 1‖^2 := by
          have h_nn : 0 ≤ ‖2 * τStar - 1‖ := norm_nonneg _
          nlinarith [hτs_sc]
        have h_2zm1_sq : ‖2 * τStar - 1‖^2 = (2 * τStar.re - 1)^2 + (2 * τStar.im)^2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
            Complex.one_re, Complex.one_im]
          ring
        rw [h_2zm1_sq, h_τs_im_zero] at h_sc_sq
        have h_re_sq : 1 ≤ (2 * τStar.re - 1)^2 := by linarith
        have h_re_outside : τStar.re ≤ 0 ∨ 1 ≤ τStar.re := by
          rcases le_or_gt (2 * τStar.re - 1) 0 with h | h
          · left; nlinarith [sq_nonneg (2 * τStar.re - 1)]
          · right; nlinarith [sq_nonneg (2 * τStar.re - 1)]
        rcases h_re_outside with h_re_le_0 | h_re_ge_1
        · -- τStar = 0 (cusp 0). λ(τn) → 1 ⟹ w = 1 ⟹ contradiction.
          exfalso
          have h_re_zero : τStar.re = 0 := le_antisymm h_re_le_0 hτs_re_nn
          have h_τStar_eq_zero : τStar = 0 := by
            apply Complex.ext
            · simp [h_re_zero]
            · simp [h_τs_im_zero]
          have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (0 : ℂ)) := by
            rw [← h_τStar_eq_zero]; exact hφ_tendsto
          have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
            fun n => hτF (φ n + n₀)
          have hτ'φ_tendsto_in_F :
              Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
                (nhdsWithin (0 : ℂ) Gamma2FundamentalDomainInterior) := by
            rw [nhdsWithin, Filter.tendsto_inf]
            refine ⟨hτ'φ_tendsto, ?_⟩
            rw [Filter.tendsto_principal]
            exact Filter.Eventually.of_forall hτ'φ_in_F
          have h_cusp0 :
              Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop (nhds 1) :=
            modularLambdaH_cusp_zero_tendsto_one_in_F.comp hτ'φ_tendsto_in_F
          have h_w_eq_one : w = 1 := tendsto_nhds_unique h_lamτ'_tendsto h_cusp0
          exact hw1 h_w_eq_one
        · -- τStar = 1 (cusp 1). ‖λ(τn)‖ → ∞ while wn → w finite ⟹ contradiction.
          exfalso
          have h_re_one : τStar.re = 1 := le_antisymm hτs_re_le h_re_ge_1
          have h_τStar_eq_one : τStar = 1 := by
            apply Complex.ext
            · simp [h_re_one]
            · simp [h_τs_im_zero]
          have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (1 : ℂ)) := by
            rw [← h_τStar_eq_one]; exact hφ_tendsto
          have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
            fun n => hτF (φ n + n₀)
          have hτ'φ_tendsto_in_F :
              Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
                (nhdsWithin (1 : ℂ) Gamma2FundamentalDomainInterior) := by
            rw [nhdsWithin, Filter.tendsto_inf]
            refine ⟨hτ'φ_tendsto, ?_⟩
            rw [Filter.tendsto_principal]
            exact Filter.Eventually.of_forall hτ'φ_in_F
          have h_cusp1 :
              Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop Filter.atTop :=
            modularLambdaH_cusp_one_tendsto_norm_atTop_in_F.comp hτ'φ_tendsto_in_F
          have h_norm_lamτ'φ_tendsto :
              Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop
                (nhds ‖w‖) := (continuous_norm.tendsto _).comp h_lamτ'_tendsto
          rw [Filter.tendsto_atTop] at h_cusp1
          have h_at1_event := h_cusp1 (‖w‖ + 1)
          rw [Metric.tendsto_atTop] at h_norm_lamτ'φ_tendsto
          obtain ⟨N₂, hN₂⟩ := h_norm_lamτ'φ_tendsto 1 (by norm_num)
          obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_at1_event
          set N := max N₁ N₂
          have h_ge : ‖w‖ + 1 ≤ ‖modularLambdaH (τ' (φ N))‖ :=
            hN₁ N (le_max_left _ _)
          have h_close : dist (‖modularLambdaH (τ' (φ N))‖) ‖w‖ < 1 :=
            hN₂ N (le_max_right _ _)
          rw [Real.dist_eq] at h_close
          have h_lt : ‖modularLambdaH (τ' (φ N))‖ - ‖w‖ < 1 :=
            (abs_lt.mp h_close).2
          linarith

/-- The image of `modularLambda` on `𝔻` is exactly `ℂ ∖ {0, 1}`.
Combines `cayleyToHalfPlane_image_ball` (Cayley sends `𝔻` onto `ℍ`)
with `modularLambdaH_image` (surjectivity of `λ` onto the
triply-punctured plane). -/
theorem modularLambda_image :
    modularLambda '' Metric.ball (0 : ℂ) 1 = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  unfold modularLambda
  rw [show (fun z => modularLambdaH (cayleyToHalfPlane z))
        = modularLambdaH ∘ cayleyToHalfPlane from rfl,
      Set.image_comp, cayleyToHalfPlane_image_ball]
  exact modularLambdaH_image

end RiemannDynamics

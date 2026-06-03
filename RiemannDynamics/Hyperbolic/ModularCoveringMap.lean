/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.Gamma2FundamentalDomain

/-!
# Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`

The level-2 modular function `λ` is a holomorphic covering map of the
triply-punctured plane by the upper half-plane. The proof factors
through four classical statements:

* **Freeness mod `±I`** (`gamma_two_fixed_point_implies_pm_one`):
  any `γ ∈ Γ(2)` with a fixed point in `ℍ` is `±I`.
* **Proper discontinuity** (`gamma_two_properlyDiscontinuousSMul`):
  `Γ(2)` acts properly discontinuously on `ℍ`.
* **Non-vanishing derivative** (`modularLambdaH_deriv_ne_zero_on_upperHalf`):
  `λ' ≠ 0` on `ℍ`.
* **Orbit identification** (`modularLambdaH_eq_iff_gamma2_orbit`):
  `λ(τ₁) = λ(τ₂) ↔ ∃ γ ∈ Γ(2), γ • τ₁ = τ₂`.

The first two pillars depend only on the `SL₂(ℤ)`-action and live in
`Hyperbolic/ModularFunction.lean`. The last two pillars use the Step-D
biholomorphism `λ : F^o → {Im w > 0}`
(`modularLambdaH_image_fundamentalDomainInterior`) and the
"half-fundamental-domain" property of `F`, both established in
`Hyperbolic/Gamma2FundamentalDomain.lean`.

`F` has hyperbolic area `π` (an ideal triangle with vertices
`0, 1, ∞`), half the `Γ(2)`-covolume `2π`. So `F` is a *half*
fundamental domain: the upper-`λ`-image branch `λ : F^o → {Im w > 0}`
(Step D) is a biholomorphism, while the conjugation symmetry
`λ(-conj τ) = conj(λ τ)` produces the lower-`λ`-image branch on the
reflected half.

Pillars 3 and 4 consequently split into three cases each, separated
by the sign of `Im(λ τ)`. The `Im(λ) > 0` branch reduces to `F` via
the half-FD property. The `Im(λ) < 0` branch is handled by the
conjugation argument: for Pillar 4 by a direct matrix conjugation
turning `γ = ⟨⟨a, b⟩, ⟨c, d⟩⟩` into `γ' = ⟨⟨a, -b⟩, ⟨-c, d⟩⟩`, also
in `Γ(2)`. The `Im(λ) = 0` boundary branch reduces to the closed
boundary arcs of `F` and is handled by Schwarz reflection (still an
architectural sub-lemma).
-/

namespace RiemannDynamics

open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## Half-fundamental-domain infrastructure (sub-lemmas) -/

/-- The reflected half-fundamental domain `F^σ := { τ : -1 ≤ Re τ ≤ 0,
|2τ + 1| ≥ 1, Im τ > 0 }`. This is `-conj(F)`: the conjugation
`τ ↦ -conj τ` maps `F` (closed) to `F^σ` (closed) homeomorphically.
Together with `F`, `F^σ` tessellates a strict `Γ(2)`-fundamental
domain of `ℍ` with hyperbolic covolume `2π`. The image of `F^σ`
under `λ` is the closed lower half of `ℂ ∖ {0, 1}` (by
`modularLambdaH_conj_symmetry`). -/
def Gamma2FundamentalDomainReflected : Set ℂ :=
  { τ : ℂ | 0 < τ.im ∧ -1 ≤ τ.re ∧ τ.re ≤ 0 ∧ 1 ≤ ‖2 * τ + 1‖ }

/-- **Existence of a `Γ(2)`-translate in `F ∪ F^σ`.** For every
`τ ∈ ℍ`, there is `γ ∈ Γ(2)` such that `γ • τ` lies in either the
half-fundamental domain `F` or its reflection `F^σ`. This is the
classical strict fundamental-domain property of `Γ(2)`: the six
right cosets `SL(2, ℤ) / Γ(2) ≃ S₃` partition `SL(2, ℤ)`; combined
with the Mathlib reduction `ModularGroup.exists_smul_mem_fd`
(placing every orbit into the standard `SL(2, ℤ)` fundamental
domain `𝒟`), each of the six tiles `c⁻¹ · 𝒟` lies in `F ∪ F^σ`
(verifiable explicitly per coset rep). -/
theorem gamma2_translate_in_F_union_F_sigma (τ : UpperHalfPlane) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2,
      ((γ • τ : UpperHalfPlane) : ℂ) ∈
        Gamma2FundamentalDomain ∪ Gamma2FundamentalDomainReflected := by
  sorry

/-- **`Im λ ≥ 0` on the closed half-fundamental domain `F`.**
Combines `modularLambdaH_F_im_pos` (strict positivity on the open
interior `F^o`) with the three boundary-arc lemmas
`modularLambdaH_pure_imag_real` (left edge, `λ ∈ ℝ`),
`modularLambdaH_one_add_imag_real` (right edge), and
`modularLambdaH_semicircle_real` (semicircular bottom arc). -/
theorem modularLambdaH_im_nonneg_on_closed_F
    {τ : ℂ} (hτ_F : τ ∈ Gamma2FundamentalDomain) :
    0 ≤ (modularLambdaH τ).im := by
  obtain ⟨hτ_im_pos, hτ_re_nonneg, hτ_re_le_one, hτ_semicircle⟩ := hτ_F
  -- Case split on left/right edges and semicircle vs interior.
  by_cases h_re_zero : τ.re = 0
  · -- Left edge: τ = i·y for some y > 0.
    have h_τ_eq : τ = Complex.I * τ.im := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [h_τ_eq]
    rw [modularLambdaH_pure_imag_real hτ_im_pos]
  · by_cases h_re_one : τ.re = 1
    · -- Right edge: τ = 1 + i·y for some y > 0.
      have h_τ_eq : τ = 1 + Complex.I * τ.im := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h_τ_eq]
      rw [modularLambdaH_one_add_imag_real hτ_im_pos]
    · by_cases h_semicircle : ‖2 * τ - 1‖ = 1
      · -- Semicircle: λ ∈ ℝ.
        rw [modularLambdaH_semicircle_real hτ_im_pos h_semicircle]
      · -- Strict interior: use Step A.
        have hτ_interior : τ ∈ Gamma2FundamentalDomainInterior := by
          refine ⟨hτ_im_pos, ?_, ?_, ?_⟩
          · rcases lt_or_eq_of_le hτ_re_nonneg with h | h
            · exact h
            · exact absurd h.symm h_re_zero
          · rcases lt_or_eq_of_le hτ_re_le_one with h | h
            · exact h
            · exact absurd h h_re_one
          · rcases lt_or_eq_of_le hτ_semicircle with h | h
            · exact h
            · exact absurd h.symm h_semicircle
        exact (modularLambdaH_F_im_pos τ hτ_interior).le

/-- **Half-FD existence (upper branch).** Every `τ ∈ ℍ` with
`Im(λ τ) > 0` has a `Γ(2)`-translate in the half-fundamental domain
`F`. Proof: use the strict fundamental-domain property
`gamma2_translate_in_F_union_F_sigma` to obtain `γ ∈ Γ(2)` with
`γ • τ ∈ F ∪ F^σ`. If `γ • τ ∈ F^σ`, then `-conj(γ • τ) ∈ F`
(by definition of `F^σ` as the reflection of `F`); by
`modularLambdaH_conj_symmetry` and `modularLambdaH_im_nonneg_on_closed_F`,
`Im(λ(γ • τ)) ≤ 0`; but by `Γ(2)`-invariance of `λ`,
`Im(λ(γ • τ)) = Im(λ τ) > 0` — contradiction. So `γ • τ ∈ F`. -/
theorem gamma2_orbit_meets_F_when_im_lambda_pos (τ : UpperHalfPlane)
    (hτ_pos : 0 < (modularLambdaH (τ : ℂ)).im) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2,
      ((γ • τ : UpperHalfPlane) : ℂ) ∈ Gamma2FundamentalDomain := by
  obtain ⟨γ, hγ_in, h_in_union⟩ := gamma2_translate_in_F_union_F_sigma τ
  -- λ-invariance: λ(γ•τ) = λ(τ).
  have h_lam_inv : modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) = modularLambdaH (τ : ℂ) :=
    modularLambdaH_gamma2_invariant γ hγ_in τ
  -- Im(λ γτ) = Im(λ τ) > 0.
  have h_im_lam_γτ : 0 < (modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ)).im := by
    rw [h_lam_inv]; exact hτ_pos
  rcases h_in_union with h_F | h_Fσ
  · exact ⟨γ, hγ_in, h_F⟩
  · -- γ • τ ∈ F^σ: derive contradiction via conjugation.
    exfalso
    -- Extract F^σ membership data.
    obtain ⟨hγτ_im, hγτ_re_ge, hγτ_re_le, hγτ_semicircle⟩ := h_Fσ
    -- -conj(γ • τ) ∈ F.
    set γτ_c : ℂ := ((γ • τ : UpperHalfPlane) : ℂ) with hγτ_c_def
    have h_neg_conj_in_F : -(starRingEnd ℂ γτ_c) ∈ Gamma2FundamentalDomain := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Im(-conj γτ) = Im(γτ) > 0.
        simp only [Complex.neg_im, Complex.conj_im, neg_neg]
        exact hγτ_im
      · -- Re(-conj γτ) = -Re(γτ) ≥ 0 (since Re(γτ) ≤ 0).
        simp only [Complex.neg_re, Complex.conj_re]
        linarith
      · -- Re(-conj γτ) = -Re(γτ) ≤ 1 (since Re(γτ) ≥ -1).
        simp only [Complex.neg_re, Complex.conj_re]
        linarith
      · -- |2(-conj γτ) - 1| = |2γτ + 1| ≥ 1.
        have h_eq_neg_conj : (2 * (-(starRingEnd ℂ γτ_c)) - 1 : ℂ) =
            -(starRingEnd ℂ (2 * γτ_c + 1)) := by
          simp only [map_add, map_mul, Complex.conj_ofNat, map_one]
          ring
        have h_norm_eq : ‖2 * (-(starRingEnd ℂ γτ_c)) - 1‖ = ‖2 * γτ_c + 1‖ := by
          rw [h_eq_neg_conj, norm_neg, Complex.norm_conj]
        rw [h_norm_eq]
        exact hγτ_semicircle
    -- λ(-conj γτ) = conj(λ γτ) by conjugation symmetry.
    have h_lam_neg_conj : modularLambdaH (-(starRingEnd ℂ γτ_c)) =
        starRingEnd ℂ (modularLambdaH γτ_c) :=
      modularLambdaH_conj_symmetry hγτ_im
    -- Im(λ(-conj γτ)) ≥ 0 (from closed F).
    have h_im_neg_conj_nonneg : 0 ≤ (modularLambdaH (-(starRingEnd ℂ γτ_c))).im :=
      modularLambdaH_im_nonneg_on_closed_F h_neg_conj_in_F
    -- Im(conj(λ γτ)) = -Im(λ γτ).
    have h_im_conj_eq : (starRingEnd ℂ (modularLambdaH γτ_c)).im =
        -(modularLambdaH γτ_c).im := by
      simp [Complex.conj_im]
    -- Combine: Im(λ γτ) ≤ 0.
    rw [h_lam_neg_conj, h_im_conj_eq] at h_im_neg_conj_nonneg
    -- h_im_neg_conj_nonneg : 0 ≤ -(modularLambdaH γτ_c).im
    have h_im_γτ_le : (modularLambdaH γτ_c).im ≤ 0 := by linarith
    -- But h_im_lam_γτ : 0 < (modularLambdaH γτ_c).im. Contradiction.
    linarith

/-! ## Half-fundamental-domain injectivity (architectural helper) -/

/-- **Existence and uniqueness of `λ`-preimage in `F^o`.** For each
`w` with `Im w > 0`, there is a unique `τ ∈ F^o` with `λ(τ) = w`.

This is the argument-principle output for the truncated fundamental
domain `F_Y = F ∩ {Im τ ≤ Y}` (Y large): `F_Y` is the closed rectangle
`[0, 1] × [0, Y]` with the open half-disk
`{τ : |2τ − 1| < 1, Im τ > 0}` removed. The boundary
`∂F_Y` decomposes into four arcs: the left vertical edge `Re τ = 0`,
the bottom semicircular arc `|2τ − 1| = 1, Im τ ≥ 0`, the right
vertical edge `Re τ = 1`, and the top horizontal segment `Im τ = Y`.

Applying `cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusDisk` to
`g(z) := λ(z) − w` (analytic on a neighborhood of `F_Y`,
non-vanishing on `∂F_Y` because `λ` maps each of the three permanent
arcs into disjoint real-axis intervals `(0, 1)`, `(−∞, 0)`, `(1, +∞)`
while `Im w > 0`), gives the count of preimages of `w` in the open
`F_Y^o` as a natural number `n`. The three boundary-arc image
intervals together with the cusp asymptotic `λ(τ) → 0` along the
top edge (combining `modularLambdaH_iy_tendsto_zero_atTop` and
`modularLambdaH_one_add_iy_tendsto_zero_atTop`) show that the
winding number of `λ ∘ ∂F_Y` around `w` equals `1` for any
`w ∈ {Im w > 0}` and all `Y` sufficiently large. Hence `n = 1`,
i.e., there is exactly one preimage of `w` in `F_Y^o`, and the count
is independent of `Y`. Taking `Y → ∞` extends this to all of `F^o`. -/
theorem modularLambdaH_existsUnique_in_F_interior_of_im_pos
    {w : ℂ} (_hw : 0 < w.im) :
    ∃! τ : ℂ, τ ∈ Gamma2FundamentalDomainInterior ∧ modularLambdaH τ = w := by
  sorry

/-- **Injectivity of `λ` on the open interior `F^o`.** Combined
with the surjectivity from Step D
`modularLambdaH_image_fundamentalDomainInterior`, this yields the
biholomorphism `λ : F^o ≅ {Im w > 0}`. Direct consequence of
`modularLambdaH_existsUnique_in_F_interior_of_im_pos`: the unique
preimage of `λ τ₁` in `F^o` is both `τ₁` and `τ₂`. -/
theorem modularLambdaH_injOn_F_interior :
    Set.InjOn modularLambdaH Gamma2FundamentalDomainInterior := by
  intro τ₁ h₁ τ₂ h₂ h_eq
  have hw : 0 < (modularLambdaH τ₁).im := modularLambdaH_F_im_pos τ₁ h₁
  obtain ⟨τ, _, hτ_unique⟩ :=
    modularLambdaH_existsUnique_in_F_interior_of_im_pos hw
  have h_τ₁ : τ₁ = τ := hτ_unique τ₁ ⟨h₁, rfl⟩
  have h_τ₂ : τ₂ = τ := hτ_unique τ₂ ⟨h₂, h_eq.symm⟩
  rw [h_τ₁, h_τ₂]

/-- **Injectivity of `λ` on the boundary `∂F`.** For two boundary
points `τ₁, τ₂ ∈ F \ F^o` with `λ(τ₁) = λ(τ₂)`, we have `τ₁ = τ₂`.
The proof case-splits on which of the three boundary arcs each `τᵢ`
lies on (left edge `Re τ = 0`, right edge `Re τ = 1`, upper
semicircle `|2τ − 1| = 1`). Same arc ⟹ same point by strict
monotonicity (left edge: existing `modularLambdaH_iy_strictAntitone`;
right edge: derivable from `modularLambdaH_T_smul` + left-edge
antitone, with `λ(1 + iy) = λ(iy) / (λ(iy) − 1)` after the Jacobi
identity simplification; semicircle: derivable from
`modularLambdaH_add_S_smul_eq_one` + left-edge antitone via
`−1/τ = −1 + i tan(θ/2)`). Different arcs ⟹ disjoint images in
`(0, 1)`, `(−∞, 0)`, `(1, +∞)` contradict `λ`-equality. -/
theorem modularLambdaH_injOn_F_boundary
    {τ₁ τ₂ : ℂ}
    (h₁ : τ₁ ∈ Gamma2FundamentalDomain)
    (h₁_not_int : τ₁ ∉ Gamma2FundamentalDomainInterior)
    (h₂ : τ₂ ∈ Gamma2FundamentalDomain)
    (h₂_not_int : τ₂ ∉ Gamma2FundamentalDomainInterior)
    (h_eq : modularLambdaH τ₁ = modularLambdaH τ₂) :
    τ₁ = τ₂ := by
  sorry

/-- **Injectivity of `λ` on the closed half-fundamental domain `F`.**
Case split on `F^o` vs `∂F` for each of `τ₁`, `τ₂`:

* **Both `F^o`**: `modularLambdaH_injOn_F_interior`.
* **Both `∂F`**: `modularLambdaH_injOn_F_boundary`.
* **Mixed (one `F^o`, one `∂F`)**: `Im λ > 0` on `F^o` (Step A,
  `modularLambdaH_F_im_pos`) versus `Im λ = 0` on `∂F` (from one of
  the three boundary real-value lemmas
  `modularLambdaH_pure_imag_real` / `_one_add_imag_real` /
  `_semicircle_real`) — contradicts `λ`-equality. -/
theorem modularLambdaH_injOn_F_closed :
    Set.InjOn modularLambdaH Gamma2FundamentalDomain := by
  intro τ₁ h₁ τ₂ h₂ h_eq
  obtain ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ := h₁
  obtain ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ := h₂
  -- Helper: `Im(λ τ) = 0` for `τ ∈ ∂F`.
  have h_im_zero_on_boundary : ∀ {τ : ℂ}, τ ∈ Gamma2FundamentalDomain →
      τ ∉ Gamma2FundamentalDomainInterior → (modularLambdaH τ).im = 0 := by
    intro τ hτ_F hτ_not_int
    obtain ⟨hτ_im, hτ_re_nn, hτ_re_le, hτ_semi⟩ := hτ_F
    by_cases h_re_zero : τ.re = 0
    · have h_τ_eq : τ = Complex.I * τ.im := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h_τ_eq]; exact modularLambdaH_pure_imag_real hτ_im
    · by_cases h_re_one : τ.re = 1
      · have h_τ_eq : τ = 1 + Complex.I * τ.im := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
        rw [h_τ_eq]; exact modularLambdaH_one_add_imag_real hτ_im
      · by_cases h_semi_eq : ‖2 * τ - 1‖ = 1
        · exact modularLambdaH_semicircle_real hτ_im h_semi_eq
        · -- All three boundary inequalities strict ⟹ τ ∈ F^o, contradicts.
          exfalso
          apply hτ_not_int
          refine ⟨hτ_im, ?_, ?_, ?_⟩
          · rcases lt_or_eq_of_le hτ_re_nn with h | h
            · exact h
            · exact absurd h.symm h_re_zero
          · rcases lt_or_eq_of_le hτ_re_le with h | h
            · exact h
            · exact absurd h h_re_one
          · rcases lt_or_eq_of_le hτ_semi with h | h
            · exact h
            · exact absurd h.symm h_semi_eq
  by_cases h₁_int : τ₁ ∈ Gamma2FundamentalDomainInterior
  · by_cases h₂_int : τ₂ ∈ Gamma2FundamentalDomainInterior
    · -- Both interior.
      exact modularLambdaH_injOn_F_interior h₁_int h₂_int h_eq
    · -- τ₁ interior, τ₂ boundary: contradicts via Im λ.
      exfalso
      have h_im_1 : 0 < (modularLambdaH τ₁).im := modularLambdaH_F_im_pos _ h₁_int
      have h_im_2 : (modularLambdaH τ₂).im = 0 :=
        h_im_zero_on_boundary ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ h₂_int
      rw [h_eq] at h_im_1
      linarith
  · by_cases h₂_int : τ₂ ∈ Gamma2FundamentalDomainInterior
    · -- τ₁ boundary, τ₂ interior: contradicts via Im λ.
      exfalso
      have h_im_2 : 0 < (modularLambdaH τ₂).im := modularLambdaH_F_im_pos _ h₂_int
      have h_im_1 : (modularLambdaH τ₁).im = 0 :=
        h_im_zero_on_boundary ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ h₁_int
      rw [← h_eq] at h_im_2
      linarith
    · -- Both boundary.
      exact modularLambdaH_injOn_F_boundary
        ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ h₁_int
        ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ h₂_int h_eq

/-- **Injectivity of `λ` on `F` modulo `Γ(2)`.** For
`τ₁, τ₂ ∈ F ⊂ ℍ` with `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Direct consequence of `modularLambdaH_injOn_F_closed`:
`λ` injective on `F` gives `τ₁ = τ₂` in `ℂ`, hence `τ₁ = τ₂` in `ℍ`
(by `UpperHalfPlane.ext`), and `γ = 1 ∈ Γ(2)` does the job. -/
theorem modularLambdaH_injOn_F_mod_gamma2
    {τ₁ τ₂ : UpperHalfPlane}
    (h₁ : (τ₁ : ℂ) ∈ Gamma2FundamentalDomain)
    (h₂ : (τ₂ : ℂ) ∈ Gamma2FundamentalDomain)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have h_eq_c : (τ₁ : ℂ) = (τ₂ : ℂ) :=
    modularLambdaH_injOn_F_closed h₁ h₂ h_eq
  have h_eq_h : τ₁ = τ₂ := UpperHalfPlane.ext h_eq_c
  refine ⟨1, (CongruenceSubgroup.Gamma 2).one_mem, ?_⟩
  rw [h_eq_h]; exact one_smul _ _

/-! ## Pillar-4 sub-lemmas (orbit identification, three branches) -/

/-- **Pillar-4 upper branch.** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) > 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Reduce both `τ₁`, `τ₂` to `F` via
`gamma2_orbit_meets_F_when_im_lambda_pos`, apply
`modularLambdaH_injOn_F_mod_gamma2`, transport via the
`Γ(2)`-action. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_pos : 0 < (modularLambdaH (τ₁ : ℂ)).im)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have h_im_pos_2 : 0 < (modularLambdaH (τ₂ : ℂ)).im := by rw [← h_eq]; exact h_im_pos
  obtain ⟨γ₁, hγ₁_in, hγ₁τ₁_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ₁ h_im_pos
  obtain ⟨γ₂, hγ₂_in, hγ₂τ₂_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ₂ h_im_pos_2
  have h_eq_γ : modularLambdaH ((γ₁ • τ₁ : UpperHalfPlane) : ℂ)
      = modularLambdaH ((γ₂ • τ₂ : UpperHalfPlane) : ℂ) := by
    rw [modularLambdaH_gamma2_invariant γ₁ hγ₁_in τ₁,
      modularLambdaH_gamma2_invariant γ₂ hγ₂_in τ₂]
    exact h_eq
  obtain ⟨γ, hγ_in, hγ_eq⟩ :=
    modularLambdaH_injOn_F_mod_gamma2 hγ₁τ₁_F hγ₂τ₂_F h_eq_γ
  refine ⟨γ₂⁻¹ * γ * γ₁, ?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma 2).mul_mem
      ((CongruenceSubgroup.Gamma 2).mul_mem
        ((CongruenceSubgroup.Gamma 2).inv_mem hγ₂_in) hγ_in) hγ₁_in
  · rw [mul_smul, mul_smul, hγ_eq, ← mul_smul, inv_mul_cancel, one_smul]

/-! ## Analytic non-injectivity helper -/

set_option maxHeartbeats 400000 in
-- Composes the multiplicity factorization with an analytic n-th root
-- (`Complex.log` + `Complex.exp`) and the inverse function theorem; the
-- combined elaboration pressure exceeds the default heartbeat limit.
/-- **Analytic local openness with multiplicity.** If `f : ℂ → ℂ`
is analytic at `z₀`, not eventually constant near `z₀`, and
`deriv f z₀ = 0`, then in any neighbourhood `U` of `z₀` and for any
value `w` sufficiently close (but unequal) to `f z₀`, there exist
two distinct points `z₁, z₂ ∈ U` with `f z₁ = f z₂ = w`. This is
the classical "open mapping with multiplicity ≥ 2" statement: the
factorization `f(z) - f(z₀) = (z - z₀)^n · g(z)` with `n ≥ 2`,
`g(z₀) ≠ 0`, combined with the existence of an analytic `n`-th root
of `g` near `z₀` (via `Complex.exp ∘ ((1/n) * Complex.log ∘ h)`),
yields `n` distinct preimages for each `w` in a small punctured
neighbourhood of `f(z₀)`. -/
theorem analyticAt_localOpen_with_multiplicity
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀)
    (h_nc : ¬ ∀ᶠ z in nhds z₀, f z = f z₀)
    (h_dz : deriv f z₀ = 0)
    (U : Set ℂ) (hU : U ∈ nhds z₀) :
    ∃ V ∈ nhds (f z₀), ∀ w ∈ V, w ≠ f z₀ →
      ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ ∧ f z₁ = w ∧ f z₂ = w := by
  -- Abbreviate f₀(z) := f(z) - f(z₀). Analytic at z₀ with f₀(z₀) = 0.
  set f₀ : ℂ → ℂ := fun z => f z - f z₀ with hf₀_def
  have hf₀_at : AnalyticAt ℂ f₀ z₀ := hf.sub analyticAt_const
  -- Order of f₀ is not ⊤ (else f₀ ≡ 0 near z₀, i.e. f eventually constant).
  have h_order_ne_top : analyticOrderAt f₀ z₀ ≠ ⊤ := by
    intro h_top
    rw [analyticOrderAt_eq_top] at h_top
    apply h_nc
    filter_upwards [h_top] with z hz
    exact sub_eq_zero.mp hz
  -- Use analyticOrderAt_deriv_add_one to obtain n ≥ 2.
  have h_order_chain :
      analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f₀ z₀ := by
    have h := hf.analyticOrderAt_deriv_add_one
    -- h : order(deriv f) + 1 = order (fun x_1 => f x_1 - f z₀) = order f₀.
    exact h
  -- deriv f is analytic at z₀ (from f analytic at z₀).
  have h_deriv_at : AnalyticAt ℂ (deriv f) z₀ := hf.deriv
  -- (deriv f)(z₀) = 0, and deriv f is analytic, so analyticOrderAt (deriv f) z₀ ≥ 1.
  -- Specifically: if order = 0, then (deriv f)(z₀) ≠ 0 by definition.
  have h_deriv_order_ge_one : 1 ≤ analyticOrderAt (deriv f) z₀ := by
    rw [ENat.one_le_iff_ne_zero]
    intro h_eq
    rw [h_deriv_at.analyticOrderAt_eq_zero] at h_eq
    exact h_eq h_dz
  -- Hence order(f₀) ≥ 2.
  have h_order_f₀_ge_two : 2 ≤ analyticOrderAt f₀ z₀ := by
    rw [← h_order_chain]
    calc (2 : ℕ∞) = 1 + 1 := by rfl
      _ ≤ analyticOrderAt (deriv f) z₀ + 1 := by
        gcongr
  -- Convert order to natural number n.
  obtain ⟨n, hn_coe⟩ := ENat.ne_top_iff_exists.mp h_order_ne_top
  have hn_eq : analyticOrderAt f₀ z₀ = (n : ℕ∞) := hn_coe.symm
  have hn_ge_two : 2 ≤ n := by
    have : ((2 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by rw [← hn_eq]; exact_mod_cast h_order_f₀_ge_two
    exact_mod_cast this
  have hn_pos : 0 < n := by linarith
  have hn_ne_zero : n ≠ 0 := by linarith
  -- Get the factorization.
  obtain ⟨g, hg_at, hg_ne, hg_eq⟩ :=
    (hf₀_at.analyticOrderAt_eq_natCast).mp hn_eq
  -- hg_eq : ∀ᶠ z in nhds z₀, f₀ z = (z - z₀) ^ n • g z
  -- Define c := g z₀, and h(z) := g(z) / c.
  set c : ℂ := g z₀ with hc_def
  have hc_ne : c ≠ 0 := hg_ne
  set h : ℂ → ℂ := fun z => g z / c with hh_def
  have hh_at : AnalyticAt ℂ h z₀ := (hg_at.div_const : AnalyticAt ℂ (fun z => g z / c) z₀)
  have hh_z₀_one : h z₀ = 1 := by
    change g z₀ / c = 1
    exact div_self hc_ne
  have hh_in_slit : h z₀ ∈ Complex.slitPlane := by
    rw [hh_z₀_one]; exact Complex.one_mem_slitPlane
  -- Eventually h(z) ∈ slitPlane (since slitPlane is open + h continuous).
  have h_h_slit_evt : ∀ᶠ z in nhds z₀, h z ∈ Complex.slitPlane :=
    hh_at.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hh_in_slit)
  -- log analytic at h(z₀) = 1.
  have h_log_at : AnalyticAt ℂ Complex.log (h z₀) := by
    apply DifferentiableOn.analyticAt _ (Complex.isOpen_slitPlane.mem_nhds hh_in_slit)
    intro z hz
    exact (Complex.differentiableAt_log hz).differentiableWithinAt
  -- log ∘ h analytic at z₀.
  have h_log_h_at : AnalyticAt ℂ (Complex.log ∘ h) z₀ := h_log_at.comp hh_at
  -- Define ρ(z) := exp ((1/n) * log(h z)).
  set ρ : ℂ → ℂ := fun z => Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z)) with hρ_def
  -- ρ analytic at z₀.
  have hρ_at : AnalyticAt ℂ ρ z₀ := by
    have h_mul : AnalyticAt ℂ (fun z => (n : ℂ)⁻¹ * Complex.log (h z)) z₀ :=
      (analyticAt_const).mul h_log_h_at
    exact h_mul.cexp
  -- ρ(z₀) = 1.
  have hρ_z₀ : ρ z₀ = 1 := by
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z₀)) = 1
    rw [hh_z₀_one, Complex.log_one, mul_zero, Complex.exp_zero]
  -- Eventually ρ(z)^n = h(z).
  have h_nC_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn_ne_zero
  have h_ρ_pow_eq : ∀ᶠ z in nhds z₀, ρ z ^ n = h z := by
    filter_upwards [h_h_slit_evt] with z hz_slit
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z)) ^ n = h z
    rw [← Complex.exp_nat_mul]
    have h_h_ne : h z ≠ 0 := Complex.slitPlane_ne_zero hz_slit
    have h_simp : (n : ℂ) * ((n : ℂ)⁻¹ * Complex.log (h z)) = Complex.log (h z) := by
      field_simp
    rw [h_simp]
    exact Complex.exp_log h_h_ne
  -- Define φ(z) := (z - z₀) · ρ(z).
  set φ : ℂ → ℂ := fun z => (z - z₀) * ρ z with hφ_def
  have hφ_at : AnalyticAt ℂ φ z₀ :=
    (analyticAt_id.sub analyticAt_const).mul hρ_at
  have hφ_z₀ : φ z₀ = 0 := by change (z₀ - z₀) * _ = 0; ring
  -- HasDerivAt φ 1 z₀.
  have hφ_hasDeriv : HasDerivAt φ 1 z₀ := by
    have h_a : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := by
      simpa using (hasDerivAt_id z₀).sub_const z₀
    have h_b : HasDerivAt ρ (deriv ρ z₀) z₀ := hρ_at.differentiableAt.hasDerivAt
    have h_mul := h_a.mul h_b
    have h_simpl : (1 : ℂ) * ρ z₀ + (z₀ - z₀) * deriv ρ z₀ = 1 := by
      rw [hρ_z₀]; ring
    rw [← h_simpl]
    exact h_mul
  have hφ_deriv_eq : deriv φ z₀ = 1 := hφ_hasDeriv.deriv
  -- HasStrictDerivAt φ 1 z₀.
  have hφ_strict : HasStrictDerivAt φ 1 z₀ := by
    have := hφ_at.hasStrictDerivAt
    rw [hφ_deriv_eq] at this
    exact this
  -- Local inverse ψ.
  set ψ : ℂ → ℂ := hφ_strict.localInverse φ 1 z₀ one_ne_zero with hψ_def
  -- ψ(0) = z₀ via eventually_left_inverse at z₀.
  have hψ_0 : ψ 0 = z₀ := by
    have h_ev := hφ_strict.eventually_left_inverse one_ne_zero
    have h_at_z₀ : ψ (φ z₀) = z₀ := h_ev.self_of_nhds
    rwa [hφ_z₀] at h_at_z₀
  -- ψ continuous at 0 via HasStrictFDerivAt.localInverse_continuousAt.
  have hψ_cont : ContinuousAt ψ 0 := by
    have h_cont_at : ContinuousAt ψ (φ z₀) :=
      (hφ_strict.hasStrictFDerivAt_equiv one_ne_zero).localInverse_continuousAt
    rwa [hφ_z₀] at h_cont_at
  -- Eventually φ(ψ y) = y near 0 (right inverse).
  have h_right_inv : ∀ᶠ y in nhds 0, φ (ψ y) = y := by
    have h_ev := hφ_strict.eventually_right_inverse one_ne_zero
    rwa [hφ_z₀] at h_ev
  -- Eventually f(z) = f(z₀) + c · φ(z)^n.
  have h_factor_eq : ∀ᶠ z in nhds z₀, f z = f z₀ + c * φ z ^ n := by
    filter_upwards [hg_eq, h_ρ_pow_eq] with z h_fact h_pow
    -- h_fact : f z - f z₀ = (z - z₀)^n • g z
    -- h_pow : ρ z ^ n = h z = g z / c
    change f z = f z₀ + c * ((z - z₀) * ρ z) ^ n
    have h_sub : f z - f z₀ = (z - z₀)^n • g z := h_fact
    have h_smul : (z - z₀)^n • g z = (z - z₀)^n * g z := by rw [smul_eq_mul]
    rw [h_smul] at h_sub
    have h_g_eq : g z = c * h z := by
      change g z = c * (g z / c)
      field_simp
    rw [h_g_eq] at h_sub
    have h_pow_expand : ((z - z₀) * ρ z) ^ n = (z - z₀)^n * ρ z ^ n := by
      rw [mul_pow]
    rw [h_pow_expand, h_pow]
    linear_combination h_sub
  -- Collect all eventually-conditions into a single open ball around z₀:
  -- ∃ ε > 0, ∀ z ∈ B(z₀, ε), ψ z ∈ U ∧ f(ψ z + extra) etc.
  -- Use that ψ(0) = z₀ ∈ U (since U ∈ nhds z₀).
  -- Build the witness V around f(z₀) such that w ∈ V → ζ = (w - f(z₀))/c is small enough
  -- that both ζ_0 = exp((1/n) log ζ) and ζ_1 = ζ_0 * exp(2πi/n) are in nhds 0 with all
  -- needed properties.
  -- Combine eventually facts: ψ(0) = z₀ ∈ U, ψ continuous, etc.
  -- Get a single radius δ that handles everything.
  have h_all_nhd_0 : ∀ᶠ y in nhds 0, φ (ψ y) = y ∧ ψ y ∈ U ∧ f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
    have h_ψU : ∀ᶠ y in nhds 0, ψ y ∈ U := by
      have h_ψU_filter : Filter.Tendsto ψ (nhds 0) (nhds (ψ 0)) := hψ_cont
      rw [hψ_0] at h_ψU_filter
      exact h_ψU_filter hU
    have h_fac_ψ : ∀ᶠ y in nhds 0, f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
      have h_ψ_to_z₀ : Filter.Tendsto ψ (nhds 0) (nhds z₀) := by
        rw [← hψ_0]; exact hψ_cont
      exact h_ψ_to_z₀ h_factor_eq
    filter_upwards [h_right_inv, h_ψU, h_fac_ψ] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- Extract ε > 0 such that B(0, ε) is in the eventually set.
  rcases Metric.eventually_nhds_iff.mp h_all_nhd_0 with ⟨δ, hδ_pos, hδ_prop⟩
  -- Define V = B(f z₀, |c| · δ^n).
  set η : ℝ := ‖c‖ * δ^n with hη_def
  have hη_pos : 0 < η := by
    have hδ_pow_pos : 0 < δ^n := pow_pos hδ_pos n
    have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    positivity
  refine ⟨Metric.ball (f z₀) η, Metric.ball_mem_nhds _ hη_pos, ?_⟩
  intro w hw_in_V hw_ne
  -- w ∈ B(f z₀, η), w ≠ f z₀.
  -- Define ζ = (w - f z₀) / c.
  set ζ : ℂ := (w - f z₀) / c with hζ_def
  have hζ_ne : ζ ≠ 0 := by
    intro hζ_zero
    apply hw_ne
    have h_sub_zero : w - f z₀ = 0 := by
      have h1 : (w - f z₀) / c = 0 := hζ_zero
      have h_mul : (w - f z₀) / c * c = 0 * c := by rw [h1]
      rw [div_mul_cancel₀ _ hc_ne, zero_mul] at h_mul
      exact h_mul
    linear_combination h_sub_zero
  -- Define ζ_0 = exp((1/n) * log ζ), ζ_1 = ζ_0 * exp(2πi/n).
  set ζ_0 : ℂ := Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ) with hζ_0_def
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hω_def
  set ζ_1 : ℂ := ζ_0 * ω with hζ_1_def
  -- ζ_0 ^ n = ζ.
  have hζ_0_pow : ζ_0 ^ n = ζ := by
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ) ^ n = ζ
    rw [← Complex.exp_nat_mul]
    have h_simp : (n : ℂ) * ((n : ℂ)⁻¹ * Complex.log ζ) = Complex.log ζ := by field_simp
    rw [h_simp]
    exact Complex.exp_log hζ_ne
  -- ω ^ n = 1.
  have hω_pow : ω ^ n = 1 := by
    change Complex.exp (2 * Real.pi * Complex.I / n) ^ n = 1
    rw [← Complex.exp_nat_mul]
    have h_simp : (n : ℂ) * (2 * Real.pi * Complex.I / n) = 2 * Real.pi * Complex.I := by
      field_simp
    rw [h_simp]
    exact Complex.exp_two_pi_mul_I
  -- ζ_1 ^ n = ζ.
  have hζ_1_pow : ζ_1 ^ n = ζ := by
    change (ζ_0 * ω) ^ n = ζ
    rw [mul_pow, hω_pow, mul_one, hζ_0_pow]
  -- ω ≠ 1 (since n ≥ 2).
  have hω_ne_one : ω ≠ 1 := by
    intro hω_one
    -- ω = 1 means exp(2πi/n) = 1, so 2πi/n = 2πi·k for some k ∈ ℤ.
    -- This means 1/n = k, so n | 1, so n = 1, contradicting n ≥ 2.
    have h_log_eq : Complex.log ω = 0 := by rw [hω_one]; exact Complex.log_one
    -- log(exp(z)) = z when -π < z.im ≤ π.
    have h_2pi_div_n_im : ((2 * Real.pi * Complex.I / n : ℂ)).im = 2 * Real.pi / n := by
      have h_n_re : (n : ℂ).re = n := by simp
      have h_n_im : (n : ℂ).im = 0 := by simp
      have h_n_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      simp [Complex.div_im, Complex.mul_im, Complex.mul_re,
        Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im, h_n_im]
      field_simp
    have h_2pi_div_n_lt : (2 * Real.pi * Complex.I / n : ℂ).im ≤ Real.pi := by
      rw [h_2pi_div_n_im]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn_ge_two
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have : 2 * Real.pi / n ≤ Real.pi := by
        rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (n : ℝ))]
        nlinarith
      exact this
    have h_2pi_div_n_gt : -Real.pi < (2 * Real.pi * Complex.I / n : ℂ).im := by
      rw [h_2pi_div_n_im]
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      have : 0 < 2 * Real.pi / n := by positivity
      linarith
    have h_log_omega : Complex.log ω = 2 * Real.pi * Complex.I / n := by
      change Complex.log (Complex.exp (2 * Real.pi * Complex.I / n)) = 2 * Real.pi * Complex.I / n
      exact Complex.log_exp h_2pi_div_n_gt h_2pi_div_n_lt
    rw [h_log_omega] at h_log_eq
    -- h_log_eq : 2πi/n = 0, but 2πi/n ≠ 0.
    have h_im : (2 * Real.pi * Complex.I / n : ℂ).im = 0 := by rw [h_log_eq]; simp
    rw [h_2pi_div_n_im] at h_im
    have h_pos : 0 < 2 * Real.pi / n := by
      have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      have : 0 < Real.pi := Real.pi_pos
      positivity
    linarith
  -- ζ_1 ≠ ζ_0.
  have hζ_ne_distinct : ζ_0 ≠ ζ_1 := by
    intro h_eq
    have h_ζ₀_ne : ζ_0 ≠ 0 := by
      intro h_ζ₀_zero
      have : ζ_0 ^ n = 0 := by rw [h_ζ₀_zero]; exact zero_pow hn_ne_zero
      rw [hζ_0_pow] at this
      exact hζ_ne this
    have : ω = 1 := by
      have h_eq' : ζ_0 * ω = ζ_0 * 1 := by rw [mul_one]; exact h_eq.symm
      exact mul_left_cancel₀ h_ζ₀_ne h_eq'
    exact hω_ne_one this
  -- |ζ| < δ^n.
  have h_ζ_norm : ‖ζ‖ < δ^n := by
    change ‖(w - f z₀) / c‖ < δ^n
    rw [norm_div]
    rw [Metric.mem_ball, dist_eq_norm] at hw_in_V
    have h_num_lt : ‖w - f z₀‖ < η := hw_in_V
    have h_c_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    rw [div_lt_iff₀ h_c_norm_pos]
    have h_η_def : η = ‖c‖ * δ^n := hη_def
    nlinarith
  -- ‖ζ_0‖ = |ζ|^(1/n) < δ.
  have h_ζ₀_norm_eq : ‖ζ_0‖ = ‖ζ‖^((n : ℝ)⁻¹) := by
    change ‖Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ)‖ = ‖ζ‖^((n : ℝ)⁻¹)
    rw [Complex.norm_exp]
    -- Re((n : ℂ)⁻¹ * log ζ) = (1/n) * Re(log ζ) = (1/n) * log ‖ζ‖
    have h_n_re : ((n : ℂ)⁻¹).re = (n : ℝ)⁻¹ := by
      have : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [this, ← Complex.ofReal_inv]
      simp
    have h_n_im : ((n : ℂ)⁻¹).im = 0 := by
      have : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [this, ← Complex.ofReal_inv]
      simp
    rw [Complex.mul_re, h_n_re, h_n_im, zero_mul, sub_zero]
    rw [Complex.log_re]
    have h_norm_pos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ_ne
    rw [show (n : ℝ)⁻¹ * Real.log ‖ζ‖ = Real.log ‖ζ‖ * (n : ℝ)⁻¹ from by ring]
    exact (Real.rpow_def_of_pos h_norm_pos _).symm
  have h_ζ₀_norm_lt : ‖ζ_0‖ < δ := by
    rw [h_ζ₀_norm_eq]
    have h_pos_zeta : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ_ne
    have h_n_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h_n_real_ne : (n : ℝ) ≠ 0 := ne_of_gt h_n_real_pos
    have h_n_inv_pos : 0 < ((n : ℝ))⁻¹ := inv_pos.mpr h_n_real_pos
    -- We need ‖ζ‖^(1/n) < δ.
    -- We have ‖ζ‖ < δ^n (= h_ζ_norm).
    -- Apply rpow with positive 1/n: (‖ζ‖)^(1/n) < (δ^n)^(1/n) = δ.
    have h_δ_pos : 0 < δ := hδ_pos
    have h_step1 : ‖ζ‖ ^ ((n : ℝ)⁻¹) < (δ^n) ^ ((n : ℝ)⁻¹) := by
      exact Real.rpow_lt_rpow h_pos_zeta.le h_ζ_norm h_n_inv_pos
    have h_step2 : (δ^n) ^ ((n : ℝ)⁻¹) = δ := by
      rw [show δ^n = δ ^ ((n : ℕ) : ℝ) from (Real.rpow_natCast δ n).symm]
      rw [← Real.rpow_mul h_δ_pos.le]
      rw [mul_inv_cancel₀ h_n_real_ne]
      exact Real.rpow_one _
    linarith
  -- ‖ζ_1‖ = ‖ζ_0‖ < δ.
  have h_ζ₁_norm_lt : ‖ζ_1‖ < δ := by
    change ‖ζ_0 * ω‖ < δ
    rw [norm_mul]
    have h_omega_norm : ‖ω‖ = 1 := by
      change ‖Complex.exp (2 * Real.pi * Complex.I / n)‖ = 1
      rw [Complex.norm_exp]
      -- Re(2πi/n) = 0
      have h_re_zero : ((2 * Real.pi * Complex.I / n : ℂ)).re = 0 := by
        simp [Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [h_re_zero, Real.exp_zero]
    rw [h_omega_norm, mul_one]
    exact h_ζ₀_norm_lt
  -- ζ_0, ζ_1 ∈ B(0, δ).
  have h_ζ₀_in_ball : ζ_0 ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact h_ζ₀_norm_lt
  have h_ζ₁_in_ball : ζ_1 ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact h_ζ₁_norm_lt
  -- Convert to membership in nhds 0 (for hδ_prop).
  have hδ_at_ball : ∀ y ∈ Metric.ball (0 : ℂ) δ,
      φ (ψ y) = y ∧ ψ y ∈ U ∧ f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
    intro y hy
    have : dist y 0 < δ := Metric.mem_ball.mp hy
    exact hδ_prop this
  obtain ⟨h_φψ_ζ₀, hψ_ζ₀_U, h_f_ψ_ζ₀⟩ := hδ_at_ball ζ_0 h_ζ₀_in_ball
  obtain ⟨h_φψ_ζ₁, hψ_ζ₁_U, h_f_ψ_ζ₁⟩ := hδ_at_ball ζ_1 h_ζ₁_in_ball
  -- f(ψ ζ_i) = w.
  have h_f_ψ_ζ₀_eq_w : f (ψ ζ_0) = w := by
    rw [h_f_ψ_ζ₀, h_φψ_ζ₀, hζ_0_pow]
    change f z₀ + c * ((w - f z₀) / c) = w
    rw [mul_div_cancel₀ _ hc_ne]; ring
  have h_f_ψ_ζ₁_eq_w : f (ψ ζ_1) = w := by
    rw [h_f_ψ_ζ₁, h_φψ_ζ₁, hζ_1_pow]
    change f z₀ + c * ((w - f z₀) / c) = w
    rw [mul_div_cancel₀ _ hc_ne]; ring
  -- ψ ζ_0 ≠ ψ ζ_1.
  have hψ_ne : ψ ζ_0 ≠ ψ ζ_1 := by
    intro h_eq
    -- ψ injective on its image (since ψ is local inverse).
    have h_eq' : φ (ψ ζ_0) = φ (ψ ζ_1) := by rw [h_eq]
    rw [h_φψ_ζ₀, h_φψ_ζ₁] at h_eq'
    exact hζ_ne_distinct h_eq'
  -- Wrap up.
  exact ⟨ψ ζ_0, hψ_ζ₀_U, ψ ζ_1, hψ_ζ₁_U, hψ_ne, h_f_ψ_ζ₀_eq_w, h_f_ψ_ζ₁_eq_w⟩

/-- **Pillar-3 boundary `= 0` branch.** For `τ ∈ ℍ` with
`Im(λ τ) = 0`, `deriv λ τ ≠ 0`. Suppose `deriv λ τ = 0` for
contradiction. By `analyticAt_localOpen_with_multiplicity`, for
each `k` there are distinct `z₁ᵏ, z₂ᵏ ∈ B(τ, 1/(k+1)) ⊂ ℍ` with
`λ(z₁ᵏ) = λ(z₂ᵏ)` and `Im λ(z₁ᵏ) > 0` (the witness `λ τ + (r/2)·i`
inside the helper neighbourhood `V`). By Pillar-4 upper branch,
`z₂ᵏ = γₖ • z₁ᵏ` for some `γₖ ∈ Γ(2)`. Proper discontinuity
restricts `γₖ` to a finite set on a compact ball around `τ`;
extract a constant subsequence `γₖ = γ`. Passing to the limit,
`γ • τ = τ`, so by Pillar 1 (`gamma_two_fixed_point_implies_pm_one`)
`γ ∈ {I, -I}`. But `±I` acts trivially on `ℍ`, so along the
subsequence `z₁ᵏ = z₂ᵏ`, contradicting distinctness. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_zero
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im = 0) :
    deriv modularLambdaH τ ≠ 0 := by
  intro h_dz
  -- Setup: H is the open upper half-plane in ℂ.
  set H : Set ℂ := {z | 0 < z.im} with hH_def
  have hH_open : IsOpen H := by
    have : H = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp [hH_def]
    rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH H :=
    modularLambdaH_differentiableOn.analyticOnNhd hH_open
  have h_lam_at : AnalyticAt ℂ modularLambdaH τ := h_lam_an τ hτ
  have h_H_preconn : IsPreconnected H := by
    apply Convex.isPreconnected
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
  -- λ is not eventually constant at τ (identity theorem + global non-constancy).
  have h_lam_not_const : ¬ ∀ᶠ z in nhds τ, modularLambdaH z = modularLambdaH τ := by
    intro h_eq
    have h_const_an : AnalyticOnNhd ℂ (fun _ : ℂ => modularLambdaH τ) H :=
      fun _ _ => analyticAt_const
    have h_eqOn : Set.EqOn modularLambdaH (fun _ => modularLambdaH τ) H :=
      h_lam_an.eqOn_of_preconnected_of_eventuallyEq h_const_an h_H_preconn hτ h_eq
    have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.im h; simp at this
    have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.re h; simp at this
    have h_lam_img : modularLambdaH '' H = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := modularLambdaH_image
    have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' H := h_lam_img ▸ h_1i_in
    have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' H := h_lam_img ▸ h_2i_in
    obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
    obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
    have h_a := h_eqOn hτ_a_H
    have h_b := h_eqOn hτ_b_H
    rw [hτ_a_eq] at h_a
    rw [hτ_b_eq] at h_b
    have h_eq_12 : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := h_a.trans h_b.symm
    have h_re := congrArg Complex.re h_eq_12
    simp at h_re
  -- Setup τ_h and proper-discontinuity instance.
  haveI := gamma_two_properlyDiscontinuousSMul
  set τ_h : UpperHalfPlane := ⟨τ, hτ⟩ with hτ_h_def
  -- For each k, helper produces distinct preimages with Im λ > 0.
  have h_seq : ∀ k : ℕ, ∃ z₁ z₂ : ℂ, 0 < z₁.im ∧ 0 < z₂.im ∧
      ‖z₁ - τ‖ < 1/(k+1) ∧ ‖z₂ - τ‖ < 1/(k+1) ∧
      z₁ ≠ z₂ ∧ modularLambdaH z₁ = modularLambdaH z₂ ∧
      0 < (modularLambdaH z₁).im := by
    intro k
    set ε : ℝ := 1/(k+1) with hε_def
    have hε_pos : 0 < ε := by positivity
    set U : Set ℂ := Metric.ball τ ε ∩ H with hU_def
    have hU_nhds : U ∈ nhds τ := Filter.inter_mem
      (Metric.ball_mem_nhds _ hε_pos) (hH_open.mem_nhds hτ)
    obtain ⟨V, hV_nhds, hV_prop⟩ :=
      analyticAt_localOpen_with_multiplicity h_lam_at h_lam_not_const h_dz U hU_nhds
    rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨r, hr_pos, hr_sub⟩
    set w : ℂ := modularLambdaH τ + (r/2 : ℝ) * Complex.I with hw_def
    have h_dist_w : dist w (modularLambdaH τ) = r/2 := by
      rw [hw_def, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr_pos)]
    have hw_in_V : w ∈ V := by
      apply hr_sub
      rw [Metric.mem_ball, h_dist_w]; linarith
    have hw_ne : w ≠ modularLambdaH τ := by
      intro h_eq
      have h_im_eq : w.im = (modularLambdaH τ).im := congrArg Complex.im h_eq
      rw [hw_def, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero, hlam_im] at h_im_eq
      linarith
    obtain ⟨z₁, hz₁_U, z₂, hz₂_U, hne, h_lam_z₁, h_lam_z₂⟩ := hV_prop w hw_in_V hw_ne
    obtain ⟨hz₁_ball, hz₁_im⟩ := hz₁_U
    obtain ⟨hz₂_ball, hz₂_im⟩ := hz₂_U
    refine ⟨z₁, z₂, hz₁_im, hz₂_im, ?_, ?_, hne, ?_, ?_⟩
    · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz₁_ball
    · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz₂_ball
    · rw [h_lam_z₁, h_lam_z₂]
    · rw [h_lam_z₁, hw_def]
      show 0 < (modularLambdaH τ + ↑(r/2) * Complex.I).im
      rw [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero, hlam_im, zero_add]
      exact half_pos hr_pos
  choose z₁ z₂ hz₁_im hz₂_im hd₁ hd₂ hne h_lam_eq h_im_pos using h_seq
  -- Sequences in ℍ.
  set z₁_h : ℕ → UpperHalfPlane := fun n => ⟨z₁ n, hz₁_im n⟩ with hz₁_h_def
  set z₂_h : ℕ → UpperHalfPlane := fun n => ⟨z₂ n, hz₂_im n⟩ with hz₂_h_def
  -- Pillar-4 upper for each n.
  have h_orbit : ∀ n, ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • z₁_h n = z₂_h n := by
    intro n
    exact gamma2_lambda_eq_implies_orbit_when_im_lambda_pos (h_im_pos n) (h_lam_eq n)
  choose γ hγ_in hγ_eq using h_orbit
  -- Tendsto z₁, z₂ → τ in ℂ via norm bounds.
  have h_z₁_tend_c : Filter.Tendsto z₁ Filter.atTop (nhds τ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h_nb : ‖z₁ n - τ‖ < 1/(n+1) := hd₁ n
    have h_le : (1 : ℝ)/(n+1) ≤ 1/(N+1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hn
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h_nb (le_of_lt (lt_of_le_of_lt h_le hN))
  have h_z₂_tend_c : Filter.Tendsto z₂ Filter.atTop (nhds τ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h_nb : ‖z₂ n - τ‖ < 1/(n+1) := hd₂ n
    have h_le : (1 : ℝ)/(n+1) ≤ 1/(N+1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hn
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h_nb (le_of_lt (lt_of_le_of_lt h_le hN))
  -- Bridge ℂ-Tendsto to ℍ-Tendsto via the open embedding.
  have h_ind : Topology.IsInducing (UpperHalfPlane.coe) :=
    UpperHalfPlane.isOpenEmbedding_coe.isInducing
  have h_z₁_tend_h : Filter.Tendsto z₁_h Filter.atTop (nhds τ_h) := by
    rw [h_ind.tendsto_nhds_iff]
    change Filter.Tendsto (fun n => (z₁_h n : ℂ)) Filter.atTop (nhds (τ_h : ℂ))
    exact h_z₁_tend_c
  have h_z₂_tend_h : Filter.Tendsto z₂_h Filter.atTop (nhds τ_h) := by
    rw [h_ind.tendsto_nhds_iff]
    change Filter.Tendsto (fun n => (z₂_h n : ℂ)) Filter.atTop (nhds (τ_h : ℂ))
    exact h_z₂_tend_c
  -- Compact ball K in ℍ.
  set K : Set UpperHalfPlane := Metric.closedBall τ_h 1 with hK_def
  have hK_compact : IsCompact K := isCompact_closedBall _ _
  -- Finite γ-set via proper discontinuity.
  set S : Set (↥(CongruenceSubgroup.Gamma 2)) :=
    { g | ((fun τ => g • τ) '' K ∩ K).Nonempty } with hS_def
  have hS_finite : S.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK_compact hK_compact
  -- For n large, z_h n ∈ K (using dist < 1/2 < 1).
  rw [Metric.tendsto_atTop] at h_z₁_tend_h h_z₂_tend_h
  obtain ⟨N₁, hN₁⟩ := h_z₁_tend_h (1/2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := h_z₂_tend_h (1/2) (by norm_num)
  set N : ℕ := max N₁ N₂ with hN_def
  have h_γ_in_S : ∀ n, N ≤ n →
      (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) ∈ S := by
    intro n hn
    have h1 := hN₁ n (le_of_max_le_left hn)
    have h2 := hN₂ n (le_of_max_le_right hn)
    refine ⟨z₂_h n, ⟨z₁_h n, ?_, hγ_eq n⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr (le_trans h1.le (by norm_num))
    · exact Metric.mem_closedBall.mpr (le_trans h2.le (by norm_num))
  -- Pigeonhole: some γ in S occurs at infinitely many n ≥ N.
  have h_pigeon : ∃ γ_lim : ↥(CongruenceSubgroup.Gamma 2), γ_lim ∈ S ∧
      {n : ℕ | N ≤ n ∧
        (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim}.Infinite := by
    by_contra h_neg
    push Not at h_neg
    have h_ici_infinite : Set.Infinite (Set.Ici N) := Set.Ici_infinite N
    apply h_ici_infinite
    have h_eq : Set.Ici N =
        ⋃ γ_lim ∈ S, {n : ℕ | N ≤ n ∧
          (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim} := by
      ext n
      simp only [Set.mem_Ici, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
      constructor
      · intro hn
        refine ⟨⟨γ n, hγ_in n⟩, h_γ_in_S n hn, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩
        exact hn
    rw [h_eq]
    apply hS_finite.biUnion
    intro γ_lim hγ_lim
    exact h_neg γ_lim hγ_lim
  obtain ⟨γ_lim, _hγ_lim_in_S, hγ_inf⟩ := h_pigeon
  -- Strictly mono subseq in the fiber {γ n = γ_lim}.
  have h_seq_idx : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, φ k ∈
      {n : ℕ | N ≤ n ∧
        (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim} := by
    apply Nat.exists_strictMono_subsequence
    intro M
    obtain ⟨b, hb_in, hb_gt⟩ := hγ_inf.exists_gt M
    exact ⟨b, hb_gt, hb_in⟩
  obtain ⟨φ, hφ_mono, hφ_in⟩ := h_seq_idx
  -- Along subseq, γ_lim.val • z₁_h (φ k) = z₂_h (φ k).
  have h_subseq_eq : ∀ k, γ_lim.val • z₁_h (φ k) = z₂_h (φ k) := by
    intro k
    have h_γ_eq_lim : γ (φ k) = γ_lim.val := by
      have := (hφ_in k).2
      exact congrArg Subtype.val this
    rw [← h_γ_eq_lim]
    exact hγ_eq (φ k)
  -- Distinct along subseq.
  have h_subseq_ne : ∀ k, z₁_h (φ k) ≠ z₂_h (φ k) := by
    intro k h_eq
    have h_z_eq : z₁ (φ k) = z₂ (φ k) := by
      have : (z₁_h (φ k) : ℂ) = (z₂_h (φ k) : ℂ) := by rw [h_eq]
      exact this
    exact hne (φ k) h_z_eq
  -- Take limit: γ_lim.val • τ_h = τ_h.
  have h_cont : Continuous (fun σ : UpperHalfPlane => γ_lim.val • σ) := by
    change Continuous (fun σ : UpperHalfPlane => ((γ_lim.val : SL(2, ℝ)) • σ))
    exact continuous_const_smul _
  have h_z₁_tend_h' : Filter.Tendsto z₁_h Filter.atTop (nhds τ_h) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    exact h_z₁_tend_h δ hδ
  have h_z₂_tend_h' : Filter.Tendsto z₂_h Filter.atTop (nhds τ_h) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    exact h_z₂_tend_h δ hδ
  have h_tend_left : Filter.Tendsto (fun k => γ_lim.val • z₁_h (φ k)) Filter.atTop
      (nhds (γ_lim.val • τ_h)) :=
    (h_cont.tendsto _).comp (h_z₁_tend_h'.comp hφ_mono.tendsto_atTop)
  have h_tend_right : Filter.Tendsto (fun k => z₂_h (φ k)) Filter.atTop (nhds τ_h) :=
    h_z₂_tend_h'.comp hφ_mono.tendsto_atTop
  have h_replace : (fun k => γ_lim.val • z₁_h (φ k)) = (fun k => z₂_h (φ k)) :=
    funext h_subseq_eq
  rw [h_replace] at h_tend_left
  have h_γ_fix : γ_lim.val • τ_h = τ_h :=
    tendsto_nhds_unique h_tend_left h_tend_right
  -- Pillar 1: γ_lim ∈ {I, -I}.
  have h_pm := gamma_two_fixed_point_implies_pm_one γ_lim.val γ_lim.property τ_h h_γ_fix
  -- ±I acts trivially: γ_lim • z = z. Contradicts h_subseq_ne for k = 0.
  have h_triv : γ_lim.val • z₁_h (φ 0) = z₁_h (φ 0) := by
    rcases h_pm with h | h
    · rw [h]; simp
    · rw [h]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp
  have h_contra : z₁_h (φ 0) = z₂_h (φ 0) := by
    rw [← h_subseq_eq 0, h_triv]
  exact h_subseq_ne 0 h_contra


/-- **Non-vanishing of `λ'` on the closed half-fundamental domain
`F`.** Case split on `F^o` vs `∂F`. For interior points, suppose
`deriv λ τ = 0`; by `analyticAt_localOpen_with_multiplicity` the
helper produces two distinct preimages `z₁ ≠ z₂` of some value
`w ≠ λ τ` inside a small ball `B(τ, ε) ⊆ F^o`, contradicting
`modularLambdaH_injOn_F_interior`. For boundary points,
`Im(λ τ) = 0` (from the three boundary real-value lemmas) so
`modularLambdaH_deriv_ne_zero_when_im_lambda_zero` applies
directly. -/
theorem modularLambdaH_deriv_ne_zero_on_F
    {τ : ℂ} (hτ_F : τ ∈ Gamma2FundamentalDomain) :
    deriv modularLambdaH τ ≠ 0 := by
  obtain ⟨hτ_im, hτ_re_nn, hτ_re_le, hτ_semicircle⟩ := hτ_F
  by_cases h_interior : τ ∈ Gamma2FundamentalDomainInterior
  · -- F^o case: use H_inj_F^o + multiplicity helper.
    intro h_dz
    -- λ analytic at τ.
    have hH_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    have h_lam_at : AnalyticAt ℂ modularLambdaH τ :=
      (modularLambdaH_differentiableOn.analyticOnNhd hH_open) τ hτ_im
    -- ℍ is preconnected (convex).
    have h_H_preconn : IsPreconnected {z : ℂ | 0 < z.im} := by
      apply Convex.isPreconnected
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
    have h_lam_an : AnalyticOnNhd ℂ modularLambdaH {z : ℂ | 0 < z.im} :=
      modularLambdaH_differentiableOn.analyticOnNhd hH_open
    have h_lam_not_const : ¬ ∀ᶠ z in nhds τ, modularLambdaH z = modularLambdaH τ := by
      intro h_eq
      have h_const_an : AnalyticOnNhd ℂ (fun _ : ℂ => modularLambdaH τ) {z : ℂ | 0 < z.im} :=
        fun _ _ => analyticAt_const
      have h_eqOn : Set.EqOn modularLambdaH (fun _ => modularLambdaH τ) {z : ℂ | 0 < z.im} :=
        h_lam_an.eqOn_of_preconnected_of_eventuallyEq h_const_an h_H_preconn hτ_im h_eq
      have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
        refine ⟨?_, ?_⟩
        · intro h; have := congrArg Complex.im h; simp at this
        · intro h; have := congrArg Complex.im h; simp at this
      have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
        refine ⟨?_, ?_⟩
        · intro h; have := congrArg Complex.im h; simp at this
        · intro h; have := congrArg Complex.re h; simp at this
      have h_lam_img : modularLambdaH '' {z : ℂ | 0 < z.im} = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } :=
        modularLambdaH_image
      have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' {z : ℂ | 0 < z.im} :=
        h_lam_img ▸ h_1i_in
      have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' {z : ℂ | 0 < z.im} :=
        h_lam_img ▸ h_2i_in
      obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
      obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
      have h_a := h_eqOn hτ_a_H
      have h_b := h_eqOn hτ_b_H
      rw [hτ_a_eq] at h_a
      rw [hτ_b_eq] at h_b
      have h_eq_12 : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := h_a.trans h_b.symm
      have h_re := congrArg Complex.re h_eq_12
      simp at h_re
    -- F^o is nhd of τ.
    have hF_open : IsOpen Gamma2FundamentalDomainInterior :=
      Gamma2FundamentalDomainInterior_isOpen
    have hF_nhds : Gamma2FundamentalDomainInterior ∈ nhds τ :=
      hF_open.mem_nhds h_interior
    -- Apply multiplicity helper.
    obtain ⟨V, hV_nhds, hV_prop⟩ :=
      analyticAt_localOpen_with_multiplicity h_lam_at h_lam_not_const h_dz
        Gamma2FundamentalDomainInterior hF_nhds
    -- Pick w ∈ V with w ≠ λ τ.
    rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨r, hr_pos, hr_sub⟩
    set w : ℂ := modularLambdaH τ + (r/2 : ℝ) with hw_def
    have h_dist_w : dist w (modularLambdaH τ) = r/2 := by
      rw [hw_def, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr_pos)]
    have hw_in_V : w ∈ V := by
      apply hr_sub
      rw [Metric.mem_ball, h_dist_w]; linarith
    have hw_ne : w ≠ modularLambdaH τ := by
      intro h_eq
      have h_re_eq : w.re = (modularLambdaH τ).re := congrArg Complex.re h_eq
      rw [hw_def, Complex.add_re, Complex.ofReal_re] at h_re_eq
      linarith
    obtain ⟨z_1, hz_1_in, z_2, hz_2_in, h_ne, h_lam_z_1, h_lam_z_2⟩ :=
      hV_prop w hw_in_V hw_ne
    -- z_1, z_2 ∈ F^o, λ(z_1) = λ(z_2). By H_inj_F^o, z_1 = z_2.
    have h_lam_eq : modularLambdaH z_1 = modularLambdaH z_2 := h_lam_z_1.trans h_lam_z_2.symm
    have h_z_eq : z_1 = z_2 :=
      modularLambdaH_injOn_F_interior hz_1_in hz_2_in h_lam_eq
    exact h_ne h_z_eq
  · -- ∂F case: τ ∈ F but not in F^o. Hence Im(λ τ) = 0 (boundary real-value).
    have h_im_lam_zero : (modularLambdaH τ).im = 0 := by
      by_cases h_re_zero : τ.re = 0
      · have h_τ_eq : τ = Complex.I * τ.im := by
          apply Complex.ext
          · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
          · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
        rw [h_τ_eq]
        exact modularLambdaH_pure_imag_real hτ_im
      · by_cases h_re_one : τ.re = 1
        · have h_τ_eq : τ = 1 + Complex.I * τ.im := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          rw [h_τ_eq]
          exact modularLambdaH_one_add_imag_real hτ_im
        · by_cases h_semicircle : ‖2 * τ - 1‖ = 1
          · exact modularLambdaH_semicircle_real hτ_im h_semicircle
          · -- All three boundary conditions strict: τ ∈ F^o, contradicting h_interior.
            exfalso
            apply h_interior
            refine ⟨hτ_im, ?_, ?_, ?_⟩
            · rcases lt_or_eq_of_le hτ_re_nn with h | h
              · exact h
              · exact absurd h.symm h_re_zero
            · rcases lt_or_eq_of_le hτ_re_le with h | h
              · exact h
              · exact absurd h h_re_one
            · rcases lt_or_eq_of_le hτ_semicircle with h | h
              · exact h
              · exact absurd h.symm h_semicircle
    exact modularLambdaH_deriv_ne_zero_when_im_lambda_zero hτ_im h_im_lam_zero

/-- **Möbius-derivative + upper branch for Pillar 3.** For
`τ ∈ ℍ` with `Im(λ τ) > 0`, `deriv λ τ ≠ 0`. Reduce `τ` to
`γ • τ ∈ F` via the half-FD property; apply
`modularLambdaH_deriv_ne_zero_on_F`; transport back along the
`Γ(2)`-orbit via the Möbius chain rule. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_pos
    {τ : ℂ} (hτ : 0 < τ.im)
    (h_im_pos : 0 < (modularLambdaH τ).im) :
    deriv modularLambdaH τ ≠ 0 := by
  set τ_h : UpperHalfPlane := ⟨τ, hτ⟩ with hτ_h_def
  have hlam_τ_h : 0 < (modularLambdaH (τ_h : ℂ)).im := h_im_pos
  obtain ⟨γ, hγ_in, hγτ_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ_h hlam_τ_h
  have h_deriv_γτ : deriv modularLambdaH ((γ • τ_h : UpperHalfPlane) : ℂ) ≠ 0 :=
    modularLambdaH_deriv_ne_zero_on_F hγτ_F
  set a : ℂ := (γ.val 0 0 : ℂ) with ha_def
  set b : ℂ := (γ.val 0 1 : ℂ) with hb_def
  set c : ℂ := (γ.val 1 0 : ℂ) with hc_def
  set d : ℂ := (γ.val 1 1 : ℂ) with hd_def
  have h_det : a * d - b * c = 1 := by
    have hγ_det := γ.2
    have : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
      have := Matrix.det_fin_two γ.val
      rw [hγ_det] at this
      linarith
    push_cast [ha_def, hb_def, hc_def, hd_def]
    exact_mod_cast this
  set Mob : ℂ → ℂ := fun z => (a * z + b) / (c * z + d) with hMob_def
  have h_smul_coe : ((γ • τ_h : UpperHalfPlane) : ℂ) = Mob τ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change ((((algebraMap ℤ ℝ) (γ.val 0 0)) : ℂ) * (τ_h : ℂ) +
        ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ)) /
        (((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) * (τ_h : ℂ) +
          ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ)) = Mob τ
    simp [hMob_def, ha_def, hb_def, hc_def, hd_def, hτ_h_def]
  have h_denom_ne : c * τ + d ≠ 0 := by
    intro h_eq
    have h_im_pos : 0 < ((γ • τ_h : UpperHalfPlane) : ℂ).im :=
      (γ • τ_h : UpperHalfPlane).2
    rw [h_smul_coe] at h_im_pos
    have h_Mob_undef : Mob τ = (a * τ + b) / 0 := by
      change (a * τ + b) / (c * τ + d) = (a * τ + b) / 0
      rw [h_eq]
    rw [h_Mob_undef] at h_im_pos
    simp at h_im_pos
  have h_Mob_deriv : HasDerivAt Mob (1 / (c * τ + d) ^ 2) τ := by
    have h_num : HasDerivAt (fun z : ℂ => a * z + b) a τ := by
      have := (hasDerivAt_id τ).const_mul a
      simpa using this.add_const b
    have h_den : HasDerivAt (fun z : ℂ => c * z + d) c τ := by
      have := (hasDerivAt_id τ).const_mul c
      simpa using this.add_const d
    have h_div : HasDerivAt Mob
        ((a * (c * τ + d) - (a * τ + b) * c) / (c * τ + d) ^ 2) τ := h_num.div h_den h_denom_ne
    have h_simpl : (a * (c * τ + d) - (a * τ + b) * c) / (c * τ + d) ^ 2
        = 1 / (c * τ + d) ^ 2 := by
      rw [div_eq_div_iff (pow_ne_zero 2 h_denom_ne) (pow_ne_zero 2 h_denom_ne)]
      linear_combination ((c * τ + d) ^ 2) * h_det
    rw [← h_simpl]
    exact h_div
  have hγτ_im_pos : 0 < ((γ • τ_h : UpperHalfPlane) : ℂ).im := (γ • τ_h).2
  have h_inv_local :
      ∀ᶠ z in nhds τ, modularLambdaH (Mob z) = modularLambdaH z := by
    have h_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    have hτ_mem : τ ∈ {z : ℂ | 0 < z.im} := hτ
    refine Filter.eventually_of_mem (h_open.mem_nhds hτ_mem) ?_
    intro z hz
    have hz_im : 0 < z.im := hz
    set z_h : UpperHalfPlane := ⟨z, hz_im⟩ with hz_h_def
    have h_inv_z := modularLambdaH_gamma2_invariant γ hγ_in z_h
    have h_smul_z_coe : ((γ • z_h : UpperHalfPlane) : ℂ) = Mob z := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      change ((((algebraMap ℤ ℝ) (γ.val 0 0)) : ℂ) * (z_h : ℂ) +
          ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ)) /
          (((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) * (z_h : ℂ) +
            ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ)) = Mob z
      simp [hMob_def, ha_def, hb_def, hc_def, hd_def, hz_h_def]
    rw [h_smul_z_coe] at h_inv_z
    exact h_inv_z
  have h_compose_deriv :
      deriv (fun z : ℂ => modularLambdaH (Mob z)) τ
        = deriv modularLambdaH (Mob τ) * (1 / (c * τ + d) ^ 2) := by
    have h_Mob_im_pos : 0 < (Mob τ).im := by
      have hh := (γ • τ_h : UpperHalfPlane).2
      rw [h_smul_coe] at hh
      exact hh
    have h_lam_diff_at_Mobτ : DifferentiableAt ℂ modularLambdaH (Mob τ) :=
      modularLambdaH_differentiableAt_of_im_pos h_Mob_im_pos
    have h_chain : HasDerivAt (fun z : ℂ => modularLambdaH (Mob z))
        (deriv modularLambdaH (Mob τ) * (1 / (c * τ + d) ^ 2)) τ :=
      (h_lam_diff_at_Mobτ.hasDerivAt).comp τ h_Mob_deriv
    exact h_chain.deriv
  have h_deriv_eq :
      deriv (fun z : ℂ => modularLambdaH (Mob z)) τ = deriv modularLambdaH τ :=
    Filter.EventuallyEq.deriv_eq h_inv_local
  rw [h_compose_deriv] at h_deriv_eq
  rw [h_smul_coe] at h_deriv_γτ
  intro h_zero
  rw [h_zero] at h_deriv_eq
  have h_factor_ne : (1 : ℂ) / (c * τ + d) ^ 2 ≠ 0 :=
    one_div_ne_zero (pow_ne_zero 2 h_denom_ne)
  have := h_deriv_eq.symm
  rw [eq_comm, mul_eq_zero] at this
  rcases this with h | h
  · exact h_deriv_γτ h
  · exact h_factor_ne h

/-- **Pillar-3 LHP `< 0` branch.** For `τ ∈ ℍ` with `Im(λ τ) < 0`,
`deriv λ τ ≠ 0`. Proof: pass to `τ' := -conj τ ∈ ℍ`; by
`modularLambdaH_conj_symmetry`, `λ τ' = conj(λ τ)` so
`Im(λ τ') > 0` and the upper branch gives `deriv λ τ' ≠ 0`. Define
`G(z) := conj(λ(-conj z))`; by the conjugation identity `G = λ`
locally on `ℍ`. Compute `deriv G τ = -conj(deriv λ τ')` via the
Wirtinger / FDeriv composition `conj ∘ λ ∘ negConj` over `ℝ`; the
two anti-holomorphic `conj` factors cancel algebraically so the
composition is the `ℝ`-linear map `h ↦ -conj(d) · h`, identified as
`(-conj d) • id_ℝ`. Convert this `ℝ`-FDeriv to a `ℂ`-derivative via
the `isLittleO` characterisation. Combined with
`deriv G τ = deriv λ τ` (EventuallyEq), conclude
`deriv λ τ = -conj(deriv λ τ') ≠ 0`. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_neg
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im < 0) :
    deriv modularLambdaH τ ≠ 0 := by
  -- τ' := -conj τ ∈ ℍ.
  have hτ' : 0 < (-(starRingEnd ℂ τ)).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ
  have h_lam_τ' :
      modularLambdaH (-(starRingEnd ℂ τ)) = starRingEnd ℂ (modularLambdaH τ) :=
    modularLambdaH_conj_symmetry hτ
  have h_im_pos' : 0 < (modularLambdaH (-(starRingEnd ℂ τ))).im := by
    rw [h_lam_τ', Complex.conj_im]; linarith
  -- Upper branch: deriv λ at τ' is non-zero.
  have hd_ne : deriv modularLambdaH (-(starRingEnd ℂ τ)) ≠ 0 :=
    modularLambdaH_deriv_ne_zero_when_im_lambda_pos hτ' h_im_pos'
  -- G(z) := conj(λ(-conj z)); G = λ locally at τ.
  have hG_eq_lam :
      (fun z => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) =ᶠ[nhds τ] modularLambdaH := by
    have h_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    filter_upwards [h_open.mem_nhds (show τ ∈ {z : ℂ | 0 < z.im} from hτ)] with z hz_im
    show starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z))) = modularLambdaH z
    rw [show modularLambdaH (-(starRingEnd ℂ z)) = starRingEnd ℂ (modularLambdaH z) from
        modularLambdaH_conj_symmetry hz_im, Complex.conj_conj]
  -- Abbreviate d := deriv λ τ'.
  set d : ℂ := deriv modularLambdaH (-(starRingEnd ℂ τ)) with hd_def
  -- HasFDerivAt for the three pieces (all `ℝ`-linear, avoiding `restrictScalars`).
  have h_negconj_fderiv : HasFDerivAt (fun z : ℂ => -(starRingEnd ℂ z))
      (-(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)) τ :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.neg
  have h_conj_fderiv : HasFDerivAt (fun w : ℂ => starRingEnd ℂ w)
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)
      (modularLambdaH (-(starRingEnd ℂ τ))) :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  -- `λ` has `ℝ`-FDeriv `d • (id ℝ ℂ)` at `-conj τ`. Bypass the `restrictScalars`
  -- type-class issue by constructing the `ℝ`-linear FDeriv directly via
  -- `hasFDerivAt_iff_isLittleO` from the underlying `HasDerivAt`.
  have h_lam_diff_at : DifferentiableAt ℂ modularLambdaH (-(starRingEnd ℂ τ)) :=
    modularLambdaH_differentiableAt_of_im_pos hτ'
  have h_lam_hasDeriv : HasDerivAt modularLambdaH d (-(starRingEnd ℂ τ)) :=
    h_lam_diff_at.hasDerivAt
  have h_lam_fderiv : HasFDerivAt modularLambdaH
      (d • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ))
      (-(starRingEnd ℂ τ)) := by
    rw [hasFDerivAt_iff_isLittleO]
    have h_o := h_lam_hasDeriv.isLittleO
    refine h_o.congr_left ?_
    intro y
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- Inner composition: λ ∘ negConj.
  have h_inner := h_lam_fderiv.comp τ h_negconj_fderiv
  -- Outer composition: conj ∘ (λ ∘ negConj).
  have h_outer := h_conj_fderiv.comp τ h_inner
  -- The `ℝ`-linear composition equals `(-conj d) • id_ℝ` by ring after
  -- pushing `conj` through products and using `conj_conj`.
  have h_comp_eq :
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp
        ((d • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)).comp
          (-(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ))) =
        (-(starRingEnd ℂ d)) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) := by
    ext h
    have h_cle : ∀ z : ℂ, (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) z = starRingEnd ℂ z :=
      fun _ => rfl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply, h_cle, smul_eq_mul]
    rw [map_mul, map_neg, Complex.conj_conj]
    ring
  rw [h_comp_eq] at h_outer
  -- Convert the `ℝ`-FDeriv with `(-conj d) • id_ℝ` to a `ℂ`-derivative.
  have hG_hasDeriv : HasDerivAt
      (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z))))
      (-(starRingEnd ℂ d)) τ := by
    rw [hasDerivAt_iff_isLittleO]
    have h_outer_o := h_outer.isLittleO
    refine h_outer_o.congr_left ?_
    intro y
    simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- deriv G τ = -conj d via chain rule.
  have h_deriv_G_chain :
      deriv (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) τ
        = -(starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ)))) :=
    hG_hasDeriv.deriv
  -- deriv G τ = deriv λ τ via EventuallyEq.
  have h_deriv_G_local :
      deriv (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) τ
        = deriv modularLambdaH τ :=
    hG_eq_lam.deriv_eq
  -- Conclude.
  intro h_zero
  rw [h_zero] at h_deriv_G_local
  rw [h_deriv_G_chain] at h_deriv_G_local
  -- h_deriv_G_local : -(starRingEnd ℂ (deriv λ (-conj τ))) = 0.
  have h_conjd_zero : starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ))) = 0 :=
    neg_eq_zero.mp h_deriv_G_local
  have h_d_zero : deriv modularLambdaH (-(starRingEnd ℂ τ)) = 0 := by
    have h_conj_conj :
        starRingEnd ℂ (starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ)))) =
          starRingEnd ℂ 0 := congr_arg _ h_conjd_zero
    rwa [Complex.conj_conj, map_zero] at h_conj_conj
  exact hd_ne h_d_zero
/-- **Pillar-3 LHP-and-boundary branch (dispatcher).** -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_non_pos
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im ≤ 0) :
    deriv modularLambdaH τ ≠ 0 := by
  rcases lt_or_eq_of_le hlam_im with h | h
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_neg hτ h
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_zero hτ h

/-- **Pillar-4 LHP branch (Im λ < 0).** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) < 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`.

Proof: pass to `τ_i' := -conj τ_i ∈ ℍ`; by
`modularLambdaH_conj_symmetry` we have `Im(λ τ_i') > 0` and
`λ(τ₁') = λ(τ₂')`. Apply the upper branch to obtain
`γ = ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∈ Γ(2)` with `γ • τ₁' = τ₂'`. Conjugating
both sides translates to `γ' • τ₁ = τ₂` for
`γ' := ⟨⟨a, -b⟩, ⟨-c, d⟩⟩`, also in `Γ(2)`. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_neg
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_neg : (modularLambdaH (τ₁ : ℂ)).im < 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have hτ₁_im : 0 < (τ₁ : ℂ).im := τ₁.2
  have hτ₂_im : 0 < (τ₂ : ℂ).im := τ₂.2
  -- Build τ_i' := -conj τ_i ∈ ℍ.
  have hτ₁'_im : 0 < (-(starRingEnd ℂ (τ₁ : ℂ))).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ₁_im
  have hτ₂'_im : 0 < (-(starRingEnd ℂ (τ₂ : ℂ))).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ₂_im
  set τ₁' : UpperHalfPlane := ⟨-(starRingEnd ℂ (τ₁ : ℂ)), hτ₁'_im⟩ with hτ₁'_def
  set τ₂' : UpperHalfPlane := ⟨-(starRingEnd ℂ (τ₂ : ℂ)), hτ₂'_im⟩ with hτ₂'_def
  have h_lam_τ₁' : modularLambdaH (τ₁' : ℂ) = starRingEnd ℂ (modularLambdaH (τ₁ : ℂ)) :=
    modularLambdaH_conj_symmetry hτ₁_im
  have h_lam_τ₂' : modularLambdaH (τ₂' : ℂ) = starRingEnd ℂ (modularLambdaH (τ₂ : ℂ)) :=
    modularLambdaH_conj_symmetry hτ₂_im
  have h_im_pos' : 0 < (modularLambdaH (τ₁' : ℂ)).im := by
    rw [h_lam_τ₁', Complex.conj_im]
    linarith
  have h_eq' : modularLambdaH (τ₁' : ℂ) = modularLambdaH (τ₂' : ℂ) := by
    rw [h_lam_τ₁', h_lam_τ₂', h_eq]
  obtain ⟨γ, hγ_in, hγ_eq⟩ :=
    gamma2_lambda_eq_implies_orbit_when_im_lambda_pos h_im_pos' h_eq'
  -- Build γ' = [[a, -b], [-c, d]] ∈ SL(2, ℤ).
  set γ'_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![γ.val 0 0, -γ.val 0 1; -γ.val 1 0, γ.val 1 1] with hγ'_mat_def
  have hγ'_det : γ'_mat.det = 1 := by
    simp only [hγ'_mat_def, Matrix.det_fin_two_of]
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    linarith
  set γ' : SL(2, ℤ) := ⟨γ'_mat, hγ'_det⟩ with hγ'_def
  have hγ'_in : γ' ∈ CongruenceSubgroup.Gamma 2 := by
    rw [CongruenceSubgroup.Gamma_mem]
    have hγ_mem : _ ∧ _ ∧ _ ∧ _ := CongruenceSubgroup.Gamma_mem.mp hγ_in
    obtain ⟨ha, hb, hc, hd⟩ := hγ_mem
    have h00' : γ'.val 0 0 = γ.val 0 0 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    have h01' : γ'.val 0 1 = -γ.val 0 1 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    have h10' : γ'.val 1 0 = -γ.val 1 0 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    have h11' : γ'.val 1 1 = γ.val 1 1 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h00']; exact ha
    · rw [h01']; push_cast; rw [hb]; ring
    · rw [h10']; push_cast; rw [hc]; ring
    · rw [h11']; exact hd
  refine ⟨γ', hγ'_in, ?_⟩
  apply UpperHalfPlane.ext
  -- The upper-branch identity in ℂ.
  have h_γ_eq_c : ((γ • τ₁' : UpperHalfPlane) : ℂ) = (τ₂' : ℂ) := by rw [hγ_eq]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h_γ_eq_c
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  -- γ' entries match γ with sign flips on b, c.
  have h00 : γ'.val 0 0 = γ.val 0 0 := by simp [hγ'_def, hγ'_mat_def]
  have h01 : γ'.val 0 1 = -γ.val 0 1 := by simp [hγ'_def, hγ'_mat_def]
  have h10 : γ'.val 1 0 = -γ.val 1 0 := by simp [hγ'_def, hγ'_mat_def]
  have h11 : γ'.val 1 1 = γ.val 1 1 := by simp [hγ'_def, hγ'_mat_def]
  rw [h00, h01, h10, h11]
  -- Abbreviate the real-cast entries.
  set a : ℂ := ((algebraMap ℤ ℝ) (γ.val 0 0) : ℂ) with ha_def
  set b : ℂ := ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ) with hb_def
  set c : ℂ := ((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) with hc_def
  set d : ℂ := ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ) with hd_def
  -- Negation through algebraMap.
  have hb_neg : ((algebraMap ℤ ℝ) (-γ.val 0 1) : ℂ) = -b := by push_cast; ring
  have hc_neg : ((algebraMap ℤ ℝ) (-γ.val 1 0) : ℂ) = -c := by push_cast; ring
  rw [hb_neg, hc_neg]
  -- Substitute τ_i' = -conj τ_i in h_γ_eq_c.
  have h_τ₁'_c_eq : (τ₁' : ℂ) = -(starRingEnd ℂ (τ₁ : ℂ)) := rfl
  have h_τ₂'_c_eq : (τ₂' : ℂ) = -(starRingEnd ℂ (τ₂ : ℂ)) := rfl
  rw [h_τ₁'_c_eq, h_τ₂'_c_eq] at h_γ_eq_c
  -- Take conjugate of the equation.
  have h_conj := congr_arg (starRingEnd ℂ) h_γ_eq_c
  simp only [map_div₀, map_add, map_mul, map_neg, Complex.conj_conj] at h_conj
  -- Conj of real-coerced values is itself.
  have hca : starRingEnd ℂ a = a := Complex.conj_ofReal _
  have hcb : starRingEnd ℂ b = b := Complex.conj_ofReal _
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  have hcd : starRingEnd ℂ d = d := Complex.conj_ofReal _
  rw [hca, hcb, hcc, hcd] at h_conj
  -- h_conj : (a * -(τ₁) + b) / (c * -(τ₁) + d) = -(τ₂).
  -- Goal: (a * τ₁ + -b) / (-c * τ₁ + d) = τ₂.
  -- Reduce to h_conj via numerator/denominator sign manipulation.
  have h_num_eq : a * (τ₁ : ℂ) + -b = -(a * -(τ₁ : ℂ) + b) := by ring
  have h_den_eq : -c * (τ₁ : ℂ) + d = c * -(τ₁ : ℂ) + d := by ring
  rw [h_num_eq, h_den_eq, neg_div, h_conj, neg_neg]

/-- **Orbit relation is closed.** The `Γ(2)`-orbit relation
`{(τ₁, τ₂) : ∃ γ ∈ Γ(2), γ • τ₁ = τ₂}` is closed in
`ℍ × ℍ`. Proof: take a convergent sequence
`(τ₁^n, τ₂^n) → (τ₁, τ₂)` with `γₙ • τ₁^n = τ₂^n`. Locally compact
neighbourhoods of `τ₁, τ₂` and `gamma_two_properlyDiscontinuousSMul`
restrict `γₙ` to a finite set; extract a subsequence with constant
`γₙ = γ`, take the limit using continuity of `γ•`, and conclude
`γ • τ₁ = τ₂`. -/
theorem gamma2_orbitRel_isClosed :
    IsClosed { p : UpperHalfPlane × UpperHalfPlane |
      ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • p.1 = p.2 } := by
  rw [← isSeqClosed_iff_isClosed]
  intro xn x h_in_n h_tendsto
  haveI := gamma_two_properlyDiscontinuousSMul
  -- Extract γₙ for each xₙ.
  choose γn hγn_in hγn_eq using h_in_n
  -- Compact closed balls around x.1, x.2.
  set K₁ : Set UpperHalfPlane := Metric.closedBall x.1 1 with hK₁_def
  set K₂ : Set UpperHalfPlane := Metric.closedBall x.2 1 with hK₂_def
  have hK₁_compact : IsCompact K₁ := isCompact_closedBall _ _
  have hK₂_compact : IsCompact K₂ := isCompact_closedBall _ _
  -- Convergence in each coordinate.
  have h_tendsto_1 : Filter.Tendsto (fun n => (xn n).1) Filter.atTop (nhds x.1) :=
    (continuous_fst.tendsto x).comp h_tendsto
  have h_tendsto_2 : Filter.Tendsto (fun n => (xn n).2) Filter.atTop (nhds x.2) :=
    (continuous_snd.tendsto x).comp h_tendsto
  rw [Metric.tendsto_atTop] at h_tendsto_1 h_tendsto_2
  obtain ⟨N₁, hN₁⟩ := h_tendsto_1 (1/2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := h_tendsto_2 (1/2) (by norm_num)
  set N : ℕ := max N₁ N₂ with hN_def
  -- Finite γ-set from proper discontinuity.
  set S : Set (↥(CongruenceSubgroup.Gamma 2)) :=
    { g | ((fun τ => g • τ) '' K₁ ∩ K₂).Nonempty } with hS_def
  have hS_finite : S.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK₁_compact hK₂_compact
  -- For n ≥ N, the lifted γn n lives in S.
  have h_γn_in_S : ∀ n, N ≤ n →
      (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) ∈ S := by
    intro n hn
    have h1 := hN₁ n (le_of_max_le_left hn)
    have h2 := hN₂ n (le_of_max_le_right hn)
    refine ⟨(xn n).2, ⟨(xn n).1, ?_, hγn_eq n⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr (le_trans h1.le (by norm_num))
    · exact Metric.mem_closedBall.mpr (le_trans h2.le (by norm_num))
  -- Pigeonhole: some γ ∈ S is hit infinitely often in (γn n)_{n ≥ N}.
  have h_pigeon : ∃ γ : ↥(CongruenceSubgroup.Gamma 2), γ ∈ S ∧
      {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ}.Infinite := by
    by_contra h_neg
    push Not at h_neg
    have h_ici_infinite : Set.Infinite (Set.Ici N) := Set.Ici_infinite N
    apply h_ici_infinite
    have h_eq : Set.Ici N =
        ⋃ γ ∈ S, {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} := by
      ext n
      simp only [Set.mem_Ici, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
      constructor
      · intro hn
        refine ⟨⟨γn n, hγn_in n⟩, h_γn_in_S n hn, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩
        exact hn
    rw [h_eq]
    apply hS_finite.biUnion
    intro γ hγ
    exact h_neg γ hγ
  -- Extract γ and infinite subsequence.
  obtain ⟨γ, _hγ_in_S, hγ_inf⟩ := h_pigeon
  -- Build a strictly increasing index sequence in the fiber.
  have h_seq : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, φ k ∈ {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} := by
    apply Nat.exists_strictMono_subsequence
    intro M
    obtain ⟨b, hb_in, hb_gt⟩ := hγ_inf.exists_gt M
    exact ⟨b, hb_gt, hb_in⟩
  obtain ⟨φ, hφ_mono, hφ_in⟩ := h_seq
  -- For each k: γn (φ k) = γ.val, so γ.val • (xn (φ k)).1 = (xn (φ k)).2.
  -- Take limit using continuity of γ.val•.
  refine ⟨γ.val, γ.property, ?_⟩
  -- γ.val • x.1 = x.2: use continuity.
  have h_cont : Continuous (fun τ : UpperHalfPlane => γ.val • τ) := by
    change Continuous (fun τ : UpperHalfPlane => ((γ.val : SL(2, ℝ)) • τ))
    exact continuous_const_smul _
  have h_tend1 : Filter.Tendsto (fun n => (xn n).1) Filter.atTop (nhds x.1) :=
    (continuous_fst.tendsto x).comp h_tendsto
  have h_tend2 : Filter.Tendsto (fun n => (xn n).2) Filter.atTop (nhds x.2) :=
    (continuous_snd.tendsto x).comp h_tendsto
  have h_tendsto_left : Filter.Tendsto (fun k => γ.val • (xn (φ k)).1) Filter.atTop
      (nhds (γ.val • x.1)) :=
    (h_cont.tendsto _).comp (h_tend1.comp hφ_mono.tendsto_atTop)
  have h_tendsto_right : Filter.Tendsto (fun k => (xn (φ k)).2) Filter.atTop (nhds x.2) :=
    h_tend2.comp hφ_mono.tendsto_atTop
  -- For each k: γ.val • (xn (φ k)).1 = (xn (φ k)).2.
  have h_eq_seq : ∀ k, γ.val • (xn (φ k)).1 = (xn (φ k)).2 := by
    intro k
    have hk_in : φ k ∈ {n | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} :=
      hφ_in k
    have h_γ_eq : γn (φ k) = γ.val := by
      have := hk_in.2
      exact congrArg Subtype.val this
    rw [← h_γ_eq]
    exact hγn_eq (φ k)
  have h_replace : (fun k => γ.val • (xn (φ k)).1) = (fun k => (xn (φ k)).2) :=
    funext h_eq_seq
  rw [h_replace] at h_tendsto_left
  exact tendsto_nhds_unique h_tendsto_left h_tendsto_right

/-- **Density of upper `λ`-fibre at the boundary.** For
`(τ₁, τ₂) ∈ ℍ × ℍ` with `λ(τ₁) = λ(τ₂)` and `Im(λ τ₁) = 0` (the
boundary case), every neighbourhood of `(τ₁, τ₂)` in `ℍ × ℍ`
contains some `(τ₁', τ₂')` with `λ(τ₁') = λ(τ₂')` and
`Im(λ τ₁') > 0`. Proof: the open mapping theorem
(`AnalyticAt.eventually_constant_or_nhds_le_map_nhds` applied to `λ`
at `τ₁, τ₂`) gives `λ(D₁) ∩ λ(D₂)` as a neighbourhood of
`λ(τ₁) = λ(τ₂)` for any small balls `D₁, D₂`. With `Im λ τ₁ = 0`,
the open neighbourhood intersects `{Im > 0}`; pick `v` there and
pull back to `τ₁' ∈ D₁`, `τ₂' ∈ D₂`. -/
theorem modularLambdaH_eq_fibre_dense_in_im_lambda_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_zero : (modularLambdaH (τ₁ : ℂ)).im = 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ))
    (U : Set (UpperHalfPlane × UpperHalfPlane))
    (hU : U ∈ nhds (τ₁, τ₂)) :
    ∃ p ∈ U, modularLambdaH (p.1 : ℂ) = modularLambdaH (p.2 : ℂ) ∧
      0 < (modularLambdaH (p.1 : ℂ)).im := by
  -- Get product nhd V₁ ×ˢ V₂ ⊆ U.
  obtain ⟨V₁, hV₁, V₂, hV₂, hV_sub⟩ := mem_nhds_prod_iff.mp hU
  -- Set H := {z : ℂ | 0 < z.im}, open.
  set H : Set ℂ := {z : ℂ | 0 < z.im} with hH_def
  have hH_open : IsOpen H := by
    have : H = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp [hH_def]
    rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
  have hH_preconn : IsPreconnected H := by
    apply Convex.isPreconnected
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
  -- λ is analytic on H.
  have h_lam_analytic : AnalyticOnNhd ℂ modularLambdaH H :=
    modularLambdaH_differentiableOn.analyticOnNhd hH_open
  -- λ has different values: 1+i and 2+i are both in image (in ℂ ∖ {0, 1}).
  have h_lam_not_const : ¬ Set.EqOn modularLambdaH (fun _ => modularLambdaH (τ₁ : ℂ)) H := by
    intro h_eqOn
    -- Use modularLambdaH_image to find τ_a, τ_b with different λ-values.
    have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.im h; simp at this
    have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.re h; simp at this
    have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' H := by
      rw [modularLambdaH_image]; exact h_1i_in
    have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' H := by
      rw [modularLambdaH_image]; exact h_2i_in
    obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
    obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
    have h_eq_a : modularLambdaH τ_a = modularLambdaH (τ₁ : ℂ) := h_eqOn hτ_a_H
    have h_eq_b : modularLambdaH τ_b = modularLambdaH (τ₁ : ℂ) := h_eqOn hτ_b_H
    have : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := by
      rw [← hτ_a_eq, ← hτ_b_eq, h_eq_a, h_eq_b]
    have h_re := congrArg Complex.re this
    simp at h_re
  -- λ is not eventually constant at (τ₁ : ℂ).
  have hτ₁_in_H : (τ₁ : ℂ) ∈ H := τ₁.2
  have hτ₂_in_H : (τ₂ : ℂ) ∈ H := τ₂.2
  have h_not_evt_const_at_τ₁ : ¬ (∀ᶠ z in nhds (τ₁ : ℂ),
      modularLambdaH z = modularLambdaH (τ₁ : ℂ)) := by
    intro h_evt
    apply h_lam_not_const
    exact h_lam_analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hH_preconn
      hτ₁_in_H h_evt
  have h_not_evt_const_at_τ₂ : ¬ (∀ᶠ z in nhds (τ₂ : ℂ),
      modularLambdaH z = modularLambdaH (τ₂ : ℂ)) := by
    intro h_evt
    apply h_lam_not_const
    have h_lam_analytic_const : AnalyticOnNhd ℂ (fun _ => modularLambdaH (τ₁ : ℂ)) H :=
      analyticOnNhd_const
    -- λ =ᶠ const-at-τ₂ at τ₂, but const-at-τ₂ = const-at-τ₁ (h_eq).
    have h_evt' : ∀ᶠ z in nhds (τ₂ : ℂ), modularLambdaH z = modularLambdaH (τ₁ : ℂ) := by
      filter_upwards [h_evt] with z hz
      rw [hz]; exact h_eq.symm
    exact h_lam_analytic.eqOn_of_preconnected_of_eventuallyEq h_lam_analytic_const hH_preconn
      hτ₂_in_H h_evt'
  -- Apply open mapping at τ₁ and τ₂.
  have h_lam_at_τ₁ : AnalyticAt ℂ modularLambdaH (τ₁ : ℂ) :=
    h_lam_analytic _ hτ₁_in_H
  have h_lam_at_τ₂ : AnalyticAt ℂ modularLambdaH (τ₂ : ℂ) :=
    h_lam_analytic _ hτ₂_in_H
  have h_open_τ₁ : nhds (modularLambdaH (τ₁ : ℂ)) ≤ Filter.map modularLambdaH (nhds (τ₁ : ℂ)) :=
    (h_lam_at_τ₁.eventually_constant_or_nhds_le_map_nhds).resolve_left h_not_evt_const_at_τ₁
  have h_open_τ₂ : nhds (modularLambdaH (τ₂ : ℂ)) ≤ Filter.map modularLambdaH (nhds (τ₂ : ℂ)) :=
    (h_lam_at_τ₂.eventually_constant_or_nhds_le_map_nhds).resolve_left h_not_evt_const_at_τ₂
  -- Bridge V_i to nhd in ℂ via open embedding.
  have hW₁_nhd : ((↑) : UpperHalfPlane → ℂ) '' V₁ ∈ nhds (τ₁ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ₁).symm ▸ Filter.image_mem_map hV₁
  have hW₂_nhd : ((↑) : UpperHalfPlane → ℂ) '' V₂ ∈ nhds (τ₂ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ₂).symm ▸ Filter.image_mem_map hV₂
  -- λ(W_i) is a nhd of λ τ_i.
  have h_lamW₁_nhd : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∈
      nhds (modularLambdaH (τ₁ : ℂ)) :=
    h_open_τ₁ (Filter.image_mem_map hW₁_nhd)
  have h_lamW₂_nhd : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
      nhds (modularLambdaH (τ₂ : ℂ)) :=
    h_open_τ₂ (Filter.image_mem_map hW₂_nhd)
  -- λ(W₁) ∩ λ(W₂) is a nhd of λ τ_1 (= λ τ_2).
  have h_inter_nhd :
      modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∩
        modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
      nhds (modularLambdaH (τ₁ : ℂ)) := by
    have h_lamW₂_nhd' : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
        nhds (modularLambdaH (τ₁ : ℂ)) := h_eq ▸ h_lamW₂_nhd
    exact Filter.inter_mem h_lamW₁_nhd h_lamW₂_nhd'
  -- {Im > 0} ∩ (nhd of λ τ_1) is non-empty since Im(λ τ_1) = 0.
  have h_im_pos_nhd : ∃ v ∈ modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∩
        modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂), 0 < v.im := by
    -- Take open ball around λ τ_1 small enough inside the inter nhd; pick a point with Im > 0.
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp h_inter_nhd
    refine ⟨modularLambdaH (τ₁ : ℂ) + (ε/2 : ℝ) * Complex.I, ?_, ?_⟩
    · apply hε_ball
      rw [Metric.mem_ball, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε/2)]
      linarith
    · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, h_im_zero]
      linarith
  obtain ⟨v, hv_inter, hv_im⟩ := h_im_pos_nhd
  -- Pull back v to τ_1' ∈ V_1 and τ_2' ∈ V_2.
  obtain ⟨hv₁_in, hv₂_in⟩ := hv_inter
  obtain ⟨z₁, ⟨τ₁', hτ₁'_V, rfl⟩, h_lam_z₁⟩ := hv₁_in
  obtain ⟨z₂, ⟨τ₂', hτ₂'_V, rfl⟩, h_lam_z₂⟩ := hv₂_in
  -- The witness pair.
  refine ⟨(τ₁', τ₂'), hV_sub ⟨hτ₁'_V, hτ₂'_V⟩, ?_, ?_⟩
  · change modularLambdaH (τ₁' : ℂ) = modularLambdaH (τ₂' : ℂ)
    rw [h_lam_z₁, h_lam_z₂]
  · change 0 < (modularLambdaH (τ₁' : ℂ)).im
    rw [h_lam_z₁]; exact hv_im

/-- **Pillar-4 boundary branch (Im λ = 0).** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) = 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Closes via density (`modularLambdaH_eq_fibre_dense_in_im_lambda_pos`)
of the upper `λ`-fibre + closedness of the orbit relation
(`gamma2_orbitRel_isClosed`) + the upper branch
`gamma2_lambda_eq_implies_orbit_when_im_lambda_pos`. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_zero
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_zero : (modularLambdaH (τ₁ : ℂ)).im = 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  -- The orbit relation R, the target set of (τ₁, τ₂).
  set R : Set (UpperHalfPlane × UpperHalfPlane) :=
    { p | ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • p.1 = p.2 } with hR_def
  change (τ₁, τ₂) ∈ R
  have hR_closed : IsClosed R := gamma2_orbitRel_isClosed
  rw [← hR_closed.closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨p, hp_U, hp_eq, hp_im⟩ :=
    modularLambdaH_eq_fibre_dense_in_im_lambda_pos h_im_zero h_eq U hU
  exact ⟨p, hp_U, gamma2_lambda_eq_implies_orbit_when_im_lambda_pos hp_im hp_eq⟩

/-- **Pillar-4 LHP-and-boundary branch.** Combination of the
`Im(λ) < 0` and `Im(λ) = 0` cases. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_non_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_le : (modularLambdaH (τ₁ : ℂ)).im ≤ 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  rcases lt_or_eq_of_le h_im_le with h_lt | h_eq_zero
  · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_neg h_lt h_eq
  · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_zero h_eq_zero h_eq

/-! ## Pillar 3: non-vanishing of the derivative -/

/-- **Pillar 3: `λ'(τ) ≠ 0` for every `τ ∈ ℍ`.** Case split on the
sign of `Im(λ τ)`. -/
theorem modularLambdaH_deriv_ne_zero_on_upperHalf
    {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambdaH τ ≠ 0 := by
  rcases le_or_gt (modularLambdaH τ).im 0 with h_im_le | h_im_pos
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_non_pos hτ h_im_le
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_pos hτ h_im_pos

/-! ## Pillar 4: orbit identification -/

/-- **Pillar 4: `λ` separates `Γ(2)`-orbits.** Case split on the
sign of `Im(λ τ₁)` (which equals `Im(λ τ₂)` by hypothesis). -/
theorem modularLambdaH_eq_iff_gamma2_orbit
    {τ₁ τ₂ : UpperHalfPlane} :
    modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ) ↔
      ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  constructor
  · intro h_eq
    rcases le_or_gt (modularLambdaH (τ₁ : ℂ)).im 0 with h_im_le | h_im_pos
    · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_non_pos h_im_le h_eq
    · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_pos h_im_pos h_eq
  · rintro ⟨γ, hγ_in, h_eq⟩
    rw [← h_eq]
    exact (modularLambdaH_gamma2_invariant γ hγ_in τ₁).symm

/-! ## Main covering-map theorems -/

/-- **Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`.** -/
theorem modularLambdaH_isCoveringMapOn :
    IsCoveringMapOn modularLambdaH { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

/-- **Covering property of `λ` on the unit disk.** -/
theorem modularLambda_isCoveringMapOn :
    IsCoveringMapOn modularLambda { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  sorry

end RiemannDynamics

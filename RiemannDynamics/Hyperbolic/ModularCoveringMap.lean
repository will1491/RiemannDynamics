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

/-- **Half-FD existence (upper branch).** Every `τ ∈ ℍ` with
`Im(λ τ) > 0` has a `Γ(2)`-translate in the half-fundamental domain
`F`. -/
theorem gamma2_orbit_meets_F_when_im_lambda_pos (τ : UpperHalfPlane)
    (hτ_pos : 0 < (modularLambdaH (τ : ℂ)).im) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2,
      ((γ • τ : UpperHalfPlane) : ℂ) ∈ Gamma2FundamentalDomain := by
  sorry

/-- **Injectivity of `λ` on `F` modulo `Γ(2)`.** For
`τ₁, τ₂ ∈ F ⊂ ℍ` with `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. -/
theorem modularLambdaH_injOn_F_mod_gamma2
    {τ₁ τ₂ : UpperHalfPlane}
    (h₁ : (τ₁ : ℂ) ∈ Gamma2FundamentalDomain)
    (h₂ : (τ₂ : ℂ) ∈ Gamma2FundamentalDomain)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  sorry

/-- **Non-vanishing of `λ'` on the closed half-fundamental domain
`F`.** -/
theorem modularLambdaH_deriv_ne_zero_on_F
    {τ : ℂ} (hτ_F : τ ∈ Gamma2FundamentalDomain) :
    deriv modularLambdaH τ ≠ 0 := by
  sorry

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

/-- **Pillar-3 LHP-and-boundary branch.** For `τ ∈ ℍ` with
`Im(λ τ) ≤ 0` (lower half-plane or the real axis), `deriv λ τ ≠ 0`.
The `Im(λ) < 0` case mirrors the upper branch across the imaginary
axis (via `modularLambdaH_conj_symmetry`); the `Im(λ) = 0` boundary
case is handled by Schwarz reflection along the real-axis pre-image
arcs. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_non_pos
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im ≤ 0) :
    deriv modularLambdaH τ ≠ 0 := by
  sorry

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
  sorry

/-- **Pillar-4 boundary branch (Im λ = 0).** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) = 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Boundary case: the `λ-image` is real, so both
`τ₁, τ₂` lie on the `Γ(2)`-translates of the three boundary arcs of
`F`. Uses Schwarz reflection plus the proper-discontinuity sequential
extraction. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_zero
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_zero : (modularLambdaH (τ₁ : ℂ)).im = 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  sorry

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

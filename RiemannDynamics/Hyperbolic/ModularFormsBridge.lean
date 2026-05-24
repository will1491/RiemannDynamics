/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.Delta
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Geometry.Manifold.Notation

/-!
# Modular forms bridge: from generator-level data to `Mathlib.CuspForm`

The Mathlib `CuspForm Γ(1) k` structure carries slash invariance under
every `γ ∈ SL(2, ℤ)`, manifold differentiability, and zero-at-cusp.
Our project's "weight-`k` cusp form" data — coming from work on the
modular function `λ` and Jacobi's identity — naturally surfaces only
the two generator-level slash relations (under `S` and `T`), the
standard `DifferentiableOn ℂ` holomorphy on the upper half-plane, and
an explicit exponential decay at `+i∞`. This file bridges the two
APIs.

The eventual consumer is `holomorphic_weight4_modform_cusp_vanishes`
in `ModularFunction.lean`, which closes the deferred Jacobi identity
sorry once a bundled `CuspForm Γ(1) 4` is in hand. The classical
endpoint `dim S_4(SL(2, ℤ)) = 0` is captured here as
`weight4_levelOne_cuspForm_vanishes`, an architectural sorry pending
the `Δ`-division route (or any equivalent dimension argument).
-/

namespace RiemannDynamics

open ModularForm UpperHalfPlane CongruenceSubgroup Complex Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold

/-- **Slash invariance from the generators `S, T`.** Since
`SpecialLinearGroup.SL2Z_generators` shows `Subgroup.closure {S, T} = ⊤`
in `SL(2, ℤ)`, any weight-`k` slash invariance under both `S` and `T`
propagates by `Subgroup.closure_induction` to every `γ ∈ SL(2, ℤ)`. -/
theorem slashInvariant_via_S_T_in_SL2Z {f : ℍ → ℂ} {k : ℤ}
    (h_S : f ∣[k] ModularGroup.S = f)
    (h_T : f ∣[k] ModularGroup.T = f)
    (γ : SL(2, ℤ)) :
    f ∣[k] γ = f := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | one => exact SlashAction.slash_one _ _
  | mem g hg =>
    rcases hg with h1 | h2
    · rw [h1]; exact h_S
    · rw [h2]; exact h_T
  | mul g h _ _ ig ih =>
    rw [SlashAction.slash_mul, ig, ih]
  | inv g _ ig =>
    have key : (f ∣[k] g) ∣[k] g⁻¹ = f ∣[k] g⁻¹ := by rw [ig]
    rwa [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, eq_comm] at key

/-- **`T`-slash of a `T`-invariant function on `ℍ`.** If `g : ℂ → ℂ`
satisfies `g(τ + 1) = g(τ)` on the upper half-plane, then the
restriction `g_H σ = g σ` satisfies `g_H ∣[k] T = g_H` as a function
`ℍ → ℂ`. -/
theorem slash_T_eq_of_T_invariant {g : ℂ → ℂ} {k : ℤ}
    (h_T : ∀ τ : ℂ, 0 < τ.im → g (τ + 1) = g τ) :
    (fun σ : ℍ => g (↑σ : ℂ)) ∣[k] ModularGroup.T
      = (fun σ : ℍ => g (↑σ : ℂ)) := by
  funext σ
  rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul,
      UpperHalfPlane.coe_vadd]
  -- Goal: g (↑(1 : ℝ) + ↑σ) * denom T σ ^ (-k) = g ↑σ.
  -- denom T σ = 1, so the `(denom T σ) ^ (-k)` factor is 1.
  have h_denom : denom ModularGroup.T σ = 1 := by
    simp [denom, ModularGroup.T]
  rw [h_denom, one_zpow, mul_one]
  -- Goal: g (↑(1 : ℝ) + ↑σ) = g ↑σ.  Cast ↑(1 : ℝ) → 1, then apply h_T.
  rw [show ((1 : ℝ) : ℂ) + (↑σ : ℂ) = (↑σ : ℂ) + 1 from by push_cast; ring]
  exact h_T _ σ.2

/-- **`S`-slash of a `weight-k`-`S`-form.** If `g : ℂ → ℂ` satisfies
`g(-1/τ) = τ^k · g(τ)` on the upper half-plane, then the restriction
`g_H` satisfies `g_H ∣[k] S = g_H` as a function `ℍ → ℂ`. -/
theorem slash_S_eq_of_S_weight_k {g : ℂ → ℂ} {k : ℤ}
    (h_S : ∀ τ : ℂ, 0 < τ.im → g (-1 / τ) = τ ^ k * g τ) :
    (fun σ : ℍ => g (↑σ : ℂ)) ∣[k] ModularGroup.S
      = (fun σ : ℍ => g (↑σ : ℂ)) := by
  funext σ
  have h_σ_ne : (↑σ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero σ
  have h_σ_pos : 0 < (↑σ : ℂ).im := σ.2
  -- Rewrite slash + S-smul; then handle denom and the substituted argument.
  suffices h_main : g ((-(↑σ : ℂ))⁻¹) * denom ModularGroup.S σ ^ (-k) = g (↑σ : ℂ) by
    rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_S_smul]
    exact h_main
  have h_denom : denom ModularGroup.S σ = (↑σ : ℂ) := by
    simp [denom, ModularGroup.S]
  have h_arg : (-(↑σ : ℂ))⁻¹ = -1 / (↑σ : ℂ) := by field_simp
  rw [h_arg, h_S _ h_σ_pos, h_denom]
  rw [show (↑σ : ℂ) ^ k * g (↑σ : ℂ) * (↑σ : ℂ) ^ (-k)
      = g (↑σ : ℂ) * ((↑σ : ℂ) ^ k * (↑σ : ℂ) ^ (-k)) from by ring]
  rw [← zpow_add₀ h_σ_ne, add_neg_cancel, zpow_zero, mul_one]

/-- **Manifold differentiability from `DifferentiableOn ℂ` on `ℍ`.**
The restriction of a function holomorphic on `{τ | 0 < τ.im}` is
manifold-differentiable on `ℍ`. -/
theorem mdiff_of_differentiableOn_upperHalfPlane {g : ℂ → ℂ}
    (h_holo : DifferentiableOn ℂ g { τ : ℂ | 0 < τ.im }) :
    MDiff (fun σ : ℍ => g (↑σ : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine h_holo.congr ?_
  intro z hz
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- **Cusp vanishing from exponential decay.** A function on `ℍ` whose
underlying values decay like `exp(-π · τ.im)` at `+i∞` is zero at
`atImInfty`. -/
theorem isZeroAtImInfty_of_exp_decay {g : ℂ → ℂ}
    (h_cusp : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℂ, 1 ≤ τ.im →
        ‖g τ‖ ≤ C * Real.exp (-Real.pi * τ.im)) :
    IsZeroAtImInfty (fun σ : ℍ => g (↑σ : ℂ)) := by
  obtain ⟨C, hC_pos, h_bound⟩ := h_cusp
  -- `IsZeroAtImInfty f = Filter.Tendsto f atImInfty (𝓝 0)`.
  -- For `σ.im ≥ 1`, `‖g ↑σ‖ ≤ C · exp(-π · σ.im) → 0` as `σ.im → ∞`.
  rw [show IsZeroAtImInfty (fun σ : ℍ => g (↑σ : ℂ))
        ↔ Filter.Tendsto (fun σ : ℍ => g (↑σ : ℂ)) atImInfty (nhds 0) from Iff.rfl]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- Show `‖g ↑σ‖ → 0` as `σ.im → ∞`, by squeezing between 0 and `C * exp(-π · σ.im)`.
  have h_bound_ev : ∀ᶠ σ : ℍ in atImInfty,
      ‖g (↑σ : ℂ)‖ ≤ C * Real.exp (-Real.pi * σ.im) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{σ : ℍ | 1 ≤ σ.im}, ?_, fun σ hσ => h_bound (↑σ : ℂ) hσ⟩
    rw [atImInfty_mem]
    exact ⟨1, fun _ h => h⟩
  have h_rhs_tend : Filter.Tendsto (fun σ : ℍ => C * Real.exp (-Real.pi * σ.im))
      atImInfty (nhds 0) := by
    have h_tend_im : Filter.Tendsto (fun σ : ℍ => σ.im) atImInfty Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro A
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨{σ : ℍ | A ≤ σ.im}, ?_, fun _ hσ => hσ⟩
      rw [atImInfty_mem]
      exact ⟨A, fun _ hσ => hσ⟩
    have h_neg_pi : Filter.Tendsto (fun σ : ℍ => -Real.pi * σ.im)
        atImInfty Filter.atBot := by
      simpa using h_tend_im.const_mul_atTop_of_neg (show -Real.pi < 0 by
        simpa using Real.pi_pos)
    have h_exp : Filter.Tendsto (fun σ : ℍ => Real.exp (-Real.pi * σ.im))
        atImInfty (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_neg_pi
    simpa using h_exp.const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    h_bound_ev h_rhs_tend

/-! ### Bundling `Δ` as a Mathlib `CuspForm`

Mathlib provides `delta : ℍ → ℂ` along with `delta_T_invariant`,
`delta_S_invariant`, `delta_ne_zero`, and the q-product expansion
`delta_eq_q_prod`, but does not bundle the discriminant as a
`CuspForm Γ(1) 12`. We do so here. The three components are:
- Slash invariance for every `γ ∈ SL(2, ℤ)`, closed via the
  generator-level invariances and `slashInvariant_via_S_T_in_SL2Z`.
- Manifold holomorphy `MDiff delta` (deferred — needs
  `MDiff` on `eta z ^ 24` from Mathlib's η-machinery).
- Vanishing at every cusp, reduced to `IsZeroAtImInfty delta` via
  the `IsArithmetic` cusp-iff-SL2Z lemma + slash invariance. The
  `IsZeroAtImInfty delta` step is itself deferred — it follows from
  the leading `q¹` factor in the q-expansion `Δ = q · ∏(1 − qⁿ)²⁴`. -/

/-- The slash-action equation for `delta` under every `γ ∈ SL(2, ℤ)`,
extending the two-generator invariance via `SL2Z_generators`. -/
theorem delta_slash_action_eq (γ : SL(2, ℤ)) :
    delta ∣[(12 : ℤ)] γ = delta :=
  slashInvariant_via_S_T_in_SL2Z delta_S_invariant delta_T_invariant γ

/-- Manifold holomorphy of `delta : ℍ → ℂ`. Follows from
`Δ = η²⁴` and the Mathlib `differentiableAt_eta_of_mem_upperHalfPlaneSet`. -/
theorem delta_mdiff : MDiff (delta : ℍ → ℂ) := by
  have h_eta : MDiff (fun τ : ℍ => η (↑τ : ℂ)) := fun τ =>
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
      (z := (↑τ : ℂ)) τ.2).mdifferentiableAt.comp τ (UpperHalfPlane.mdifferentiable_coe τ)
  have h_pow : MDiff (fun τ : ℍ => (η (↑τ : ℂ)) ^ 24) := by
    simpa [Pi.pow_apply] using h_eta.pow 24
  exact h_pow

/-- **Boundedness of the eta-related product `∏(1 − qⁿ)` near `+i∞`.**
For `τ.im ≥ 1`, the infinite product `∏' n, (1 − eta_q n τ)` is
uniformly bounded by a constant `M`. The proof uses
`Finset.norm_prod_one_add_sub_one_le` (giving the partial product
bound `‖∏(1 + fᵢ) − 1‖ ≤ exp(∑‖fᵢ‖) − 1`) applied to `fᵢ = -eta_q i τ`,
passed to the infinite limit via `Multipliable.norm_tprod` and the
geometric sum `∑' n, exp(−2π(n+1)·τ.im) ≤ exp(−2π)/(1 − exp(−2π))`. -/
theorem tprod_norm_one_sub_eta_q_le :
    ∃ M : ℝ, 0 < M ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖∏' n : ℕ, (1 - eta_q n τ)‖ ≤ M := by
  sorry

/-- **Exponential decay bound for `delta` near the cusp.** For
`τ.im ≥ 1`, the discriminant `delta τ = q · ∏(1 − qⁿ)²⁴` satisfies
`‖delta τ‖ ≤ C · exp(−2π · τ.im)` for `C = M²⁴` where `M` is the
product bound from `tprod_norm_one_sub_eta_q_le`. The factor
`exp(−2π · τ.im) = ‖𝕢 1 τ‖` comes from `Function.Periodic.norm_qParam`. -/
theorem delta_norm_le_exp_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖delta τ‖ ≤ C * Real.exp (-2 * Real.pi * τ.im) := by
  obtain ⟨M, hM_pos, hM_bound⟩ := tprod_norm_one_sub_eta_q_le
  refine ⟨M ^ 24, by positivity, ?_⟩
  intro τ hτ_im
  have h_summ : Summable fun n : ℕ => ‖-eta_q n (↑τ : ℂ)‖ := by
    simpa using summable_eta_q τ
  have h_mul : Multipliable fun n : ℕ => 1 + (-eta_q n (↑τ : ℂ)) :=
    multipliable_one_add_of_summable h_summ
  have h_mul' : Multipliable fun n : ℕ => 1 - eta_q n (↑τ : ℂ) := by
    have h_eq : (fun n : ℕ => (1 : ℂ) - eta_q n (↑τ : ℂ))
        = fun n : ℕ => 1 + (-eta_q n (↑τ : ℂ)) := by funext n; ring
    rw [h_eq]; exact h_mul
  -- `∏'((1 - eta_q n τ)^24) = (∏'(1 - eta_q n τ))^24`.
  have h_tprod_pow : ∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ)) ^ 24
      = (∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))) ^ 24 :=
    h_mul'.tprod_pow 24
  rw [delta_eq_q_prod, h_tprod_pow, norm_mul, norm_pow]
  -- `‖𝕢 1 τ‖ = exp(-2π τ.im)`.
  rw [Function.Periodic.norm_qParam]
  have h_div_one : Real.exp (-2 * Real.pi * (↑τ : ℂ).im / 1)
      = Real.exp (-2 * Real.pi * τ.im) := by
    rw [div_one]; rfl
  rw [h_div_one]
  have h_prod_nn : 0 ≤ ‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ := norm_nonneg _
  have h_pow_le : ‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ ^ 24 ≤ M ^ 24 :=
    pow_le_pow_left₀ h_prod_nn (hM_bound τ hτ_im) 24
  have h_exp_pos' : 0 < Real.exp (-2 * Real.pi * τ.im) := Real.exp_pos _
  calc Real.exp (-2 * Real.pi * τ.im) * ‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ ^ 24
      ≤ Real.exp (-2 * Real.pi * τ.im) * M ^ 24 :=
        mul_le_mul_of_nonneg_left h_pow_le h_exp_pos'.le
    _ = M ^ 24 * Real.exp (-2 * Real.pi * τ.im) := by ring

/-- `delta : ℍ → ℂ` is zero at the cusp `+i∞`: this is the leading
`q¹` behaviour in the q-expansion `Δ = q · ∏(1 − qⁿ)²⁴`. The proof
combines the explicit exponential decay bound `delta_norm_le_exp_decay`
with a squeeze using `Real.tendsto_exp_atBot`. -/
theorem delta_isZeroAtImInfty : IsZeroAtImInfty (delta : ℍ → ℂ) := by
  obtain ⟨C, hC_pos, h_bound⟩ := delta_norm_le_exp_decay
  rw [show IsZeroAtImInfty (delta : ℍ → ℂ)
        ↔ Filter.Tendsto (delta : ℍ → ℂ) atImInfty (nhds 0) from Iff.rfl]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_bound_ev : ∀ᶠ τ : ℍ in atImInfty,
      ‖delta τ‖ ≤ C * Real.exp (-2 * Real.pi * τ.im) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{τ : ℍ | 1 ≤ τ.im}, ?_, fun τ hτ => h_bound τ hτ⟩
    rw [atImInfty_mem]
    exact ⟨1, fun _ hσ => hσ⟩
  have h_tend_im : Filter.Tendsto (fun τ : ℍ => τ.im) atImInfty Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro A
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{σ : ℍ | A ≤ σ.im}, ?_, fun _ hσ => hσ⟩
    rw [atImInfty_mem]
    exact ⟨A, fun _ hσ => hσ⟩
  have h_neg : Filter.Tendsto (fun τ : ℍ => -2 * Real.pi * τ.im)
      atImInfty Filter.atBot := by
    have h_neg_2pi : (-2 * Real.pi : ℝ) < 0 := by
      have := Real.pi_pos; linarith
    simpa using h_tend_im.const_mul_atTop_of_neg h_neg_2pi
  have h_exp : Filter.Tendsto (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im))
      atImInfty (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_neg
  have h_rhs_tendsto : Filter.Tendsto
      (fun τ : ℍ => C * Real.exp (-2 * Real.pi * τ.im)) atImInfty (nhds 0) := by
    simpa using h_exp.const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    h_bound_ev h_rhs_tendsto

/-- **`Δ` as a Mathlib `CuspForm`.** The modular discriminant
`delta : ℍ → ℂ` packaged as a weight-12 cusp form for `Γ(1) = SL(2, ℤ)`. -/
noncomputable def delta_cuspForm : CuspForm Γ(1) 12 where
  toFun := delta
  slash_action_eq' := by
    intro γ_GL hγ_GL
    obtain ⟨g_SL, _hg_mem, h_eq⟩ := hγ_GL
    have h := delta_slash_action_eq g_SL
    rw [ModularForm.SL_slash] at h
    rw [← h_eq]; exact h
  holo' := delta_mdiff
  zero_at_cusps' := by
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _hγ
    rw [delta_slash_action_eq γ]
    exact delta_isZeroAtImInfty

/-- **Weight-4 cusp form vanishing for `SL(2, ℤ)`.** The space
`S_4(SL(2, ℤ))` of weight-4 cusp forms for the full modular group is
zero-dimensional. The standard proof uses the `Δ`-division route:
given a weight-4 cusp form `F`, the quotient `F² / Δ` is a weight-4·2
− 12 = −4 modular form (with `Δ ≠ 0` on `ℍ` from `delta_ne_zero`),
hence identically zero by Mathlib's
`ModularFormClass.levelOne_neg_weight_eq_zero`. Closing this sorry
requires constructing the quotient `F² / Δ` as
`ModularForm Γ(1) (−4)` (no Mathlib API for modular-form division —
needs custom construction using `delta_ne_zero` and `delta_cuspForm`),
and the final application of `levelOne_neg_weight_eq_zero`. -/
theorem weight4_levelOne_cuspForm_vanishes
    (F : CuspForm Γ(1) 4) (τ : ℍ) :
    F τ = 0 := by
  sorry

end RiemannDynamics

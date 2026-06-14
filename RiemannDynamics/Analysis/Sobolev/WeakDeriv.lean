/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.Wirtinger
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Weak derivatives and Sobolev membership on `ℂ`

This file develops the weak (distributional) first derivatives of a function
`f : ℂ → ℂ` and the local Sobolev membership predicate `W^{k,p}_loc`, working
directly over `ℂ ≃ ℝ²` so that complex-valued maps and Beltrami coefficients
are handled without a real componentwise detour.

`g` is a **weak directional derivative** of `f` in the real direction `v : ℂ`
on `Ω` when the integration-by-parts identity

`∫ (∂ᵥφ) • f = − ∫ φ • g`

holds against every smooth, compactly supported real test function `φ`
supported in `Ω`. The two weak partial derivatives are `HasWeakDirDeriv 1`
(in the `x`-direction) and `HasWeakDirDeriv I` (in the `y`-direction), packaged
as `HasWeakGradient`.

On top of weak gradients we define:

* `MemLpLocOn f p Ω` — `f` is `Lᵖ` on every compact subset of `Ω`;
* `MemWklocP f k p Ω` — local membership in `W^{k,p}`: `f ∈ Lᵖ_loc` together
  with weak partial derivatives of every order up to `k` that are themselves
  in `W^{k-1,p}_loc`;
* `MemW12loc f` — the abbreviation `MemWklocP f 1 2 univ`, the `W^{1,2}_loc(ℂ)`
  class the analytic quasiconformal theory lives in.

The basic calculus proved here is what the rest of the engine consumes: weak
derivatives are unique almost everywhere (the fundamental lemma of the calculus
of variations), they restrict to open subsets, and the class is closed under
multiplication by smooth functions (the Leibniz rule). The absolute-continuity-
on-lines characterization is developed in `QC/Equivalence.lean`, its only
consumer.
-/

open MeasureTheory Complex
open scoped ContDiff ENNReal

namespace RiemannDynamics

variable {f g g₁ g₂ : ℂ → ℂ} {v : ℂ} {Ω : Set ℂ}

/-- `g` is a **weak directional derivative** of `f` in the real direction `v`
on `Ω`: the integration-by-parts identity `∫ (∂ᵥφ) • f = − ∫ φ • g` holds for
every smooth compactly supported real test function `φ` supported in `Ω`. -/
def HasWeakDirDeriv (v : ℂ) (g f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ z, ((fderiv ℝ φ z) v) • f z = - ∫ z, φ z • g z

/-- A **weak gradient** of `f` on `Ω`: weak partial derivatives `gx` in the
`x`-direction (`v = 1`) and `gy` in the `y`-direction (`v = I`). -/
def HasWeakGradient (gx gy f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  HasWeakDirDeriv 1 gx f Ω ∧ HasWeakDirDeriv Complex.I gy f Ω

/-- `f` is **locally `Lᵖ`** on `Ω`: `Lᵖ` with respect to `volume` restricted to
every compact subset of `Ω`. -/
def MemLpLocOn (f : ℂ → ℂ) (p : ℝ≥0∞) (Ω : Set ℂ) : Prop :=
  ∀ K : Set ℂ, K ⊆ Ω → IsCompact K → MemLp f p (volume.restrict K)

/-- **Local Sobolev membership** `f ∈ W^{k,p}_loc(Ω)`: defined by recursion on
the order `k`. Order `0` is `Lᵖ_loc`; order `k+1` asks for `Lᵖ_loc` membership
together with a weak gradient whose components lie in `W^{k,p}_loc`. -/
def MemWklocP (f : ℂ → ℂ) (k : ℕ) (p : ℝ≥0∞) (Ω : Set ℂ) : Prop :=
  match k with
  | 0 => MemLpLocOn f p Ω
  | k + 1 =>
      MemLpLocOn f p Ω ∧
        ∃ gx gy : ℂ → ℂ, HasWeakGradient gx gy f Ω ∧
          MemWklocP gx k p Ω ∧ MemWklocP gy k p Ω

/-- The class `W^{1,2}_loc(ℂ)` the analytic quasiconformal theory lives in. -/
def MemW12loc (f : ℂ → ℂ) : Prop :=
  MemWklocP f 1 2 Set.univ

/-- **Uniqueness of weak derivatives.** On an open set two weak directional
derivatives of the same function in the same direction agree almost everywhere
(the fundamental lemma of the calculus of variations). -/
theorem HasWeakDirDeriv.ae_eq (hΩ : IsOpen Ω)
    (h₁ : HasWeakDirDeriv v g₁ f Ω) (h₂ : HasWeakDirDeriv v g₂ f Ω)
    (hg₁ : LocallyIntegrableOn g₁ Ω) (hg₂ : LocallyIntegrableOn g₂ Ω) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω → g₁ z = g₂ z := by
  -- (smooth, compactly supported real `φ` with `tsupport φ ⊆ Ω`) • (locally integrable on `Ω`)
  -- is integrable on all of `ℂ`.
  have integ : ∀ (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∀ {g : ℂ → ℂ}, LocallyIntegrableOn g Ω → Integrable (fun z => φ z • g z) volume := by
    intro φ hφ hcs htsupp g hg
    have hK : IsCompact (tsupport φ) := hcs
    have hgon : IntegrableOn g (tsupport φ) volume :=
      hg.integrableOn_compact_subset htsupp hK
    have hon : IntegrableOn (fun z => φ z • g z) (tsupport φ) volume :=
      hgon.continuousOn_smul hφ.continuous.continuousOn hK
    have hsupp : Function.support (fun z => φ z • g z) ⊆ tsupport φ := by
      intro z hz
      apply subset_tsupport φ
      simp only [Function.mem_support] at hz ⊢
      intro hφz; apply hz; simp [hφz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- The fundamental lemma of the calculus of variations applied to `g₁ - g₂`.
  have key : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω → (g₁ - g₂) z = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg₁.sub hg₂)
    intro φ hφ hcs htsupp
    have e1 : ∫ z, φ z • g₁ z = ∫ z, φ z • g₂ z := by
      refine neg_inj.mp ?_
      rw [← h₁ φ hφ hcs htsupp, ← h₂ φ hφ hcs htsupp]
    have hi1 := integ φ hφ hcs htsupp hg₁
    have hi2 := integ φ hφ hcs htsupp hg₂
    calc ∫ z, φ z • (g₁ - g₂) z
        = ∫ z, (φ z • g₁ z - φ z • g₂ z) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Pi.sub_apply]; exact smul_sub _ _ _
      _ = (∫ z, φ z • g₁ z) - ∫ z, φ z • g₂ z := integral_sub hi1 hi2
      _ = 0 := by rw [e1]; ring
  filter_upwards [key] with z hz hzΩ
  have := hz hzΩ
  simpa [Pi.sub_apply, sub_eq_zero] using this

/-- **Restriction.** A weak directional derivative on `Ω` is a weak directional
derivative on every subset. -/
theorem HasWeakDirDeriv.mono (h : HasWeakDirDeriv v g f Ω) {Ω' : Set ℂ}
    (hsub : Ω' ⊆ Ω) : HasWeakDirDeriv v g f Ω' := by
  intro φ hφ hcs htsupp
  exact h φ hφ hcs (htsupp.trans hsub)

/-- **Leibniz rule / closure under smooth multiplication.** If `g` is a weak
directional derivative of `f` and `ψ` is smooth, then `ψ • g + (∂ᵥψ) • f` is a
weak directional derivative of `ψ • f` — the product rule
`∂ᵥ(ψ f) = ψ ∂ᵥf + (∂ᵥψ) f` at the level of weak derivatives. -/
theorem HasWeakDirDeriv.smul_smooth (hf : HasWeakDirDeriv v g f Ω)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hfloc : LocallyIntegrableOn f Ω) (hgloc : LocallyIntegrableOn g Ω) :
    HasWeakDirDeriv v (fun z => ψ z • g z + ((fderiv ℝ ψ z) v) • f z)
      (fun z => ψ z • f z) Ω := by
  -- (continuous real, compactly supported in `Ω`) • (locally integrable on `Ω`) is integrable.
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • (ψ z • f z) = - ∫ z, φ z • (ψ z • g z + ((fderiv ℝ ψ z) v) • f z)
  -- Test the hypothesis against the product test function `Φ = ψ * φ`.
  set Φ : ℂ → ℝ := fun z => ψ z * φ z with hΦ
  have hΦsmooth : ContDiff ℝ ∞ Φ := hψ.mul hφ
  have hΦcs : HasCompactSupport Φ := hcs.mul_left
  have hΦtsupp : tsupport Φ ⊆ Ω := subset_trans (tsupport_mul_subset_right) htsupp
  -- Product rule for the directional derivative `(fderiv ℝ Φ z) v`.
  have hpr : ∀ z, (fderiv ℝ Φ z) v = ψ z * ((fderiv ℝ φ z) v) + φ z * ((fderiv ℝ ψ z) v) := by
    intro z
    have hdψ : DifferentiableAt ℝ ψ z := (hψ.differentiable (by norm_num)).differentiableAt
    have hdφ : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
    change (fderiv ℝ (fun y => ψ y * φ y) z) v = _
    rw [fderiv_fun_mul hdψ hdφ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hfΦ := hf Φ hΦsmooth hΦcs hΦtsupp
  have hcont_ψ : Continuous ψ := hψ.continuous
  have hcont_φ : Continuous φ := hφ.continuous
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont_dψ : Continuous (fun z => (fderiv ℝ ψ z) v) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_m1 : HasCompactSupport (fun z => ψ z * ((fderiv ℝ φ z) v)) :=
    HasCompactSupport.mul_left (HasCompactSupport.fderiv_apply ℝ hcs v)
  have hts_m1 : tsupport (fun z => ψ z * ((fderiv ℝ φ z) v)) ⊆ Ω :=
    subset_trans (tsupport_mul_subset_right)
      (subset_trans (tsupport_fderiv_apply_subset ℝ v) htsupp)
  have hcs_m2 : HasCompactSupport (fun z => φ z * ((fderiv ℝ ψ z) v)) := hcs.mul_right
  have hts_m2 : tsupport (fun z => φ z * ((fderiv ℝ ψ z) v)) ⊆ Ω :=
    subset_trans (tsupport_mul_subset_left) htsupp
  have iI_m1f : Integrable (fun z => (ψ z * ((fderiv ℝ φ z) v)) • f z) volume :=
    integ _ (hcont_ψ.mul hcont_dφ) hcs_m1 hts_m1 hfloc
  have iI_m2f : Integrable (fun z => (φ z * ((fderiv ℝ ψ z) v)) • f z) volume :=
    integ _ (hcont_φ.mul hcont_dψ) hcs_m2 hts_m2 hfloc
  -- Split the tested identity along the product rule.
  have hfΦ' : (∫ z, (ψ z * ((fderiv ℝ φ z) v)) • f z)
      + ∫ z, (φ z * ((fderiv ℝ ψ z) v)) • f z = - ∫ z, Φ z • g z := by
    rw [← integral_add iI_m1f iI_m2f, ← hfΦ]
    apply integral_congr_ae
    filter_upwards with z
    rw [hpr z]; module
  -- Rewrite the goal's two sides into the same pieces.
  have goalLHS : (∫ z, ((fderiv ℝ φ z) v) • (ψ z • f z))
      = ∫ z, (ψ z * ((fderiv ℝ φ z) v)) • f z := by
    apply integral_congr_ae
    filter_upwards with z
    module
  have goalRHS : (∫ z, φ z • (ψ z • g z + ((fderiv ℝ ψ z) v) • f z))
      = (∫ z, Φ z • g z) + ∫ z, (φ z * ((fderiv ℝ ψ z) v)) • f z := by
    have iI_g : Integrable (fun z => Φ z • g z) volume :=
      integ _ (hcont_ψ.mul hcont_φ) hΦcs hΦtsupp hgloc
    rw [← integral_add iI_g iI_m2f]
    apply integral_congr_ae
    filter_upwards with z
    simp only [hΦ]; module
  rw [goalLHS, goalRHS, neg_add, ← hfΦ']
  ring

end RiemannDynamics

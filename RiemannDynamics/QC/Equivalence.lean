/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.Analytic
import RiemannDynamics.QC.LengthArea
import RiemannDynamics.Analysis.Sobolev.SobolevToACL

/-!
# Equivalence of the analytic and geometric quasiconformal definitions

The two standard definitions of a quasiconformal map — the **analytic** one
(`IsQCAnalytic`, an orientation-preserving `W^{1,2}_loc` homeomorphism satisfying
the Beltrami equation `∂̄f = μ ∂f` with `‖μ‖∞ < 1`) and the **geometric** one
(`IsQCGeometric`, modulus quasi-invariance of quadrilaterals) — describe the same
maps, with the dilatation `K` and the Beltrami bound `‖μ‖∞` related by
`‖μ‖∞ ≤ (K − 1)/(K + 1)`.

This file proves the bridge `qc_analytic_iff_geometric`, splitting it into the two
directions:

* `isQCGeometric_of_isQCAnalytic` — analytic ⇒ geometric. Uses the
  `Sobolev ⇒ ACL` theorems (`exists_aclHorizontal_of_hasWeakDirDeriv_one`,
  `exists_aclVertical_of_hasWeakDirDeriv_I`) to extract absolute continuity on
  lines from `MemW12loc`, then the length–area modulus estimate bounds the modulus
  distortion by the dilatation `K`.
* `isQCAnalytic_of_isQCGeometric` — geometric ⇒ analytic (the hard direction). A
  modulus-quasi-invariant homeomorphism is absolutely continuous on lines (a
  length–area argument), hence in `W^{1,2}_loc` via `memWklocP_one_of_acl`, and the
  modulus bound forces the Beltrami coefficient to satisfy `‖μ‖∞ ≤ (K − 1)/(K + 1)`.

The analytic and geometric tracks meet only here; results stated in one track are
transferred to the other through this equivalence.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **Analytic ⇒ geometric, pushforward bound.** A map satisfying the analytic
definition with a Beltrami coefficient of norm at most `(K − 1)/(K + 1)` distorts
the modulus of the **pushforward** curve family `(f ∘ ·) '' Q.curveFamily` by at
most `K`. The `Sobolev ⇒ ACL` theorems give absolute continuity on lines, and the
length–area estimate bounds the modulus distortion by `K`.

This is the length–area half of the geometric definition. It bounds the modulus of
the pushforward of `Q`'s connecting family, which is the sub-family of the genuine
image family `Q.imageCurveFamily f` consisting of curves `f ∘ γ` with `γ`
absolutely continuous and `f` good along `γ`. The genuine bound `M(f(Q)) ≤ K · M(Q)`
(`isQCGeometric_of_isQCAnalytic`) follows from this together with the nullity of the
complementary image curves (image-side Fuglede); see the note there. -/
theorem isQCGeometric_of_isQCAnalytic_pushforward {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    {b : BeltramiCoeff} (hb : b.normInf ≤ (K - 1) / (K + 1)) (hf : IsQCAnalytic f b) :
    OrientationPreservingHomeo f ∧ ∀ Q : Quadrilateral,
      curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Q.curveFamily)
        ≤ ENNReal.ofReal K * Q.modulus := by
  classical
  -- Notation.
  set hhom : IsHomeomorph f := hf.1.1 with hhom_def
  -- The almost-everywhere essential-sup bound on the Beltrami coefficient.
  have hμae : ∀ᵐ z : ℂ, ‖b.μ z‖ ≤ b.normInf := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    -- `‖b.μ z‖ₑ ≤ eLpNormEssSup`, and the right side is finite (`< 1 < ⊤`).
    have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := ne_top_of_lt b.bound
    have hz' : (‖b.μ z‖₊ : ℝ≥0∞) ≤ eLpNormEssSup b.μ volume := by
      simpa [enorm_eq_nnnorm] using hz
    have := (ENNReal.toReal_le_toReal (by simp) hfin).mpr hz'
    simpa [BeltramiCoeff.normInf, coe_nnnorm] using this
  -- ============================================================
  -- STEP 1.  Almost-everywhere dilatation bound:
  --   ‖(Df z)⁻¹‖² · det (Df z) ≤ K.
  -- ============================================================
  have hkbound : b.normInf < 1 := b.normInf_lt_one
  have hKkey : (1 + b.normInf) / (1 - b.normInf) ≤ K := by
    -- From `b.normInf ≤ (K-1)/(K+1)`, derive `(1+k)/(1-k) ≤ K`.
    have hknn : (0 : ℝ) ≤ b.normInf := b.normInf_nonneg
    have hKpos : (0 : ℝ) < K + 1 := by linarith
    have hk_le : b.normInf ≤ (K - 1) / (K + 1) := hb
    -- `(K-1)/(K+1) < 1`, so `1 - k > 0`.
    have hKm1 : (K - 1) / (K + 1) < 1 := by
      rw [div_lt_one hKpos]; linarith
    have h1mk : (0 : ℝ) < 1 - b.normInf := by linarith
    rw [div_le_iff₀ h1mk]
    -- `1 + k ≤ K (1 - k) = K - K k`, i.e. `k (1 + K) ≤ K - 1`.
    have hk_mul : b.normInf * (K + 1) ≤ K - 1 := by
      rw [← le_div_iff₀ hKpos]; exact hk_le
    nlinarith [hk_mul]
  have hdil : ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K := by
    filter_upwards [hf.1.2, hf.2.2, hμae] with z hdet hbel hμz
    -- Abbreviations.
    set p : ℂ := dz f z with hp
    set q : ℂ := dzbar f z with hq
    set d : ℝ := (fderiv ℝ f z).det with hd
    have hdval : d = ‖p‖ ^ 2 - ‖q‖ ^ 2 := det_fderiv_eq_wirtinger f z
    have hinvval : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ = (‖p‖ + ‖q‖) / d :=
      opNorm_inverse_eq_wirtinger f z hdet
    -- `‖q‖ ≤ k ‖p‖` from the Beltrami equation and the L∞ bound.
    have hqeq : ‖q‖ = ‖b.μ z‖ * ‖p‖ := by rw [hq, ← hq, hbel, norm_mul]
    have hqp : ‖q‖ ≤ b.normInf * ‖p‖ := by
      rw [hqeq]; gcongr
    -- Positivity facts.
    have hdpos : 0 < d := hdet
    have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg q, norm_nonneg p, hdval, hdpos]
    have hqnn : 0 ≤ ‖q‖ := norm_nonneg q
    have hpqlt : ‖q‖ < ‖p‖ := by nlinarith [hdval, hdpos, norm_nonneg p]
    have hpmq : 0 < ‖p‖ - ‖q‖ := by linarith
    -- `‖inv‖² · d = (‖p‖+‖q‖)/(‖p‖-‖q‖)`.
    have hfactor : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * d
        = (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) := by
      rw [hinvval, div_pow, hdval]
      have hsplit : ‖p‖ ^ 2 - ‖q‖ ^ 2 = (‖p‖ + ‖q‖) * (‖p‖ - ‖q‖) := by ring
      rw [hsplit]
      have hsum_ne : ‖p‖ + ‖q‖ ≠ 0 := by positivity
      have hpmq_ne : ‖p‖ - ‖q‖ ≠ 0 := ne_of_gt hpmq
      field_simp
    rw [hfactor]
    -- `(‖p‖+‖q‖)/(‖p‖-‖q‖) ≤ (1+k)/(1-k) ≤ K`.
    refine le_trans ?_ hKkey
    rw [div_le_div_iff₀ hpmq (by linarith : (0:ℝ) < 1 - b.normInf)]
    -- `(‖p‖+‖q‖)(1-k) ≤ (1+k)(‖p‖-‖q‖)`, i.e. `2‖q‖ ≤ 2k‖p‖`.
    nlinarith [hqp, hppos]
  -- ============================================================
  -- Global infrastructure: the differentiability set and the inverse map.
  -- ============================================================
  -- `S` is the (measurable, full-measure) set where `f` is differentiable with
  -- positive Jacobian determinant.
  set S : Set ℂ := {z : ℂ | DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det} with hSdef
  have hSmeas : MeasurableSet S := by
    apply MeasurableSet.inter (measurableSet_of_differentiableAt ℝ f)
    exact measurableSet_lt measurable_const
      ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
  -- `S` is a.e. all of `ℂ`.
  have hSae : ∀ᵐ z : ℂ, z ∈ S := by
    filter_upwards [hf.1.2, IsQCAnalytic.ae_differentiableAt hf] with z hz hzd
    exact ⟨hzd, hz⟩
  have hScompl_null : volume (Sᶜ : Set ℂ) = 0 := by
    have : {z : ℂ | ¬ z ∈ S} = (Sᶜ : Set ℂ) := rfl
    rw [← this, ← ae_iff]
    filter_upwards [hSae] with z hz using hz
  -- The inverse homeomorphism `g = f⁻¹`.
  set g : ℂ → ℂ := ⇑(hhom.homeomorph f).symm with hg_def
  have hgf : ∀ z, g (f z) = z := (hhom.homeomorph f).symm_apply_apply
  have hfg : ∀ w, f (g w) = w := (hhom.homeomorph f).apply_symm_apply
  have hg_cont : Continuous g := (hhom.homeomorph f).symm.continuous
  -- The differentiability data on `S` for change-of-variables.
  have hfderiv_S : ∀ z ∈ S, HasFDerivWithinAt f (fderiv ℝ f z) S z := fun z hz =>
    (hz.1.hasFDerivAt).hasFDerivWithinAt
  have hfinj_S : Set.InjOn f S := hhom.injective.injOn
  -- `f '' S` is measurable, and a.e. all of `ℂ`.
  have hfSmeas : MeasurableSet (f '' S) :=
    measurable_image_of_fderivWithin hSmeas hfderiv_S hfinj_S
  -- ============================================================
  -- Refine to: homeomorphism + per-quadrilateral modulus bound.
  -- ============================================================
  refine ⟨hf.1, fun Q => ?_⟩
  set Γ : Set (ℝ → ℂ) := Q.curveFamily with hΓdef
  rw [Quadrilateral.modulus]
  -- The exceptional (bad) and good subfamilies of `Γ`.
  set badProp : (ℝ → ℂ) → Prop := fun γ =>
    ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t) with hbadProp
  set Γbad : Set (ℝ → ℂ) := {γ ∈ Γ | badProp γ} with hΓbad
  set Γgood : Set (ℝ → ℂ) := Γ \ Γbad with hΓgood
  -- The bad family and its image have zero modulus.
  have hbad0 : curveModulus Γbad = 0 :=
    IsQCAnalytic.chainRule_exceptional_modulus_zero hf Γ (fun γ hγ => hγ.1)
      (fun γ hγ => hγ.2.1)
  have hbadimg0 : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γbad) = 0 :=
    IsQCAnalytic.image_modulus_zero hf (Γ' := Γbad)
      (fun γ hγ => hγ.1.1) (fun γ hγ => hγ.1.2.1) hbad0
  -- ============================================================
  -- KEY: for every density `ρ` admissible for `Γ`,
  --   curveModulus ((f∘·)''Γgood) ≤ ofReal K * ∫⁻ ρ².
  -- ============================================================
  have key : ∀ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ Γ →
      curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood)
        ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
    intro ρ ⟨hρmeas, hρadm⟩
    -- The pointwise reciprocal-singular-value weight, written as an explicit
    -- (measurable) formula in the Wirtinger derivatives rather than via `inverse`.
    set wt : ℂ → ℝ≥0∞ := fun z =>
      ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (fderiv ℝ f z).det) with hwt_def
    -- On `S`, `wt z` is exactly `‖(Df z)⁻¹‖`.
    have hwt_eq : ∀ z ∈ S, wt z =
        ENNReal.ofReal ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ := by
      intro z hz
      rw [hwt_def, opNorm_inverse_eq_wirtinger f z hz.2]
    -- The transferred density `σ`, supported on `f '' S`.
    set σ : ℂ → ℝ≥0∞ := fun w =>
      (f '' S).indicator (fun w => ρ (g w) * wt (g w)) w with hσ_def
    -- Measurability of the Wirtinger building blocks.
    have hfderivmeas : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
    have hdzmeas : Measurable (fun z : ℂ => dz f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dz] using (measurable_const.mul ((h1.sub (measurable_const.mul h2))))
    have hdzbarmeas : Measurable (fun z : ℂ => dzbar f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dzbar] using (measurable_const.mul ((h1.add (measurable_const.mul h2))))
    have hdetmeas : Measurable (fun z : ℂ => (fderiv ℝ f z).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp hfderivmeas
    have hwtmeas : Measurable wt := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact ((hdzmeas.norm.add hdzbarmeas.norm).div hdetmeas)
    -- Measurability of `σ`.
    have hσmeas : Measurable σ := by
      refine (Measurable.indicator ?_ hfSmeas)
      exact (hρmeas.comp hg_cont.measurable).mul (hwtmeas.comp hg_cont.measurable)
    -- ------------------------------------------------------------------
    -- STEP 2.  Energy bound: ∫⁻ σ² ≤ ofReal K * ∫⁻ ρ².
    -- ------------------------------------------------------------------
    have henergy : ∫⁻ w, (σ w) ^ 2 ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
      -- `∫⁻ σ²` is supported on `f '' S`.
      have hσsq_ind : (fun w => (σ w) ^ 2)
          = (f '' S).indicator (fun w => (ρ (g w) * wt (g w)) ^ 2) := by
        funext w
        simp only [hσ_def]
        by_cases hw : w ∈ f '' S
        · simp only [Set.indicator_of_mem hw]
        · simp only [Set.indicator_of_notMem hw]; ring
      rw [hσsq_ind, lintegral_indicator hfSmeas]
      -- Change of variables `w = f z`, `z ∈ S`.
      have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (volume : Measure ℂ) hSmeas hfderiv_S hfinj_S
        (fun w => (ρ (g w) * wt (g w)) ^ 2)
      rw [hcov]
      -- Pointwise (a.e.-on-`S`) bound on the transformed integrand.
      have hmono : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := by
        refine setLIntegral_mono_ae' hSmeas ?_
        filter_upwards [hdil] with z hzdil hzS
        -- Rewrite the integrand at `z ∈ S`.
        rw [hgf z, hwt_eq z hzS]
        have hdetpos : 0 < (fderiv ℝ f z).det := hzS.2
        rw [abs_of_pos hdetpos, mul_pow, ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [show ENNReal.ofReal (fderiv ℝ f z).det *
              ((ρ z) ^ 2 * ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2))
            = (ρ z) ^ 2 * (ENNReal.ofReal (fderiv ℝ f z).det *
                ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2)) by ring]
        rw [← ENNReal.ofReal_mul hdetpos.le, mul_comm (ENNReal.ofReal K) ((ρ z) ^ 2)]
        gcongr
        -- `det · ‖inv‖² ≤ K` from the dilatation bound `‖inv‖² · det ≤ K`.
        rw [mul_comm]; exact hzdil
      calc ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := hmono
        _ = ENNReal.ofReal K * ∫⁻ z in S, (ρ z) ^ 2 := by
            rw [lintegral_const_mul _ (hρmeas.pow_const 2)]
        _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    -- ------------------------------------------------------------------
    -- STEP 3.  `σ` is admissible for `(f∘·)''Γgood`.
    -- ------------------------------------------------------------------
    have hσadm : IsAdmissibleDensity σ ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood) := by
      refine ⟨hσmeas, ?_⟩
      rintro δ ⟨γ, hγgood, rfl⟩
      -- Unpack the "good" hypotheses on `γ`.
      have hγΓ : γ ∈ Γ := hγgood.1
      have hnotbad : ¬ badProp γ := by
        intro hbad; exact hγgood.2 ⟨hγΓ, hbad⟩
      rw [hbadProp] at hnotbad
      obtain ⟨hAC, hdetγ, hchainγ⟩ := not_not.mp hnotbad
      -- Pointwise lower bound on the σ-integrand, a.e.-`t` on `[0,1]` (the only
      -- range that matters: the arc-length integrals live on `[0,1]`).
      have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ σ ((f ∘ γ) t) * (‖deriv (f ∘ γ) t‖₊ : ℝ≥0∞) := by
        filter_upwards [hdetγ, hchainγ] with t hdett₀ hchaint₀
        -- Where `deriv γ t = 0` the left-hand side vanishes, so the bound is trivial.
        rcases eq_or_ne (deriv γ t) 0 with hd0 | hd0
        · simp [hd0]
        -- Otherwise discharge the `deriv γ t ≠ 0` guards on both clauses.
        have hdett : 0 < (fderiv ℝ f (γ t)).det := hdett₀ hd0
        have hchaint : HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t :=
          hchaint₀ hd0
        set A : ℂ →L[ℝ] ℂ := fderiv ℝ f (γ t) with hA
        -- `γ t ∈ S` (differentiable, since `0 < det`).
        have hdett' : 0 < (fderiv ℝ f (γ t)).det := hdett
        have hγtS : γ t ∈ S := by
          refine ⟨?_, hdett'⟩
          by_contra hnd
          rw [fderiv_zero_of_not_differentiableAt hnd] at hdett'
          simp [ContinuousLinearMap.det] at hdett'
        -- `A` is invertible.
        have hAinv : A.IsInvertible :=
          ⟨A.toContinuousLinearEquivOfDetNeZero hdett.ne',
            A.coe_toContinuousLinearEquivOfDetNeZero hdett.ne'⟩
        -- `deriv (f∘γ) t = A (deriv γ t)`.
        have hderiv : deriv (f ∘ γ) t = A (deriv γ t) := hchaint.deriv
        -- `σ (f (γ t)) = ρ (γ t) * ofReal ‖inverse A‖`.
        have hfγtS : f (γ t) ∈ f '' S := ⟨γ t, hγtS, rfl⟩
        have hσval : σ ((f ∘ γ) t) = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ := by
          simp only [Function.comp_apply, hσ_def]
          rw [Set.indicator_of_mem hfγtS, hgf, hwt_eq (γ t) hγtS]
        rw [hσval, hderiv]
        -- Lower bound: `‖v‖₊ ≤ ‖inverse A‖₊ · ‖A v‖₊`, i.e. the integrand dominates.
        have hkey : (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by
          have hself : A.inverse (A (deriv γ t)) = deriv γ t :=
            ContinuousLinearMap.IsInvertible.inverse_apply_self hAinv (deriv γ t)
          have hop : ‖deriv γ t‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ := by
            have hle : ‖A.inverse (A (deriv γ t))‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ :=
              A.inverse.le_opNNNorm _
            rwa [hself] at hle
          have hcoe : ENNReal.ofReal ‖A.inverse‖ = (‖A.inverse‖₊ : ℝ≥0∞) := by
            rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]
          rw [hcoe, ← ENNReal.coe_mul]
          exact_mod_cast hop
        calc ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ρ (γ t) * (ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞)) := by
              gcongr
          _ = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by ring
      -- Integrate the pointwise bound.
      have hint : arcLengthLineIntegral ρ γ ≤ arcLengthLineIntegral σ (f ∘ γ) := by
        unfold arcLengthLineIntegral
        exact lintegral_mono_ae hpoint
      exact le_trans (hρadm γ hγΓ) hint
    -- ------------------------------------------------------------------
    -- Conclude `key`: bound the image modulus by the energy of `σ`.
    -- ------------------------------------------------------------------
    calc curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood)
        ≤ ∫⁻ w, (σ w) ^ 2 := iInf₂_le σ hσadm
      _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := henergy
  -- ============================================================
  -- STEP 4.  Assemble.
  -- ============================================================
  -- The good image equals the full image minus the (zero-modulus) bad image.
  -- Injectivity of post-composition by `f`.
  have hinj : Function.Injective (fun γ : ℝ → ℂ => f ∘ γ) := by
    intro γ₁ γ₂ h
    funext s
    exact hhom.injective (congrFun h s)
  have himg_eq : (fun γ : ℝ → ℂ => f ∘ γ) '' Γgood
      = (fun γ : ℝ → ℂ => f ∘ γ) '' Γ \ (fun γ : ℝ → ℂ => f ∘ γ) '' Γbad := by
    rw [hΓgood, Set.image_diff hinj]
  -- The bad image is `⊆` the full image, with zero modulus, so removing it is harmless.
  have hsub : (fun γ : ℝ → ℂ => f ∘ γ) '' Γbad ⊆ (fun γ : ℝ → ℂ => f ∘ γ) '' Γ :=
    Set.image_mono (by rw [hΓbad]; exact fun γ hγ => hγ.1)
  have himg_mod_eq : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood)
      = curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ) := by
    rw [himg_eq]
    exact curveModulus_sdiff_modulus_zero hsub hbadimg0
  -- Push `ofReal K` inside the modulus infimum and conclude with `key`.
  have hKne0 : ENNReal.ofReal K ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hKnetop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← himg_mod_eq]
  -- `ofReal K * curveModulus Γ = ⨅ ρ ∈ adm, ofReal K * ∫⁻ ρ²`.
  conv_rhs => rw [curveModulus, ENNReal.mul_iInf_of_ne hKne0 hKnetop]
  refine le_iInf fun ρ => ?_
  rw [ENNReal.mul_iInf_of_ne hKne0 hKnetop]
  refine le_iInf fun hρ => ?_
  exact key ρ hρ

/-- **Analytic ⇒ geometric.** A map satisfying the analytic definition with a
Beltrami coefficient of norm at most `(K − 1)/(K + 1)` is `K`-quasiconformal in the
geometric (modulus) sense: `M(f(Q)) ≤ K · M(Q)` for every quadrilateral `Q`, where
`M(f(Q))` is the modulus of the genuine image family `Q.imageCurveFamily f`.

The orientation clause is immediate from `IsQCAnalytic`. For the modulus bound, the
genuine image family `Q.imageCurveFamily f` splits into the curves whose `f⁻¹`-image
is an absolutely continuous, chain-rule-good curve of `Q.curveFamily` — these embed
in the pushforward `(f ∘ ·) '' Q.curveFamily`, already bounded by `K · M(Q)` via
`isQCGeometric_of_isQCAnalytic_pushforward` — and the complementary curves (image AC
curves whose `f⁻¹`-image fails absolute continuity), which form a **zero-modulus
family**. The latter nullity is the image-side Fuglede fact: it follows from
`f⁻¹` being itself analytic-quasiconformal (inverse-is-QC), applying the source-side
`IsQCAnalytic.chainRule_exceptional_modulus_zero` to `f⁻¹` over the image family. It
is the same wall isolated by `IsQCAnalytic.image_chainRule_exceptional_modulus_zero`
in `QC/LengthArea.lean`, whose crux is planar Lusin-(N) `volume (f '' {¬diff}) = 0`.
Assembling the two pieces via `curveModulus_union_zero` gives the genuine bound. -/
theorem isQCGeometric_of_isQCAnalytic {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    {b : BeltramiCoeff} (hb : b.normInf ≤ (K - 1) / (K + 1)) (hf : IsQCAnalytic f b) :
    IsQCGeometric f K := by
  refine ⟨hf.1, fun Q => ?_⟩
  sorry

/-- **Geometric ⇒ analytic** (the hard direction). A `K`-quasiconformal map in the
geometric (modulus) sense is absolutely continuous on lines, hence lies in
`W^{1,2}_loc`, and satisfies the Beltrami equation with a coefficient of norm at
most `(K − 1)/(K + 1)`. -/
theorem isQCAnalytic_of_isQCGeometric {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hf : IsQCGeometric f K) :
    ∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧ IsQCAnalytic f b := by
  sorry

/-- **Equivalence of the analytic and geometric quasiconformal definitions.** For
`1 ≤ K`, a map admits an analytic-quasiconformal structure with Beltrami norm at
most `(K − 1)/(K + 1)` if and only if it is `K`-quasiconformal in the geometric
(modulus) sense. -/
theorem qc_analytic_iff_geometric {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K) :
    (∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧ IsQCAnalytic f b) ↔
      IsQCGeometric f K :=
  ⟨fun ⟨_, hb, hf⟩ => isQCGeometric_of_isQCAnalytic hK hb hf,
    isQCAnalytic_of_isQCGeometric hK⟩

end RiemannDynamics

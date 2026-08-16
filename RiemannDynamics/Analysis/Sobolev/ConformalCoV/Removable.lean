/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.ConformalCoV.Comp

/-!
# Removable singletons for weak directional derivatives

A weak directional derivative on an open set minus a point extends across the
point: single points are removable for the weak derivative relation.

* `HasWeakDirDeriv.removable_singleton` — the removable-point lemma.
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace RiemannDynamics

/-- **`W^{1,2}` removability of a point.** A single point has zero `W^{1,2}`-capacity: if `f`
is continuous on the open set `Ω`, `g` is locally square-integrable on `Ω`, and `g` is a weak
directional derivative of `f` in the direction `v` on `Ω \ {p}`, then `g` is a weak
directional derivative of `f` in the direction `v` on all of `Ω`. -/
theorem HasWeakDirDeriv.removable_singleton {f g : ℂ → ℂ} {v p : ℂ} {Ω : Set ℂ}
    (h : HasWeakDirDeriv v g f (Ω \ {p})) (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hg : MemLpLocOn g 2 Ω) :
    HasWeakDirDeriv v g f Ω := by
  classical
  have : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  have : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  have : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  by_cases hp : p ∈ Ω
  swap
  · rwa [Set.sdiff_singleton_eq_self hp] at h
  intro φ hφ hcs htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • f z = - ∫ z, φ z • g z
  set K : Set ℂ := tsupport φ with hKdef
  have hKc : IsCompact K := hcs
  have hKΩ : K ⊆ Ω := htsupp
  -- A safety radius around the puncture.
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hΩ p hp
  set δ₀ : ℝ := r / 4 with hδ₀def
  have hδ₀pos : 0 < δ₀ := by positivity
  have hball : Metric.closedBall p (2 * δ₀) ⊆ Ω := by
    intro z hz
    apply hrball
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : 2 * δ₀ < r := by rw [hδ₀def]; linarith
    linarith
  -- The compact carrier `KK` on which `f` is bounded.
  set KK : Set ℂ := K ∪ Metric.closedBall p (2 * δ₀) with hKKdef
  have hKKc : IsCompact KK := hKc.union (isCompact_closedBall _ _)
  have hKKΩ : KK ⊆ Ω := Set.union_subset hKΩ hball
  obtain ⟨Mf, hMf⟩ := hKKc.exists_bound_of_continuousOn (hf.mono hKKΩ)
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _)
    (hMf p (Set.mem_union_right _ (Metric.mem_closedBall_self (by positivity))))
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hcs
  -- The shrinking scale sequence `δs k = δ₀ / (k+1) → 0`.
  set δs : ℕ → ℝ := fun k => δ₀ / (k + 1) with hδsdef
  have hδpos : ∀ k, 0 < δs k := fun k => by positivity
  have hδle : ∀ k, δs k ≤ δ₀ := by
    intro k
    rw [hδsdef]
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    calc δ₀ / ((k : ℝ) + 1) ≤ δ₀ / 1 := by
          apply div_le_div_of_nonneg_left hδ₀pos.le (by norm_num) h1
      _ = δ₀ := div_one δ₀
  have hδid : ∀ k : ℕ, ((k : ℝ) + 1) * δs k = δ₀ := by
    intro k
    have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [hδsdef, mul_comm]
    exact div_mul_cancel₀ δ₀ hk0
  have hδtend : Filter.Tendsto δs Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun k : ℕ => δ₀ / ((k : ℝ) + 1)) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [hδsdef] using h2
  -- The reference cutoff at scale `δ₀` and its rescalings `χs k` at scale `δs k`.
  obtain ⟨χ₁, hχ₁sm, hχ₁cs, hχ₁0, hχ₁1, hχ₁one, hχ₁supp, C₀, hC₀0, hC₀⟩ :=
    exists_cutoff_ball p δ₀ hδ₀pos
  set c : ℕ → ℂ := fun k => ((((k : ℝ) + 1) : ℝ) : ℂ) with hcdef
  have hcnorm : ∀ k, ‖c k‖ = (k : ℝ) + 1 := by
    intro k
    rw [hcdef]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  set A : ℕ → ℂ → ℂ := fun k z => p + c k * (z - p) with hAdef
  have hA_fd : ∀ k z, HasFDerivAt (A k)
      (c k • ContinuousLinearMap.id ℝ ℂ) z := by
    intro k z
    have h1 : HasFDerivAt (fun z : ℂ => z - p) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const p
    have h2 := (h1.const_mul (c k)).const_add p
    have h3 : c k • ContinuousLinearMap.id ℝ ℂ
        = (c k) • (ContinuousLinearMap.id ℝ ℂ) := rfl
    exact h2
  have hA_sm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (A k) := by
    intro k
    exact contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hA_dist : ∀ k z, dist (A k z) p = ((k : ℝ) + 1) * dist z p := by
    intro k z
    rw [hAdef]
    simp only [dist_eq_norm, add_sub_cancel_left]
    rw [norm_mul, hcnorm]
  set χs : ℕ → ℂ → ℝ := fun k z => χ₁ (A k z) with hχsdef
  have hχsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (χs k) := fun k => hχ₁sm.comp (hA_sm k)
  have hχ0 : ∀ k z, 0 ≤ χs k z := fun k z => hχ₁0 _
  have hχ1 : ∀ k z, χs k z ≤ 1 := fun k z => hχ₁1 _
  have hχone : ∀ k, ∀ z ∈ Metric.ball p (δs k), χs k z = 1 := by
    intro k z hz
    apply hχ₁one
    rw [Metric.mem_ball] at hz ⊢
    rw [hA_dist]
    calc ((k : ℝ) + 1) * dist z p < ((k : ℝ) + 1) * δs k := by
          apply mul_lt_mul_of_pos_left hz (by positivity)
      _ = δ₀ := hδid k
  have hχsupp : ∀ k, tsupport (χs k) ⊆ Metric.closedBall p (3 * δs k / 2) := by
    intro k
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    have hAz : A k z ∈ tsupport χ₁ := subset_tsupport χ₁ (by
      simp only [Function.mem_support] at hz ⊢
      exact hz)
    have h1 := hχ₁supp hAz
    rw [Metric.mem_closedBall] at h1 ⊢
    rw [hA_dist] at h1
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← hδid k] at h1
    calc dist z p = (((k : ℝ) + 1) * dist z p) / ((k : ℝ) + 1) := by field_simp
      _ ≤ (3 * (((k : ℝ) + 1) * δs k) / 2) / ((k : ℝ) + 1) := by
          apply div_le_div_of_nonneg_right h1 hk1.le
      _ = 3 * δs k / 2 := by field_simp
  have hχcs : ∀ k, HasCompactSupport (χs k) := by
    intro k
    exact IsCompact.of_isClosed_subset (isCompact_closedBall p (3 * δs k / 2))
      (isClosed_tsupport _) (hχsupp k)
  -- The scaled derivative bound `‖(fderiv χs k z) v‖ ≤ (k+1) * (C₀/δ₀) * ‖v‖`.
  have hχfd : ∀ k z, ‖(fderiv ℝ (χs k) z) v‖ ≤ ((k : ℝ) + 1) * (C₀ / δ₀) * ‖v‖ := by
    intro k z
    have hχ₁d : DifferentiableAt ℝ χ₁ (A k z) :=
      (hχ₁sm.differentiable (by norm_num)).differentiableAt
    have hcomp : HasFDerivAt (χs k)
        ((fderiv ℝ χ₁ (A k z)).comp (c k • ContinuousLinearMap.id ℝ ℂ)) z :=
      hχ₁d.hasFDerivAt.comp z (hA_fd k z)
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    calc ‖(fderiv ℝ χ₁ (A k z)) (c k • v)‖
        ≤ ‖fderiv ℝ χ₁ (A k z)‖ * ‖c k • v‖ := (fderiv ℝ χ₁ (A k z)).le_opNorm _
      _ = ‖fderiv ℝ χ₁ (A k z)‖ * (((k:ℝ)+1) * ‖v‖) := by
          rw [smul_eq_mul, norm_mul, hcnorm]
      _ ≤ (C₀ / δ₀) * (((k:ℝ)+1) * ‖v‖) := by
          apply mul_le_mul_of_nonneg_right (hC₀ _) (by positivity)
      _ = ((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖ := by ring
  -- Outside the closed ball of radius `3δs k/2` the derivative of the cutoff vanishes.
  have hχfd0 : ∀ k z, z ∉ Metric.closedBall p (3 * δs k / 2) → (fderiv ℝ (χs k) z) v = 0 := by
    intro k z hz
    have hz' : z ∉ tsupport (χs k) := fun hmem => hz (hχsupp k hmem)
    have : fderiv ℝ (χs k) z = 0 := by
      by_contra hne
      exact hz' (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    rw [this]
    rfl
  -- Local integrability of `f` and `g` on `Ω`, and the basic integrability engine.
  have hfli : LocallyIntegrableOn f Ω := hf.locallyIntegrableOn hΩ.measurableSet
  have hgli : LocallyIntegrableOn g Ω := by
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk hkc
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    have h1le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    exact memLp_one_iff_integrable.mp ((hg k hk hkc).mono_exponent h1le)
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
  -- The truncated test functions `φs k = φ · (1 - χs k)` and their admissibility.
  set φs : ℕ → ℂ → ℝ := fun k z => φ z * (1 - χs k z) with hφsdef
  have hφs_sm : ∀ k, ContDiff ℝ ∞ (φs k) :=
    fun k => hφ.mul (contDiff_const.sub (hχsm k))
  have hφs_cs : ∀ k, HasCompactSupport (φs k) := fun k => hcs.mul_right
  have hφs_le : ∀ k z, |φs k z| ≤ |φ z| := by
    intro k z
    rw [hφsdef]
    simp only [abs_mul]
    have h1 : |1 - χs k z| ≤ 1 := by
      rw [abs_le]
      constructor
      · have := hχ1 k z; linarith
      · have := hχ0 k z; linarith
    calc |φ z| * |1 - χs k z| ≤ |φ z| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |φ z| := mul_one _
  have hφs_ts : ∀ k, tsupport (φs k) ⊆ Ω \ {p} := by
    intro k z hz
    have h1 : z ∈ K := tsupport_mul_subset_left hz
    have h2 : z ∈ tsupport (fun z => 1 - χs k z) := tsupport_mul_subset_right hz
    have h3 : z ∉ Metric.ball p (δs k) := by
      have hsub : Function.support (fun z => 1 - χs k z) ⊆ (Metric.ball p (δs k))ᶜ := by
        intro w hw
        simp only [Function.mem_support] at hw
        intro hwball
        exact hw (by rw [hχone k w hwball]; ring)
      have := closure_minimal hsub (Metric.isOpen_ball.isClosed_compl) h2
      exact this
    refine ⟨hKΩ h1, ?_⟩
    intro hzp
    rw [Set.mem_singleton_iff] at hzp
    subst hzp
    exact h3 (Metric.mem_ball_self (hδpos k))
  -- The truncated integration-by-parts identities.
  have hIk : ∀ k, ∫ z, ((fderiv ℝ (φs k) z) v) • f z = - ∫ z, φs k z • g z :=
    fun k => h (φs k) (hφs_sm k) (hφs_cs k) (hφs_ts k)
  -- The product-rule split of `fderiv (φs k)`.
  have hsplit : ∀ k z, (fderiv ℝ (φs k) z) v
      = (1 - χs k z) * ((fderiv ℝ φ z) v) - φ z * ((fderiv ℝ (χs k) z) v) := by
    intro k z
    have hφd : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
    have hχd : DifferentiableAt ℝ (χs k) z :=
      ((hχsm k).differentiable (by norm_num)).differentiableAt
    have hmul := fderiv_fun_mul (𝕜 := ℝ) hφd (hχd.const_sub 1)
    have hsub : fderiv ℝ (fun w => 1 - χs k w) z = - fderiv ℝ (χs k) z :=
      ((hχd.hasFDerivAt.const_sub 1).fderiv)
    rw [hφsdef]
    simp only
    rw [hmul, hsub]
    simp only [add_apply, smul_apply,
      neg_apply, smul_eq_mul]
    ring
  -- The three integral pieces.
  set Ak : ℕ → ℂ := fun k => ∫ z, ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z with hAkdef
  set Bk : ℕ → ℂ := fun k => ∫ z, (φ z * ((fderiv ℝ (χs k) z) v)) • f z with hBkdef
  set Ck : ℕ → ℂ := fun k => ∫ z, φs k z • g z with hCkdef
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) v) :=
    HasCompactSupport.fderiv_apply ℝ hcs v
  have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans htsupp
  have hint_m1 : ∀ k, Integrable (fun z => ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z) volume := by
    intro k
    apply integ _ ((continuous_const.sub (hχsm k).continuous).mul hcont_dφ)
      hcs_dφ.mul_left (subset_trans tsupport_mul_subset_right hts_dφ) hfli
  have hint_m2 : ∀ k, Integrable (fun z => (φ z * ((fderiv ℝ (χs k) z) v)) • f z) volume := by
    intro k
    have hcont_dχ : Continuous (fun z => (fderiv ℝ (χs k) z) v) :=
      ((hχsm k).continuous_fderiv (by norm_num)).clm_apply continuous_const
    apply integ _ (hφ.continuous.mul hcont_dχ) hcs.mul_right
      (subset_trans tsupport_mul_subset_left htsupp) hfli
  have hIk' : ∀ k, Ak k - Bk k = - Ck k := by
    intro k
    have h1 : (∫ z, ((fderiv ℝ (φs k) z) v) • f z) = Ak k - Bk k := by
      rw [hAkdef, hBkdef]
      simp only
      rw [← integral_sub (hint_m1 k) (hint_m2 k)]
      apply integral_congr_ae
      filter_upwards with z
      rw [hsplit k z]
      module
    rw [← h1, hIk k, hCkdef]
  -- ==================== Limit (A): `Ak → ∫ (∂ᵥφ) • f`. ====================
  have hA : Filter.Tendsto Ak Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) v) • f z)) := by
    rw [hAkdef]
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun z => ‖(fderiv ℝ φ z) v‖ * Mf)
    · -- a.e. strong measurability of each integrand
      intro k
      have heq : (fun z => ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z)
          = K.indicator (fun z => ((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z) := by
        funext z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          have hznot : z ∉ tsupport (fun x => (fderiv ℝ φ x) v) :=
            fun hmem => hz (tsupport_fderiv_apply_subset ℝ v hmem)
          rw [image_eq_zero_of_notMem_tsupport hznot]
          simp
      rw [heq]
      rw [aestronglyMeasurable_indicator_iff hKc.measurableSet]
      exact (((continuous_const.sub (hχsm k).continuous).mul
        hcont_dφ).aestronglyMeasurable.restrict).smul
        ((hf.mono hKΩ).aestronglyMeasurable hKc.measurableSet)
    · apply Continuous.integrable_of_hasCompactSupport
      · exact hcont_dφ.norm.mul continuous_const
      · exact hcs_dφ.norm.mul_right
    · intro k
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ K
      · calc ‖((1 - χs k z) * ((fderiv ℝ φ z) v)) • f z‖
            = |1 - χs k z| * ‖(fderiv ℝ φ z) v‖ * ‖f z‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          _ ≤ 1 * ‖(fderiv ℝ φ z) v‖ * Mf := by
              have h1 : |1 - χs k z| ≤ 1 := by
                rw [abs_le]
                exact ⟨by have := hχ1 k z; linarith, by have := hχ0 k z; linarith⟩
              have h2 : ‖f z‖ ≤ Mf := hMf z (Set.mem_union_left _ hz)
              apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2
                (norm_nonneg _) (by positivity)
          _ = ‖(fderiv ℝ φ z) v‖ * Mf := by ring
      · have hznot : z ∉ tsupport (fun x => (fderiv ℝ φ x) v) :=
          fun hmem => hz (tsupport_fderiv_apply_subset ℝ v hmem)
        rw [image_eq_zero_of_notMem_tsupport hznot]
        simp
    · -- pointwise a.e. convergence: away from `p` the cutoff is eventually zero
      have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ p := by
        rw [MeasureTheory.ae_iff]
        have : {z : ℂ | ¬z ≠ p} = {p} := by
          ext z
          simp [Set.mem_singleton_iff]
        rw [this]
        exact measure_singleton p
      filter_upwards [hae] with z hz
      have hev : ∀ᶠ k in Filter.atTop, χs k z = 0 := by
        have hzp : 0 < dist z p := dist_pos.mpr hz
        have hev1 : ∀ᶠ k in Filter.atTop, δs k < dist z p / 2 :=
          hδtend.eventually (eventually_lt_nhds (by positivity))
        filter_upwards [hev1] with k hk
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχsupp k hmem
        rw [Metric.mem_closedBall] at this
        nlinarith
      apply Filter.Tendsto.congr'
        (Filter.EventuallyEq.symm ?_) tendsto_const_nhds
      filter_upwards [hev] with k hk
      rw [hk]
      simp
  -- ==================== Limit (B): `Bk → 0`. ====================
  have hB : Filter.Tendsto Bk Filter.atTop (nhds 0) := by
    set vb : ℝ := (volume (Metric.ball (0 : ℂ) 1)).toReal with hvbdef
    have hvb0 : 0 ≤ vb := ENNReal.toReal_nonneg
    have htend : Filter.Tendsto
        (fun k => Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * δs k)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k => Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * δs k)
          Filter.atTop (nhds (Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * 0)) :=
        hδtend.const_mul _
      simpa using h1
    refine squeeze_zero_norm (fun k => ?_) htend
    -- the per-`k` bound
    have hvanish : ∀ z ∉ Metric.closedBall p (3 * δs k / 2),
        (φ z * ((fderiv ℝ (χs k) z) v)) • f z = 0 := by
      intro z hz
      rw [hχfd0 k z hz]
      simp
    have hBk_eq : Bk k = ∫ z in Metric.closedBall p (3 * δs k / 2),
        (φ z * ((fderiv ℝ (χs k) z) v)) • f z := by
      rw [hBkdef]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hvanish).symm
    have hMφ0 : 0 ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
    have hCb0 : (0:ℝ) ≤ ((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖ := by positivity
    have hptbd : ∀ z ∈ Metric.closedBall p (3 * δs k / 2),
        ‖(φ z * ((fderiv ℝ (χs k) z) v)) • f z‖
          ≤ Mφ * (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * Mf := by
      intro z hz
      have hzKK : z ∈ KK := by
        apply Set.mem_union_right
        rw [Metric.mem_closedBall] at hz ⊢
        have := hδle k
        nlinarith
      calc ‖(φ z * ((fderiv ℝ (χs k) z) v)) • f z‖
          = |φ z| * ‖(fderiv ℝ (χs k) z) v‖ * ‖f z‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        _ ≤ Mφ * (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * Mf := by
            have h1 : |φ z| ≤ Mφ := by
              have := hMφ z
              rwa [Real.norm_eq_abs] at this
            apply mul_le_mul (mul_le_mul h1 (hχfd k z) (norm_nonneg _) hMφ0)
              (hMf z hzKK) (norm_nonneg _) (by positivity)
    have hvol : volume (Metric.closedBall p (3 * δs k / 2)) < ⊤ :=
      (isCompact_closedBall _ _).measure_lt_top
    have hbd := norm_setIntegral_le_of_norm_le_const (μ := volume) hvol hptbd
    rw [← hBk_eq] at hbd
    refine le_trans hbd ?_
    -- compute the volume and rearrange
    have hrad : (0:ℝ) ≤ 3 * δs k / 2 := by positivity
    have hvol_eq : (volume : Measure ℂ).real (Metric.closedBall p (3 * δs k / 2))
        = (3 * δs k / 2) ^ 2 * vb := by
      rw [measureReal_def, Measure.addHaar_closedBall _ _ hrad, Complex.finrank_real_complex]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hvbdef]
    rw [hvol_eq]
    apply le_of_eq
    have hkey : (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * ((3 * δs k / 2) ^ 2 * vb)
        = ((C₀ / δ₀) * ‖v‖) * (9 / 4 * (((k:ℝ)+1) * δs k) * δs k * vb) := by ring
    calc Mφ * (((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * Mf * ((3 * δs k / 2) ^ 2 * vb)
        = Mφ * Mf * ((((k:ℝ)+1) * (C₀ / δ₀) * ‖v‖) * ((3 * δs k / 2) ^ 2 * vb)) := by ring
      _ = Mφ * Mf * (((C₀ / δ₀) * ‖v‖) * (9 / 4 * δ₀ * δs k * vb)) := by
          rw [hkey, hδid k]
      _ = Mφ * ((C₀ / δ₀) * ‖v‖) * Mf * (9 / 4 * δ₀ * vb) * δs k := by ring
  -- ==================== Limit (C): `Ck → ∫ φ • g`. ====================
  have hgK : IntegrableOn g K volume := by
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp ((hg K hKΩ hKc).mono_exponent (by norm_num))
  have hgasm : AEStronglyMeasurable g (volume.restrict K) := (hg K hKΩ hKc).1
  have hC : Filter.Tendsto Ck Filter.atTop (nhds (∫ z, φ z • g z)) := by
    rw [hCkdef]
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (K.indicator (fun z => Mφ * ‖g z‖))
    · intro k
      have heq : (fun z => φs k z • g z) = K.indicator (fun z => φs k z • g z) := by
        funext z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
          rw [hφsdef]
          simp [hφz]
      rw [heq]
      rw [aestronglyMeasurable_indicator_iff hKc.measurableSet]
      exact ((hφs_sm k).continuous.aestronglyMeasurable.restrict).smul hgasm
    · exact MeasureTheory.IntegrableOn.integrable_indicator
        (hgK.norm.const_mul Mφ) hKc.measurableSet
    · intro k
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
        calc ‖φs k z • g z‖ = |φs k z| * ‖g z‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ Mφ * ‖g z‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              refine le_trans (hφs_le k z) ?_
              have := hMφ z
              rwa [Real.norm_eq_abs] at this
      · rw [Set.indicator_of_notMem hz]
        have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        have : φs k z = 0 := by rw [hφsdef]; simp [hφz]
        rw [this]
        simp
    · have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ p := by
        rw [MeasureTheory.ae_iff]
        have : {z : ℂ | ¬z ≠ p} = {p} := by
          ext z
          simp [Set.mem_singleton_iff]
        rw [this]
        exact measure_singleton p
      filter_upwards [hae] with z hz
      have hev : ∀ᶠ k in Filter.atTop, χs k z = 0 := by
        have hzp : 0 < dist z p := dist_pos.mpr hz
        have hev1 : ∀ᶠ k in Filter.atTop, δs k < dist z p / 2 :=
          hδtend.eventually (eventually_lt_nhds (by positivity))
        filter_upwards [hev1] with k hk
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχsupp k hmem
        rw [Metric.mem_closedBall] at this
        nlinarith
      apply Filter.Tendsto.congr'
        (Filter.EventuallyEq.symm ?_) tendsto_const_nhds
      filter_upwards [hev] with k hk
      rw [hφsdef]
      simp only [hk]
      ring_nf
  -- ==================== Assembly. ====================
  have hAB : Filter.Tendsto (fun k => Ak k - Bk k) Filter.atTop
      (nhds ((∫ z, ((fderiv ℝ φ z) v) • f z) - 0)) := hA.sub hB
  have hnegC : Filter.Tendsto (fun k => - Ck k) Filter.atTop
      (nhds (- ∫ z, φ z • g z)) := hC.neg
  have heq : (fun k => Ak k - Bk k) = fun k => - Ck k := funext hIk'
  rw [heq] at hAB
  have := tendsto_nhds_unique hAB hnegC
  rw [sub_zero] at this
  exact this

end RiemannDynamics

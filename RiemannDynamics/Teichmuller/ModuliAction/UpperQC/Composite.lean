/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.UpperQC.Basic

/-!
# Weak derivatives and holomorphy of quasiconformal composites

Weak directional derivatives compose with quasiconformal maps, cutoffs and the
Wirtinger cancellation feed the holomorphy of the composite, and a holomorphic
self-map of the upper half plane arising this way is a real Möbius map.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

-- Instantiating the two abstract limit lemmas over the mollified frames is a heavy
-- elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The weak chain rule assembles the three mollification steps in one declaration;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Weak chain rule for the composition of a compactly supported
continuous `W^{1,2}` function with a plane quasiconformal map, in the directions `1, I`. -/
theorem hasWeakDirDeriv_comp_qc
    {q : ℂ → ℂ} {bq : BeltramiCoeff} (hq : IsQCAnalytic q bq)
    {e : ℂ} (he : e = 1 ∨ e = Complex.I)
    {qe : ℂ → ℂ} (hqe : HasWeakDirDeriv e qe q Set.univ) (hqem : Measurable qe)
    (hqe2 : MemLpLocOn qe 2 Set.univ)
    {F Fx Fy : ℂ → ℂ} (hFc : Continuous F) (hFsupp : HasCompactSupport F)
    (hFwg : HasWeakGradient Fx Fy F Set.univ)
    (hFxm : Measurable Fx) (hFym : Measurable Fy)
    (hFx2 : MemLp Fx 2 volume) (hFy2 : MemLp Fy 2 volume) :
    HasWeakDirDeriv e
      (fun w => (qe w).re • Fx (q w) + (qe w).im • Fy (q w)) (fun w => F (q w))
      Set.univ := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hone_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one]
    exact WithTop.coe_le_coe.mpr le_top
  have htop_add : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hqcont : Continuous q := hq.1.1.continuous
  have hqloc : MeasureTheory.LocallyIntegrable q volume := hqcont.locallyIntegrable
  have hqeloc : MeasureTheory.LocallyIntegrable qe volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hqe2 k (Set.subset_univ k) hk).mono_exponent (by norm_num))
  have hFloc : MeasureTheory.LocallyIntegrable F volume := hFc.locallyIntegrable
  have hFxloc : MeasureTheory.LocallyIntegrable Fx volume :=
    hFx2.locallyIntegrable (by norm_num)
  have hFyloc : MeasureTheory.LocallyIntegrable Fy volume :=
    hFy2.locallyIntegrable (by norm_num)
  have henorm : ‖e‖ = 1 := by
    rcases he with rfl | rfl
    · simp
    · simp
  have hae : ∀ᵐ w : ℂ, (fderiv ℝ q w) e = qe w := by
    refine fderiv_ae_eq_weakDirDeriv hqe ?_ hq.ae_differentiableAt he hqloc
    rwa [MeasureTheory.locallyIntegrableOn_univ]
  obtain ⟨MF, hMF⟩ := hFc.bounded_above_of_compact_support hFsupp
  -- The bump family and the mollified outer maps.
  set Φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := 1 / (n + 2), rOut := 1 / (n + 1),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        have h1 : (0 : ℝ) < n + 1 := by positivity
        exact one_div_lt_one_div_of_lt h1 (by nlinarith) } with hΦdef
  have hΦr : Filter.Tendsto (fun n => (Φ n).rOut) Filter.atTop (nhds 0) := by
    have : (fun n : ℕ => (Φ n).rOut) = fun n : ℕ => 1 / ((n : ℝ) + 1) := rfl
    rw [this]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set ρ : ℕ → ℂ → ℝ := fun n => (Φ n).normed volume with hρdef
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (Φ n).contDiff_normed
  have hρcs : ∀ n, HasCompactSupport (ρ n) := fun n => (Φ n).hasCompactSupport_normed
  set Fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) F L volume with hFndef
  have hFnsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fn n) := fun n =>
    (hρcs n).contDiff_convolution_left L (hρsm n) hFloc
  have hFncs : ∀ n, HasCompactSupport (Fn n) := fun n =>
    (hρcs n).convolution L hFsupp
  have hFnpt : ∀ p : ℂ, Filter.Tendsto (fun n => Fn n p) Filter.atTop (nhds (F p)) :=
    fun p => ContDiffBump.convolution_tendsto_right_of_continuous hΦr hFc p
  -- Uniform bound on the mollified outer maps.
  have hFnbd : ∀ n z, ‖Fn n z‖ ≤ MF := by
    intro n z
    have hce : ConvolutionExistsAt (ρ n) F z L volume :=
      ((hρcs n).convolutionExists_left L ((Φ n).continuous_normed) hFloc) z
    have h1 : ‖Fn n z‖ ≤ ∫ t, ‖(ρ n) t • F (z - t)‖ := by
      rw [hFndef]
      exact norm_integral_le_integral_norm _
    have h2 : ∫ t, ‖(ρ n) t • F (z - t)‖ ≤ ∫ t, (ρ n) t * MF := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
        (((Φ n).integrable_normed).mul_const MF) ?_
      refine Filter.Eventually.of_forall fun t => ?_
      change ‖(ρ n) t • F (z - t)‖ ≤ (ρ n) t * MF
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((Φ n).nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hMF _) ((Φ n).nonneg_normed t)
    have h3 : ∫ t, (ρ n) t * MF = MF := by
      rw [MeasureTheory.integral_mul_const, (Φ n).integral_normed, one_mul]
    calc ‖Fn n z‖ ≤ ∫ t, ‖(ρ n) t • F (z - t)‖ := h1
      _ ≤ ∫ t, (ρ n) t * MF := h2
      _ = MF := h3
  -- The frame sequences: partial derivatives of the mollified outer maps.
  set GX : ℕ → ℂ → ℂ := fun n p => (fderiv ℝ (Fn n) p) 1 with hGXdef
  set GY : ℕ → ℂ → ℂ := fun n p => (fderiv ℝ (Fn n) p) Complex.I with hGYdef
  have hDFncont : ∀ n, Continuous (fderiv ℝ (Fn n)) := fun n =>
    ((hFnsm n).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) htop_add).continuous
  have hGXc : ∀ n, Continuous (GX n) := fun n =>
    (ContinuousLinearMap.apply ℝ ℂ 1).continuous.comp (hDFncont n)
  have hGYc : ∀ n, Continuous (GY n) := fun n =>
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous.comp (hDFncont n)
  have hGbd : ∀ n (u : ℂ), ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖(fderiv ℝ (Fn n) p) u‖ ≤ M := by
    intro n u
    have hcont : Continuous fun p => (fderiv ℝ (Fn n) p) u :=
      (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp (hDFncont n)
    have hcs : HasCompactSupport fun p => (fderiv ℝ (Fn n) p) u := by
      have h1 : Function.support (fun p => (fderiv ℝ (Fn n) p) u)
          ⊆ tsupport (fderiv ℝ (Fn n)) := by
        intro p hp
        have h2 : fderiv ℝ (Fn n) p ≠ 0 := by
          intro h0
          refine hp ?_
          change (fderiv ℝ (Fn n) p) u = 0
          rw [h0]
          rfl
        exact subset_tsupport _ h2
      refine IsCompact.of_isClosed_subset ((hFncs n).fderiv ℝ) (isClosed_tsupport _) ?_
      exact closure_minimal h1 (isClosed_tsupport _)
    obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), hM⟩
  -- The `L²` convergence of the frames, from the derivative-of-mollification identity.
  have hFnx : ∀ n p, GX n p = MeasureTheory.convolution (ρ n) Fx L volume p :=
    fun n p => fderiv_convolution_normed_apply_eq hFwg.1 hFloc hFxloc (hρsm n) (hρcs n) p
  have hFny : ∀ n p, GY n p = MeasureTheory.convolution (ρ n) Fy L volume p :=
    fun n p => fderiv_convolution_normed_apply_eq hFwg.2 hFloc hFyloc (hρsm n) (hρcs n) p
  have hX2 : Filter.Tendsto (fun n => eLpNorm (fun z => GX n z - Fx z) 2 volume)
      Filter.atTop (nhds 0) := by
    have hcong : (fun n => eLpNorm (fun z => GX n z - Fx z) 2 volume)
        = fun n => eLpNorm
          (MeasureTheory.convolution (ρ n) Fx L volume - Fx) 2 volume := by
      funext n
      congr 1
      funext z
      rw [hFnx n z]
      rfl
    rw [hcong]
    exact eLpNorm_convolution_normed_sub_tendsto_zero hFx2 Φ hΦr
  have hY2 : Filter.Tendsto (fun n => eLpNorm (fun z => GY n z - Fy z) 2 volume)
      Filter.atTop (nhds 0) := by
    have hcong : (fun n => eLpNorm (fun z => GY n z - Fy z) 2 volume)
        = fun n => eLpNorm
          (MeasureTheory.convolution (ρ n) Fy L volume - Fy) 2 volume := by
      funext n
      congr 1
      funext z
      rw [hFny n z]
      rfl
    rw [hcong]
    exact eLpNorm_convolution_normed_sub_tendsto_zero hFy2 Φ hΦr
  -- The test-function identity.
  intro φ hφ hφc hφs
  set S : Set ℂ := tsupport φ with hSdef
  have hScomp : IsCompact S := hφc
  have hSm : MeasurableSet S := (isClosed_tsupport φ).measurableSet
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Mφ, hMφ⟩ := hφcont.bounded_above_of_compact_support hφc
  have hφzero : ∀ z, z ∉ S → φ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (subset_tsupport φ hne)
  have hqeS : IntegrableOn qe S volume := hqeloc.integrableOn_isCompact hScomp
  have hdφcont : Continuous fun z => (fderiv ℝ φ z) e := by
    have h1 : Continuous (fderiv ℝ φ) :=
      (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by
        rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])).continuous
    exact (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp h1
  have hdφsupp : Function.support (fun z => (fderiv ℝ φ z) e) ⊆ S := by
    intro z hz
    have h1 : fderiv ℝ φ z ≠ 0 := by
      intro h0
      refine hz ?_
      change (fderiv ℝ φ z) e = 0
      rw [h0]
      rfl
    exact (support_fderiv_subset ℝ) h1
  -- The level-`n` identities from the smooth chain rule.
  have key1 : ∀ n : ℕ, ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z)
      = -∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)) := by
    intro n
    exact comp_smooth_qc hq hqe hqem hqe2 (hFnsm n) (hFncs n) φ hφ hφc
      (by intro z _; trivial)
  -- The left-hand limit.
  have hLHS : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z))
      Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) e) • F (q z))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun z => ‖(fderiv ℝ φ z) e‖ * MF) ?_ ?_ ?_ ?_
    · intro n
      exact (hdφcont.smul ((hFnsm n).continuous.comp hqcont)).aestronglyMeasurable
    · have hbcont : Continuous fun z => ‖(fderiv ℝ φ z) e‖ * MF :=
        (hdφcont.norm).mul continuous_const
      have hbcs : HasCompactSupport fun z => ‖(fderiv ℝ φ z) e‖ * MF := by
        have h1 : Function.support (fun z => ‖(fderiv ℝ φ z) e‖ * MF) ⊆ S := by
          intro z hz
          refine hdφsupp ?_
          intro h0
          have h0' : (fderiv ℝ φ z) e = 0 := h0
          refine hz ?_
          change ‖(fderiv ℝ φ z) e‖ * MF = 0
          rw [h0']
          simp
        refine IsCompact.of_isClosed_subset hScomp (isClosed_tsupport _) ?_
        exact closure_minimal h1 (isClosed_tsupport φ)
      exact hbcont.integrable_of_hasCompactSupport hbcs
    · intro n
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hFnbd n _) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun z => ?_
      exact Filter.Tendsto.const_smul (hFnpt (q z)) _
  -- The right-hand limit, from the `L²` pairing lemma.
  have hRHS : Filter.Tendsto
      (fun n => ∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)))
      Filter.atTop
      (nhds (∫ z, φ z • ((qe z).re • Fx (q z) + (qe z).im • Fy (q z)))) :=
    pairing_tendsto_L2 hq henorm hqem hae hScomp hSm hφcont hφzero hMφ hqeS
      hFxm hFym hFx2 hFy2 hGXc hGYc (fun n => hGbd n 1) (fun n => hGbd n Complex.I)
      hX2 hY2
  -- Conclude by uniqueness of limits.
  have h1 : (fun n => ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z))
      = fun n => -∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)) :=
    funext key1
  have h2 : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z))
      Filter.atTop
      (nhds (-∫ z, φ z • ((qe z).re • Fx (q z) + (qe z).im • Fy (q z)))) := by
    rw [h1]
    exact hRHS.neg
  exact tendsto_nhds_unique hLHS h2

-- The cutoff transfer to the plane lemma and the covering assembly are one long
-- elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The classical-derivative bridge runs a Lebesgue-point argument over the open set;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- On an open set, the classical directional derivative of an
almost-everywhere differentiable function agrees almost everywhere with any locally
integrable weak directional derivative, by cutoff transfer to the plane statement. -/
theorem fderiv_ae_eq_weakDirDeriv_on
    {v g : ℂ → ℂ} {ed : ℂ} (hed : ed = 1 ∨ ed = Complex.I)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hg : HasWeakDirDeriv ed g v Ω)
    (hgloc : MeasureTheory.LocallyIntegrableOn g Ω volume)
    (hvcont : ContinuousOn v Ω)
    (hdiff : ∀ᵐ z ∂(volume.restrict Ω), DifferentiableAt ℝ v z) :
    ∀ᵐ z ∂(volume.restrict Ω), (fderiv ℝ v z) ed = g z := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hdiff' : ∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ v z :=
    (ae_restrict_iff' hΩ.measurableSet).mp hdiff
  -- The per-ball statement.
  have hball : ∀ z₀ : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall z₀ (2*r) ⊆ Ω →
      ∀ᵐ z : ℂ, z ∈ Metric.ball z₀ r → (fderiv ℝ v z) ed = g z := by
    intro z₀ r hr hsub
    -- The cutoff bump.
    set χb : ContDiffBump z₀ :=
      { rIn := (3/2) * r, rOut := (9/5) * r,
        rIn_pos := by linarith,
        rIn_lt_rOut := by linarith } with hχdef
    set χ : ℂ → ℝ := fun z => χb z with hχfun
    have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := χb.contDiff
    have hχsupp : Function.support χ = Metric.ball z₀ ((9/5) * r) := χb.support_eq
    have hχone : ∀ z ∈ Metric.closedBall z₀ ((3/2) * r), χ z = 1 := fun z hz =>
      χb.one_of_mem_closedBall hz
    have htsχ : tsupport χ ⊆ Metric.closedBall z₀ ((9/5) * r) := by
      rw [tsupport, hχsupp]
      exact Metric.closure_ball_subset_closedBall
    have htsΩ : tsupport χ ⊆ Ω := by
      refine subset_trans htsχ (subset_trans ?_ hsub)
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      linarith
    have hcompl : ∀ z : ℂ, z ∉ tsupport χ → χ z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport hz
    -- The plane cover: `ℂ = Ω ∪ (tsupport χ)ᶜ`.
    have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport χ := by
      intro z
      by_cases hz : z ∈ tsupport χ
      · exact Or.inl (htsΩ hz)
      · exact Or.inr hz
    -- The localized function and its weak derivative.
    set Fc : ℂ → ℂ := fun z => χ z • v z with hFcdef
    set Fg : ℂ → ℂ := fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z with hFgdef
    have hχcont : Continuous χ := hχsm.continuous
    have hdχcont : Continuous fun z => (fderiv ℝ χ z) ed := by
      have h1 : Continuous (fderiv ℝ χ) :=
        (hχsm.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
          (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
      exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
    have hdχsupp : ∀ z : ℂ, z ∉ tsupport χ → (fderiv ℝ χ z) ed = 0 := by
      intro z hz
      have h1 : fderiv ℝ χ z = 0 := by
        by_contra hne
        exact hz ((support_fderiv_subset ℝ)
          (by simpa [Function.mem_support] using hne))
      rw [h1]
      rfl
    have hKχ : IsCompact (tsupport χ) :=
      IsCompact.of_isClosed_subset (isCompact_closedBall z₀ ((9/5) * r))
        (isClosed_tsupport χ) htsχ
    -- Gluing continuity: continuous on `Ω`, vanishing off the support of the cutoff.
    have htop_ne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hcont_of : ∀ H : ℂ → ℂ, (∀ z, z ∈ Ω → ContinuousAt H z) →
        (∀ z, z ∉ tsupport χ → H z = 0) → Continuous H := by
      intro H h1 h2
      rw [continuous_iff_continuousAt]
      intro z
      rcases hcover z with hzΩ | hzout
      · exact h1 z hzΩ
      · have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
        have hev : ∀ᶠ w in nhds z, H w = 0 := by
          filter_upwards [hopen.mem_nhds hzout] with w hw
          exact h2 w hw
        refine ContinuousAt.congr (f := fun _ : ℂ => (0 : ℂ)) continuousAt_const ?_
        filter_upwards [hev] with w hw
        exact hw.symm
    have hFccont : Continuous Fc := by
      refine hcont_of Fc ?_ ?_
      · intro z hzΩ
        exact (hχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
      · intro z hz
        change χ z • v z = 0
        rw [hcompl z hz]
        exact zero_smul ℝ _
    -- Global integrability of the cutoff-weighted weak derivative.
    have hgK : IntegrableOn g (tsupport χ) volume :=
      hgloc.integrableOn_compact_subset htsΩ hKχ
    have hbmul : ∀ (b : ℂ → ℝ) (Mb : ℝ), Continuous b → (∀ z, |b z| ≤ Mb) →
        (∀ z, z ∉ tsupport χ → b z = 0) →
        Integrable (fun z => b z • g z) volume := by
      intro b Mb hbc hbM hb0
      have hmeas : AEStronglyMeasurable (fun z => b z • g z)
          (volume.restrict (tsupport χ)) :=
        (hbc.aestronglyMeasurable).smul hgK.aestronglyMeasurable
      have hint : IntegrableOn (fun z => b z • g z) (tsupport χ) volume := by
        refine MeasureTheory.Integrable.mono' (hgK.norm.const_mul Mb) hmeas ?_
        refine Filter.Eventually.of_forall fun z => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbM z) (norm_nonneg _)
      have hsupp : Function.support (fun z => b z • g z) ⊆ tsupport χ := by
        intro z hz
        by_contra hzout
        rw [Function.mem_support] at hz
        rw [hb0 z hzout] at hz
        exact hz (zero_smul ℝ _)
      exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hint
    -- The weak-derivative identity for the localization `Fc` on the whole plane.
    have hFcweak : HasWeakDirDeriv ed Fg Fc Set.univ := by
      intro φ hφ hφc hφs
      have hφcont : Continuous φ := hφ.continuous
      obtain ⟨Mφ, hMφ⟩ := hφcont.bounded_above_of_compact_support hφc
      have hφχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z * χ z) :=
        hφ.mul hχsm
      have hφχcs : HasCompactSupport (fun z => φ z * χ z) := by
        refine HasCompactSupport.intro hφc ?_
        intro z hz
        change φ z * χ z = 0
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      have hφχsupp : tsupport (fun z => φ z * χ z) ⊆ Ω := by
        refine subset_trans (closure_minimal ?_ (isClosed_tsupport χ)) htsΩ
        intro z hz
        rw [Function.mem_support] at hz
        have hχz : χ z ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
        exact subset_tsupport χ hχz
      have hid := hg (fun z => φ z * χ z) hφχsm hφχcs hφχsupp
      -- The product rule for the localized test function.
      have hfd : ∀ z, (fderiv ℝ (fun w => φ w * χ w) z) ed
          = φ z * ((fderiv ℝ χ z) ed) + χ z * ((fderiv ℝ φ z) ed) := by
        intro z
        have hφd : DifferentiableAt ℝ φ z :=
          (hφ.differentiable htop_ne).differentiableAt
        have hχd : DifferentiableAt ℝ χ z :=
          (hχsm.differentiable htop_ne).differentiableAt
        have h1 : (fun w => φ w * χ w) = φ * χ := rfl
        rw [h1, fderiv_mul hφd hχd]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul]
      -- The three integrable pieces.
      have hdφcont : Continuous fun z => (fderiv ℝ φ z) ed := by
        have h1 : Continuous (fderiv ℝ φ) :=
          (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
            (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
        exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
      have hI1cont : Continuous fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
        refine hcont_of _ ?_ ?_
        · intro z hzΩ
          exact ((hφcont.mul hdχcont).continuousAt).smul
            (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
        · intro z hz
          rw [hdχsupp z hz, mul_zero]
          exact zero_smul ℝ _
      have hI1cs : HasCompactSupport fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
        refine HasCompactSupport.intro hKχ ?_
        intro z hz
        rw [hdχsupp z hz, mul_zero]
        exact zero_smul ℝ _
      have hI1int : Integrable (fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z) volume :=
        hI1cont.integrable_of_hasCompactSupport hI1cs
      have hI2cont : Continuous fun z => ((fderiv ℝ φ z) ed) • Fc z :=
        hdφcont.smul hFccont
      have hI2cs : HasCompactSupport fun z => ((fderiv ℝ φ z) ed) • Fc z := by
        refine HasCompactSupport.intro hφc ?_
        intro z hz
        have h1 : fderiv ℝ φ z = 0 := by
          by_contra hne
          exact hz ((support_fderiv_subset ℝ)
            (by simpa [Function.mem_support] using hne))
        have h2 : (fderiv ℝ φ z) ed = 0 := by
          rw [h1]
          rfl
        rw [h2]
        exact zero_smul ℝ _
      have hI2int : Integrable (fun z => ((fderiv ℝ φ z) ed) • Fc z) volume :=
        hI2cont.integrable_of_hasCompactSupport hI2cs
      have hφχg_int : Integrable (fun z => (φ z * χ z) • g z) volume := by
        refine hbmul (fun z => φ z * χ z) (Mφ * 1) (hφcont.mul hχcont) ?_ ?_
        · intro z
          rw [abs_mul]
          have h1 : |φ z| ≤ Mφ := by
            have := hMφ z
            rwa [Real.norm_eq_abs] at this
          have h2 : |χ z| ≤ 1 := by
            rw [abs_of_nonneg (χb.nonneg)]
            exact χb.le_one
          have h3 : (0:ℝ) ≤ |φ z| := abs_nonneg _
          nlinarith [abs_nonneg (χ z)]
        · intro z hz
          change φ z * χ z = 0
          rw [hcompl z hz, mul_zero]
      have hI1g_int : Integrable
          (fun z => (φ z * χ z) • g z + (φ z * ((fderiv ℝ χ z) ed)) • v z) volume :=
        hφχg_int.add hI1int
      -- Assemble the identity.
      have hsplit : ∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
          = (∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z)
            + ∫ z, ((fderiv ℝ φ z) ed) • Fc z := by
        rw [← MeasureTheory.integral_add hI1int hI2int]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        change ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
          = (φ z * ((fderiv ℝ χ z) ed)) • v z + ((fderiv ℝ φ z) ed) • (χ z • v z)
        rw [hfd z]
        module
      have hgoal : ∫ z, ((fderiv ℝ φ z) ed) • Fc z = -∫ z, φ z • Fg z := by
        have h1 : ∫ z, ((fderiv ℝ φ z) ed) • Fc z
            = (∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z)
              - ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
          rw [hsplit]
          ring
        rw [h1, hid]
        have h2 : ∫ z, φ z • Fg z
            = (∫ z, (φ z * χ z) • g z) + ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
          rw [← MeasureTheory.integral_add hφχg_int hI1int]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          change φ z • (χ z • g z + ((fderiv ℝ χ z) ed) • v z)
            = (φ z * χ z) • g z + (φ z * ((fderiv ℝ χ z) ed)) • v z
          module
        rw [h2]
        ring
      exact hgoal
    -- Global almost-everywhere differentiability and integrability data.
    have hFcdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ Fc z := by
      filter_upwards [hdiff'] with z hz
      rcases hcover z with hzΩ | hzout
      · have hχd : DifferentiableAt ℝ χ z :=
          (hχsm.differentiable htop_ne).differentiableAt
        exact hχd.smul (hz hzΩ)
      · have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
        have hev : Fc =ᶠ[nhds z] fun _ => (0 : ℂ) := by
          filter_upwards [hopen.mem_nhds hzout] with w hw
          change χ w • v w = 0
          rw [hcompl w hw]
          exact zero_smul ℝ _
        exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr
          (differentiableAt_const 0)
    have hFcloc : MeasureTheory.LocallyIntegrable Fc volume := hFccont.locallyIntegrable
    have hFgint : Integrable Fg volume := by
      have h1 : Integrable (fun z => χ z • g z) volume := by
        refine hbmul χ 1 hχcont ?_ ?_
        · intro z
          rw [abs_of_nonneg (χb.nonneg)]
          exact χb.le_one
        · intro z hz
          exact hcompl z hz
      have h2cont : Continuous fun z => ((fderiv ℝ χ z) ed) • v z := by
        refine hcont_of _ ?_ ?_
        · intro z hzΩ
          exact (hdχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
        · intro z hz
          rw [hdχsupp z hz]
          exact zero_smul ℝ _
      have h2cs : HasCompactSupport fun z => ((fderiv ℝ χ z) ed) • v z := by
        refine HasCompactSupport.intro hKχ ?_
        intro z hz
        rw [hdχsupp z hz]
        exact zero_smul ℝ _
      exact h1.add (h2cont.integrable_of_hasCompactSupport h2cs)
    have hFgloc : MeasureTheory.LocallyIntegrableOn Fg Set.univ volume := by
      rw [MeasureTheory.locallyIntegrableOn_univ]
      exact hFgint.locallyIntegrable
    -- The plane statement applies to the localization.
    have haefd : ∀ᵐ z : ℂ, (fderiv ℝ Fc z) ed = Fg z :=
      fderiv_ae_eq_weakDirDeriv hFcweak hFgloc hFcdiff hed hFcloc
    -- Localize back to the small ball.
    filter_upwards [haefd] with z hz hzB
    have hmemIn : Metric.ball z₀ r ⊆ Metric.ball z₀ ((3/2) * r) :=
      Metric.ball_subset_ball (by linarith)
    have hopenIn : IsOpen (Metric.ball z₀ ((3/2) * r)) := Metric.isOpen_ball
    have hnb : Metric.ball z₀ ((3/2) * r) ∈ nhds z := hopenIn.mem_nhds (hmemIn hzB)
    have hFcev : Fc =ᶠ[nhds z] v := by
      filter_upwards [hnb] with w hw
      change χ w • v w = v w
      rw [hχone w (Metric.ball_subset_closedBall hw)]
      exact one_smul ℝ _
    have hχev : χ =ᶠ[nhds z] fun _ => (1 : ℝ) := by
      filter_upwards [hnb] with w hw
      exact hχone w (Metric.ball_subset_closedBall hw)
    have hfd1 : fderiv ℝ Fc z = fderiv ℝ v z := hFcev.fderiv_eq
    have hfd2 : fderiv ℝ χ z = 0 := by
      rw [hχev.fderiv_eq]
      exact fderiv_const_apply 1
    have hχz1 : χ z = 1 := hχone z (Metric.ball_subset_closedBall (hmemIn hzB))
    rw [hfd1] at hz
    rw [hz]
    change χ z • g z + ((fderiv ℝ χ z) ed) • v z = g z
    rw [hχz1, hfd2]
    simp
  -- Countable covering assembly.
  have hchoice : ∀ p : ℂ, p ∈ Ω → ∃ r : ℝ, 0 < r ∧ Metric.closedBall p (2*r) ⊆ Ω := by
    intro p hp
    obtain ⟨ε, hε, hballsub⟩ := Metric.isOpen_iff.mp hΩ p hp
    refine ⟨ε/3, by linarith, ?_⟩
    intro w hw
    refine hballsub ?_
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith
  classical
  set rad : Ω → ℝ := fun p => (hchoice p.1 p.2).choose with hraddef
  have hrad : ∀ p : Ω, 0 < rad p ∧ Metric.closedBall p.1 (2 * rad p) ⊆ Ω := fun p =>
    (hchoice p.1 p.2).choose_spec
  set s : Ω → Set ℂ := fun p => Metric.ball p.1 (rad p) with hsdef
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable s
    (fun p => Metric.isOpen_ball)
  have hcov : Ω ⊆ ⋃ p ∈ T, s p := by
    rw [hTeq]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hrad ⟨z, hz⟩).1⟩
  rw [ae_restrict_iff' hΩ.measurableSet]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ⋃ p ∈ T, {z : ℂ | z ∈ s p ∧ ¬ (fderiv ℝ v z) ed = g z})
    ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, not_forall] at hz
    obtain ⟨hzΩ, hzne⟩ := hz
    obtain ⟨p, hpT, hps⟩ := Set.mem_iUnion₂.mp (hcov hzΩ)
    exact Set.mem_iUnion₂.mpr ⟨p, hpT, ⟨hps, hzne⟩⟩
  · rw [measure_biUnion_null_iff hTc]
    intro p _
    have hp := hball p.1 (rad p) (hrad p).1 (hrad p).2
    rw [MeasureTheory.ae_iff] at hp
    refine measure_mono_null ?_ hp
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    intro hcontra
    exact hz.2 (hcontra hz.1)

-- The localized integration-by-parts assembly is one long elaboration; the raised
-- budget is required.
set_option maxHeartbeats 400000 in
-- The cutoff package discharges support, smoothness, and derivative bounds together;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- The cutoff package. For a smooth compactly supported cutoff `χ` with
support in the open set `Ω`, the localization `χ • v` of a function with weak
directional derivative `g` on `Ω` has the Leibniz combination as a weak directional
derivative on the whole plane, and the two localized pieces are continuous. -/
theorem cutoff_hasWeakDirDeriv
    {v g : ℂ → ℂ} {ed : ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hg : HasWeakDirDeriv ed g v Ω)
    (hgloc : MeasureTheory.LocallyIntegrableOn g Ω volume)
    (hvcont : ContinuousOn v Ω)
    {χ : ℂ → ℝ} (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχcs : HasCompactSupport χ) (htsΩ : tsupport χ ⊆ Ω)
    (hχ1 : ∀ z, |χ z| ≤ 1) :
    HasWeakDirDeriv ed (fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z)
        (fun z => χ z • v z) Set.univ
      ∧ Continuous (fun z => χ z • v z)
      ∧ Continuous (fun z => ((fderiv ℝ χ z) ed) • v z)
      ∧ Integrable (fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z) volume := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have htop_ne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hχcont : Continuous χ := hχsm.continuous
  have hcompl : ∀ z : ℂ, z ∉ tsupport χ → χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport hz
  have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport χ := by
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact Or.inl (htsΩ hz)
    · exact Or.inr hz
  have hdχcont : Continuous fun z => (fderiv ℝ χ z) ed := by
    have h1 : Continuous (fderiv ℝ χ) :=
      (hχsm.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
        (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
    exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
  have hdχsupp : ∀ z : ℂ, z ∉ tsupport χ → (fderiv ℝ χ z) ed = 0 := by
    intro z hz
    have h1 : fderiv ℝ χ z = 0 := by
      by_contra hne
      exact hz ((support_fderiv_subset ℝ)
        (by simpa [Function.mem_support] using hne))
    rw [h1]
    rfl
  have hKχ : IsCompact (tsupport χ) := hχcs
  have hcont_of : ∀ H : ℂ → ℂ, (∀ z, z ∈ Ω → ContinuousAt H z) →
      (∀ z, z ∉ tsupport χ → H z = 0) → Continuous H := by
    intro H h1 h2
    rw [continuous_iff_continuousAt]
    intro z
    rcases hcover z with hzΩ | hzout
    · exact h1 z hzΩ
    · have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
      have hev : ∀ᶠ w in nhds z, H w = 0 := by
        filter_upwards [hopen.mem_nhds hzout] with w hw
        exact h2 w hw
      refine ContinuousAt.congr (f := fun _ : ℂ => (0 : ℂ)) continuousAt_const ?_
      filter_upwards [hev] with w hw
      exact hw.symm
  have hFccont : Continuous (fun z => χ z • v z) := by
    refine hcont_of _ ?_ ?_
    · intro z hzΩ
      exact (hχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
    · intro z hz
      change χ z • v z = 0
      rw [hcompl z hz]
      exact zero_smul ℝ _
  have hdχvcont : Continuous (fun z => ((fderiv ℝ χ z) ed) • v z) := by
    refine hcont_of _ ?_ ?_
    · intro z hzΩ
      exact (hdχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
    · intro z hz
      change ((fderiv ℝ χ z) ed) • v z = 0
      rw [hdχsupp z hz]
      exact zero_smul ℝ _
  have hgK : IntegrableOn g (tsupport χ) volume :=
    hgloc.integrableOn_compact_subset htsΩ hKχ
  have hbmul : ∀ (b : ℂ → ℝ) (Mb : ℝ), Continuous b → (∀ z, |b z| ≤ Mb) →
      (∀ z, z ∉ tsupport χ → b z = 0) →
      Integrable (fun z => b z • g z) volume := by
    intro b Mb hbc hbM hb0
    have hmeas : AEStronglyMeasurable (fun z => b z • g z)
        (volume.restrict (tsupport χ)) :=
      (hbc.aestronglyMeasurable).smul hgK.aestronglyMeasurable
    have hint : IntegrableOn (fun z => b z • g z) (tsupport χ) volume := by
      refine MeasureTheory.Integrable.mono' (hgK.norm.const_mul Mb) hmeas ?_
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbM z) (norm_nonneg _)
    have hsupp : Function.support (fun z => b z • g z) ⊆ tsupport χ := by
      intro z hz
      by_contra hzout
      rw [Function.mem_support] at hz
      rw [hb0 z hzout] at hz
      exact hz (zero_smul ℝ _)
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hint
  have hχg_int : Integrable (fun z => χ z • g z) volume :=
    hbmul χ 1 hχcont hχ1 hcompl
  have hdχv_cs : HasCompactSupport (fun z => ((fderiv ℝ χ z) ed) • v z) := by
    refine HasCompactSupport.intro hKχ ?_
    intro z hz
    change ((fderiv ℝ χ z) ed) • v z = 0
    rw [hdχsupp z hz]
    exact zero_smul ℝ _
  have hFg_int : Integrable (fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z) volume :=
    hχg_int.add (hdχvcont.integrable_of_hasCompactSupport hdχv_cs)
  refine ⟨?_, hFccont, hdχvcont, hFg_int⟩
  intro φ hφ hφc hφs
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Mφ, hMφ⟩ := hφcont.bounded_above_of_compact_support hφc
  have hφχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z * χ z) := hφ.mul hχsm
  have hφχcs : HasCompactSupport (fun z => φ z * χ z) := by
    refine HasCompactSupport.intro hφc ?_
    intro z hz
    change φ z * χ z = 0
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hφχsupp : tsupport (fun z => φ z * χ z) ⊆ Ω := by
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport χ)) htsΩ
    intro z hz
    rw [Function.mem_support] at hz
    have hχz : χ z ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    exact subset_tsupport χ hχz
  have hid := hg (fun z => φ z * χ z) hφχsm hφχcs hφχsupp
  have hfd : ∀ z, (fderiv ℝ (fun w => φ w * χ w) z) ed
      = φ z * ((fderiv ℝ χ z) ed) + χ z * ((fderiv ℝ φ z) ed) := by
    intro z
    have hφd : DifferentiableAt ℝ φ z := (hφ.differentiable htop_ne).differentiableAt
    have hχd : DifferentiableAt ℝ χ z := (hχsm.differentiable htop_ne).differentiableAt
    have h1 : (fun w => φ w * χ w) = φ * χ := rfl
    rw [h1, fderiv_mul hφd hχd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  have hdφcont : Continuous fun z => (fderiv ℝ φ z) ed := by
    have h1 : Continuous (fderiv ℝ φ) :=
      (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
        (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
    exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
  have hI1cont : Continuous fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    refine hcont_of _ ?_ ?_
    · intro z hzΩ
      exact ((hφcont.mul hdχcont).continuousAt).smul
        (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
    · intro z hz
      change (φ z * ((fderiv ℝ χ z) ed)) • v z = 0
      rw [hdχsupp z hz, mul_zero]
      exact zero_smul ℝ _
  have hI1cs : HasCompactSupport fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    refine HasCompactSupport.intro hKχ ?_
    intro z hz
    change (φ z * ((fderiv ℝ χ z) ed)) • v z = 0
    rw [hdχsupp z hz, mul_zero]
    exact zero_smul ℝ _
  have hI1int : Integrable (fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z) volume :=
    hI1cont.integrable_of_hasCompactSupport hI1cs
  have hI2cont : Continuous fun z => ((fderiv ℝ φ z) ed) • (χ z • v z) :=
    hdφcont.smul hFccont
  have hI2cs : HasCompactSupport fun z => ((fderiv ℝ φ z) ed) • (χ z • v z) := by
    refine HasCompactSupport.intro hφc ?_
    intro z hz
    have h1 : fderiv ℝ φ z = 0 := by
      by_contra hne
      exact hz ((support_fderiv_subset ℝ)
        (by simpa [Function.mem_support] using hne))
    have h2 : (fderiv ℝ φ z) ed = 0 := by
      rw [h1]
      rfl
    change ((fderiv ℝ φ z) ed) • (χ z • v z) = 0
    rw [h2]
    exact zero_smul ℝ _
  have hI2int : Integrable (fun z => ((fderiv ℝ φ z) ed) • (χ z • v z)) volume :=
    hI2cont.integrable_of_hasCompactSupport hI2cs
  have hφχg_int : Integrable (fun z => (φ z * χ z) • g z) volume := by
    refine hbmul (fun z => φ z * χ z) (Mφ * 1) (hφcont.mul hχcont) ?_ ?_
    · intro z
      rw [abs_mul]
      have h1 : |φ z| ≤ Mφ := by
        have := hMφ z
        rwa [Real.norm_eq_abs] at this
      have h3 : (0:ℝ) ≤ |φ z| := abs_nonneg _
      nlinarith [abs_nonneg (χ z), hχ1 z]
    · intro z hz
      change φ z * χ z = 0
      rw [hcompl z hz, mul_zero]
  have hsplit : ∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
      = (∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z)
        + ∫ z, ((fderiv ℝ φ z) ed) • (χ z • v z) := by
    rw [← MeasureTheory.integral_add hI1int hI2int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
      = (φ z * ((fderiv ℝ χ z) ed)) • v z + ((fderiv ℝ φ z) ed) • (χ z • v z)
    rw [hfd z]
    module
  have hgoal2 : ∫ z, φ z • (χ z • g z + ((fderiv ℝ χ z) ed) • v z)
      = (∫ z, (φ z * χ z) • g z) + ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    rw [← MeasureTheory.integral_add hφχg_int hI1int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change φ z • (χ z • g z + ((fderiv ℝ χ z) ed) • v z)
      = (φ z * χ z) • g z + (φ z * ((fderiv ℝ χ z) ed)) • v z
    module
  have h1 : ∫ z, ((fderiv ℝ φ z) ed) • (χ z • v z)
      = (∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z)
        - ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    rw [hsplit]
    ring
  rw [h1, hid, hgoal2]
  ring

/-- A smooth compact-set cutoff by mollification of an indicator: it is `1` on
an open neighbourhood of the compact set `K`, supported inside the open set `U`. -/
theorem smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ z, |χ z| ≤ 1) ∧
      ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ ∀ z ∈ V, χ z = 1 := by
  classical
  obtain ⟨δ, hδ0, hδsub⟩ := hK.exists_cthickening_subset_open hU hKU
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  set A : Set ℂ := Metric.cthickening (δ/2) K with hAdef
  have hAm : MeasurableSet A := (Metric.isClosed_cthickening).measurableSet
  have hAc : IsCompact A := hK.cthickening
  set ind : ℂ → ℝ := A.indicator (fun _ => (1:ℝ)) with hinddef
  have hind_int : Integrable ind volume := by
    rw [hinddef, MeasureTheory.integrable_indicator_iff hAm]
    exact integrableOn_const (hAc.measure_lt_top.ne) (by simp)
  have hindloc : MeasureTheory.LocallyIntegrable ind volume := hind_int.locallyIntegrable
  have hind01 : ∀ z, 0 ≤ ind z ∧ ind z ≤ 1 := by
    intro z
    rw [hinddef]
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz]
      norm_num
    · rw [Set.indicator_of_notMem hz]
      norm_num
  set Φδ : ContDiffBump (0 : ℂ) :=
    { rIn := δ/8, rOut := δ/4,
      rIn_pos := by linarith,
      rIn_lt_rOut := by linarith } with hΦδdef
  set ρδ : ℂ → ℝ := Φδ.normed volume with hρδdef
  have hρsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρδ := Φδ.contDiff_normed
  have hρcs : HasCompactSupport ρδ := Φδ.hasCompactSupport_normed
  set χ : ℂ → ℝ := MeasureTheory.convolution ρδ ind L volume with hχdef
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    hρcs.contDiff_convolution_left L hρsm hindloc
  have hind_cs : HasCompactSupport ind := by
    refine HasCompactSupport.intro hAc ?_
    intro z hz
    rw [hinddef, Set.indicator_of_notMem hz]
  have hχcs : HasCompactSupport χ := hρcs.convolution L hind_cs
  have hce : ∀ z, ConvolutionExistsAt ρδ ind z L volume :=
    fun z => (hρcs.convolutionExists_left L (Φδ.continuous_normed) hindloc) z
  -- Support estimate.
  have hsupp : tsupport χ ⊆ U := by
    have h1 : Function.support χ ⊆ Metric.cthickening ((3/4)*δ) K := by
      intro z hz
      have h2 := MeasureTheory.support_convolution_subset (μ := volume)
        (f := ρδ) (g := ind) L hz
      obtain ⟨b, hb, a, ha, hab⟩ := h2
      have hbball : b ∈ Metric.ball (0 : ℂ) (δ/4) := by
        rw [← Φδ.support_normed_eq (μ := volume)]
        exact hb
      have haA : a ∈ A := by
        by_contra haA
        have h0 : ind a = 0 := by rw [hinddef, Set.indicator_of_notMem haA]
        exact ha h0
      rw [Metric.mem_cthickening_iff]
      have h3 : Metric.infEDist z K ≤ Metric.infEDist a K + edist z a :=
        Metric.infEDist_le_infEDist_add_edist
      have h4 : Metric.infEDist a K ≤ ENNReal.ofReal (δ/2) := by
        rw [hAdef, Metric.mem_cthickening_iff] at haA
        exact haA
      have h5 : edist z a ≤ ENNReal.ofReal (δ/4) := by
        have h6 : z - a = b := by rw [← hab]; ring
        rw [edist_eq_enorm_sub, h6, ← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Metric.mem_ball, dist_zero_right] at hbball
        linarith
      calc Metric.infEDist z K ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/4) :=
            le_trans h3 (add_le_add h4 h5)
        _ = ENNReal.ofReal (δ/2 + δ/4) := (ENNReal.ofReal_add (by linarith)
            (by linarith)).symm
        _ ≤ ENNReal.ofReal ((3/4)*δ) := by
            refine ENNReal.ofReal_le_ofReal ?_
            linarith
    refine subset_trans (closure_minimal h1 Metric.isClosed_cthickening) ?_
    refine subset_trans (Metric.cthickening_mono (by linarith) K) hδsub
  -- Value bounds.
  have hval : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := by
    intro z
    constructor
    · rw [hχdef]
      refine integral_nonneg fun t => ?_
      have h1 := (hind01 (z - t)).1
      have h2 : 0 ≤ ρδ t := Φδ.nonneg_normed t
      simpa [hLdef, smul_eq_mul] using mul_nonneg h2 h1
    · rw [hχdef]
      have h2 : ∫ t, ρδ t * ind (z - t) ≤ ∫ t, ρδ t * 1 := by
        refine integral_mono_of_nonneg ?_ ((Φδ.integrable_normed).mul_const 1) ?_
        · refine Filter.Eventually.of_forall fun t => ?_
          exact mul_nonneg (Φδ.nonneg_normed t) (hind01 (z - t)).1
        · refine Filter.Eventually.of_forall fun t => ?_
          exact mul_le_mul_of_nonneg_left (hind01 (z - t)).2 (Φδ.nonneg_normed t)
      have h3 : ∫ t, ρδ t * 1 = 1 := by
        rw [MeasureTheory.integral_mul_const, Φδ.integral_normed, one_mul]
      calc MeasureTheory.convolution ρδ ind L volume z
          = ∫ t, ρδ t * ind (z - t) := by rfl
        _ ≤ ∫ t, ρδ t * 1 := h2
        _ = 1 := h3
  refine ⟨χ, hχsm, hχcs, hsupp, ?_, ?_⟩
  · intro z
    rw [abs_le]
    exact ⟨by linarith [(hval z).1], (hval z).2⟩
  -- The neighbourhood where `χ = 1`.
  refine ⟨Metric.thickening (δ/8) K, Metric.isOpen_thickening,
    Metric.self_subset_thickening (by linarith) K, ?_⟩
  intro z hz
  have hzA : ∀ t ∈ Metric.ball (0 : ℂ) (δ/4), z - t ∈ A := by
    intro t ht
    rw [hAdef, Metric.mem_cthickening_iff]
    have h3 : Metric.infEDist (z - t) K ≤ Metric.infEDist z K + edist (z - t) z :=
      Metric.infEDist_le_infEDist_add_edist
    have h4 : Metric.infEDist z K < ENNReal.ofReal (δ/8) :=
      Metric.mem_thickening_iff_infEDist_lt.mp hz
    have h5 : edist (z - t) z ≤ ENNReal.ofReal (δ/4) := by
      have h6 : (z - t) - z = -t := by ring
      rw [edist_eq_enorm_sub, h6, enorm_neg, ← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Metric.mem_ball, dist_zero_right] at ht
      linarith
    calc Metric.infEDist (z - t) K
        ≤ ENNReal.ofReal (δ/8) + ENNReal.ofReal (δ/4) :=
          le_trans h3 (add_le_add h4.le h5)
      _ = ENNReal.ofReal (δ/8 + δ/4) := (ENNReal.ofReal_add (by linarith)
          (by linarith)).symm
      _ ≤ ENNReal.ofReal (δ/2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          linarith
  have hptwise : ∀ t, ρδ t * ind (z - t) = ρδ t := by
    intro t
    by_cases ht : t ∈ Function.support ρδ
    · have htball : t ∈ Metric.ball (0 : ℂ) (δ/4) := by
        rw [← Φδ.support_normed_eq (μ := volume)]
        exact ht
      have h1 : ind (z - t) = 1 := by
        rw [hinddef, Set.indicator_of_mem (hzA t htball)]
      rw [h1, mul_one]
    · have h0 : ρδ t = 0 := Function.notMem_support.mp ht
      rw [h0, zero_mul]
  calc χ z = ∫ t, ρδ t * ind (z - t) := by rfl
    _ = ∫ t, ρδ t := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        exact hptwise t
    _ = 1 := Φδ.integral_normed

/-- Pointwise Wirtinger cancellation. If `w` and `v` solve the same Beltrami
ratio at `z`, with invertible sense-preserving differential of `w`, then the pairing of
the differential of `v` against the inverse differential of `w` has vanishing
`∂̄`-combination. -/
theorem wirtinger_cancel
    {w v : ℂ → ℂ} {z : ℂ} {μz : ℂ}
    (hwdet : 0 < (fderiv ℝ w z).det)
    (hwbelt : dzbar w z = μz * dz w z)
    (hvbelt : dzbar v z = μz * dz v z)
    (A : ℂ →L[ℝ] ℂ) (hA : ∀ u : ℂ, (fderiv ℝ w z) (A u) = u) :
    ((A 1).re • (fderiv ℝ v z) 1 + (A 1).im • (fderiv ℝ v z) Complex.I)
      + Complex.I * ((A Complex.I).re • (fderiv ℝ v z) 1
        + (A Complex.I).im • (fderiv ℝ v z) Complex.I) = 0 := by
  classical
  -- The Wirtinger representation of a real differential.
  have hrepr : ∀ (F : ℂ → ℂ) (ζ u : ℂ),
      (fderiv ℝ F ζ) u = dz F ζ * u + dzbar F ζ * (starRingEnd ℂ) u := by
    intro F ζ u
    set T : ℂ →L[ℝ] ℂ := fderiv ℝ F ζ with hT
    have hTv : T u = (u.re : ℂ) * T 1 + (u.im : ℂ) * T Complex.I := by
      conv_lhs => rw [show u = u.re • (1 : ℂ) + u.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcv : (starRingEnd ℂ) u = (u.re : ℂ) - (u.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im u]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hv : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
    simp only [dz, dzbar, ← hT]
    rw [hTv, hcv]
    linear_combination (-(1 / 2 : ℂ) * (T 1 - Complex.I * T Complex.I)) * hv +
      ((u.im : ℂ) * T Complex.I) * Complex.I_sq
  -- The linear-map decomposition.
  have hdec : ∀ (T : ℂ →L[ℝ] ℂ) (u : ℂ), u.re • T 1 + u.im • T Complex.I = T u := by
    intro T u
    conv_rhs => rw [show u = u.re • (1 : ℂ) + u.im • Complex.I by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
    rw [map_add, map_smul, map_smul]
  rw [hdec (fderiv ℝ v z) (A 1), hdec (fderiv ℝ v z) (A Complex.I)]
  -- `∂w ≠ 0` from the positive Jacobian.
  have hpBne : dz w z ≠ 0 := by
    intro h0
    have hdd := det_fderiv_eq_wirtinger w z
    rw [h0, norm_zero] at hdd
    nlinarith [hwdet, sq_nonneg ‖dzbar w z‖]
  -- The defining equations of the inverse differential.
  have h1 : dz w z * A 1 + dzbar w z * (starRingEnd ℂ) (A 1) = 1 := by
    rw [← hrepr w z (A 1)]
    exact hA 1
  have hI : dz w z * A Complex.I + dzbar w z * (starRingEnd ℂ) (A Complex.I)
      = Complex.I := by
    rw [← hrepr w z (A Complex.I)]
    exact hA Complex.I
  -- Beltrami cancellation.
  have hbr : A 1 + μz * (starRingEnd ℂ) (A 1)
      + Complex.I * (A Complex.I + μz * (starRingEnd ℂ) (A Complex.I)) = 0 := by
    have hkey : dz w z * (A 1 + μz * (starRingEnd ℂ) (A 1)
        + Complex.I * (A Complex.I + μz * (starRingEnd ℂ) (A Complex.I))) = 0 := by
      linear_combination h1 + Complex.I * hI + Complex.I_sq
        - ((starRingEnd ℂ) (A 1)
            + Complex.I * (starRingEnd ℂ) (A Complex.I)) * hwbelt
    exact (mul_eq_zero.mp hkey).resolve_left hpBne
  -- Conclude by the representation of the differential of `v`.
  rw [hrepr v z (A 1), hrepr v z (A Complex.I)]
  linear_combination (dz v z) * hbr +
    ((starRingEnd ℂ) (A 1) + Complex.I * (starRingEnd ℂ) (A Complex.I)) * hvbelt

-- Assembling the composite through the abstract bricks over a per-point ball is a heavy
-- elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The transition-map analysis composes the chain rule with the Weyl lemma input;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- The transition map `v ∘ u.w⁻¹` of two solutions of the same
Beltrami equation on the upper half plane is holomorphic there, provided the normalized
plane solution preserves the upper half plane. -/
theorem composite_holomorphic
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (u : TeichRep Γ₀)
    {v vinv : ℂ → ℂ} {κ : ℝ} (hv : IsQCUpper v vinv κ)
    (hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar v z = u.b.μ z * dz v z)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 < (u.w z).im)
    {uinv : ℂ → ℂ} (huinvc : Continuous uinv)
    (_hui1 : ∀ z, uinv (u.w z) = z) (hui2 : ∀ z, u.w (uinv z) = z) :
    DifferentiableOn ℂ (fun w => v (uinv w)) {z : ℂ | 0 < z.im} := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  set Ω : Set ℂ := {z : ℂ | 0 < z.im} with hΩdef
  have hΩ : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_im
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  -- The plane solution and its inverse.
  have hwqc : IsQCAnalytic u.w u.b := u.w_isQCAnalytic
  have hwcont : Continuous u.w := hwqc.1.1.continuous
  obtain ⟨p, wgx, wgy, hp2, hwgrad, hgxp, hgyp⟩ :=
    hwqc.exists_weakGradient_memLpLocOn_gt_two
  have hLusin : ∀ S : Set ℂ, volume S = 0 → volume (u.w '' S) = 0 := fun S hS =>
    lusinN_image_null_of_weakGradient hp2 hwcont hwgrad hgxp hgyp hS
  have hK1 : 1 ≤ u.b.K := u.b.one_le_K
  have hbnd : u.b.normInf ≤ (u.b.K - 1) / (u.b.K + 1) := by
    have hm0 := u.b.normInf_nonneg
    have hm1 := u.b.normInf_lt_one
    have hden : (0 : ℝ) < 1 - u.b.normInf := by linarith
    have hKval : u.b.K = (1 + u.b.normInf) / (1 - u.b.normInf) := rfl
    have hKeq : u.b.K * (1 - u.b.normInf) = 1 + u.b.normInf := by
      rw [hKval, div_mul_cancel₀ _ (ne_of_gt hden)]
    have hKpos : (0 : ℝ) < u.b.K + 1 := by linarith
    rw [le_div_iff₀ hKpos]
    nlinarith [hKeq]
  have hwgeom : IsQCGeometric u.w u.b.K := isQCGeometric_of_isQCAnalytic hK1 hbnd hwqc
  have hinvgeom := isQCGeometric_inv_of_isQCGeometric hwgeom
  have hbridge : ⇑(hwgeom.2.1.isHomeomorph.homeomorph u.w).symm = uinv := by
    funext w
    have hinj : Function.Injective u.w := hwqc.injective
    have hL : u.w ((hwgeom.2.1.isHomeomorph.homeomorph u.w).symm w) = w := by
      rw [← IsHomeomorph.homeomorph_apply u.w hwgeom.2.1.isHomeomorph
            ((hwgeom.2.1.isHomeomorph.homeomorph u.w).symm w)]
      exact (hwgeom.2.1.isHomeomorph.homeomorph u.w).apply_symm_apply w
    exact hinj (hL.trans (hui2 w).symm)
  have huinv_geom : IsQCGeometric uinv u.b.K := hbridge ▸ hinvgeom
  obtain ⟨bq, hbqle, hqinv⟩ := isQCAnalytic_of_isQCGeometric hK1 huinv_geom
  -- The inverse preserves the upper half plane.
  have huinvΩ : ∀ w' : ℂ, w' ∈ Ω → uinv w' ∈ Ω := by
    intro w' hw'
    have hw'pos : 0 < w'.im := hw'
    by_contra hle
    have hle' : (uinv w').im ≤ 0 := not_lt.mp hle
    rcases eq_or_lt_of_le hle' with heq | hlt
    · have hzr : ((((uinv w').re : ℝ)) : ℂ) = uinv w' :=
        Complex.ext (by simp) (by simp [heq.symm])
      have h1 : (u.w (uinv w')).im = 0 := by
        rw [← hzr]
        exact u.w_real (uinv w').re
      rw [hui2 w'] at h1
      rw [h1] at hw'pos
      exact lt_irrefl 0 hw'pos
    · have h1 : 0 < (starRingEnd ℂ (uinv w')).im := by
        rw [Complex.conj_im]
        linarith
      have h2 := hpos _ h1
      rw [u.w_conj (uinv w'), hui2 w', Complex.conj_im] at h2
      linarith
  -- The upper-half-plane weak-gradient data, with measurable representatives.
  obtain ⟨hvL2, gx, gy, hvgrad, hgx2, hgy2⟩ := hv.sobolev
  have hlocOn : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Ω →
      MeasureTheory.LocallyIntegrableOn h Ω volume := by
    intro h hh
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk1 hk2
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk2.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp ((hh k hk1 hk2).mono_exponent (by norm_num))
  have hgxli : MeasureTheory.LocallyIntegrableOn gx Ω volume := hlocOn hgx2
  have hgyli : MeasureTheory.LocallyIntegrableOn gy Ω volume := hlocOn hgy2
  -- Measurable representatives of the witnesses.
  have hrep : ∀ (g : ℂ → ℂ), MeasureTheory.LocallyIntegrableOn g Ω volume →
      ∃ g' : ℂ → ℂ, Measurable g' ∧ volume {z | z ∈ Ω ∧ g z ≠ g' z} = 0 := by
    intro g hgli
    have hAESM := hgli.aestronglyMeasurable
    refine ⟨hAESM.mk g, hAESM.stronglyMeasurable_mk.measurable, ?_⟩
    have h1 : ∀ᵐ z ∂(volume.restrict Ω), g z = hAESM.mk g z := hAESM.ae_eq_mk
    rw [MeasureTheory.ae_iff] at h1
    rw [Measure.restrict_apply' hΩm] at h1
    refine measure_mono_null ?_ h1
    intro z hz
    exact ⟨hz.2, hz.1⟩
  obtain ⟨gx', hgx'm, hgx'eq⟩ := hrep gx hgxli
  obtain ⟨gy', hgy'm, hgy'eq⟩ := hrep gy hgyli
  -- Transfer of the weak-derivative identities to the representatives.
  have htransfer : ∀ (g g' : ℂ → ℂ) (ed : ℂ), HasWeakDirDeriv ed g v Ω →
      volume {z | z ∈ Ω ∧ g z ≠ g' z} = 0 → HasWeakDirDeriv ed g' v Ω := by
    intro g g' ed hg hnull φ hφ hφc hφs
    rw [hg φ hφ hφc hφs]
    congr 1
    refine integral_congr_ae ?_
    have h1 : {z : ℂ | ¬ φ z • g z = φ z • g' z} ⊆ {z | z ∈ Ω ∧ g z ≠ g' z} := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      by_cases hzs : z ∈ tsupport φ
      · refine ⟨hφs hzs, ?_⟩
        intro heq
        exact hz (by rw [heq])
      · exfalso
        have h0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hzs
        have e1 : φ z • g z = 0 := by rw [h0]; exact zero_smul ℝ _
        have e2 : φ z • g' z = 0 := by rw [h0]; exact zero_smul ℝ _
        exact hz (by rw [e1, e2])
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    exact measure_mono_null h1 hnull
  have hvgradx' : HasWeakDirDeriv 1 gx' v Ω := htransfer gx gx' 1 hvgrad.1 hgx'eq
  have hvgrady' : HasWeakDirDeriv Complex.I gy' v Ω := htransfer gy gy' Complex.I
    hvgrad.2 hgy'eq
  have hgx'li : MeasureTheory.LocallyIntegrableOn gx' Ω volume := by
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk1 hk2
    have h1 : IntegrableOn gx k volume := by
      have := hgxli
      rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed] at this
      exact this k hk1 hk2
    refine h1.congr ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    rw [Measure.restrict_apply' hk2.measurableSet]
    refine measure_mono_null ?_ hgx'eq
    intro z hz
    exact ⟨hk1 hz.2, hz.1⟩
  have hgy'li : MeasureTheory.LocallyIntegrableOn gy' Ω volume := by
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk1 hk2
    have h1 : IntegrableOn gy k volume := by
      have := hgyli
      rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed] at this
      exact this k hk1 hk2
    refine h1.congr ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    rw [Measure.restrict_apply' hk2.measurableSet]
    refine measure_mono_null ?_ hgy'eq
    intro z hz
    exact ⟨hk1 hz.2, hz.1⟩
  have hgx'2 : MemLpLocOn gx' 2 Ω := by
    intro k hk1 hk2
    refine ⟨((hgx'm).aestronglyMeasurable), ?_⟩
    have h1 := (hgx2 k hk1 hk2).2
    have h2 : eLpNorm gx' 2 (volume.restrict k) = eLpNorm gx 2 (volume.restrict k) := by
      refine eLpNorm_congr_ae ?_
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      rw [Measure.restrict_apply' hk2.measurableSet]
      refine measure_mono_null ?_ hgx'eq
      intro z hz
      exact ⟨hk1 hz.2, Ne.symm hz.1⟩
    rw [h2]
    exact h1
  have hgy'2 : MemLpLocOn gy' 2 Ω := by
    intro k hk1 hk2
    refine ⟨((hgy'm).aestronglyMeasurable), ?_⟩
    have h1 := (hgy2 k hk1 hk2).2
    have h2 : eLpNorm gy' 2 (volume.restrict k) = eLpNorm gy 2 (volume.restrict k) := by
      refine eLpNorm_congr_ae ?_
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      rw [Measure.restrict_apply' hk2.measurableSet]
      refine measure_mono_null ?_ hgy'eq
      intro z hz
      exact ⟨hk1 hz.2, Ne.symm hz.1⟩
    rw [h2]
    exact h1
  -- Almost-everywhere differentiability of `v` on `Ω`.
  have hvdiff : ∀ᵐ z ∂(volume.restrict Ω), DifferentiableAt ℝ v z := by
    filter_upwards [hv.jac] with z hz
    by_contra h
    have h0 : fderiv ℝ v z = 0 := fderiv_zero_of_not_differentiableAt h
    rw [h0] at hz
    have hdet0 : (0 : ℂ →L[ℝ] ℂ).det = 0 := by
      simp [ContinuousLinearMap.det]
    rw [hdet0] at hz
    exact lt_irrefl 0 hz
  -- The pointwise partials agree with the representatives almost everywhere on `Ω`.
  have hbrx := fderiv_ae_eq_weakDirDeriv_on (Or.inl rfl) hΩ hvgradx' hgx'li
    hv.cont hvdiff
  have hbry := fderiv_ae_eq_weakDirDeriv_on (Or.inr rfl) hΩ hvgrady' hgy'li
    hv.cont hvdiff
  -- Weak-gradient data for the inverse plane map, with measurable representatives.
  obtain ⟨hqL2, qx, qy, hqgrad, hqx2, hqy2⟩ := hqinv.2.1
  have hlocU : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ →
      MeasureTheory.LocallyIntegrable h volume := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hh k (Set.subset_univ k) hk).mono_exponent (by norm_num))
  have hqxli : MeasureTheory.LocallyIntegrable qx volume := hlocU hqx2
  have hqyli : MeasureTheory.LocallyIntegrable qy volume := hlocU hqy2
  have hrepU : ∀ (g : ℂ → ℂ), MeasureTheory.LocallyIntegrable g volume →
      ∃ g' : ℂ → ℂ, Measurable g' ∧ ∀ᵐ z : ℂ, g z = g' z := by
    intro g hgli
    have hAESM := hgli.aestronglyMeasurable
    exact ⟨hAESM.mk g, hAESM.stronglyMeasurable_mk.measurable, hAESM.ae_eq_mk⟩
  obtain ⟨qx', hqx'm, hqx'eq⟩ := hrepU qx hqxli
  obtain ⟨qy', hqy'm, hqy'eq⟩ := hrepU qy hqyli
  have htransferU : ∀ (g g' : ℂ → ℂ) (ed : ℂ), HasWeakDirDeriv ed g uinv Set.univ →
      (∀ᵐ z : ℂ, g z = g' z) → HasWeakDirDeriv ed g' uinv Set.univ := by
    intro g g' ed hg hae φ hφ hφc hφs
    rw [hg φ hφ hφc hφs]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  have hqgradx' : HasWeakDirDeriv 1 qx' uinv Set.univ :=
    htransferU qx qx' 1 hqgrad.1 hqx'eq
  have hqgrady' : HasWeakDirDeriv Complex.I qy' uinv Set.univ :=
    htransferU qy qy' Complex.I hqgrad.2 hqy'eq
  have hqx'li : MeasureTheory.LocallyIntegrable qx' volume := hqxli.congr hqx'eq
  have hqy'li : MeasureTheory.LocallyIntegrable qy' volume := hqyli.congr hqy'eq
  have hqx'2 : MemLpLocOn qx' 2 Set.univ := by
    intro k hk1 hk2
    refine ⟨hqx'm.aestronglyMeasurable, ?_⟩
    have h2 : eLpNorm qx' 2 (volume.restrict k) = eLpNorm qx 2 (volume.restrict k) :=
      eLpNorm_congr_ae (ae_restrict_of_ae (by filter_upwards [hqx'eq] with z hz
        using hz.symm))
    rw [h2]
    exact (hqx2 k hk1 hk2).2
  have hqy'2 : MemLpLocOn qy' 2 Set.univ := by
    intro k hk1 hk2
    refine ⟨hqy'm.aestronglyMeasurable, ?_⟩
    have h2 : eLpNorm qy' 2 (volume.restrict k) = eLpNorm qy 2 (volume.restrict k) :=
      eLpNorm_congr_ae (ae_restrict_of_ae (by filter_upwards [hqy'eq] with z hz
        using hz.symm))
    rw [h2]
    exact (hqy2 k hk1 hk2).2
  have hqae_x : ∀ᵐ w : ℂ, (fderiv ℝ uinv w) 1 = qx' w :=
    fderiv_ae_eq_weakDirDeriv hqgradx'
      (by rwa [MeasureTheory.locallyIntegrableOn_univ])
      hqinv.ae_differentiableAt (Or.inl rfl) huinvc.locallyIntegrable
  have hqae_y : ∀ᵐ w : ℂ, (fderiv ℝ uinv w) Complex.I = qy' w :=
    fderiv_ae_eq_weakDirDeriv hqgrady'
      (by rwa [MeasureTheory.locallyIntegrableOn_univ])
      hqinv.ae_differentiableAt (Or.inr rfl) huinvc.locallyIntegrable
  -- The good-point package on the `z`-side.
  have hgood : ∀ᵐ z ∂(volume.restrict Ω),
      (0 < (fderiv ℝ u.w z).det ∧ dzbar u.w z = u.b.μ z * dz u.w z) ∧
      (dzbar v z = u.b.μ z * dz v z) ∧
      ((fderiv ℝ v z) 1 = gx' z ∧ (fderiv ℝ v z) Complex.I = gy' z) := by
    have h1 : ∀ᵐ z : ℂ, 0 < (fderiv ℝ u.w z).det := hwqc.1.2
    have h2 : ∀ᵐ z : ℂ, dzbar u.w z = u.b.μ z * dz u.w z := hwqc.2.2
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae h2, hcoeff, hbrx, hbry]
      with z hz1 hz2 hz3 hz4 hz5
    exact ⟨⟨hz1, hz2⟩, hz3, hz4, hz5⟩
  -- Transfer of the good-point package to the `w`-side through the solution.
  have hwside : ∀ᵐ w' ∂(volume.restrict Ω),
      (0 < (fderiv ℝ u.w (uinv w')).det ∧
        dzbar u.w (uinv w') = u.b.μ (uinv w') * dz u.w (uinv w')) ∧
      (dzbar v (uinv w') = u.b.μ (uinv w') * dz v (uinv w')) ∧
      ((fderiv ℝ v (uinv w')) 1 = gx' (uinv w') ∧
        (fderiv ℝ v (uinv w')) Complex.I = gy' (uinv w')) := by
    have h1 := hgood
    rw [MeasureTheory.ae_iff, Measure.restrict_apply' hΩm] at h1 ⊢
    refine measure_mono_null ?_ (hLusin _ h1)
    intro w' hw'
    exact ⟨uinv w', ⟨hw'.1, huinvΩ w' hw'.2⟩, hui2 w'⟩
  -- The per-point ball argument.
  intro w₀ hw₀
  obtain ⟨ε0, hε00, hεsub⟩ := Metric.isOpen_iff.mp hΩ w₀ hw₀
  set s3 : ℝ := ε0/2 with hs3def
  have hs30 : 0 < s3 := by rw [hs3def]; linarith
  have hcbsub : Metric.closedBall w₀ s3 ⊆ Ω := by
    refine subset_trans ?_ hεsub
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    rw [hs3def] at hz
    linarith
  set K2 : Set ℂ := uinv '' (Metric.closedBall w₀ s3) with hK2def
  have hK2c : IsCompact K2 := (isCompact_closedBall _ _).image huinvc
  have hK2sub : K2 ⊆ Ω := by
    rintro z ⟨w', hw', rfl⟩
    exact huinvΩ w' (hcbsub hw')
  obtain ⟨χ2, hχ2sm, hχ2cs, hχ2ts, hχ2le, V2, hV2open, hKV2, hV2one⟩ :=
    smooth_cutoff hK2c hΩ hK2sub
  -- The cutoff package in the two directions.
  obtain ⟨hFwx, hFcont, hdxvcont, hFgx_int⟩ :=
    cutoff_hasWeakDirDeriv hΩ hvgradx' hgx'li hv.cont hχ2sm hχ2cs hχ2ts hχ2le
  obtain ⟨hFwy, -, hdyvcont, hFgy_int⟩ :=
    cutoff_hasWeakDirDeriv hΩ hvgrady' hgy'li hv.cont hχ2sm hχ2cs hχ2ts hχ2le
  have hχ2compl : ∀ z : ℂ, z ∉ tsupport χ2 → χ2 z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport hz
  have hdχ2supp : ∀ (ed : ℂ) (z : ℂ), z ∉ tsupport χ2 → (fderiv ℝ χ2 z) ed = 0 := by
    intro ed z hz
    have h1 : fderiv ℝ χ2 z = 0 := by
      by_contra hne
      exact hz ((support_fderiv_subset ℝ)
        (by simpa [Function.mem_support] using hne))
    rw [h1]
    rfl
  have hFcs : HasCompactSupport (fun z => χ2 z • v z) := by
    refine HasCompactSupport.intro hχ2cs ?_
    intro z hz
    change χ2 z • v z = 0
    rw [hχ2compl z hz]
    exact zero_smul ℝ _
  -- Measurability and square-integrability of the localized weak gradient.
  have hsmul_meas : ∀ {g : ℂ → ℂ}, Measurable g →
      Measurable (fun z => χ2 z • g z) := by
    intro g hgm
    have h1 : (fun z => χ2 z • g z) = fun z => ((χ2 z : ℝ) : ℂ) * g z := by
      funext z
      rw [Complex.real_smul]
    rw [h1]
    exact (Complex.measurable_ofReal.comp hχ2sm.continuous.measurable).mul hgm
  have hFxm : Measurable (fun z => χ2 z • gx' z + ((fderiv ℝ χ2 z) 1) • v z) :=
    (hsmul_meas hgx'm).add hdxvcont.measurable
  have hFym : Measurable
      (fun z => χ2 z • gy' z + ((fderiv ℝ χ2 z) Complex.I) • v z) :=
    (hsmul_meas hgy'm).add hdyvcont.measurable
  have hmemLp_part : ∀ {g : ℂ → ℂ}, Measurable g → MemLpLocOn g 2 Ω →
      MemLp (fun z => χ2 z • g z) 2 volume := by
    intro g hgm hg2
    refine ⟨(hsmul_meas hgm).aestronglyMeasurable, ?_⟩
    have h1 : eLpNorm (fun z => χ2 z • g z) 2 volume
        ≤ eLpNorm ((tsupport χ2).indicator g) 2 volume := by
      refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ tsupport χ2
      · rw [Set.indicator_of_mem hz, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχ2le z)
      · have h0 : χ2 z • g z = 0 := by
          rw [hχ2compl z hz]
          exact zero_smul ℝ _
        rw [h0, Set.indicator_of_notMem hz]
    refine lt_of_le_of_lt h1 ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hχ2cs.isClosed.measurableSet)]
    exact (hg2 (tsupport χ2) hχ2ts hχ2cs).2
  have hdχv_cs : ∀ ed : ℂ, HasCompactSupport
      (fun z => ((fderiv ℝ χ2 z) ed) • v z) := by
    intro ed
    refine HasCompactSupport.intro hχ2cs ?_
    intro z hz
    change ((fderiv ℝ χ2 z) ed) • v z = 0
    rw [hdχ2supp ed z hz]
    exact zero_smul ℝ _
  have hFx2 : MemLp (fun z => χ2 z • gx' z + ((fderiv ℝ χ2 z) 1) • v z) 2 volume :=
    (hmemLp_part hgx'm hgx'2).add
      (hdxvcont.memLp_of_hasCompactSupport (hdχv_cs 1))
  have hFy2 : MemLp
      (fun z => χ2 z • gy' z + ((fderiv ℝ χ2 z) Complex.I) • v z) 2 volume :=
    (hmemLp_part hgy'm hgy'2).add
      (hdyvcont.memLp_of_hasCompactSupport (hdχv_cs Complex.I))
  -- The composite weak derivatives on the plane.
  have hcompX := hasWeakDirDeriv_comp_qc hqinv (Or.inl rfl) hqgradx' hqx'm hqx'2
    hFcont hFcs ⟨hFwx, hFwy⟩ hFxm hFym hFx2 hFy2
  have hcompY := hasWeakDirDeriv_comp_qc hqinv (Or.inr rfl) hqgrady' hqy'm hqy'2
    hFcont hFcs ⟨hFwx, hFwy⟩ hFxm hFym hFx2 hFy2
  -- Names for the pairing functions.
  set FxD : ℂ → ℂ := fun z => χ2 z • gx' z + ((fderiv ℝ χ2 z) 1) • v z with hFxDdef
  set FyD : ℂ → ℂ := fun z => χ2 z • gy' z + ((fderiv ℝ χ2 z) Complex.I) • v z
    with hFyDdef
  set GxD : ℂ → ℂ := fun w => (qx' w).re • FxD (uinv w) + (qx' w).im • FyD (uinv w)
    with hGxDdef
  set GyD : ℂ → ℂ := fun w => (qy' w).re • FxD (uinv w) + (qy' w).im • FyD (uinv w)
    with hGyDdef
  set B3 : Set ℂ := Metric.ball w₀ s3 with hB3def
  have hB3sub : B3 ⊆ Ω := fun w' hw' => hcbsub (Metric.ball_subset_closedBall hw')
  have hψeqB : ∀ w' ∈ B3, χ2 (uinv w') • v (uinv w') = v (uinv w') := by
    intro w' hw'
    have h1 : uinv w' ∈ V2 :=
      hKV2 ⟨w', Metric.ball_subset_closedBall hw', rfl⟩
    rw [hV2one _ h1]
    exact one_smul ℝ _
  -- Restriction of the composite weak derivatives to the ball, transferred to `v∘uinv`.
  have hrestr : ∀ (ed : ℂ) (G : ℂ → ℂ),
      HasWeakDirDeriv ed G (fun w => χ2 (uinv w) • v (uinv w)) Set.univ →
      HasWeakDirDeriv ed G (fun w => v (uinv w)) B3 := by
    intro ed G hG φ hφ hφc hφs
    rw [← hG φ hφ hφc (by intro z _; trivial)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · change ((fderiv ℝ φ z) ed) • v (uinv z)
        = ((fderiv ℝ φ z) ed) • (χ2 (uinv z) • v (uinv z))
      rw [hψeqB z (hφs hz)]
    · have h1 : fderiv ℝ φ z = 0 := by
        by_contra hne
        exact hz ((support_fderiv_subset ℝ)
          (by simpa [Function.mem_support] using hne))
      have h2 : (fderiv ℝ φ z) ed = 0 := by
        rw [h1]
        rfl
      change ((fderiv ℝ φ z) ed) • v (uinv z)
        = ((fderiv ℝ φ z) ed) • (χ2 (uinv z) • v (uinv z))
      rw [h2]
      have e1 : (0:ℝ) • v (uinv z) = 0 := zero_smul ℝ _
      have e2 : (0:ℝ) • (χ2 (uinv z) • v (uinv z)) = 0 := zero_smul ℝ _
      rw [e1, e2]
  have hwx : HasWeakDirDeriv 1 GxD (fun w => v (uinv w)) B3 := hrestr 1 GxD hcompX
  have hwy : HasWeakDirDeriv Complex.I GyD (fun w => v (uinv w)) B3 :=
    hrestr Complex.I GyD hcompY
  -- Local integrability of the pairing functions on the ball.
  set Φ3 : ContDiffBump w₀ :=
    { rIn := s3, rOut := 2*s3,
      rIn_pos := hs30,
      rIn_lt_rOut := by linarith } with hΦ3def
  set S3 : Set ℂ := Metric.closedBall w₀ (2*s3) with hS3def
  have hS3m : MeasurableSet S3 := (Metric.isClosed_closedBall).measurableSet
  have hφ3zero : ∀ z, z ∉ S3 → (Φ3 : ℂ → ℝ) z = 0 := by
    intro z hz
    have h1 : z ∉ Function.support (Φ3 : ℂ → ℝ) := by
      rw [Φ3.support_eq]
      intro h2
      exact hz (Metric.ball_subset_closedBall h2)
    exact Function.notMem_support.mp h1
  have hφ3bd : ∀ z, ‖(Φ3 : ℂ → ℝ) z‖ ≤ 1 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (Φ3.nonneg)]
    exact Φ3.le_one
  have hel2 : ∀ h : ℂ → ℂ, ((∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)) = eLpNorm h 2 volume := by
    intro h
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
    rw [h2]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.rpow_natCast (‖h z‖ₑ) 2]
    norm_num
  have hGmeas : ∀ (qe' : ℂ → ℂ), Measurable qe' → Measurable
      (fun w => (qe' w).re • FxD (uinv w) + (qe' w).im • FyD (uinv w)) := by
    intro qe' hqe'm
    have h1 : (fun w => (qe' w).re • FxD (uinv w) + (qe' w).im • FyD (uinv w))
        = fun w => (((qe' w).re : ℝ) : ℂ) * FxD (uinv w)
          + (((qe' w).im : ℝ) : ℂ) * FyD (uinv w) := by
      funext w
      rw [Complex.real_smul, Complex.real_smul]
    rw [h1]
    exact ((Complex.measurable_ofReal.comp (Complex.measurable_re.comp hqe'm)).mul
        (hFxm.comp huinvc.measurable)).add
      ((Complex.measurable_ofReal.comp (Complex.measurable_im.comp hqe'm)).mul
        (hFym.comp huinvc.measurable))
  have hGint : ∀ (qe' : ℂ → ℂ), Measurable qe' →
      (∀ᵐ w : ℂ, (fderiv ℝ uinv w) 1 = qe' w) ∨
        (∀ᵐ w : ℂ, (fderiv ℝ uinv w) Complex.I = qe' w) →
      MeasureTheory.LocallyIntegrableOn
        (fun w => (qe' w).re • FxD (uinv w) + (qe' w).im • FyD (uinv w)) B3 volume := by
    intro qe' hqe'm hae'
    rw [MeasureTheory.locallyIntegrableOn_iff Metric.isOpen_ball.isLocallyClosed]
    intro k hk1 hk2
    refine IntegrableOn.mono_set ?_
      (subset_trans hk1 Metric.ball_subset_closedBall)
    refine ⟨(hGmeas qe' hqe'm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hone : ∀ w' ∈ Metric.closedBall w₀ s3, (Φ3 : ℂ → ℝ) w' = 1 := fun w' hw' =>
      Φ3.one_of_mem_closedBall hw'
    have hcov : ∫⁻ w' in Metric.closedBall w₀ s3,
        ‖(qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w')‖ₑ
        ≤ ∫⁻ w', ‖(Φ3 : ℂ → ℝ) w' • ((qe' w').re • FxD (uinv w')
          + (qe' w').im • FyD (uinv w'))‖ₑ := by
      have h1 : ∫⁻ w' in Metric.closedBall w₀ s3,
          ‖(qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w')‖ₑ
          = ∫⁻ w' in Metric.closedBall w₀ s3,
            ‖(Φ3 : ℂ → ℝ) w' • ((qe' w').re • FxD (uinv w')
              + (qe' w').im • FyD (uinv w'))‖ₑ := by
        refine setLIntegral_congr_fun (Metric.isClosed_closedBall).measurableSet ?_
        intro w' hw'
        change ‖(qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w')‖ₑ
          = ‖(Φ3 : ℂ → ℝ) w' • ((qe' w').re • FxD (uinv w')
            + (qe' w').im • FyD (uinv w'))‖ₑ
        have e1 : (1:ℝ) • ((qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w'))
            = (qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w') := one_smul ℝ _
        rw [hone w' hw', e1]
      rw [h1]
      exact setLIntegral_le_lintegral _ _
    have hbound : ∀ (hen' : ‖(1:ℂ)‖ = 1 ∨ ‖(Complex.I)‖ = 1), True := fun _ => trivial
    rcases hae' with hae1 | haeI
    · have h2 := cov_pairing_bound hqinv (by norm_num : ‖(1:ℂ)‖ = 1) hqe'm hae1
        hS3m hφ3zero hφ3bd hFxm hFym
      refine lt_of_le_of_lt (le_trans hcov h2) ?_
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine ENNReal.mul_lt_top ?_ ?_
      · rw [lt_top_iff_ne_top]
        refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
        · rw [hel2 FxD]
          exact hFx2.2.ne
        · rw [hel2 FyD]
          exact hFy2.2.ne
      · rw [lt_top_iff_ne_top]
        refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
        exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (isCompact_closedBall _ _).measure_lt_top).ne
    · have h2 := cov_pairing_bound hqinv (by simp : ‖(Complex.I)‖ = 1) hqe'm haeI
        hS3m hφ3zero hφ3bd hFxm hFym
      refine lt_of_le_of_lt (le_trans hcov h2) ?_
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine ENNReal.mul_lt_top ?_ ?_
      · rw [lt_top_iff_ne_top]
        refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
        · rw [hel2 FxD]
          exact hFx2.2.ne
        · rw [hel2 FyD]
          exact hFy2.2.ne
      · rw [lt_top_iff_ne_top]
        refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
        exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (isCompact_closedBall _ _).measure_lt_top).ne
  have hGxli2 : MeasureTheory.LocallyIntegrableOn GxD B3 volume :=
    hGint qx' hqx'm (Or.inl hqae_x)
  have hGyli2 : MeasureTheory.LocallyIntegrableOn GyD B3 volume :=
    hGint qy' hqy'm (Or.inr hqae_y)
  -- The combination vanishes almost everywhere on the ball.
  have hcomb : ∀ᵐ z : ℂ, z ∈ B3 → GxD z + Complex.I * GyD z = 0 := by
    have h1 := hwside
    rw [ae_restrict_iff' hΩm] at h1
    filter_upwards [h1, hqae_x, hqae_y] with w' hP hqx hqy
    intro hw'B
    have hw'Ω : w' ∈ Ω := hB3sub hw'B
    obtain ⟨⟨hdet, hwbelt⟩, hvbelt, hgx'v, hgy'v⟩ := hP hw'Ω
    have hwdiffz : DifferentiableAt ℝ u.w (uinv w') := by
      by_contra h
      rw [fderiv_zero_of_not_differentiableAt h] at hdet
      have hdet0 : (0 : ℂ →L[ℝ] ℂ).det = 0 := by
        simp [ContinuousLinearMap.det]
      rw [hdet0] at hdet
      exact lt_irrefl 0 hdet
    have hdetne : (fderiv ℝ u.w (uinv w')).det ≠ 0 := ne_of_gt hdet
    set eL := (fderiv ℝ u.w (uinv w')).toContinuousLinearEquivOfDetNeZero hdetne
      with heLdef
    have hecoe : (eL : ℂ →L[ℝ] ℂ) = fderiv ℝ u.w (uinv w') :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdetne
    have hfd1 : HasFDerivAt u.w (eL : ℂ →L[ℝ] ℂ) (uinv w') := by
      rw [hecoe]
      exact hwdiffz.hasFDerivAt
    have hloc : ∀ᶠ y in nhds w', u.w (uinv y) = y := Filter.Eventually.of_forall hui2
    have hgfd : HasFDerivAt uinv ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) w' :=
      HasFDerivAt.of_local_left_inverse huinvc.continuousAt hfd1 hloc
    have hqx1 : qx' w' = ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 1 := by
      rw [← hqx, hgfd.fderiv]
    have hqy1 : qy' w' = ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) Complex.I := by
      rw [← hqy, hgfd.fderiv]
    have hzV2 : uinv w' ∈ V2 :=
      hKV2 ⟨w', Metric.ball_subset_closedBall hw'B, rfl⟩
    have hχ2z : χ2 (uinv w') = 1 := hV2one _ hzV2
    have hdχ2z : fderiv ℝ χ2 (uinv w') = 0 := by
      have hev : χ2 =ᶠ[nhds (uinv w')] fun _ => (1:ℝ) := by
        filter_upwards [hV2open.mem_nhds hzV2] with p hp
        exact hV2one p hp
      rw [hev.fderiv_eq]
      exact fderiv_const_apply 1
    have hFxz : FxD (uinv w') = gx' (uinv w') := by
      change χ2 (uinv w') • gx' (uinv w')
        + ((fderiv ℝ χ2 (uinv w')) 1) • v (uinv w') = gx' (uinv w')
      rw [hχ2z, hdχ2z]
      have e1 : (1:ℝ) • gx' (uinv w') = gx' (uinv w') := one_smul ℝ _
      have e2 : ((0 : ℂ →L[ℝ] ℝ) 1) • v (uinv w') = 0 := by
        rw [ContinuousLinearMap.zero_apply]
        exact zero_smul ℝ _
      rw [e1, e2, add_zero]
    have hFyz : FyD (uinv w') = gy' (uinv w') := by
      change χ2 (uinv w') • gy' (uinv w')
        + ((fderiv ℝ χ2 (uinv w')) Complex.I) • v (uinv w') = gy' (uinv w')
      rw [hχ2z, hdχ2z]
      have e1 : (1:ℝ) • gy' (uinv w') = gy' (uinv w') := one_smul ℝ _
      have e2 : ((0 : ℂ →L[ℝ] ℝ) Complex.I) • v (uinv w') = 0 := by
        rw [ContinuousLinearMap.zero_apply]
        exact zero_smul ℝ _
      rw [e1, e2, add_zero]
    have hA : ∀ u' : ℂ, (fderiv ℝ u.w (uinv w'))
        (((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) u') = u' := by
      intro u'
      rw [← hecoe]
      simp
    have hcancel := wirtinger_cancel hdet hwbelt hvbelt
      ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) hA
    change ((qx' w').re • FxD (uinv w') + (qx' w').im • FyD (uinv w'))
      + Complex.I * ((qy' w').re • FxD (uinv w') + (qy' w').im • FyD (uinv w')) = 0
    rw [hFxz, hFyz, hqx1, hqy1, hgx'v.symm, hgy'v.symm]
    exact hcancel
  -- Weyl's lemma on the ball, and the conclusion at the point.
  have hψcont : ContinuousOn (fun w => v (uinv w)) B3 := by
    refine ContinuousOn.comp hv.cont huinvc.continuousOn ?_
    intro w' hw'
    exact huinvΩ w' (hB3sub hw')
  have hweyl := weyl_lemma_on Metric.isOpen_ball hψcont ⟨hwx, hwy⟩ hGxli2 hGyli2 hcomb
  have hw₀B : w₀ ∈ B3 := Metric.mem_ball_self hs30
  exact ((hweyl w₀ hw₀B).differentiableAt
    (Metric.isOpen_ball.mem_nhds hw₀B)).differentiableWithinAt

-- The removable-singularity inverse-holomorphy transcription and the manifold
-- plumbing are one long elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The Moebius classification splits into affine and inversion branches with long algebra;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- A holomorphic homeomorphism of the upper half plane is a real
Möbius map, through the Cayley transform and the classification of disc automorphisms. -/
theorem holo_upper_selfmap_moebius
    {ψ θ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | 0 < z.im})
    (hψmaps : ∀ z : ℂ, 0 < z.im → 0 < (ψ z).im)
    (hθmaps : ∀ z : ℂ, 0 < z.im → 0 < (θ z).im)
    (hθψ : ∀ z : ℂ, 0 < z.im → θ (ψ z) = z)
    (hψθ : ∀ z : ℂ, 0 < z.im → ψ (θ z) = z)
    (hθcont : ContinuousOn θ {z : ℂ | 0 < z.im}) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → ψ z = moebiusMap A z := by
  classical
  set Ω : Set ℂ := {z : ℂ | 0 < z.im} with hΩdef
  have hΩ : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_im
  have hAn : AnalyticOnNhd ℂ ψ Ω := hψ.analyticOnNhd hΩ
  have hinj : Set.InjOn ψ Ω := by
    intro a ha b hb hab
    have h1 := hθψ  -- keep the name in scope
    calc a = θ (ψ a) := (hθψ a ha).symm
      _ = θ (ψ b) := by rw [hab]
      _ = b := hθψ b hb
  -- `ψ` is an open map on `Ω`.
  have hopen : ∀ z ∈ Ω, nhds (ψ z) ≤ Filter.map ψ (nhds z) := by
    intro z hz
    rcases (hAn z hz).eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have h1 : ∀ᶠ z' in nhdsWithin z {z}ᶜ, ψ z' = ψ z ∧ z' ∈ Ω :=
        (hconst.and (hΩ.eventually_mem hz)).filter_mono nhdsWithin_le_nhds
      obtain ⟨z', ⟨hfz', hz'Ω⟩, hz'ne⟩ := (h1.and eventually_mem_nhdsWithin).exists
      exact hz'ne (Set.mem_singleton_iff.mpr (hinj hz'Ω hz hfz'))
    · exact hle
  -- Critical points of `ψ` are isolated in `Ω`.
  have hcrit : ∀ z ∈ Ω, ∀ᶠ z' in nhdsWithin z {z}ᶜ, deriv ψ z' ≠ 0 := by
    intro z hz
    rcases (hAn.deriv z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      obtain ⟨r, hr0, hball⟩ :=
        Metric.eventually_nhds_iff_ball.mp (h0.and (hΩ.eventually_mem hz))
      have hconst : ∀ z' ∈ Metric.ball z r, ψ z' = ψ z := by
        intro z' hz'
        refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball z r)
          (hψ.mono fun p hp => (hball p hp).2) ?_ hz' (Metric.mem_ball_self hr0)
        intro p hp
        rw [fderivWithin_of_isOpen Metric.isOpen_ball hp]
        refine ContinuousLinearMap.ext_ring ?_
        rw [fderiv_apply_one_eq_deriv, (hball p hp).1]
        simp
      have hmem : z + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have heq : z + ((r / 2 : ℝ) : ℂ) = z :=
        hinj (hball _ hmem).2 hz (hconst _ hmem)
      have hr2 : ((r / 2 : ℝ) : ℂ) = 0 := by simpa using heq
      have : (r / 2 : ℝ) = 0 := by exact_mod_cast hr2
      linarith
    · exact hne
  -- Inverse differentiability at non-critical values.
  have hθd_nc : ∀ w ∈ Ω, deriv ψ (θ w) ≠ 0 → DifferentiableAt ℂ θ w := by
    intro w hw hder
    have hθwΩ : θ w ∈ Ω := hθmaps w hw
    have hfd : HasDerivAt ψ (deriv ψ (θ w)) (θ w) :=
      ((hAn (θ w) hθwΩ).differentiableAt).hasDerivAt
    have hev : ∀ᶠ y in nhds w, ψ (θ y) = y := by
      filter_upwards [hΩ.mem_nhds hw] with y hy
      exact hψθ y hy
    exact (HasDerivAt.of_local_left_inverse (hθcont.continuousAt (hΩ.mem_nhds hw))
      hfd hder hev).differentiableAt
  -- `ψ` maps `Ω` onto `Ω`.
  have himg : ∀ w ∈ Ω, ∃ z ∈ Ω, ψ z = w := fun w hw =>
    ⟨θ w, hθmaps w hw, hψθ w hw⟩
  have himgOpen : ∀ S : Set ℂ, S ⊆ Ω → IsOpen S → IsOpen (ψ '' S) := by
    intro S hSΩ hSo
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hzS, rfl⟩
    exact Filter.le_def.mp (hopen z (hSΩ hzS)) _
      (Filter.image_mem_map (hSo.mem_nhds hzS))
  -- Inverse differentiability everywhere on `Ω`, via removable singularities.
  have hθd : ∀ w ∈ Ω, DifferentiableAt ℂ θ w := by
    intro w hw
    by_cases hder : deriv ψ (θ w) = 0
    swap
    · exact hθd_nc w hw hder
    have hθwΩ : θ w ∈ Ω := hθmaps w hw
    obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      ((eventually_nhdsWithin_iff.mp (hcrit (θ w) hθwΩ)).and (hΩ.eventually_mem hθwΩ))
    have hballΩ : Metric.ball (θ w) r ⊆ Ω := fun p hp => (hball p hp).2
    have hWo : IsOpen (ψ '' Metric.ball (θ w) r) :=
      himgOpen _ hballΩ Metric.isOpen_ball
    have hwW : w ∈ ψ '' Metric.ball (θ w) r :=
      ⟨θ w, Metric.mem_ball_self hr0, hψθ w hw⟩
    have hWΩ : ψ '' Metric.ball (θ w) r ⊆ Ω := by
      rintro w' ⟨z', hz'b, rfl⟩
      exact hψmaps z' (hballΩ hz'b)
    have hoff : DifferentiableOn ℂ θ (ψ '' Metric.ball (θ w) r \ {w}) := by
      rintro w' ⟨⟨z', hz'b, rfl⟩, hw'ne⟩
      have hθz' : θ (ψ z') = z' := hθψ z' (hballΩ hz'b)
      have hz'ne : z' ∈ ({θ w}ᶜ : Set ℂ) := by
        intro hmem
        refine hw'ne (Set.mem_singleton_iff.mpr ?_)
        rw [Set.mem_singleton_iff.mp hmem]
        exact hψθ w hw
      refine ((hθd_nc (ψ z') (hWΩ ⟨z', hz'b, rfl⟩) ?_).differentiableWithinAt)
      rw [hθz']
      exact (hball z' hz'b).1 hz'ne
    have hθW : DifferentiableOn ℂ θ (ψ '' Metric.ball (θ w) r) :=
      (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (hWo.mem_nhds hwW)).mp ⟨hoff, hθcont.continuousAt (hΩ.mem_nhds hw)⟩
    exact hθW.differentiableAt (hWo.mem_nhds hwW)
  have hθdiff : DifferentiableOn ℂ θ Ω := fun w hw =>
    (hθd w hw).differentiableWithinAt
  -- Cayley transport to the unit disc.
  have hcay_holo : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 →
      DifferentiableAt ℂ cayleyToHalfPlane d := by
    intro d hd
    have hne : (1:ℂ) - d ≠ 0 := by
      intro h0
      have h1 : d = 1 := by
        have := sub_eq_zero.mp h0
        exact this.symm
      rw [h1] at hd
      rw [Metric.mem_ball, dist_zero_right] at hd
      simp at hd
    have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.I * (1 + z)) d :=
      (differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (1:ℂ) - z) d :=
      (differentiableAt_const _).sub differentiableAt_id
    have h3 := h1.div h2 hne
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  have hhtc_holo : ∀ τ : ℂ, τ ∈ Ω → DifferentiableAt ℂ halfPlaneToCayley τ := by
    intro τ hτ
    have hne : τ + Complex.I ≠ 0 := by
      intro h0
      have h1 : (τ + Complex.I).im = 0 := by rw [h0]; rfl
      rw [Complex.add_im, Complex.I_im] at h1
      have hτ' : 0 < τ.im := hτ
      linarith
    have h1 : DifferentiableAt ℂ (fun z : ℂ => z - Complex.I) τ :=
      differentiableAt_id.sub (differentiableAt_const _)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => z + Complex.I) τ :=
      differentiableAt_id.add (differentiableAt_const _)
    have h3 := h1.div h2 hne
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  have hcay_mem : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → cayleyToHalfPlane d ∈ Ω :=
    fun d hd => cayleyToHalfPlane_im_pos hd
  -- The transported disc maps.
  set E : ℂ → ℂ := fun d => halfPlaneToCayley (ψ (cayleyToHalfPlane d)) with hEdef
  set Einv : ℂ → ℂ := fun d => halfPlaneToCayley (θ (cayleyToHalfPlane d)) with hEinvdef
  have hE_mem : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → E d ∈ Metric.ball (0:ℂ) 1 := by
    intro d hd
    exact halfPlaneToCayley_mem_ball (hψmaps _ (hcay_mem d hd))
  have hEinv_mem : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 →
      Einv d ∈ Metric.ball (0:ℂ) 1 := by
    intro d hd
    exact halfPlaneToCayley_mem_ball (hθmaps _ (hcay_mem d hd))
  have hE_left : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → Einv (E d) = d := by
    intro d hd
    have h1 : cayleyToHalfPlane (E d) = ψ (cayleyToHalfPlane d) := by
      rw [hEdef]
      exact cayleyToHalfPlane_halfPlaneToCayley (hψmaps _ (hcay_mem d hd))
    rw [hEinvdef]
    change halfPlaneToCayley (θ (cayleyToHalfPlane (E d))) = d
    rw [h1, hθψ _ (hcay_mem d hd)]
    exact halfPlaneToCayley_cayleyToHalfPlane hd
  have hE_right : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → E (Einv d) = d := by
    intro d hd
    have h1 : cayleyToHalfPlane (Einv d) = θ (cayleyToHalfPlane d) := by
      rw [hEinvdef]
      exact cayleyToHalfPlane_halfPlaneToCayley (hθmaps _ (hcay_mem d hd))
    rw [hEdef]
    change halfPlaneToCayley (ψ (cayleyToHalfPlane (Einv d))) = d
    rw [h1, hψθ _ (hcay_mem d hd)]
    exact halfPlaneToCayley_cayleyToHalfPlane hd
  have hE_holo : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → DifferentiableAt ℂ E d := by
    intro d hd
    have h1 := hcay_holo d hd
    have h2 : DifferentiableAt ℂ ψ (cayleyToHalfPlane d) :=
      (hAn _ (hcay_mem d hd)).differentiableAt
    have h3 : DifferentiableAt ℂ halfPlaneToCayley (ψ (cayleyToHalfPlane d)) :=
      hhtc_holo _ (hψmaps _ (hcay_mem d hd))
    exact DifferentiableAt.comp d h3 (DifferentiableAt.comp d h2 h1)
  have hEinv_holo : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 →
      DifferentiableAt ℂ Einv d := by
    intro d hd
    have h1 := hcay_holo d hd
    have h2 : DifferentiableAt ℂ θ (cayleyToHalfPlane d) :=
      hθd _ (hcay_mem d hd)
    have h3 : DifferentiableAt ℂ halfPlaneToCayley (θ (cayleyToHalfPlane d)) :=
      hhtc_holo _ (hθmaps _ (hcay_mem d hd))
    exact DifferentiableAt.comp d h3 (DifferentiableAt.comp d h2 h1)
  -- The disc diffeomorphism.
  have hmem_disc : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 ↔ d ∈ unitDiscOpens := by
    intro d
    rfl
  have hbridge : ∀ (F : ℂ → ↥unitDiscOpens) (z : ℂ),
      AnalyticAt ℂ (fun p => (F p : ℂ)) z →
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤ F z := by
    intro F z hFa
    rw [contMDiffAt_iff]
    constructor
    · exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hFa.continuousAt
    · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        PartialEquiv.refl_symm, Function.comp_id, modelWithCornersSelf_coe,
        Set.range_id, id_eq]
      rw [contDiffWithinAt_univ]
      exact hFa.contDiffAt
  have h0disc : (0:ℂ) ∈ Metric.ball (0:ℂ) 1 := Metric.mem_ball_self one_pos
  set D : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ↥unitDiscOpens ↥unitDiscOpens ⊤ :=
    { toFun := fun d => ⟨E (d : ℂ), hE_mem (d : ℂ) d.2⟩
      invFun := fun d => ⟨Einv (d : ℂ), hEinv_mem (d : ℂ) d.2⟩
      left_inv := fun d => Subtype.ext (hE_left (d : ℂ) d.2)
      right_inv := fun d => Subtype.ext (hE_right (d : ℂ) d.2)
      contMDiff_toFun := by
        intro x
        have hxmem : E (x : ℂ) ∈ Metric.ball (0:ℂ) 1 := hE_mem (x : ℂ) x.2
        have key : ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
            (fun d : ℂ =>
              if h : E d ∈ Metric.ball (0:ℂ) 1 then (⟨E d, h⟩ : ↥unitDiscOpens)
              else ⟨E (x : ℂ), hxmem⟩) (x : ℂ) := by
          refine hbridge _ (x : ℂ) ?_
          have h1 : AnalyticAt ℂ E (x : ℂ) := by
            have hEdiffOn : DifferentiableOn ℂ E (Metric.ball (0:ℂ) 1) :=
              fun p hp => (hE_holo p hp).differentiableWithinAt
            exact hEdiffOn.analyticAt (Metric.isOpen_ball.mem_nhds x.2)
          refine h1.congr ?_
          filter_upwards [Metric.isOpen_ball.mem_nhds x.2] with p hp
          rw [dif_pos (hE_mem p hp)]
        have key2 := key.comp x (contMDiff_subtype_val.contMDiffAt
          (I := modelWithCornersSelf ℂ ℂ) (n := (⊤ : WithTop ℕ∞)))
        refine key2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun d => ?_)
        change (⟨E (d : ℂ), hE_mem (d : ℂ) d.2⟩ : ↥unitDiscOpens)
          = if h : E (d : ℂ) ∈ Metric.ball (0:ℂ) 1 then (⟨E (d : ℂ), h⟩ : ↥unitDiscOpens)
            else ⟨E (x : ℂ), hxmem⟩
        rw [dif_pos (hE_mem (d : ℂ) d.2)]
      contMDiff_invFun := by
        intro x
        have hxmem : Einv (x : ℂ) ∈ Metric.ball (0:ℂ) 1 := hEinv_mem (x : ℂ) x.2
        have key : ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
            (fun d : ℂ =>
              if h : Einv d ∈ Metric.ball (0:ℂ) 1 then (⟨Einv d, h⟩ : ↥unitDiscOpens)
              else ⟨Einv (x : ℂ), hxmem⟩) (x : ℂ) := by
          refine hbridge _ (x : ℂ) ?_
          have h1 : AnalyticAt ℂ Einv (x : ℂ) := by
            have hEdiffOn : DifferentiableOn ℂ Einv (Metric.ball (0:ℂ) 1) :=
              fun p hp => (hEinv_holo p hp).differentiableWithinAt
            exact hEdiffOn.analyticAt (Metric.isOpen_ball.mem_nhds x.2)
          refine h1.congr ?_
          filter_upwards [Metric.isOpen_ball.mem_nhds x.2] with p hp
          rw [dif_pos (hEinv_mem p hp)]
        have key2 := key.comp x (contMDiff_subtype_val.contMDiffAt
          (I := modelWithCornersSelf ℂ ℂ) (n := (⊤ : WithTop ℕ∞)))
        refine key2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun d => ?_)
        change (⟨Einv (d : ℂ), hEinv_mem (d : ℂ) d.2⟩ : ↥unitDiscOpens)
          = if h : Einv (d : ℂ) ∈ Metric.ball (0:ℂ) 1
            then (⟨Einv (d : ℂ), h⟩ : ↥unitDiscOpens)
            else ⟨Einv (x : ℂ), hxmem⟩
        rw [dif_pos (hEinv_mem (d : ℂ) d.2)] } with hDdef
  obtain ⟨A, hA⟩ := exists_sl2_of_diffeomorph_unitDisc D
  refine ⟨A, ?_⟩
  intro z hz
  set d : ↥unitDiscOpens := ⟨halfPlaneToCayley z, halfPlaneToCayley_mem_ball hz⟩
    with hddef
  obtain ⟨τ, τ', h1, h2, h3⟩ := hA d
  have hτ : (τ : ℂ) = z := by
    rw [h1, hddef]
    exact cayleyToHalfPlane_halfPlaneToCayley hz
  have hDd : ((D d : ↥unitDiscOpens) : ℂ) = halfPlaneToCayley (ψ z) := by
    change E (halfPlaneToCayley z) = halfPlaneToCayley (ψ z)
    rw [hEdef]
    change halfPlaneToCayley (ψ (cayleyToHalfPlane (halfPlaneToCayley z)))
      = halfPlaneToCayley (ψ z)
    rw [cayleyToHalfPlane_halfPlaneToCayley hz]
  have hτ' : (τ' : ℂ) = ψ z := by
    rw [h2, hDd]
    exact cayleyToHalfPlane_halfPlaneToCayley (hψmaps z hz)
  have h4 := coe_smul_eq_moebiusMap A τ
  rw [h3] at h4
  rw [hτ, hτ'] at h4
  exact h4

end RiemannDynamics

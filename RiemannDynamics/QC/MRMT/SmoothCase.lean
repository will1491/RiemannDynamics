/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.MRMT.NeumannSeries
import RiemannDynamics.QC.LengthArea.Mollification

/-!
# The smooth-case principal solution and the Ahlfors–Bers endgame

The measurable Riemann mapping theorem is proved by first solving the Beltrami
equation for a **smooth, compactly supported** coefficient — where the principal
solution can be exhibited as an explicit `C¹` diffeomorphism through the
exponential representation `F = id + P(μ·e^σ)`, `∂F = e^σ` — and then passing to
a measurable coefficient by mollification, using the Ahlfors–Bers stability and
two-sided Hölder estimates to carry injectivity and surjectivity to the limit
(Astala–Iwaniec–Martin §§5.2–5.3, Ahlfors–Bers 1960).


* **Smooth Calderón–Zygmund calculus** — on `C∞₀` data the Beurling transform is
  `S u = P(∂u)` (`beurling_eq_cauchyTransform_dz`, the companion of the proved
  bridge `T = ∂ ∘ P`), and both `P` and `S` preserve smoothness
  (`contDiff_cauchyTransform`, `contDiff_beurling`).
* **`C¹` criterion** — a continuous function with continuous weak gradient is
  genuinely `C¹` with the weak gradient as its differential
  (`contDiffOne_of_continuous_hasWeakGradient`).
* **Smooth fixed point** — for smooth data the `Lᵖ` fixed point of
  `φ ↦ μ·Sφ + g` is continuous with continuous Beurling image and satisfies the
  equation pointwise (`exists_continuous_fixedPoint_beltrami_of_contDiff`,
  the regularity content of AIM Lemma 5.2.1/Theorem 5.2.2).
* **The smooth principal solution** — for a smooth compactly supported
  coefficient the principal solution is `C¹` with everywhere-positive Jacobian
  and nonvanishing `∂f` (`exists_contDiffOne_principalSolution`, AIM
  Theorem 5.2.3), and is a homeomorphism of the plane
  (`isHomeomorph_of_contDiffOne_principalSolution`, AIM Theorem 5.2.4).
* **The inverse solution** — the inverse of the smooth-case principal solution
  is the principal solution of the explicit coefficient
  `ν = −(μ∘g)·(∂f∘g)/conj(∂f∘g)`, of no larger dilatation and compactly
  supported in the image of `supp μ`
  (`IsPrincipalSolution.inverse_principalSolution_of_contDiff`, Ahlfors–Bers
  Lemma 11).
* **The Ahlfors–Bers endgame** — the uniform potential estimates
  (`norm_cauchyTransform_le_of_memLp_support`,
  `cauchyTransform_sub_le_holder_uniform`, `isPrincipalSolution_uniform_image_bound`),
  the resolvent stability of the fixed-point field
  (`lp_fixedPoint_beltrami_stability`, AIM Lemma 5.3.1), locally uniform
  convergence of principal solutions under a.e. convergence of coefficients
  (`isPrincipalSolution_tendstoUniformly_of_ae_tendsto`, AIM Theorem 5.3.2),
  the two-sided Hölder inequality with constants uniform over the smooth family
  (`isPrincipalSolution_two_sided_holder`, Ahlfors–Bers Lemma 8 — the estimate
  that forces injectivity of the measurable-case limit), and mollification of a
  Beltrami coefficient (`exists_contDiff_mollification_beltrami`).
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace RiemannDynamics

/-! ## Smooth Calderón–Zygmund calculus -/

/-- **`S = P ∘ ∂` on smooth data.** For a smooth compactly supported `u` the
Beurling transform is the Cauchy transform of the holomorphic Wirtinger
derivative: `S u = P(∂u)`. Companion of the proved bridge
`beurling_eq_dz_cauchyTransform` (`S u = ∂(P u)`): both sides are continuous,
vanish at infinity, and have the same `∂̄` (namely `∂u`, by Cauchy–Pompeiu and
the commutation of `∂̄` with `P`), so the difference is entire and vanishes by
Liouville. -/
theorem beurling_eq_cauchyTransform_dz {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (z : ℂ) :
    beurling u z = cauchyTransform (fun ζ => dz u ζ) z := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast le_top)
  -- Both sides are `-(1/π)` times an integral: the Beurling side is the
  -- principal-value limit of the truncated singular integrals, and the
  -- extracted Tendsto `czOperator_beurling_tendsto_smooth` identifies that
  -- limit with the Cauchy-transform integral of `∂u`.
  rw [beurling, cauchyTransform]
  congr 1
  refine Filter.Tendsto.limUnder_eq ?_
  have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r u z
      = czOperator beurlingKernel r u z := fun r => rfl
  simpa only [hcz] using czOperator_beurling_tendsto_smooth hu1 huc z

/-- **The Cauchy transform preserves smoothness.** For smooth compactly
supported `u` the potential `P u` is smooth: `P u` is the convolution of `u`
with the locally integrable kernel `-1/(π·)`, so all derivatives fall on `u`
(`HasCompactSupport.hasFDerivAt_convolution_left`, iterated). -/
theorem contDiff_cauchyTransform {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    ContDiff ℝ ∞ (cauchyTransform u) := by
  set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
  set k : ℂ → ℂ := fun w => -w⁻¹ with hk
  -- The kernel `-w⁻¹` is locally integrable: in polar coordinates the Jacobian
  -- factor `r` cancels the singularity `r⁻¹`, leaving a finite box integral.
  have hk_loc : LocallyIntegrable k volume := by
    rw [hk]
    apply LocallyIntegrable.neg
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR₀
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ q ∈ polarCoord.target,
        ENNReal.ofReal q.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
          (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q) ≤ box q := by
      intro q hq
      simp only [hbox]
      rw [polarCoord_target, Set.mem_prod] at hq
      obtain ⟨hq1, hq2⟩ := hq
      simp only [Set.mem_Ioi] at hq1
      by_cases hmem : Complex.polarCoord.symm q ∈ Metric.closedBall (0 : ℂ) R₀
      · rw [Set.indicator_of_mem hmem]
        have hnorm : ‖Complex.polarCoord.symm q‖ = q.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hq1]
        have hsymm_ne : Complex.polarCoord.symm q ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hq1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm q‖ₑ = ENNReal.ofReal q.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel
            (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq1)
            ENNReal.ofReal_lt_top.ne]
        have hqR : q.1 ≤ R₀ := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hq1, hqR⟩, hq2⟩)]
      · rw [Set.indicator_of_notMem hmem]; simp
    calc
      ∫⁻ q in polarCoord.target, ENNReal.ofReal q.1 •
          (Metric.closedBall (0 : ℂ) R₀).indicator
            (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q)
          ≤ ∫⁻ q in polarCoord.target, box q :=
            setLIntegral_mono (measurable_const.indicator
              (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
      _ ≤ ∫⁻ q, box q := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
            rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
            simp
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc,
              Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- `P u` is `-(1/π)` times the convolution of `u` with the kernel.
  have hCT : cauchyTransform u
      = fun w => (-(1 / (Real.pi : ℂ))) • (MeasureTheory.convolution u k L volume) w := by
    funext w
    rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
    congr 1
    apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
    rw [hL, ContinuousLinearMap.mul_apply']
    change u ζ / (ζ - w) = u ζ * -(w - ζ)⁻¹
    have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
    rw [hflip, div_eq_mul_inv]
  rw [hCT]
  exact (huc.contDiff_convolution_left L hu hk_loc).const_smul _

/-- **The Beurling transform preserves smoothness.** For smooth compactly
supported `u` the singular integral `S u` is smooth: by
`beurling_eq_cauchyTransform_dz`, `S u = P(∂u)` with `∂u` smooth and compactly
supported, and `P` preserves smoothness (`contDiff_cauchyTransform`). -/
theorem contDiff_beurling {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    ContDiff ℝ ∞ (beurling u) := by
  -- `S u = P(∂u)` pointwise.
  have hbeq : beurling u = cauchyTransform (fun ζ => dz u ζ) := by
    funext z; exact beurling_eq_cauchyTransform_dz hu huc z
  -- `∂u` is a fixed continuous-linear expression in `fderiv ℝ u`.
  have hcomp : (fun ζ => dz u ζ)
      = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
        ∘ (fun ζ => fderiv ℝ u ζ) := by
    funext ζ; rfl
  -- Smoothness of `∂u`.
  have hfderiv_cinf : ContDiff ℝ ∞ (fun ζ => fderiv ℝ u ζ) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hΦ_cd : ContDiff ℝ ∞
      (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I)) := by
    have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
        = (fun D : ℂ →L[ℝ] ℂ =>
            (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
              - Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
      funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
    rw [hΦ_lin]
    exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).sub
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
  have hdzu_cinf : ContDiff ℝ ∞ (fun ζ => dz u ζ) := by
    rw [hcomp]; exact hΦ_cd.comp hfderiv_cinf
  -- Compact support of `∂u`.
  have hdzu_cs : HasCompactSupport (fun ζ => dz u ζ) := by
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ u ζ) := huc.fderiv (𝕜 := ℝ)
    rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  -- Conclude via the smoothness of the Cauchy transform.
  rw [hbeq]
  exact contDiff_cauchyTransform hdzu_cinf hdzu_cs

/-! ## The `C¹` criterion from continuous weak gradients -/

/-- **Continuous weak gradient ⇒ `C¹`.** A continuous function on `ℂ` whose
weak gradient components are continuous is continuously differentiable, and the
weak partials are the genuine directional derivatives everywhere. Classical
mollification argument: `f ∗ φ_ε → f` locally uniformly and
`∂(f ∗ φ_ε) = gx ∗ φ_ε → gx` locally uniformly, so the limit `f` is `C¹` with
the asserted differential. -/
theorem contDiffOne_of_continuous_hasWeakGradient {f gx gy : ℂ → ℂ}
    (hf : Continuous f) (hgrad : HasWeakGradient gx gy f Set.univ)
    (hgx : Continuous gx) (hgy : Continuous gy) :
    ContDiff ℝ 1 f ∧
      ∀ z : ℂ, (fderiv ℝ f z) 1 = gx z ∧ (fderiv ℝ f z) Complex.I = gy z := by
  classical
  obtain ⟨hwgx, hwgy⟩ := hgrad
  have hfloc : LocallyIntegrable f := hf.locallyIntegrable
  have hgxLI : LocallyIntegrable gx := hgx.locallyIntegrable
  have hgyLI : LocallyIntegrable gy := hgy.locallyIntegrable
  -- ===== Mollifier sequence `φ n` with `rOut → 0`. =====
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hφdef
  have hφrout : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hφdef] using this
  -- The normed bumps and the three mollifications.
  set ρ : ℕ → ℂ → ℝ := fun n => (φ n).normed volume with hρ
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φ n).contDiff_normed (n := ⊤)
  have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φ n).hasCompactSupport_normed
  set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
    (ContinuousLinearMap.lsmul ℝ ℝ) volume with hfn
  set cx : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) gx
    (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcx
  set cy : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) gy
    (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcy
  -- Directional derivatives of the mollification are the mollified weak partials.
  have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ) = cx n z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
  have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I = cy n z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
  -- Each mollification is smooth.
  have hfn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) := fun n =>
    (hρsupp n).contDiff_convolution_left _ (hρsm n) hfloc
  -- Two `ℝ`-linear CLMs on `ℂ` agreeing at `1` and `I` are equal.
  have hCLMext : ∀ T S : ℂ →L[ℝ] ℂ, T 1 = S 1 → T Complex.I = S Complex.I → T = S := by
    intro T S h1 hI
    ext w
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    rw [hw]
    simp only [map_add, map_smul, h1, hI]
  -- Basis values of the assembled derivative candidates.
  have hA_apply : ∀ a b : ℂ,
      (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) (1 : ℂ) = a
      ∧ (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) Complex.I = b := by
    intro a b
    constructor
    · simp [ContinuousLinearMap.smulRight_apply]
    · simp [ContinuousLinearMap.smulRight_apply]
  -- Each mollification has the assembled derivative everywhere.
  have hfnFD : ∀ n z, HasFDerivAt (fn n)
      (Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z)) z := by
    intro n z
    have hd : DifferentiableAt ℝ (fn n) z :=
      ((hfn_smooth n).differentiable (by simp)).differentiableAt
    have hEq : fderiv ℝ (fn n) z
        = Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z) := by
      refine hCLMext _ _ ?_ ?_
      · rw [hA1x n z, (hA_apply (cx n z) (cy n z)).1]
      · rw [hA1y n z, (hA_apply (cx n z) (cy n z)).2]
    exact hEq ▸ hd.hasFDerivAt
  -- ===== Mollifications of a continuous map converge locally uniformly. =====
  have hconvTLU : ∀ (g : ℂ → ℂ), Continuous g →
      TendstoLocallyUniformly (fun n => MeasureTheory.convolution (ρ n) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) g atTop := by
    intro g hgcont
    refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
    have hUC : UniformContinuousOn g (Metric.closedBall x 2) :=
      (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hgcont.continuousOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
    have hev : ∀ᶠ n in atTop, (φ n).rOut < min δ 1 := by
      have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
      filter_upwards [this] with n hn using hn
    filter_upwards [hev] with n hn z hz
    have hrout_le_one : (φ n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
    have hrout_le_δ : (φ n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
    have hsupp : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φ n).rOut := by
      rw [hρ, (φ n).support_normed_eq]
    have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φ n).nonneg_normed y
    have hintf : ∫ y, ρ n y ∂volume = 1 := (φ n).integral_normed
    have hclose : ∀ y ∈ Metric.ball z (φ n).rOut, dist (g y) (g z) ≤ ε / 2 := by
      intro y hy
      have hzmem : z ∈ Metric.closedBall x 2 :=
        Metric.closedBall_subset_closedBall (by norm_num) hz
      rw [Metric.mem_ball] at hy
      have hymem : y ∈ Metric.closedBall x 2 := by
        rw [Metric.mem_closedBall] at hz ⊢
        calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
          _ ≤ (φ n).rOut + 1 := by gcongr
          _ ≤ 1 + 1 := by gcongr
          _ = 2 := by norm_num
      exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
    calc dist (g z) (MeasureTheory.convolution (ρ n) g (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
        = dist (MeasureTheory.convolution (ρ n) g (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
            (g z) := dist_comm _ _
      _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp hnf hintf
            hgcont.aestronglyMeasurable hclose
      _ < ε := by linarith
  have hcxTLU : TendstoLocallyUniformly cx gx atTop := by
    have := hconvTLU gx hgx; rwa [← hcx] at this
  have hcyTLU : TendstoLocallyUniformly cy gy atTop := by
    have := hconvTLU gy hgy; rwa [← hcy] at this
  -- ===== The assembled derivatives converge locally uniformly. =====
  have hTLU : TendstoLocallyUniformlyOn
      (fun n z => Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z))
      (fun z => Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z))
      atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    have hx := tendstoLocallyUniformly_iff_forall_isCompact.mp hcxTLU K hK
    have hy := tendstoLocallyUniformly_iff_forall_isCompact.mp hcyTLU K hK
    rw [Metric.tendstoUniformlyOn_iff] at hx hy ⊢
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    filter_upwards [hx (ε / 2) hε2, hy (ε / 2) hε2] with n hnx hny z hz
    have h1 := hnx z hz
    have h2 := hny z hz
    rw [dist_eq_norm] at h1 h2
    change dist (Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z))
      (Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z)) < ε
    rw [dist_eq_norm]
    have hdiff : (Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z))
        - (Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z))
        = Complex.reCLM.smulRight (gx z - cx n z)
          + Complex.imCLM.smulRight (gy z - cy n z) := by
      ext w
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, smul_sub]
      abel
    rw [hdiff]
    have hbound : ‖Complex.reCLM.smulRight (gx z - cx n z)
          + Complex.imCLM.smulRight (gy z - cy n z)‖
        ≤ ‖gx z - cx n z‖ + ‖gy z - cy n z‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        Complex.reCLM_apply, Complex.imCLM_apply]
      calc ‖w.re • (gx z - cx n z) + w.im • (gy z - cy n z)‖
          ≤ ‖w.re • (gx z - cx n z)‖ + ‖w.im • (gy z - cy n z)‖ := norm_add_le _ _
        _ = |w.re| * ‖gx z - cx n z‖ + |w.im| * ‖gy z - cy n z‖ := by
            rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖gx z - cx n z‖ + ‖w‖ * ‖gy z - cy n z‖ := by
            gcongr
            · exact Complex.abs_re_le_norm w
            · exact Complex.abs_im_le_norm w
        _ = (‖gx z - cx n z‖ + ‖gy z - cy n z‖) * ‖w‖ := by ring
    calc ‖Complex.reCLM.smulRight (gx z - cx n z)
          + Complex.imCLM.smulRight (gy z - cy n z)‖
        ≤ ‖gx z - cx n z‖ + ‖gy z - cy n z‖ := hbound
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  -- ===== Pointwise convergence of the mollifications. =====
  have hptw : ∀ x : ℂ, Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous hφrout hf x
  -- ===== The uniform-limit theorem: `f` has the assembled derivative everywhere. =====
  have hFD : ∀ z : ℂ, HasFDerivAt f
      (Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z)) z := fun z =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hTLU
      (fun n x _ => hfnFD n x) (fun x _ => hptw x) (Set.mem_univ z)
  have hfeq : ∀ z : ℂ, fderiv ℝ f z
      = Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z) := fun z =>
    (hFD z).fderiv
  -- ===== Assembly. =====
  have hLcont : Continuous (fun z : ℂ =>
      Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z)) := by
    have h1 : Continuous (fun z : ℂ => Complex.reCLM.smulRight (gx z)) :=
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).continuous.comp hgx
    have h2 : Continuous (fun z : ℂ => Complex.imCLM.smulRight (gy z)) :=
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).continuous.comp hgy
    exact h1.add h2
  constructor
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (hFD z).differentiableAt, ?_⟩
    have heq : fderiv ℝ f = fun z =>
        Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z) := funext hfeq
    rw [heq]
    exact hLcont
  · intro z
    rw [hfeq z]
    exact ⟨(hA_apply (gx z) (gy z)).1, (hA_apply (gx z) (gy z)).2⟩

/-- **Uniform sup bound for the Cauchy transform of compactly vanishing `Lᵖ`
fields** (`p > 2`): a constant `C = C(p, R)` with
`‖P h‖_∞ ≤ C·‖h‖ₚ` for every field `h ∈ Lᵖ` vanishing outside the ball of
radius `R`. Hölder's inequality against the kernel: the conjugate exponent
satisfies `q < 2`, so `sup_z ∫_{B_R} |ζ − z|^{-q} dA < ∞`. The constant is
uniform over the family — the source of every uniformity in the
Ahlfors–Bers limit argument. -/
theorem norm_cauchyTransform_le_of_memLp_support {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ → ℂ, MemLp h p volume →
      (∀ z : ℂ, R < ‖z‖ → h z = 0) →
      ∀ z : ℂ, ‖cauchyTransform h z‖ ≤ C * (eLpNorm h p volume).toReal := by
  -- ===== Exponent bookkeeping: `pr > 2`, conjugate `qr ∈ (1,2)` =====
  set pr : ℝ := p.toReal with hpr_def
  have hp0 : p ≠ 0 := (lt_trans (by norm_num : (0:ℝ≥0∞) < 2) hp).ne'
  have hpr2 : 2 < pr := by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp').mpr hp
    simpa [← hpr_def] using h2
  have hpr0 : 0 < pr := lt_trans two_pos hpr2
  set qr : ℝ := (1 - pr⁻¹)⁻¹ with hqr_def
  have hainv0 : 0 < pr⁻¹ := inv_pos.mpr hpr0
  have hainv : pr⁻¹ < 2⁻¹ := by
    have hmul : pr * pr⁻¹ = 1 := mul_inv_cancel₀ hpr0.ne'
    nlinarith [hainv0, hpr2, hmul]
  have hb0 : 0 < 1 - pr⁻¹ := by
    have h12 : (2 : ℝ)⁻¹ < 1 := by norm_num
    linarith
  have hbinv0 : 0 < (1 - pr⁻¹)⁻¹ := inv_pos.mpr hb0
  have hbmul : (1 - pr⁻¹) * (1 - pr⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
  have hqr1 : 1 < qr := by
    rw [hqr_def]
    nlinarith [hbmul, mul_pos hainv0 hbinv0, hbinv0]
  have hqr2 : qr < 2 := by
    rw [hqr_def]
    nlinarith [hbmul, hainv, hbinv0]
  have hqr0 : 0 < qr := lt_trans one_pos hqr1
  have hpq : pr.HolderConjugate qr := by
    refine ⟨?_, hpr0, hqr0⟩
    rw [hqr_def, inv_inv, inv_one]
    ring
  -- ===== Radial kernel integrals =====
  -- pointwise: `‖w⁻¹‖ₑ ^ qr = ofReal (‖w‖ ^ (-qr))`
  have hpt : ∀ w : ℂ, ‖w⁻¹‖ₑ ^ qr = ENNReal.ofReal (‖w‖ ^ (-qr)) := fun w => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hqr0.le,
      norm_inv, Real.inv_rpow (norm_nonneg w), ← Real.rpow_neg (norm_nonneg w)]
  -- `‖·‖^(-qr)` is integrable on balls (dimension 2, `qr < 2`)
  have hnegpow_int : ∀ r : ℝ, 0 < r →
      IntegrableOn (fun w : ℂ => ‖w‖ ^ (-qr)) (Metric.ball (0:ℂ) r) volume := by
    intro r hr
    rw [← integrable_indicator_iff measurableSet_ball]
    set F : ℝ → ℝ := fun t : ℝ => if t < r then t ^ (-qr) else 0 with hF
    have heq : (Metric.ball (0:ℂ) r).indicator (fun w : ℂ => ‖w‖ ^ (-qr))
        = fun w : ℂ => F ‖w‖ := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ Metric.ball (0:ℂ) r
      · rw [if_pos hw]
        have hwr : ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_pos hwr]
      · rw [if_neg hw]
        have hwr : ¬ ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_neg hwr]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn
        ((Set.Ioo (0 : ℝ) r).indicator fun y : ℝ => y ^ (1 - qr)) (Set.Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ioo]
      have hsub : Set.Ioo (0 : ℝ) r ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) r :=
        Set.inter_eq_left.mpr fun y hy => hy.1
      rw [hsub, intervalIntegral.integrableOn_Ioo_rpow_iff hr]
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator]
    by_cases hyR : y < r
    · rw [if_pos ⟨hy, hyR⟩, if_pos hyR,
        show (1 - qr) = (1 : ℝ) + (-qr) by ring, Real.rpow_add hy, Real.rpow_one]
      norm_num
    · rw [if_neg fun hc => hyR hc.2, if_neg hyR, mul_zero]
  -- explicit value bound on the ball
  have hball_val : ∀ r : ℝ, 0 < r →
      ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) ≤ 2 * Real.pi / (2 - qr) * r ^ (2 - qr) := by
    intro r hr
    set f : ℝ → ℝ := fun t => if t < r then t ^ (-qr) else 0 with hf
    have hconv : ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) = ∫ x : ℂ, f ‖x‖ := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ Metric.ball (0:ℂ) r
      · rw [Set.indicator_of_mem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_pos hx]
      · rw [Set.indicator_of_notMem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_neg hx]
    rw [hconv]
    rw [integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
    have hvol : volume.real (Metric.ball (0:ℂ) 1) = Real.pi := by
      rw [Measure.real, Complex.volume_ball]; simp
    rw [hvol]
    have hinner : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y = r ^ (2 - qr) / (2 - qr) := by
      have hsub' : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
        · intro x hx
          simp only [Set.mem_Ioo, Set.mem_Ioi] at *
          exact hx.1
        · intro x hx
          simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_diff, not_and, not_lt] at hx
          obtain ⟨hx0, hxR⟩ := hx
          have hnlt : ¬ (x < r) := not_lt.mpr (hxR hx0)
          rw [hf]; simp only [if_neg hnlt, smul_zero]
      rw [hsub']
      have hcongr : ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (1 - qr) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        simp only [Set.mem_Ioo] at hy
        rw [hf]
        simp only [if_pos hy.2]
        rw [pow_one, smul_eq_mul]
        rw [show y * y ^ (-qr) = y ^ (1:ℝ) * y ^ (-qr) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hy.1]
        ring_nf
      rw [hcongr]
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
      rw [integral_rpow (Or.inl (by linarith))]
      have h1 : (1 : ℝ) - qr + 1 = 2 - qr := by ring
      rw [h1, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < 2 - qr))]
      ring
    rw [hinner]
    rw [le_iff_lt_or_eq]; right
    rw [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  -- translation of set-lintegrals to the origin
  have htransl : ∀ S₀ : Set ℂ, MeasurableSet S₀ → ∀ (g : ℂ → ℝ≥0∞) (y : ℂ),
      ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y) = ∫⁻ w in S₀, g w := by
    intro S₀ hS₀ g y
    have hpre : MeasurableSet {ζ : ℂ | ζ - y ∈ S₀} := (measurable_id.sub_const y) hS₀
    calc ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y)
        = ∫⁻ ζ, ({ζ : ℂ | ζ - y ∈ S₀}).indicator (fun ζ => g (ζ - y)) ζ := by
          rw [lintegral_indicator hpre]
      _ = ∫⁻ ζ, S₀.indicator g (ζ - y) := by
          apply lintegral_congr
          intro ζ
          unfold Set.indicator
          by_cases hζ : ζ - y ∈ S₀
          · rw [if_pos hζ, if_pos (by exact hζ)]
          · rw [if_neg hζ, if_neg (by exact hζ)]
      _ = ∫⁻ ζ, S₀.indicator g ζ := lintegral_sub_right_eq_self _ y
      _ = ∫⁻ w in S₀, g w := by rw [lintegral_indicator hS₀]
  -- ball kernel bound (single pole)
  have hballE : ∀ (y : ℂ) (r : ℝ), 0 < r →
      ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) := by
    intro y r hr
    have hset : Metric.ball y r = {ζ : ℂ | ζ - y ∈ Metric.ball (0:ℂ) r} := by
      ext ζ
      simp [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        = ∫⁻ w in Metric.ball (0:ℂ) r, ‖w⁻¹‖ₑ ^ qr := by
          rw [hset]
          exact htransl _ measurableSet_ball (fun w => ‖w⁻¹‖ₑ ^ qr) y
      _ = ∫⁻ w in Metric.ball (0:ℂ) r, ENNReal.ofReal (‖w‖ ^ (-qr)) := lintegral_congr hpt
      _ = ENNReal.ofReal (∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr)) :=
          (ofReal_integral_eq_lintegral_ofReal (hnegpow_int r hr)
            (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg w) _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) :=
          ENNReal.ofReal_le_ofReal (hball_val r hr)
  -- ===== The uniform (in the pole) kernel constant over the support ball =====
  set B : Set ℂ := Metric.closedBall (0:ℂ) R with hB_def
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi / (2 - qr) * 1 ^ (2 - qr)) + volume B
    with hK₀_def
  have hK₀top : K₀ ≠ ⊤ := by
    rw [hK₀_def]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
    rw [hB_def]
    exact ((isCompact_closedBall _ _).measure_lt_top).ne
  -- pointwise domination of the shifted kernel: near the pole use the ball kernel,
  -- away from it the kernel is bounded by `1`
  have hptw : ∀ z ζ : ℂ, ‖(ζ - z)⁻¹‖ₑ ^ qr
      ≤ (Metric.ball z 1).indicator (fun ξ => ‖(ξ - z)⁻¹‖ₑ ^ qr) ζ + 1 := by
    intro z ζ
    by_cases hζ : ζ ∈ Metric.ball z 1
    · rw [Set.indicator_of_mem hζ]
      exact le_self_add
    · rw [Set.indicator_of_notMem hζ, zero_add]
      have h1 : (1:ℝ) ≤ ‖ζ - z‖ := by
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at hζ
        exact hζ
      have hle : ‖(ζ - z)⁻¹‖ₑ ≤ 1 := by
        rw [← ofReal_norm_eq_enorm, norm_inv]
        exact ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ h1)
      calc ‖(ζ - z)⁻¹‖ₑ ^ qr ≤ 1 ^ qr := ENNReal.rpow_le_rpow hle hqr0.le
        _ = 1 := ENNReal.one_rpow _
  -- the uniform kernel mass bound over the support ball
  have hker : ∀ z : ℂ, ∫⁻ ζ in B, ‖(ζ - z)⁻¹‖ₑ ^ qr ≤ K₀ := by
    intro z
    calc ∫⁻ ζ in B, ‖(ζ - z)⁻¹‖ₑ ^ qr
        ≤ ∫⁻ ζ in B, ((Metric.ball z 1).indicator (fun ξ => ‖(ξ - z)⁻¹‖ₑ ^ qr) ζ + 1) :=
          lintegral_mono fun ζ => hptw z ζ
      _ = (∫⁻ ζ in B, (Metric.ball z 1).indicator (fun ξ => ‖(ξ - z)⁻¹‖ₑ ^ qr) ζ)
            + ∫⁻ _ in B, 1 :=
          lintegral_add_right' _ aemeasurable_const
      _ = (∫⁻ ζ in Metric.ball z 1 ∩ B, ‖(ζ - z)⁻¹‖ₑ ^ qr) + volume B := by
          rw [lintegral_indicator measurableSet_ball,
            Measure.restrict_restrict measurableSet_ball, setLIntegral_one]
      _ ≤ (∫⁻ ζ in Metric.ball z 1, ‖(ζ - z)⁻¹‖ₑ ^ qr) + volume B :=
          add_le_add (lintegral_mono_set Set.inter_subset_left) le_rfl
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * 1 ^ (2 - qr)) + volume B :=
          add_le_add (hballE z 1 one_pos) le_rfl
      _ = K₀ := hK₀_def.symm
  set Kc : ℝ≥0∞ := K₀ ^ (1/qr) with hKc_def
  have hKctop : Kc ≠ ⊤ := by
    rw [hKc_def]
    exact ENNReal.rpow_ne_top_of_nonneg (le_of_lt (one_div_pos.mpr hqr0)) hK₀top
  -- ===== Conclusion =====
  refine ⟨1 / Real.pi * Kc.toReal,
    mul_nonneg (by positivity) ENNReal.toReal_nonneg, ?_⟩
  intro h hh hsupp z
  set N : ℝ≥0∞ := eLpNorm h p volume with hN_def
  have hN_ne : N ≠ ⊤ := hh.2.ne
  -- the integrand vanishes off the support ball
  have hrestrict : ∫⁻ ζ, ‖h ζ / (ζ - z)‖ₑ = ∫⁻ ζ in B, ‖h ζ / (ζ - z)‖ₑ := by
    rw [← lintegral_indicator hBmeas]
    apply lintegral_congr
    intro ζ
    by_cases hζ : ζ ∈ B
    · rw [Set.indicator_of_mem hζ]
    · rw [Set.indicator_of_notMem hζ]
      have hζR : R < ‖ζ‖ := by
        rw [hB_def] at hζ
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      rw [hsupp ζ hζR, zero_div]
      simp
  -- Hölder pairing against the kernel on the support ball
  have hHolder : ∫⁻ ζ in B, ‖h ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ ≤ N * Kc := by
    have hNle : (∫⁻ ζ in B, ‖h ζ‖ₑ ^ pr) ^ (1/pr) ≤ N := by
      rw [hN_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
      exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _)
        (le_of_lt (one_div_pos.mpr hpr0))
    calc ∫⁻ ζ in B, ‖h ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ
        ≤ (∫⁻ ζ in B, ‖h ζ‖ₑ ^ pr) ^ (1/pr)
            * (∫⁻ ζ in B, ‖(ζ - z)⁻¹‖ₑ ^ qr) ^ (1/qr) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (hh.1.restrict.enorm)
            (((measurable_id.sub_const z).inv).enorm.aemeasurable.restrict)
      _ ≤ N * Kc := by
          refine mul_le_mul' hNle ?_
          rw [hKc_def]
          exact ENNReal.rpow_le_rpow (hker z) (le_of_lt (one_div_pos.mpr hqr0))
  -- main estimate at the level of the integral
  have hmain : ‖∫ ζ, h ζ / (ζ - z)‖ₑ ≤ N * Kc := by
    calc ‖∫ ζ, h ζ / (ζ - z)‖ₑ
        ≤ ∫⁻ ζ, ‖h ζ / (ζ - z)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ζ in B, ‖h ζ / (ζ - z)‖ₑ := hrestrict
      _ = ∫⁻ ζ in B, ‖h ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ := lintegral_congr fun ζ => by
          rw [div_eq_mul_inv, enorm_mul]
      _ ≤ N * Kc := hHolder
  -- pass to the real inequality
  have hnn : (0:ℝ) ≤ N.toReal * Kc.toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hX : ‖∫ ζ, h ζ / (ζ - z)‖ ≤ N.toReal * Kc.toReal := by
    have h2 := hmain
    rw [show N * Kc = ENNReal.ofReal (N.toReal * Kc.toReal) by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hN_ne,
          ENNReal.ofReal_toReal hKctop],
      ← ofReal_norm_eq_enorm] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h2
  -- unfold the Cauchy transform and conclude
  have hCT : ‖cauchyTransform h z‖ = 1/Real.pi * ‖∫ ζ, h ζ / (ζ - z)‖ := by
    rw [cauchyTransform, norm_mul]
    congr 1
    rw [norm_neg, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hCT]
  calc 1/Real.pi * ‖∫ ζ, h ζ / (ζ - z)‖
      ≤ 1/Real.pi * (N.toReal * Kc.toReal) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 1 / Real.pi * Kc.toReal * N.toReal := by ring

/-! ## The smooth fixed point -/

/-- **Regularity of the Beltrami fixed point for smooth data** (AIM
Lemma 5.2.1 / Theorem 5.2.2, the regularity content). For a smooth compactly
supported multiplier `μ` and datum `g`, and contraction data at an exponent
`p > 2`, the fixed-point equation `φ = μ·Sφ + g` has a solution `φ ∈ Lᵖ`,
vanishing outside the common support ball, which is **continuous with
continuous Beurling transform** and satisfies the equation **pointwise**.
Internally: the `Lᵖ` fixed point of the proved `exists_lp_fixedPoint_beltrami`
is `W^{1,p}` (differentiate the equation: `∂φ` solves the same-multiplier
equation with datum `∂μ·Sφ + ∂g`), hence Hölder continuous by the Morrey
embedding (`Analysis/Sobolev/Morrey/OscillationBound.lean`), and `S` preserves
the Hölder class of compactly supported fields; continuity of both sides
upgrades the a.e. equation to a pointwise one. -/
theorem exists_continuous_fixedPoint_beltrami_of_contDiff {μ g : ℂ → ℂ}
    {p : ℝ≥0∞} {C R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤)
    (hμs : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hcontr : (eLpNormEssSup μ volume).toReal * C < 1)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → μ z = 0 ∧ g z = 0) :
    ∃ φ : ℂ → ℂ, MemLp φ p volume ∧ (∀ z : ℂ, R < ‖z‖ → φ z = 0) ∧
      Continuous φ ∧ Continuous (beurling φ) ∧
      ∀ z : ℂ, φ z = μ z * beurling φ z + g z := by
  classical
  -- ===== Constants. =====
  set k : ℝ := (eLpNormEssSup μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ C := hCb.1
  have hr0 : 0 ≤ k * C := mul_nonneg hk0 hC0
  have hr1 : k * C < 1 := hcontr
  set r' : ℝ := (k * C + 1) / 2 with hr'def
  have hr'0 : 0 < r' := by rw [hr'def]; linarith
  have hrr' : k * C < r' := by rw [hr'def]; linarith
  have hr'1 : r' < 1 := by rw [hr'def]; linarith
  set δ : ℝ := r' - k * C with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.le
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp; exact (not_lt_of_ge (zero_le _)) hp
  -- ===== Differentiability shorthands. =====
  have hd1 : ∀ {u : ℂ → ℂ}, ContDiff ℝ ∞ u → Differentiable ℝ u := by
    intro u hu
    exact (hu.of_le (by exact_mod_cast le_top : ((1 : ℕ∞) : WithTop ℕ∞) ≤ _)).differentiable
      one_ne_zero
  -- ===== `dz`/`dzbar` of a smooth function are smooth. =====
  have hdz_sm : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u →
      ContDiff ℝ ∞ (fun ζ => dz u ζ) ∧ ContDiff ℝ ∞ (fun ζ => dzbar u ζ) := by
    intro u hu
    have hfderiv_cinf : ContDiff ℝ ∞ (fun ζ => fderiv ℝ u ζ) :=
      hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    constructor
    · have hcomp : (fun ζ => dz u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
            ∘ (fun ζ => fderiv ℝ u ζ) := by funext ζ; rfl
      have hΦ : ContDiff ℝ ∞
          (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I)) := by
        have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
            = (fun D : ℂ →L[ℝ] ℂ =>
                (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
                  - Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
          funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
        rw [hΦ_lin]
        exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).sub
          ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
      rw [hcomp]; exact hΦ.comp hfderiv_cinf
    · have hcomp : (fun ζ => dzbar u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I))
            ∘ (fun ζ => fderiv ℝ u ζ) := by funext ζ; rfl
      have hΦ : ContDiff ℝ ∞
          (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I)) := by
        have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I))
            = (fun D : ℂ →L[ℝ] ℂ =>
                (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
                  + Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
          funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
        rw [hΦ_lin]
        exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).add
          ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
      rw [hcomp]; exact hΦ.comp hfderiv_cinf
  -- ===== `dz`/`dzbar` of a compactly supported function are compactly supported. =====
  have hdz_cs : ∀ u : ℂ → ℂ, HasCompactSupport u →
      HasCompactSupport (fun ζ => dz u ζ) ∧ HasCompactSupport (fun ζ => dzbar u ζ) := by
    intro u huc
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ u ζ) := huc.fderiv (𝕜 := ℝ)
    constructor
    · have hcomp : (fun ζ => dz u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 - I * D I)) ∘ (fun ζ => fderiv ℝ u ζ) := by
        funext ζ; rfl
      rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
    · have hcomp : (fun ζ => dzbar u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 + I * D I)) ∘ (fun ζ => fderiv ℝ u ζ) := by
        funext ζ; rfl
      rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  -- ===== Derivatives vanish where the function vanishes on the outer region. =====
  have hvanish : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → ∀ z, R < ‖z‖ →
      dz u z = 0 ∧ dzbar u z = 0 := by
    intro u hu z hz
    have hopen : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
    have hev : u =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun w hw => hu w hw)
    have hfd : fderiv ℝ u z = 0 := by
      rw [hev.fderiv_eq]; exact fderiv_const_apply 0
    constructor <;> simp [dz, dzbar, hfd]
  -- ===== The Neumann iterates. =====
  set T : (ℂ → ℂ) → (ℂ → ℂ) := fun w z => μ z * beurling w z with hTdef
  set v : ℕ → ℂ → ℂ := fun n => T^[n] g with hvdef
  have hvsucc : ∀ n, v (n + 1) = fun z => μ z * beurling (v n) z := by
    intro n
    simp only [hvdef]
    rw [Function.iterate_succ_apply']
  have hvprop : ∀ n, ContDiff ℝ ∞ (v n) ∧ HasCompactSupport (v n) ∧
      ∀ z, R < ‖z‖ → v n z = 0 := by
    intro n
    induction n with
    | zero => exact ⟨hgs, hgc, fun z hz => (hsupp z hz).2⟩
    | succ n ih =>
      obtain ⟨hsm, hcs, hvan⟩ := ih
      rw [hvsucc n]
      refine ⟨hμs.mul (contDiff_beurling hsm hcs), hμc.mul_right, ?_⟩
      intro z hz; simp only [(hsupp z hz).1, zero_mul]
  -- ===== Smooth identities: `S u = P (∂u)`, `∂(S u) = S (∂u)`, `∂̄(S u) = ∂u`. =====
  have hdzS : ∀ (u : ℂ → ℂ), ContDiff ℝ ∞ u → HasCompactSupport u → ∀ z,
      dz (fun w => beurling u w) z = beurling (fun ζ => dz u ζ) z ∧
      dzbar (fun w => beurling u w) z = dz u z := by
    intro u hu huc z
    have hdzu_sm : ContDiff ℝ ∞ (fun ζ => dz u ζ) := (hdz_sm u hu).1
    have hdzu_cs : HasCompactSupport (fun ζ => dz u ζ) := (hdz_cs u huc).1
    have hdzu1 : ContDiff ℝ 1 (fun ζ => dz u ζ) :=
      hdzu_sm.of_le (by exact_mod_cast le_top)
    have hfun : (fun w => beurling u w) = cauchyTransform (fun ζ => dz u ζ) := by
      funext w; exact beurling_eq_cauchyTransform_dz hu huc w
    rw [hfun]
    exact ⟨beurling_eq_dz_cauchyTransform hdzu1 hdzu_cs z,
      dzbar_cauchyTransform hdzu1 hdzu_cs z⟩
  -- ===== First-derivative recursion. =====
  have hrec : ∀ n z,
      dz (v (n + 1)) z
        = dz μ z * beurling (v n) z + μ z * beurling (fun ζ => dz (v n) ζ) z ∧
      dzbar (v (n + 1)) z
        = dzbar μ z * beurling (v n) z + μ z * dz (v n) z := by
    intro n z
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hμd : DifferentiableAt ℝ μ z := hd1 hμs z
    have hSd : DifferentiableAt ℝ (fun w => beurling (v n) w) z :=
      hd1 (contDiff_beurling hsm hcs) z
    have hzz := hdzS (v n) hsm hcs z
    rw [hvsucc n]
    constructor
    · rw [dz_mul hμd hSd, hzz.1]; ring
    · rw [dzbar_mul hμd hSd, hzz.2]; ring
  -- ===== Second-derivative recursion. =====
  have hrec2 : ∀ n z,
      dz (fun ζ => dz (v (n + 1)) ζ) z
        = dz (fun ζ => dz μ ζ) z * beurling (v n) z
          + dz μ z * beurling (fun ζ => dz (v n) ζ) z
          + (dz μ z * beurling (fun ζ => dz (v n) ζ) z
            + μ z * beurling (fun ζ => dz (fun w => dz (v n) w) ζ) z) := by
    intro n z
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hdzvn_sm : ContDiff ℝ ∞ (fun ζ => dz (v n) ζ) := (hdz_sm (v n) hsm).1
    have hdzvn_cs : HasCompactSupport (fun ζ => dz (v n) ζ) := (hdz_cs (v n) hcs).1
    have hfun : (fun ζ => dz (v (n + 1)) ζ)
        = fun ζ => dz μ ζ * beurling (v n) ζ + μ ζ * beurling (fun w => dz (v n) w) ζ := by
      funext ζ; exact (hrec n ζ).1
    rw [hfun]
    have hμd : DifferentiableAt ℝ (fun ζ => dz μ ζ) z := hd1 (hdz_sm μ hμs).1 z
    have hμd' : DifferentiableAt ℝ μ z := hd1 hμs z
    have hS1 : DifferentiableAt ℝ (fun w => beurling (v n) w) z :=
      hd1 (contDiff_beurling hsm hcs) z
    have hS2 : DifferentiableAt ℝ (fun w => beurling (fun ζ => dz (v n) ζ) w) z :=
      hd1 (contDiff_beurling hdzvn_sm hdzvn_cs) z
    have hprod1 : DifferentiableAt ℝ (fun ζ => dz μ ζ * beurling (v n) ζ) z :=
      hμd.mul hS1
    have hprod2 : DifferentiableAt ℝ
        (fun ζ => μ ζ * beurling (fun w => dz (v n) w) ζ) z := hμd'.mul hS2
    rw [dz_add hprod1 hprod2, dz_mul hμd hS1, dz_mul hμd' hS2,
      (hdzS (v n) hsm hcs z).1, (hdzS (fun ζ => dz (v n) ζ) hdzvn_sm hdzvn_cs z).1]
    ring
  -- ===== Sup-norm bounds for the fixed smooth data. =====
  obtain ⟨M₀, hM₀⟩ := hμs.continuous.bounded_above_of_compact_support hμc
  obtain ⟨M₁, hM₁⟩ :=
    (hdz_sm μ hμs).1.continuous.bounded_above_of_compact_support (hdz_cs μ hμc).1
  obtain ⟨M₂, hM₂⟩ := ((hdz_sm (fun ζ => dz μ ζ)
    (hdz_sm μ hμs).1).1).continuous.bounded_above_of_compact_support
    ((hdz_cs (fun ζ => dz μ ζ) (hdz_cs μ hμc).1).1)
  obtain ⟨M₃, hM₃⟩ :=
    (hdz_sm μ hμs).2.continuous.bounded_above_of_compact_support (hdz_cs μ hμc).2
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hM₃0 : 0 ≤ M₃ := le_trans (norm_nonneg _) (hM₃ 0)
  -- ===== `MemLp` for continuous compactly supported functions. =====
  have hmem : ∀ (u : ℂ → ℂ), Continuous u → HasCompactSupport u → MemLp u p volume :=
    fun u hu huc => hu.memLp_of_hasCompactSupport huc
  have hvmem : ∀ n, MemLp (v n) p volume := fun n =>
    hmem _ (hvprop n).1.continuous (hvprop n).2.1
  have hdzvmem : ∀ n, MemLp (fun ζ => dz (v n) ζ) p volume := fun n =>
    hmem _ ((hdz_sm _ (hvprop n).1).1).continuous ((hdz_cs _ (hvprop n).2.1).1)
  have hdz2vmem : ∀ n, MemLp (fun ζ => dz (fun w => dz (v n) w) ζ) p volume := fun n =>
    hmem _ ((hdz_sm _ ((hdz_sm _ (hvprop n).1).1)).1).continuous
      ((hdz_cs _ ((hdz_cs _ (hvprop n).2.1).1)).1)
  -- ===== a.e. bound `‖μ‖ ≤ k`. =====
  have hμ_ae : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ₑ ≤ eLpNormEssSup μ volume :=
      ae_le_eLpNormEssSup
    have hfin : eLpNormEssSup μ volume ≠ ⊤ := by
      have h2 := (memLp_top_of_continuous_hasCompactSupport hμs.continuous hμc).2
      rw [eLpNorm_exponent_top] at h2
      exact h2.ne
    filter_upwards [h1] with z hz
    rw [← ofReal_norm_eq_enorm] at hz
    have h3 := ENNReal.toReal_mono hfin hz
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h3
  -- ===== `Lᵖ` multiplication bound by an a.e.-bounded factor. =====
  have hmul : ∀ (afn h : ℂ → ℂ) (M : ℝ), 0 ≤ M →
      (∀ᵐ z ∂(volume : Measure ℂ), ‖afn z‖ ≤ M) →
      eLpNorm (fun z => afn z * h z) p volume
        ≤ ENNReal.ofReal M * eLpNorm h p volume := by
    intro afn h M hM0 hb
    have hMnorm : ‖(M : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
    have hpt : ∀ᵐ z ∂(volume : Measure ℂ), ‖afn z * h z‖ ≤ ‖(M : ℂ) * h z‖ := by
      filter_upwards [hb] with z hz
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hz.trans (le_of_eq hMnorm.symm)) (norm_nonneg _)
    calc eLpNorm (fun z => afn z * h z) p volume
        ≤ eLpNorm (fun z => (M : ℂ) * h z) p volume := eLpNorm_mono_ae hpt
      _ = ‖(M : ℂ)‖ₑ * eLpNorm h p volume := by
          have heq : (fun z => (M : ℂ) * h z) = (M : ℂ) • h := by
            funext z; rw [Pi.smul_apply, smul_eq_mul]
          rw [heq, eLpNorm_const_smul]
      _ = ENNReal.ofReal M * eLpNorm h p volume := by
          rw [← ofReal_norm_eq_enorm, hMnorm]
  -- ===== The core term bound: `‖a·S u‖ₚ ≤ (M·C)·‖u‖ₚ`. =====
  have hterm : ∀ (M : ℝ) (afn u : ℂ → ℂ), 0 ≤ M →
      (∀ᵐ z ∂(volume : Measure ℂ), ‖afn z‖ ≤ M) → MemLp u p volume →
      eLpNorm (fun z => afn z * beurling u z) p volume
        ≤ ENNReal.ofReal (M * C) * eLpNorm u p volume := by
    intro M afn u hM0 hb hu
    calc eLpNorm (fun z => afn z * beurling u z) p volume
        ≤ ENNReal.ofReal M * eLpNorm (beurling u) p volume := hmul afn _ M hM0 hb
      _ ≤ ENNReal.ofReal M * (ENNReal.ofReal C * eLpNorm u p volume) :=
          mul_le_mul_right (hCb.2 u hu) _
      _ = ENNReal.ofReal (M * C) * eLpNorm u p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hM0]
  -- ===== The real-valued `Lᵖ` norms of the cascade. =====
  set a : ℕ → ℝ := fun n => (eLpNorm (v n) p volume).toReal with hadef
  set b : ℕ → ℝ := fun n => (eLpNorm (fun ζ => dz (v n) ζ) p volume).toReal with hbdef
  set c : ℕ → ℝ :=
    fun n => (eLpNorm (fun ζ => dz (fun w => dz (v n) w) ζ) p volume).toReal with hcdef
  have haN : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  have hbN : ∀ n, 0 ≤ b n := fun n => ENNReal.toReal_nonneg
  have hcN : ∀ n, 0 ≤ c n := fun n => ENNReal.toReal_nonneg
  -- Level 0: `a (n+1) ≤ (k·C)·a n`.
  have hab : ∀ n, a (n + 1) ≤ (k * C) * a n := by
    intro n
    have h1 : eLpNorm (v (n + 1)) p volume
        ≤ ENNReal.ofReal (k * C) * eLpNorm (v n) p volume := by
      rw [hvsucc n]; exact hterm k μ (v n) hk0 hμ_ae (hvmem n)
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hvmem n).2.ne) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0] at h2
  -- Level 1: `b (n+1) ≤ M₁·C·a n + (k·C)·b n`.
  have hbb : ∀ n, b (n + 1) ≤ M₁ * C * a n + (k * C) * b n := by
    intro n
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hfun : (fun ζ => dz (v (n + 1)) ζ)
        = fun ζ => dz μ ζ * beurling (v n) ζ
            + μ ζ * beurling (fun w => dz (v n) w) ζ := by
      funext ζ; exact (hrec n ζ).1
    have hcont1 : Continuous (fun ζ => dz μ ζ * beurling (v n) ζ) :=
      (hdz_sm μ hμs).1.continuous.mul (contDiff_beurling hsm hcs).continuous
    have hcont2 : Continuous (fun ζ => μ ζ * beurling (fun w => dz (v n) w) ζ) :=
      hμs.continuous.mul (contDiff_beurling (hdz_sm _ hsm).1 (hdz_cs _ hcs).1).continuous
    have hadd : eLpNorm (fun ζ => dz (v (n + 1)) ζ) p volume
        ≤ ENNReal.ofReal (M₁ * C) * eLpNorm (v n) p volume
          + ENNReal.ofReal (k * C) * eLpNorm (fun w => dz (v n) w) p volume := by
      rw [hfun]
      refine le_trans
        (eLpNorm_add_le hcont1.aestronglyMeasurable hcont2.aestronglyMeasurable hp1) ?_
      exact add_le_add
        (hterm M₁ _ _ hM₁0 (Filter.Eventually.of_forall hM₁) (hvmem n))
        (hterm k μ _ hk0 hμ_ae (hdzvmem n))
    have hne1 : ENNReal.ofReal (M₁ * C) * eLpNorm (v n) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hvmem n).2.ne
    have hne2 : ENNReal.ofReal (k * C) * eLpNorm (fun w => dz (v n) w) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdzvmem n).2.ne
    have h2 := ENNReal.toReal_mono (by
      rw [ENNReal.add_ne_top]; exact ⟨hne1, hne2⟩) hadd
    rwa [ENNReal.toReal_add hne1 hne2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg hM₁0 hC0), ENNReal.toReal_ofReal hr0] at h2
  -- Level 2: `c (n+1) ≤ M₂·C·a n + M₁·C·b n + (M₁·C·b n + (k·C)·c n)`.
  have hcc : ∀ n, c (n + 1)
      ≤ (M₂ * C * a n + M₁ * C * b n) + (M₁ * C * b n + (k * C) * c n) := by
    intro n
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hdzvn_sm : ContDiff ℝ ∞ (fun ζ => dz (v n) ζ) := (hdz_sm (v n) hsm).1
    have hdzvn_cs : HasCompactSupport (fun ζ => dz (v n) ζ) := (hdz_cs (v n) hcs).1
    have hfun : (fun ζ => dz (fun w => dz (v (n + 1)) w) ζ)
        = fun ζ => (dz (fun w => dz μ w) ζ * beurling (v n) ζ
            + dz μ ζ * beurling (fun w => dz (v n) w) ζ)
          + (dz μ ζ * beurling (fun w => dz (v n) w) ζ
            + μ ζ * beurling (fun w => dz (fun t => dz (v n) t) w) ζ) := by
      funext ζ
      exact hrec2 n ζ
    have hcA : Continuous (fun ζ => dz (fun w => dz μ w) ζ * beurling (v n) ζ) :=
      ((hdz_sm _ (hdz_sm μ hμs).1).1).continuous.mul
        (contDiff_beurling hsm hcs).continuous
    have hcB : Continuous (fun ζ => dz μ ζ * beurling (fun w => dz (v n) w) ζ) :=
      (hdz_sm μ hμs).1.continuous.mul
        (contDiff_beurling hdzvn_sm hdzvn_cs).continuous
    have hcC : Continuous
        (fun ζ => μ ζ * beurling (fun w => dz (fun t => dz (v n) t) w) ζ) :=
      hμs.continuous.mul (contDiff_beurling (hdz_sm _ hdzvn_sm).1
        (hdz_cs _ hdzvn_cs).1).continuous
    have htA : eLpNorm (fun ζ => dz (fun w => dz μ w) ζ * beurling (v n) ζ) p volume
        ≤ ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume :=
      hterm M₂ _ _ hM₂0 (Filter.Eventually.of_forall hM₂) (hvmem n)
    have htB : eLpNorm (fun ζ => dz μ ζ * beurling (fun w => dz (v n) w) ζ) p volume
        ≤ ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume :=
      hterm M₁ _ _ hM₁0 (Filter.Eventually.of_forall hM₁) (hdzvmem n)
    have htC : eLpNorm
        (fun ζ => μ ζ * beurling (fun w => dz (fun t => dz (v n) t) w) ζ) p volume
        ≤ ENNReal.ofReal (k * C)
            * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume :=
      hterm k μ _ hk0 hμ_ae (hdz2vmem n)
    have hadd : eLpNorm (fun ζ => dz (fun w => dz (v (n + 1)) w) ζ) p volume
        ≤ (ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume
            + ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume)
          + (ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume
            + ENNReal.ofReal (k * C)
                * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume) := by
      rw [hfun]
      refine le_trans (eLpNorm_add_le
        (hcA.add hcB).aestronglyMeasurable (hcB.add hcC).aestronglyMeasurable hp1) ?_
      refine add_le_add ?_ ?_
      · exact le_trans (eLpNorm_add_le hcA.aestronglyMeasurable
          hcB.aestronglyMeasurable hp1) (add_le_add htA htB)
      · exact le_trans (eLpNorm_add_le hcB.aestronglyMeasurable
          hcC.aestronglyMeasurable hp1) (add_le_add htB htC)
    have hneA : ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hvmem n).2.ne
    have hneB : ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdzvmem n).2.ne
    have hneC : ENNReal.ofReal (k * C)
        * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdz2vmem n).2.ne
    have hneAB : ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume
        + ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume ≠ ⊤ := by
      rw [ENNReal.add_ne_top]; exact ⟨hneA, hneB⟩
    have hneBC : ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume
        + ENNReal.ofReal (k * C)
            * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume ≠ ⊤ := by
      rw [ENNReal.add_ne_top]; exact ⟨hneB, hneC⟩
    have h2 := ENNReal.toReal_mono (by
      rw [ENNReal.add_ne_top]; exact ⟨hneAB, hneBC⟩) hadd
    rwa [ENNReal.toReal_add hneAB hneBC, ENNReal.toReal_add hneA hneB,
      ENNReal.toReal_add hneB hneC, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hM₂0 hC0),
      ENNReal.toReal_ofReal (mul_nonneg hM₁0 hC0), ENNReal.toReal_ofReal hr0] at h2
  -- ===== Geometric decay with margin: `a n, b n, c n ≤ Dᵢ · r'^n`. =====
  have hr'pow : ∀ n : ℕ, (0 : ℝ) ≤ r' ^ n := fun n => pow_nonneg hr'0.le n
  set D₀ : ℝ := a 0 with hD₀def
  have hD₀0 : 0 ≤ D₀ := haN 0
  have haD : ∀ n, a n ≤ D₀ * r' ^ n := by
    intro n
    induction n with
    | zero => simp [hD₀def]
    | succ n ih =>
      calc a (n + 1) ≤ (k * C) * a n := hab n
        _ ≤ (k * C) * (D₀ * r' ^ n) := mul_le_mul_of_nonneg_left ih hr0
        _ ≤ r' * (D₀ * r' ^ n) :=
            mul_le_mul_of_nonneg_right hrr'.le (mul_nonneg hD₀0 (hr'pow n))
        _ = D₀ * r' ^ (n + 1) := by ring
  set D₁ : ℝ := b 0 + M₁ * C * D₀ / δ with hD₁def
  have hD₁0 : 0 ≤ D₁ :=
    add_nonneg (hbN 0) (div_nonneg (mul_nonneg (mul_nonneg hM₁0 hC0) hD₀0) hδ0.le)
  have hδD₁ : M₁ * C * D₀ ≤ δ * D₁ := by
    rw [hD₁def, mul_add, mul_div_cancel₀ _ hδ0.ne']
    nlinarith [mul_nonneg hδ0.le (hbN 0)]
  have hbD : ∀ n, b n ≤ D₁ * r' ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 : 0 ≤ M₁ * C * D₀ / δ :=
        div_nonneg (mul_nonneg (mul_nonneg hM₁0 hC0) hD₀0) hδ0.le
      rw [pow_zero, mul_one, hD₁def]
      linarith
    | succ n ih =>
      calc b (n + 1) ≤ M₁ * C * a n + (k * C) * b n := hbb n
        _ ≤ M₁ * C * (D₀ * r' ^ n) + (k * C) * (D₁ * r' ^ n) :=
            add_le_add (mul_le_mul_of_nonneg_left (haD n) (mul_nonneg hM₁0 hC0))
              (mul_le_mul_of_nonneg_left ih hr0)
        _ = (M₁ * C * D₀ + (k * C) * D₁) * r' ^ n := by ring
        _ ≤ (δ * D₁ + (k * C) * D₁) * r' ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (hr'pow n)
            exact add_le_add hδD₁ le_rfl
        _ = D₁ * r' ^ (n + 1) := by rw [hδdef]; ring
  set D₂ : ℝ := c 0 + (M₂ * C * D₀ + 2 * (M₁ * C) * D₁) / δ with hD₂def
  have hnum2 : 0 ≤ M₂ * C * D₀ + 2 * (M₁ * C) * D₁ := by
    have h1 : 0 ≤ M₂ * C * D₀ := mul_nonneg (mul_nonneg hM₂0 hC0) hD₀0
    have h2 : 0 ≤ 2 * (M₁ * C) * D₁ :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hM₁0 hC0)) hD₁0
    linarith
  have hD₂0 : 0 ≤ D₂ := add_nonneg (hcN 0) (div_nonneg hnum2 hδ0.le)
  have hδD₂ : M₂ * C * D₀ + 2 * (M₁ * C) * D₁ ≤ δ * D₂ := by
    have hexp : δ * D₂ = δ * c 0 + (M₂ * C * D₀ + 2 * (M₁ * C) * D₁) := by
      rw [hD₂def, mul_add, mul_div_cancel₀ _ hδ0.ne']
    rw [hexp]
    have h0 : 0 ≤ δ * c 0 := mul_nonneg hδ0.le (hcN 0)
    linarith
  have hcD : ∀ n, c n ≤ D₂ * r' ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 : 0 ≤ (M₂ * C * D₀ + 2 * (M₁ * C) * D₁) / δ := div_nonneg hnum2 hδ0.le
      rw [pow_zero, mul_one, hD₂def]
      linarith
    | succ n ih =>
      calc c (n + 1)
          ≤ (M₂ * C * a n + M₁ * C * b n) + (M₁ * C * b n + (k * C) * c n) := hcc n
        _ ≤ (M₂ * C * (D₀ * r' ^ n) + M₁ * C * (D₁ * r' ^ n))
              + (M₁ * C * (D₁ * r' ^ n) + (k * C) * (D₂ * r' ^ n)) := by
            refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ ?_)
            · exact mul_le_mul_of_nonneg_left (haD n) (mul_nonneg hM₂0 hC0)
            · exact mul_le_mul_of_nonneg_left (hbD n) (mul_nonneg hM₁0 hC0)
            · exact mul_le_mul_of_nonneg_left (hbD n) (mul_nonneg hM₁0 hC0)
            · exact mul_le_mul_of_nonneg_left ih hr0
        _ = (M₂ * C * D₀ + 2 * (M₁ * C) * D₁ + (k * C) * D₂) * r' ^ n := by ring
        _ ≤ (δ * D₂ + (k * C) * D₂) * r' ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (hr'pow n)
            nlinarith
        _ = D₂ * r' ^ (n + 1) := by rw [hδdef]; ring
  -- ===== The uniform sup bound for the Cauchy transform. =====
  obtain ⟨CR, hCR0, hCR⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp hp'
  -- Vanishing of iterate derivatives outside the support ball.
  have hdzv_van : ∀ n, ∀ z, R < ‖z‖ → dz (v n) z = 0 := fun n z hz =>
    (hvanish (v n) (hvprop n).2.2 z hz).1
  have hdbv_van : ∀ n, ∀ z, R < ‖z‖ → dzbar (v n) z = 0 := fun n z hz =>
    (hvanish (v n) (hvprop n).2.2 z hz).2
  -- Sup bound for `S u` through the potential bound: `‖S u‖∞ ≤ CR·‖∂u‖ₚ`.
  have hSsup : ∀ (u : ℂ → ℂ), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ z, R < ‖z‖ → u z = 0) → ∀ z,
      ‖beurling u z‖ ≤ CR * (eLpNorm (fun ζ => dz u ζ) p volume).toReal := by
    intro u hu huc huv z
    rw [beurling_eq_cauchyTransform_dz hu huc z]
    exact hCR _ (hmem _ ((hdz_sm u hu).1).continuous ((hdz_cs u huc).1))
      (fun w hw => (hvanish u huv w hw).1) z
  -- Sup decay of the transforms of the iterates.
  have hsupS : ∀ n z, ‖beurling (v n) z‖ ≤ CR * (D₁ * r' ^ n) := by
    intro n z
    refine le_trans (hSsup (v n) (hvprop n).1 (hvprop n).2.1 (hvprop n).2.2 z) ?_
    exact mul_le_mul_of_nonneg_left (hbD n) hCR0
  have hsupSdz : ∀ n z, ‖beurling (fun ζ => dz (v n) ζ) z‖ ≤ CR * (D₂ * r' ^ n) := by
    intro n z
    refine le_trans (hSsup (fun ζ => dz (v n) ζ) ((hdz_sm _ (hvprop n).1).1)
      ((hdz_cs _ (hvprop n).2.1).1) (hdzv_van n) z) ?_
    exact mul_le_mul_of_nonneg_left (hcD n) hCR0
  -- Sup bounds for the data `g`.
  obtain ⟨Mg, hMg⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  obtain ⟨Mg₁, hMg₁⟩ :=
    ((hdz_sm g hgs).1).continuous.bounded_above_of_compact_support ((hdz_cs g hgc).1)
  obtain ⟨Mg₂, hMg₂⟩ :=
    ((hdz_sm g hgs).2).continuous.bounded_above_of_compact_support ((hdz_cs g hgc).2)
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0)
  have hMg₁0 : 0 ≤ Mg₁ := le_trans (norm_nonneg _) (hMg₁ 0)
  have hMg₂0 : 0 ≤ Mg₂ := le_trans (norm_nonneg _) (hMg₂ 0)
  -- ===== Geometric sup decay of the iterates and their first derivatives. =====
  set Kv : ℝ := max Mg (M₀ * (CR * D₁) / r') with hKvdef
  have hKv0 : 0 ≤ Kv := le_trans hMg0 (le_max_left _ _)
  have hKv : ∀ n z, ‖v n z‖ ≤ Kv * r' ^ n := by
    intro n z
    cases n with
    | zero =>
      rw [pow_zero, mul_one]
      exact le_trans (hMg z) (le_max_left _ _)
    | succ n =>
      have h1 : v (n + 1) z = μ z * beurling (v n) z := congrFun (hvsucc n) z
      rw [h1, norm_mul]
      calc ‖μ z‖ * ‖beurling (v n) z‖
          ≤ M₀ * (CR * (D₁ * r' ^ n)) :=
            mul_le_mul (hM₀ z) (hsupS n z) (norm_nonneg _) hM₀0
        _ = (M₀ * (CR * D₁) / r') * r' ^ (n + 1) := by
            rw [pow_succ]; field_simp
        _ ≤ Kv * r' ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hr'pow (n + 1))
  set Kdz : ℝ := max Mg₁ ((M₁ * (CR * D₁) + M₀ * (CR * D₂)) / r') with hKdzdef
  have hKdz0 : 0 ≤ Kdz := le_trans hMg₁0 (le_max_left _ _)
  have hKdz : ∀ n z, ‖dz (v n) z‖ ≤ Kdz * r' ^ n := by
    intro n z
    cases n with
    | zero =>
      rw [pow_zero, mul_one]
      exact le_trans (hMg₁ z) (le_max_left _ _)
    | succ n =>
      rw [(hrec n z).1]
      calc ‖dz μ z * beurling (v n) z + μ z * beurling (fun ζ => dz (v n) ζ) z‖
          ≤ ‖dz μ z * beurling (v n) z‖
            + ‖μ z * beurling (fun ζ => dz (v n) ζ) z‖ := norm_add_le _ _
        _ = ‖dz μ z‖ * ‖beurling (v n) z‖
            + ‖μ z‖ * ‖beurling (fun ζ => dz (v n) ζ) z‖ := by rw [norm_mul, norm_mul]
        _ ≤ M₁ * (CR * (D₁ * r' ^ n)) + M₀ * (CR * (D₂ * r' ^ n)) :=
            add_le_add (mul_le_mul (hM₁ z) (hsupS n z) (norm_nonneg _) hM₁0)
              (mul_le_mul (hM₀ z) (hsupSdz n z) (norm_nonneg _) hM₀0)
        _ = ((M₁ * (CR * D₁) + M₀ * (CR * D₂)) / r') * r' ^ (n + 1) := by
            rw [pow_succ]; field_simp
        _ ≤ Kdz * r' ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hr'pow (n + 1))
  set Kdb : ℝ := max Mg₂ ((M₃ * (CR * D₁) + M₀ * Kdz) / r') with hKdbdef
  have hKdb0 : 0 ≤ Kdb := le_trans hMg₂0 (le_max_left _ _)
  have hKdb : ∀ n z, ‖dzbar (v n) z‖ ≤ Kdb * r' ^ n := by
    intro n z
    cases n with
    | zero =>
      rw [pow_zero, mul_one]
      exact le_trans (hMg₂ z) (le_max_left _ _)
    | succ n =>
      rw [(hrec n z).2]
      calc ‖dzbar μ z * beurling (v n) z + μ z * dz (v n) z‖
          ≤ ‖dzbar μ z * beurling (v n) z‖ + ‖μ z * dz (v n) z‖ := norm_add_le _ _
        _ = ‖dzbar μ z‖ * ‖beurling (v n) z‖ + ‖μ z‖ * ‖dz (v n) z‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ M₃ * (CR * (D₁ * r' ^ n)) + M₀ * (Kdz * r' ^ n) :=
            add_le_add (mul_le_mul (hM₃ z) (hsupS n z) (norm_nonneg _) hM₃0)
              (mul_le_mul (hM₀ z) (hKdz n z) (norm_nonneg _) hM₀0)
        _ = ((M₃ * (CR * D₁) + M₀ * Kdz) / r') * r' ^ (n + 1) := by
            rw [pow_succ]; field_simp
        _ ≤ Kdb * r' ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hr'pow (n + 1))
  -- ===== Summability of the geometric envelopes. =====
  have hgeom : Summable (fun n : ℕ => r' ^ n) :=
    summable_geometric_of_lt_one hr'0.le hr'1
  have hsum_v : Summable (fun n => Kv * r' ^ n) := hgeom.mul_left Kv
  have hsum_dz : Summable (fun n => Kdz * r' ^ n) := hgeom.mul_left Kdz
  have hsum_db : Summable (fun n => Kdb * r' ^ n) := hgeom.mul_left Kdb
  -- ===== The limit functions. =====
  set φ : ℂ → ℂ := fun z => ∑' n, v n z with hφdef
  set u₁ : ℂ → ℂ := fun z => ∑' n, dz (v n) z with hu₁def
  set u₂ : ℂ → ℂ := fun z => ∑' n, dzbar (v n) z with hu₂def
  have hφcont : Continuous φ :=
    continuous_tsum (fun n => (hvprop n).1.continuous) hsum_v (fun n z => hKv n z)
  have hu₁cont : Continuous u₁ :=
    continuous_tsum (fun n => ((hdz_sm _ (hvprop n).1).1).continuous) hsum_dz
      (fun n z => hKdz n z)
  have hu₂cont : Continuous u₂ :=
    continuous_tsum (fun n => ((hdz_sm _ (hvprop n).1).2).continuous) hsum_db
      (fun n z => hKdb n z)
  have hφvan : ∀ z, R < ‖z‖ → φ z = 0 := by
    intro z hz
    have h0 : ∀ n, v n z = 0 := fun n => (hvprop n).2.2 z hz
    simp only [hφdef]
    rw [tsum_congr h0, tsum_zero]
  have hu₁van : ∀ z, R < ‖z‖ → u₁ z = 0 := by
    intro z hz
    have h0 : ∀ n, dz (v n) z = 0 := fun n => hdzv_van n z hz
    simp only [hu₁def]
    rw [tsum_congr h0, tsum_zero]
  have hu₂van : ∀ z, R < ‖z‖ → u₂ z = 0 := by
    intro z hz
    have h0 : ∀ n, dzbar (v n) z = 0 := fun n => hdbv_van n z hz
    simp only [hu₂def]
    rw [tsum_congr h0, tsum_zero]
  have hcs_of_van : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → HasCompactSupport u := by
    intro u huv
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) ?_
    intro x hx
    refine huv x ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx
  have hφcs : HasCompactSupport φ := hcs_of_van φ hφvan
  have hu₁cs : HasCompactSupport u₁ := hcs_of_van u₁ hu₁van
  have hφmem : MemLp φ p volume := hmem φ hφcont hφcs
  -- ===== Partial sums and their Wirtinger derivatives. =====
  set s : ℕ → ℂ → ℂ := fun m z => ∑ n ∈ Finset.range m, v n z with hsdef
  set ds : ℕ → ℂ → ℂ := fun m z => ∑ n ∈ Finset.range m, dz (v n) z with hdsdef
  set db : ℕ → ℂ → ℂ := fun m z => ∑ n ∈ Finset.range m, dzbar (v n) z with hdbdef
  have hs_succ : ∀ m, s (m + 1) = fun z => s m z + v m z := by
    intro m; funext z; simp only [hsdef]; rw [Finset.sum_range_succ]
  have hds_succ : ∀ m z, ds (m + 1) z = ds m z + dz (v m) z := by
    intro m z; simp only [hdsdef]; rw [Finset.sum_range_succ]
  have hdb_succ : ∀ m z, db (m + 1) z = db m z + dzbar (v m) z := by
    intro m z; simp only [hdbdef]; rw [Finset.sum_range_succ]
  have hs_sm : ∀ m, ContDiff ℝ ∞ (s m) := by
    intro m
    induction m with
    | zero =>
      have h0 : s 0 = fun _ => (0 : ℂ) := by
        funext z; simp only [hsdef]; rw [Finset.range_zero, Finset.sum_empty]
      rw [h0]; exact contDiff_const
    | succ m ih =>
      rw [hs_succ m]; exact ih.add (hvprop m).1
  have hs_dz : ∀ m z, dz (s m) z = ds m z ∧ dzbar (s m) z = db m z := by
    intro m z
    induction m with
    | zero =>
      have h0 : s 0 = fun _ => (0 : ℂ) := by
        funext w; simp only [hsdef]; rw [Finset.range_zero, Finset.sum_empty]
      have hd0 : ds 0 z = 0 := by
        simp only [hdsdef]; rw [Finset.range_zero, Finset.sum_empty]
      have hb0 : db 0 z = 0 := by
        simp only [hdbdef]; rw [Finset.range_zero, Finset.sum_empty]
      rw [h0, hd0, hb0]
      have hfd : fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z = 0 := fderiv_const_apply 0
      constructor <;> simp [dz, dzbar, hfd]
    | succ m ih =>
      rw [hs_succ m]
      have hd₁ : DifferentiableAt ℝ (s m) z := hd1 (hs_sm m) z
      have hd₂ : DifferentiableAt ℝ (v m) z := hd1 (hvprop m).1 z
      constructor
      · rw [dz_add hd₁ hd₂, ih.1, hds_succ m z]
      · rw [dzbar_add hd₁ hd₂, ih.2, hdb_succ m z]
  -- ===== CLM assembly toolkit. =====
  have hCLMext : ∀ T S : ℂ →L[ℝ] ℂ, T 1 = S 1 → T Complex.I = S Complex.I → T = S := by
    intro T S h1 hI
    ext w
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    rw [hw]
    simp only [map_add, map_smul, h1, hI]
  have hA_apply : ∀ a b : ℂ,
      (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) (1 : ℂ) = a
      ∧ (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) Complex.I = b := by
    intro a b
    constructor
    · simp [ContinuousLinearMap.smulRight_apply]
    · simp [ContinuousLinearMap.smulRight_apply]
  have hopb : ∀ a b : ℂ,
      ‖Complex.reCLM.smulRight a + Complex.imCLM.smulRight b‖ ≤ ‖a‖ + ‖b‖ := by
    intro a b
    refine ContinuousLinearMap.opNorm_le_bound _
      (add_nonneg (norm_nonneg a) (norm_nonneg b)) (fun w => ?_)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply]
    calc ‖w.re • a + w.im • b‖
        ≤ ‖w.re • a‖ + ‖w.im • b‖ := norm_add_le _ _
      _ = |w.re| * ‖a‖ + |w.im| * ‖b‖ := by
          rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖w‖ * ‖a‖ + ‖w‖ * ‖b‖ := by
          gcongr
          · exact Complex.abs_re_le_norm w
          · exact Complex.abs_im_le_norm w
      _ = (‖a‖ + ‖b‖) * ‖w‖ := by ring
  -- ===== The Wirtinger dictionary for the total derivative. =====
  have hdict : ∀ (f : ℂ → ℂ) (z : ℂ), (fderiv ℝ f z) 1 = dz f z + dzbar f z ∧
      (fderiv ℝ f z) Complex.I = Complex.I * (dz f z - dzbar f z) := by
    intro f z
    constructor
    · rw [dz, dzbar]; ring
    · rw [dz, dzbar]
      linear_combination ((fderiv ℝ f z) Complex.I) * Complex.I_mul_I
  -- ===== Each partial sum has the assembled derivative. =====
  have hsFD : ∀ m z, HasFDerivAt (s m)
      (Complex.reCLM.smulRight (ds m z + db m z)
        + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z))) z := by
    intro m z
    have hd : DifferentiableAt ℝ (s m) z := hd1 (hs_sm m) z
    have hEq : fderiv ℝ (s m) z
        = Complex.reCLM.smulRight (ds m z + db m z)
          + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z)) := by
      refine hCLMext _ _ ?_ ?_
      · rw [(hdict (s m) z).1, (hA_apply _ _).1, (hs_dz m z).1, (hs_dz m z).2]
      · rw [(hdict (s m) z).2, (hA_apply _ _).2, (hs_dz m z).1, (hs_dz m z).2]
    exact hEq ▸ hd.hasFDerivAt
  -- ===== Uniform convergence of the partial sums and their derivatives. =====
  have hsTU : TendstoUniformly (fun m z => s m z) φ atTop :=
    tendstoUniformly_tsum_nat hsum_v (fun n z => hKv n z)
  have hdsTU : TendstoUniformly (fun m z => ds m z) u₁ atTop :=
    tendstoUniformly_tsum_nat hsum_dz (fun n z => hKdz n z)
  have hdbTU : TendstoUniformly (fun m z => db m z) u₂ atTop :=
    tendstoUniformly_tsum_nat hsum_db (fun n z => hKdb n z)
  -- ===== Locally uniform convergence of the assembled derivatives. =====
  have hATLU : TendstoLocallyUniformlyOn
      (fun m z => Complex.reCLM.smulRight (ds m z + db m z)
        + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z)))
      (fun z => Complex.reCLM.smulRight (u₁ z + u₂ z)
        + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)))
      atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]
    refine TendstoUniformly.tendstoLocallyUniformly ?_
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε4 : (0 : ℝ) < ε / 4 := by positivity
    rw [Metric.tendstoUniformly_iff] at hdsTU hdbTU
    filter_upwards [hdsTU (ε / 4) hε4, hdbTU (ε / 4) hε4] with m hm₁ hm₂ z
    have h1 := hm₁ z
    have h2 := hm₂ z
    rw [dist_eq_norm] at h1 h2
    rw [dist_eq_norm]
    have hdiff : (Complex.reCLM.smulRight (u₁ z + u₂ z)
          + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)))
        - (Complex.reCLM.smulRight (ds m z + db m z)
          + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z)))
        = Complex.reCLM.smulRight ((u₁ z - ds m z) + (u₂ z - db m z))
          + Complex.imCLM.smulRight
              (Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z))) := by
      refine hCLMext _ _ ?_ ?_
      · rw [ContinuousLinearMap.sub_apply,
          (hA_apply (u₁ z + u₂ z) (Complex.I * (u₁ z - u₂ z))).1,
          (hA_apply (ds m z + db m z) (Complex.I * (ds m z - db m z))).1,
          (hA_apply ((u₁ z - ds m z) + (u₂ z - db m z))
            (Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z)))).1]
        ring
      · rw [ContinuousLinearMap.sub_apply,
          (hA_apply (u₁ z + u₂ z) (Complex.I * (u₁ z - u₂ z))).2,
          (hA_apply (ds m z + db m z) (Complex.I * (ds m z - db m z))).2,
          (hA_apply ((u₁ z - ds m z) + (u₂ z - db m z))
            (Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z)))).2]
        ring
    rw [hdiff]
    refine lt_of_le_of_lt (hopb _ _) ?_
    have hb1 : ‖(u₁ z - ds m z) + (u₂ z - db m z)‖ < ε / 4 + ε / 4 :=
      lt_of_le_of_lt (norm_add_le _ _) (add_lt_add h1 h2)
    have hb2 : ‖Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z))‖ < ε / 4 + ε / 4 := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact lt_of_le_of_lt (norm_sub_le _ _) (add_lt_add h1 h2)
    linarith
  -- ===== The limit: `φ` is differentiable with the assembled derivative. =====
  have hφFD : ∀ z, HasFDerivAt φ
      (Complex.reCLM.smulRight (u₁ z + u₂ z)
        + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z))) z := fun z =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hATLU
      (fun m x _ => hsFD m x) (fun x _ => hsTU.tendsto_at x) (Set.mem_univ z)
  have hφfeq : ∀ z, fderiv ℝ φ z
      = Complex.reCLM.smulRight (u₁ z + u₂ z)
        + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)) := fun z =>
    (hφFD z).fderiv
  have hφC1 : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (hφFD z).differentiableAt, ?_⟩
    have heqf : fderiv ℝ φ = fun z =>
        Complex.reCLM.smulRight (u₁ z + u₂ z)
          + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)) := funext hφfeq
    rw [heqf]
    have hc1 : Continuous (fun z => u₁ z + u₂ z) := hu₁cont.add hu₂cont
    have hc2 : Continuous (fun z => Complex.I * (u₁ z - u₂ z)) :=
      continuous_const.mul (hu₁cont.sub hu₂cont)
    exact (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).continuous.comp hc1).add
      (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).continuous.comp hc2)))
  -- ===== The Wirtinger derivatives of `φ` are the summed series. =====
  have hφdz : ∀ z, dz φ z = u₁ z ∧ dzbar φ z = u₂ z := by
    intro z
    have h1 : (fderiv ℝ φ z) 1 = u₁ z + u₂ z := by
      rw [hφfeq z]; exact (hA_apply _ _).1
    have hI : (fderiv ℝ φ z) Complex.I = Complex.I * (u₁ z - u₂ z) := by
      rw [hφfeq z]; exact (hA_apply _ _).2
    constructor
    · rw [dz, h1, hI]
      linear_combination (-(1 / 2 : ℂ) * (u₁ z - u₂ z)) * Complex.I_mul_I
    · rw [dzbar, h1, hI]
      linear_combination ((1 / 2 : ℂ) * (u₁ z - u₂ z)) * Complex.I_mul_I
  -- ===== `S φ = P (∂φ)` pointwise (`φ` is `C¹` with compact support). =====
  have hbeurφ : ∀ z, beurling φ z = cauchyTransform (fun ζ => dz φ ζ) z := by
    intro z
    rw [beurling, cauchyTransform]
    congr 1
    refine Filter.Tendsto.limUnder_eq ?_
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r φ z
        = czOperator beurlingKernel r φ z := fun r => rfl
    simpa only [hcz] using czOperator_beurling_tendsto_smooth hφC1 hφcs z
  have hdzφfun : (fun ζ => dz φ ζ) = u₁ := by funext ζ; exact (hφdz ζ).1
  have hbeurφ' : ∀ z, beurling φ z = cauchyTransform u₁ z := by
    intro z; rw [hbeurφ z, hdzφfun]
  have hSφcont : Continuous (beurling φ) := by
    have hfun : beurling φ = cauchyTransform u₁ := funext hbeurφ'
    rw [hfun]
    exact continuous_cauchyTransform_of_memLp_of_support hp hp'
      (hmem u₁ hu₁cont hu₁cs) hu₁van
  -- ===== Local integrability of the Cauchy kernel (polar coordinates). =====
  have hk_loc : LocallyIntegrable (fun w : ℂ => -w⁻¹) volume := by
    apply LocallyIntegrable.neg
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR₀
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ q ∈ polarCoord.target,
        ENNReal.ofReal q.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
          (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q) ≤ box q := by
      intro q hq
      simp only [hbox]
      rw [polarCoord_target, Set.mem_prod] at hq
      obtain ⟨hq1, hq2⟩ := hq
      simp only [Set.mem_Ioi] at hq1
      by_cases hmem' : Complex.polarCoord.symm q ∈ Metric.closedBall (0 : ℂ) R₀
      · rw [Set.indicator_of_mem hmem']
        have hnorm : ‖Complex.polarCoord.symm q‖ = q.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hq1]
        have hsymm_ne : Complex.polarCoord.symm q ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hq1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm q‖ₑ = ENNReal.ofReal q.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel
            (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq1)
            ENNReal.ofReal_lt_top.ne]
        have hqR : q.1 ≤ R₀ := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem'; exact hmem'
        rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hq1, hqR⟩, hq2⟩)]
      · rw [Set.indicator_of_notMem hmem']; simp
    calc
      ∫⁻ q in polarCoord.target, ENNReal.ofReal q.1 •
          (Metric.closedBall (0 : ℂ) R₀).indicator
            (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q)
          ≤ ∫⁻ q in polarCoord.target, box q :=
            setLIntegral_mono (measurable_const.indicator
              (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
      _ ≤ ∫⁻ q, box q := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
            rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
            simp
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc,
              Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- ===== Integrability of Cauchy integrands over continuous c.s. data. =====
  have hPint : ∀ (w : ℂ → ℂ), Continuous w → HasCompactSupport w → ∀ z : ℂ,
      Integrable (fun ζ => w ζ / (ζ - z)) volume := by
    intro w hw hwc z
    have h : Integrable (fun t =>
        (ContinuousLinearMap.mul ℝ ℂ) (w t) ((fun u : ℂ => -u⁻¹) (z - t))) volume :=
      (hwc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hw hk_loc) z
    have heq : (fun t =>
        (ContinuousLinearMap.mul ℝ ℂ) (w t) ((fun u : ℂ => -u⁻¹) (z - t)))
        = fun ζ => w ζ / (ζ - z) := by
      funext ζ
      rw [ContinuousLinearMap.mul_apply']
      change w ζ * -(z - ζ)⁻¹ = w ζ / (ζ - z)
      have hflip : -(z - ζ)⁻¹ = (ζ - z)⁻¹ := by rw [← neg_sub ζ z, inv_neg, neg_neg]
      rw [hflip, div_eq_mul_inv]
    rw [heq] at h
    exact h
  -- ===== Finite additivity of the Cauchy transform over the partial sums. =====
  have hds_cont : ∀ m, Continuous (fun ζ => ds m ζ) := by
    intro m
    have hc : ∀ n ∈ Finset.range m, Continuous (fun ζ => dz (v n) ζ) := fun n _ =>
      ((hdz_sm _ (hvprop n).1).1).continuous
    simpa only [hdsdef] using continuous_finset_sum _ hc
  have hds_van : ∀ m, ∀ ζ, R < ‖ζ‖ → ds m ζ = 0 := by
    intro m ζ hζ
    simp only [hdsdef]
    exact Finset.sum_eq_zero (fun n _ => hdzv_van n ζ hζ)
  have hPadd : ∀ m z, (∑ n ∈ Finset.range m,
      cauchyTransform (fun ζ => dz (v n) ζ) z) = cauchyTransform (fun ζ => ds m ζ) z := by
    intro m z
    have hint : ∀ n ∈ Finset.range m,
        Integrable (fun ζ => dz (v n) ζ / (ζ - z)) volume := fun n _ =>
      hPint _ ((hdz_sm _ (hvprop n).1).1).continuous ((hdz_cs _ (hvprop n).2.1).1) z
    simp only [cauchyTransform]
    rw [← Finset.mul_sum]
    congr 1
    rw [← MeasureTheory.integral_finset_sum _ hint]
    congr 1
    funext ζ
    simp only [hdsdef]
    rw [Finset.sum_div]
  -- ===== `eLpNorm` from a uniform bound on the support ball. =====
  have hpt0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hVfin : volume (Metric.closedBall (0 : ℂ) R) ≠ ⊤ :=
    ((isCompact_closedBall (0 : ℂ) R).measure_lt_top).ne
  set Vp : ℝ := ((volume (Metric.closedBall (0 : ℂ) R)) ^ (1 / p.toReal)).toReal
    with hVpdef
  have help : ∀ (w : ℂ → ℂ) (t : ℝ), 0 ≤ t → (∀ ζ, ‖w ζ‖ ≤ t) →
      (∀ ζ, R < ‖ζ‖ → w ζ = 0) →
      (eLpNorm w p volume).toReal ≤ t * Vp := by
    intro w t ht hb hv
    have hmono : eLpNorm w p volume
        ≤ eLpNorm ((Metric.closedBall (0 : ℂ) R).indicator (fun _ => t)) p volume := by
      apply eLpNorm_mono
      intro ζ
      by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hζ, Real.norm_eq_abs, abs_of_nonneg ht]
        exact hb ζ
      · rw [Set.indicator_of_notMem hζ]
        have hout : R < ‖ζ‖ := by
          rwa [Metric.mem_closedBall, dist_zero_right, not_le] at hζ
        rw [hv ζ hout]
        simp
    rw [eLpNorm_indicator_const measurableSet_closedBall hp0 hp'] at hmono
    have hne : ‖t‖ₑ * volume (Metric.closedBall (0 : ℂ) R) ^ (1 / p.toReal) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ?_ (ENNReal.rpow_lt_top_of_nonneg
        (div_nonneg zero_le_one hpt0.le) hVfin).ne
      rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_ne_top
    have h2 := ENNReal.toReal_mono hne hmono
    rwa [ENNReal.toReal_mul, ← ofReal_norm_eq_enorm,
      ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs, abs_of_nonneg ht] at h2
  -- ===== The pointwise fixed-point equation. =====
  have heqn : ∀ z : ℂ, φ z = μ z * beurling φ z + g z := by
    intro z
    -- The partial-sum recursion at `z`.
    have hids : ∀ m, s (m + 1) z
        = μ z * cauchyTransform (fun ζ => ds m ζ) z + g z := by
      intro m
      have hv0 : v 0 z = g z := by
        simp only [hvdef]; rw [Function.iterate_zero_apply]
      have h1 : s (m + 1) z = (∑ n ∈ Finset.range m, v (n + 1) z) + g z := by
        simp only [hsdef]
        rw [Finset.sum_range_succ', hv0]
      have h2 : ∀ n, v (n + 1) z
          = μ z * cauchyTransform (fun ζ => dz (v n) ζ) z := by
        intro n
        rw [congrFun (hvsucc n) z,
          beurling_eq_cauchyTransform_dz (hvprop n).1 (hvprop n).2.1 z]
      rw [h1, Finset.sum_congr rfl (fun n _ => h2 n), ← Finset.mul_sum, hPadd m z]
    -- LHS: the partial sums converge to `φ z`.
    have hsummz : Summable (fun n => v n z) :=
      Summable.of_norm_bounded hsum_v (fun n => hKv n z)
    have hφz : Tendsto (fun m => s m z) atTop (𝓝 (φ z)) :=
      hsummz.hasSum.tendsto_sum_nat
    have hL : Tendsto (fun m => s (m + 1) z) atTop (𝓝 (φ z)) :=
      hφz.comp (tendsto_add_atTop_nat 1)
    -- RHS: `P (ds m) z → P u₁ z` by the uniform tail bound.
    have hu₁intz : Integrable (fun ζ => u₁ ζ / (ζ - z)) volume :=
      hPint u₁ hu₁cont hu₁cs z
    have hPdiff : ∀ m, cauchyTransform (fun ζ => ds m ζ) z - cauchyTransform u₁ z
        = cauchyTransform (fun ζ => ds m ζ - u₁ ζ) z := by
      intro m
      simp only [cauchyTransform]
      rw [← mul_sub]
      congr 1
      rw [← MeasureTheory.integral_sub
        (hPint _ (hds_cont m) (hcs_of_van _ (hds_van m)) z) hu₁intz]
      congr 1
      funext ζ
      rw [← sub_div]
    have htail : ∀ m ζ, ‖ds m ζ - u₁ ζ‖ ≤ Kdz * (1 - r')⁻¹ * r' ^ m := by
      intro m ζ
      have hsummdzζ : Summable (fun n => dz (v n) ζ) :=
        Summable.of_norm_bounded hsum_dz (fun n => hKdz n ζ)
      have hsplit : ds m ζ + ∑' i, dz (v (i + m)) ζ = u₁ ζ := by
        simp only [hdsdef, hu₁def]
        exact hsummdzζ.sum_add_tsum_nat_add m
      have heqm : ds m ζ - u₁ ζ = -(∑' i, dz (v (i + m)) ζ) := by
        rw [← hsplit]; ring
      rw [heqm, norm_neg]
      have hb : ∀ i, ‖dz (v (i + m)) ζ‖ ≤ Kdz * r' ^ m * r' ^ i := by
        intro i
        calc ‖dz (v (i + m)) ζ‖ ≤ Kdz * r' ^ (i + m) := hKdz (i + m) ζ
          _ = Kdz * r' ^ m * r' ^ i := by rw [pow_add]; ring
      have hsum_geom : Summable (fun i : ℕ => Kdz * r' ^ m * r' ^ i) :=
        hgeom.mul_left _
      have hsumnorm : Summable (fun i => ‖dz (v (i + m)) ζ‖) :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb hsum_geom
      calc ‖∑' i, dz (v (i + m)) ζ‖
          ≤ ∑' i, ‖dz (v (i + m)) ζ‖ := norm_tsum_le_tsum_norm hsumnorm
        _ ≤ ∑' i, Kdz * r' ^ m * r' ^ i := Summable.tsum_le_tsum hb hsumnorm hsum_geom
        _ = Kdz * r' ^ m * (1 - r')⁻¹ := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one hr'0.le hr'1]
        _ = Kdz * (1 - r')⁻¹ * r' ^ m := by ring
    have hPtail : ∀ m, ‖cauchyTransform (fun ζ => ds m ζ - u₁ ζ) z‖
        ≤ CR * (Kdz * (1 - r')⁻¹ * r' ^ m * Vp) := by
      intro m
      have hcontm : Continuous (fun ζ => ds m ζ - u₁ ζ) := (hds_cont m).sub hu₁cont
      have hvanm : ∀ ζ, R < ‖ζ‖ → ds m ζ - u₁ ζ = 0 := by
        intro ζ hζ; rw [hds_van m ζ hζ, hu₁van ζ hζ, sub_zero]
      have ht0 : 0 ≤ Kdz * (1 - r')⁻¹ * r' ^ m :=
        mul_nonneg (mul_nonneg hKdz0 (inv_nonneg.mpr (by linarith))) (hr'pow m)
      have h1 := hCR _ (hmem _ hcontm (hcs_of_van _ hvanm)) hvanm z
      refine le_trans h1 ?_
      exact mul_le_mul_of_nonneg_left
        (help _ _ ht0 (fun ζ => htail m ζ) hvanm) hCR0
    have hto0 : Tendsto (fun m => CR * (Kdz * (1 - r')⁻¹ * r' ^ m * Vp)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => r' ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr'0.le hr'1
      have h2 : (fun m => CR * (Kdz * (1 - r')⁻¹ * r' ^ m * Vp))
          = fun m => (CR * (Kdz * (1 - r')⁻¹) * Vp) * r' ^ m := by
        funext m; ring
      rw [h2]
      simpa using h1.const_mul (CR * (Kdz * (1 - r')⁻¹) * Vp)
    have hPconv : Tendsto (fun m => cauchyTransform (fun ζ => ds m ζ) z) atTop
        (𝓝 (cauchyTransform u₁ z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hto0
      rw [hPdiff m]
      exact hPtail m
    have hR : Tendsto (fun m => μ z * cauchyTransform (fun ζ => ds m ζ) z + g z)
        atTop (𝓝 (μ z * cauchyTransform u₁ z + g z)) :=
      (hPconv.const_mul (μ z)).add_const (g z)
    have hL' : Tendsto (fun m => s (m + 1) z) atTop
        (𝓝 (μ z * cauchyTransform u₁ z + g z)) := by
      have hfe : (fun m => s (m + 1) z)
          = fun m => μ z * cauchyTransform (fun ζ => ds m ζ) z + g z := funext hids
      rw [hfe]; exact hR
    have hkey : φ z = μ z * cauchyTransform u₁ z + g z := tendsto_nhds_unique hL hL'
    rw [hkey, hbeurφ' z]
  -- ===== Assemble the witness. =====
  exact ⟨φ, hφmem, hφvan, hφcont, hSφcont, heqn⟩

/-! ## The smooth principal solution -/

/-- **The smooth-case principal solution is a nondegenerate `C¹` map** (AIM
Theorem 5.2.3). For a Beltrami coefficient with smooth compactly supported `μ`
there is a principal solution `f` of class `C¹` whose Jacobian is positive at
**every** point and whose `∂`-derivative never vanishes. Exponential
representation: solve the auxiliary equation `ω = μ·Sω + ∂μ` (the fixed point
of `exists_continuous_fixedPoint_beltrami_of_contDiff` with datum `∂μ`), set
`σ = P ω` and `F = id + P(μ·e^σ)`; the identity `e^σ − 1 = S(μ·e^σ)` gives
`∂F = e^σ ≠ 0`, `∂̄F = μ·e^σ`, hence `J(z, F) = |e^σ|²·(1 − |μ|²) > 0`, and
`F` is itself a principal solution with field `h = μ·e^σ`. -/
theorem exists_contDiffOne_principalSolution (b : BeltramiCoeff)
    (hμs : ContDiff ℝ ∞ b.μ) (hμc : HasCompactSupport b.μ) :
    ∃ f : ℂ → ℂ, IsPrincipalSolution b f ∧ ContDiff ℝ 1 f ∧
      (∀ z : ℂ, 0 < (fderiv ℝ f z).det) ∧ ∀ z : ℂ, dz f z ≠ 0 := by
  classical
  -- ===== Constants and the pointwise coefficient bound. =====
  set k : ℝ := (eLpNormEssSup b.μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkfin : eLpNormEssSup b.μ volume ≠ ⊤ := (b.bound.trans_le le_top).ne
  have hk1 : k < 1 := by
    rw [hkdef, show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hkfin ENNReal.one_ne_top).2 b.bound
  have hμ_ae : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ ≤ k := by
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ₑ ≤ eLpNormEssSup b.μ volume :=
      ae_le_eLpNormEssSup
    filter_upwards [h1] with z hz
    rw [← ofReal_norm_eq_enorm] at hz
    have h3 := ENNReal.toReal_mono hkfin hz
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h3
  have hμpt : ∀ z, ‖b.μ z‖ ≤ k := by
    by_contra hcon
    obtain ⟨z₀, hz₀⟩ := not_forall.mp hcon
    rw [not_le] at hz₀
    have hopen : IsOpen {z : ℂ | k < ‖b.μ z‖} :=
      isOpen_lt continuous_const hμs.continuous.norm
    have hnull : volume {z : ℂ | k < ‖b.μ z‖} = 0 := by
      have h2 := hμ_ae
      rw [MeasureTheory.ae_iff] at h2
      have hset : {z : ℂ | ¬ ‖b.μ z‖ ≤ k} = {z : ℂ | k < ‖b.μ z‖} := by
        ext z; simp [not_le]
      rwa [hset] at h2
    exact absurd hnull (hopen.measure_pos volume ⟨z₀, hz₀⟩).ne'
  -- ===== A support radius. =====
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport b.μ ⊆ Metric.closedBall 0 R :=
    (hμc.isCompact.isBounded).subset_closedBall 0
  have hμvan : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hmem'
    have h2 := hR hmem'
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    exact absurd h2 (not_le.mpr hz)
  -- ===== Differentiability and Wirtinger toolkit. =====
  have hd1 : ∀ {u : ℂ → ℂ}, ContDiff ℝ ∞ u → Differentiable ℝ u := by
    intro u hu
    exact (hu.of_le (by exact_mod_cast le_top : ((1 : ℕ∞) : WithTop ℕ∞) ≤ _)).differentiable
      one_ne_zero
  have hdz_sm : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u →
      ContDiff ℝ ∞ (fun ζ => dz u ζ) := by
    intro u hu
    have hfderiv_cinf : ContDiff ℝ ∞ (fun ζ => fderiv ℝ u ζ) :=
      hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have hcomp : (fun ζ => dz u ζ)
        = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
          ∘ (fun ζ => fderiv ℝ u ζ) := by funext ζ; rfl
    have hΦ : ContDiff ℝ ∞
        (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I)) := by
      have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
          = (fun D : ℂ →L[ℝ] ℂ =>
              (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
                - Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
        funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
      rw [hΦ_lin]
      exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).sub
        ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
    rw [hcomp]; exact hΦ.comp hfderiv_cinf
  have hdz_cs : ∀ u : ℂ → ℂ, HasCompactSupport u →
      HasCompactSupport (fun ζ => dz u ζ) := by
    intro u huc
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ u ζ) := huc.fderiv (𝕜 := ℝ)
    have hcomp : (fun ζ => dz u ζ)
        = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 - I * D I)) ∘ (fun ζ => fderiv ℝ u ζ) := by
      funext ζ; rfl
    rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  have hvanish : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → ∀ z, R < ‖z‖ →
      dz u z = 0 := by
    intro u hu z hz
    have hopen : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
    have hev : u =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun w hw => hu w hw)
    have hfd : fderiv ℝ u z = 0 := by
      rw [hev.fderiv_eq]; exact fderiv_const_apply 0
    simp [dz, hfd]
  have hcs_of_van : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → HasCompactSupport u := by
    intro u huv
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) ?_
    intro x hx
    refine huv x ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx
  have hdict : ∀ (f : ℂ → ℂ) (z : ℂ), (fderiv ℝ f z) 1 = dz f z + dzbar f z ∧
      (fderiv ℝ f z) Complex.I = Complex.I * (dz f z - dzbar f z) := by
    intro f z
    constructor
    · rw [dz, dzbar]; ring
    · rw [dz, dzbar]
      linear_combination ((fderiv ℝ f z) Complex.I) * Complex.I_mul_I
  -- ===== The Weyl mollification lemma (continuous + vanishing weak `∂̄` ⇒ entire). =====
  have hweyl : ∀ (f gx gy : ℂ → ℂ), Continuous f →
      HasWeakDirDeriv 1 gx f Set.univ → HasWeakDirDeriv Complex.I gy f Set.univ →
      LocallyIntegrable gx → LocallyIntegrable gy →
      (∀ z, gx z + Complex.I * gy z = 0) →
      Differentiable ℂ f := by
    intro f gx gy hfcont hwgx hwgy hgxLI hgyLI hcombpt
    have hfloc : LocallyIntegrable f := hfcont.locallyIntegrable
    have hcomb : ∀ᵐ z ∂(volume : Measure ℂ), gx z + Complex.I * gy z = 0 :=
      Filter.Eventually.of_forall hcombpt
    set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
        rIn_pos := by positivity,
        rIn_lt_rOut := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hφbdef
    have hφrout : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [hφbdef] using h2
    set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρdef
    set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume with hfndef
    have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
      (φb n).contDiff_normed (n := ⊤)
    have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φb n).hasCompactSupport_normed
    have hρcont : ∀ n, Continuous (ρ n) := fun n => (hρsm n).continuous
    have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ)
        = MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
    have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I
        = MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
    have hexx : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gx
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
      (hρsupp n).convolutionExists_left _ (hρcont n) hgxLI
    have hexy : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gy
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
      (hρsupp n).convolutionExists_left _ (hρcont n) hgyLI
    have hfn_holo : ∀ n, DifferentiableOn ℂ (fn n) Set.univ := by
      intro n
      have hfn_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) :=
        (hρsupp n).contDiff_convolution_left _ (hρsm n) hfloc
      have hfn_diffR : ∀ z, DifferentiableAt ℝ (fn n) z := fun z =>
        (hfn_smooth.differentiable (by simp)).differentiableAt
      have hdzbar0 : ∀ z, dzbar (fn n) z = 0 := by
        intro z
        have hval : dzbar (fn n) z
            = (1 / 2 : ℂ) *
              (MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                + Complex.I * MeasureTheory.convolution (ρ n) gy
                  (ContinuousLinearMap.lsmul ℝ ℝ) volume z) := by
          rw [dzbar, hA1x n z, hA1y n z]
        have hzero : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
              volume z
            + Complex.I * MeasureTheory.convolution (ρ n) gy
              (ContinuousLinearMap.lsmul ℝ ℝ) volume z = 0 := by
          set Fx : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gx (z - t))
            with hFx
          set Fy : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gy (z - t))
            with hFy
          have hcx : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
              volume z = ∫ t, Fx t := rfl
          have hcy : MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
              volume z = ∫ t, Fy t := rfl
          rw [hcx, hcy]
          have hIint : Complex.I * ∫ t, Fy t = ∫ t, Complex.I * Fy t :=
            (MeasureTheory.integral_const_mul Complex.I Fy).symm
          rw [hIint]
          have hix : MeasureTheory.Integrable Fx volume := (hexx n z)
          have hiy : MeasureTheory.Integrable (fun t => Complex.I * Fy t) volume :=
            (hexy n z).const_mul Complex.I
          rw [← MeasureTheory.integral_add hix hiy]
          refine MeasureTheory.integral_eq_zero_of_ae ?_
          have hshift : ∀ᵐ t ∂(volume : Measure ℂ),
              gx (z - t) + Complex.I * gy (z - t) = 0 := by
            have hmp : MeasureTheory.MeasurePreserving (fun t : ℂ => z - t)
                (volume : Measure ℂ) volume :=
              (volume : Measure ℂ).measurePreserving_sub_left z
            exact hmp.quasiMeasurePreserving.ae hcomb
          filter_upwards [hshift] with t ht
          simp only [hFx, hFy, ContinuousLinearMap.lsmul_apply, Pi.zero_apply]
          rw [mul_smul_comm, ← smul_add, ht, smul_zero]
        rw [hval, hzero, mul_zero]
      refine (differentiableOn_iff_dzbar_eq_zero isOpen_univ ?_).mpr (fun z _ => hdzbar0 z)
      exact fun z _ => (hfn_diffR z).differentiableWithinAt
    have hTLU : TendstoLocallyUniformlyOn fn f atTop Set.univ := by
      rw [tendstoLocallyUniformlyOn_univ]
      refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
      refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
      have hUC : UniformContinuousOn f (Metric.closedBall x 2) :=
        (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hfcont.continuousOn
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hε2 : (0 : ℝ) < ε / 2 := by positivity
      obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
      have hev : ∀ᶠ n in atTop, (φb n).rOut < min δ 1 := by
        have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
        filter_upwards [this] with n hn using hn
      filter_upwards [hev] with n hn z hz
      have hrout_le_one : (φb n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
      have hrout_le_δ : (φb n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
      have hsupp2 : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φb n).rOut := by
        rw [hρdef, (φb n).support_normed_eq]
      have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φb n).nonneg_normed y
      have hintf : ∫ y, ρ n y ∂volume = 1 := (φb n).integral_normed
      have hclose : ∀ y ∈ Metric.ball z (φb n).rOut, dist (f y) (f z) ≤ ε / 2 := by
        intro y hy
        have hzmem : z ∈ Metric.closedBall x 2 :=
          Metric.closedBall_subset_closedBall (by norm_num) hz
        rw [Metric.mem_ball] at hy
        have hymem : y ∈ Metric.closedBall x 2 := by
          rw [Metric.mem_closedBall] at hz ⊢
          calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
            _ ≤ (φb n).rOut + 1 := by gcongr
            _ ≤ 1 + 1 := by gcongr
            _ = 2 := by norm_num
        exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
      calc dist (f z) (fn n z) = dist (fn n z) (f z) := dist_comm _ _
        _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp2 hnf hintf
              hfcont.aestronglyMeasurable hclose
        _ < ε := by linarith
    have hdiffOn : DifferentiableOn ℂ f Set.univ :=
      hTLU.differentiableOn (Filter.Eventually.of_forall hfn_holo) isOpen_univ
    rw [← differentiableOn_univ]
    exact hdiffOn
  -- ===== Contraction data and the σ-equation. =====
  obtain ⟨p, hp, hp', C, hCb, hcontr⟩ :=
    exists_p_gt_two_beurling_contraction b.measurable b.bound
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.le
  have hmem : ∀ (u : ℂ → ℂ), Continuous u → HasCompactSupport u → MemLp u p volume :=
    fun u hu huc => hu.memLp_of_hasCompactSupport huc
  have hsupp' : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0 ∧ dz b.μ z = 0 := fun z hz =>
    ⟨hμvan z hz, hvanish b.μ hμvan z hz⟩
  obtain ⟨ν, hνmem, hνvan, hνcont, hSνcont, hνeq⟩ :=
    exists_continuous_fixedPoint_beltrami_of_contDiff hp hp' hμs hμc
      (hdz_sm b.μ hμs) (hdz_cs b.μ hμc) hCb hcontr hsupp'
  have hνeq' : ∀ z, ν z = b.μ z * beurling ν z + dz b.μ z := fun z => hνeq z
  -- ===== `σ = P ν` is C¹ with `∂σ = Sν`, `∂̄σ = ν`. =====
  set σ : ℂ → ℂ := cauchyTransform ν with hσdef
  have hσcont : Continuous σ :=
    continuous_cauchyTransform_of_memLp_of_support hp hp' hνmem hνvan
  have hσgrad := hasWeakGradient_cauchyTransform hp hp' hνmem hνvan
  have hσpkg := contDiffOne_of_continuous_hasWeakGradient hσcont hσgrad
    (hSνcont.add hνcont) (continuous_const.mul (hSνcont.sub hνcont))
  have hσC1 : ContDiff ℝ 1 σ := hσpkg.1
  have hσdiff : ∀ z, DifferentiableAt ℝ σ z :=
    fun z => (hσC1.differentiable one_ne_zero).differentiableAt
  have hσdz : ∀ z, dz σ z = beurling ν z ∧ dzbar σ z = ν z := by
    intro z
    have h1 : (fderiv ℝ σ z) 1 = beurling ν z + ν z := (hσpkg.2 z).1
    have hI : (fderiv ℝ σ z) Complex.I = Complex.I * (beurling ν z - ν z) := (hσpkg.2 z).2
    constructor
    · rw [dz, h1, hI]
      linear_combination (-(1 / 2 : ℂ) * (beurling ν z - ν z)) * Complex.I_mul_I
    · rw [dzbar, h1, hI]
      linear_combination ((1 / 2 : ℂ) * (beurling ν z - ν z)) * Complex.I_mul_I
  -- ===== The exponential `e^σ` and its Wirtinger derivatives. =====
  have hexpσC1 : ContDiff ℝ 1 (fun z => Complex.exp (σ z)) :=
    Complex.contDiff_exp.comp hσC1
  have hEdz : ∀ z, dz (fun w => Complex.exp (σ w)) z = Complex.exp (σ z) * beurling ν z
      ∧ dzbar (fun w => Complex.exp (σ w)) z = Complex.exp (σ z) * ν z := by
    intro z
    have hgd : DifferentiableAt ℂ Complex.exp (σ z) := Complex.differentiable_exp _
    have hgd' : DifferentiableAt ℝ Complex.exp (σ z) :=
      (Complex.contDiff_exp.differentiable one_ne_zero) (σ z)
    have hdzexp : dz Complex.exp (σ z) = Complex.exp (σ z) := by
      rw [dz_eq_deriv_of_differentiableAt hgd, Complex.deriv_exp]
    have hdzbarexp : dzbar Complex.exp (σ z) = 0 := dzbar_eq_zero_of_differentiableAt hgd
    constructor
    · rw [dz_comp (hσdiff z) hgd', hdzexp, hdzbarexp, (hσdz z).1]; ring
    · rw [dzbar_comp (hσdiff z) hgd', hdzexp, hdzbarexp, (hσdz z).2]; ring
  -- ===== The field `h = μ·e^σ`. =====
  set h : ℂ → ℂ := fun z => b.μ z * Complex.exp (σ z) with hhdef
  have hhC1 : ContDiff ℝ 1 h := (hμs.of_le (by exact_mod_cast le_top)).mul hexpσC1
  have hhcont : Continuous h := hhC1.continuous
  have hhcs : HasCompactSupport h := hμc.mul_right
  have hhvan : ∀ z, R < ‖z‖ → h z = 0 := by
    intro z hz; simp only [hhdef, hμvan z hz, zero_mul]
  have hhmem : MemLp h p volume := hmem h hhcont hhcs
  have hdzh : ∀ z, dz h z = Complex.exp (σ z) * ν z := by
    intro z
    have hμd : DifferentiableAt ℝ b.μ z := hd1 hμs z
    have hEd : DifferentiableAt ℝ (fun w => Complex.exp (σ w)) z :=
      (hexpσC1.differentiable one_ne_zero).differentiableAt
    calc dz h z
        = b.μ z * dz (fun w => Complex.exp (σ w)) z
          + Complex.exp (σ z) * dz b.μ z := by
          rw [hhdef]; exact dz_mul hμd hEd
      _ = b.μ z * (Complex.exp (σ z) * beurling ν z)
          + Complex.exp (σ z) * dz b.μ z := by rw [(hEdz z).1]
      _ = Complex.exp (σ z) * (b.μ z * beurling ν z + dz b.μ z) := by ring
      _ = Complex.exp (σ z) * ν z := by rw [← hνeq' z]
  -- ===== `S h = P (∂h)` pointwise, and continuity of `S h`. =====
  have hbeurh : ∀ z, beurling h z = cauchyTransform (fun ζ => dz h ζ) z := by
    intro z
    rw [beurling, cauchyTransform]
    congr 1
    refine Filter.Tendsto.limUnder_eq ?_
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r h z
        = czOperator beurlingKernel r h z := fun r => rfl
    simpa only [hcz] using czOperator_beurling_tendsto_smooth hhC1 hhcs z
  have hdzhfun : (fun ζ => dz h ζ) = fun ζ => Complex.exp (σ ζ) * ν ζ := by
    funext ζ; exact hdzh ζ
  have hdzhcont : Continuous (fun ζ => dz h ζ) := by
    rw [hdzhfun]; exact (Complex.continuous_exp.comp hσcont).mul hνcont
  have hdzhvan : ∀ ζ, R < ‖ζ‖ → dz h ζ = 0 := fun ζ hζ => hvanish h hhvan ζ hζ
  have hdzhcs : HasCompactSupport (fun ζ => dz h ζ) := hcs_of_van _ hdzhvan
  have hdzhmem : MemLp (fun ζ => dz h ζ) p volume := hmem _ hdzhcont hdzhcs
  have hShcont : Continuous (beurling h) := by
    have hfun : beurling h = cauchyTransform (fun ζ => dz h ζ) := funext hbeurh
    rw [hfun]
    exact continuous_cauchyTransform_of_memLp_of_support hp hp' hdzhmem hdzhvan
  -- ===== `P h` is C¹ with `∂(P h) = S h`, `∂̄(P h) = h`. =====
  have hPhcont : Continuous (cauchyTransform h) :=
    continuous_cauchyTransform_of_memLp_of_support hp hp' hhmem hhvan
  have hPhgrad := hasWeakGradient_cauchyTransform hp hp' hhmem hhvan
  have hPhpkg := contDiffOne_of_continuous_hasWeakGradient hPhcont hPhgrad
    (hShcont.add hhcont) (continuous_const.mul (hShcont.sub hhcont))
  have hPhC1 : ContDiff ℝ 1 (cauchyTransform h) := hPhpkg.1
  have hPhdz : ∀ z, dz (cauchyTransform h) z = beurling h z
      ∧ dzbar (cauchyTransform h) z = h z := by
    intro z
    have h1 : (fderiv ℝ (cauchyTransform h) z) 1 = beurling h z + h z := (hPhpkg.2 z).1
    have hI : (fderiv ℝ (cauchyTransform h) z) Complex.I
        = Complex.I * (beurling h z - h z) := (hPhpkg.2 z).2
    constructor
    · rw [dz, h1, hI]
      linear_combination (-(1 / 2 : ℂ) * (beurling h z - h z)) * Complex.I_mul_I
    · rw [dzbar, h1, hI]
      linear_combination ((1 / 2 : ℂ) * (beurling h z - h z)) * Complex.I_mul_I
  -- ===== The comparison function `u = (e^σ − 1) − P(∂h)` is entire and vanishes. =====
  set A : ℂ → ℂ := fun z => Complex.exp (σ z) - 1 with hAdef
  have hAC1 : ContDiff ℝ 1 A := hexpσC1.sub contDiff_const
  set B : ℂ → ℂ := cauchyTransform (fun ζ => dz h ζ) with hBdef
  have hBgrad := hasWeakGradient_cauchyTransform hp hp' hdzhmem hdzhvan
  have hBcont : Continuous B :=
    continuous_cauchyTransform_of_memLp_of_support hp hp' hdzhmem hdzhvan
  set u : ℂ → ℂ := fun z => A z - B z with hudef
  have hucont : Continuous u := hAC1.continuous.sub hBcont
  have hwAx : HasWeakDirDeriv 1 (fun z => (fderiv ℝ A z) 1) A Set.univ :=
    HasWeakDirDeriv.of_contDiffOn isOpen_univ hAC1.contDiffOn
  have hwAy : HasWeakDirDeriv Complex.I (fun z => (fderiv ℝ A z) Complex.I) A Set.univ :=
    HasWeakDirDeriv.of_contDiffOn isOpen_univ hAC1.contDiffOn
  have hfdA_cont : Continuous (fun z => fderiv ℝ A z) := (contDiff_one_iff_fderiv.mp hAC1).2
  have hgAx_cont : Continuous (fun z => (fderiv ℝ A z) 1) :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdA_cont
  have hgAy_cont : Continuous (fun z => (fderiv ℝ A z) Complex.I) :=
    ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdA_cont
  have hSdzhmem : MemLp (beurling (fun ζ => dz h ζ)) p volume :=
    memLp_beurling_of_memLp hp hp' hdzhmem
  have hgxB_LI : LocallyIntegrable (fun z => beurling (fun ζ => dz h ζ) z + dz h z) :=
    (hSdzhmem.add hdzhmem).locallyIntegrable hp1
  have hgyB_LI : LocallyIntegrable
      (fun z => Complex.I * (beurling (fun ζ => dz h ζ) z - dz h z)) :=
    ((hSdzhmem.sub hdzhmem).const_mul Complex.I).locallyIntegrable hp1
  have hwux : HasWeakDirDeriv 1
      (fun z => (fderiv ℝ A z) 1 - (beurling (fun ζ => dz h ζ) z + dz h z)) u Set.univ :=
    HasWeakDirDeriv.sub hwAx hBgrad.1
      (locallyIntegrableOn_univ.mpr hAC1.continuous.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hBcont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgAx_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgxB_LI)
  have hwuy : HasWeakDirDeriv Complex.I
      (fun z => (fderiv ℝ A z) Complex.I
        - Complex.I * (beurling (fun ζ => dz h ζ) z - dz h z)) u Set.univ :=
    HasWeakDirDeriv.sub hwAy hBgrad.2
      (locallyIntegrableOn_univ.mpr hAC1.continuous.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hBcont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgAy_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgyB_LI)
  have hdzbarA : ∀ z, dzbar A z = Complex.exp (σ z) * ν z := by
    intro z
    have hfdA : fderiv ℝ A z = fderiv ℝ (fun w => Complex.exp (σ w)) z := by
      rw [hAdef]; exact fderiv_sub_const 1
    have h2 := (hEdz z).2
    rw [dzbar] at h2 ⊢
    rw [hfdA]
    exact h2
  have hcombpt : ∀ z,
      ((fderiv ℝ A z) 1 - (beurling (fun ζ => dz h ζ) z + dz h z))
        + Complex.I * ((fderiv ℝ A z) Complex.I
          - Complex.I * (beurling (fun ζ => dz h ζ) z - dz h z)) = 0 := by
    intro z
    rw [(hdict A z).1, (hdict A z).2, hdzbarA z, hdzh z]
    linear_combination (dz A z - beurling (fun ζ => dz h ζ) z) * Complex.I_mul_I
  have hu_ent : Differentiable ℂ u :=
    hweyl u _ _ hucont hwux hwuy
      (hgAx_cont.locallyIntegrable.sub hgxB_LI)
      (hgAy_cont.locallyIntegrable.sub hgyB_LI)
      hcombpt
  -- ===== `u → 0` cocompactly, hence `u ≡ 0` by Liouville. =====
  have hσ0 : Tendsto σ (Filter.cocompact ℂ) (𝓝 0) :=
    cauchyTransform_tendsto_cocompact hp hp' hνmem hνvan
  have hA0 : Tendsto A (Filter.cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun z => Complex.exp (σ z)) (Filter.cocompact ℂ) (𝓝 1) := by
      have h2 := (Complex.continuous_exp.tendsto 0).comp hσ0
      simpa using h2
    have h2 := h1.sub_const 1
    simpa [hAdef] using h2
  have hB0 : Tendsto B (Filter.cocompact ℂ) (𝓝 0) :=
    cauchyTransform_tendsto_cocompact hp hp' hdzhmem hdzhvan
  have hu0 : Tendsto u (Filter.cocompact ℂ) (𝓝 0) := by
    have h2 := hA0.sub hB0
    simpa [hudef] using h2
  have hubdd : Bornology.IsBounded (Set.range u) := by
    have h1 : ∀ᶠ z in Filter.cocompact ℂ, u z ∈ Metric.closedBall (0 : ℂ) 1 :=
      hu0 (Metric.closedBall_mem_nhds 0 one_pos)
    rw [Filter.eventually_iff, Filter.mem_cocompact] at h1
    obtain ⟨K, hKc, hKsub⟩ := h1
    have h2 : Set.range u ⊆ (u '' K) ∪ Metric.closedBall (0 : ℂ) 1 := by
      rintro _ ⟨z, rfl⟩
      by_cases hz : z ∈ K
      · exact Or.inl ⟨z, hz, rfl⟩
      · exact Or.inr (hKsub hz)
    exact (((hKc.image hucont).isBounded).union Metric.isBounded_closedBall).subset h2
  have hu_zero : ∀ z, u z = 0 := by
    intro z
    have hconst : ∀ w, u w = u z := fun w => hu_ent.apply_eq_apply_of_bounded hubdd w z
    have hc' : Tendsto u (Filter.cocompact ℂ) (𝓝 (u z)) := by
      have hfe : u = fun _ => u z := funext hconst
      rw [hfe]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hc' hu0
  -- ===== The key identity `e^σ = 1 + S h`. =====
  have hkey : ∀ z, Complex.exp (σ z) = 1 + beurling h z := by
    intro z
    have h0 : A z - B z = 0 := hu_zero z
    have h1 : Complex.exp (σ z) - 1 - cauchyTransform (fun ζ => dz h ζ) z = 0 := by
      simpa [hAdef, hBdef, sub_sub] using h0
    rw [hbeurh z]
    linear_combination h1
  -- ===== Assemble the principal solution `F = id + P h`. =====
  have hidd : ∀ z : ℂ, DifferentiableAt ℝ (fun w : ℂ => w) z :=
    fun z => differentiable_id.differentiableAt
  have hPd : ∀ z, DifferentiableAt ℝ (cauchyTransform h) z :=
    fun z => (hPhC1.differentiable one_ne_zero).differentiableAt
  have hdzid : ∀ z : ℂ, dz (fun w : ℂ => w) z = 1 ∧ dzbar (fun w : ℂ => w) z = 0 := by
    intro z
    have hfd : fderiv ℝ (fun w : ℂ => w) z = ContinuousLinearMap.id ℝ ℂ := fderiv_id'
    constructor
    · rw [dz, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination (-(1 / 2 : ℂ)) * Complex.I_mul_I
    · rw [dzbar, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination ((1 / 2 : ℂ)) * Complex.I_mul_I
  have hFdz : ∀ z, dz (fun w => w + cauchyTransform h w) z = Complex.exp (σ z)
      ∧ dzbar (fun w => w + cauchyTransform h w) z = h z := by
    intro z
    constructor
    · rw [dz_add (hidd z) (hPd z), (hdzid z).1, (hPhdz z).1, hkey z]
    · rw [dzbar_add (hidd z) (hPd z), (hdzid z).2, (hPhdz z).2, zero_add]
  refine ⟨fun w => w + cauchyTransform h w, ?_, ?_, ?_, ?_⟩
  · -- IsPrincipalSolution
    refine ⟨p, h, R, hp, hp', hhmem, hhvan, ?_, fun z => rfl⟩
    refine Filter.Eventually.of_forall (fun z => ?_)
    have h1 : h z = b.μ z * Complex.exp (σ z) := by rw [hhdef]
    rw [h1, hkey z]
    ring
  · -- C¹
    exact contDiff_id.add hPhC1
  · -- positive Jacobian
    intro z
    rw [det_fderiv_eq_wirtinger, (hFdz z).1, (hFdz z).2]
    have h1 : ‖h z‖ = ‖b.μ z‖ * ‖Complex.exp (σ z)‖ := by
      rw [hhdef]; exact norm_mul _ _
    have h2 : 0 < ‖Complex.exp (σ z)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
    have h3 : ‖b.μ z‖ ≤ k := hμpt z
    have h4 : 0 ≤ ‖b.μ z‖ := norm_nonneg _
    rw [h1]
    have h5 : ‖b.μ z‖ * ‖b.μ z‖ ≤ k * k := mul_le_mul h3 h3 h4 hk0
    have h6 : k * k < 1 := by nlinarith
    have h7 : ‖b.μ z‖ * ‖b.μ z‖ < 1 := lt_of_le_of_lt h5 h6
    have h8 : 0 < ‖Complex.exp (σ z)‖ * ‖Complex.exp (σ z)‖ := mul_pos h2 h2
    nlinarith [mul_pos h8 (sub_pos.mpr h7)]
  · -- nonvanishing ∂F
    intro z
    rw [(hFdz z).1]
    exact Complex.exp_ne_zero _

/-- **A nondegenerate `C¹` principal solution is a homeomorphism of the plane**
(AIM Theorem 5.2.4). Everywhere-positive Jacobian makes `f` a local
homeomorphism (inverse function theorem); the principal normalization makes it
proper (`f − id → 0` at infinity) and holomorphic and injective near infinity
(off the support ball of its field, `f = id + P h` is holomorphic with Laurent
expansion `z + O(1/z)`); the fiber-count function of a proper local
homeomorphism of the plane is locally constant, and it equals `1` near
infinity, so `f` is a global homeomorphism. -/
theorem isHomeomorph_of_contDiffOne_principalSolution {b : BeltramiCoeff}
    {f : ℂ → ℂ} (hf : IsPrincipalSolution b f) (hf1 : ContDiff ℝ 1 f)
    (hdet : ∀ z : ℂ, 0 < (fderiv ℝ f z).det) :
    IsHomeomorph f := by
  classical
  have hcont : Continuous f := hf1.continuous
  have hdecay : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0) :=
    hf.tendsto_sub_id_cocompact
  -- ===== 1. `f` is a local homeomorphism (inverse function theorem). =====
  have hlocal : IsLocalHomeomorph f := by
    intro z
    have hsd : HasStrictFDerivAt f (fderiv ℝ f z) z :=
      hf1.contDiffAt.hasStrictFDerivAt one_ne_zero
    have hAdet : LinearMap.det ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ≠ 0 :=
      (hdet z).ne'
    set eqv : ℂ ≃L[ℝ] ℂ :=
      (LinearMap.equivOfDetNeZero ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
        hAdet).toContinuousLinearEquiv with heqv
    have hcoe : (eqv : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := by
      ext w
      simp [heqv]
    have hsd' : HasStrictFDerivAt f ((eqv : ℂ →L[ℝ] ℂ)) z := by
      rw [hcoe]; exact hsd
    exact ⟨hsd'.toOpenPartialHomeomorph f, hsd'.mem_toOpenPartialHomeomorph_source,
      (hsd'.toOpenPartialHomeomorph_coe).symm⟩
  have hopen : IsOpenMap f := hlocal.isOpenMap
  have hstack : ∀ z : ℂ, ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ Set.InjOn f W := by
    intro z
    obtain ⟨e, hz, hfe⟩ := hlocal z
    refine ⟨e.source, e.open_source, hz, ?_⟩
    rw [hfe]
    exact e.injOn
  -- ===== 2. `f` is proper, hence a closed map. =====
  have hnormf : Tendsto (fun z : ℂ => ‖f z‖) (cocompact ℂ) atTop := by
    have h1 : Tendsto (fun z : ℂ => ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
      simpa using hdecay.norm
    have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖f z - z‖ < 1 :=
      h1.eventually_lt_const one_pos
    have hz1 : Tendsto (fun z : ℂ => ‖z‖ - 1) (cocompact ℂ) atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right (cocompact ℂ) (-1 : ℝ) tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono' (cocompact ℂ) ?_ hz1
    filter_upwards [hev] with z hz
    have h2 : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ := by
      simpa [sub_sub_cancel] using norm_sub_le (f z) (f z - z)
    linarith
  have hcoc : Tendsto f (cocompact ℂ) (cocompact ℂ) := by
    rw [Filter.hasBasis_cocompact.tendsto_right_iff]
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    filter_upwards [hnormf.eventually (eventually_gt_atTop r)] with z hz
    exact fun hmem => absurd (mem_closedBall_zero_iff.mp (hr hmem)) (not_le.mpr hz)
  have hproper : IsProperMap f := isProperMap_iff_tendsto_cocompact.mpr ⟨hcont, hcoc⟩
  have hclosedmap : IsClosedMap f := hproper.isClosedMap
  -- ===== 3. `f` is surjective (open + closed range in the connected plane). =====
  have hrange_closed : IsClosed (Set.range f) := by
    have h1 := hclosedmap Set.univ isClosed_univ
    rwa [Set.image_univ] at h1
  have hsurj : Function.Surjective f := by
    rw [← Set.range_eq_univ]
    exact IsClopen.eq_univ ⟨hrange_closed, hopen.isOpen_range⟩ ⟨f 0, 0, rfl⟩
  -- ===== 4. far-region holomorphy and injectivity. =====
  obtain ⟨p, h, R, hp, hp', hmem, hsupp_h, _heq, hrepr⟩ := hf
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.le
  have hgfun : (fun z => f z - z) = cauchyTransform h := by
    funext z; rw [hrepr z]; ring
  have hgC1 : ContDiff ℝ 1 (fun z => f z - z) := hf1.sub contDiff_id
  have hPhC1 : ContDiff ℝ 1 (cauchyTransform h) := by rw [← hgfun]; exact hgC1
  -- a.e. identification of `∂̄f` with the field `h` by weak-derivative uniqueness.
  have hwg := hasWeakGradient_cauchyTransform hp hp' hmem hsupp_h
  have hfdPh_cont : Continuous (fun z => fderiv ℝ (cauchyTransform h) z) :=
    (contDiff_one_iff_fderiv.mp hPhC1).2
  have hclx_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h) z) 1) :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdPh_cont
  have hcly_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h) z) Complex.I) :=
    ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdPh_cont
  have hSh_mem : MemLp (beurling h) p volume := memLp_beurling_of_memLp hp hp' hmem
  have haex := HasWeakDirDeriv.ae_eq isOpen_univ
    (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPhC1.contDiffOn) hwg.1
    (locallyIntegrableOn_univ.mpr hclx_cont.locallyIntegrable)
    (locallyIntegrableOn_univ.mpr ((hSh_mem.add hmem).locallyIntegrable hp1))
  have haey := HasWeakDirDeriv.ae_eq isOpen_univ
    (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPhC1.contDiffOn) hwg.2
    (locallyIntegrableOn_univ.mpr hcly_cont.locallyIntegrable)
    (locallyIntegrableOn_univ.mpr
      (((hSh_mem.sub hmem).const_mul Complex.I).locallyIntegrable hp1))
  have hff : f = fun w => w + cauchyTransform h w := funext hrepr
  have haedzbar : ∀ᵐ z ∂(volume : Measure ℂ), dzbar f z = h z := by
    filter_upwards [haex, haey] with z hx hy
    have hx' : (fderiv ℝ (cauchyTransform h) z) 1 = beurling h z + h z :=
      hx (Set.mem_univ z)
    have hy' : (fderiv ℝ (cauchyTransform h) z) Complex.I
        = Complex.I * (beurling h z - h z) := hy (Set.mem_univ z)
    have hidd : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiable_id.differentiableAt
    have hPd : DifferentiableAt ℝ (cauchyTransform h) z :=
      (hPhC1.differentiable one_ne_zero).differentiableAt
    have hdzbarid : dzbar (fun w : ℂ => w) z = 0 := by
      rw [dzbar, fderiv_id']
      simp only [ContinuousLinearMap.id_apply]
      linear_combination ((1 / 2 : ℂ)) * Complex.I_mul_I
    rw [hff, dzbar_add hidd hPd, hdzbarid, zero_add, dzbar, hx', hy']
    linear_combination ((1 / 2 : ℂ) * (beurling h z - h z)) * Complex.I_mul_I
  -- `∂̄f` is continuous and vanishes pointwise on the far region.
  have hdzbarf_cont : Continuous (fun z => dzbar f z) := by
    have h1 : Continuous (fun z => fderiv ℝ f z) := (contDiff_one_iff_fderiv.mp hf1).2
    have h2 : Continuous (fun z => (fderiv ℝ f z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp h1
    have h3 : Continuous (fun z => (fderiv ℝ f z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp h1
    have h4 : (fun z => dzbar f z)
        = fun z => (1 / 2 : ℂ)
            * ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I) := by
      funext z; rw [dzbar]
    rw [h4]
    exact continuous_const.mul (h2.add (continuous_const.mul h3))
  have hUfar_open : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hdzbarf_far : ∀ z, R < ‖z‖ → dzbar f z = 0 := by
    intro z hz
    by_contra hne
    have hopen2 : IsOpen ({w : ℂ | R < ‖w‖} ∩ {w | dzbar f w ≠ 0}) :=
      hUfar_open.inter (isOpen_ne_fun hdzbarf_cont continuous_const)
    have hnull : volume ({w : ℂ | R < ‖w‖} ∩ {w | dzbar f w ≠ 0}) = 0 := by
      have h5 : ({w : ℂ | R < ‖w‖} ∩ {w | dzbar f w ≠ 0})
          ⊆ {w | ¬ dzbar f w = h w} := by
        rintro w ⟨hw1, hw2⟩ hcontra
        exact hw2 (by rw [hcontra, hsupp_h w hw1])
      exact measure_mono_null h5 (MeasureTheory.ae_iff.mp haedzbar)
    exact absurd hnull (hopen2.measure_pos volume ⟨z, hz, hne⟩).ne'
  have hholo_far : DifferentiableOn ℂ f {w : ℂ | R < ‖w‖} := by
    refine (differentiableOn_iff_dzbar_eq_zero hUfar_open ?_).mpr
      (fun z hz => hdzbarf_far z hz)
    exact fun z _ => ((hf1.differentiable one_ne_zero) z).differentiableWithinAt
  have hgholo : DifferentiableOn ℂ (fun z => f z - z) {w : ℂ | R < ‖w‖} :=
    hholo_far.sub differentiable_id.differentiableOn
  -- Far smallness of the displacement.
  have hev4 : ∀ᶠ z : ℂ in cocompact ℂ, ‖f z - z‖ ≤ 1 / 4 := by
    have h1 : Tendsto (fun z : ℂ => ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
      simpa using hdecay.norm
    exact h1.eventually (eventually_le_nhds (by norm_num))
  rw [Filter.eventually_iff, Filter.mem_cocompact] at hev4
  obtain ⟨K, hKc, hKsub⟩ := hev4
  obtain ⟨r, hr⟩ := hKc.isBounded.subset_closedBall 0
  set R₁ : ℝ := max r (R + 1) + 1 with hR₁def
  have hR₁r : r < R₁ := by
    have := le_max_left r (R + 1); rw [hR₁def]; linarith
  have hR₁R : R + 1 < R₁ := by
    have := le_max_right r (R + 1); rw [hR₁def]; linarith
  have hgsm : ∀ z : ℂ, R₁ ≤ ‖z‖ → ‖f z - z‖ ≤ 1 / 4 := by
    intro z hz
    refine hKsub ?_
    intro hzK
    have h6 := hr hzK
    rw [Metric.mem_closedBall, dist_zero_right] at h6
    linarith
  -- Cauchy estimate for the derivative of the displacement on the far region.
  have hderiv_bd : ∀ x : ℂ, R₁ + 1 < ‖x‖ → ‖deriv (fun z => f z - z) x‖ ≤ 1 / 4 := by
    intro x hx
    have hsub1 : Metric.closedBall x 1 ⊆ {w : ℂ | R < ‖w‖} := by
      intro w hw
      rw [Metric.mem_closedBall] at hw
      have h7 : ‖x‖ - ‖w‖ ≤ 1 := by
        calc ‖x‖ - ‖w‖ ≤ ‖x - w‖ := norm_sub_norm_le x w
          _ = dist w x := by rw [dist_comm, dist_eq_norm]
          _ ≤ 1 := hw
      simp only [Set.mem_setOf_eq]
      linarith
    have hdiff : DifferentiableOn ℂ (fun z => f z - z) (closure (Metric.ball x 1)) := by
      rw [closure_ball x one_ne_zero]
      exact hgholo.mono hsub1
    have hdc : DiffContOnCl ℂ (fun z => f z - z) (Metric.ball x 1) :=
      hdiff.diffContOnCl
    have hsp : ∀ w ∈ Metric.sphere x 1, ‖f w - w‖ ≤ 1 / 4 := by
      intro w hw
      rw [Metric.mem_sphere] at hw
      refine hgsm w ?_
      have h8 : ‖x‖ - ‖w‖ ≤ 1 := by
        calc ‖x‖ - ‖w‖ ≤ ‖x - w‖ := norm_sub_norm_le x w
          _ = dist w x := by rw [dist_comm, dist_eq_norm]
          _ = 1 := hw
      linarith
    have h9 := norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hdc hsp
    simpa using h9
  -- Far injectivity.
  have hfar_inj : ∀ z₁ z₂ : ℂ, R₁ + 2 < ‖z₁‖ → R₁ + 2 < ‖z₂‖ → f z₁ = f z₂ → z₁ = z₂ := by
    intro z₁ z₂ h₁ h₂ hf12
    have hnormdiff : z₁ - z₂ = (f z₂ - z₂) - (f z₁ - z₁) := by rw [hf12]; ring
    have hsmall12 : ‖z₁ - z₂‖ ≤ 1 / 2 := by
      rw [hnormdiff]
      calc ‖(f z₂ - z₂) - (f z₁ - z₁)‖
          ≤ ‖f z₂ - z₂‖ + ‖f z₁ - z₁‖ := norm_sub_le _ _
        _ ≤ 1 / 4 + 1 / 4 :=
            add_le_add (hgsm z₂ (by linarith)) (hgsm z₁ (by linarith))
        _ = 1 / 2 := by norm_num
    have hballfar : ∀ x ∈ Metric.closedBall z₁ (1 : ℝ), R₁ + 1 < ‖x‖ := by
      intro x hx
      rw [Metric.mem_closedBall] at hx
      have h8 : ‖z₁‖ - ‖x‖ ≤ 1 := by
        calc ‖z₁‖ - ‖x‖ ≤ ‖z₁ - x‖ := norm_sub_norm_le z₁ x
          _ = dist x z₁ := by rw [dist_comm, dist_eq_norm]
          _ ≤ 1 := hx
      linarith
    have hreprL : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ),
        L w = (1 / 2 : ℂ) * ((L 1) - I * (L I)) * w
          + (1 / 2 : ℂ) * ((L 1) + I * (L I)) * (starRingEnd ℂ) w := by
      intro L w
      have hLw : L w = (↑w.re : ℂ) * L 1 + (↑w.im : ℂ) * L I := by
        conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • I by
          rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
        rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * I := by
        conv_lhs => rw [← Complex.re_add_im w]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hw : w = (↑w.re : ℂ) + ↑w.im * I := (Complex.re_add_im w).symm
      rw [hLw, hcw]
      set a : ℂ := (↑w.re : ℂ) with ha
      set bb : ℂ := (↑w.im : ℂ) with hbb
      rw [hw]
      linear_combination (bb * L I) * Complex.I_mul_I
    have hdzbarg : ∀ x, R < ‖x‖ → dzbar (fun z => f z - z) x = 0 := by
      intro x hx
      have hd1' : DifferentiableAt ℝ f x := (hf1.differentiable one_ne_zero) x
      have hd2' : DifferentiableAt ℝ (fun w : ℂ => w) x := differentiable_id.differentiableAt
      have hfdsub : fderiv ℝ (fun z : ℂ => f z - z) x
          = fderiv ℝ f x - fderiv ℝ (fun w : ℂ => w) x := fderiv_fun_sub hd1' hd2'
      have h0 := hdzbarf_far x hx
      rw [dzbar] at h0
      rw [dzbar, hfdsub, fderiv_id']
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      linear_combination h0 + (-(1 / 2 : ℂ)) * Complex.I_mul_I
    have hderivsW : ∀ x ∈ Metric.closedBall z₁ (1 : ℝ),
        HasFDerivWithinAt (fun z => f z - z) (fderiv ℝ (fun z => f z - z) x)
          (Metric.closedBall z₁ 1) x := fun x _ =>
      ((hgC1.differentiable one_ne_zero x).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ x ∈ Metric.closedBall z₁ (1 : ℝ),
        ‖fderiv ℝ (fun z => f z - z) x‖ ≤ 1 / 4 := by
      intro x hx
      have hxfar := hballfar x hx
      have hxR : R < ‖x‖ := by linarith [hR₁R]
      have hxU : {w : ℂ | R < ‖w‖} ∈ 𝓝 x := hUfar_open.mem_nhds hxR
      have hdC : DifferentiableAt ℂ (fun z => f z - z) x := hgholo.differentiableAt hxU
      have hdzg' := dz_eq_deriv_of_differentiableAt hdC
      rw [dz] at hdzg'
      have hdzbarg0' := hdzbarg x hxR
      rw [dzbar] at hdzbarg0'
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => ?_)
      have hval := hreprL (fderiv ℝ (fun z => f z - z) x) v
      rw [hdzg', hdzbarg0', zero_mul, add_zero] at hval
      rw [hval, norm_mul]
      exact mul_le_mul_of_nonneg_right (hderiv_bd x hxfar) (norm_nonneg v)
    have hz₂mem : z₂ ∈ Metric.closedBall z₁ (1 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖z₂ - z₁‖ = ‖z₁ - z₂‖ := norm_sub_rev _ _
        _ ≤ 1 / 2 := hsmall12
        _ ≤ 1 := by norm_num
    have hz₁mem : z₁ ∈ Metric.closedBall z₁ (1 : ℝ) :=
      Metric.mem_closedBall_self one_pos.le
    have hMVT := (convex_closedBall z₁ (1 : ℝ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hderivsW hbound hz₁mem hz₂mem
    have h9 : ‖z₁ - z₂‖ ≤ 1 / 4 * ‖z₁ - z₂‖ := by
      calc ‖z₁ - z₂‖ = ‖(f z₂ - z₂) - (f z₁ - z₁)‖ := by rw [hnormdiff]
        _ ≤ 1 / 4 * ‖z₂ - z₁‖ := hMVT
        _ = 1 / 4 * ‖z₁ - z₂‖ := by rw [norm_sub_rev]
    have h10 : ‖z₁ - z₂‖ = 0 := by nlinarith [norm_nonneg (z₁ - z₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h10)
  -- A global displacement bound and a very far target point.
  obtain ⟨Mg, hMg0, hMg⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖f z - z‖ ≤ M := by
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R₁).exists_bound_of_continuousOn
      (hgC1.continuous.continuousOn)
    refine ⟨max M₀ (1 / 4), le_trans (by norm_num) (le_max_right _ _), fun z => ?_⟩
    by_cases hz : R₁ ≤ ‖z‖
    · exact le_trans (hgsm z hz) (le_max_right _ _)
    · refine le_trans (hM₀ z ?_) (le_max_left _ _)
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
  set w₀ : ℂ := ((|R₁| + Mg + 4 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = |R₁| + Mg + 4 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [abs_nonneg R₁] : (0 : ℝ) ≤ |R₁| + Mg + 4)]
  have hfarfiber : ∀ z, f z = w₀ → R₁ + 2 < ‖z‖ := by
    intro z hz
    have h2 : ‖w₀‖ ≤ ‖z‖ + ‖f z - z‖ := by
      rw [← hz]
      calc ‖f z‖ = ‖z + (f z - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖f z - z‖ := norm_add_le _ _
    have h3 := hMg z
    rw [hw₀norm] at h2
    have habs : R₁ ≤ |R₁| := le_abs_self R₁
    linarith
  -- ===== 5. the set of subsingleton fibers is clopen, hence everything. =====
  set Good : Set ℂ := {w | Set.Subsingleton (f ⁻¹' {w})} with hGooddef
  have hGood_open : IsOpen Good := by
    rw [isOpen_iff_forall_mem_open]
    intro w₁ hw₁
    have hw₁' : (f ⁻¹' {w₁}).Subsingleton := hw₁
    obtain ⟨z₀, hz₀⟩ := hsurj w₁
    have hfib : ∀ c, f c = w₁ → c = z₀ := fun c hc =>
      hw₁' (show c ∈ f ⁻¹' {w₁} from hc) (show z₀ ∈ f ⁻¹' {w₁} from hz₀)
    obtain ⟨W, hWopen, hz₀W, hWinj⟩ := hstack z₀
    refine ⟨(f '' W) ∩ (f '' Wᶜ)ᶜ, ?_, ?_, ?_⟩
    · rintro w ⟨hw1, hw2⟩
      have hfibW : ∀ c, f c = w → c ∈ W := by
        intro c hc
        by_contra hcW
        exact hw2 ⟨c, hcW, hc⟩
      intro a ha c hc
      have ha' : f a = w := ha
      have hc' : f c = w := hc
      exact hWinj (hfibW a ha') (hfibW c hc') (ha'.trans hc'.symm)
    · exact (hopen W hWopen).inter (isOpen_compl_iff.mpr (hclosedmap Wᶜ hWopen.isClosed_compl))
    · constructor
      · exact ⟨z₀, hz₀W, hz₀⟩
      · rintro ⟨c, hcW, hc⟩
        exact hcW (hfib c hc ▸ hz₀W)
  have hGoodc_open : IsOpen Goodᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro w₁ hw₁
    have hw₁' : ¬ (f ⁻¹' {w₁}).Subsingleton := hw₁
    rw [Set.not_subsingleton_iff] at hw₁'
    obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hw₁'
    have hz₁' : f z₁ = w₁ := hz₁
    have hz₂' : f z₂ = w₁ := hz₂
    obtain ⟨W₁, hW₁o, hzW₁, hinj₁⟩ := hstack z₁
    obtain ⟨W₂, hW₂o, hzW₂, hinj₂⟩ := hstack z₂
    obtain ⟨U₁, U₂, hU₁o, hU₂o, hzU₁, hzU₂, hUdisj⟩ := t2_separation hne
    refine ⟨f '' (W₁ ∩ U₁) ∩ f '' (W₂ ∩ U₂), ?_, ?_, ?_⟩
    · rintro w ⟨⟨a, ⟨haW, haU⟩, ha⟩, ⟨c, ⟨hcW, hcU⟩, hc⟩⟩
      have hac : a ≠ c := by
        intro haceq
        rw [haceq] at haU
        exact (Set.disjoint_left.mp hUdisj haU) hcU
      intro hsub
      exact hac (hsub (show a ∈ f ⁻¹' {w} from ha) (show c ∈ f ⁻¹' {w} from hc))
    · exact (hopen _ (hW₁o.inter hU₁o)).inter (hopen _ (hW₂o.inter hU₂o))
    · exact ⟨⟨z₁, ⟨hzW₁, hzU₁⟩, hz₁'⟩, ⟨z₂, ⟨hzW₂, hzU₂⟩, hz₂'⟩⟩
  have hGood_w₀ : w₀ ∈ Good := by
    have h1 : (f ⁻¹' {w₀}).Subsingleton := by
      intro a ha c hc
      have ha' : f a = w₀ := ha
      have hc' : f c = w₀ := hc
      exact hfar_inj a c (hfarfiber a ha') (hfarfiber c hc') (ha'.trans hc'.symm)
    exact h1
  have hGood_univ : Good = Set.univ :=
    IsClopen.eq_univ ⟨isOpen_compl_iff.mp hGoodc_open, hGood_open⟩ ⟨w₀, hGood_w₀⟩
  have hinj : Function.Injective f := by
    intro a c hac
    have h1 : f c ∈ Good := by rw [hGood_univ]; exact Set.mem_univ _
    have h2 : (f ⁻¹' {f c}).Subsingleton := h1
    exact h2 (show a ∈ f ⁻¹' {f c} from hac) (show c ∈ f ⁻¹' {f c} from rfl)
  exact ⟨hcont, hopen, hinj, hsurj⟩

/-- **The inverse of the smooth-case principal solution is a principal
solution** (Ahlfors–Bers Lemma 11). If `f` is a `C¹` homeomorphic principal
solution for a smooth compactly supported coefficient, its inverse
`g = f⁻¹` is the principal solution of the explicit coefficient

`ν(w) = −μ(g w)·∂f(g w) / conj (∂f(g w))`

(chain rule for `C¹` diffeomorphisms: `∂g = conj(∂f)/J ∘ g`,
`∂̄g = −∂̄f/J ∘ g`). Since `|ν| = |μ ∘ g|` pointwise, the dilatation does not
grow, and `ν` is supported in the compact image `f '' supp μ` — the two
uniformities the measurable-case endgame consumes. -/
theorem IsPrincipalSolution.inverse_principalSolution_of_contDiff
    {b : BeltramiCoeff} {f : ℂ → ℂ} (hf : IsPrincipalSolution b f)
    (hμs : ContDiff ℝ ∞ b.μ) (hμc : HasCompactSupport b.μ)
    (hf1 : ContDiff ℝ 1 f) (hdet : ∀ z : ℂ, 0 < (fderiv ℝ f z).det)
    (hhom : IsHomeomorph f) :
    ∃ ν : BeltramiCoeff,
      (∀ w : ℂ, ν.μ w = -(b.μ ((hhom.homeomorph f).symm w)
          * dz f ((hhom.homeomorph f).symm w)
          / (starRingEnd ℂ) (dz f ((hhom.homeomorph f).symm w)))) ∧
      eLpNormEssSup ν.μ volume ≤ eLpNormEssSup b.μ volume ∧
      HasCompactSupport ν.μ ∧
      (∀ w : ℂ, ν.μ w ≠ 0 → w ∈ f '' tsupport b.μ) ∧
      IsPrincipalSolution ν ⇑(hhom.homeomorph f).symm := by
  classical
  -- ===== 0. homeomorphism bookkeeping =====
  set G := hhom.homeomorph f with hGdef
  set g : ℂ → ℂ := ⇑G.symm with hgdef
  have hGcoe : ⇑G = f := by
    funext a
    rw [hGdef]
    exact IsHomeomorph.homeomorph_apply f hhom a
  have hcont : Continuous f := hf1.continuous
  have hgc : Continuous g := by rw [hgdef]; exact G.symm.continuous
  have hfg : ∀ w, f (g w) = w := by
    intro w
    rw [hgdef, ← hGcoe]
    exact G.apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := by
    intro z
    rw [hgdef, ← hGcoe]
    exact G.symm_apply_apply z
  have hinj : Function.Injective f := by
    intro a c hac
    have h1 := congrArg g hac
    rwa [hgf, hgf] at h1
  -- ===== 1. pointwise coefficient bound =====
  set k : ℝ := (eLpNormEssSup b.μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkfin : eLpNormEssSup b.μ volume ≠ ⊤ := (b.bound.trans_le le_top).ne
  have hk1 : k < 1 := by
    rw [hkdef, show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hkfin ENNReal.one_ne_top).2 b.bound
  have hμ_ae : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ ≤ k := by
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ₑ ≤ eLpNormEssSup b.μ volume :=
      ae_le_eLpNormEssSup
    filter_upwards [h1] with z hz
    rw [← ofReal_norm_eq_enorm] at hz
    have h3 := ENNReal.toReal_mono hkfin hz
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h3
  have hμpt : ∀ z, ‖b.μ z‖ ≤ k := by
    by_contra hcon
    obtain ⟨z₀, hz₀⟩ := not_forall.mp hcon
    rw [not_le] at hz₀
    have hopen : IsOpen {z : ℂ | k < ‖b.μ z‖} :=
      isOpen_lt continuous_const hμs.continuous.norm
    have hnull : volume {z : ℂ | k < ‖b.μ z‖} = 0 := by
      have h2 := hμ_ae
      rw [MeasureTheory.ae_iff] at h2
      have hset : {z : ℂ | ¬ ‖b.μ z‖ ≤ k} = {z : ℂ | k < ‖b.μ z‖} := by
        ext z; simp [not_le]
      rwa [hset] at h2
    exact absurd hnull (hopen.measure_pos volume ⟨z₀, hz₀⟩).ne'
  -- ===== 2. continuity toolkit for Wirtinger derivatives =====
  have hdifff : ∀ z, DifferentiableAt ℝ f z :=
    fun z => hf1.differentiable one_ne_zero z
  have happly_cont : ∀ F : ℂ → ℂ, Continuous (fun z => fderiv ℝ F z) →
      Continuous (fun z => dz F z) ∧ Continuous (fun z => dzbar F z) := by
    intro F hF
    have h2 : Continuous (fun z => (fderiv ℝ F z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hF
    have h3 : Continuous (fun z => (fderiv ℝ F z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hF
    constructor
    · have h4 : (fun z => dz F z)
          = fun z => (1 / 2 : ℂ)
              * ((fderiv ℝ F z) 1 - Complex.I * (fderiv ℝ F z) Complex.I) := by
        funext z; rw [dz]
      rw [h4]
      exact continuous_const.mul (h2.sub (continuous_const.mul h3))
    · have h4 : (fun z => dzbar F z)
          = fun z => (1 / 2 : ℂ)
              * ((fderiv ℝ F z) 1 + Complex.I * (fderiv ℝ F z) Complex.I) := by
        funext z; rw [dzbar]
      rw [h4]
      exact continuous_const.mul (h2.add (continuous_const.mul h3))
  have hfd_cont : Continuous (fun z => fderiv ℝ f z) := (contDiff_one_iff_fderiv.mp hf1).2
  have hdzf_cont : Continuous (fun z => dz f z) := (happly_cont f hfd_cont).1
  have hdzbarf_cont : Continuous (fun z => dzbar f z) := (happly_cont f hfd_cont).2
  -- ===== 3. nonvanishing of `∂f` and the complex Jacobian =====
  have hdzf_ne : ∀ z, dz f z ≠ 0 := by
    intro z hz
    have h1 := hdet z
    rw [det_fderiv_eq_wirtinger, hz] at h1
    simp only [norm_zero] at h1
    nlinarith [sq_nonneg ‖dzbar f z‖]
  have hconj_ne : ∀ z, (starRingEnd ℂ) (dz f z) ≠ 0 := by
    intro z hz
    rw [starRingEnd_apply, star_eq_zero] at hz
    exact hdzf_ne z hz
  have hJC : ∀ z, dz f z * (starRingEnd ℂ) (dz f z)
      - dzbar f z * (starRingEnd ℂ) (dzbar f z) = ((fderiv ℝ f z).det : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.mul_conj, det_fderiv_eq_wirtinger,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hDneC : ∀ z, ((fderiv ℝ f z).det : ℂ) ≠ 0 :=
    fun z => Complex.ofReal_ne_zero.mpr (hdet z).ne'
  -- ===== 4. the inverse is `C¹` =====
  have hg1 : ContDiff ℝ 1 g := by
    have hcle : ∀ a : ℂ, ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f a := by
      intro a
      have hAdet : LinearMap.det ((fderiv ℝ f a : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ≠ 0 :=
        (hdet a).ne'
      refine ⟨(LinearMap.equivOfDetNeZero ((fderiv ℝ f a : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
          hAdet).toContinuousLinearEquiv, ?_⟩
      ext v
      simp
    choose eqv heqv using hcle
    have hfd : ∀ a : ℂ, HasFDerivAt (⇑G) ((eqv a : ℂ →L[ℝ] ℂ)) a := by
      intro a
      rw [hGcoe, heqv a]
      exact (hf1.differentiable one_ne_zero a).hasFDerivAt
    have hGC1 : ContDiff ℝ 1 ⇑G := by rw [hGcoe]; exact hf1
    rw [hgdef]
    exact G.contDiff_symm hfd hGC1
  have hdiffg : ∀ w, DifferentiableAt ℝ g w :=
    fun w => hg1.differentiable one_ne_zero w
  have hgfd_cont : Continuous (fun w => fderiv ℝ g w) := (contDiff_one_iff_fderiv.mp hg1).2
  have hdzg_cont : Continuous (fun w => dz g w) := (happly_cont g hgfd_cont).1
  have hdzbarg_cont : Continuous (fun w => dzbar g w) := (happly_cont g hgfd_cont).2
  -- ===== 5. Wirtinger derivatives of the identity, and the dictionary =====
  have hdzid : ∀ z : ℂ, dz (fun w : ℂ => w) z = 1 ∧ dzbar (fun w : ℂ => w) z = 0 := by
    intro z
    have hfd : fderiv ℝ (fun w : ℂ => w) z = ContinuousLinearMap.id ℝ ℂ := fderiv_id'
    constructor
    · rw [dz, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination (-(1 / 2 : ℂ)) * Complex.I_mul_I
    · rw [dzbar, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination ((1 / 2 : ℂ)) * Complex.I_mul_I
  have hdict : ∀ (F : ℂ → ℂ) (z : ℂ), (fderiv ℝ F z) 1 = dz F z + dzbar F z ∧
      (fderiv ℝ F z) Complex.I = Complex.I * (dz F z - dzbar F z) := by
    intro F z
    constructor
    · rw [dz, dzbar]; ring
    · rw [dz, dzbar]
      linear_combination ((fderiv ℝ F z) Complex.I) * Complex.I_mul_I
  -- ===== 6. chain rule: the Wirtinger derivatives of the inverse =====
  have hcompid : (fun x : ℂ => f (g x)) = fun x : ℂ => x := funext hfg
  have hchain1 : ∀ w, dz f (g w) * dz g w
      + dzbar f (g w) * (starRingEnd ℂ) (dzbar g w) = 1 := by
    intro w
    have h0 := dz_comp (hdiffg w) (hdifff (g w))
    rw [hcompid, (hdzid w).1] at h0
    exact h0.symm
  have hchain2 : ∀ w, dz f (g w) * dzbar g w
      + dzbar f (g w) * (starRingEnd ℂ) (dz g w) = 0 := by
    intro w
    have h0 := dzbar_comp (hdiffg w) (hdifff (g w))
    rw [hcompid, (hdzid w).2] at h0
    exact h0.symm
  have hdzg : ∀ w, dz g w
      = (starRingEnd ℂ) (dz f (g w)) / ((fderiv ℝ f (g w)).det : ℂ) := by
    intro w
    have h1 := hchain1 w
    have h2 := hchain2 w
    have hD := hJC (g w)
    have hDne := hDneC (g w)
    have hconj2 : (starRingEnd ℂ) (dz f (g w)) * (starRingEnd ℂ) (dzbar g w)
        + (starRingEnd ℂ) (dzbar f (g w)) * dz g w = 0 := by
      have h3 := congrArg (starRingEnd ℂ) h2
      simpa [map_add, map_mul] using h3
    rw [eq_div_iff hDne]
    linear_combination (starRingEnd ℂ) (dz f (g w)) * h1
      - dzbar f (g w) * hconj2 - dz g w * hD
  have hdzbarg : ∀ w, dzbar g w
      = -(dzbar f (g w)) / ((fderiv ℝ f (g w)).det : ℂ) := by
    intro w
    have h1 := hchain1 w
    have h2 := hchain2 w
    have hD := hJC (g w)
    have hDne := hDneC (g w)
    have hconj1 : (starRingEnd ℂ) (dz f (g w)) * (starRingEnd ℂ) (dz g w)
        + (starRingEnd ℂ) (dzbar f (g w)) * dzbar g w = 1 := by
      have h3 := congrArg (starRingEnd ℂ) h1
      simpa [map_add, map_mul] using h3
    rw [eq_div_iff hDne]
    linear_combination (starRingEnd ℂ) (dz f (g w)) * h2
      - dzbar f (g w) * hconj1 - dzbar g w * hD
  -- ===== 7. pointwise Beltrami equation for `f` =====
  have hbelt : ∀ z, dzbar f z = b.μ z * dz f z := by
    obtain ⟨p₀, h₀, R₀, hp₀, hp₀', hmem₀, hsupp₀, heq₀, hrepr₀⟩ := hf
    have hp₀1 : (1 : ℝ≥0∞) ≤ p₀ := le_of_lt (lt_trans ENNReal.one_lt_two hp₀)
    have hPh₀fun : cauchyTransform h₀ = fun z => f z - z := by
      funext z; rw [hrepr₀ z]; ring
    have hPh₀C1 : ContDiff ℝ 1 (cauchyTransform h₀) := by
      rw [hPh₀fun]; exact hf1.sub contDiff_id
    have hwg₀ := hasWeakGradient_cauchyTransform hp₀ hp₀' hmem₀ hsupp₀
    have hSh₀mem : MemLp (beurling h₀) p₀ volume := memLp_beurling_of_memLp hp₀ hp₀' hmem₀
    have hfdPh₀_cont : Continuous (fun z => fderiv ℝ (cauchyTransform h₀) z) :=
      (contDiff_one_iff_fderiv.mp hPh₀C1).2
    have hclx_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h₀) z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdPh₀_cont
    have hcly_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h₀) z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdPh₀_cont
    have haex := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPh₀C1.contDiffOn) hwg₀.1
      (locallyIntegrableOn_univ.mpr hclx_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr ((hSh₀mem.add hmem₀).locallyIntegrable hp₀1))
    have haey := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPh₀C1.contDiffOn) hwg₀.2
      (locallyIntegrableOn_univ.mpr hcly_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr
        (((hSh₀mem.sub hmem₀).const_mul Complex.I).locallyIntegrable hp₀1))
    have hff : f = fun w => w + cauchyTransform h₀ w := funext hrepr₀
    have haeBelt : (fun z => dzbar f z) =ᵐ[volume] (fun z => b.μ z * dz f z) := by
      filter_upwards [haex, haey, heq₀] with z hx hy heqz
      have hx' : (fderiv ℝ (cauchyTransform h₀) z) 1 = beurling h₀ z + h₀ z :=
        hx (Set.mem_univ z)
      have hy' : (fderiv ℝ (cauchyTransform h₀) z) Complex.I
          = Complex.I * (beurling h₀ z - h₀ z) := hy (Set.mem_univ z)
      have hidd : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiable_id.differentiableAt
      have hPd : DifferentiableAt ℝ (cauchyTransform h₀) z :=
        hPh₀C1.differentiable one_ne_zero z
      have hdzbarfz : dzbar f z = h₀ z := by
        rw [hff, dzbar_add hidd hPd, (hdzid z).2, zero_add, dzbar, hx', hy']
        linear_combination ((1 / 2 : ℂ) * (beurling h₀ z - h₀ z)) * Complex.I_mul_I
      have hdzfz : dz f z = 1 + beurling h₀ z := by
        rw [hff, dz_add hidd hPd, (hdzid z).1, dz, hx', hy']
        linear_combination (-(1 / 2 : ℂ) * (beurling h₀ z - h₀ z)) * Complex.I_mul_I
      rw [hdzbarfz, hdzfz, heqz]
      ring
    have hEq := (Continuous.ae_eq_iff_eq volume hdzbarf_cont
      (hμs.continuous.mul hdzf_cont)).mp haeBelt
    intro z
    exact congrFun hEq z
  -- ===== 8. the inverse coefficient =====
  set μν : ℂ → ℂ :=
    fun w => -(b.μ (g w) * dz f (g w) / (starRingEnd ℂ) (dz f (g w))) with hμνdef
  have hμν_cont : Continuous μν := by
    rw [hμνdef]
    refine Continuous.neg (Continuous.div ?_ ?_ ?_)
    · exact (hμs.continuous.comp hgc).mul (hdzf_cont.comp hgc)
    · exact Complex.continuous_conj.comp (hdzf_cont.comp hgc)
    · intro w
      exact hconj_ne (g w)
  have hμν_norm : ∀ w, ‖μν w‖ = ‖b.μ (g w)‖ := by
    intro w
    rw [hμνdef]
    rw [norm_neg, norm_div, norm_mul, RCLike.norm_conj, mul_div_assoc,
      div_self (norm_ne_zero_iff.mpr (hdzf_ne (g w))), mul_one]
  have hμν_essSup : eLpNormEssSup μν volume ≤ eLpNormEssSup b.μ volume := by
    have h1 : ∀ᵐ w ∂(volume : Measure ℂ), ‖μν w‖ ≤ k :=
      Filter.Eventually.of_forall (fun w => (hμν_norm w) ▸ hμpt (g w))
    have h2 := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure ℂ)) h1
    rwa [hkdef, ENNReal.ofReal_toReal hkfin] at h2
  have himg_cpt : IsCompact (f '' tsupport b.μ) := hμc.isCompact.image hcont
  have hgw_supp : ∀ w, w ∉ f '' tsupport b.μ → b.μ (g w) = 0 := by
    intro w hw
    by_contra hne
    exact hw ⟨g w, subset_tsupport _ (Function.mem_support.mpr hne), hfg w⟩
  have hμν_zero : ∀ w, w ∉ f '' tsupport b.μ → μν w = 0 := by
    intro w hw
    rw [hμνdef]
    simp only [hgw_supp w hw, zero_mul, zero_div, neg_zero]
  refine ⟨⟨μν, hμν_cont.measurable, lt_of_le_of_lt hμν_essSup b.bound⟩,
    fun w => rfl, hμν_essSup, ?_, ?_, ?_⟩
  · exact HasCompactSupport.intro himg_cpt hμν_zero
  · intro w hw
    by_contra hmem
    exact hw (hμν_zero w hmem)
  · -- ===== 9. the inverse is the principal solution of `ν` =====
    -- The canonical field of the inverse: `h = ∂̄g`, continuous with compact
    -- support in the image of `supp μ`.
    have hbeltg : ∀ w, dzbar g w = μν w * dz g w := by
      intro w
      have hca := hconj_ne (g w)
      have hD := hDneC (g w)
      rw [hdzbarg w, hdzg w, hbelt (g w)]
      simp only [hμνdef]
      field_simp
    obtain ⟨R₂, hR₂⟩ : ∃ r : ℝ, f '' tsupport b.μ ⊆ Metric.closedBall 0 r :=
      himg_cpt.isBounded.subset_closedBall 0
    have hfar_notmem : ∀ w : ℂ, R₂ < ‖w‖ → w ∉ f '' tsupport b.μ := by
      intro w hw hmem
      have h2 := hR₂ hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      exact absurd h2 (not_le.mpr hw)
    have hg_van : ∀ w : ℂ, R₂ < ‖w‖ → dzbar g w = 0 := by
      intro w hw
      have h0 : b.μ (g w) = 0 := hgw_supp w (hfar_notmem w hw)
      rw [hdzbarg w, hbelt (g w), h0, zero_mul, neg_zero, zero_div]
    have hg_cs : HasCompactSupport (fun w => dzbar g w) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R₂) ?_
      intro w hw
      refine hg_van w ?_
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
      exact hw
    have hp4 : (2 : ℝ≥0∞) < 4 := by norm_num
    have hp4' : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h14 : (1 : ℝ≥0∞) ≤ 4 := by norm_num
    have hg_mem : MemLp (fun w => dzbar g w) 4 volume :=
      hdzbarg_cont.memLp_of_hasCompactSupport hg_cs
    have hSg_mem : MemLp (beurling (fun w => dzbar g w)) 4 volume :=
      memLp_beurling_of_memLp hp4 hp4' hg_mem
    have hPg_cont : Continuous (cauchyTransform (fun w => dzbar g w)) :=
      continuous_cauchyTransform_of_memLp_of_support hp4 hp4' hg_mem hg_van
    have hwg_g := hasWeakGradient_cauchyTransform hp4 hp4' hg_mem hg_van
    have hweyl : ∀ (f gx gy : ℂ → ℂ), Continuous f →
        HasWeakDirDeriv 1 gx f Set.univ → HasWeakDirDeriv Complex.I gy f Set.univ →
        LocallyIntegrable gx → LocallyIntegrable gy →
        (∀ z, gx z + Complex.I * gy z = 0) →
        Differentiable ℂ f := by
      intro f gx gy hfcont hwgx hwgy hgxLI hgyLI hcombpt
      have hfloc : LocallyIntegrable f := hfcont.locallyIntegrable
      have hcomb : ∀ᵐ z ∂(volume : Measure ℂ), gx z + Complex.I * gy z = 0 :=
        Filter.Eventually.of_forall hcombpt
      set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
        { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
          rIn_pos := by positivity,
          rIn_lt_rOut := by
            rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hφbdef
      have hφrout : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        simpa [hφbdef] using h2
      set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρdef
      set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hfndef
      have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
        (φb n).contDiff_normed (n := ⊤)
      have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φb n).hasCompactSupport_normed
      have hρcont : ∀ n, Continuous (ρ n) := fun n => (hρsm n).continuous
      have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ)
          = MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
        fun n z => fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
      have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I
          = MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
        fun n z => fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
      have hexx : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gx
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
        (hρsupp n).convolutionExists_left _ (hρcont n) hgxLI
      have hexy : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gy
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
        (hρsupp n).convolutionExists_left _ (hρcont n) hgyLI
      have hfn_holo : ∀ n, DifferentiableOn ℂ (fn n) Set.univ := by
        intro n
        have hfn_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) :=
          (hρsupp n).contDiff_convolution_left _ (hρsm n) hfloc
        have hfn_diffR : ∀ z, DifferentiableAt ℝ (fn n) z := fun z =>
          (hfn_smooth.differentiable (by simp)).differentiableAt
        have hdzbar0 : ∀ z, dzbar (fn n) z = 0 := by
          intro z
          have hval : dzbar (fn n) z
              = (1 / 2 : ℂ) *
                (MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                  + Complex.I * MeasureTheory.convolution (ρ n) gy
                    (ContinuousLinearMap.lsmul ℝ ℝ) volume z) := by
            rw [dzbar, hA1x n z, hA1y n z]
          have hzero : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
                volume z
              + Complex.I * MeasureTheory.convolution (ρ n) gy
                (ContinuousLinearMap.lsmul ℝ ℝ) volume z = 0 := by
            set Fx : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gx (z - t))
              with hFx
            set Fy : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gy (z - t))
              with hFy
            have hcx : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
                volume z = ∫ t, Fx t := rfl
            have hcy : MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
                volume z = ∫ t, Fy t := rfl
            rw [hcx, hcy]
            have hIint : Complex.I * ∫ t, Fy t = ∫ t, Complex.I * Fy t :=
              (MeasureTheory.integral_const_mul Complex.I Fy).symm
            rw [hIint]
            have hix : MeasureTheory.Integrable Fx volume := (hexx n z)
            have hiy : MeasureTheory.Integrable (fun t => Complex.I * Fy t) volume :=
              (hexy n z).const_mul Complex.I
            rw [← MeasureTheory.integral_add hix hiy]
            refine MeasureTheory.integral_eq_zero_of_ae ?_
            have hshift : ∀ᵐ t ∂(volume : Measure ℂ),
                gx (z - t) + Complex.I * gy (z - t) = 0 := by
              have hmp : MeasureTheory.MeasurePreserving (fun t : ℂ => z - t)
                  (volume : Measure ℂ) volume :=
                (volume : Measure ℂ).measurePreserving_sub_left z
              exact hmp.quasiMeasurePreserving.ae hcomb
            filter_upwards [hshift] with t ht
            simp only [hFx, hFy, ContinuousLinearMap.lsmul_apply, Pi.zero_apply]
            rw [mul_smul_comm, ← smul_add, ht, smul_zero]
          rw [hval, hzero, mul_zero]
        refine (differentiableOn_iff_dzbar_eq_zero isOpen_univ ?_).mpr (fun z _ => hdzbar0 z)
        exact fun z _ => (hfn_diffR z).differentiableWithinAt
      have hTLU : TendstoLocallyUniformlyOn fn f atTop Set.univ := by
        rw [tendstoLocallyUniformlyOn_univ]
        refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
        refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
        have hUC : UniformContinuousOn f (Metric.closedBall x 2) :=
          (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hfcont.continuousOn
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hε2 : (0 : ℝ) < ε / 2 := by positivity
        obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
        have hev : ∀ᶠ n in atTop, (φb n).rOut < min δ 1 := by
          have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
          filter_upwards [this] with n hn using hn
        filter_upwards [hev] with n hn z hz
        have hrout_le_one : (φb n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
        have hrout_le_δ : (φb n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
        have hsupp2 : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φb n).rOut := by
          rw [hρdef, (φb n).support_normed_eq]
        have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φb n).nonneg_normed y
        have hintf : ∫ y, ρ n y ∂volume = 1 := (φb n).integral_normed
        have hclose : ∀ y ∈ Metric.ball z (φb n).rOut, dist (f y) (f z) ≤ ε / 2 := by
          intro y hy
          have hzmem : z ∈ Metric.closedBall x 2 :=
            Metric.closedBall_subset_closedBall (by norm_num) hz
          rw [Metric.mem_ball] at hy
          have hymem : y ∈ Metric.closedBall x 2 := by
            rw [Metric.mem_closedBall] at hz ⊢
            calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
              _ ≤ (φb n).rOut + 1 := by gcongr
              _ ≤ 1 + 1 := by gcongr
              _ = 2 := by norm_num
          exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
        calc dist (f z) (fn n z) = dist (fn n z) (f z) := dist_comm _ _
          _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp2 hnf hintf
                hfcont.aestronglyMeasurable hclose
          _ < ε := by linarith
      have hdiffOn : DifferentiableOn ℂ f Set.univ :=
        hTLU.differentiableOn (Filter.Eventually.of_forall hfn_holo) isOpen_univ
      rw [← differentiableOn_univ]
      exact hdiffOn
    -- ===== the comparison function `u = g − (id + P(∂̄g))` =====
    set u : ℂ → ℂ := fun w => g w - (w + cauchyTransform (fun x => dzbar g x) w)
      with hu_def
    have hu_cont : Continuous u := by
      rw [hu_def]
      exact hgc.sub (continuous_id.add hPg_cont)
    -- weak gradients
    have hwgx_g : HasWeakDirDeriv 1 (fun z => (fderiv ℝ g z) 1) g Set.univ :=
      HasWeakDirDeriv.of_contDiffOn isOpen_univ hg1.contDiffOn
    have hwgy_g : HasWeakDirDeriv Complex.I (fun z => (fderiv ℝ g z) Complex.I) g
        Set.univ :=
      HasWeakDirDeriv.of_contDiffOn isOpen_univ hg1.contDiffOn
    have hidC : ContDiffOn ℝ 1 (fun z : ℂ => z) Set.univ := contDiffOn_id
    have hid1 := HasWeakDirDeriv.of_contDiffOn (v := 1) isOpen_univ hidC
    have hidI := HasWeakDirDeriv.of_contDiffOn (v := Complex.I) isOpen_univ hidC
    have hfder1 : (fun z : ℂ => (fderiv ℝ (fun z : ℂ => z) z) 1) = fun _ : ℂ => (1:ℂ) := by
      funext z
      rw [fderiv_id']
      rfl
    have hfderI : (fun z : ℂ => (fderiv ℝ (fun z : ℂ => z) z) Complex.I)
        = fun _ : ℂ => Complex.I := by
      funext z
      rw [fderiv_id']
      rfl
    rw [hfder1] at hid1
    rw [hfderI] at hidI
    have hLIid : LocallyIntegrableOn (fun z : ℂ => z) Set.univ :=
      continuous_id.locallyIntegrable.locallyIntegrableOn _
    have hLIP : LocallyIntegrableOn (cauchyTransform (fun x => dzbar g x)) Set.univ :=
      hPg_cont.locallyIntegrable.locallyIntegrableOn _
    have hLI1 : LocallyIntegrableOn (fun _ : ℂ => (1:ℂ)) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hLII : LocallyIntegrableOn (fun _ : ℂ => Complex.I) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hLIgx : LocallyIntegrableOn
        (fun z => beurling (fun x => dzbar g x) z + dzbar g z) Set.univ :=
      ((hSg_mem.add hg_mem).locallyIntegrable h14).locallyIntegrableOn _
    have hLIgy : LocallyIntegrableOn
        (fun z => Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) Set.univ :=
      (((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14).locallyIntegrableOn _
    have hwF0x := HasWeakDirDeriv.add hid1 hwg_g.1 hLIid hLIP hLI1 hLIgx
    have hwF0y := HasWeakDirDeriv.add hidI hwg_g.2 hLIid hLIP hLII hLIgy
    have hLIg : LocallyIntegrableOn g Set.univ :=
      hgc.locallyIntegrable.locallyIntegrableOn _
    have hLIF0 : LocallyIntegrableOn
        (fun z : ℂ => z + cauchyTransform (fun x => dzbar g x) z) Set.univ :=
      (continuous_id.add hPg_cont).locallyIntegrable.locallyIntegrableOn _
    have hLIgx_g : LocallyIntegrableOn (fun z => (fderiv ℝ g z) 1) Set.univ :=
      ((((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).continuous).comp
        hgfd_cont).locallyIntegrable).locallyIntegrableOn _
    have hLIgy_g : LocallyIntegrableOn (fun z => (fderiv ℝ g z) Complex.I) Set.univ :=
      ((((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp
        hgfd_cont).locallyIntegrable).locallyIntegrableOn _
    have hLIF0x : LocallyIntegrableOn
        (fun z => (1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z)) Set.univ := by
      have h1 : LocallyIntegrable (fun _ : ℂ => (1:ℂ)) volume :=
        continuous_const.locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => beurling (fun x => dzbar g x) z + dzbar g z) volume :=
        (hSg_mem.add hg_mem).locallyIntegrable h14
      exact (h1.add h2).locallyIntegrableOn _
    have hLIF0y : LocallyIntegrableOn
        (fun z => Complex.I
          + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) Set.univ := by
      have h1 : LocallyIntegrable (fun _ : ℂ => Complex.I) volume :=
        continuous_const.locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) volume :=
        ((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14
      exact (h1.add h2).locallyIntegrableOn _
    have hwux := HasWeakDirDeriv.sub hwgx_g hwF0x hLIg hLIF0 hLIgx_g hLIF0x
    have hwuy := HasWeakDirDeriv.sub hwgy_g hwF0y hLIg hLIF0 hLIgy_g hLIF0y
    have hLIux : LocallyIntegrable (fun z => (fderiv ℝ g z) 1
        - ((1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z))) volume := by
      have h1 : LocallyIntegrable (fun z => (fderiv ℝ g z) 1) volume :=
        (((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).continuous).comp hgfd_cont).locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => (1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z)) volume := by
        have h3 : LocallyIntegrable (fun _ : ℂ => (1:ℂ)) volume :=
          continuous_const.locallyIntegrable
        have h4 : LocallyIntegrable
            (fun z => beurling (fun x => dzbar g x) z + dzbar g z) volume :=
          (hSg_mem.add hg_mem).locallyIntegrable h14
        exact h3.add h4
      exact h1.sub h2
    have hLIuy : LocallyIntegrable (fun z => (fderiv ℝ g z) Complex.I
        - (Complex.I + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)))
        volume := by
      have h1 : LocallyIntegrable (fun z => (fderiv ℝ g z) Complex.I) volume :=
        (((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp
          hgfd_cont).locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => Complex.I
            + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) volume := by
        have h3 : LocallyIntegrable (fun _ : ℂ => Complex.I) volume :=
          continuous_const.locallyIntegrable
        have h4 : LocallyIntegrable
            (fun z => Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) volume :=
          ((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14
        exact h3.add h4
      exact h1.sub h2
    have hcombpt : ∀ z, ((fderiv ℝ g z) 1
        - ((1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z)))
        + Complex.I * ((fderiv ℝ g z) Complex.I
          - (Complex.I + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)))
        = 0 := by
      intro z
      rw [(hdict g z).1, (hdict g z).2]
      linear_combination (dz g z - 1 - beurling (fun x => dzbar g x) z) * Complex.I_mul_I
    have hu_ent : Differentiable ℂ u :=
      hweyl u _ _ hu_cont hwux hwuy hLIux hLIuy hcombpt
    -- ===== `u → 0` cocompactly, hence `u ≡ 0` by Liouville =====
    have hdecay : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0) :=
      hf.tendsto_sub_id_cocompact
    have hgproper : Tendsto g (cocompact ℂ) (cocompact ℂ) := by
      have h1 : IsProperMap g := by
        rw [hgdef]
        exact G.symm.isProperMap
      exact (isProperMap_iff_tendsto_cocompact.mp h1).2
    have ht1 : Tendsto (fun w => g w - w) (cocompact ℂ) (𝓝 0) := by
      have h3 : Tendsto (fun z => -(f z - z)) (cocompact ℂ) (𝓝 0) := by
        have h4 := hdecay.neg
        rwa [neg_zero] at h4
      have h2 : Tendsto ((fun z => -(f z - z)) ∘ g) (cocompact ℂ) (𝓝 0) :=
        h3.comp hgproper
      refine h2.congr ?_
      intro w
      simp only [Function.comp_apply]
      rw [hfg w]
      ring
    have ht2 : Tendsto (cauchyTransform (fun x => dzbar g x)) (cocompact ℂ) (𝓝 0) :=
      cauchyTransform_tendsto_cocompact hp4 hp4' hg_mem hg_van
    have hu0 : Tendsto u (cocompact ℂ) (𝓝 0) := by
      have h2 := ht1.sub ht2
      rw [sub_zero] at h2
      refine h2.congr ?_
      intro w
      simp only [hu_def]
      ring
    have hubdd : Bornology.IsBounded (Set.range u) := by
      have h1 : ∀ᶠ z in Filter.cocompact ℂ, u z ∈ Metric.closedBall (0 : ℂ) 1 :=
        hu0 (Metric.closedBall_mem_nhds 0 one_pos)
      rw [Filter.eventually_iff, Filter.mem_cocompact] at h1
      obtain ⟨K, hKc, hKsub⟩ := h1
      have h2 : Set.range u ⊆ (u '' K) ∪ Metric.closedBall (0 : ℂ) 1 := by
        rintro _ ⟨z, rfl⟩
        by_cases hz : z ∈ K
        · exact Or.inl ⟨z, hz, rfl⟩
        · exact Or.inr (hKsub hz)
      exact (((hKc.image hu_cont).isBounded).union Metric.isBounded_closedBall).subset h2
    have hu_zero : ∀ z, u z = 0 := by
      intro z
      have hconst : ∀ w, u w = u z := fun w => hu_ent.apply_eq_apply_of_bounded hubdd w z
      have hc' : Tendsto u (Filter.cocompact ℂ) (𝓝 (u z)) := by
        have hfe : u = fun _ => u z := funext hconst
        rw [hfe]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique hc' hu0
    have hrepr_g : ∀ w, g w = w + cauchyTransform (fun x => dzbar g x) w := by
      intro w
      have h0 := hu_zero w
      simp only [hu_def] at h0
      linear_combination h0
    -- ===== the a.e. fixed-point equation for the inverse field =====
    have hPgfun : cauchyTransform (fun x => dzbar g x) = fun w => g w - w := by
      funext w
      rw [hrepr_g w]
      ring
    have hPgC1 : ContDiff ℝ 1 (cauchyTransform (fun x => dzbar g x)) := by
      rw [hPgfun]
      exact hg1.sub contDiff_id
    have hfdPg_cont : Continuous
        (fun z => fderiv ℝ (cauchyTransform (fun x => dzbar g x)) z) :=
      (contDiff_one_iff_fderiv.mp hPgC1).2
    have hclxg_cont : Continuous
        (fun z => (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdPg_cont
    have hclyg_cont : Continuous
        (fun z => (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdPg_cont
    have haex_g := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPgC1.contDiffOn) hwg_g.1
      (locallyIntegrableOn_univ.mpr hclxg_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr ((hSg_mem.add hg_mem).locallyIntegrable h14))
    have haey_g := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPgC1.contDiffOn) hwg_g.2
      (locallyIntegrableOn_univ.mpr hclyg_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr
        (((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14))
    have heq_g : (fun w => dzbar g w) =ᵐ[volume]
        (fun w => μν w * beurling (fun x => dzbar g x) w + μν w) := by
      filter_upwards [haex_g, haey_g] with w hx hy
      have hx' : (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) w) 1
          = beurling (fun x => dzbar g x) w + dzbar g w := hx (Set.mem_univ w)
      have hy' : (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) w) Complex.I
          = Complex.I * (beurling (fun x => dzbar g x) w - dzbar g w) :=
        hy (Set.mem_univ w)
      have hgfun2 : g = fun x => x + cauchyTransform (fun y => dzbar g y) x :=
        funext hrepr_g
      have hidd : DifferentiableAt ℝ (fun x : ℂ => x) w := differentiable_id.differentiableAt
      have hPd : DifferentiableAt ℝ (cauchyTransform (fun x => dzbar g x)) w :=
        hPgC1.differentiable one_ne_zero w
      have hdzg_ae : dz g w = 1 + beurling (fun x => dzbar g x) w := by
        conv_lhs => rw [hgfun2]
        rw [dz_add hidd hPd, (hdzid w).1, dz, hx', hy']
        linear_combination (-(1 / 2 : ℂ)
          * (beurling (fun x => dzbar g x) w - dzbar g w)) * Complex.I_mul_I
      change dzbar g w = μν w * beurling (fun x => dzbar g x) w + μν w
      rw [hbeltg w, hdzg_ae]
      ring
    exact ⟨4, (fun w => dzbar g w), R₂, hp4, hp4', hg_mem, hg_van, heq_g, hrepr_g⟩

/-! ## Uniform potential estimates -/


/-- **Uniform Hölder bound for the Cauchy transform** — the family-uniform form
of the proved `cauchyTransform_sub_le_holder`: a constant `C = C(p, R)` with

`‖P h z₁ − P h z₂‖ ≤ C·‖h‖ₚ·‖z₁ − z₂‖^(1−2/p)`

for **every** field `h ∈ Lᵖ` (`p > 2`) vanishing outside the ball of radius
`R`. The difference kernel scales: `∫ |1/(ζ−z₁) − 1/(ζ−z₂)|^q dA =
c(q)·‖z₁ − z₂‖^(2−q)`, so the constant depends only on the exponent data. -/
theorem cauchyTransform_sub_le_holder_uniform {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ → ℂ, MemLp h p volume →
      (∀ z : ℂ, R < ‖z‖ → h z = 0) →
      ∀ z₁ z₂ : ℂ, ‖cauchyTransform h z₁ - cauchyTransform h z₂‖
        ≤ C * (eLpNorm h p volume).toReal * ‖z₁ - z₂‖ ^ (1 - 2 / p.toReal) := by
  -- ===== Exponent bookkeeping: `pr > 2`, conjugate `qr ∈ (1,2)`, `α ∈ (0,1)` =====
  set pr : ℝ := p.toReal with hpr_def
  have hp0 : p ≠ 0 := (lt_trans (by norm_num : (0:ℝ≥0∞) < 2) hp).ne'
  have hpr2 : 2 < pr := by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp').mpr hp
    simpa [← hpr_def] using h2
  have hpr0 : 0 < pr := lt_trans two_pos hpr2
  set qr : ℝ := (1 - pr⁻¹)⁻¹ with hqr_def
  have hainv0 : 0 < pr⁻¹ := inv_pos.mpr hpr0
  have hainv : pr⁻¹ < 2⁻¹ := by
    have hmul : pr * pr⁻¹ = 1 := mul_inv_cancel₀ hpr0.ne'
    nlinarith [hainv0, hpr2, hmul]
  have hb0 : 0 < 1 - pr⁻¹ := by
    have h12 : (2 : ℝ)⁻¹ < 1 := by norm_num
    linarith
  have hbinv0 : 0 < (1 - pr⁻¹)⁻¹ := inv_pos.mpr hb0
  have hbmul : (1 - pr⁻¹) * (1 - pr⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
  have hqr1 : 1 < qr := by
    rw [hqr_def]
    nlinarith [hbmul, mul_pos hainv0 hbinv0, hbinv0]
  have hqr2 : qr < 2 := by
    rw [hqr_def]
    nlinarith [hbmul, hainv, hbinv0]
  have hqr0 : 0 < qr := lt_trans one_pos hqr1
  have hpq : pr.HolderConjugate qr := by
    refine ⟨?_, hpr0, hqr0⟩
    rw [hqr_def, inv_inv, inv_one]
    ring
  set α : ℝ := 1 - 2 / pr with hα_def
  have hα0 : 0 < α := by
    rw [hα_def]
    have hlt : 2 / pr < 1 := (div_lt_one hpr0).mpr hpr2
    linarith
  have hαqr : (2 - qr) / qr = α := by
    have h1qr : qr⁻¹ = 1 - pr⁻¹ := by rw [hqr_def, inv_inv]
    rw [hα_def, div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hqr0.ne', h1qr]
    ring
  -- ===== Global constants (independent of the field `h`) =====
  set κ₁ : ℝ := (2 * Real.pi / (2 - qr)) ^ (1/qr) with hκ₁_def
  set κ₂ : ℝ := (2 * Real.pi / (2*qr - 2)) ^ (1/qr) with hκ₂_def
  have hκ₁0 : 0 ≤ κ₁ := Real.rpow_nonneg (div_nonneg (by positivity) (by linarith)) _
  have hκ₂0 : 0 ≤ κ₂ := Real.rpow_nonneg (div_nonneg (by positivity) (by linarith)) _
  set κ : ℝ := κ₁ * 2 ^ α + κ₁ * 3 ^ α + κ₂ * 2 ^ α with hκ_def
  have h2α : (0:ℝ) ≤ 2 ^ α := Real.rpow_nonneg (by norm_num) _
  have h3α : (0:ℝ) ≤ 3 ^ α := Real.rpow_nonneg (by norm_num) _
  have hκ0 : 0 ≤ κ := by
    rw [hκ_def]
    have := mul_nonneg hκ₁0 h2α
    have := mul_nonneg hκ₁0 h3α
    have := mul_nonneg hκ₂0 h2α
    linarith
  -- ===== Radial kernel integrals =====
  -- pointwise: `‖w⁻¹‖ₑ ^ qr = ofReal (‖w‖ ^ (-qr))`
  have hpt : ∀ w : ℂ, ‖w⁻¹‖ₑ ^ qr = ENNReal.ofReal (‖w‖ ^ (-qr)) := fun w => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hqr0.le,
      norm_inv, Real.inv_rpow (norm_nonneg w), ← Real.rpow_neg (norm_nonneg w)]
  -- `‖·‖^(-qr)` is integrable on balls (dimension 2, `qr < 2`)
  have hnegpow_int : ∀ r : ℝ, 0 < r →
      IntegrableOn (fun w : ℂ => ‖w‖ ^ (-qr)) (Metric.ball (0:ℂ) r) volume := by
    intro r hr
    rw [← integrable_indicator_iff measurableSet_ball]
    set F : ℝ → ℝ := fun t : ℝ => if t < r then t ^ (-qr) else 0 with hF
    have heq : (Metric.ball (0:ℂ) r).indicator (fun w : ℂ => ‖w‖ ^ (-qr))
        = fun w : ℂ => F ‖w‖ := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ Metric.ball (0:ℂ) r
      · rw [if_pos hw]
        have hwr : ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_pos hwr]
      · rw [if_neg hw]
        have hwr : ¬ ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_neg hwr]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn
        ((Set.Ioo (0 : ℝ) r).indicator fun y : ℝ => y ^ (1 - qr)) (Set.Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ioo]
      have hsub : Set.Ioo (0 : ℝ) r ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) r :=
        Set.inter_eq_left.mpr fun y hy => hy.1
      rw [hsub, intervalIntegral.integrableOn_Ioo_rpow_iff hr]
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator]
    by_cases hyR : y < r
    · rw [if_pos ⟨hy, hyR⟩, if_pos hyR,
        show (1 - qr) = (1 : ℝ) + (-qr) by ring, Real.rpow_add hy, Real.rpow_one]
      norm_num
    · rw [if_neg fun hc => hyR hc.2, if_neg hyR, mul_zero]
  -- explicit value bound on the ball
  have hball_val : ∀ r : ℝ, 0 < r →
      ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) ≤ 2 * Real.pi / (2 - qr) * r ^ (2 - qr) := by
    intro r hr
    set f : ℝ → ℝ := fun t => if t < r then t ^ (-qr) else 0 with hf
    have hconv : ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) = ∫ x : ℂ, f ‖x‖ := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ Metric.ball (0:ℂ) r
      · rw [Set.indicator_of_mem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_pos hx]
      · rw [Set.indicator_of_notMem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_neg hx]
    rw [hconv]
    rw [integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
    have hvol : volume.real (Metric.ball (0:ℂ) 1) = Real.pi := by
      rw [Measure.real, Complex.volume_ball]; simp
    rw [hvol]
    have hinner : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y = r ^ (2 - qr) / (2 - qr) := by
      have hsub' : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
        · intro x hx
          simp only [Set.mem_Ioo, Set.mem_Ioi] at *
          exact hx.1
        · intro x hx
          simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_diff, not_and, not_lt] at hx
          obtain ⟨hx0, hxR⟩ := hx
          have hnlt : ¬ (x < r) := not_lt.mpr (hxR hx0)
          rw [hf]; simp only [if_neg hnlt, smul_zero]
      rw [hsub']
      have hcongr : ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (1 - qr) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        simp only [Set.mem_Ioo] at hy
        rw [hf]
        simp only [if_pos hy.2]
        rw [pow_one, smul_eq_mul]
        rw [show y * y ^ (-qr) = y ^ (1:ℝ) * y ^ (-qr) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hy.1]
        ring_nf
      rw [hcongr]
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
      rw [integral_rpow (Or.inl (by linarith))]
      have h1 : (1 : ℝ) - qr + 1 = 2 - qr := by ring
      rw [h1, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < 2 - qr))]
      ring
    rw [hinner]
    rw [le_iff_lt_or_eq]; right
    rw [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  -- translation of set-lintegrals to the origin
  have htransl : ∀ S₀ : Set ℂ, MeasurableSet S₀ → ∀ (g : ℂ → ℝ≥0∞) (y : ℂ),
      ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y) = ∫⁻ w in S₀, g w := by
    intro S₀ hS₀ g y
    have hpre : MeasurableSet {ζ : ℂ | ζ - y ∈ S₀} := (measurable_id.sub_const y) hS₀
    calc ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y)
        = ∫⁻ ζ, ({ζ : ℂ | ζ - y ∈ S₀}).indicator (fun ζ => g (ζ - y)) ζ := by
          rw [lintegral_indicator hpre]
      _ = ∫⁻ ζ, S₀.indicator g (ζ - y) := by
          apply lintegral_congr
          intro ζ
          unfold Set.indicator
          by_cases hζ : ζ - y ∈ S₀
          · rw [if_pos hζ, if_pos (by exact hζ)]
          · rw [if_neg hζ, if_neg (by exact hζ)]
      _ = ∫⁻ ζ, S₀.indicator g ζ := lintegral_sub_right_eq_self _ y
      _ = ∫⁻ w in S₀, g w := by rw [lintegral_indicator hS₀]
  -- ball kernel bound (single pole)
  have hballE : ∀ (y : ℂ) (r : ℝ), 0 < r →
      ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) := by
    intro y r hr
    have hset : Metric.ball y r = {ζ : ℂ | ζ - y ∈ Metric.ball (0:ℂ) r} := by
      ext ζ
      simp [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        = ∫⁻ w in Metric.ball (0:ℂ) r, ‖w⁻¹‖ₑ ^ qr := by
          rw [hset]
          exact htransl _ measurableSet_ball (fun w => ‖w⁻¹‖ₑ ^ qr) y
      _ = ∫⁻ w in Metric.ball (0:ℂ) r, ENNReal.ofReal (‖w‖ ^ (-qr)) := lintegral_congr hpt
      _ = ENNReal.ofReal (∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr)) :=
          (ofReal_integral_eq_lintegral_ofReal (hnegpow_int r hr)
            (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg w) _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) :=
          ENNReal.ofReal_le_ofReal (hball_val r hr)
  -- annulus integrability (exponent `2qr > 2` at infinity)
  have hann_int : ∀ r : ℝ, 0 < r →
      IntegrableOn (fun w : ℂ => ‖w‖ ^ (-(2*qr))) {w : ℂ | r ≤ ‖w‖} volume := by
    intro r hr
    have hSmeas : MeasurableSet {w : ℂ | r ≤ ‖w‖} :=
      measurableSet_le measurable_const measurable_norm
    rw [← integrable_indicator_iff hSmeas]
    set F : ℝ → ℝ := fun t : ℝ => if r ≤ t then t ^ (-(2*qr)) else 0 with hF
    have heq : ({w : ℂ | r ≤ ‖w‖}).indicator (fun w : ℂ => ‖w‖ ^ (-(2*qr)))
        = fun w : ℂ => F ‖w‖ := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ {w : ℂ | r ≤ ‖w‖}
      · rw [if_pos hw, if_pos (by exact hw)]
      · rw [if_neg hw, if_neg (by exact hw)]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn
        ((Set.Ici r).indicator fun y : ℝ => y ^ (1 - 2*qr)) (Set.Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ici]
      have hsub : Set.Ici r ∩ Set.Ioi 0 = Set.Ici r :=
        Set.inter_eq_left.mpr fun y hy => lt_of_lt_of_le hr hy
      rw [hsub, integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_Ioi_rpow_iff hr]
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator, Set.mem_Ici]
    by_cases hyr : r ≤ y
    · rw [if_pos hyr, if_pos hyr,
        show (1 - 2*qr) = (1 : ℝ) + (-(2*qr)) by ring, Real.rpow_add hy, Real.rpow_one]
      norm_num
    · rw [if_neg hyr, if_neg hyr, mul_zero]
  -- explicit value bound on the annulus
  have hann_val : ∀ r : ℝ, 0 < r →
      ∫ w in {w : ℂ | r ≤ ‖w‖}, ‖w‖ ^ (-(2*qr))
        ≤ 2 * Real.pi / (2*qr - 2) * r ^ (2 - 2*qr) := by
    intro r hr
    set F : ℝ → ℝ := fun t : ℝ => if r ≤ t then t ^ (-(2*qr)) else 0 with hF
    have hSmeas : MeasurableSet {w : ℂ | r ≤ ‖w‖} :=
      measurableSet_le measurable_const measurable_norm
    have hconv : ∫ w in {w : ℂ | r ≤ ‖w‖}, ‖w‖ ^ (-(2*qr)) = ∫ x : ℂ, F ‖x‖ := by
      rw [← integral_indicator hSmeas]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ {w : ℂ | r ≤ ‖w‖}
      · rw [Set.indicator_of_mem hx]
        simp only [hF]
        rw [if_pos (by exact hx)]
      · rw [Set.indicator_of_notMem hx]
        simp only [hF]
        rw [if_neg (by exact hx)]
    rw [hconv]
    rw [integral_fun_norm_addHaar volume F, Complex.finrank_real_complex]
    have hvol : volume.real (Metric.ball (0:ℂ) 1) = Real.pi := by
      rw [Measure.real, Complex.volume_ball]; simp
    rw [hvol]
    have hinner : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • F y = r ^ (2 - 2*qr) / (2*qr - 2) := by
      have hsub' : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • F y
          = ∫ y in Set.Ici r, y ^ (2 - 1) • F y := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
        · intro y hy
          exact lt_of_lt_of_le hr hy
        · intro y hy
          simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ici, not_le] at hy
          rw [hF]
          simp only [if_neg (not_le.mpr hy.2), smul_zero]
      rw [hsub']
      have hcongr : ∫ y in Set.Ici r, y ^ (2 - 1) • F y
          = ∫ y in Set.Ici r, y ^ (1 - 2*qr) := by
        apply setIntegral_congr_fun measurableSet_Ici
        intro y hy
        simp only [Set.mem_Ici] at hy
        have hy0 : 0 < y := lt_of_lt_of_le hr hy
        rw [hF]
        simp only [if_pos hy]
        rw [pow_one, smul_eq_mul]
        rw [show y * y ^ (-(2*qr)) = y ^ (1:ℝ) * y ^ (-(2*qr)) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hy0]
        ring_nf
      rw [hcongr, integral_Ici_eq_integral_Ioi,
        integral_Ioi_rpow_of_lt (by linarith : (1:ℝ) - 2*qr < -1) hr]
      rw [show (1:ℝ) - 2*qr + 1 = 2 - 2*qr from by ring]
      rw [neg_div, ← div_neg, show -(2 - 2*qr) = 2*qr - 2 from by ring]
    rw [hinner]
    rw [le_iff_lt_or_eq]; right
    rw [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  -- annulus kernel bound (single pole)
  have hannE : ∀ (y : ℂ) (r : ℝ), 0 < r →
      ∫⁻ ζ in {ζ : ℂ | r ≤ ‖ζ - y‖}, ENNReal.ofReal (‖ζ - y‖ ^ (-(2*qr)))
        ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * r ^ (2 - 2*qr)) := by
    intro y r hr
    have hSmeas : MeasurableSet {w : ℂ | r ≤ ‖w‖} :=
      measurableSet_le measurable_const measurable_norm
    have hset : {ζ : ℂ | r ≤ ‖ζ - y‖} = {ζ : ℂ | ζ - y ∈ {w : ℂ | r ≤ ‖w‖}} := rfl
    calc ∫⁻ ζ in {ζ : ℂ | r ≤ ‖ζ - y‖}, ENNReal.ofReal (‖ζ - y‖ ^ (-(2*qr)))
        = ∫⁻ w in {w : ℂ | r ≤ ‖w‖}, ENNReal.ofReal (‖w‖ ^ (-(2*qr))) := by
          rw [hset]
          exact htransl _ hSmeas (fun w => ENNReal.ofReal (‖w‖ ^ (-(2*qr)))) y
      _ = ENNReal.ofReal (∫ w in {w : ℂ | r ≤ ‖w‖}, ‖w‖ ^ (-(2*qr))) :=
          (ofReal_integral_eq_lintegral_ofReal (hann_int r hr)
            (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg w) _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * r ^ (2 - 2*qr)) :=
          ENNReal.ofReal_le_ofReal (hann_val r hr)
  -- ===== Hölder machinery (field-free parts) =====
  have htri : ∀ a b : ℂ, ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := fun a b => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_sub_le a b)
  have hscale : ∀ c r : ℝ, 0 ≤ c → 0 < r →
      ENNReal.ofReal (c * r ^ (2 - qr)) ^ (1/qr)
        = ENNReal.ofReal (c ^ (1/qr) * r ^ α) := by
    intro c r hc hr
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hr.le _))
        (le_of_lt (one_div_pos.mpr hqr0)),
      Real.mul_rpow hc (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
      mul_one_div, hαqr]
  -- ===== Exhibit the uniform constant, then quantify over the field =====
  refine ⟨1 / Real.pi * κ, mul_nonneg (by positivity) hκ0, ?_⟩
  intro h hh hsupp
  have hint : ∀ z : ℂ, Integrable (fun ζ => h ζ / (ζ - z)) volume := fun z =>
    integrable_div_sub_of_memLp_of_support hp hp' hh hsupp z
  set N : ℝ≥0∞ := eLpNorm h p volume with hN_def
  have hN_ne : N ≠ ⊤ := hh.2.ne
  have hNle : ∀ S : Set ℂ, (∫⁻ ζ in S, ‖h ζ‖ₑ ^ pr) ^ (1/pr) ≤ N := by
    intro S
    rw [hN_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
    exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _)
      (le_of_lt (one_div_pos.mpr hpr0))
  have hHolder : ∀ (S : Set ℂ) (k : ℂ → ℝ≥0∞), AEMeasurable k (volume.restrict S) →
      ∫⁻ ζ in S, ‖h ζ‖ₑ * k ζ ≤ N * (∫⁻ ζ in S, k ζ ^ qr) ^ (1/qr) := by
    intro S k hk
    calc ∫⁻ ζ in S, ‖h ζ‖ₑ * k ζ
        ≤ (∫⁻ ζ in S, ‖h ζ‖ₑ ^ pr) ^ (1/pr) * (∫⁻ ζ in S, k ζ ^ qr) ^ (1/qr) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (hh.1.restrict.enorm) hk
      _ ≤ N * (∫⁻ ζ in S, k ζ ^ qr) ^ (1/qr) := mul_le_mul' (hNle S) le_rfl
  -- ===== Conclusion =====
  intro z₁ z₂
  by_cases hz : z₁ = z₂
  · rw [hz]
    simp [Real.zero_rpow hα0.ne']
  · set d : ℝ := ‖z₁ - z₂‖ with hd_def
    have hd : 0 < d := by
      rw [hd_def, norm_pos_iff]
      exact sub_ne_zero_of_ne hz
    set G : ℂ → ℂ := fun ζ => (ζ - z₁)⁻¹ - (ζ - z₂)⁻¹ with hG_def
    have hGmeas : Measurable G :=
      ((measurable_id.sub_const z₁).inv).sub ((measurable_id.sub_const z₂).inv)
    set A : Set ℂ := Metric.ball z₁ (2*d) with hA_def
    have hAmeas : MeasurableSet A := by rw [hA_def]; exact measurableSet_ball
    have hAc : Aᶜ = {ζ : ℂ | 2*d ≤ ‖ζ - z₁‖} := by
      rw [hA_def]
      ext ζ
      simp [Metric.mem_ball, dist_eq_norm, not_lt]
    have hA_sub : A ⊆ Metric.ball z₂ (3*d) := by
      intro ζ hζ
      rw [hA_def, Metric.mem_ball, dist_eq_norm] at hζ
      rw [Metric.mem_ball, dist_eq_norm]
      have hstep : ‖ζ - z₂‖ ≤ ‖ζ - z₁‖ + d := by
        calc ‖ζ - z₂‖ = ‖(ζ - z₁) + (z₁ - z₂)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖ζ - z₁‖ + ‖z₁ - z₂‖ := norm_add_le _ _
          _ = ‖ζ - z₁‖ + d := by rw [← hd_def]
      linarith
    -- pointwise off-ball bound
    have hGoff : ∀ ζ : ℂ, 2*d ≤ ‖ζ - z₁‖ →
        ‖G ζ‖ₑ ^ qr ≤ ENNReal.ofReal ((2*d) ^ qr)
          * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) := by
      intro ζ hζ
      have ha0 : 0 < ‖ζ - z₁‖ := lt_of_lt_of_le (by positivity) hζ
      have hane : ζ - z₁ ≠ 0 := norm_pos_iff.mp ha0
      have hcge : ‖ζ - z₁‖ - d ≤ ‖ζ - z₂‖ := by
        have h1 : ‖ζ - z₁‖ - ‖z₂ - z₁‖ ≤ ‖(ζ - z₁) - (z₂ - z₁)‖ := norm_sub_norm_le _ _
        have h2 : (ζ - z₁) - (z₂ - z₁) = ζ - z₂ := by ring
        have h3 : ‖z₂ - z₁‖ = d := by rw [hd_def, norm_sub_rev]
        rw [h2, h3] at h1
        exact h1
      have hc0 : 0 < ‖ζ - z₂‖ := by linarith
      have hcne : ζ - z₂ ≠ 0 := norm_pos_iff.mp hc0
      have hbc : ‖ζ - z₁‖ ≤ 2 * ‖ζ - z₂‖ := by linarith
      have hGval : ‖G ζ‖ = d / (‖ζ - z₁‖ * ‖ζ - z₂‖) := by
        have hid : G ζ = (z₁ - z₂) / ((ζ - z₁) * (ζ - z₂)) := by
          simp only [hG_def]
          rw [inv_sub_inv hane hcne]
          congr 1
          ring
        rw [hid, norm_div, norm_mul]
      have hGle : ‖G ζ‖ ≤ 2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖) := by
        rw [hGval, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hbc (mul_nonneg hd.le ha0.le)]
      have hsq : ‖ζ - z₁‖ ^ (2:ℝ) = ‖ζ - z₁‖ * ‖ζ - z₁‖ := by
        rw [show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast, pow_two]
      have hkey : (2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖)) ^ qr
          = (2*d) ^ qr * ‖ζ - z₁‖ ^ (-(2*qr)) := by
        rw [Real.div_rpow (by positivity) (by positivity), ← hsq,
          ← Real.rpow_mul (norm_nonneg _), div_eq_mul_inv,
          ← Real.rpow_neg (norm_nonneg _)]
      calc ‖G ζ‖ₑ ^ qr
          ≤ ENNReal.ofReal (2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖)) ^ qr := by
            refine ENNReal.rpow_le_rpow ?_ hqr0.le
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal hGle
        _ = ENNReal.ofReal ((2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖)) ^ qr) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hqr0.le
        _ = ENNReal.ofReal ((2*d) ^ qr * ‖ζ - z₁‖ ^ (-(2*qr))) := by rw [hkey]
        _ = ENNReal.ofReal ((2*d) ^ qr) * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) :=
            ENNReal.ofReal_mul (by positivity)
    -- the three kernel-piece bounds
    have hE₁ : (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
        ≤ ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α)) := by
      calc (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
          ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * (2*d) ^ (2 - qr)) ^ (1/qr) :=
            ENNReal.rpow_le_rpow (hballE z₁ (2*d) (by positivity))
              (le_of_lt (one_div_pos.mpr hqr0))
        _ = ENNReal.ofReal ((2 * Real.pi / (2 - qr)) ^ (1/qr) * (2*d) ^ α) :=
            hscale _ _ (div_nonneg (by positivity) (by linarith)) (by positivity)
        _ = ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α)) := by
            rw [hκ₁_def]
            congr 1
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hd.le]
    have hE₂ : (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr)
        ≤ ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α)) := by
      have hmono : ∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr
          ≤ ∫⁻ ζ in Metric.ball z₂ (3*d), ‖(ζ - z₂)⁻¹‖ₑ ^ qr :=
        lintegral_mono_set hA_sub
      calc (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr)
          ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * (3*d) ^ (2 - qr)) ^ (1/qr) :=
            ENNReal.rpow_le_rpow
              (le_trans hmono (hballE z₂ (3*d) (by positivity)))
              (le_of_lt (one_div_pos.mpr hqr0))
        _ = ENNReal.ofReal ((2 * Real.pi / (2 - qr)) ^ (1/qr) * (3*d) ^ α) :=
            hscale _ _ (div_nonneg (by positivity) (by linarith)) (by positivity)
        _ = ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α)) := by
            rw [hκ₁_def]
            congr 1
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hd.le]
    have hE₃ : (∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr) ^ (1/qr)
        ≤ ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α)) := by
      have hstep : ∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr
          ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - qr)) := by
        have h1 : ∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr
            ≤ ∫⁻ ζ in Aᶜ, ENNReal.ofReal ((2*d) ^ qr)
                * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) := by
          refine setLIntegral_mono
            (measurable_const.mul
              ((?_ : Measurable fun ζ : ℂ => ‖ζ - z₁‖ ^ (-(2*qr))).ennreal_ofReal)) ?_
          · fun_prop
          · intro ζ hζ
            refine hGoff ζ ?_
            rw [hAc] at hζ
            exact hζ
        have h2 : ∫⁻ ζ in Aᶜ, ENNReal.ofReal ((2*d) ^ qr)
              * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr)))
            = ENNReal.ofReal ((2*d) ^ qr)
              * ∫⁻ ζ in Aᶜ, ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        have h3 : ∫⁻ ζ in Aᶜ, ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr)))
            ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr)) := by
          rw [hAc]
          exact hannE z₁ (2*d) (by positivity)
        calc ∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr
            ≤ ENNReal.ofReal ((2*d) ^ qr)
                * ∫⁻ ζ in Aᶜ, ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) := by
              rw [← h2]
              exact h1
          _ ≤ ENNReal.ofReal ((2*d) ^ qr)
                * ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr)) :=
              mul_le_mul' le_rfl h3
          _ = ENNReal.ofReal ((2*d) ^ qr
                * (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr))) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ = ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - qr)) := by
              congr 1
              rw [show (2*d) ^ qr * (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr))
                  = 2 * Real.pi / (2*qr - 2) * ((2*d) ^ qr * (2*d) ^ (2 - 2*qr)) from by ring,
                ← Real.rpow_add (by positivity : (0:ℝ) < 2*d)]
              rw [show qr + (2 - 2*qr) = 2 - qr from by ring]
      calc (∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr) ^ (1/qr)
          ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - qr)) ^ (1/qr) :=
            ENNReal.rpow_le_rpow hstep (le_of_lt (one_div_pos.mpr hqr0))
        _ = ENNReal.ofReal ((2 * Real.pi / (2*qr - 2)) ^ (1/qr) * (2*d) ^ α) :=
            hscale _ _ (div_nonneg (by positivity) (by linarith)) (by positivity)
        _ = ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α)) := by
            rw [hκ₂_def]
            congr 1
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hd.le]
    -- collect the constants
    have hsum : ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α)) + ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α))
          + ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α))
        = ENNReal.ofReal (κ * d ^ α) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hκ_def]
      ring
    -- main estimate at the level of the integrals
    have hmain : ‖(∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)‖ₑ
        ≤ ENNReal.ofReal (N.toReal * (κ * d ^ α)) := by
      rw [← integral_sub (hint z₁) (hint z₂)]
      have hptG : (fun ζ => h ζ / (ζ - z₁) - h ζ / (ζ - z₂))
          =ᵐ[volume] fun ζ => h ζ * G ζ := by
        apply Filter.Eventually.of_forall
        intro ζ
        simp only [hG_def]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      calc ‖∫ ζ, (h ζ / (ζ - z₁) - h ζ / (ζ - z₂))‖ₑ
          = ‖∫ ζ, h ζ * G ζ‖ₑ := by rw [integral_congr_ae hptG]
        _ ≤ ∫⁻ ζ, ‖h ζ * G ζ‖ₑ := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ ζ, ‖h ζ‖ₑ * ‖G ζ‖ₑ := lintegral_congr fun ζ => enorm_mul _ _
        _ = (∫⁻ ζ in A, ‖h ζ‖ₑ * ‖G ζ‖ₑ) + ∫⁻ ζ in Aᶜ, ‖h ζ‖ₑ * ‖G ζ‖ₑ :=
            (lintegral_add_compl _ hAmeas).symm
        _ ≤ (N * (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
              + N * (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr))
            + N * (∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr) ^ (1/qr) := by
            refine add_le_add ?_ (hHolder Aᶜ _ (hGmeas.enorm.aemeasurable.restrict))
            calc ∫⁻ ζ in A, ‖h ζ‖ₑ * ‖G ζ‖ₑ
                ≤ ∫⁻ ζ in A, (‖h ζ‖ₑ * ‖(ζ - z₁)⁻¹‖ₑ + ‖h ζ‖ₑ * ‖(ζ - z₂)⁻¹‖ₑ) := by
                  apply lintegral_mono
                  intro ζ
                  change ‖h ζ‖ₑ * ‖G ζ‖ₑ
                    ≤ ‖h ζ‖ₑ * ‖(ζ - z₁)⁻¹‖ₑ + ‖h ζ‖ₑ * ‖(ζ - z₂)⁻¹‖ₑ
                  rw [← mul_add]
                  exact mul_le_mul' le_rfl (htri _ _)
              _ = (∫⁻ ζ in A, ‖h ζ‖ₑ * ‖(ζ - z₁)⁻¹‖ₑ)
                    + ∫⁻ ζ in A, ‖h ζ‖ₑ * ‖(ζ - z₂)⁻¹‖ₑ :=
                  lintegral_add_left'
                    ((hh.1.restrict.enorm).mul
                      (((measurable_id.sub_const z₁).inv).enorm.aemeasurable.restrict)) _
              _ ≤ N * (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
                    + N * (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr) :=
                  add_le_add
                    (hHolder A _ (((measurable_id.sub_const z₁).inv).enorm.aemeasurable.restrict))
                    (hHolder A _ (((measurable_id.sub_const z₂).inv).enorm.aemeasurable.restrict))
        _ ≤ (N * ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α))
              + N * ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α)))
            + N * ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α)) :=
            add_le_add (add_le_add (mul_le_mul' le_rfl hE₁) (mul_le_mul' le_rfl hE₂))
              (mul_le_mul' le_rfl hE₃)
        _ = N * (ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α))
              + ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α))
              + ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α))) := by ring
        _ = N * ENNReal.ofReal (κ * d ^ α) := by rw [hsum]
        _ = ENNReal.ofReal (N.toReal * (κ * d ^ α)) := by
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hN_ne]
    -- pass to the real inequality and unfold the Cauchy transform
    have hnn : (0:ℝ) ≤ N.toReal * (κ * d ^ α) :=
      mul_nonneg ENNReal.toReal_nonneg (mul_nonneg hκ0 (Real.rpow_nonneg hd.le _))
    have hX : ‖(∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)‖ ≤ N.toReal * (κ * d ^ α) := by
      have h2 := hmain
      rw [← ofReal_norm_eq_enorm] at h2
      exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h2
    have hPdiff : cauchyTransform h z₁ - cauchyTransform h z₂
        = -(1/(Real.pi:ℂ)) * ((∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)) := by
      rw [cauchyTransform, cauchyTransform, mul_sub]
    have hconst : ‖-(1/(Real.pi:ℂ))‖ = 1/Real.pi := by
      rw [norm_neg, norm_div, norm_one, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    rw [hPdiff, norm_mul, hconst]
    calc 1/Real.pi * ‖(∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)‖
        ≤ 1/Real.pi * (N.toReal * (κ * d ^ α)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 1 / Real.pi * κ * N.toReal * d ^ α := by ring

/-- **Uniform image bound for principal solutions.** Over all coefficients of
dilatation at most `k < 1` supported in the ball of radius `R`, the principal
solutions displace points by a bounded amount: there is `R' = R'(k, R)` with
`‖f z‖ ≤ R'` whenever `‖z‖ ≤ R`. Choose `p = p(k) > 2` with the Neumann
contraction (`exists_p_gt_two_beurling_contraction`); the canonical field has
`‖h‖ₚ ≤ (1 − kC)⁻¹·‖μ‖ₚ ≤ (1 − kC)⁻¹·k·|B_R|^{1/p}`, and
`norm_cauchyTransform_le_of_memLp_support` bounds the displacement `‖P h‖_∞`.
Needed to place the supports of the inverse coefficients
(`IsPrincipalSolution.inverse_principalSolution_of_contDiff`) in a uniform
ball. -/
theorem isPrincipalSolution_uniform_image_bound {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1) :
    ∃ R' : ℝ, R ≤ R' ∧ ∀ (b : BeltramiCoeff) (f : ℂ → ℂ),
      eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      IsPrincipalSolution b f →
      ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ R' := by
  classical
  -- ===== Uniform exponent data: `p₀ > 2`, CZ bound `C₀` with `k·C₀ < 1`. =====
  set ε : ℝ := (1 - k) / 2 with hε_def
  have hεpos : 0 < ε := by rw [hε_def]; linarith
  obtain ⟨p₀, hp2, hptop, C₀, hClt, hCb⟩ := beurling_opNorm_continuous ε hεpos
  have hC0 : 0 ≤ C₀ := hCb.1
  have hkC : k * C₀ < 1 := by
    have h1 : k * C₀ ≤ k * (1 + ε) := mul_le_mul_of_nonneg_left hClt.le hk0
    have h2 : k * (1 + ε) < 1 := by rw [hε_def]; nlinarith
    linarith
  have h1pos : 0 < 1 - k * C₀ := by linarith
  -- ===== The uniform `Lᵖ⁰` bound for the coefficients: `M = |B|^{1/p₀}·k`. =====
  set m : ℝ := max R 0 with hm_def
  set B : Set ℂ := Metric.closedBall (0 : ℂ) m with hB_def
  have hBmeas : MeasurableSet B := by rw [hB_def]; exact measurableSet_closedBall
  have hBfin : volume B ≠ ⊤ := by
    rw [hB_def]; exact (isCompact_closedBall _ _).measure_lt_top.ne
  set M : ℝ≥0∞ := volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k with hM_def
  have hMfin : M ≠ ⊤ := by
    rw [hM_def]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hBfin)
      ENNReal.ofReal_ne_top
  -- ===== The uniform sup-norm constant for the Cauchy transform at `(p₀, R)`. =====
  obtain ⟨C₉, hC90, hC9⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp2 hptop
  -- ===== The uniform displacement bound `D = (1 − kC₀)⁻¹·M`. =====
  set D : ℝ := (1 - k * C₀)⁻¹ * M.toReal with hD_def
  have hD0 : 0 ≤ D := by
    rw [hD_def]
    exact mul_nonneg (inv_nonneg.2 h1pos.le) ENNReal.toReal_nonneg
  refine ⟨R + C₉ * D, by linarith [mul_nonneg hC90 hD0], ?_⟩
  intro b f hkb hsupp hf
  -- The coefficient's essential bound is finite.
  have hμfin : eLpNormEssSup b.μ volume ≠ ⊤ :=
    (lt_of_le_of_lt hkb ENNReal.ofReal_lt_top).ne
  -- `b.μ ∈ Lᵖ⁰` with the quantitative bound `‖b.μ‖ₚ₀ ≤ M`.
  have hμLp : MemLp b.μ p₀ volume :=
    memLp_of_eLpNormEssSup_ne_top_of_support hptop b.measurable hμfin hsupp
  have hind : b.μ = B.indicator b.μ := by
    funext ζ
    by_cases hζ : ζ ∈ B
    · rw [Set.indicator_of_mem hζ]
    · rw [Set.indicator_of_notMem hζ]
      refine hsupp ζ ?_
      have hmζ : m < ‖ζ‖ := by
        simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      exact lt_of_le_of_lt (le_max_left R 0) hmζ
  have hae_k : ∀ᵐ z ∂volume, ‖b.μ z‖ ≤ k := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    have h1 : ‖b.μ z‖ₑ ≤ ENNReal.ofReal k := le_trans hz hkb
    rwa [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff hk0] at h1
  have hμM : eLpNorm b.μ p₀ volume ≤ M := by
    calc eLpNorm b.μ p₀ volume = eLpNorm (B.indicator b.μ) p₀ volume := by rw [← hind]
      _ = eLpNorm b.μ p₀ (volume.restrict B) :=
          eLpNorm_indicator_eq_eLpNorm_restrict hBmeas
      _ ≤ (volume.restrict B) Set.univ ^ p₀.toReal⁻¹ * ENNReal.ofReal k :=
          eLpNorm_le_of_ae_bound (ae_restrict_of_ae hae_k)
      _ = M := by rw [Measure.restrict_apply_univ, hM_def]
  -- Contraction at `b`'s essential bound.
  have ht : (eLpNormEssSup b.μ volume).toReal ≤ k :=
    ENNReal.toReal_le_of_le_ofReal hk0 hkb
  have hcontr : (eLpNormEssSup b.μ volume).toReal * C₀ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht hC0) hkC
  -- Solve the fixed-point equation with datum `b.μ`.
  obtain ⟨h, hLp, haeeq, hbound⟩ :=
    exists_lp_fixedPoint_beltrami hp2 hptop b.measurable hμfin hCb hcontr hμLp
  -- The everywhere-defined representative, vanishing pointwise outside the ball.
  set h' : ℂ → ℂ := fun z => b.μ z * beurling h z + b.μ z with hh'_def
  have hh'ae : h' =ᵐ[volume] h := haeeq.symm
  have hh'Lp : MemLp h' p₀ volume := hLp.ae_eq haeeq
  have hh'supp : ∀ z : ℂ, R < ‖z‖ → h' z = 0 := by
    intro z hz
    simp only [hh'_def]
    rw [hsupp z hz, zero_mul, zero_add]
  -- `L²` memberships (finite-measure embedding on the support ball).
  have hL2h' : MemLp h' 2 volume := by
    haveI : IsFiniteMeasure (volume.restrict B) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.2 hBfin⟩
    have hind' : h' = B.indicator h' := by
      funext ζ
      by_cases hζ : ζ ∈ B
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine hh'supp ζ ?_
        have hmζ : m < ‖ζ‖ := by
          simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
        exact lt_of_le_of_lt (le_max_left R 0) hmζ
    rw [hind']
    exact (memLp_indicator_iff_restrict hBmeas).2 ((hh'Lp.restrict B).mono_exponent hp2.le)
  have hL2h : MemLp h 2 volume := hL2h'.ae_eq hh'ae
  -- The fixed-point equation transfers to `h'`.
  have hSeq : beurling h =ᵐ[volume] beurling h' := beurling_congr_ae hL2h hL2h' haeeq
  have heq' : h' =ᵐ[volume] (fun z => b.μ z * beurling h' z + b.μ z) := by
    filter_upwards [hSeq] with z hz
    rw [← hz]
  -- `f = id + P h'` by uniqueness of the principal solution.
  have hf0 : IsPrincipalSolution b (fun z => z + cauchyTransform h' z) :=
    ⟨p₀, h', R, hp2, hptop, hh'Lp, hh'supp, heq', fun z => rfl⟩
  have hfeq : f = fun z => z + cauchyTransform h' z := isPrincipalSolution_unique hf hf0
  -- The uniform norm bound on the field: `‖h'‖ₚ₀ ≤ (1 − kC₀)⁻¹·M`.
  have hnorm' : eLpNorm h' p₀ volume = eLpNorm h p₀ volume := eLpNorm_congr_ae hh'ae
  have hinv : (1 - (eLpNormEssSup b.μ volume).toReal * C₀)⁻¹ ≤ (1 - k * C₀)⁻¹ := by
    rw [← one_div, ← one_div]
    refine one_div_le_one_div_of_le h1pos ?_
    have := mul_le_mul_of_nonneg_right ht hC0
    linarith
  have hchain : eLpNorm h p₀ volume ≤ ENNReal.ofReal ((1 - k * C₀)⁻¹) * M :=
    le_trans hbound (mul_le_mul' (ENNReal.ofReal_le_ofReal hinv) hμM)
  have htoReal : (eLpNorm h' p₀ volume).toReal ≤ D := by
    rw [hnorm']
    have h1 : (eLpNorm h p₀ volume).toReal
        ≤ (ENNReal.ofReal ((1 - k * C₀)⁻¹) * M).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin) hchain
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 h1pos.le)] at h1
    rw [hD_def]
    exact h1
  -- Assemble: for `‖z‖ ≤ R`, `‖f z‖ ≤ ‖z‖ + ‖P h' z‖ ≤ R + C₉·D`.
  intro z hz
  have hPz : ‖cauchyTransform h' z‖ ≤ C₉ * (eLpNorm h' p₀ volume).toReal :=
    hC9 h' hh'Lp hh'supp z
  have hfz : f z = z + cauchyTransform h' z := by rw [hfeq]
  calc ‖f z‖ = ‖z + cauchyTransform h' z‖ := by rw [hfz]
    _ ≤ ‖z‖ + ‖cauchyTransform h' z‖ := norm_add_le _ _
    _ ≤ R + C₉ * D :=
        add_le_add hz (le_trans hPz (mul_le_mul_of_nonneg_left htoReal hC90))

/-! ## The Ahlfors–Bers endgame: stability, convergence, injectivity -/

/-- **Resolvent stability of the Beltrami fixed point** (AIM Lemma 5.3.1). Two
fixed points `hᵢ = μᵢ·S hᵢ + μᵢ` with common contraction data satisfy the
resolvent identity `h₁ − h₂ = μ₁·S(h₁ − h₂) + (μ₁ − μ₂)·(1 + S h₂)`, so the
Neumann bound controls their distance by the coefficient difference:

`‖h₁ − h₂‖ₚ ≤ (1 − kC)⁻¹·‖(μ₁ − μ₂)·(1 + S h₂)‖ₚ`.

With `μₙ → μ` a.e., uniformly bounded and commonly supported, dominated
convergence sends the right side to `0` — the quantitative engine of the
mollification limit. -/
theorem lp_fixedPoint_beltrami_stability {μ₁ μ₂ h₁ h₂ : ℂ → ℂ}
    {p : ℝ≥0∞} {C k : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤)
    (hμ₁ : Measurable μ₁) (hμ₂ : Measurable μ₂)
    (hk₁ : eLpNormEssSup μ₁ volume ≤ ENNReal.ofReal k)
    (_hk₂ : eLpNormEssSup μ₂ volume ≤ ENNReal.ofReal k)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hk0 : 0 ≤ k) (hcontr : k * C < 1)
    (hh₁ : MemLp h₁ p volume) (hh₂ : MemLp h₂ p volume)
    (heq₁ : h₁ =ᵐ[volume] fun z => μ₁ z * beurling h₁ z + μ₁ z)
    (heq₂ : h₂ =ᵐ[volume] fun z => μ₂ z * beurling h₂ z + μ₂ z) :
    eLpNorm (fun z => h₁ z - h₂ z) p volume
      ≤ ENNReal.ofReal ((1 - k * C)⁻¹)
        * eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp)
  obtain ⟨hC0, hCbound⟩ := hCb
  have hkC0 : 0 ≤ k * C := mul_nonneg hk0 hC0
  have h1pos : 0 < 1 - k * C := by linarith
  -- The difference field is in `Lᵖ`.
  have hd : MemLp (fun z => h₁ z - h₂ z) p volume := hh₁.sub hh₂
  -- Beurling sends `Lᵖ` to `Lᵖ`.
  have hbeurLp : ∀ {u : ℂ → ℂ}, MemLp u p volume → MemLp (beurling u) p volume :=
    fun {u} hu => memLp_beurling_of_memLp hp hp' hu
  -- Beurling subtractivity a.e. on `Lᵖ` (corollary of `beurling_add_ae_lp`).
  have hbsub : beurling (fun w => h₁ w - h₂ w) =ᵐ[volume] beurling h₁ - beurling h₂ := by
    have hadd := beurling_add_ae_lp hp hp' hh₂
      (show MemLp (fun w => h₁ w - h₂ w) p volume from hd)
    have hvuv : (h₂ + fun w => h₁ w - h₂ w) = h₁ := by funext w; simp
    rw [hvuv] at hadd
    filter_upwards [hadd] with z hz
    simp only [Pi.add_apply, Pi.sub_apply] at hz ⊢
    rw [hz]; ring
  -- The resolvent identity a.e.:
  -- `h₁ − h₂ = μ₁·S(h₁ − h₂) + (μ₁ − μ₂)·(1 + S h₂)`.
  have hres : (fun z => h₁ z - h₂ z) =ᵐ[volume]
      fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z
        + (μ₁ z - μ₂ z) * (1 + beurling h₂ z) := by
    filter_upwards [heq₁, heq₂, hbsub] with z e₁ e₂ eb
    have e₁' : h₁ z = μ₁ z * beurling h₁ z + μ₁ z := e₁
    have e₂' : h₂ z = μ₂ z * beurling h₂ z + μ₂ z := e₂
    have eb' : beurling (fun w => h₁ w - h₂ w) z = beurling h₁ z - beurling h₂ z := eb
    change h₁ z - h₂ z
      = μ₁ z * beurling (fun w => h₁ w - h₂ w) z + (μ₁ z - μ₂ z) * (1 + beurling h₂ z)
    rw [e₁', e₂', eb']
    ring
  -- Measurability of the two resolvent terms.
  have hT1m : AEStronglyMeasurable
      (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) volume :=
    hμ₁.aestronglyMeasurable.mul (hbeurLp hd).aestronglyMeasurable
  have hT2m : AEStronglyMeasurable
      (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) volume :=
    (hμ₁.sub hμ₂).aestronglyMeasurable.mul
      (aestronglyMeasurable_const.add (hbeurLp hh₂).aestronglyMeasurable)
  -- The contraction bound on the first term:
  -- `‖μ₁·S(h₁−h₂)‖ₚ ≤ (k·C)·‖h₁−h₂‖ₚ`.
  have hT1bound : eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) p volume
      ≤ ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume := by
    calc eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) p volume
        ≤ eLpNormEssSup μ₁ volume
            * eLpNorm (beurling (fun w => h₁ w - h₂ w)) p volume :=
          eLpNorm_mul_le_essSup_mul hμ₁.aestronglyMeasurable (hbeurLp hd)
      _ ≤ ENNReal.ofReal k
            * (ENNReal.ofReal C * eLpNorm (fun z => h₁ z - h₂ z) p volume) :=
          mul_le_mul' hk₁ (hCbound (fun z => h₁ z - h₂ z) hd)
      _ = ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hk0]
  -- Triangle inequality: `A ≤ (k·C)·A + B`.
  have hE_le : eLpNorm (fun z => h₁ z - h₂ z) p volume
      ≤ ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume
        + eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := by
    calc eLpNorm (fun z => h₁ z - h₂ z) p volume
        = eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z
            + (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := eLpNorm_congr_ae hres
      _ ≤ eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) p volume
            + eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume :=
          eLpNorm_add_le hT1m hT2m hp1
      _ ≤ ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume
            + eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume :=
          add_le_add hT1bound le_rfl
  -- Rearrange. If the right side is infinite the bound is trivial.
  have hAfin : eLpNorm (fun z => h₁ z - h₂ z) p volume ≠ ⊤ := hd.2.ne
  by_cases hBtop :
      eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume = ⊤
  · rw [hBtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (inv_pos.mpr h1pos)).ne']
    exact le_top
  -- Otherwise pass to real numbers, rearrange, and return to `ℝ≥0∞`.
  · have hmul_ne : ENNReal.ofReal (k * C)
        * eLpNorm (fun z => h₁ z - h₂ z) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
    have hreal : (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal
        ≤ k * C * (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal
          + (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmul_ne, hBtop⟩) hE_le
      rwa [ENNReal.toReal_add hmul_ne hBtop, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hkC0] at this
    have hreal2 : (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal
        ≤ (1 - k * C)⁻¹
          * (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal := by
      rw [inv_mul_eq_div, le_div_iff₀ h1pos]
      nlinarith [hreal]
    calc eLpNorm (fun z => h₁ z - h₂ z) p volume
        = ENNReal.ofReal (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal :=
          (ENNReal.ofReal_toReal hAfin).symm
      _ ≤ ENNReal.ofReal ((1 - k * C)⁻¹
            * (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal) :=
          ENNReal.ofReal_le_ofReal hreal2
      _ = ENNReal.ofReal ((1 - k * C)⁻¹)
            * ENNReal.ofReal
              (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal :=
          ENNReal.ofReal_mul (inv_nonneg.2 h1pos.le)
      _ = ENNReal.ofReal ((1 - k * C)⁻¹)
            * eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := by
          rw [ENNReal.ofReal_toReal hBtop]

/-- **Principal solutions converge uniformly under a.e. convergence of the
coefficients** (AIM Theorem 5.3.2, convergence half). For coefficients of
dilatation at most `k < 1` supported in a common ball, a.e. convergence
`μₙ → μ` forces the principal solutions to converge uniformly on all of `ℂ`:
the fixed-point fields converge in `Lᵖ` (`lp_fixedPoint_beltrami_stability` +
dominated convergence), and `fₙ − f = P(hₙ − h)` is controlled in sup norm by
`norm_cauchyTransform_le_of_memLp_support`. -/
theorem isPrincipalSolution_tendstoUniformly_of_ae_tendsto
    {bs : ℕ → BeltramiCoeff} {b : BeltramiCoeff}
    {fs : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1)
    (hbound : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal k)
    (hbound' : eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k)
    (hsupp : ∀ n, ∀ z : ℂ, R < ‖z‖ → (bs n).μ z = 0)
    (hsupp' : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0)
    (htend : ∀ᵐ z, Tendsto (fun n => (bs n).μ z) atTop (𝓝 (b.μ z)))
    (hfs : ∀ n, IsPrincipalSolution (bs n) (fs n))
    (hf : IsPrincipalSolution b f) :
    TendstoUniformly fs f atTop := by
  classical
  -- ===== Step 0: contraction data `(p₀, C₀)` at the common dilatation bound `k`. =====
  have hkenorm : ‖(k : ℂ)‖ₑ = ENNReal.ofReal k := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
  have hkonec : eLpNormEssSup (fun _ : ℂ => (k : ℂ)) volume < 1 := by
    rw [eLpNormEssSup_const _ (NeZero.ne volume), hkenorm]
    exact ENNReal.ofReal_lt_one.2 hk
  obtain ⟨p0, hp2, hptop, C0, hCb, hcontr0⟩ :=
    exists_p_gt_two_beurling_contraction
      (measurable_const : Measurable fun _ : ℂ => (k : ℂ)) hkonec
  have hC00 : 0 ≤ C0 := hCb.1
  have hcontr : k * C0 < 1 := by
    rwa [eLpNormEssSup_const _ (NeZero.ne volume), hkenorm,
      ENNReal.toReal_ofReal hk0] at hcontr0
  have hp00 : p0 ≠ 0 := by
    intro h0
    rw [h0] at hp2
    exact absurd hp2 (by simp)
  have hp0rpos : 0 < p0.toReal := ENNReal.toReal_pos hp00 hptop
  -- ===== Step 1: canonical fixed-point fields at exponent `p₀`. =====
  have key : ∀ (bb : BeltramiCoeff) (ff : ℂ → ℂ),
      eLpNormEssSup bb.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → bb.μ z = 0) →
      IsPrincipalSolution bb ff →
      ∃ hh : ℂ → ℂ, MemLp hh p0 volume ∧
        (∀ z : ℂ, R < ‖z‖ → hh z = 0) ∧
        (hh =ᵐ[volume] fun z => bb.μ z * beurling hh z + bb.μ z) ∧
        ∀ z : ℂ, ff z = z + cauchyTransform hh z := by
    intro bb ff hbb hsuppbb hffsol
    have hμfin : eLpNormEssSup bb.μ volume ≠ ⊤ :=
      (lt_of_le_of_lt hbb ENNReal.ofReal_lt_top).ne
    have hμLp : MemLp bb.μ p0 volume :=
      memLp_of_eLpNormEssSup_ne_top_of_support hptop bb.measurable hμfin hsuppbb
    have hbbk : (eLpNormEssSup bb.μ volume).toReal ≤ k := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbb
      rwa [ENNReal.toReal_ofReal hk0] at h1
    have hcontrbb : (eLpNormEssSup bb.μ volume).toReal * C0 < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbbk hC00) hcontr
    obtain ⟨h0, hLp, haeeq, _⟩ :=
      exists_lp_fixedPoint_beltrami hp2 hptop bb.measurable hμfin hCb hcontrbb hμLp
    -- The everywhere-defined representative, vanishing pointwise outside the ball.
    set h' : ℂ → ℂ := fun z => bb.μ z * beurling h0 z + bb.μ z with hh'_def
    have hh'ae : h' =ᵐ[volume] h0 := haeeq.symm
    have hh'Lp : MemLp h' p0 volume := hLp.ae_eq haeeq
    have hh'supp : ∀ z : ℂ, R < ‖z‖ → h' z = 0 := by
      intro z hz
      simp only [hh'_def]
      rw [hsuppbb z hz, zero_mul, zero_add]
    -- `L²` memberships (finite-measure embedding on the support ball).
    have hL2h' : MemLp h' 2 volume := by
      set m : ℝ := max R 0 with hm_def
      set Bm : Set ℂ := Metric.closedBall (0 : ℂ) m with hBm_def
      have hBmmeas : MeasurableSet Bm := by rw [hBm_def]; exact measurableSet_closedBall
      haveI : IsFiniteMeasure (volume.restrict Bm) :=
        ⟨by
          rw [Measure.restrict_apply_univ]
          exact (isCompact_closedBall _ _).measure_lt_top⟩
      have hind : h' = Bm.indicator h' := by
        funext ζ
        by_cases hζ : ζ ∈ Bm
        · rw [Set.indicator_of_mem hζ]
        · rw [Set.indicator_of_notMem hζ]
          refine hh'supp ζ ?_
          have hm : m < ‖ζ‖ := by
            simpa [hBm_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
          exact lt_of_le_of_lt (le_max_left R 0) hm
      rw [hind]
      exact (memLp_indicator_iff_restrict hBmmeas).2
        ((hh'Lp.restrict Bm).mono_exponent hp2.le)
    have hL2h0 : MemLp h0 2 volume := hL2h'.ae_eq hh'ae
    -- The fixed-point equation transfers to `h'`.
    have hSeq : beurling h0 =ᵐ[volume] beurling h' := beurling_congr_ae hL2h0 hL2h' haeeq
    have heq' : h' =ᵐ[volume] (fun z => bb.μ z * beurling h' z + bb.μ z) := by
      filter_upwards [hSeq] with z hz
      rw [← hz]
    -- Identification with the given principal solution.
    have hsol' : IsPrincipalSolution bb (fun z => z + cauchyTransform h' z) :=
      ⟨p0, h', R, hp2, hptop, hh'Lp, hh'supp, heq', fun z => rfl⟩
    have hffeq := isPrincipalSolution_unique hffsol hsol'
    exact ⟨h', hh'Lp, hh'supp, heq', fun z => by rw [hffeq]⟩
  choose hs hsmem hssupp hseq hsrepr using
    fun n => key (bs n) (fs n) (hbound n) (hsupp n) (hfs n)
  obtain ⟨h, hhmem, hhsupp, hheq, hhrepr⟩ := key b f hbound' hsupp' hf
  -- ===== Step 2: resolvent stability bounds the field differences. =====
  have hstab : ∀ n, eLpNorm (fun z => hs n z - h z) p0 volume
      ≤ ENNReal.ofReal ((1 - k * C0)⁻¹)
        * eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume :=
    fun n => lp_fixedPoint_beltrami_stability hp2 hptop (bs n).measurable b.measurable
      (hbound n) hbound' hCb hk0 hcontr (hsmem n) hhmem (hseq n) hheq
  -- ===== Step 3: the stability majorant tends to `0` (dominated convergence). =====
  have hSh : MemLp (beurling h) p0 volume := memLp_beurling_of_memLp hp2 hptop hhmem
  have hShm : AEStronglyMeasurable (fun z => 1 + beurling h z) volume :=
    aestronglyMeasurable_const.add hSh.1
  set B : Set ℂ := Metric.closedBall (0 : ℂ) R with hB_def
  have hBmeas : MeasurableSet B := by rw [hB_def]; exact measurableSet_closedBall
  haveI : IsFiniteMeasure (volume.restrict B) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  -- The dominator: `(2k·|1 + S h|)^{p₀}` cut off to the support ball.
  set D : ℂ → ℝ≥0∞ := fun z =>
    B.indicator (fun w => (ENNReal.ofReal (2 * k) * ‖1 + beurling h w‖ₑ) ^ p0.toReal) z
    with hD_def
  have hconst_ne : ENNReal.ofReal (2 * k) ^ p0.toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0rpos.le ENNReal.ofReal_ne_top
  have honeB : MemLp (fun _ : ℂ => (1 : ℂ)) p0 (volume.restrict B) := memLp_const _
  have hSB : MemLp (beurling h) p0 (volume.restrict B) := hSh.restrict B
  have hgB : MemLp (fun z => 1 + beurling h z) p0 (volume.restrict B) := honeB.add hSB
  have hDint : ∫⁻ z in B, ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume ≠ ⊤ :=
    ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp00 hptop).1 hgB.2).ne
  have hDfin : ∫⁻ z, D z ∂volume ≠ ⊤ := by
    have heq1 : ∫⁻ z, D z ∂volume
        = ENNReal.ofReal (2 * k) ^ p0.toReal
          * ∫⁻ z in B, ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume := by
      calc ∫⁻ z, D z ∂volume
          = ∫⁻ z in B, (ENNReal.ofReal (2 * k) * ‖1 + beurling h z‖ₑ) ^ p0.toReal ∂volume := by
            simp only [hD_def]
            exact lintegral_indicator hBmeas _
        _ = ∫⁻ z in B, ENNReal.ofReal (2 * k) ^ p0.toReal
              * ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume :=
            lintegral_congr fun z => ENNReal.mul_rpow_of_nonneg _ _ hp0rpos.le
        _ = ENNReal.ofReal (2 * k) ^ p0.toReal
              * ∫⁻ z in B, ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume :=
            lintegral_const_mul' _ _ hconst_ne
    rw [heq1]
    exact ENNReal.mul_ne_top hconst_ne hDint
  -- a.e. dilatation bounds.
  have hkn : ∀ n, ∀ᵐ z ∂volume, ‖(bs n).μ z‖ₑ ≤ ENNReal.ofReal k := fun n =>
    (enorm_ae_le_eLpNormEssSup ((bs n).μ) volume).mono fun z hz => hz.trans (hbound n)
  have hkb : ∀ᵐ z ∂volume, ‖b.μ z‖ₑ ≤ ENNReal.ofReal k :=
    (enorm_ae_le_eLpNormEssSup (b.μ) volume).mono fun z hz => hz.trans hbound'
  -- Dominated convergence for the `p₀`-th powers.
  have hDCT : Tendsto
      (fun n => ∫⁻ z, ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal ∂volume)
      atTop (𝓝 0) := by
    have hlim := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun n z => ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal)
      (f := fun _ => (0 : ℝ≥0∞)) D
      (fun n => by
        have h1 : AEStronglyMeasurable
            (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) volume :=
          (((bs n).measurable.sub b.measurable).aestronglyMeasurable).mul hShm
        exact (ENNReal.continuous_rpow_const.measurable).comp_aemeasurable h1.enorm)
      (fun n => by
        filter_upwards [hkn n, hkb] with z hzn hzb
        by_cases hzB : z ∈ B
        · simp only [hD_def, Set.indicator_of_mem hzB]
          refine ENNReal.rpow_le_rpow ?_ hp0rpos.le
          rw [enorm_mul]
          gcongr
          refine le_trans enorm_sub_le ?_
          calc ‖(bs n).μ z‖ₑ + ‖b.μ z‖ₑ
              ≤ ENNReal.ofReal k + ENNReal.ofReal k := add_le_add hzn hzb
            _ = ENNReal.ofReal (2 * k) := by
                rw [← ENNReal.ofReal_add hk0 hk0, two_mul]
        · simp only [hD_def, Set.indicator_of_notMem hzB]
          have hzR : R < ‖z‖ := by
            simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hzB
          rw [hsupp n z hzR, hsupp' z hzR, sub_zero, zero_mul]
          simp [ENNReal.zero_rpow_of_pos hp0rpos])
      hDfin
      (by
        filter_upwards [htend] with z hz
        have h1 : Tendsto (fun n => ((bs n).μ z - b.μ z) * (1 + beurling h z))
            atTop (𝓝 0) := by
          have h2 := (hz.sub_const (b.μ z)).mul_const (1 + beurling h z)
          rwa [sub_self, zero_mul] at h2
        have h3 : Tendsto (fun n => ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ)
            atTop (𝓝 (‖(0 : ℂ)‖ₑ)) := (continuous_enorm.tendsto (0 : ℂ)).comp h1
        rw [enorm_zero] at h3
        have h5 : Tendsto (fun n => ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal)
            atTop (𝓝 ((0 : ℝ≥0∞) ^ p0.toReal)) :=
          ((ENNReal.continuous_rpow_const (y := p0.toReal)).tendsto (0 : ℝ≥0∞)).comp h3
        rwa [ENNReal.zero_rpow_of_pos hp0rpos] at h5)
    simpa using hlim
  -- The `eLpNorm` of the majorant tends to `0`.
  have hG0 : Tendsto
      (fun n => eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume)
      atTop (𝓝 0) := by
    have hrw : ∀ n, eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume
        = (∫⁻ z, ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal ∂volume)
            ^ (1 / p0.toReal) :=
      fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal hp00 hptop
    simp only [hrw]
    have h5 : Tendsto
        (fun n => (∫⁻ z, ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal ∂volume)
          ^ (1 / p0.toReal))
        atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / p0.toReal))) :=
      ((ENNReal.continuous_rpow_const (y := 1 / p0.toReal)).tendsto (0 : ℝ≥0∞)).comp hDCT
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.2 hp0rpos)] at h5
  -- The field differences tend to `0` in `L^{p₀}` (squeeze).
  have hfield0 : Tendsto (fun n => eLpNorm (fun z => hs n z - h z) p0 volume)
      atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => ENNReal.ofReal ((1 - k * C0)⁻¹)
        * eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume)
        atTop (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((1 - k * C0)⁻¹)) hG0
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => zero_le _) (fun n => hstab n)
  -- ===== Step 4: the uniform sup bound converts `Lᵖ` convergence to uniform. =====
  obtain ⟨CR, hCR0, hCR⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp2 hptop
  have hdmem : ∀ n, MemLp (fun w => hs n w - h w) p0 volume :=
    fun n => (hsmem n).sub hhmem
  have hdsupp : ∀ n, ∀ w : ℂ, R < ‖w‖ → hs n w - h w = 0 := fun n w hw => by
    rw [hssupp n w hw, hhsupp w hw, sub_zero]
  -- Cauchy-transform subtractivity from integral linearity.
  have hPsub : ∀ n, ∀ z : ℂ, cauchyTransform (fun w => hs n w - h w) z
      = cauchyTransform (hs n) z - cauchyTransform h z := by
    intro n z
    have h1 := integrable_div_sub_of_memLp_of_support hp2 hptop (hsmem n) (hssupp n) z
    have h2 := integrable_div_sub_of_memLp_of_support hp2 hptop hhmem hhsupp z
    simp only [cauchyTransform]
    rw [← mul_sub, ← integral_sub h1 h2]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => sub_div _ _ _)
  have hdiffz : ∀ n, ∀ z : ℂ, fs n z - f z = cauchyTransform (fun w => hs n w - h w) z := by
    intro n z
    rw [hsrepr n z, hhrepr z, hPsub n z]
    ring
  -- Assemble the uniform convergence.
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htoReal : Tendsto (fun n => (eLpNorm (fun z => hs n z - h z) p0 volume).toReal)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (eLpNorm (fun z => hs n z - h z) p0 volume).toReal)
        atTop (𝓝 ((0 : ℝ≥0∞).toReal)) :=
      (ENNReal.tendsto_toReal (by simp)).comp hfield0
    simpa using h1
  have hCRtend : Tendsto
      (fun n => CR * (eLpNorm (fun z => hs n z - h z) p0 volume).toReal) atTop (𝓝 0) := by
    have h1 := htoReal.const_mul CR
    rwa [mul_zero] at h1
  filter_upwards [hCRtend.eventually_lt_const hε] with n hn z
  have h1 : ‖cauchyTransform (fun w => hs n w - h w) z‖
      ≤ CR * (eLpNorm (fun w => hs n w - h w) p0 volume).toReal :=
    hCR _ (hdmem n) (hdsupp n) z
  have h2 : dist (f z) (fs n z) = ‖cauchyTransform (fun w => hs n w - h w) z‖ := by
    rw [dist_comm, dist_eq_norm, hdiffz n z]
  rw [h2]
  exact lt_of_le_of_lt h1 hn

/-- **The two-sided Hölder inequality, uniformly over the smooth family**
(Ahlfors–Bers Lemma 8). For every dilatation bound `k < 1` and support radius
`R` there are constants `c` and `α > 0` such that **every** principal solution
of a smooth compactly supported coefficient within those bounds satisfies

`‖z₁ − z₂‖ ≤ ‖f z₁ − f z₂‖ + c·‖f z₁ − f z₂‖^α` for all `z₁ z₂`.

Apply the inverse-solution package
(`IsPrincipalSolution.inverse_principalSolution_of_contDiff`): the inverse
`g = id + P h'` has field norm `‖h'‖ₚ` bounded by `k`, the uniform image ball
(`isPrincipalSolution_uniform_image_bound`), and the Neumann bound, so the
uniform Hölder estimate `cauchyTransform_sub_le_holder_uniform` at
`wᵢ = f zᵢ` gives `‖z₁ − z₂‖ − ‖w₁ − w₂‖ ≤ ‖P h' w₁ − P h' w₂‖ ≤
c·‖w₁ − w₂‖^α`. Since the constants survive the mollification limit, this
inequality is what forces the measurable-case principal solution to be
injective. -/
theorem isPrincipalSolution_two_sided_holder {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1) :
    ∃ c α : ℝ, 0 ≤ c ∧ 0 < α ∧ ∀ (b : BeltramiCoeff) (f : ℂ → ℂ),
      ContDiff ℝ ∞ b.μ → HasCompactSupport b.μ →
      eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      IsPrincipalSolution b f →
      ∀ z₁ z₂ : ℂ, ‖z₁ - z₂‖ ≤ ‖f z₁ - f z₂‖ + c * ‖f z₁ - f z₂‖ ^ α := by
  classical
  -- ===== Step 0: all constants are chosen before the family. =====
  -- Contraction exponent data at the numeric dilatation bound `k`.
  set ε : ℝ := (1 - k) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨p₀, hp₀2, hp₀top, C₀, hC₀lt, hCZ⟩ := beurling_opNorm_continuous ε hεpos
  have hC₀0 : 0 ≤ C₀ := hCZ.1
  have hkC : k * C₀ < 1 := by
    have h1 : k * C₀ ≤ k * (1 + ε) := mul_le_mul_of_nonneg_left hC₀lt.le hk0
    have h2 : k * (1 + ε) < 1 := by rw [hε]; nlinarith [hk0, hk]
    linarith
  have h1kC : 0 < 1 - k * C₀ := by linarith
  -- The Hölder exponent `α = 1 − 2/p₀ > 0`.
  have hp₀R : 2 < p₀.toReal := by
    have h1 : ((2 : ℝ≥0∞)).toReal < p₀.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) hp₀top).2 hp₀2
    simpa using h1
  have hα : 0 < 1 - 2 / p₀.toReal := by
    have h2 : 2 / p₀.toReal < 1 := (div_lt_one (by linarith)).2 hp₀R
    linarith
  -- The uniform image radius `R'` and the uniform Hölder constant at `(p₀, R')`.
  obtain ⟨R', hRR', himg⟩ := isPrincipalSolution_uniform_image_bound (k := k) (R := R) hk0 hk
  obtain ⟨C₁₀, hC₁₀0, hHold⟩ :=
    cauchyTransform_sub_le_holder_uniform (p := p₀) (R := R') hp₀2 hp₀top
  -- The uniform bound on the `Lᵖ⁰` norms of the inverse fields.
  set B : Set ℂ := Metric.closedBall (0 : ℂ) R' with hB
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  have hBfin : volume B ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  set Hb : ℝ≥0∞ :=
    ENNReal.ofReal ((1 - k * C₀)⁻¹) * (volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k) with hHb
  have hHbfin : Hb ≠ ⊤ := by
    rw [hHb]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hBfin)
        ENNReal.ofReal_ne_top)
  refine ⟨C₁₀ * Hb.toReal, 1 - 2 / p₀.toReal,
    mul_nonneg hC₁₀0 ENNReal.toReal_nonneg, hα, ?_⟩
  -- ===== The family. =====
  intro b f hbs hbc hbk hbsupp hpf
  -- Step 1: `f` is the `C¹` nondegenerate principal solution, hence a homeomorphism.
  obtain ⟨F, hFps, hF1, hFdet, _hFdz⟩ := exists_contDiffOne_principalSolution b hbs hbc
  obtain rfl : f = F := isPrincipalSolution_unique hpf hFps
  have hhom : IsHomeomorph f := isHomeomorph_of_contDiffOne_principalSolution hpf hF1 hFdet
  -- Step 2: the inverse-solution package.
  obtain ⟨ν, _hνformula, hνbound, _hνcs, hνimg, hνps⟩ :=
    hpf.inverse_principalSolution_of_contDiff hbs hbc hF1 hFdet hhom
  -- Step 3: `ν` is bounded by `k` and supported in the ball of radius `R'`.
  have hνk : eLpNormEssSup ν.μ volume ≤ ENNReal.ofReal k := hνbound.trans hbk
  have hνfin : eLpNormEssSup ν.μ volume ≠ ⊤ :=
    (lt_of_le_of_lt hνk ENNReal.ofReal_lt_top).ne
  have hνtoReal : (eLpNormEssSup ν.μ volume).toReal ≤ k := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hνk
    rwa [ENNReal.toReal_ofReal hk0] at h1
  have htsupp : tsupport b.μ ⊆ Metric.closedBall 0 R := by
    have hsub : Function.support b.μ ⊆ Metric.closedBall 0 R := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hcon
      rw [not_le] at hcon
      exact hz (hbsupp z hcon)
    exact closure_minimal hsub Metric.isClosed_closedBall
  have hνvan : ∀ w : ℂ, R' < ‖w‖ → ν.μ w = 0 := by
    intro w hw
    by_contra hne
    obtain ⟨z, hz, hzw⟩ := hνimg w hne
    have h1 : ‖z‖ ≤ R := by
      have h2 := htsupp hz
      rwa [Metric.mem_closedBall, dist_zero_right] at h2
    have h3 : ‖f z‖ ≤ R' := himg b f hbk hbsupp hpf z h1
    rw [hzw] at h3
    exact absurd h3 (not_le.mpr hw)
  -- Step 4: the canonical field of the inverse at the exponent `p₀`.
  have hνLp : MemLp ν.μ p₀ volume :=
    memLp_of_eLpNormEssSup_ne_top_of_support hp₀top ν.measurable hνfin hνvan
  have hνcontr : (eLpNormEssSup ν.μ volume).toReal * C₀ < 1 := by
    have h1 : (eLpNormEssSup ν.μ volume).toReal * C₀ ≤ k * C₀ :=
      mul_le_mul_of_nonneg_right hνtoReal hC₀0
    linarith
  obtain ⟨h₀, hh₀mem, hh₀eq, hh₀norm⟩ :=
    exists_lp_fixedPoint_beltrami hp₀2 hp₀top ν.measurable hνfin hCZ hνcontr hνLp
  -- The everywhere-defined representative, vanishing pointwise outside the ball.
  set u : ℂ → ℂ := fun z => ν.μ z * beurling h₀ z + ν.μ z with hu_def
  have hh₀u : h₀ =ᵐ[volume] u := hh₀eq
  have humem : MemLp u p₀ volume := hh₀mem.ae_eq hh₀u
  have husupp : ∀ z : ℂ, R' < ‖z‖ → u z = 0 := by
    intro z hz
    simp only [hu_def]
    rw [hνvan z hz, zero_mul, zero_add]
  -- `L²` memberships for the Beurling congruence.
  have huL2 : MemLp u 2 volume := by
    set m : ℝ := max R' 0 with hm_def
    set B₂ : Set ℂ := Metric.closedBall (0 : ℂ) m with hB₂_def
    have hB₂meas : MeasurableSet B₂ := by rw [hB₂_def]; exact measurableSet_closedBall
    haveI : IsFiniteMeasure (volume.restrict B₂) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
    have hind : u = B₂.indicator u := by
      funext ζ
      by_cases hζ : ζ ∈ B₂
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine husupp ζ ?_
        have hm : m < ‖ζ‖ := by
          simpa [hB₂_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
        exact lt_of_le_of_lt (le_max_left R' 0) hm
    rw [hind]
    exact (memLp_indicator_iff_restrict hB₂meas).2 ((humem.restrict B₂).mono_exponent hp₀2.le)
  have hh₀L2 : MemLp h₀ 2 volume := huL2.ae_eq hh₀u.symm
  have hSeq : beurling h₀ =ᵐ[volume] beurling u := beurling_congr_ae hh₀L2 huL2 hh₀u
  have hueq : u =ᵐ[volume] (fun z => ν.μ z * beurling u z + ν.μ z) := by
    filter_upwards [hSeq] with z hz
    rw [← hz]
  -- `id + P u` is a principal solution of `ν`, hence equal to the inverse of `f`.
  have hg'ps : IsPrincipalSolution ν (fun w => w + cauchyTransform u w) :=
    ⟨p₀, u, R', hp₀2, hp₀top, humem, husupp, hueq, fun z => rfl⟩
  have hgg' : (fun w => w + cauchyTransform u w) = ⇑(hhom.homeomorph f).symm :=
    isPrincipalSolution_unique hg'ps hνps
  -- The uniform field-norm bound `‖u‖ₚ₀ ≤ Hb`.
  have hunorm : eLpNorm u p₀ volume ≤ Hb := by
    have hcalc : eLpNorm ν.μ p₀ volume ≤ volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k := by
      have hband : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν.μ z‖ ≤ k := by
        filter_upwards [ae_le_eLpNormEssSup (f := ν.μ) (μ := volume)] with z hz
        have h2 : ‖ν.μ z‖ₑ ≤ ENNReal.ofReal k := le_trans hz hνk
        rw [← ofReal_norm_eq_enorm] at h2
        exact (ENNReal.ofReal_le_ofReal_iff hk0).1 h2
      have hind : ν.μ = B.indicator ν.μ := by
        funext ζ
        by_cases hζ : ζ ∈ B
        · rw [Set.indicator_of_mem hζ]
        · rw [Set.indicator_of_notMem hζ]
          refine hνvan ζ ?_
          simpa [hB, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      calc eLpNorm ν.μ p₀ volume
          = eLpNorm (B.indicator ν.μ) p₀ volume :=
            eLpNorm_congr_ae (Filter.EventuallyEq.of_eq hind)
        _ = eLpNorm ν.μ p₀ (volume.restrict B) :=
            eLpNorm_indicator_eq_eLpNorm_restrict hBmeas
        _ ≤ (volume.restrict B) Set.univ ^ p₀.toReal⁻¹ * ENNReal.ofReal k :=
            eLpNorm_le_of_ae_bound (ae_restrict_of_ae hband)
        _ = volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k := by
            rw [Measure.restrict_apply_univ]
    have hinv : (1 - (eLpNormEssSup ν.μ volume).toReal * C₀)⁻¹ ≤ (1 - k * C₀)⁻¹ := by
      have h1 : 1 - k * C₀ ≤ 1 - (eLpNormEssSup ν.μ volume).toReal * C₀ := by
        have h2 : (eLpNormEssSup ν.μ volume).toReal * C₀ ≤ k * C₀ :=
          mul_le_mul_of_nonneg_right hνtoReal hC₀0
        linarith
      gcongr
    calc eLpNorm u p₀ volume = eLpNorm h₀ p₀ volume := eLpNorm_congr_ae hh₀u.symm
      _ ≤ ENNReal.ofReal ((1 - (eLpNormEssSup ν.μ volume).toReal * C₀)⁻¹)
          * eLpNorm ν.μ p₀ volume := hh₀norm
      _ ≤ ENNReal.ofReal ((1 - k * C₀)⁻¹)
          * (volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hinv) hcalc
      _ = Hb := hHb.symm
  have huD : (eLpNorm u p₀ volume).toReal ≤ Hb.toReal := ENNReal.toReal_mono hHbfin hunorm
  -- ===== Step 5: the two-sided inequality. =====
  intro z₁ z₂
  have hrep : ∀ z : ℂ, z = f z + cauchyTransform u (f z) := by
    intro z
    have h1 : (hhom.homeomorph f).symm (f z) = z := Homeomorph.symm_apply_apply _ z
    calc z = (hhom.homeomorph f).symm (f z) := h1.symm
      _ = f z + cauchyTransform u (f z) := by rw [← hgg']
  have hdiff : z₁ - z₂
      = (f z₁ - f z₂) + (cauchyTransform u (f z₁) - cauchyTransform u (f z₂)) := by
    calc z₁ - z₂
        = (f z₁ + cauchyTransform u (f z₁)) - (f z₂ + cauchyTransform u (f z₂)) := by
          rw [← hrep z₁, ← hrep z₂]
      _ = (f z₁ - f z₂) + (cauchyTransform u (f z₁) - cauchyTransform u (f z₂)) := by
          ring
  calc ‖z₁ - z₂‖
      = ‖(f z₁ - f z₂) + (cauchyTransform u (f z₁) - cauchyTransform u (f z₂))‖ := by
        rw [hdiff]
    _ ≤ ‖f z₁ - f z₂‖ + ‖cauchyTransform u (f z₁) - cauchyTransform u (f z₂)‖ :=
        norm_add_le _ _
    _ ≤ ‖f z₁ - f z₂‖
        + C₁₀ * (eLpNorm u p₀ volume).toReal * ‖f z₁ - f z₂‖ ^ (1 - 2 / p₀.toReal) := by
        have h1 := hHold u humem husupp (f z₁) (f z₂)
        linarith
    _ ≤ ‖f z₁ - f z₂‖ + C₁₀ * Hb.toReal * ‖f z₁ - f z₂‖ ^ (1 - 2 / p₀.toReal) := by
        have hX : (0:ℝ) ≤ ‖f z₁ - f z₂‖ ^ (1 - 2 / p₀.toReal) :=
          Real.rpow_nonneg (norm_nonneg _) _
        have h2 : C₁₀ * (eLpNorm u p₀ volume).toReal ≤ C₁₀ * Hb.toReal :=
          mul_le_mul_of_nonneg_left huD hC₁₀0
        have h3 := mul_le_mul_of_nonneg_right h2 hX
        linarith

/-- **Mollification of a Beltrami coefficient.** Every compactly vanishing
Beltrami coefficient is the a.e. limit of smooth compactly supported
coefficients of no larger dilatation, supported in a slightly larger ball:
convolve with a mollifier at scales `εₙ → 0` — the convolution is smooth, its
modulus is bounded by the essential supremum of `|μ|` everywhere, its support
lies in `supp μ + B(εₙ)`, and it converges at every Lebesgue point of `μ`. -/
theorem exists_contDiff_mollification_beltrami (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ bs : ℕ → BeltramiCoeff,
      (∀ n, ContDiff ℝ ∞ (bs n).μ) ∧ (∀ n, HasCompactSupport (bs n).μ) ∧
      (∀ n, eLpNormEssSup (bs n).μ volume ≤ eLpNormEssSup b.μ volume) ∧
      (∀ n, ∀ z : ℂ, R + 1 < ‖z‖ → (bs n).μ z = 0) ∧
      ∀ᵐ z, Tendsto (fun n => (bs n).μ z) atTop (𝓝 (b.μ z)) := by
  classical
  -- ===== The `L∞` bound `k` of `b.μ` and its basic properties. =====
  have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := (b.bound.trans ENNReal.one_lt_top).ne
  set k : ℝ := (eLpNormEssSup b.μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  -- The pointwise a.e. bound `‖b.μ w‖ ≤ k`.
  have hbae : ∀ᵐ w : ℂ, ‖b.μ w‖ ≤ k := by
    filter_upwards [MeasureTheory.enorm_ae_le_eLpNormEssSup b.μ volume] with w hw
    have h1 := ENNReal.toReal_mono hfin hw
    rwa [toReal_enorm] at h1
  -- ===== The truncation `ν` of `b.μ` at level `k`. =====
  -- It is bounded by `k` *everywhere*, a.e. equal to `b.μ`, measurable, and
  -- vanishes wherever `b.μ` does.
  set ν : ℂ → ℂ := fun w => if ‖b.μ w‖ ≤ k then b.μ w else 0 with hνdef
  have hν_meas : Measurable ν :=
    Measurable.ite (measurableSet_le b.measurable.norm measurable_const)
      b.measurable measurable_const
  have hν_bdd : ∀ w, ‖ν w‖ ≤ k := by
    intro w
    by_cases hw : ‖b.μ w‖ ≤ k
    · simp [hνdef, hw]
    · simp [hνdef, hw, hk0]
  have hν_ae : ν =ᵐ[volume] b.μ := by
    filter_upwards [hbae] with w hw
    simp [hνdef, hw]
  have hν_supp : ∀ w : ℂ, R < ‖w‖ → ν w = 0 := by
    intro w hw
    simp [hνdef, hsupp w hw]
  -- `ν` is integrable (bounded, measurable, supported in `closedBall 0 R`),
  -- hence locally integrable.
  have hν_int : Integrable ν volume := by
    refine Integrable.mono' (g := (Metric.closedBall (0 : ℂ) R).indicator fun _ => k) ?_
      hν_meas.aestronglyMeasurable ?_
    · exact (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    · refine Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ Metric.closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hw]
        exact hν_bdd w
      · rw [Set.indicator_of_notMem hw]
        have hRw : R < ‖w‖ := by
          simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw
        simp [hν_supp w hRw]
  have hν_li : LocallyIntegrable ν volume := hν_int.locallyIntegrable
  -- ===== The mollifier bumps at scales `1/(n+1)` with `rOut = 2 · rIn`. =====
  set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := 1 / (2 * ((n : ℝ) + 1)), rOut := 1 / ((n : ℝ) + 1),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        refine div_lt_div_of_pos_left one_pos (by positivity) ?_
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith } with hφbdef
  have hrIn : ∀ n : ℕ, (φb n).rIn = 1 / (2 * ((n : ℝ) + 1)) := fun n => rfl
  have hrOut : ∀ n : ℕ, (φb n).rOut = 1 / ((n : ℝ) + 1) := fun n => rfl
  set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρdef
  have hρ_int : ∀ n, ∫ t : ℂ, ρ n t ∂volume = 1 := fun n => (φb n).integral_normed
  have hρ_nonneg : ∀ n t, 0 ≤ ρ n t := fun n t => (φb n).nonneg_normed t
  have hρ_integrable : ∀ n, Integrable (ρ n) volume := fun n => (φb n).integrable_normed
  have hρ_supp_eq : ∀ n, Function.support (ρ n) = Metric.ball (0 : ℂ) (φb n).rOut :=
    fun n => (φb n).support_normed_eq
  -- ===== The mollified coefficients `mol n = ρ n ⋆ ν`. =====
  set mol : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) ν (ContinuousLinearMap.lsmul ℝ ℝ) volume with hmoldef
  have hmol_eq : ∀ n z, mol n z
      = ∫ t : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t)) ∂volume := by
    intro n z
    simp only [hmoldef, MeasureTheory.convolution_def]
  -- (a) Smoothness: convolution of the smooth compactly supported bump with the
  -- locally integrable `ν`.
  have hsmooth : ∀ n, ContDiff ℝ ∞ (mol n) := fun n =>
    ((φb n).hasCompactSupport_normed).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((φb n).contDiff_normed (n := ⊤)) hν_li
  have hmol_meas : ∀ n, Measurable (mol n) := fun n => (hsmooth n).continuous.measurable
  -- (b) Everywhere pointwise bound `‖mol n z‖ ≤ k`.
  have hmol_bdd : ∀ n z, ‖mol n z‖ ≤ k := by
    intro n z
    rw [hmol_eq n z]
    calc ‖∫ t : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t)) ∂volume‖
        ≤ ∫ t : ℂ, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t))‖ ∂volume :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℂ, ρ n t * k ∂volume := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            ((hρ_integrable n).mul_const k)
          refine Eventually.of_forall fun t => ?_
          simp only [ContinuousLinearMap.lsmul_apply, norm_smul,
            Real.norm_of_nonneg (hρ_nonneg n t)]
          exact mul_le_mul_of_nonneg_left (hν_bdd _) (hρ_nonneg n t)
      _ = (∫ t : ℂ, ρ n t ∂volume) * k := integral_mul_const k _
      _ = k := by rw [hρ_int n, one_mul]
  -- The `L∞` bound conjunct.
  have hmol_esssup : ∀ n, eLpNormEssSup (mol n) volume ≤ eLpNormEssSup b.μ volume := by
    intro n
    have h1 : eLpNormEssSup (mol n) volume ≤ ENNReal.ofReal k :=
      eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun z => hmol_bdd n z)
    rwa [hkdef, ENNReal.ofReal_toReal hfin] at h1
  have hmol_lt : ∀ n, eLpNormEssSup (mol n) volume < 1 :=
    fun n => lt_of_le_of_lt (hmol_esssup n) b.bound
  -- (c) Vanishing outside `closedBall 0 (R + 1)`: for `‖z‖ > R + 1` the integrand
  -- vanishes identically (either the bump or the translated `ν` is zero).
  have hmol_vanish : ∀ n, ∀ z : ℂ, R + 1 < ‖z‖ → mol n z = 0 := by
    intro n z hz
    rw [hmol_eq n z]
    have hzero : ∀ t : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t)) = 0 := by
      intro t
      by_cases ht : ‖t‖ < (φb n).rOut
      · -- inside the bump: `‖t‖ < rOut ≤ 1`, so `‖z - t‖ > R` and `ν (z - t) = 0`.
        have hrOut_le : (φb n).rOut ≤ 1 := by
          rw [hrOut n, div_le_one (by positivity)]
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have h2 : ‖z‖ - ‖t‖ ≤ ‖z - t‖ := norm_sub_norm_le z t
        have h3 : ‖t‖ < 1 := lt_of_lt_of_le ht hrOut_le
        have h1 : R < ‖z - t‖ := by linarith
        rw [hν_supp _ h1]
        exact map_zero _
      · -- outside the bump support: `ρ n t = 0`.
        have hρ0 : ρ n t = 0 := by
          apply Function.notMem_support.mp
          rw [hρ_supp_eq n]
          simpa [Metric.mem_ball, dist_zero_right] using ht
        rw [hρ0]
        simp
    simp only [hzero, integral_zero]
  -- Compact support.
  have hmol_cs : ∀ n, HasCompactSupport (mol n) := by
    intro n
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) fun z hz => ?_
    have hz1 : R + 1 < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    exact hmol_vanish n z hz1
  -- (d) a.e. convergence `mol n z → ν z = b.μ z` (Lebesgue differentiation:
  -- Mathlib's a.e. bump-convolution convergence for locally integrable functions,
  -- with bounded ratio `rOut ≤ 2 · rIn`).
  have hφ_rout : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ_ratio : ∀ n : ℕ, (φb n).rOut ≤ 2 * (φb n).rIn := by
    intro n
    have h2 : 2 * (1 / (2 * ((n : ℝ) + 1))) = 1 / ((n : ℝ) + 1) := by
      have hx : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hrOut n, hrIn n, h2]
  have htends : ∀ᵐ z : ℂ, Tendsto (fun n => mol n z) atTop (𝓝 (ν z)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2)
      hφ_rout (Eventually.of_forall hφ_ratio) hν_li
  -- ===== Assemble the Beltrami coefficients and the five conjuncts. =====
  refine ⟨fun n => ⟨mol n, hmol_meas n, hmol_lt n⟩, fun n => hsmooth n, fun n => hmol_cs n,
    fun n => hmol_esssup n, fun n z hz => hmol_vanish n z hz, ?_⟩
  filter_upwards [htends, hν_ae] with z hz hze
  rw [← hze]
  exact hz

end RiemannDynamics

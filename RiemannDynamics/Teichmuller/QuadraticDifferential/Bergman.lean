/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Def

/-!
# The Bergman unit ball of automorphic quadratic differentials

Over a cocompact free Fuchsian base the space of holomorphic quadratic differentials with
finite `L¹` mass behaves like a finite-dimensional normed space: an `L¹` bound over the
Dirichlet domain controls the differential uniformly on compact subsets of the upper half
plane (sub-mean-value estimate plus the tiling by translates of the domain), so the unit
ball is sequentially compact for locally uniform convergence, and the Hamilton pairing
`q ↦ ∫ μ q` against a bounded measurable coefficient attains its supremum on the ball.

* `enorm_mul_le_lintegral_closedBall` — the areal sub-mean-value estimate for a
  holomorphic function.
* `lintegral_enorm_le_of_isCompact` — the `L¹` mass of a differential over a compact
  subset of the upper half plane is at most a fixed multiple of its `l1Norm`.
* `exists_enorm_le_of_l1Norm` — the uniform pointwise bound on compacts from the `l1Norm`.
* `exists_subseq_qd_tendstoLocallyUniformlyOn` — sequential compactness of `L¹`-bounded
  families of differentials.
* `qdPairing` — the Hamilton pairing over the canonical Dirichlet domain.
* `exists_qdPairing_maximizer` — attainment of the pairing supremum on the unit ball.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The sub-mean-value estimate -/

/-- **Areal sub-mean-value estimate**: a function holomorphic on an open ball and
continuous up to its closure is bounded at the center by its normalized area integral,
`π r² ‖f z₀‖ ≤ ∫_{B̄(z₀,r)} ‖f‖`. -/
theorem enorm_mul_le_lintegral_closedBall {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ r))
    (hc : ContinuousOn f (Metric.closedBall z₀ r)) :
    ‖f z₀‖ₑ * ENNReal.ofReal (Real.pi * r ^ 2)
      ≤ ∫⁻ z in Metric.closedBall z₀ r, ‖f z‖ₑ := by
  -- The circle bound for each radius `s ∈ (0, r)`.
  have hcirc : ∀ s ∈ Set.Ioo (0 : ℝ) r,
      2 * Real.pi * ‖f z₀‖ ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap z₀ s θ)‖ := by
    intro s hs
    have habs : |s| = s := abs_of_pos hs.1
    have h₁f : ContinuousOn f (Metric.closedBall z₀ |s|) := by
      rw [habs]; exact hc.mono (Metric.closedBall_subset_closedBall hs.2.le)
    have h₂f : ∀ z ∈ Metric.ball z₀ |s| \ (∅ : Set ℂ), DifferentiableAt ℂ f z := by
      intro z hz
      rw [Set.diff_empty, habs] at hz
      exact hf.differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hs.2.le hz))
    have hmean := circleAverage_of_differentiable_on_off_countable Set.countable_empty h₁f h₂f
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hnorm : ‖f z₀‖
        ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap z₀ s θ)‖ := by
      calc ‖f z₀‖ = ‖Real.circleAverage f z₀ s‖ := by rw [hmean]
        _ = (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap z₀ s θ)‖ := by
            rw [Real.circleAverage_def, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        _ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap z₀ s θ)‖ := by
            have := intervalIntegral.norm_integral_le_integral_norm
              (f := fun θ : ℝ => f (circleMap z₀ s θ)) (μ := volume)
              (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
            exact mul_le_mul_of_nonneg_left this (by positivity)
    have h := mul_le_mul_of_nonneg_left hnorm hpi.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at h
  -- Continuity of the composed circle map.
  have hfc : ∀ s ∈ Set.Ioo (0 : ℝ) r, Continuous fun θ : ℝ => ‖f (circleMap z₀ s θ)‖ := by
    intro s hs
    have hmem : ∀ θ : ℝ, circleMap z₀ s θ ∈ Metric.closedBall z₀ r := fun θ =>
      Metric.closedBall_subset_closedBall hs.2.le
        (Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hs.1.le θ))
    exact (hc.comp_continuous (continuous_circleMap z₀ s) hmem).norm
  -- The polar integrand.
  set g : ℝ × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (p.1 * ‖f (z₀ + Complex.polarCoord.symm p)‖) with hg
  set T : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi with hT
  have hTmeas : MeasurableSet T := measurableSet_Ioo.prod measurableSet_Ioo
  have hTsub : T ⊆ polarCoord.target := by
    rintro ⟨s, θ⟩ hp
    obtain ⟨hs, hθ⟩ := Set.mem_prod.mp hp
    rw [polarCoord_target]
    exact Set.mem_prod.mpr ⟨hs.1, hθ⟩
  -- Translation step.
  have htrans : (∫⁻ w in Metric.ball (0 : ℂ) r, ‖f (z₀ + w)‖ₑ)
      = ∫⁻ z in Metric.ball z₀ r, ‖f z‖ₑ := by
    have hmp : MeasurePreserving (fun w : ℂ => z₀ + w) volume volume :=
      measurePreserving_add_left volume z₀
    have hemb : MeasurableEmbedding (fun w : ℂ => z₀ + w) :=
      (Homeomorph.addLeft z₀).measurableEmbedding
    have hpre : (fun w : ℂ => z₀ + w) ⁻¹' Metric.ball z₀ r = Metric.ball (0 : ℂ) r := by
      ext w
      simp [Metric.mem_ball, dist_eq_norm]
    rw [← hpre]
    exact hmp.setLIntegral_comp_preimage_emb hemb (fun z => ‖f z‖ₑ) (Metric.ball z₀ r)
  -- Polar coordinates.
  have hpolar := Complex.lintegral_comp_polarCoord_symm
    ((Metric.ball (0 : ℂ) r).indicator fun w => ‖f (z₀ + w)‖ₑ)
  -- Identify the polar integral with the integral of `g` over the box `T`.
  have hptwise : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (Metric.ball (0 : ℂ) r).indicator (fun w => ‖f (z₀ + w)‖ₑ)
        (Complex.polarCoord.symm p) = T.indicator g p := by
    rintro ⟨s, θ⟩ hp
    rw [polarCoord_target] at hp
    obtain ⟨hs, hθ⟩ := Set.mem_prod.mp hp
    have hs0 : (0 : ℝ) < s := hs
    have hnorm : ‖Complex.polarCoord.symm (s, θ)‖ = s := by
      rw [Complex.norm_polarCoord_symm]
      exact abs_of_pos hs0
    by_cases hsr : s < r
    · have hmem : Complex.polarCoord.symm (s, θ) ∈ Metric.ball (0 : ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hsr
      have hmemT : ((s, θ) : ℝ × ℝ) ∈ T :=
        Set.mem_prod.mpr ⟨⟨hs0, hsr⟩, hθ⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemT, hg, smul_eq_mul,
        ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hs0.le]
    · have hnmem : Complex.polarCoord.symm (s, θ) ∉ Metric.ball (0 : ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hsr
      have hnmemT : ((s, θ) : ℝ × ℝ) ∉ T := by
        intro hmemT
        exact hsr (Set.mem_prod.mp hmemT).1.2
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmemT, smul_zero]
  have hsetEq : (∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 • (Metric.ball (0 : ℂ) r).indicator (fun w => ‖f (z₀ + w)‖ₑ)
          (Complex.polarCoord.symm p))
      = ∫⁻ p in T, g p := by
    rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hptwise,
      setLIntegral_indicator hTmeas, Set.inter_eq_self_of_subset_left hTsub]
  -- Tonelli.
  have hmeq : (volume.restrict (Set.Ioo (0 : ℝ) r)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))
      = volume.restrict T := by
    rw [Measure.prod_restrict, hT, ← Measure.volume_eq_prod]
  have haem : AEMeasurable g (volume.restrict T) := by
    have hsymm : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
      have heq : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
          = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
        funext p
        exact Complex.polarCoord_symm_apply p
      rw [heq]
      fun_prop
    have hmapsTo : Set.MapsTo (fun p : ℝ × ℝ => z₀ + Complex.polarCoord.symm p) T
        (Metric.closedBall z₀ r) := by
      rintro ⟨s, θ⟩ hp
      obtain ⟨hs, hθ⟩ := Set.mem_prod.mp hp
      have hnorm : ‖Complex.polarCoord.symm (s, θ)‖ = s := by
        rw [Complex.norm_polarCoord_symm]
        exact abs_of_pos hs.1
      have hd : dist (z₀ + Complex.polarCoord.symm (s, θ)) z₀ ≤ r := by
        rw [dist_eq_norm, add_sub_cancel_left, hnorm]
        exact hs.2.le
      exact Metric.mem_closedBall.mpr hd
    have hcof : ContinuousOn (fun p : ℝ × ℝ => ‖f (z₀ + Complex.polarCoord.symm p)‖) T :=
      (hc.comp ((continuous_const.add hsymm).continuousOn) hmapsTo).norm
    have hco : ContinuousOn (fun p : ℝ × ℝ => p.1 * ‖f (z₀ + Complex.polarCoord.symm p)‖) T :=
      continuous_fst.continuousOn.mul hcof
    exact (ENNReal.continuous_ofReal.comp_continuousOn hco).aemeasurable hTmeas
  have htonelli : (∫⁻ p in T, g p)
      = ∫⁻ s in Set.Ioo (0 : ℝ) r, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (s, θ) := by
    rw [← hmeq]
    exact lintegral_prod g (hmeq ▸ haem)
  -- The inner circle bound in `ℝ≥0∞` form.
  have hinner : ∀ s ∈ Set.Ioo (0 : ℝ) r,
      ENNReal.ofReal (s * (2 * Real.pi * ‖f z₀‖))
        ≤ ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (s, θ) := by
    intro s hs
    have hcm : ∀ θ : ℝ, z₀ + Complex.polarCoord.symm (s, θ) = circleMap z₀ s θ := by
      intro θ
      rw [Complex.polarCoord_symm_apply]
      simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hgeq : ∀ θ : ℝ, g (s, θ) = ENNReal.ofReal (s * ‖f (circleMap z₀ s θ)‖) := by
      intro θ
      rw [hg]
      simp only [← hcm θ]
    have hcont : Continuous fun θ : ℝ => s * ‖f (circleMap z₀ s θ)‖ :=
      continuous_const.mul (hfc s hs)
    have hint : IntegrableOn (fun θ : ℝ => s * ‖f (circleMap z₀ s θ)‖)
        (Set.Ioo (-Real.pi) Real.pi) :=
      (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-Real.pi) Real.pi)]
        fun θ : ℝ => s * ‖f (circleMap z₀ s θ)‖ :=
      Filter.Eventually.of_forall fun θ => mul_nonneg hs.1.le (norm_nonneg _)
    have hofReal := ofReal_integral_eq_lintegral_ofReal hint hnn
    have hper : Function.Periodic (fun θ : ℝ => s * ‖f (circleMap z₀ s θ)‖) (2 * Real.pi) := by
      intro θ
      simp only [periodic_circleMap z₀ s θ]
    have hIoo : (∫ θ in Set.Ioo (-Real.pi) Real.pi, s * ‖f (circleMap z₀ s θ)‖)
        = ∫ θ in (0 : ℝ)..2 * Real.pi, s * ‖f (circleMap z₀ s θ)‖ := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      have h := hper.intervalIntegral_add_eq (-Real.pi) 0
      have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
      have h3 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
      rw [h2, h3] at h
      exact h
    have hlow : s * (2 * Real.pi * ‖f z₀‖)
        ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, s * ‖f (circleMap z₀ s θ)‖ := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hcirc s hs) hs.1.le
    calc ENNReal.ofReal (s * (2 * Real.pi * ‖f z₀‖))
        ≤ ENNReal.ofReal (∫ θ in Set.Ioo (-Real.pi) Real.pi, s * ‖f (circleMap z₀ s θ)‖) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hIoo]
          exact hlow
      _ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (s * ‖f (circleMap z₀ s θ)‖) := hofReal
      _ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (s, θ) := by
          refine lintegral_congr fun θ => ?_
          rw [hgeq θ]
  -- The outer radial integral.
  have hcalc : (∫⁻ s in Set.Ioo (0 : ℝ) r, ENNReal.ofReal (s * (2 * Real.pi * ‖f z₀‖)))
      = ENNReal.ofReal (r ^ 2 / 2 * (2 * Real.pi * ‖f z₀‖)) := by
    have hcont : Continuous fun s : ℝ => s * (2 * Real.pi * ‖f z₀‖) :=
      continuous_id.mul continuous_const
    have hint : IntegrableOn (fun s : ℝ => s * (2 * Real.pi * ‖f z₀‖)) (Set.Ioo (0 : ℝ) r) :=
      (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) r)]
        fun s : ℝ => s * (2 * Real.pi * ‖f z₀‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact mul_nonneg hs.1.le (by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
      intervalIntegral.integral_mul_const, integral_id]
    ring
  have houter : ‖f z₀‖ₑ * ENNReal.ofReal (Real.pi * r ^ 2)
      ≤ ∫⁻ s in Set.Ioo (0 : ℝ) r, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (s, θ) := by
    have hmono : (∫⁻ s in Set.Ioo (0 : ℝ) r, ENNReal.ofReal (s * (2 * Real.pi * ‖f z₀‖)))
        ≤ ∫⁻ s in Set.Ioo (0 : ℝ) r, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (s, θ) :=
      setLIntegral_mono' measurableSet_Ioo fun s hs => hinner s hs
    have hfin : ENNReal.ofReal (r ^ 2 / 2 * (2 * Real.pi * ‖f z₀‖))
        = ‖f z₀‖ₑ * ENNReal.ofReal (Real.pi * r ^ 2) := by
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      ring
    rw [← hfin, ← hcalc]
    exact hmono
  calc ‖f z₀‖ₑ * ENNReal.ofReal (Real.pi * r ^ 2)
      ≤ ∫⁻ s in Set.Ioo (0 : ℝ) r, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (s, θ) := houter
    _ = ∫⁻ p in T, g p := htonelli.symm
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.ball (0 : ℂ) r).indicator (fun w => ‖f (z₀ + w)‖ₑ)
            (Complex.polarCoord.symm p) := hsetEq.symm
    _ = ∫⁻ w, (Metric.ball (0 : ℂ) r).indicator (fun w => ‖f (z₀ + w)‖ₑ) w := hpolar
    _ = ∫⁻ w in Metric.ball (0 : ℂ) r, ‖f (z₀ + w)‖ₑ :=
        lintegral_indicator Metric.isOpen_ball.measurableSet _
    _ = ∫⁻ z in Metric.ball z₀ r, ‖f z‖ₑ := htrans
    _ ≤ ∫⁻ z in Metric.closedBall z₀ r, ‖f z‖ₑ :=
        lintegral_mono_set Metric.ball_subset_closedBall

/-! ## From the `L¹` mass to locally uniform bounds -/

/-- **Tiling bound for compact mass**: over a cocompact free Fuchsian base, the `L¹` mass
of a quadratic differential on a compact subset of the upper half plane is bounded by a
fixed multiple (the number of Dirichlet tiles meeting the compact) of its `l1Norm`. -/
theorem lintegral_enorm_le_of_isCompact (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {S : Set ℂ} (hS : IsCompact S) (hSsub : S ⊆ {z : ℂ | 0 < z.im}) :
    ∃ N : ℕ, ∀ q : QuadraticDifferential Γ, ∫⁻ z in S, ‖q z‖ₑ ≤ N * q.l1Norm := by
  classical
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  have hDcpt : IsCompact (dirichletDomain Γ UpperHalfPlane.I) := isCompact_dirichletDomain hdense
  set D : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hD
  have hDc : IsCompact D := hDcpt.image UpperHalfPlane.continuous_coe
  have hDmeas : MeasurableSet D := hDc.measurableSet
  have hDsub : D ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hS' : IsCompact (UpperHalfPlane.coe ⁻¹' S) := by
    refine UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage' hS ?_
    intro z hz
    exact ⟨⟨z, hSsub hz⟩, rfl⟩
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have hfin : {γ : Γ | ((γ • ·) '' dirichletDomain Γ UpperHalfPlane.I
      ∩ UpperHalfPlane.coe ⁻¹' S).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hDcpt hS'
  set F : Finset Γ := hfin.toFinset with hF
  refine ⟨F.card, fun q => ?_⟩
  have hcover : S ⊆ ⋃ δ ∈ F,
      moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D := by
    intro z hz
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ UpperHalfPlane.I ⟨z, hSsub hz⟩
    set τ : UpperHalfPlane := ⟨z, hSsub hz⟩ with hτ
    have hmemF : γ⁻¹ ∈ F := by
      rw [hF, Set.Finite.mem_toFinset]
      refine ⟨τ, ⟨γ • τ, hγ, ?_⟩, ?_⟩
      · exact inv_smul_smul γ τ
      · change UpperHalfPlane.coe τ ∈ S
        exact hz
    refine Set.mem_biUnion hmemF ⟨UpperHalfPlane.coe (γ • τ), ⟨γ • τ, hγ, rfl⟩, ?_⟩
    have hcoe : ((((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (γ • τ)
        : UpperHalfPlane) : ℂ)
        = moebiusMap ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          (UpperHalfPlane.coe (γ • τ)) :=
      coe_smul_eq_moebiusMap _ _
    have hact : (((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (γ • τ)
        : UpperHalfPlane) = τ := by
      have : (γ⁻¹ : Γ) • (γ • τ) = τ := inv_smul_smul γ τ
      exact this
    rw [← hcoe, hact]
  have hpiece : ∀ δ : Γ, δ ∈ F →
      (∫⁻ w in moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D, ‖q w‖ₑ)
        = q.l1Norm := by
    intro δ _
    have h := q.lintegral_enorm_image (SetLike.coe_mem δ) hDmeas hDsub
    rw [h]
    rfl
  have hsum : (∫⁻ z in ⋃ δ ∈ F,
        moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D, ‖q z‖ₑ)
      ≤ ∑ δ ∈ F, ∫⁻ w in moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D,
          ‖q w‖ₑ := by
    clear hcover hpiece
    induction F using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
        calc (∫⁻ z in (moebiusMap (i : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D)
              ∪ ⋃ δ ∈ s, moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D, ‖q z‖ₑ)
            ≤ (∫⁻ w in moebiusMap (i : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D, ‖q w‖ₑ)
              + ∫⁻ z in ⋃ δ ∈ s,
                  moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D, ‖q z‖ₑ :=
              lintegral_union_le _ _ _
          _ ≤ (∫⁻ w in moebiusMap (i : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D, ‖q w‖ₑ)
              + ∑ δ ∈ s, ∫⁻ w in moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D,
                  ‖q w‖ₑ := by gcongr
  calc (∫⁻ z in S, ‖q z‖ₑ)
      ≤ ∫⁻ z in ⋃ δ ∈ F,
          moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D, ‖q z‖ₑ :=
        lintegral_mono_set hcover
    _ ≤ ∑ δ ∈ F, ∫⁻ w in moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' D,
          ‖q w‖ₑ := hsum
    _ = ∑ _δ ∈ F, q.l1Norm := Finset.sum_congr rfl hpiece
    _ = F.card * q.l1Norm := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Uniform pointwise bound on compacts**: over a cocompact free Fuchsian base, the
values of a quadratic differential on a compact subset of the upper half plane are
bounded by a fixed multiple of its `l1Norm`. -/
theorem exists_enorm_le_of_l1Norm (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {S : Set ℂ} (hS : IsCompact S) (hSsub : S ⊆ {z : ℂ | 0 < z.im}) :
    ∃ C : ℝ≥0, ∀ (q : QuadraticDifferential Γ), ∀ z ∈ S, ‖q z‖ₑ ≤ C * q.l1Norm := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨δ, hδ0, hδsub⟩ := hS.exists_thickening_subset_open hUopen hSsub
  set ρ : ℝ := δ / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρδ : ρ < δ := by
    rw [hρ]
    linarith
  set S₂ : Set ℂ := Metric.cthickening ρ S with hS₂
  have hS₂c : IsCompact S₂ := hS.cthickening
  have hS₂sub : S₂ ⊆ {z : ℂ | 0 < z.im} :=
    (Metric.cthickening_subset_thickening' hδ0 hρδ S).trans hδsub
  obtain ⟨N, hN⟩ := lintegral_enorm_le_of_isCompact hΓ hfree hcc hS₂c hS₂sub
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.pi * ρ ^ 2) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdivtop : (N : ℝ≥0∞) / c ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top N) hc0).ne
  refine ⟨((N : ℝ≥0∞) / c).toNNReal, fun q z hz => ?_⟩
  have hball : Metric.closedBall z ρ ⊆ S₂ := Metric.closedBall_subset_cthickening hz ρ
  have hballU : Metric.closedBall z ρ ⊆ {w : ℂ | 0 < w.im} := hball.trans hS₂sub
  have hf : DifferentiableOn ℂ q (Metric.ball z ρ) :=
    q.holo.mono (Metric.ball_subset_closedBall.trans hballU)
  have hcont : ContinuousOn q (Metric.closedBall z ρ) :=
    q.continuousOn_upper.mono hballU
  have h1 : ‖q z‖ₑ * c ≤ ∫⁻ w in Metric.closedBall z ρ, ‖q w‖ₑ :=
    enorm_mul_le_lintegral_closedBall hρ0 hf hcont
  have h2 : (∫⁻ w in Metric.closedBall z ρ, ‖q w‖ₑ) ≤ ∫⁻ w in S₂, ‖q w‖ₑ :=
    lintegral_mono_set hball
  have h3 : ‖q z‖ₑ * c ≤ (N : ℝ≥0∞) * q.l1Norm :=
    (h1.trans h2).trans (hN q)
  have h4 : ‖q z‖ₑ ≤ (N : ℝ≥0∞) * q.l1Norm / c :=
    (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop)).mpr h3
  calc ‖q z‖ₑ ≤ (N : ℝ≥0∞) * q.l1Norm / c := h4
    _ = (N : ℝ≥0∞) / c * q.l1Norm := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
    _ = (((N : ℝ≥0∞) / c).toNNReal : ℝ≥0∞) * q.l1Norm := by
        rw [ENNReal.coe_toNNReal hdivtop]

/-! ## Sequential compactness of the unit ball -/

/-- **Sequential compactness of `L¹`-bounded families**: a sequence of quadratic
differentials with uniformly bounded `l1Norm` subconverges locally uniformly on the upper
half plane to a quadratic differential obeying the same bound. -/
theorem exists_subseq_qd_tendstoLocallyUniformlyOn (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {A : ℝ≥0∞} (hA : A ≠ ⊤) (F : ℕ → QuadraticDifferential Γ)
    (hF : ∀ n, (F n).l1Norm ≤ A) :
    ∃ (φ : ℕ → ℕ) (q : QuadraticDifferential Γ), StrictMono φ ∧ q.l1Norm ≤ A ∧
      TendstoLocallyUniformlyOn (fun n z => F (φ n) z) (fun z => q z) atTop
        {z : ℂ | 0 < z.im} := by
  classical
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  -- The restricted continuous maps on the open upper half plane.
  set Gn : ℕ → C({z : ℂ | 0 < z.im}, ℂ) :=
    fun n => ⟨fun x => F n (x : ℂ), (F n).continuousOn_upper.restrict⟩ with hGn
  -- Equicontinuity of the family, from the Cauchy estimates.
  have heqc : Equicontinuous fun n => fun x : {z : ℂ | 0 < z.im} => F n (x : ℂ) := by
    rintro ⟨z₀, hz₀⟩
    have him : 0 < z₀.im := hz₀
    set ρ : ℝ := z₀.im / 3 with hρdef
    have hρ0 : 0 < ρ := by rw [hρdef]; linarith
    have h2ρU : Metric.closedBall z₀ (2 * ρ) ⊆ {z : ℂ | 0 < z.im} := by
      intro w hw
      have h1 : |w.im - z₀.im| ≤ ‖w - z₀‖ := by
        have h := Complex.abs_im_le_norm (w - z₀)
        rwa [Complex.sub_im] at h
      have h2 : ‖w - z₀‖ ≤ 2 * ρ := by
        rw [← dist_eq_norm]
        exact hw
      have h4 := (abs_le.mp (h1.trans h2)).1
      have h5 : z₀.im = 3 * ρ := by rw [hρdef]; ring
      change 0 < w.im
      linarith
    obtain ⟨C, hC⟩ := exists_enorm_le_of_l1Norm hΓ hfree hcc
      (isCompact_closedBall z₀ (2 * ρ)) h2ρU
    have hBne : (C : ℝ≥0∞) * A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hA
    set M : ℝ := ((C : ℝ≥0∞) * A).toReal with hMdef
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    have hM : ∀ n, ∀ w ∈ Metric.closedBall z₀ (2 * ρ), ‖F n w‖ ≤ M := by
      intro n w hw
      have h1 : ‖F n w‖ₑ ≤ (C : ℝ≥0∞) * A :=
        (hC (F n) w hw).trans (mul_le_mul_right (hF n) _)
      have h2 := ENNReal.toReal_mono hBne h1
      rwa [toReal_enorm] at h2
    have hderiv : ∀ n, ∀ w ∈ Metric.closedBall z₀ ρ, ‖deriv (F n) w‖ ≤ M / ρ := by
      intro n w hw
      have hwd : dist w z₀ ≤ ρ := hw
      have hball2 : Metric.closedBall w ρ ⊆ Metric.closedBall z₀ (2 * ρ) := by
        intro v hv
        have hvd : dist v w ≤ ρ := hv
        have htri : dist v z₀ ≤ dist v w + dist w z₀ := dist_triangle v w z₀
        change dist v z₀ ≤ 2 * ρ
        linarith
      have hdc : DiffContOnCl ℂ (F n) (Metric.ball w ρ) := by
        constructor
        · exact (F n).holo.mono ((Metric.ball_subset_closedBall.trans hball2).trans h2ρU)
        · refine (F n).continuousOn_upper.mono ?_
          rw [closure_ball w hρ0.ne']
          exact hball2.trans h2ρU
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 hdc fun v hv => ?_
      exact hM n v (hball2 (Metric.sphere_subset_closedBall hv))
    have hlip : ∀ n, ∀ x ∈ Metric.closedBall z₀ ρ, ∀ y ∈ Metric.closedBall z₀ ρ,
        ‖F n y - F n x‖ ≤ M / ρ * ‖y - x‖ := by
      intro n x hx y hy
      refine Convex.norm_image_sub_le_of_norm_deriv_le (fun w hw => ?_)
        (fun w hw => hderiv n w hw) (convex_closedBall z₀ ρ) hx hy
      have hwU : w ∈ {z : ℂ | 0 < z.im} :=
        h2ρU (Metric.closedBall_subset_closedBall (by linarith) hw)
      exact (F n).holo.differentiableAt (hUopen.mem_nhds hwU)
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    have hL0 : 0 ≤ M / ρ := div_nonneg hM0 hρ0.le
    have hL1 : (0 : ℝ) < M / ρ + 1 := by linarith
    refine ⟨min ρ (ε / (M / ρ + 1)), lt_min hρ0 (div_pos hε hL1), ?_⟩
    rintro ⟨x, hxU⟩ hxd n
    rw [Subtype.dist_eq] at hxd
    change dist (F n z₀) (F n x) < ε
    have hx1 : dist x z₀ < ρ := lt_of_lt_of_le hxd (min_le_left _ _)
    have hx2 : dist x z₀ < ε / (M / ρ + 1) := lt_of_lt_of_le hxd (min_le_right _ _)
    have hxmem : x ∈ Metric.closedBall z₀ ρ := le_of_lt hx1
    have hz₀mem : z₀ ∈ Metric.closedBall z₀ ρ := Metric.mem_closedBall_self hρ0.le
    have hd : dist (F n z₀) (F n x) ≤ M / ρ * dist x z₀ := by
      calc dist (F n z₀) (F n x) = ‖F n z₀ - F n x‖ := dist_eq_norm _ _
        _ ≤ M / ρ * ‖z₀ - x‖ := hlip n x hxmem z₀ hz₀mem
        _ = M / ρ * dist x z₀ := by rw [← dist_eq_norm, dist_comm]
    have hfinal : M / ρ * dist x z₀ < ε := by
      have h1 : M / ρ * dist x z₀ ≤ M / ρ * (ε / (M / ρ + 1)) :=
        mul_le_mul_of_nonneg_left hx2.le hL0
      have h2 : M / ρ * (ε / (M / ρ + 1)) < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ hL1]
        nlinarith
      exact lt_of_le_of_lt h1 h2
    exact lt_of_le_of_lt hd hfinal
  have heqcG : Equicontinuous fun n => ⇑(Gn n) := heqc
  -- Pointwise relative compactness of the orbits.
  have hpt : ∀ x : {z : ℂ | 0 < z.im}, ∃ Q : Set ℂ, IsCompact Q ∧ ∀ n, F n (x : ℂ) ∈ Q := by
    intro x
    obtain ⟨C, hC⟩ := exists_enorm_le_of_l1Norm hΓ hfree hcc
      (isCompact_singleton (x := (x : ℂ))) (Set.singleton_subset_iff.mpr x.2)
    refine ⟨Metric.closedBall 0 (((C : ℝ≥0∞) * A).toReal), isCompact_closedBall _ _,
      fun n => ?_⟩
    have h1 : ‖F n (x : ℂ)‖ₑ ≤ (C : ℝ≥0∞) * A :=
      (hC (F n) (x : ℂ) rfl).trans (mul_le_mul_right (hF n) _)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hA) h1
    rw [toReal_enorm] at h2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h2
  -- Arzelà–Ascoli in the compact-open topology of `C(upper, ℂ)`.
  haveI : LocallyCompactSpace {z : ℂ | 0 < z.im} := hUopen.locallyCompactSpace
  set 𝔖 : Set (Set {z : ℂ | 0 < z.im}) := {K | IsCompact K} with h𝔖
  have hce : IsClosedEmbedding
      (⇑(UniformOnFun.ofFun 𝔖) ∘
        (DFunLike.coe : C({z : ℂ | 0 < z.im}, ℂ) → ({z : ℂ | 0 < z.im} → ℂ))) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [show (⇑(UniformOnFun.ofFun 𝔖) ∘
          (DFunLike.coe : C({z : ℂ | 0 < z.im}, ℂ) → ({z : ℂ | 0 < z.im} → ℂ)))
          = ContinuousMap.toUniformOnFunIsCompact from rfl,
        ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous
      (CompactlyCoherentSpace.isCoherentWith (X := {z : ℂ | 0 < z.im}))
  set s : Set C({z : ℂ | 0 < z.im}, ℂ) := Set.range Gn with hs
  have hKcpt : IsCompact (closure s) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := 𝔖)
      (F := (DFunLike.coe : C({z : ℂ | 0 < z.im}, ℂ) → ({z : ℂ | 0 < z.im} → ℂ)))
      (fun K hK => hK) hce ?_ ?_
    · intro K hK
      have hu : ∀ pt : s, ∃ n : ℕ, Gn n = (pt : C({z : ℂ | 0 < z.im}, ℂ)) := by
        rintro ⟨_, n, rfl⟩; exact ⟨n, rfl⟩
      choose u hu using hu
      have heqfun : (fun n => (Gn n : {z : ℂ | 0 < z.im} → ℂ)) ∘ u
          = (DFunLike.coe : C({z : ℂ | 0 < z.im}, ℂ) → ({z : ℂ | 0 < z.im} → ℂ))
            ∘ (Subtype.val : s → C({z : ℂ | 0 < z.im}, ℂ)) := by
        funext pt; simp only [Function.comp_apply, hu pt]
      have hcomp := (heqcG.equicontinuousOn K).comp u
      rwa [heqfun] at hcomp
    · intro K hK x hx
      obtain ⟨Q, hQ, hQmem⟩ := hpt x
      exact ⟨Q, hQ, by rintro i ⟨n, rfl⟩; exact hQmem n⟩
  have hmem : ∀ n, Gn n ∈ closure s := fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨g₀, _hg₀, φ, hφ, htends⟩ := hKcpt.tendsto_subseq hmem
  -- Locally uniform convergence of the restricted maps.
  have hTLUsub : TendstoLocallyUniformly
      (fun i (x : {z : ℂ | 0 < z.im}) => F (φ i) (x : ℂ)) (⇑g₀) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp htends
  -- The limit carrier on the plane.
  set q0 : ℂ → ℂ := fun z => if hz : z ∈ {w : ℂ | 0 < w.im} then g₀ ⟨z, hz⟩ else 0 with hq0def
  have hcompeq : (q0 ∘ (Subtype.val : {z : ℂ | 0 < z.im} → ℂ)) = ⇑g₀ := by
    funext x
    obtain ⟨z, hz⟩ := x
    change q0 z = g₀ ⟨z, hz⟩
    rw [hq0def]
    exact dif_pos hz
  have hTLUon : TendstoLocallyUniformlyOn (fun n z => F (φ n) z) q0 atTop
      {z : ℂ | 0 < z.im} := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hcompeq]
    exact hTLUsub
  -- The limit is a quadratic differential.
  have hmeas0 : Measurable q0 := by
    rw [hq0def]
    exact Measurable.dite g₀.continuous.measurable measurable_const hUopen.measurableSet
  have hholo0 : DifferentiableOn ℂ q0 {z : ℂ | 0 < z.im} :=
    hTLUon.differentiableOn (Filter.Eventually.of_forall fun n => (F (φ n)).holo) hUopen
  have hauto0 : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      q0 (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q0 z := by
    intro γ hγ z hz
    have hzU : z ∈ {w : ℂ | 0 < w.im} := hz
    have hmU : moebiusMap γ z ∈ {w : ℂ | 0 < w.im} := moebiusMap_im_pos γ hz
    have h1 : Tendsto (fun n => F (φ n) (moebiusMap γ z)) atTop
        (𝓝 (q0 (moebiusMap γ z))) := hTLUon.tendsto_at hmU
    have h2 : Tendsto (fun n => moebiusDenom γ z ^ 4 * F (φ n) z) atTop
        (𝓝 (moebiusDenom γ z ^ 4 * q0 z)) :=
      (hTLUon.tendsto_at hzU).const_mul _
    have heqn : (fun n => F (φ n) (moebiusMap γ z))
        = fun n => moebiusDenom γ z ^ 4 * F (φ n) z := by
      funext n
      exact (F (φ n)).automorphy γ hγ z hz
    rw [heqn] at h1
    exact tendsto_nhds_unique h1 h2
  refine ⟨φ, ⟨q0, hmeas0, hholo0, hauto0⟩, hφ, ?_, ?_⟩
  · -- the mass bound, by Fatou
    have hptle : ∀ z : ℂ, ‖q0 z‖ₑ ≤ liminf (fun n => ‖F (φ n) z‖ₑ) atTop := by
      intro z
      by_cases hz : z ∈ {w : ℂ | 0 < w.im}
      · have h := (hTLUon.tendsto_at hz).enorm
        exact le_of_eq h.liminf_eq.symm
      · have h0 : q0 z = 0 := by rw [hq0def]; exact dif_neg hz
        rw [h0]
        simp
    calc (⟨q0, hmeas0, hholo0, hauto0⟩ : QuadraticDifferential Γ).l1Norm
        = ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, ‖q0 z‖ₑ := rfl
      _ ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
            liminf (fun n => ‖F (φ n) z‖ₑ) atTop := lintegral_mono hptle
      _ ≤ liminf (fun n => ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
            ‖F (φ n) z‖ₑ) atTop := lintegral_liminf_le fun n => (F (φ n)).measurable.enorm
      _ = liminf (fun n => (F (φ n)).l1Norm) atTop := rfl
      _ ≤ liminf (fun _ => A) atTop :=
          liminf_le_liminf (Filter.Eventually.of_forall fun n => hF (φ n))
      _ = A := liminf_const A
  · exact hTLUon

/-! ## The Hamilton pairing -/

/-- The **Hamilton pairing** of a plane coefficient with a quadratic differential: the
integral `∫ μ q` over the canonical Dirichlet domain at `i`, viewed inside the plane. -/
noncomputable def qdPairing (μ : ℂ → ℂ) (q : QuadraticDifferential Γ) : ℂ :=
  ∫ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, μ z * q z

/-- The Hamilton pairing is `ℂ`-homogeneous in the differential. -/
theorem qdPairing_smul (μ : ℂ → ℂ) (c : ℂ) (q : QuadraticDifferential Γ) :
    qdPairing μ (c • q) = c * qdPairing μ q := by
  unfold qdPairing
  calc ∫ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, μ z * (c • q) z
      = ∫ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, c * (μ z * q z) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by
          simp only [QuadraticDifferential.smul_apply]; ring)
    _ = c * ∫ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, μ z * q z :=
        integral_const_mul c _

/-- The `l1Norm` is absolutely homogeneous. -/
theorem l1Norm_smul (c : ℂ) (q : QuadraticDifferential Γ) :
    (c • q).l1Norm = ‖c‖ₑ * q.l1Norm := by
  unfold QuadraticDifferential.l1Norm
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  refine lintegral_congr fun z => ?_
  rw [QuadraticDifferential.smul_apply, enorm_mul]

/-- **Hölder bound for the Hamilton pairing**: a coefficient bounded by `m` almost
everywhere on the upper half plane pairs with a differential of finite mass to a value of
norm at most `m` times the mass. -/
theorem norm_qdPairing_le {μ : ℂ → ℂ} {m : ℝ} (hm0 : 0 ≤ m)
    (hμ : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖μ z‖ ≤ m)
    (q : QuadraticDifferential Γ) (hfin : q.l1Norm ≠ ⊤) :
    ‖qdPairing μ q‖ ≤ m * q.l1Norm.toReal := by
  have hDsub : UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I
      ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hμD := ae_restrict_of_ae_restrict_of_subset hDsub hμ
  have h2 : (∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, ‖μ z * q z‖ₑ)
      ≤ ENNReal.ofReal m * q.l1Norm := by
    rw [show q.l1Norm
        = ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, ‖q z‖ₑ from rfl,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hμD] with z hz
    rw [enorm_mul]
    exact mul_le_mul_left
      (by rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal hz) _
  have h1 : ‖qdPairing μ q‖
      ≤ (∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          ‖μ z * q z‖ₑ).toReal := by
    simpa only [ofReal_norm_eq_enorm] using
      norm_integral_le_lintegral_norm
        (μ := volume.restrict (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I))
        (fun z => μ z * q z)
  calc ‖qdPairing μ q‖
      ≤ (∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          ‖μ z * q z‖ₑ).toReal := h1
    _ ≤ (ENNReal.ofReal m * q.l1Norm).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h2
    _ = m * q.l1Norm.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm0]

/-- **Continuity of the Hamilton pairing under locally uniform convergence**: for a
bounded measurable coefficient, the pairing converges along any sequence of differentials
converging locally uniformly on the upper half plane. -/
theorem qdPairing_tendsto (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {μ : ℂ → ℂ} (hmeas : Measurable μ) {m : ℝ}
    (hμ : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖μ z‖ ≤ m)
    {F : ℕ → QuadraticDifferential Γ} {q : QuadraticDifferential Γ}
    (hconv : TendstoLocallyUniformlyOn (fun n z => F n z) (fun z => q z) atTop
      {z : ℂ | 0 < z.im}) :
    Tendsto (fun n => qdPairing μ (F n)) atTop (𝓝 (qdPairing μ q)) := by
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  unfold qdPairing
  set K : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hKdef
  have hKc : IsCompact K :=
    (isCompact_dirichletDomain hdense).image UpperHalfPlane.continuous_coe
  have hsub : K ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have huc : TendstoUniformlyOn (fun n z => F n z) (fun z => q z) atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp hconv K hsub hKc
  have hμK : ∀ᵐ z ∂(volume.restrict K), ‖μ z‖ ≤ m :=
    ae_restrict_of_ae_restrict_of_subset hsub hμ
  have hKmeas : MeasurableSet K := hKc.measurableSet
  have hbound_int : Integrable (fun z => m * (‖q z‖ + 1)) (volume.restrict K) :=
    (continuousOn_const.mul
      ((q.continuousOn_upper.mono hsub).norm.add continuousOn_const)).integrableOn_compact
      hKc
  have h_meas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun z => μ z * (F n) z) (volume.restrict K) :=
    Filter.Eventually.of_forall fun n => (hmeas.mul (F n).measurable).aestronglyMeasurable
  have h_bound : ∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict K),
      ‖μ z * (F n) z‖ ≤ m * (‖q z‖ + 1) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp huc 1 one_pos] with n hn
    filter_upwards [hμK, ae_restrict_mem hKmeas] with z hzμ hzK
    have hdist : ‖(F n) z - q z‖ < 1 := by
      have h := hn z hzK
      rw [dist_comm, dist_eq_norm] at h
      exact h
    have hFle : ‖(F n) z‖ ≤ ‖q z‖ + 1 := by
      have hdecomp : (F n) z = q z + ((F n) z - q z) := by ring
      calc ‖(F n) z‖ = ‖q z + ((F n) z - q z)‖ := by rw [← hdecomp]
        _ ≤ ‖q z‖ + ‖(F n) z - q z‖ := norm_add_le _ _
        _ ≤ ‖q z‖ + 1 := by linarith
    calc ‖μ z * (F n) z‖ = ‖μ z‖ * ‖(F n) z‖ := norm_mul _ _
      _ ≤ m * (‖q z‖ + 1) :=
          mul_le_mul hzμ hFle (norm_nonneg _) (le_trans (norm_nonneg _) hzμ)
  have h_lim : ∀ᵐ z ∂(volume.restrict K),
      Tendsto (fun n => μ z * (F n) z) atTop (𝓝 (μ z * q z)) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hzK
    exact (huc.tendsto_at hzK).const_mul (μ z)
  exact tendsto_integral_filter_of_dominated_convergence _ h_meas h_bound hbound_int h_lim

/-- **Attainment of the Hamilton supremum**: over a cocompact free Fuchsian base, the
real part of the pairing with a bounded measurable coefficient attains its supremum over
the `l1Norm` unit ball of quadratic differentials. -/
theorem exists_qdPairing_maximizer (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {μ : ℂ → ℂ} (hmeas : Measurable μ) {m : ℝ}
    (hμ : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖μ z‖ ≤ m) :
    ∃ q₀ : QuadraticDifferential Γ, q₀.l1Norm ≤ 1 ∧
      ∀ q : QuadraticDifferential Γ, q.l1Norm ≤ 1 →
        (qdPairing μ q).re ≤ (qdPairing μ q₀).re := by
  have hμ' : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖μ z‖ ≤ max m 0 :=
    hμ.mono fun z hz => le_trans hz (le_max_left m 0)
  have hm'0 : (0 : ℝ) ≤ max m 0 := le_max_right m 0
  set V : Set ℝ :=
    {r : ℝ | ∃ q : QuadraticDifferential Γ, q.l1Norm ≤ 1 ∧ (qdPairing μ q).re = r} with hV
  have hz0 : (0 : QuadraticDifferential Γ).l1Norm = 0 := by
    unfold QuadraticDifferential.l1Norm
    simp
  have hzp : qdPairing μ (0 : QuadraticDifferential Γ) = 0 := by
    unfold qdPairing
    simp
  have h0V : (0 : ℝ) ∈ V := by
    rw [hV]
    refine ⟨0, ?_, ?_⟩
    · simp [hz0]
    · rw [hzp]
      simp
  have hbdd : BddAbove V := by
    refine ⟨max m 0, ?_⟩
    rintro r hr
    rw [hV] at hr
    obtain ⟨q, hq1, rfl⟩ := hr
    have hfin : q.l1Norm ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
    have h3 : q.l1Norm.toReal ≤ 1 := by
      have h4 := ENNReal.toReal_mono ENNReal.one_ne_top hq1
      simpa using h4
    calc (qdPairing μ q).re ≤ ‖qdPairing μ q‖ := Complex.re_le_norm _
      _ ≤ max m 0 * q.l1Norm.toReal := norm_qdPairing_le hm'0 hμ' q hfin
      _ ≤ max m 0 * 1 := mul_le_mul_of_nonneg_left h3 hm'0
      _ = max m 0 := mul_one _
  obtain ⟨u, -, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sSup ⟨0, h0V⟩ hbdd
  simp only [hV, Set.mem_setOf_eq] at hu_mem
  choose Q hQ1 hQre using hu_mem
  obtain ⟨φ, q₀, hφ, hq₀1, hq₀conv⟩ :=
    exists_subseq_qd_tendstoLocallyUniformlyOn hΓ hfree hcc ENNReal.one_ne_top Q hQ1
  refine ⟨q₀, hq₀1, fun q hq => ?_⟩
  have hpair : Tendsto (fun n => qdPairing μ (Q (φ n))) atTop (𝓝 (qdPairing μ q₀)) :=
    qdPairing_tendsto hΓ hfree hcc hmeas hμ (F := fun n => Q (φ n)) hq₀conv
  have hre : Tendsto (fun n => (qdPairing μ (Q (φ n))).re) atTop
      (𝓝 ((qdPairing μ q₀).re)) :=
    (Complex.continuous_re.tendsto _).comp hpair
  have hre' : Tendsto (fun n => u (φ n)) atTop (𝓝 (sSup V)) :=
    hu_tendsto.comp hφ.tendsto_atTop
  have hq₀re : (qdPairing μ q₀).re = sSup V :=
    tendsto_nhds_unique (hre.congr fun n => hQre (φ n)) hre'
  have hmem : (qdPairing μ q).re ∈ V := by
    rw [hV]
    exact ⟨q, hq, rfl⟩
  calc (qdPairing μ q).re ≤ sSup V := le_csSup hbdd hmem
    _ = (qdPairing μ q₀).re := hq₀re.symm

end RiemannDynamics

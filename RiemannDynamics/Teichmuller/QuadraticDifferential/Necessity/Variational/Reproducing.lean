/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Schwarzian

/-!
# The reproducing formula for the quartic kernel

A holomorphic function on the lower half plane bounded in the Poincaré-weighted norm
`4y²|φ|` is reproduced from its reflection: pairing the coefficient
`c·(ζ − ζ̄)²·φ(ζ̄)` against the quartic kernel `(ζ − z)⁻⁴` over the upper half plane
returns `φ(z)`, for a single nonzero constant `c` independent of `φ`. This is the
Bers–Earle reproducing formula in the form Hamilton uses: it exhibits an explicit
bounded right inverse of the derivative of the Bers-type map at the origin, replacing
the Ahlfors–Weill section in the variational lemma.

* `exists_reproducing_constant` — the reproducing identity with its universal constant.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **The reproducing formula**: there is a nonzero universal constant `c` such that
every holomorphic function on the lower half plane with bounded Poincaré-weighted norm
is reproduced from its reflection through the quartic kernel. -/
theorem exists_reproducing_constant :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (φ : ℂ → ℂ) (B : ℝ),
      DifferentiableOn ℂ φ {z : ℂ | z.im < 0} →
      (∀ z : ℂ, z.im < 0 → (2 * z.im) ^ 2 * ‖φ z‖ ≤ B) →
      ∀ z : ℂ, z.im < 0 →
        (∫ ζ in {ζ : ℂ | 0 < ζ.im},
          (c * (ζ - starRingEnd ℂ ζ) ^ 2 * φ (starRingEnd ℂ ζ)) / (ζ - z) ^ 4)
          = φ z := by
  -- Cauchy's formula for the third derivative on circles inside the unit disk
  have cauchy3 : ∀ (s : ℝ) (w : ℂ) (F F1 F2 F3 : ℂ → ℂ), 0 < s → s < 1 → ‖w‖ < s →
    (∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt F (F1 ζ) ζ) →
    (∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt F1 (F2 ζ) ζ) →
    (∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt F2 (F3 ζ) ζ) →
    DifferentiableOn ℂ F3 (Metric.ball (0:ℂ) 1) →
    (∮ ζ in C(0, s), F ζ * ((ζ - w) ^ 4)⁻¹)
      = (Real.pi : ℂ) * Complex.I / 3 * F3 w := by
    intro s w F F1 F2 F3 hs0 hs1 hws hF hF1 hF2 hF3
    have hsub : Metric.sphere (0:ℂ) s ⊆ Metric.ball (0:ℂ) 1 := by
      intro ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      rw [mem_ball_zero_iff, hζ]
      exact hs1
    have hne : ∀ ζ ∈ Metric.sphere (0:ℂ) s, ζ - w ≠ 0 := by
      intro ζ hζ h0
      rw [mem_sphere_zero_iff_norm] at hζ
      rw [sub_eq_zero] at h0
      rw [h0] at hζ
      exact absurd hζ (ne_of_lt hws)
    -- derivative of the inverse powers
    have hinvd : ∀ (k : ℕ), 1 ≤ k → ∀ ζ : ℂ, ζ - w ≠ 0 →
        HasDerivAt (fun x : ℂ => ((x - w) ^ k)⁻¹) (-(k : ℂ) * ((ζ - w) ^ (k + 1))⁻¹) ζ := by
      intro k hk ζ hnz
      have hpow : HasDerivAt (fun x : ℂ => (x - w) ^ k) ((k : ℂ) * (ζ - w) ^ (k - 1)) ζ := by
        have h := (hasDerivAt_pow k (ζ - w)).comp ζ ((hasDerivAt_id ζ).sub_const w)
        simpa using h
      have hbase : (ζ - w) ^ (k + 1) * (ζ - w) ^ (k - 1) = ((ζ - w) ^ k) ^ 2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      have h := hpow.fun_inv (pow_ne_zero _ hnz)
      convert h using 1
      rw [← div_eq_mul_inv,
        div_eq_div_iff (pow_ne_zero _ hnz) (pow_ne_zero 2 (pow_ne_zero k hnz)), ← hbase]
      ring
    -- kernel continuity on the circle
    have hkc : ∀ (k : ℕ), ContinuousOn (fun ζ : ℂ => ((ζ - w) ^ k)⁻¹) (Metric.sphere (0:ℂ) s) := by
      intro k
      refine ContinuousOn.inv₀ (((continuousOn_id.sub continuousOn_const).pow k)) ?_
      intro ζ hζ
      exact pow_ne_zero k (hne ζ hζ)
    -- the integration-by-parts step
    have step : ∀ (u u' : ℂ → ℂ) (k : ℕ), 1 ≤ k →
        (∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt u (u' ζ) ζ) →
        ContinuousOn u' (Metric.sphere (0:ℂ) s) →
        (∮ ζ in C(0, s), u ζ * ((ζ - w) ^ (k + 1))⁻¹)
          = (k : ℂ)⁻¹ * ∮ ζ in C(0, s), u' ζ * ((ζ - w) ^ k)⁻¹ := by
      intro u u' k hk hu hu'c
      have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have huc : ContinuousOn u (Metric.sphere (0:ℂ) s) := fun ζ hζ =>
        ((hu ζ (hsub hζ)).differentiableAt.continuousAt).continuousWithinAt
      have hzero : (∮ ζ in C(0, s),
          (u' ζ * (-(k:ℂ)⁻¹ * ((ζ - w) ^ k)⁻¹) + u ζ * ((ζ - w) ^ (k + 1))⁻¹)) = 0 := by
        refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt
          (f := fun x : ℂ => u x * (-(k:ℂ)⁻¹ * ((x - w) ^ k)⁻¹)) hs0.le fun ζ hζ => ?_
        have hconst : HasDerivAt (fun x : ℂ => -(k:ℂ)⁻¹ * ((x - w) ^ k)⁻¹)
            (-(k:ℂ)⁻¹ * (-(k : ℂ) * ((ζ - w) ^ (k + 1))⁻¹)) ζ :=
          (hinvd k hk ζ (hne ζ hζ)).const_mul (-(k:ℂ)⁻¹)
        have hprod := (hu ζ (hsub hζ)).fun_mul hconst
        have hval : u' ζ * (-(k:ℂ)⁻¹ * ((ζ - w) ^ k)⁻¹)
            + u ζ * (-(k:ℂ)⁻¹ * (-(k : ℂ) * ((ζ - w) ^ (k + 1))⁻¹))
            = u' ζ * (-(k:ℂ)⁻¹ * ((ζ - w) ^ k)⁻¹) + u ζ * ((ζ - w) ^ (k + 1))⁻¹ := by
          field_simp
        rw [hval] at hprod
        exact hprod.hasDerivWithinAt
      have hi1 : CircleIntegrable (fun ζ => u' ζ * (-(k:ℂ)⁻¹ * ((ζ - w) ^ k)⁻¹)) 0 s :=
        ContinuousOn.circleIntegrable hs0.le (hu'c.mul (continuousOn_const.mul (hkc k)))
      have hi2 : CircleIntegrable (fun ζ => u ζ * ((ζ - w) ^ (k + 1))⁻¹) 0 s :=
        ContinuousOn.circleIntegrable hs0.le (huc.mul (hkc (k + 1)))
      rw [circleIntegral.integral_add hi1 hi2] at hzero
      have hpull : (∮ ζ in C(0, s), u' ζ * (-(k:ℂ)⁻¹ * ((ζ - w) ^ k)⁻¹))
          = (-(k:ℂ)⁻¹) • ∮ ζ in C(0, s), u' ζ * ((ζ - w) ^ k)⁻¹ := by
        rw [← circleIntegral.integral_smul]
        congr 1
        funext ζ
        rw [smul_eq_mul]
        ring
      rw [hpull, smul_eq_mul] at hzero
      linear_combination hzero
    -- continuity of the intermediate derivatives on the circle
    have hF1c : ContinuousOn F1 (Metric.sphere (0:ℂ) s) := fun ζ hζ =>
      ((hF1 ζ (hsub hζ)).differentiableAt.continuousAt).continuousWithinAt
    have hF2c : ContinuousOn F2 (Metric.sphere (0:ℂ) s) := fun ζ hζ =>
      ((hF2 ζ (hsub hζ)).differentiableAt.continuousAt).continuousWithinAt
    have hF3c : ContinuousOn F3 (Metric.sphere (0:ℂ) s) :=
      hF3.continuousOn.mono hsub
    -- chain the three steps
    have s3 : (∮ ζ in C(0, s), F ζ * ((ζ - w) ^ 4)⁻¹)
        = ((3 : ℕ) : ℂ)⁻¹ * ∮ ζ in C(0, s), F1 ζ * ((ζ - w) ^ 3)⁻¹ :=
      step F F1 3 (by norm_num) hF hF1c
    have s2 : (∮ ζ in C(0, s), F1 ζ * ((ζ - w) ^ 3)⁻¹)
        = ((2 : ℕ) : ℂ)⁻¹ * ∮ ζ in C(0, s), F2 ζ * ((ζ - w) ^ 2)⁻¹ :=
      step F1 F2 2 (by norm_num) hF1 hF2c
    have s1 : (∮ ζ in C(0, s), F2 ζ * ((ζ - w) ^ 2)⁻¹)
        = ((1 : ℕ) : ℂ)⁻¹ * ∮ ζ in C(0, s), F3 ζ * ((ζ - w) ^ 1)⁻¹ :=
      step F2 F3 1 (by norm_num) hF2 hF3c
    -- the classical Cauchy formula for F3
    have hfin : (∮ ζ in C(0, s), F3 ζ * ((ζ - w) ^ 1)⁻¹)
        = (2 * (Real.pi : ℂ) * Complex.I) • F3 w := by
      have heq : (fun ζ : ℂ => F3 ζ * ((ζ - w) ^ 1)⁻¹) = fun ζ : ℂ => (ζ - w)⁻¹ • F3 ζ := by
        funext ζ
        rw [pow_one, smul_eq_mul]
        ring
      rw [heq]
      exact DifferentiableOn.circleIntegral_sub_inv_smul
        (hF3.mono (Metric.closedBall_subset_ball hs1)) (mem_ball_zero_iff.mpr hws)
    rw [s3, s2, s1, hfin, smul_eq_mul]
    push_cast
    ring
  -- the weighted Bergman reproducing identity of the unit disk
  have disk_core : ∀ (g : ℂ → ℂ) (B' : ℝ) (t : ℂ), ‖t‖ < 1 →
    DifferentiableOn ℂ g (Metric.ball 0 1) →
    (∀ v ∈ Metric.ball (0:ℂ) 1, (1 - ‖v‖ ^ 2) ^ 2 * ‖g v‖ ≤ B') →
    (∫ v in Metric.ball (0:ℂ) 1,
        (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * g v / (1 - starRingEnd ℂ v * t) ^ 4)
      = (Real.pi : ℂ) / 3 * g t := by
    intro g B' t ht hgd hgB
    have hsmul : ∀ (r : ℝ) (x : ℂ), r • x = (r : ℂ) * x := fun _ _ => rfl
    -- basic positivity and kernel bounds
    have hB'0 : 0 ≤ B' := by
      have h0 := hgB 0 (by simp)
      have : (0:ℝ) ≤ (1 - ‖(0:ℂ)‖ ^ 2) ^ 2 * ‖g 0‖ := by positivity
      linarith
    have ht1 : 0 < 1 - ‖t‖ := by
      linarith
    have hkerne : ∀ v : ℂ, ‖v‖ < 1 → 1 - starRingEnd ℂ v * t ≠ 0 := by
      intro v hv h0
      have h1 : ‖starRingEnd ℂ v * t‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg t, norm_nonneg v]
      rw [sub_eq_zero] at h0
      rw [← h0] at h1
      simp at h1
    have hkb : ∀ v : ℂ, ‖v‖ < 1 → 1 - ‖t‖ ≤ ‖1 - starRingEnd ℂ v * t‖ := by
      intro v hv
      have h2 : ‖(1:ℂ)‖ - ‖starRingEnd ℂ v * t‖ ≤ ‖1 - starRingEnd ℂ v * t‖ :=
        norm_sub_norm_le _ _
      rw [norm_mul, Complex.norm_conj, norm_one] at h2
      nlinarith [norm_nonneg t, norm_nonneg v]
    -- the analytic derivative chain of g
    have hga : AnalyticOnNhd ℂ g (Metric.ball 0 1) := hgd.analyticOnNhd Metric.isOpen_ball
    set g1 := deriv g with hg1def
    set g2 := deriv g1 with hg2def
    set g3 := deriv g2 with hg3def
    have hg1a : AnalyticOnNhd ℂ g1 (Metric.ball 0 1) := hga.deriv
    have hg2a : AnalyticOnNhd ℂ g2 (Metric.ball 0 1) := hg1a.deriv
    have hg3a : AnalyticOnNhd ℂ g3 (Metric.ball 0 1) := hg2a.deriv
    have hDg0 : ∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt g (g1 ζ) ζ := fun ζ hζ =>
      (hga ζ hζ).differentiableAt.hasDerivAt
    have hDg1 : ∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt g1 (g2 ζ) ζ := fun ζ hζ =>
      (hg1a ζ hζ).differentiableAt.hasDerivAt
    have hDg2 : ∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt g2 (g3 ζ) ζ := fun ζ hζ =>
      (hg2a ζ hζ).differentiableAt.hasDerivAt
    -- the integrand of the circle Cauchy formula and its derivative chain
    set h0 : ℂ → ℂ := fun ζ => g ζ * ζ ^ 3 with hh0def
    set h1 : ℂ → ℂ := fun ζ => g1 ζ * ζ ^ 3 + g ζ * (3 * ζ ^ 2) with hh1def
    set h2 : ℂ → ℂ := fun ζ => g2 ζ * ζ ^ 3 + 6 * ζ ^ 2 * g1 ζ + 6 * ζ * g ζ with hh2def
    set h3 : ℂ → ℂ := fun ζ => g3 ζ * ζ ^ 3 + 9 * ζ ^ 2 * g2 ζ + 18 * ζ * g1 ζ + 6 * g ζ
      with hh3def
    have hh0 : ∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt h0 (h1 ζ) ζ := by
      intro ζ hζ
      have h := (hDg0 ζ hζ).fun_mul (hasDerivAt_pow 3 ζ)
      exact h.congr_deriv (by rw [hh1def]; push_cast; ring)
    have hh1 : ∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt h1 (h2 ζ) ζ := by
      intro ζ hζ
      have h := ((hDg1 ζ hζ).fun_mul (hasDerivAt_pow 3 ζ)).add
        ((hDg0 ζ hζ).fun_mul ((hasDerivAt_pow 2 ζ).const_mul (3:ℂ)))
      exact h.congr_deriv (by rw [hh2def]; push_cast; ring)
    have hh2 : ∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt h2 (h3 ζ) ζ := by
      intro ζ hζ
      have h := (((hDg2 ζ hζ).fun_mul (hasDerivAt_pow 3 ζ)).add
        (((hasDerivAt_pow 2 ζ).const_mul (6:ℂ)).fun_mul (hDg1 ζ hζ))).add
        (((hasDerivAt_id ζ).const_mul (6:ℂ)).fun_mul (hDg0 ζ hζ))
      exact h.congr_deriv (by rw [hh3def]; simp only [id_eq]; push_cast; ring)
    have hh3d : DifferentiableOn ℂ h3 (Metric.ball (0:ℂ) 1) := by
      rw [hh3def]
      refine ((((hg3a.differentiableOn.mul ?_).add ?_).add ?_).add ?_)
      · exact (differentiable_pow 3).differentiableOn
      · exact ((differentiable_const _).mul (differentiable_pow 2)).differentiableOn.mul
          hg2a.differentiableOn
      · exact ((differentiable_const _).mul differentiable_id).differentiableOn.mul
          hg1a.differentiableOn
      · exact hgd.const_mul 6
    -- the disk integrand, its bound, and its continuity
    set W : ℂ → ℂ := fun v => (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * g v / (1 - starRingEnd ℂ v * t) ^ 4
      with hWdef
    have hWnorm : ∀ v ∈ Metric.ball (0:ℂ) 1, ‖W v‖ ≤ B' / (1 - ‖t‖) ^ 4 := by
      intro v hv
      have hv' : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
      have h1 : ‖W v‖ = (1 - ‖v‖ ^ 2) ^ 2 * ‖g v‖ / ‖1 - starRingEnd ℂ v * t‖ ^ 4 := by
        rw [hWdef]
        rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      rw [h1]
      exact div_le_div₀ hB'0 (hgB v hv) (by positivity)
        (pow_le_pow_left₀ ht1.le (hkb v hv') 4)
    have hWc : ContinuousOn W (Metric.ball (0:ℂ) 1) := by
      rw [hWdef]
      apply ContinuousOn.div
      · exact (Complex.continuous_ofReal.comp
          ((continuous_const.sub (continuous_norm.pow 2)).pow 2)).continuousOn.mul
          hga.continuousOn
      · exact ((continuous_const.sub (Complex.continuous_conj.mul continuous_const)).pow
          4).continuousOn
      · intro v hv
        exact pow_ne_zero 4 (hkerne v (mem_ball_zero_iff.mp hv))
    -- polar coordinates and the boxed double integral
    set T : Set (ℝ × ℝ) := Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi with hT
    have hTmeas : MeasurableSet T := measurableSet_Ioo.prod measurableSet_Ioo
    have hTsub : T ⊆ polarCoord.target := by
      rintro ⟨s, θ⟩ hp
      obtain ⟨hs, hθ⟩ := Set.mem_prod.mp hp
      rw [polarCoord_target]
      exact Set.mem_prod.mpr ⟨hs.1, hθ⟩
    have hpolar := Complex.integral_comp_polarCoord_symm ((Metric.ball (0:ℂ) 1).indicator W)
    have hind : ∫ v : ℂ, (Metric.ball (0:ℂ) 1).indicator W v = ∫ v in Metric.ball (0:ℂ) 1, W v :=
      integral_indicator measurableSet_ball
    have hptw : ∀ p ∈ polarCoord.target,
        p.1 • (Metric.ball (0:ℂ) 1).indicator W (Complex.polarCoord.symm p)
          = T.indicator (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) * W (Complex.polarCoord.symm q)) p := by
      rintro ⟨s, θ⟩ hp
      rw [polarCoord_target] at hp
      obtain ⟨hs, hθ⟩ := Set.mem_prod.mp hp
      have hs0 : (0:ℝ) < s := hs
      have hnorm : ‖Complex.polarCoord.symm (s, θ)‖ = s := by
        rw [Complex.norm_polarCoord_symm]
        exact abs_of_pos hs0
      by_cases hsr : s < 1
      · have hmem : Complex.polarCoord.symm (s, θ) ∈ Metric.ball (0:ℂ) 1 := by
          rw [mem_ball_zero_iff, hnorm]; exact hsr
        have hmemT : ((s, θ) : ℝ × ℝ) ∈ T := Set.mem_prod.mpr ⟨⟨hs0, hsr⟩, hθ⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemT]
        exact hsmul _ _
      · have hnmem : Complex.polarCoord.symm (s, θ) ∉ Metric.ball (0:ℂ) 1 := by
          rw [mem_ball_zero_iff, hnorm]; exact hsr
        have hnmemT : ((s, θ) : ℝ × ℝ) ∉ T := fun hmemT => hsr (Set.mem_prod.mp hmemT).1.2
        rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmemT]
        simp
    have hbox : (∫ p in polarCoord.target,
          p.1 • (Metric.ball (0:ℂ) 1).indicator W (Complex.polarCoord.symm p))
        = ∫ p in T, ((p.1 : ℝ) : ℂ) * W (Complex.polarCoord.symm p) := by
      rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hptw,
        setIntegral_indicator hTmeas, Set.inter_eq_self_of_subset_right hTsub]
    -- Fubini
    have hmeq : (volume.restrict (Set.Ioo (0:ℝ) 1)).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) = volume.restrict T := by
      rw [hT, Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hsymm_cont : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
      have heq : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
          = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
        funext p
        exact Complex.polarCoord_symm_apply p
      rw [heq]
      fun_prop
    have hmapsTo : Set.MapsTo (fun p : ℝ × ℝ => Complex.polarCoord.symm p) T
        (Metric.ball (0:ℂ) 1) := by
      rintro ⟨s, θ⟩ hp
      obtain ⟨hs, hθ⟩ := Set.mem_prod.mp hp
      have hnorm : ‖Complex.polarCoord.symm (s, θ)‖ = s := by
        rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hs.1
      rw [mem_ball_zero_iff, hnorm]
      exact hs.2
    have haes : AEStronglyMeasurable
        (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) * W (Complex.polarCoord.symm q))
        (volume.restrict T) := by
      apply ContinuousOn.aestronglyMeasurable _ hTmeas
      exact ((Complex.continuous_ofReal.comp continuous_fst).continuousOn).mul
        (hWc.comp hsymm_cont.continuousOn hmapsTo)
    have hIble : Integrable (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) * W (Complex.polarCoord.symm q))
        (volume.restrict T) := by
      haveI hfinm : IsFiniteMeasure (volume.restrict T) := by
        constructor
        rw [Measure.restrict_apply_univ, hT, Measure.volume_eq_prod, Measure.prod_prod,
          Real.volume_Ioo, Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      apply Integrable.mono' (integrable_const (B' / (1 - ‖t‖) ^ 4)) haes
      filter_upwards [ae_restrict_mem hTmeas] with q hq
      obtain ⟨hs, hθ⟩ := Set.mem_prod.mp hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
      calc q.1 * ‖W (Complex.polarCoord.symm q)‖
          ≤ 1 * (B' / (1 - ‖t‖) ^ 4) :=
            mul_le_mul hs.2.le (hWnorm _ (hmapsTo hq)) (norm_nonneg _) zero_le_one
        _ = B' / (1 - ‖t‖) ^ 4 := one_mul _
    have hfub : (∫ p in T, ((p.1 : ℝ) : ℂ) * W (Complex.polarCoord.symm p))
        = ∫ s in Set.Ioo (0:ℝ) 1, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)) := by
      rw [← hmeq]
      exact integral_prod _ (hmeq ▸ hIble)
    have hchain : (∫ v in Metric.ball (0:ℂ) 1, W v)
        = ∫ s in Set.Ioo (0:ℝ) 1, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)) := by
      calc (∫ v in Metric.ball (0:ℂ) 1, W v)
          = ∫ v : ℂ, (Metric.ball (0:ℂ) 1).indicator W v := hind.symm
        _ = ∫ p in polarCoord.target,
              p.1 • (Metric.ball (0:ℂ) 1).indicator W (Complex.polarCoord.symm p) := hpolar.symm
        _ = ∫ p in T, ((p.1 : ℝ) : ℂ) * W (Complex.polarCoord.symm p) := hbox
        _ = ∫ s in Set.Ioo (0:ℝ) 1, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
              ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)) := hfub
    -- the inner circle integral at each radius
    have hinner : ∀ s ∈ Set.Ioo (0:ℝ) 1,
        (∫ θ in Set.Ioo (-Real.pi) Real.pi, ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)))
          = ((Real.pi : ℂ) / 3) * (((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t)) := by
      intro s hs
      obtain ⟨hs0, hs1⟩ := hs
      have hcm : ∀ θ : ℝ, Complex.polarCoord.symm (s, θ) = circleMap 0 s θ := by
        intro θ
        rw [Complex.polarCoord_symm_apply]
        simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hnormc : ∀ θ : ℝ, ‖circleMap 0 s θ‖ = s := by
        intro θ
        rw [norm_circleMap_zero, abs_of_pos hs0]
      set KK : ℝ → ℂ := fun θ => g (circleMap 0 s θ)
        / (1 - starRingEnd ℂ (circleMap 0 s θ) * t) ^ 4 with hKKdef
      have hWval : ∀ θ : ℝ, ((s : ℝ) : ℂ) * W (circleMap 0 s θ)
          = ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * KK θ := by
        intro θ
        rw [hWdef, hKKdef]
        simp only [hnormc θ]
        push_cast
        ring
      have hstep1 : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)))
          = ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi, KK θ := by
        calc (∫ θ in Set.Ioo (-Real.pi) Real.pi, ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)))
            = ∫ θ in Set.Ioo (-Real.pi) Real.pi, ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * KK θ :=
              setIntegral_congr_fun measurableSet_Ioo fun θ _ => by rw [hcm θ, hWval θ]
          _ = ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi, KK θ :=
              integral_const_mul _ _
      have hper : Function.Periodic KK (2 * Real.pi) := by
        intro θ
        rw [hKKdef]
        simp only [periodic_circleMap 0 s θ]
      have hIoo : (∫ θ in Set.Ioo (-Real.pi) Real.pi, KK θ)
          = ∫ θ in (0:ℝ)..2 * Real.pi, KK θ := by
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
        have h := hper.intervalIntegral_add_eq (-Real.pi) 0
        have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
        have h3' : (0:ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
        rw [h2, h3'] at h
        exact h
      have hζne : ∀ θ : ℝ, circleMap 0 s θ ≠ 0 := by
        intro θ h0
        have := hnormc θ
        rw [h0] at this
        simp at this
        linarith
      have hpole : ∀ θ : ℝ, circleMap 0 s θ - (s : ℂ) ^ 2 * t ≠ 0 := by
        intro θ h0
        have h1 : ‖(s : ℂ) ^ 2 * t‖ < s := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
          nlinarith [norm_nonneg t]
        rw [sub_eq_zero] at h0
        rw [← h0, hnormc θ] at h1
        exact lt_irrefl s h1
      have hmc : ∀ θ : ℝ, circleMap 0 s θ * starRingEnd ℂ (circleMap 0 s θ) = (s : ℂ) ^ 2 := by
        intro θ
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnormc θ]
        push_cast
        ring
      have hw : ‖(s : ℂ) ^ 2 * t‖ < s := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        nlinarith [norm_nonneg t]
      have hmatch : (∫ θ in (0:ℝ)..2 * Real.pi, KK θ)
          = ∮ ζ in C(0, s), (-Complex.I) • (h0 ζ * ((ζ - (s : ℂ) ^ 2 * t) ^ 4)⁻¹) := by
        simp only [circleIntegral]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        rw [deriv_circleMap]
        simp only [hKKdef, hh0def]
        have h4 : 1 - starRingEnd ℂ (circleMap 0 s θ) * t
            = (circleMap 0 s θ - (s : ℂ) ^ 2 * t) / circleMap 0 s θ := by
          rw [eq_div_iff (hζne θ)]
          linear_combination (-t) * hmc θ
        rw [h4, smul_eq_mul, smul_eq_mul]
        have hI : ∀ X : ℂ, circleMap 0 s θ * Complex.I * (-Complex.I * X)
            = circleMap 0 s θ * X := by
          intro X
          linear_combination (-(circleMap 0 s θ) * X) * Complex.I_sq
        rw [hI]
        field_simp [hζne θ, hpole θ]
      have hC := cauchy3 s ((s : ℂ) ^ 2 * t) h0 h1 h2 h3 hs0 hs1 hw hh0 hh1 hh2 hh3d
      have hsm2 : (∮ ζ in C(0, s), (-Complex.I) • (h0 ζ * ((ζ - (s : ℂ) ^ 2 * t) ^ 4)⁻¹))
          = (-Complex.I) • ∮ ζ in C(0, s), h0 ζ * ((ζ - (s : ℂ) ^ 2 * t) ^ 4)⁻¹ :=
        circleIntegral.integral_smul _ _ _ _
      rw [hstep1, hIoo, hmatch, hsm2, hC, smul_eq_mul]
      linear_combination (-((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * ((Real.pi : ℂ) / 3)
        * h3 ((s : ℂ) ^ 2 * t)) * Complex.I_sq
    -- pull the constant through the radial integral
    have houter : (∫ s in Set.Ioo (0:ℝ) 1, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)))
        = ((Real.pi : ℂ) / 3) * ∫ s in Set.Ioo (0:ℝ) 1,
            ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t) := by
      calc (∫ s in Set.Ioo (0:ℝ) 1, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((s : ℝ) : ℂ) * W (Complex.polarCoord.symm (s, θ)))
          = ∫ s in Set.Ioo (0:ℝ) 1, ((Real.pi : ℂ) / 3)
              * (((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t)) :=
            setIntegral_congr_fun measurableSet_Ioo hinner
        _ = ((Real.pi : ℂ) / 3) * ∫ s in Set.Ioo (0:ℝ) 1,
              ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t) := integral_const_mul _ _
    -- radial helper functions and their derivatives
    have hmemσ : ∀ σ : ℝ, σ ∈ Set.uIcc (0:ℝ) 1 → (σ : ℂ) * t ∈ Metric.ball (0:ℂ) 1 := by
      intro σ hσ
      rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hσ
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |σ| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
      nlinarith [norm_nonneg t, abs_nonneg σ]
    have hmt : Set.MapsTo (fun σ : ℝ => (σ : ℂ) * t) (Set.uIcc (0:ℝ) 1)
        (Metric.ball (0:ℂ) 1) := fun σ hσ => hmemσ σ hσ
    have hcσt : Continuous fun σ : ℝ => (σ : ℂ) * t := by fun_prop
    have hcomp : ∀ (F F' : ℂ → ℂ), (∀ ζ ∈ Metric.ball (0:ℂ) 1, HasDerivAt F (F' ζ) ζ) →
        ∀ σ : ℝ, σ ∈ Set.uIcc (0:ℝ) 1 →
          HasDerivAt (fun x : ℝ => F ((x : ℂ) * t)) (F' ((σ : ℂ) * t) * t) σ := by
      intro F F' hF σ hσ
      have hi : HasDerivAt (fun w : ℂ => F (w * t)) (F' ((σ : ℂ) * t) * t) (σ : ℂ) := by
        have h := (hF _ (hmemσ σ hσ)).comp (σ : ℂ) ((hasDerivAt_id ((σ : ℂ))).mul_const t)
        simpa [Function.comp] using h
      exact hi.comp_ofReal
    have hpowR : ∀ (n : ℕ) (σ : ℝ), HasDerivAt (fun x : ℝ => ((x : ℂ)) ^ n)
        ((n : ℂ) * (σ : ℂ) ^ (n - 1)) σ := fun n σ => (hasDerivAt_pow n ((σ : ℂ))).comp_ofReal
    set Hr : ℝ → ℂ := fun σ => (σ : ℂ) ^ 3 * g ((σ : ℂ) * t) with hHrdef
    set H1r : ℝ → ℂ := fun σ => 3 * (σ : ℂ) ^ 2 * g ((σ : ℂ) * t)
      + (σ : ℂ) ^ 3 * (g1 ((σ : ℂ) * t) * t) with hH1rdef
    set H2r : ℝ → ℂ := fun σ => 6 * (σ : ℂ) * g ((σ : ℂ) * t)
      + 6 * (σ : ℂ) ^ 2 * (g1 ((σ : ℂ) * t) * t) + (σ : ℂ) ^ 3 * (g2 ((σ : ℂ) * t) * t ^ 2)
      with hH2rdef
    have hDHr : ∀ σ ∈ Set.uIcc (0:ℝ) 1, HasDerivAt Hr (H1r σ) σ := by
      intro σ hσ
      have h := (hpowR 3 σ).fun_mul (hcomp g g1 hDg0 σ hσ)
      exact h.congr_deriv (by rw [hH1rdef]; push_cast; ring)
    have hDH1r : ∀ σ ∈ Set.uIcc (0:ℝ) 1, HasDerivAt H1r (H2r σ) σ := by
      intro σ hσ
      have h := (((hpowR 2 σ).const_mul (3:ℂ)).fun_mul (hcomp g g1 hDg0 σ hσ)).add
        ((hpowR 3 σ).fun_mul ((hcomp g1 g2 hDg1 σ hσ).mul_const t))
      exact h.congr_deriv (by rw [hH2rdef]; push_cast; ring)
    have hDH2r : ∀ σ ∈ Set.uIcc (0:ℝ) 1, HasDerivAt H2r (h3 ((σ : ℂ) * t)) σ := by
      intro σ hσ
      have hcast : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) (((1 : ℝ) : ℂ)) σ :=
        HasDerivAt.ofReal_comp (hasDerivAt_id σ)
      have h := (((hcast.const_mul (6:ℂ)).fun_mul (hcomp g g1 hDg0 σ hσ)).add
        (((hpowR 2 σ).const_mul (6:ℂ)).fun_mul ((hcomp g1 g2 hDg1 σ hσ).mul_const t))).add
        ((hpowR 3 σ).fun_mul ((hcomp g2 g3 hDg2 σ hσ).mul_const (t ^ 2)))
      refine h.congr_deriv ?_
      rw [hh3def]
      push_cast
      ring
    -- interval integrability of the pieces
    have hcball : ∀ (F : ℂ → ℂ), ContinuousOn F (Metric.ball (0:ℂ) 1) →
        ContinuousOn (fun σ : ℝ => F ((σ : ℂ) * t)) (Set.uIcc (0:ℝ) 1) := fun F hF =>
      hF.comp hcσt.continuousOn hmt
    have hcastc : Continuous (fun σ : ℝ => ((σ : ℝ) : ℂ)) := Complex.continuous_ofReal
    have hH1rint : IntervalIntegrable H1r volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [hH1rdef]
      apply ContinuousOn.add
      · exact (continuous_const.mul (hcastc.pow 2)).continuousOn.mul (hcball g hga.continuousOn)
      · exact (hcastc.pow 3).continuousOn.mul
          ((hcball g1 hg1a.continuousOn).mul continuousOn_const)
    have hH2rint : IntervalIntegrable H2r volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [hH2rdef]
      apply ContinuousOn.add
      · apply ContinuousOn.add
        · exact (continuous_const.mul hcastc).continuousOn.mul (hcball g hga.continuousOn)
        · exact (continuous_const.mul (hcastc.pow 2)).continuousOn.mul
            ((hcball g1 hg1a.continuousOn).mul continuousOn_const)
      · exact (hcastc.pow 3).continuousOn.mul
          ((hcball g2 hg2a.continuousOn).mul continuousOn_const)
    have hH3int : IntervalIntegrable (fun σ : ℝ => h3 ((σ : ℂ) * t)) volume 0 1 :=
      ContinuousOn.intervalIntegrable (hcball h3 hh3d.continuousOn)
    -- the polynomial weights of the two integrations by parts
    set U2 : ℝ → ℂ := fun σ => ((1 - σ : ℝ) : ℂ) ^ 2 with hU2def
    set U1 : ℝ → ℂ := fun σ => -(2 * ((1 - σ : ℝ) : ℂ)) with hU1def
    have hin1 : ∀ σ : ℝ, HasDerivAt (fun x : ℝ => ((1 - x : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) σ := by
      intro σ
      apply HasDerivAt.ofReal_comp
      simpa using (hasDerivAt_id σ).const_sub 1
    have hDU2 : ∀ σ ∈ Set.uIcc (0:ℝ) 1, HasDerivAt U2 (U1 σ) σ := by
      intro σ hσ
      have h := (hin1 σ).fun_pow 2
      exact h.congr_deriv (by rw [hU1def]; push_cast; ring)
    have hDU1 : ∀ σ ∈ Set.uIcc (0:ℝ) 1, HasDerivAt U1 ((2:ℂ)) σ := by
      intro σ hσ
      have h := ((hin1 σ).const_mul (2:ℂ)).neg
      exact h.congr_deriv (by push_cast; ring)
    have hU1int : IntervalIntegrable U1 volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [hU1def]
      fun_prop
    have h2int : IntervalIntegrable (fun _ : ℝ => (2:ℂ)) volume 0 1 := intervalIntegrable_const
    -- the two integrations by parts and the fundamental theorem of calculus
    have hIBP1 : (∫ σ in (0:ℝ)..1, U2 σ * h3 ((σ : ℂ) * t))
        = U2 1 * H2r 1 - U2 0 * H2r 0 - ∫ σ in (0:ℝ)..1, U1 σ * H2r σ :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul hDU2 hDH2r hU1int hH3int
    have hIBP2 : (∫ σ in (0:ℝ)..1, U1 σ * H2r σ)
        = U1 1 * H1r 1 - U1 0 * H1r 0 - ∫ σ in (0:ℝ)..1, (2:ℂ) * H1r σ :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul hDU1 hDH1r h2int hH2rint
    have hFTC : (∫ σ in (0:ℝ)..1, H1r σ) = Hr 1 - Hr 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hDHr hH1rint
    -- boundary values
    have hU2_1 : U2 1 = 0 := by rw [hU2def]; norm_num
    have hU2_0 : U2 0 = 1 := by rw [hU2def]; norm_num
    have hU1_1 : U1 1 = 0 := by rw [hU1def]; norm_num
    have hH2r_0 : H2r 0 = 0 := by rw [hH2rdef]; norm_num
    have hH1r_0 : H1r 0 = 0 := by rw [hH1rdef]; norm_num
    have hHr_0 : Hr 0 = 0 := by rw [hHrdef]; norm_num
    have hHr_1 : Hr 1 = g t := by rw [hHrdef]; norm_num
    -- the substitution s ↦ s²
    set G : ℝ → ℂ := fun σ => (2⁻¹ : ℂ) * (U2 σ * h3 ((σ : ℂ) * t)) with hGdef
    have hGc : ContinuousOn G (Set.uIcc (0:ℝ) 1) := by
      rw [hGdef]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.mul
      · rw [hU2def]; fun_prop
      · exact hcball h3 hh3d.continuousOn
    have himg : (fun s : ℝ => s ^ 2) '' Set.uIcc (0:ℝ) 1 ⊆ Set.uIcc (0:ℝ) 1 := by
      rintro x ⟨y, hy, rfl⟩
      rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hy ⊢
      exact ⟨by positivity, by nlinarith [hy.1, hy.2]⟩
    have hsubst : (∫ x in (0:ℝ)..1, 2 * ((x : ℝ) : ℂ) * G (x ^ 2)) = ∫ u in (0:ℝ)..1, G u := by
      calc (∫ x in (0:ℝ)..1, 2 * ((x : ℝ) : ℂ) * G (x ^ 2))
          = ∫ x in (0:ℝ)..1, (fun s : ℝ => 2 * s) x • (G ∘ fun s : ℝ => s ^ 2) x := by
            refine intervalIntegral.integral_congr fun x _ => ?_
            change 2 * ((x : ℝ) : ℂ) * G (x ^ 2) = (2 * x) • G (x ^ 2)
            rw [hsmul]
            push_cast
            ring
        _ = ∫ u in (fun s : ℝ => s ^ 2) (0:ℝ)..(fun s : ℝ => s ^ 2) (1:ℝ), G u :=
            intervalIntegral.integral_deriv_smul_comp'' (a := (0:ℝ)) (b := 1)
              (f := fun s : ℝ => s ^ 2) (f' := fun s : ℝ => 2 * s) (g := G)
              ((continuous_pow 2).continuousOn)
              (fun x _ =>
                ((hasDerivAt_pow 2 x).congr_deriv (by push_cast; ring)).hasDerivWithinAt)
              ((continuous_const.mul continuous_id).continuousOn)
              (hGc.mono himg)
        _ = ∫ u in (0:ℝ)..1, G u := by norm_num
    -- the radial integral evaluates to g t
    have hrad : (∫ s in Set.Ioo (0:ℝ) 1, ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t))
        = g t := by
      have e1 : (∫ s in Set.Ioo (0:ℝ) 1, ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t))
          = ∫ s in (0:ℝ)..1, ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t) := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      have e2 : (∫ s in (0:ℝ)..1, ((s * (1 - s ^ 2) ^ 2 : ℝ) : ℂ) * h3 ((s : ℂ) ^ 2 * t))
          = ∫ x in (0:ℝ)..1, 2 * ((x : ℝ) : ℂ) * G (x ^ 2) := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        rw [hGdef, hU2def]
        push_cast
        ring
      have e3 : (∫ u in (0:ℝ)..1, G u) = 2⁻¹ * ∫ σ in (0:ℝ)..1, U2 σ * h3 ((σ : ℂ) * t) := by
        rw [hGdef]
        exact intervalIntegral.integral_const_mul _ _
      have e4 : (∫ σ in (0:ℝ)..1, (2:ℂ) * H1r σ) = 2 * g t := by
        calc (∫ σ in (0:ℝ)..1, (2:ℂ) * H1r σ)
            = 2 * ∫ σ in (0:ℝ)..1, H1r σ := intervalIntegral.integral_const_mul _ _
          _ = 2 * g t := by rw [hFTC, hHr_1, hHr_0]; ring
      rw [e1, e2, hsubst, e3, hIBP1, hIBP2, e4, hU2_1, hU2_0, hU1_1, hH2r_0, hH1r_0]
      ring
    rw [hchain, houter, hrad]
  refine ⟨((-(3 / Real.pi) : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_ne_zero]
    exact neg_ne_zero.mpr (div_ne_zero (by norm_num) Real.pi_ne_zero)
  intro φ B hφ hB z hz
  have hsmul : ∀ (r : ℝ) (x : ℂ), r • x = (r : ℂ) * x := fun _ _ => rfl
  -- basic facts about z and the Cayley data
  have hzi : z - Complex.I ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.im h0
    simp [Complex.sub_im] at h1
    linarith
  have hnormlt : ∀ η : ℂ, η.im < 0 → ‖(η + Complex.I) / (η - Complex.I)‖ < 1 := by
    intro η hη
    have hden : η - Complex.I ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.im h0
      simp [Complex.sub_im] at h1
      linarith
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
    have h2 : ‖η + Complex.I‖ ^ 2 < ‖η - Complex.I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.I_re, Complex.I_im]
      nlinarith
    nlinarith [norm_nonneg (η + Complex.I), norm_nonneg (η - Complex.I)]
  set t : ℂ := (z + Complex.I) / (z - Complex.I) with htdef
  have ht : ‖t‖ < 1 := by
    rw [htdef]
    exact hnormlt z hz
  set Cinv : ℂ → ℂ := fun v => -Complex.I * (1 + v) / (1 - v) with hCdef
  have h1vne : ∀ v : ℂ, ‖v‖ < 1 → (1 : ℂ) - v ≠ 0 := by
    intro v hv h0
    rw [sub_eq_zero] at h0
    rw [← h0] at hv
    simp at hv
  have hCd : ∀ v ∈ Metric.ball (0:ℂ) 1,
      HasDerivAt Cinv (-2 * Complex.I / (1 - v) ^ 2) v := by
    intro v hv
    have h1v := h1vne v (mem_ball_zero_iff.mp hv)
    have ha : HasDerivAt (fun v : ℂ => -Complex.I * (1 + v)) (-Complex.I) v := by
      simpa using ((hasDerivAt_id v).const_add 1).const_mul (-Complex.I)
    have hb : HasDerivAt (fun v : ℂ => (1:ℂ) - v) (-1) v := by
      simpa using (hasDerivAt_id v).const_sub 1
    have h := ha.fun_div hb h1v
    convert h using 1
    field_simp
    ring
  -- the imaginary part of the Cayley image
  have hIm : ∀ v : ℂ, ‖v‖ < 1 →
      (Cinv v).im * Complex.normSq (1 - v) = -(1 - Complex.normSq v) := by
    intro v hv
    have h1v := h1vne v hv
    have hnS : Complex.normSq (1 - v) ≠ 0 := fun h => h1v (Complex.normSq_eq_zero.mp h)
    rw [hCdef]
    simp only [Complex.div_im]
    field_simp
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  have hImneg : ∀ v ∈ Metric.ball (0:ℂ) 1, (Cinv v).im < 0 := by
    intro v hv
    have hv' := mem_ball_zero_iff.mp hv
    have h1 := hIm v hv'
    have hnS : 0 < Complex.normSq (1 - v) := Complex.normSq_pos.mpr (h1vne v hv')
    have hnSv : Complex.normSq v < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg v]
    nlinarith
  -- the Cayley map inverts the standard map to the disk
  have hCinvC : ∀ η : ℂ, η.im < 0 → Cinv ((η + Complex.I) / (η - Complex.I)) = η := by
    intro η hη
    have hden : η - Complex.I ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.im h0
      simp [Complex.sub_im] at h1
      linarith
    have h1 : (1:ℂ) - (η + Complex.I) / (η - Complex.I) = -2 * Complex.I / (η - Complex.I) := by
      field_simp
      ring
    rw [hCdef]
    change -Complex.I * (1 + (η + Complex.I) / (η - Complex.I))
      / (1 - (η + Complex.I) / (η - Complex.I)) = η
    have hne2 : (1:ℂ) - (η + Complex.I) / (η - Complex.I) ≠ 0 := by
      rw [h1]
      simp [hden, Complex.I_ne_zero]
    rw [div_eq_iff hne2, h1]
    field_simp
    ring
  have himage : Cinv '' Metric.ball (0:ℂ) 1 = {η : ℂ | η.im < 0} := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨v, hv, rfl⟩
      exact hImneg v hv
    · intro η hη
      have hη' : η.im < 0 := hη
      refine ⟨(η + Complex.I) / (η - Complex.I), ?_, hCinvC η hη'⟩
      rw [mem_ball_zero_iff]
      exact hnormlt η hη'
  have hCfwd : ∀ v ∈ Metric.ball (0:ℂ) 1,
      (Cinv v + Complex.I) / (Cinv v - Complex.I) = v := by
    intro v hv
    have h1v := h1vne v (mem_ball_zero_iff.mp hv)
    rw [hCdef]
    change (-Complex.I * (1 + v) / (1 - v) + Complex.I)
      / (-Complex.I * (1 + v) / (1 - v) - Complex.I) = v
    have hnum : -Complex.I * (1 + v) / (1 - v) + Complex.I = -2 * Complex.I * v / (1 - v) := by
      field_simp
      ring
    have hden : -Complex.I * (1 + v) / (1 - v) - Complex.I = -2 * Complex.I / (1 - v) := by
      field_simp
      ring
    have hd2 : -Complex.I * (1 + v) / (1 - v) - Complex.I ≠ 0 := by
      rw [hden]
      simp [h1v, Complex.I_ne_zero]
    rw [div_eq_iff hd2, hden, hnum]
    field_simp
  have hinj : Set.InjOn Cinv (Metric.ball (0:ℂ) 1) := by
    intro v1 hv1 v2 hv2 heq
    have h1 := hCfwd v1 hv1
    have h2 := hCfwd v2 hv2
    rw [← h1, ← h2, heq]
  -- the real Jacobian of the Cayley map
  set d : ℂ → ℂ := fun v => -2 * Complex.I / (1 - v) ^ 2 with hddef
  set f' : ℂ → ℂ →L[ℝ] ℂ := fun v => (d v) • (1 : ℂ →L[ℝ] ℂ) with hf'def
  have hfd : ∀ v ∈ Metric.ball (0:ℂ) 1,
      HasFDerivWithinAt Cinv (f' v) (Metric.ball (0:ℂ) 1) v := by
    intro v hv
    have h : HasDerivWithinAt Cinv (-2 * Complex.I / (1 - v) ^ 2) (Metric.ball (0:ℂ) 1) v :=
      (hCd v hv).hasDerivWithinAt
    exact h.complexToReal_fderiv
  have hdet : ∀ v : ℂ, (f' v).det = Complex.normSq (d v) := by
    intro v
    have hM : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI)
        ((f' v : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
        = !![(d v).re, -(d v).im; (d v).im, (d v).re] := by
      ext i j
      rw [LinearMap.toMatrix_apply, Complex.coe_basisOneI]
      fin_cases j <;> fin_cases i
      · change (Complex.basisOneI.repr (d v * 1)) 0 = (d v).re
        rw [Complex.coe_basisOneI_repr]
        norm_num
      · change (Complex.basisOneI.repr (d v * 1)) 1 = (d v).im
        rw [Complex.coe_basisOneI_repr]
        norm_num
      · change (Complex.basisOneI.repr (d v * Complex.I)) 0 = -(d v).im
        rw [Complex.coe_basisOneI_repr]
        simp [Complex.mul_re, Complex.I_re, Complex.I_im]
      · change (Complex.basisOneI.repr (d v * Complex.I)) 1 = (d v).re
        rw [Complex.coe_basisOneI_repr]
        simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    have hdt : Matrix.det ((LinearMap.toMatrix Complex.basisOneI Complex.basisOneI)
        ((f' v : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)) = (f' v).det := LinearMap.det_toMatrix _ _
    rw [hM] at hdt
    rw [← hdt, Matrix.det_fin_two_of, Complex.normSq_apply]
    ring
  -- the integrand and the conjugation step
  set F : ℂ → ℂ := fun ζ => (((-(3 / Real.pi) : ℝ) : ℂ) * (ζ - starRingEnd ℂ ζ) ^ 2
    * φ (starRingEnd ℂ ζ)) / (ζ - z) ^ 4 with hFdef
  have hstep1 : (∫ η in {η : ℂ | η.im < 0}, F (starRingEnd ℂ η))
      = ∫ ζ in {ζ : ℂ | 0 < ζ.im}, F ζ := by
    have hconjMP : MeasurePreserving (fun η : ℂ => starRingEnd ℂ η) volume volume :=
      Complex.conjLIE.measurePreserving
    have hconjEmb : MeasurableEmbedding (fun η : ℂ => starRingEnd ℂ η) :=
      Complex.conjLIE.toHomeomorph.measurableEmbedding
    have h := hconjMP.setIntegral_preimage_emb hconjEmb F {ζ : ℂ | 0 < ζ.im}
    have hpre : (fun η : ℂ => starRingEnd ℂ η) ⁻¹' {ζ : ℂ | 0 < ζ.im}
        = {η : ℂ | η.im < 0} := by
      ext η
      simp [Complex.conj_im]
    rwa [hpre] at h
  -- change of variables to the disk
  have hCoV : (∫ η in {η : ℂ | η.im < 0}, F (starRingEnd ℂ η))
      = ∫ v in Metric.ball (0:ℂ) 1, |(f' v).det| • F (starRingEnd ℂ (Cinv v)) := by
    have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
      measurableSet_ball hfd hinj (fun η => F (starRingEnd ℂ η))
    rw [himage] at h
    exact h
  -- the transported holomorphic data
  set g : ℂ → ℂ := fun v => φ (Cinv v) * (16 / (1 - v) ^ 4) with hgdef
  have hgdiff : DifferentiableOn ℂ g (Metric.ball (0:ℂ) 1) := by
    rw [hgdef]
    apply DifferentiableOn.mul
    · apply DifferentiableOn.comp hφ
      · intro v hv
        exact ((hCd v hv).differentiableAt).differentiableWithinAt
      · intro v hv
        exact hImneg v hv
    · apply DifferentiableOn.div (differentiableOn_const _)
      · exact (differentiableOn_const _ |>.sub differentiableOn_id).pow 4
      · intro v hv
        exact pow_ne_zero 4 (h1vne v (mem_ball_zero_iff.mp hv))
  have hgB4 : ∀ v ∈ Metric.ball (0:ℂ) 1, (1 - ‖v‖ ^ 2) ^ 2 * ‖g v‖ ≤ 4 * B := by
    intro v hv
    have hv' := mem_ball_zero_iff.mp hv
    have h1v := h1vne v hv'
    have hgn : ‖g v‖ = ‖φ (Cinv v)‖ * (16 / ‖1 - v‖ ^ 4) := by
      rw [hgdef]
      rw [norm_mul, norm_div, norm_pow]
      norm_num
    have h1 := hIm v hv'
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
    have hkey : (1 - ‖v‖ ^ 2) ^ 2 * 16 = 4 * (2 * (Cinv v).im) ^ 2 * (‖1 - v‖ ^ 2) ^ 2 := by
      nlinarith [h1]
    have hpos : (0:ℝ) < ‖1 - v‖ ^ 4 := by
      have := norm_pos_iff.mpr h1v
      positivity
    have hstep : (1 - ‖v‖ ^ 2) ^ 2 * ‖g v‖ = 4 * ((2 * (Cinv v).im) ^ 2 * ‖φ (Cinv v)‖) := by
      rw [hgn]
      have hN : ‖1 - v‖ ^ 4 ≠ 0 := ne_of_gt hpos
      field_simp
      linear_combination ‖φ (Cinv v)‖ * hkey
    rw [hstep]
    have hb := hB (Cinv v) (hImneg v hv)
    nlinarith [hb]
  -- the pointwise identity between the transported integrand and the disk integrand
  have hker2 : ∀ v : ℂ, ‖v‖ < 1 → 1 - starRingEnd ℂ v * t ≠ 0 := by
    intro v hv h0
    have h1 : ‖starRingEnd ℂ v * t‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg t, norm_nonneg v]
    rw [sub_eq_zero] at h0
    rw [← h0] at h1
    simp at h1
  have hptc : ∀ v ∈ Metric.ball (0:ℂ) 1,
      |(f' v).det| • F (starRingEnd ℂ (Cinv v))
        = (-(((-(3 / Real.pi) : ℝ) : ℂ)) / (z - Complex.I) ^ 4)
          * ((((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * g v / (1 - starRingEnd ℂ v * t) ^ 4) := by
    intro v hv
    have hv' := mem_ball_zero_iff.mp hv
    have h1v := h1vne v hv'
    have h1vc : (1:ℂ) - starRingEnd ℂ v ≠ 0 := by
      intro h0
      apply h1v
      have h1 := congrArg (starRingEnd ℂ) h0
      simpa using h1
    have hkt := hker2 v hv'
    have hcAz : starRingEnd ℂ (Cinv v) - z ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.im h0
      simp [Complex.conj_im] at h1
      have h2 := hImneg v hv
      linarith
    -- conjugate of the Cayley image
    have hconjA : starRingEnd ℂ (Cinv v)
        = Complex.I * (1 + starRingEnd ℂ v) / (1 - starRingEnd ℂ v) := by
      rw [hCdef]
      simp [map_div₀, map_mul, Complex.conj_I]
    -- the difference with the conjugate
    have hAsub : starRingEnd ℂ (Cinv v) - Cinv v
        = 2 * Complex.I * (1 - v * starRingEnd ℂ v)
          / ((1 - v) * (1 - starRingEnd ℂ v)) := by
      rw [hconjA, hCdef]
      field_simp
      ring
    have hAsub2 : (starRingEnd ℂ (Cinv v) - Cinv v) ^ 2
        = -4 * (1 - v * starRingEnd ℂ v) ^ 2
          / ((1 - v) * (1 - starRingEnd ℂ v)) ^ 2 := by
      rw [hAsub, div_pow]
      have hnum : (2 * Complex.I * (1 - v * starRingEnd ℂ v)) ^ 2
          = -4 * (1 - v * starRingEnd ℂ v) ^ 2 := by
        linear_combination (4 * (1 - v * starRingEnd ℂ v) ^ 2) * Complex.I_sq
      rw [hnum]
    -- the kernel transported through the Cayley map
    have hkA : starRingEnd ℂ (Cinv v) - z
        = -((1 - starRingEnd ℂ v * t) * (z - Complex.I)) / (1 - starRingEnd ℂ v) := by
      rw [hconjA, htdef]
      field_simp
      ring
    -- the Jacobian determinant as a complex quotient
    have hdet3 : ((Complex.normSq (d v) : ℝ) : ℂ)
        = 4 / ((1 - v) ^ 2 * (1 - starRingEnd ℂ v) ^ 2) := by
      rw [← Complex.mul_conj, hddef]
      change -2 * Complex.I / (1 - v) ^ 2 * starRingEnd ℂ (-2 * Complex.I / (1 - v) ^ 2)
        = 4 / ((1 - v) ^ 2 * (1 - starRingEnd ℂ v) ^ 2)
      have hc : starRingEnd ℂ (-2 * Complex.I / (1 - v) ^ 2)
          = 2 * Complex.I / (1 - starRingEnd ℂ v) ^ 2 := by
        simp [map_div₀, map_mul, Complex.conj_I, map_ofNat]
      rw [hc, div_mul_div_comm]
      have hnum4 : -2 * Complex.I * (2 * Complex.I) = 4 := by
        linear_combination (-4 : ℂ) * Complex.I_sq
      rw [hnum4]
    -- the weight cast
    have hw2 : (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) = (1 - v * starRingEnd ℂ v) ^ 2 := by
      have hnv : ((‖v‖ ^ 2 : ℝ) : ℂ) = v * starRingEnd ℂ v := by
        rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
      rw [Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
      rw [← Complex.ofReal_pow, hnv]
    -- assemble the pointwise identity
    have hsm : |(f' v).det| • F (starRingEnd ℂ (Cinv v))
        = ((Complex.normSq (d v) : ℝ) : ℂ) * F (starRingEnd ℂ (Cinv v)) := by
      rw [hsmul, hdet v, abs_of_nonneg (Complex.normSq_nonneg _)]
    rw [hsm]
    simp only [hFdef, hgdef]
    rw [Complex.conj_conj, hAsub2, hdet3, hw2, hkA]
    field_simp
    ring
  -- pull the constant out and apply the disk identity
  have hcongr : (∫ v in Metric.ball (0:ℂ) 1, |(f' v).det| • F (starRingEnd ℂ (Cinv v)))
      = (-(((-(3 / Real.pi) : ℝ) : ℂ)) / (z - Complex.I) ^ 4)
        * ∫ v in Metric.ball (0:ℂ) 1,
            (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * g v / (1 - starRingEnd ℂ v * t) ^ 4 := by
    calc (∫ v in Metric.ball (0:ℂ) 1, |(f' v).det| • F (starRingEnd ℂ (Cinv v)))
        = ∫ v in Metric.ball (0:ℂ) 1, (-(((-(3 / Real.pi) : ℝ) : ℂ)) / (z - Complex.I) ^ 4)
            * ((((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * g v / (1 - starRingEnd ℂ v * t) ^ 4) :=
          setIntegral_congr_fun measurableSet_ball hptc
      _ = _ := integral_const_mul _ _
  have hdc := disk_core g (4 * B) t ht hgdiff hgB4
  -- evaluate the reproduced value
  have hgt : g t = φ z * (z - Complex.I) ^ 4 := by
    rw [hgdef]
    change φ (Cinv t) * (16 / (1 - t) ^ 4) = φ z * (z - Complex.I) ^ 4
    have hCt : Cinv t = z := by
      rw [htdef]
      exact hCinvC z hz
    have h1t : (1:ℂ) - t = -2 * Complex.I / (z - Complex.I) := by
      rw [htdef]
      field_simp
      ring
    rw [hCt, h1t, div_pow]
    have h16 : (-2 * Complex.I) ^ 4 = 16 := by
      linear_combination (16 * Complex.I ^ 2 - 16) * Complex.I_sq
    rw [h16, div_div_eq_mul_div]
    have hz4 : (z - Complex.I) ^ 4 ≠ 0 := pow_ne_zero _ hzi
    field_simp
  -- final assembly
  rw [← hstep1, hCoV, hcongr, hdc, hgt]
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz4 : (z - Complex.I) ^ 4 ≠ 0 := pow_ne_zero _ hzi
  push_cast
  field_simp

end RiemannDynamics

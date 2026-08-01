/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Gronwall

/-!
# The Nehari bound

An injective holomorphic map on a ball has Schwarzian derivative bounded by the ball's
Poincaré density: `(R² − |z − c|²)² |S f z| ≤ 6 R²`. The route is classical — the
Gronwall area theorem bounds the coefficients of a univalent map of the exterior disk,
the square-root transform turns it into the second-coefficient inequality
`|a₃ − a₂²| ≤ 1` for a normalized univalent map of the disk, the Schwarzian at the
center is `6(a₃ − a₂²)`, and disk automorphisms transport the center bound to every
point. Exhausting the lower half plane by balls yields the half-plane form
`4 y² |S f z| ≤ 6` consumed by the Bers-type map of the variational tier.

* `schwarzian_le_of_injOn_ball` — the Nehari bound on a ball.
* `schwarzian_le_of_injOn_lower` — the Nehari bound on the lower half plane.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **The Nehari bound on a ball**: an injective holomorphic map on an open ball
satisfies `(R² − |z − c|²)² |S f z| ≤ 6 R²`. -/
theorem schwarzian_le_of_injOn_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hinj : Set.InjOn f (Metric.ball c R)) {z : ℂ} (hz : z ∈ Metric.ball c R) :
    (R ^ 2 - ‖z - c‖ ^ 2) ^ 2 * ‖schwarzian f z‖ ≤ 6 * R ^ 2 := by
  -- The center case: a normalized injective holomorphic map of the unit ball has
  -- `‖S g 0‖ ≤ 6`, by the Gronwall bound on the tail of `1/g(1/w)`.
  have hcenter : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 1) →
      Set.InjOn g (Metric.ball 0 1) → g 0 = 0 → deriv g 0 = 1 →
      ‖schwarzian g 0‖ ≤ 6 := by
    intro g hg hginj hg0 hg1
    have hID2 : ∀ F : ℂ → ℂ, iteratedDeriv 2 F = deriv (deriv F) := fun F => by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hID3 : ∀ F : ℂ → ℂ, iteratedDeriv 3 F = deriv (iteratedDeriv 2 F) := fun F => by
      rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
    have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
    have hballnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
    have hg_an : AnalyticAt ℂ g 0 := hg.analyticAt hballnhds
    -- The order of `g` at `0` is exactly `1`.
    have hord : analyticOrderAt g 0 = (1 : ℕ) := by
      have hd0 : analyticOrderAt (deriv g) 0 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (by rw [hg1]; exact one_ne_zero))
      have key := hg_an.analyticOrderAt_deriv_add_one
      have hcongr : analyticOrderAt (fun x => g x - g 0) 0 = analyticOrderAt g 0 :=
        analyticOrderAt_congr (by filter_upwards with x using by rw [hg0, sub_zero])
      rw [hcongr] at key
      rw [← key, hd0, zero_add]
      rfl
    -- Factor `g v = v * ψ₀ v` with `ψ₀` analytic and `ψ₀ 0 = 1`.
    obtain ⟨ψ₀, hψ₀_an, hψ₀_ne, hfact⟩ := (hg_an.analyticOrderAt_eq_natCast).mp hord
    have hfact' : ∀ᶠ v in nhds (0 : ℂ), g v = v * ψ₀ v := by
      filter_upwards [hfact] with v hv
      simpa [smul_eq_mul] using hv
    have hψ₀0 : ψ₀ 0 = 1 := by
      have hder : HasDerivAt (fun v => v * ψ₀ v) (ψ₀ 0) 0 := by
        have h1 := (hasDerivAt_id (0 : ℂ)).mul (hψ₀_an.differentiableAt.hasDerivAt)
        simpa using h1
      have hde := Filter.EventuallyEq.deriv_eq hfact'
      rw [hg1, hder.deriv] at hde
      exact hde.symm
    -- The unit tail `ψ v = g v / v` (with the singularity removed) and `s = ψ⁻¹`.
    obtain ⟨ψ, hψ_def⟩ : ∃ ψ : ℂ → ℂ, ψ = fun v => if v = 0 then 1 else g v / v := ⟨_, rfl⟩
    obtain ⟨s, hs_def⟩ : ∃ s : ℂ → ℂ, s = fun v => (ψ v)⁻¹ := ⟨_, rfl⟩
    have hψ0 : ψ 0 = 1 := by rw [hψ_def]; simp
    have hψψ₀ : ψ =ᶠ[nhds (0 : ℂ)] ψ₀ := by
      filter_upwards [hfact'] with v hv
      by_cases hv0 : v = 0
      · subst hv0
        rw [hψ0, hψ₀0]
      · rw [hψ_def]
        simp only [if_neg hv0]
        rw [hv, mul_comm, mul_div_assoc, div_self hv0, mul_one]
    have hψ_an0 : AnalyticAt ℂ ψ 0 := hψ₀_an.congr hψψ₀.symm
    have hψ_an : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ ψ v := by
      intro v hv
      by_cases hv0 : v = 0
      · subst hv0; exact hψ_an0
      · have hg_anv : AnalyticAt ℂ g v := hg.analyticAt (Metric.isOpen_ball.mem_nhds hv)
        have hdiv : AnalyticAt ℂ (fun u => g u / u) v := hg_anv.fun_div analyticAt_id hv0
        apply hdiv.congr
        filter_upwards [isOpen_ne.mem_nhds hv0] with u hu
        rw [hψ_def]
        simp only [if_neg hu]
    have hg_ne : ∀ v ∈ Metric.ball (0 : ℂ) 1, v ≠ 0 → g v ≠ 0 := by
      intro v hv hv0 hgv
      exact hv0 (hginj hv h0mem (by rw [hgv, hg0]))
    have hψ_ne : ∀ v ∈ Metric.ball (0 : ℂ) 1, ψ v ≠ 0 := by
      intro v hv
      by_cases hv0 : v = 0
      · subst hv0; rw [hψ0]; exact one_ne_zero
      · rw [hψ_def]
        simp only [if_neg hv0]
        exact div_ne_zero (hg_ne v hv hv0) hv0
    have hs_an : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ s v := by
      intro v hv
      rw [hs_def]
      exact (hψ_an v hv).fun_inv (hψ_ne v hv)
    have hs_diff : DifferentiableOn ℂ s (Metric.ball 0 1) := fun v hv =>
      ((hs_an v hv).differentiableAt).differentiableWithinAt
    have hs0 : s 0 = 1 := by rw [hs_def]; simp only [hψ0, inv_one]
    -- Injectivity of the exterior map `w ↦ w · s(1/w)`.
    have hTval : ∀ w : ℂ, 1 < ‖w‖ →
        w * s w⁻¹ = 1 / g w⁻¹ ∧ w⁻¹ ∈ Metric.ball (0 : ℂ) 1 ∧ w⁻¹ ≠ 0 := by
      intro w hw
      have hw0 : w ≠ 0 := by
        intro h
        rw [h, norm_zero] at hw
        linarith
      have hwinv0 : w⁻¹ ≠ 0 := inv_ne_zero hw0
      have hwball : w⁻¹ ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_inv]
        exact inv_lt_one_of_one_lt₀ hw
      refine ⟨?_, hwball, hwinv0⟩
      have hsw : s w⁻¹ = w⁻¹ / g w⁻¹ := by
        rw [hs_def]
        simp only
        rw [hψ_def]
        simp only [if_neg hwinv0]
        rw [inv_div]
      rw [hsw, ← mul_div_assoc, mul_inv_cancel₀ hw0]
    have hTinj : Set.InjOn (fun w => w * s w⁻¹) {w : ℂ | 1 < ‖w‖} := by
      intro w₁ hw₁ w₂ hw₂ heq
      obtain ⟨hT1, hball1, hne1⟩ := hTval w₁ hw₁
      obtain ⟨hT2, hball2, hne2⟩ := hTval w₂ hw₂
      simp only at heq
      rw [hT1, hT2] at heq
      have hg1ne : g w₁⁻¹ ≠ 0 := hg_ne _ hball1 hne1
      have hg2ne : g w₂⁻¹ ≠ 0 := hg_ne _ hball2 hne2
      have hgeq : g w₁⁻¹ = g w₂⁻¹ := by
        have h := (div_eq_div_iff hg1ne hg2ne).mp heq
        rw [one_mul, one_mul] at h
        exact h.symm
      exact inv_injective (hginj hball1 hball2 hgeq)
    -- The Gronwall coefficient bound for `s`.
    have hb : ‖iteratedDeriv 2 s 0‖ ≤ 2 := abs_laurent_coeff_le_of_injOn hs_diff hs0 hTinj
    -- Derivatives of `g` in terms of `ψ`.
    have hgψ : ∀ᶠ v in nhds (0 : ℂ), g v = v * ψ v := by
      filter_upwards [hfact', hψψ₀] with v hv1 hv2
      rw [hv1, hv2]
    have hψ_evan : ∀ᶠ v in nhds (0 : ℂ), AnalyticAt ℂ ψ v := hψ_an0.eventually_analyticAt
    have hdg : ∀ᶠ v in nhds (0 : ℂ), deriv g v = ψ v + v * deriv ψ v := by
      filter_upwards [hgψ.eventually_nhds, hψ_evan] with v hv hψv
      have h1 : HasDerivAt (fun u => u * ψ u) (1 * ψ v + v * deriv ψ v) v :=
        (hasDerivAt_id v).mul hψv.differentiableAt.hasDerivAt
      rw [Filter.EventuallyEq.deriv_eq hv, h1.deriv, one_mul]
    have hd2g : ∀ᶠ v in nhds (0 : ℂ),
        iteratedDeriv 2 g v = 2 * deriv ψ v + v * deriv (deriv ψ) v := by
      filter_upwards [hdg.eventually_nhds, hψ_evan] with v hv hψv
      rw [hID2 g, Filter.EventuallyEq.deriv_eq hv]
      have h1 : HasDerivAt ψ (deriv ψ v) v := hψv.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun u => u * deriv ψ u)
          (1 * deriv ψ v + v * deriv (deriv ψ) v) v :=
        (hasDerivAt_id v).mul hψv.deriv.differentiableAt.hasDerivAt
      rw [(h1.fun_add h2).deriv]
      ring
    have h2g0 : iteratedDeriv 2 g 0 = 2 * deriv ψ 0 := by
      have h := hd2g.self_of_nhds
      rw [h]
      ring
    have h3g0 : iteratedDeriv 3 g 0 = 3 * deriv (deriv ψ) 0 := by
      rw [hID3 g, Filter.EventuallyEq.deriv_eq hd2g]
      have h1 : HasDerivAt (fun u => 2 * deriv ψ u) (2 * deriv (deriv ψ) 0) 0 :=
        (hψ_an0.deriv.differentiableAt.hasDerivAt).const_mul 2
      have h2 : HasDerivAt (fun u => u * deriv (deriv ψ) u)
          (1 * deriv (deriv ψ) 0 + 0 * deriv (deriv (deriv ψ)) 0) 0 :=
        (hasDerivAt_id 0).mul hψ_an0.deriv.deriv.differentiableAt.hasDerivAt
      rw [(h1.fun_add h2).deriv]
      ring
    -- Derivatives of `s` in terms of `ψ`.
    have hψ_ne_ev : ∀ᶠ v in nhds (0 : ℂ), ψ v ≠ 0 :=
      hψ_an0.continuousAt.eventually_ne (by rw [hψ0]; exact one_ne_zero)
    have hds : ∀ᶠ v in nhds (0 : ℂ), deriv s v = -deriv ψ v / ψ v ^ 2 := by
      filter_upwards [hψ_evan, hψ_ne_ev] with v hψv hψvne
      rw [hs_def]
      exact ((hψv.differentiableAt.hasDerivAt).fun_inv hψvne).deriv
    have h2s0 : iteratedDeriv 2 s 0 = 2 * (deriv ψ 0) ^ 2 - deriv (deriv ψ) 0 := by
      rw [hID2 s, Filter.EventuallyEq.deriv_eq hds]
      have hnum : HasDerivAt (fun v => -deriv ψ v) (-(deriv (deriv ψ) 0)) 0 :=
        (hψ_an0.deriv.differentiableAt.hasDerivAt).neg
      have hden : HasDerivAt (fun v => ψ v ^ 2) (2 * ψ 0 ^ 1 * deriv ψ 0) 0 :=
        (hψ_an0.differentiableAt.hasDerivAt).pow 2
      have hd2 : (fun v => ψ v ^ 2) 0 ≠ 0 := by
        simp only [hψ0, one_pow]
        exact one_ne_zero
      have hdiv : HasDerivAt (fun v => -deriv ψ v / ψ v ^ 2)
          ((-(deriv (deriv ψ) 0) * ψ 0 ^ 2 - -deriv ψ 0 * (2 * ψ 0 ^ 1 * deriv ψ 0))
            / (ψ 0 ^ 2) ^ 2) 0 := hnum.div hden hd2
      rw [hdiv.deriv, hψ0]
      ring
    -- Conclude: `S g 0 = −3 · s''(0)`.
    have hSg : schwarzian g 0 = -3 * iteratedDeriv 2 s 0 := by
      simp only [schwarzian]
      rw [hg1, h2g0, h3g0, h2s0, div_one, div_one]
      ring
    rw [hSg, norm_mul]
    have h3 : ‖(-3 : ℂ)‖ = 3 := by norm_num
    rw [h3]
    linarith
  -- The transport to an arbitrary center and point by a disk automorphism.
  have hID2 : ∀ F : ℂ → ℂ, iteratedDeriv 2 F = deriv (deriv F) := fun F => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hID3 : ∀ F : ℂ → ℂ, iteratedDeriv 3 F = deriv (iteratedDeriv 2 F) := fun F => by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  obtain ⟨ζ₀, hζ₀_def⟩ : ∃ ζ₀ : ℂ, ζ₀ = (z - c) / (R : ℂ) := ⟨_, rfl⟩
  have hzc : ‖z - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have hζ₀_norm : ‖ζ₀‖ = ‖z - c‖ / R := by
    rw [hζ₀_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hζ₀_lt : ‖ζ₀‖ < 1 := by
    rw [hζ₀_norm, div_lt_one hR]
    exact hzc
  -- The disk automorphism `σ` sending `0` to `z`, and its determinant `Dr`.
  obtain ⟨a, ha_def⟩ : ∃ a : ℂ, a = (R : ℂ) + c * (starRingEnd ℂ) ζ₀ := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℂ, b = (R : ℂ) * ζ₀ + c := ⟨_, rfl⟩
  obtain ⟨σ, hσ_def⟩ : ∃ σ : ℂ → ℂ,
      σ = fun w => (a * w + b) / ((starRingEnd ℂ) ζ₀ * w + 1) := ⟨_, rfl⟩
  obtain ⟨Dr, hDr_def⟩ : ∃ Dr : ℝ, Dr = R * (1 - ‖ζ₀‖ ^ 2) := ⟨_, rfl⟩
  have hDr_pos : 0 < Dr := by
    rw [hDr_def]
    have h1 : ‖ζ₀‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ₀]
    nlinarith
  have hDrC_ne : (Dr : ℂ) ≠ 0 := by exact_mod_cast hDr_pos.ne'
  have hdet : a * 1 - b * (starRingEnd ℂ) ζ₀ = (Dr : ℂ) := by
    rw [ha_def, hb_def, hDr_def]
    push_cast
    have h := Complex.mul_conj' ζ₀
    linear_combination (-(R : ℂ)) * h
  have hdet_ne : a * 1 - b * (starRingEnd ℂ) ζ₀ ≠ 0 := by
    rw [hdet]
    exact hDrC_ne
  have hden_ne : ∀ w : ℂ, ‖w‖ < 1 → (starRingEnd ℂ) ζ₀ * w + 1 ≠ 0 := by
    intro w hw h0
    have h1 : ‖(starRingEnd ℂ) ζ₀ * w‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg ζ₀, norm_nonneg w]
    have h2 : (starRingEnd ℂ) ζ₀ * w = -1 := by linear_combination h0
    rw [h2] at h1
    simp at h1
  -- The fundamental identity of the disk automorphism.
  have hkey : ∀ w : ℂ, ‖(starRingEnd ℂ) ζ₀ * w + 1‖ ^ 2 - ‖w + ζ₀‖ ^ 2
      = (1 - ‖ζ₀‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    intro w
    have hC : ((starRingEnd ℂ) ζ₀ * w + 1) * (starRingEnd ℂ) ((starRingEnd ℂ) ζ₀ * w + 1)
        - (w + ζ₀) * (starRingEnd ℂ) (w + ζ₀)
        = (1 - ζ₀ * (starRingEnd ℂ) ζ₀) * (1 - w * (starRingEnd ℂ) w) := by
      simp only [map_add, map_mul, map_one, Complex.conj_conj]
      ring
    rw [Complex.mul_conj', Complex.mul_conj', Complex.mul_conj', Complex.mul_conj'] at hC
    exact_mod_cast hC
  have hσ_sub : ∀ w : ℂ, ‖w‖ < 1 →
      σ w - c = (R : ℂ) * (w + ζ₀) / ((starRingEnd ℂ) ζ₀ * w + 1) := by
    intro w hw
    rw [hσ_def, ha_def, hb_def]
    simp only
    field_simp [hden_ne w hw]
    ring
  have hσ_maps : ∀ w : ℂ, ‖w‖ < 1 → σ w ∈ Metric.ball c R := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm, hσ_sub w hw]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have hd_pos : 0 < ‖(starRingEnd ℂ) ζ₀ * w + 1‖ := norm_pos_iff.mpr (hden_ne w hw)
    rw [div_lt_iff₀ hd_pos]
    have hlt : ‖w + ζ₀‖ < ‖(starRingEnd ℂ) ζ₀ * w + 1‖ := by
      have hk := hkey w
      have h1 : ‖ζ₀‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ₀]
      have h2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
      nlinarith [norm_nonneg (w + ζ₀), norm_nonneg ((starRingEnd ℂ) ζ₀ * w + 1)]
    exact mul_lt_mul_of_pos_left hlt hR
  have hσ0 : σ 0 = z := by
    rw [hσ_def]
    simp only [mul_zero, zero_add, div_one]
    rw [hb_def, hζ₀_def]
    field_simp
    ring
  have hσ_an : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ σ w := by
    intro w hw
    rw [hσ_def]
    exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).fun_div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const) (hden_ne w hw)
  have hσ_inj : Set.InjOn σ (Metric.ball 0 1) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have hn₁ : ‖w₁‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hw₁
    have hn₂ : ‖w₂‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hw₂
    rw [hσ_def] at heq
    simp only at heq
    rw [div_eq_div_iff (hden_ne w₁ hn₁) (hden_ne w₂ hn₂)] at heq
    have hzero : (a * 1 - b * (starRingEnd ℂ) ζ₀) * (w₁ - w₂) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hdet_ne
    · exact sub_eq_zero.mp h
  have h0ball : ‖(0 : ℂ)‖ < 1 := by norm_num
  have hσ_hd0 : HasDerivAt σ
      ((a * ((starRingEnd ℂ) ζ₀ * 0 + 1) - (a * 0 + b) * (starRingEnd ℂ) ζ₀)
        / ((starRingEnd ℂ) ζ₀ * 0 + 1) ^ 2) 0 := by
    rw [hσ_def]
    have hnum : HasDerivAt (fun x : ℂ => a * x + b) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).add_const b
    have hden : HasDerivAt (fun x : ℂ => (starRingEnd ℂ) ζ₀ * x + 1)
        ((starRingEnd ℂ) ζ₀) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul ((starRingEnd ℂ) ζ₀)).add_const 1
    exact hnum.div hden (hden_ne 0 h0ball)
  have hσ_deriv : deriv σ 0 = (Dr : ℂ) := by
    rw [hσ_hd0.deriv, ← hdet]
    ring
  have hσ_d0_ne : deriv σ 0 ≠ 0 := by
    rw [hσ_deriv]
    exact hDrC_ne
  -- The normalized composite `g = (f ∘ σ − f z) / E`.
  have hfz_ne : deriv f z ≠ 0 := deriv_ne_zero_of_injOn Metric.isOpen_ball hf hinj hz
  have hf_an_z : AnalyticAt ℂ f z := hf.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  obtain ⟨E, hE_def⟩ : ∃ E : ℂ, E = deriv f z * (Dr : ℂ) := ⟨_, rfl⟩
  have hE_ne : E ≠ 0 := by
    rw [hE_def]
    exact mul_ne_zero hfz_ne hDrC_ne
  obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℂ, g = fun w => (f (σ w) - f z) / E := ⟨_, rfl⟩
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    intro w hw
    have hn : ‖w‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hw
    have h1 : DifferentiableAt ℂ f (σ w) :=
      hf.differentiableAt (Metric.isOpen_ball.mem_nhds (hσ_maps w hn))
    have h2 : DifferentiableAt ℂ σ w := (hσ_an w hn).differentiableAt
    have h3 : DifferentiableAt ℂ (fun w => (f (σ w) - f z) / E) w :=
      ((h1.comp w h2).sub_const _).div_const _
    rw [hg_def]
    exact h3.differentiableWithinAt
  have hg_inj : Set.InjOn g (Metric.ball 0 1) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have hn₁ : ‖w₁‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hw₁
    have hn₂ : ‖w₂‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hw₂
    rw [hg_def] at heq
    simp only at heq
    rw [div_eq_div_iff hE_ne hE_ne] at heq
    have hfeq : f (σ w₁) = f (σ w₂) := by
      have h := mul_right_cancel₀ hE_ne heq
      linear_combination h
    exact hσ_inj hw₁ hw₂ (hinj (hσ_maps w₁ hn₁) (hσ_maps w₂ hn₂) hfeq)
  have hg0 : g 0 = 0 := by
    rw [hg_def]
    simp only
    rw [hσ0, sub_self, zero_div]
  have hfσ_hd : HasDerivAt (f ∘ σ) (deriv f z * (Dr : ℂ)) 0 := by
    have h1 : HasDerivAt f (deriv f z) (σ 0) := by
      rw [hσ0]
      exact hf_an_z.differentiableAt.hasDerivAt
    have h2 : HasDerivAt σ (deriv σ 0) 0 := (hσ_an 0 h0ball).differentiableAt.hasDerivAt
    rw [hσ_deriv] at h2
    exact h1.comp 0 h2
  have hg_hd : HasDerivAt g (deriv f z * (Dr : ℂ) / E) 0 := by
    rw [hg_def]
    exact (hfσ_hd.sub_const (f z)).div_const E
  have hg_d1 : deriv g 0 = 1 := by
    rw [hg_hd.deriv, hE_def]
    exact div_self (mul_ne_zero hfz_ne hDrC_ne)
  -- The center bound for `g`.
  have hSg6 : ‖schwarzian g 0‖ ≤ 6 := hcenter _ hg_diff hg_inj hg0 hg_d1
  -- The affine post-composition `A` has vanishing Schwarzian.
  obtain ⟨A, hA_def⟩ : ∃ A : ℂ → ℂ, A = fun u => (u - f z) / E := ⟨_, rfl⟩
  have hA_hd : ∀ u : ℂ, HasDerivAt A (1 / E) u := by
    intro u
    rw [hA_def]
    exact ((hasDerivAt_id u).sub_const (f z)).div_const E
  have hA_deriv : deriv A = fun _ => 1 / E := funext fun u => (hA_hd u).deriv
  have hA2 : iteratedDeriv 2 A = fun _ => (0 : ℂ) := by
    rw [hID2 A, hA_deriv]
    exact deriv_const' _
  have hA3 : iteratedDeriv 3 A = fun _ => (0 : ℂ) := by
    rw [hID3 A, hA2]
    exact deriv_const' _
  have hSA : ∀ u : ℂ, schwarzian A u = 0 := by
    intro u
    simp only [schwarzian, hA2, hA3]
    simp
  -- The cocycle chain.
  have hAn_fσ : AnalyticAt ℂ (f ∘ σ) 0 := by
    have h1 : AnalyticAt ℂ f (σ 0) := by
      rw [hσ0]
      exact hf_an_z
    exact h1.comp (hσ_an 0 h0ball)
  have hd_fσ : deriv (f ∘ σ) 0 = E := by
    rw [hfσ_hd.deriv, hE_def]
  have hd_fσ_ne : deriv (f ∘ σ) 0 ≠ 0 := by
    rw [hd_fσ]
    exact hE_ne
  have hAn_A : AnalyticAt ℂ A ((f ∘ σ) 0) := by
    rw [hA_def]
    exact (analyticAt_id.sub analyticAt_const).fun_div analyticAt_const hE_ne
  have hdA_ne : deriv A ((f ∘ σ) 0) ≠ 0 := by
    rw [hA_deriv]
    exact div_ne_zero one_ne_zero hE_ne
  have hcomp1 : schwarzian (A ∘ (f ∘ σ)) 0
      = schwarzian A ((f ∘ σ) 0) * deriv (f ∘ σ) 0 ^ 2 + schwarzian (f ∘ σ) 0 :=
    schwarzian_comp hAn_fσ hd_fσ_ne hAn_A hdA_ne
  have hgAfσ : schwarzian g 0 = schwarzian (A ∘ (f ∘ σ)) 0 := by
    apply schwarzian_congr_nhds
    filter_upwards with w
    rw [hg_def, hA_def]
    simp [Function.comp]
  have hcomp2 : schwarzian (f ∘ σ) 0
      = schwarzian f (σ 0) * deriv σ 0 ^ 2 + schwarzian σ 0 :=
    schwarzian_comp (hσ_an 0 h0ball) hσ_d0_ne
      (by rw [hσ0]; exact hf_an_z) (by rw [hσ0]; exact hfz_ne)
  have hSσ0 : schwarzian σ 0 = 0 := by
    rw [hσ_def]
    exact schwarzian_ratio_eq_zero hdet_ne (by simp)
  have hfinal : schwarzian g 0 = schwarzian f z * (Dr : ℂ) ^ 2 := by
    rw [hgAfσ, hcomp1, hSA ((f ∘ σ) 0), hcomp2, hSσ0, hσ0, hσ_deriv]
    ring
  -- Transport the bound.
  have hnorm : ‖schwarzian f z‖ * Dr ^ 2 ≤ 6 := by
    have h := hSg6
    rw [hfinal, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDr_pos] at h
    exact h
  have hzceq : ‖z - c‖ = R * ‖ζ₀‖ := by
    rw [hζ₀_norm, mul_comm, div_mul_cancel₀ _ hR.ne']
  have h2 : R ^ 2 * (‖schwarzian f z‖ * Dr ^ 2) ≤ R ^ 2 * 6 :=
    mul_le_mul_of_nonneg_left hnorm (sq_nonneg R)
  calc (R ^ 2 - ‖z - c‖ ^ 2) ^ 2 * ‖schwarzian f z‖
      = R ^ 2 * (‖schwarzian f z‖ * Dr ^ 2) := by
        rw [hzceq, hDr_def]
        ring
    _ ≤ R ^ 2 * 6 := h2
    _ = 6 * R ^ 2 := by ring

/-- **The Nehari bound on the lower half plane**: an injective holomorphic map on the
open lower half plane satisfies `4 y² |S f z| ≤ 6`. -/
theorem schwarzian_le_of_injOn_lower {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | z.im < 0})
    (hinj : Set.InjOn f {z : ℂ | z.im < 0}) {z : ℂ} (hz : z.im < 0) :
    (2 * z.im) ^ 2 * ‖schwarzian f z‖ ≤ 6 := by
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ, y = -z.im := ⟨_, rfl⟩
  have hy : 0 < y := by rw [hy_def]; linarith
  have hzim : z.im = -y := by rw [hy_def]; ring
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = 6 * y * (1 + ε⁻¹) := ⟨_, rfl⟩
  have hεinv : 0 < ε⁻¹ := by positivity
  have hs : 0 < s := by
    rw [hs_def]
    nlinarith
  have hR : 0 < s + y := by linarith
  obtain ⟨cc, hcc_def⟩ : ∃ cc : ℂ, cc = z - Complex.I * (s : ℂ) := ⟨_, rfl⟩
  have hcc_im : cc.im = z.im - s := by
    rw [hcc_def]
    simp [Complex.sub_im, Complex.mul_im]
  have hzc_norm : ‖z - cc‖ = s := by
    rw [hcc_def]
    have h1 : z - (z - Complex.I * (s : ℂ)) = Complex.I * (s : ℂ) := by ring
    rw [h1, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs]
  have hz_ball : z ∈ Metric.ball cc (s + y) := by
    rw [Metric.mem_ball, dist_eq_norm, hzc_norm]
    linarith
  have hsub : Metric.ball cc (s + y) ⊆ {w : ℂ | w.im < 0} := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 : w.im - cc.im ≤ ‖w - cc‖ := by
      have h2 := Complex.abs_im_le_norm (w - cc)
      rw [Complex.sub_im] at h2
      exact le_trans (le_abs_self _) h2
    have h2 : w.im < cc.im + (s + y) := by linarith
    rw [hcc_im, hzim] at h2
    change w.im < 0
    linarith
  have happ := schwarzian_le_of_injOn_ball hR (hf.mono hsub) (hinj.mono hsub) hz_ball
  rw [hzc_norm] at happ
  have hSnn : 0 ≤ ‖schwarzian f z‖ := norm_nonneg _
  have hεne : ε ≠ 0 := hε.ne'
  have hε2 : 0 < ε ^ 2 := by positivity
  have e1 : (s + y) * ε = y * (7 * ε + 6) := by
    rw [hs_def]
    field_simp
    ring
  have e2 : (2 * s + y) * ε = y * (13 * ε + 12) := by
    rw [hs_def]
    field_simp
    ring
  have h2' : 24 * (s + y) ^ 2 * ε ^ 2 ≤ (6 + ε) * (2 * s + y) ^ 2 * ε ^ 2 := by
    calc 24 * (s + y) ^ 2 * ε ^ 2 = 24 * ((s + y) * ε) ^ 2 := by ring
      _ = 24 * (y * (7 * ε + 6)) ^ 2 := by rw [e1]
      _ ≤ (6 + ε) * (y * (13 * ε + 12)) ^ 2 := by
          nlinarith [sq_nonneg (y * ε), mul_nonneg (sq_nonneg (y * ε)) hε.le]
      _ = (6 + ε) * ((2 * s + y) * ε) ^ 2 := by rw [e2]
      _ = (6 + ε) * (2 * s + y) ^ 2 * ε ^ 2 := by ring
  have h2 : 24 * (s + y) ^ 2 ≤ (6 + ε) * (2 * s + y) ^ 2 :=
    le_of_mul_le_mul_right h2' hε2
  have hden_pos : 0 < (2 * s + y) ^ 2 := by
    have h3 : 0 < 2 * s + y := by linarith
    exact pow_pos h3 2
  have hmain : (2 * z.im) ^ 2 * ‖schwarzian f z‖ * (2 * s + y) ^ 2
      ≤ (6 + ε) * (2 * s + y) ^ 2 := by
    have e3 : (2 * z.im) ^ 2 * ‖schwarzian f z‖ * (2 * s + y) ^ 2
        = 4 * (((s + y) ^ 2 - s ^ 2) ^ 2 * ‖schwarzian f z‖) := by
      rw [hzim]
      ring
    rw [e3]
    calc 4 * (((s + y) ^ 2 - s ^ 2) ^ 2 * ‖schwarzian f z‖)
        ≤ 4 * (6 * (s + y) ^ 2) := by linarith
      _ = 24 * (s + y) ^ 2 := by ring
      _ ≤ (6 + ε) * (2 * s + y) ^ 2 := h2
  exact le_of_mul_le_mul_right hmain hden_pos

end RiemannDynamics

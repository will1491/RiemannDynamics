/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.UpperQC.Composite

/-!
# The Möbius factorization of equal-coefficient solutions

Half-disc radial and window estimates with the logarithm branches show a
normalized solution maps the upper half plane into itself, and two solutions
with the same coefficient differ by a real Möbius factor on the upper half
plane.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

-- The gauge bookkeeping for the half-disc contour is one long elaboration; the raised
-- budget is required.
set_option maxHeartbeats 400000 in
-- The radial contour parameterization carries explicit trigonometric estimates;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- The radial parameterization of the boundary of the upper
half-disc `{‖z‖ ≤ R} ∩ {im ≥ 0}` from an interior point `z₀`, via the Minkowski gauge:
a positive continuous radial function landing on the frontier, uniquely determined by
frontier membership along each ray. -/
theorem halfdisc_radial (z₀ : ℂ) (hz₀ : 0 < z₀.im) (R : ℝ) (hR : ‖z₀‖ + 1 < R) :
    ∃ rad : ℝ → ℝ, Continuous rad ∧ (∀ ϑ : ℝ, 0 < rad ϑ) ∧
      (∀ ϑ : ℝ, ‖z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)‖ ≤ R ∧
        0 ≤ (z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)).im ∧
        (‖z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)‖ = R ∨
          (z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)).im = 0)) ∧
      (∀ (ϑ t : ℝ), 0 < t →
        ‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ ≤ R →
        0 ≤ (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im →
        ¬(‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ < R ∧
          0 < (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im) →
        rad ϑ = t) := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hRpos : 0 < R := lt_of_le_of_lt (by positivity) hR
  -- The half-disc body, shifted to put `z₀` at the origin.
  set B₀ : Set ℂ := {w : ℂ | ‖z₀ + w‖ ≤ R ∧ 0 ≤ (z₀ + w).im} with hB₀def
  have hpre : B₀ = (fun w => z₀ + w) ⁻¹'
      (Metric.closedBall 0 R ∩ {c : ℂ | 0 ≤ c.im}) := by
    ext w
    simp only [hB₀def, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right]
  have hconv : Convex ℝ B₀ := by
    have him : B₀ = (fun w => -z₀ + w) ''
        (Metric.closedBall 0 R ∩ {c : ℂ | 0 ≤ c.im}) := by
      ext w
      simp only [hB₀def, Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff,
        Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hw
        exact ⟨z₀ + w, ⟨hw.1, hw.2⟩, by ring⟩
      · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
        have h2 : z₀ + (-z₀ + k) = k := by ring
        rw [h2]
        exact ⟨hk1, hk2⟩
    rw [him]
    exact ((convex_closedBall (0:ℂ) R).inter (convex_halfSpace_im_ge 0)).translate (-z₀)
  have hclosed : IsClosed B₀ := by
    rw [hpre]
    refine IsClosed.preimage (by fun_prop) ?_
    exact (Metric.isClosed_closedBall).inter
      (isClosed_le continuous_const Complex.continuous_im)
  have hB₀nhds : B₀ ∈ nhds (0 : ℂ) := by
    have hδ : 0 < min (R - ‖z₀‖) z₀.im := by
      refine lt_min ?_ hz₀
      linarith
    refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ) ?_
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have h1 : ‖w‖ < R - ‖z₀‖ := lt_of_lt_of_le hw (min_le_left _ _)
    have h2 : ‖w‖ < z₀.im := lt_of_lt_of_le hw (min_le_right _ _)
    constructor
    · calc ‖z₀ + w‖ ≤ ‖z₀‖ + ‖w‖ := norm_add_le _ _
        _ ≤ R := by linarith
    · have h3 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      rw [Complex.add_im]
      have h4 : -z₀.im < w.im := by
        have := abs_lt.mp (lt_of_le_of_lt h3 h2)
        linarith [this.1]
      linarith
  have habs : Absorbent ℝ B₀ := absorbent_nhds_zero hB₀nhds
  have hbdd : Bornology.IsVonNBounded ℝ B₀ := by
    refine (NormedSpace.isVonNBounded_iff ℝ).mpr ?_
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall
      (x := (0:ℂ)) (r := R + ‖z₀‖)) ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ = ‖(z₀ + w) - z₀‖ := by ring_nf
      _ ≤ ‖z₀ + w‖ + ‖z₀‖ := norm_sub_le _ _
      _ ≤ R + ‖z₀‖ := by
          have := hw.1
          linarith
  have hgpos : ∀ u : ℂ, u ≠ 0 → 0 < gauge B₀ u := fun u hu =>
    (gauge_pos habs hbdd).mpr hu
  have hgcont : Continuous (gauge B₀) := continuous_gauge hconv hB₀nhds
  -- Membership from the gauge.
  have hmemB : ∀ u : ℂ, gauge B₀ u ≤ 1 → u ∈ B₀ := by
    intro u hu
    have hseq : Filter.Tendsto (fun n : ℕ => (1 - 1/(n+2) : ℝ) • u)
        Filter.atTop (nhds u) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 - 1/(n+2) : ℝ))
          Filter.atTop (nhds 1) := by
        have h2 : Filter.Tendsto (fun n : ℕ => (1/(n+2) : ℝ)) Filter.atTop (nhds 0) := by
          have h3 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h4 : (fun n : ℕ => (1/(n+2) : ℝ))
              = fun n : ℕ => 1/((((n+1 : ℕ) : ℝ)) + 1) := by
            funext n
            push_cast
            ring_nf
          rw [h4]
          exact h3.comp (Filter.tendsto_add_atTop_nat 1)
        have h5 := (tendsto_const_nhds (x := (1:ℝ))).sub h2
        rwa [sub_zero] at h5
      have h6 := h1.smul_const u
      simpa using h6
    refine hclosed.mem_of_tendsto hseq ?_
    refine Filter.Eventually.of_forall fun n => ?_
    have hn1 : (0:ℝ) < 1/(n+2) := by positivity
    have hn2 : (1 - 1/(n+2) : ℝ) < 1 := by linarith
    have hn0 : (0:ℝ) ≤ 1 - 1/(n+2) := by
      have h7 : (1/(n+2) : ℝ) ≤ 1/2 := by
        refine one_div_le_one_div_of_le (by norm_num) ?_
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    have h8 : gauge B₀ ((1 - 1/(n+2) : ℝ) • u) < 1 := by
      have h9 : gauge B₀ ((1 - 1/(n+2) : ℝ) • u) = (1 - 1/(n+2) : ℝ) * gauge B₀ u := by
        have h10 := gauge_smul_of_nonneg (s := B₀) hn0 u
        rw [smul_eq_mul] at h10
        exact h10
      rw [h9]
      calc (1 - 1/(n+2) : ℝ) * gauge B₀ u ≤ (1 - 1/(n+2) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hu hn0
        _ < 1 := by linarith
    have h10 := (gauge_lt_one_iff_mem_interior hconv hB₀nhds).mp h8
    exact interior_subset h10
  -- Strict interior points of the body.
  have hsub : interior B₀ ⊆ {w : ℂ | ‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im} := by
    intro w' hw'
    have hw'B : w' ∈ B₀ := interior_subset hw'
    constructor
    · rcases lt_or_eq_of_le hw'B.1 with h | h
      · exact h
      · exfalso
        have hne : z₀ + w' ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at h
          linarith
        have hcont2 : Filter.Tendsto
            (fun ε : ℝ => w' + (ε : ℂ) * (z₀ + w')) (nhdsWithin 0 (Set.Ioi 0))
            (nhds w') := by
          have hc : Continuous (fun ε : ℝ => w' + (ε : ℂ) * (z₀ + w')) := by
            fun_prop
          have h1 := hc.tendsto 0
          have h2 : w' + (((0:ℝ) : ℂ)) * (z₀ + w') = w' := by simp
          rw [h2] at h1
          exact h1.mono_left nhdsWithin_le_nhds
        have hmem := hcont2.eventually (isOpen_interior.mem_nhds hw')
        obtain ⟨ε, hεmem, hεpos⟩ := (hmem.and self_mem_nhdsWithin).exists
        have hεB : w' + (ε : ℂ) * (z₀ + w') ∈ B₀ := interior_subset hεmem
        have hnorm : ‖z₀ + (w' + (ε : ℂ) * (z₀ + w'))‖ = (1 + ε) * ‖z₀ + w'‖ := by
          have h2 : z₀ + (w' + (ε : ℂ) * (z₀ + w')) = ((1 + ε : ℝ) : ℂ) * (z₀ + w') := by
            push_cast
            ring
          rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [hεpos])]
        have h3 := hεB.1
        rw [hnorm, ← h] at h3
        have h4 : (0:ℝ) < ‖z₀ + w'‖ := norm_pos_iff.mpr hne
        have hε0 : (0:ℝ) < ε := hεpos
        nlinarith
    · rcases lt_or_eq_of_le hw'B.2 with h | h
      · exact h
      · exfalso
        have hcont2 : Filter.Tendsto
            (fun ε : ℝ => w' - (ε : ℂ) * Complex.I) (nhdsWithin 0 (Set.Ioi 0))
            (nhds w') := by
          have hc : Continuous (fun ε : ℝ => w' - (ε : ℂ) * Complex.I) := by
            fun_prop
          have h1 := hc.tendsto 0
          have h2 : w' - (((0:ℝ) : ℂ)) * Complex.I = w' := by simp
          rw [h2] at h1
          exact h1.mono_left nhdsWithin_le_nhds
        have hmem := hcont2.eventually (isOpen_interior.mem_nhds hw')
        obtain ⟨ε, hεmem, hεpos⟩ := (hmem.and self_mem_nhdsWithin).exists
        have hεB : w' - (ε : ℂ) * Complex.I ∈ B₀ := interior_subset hεmem
        have h3 := hεB.2
        have h4 : (z₀ + (w' - (ε : ℂ) * Complex.I)).im = (z₀ + w').im - ε := by
          simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]
          ring
        rw [h4, ← h] at h3
        have hε0 : (0:ℝ) < ε := hεpos
        linarith
  -- The gauge is `1` exactly on the non-strict frontier part.
  have hfr1 : ∀ w : ℂ, w ∈ B₀ → ¬(‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im) →
      gauge B₀ w = 1 := by
    intro w hw hnot
    refine le_antisymm (gauge_le_one_of_mem hw) ?_
    by_contra hlt
    push Not at hlt
    exact hnot (hsub ((gauge_lt_one_iff_mem_interior hconv hB₀nhds).mp hlt))
  -- The radial function.
  refine ⟨fun ϑ => (gauge B₀ (Complex.exp (ϑ * Complex.I)))⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : Continuous fun ϑ : ℝ => Complex.exp (ϑ * Complex.I) := by
      fun_prop
    refine (hgcont.comp h1).inv₀ ?_
    intro ϑ
    exact ne_of_gt (hgpos _ (Complex.exp_ne_zero _))
  · intro ϑ
    exact inv_pos.mpr (hgpos _ (Complex.exp_ne_zero _))
  · intro ϑ
    set g1 : ℝ := gauge B₀ (Complex.exp (ϑ * Complex.I)) with hg1def
    have hg1pos : 0 < g1 := hgpos _ (Complex.exp_ne_zero _)
    have hkey : gauge B₀ ((g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I)) = 1 := by
      have h10 := gauge_smul_of_nonneg (s := B₀)
        (le_of_lt (inv_pos.mpr hg1pos)) (Complex.exp (ϑ * Complex.I))
      rw [smul_eq_mul] at h10
      have h11 : gauge B₀ ((g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I))
          = g1⁻¹ * gauge B₀ (Complex.exp (ϑ * Complex.I)) := h10
      rw [h11, ← hg1def, inv_mul_cancel₀ (ne_of_gt hg1pos)]
    have hsm : ((g1⁻¹ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)
        = (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I) := by
      rw [Complex.real_smul]
    have hmem : (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I) ∈ B₀ :=
      hmemB _ (le_of_eq hkey)
    have hnotint : ¬((g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I) ∈ interior B₀) := by
      intro hint
      have := (gauge_lt_one_iff_mem_interior hconv hB₀nhds).mpr hint
      rw [hkey] at this
      exact lt_irrefl 1 this
    have hnotstrict : ¬(‖z₀ + (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I)‖ < R ∧
        0 < (z₀ + (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I)).im) := by
      intro hstrict
      refine hnotint ?_
      have hopen : IsOpen {w : ℂ | ‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im} := by
        refine IsOpen.inter ?_ ?_
        · exact isOpen_lt ((continuous_const.add continuous_id).norm) continuous_const
        · exact isOpen_lt continuous_const
            (Complex.continuous_im.comp (continuous_const.add continuous_id))
      have hsubB : {w : ℂ | ‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im} ⊆ B₀ := by
        intro w hw
        exact ⟨le_of_lt hw.1, le_of_lt hw.2⟩
      exact interior_maximal hsubB hopen hstrict
    rw [hsm]
    refine ⟨hmem.1, hmem.2, ?_⟩
    by_contra hor
    push Not at hor
    exact hnotstrict ⟨lt_of_le_of_ne hmem.1 hor.1, lt_of_le_of_ne hmem.2 (Ne.symm hor.2)⟩
  · intro ϑ t ht htle htim hnot
    have hmem : (t : ℝ) • Complex.exp (ϑ * Complex.I) ∈ B₀ := by
      rw [← Complex.real_smul] at htle htim ⊢
      exact ⟨htle, htim⟩
    have hnot' : ¬(‖z₀ + (t : ℝ) • Complex.exp (ϑ * Complex.I)‖ < R ∧
        0 < (z₀ + (t : ℝ) • Complex.exp (ϑ * Complex.I)).im) := by
      rw [← Complex.real_smul] at hnot
      exact hnot
    have h1 := hfr1 _ hmem hnot'
    have h10 := gauge_smul_of_nonneg (s := B₀) (le_of_lt ht)
      (Complex.exp (ϑ * Complex.I))
    rw [smul_eq_mul] at h10
    have h11 : gauge B₀ ((t : ℝ) • Complex.exp (ϑ * Complex.I))
        = t * gauge B₀ (Complex.exp (ϑ * Complex.I)) := h10
    rw [h11] at h1
    have h2 : gauge B₀ (Complex.exp (ϑ * Complex.I)) = t⁻¹ := by
      field_simp at h1 ⊢
      linarith [h1]
    change (gauge B₀ (Complex.exp (ϑ * Complex.I)))⁻¹ = t
    rw [h2, inv_inv]

/-- A continuous function on an interval with values in `2πiℤ` takes equal
values at the endpoints. -/
theorem disc_const {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hint : ∀ s ∈ Set.Icc a b, ∃ K : ℤ, f s = (K : ℂ) * (2 * Real.pi * Complex.I)) :
    f a = f b := by
  classical
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  -- The normalized imaginary part is an integer-valued continuous function.
  set J : ℝ → ℝ := fun s => (f s).im / (2 * Real.pi) with hJdef
  have hJc : ContinuousOn J (Set.Icc a b) :=
    (Complex.continuous_im.comp_continuousOn hf).div_const _
  have hJint : ∀ s ∈ Set.Icc a b, ∃ K : ℤ, J s = (K : ℝ) := by
    intro s hs
    obtain ⟨K, hK⟩ := hint s hs
    refine ⟨K, ?_⟩
    change (f s).im / (2 * Real.pi) = (K : ℝ)
    have h1 : (f s).im = K * (2 * Real.pi) := by
      rw [hK]
      simp [Complex.mul_im, Complex.mul_re]
    rw [h1]
    field_simp
  -- Equal endpoint values of `J` by the intermediate value theorem.
  have hJab : J a = J b := by
    by_contra hne
    obtain ⟨Ka, hKa⟩ := hJint a (Set.left_mem_Icc.mpr hab)
    obtain ⟨Kb, hKb⟩ := hJint b (Set.right_mem_Icc.mpr hab)
    have hKab : Ka ≠ Kb := by
      intro h
      exact hne (by rw [hKa, hKb, h])
    -- A value strictly between two distinct integers that is not an integer.
    set m : ℝ := (max Ka Kb : ℤ) - 1/2 with hmdef
    have hmmem : m ∈ Set.uIcc (J a) (J b) := by
      rw [Set.mem_uIcc]
      rcases lt_or_gt_of_ne hKab with h | h
      · left
        constructor
        · rw [hKa, hmdef]
          have hZ : Ka ≤ Kb - 1 := by omega
          have h1 : (Ka : ℝ) ≤ (Kb : ℝ) - 1 := by exact_mod_cast hZ
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Kb := by
            rw [max_eq_right (le_of_lt h)]
          rw [h2]
          linarith
        · rw [hKb, hmdef]
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Kb := by
            rw [max_eq_right (le_of_lt h)]
          rw [h2]
          linarith
      · right
        constructor
        · rw [hKb, hmdef]
          have hZ : Kb ≤ Ka - 1 := by omega
          have h1 : (Kb : ℝ) ≤ (Ka : ℝ) - 1 := by exact_mod_cast hZ
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Ka := by
            rw [max_eq_left (le_of_lt h)]
          rw [h2]
          linarith
        · rw [hKa, hmdef]
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Ka := by
            rw [max_eq_left (le_of_lt h)]
          rw [h2]
          linarith
    have hIVT := intermediate_value_uIcc (f := J) (a := a) (b := b)
      (hJc.mono (Set.uIcc_of_le hab).subset)
    obtain ⟨c, hc, hJceq⟩ := hIVT hmmem
    have hcIcc : c ∈ Set.Icc a b := (Set.uIcc_of_le hab).subset hc
    obtain ⟨Kc, hKc⟩ := hJint c hcIcc
    rw [hKc, hmdef] at hJceq
    have h1 : (2 * Kc : ℤ) = 2 * (max Ka Kb) - 1 := by
      have h2 : (2 * (Kc:ℝ)) = 2 * ((max Ka Kb : ℤ):ℝ) - 1 := by linarith
      exact_mod_cast h2
    omega
  -- Endpoint equality of `f` from that of `J`.
  obtain ⟨Ka, hKa⟩ := hint a (Set.left_mem_Icc.mpr hab)
  obtain ⟨Kb, hKb⟩ := hint b (Set.right_mem_Icc.mpr hab)
  have hJa : J a = (Ka : ℝ) := by
    change (f a).im / (2 * Real.pi) = (Ka : ℝ)
    have h1 : (f a).im = Ka * (2 * Real.pi) := by
      rw [hKa]
      simp [Complex.mul_im, Complex.mul_re]
    rw [h1]
    field_simp
  have hJb : J b = (Kb : ℝ) := by
    change (f b).im / (2 * Real.pi) = (Kb : ℝ)
    have h1 : (f b).im = Kb * (2 * Real.pi) := by
      rw [hKb]
      simp [Complex.mul_im, Complex.mul_re]
    rw [h1]
    field_simp
  have hKab : Ka = Kb := by
    have h1 : (Ka : ℝ) = (Kb : ℝ) := by
      rw [← hJa, ← hJb, hJab]
    exact_mod_cast h1
  rw [hKa, hKb, hKab]

-- The crossing-window geometry is one long elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The window-selection argument iterates the contour estimate through a bisection;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- The half-disc radial contour passes through a prescribed
real frontier point at a unique angle in `(π, 2π)`, and near that angle the contour is
real with strictly increasing real part. -/
theorem halfdisc_window (z₀ : ℂ) (hz₀ : 0 < z₀.im) (R : ℝ)
    (rad : ℝ → ℝ) (_hradpos : ∀ ϑ : ℝ, 0 < rad ϑ)
    (hraduniq : ∀ (ϑ t : ℝ), 0 < t →
      ‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ ≤ R →
      0 ≤ (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im →
      ¬(‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ < R ∧
        0 < (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im) →
      rad ϑ = t)
    (q : ℂ) (hqim : q.im = 0) (hqnorm : ‖q‖ < R) (hqzne : q - z₀ ≠ 0) :
    ∃ ϑstar ϑminus ϑplus : ℝ,
      (Real.pi < ϑstar ∧ ϑstar < 2*Real.pi) ∧
      (0 < ϑminus ∧ ϑminus < ϑstar ∧ ϑstar < ϑplus ∧ ϑplus < 2*Real.pi) ∧
      rad ϑstar = ‖q - z₀‖ ∧
      z₀ + ((rad ϑstar : ℝ) : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q ∧
      q - z₀ = ((‖q - z₀‖ : ℝ) : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) ∧
      (∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
        (z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).im = 0) ∧
      (∀ ϑ ϑ' : ℝ, ϑminus ≤ ϑ → ϑ < ϑ' → ϑ' ≤ ϑplus →
        (z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).re
          < (z₀ + ((rad ϑ' : ℝ) : ℂ) * Complex.exp ((ϑ' : ℂ) * Complex.I)).re) := by
  classical
  -- The crossing angle.
  set tstar : ℝ := ‖q - z₀‖ with htstardef
  have htstarpos : 0 < tstar := norm_pos_iff.mpr hqzne
  set ϑstar : ℝ := Complex.arg (q - z₀) + 2*Real.pi with hϑstardef
  have hargneg : Complex.arg (q - z₀) < 0 := by
    rw [Complex.arg_neg_iff]
    rw [Complex.sub_im, hqim]
    linarith
  have harggt : -Real.pi < Complex.arg (q - z₀) := Complex.neg_pi_lt_arg _
  have hϑstarmem : Real.pi < ϑstar ∧ ϑstar < 2*Real.pi := by
    constructor
    · rw [hϑstardef]; linarith
    · rw [hϑstardef]; linarith
  have hϑstarexp : Complex.exp ((ϑstar : ℂ) * Complex.I)
      = Complex.exp ((Complex.arg (q - z₀) : ℂ) * Complex.I) := by
    rw [hϑstardef]
    push_cast
    rw [add_mul, Complex.exp_add]
    have h1 : (2:ℂ) * Real.pi * Complex.I = 2 * ↑Real.pi * Complex.I := by ring
    rw [show ((2:ℂ) * ↑Real.pi) * Complex.I = 2 * ↑Real.pi * Complex.I by ring,
      Complex.exp_two_pi_mul_I, mul_one]
  have hpolar : q - z₀ = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := by
    rw [hϑstarexp, htstardef]
    exact (Complex.norm_mul_exp_arg_mul_I (q - z₀)).symm
  -- The radial function passes through the crossing point.
  have hradstar : rad ϑstar = tstar := by
    refine hraduniq ϑstar tstar htstarpos ?_ ?_ ?_
    · have h1 : z₀ + (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q := by
        rw [← hpolar]
        ring
      rw [h1]
      exact le_of_lt hqnorm
    · have h1 : z₀ + (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q := by
        rw [← hpolar]
        ring
      rw [h1, hqim]
    · have h1 : z₀ + (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q := by
        rw [← hpolar]
        ring
      rw [h1, hqim]
      intro hstrict
      exact lt_irrefl 0 hstrict.2
  set tr : ℝ → ℝ := fun ϑ => -z₀.im / Real.sin ϑ with htrdef
  set η : ℝ → ℂ := fun ϑ => z₀ + (tr ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)
    with hηdef
  have hexpstar : Complex.exp ((ϑstar : ℂ) * Complex.I)
      = (q - z₀) / (tstar : ℂ) := by
    rw [hpolar]
    have h1 : (tstar : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt htstarpos
    field_simp
  have hsinstar : Real.sin ϑstar < 0 := by
    have h1 : Real.sin ϑstar = ((q - z₀) / (tstar : ℂ)).im := by
      rw [← hexpstar]
      exact (Complex.exp_ofReal_mul_I_im ϑstar).symm
    have h2 : ((q - z₀) / (tstar : ℂ)).im = (q - z₀).im / tstar := by
      rw [Complex.div_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      have h3 : (tstar:ℝ) ≠ 0 := ne_of_gt htstarpos
      field_simp
      rw [Complex.normSq_ofReal]
      ring
    have h4 : (q - z₀).im = -z₀.im := by
      rw [Complex.sub_im, hqim]
      ring
    rw [h1, h2, h4]
    have h5 : (0:ℝ) < z₀.im / tstar := div_pos hz₀ htstarpos
    have h6 : -z₀.im / tstar = -(z₀.im / tstar) := by ring
    rw [h6]
    linarith
  have htrstar : tr ϑstar = tstar := by
    rw [htrdef]
    have h1 : Real.sin ϑstar = -z₀.im / tstar := by
      have h2 : Real.sin ϑstar = ((q - z₀) / (tstar : ℂ)).im := by
        rw [← hexpstar]
        exact (Complex.exp_ofReal_mul_I_im ϑstar).symm
      have h3 : ((q - z₀) / (tstar : ℂ)).im = (q - z₀).im / tstar := by
        rw [Complex.div_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im]
        field_simp
        rw [Complex.normSq_ofReal]
        ring
      have h4 : (q - z₀).im = -z₀.im := by
        rw [Complex.sub_im, hqim]
        ring
      rw [h2, h3, h4]
    change -z₀.im / Real.sin ϑstar = tstar
    rw [h1]
    have h5 : z₀.im ≠ 0 := ne_of_gt hz₀
    field_simp
  have hηstar : η ϑstar = q := by
    rw [hηdef]
    change z₀ + (tr ϑstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q
    rw [htrstar, ← hpolar]
    ring
  -- The window: an interval around the crossing angle where the contour is real.
  have hVsin : IsOpen {ϑ : ℝ | Real.sin ϑ < 0} :=
    isOpen_lt Real.continuous_sin continuous_const
  have htrcont : ContinuousOn tr {ϑ : ℝ | Real.sin ϑ < 0} := by
    refine ContinuousOn.div continuousOn_const Real.continuous_sin.continuousOn ?_
    intro ϑ hϑ
    exact ne_of_lt hϑ
  have hηcont : ContinuousOn η {ϑ : ℝ | Real.sin ϑ < 0} := by
    refine ContinuousOn.add continuousOn_const ?_
    refine ContinuousOn.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp_continuousOn htrcont
    · refine Continuous.continuousOn ?_
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal).mul continuous_const)
  have hWopen1 : IsOpen ({ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)) :=
    htrcont.isOpen_inter_preimage hVsin isOpen_Ioi
  have hWopen : IsOpen ({ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)
      ∩ (fun ϑ => ‖η ϑ‖) ⁻¹' (Set.Iio R)) := by
    have h1 : ContinuousOn (fun ϑ => ‖η ϑ‖)
        ({ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)) :=
      (hηcont.mono Set.inter_subset_left).norm
    exact h1.isOpen_inter_preimage hWopen1 isOpen_Iio
  have hstarW : ϑstar ∈ {ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)
      ∩ (fun ϑ => ‖η ϑ‖) ⁻¹' (Set.Iio R) := by
    refine ⟨⟨hsinstar, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, htrstar]
      exact htstarpos
    · rw [Set.mem_preimage, hηstar]
      exact hqnorm
  obtain ⟨ε₀, hε₀pos, hε₀ball⟩ := Metric.isOpen_iff.mp hWopen ϑstar hstarW
  set ε : ℝ := min ε₀ (min ϑstar (2*Real.pi - ϑstar)) with hεdef
  have hεpos : 0 < ε := by
    refine lt_min hε₀pos (lt_min ?_ ?_)
    · linarith [hϑstarmem.1, Real.pi_pos]
    · linarith [hϑstarmem.2]
  have hεball : Metric.ball ϑstar ε ⊆ {ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)
      ∩ (fun ϑ => ‖η ϑ‖) ⁻¹' (Set.Iio R) :=
    subset_trans (Metric.ball_subset_ball (min_le_left _ _)) hε₀ball
  have hεle1 : ε ≤ ϑstar := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle2 : ε ≤ 2*Real.pi - ϑstar := le_trans (min_le_right _ _) (min_le_right _ _)
  set ϑplus : ℝ := ϑstar + ε/2 with hϑplusdef
  set ϑminus : ℝ := ϑstar - ε/2 with hϑminusdef
  have hwin : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
      Real.sin ϑ < 0 ∧ 0 < tr ϑ ∧ ‖η ϑ‖ < R := by
    intro ϑ h1 h2
    have h3 : ϑ ∈ Metric.ball ϑstar ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · rw [hϑminusdef] at h1
        linarith
      · rw [hϑplusdef] at h2
        linarith
    obtain ⟨⟨ha, hb⟩, hc⟩ := hεball h3
    exact ⟨ha, hb, hc⟩
  -- On the window, the contour is the real hit point.
  have hηim : ∀ ϑ : ℝ, Real.sin ϑ < 0 → (η ϑ).im = 0 := by
    intro ϑ hϑ
    change (z₀ + (tr ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).im = 0
    rw [Complex.add_im, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_re]
    have h1 : Real.sin ϑ ≠ 0 := ne_of_lt hϑ
    rw [htrdef]
    field_simp
    ring
  have hradwin : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus → rad ϑ = tr ϑ := by
    intro ϑ h1 h2
    obtain ⟨ha, hb, hc⟩ := hwin ϑ h1 h2
    refine hraduniq ϑ (tr ϑ) hb ?_ ?_ ?_
    · exact le_of_lt hc
    · rw [show z₀ + ((tr ϑ : ℝ) : ℂ) * Complex.exp ((ϑ:ℂ) * Complex.I) = η ϑ from rfl]
      rw [hηim ϑ ha]
    · rw [show z₀ + ((tr ϑ : ℝ) : ℂ) * Complex.exp ((ϑ:ℂ) * Complex.I) = η ϑ from rfl]
      intro hstrict
      rw [hηim ϑ ha] at hstrict
      exact lt_irrefl 0 hstrict.2
  set X : ℝ → ℝ := fun ϑ => z₀.re - z₀.im * (Real.cos ϑ / Real.sin ϑ) with hXdef
  have hηre : ∀ ϑ : ℝ, Real.sin ϑ < 0 → (η ϑ).re = X ϑ := by
    intro ϑ hϑ
    change (z₀ + (tr ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).re = X ϑ
    rw [Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_re]
    have h1 : Real.sin ϑ ≠ 0 := ne_of_lt hϑ
    rw [htrdef, hXdef]
    field_simp
    ring
  have hηofReal : ∀ ϑ : ℝ, Real.sin ϑ < 0 → η ϑ = ((X ϑ : ℝ) : ℂ) := by
    intro ϑ hϑ
    refine Complex.ext ?_ ?_
    · rw [hηre ϑ hϑ]
      simp
    · rw [hηim ϑ hϑ]
      simp
  have hXmono : StrictMonoOn X (Set.Icc ϑminus ϑplus) := by
    have hD : Convex ℝ (Set.Icc ϑminus ϑplus) := convex_Icc _ _
    have hXd : ∀ ϑ ∈ Set.Icc ϑminus ϑplus,
        HasDerivAt X (z₀.im / (Real.sin ϑ)^2) ϑ := by
      intro ϑ hϑ
      have hsin : Real.sin ϑ < 0 := (hwin ϑ hϑ.1 hϑ.2).1
      have hsinne : Real.sin ϑ ≠ 0 := ne_of_lt hsin
      have h1 : HasDerivAt (fun ϑ => Real.cos ϑ / Real.sin ϑ)
          ((-Real.sin ϑ * Real.sin ϑ - Real.cos ϑ * Real.cos ϑ) / (Real.sin ϑ)^2) ϑ :=
        (Real.hasDerivAt_cos ϑ).div (Real.hasDerivAt_sin ϑ) hsinne
      have h2 : HasDerivAt X
          (-(z₀.im * ((-Real.sin ϑ * Real.sin ϑ - Real.cos ϑ * Real.cos ϑ)
            / (Real.sin ϑ)^2))) ϑ := by
        exact ((h1.const_mul z₀.im).neg).const_add z₀.re
      have h3 : -(z₀.im * ((-Real.sin ϑ * Real.sin ϑ - Real.cos ϑ * Real.cos ϑ)
          / (Real.sin ϑ)^2)) = z₀.im / (Real.sin ϑ)^2 := by
        have h4 : Real.sin ϑ * Real.sin ϑ + Real.cos ϑ * Real.cos ϑ = 1 := by
          have := Real.sin_sq_add_cos_sq ϑ
          nlinarith
        field_simp
        nlinarith [h4]
      rw [h3] at h2
      exact h2
    refine strictMonoOn_of_deriv_pos hD ?_ ?_
    · intro ϑ hϑ
      exact (hXd ϑ hϑ).continuousAt.continuousWithinAt
    · intro ϑ hϑ
      rw [interior_Icc] at hϑ
      have hϑ' : ϑ ∈ Set.Icc ϑminus ϑplus := ⟨le_of_lt hϑ.1, le_of_lt hϑ.2⟩
      rw [(hXd ϑ hϑ').deriv]
      have hsin : Real.sin ϑ < 0 := (hwin ϑ hϑ'.1 hϑ'.2).1
      have h5 : (0:ℝ) < (Real.sin ϑ)^2 := by
        have h6 : Real.sin ϑ ≠ 0 := ne_of_lt hsin
        positivity
      exact div_pos hz₀ h5
  have hstarwin : ϑstar ∈ Set.Icc ϑminus ϑplus := by
    constructor
    · rw [hϑminusdef]
      linarith
    · rw [hϑplusdef]
      linarith
  have hϑminus0' : 0 < ϑminus := by
    rw [hϑminusdef]
    linarith [hϑstarmem.1, Real.pi_pos, hεle1]
  have hϑplus2π' : ϑplus < 2*Real.pi := by
    rw [hϑplusdef]
    linarith [hεle2, hεpos]
  have hpolar' : q - z₀ = ((‖q - z₀‖ : ℝ) : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := by
    rw [← htstardef]
    exact hpolar
  -- Packaging.
  refine ⟨ϑstar, ϑminus, ϑplus, hϑstarmem, ⟨hϑminus0', ?_, ?_, hϑplus2π'⟩,
    hradstar, ?_, hpolar', ?_, ?_⟩
  · rw [hϑminusdef]
    linarith [hεpos]
  · rw [hϑplusdef]
    linarith [hεpos]
  · rw [hradstar, ← hpolar']
    ring
  · intro ϑ h1 h2
    have hsin : Real.sin ϑ < 0 := (hwin ϑ h1 h2).1
    have h3 : z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) = η ϑ := by
      rw [hradwin ϑ h1 h2]
    rw [h3]
    exact hηim ϑ hsin
  · intro ϑ ϑ' h1 h2 h3
    have hsin : Real.sin ϑ < 0 := (hwin ϑ h1 (by linarith)).1
    have hsin' : Real.sin ϑ' < 0 := (hwin ϑ' (by linarith) h3).1
    have h4 : z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) = η ϑ := by
      rw [hradwin ϑ h1 (by linarith)]
    have h5 : z₀ + ((rad ϑ' : ℝ) : ℂ) * Complex.exp ((ϑ' : ℂ) * Complex.I) = η ϑ' := by
      rw [hradwin ϑ' (by linarith) h3]
    rw [h4, h5, hηre ϑ hsin, hηre ϑ' hsin']
    exact hXmono ⟨h1, by linarith⟩ ⟨by linarith, h3⟩ h2

/-- The principal branch shift across the negative imaginary side: for `w` in
the open upper half plane, `log w = log (-w) + πi`. -/
theorem log_branch_plus {w : ℂ} (hw : w ≠ 0) (him : 0 < w.im) :
    Complex.log w = Complex.log (-w) + Real.pi * Complex.I := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw
  have hd1 : Complex.exp (Complex.log w
      - (Complex.log (-w) + Real.pi * Complex.I)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hw, Complex.exp_log hnw]
    have h1 : Complex.exp (Real.pi * Complex.I) = -1 := by
      have := Complex.exp_pi_mul_I
      exact_mod_cast this
    rw [h1]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hd1
  have harg1 : 0 < Complex.arg w := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr (le_of_lt him)) with h | h
    · exact h
    · exfalso
      have h1 := Complex.norm_mul_exp_arg_mul_I w
      rw [← h] at h1
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h1
      have h2 : w.im = 0 := by
        rw [← h1]
        simp
      linarith
  have harg2 : Complex.arg w < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi w) with h | h
    · exact h
    · exfalso
      have h1 := Complex.arg_eq_pi_iff.mp h
      linarith [h1.2, him]
  have harg3 : Complex.arg (-w) < 0 := by
    rw [Complex.arg_neg_iff, Complex.neg_im]
    linarith
  have harg4 : -Real.pi < Complex.arg (-w) := Complex.neg_pi_lt_arg _
  have him_eq : (Complex.log w - (Complex.log (-w) + Real.pi * Complex.I)).im
      = Complex.arg w - Complex.arg (-w) - Real.pi := by
    simp only [Complex.sub_im, Complex.add_im, Complex.log_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hn_im : Complex.arg w - Complex.arg (-w) - Real.pi = (n : ℝ) * (2 * Real.pi) := by
    have h2 := congrArg Complex.im hn
    rw [him_eq] at h2
    simpa [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] using h2
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · exfalso
      have h7 : (n:ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      nlinarith
    · exact h
    · exfalso
      have h7 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith
  rw [hn0] at hn
  simp at hn
  linear_combination hn

/-- The mirrored branch shift: for `w` in the open lower half plane,
`log w = log (-w) - πi`. -/
theorem log_branch_minus {w : ℂ} (hw : w ≠ 0) (him : w.im < 0) :
    Complex.log w = Complex.log (-w) - Real.pi * Complex.I := by
  have h1 := log_branch_plus (neg_ne_zero.mpr hw)
    (by rw [Complex.neg_im]; linarith : 0 < (-w).im)
  rw [neg_neg] at h1
  linear_combination -h1

-- The winding computation around the half-disc contour is one long elaboration; the
-- raised budget is required.
set_option maxHeartbeats 400000 in
-- The half-plane preservation proof assembles the contour, window, and winding lemmas;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- The normalized solution of a Teichmüller representative preserves
the upper half plane. The lower branch of the half-plane dichotomy is excluded by a
winding-number computation: the image of a small circle winds `+1` (sense preservation),
while the image of the half-disc contour, whose interior pieces land in the closed lower
half plane far from the base point, winds `-1`. -/
theorem teichRep_w_im_pos {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (u : TeichRep Γ₀) : ∀ z : ℂ, 0 < z.im → 0 < (u.w z).im := by
  classical
  rcases u.w_halfPlane_dichotomy with ⟨hpos, _⟩ | ⟨hneg, _⟩
  · exact hpos
  exfalso
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hwqc : IsQCAnalytic u.w u.b := u.w_isQCAnalytic
  have hwcont : Continuous u.w := hwqc.1.1.continuous
  have hwinj : Function.Injective u.w := hwqc.injective
  set h : ℂ ≃ₜ ℂ := hwqc.1.1.homeomorph u.w with hhdef
  have hhap : ∀ z : ℂ, h z = u.w z := fun z =>
    IsHomeomorph.homeomorph_apply u.w hwqc.1.1 z
  set winv : ℂ → ℂ := ⇑h.symm with hwinvdef
  have hwinv2 : ∀ z : ℂ, u.w (winv z) = z := by
    intro z
    rw [hwinvdef, ← hhap (h.symm z)]
    exact h.apply_symm_apply z
  have hwinv1 : ∀ z : ℂ, winv (u.w z) = z := by
    intro z
    refine hwinj ?_
    rw [hwinv2 (u.w z)]
  -- Real values only at real points.
  have hreal : ∀ z : ℂ, (u.w z).im = 0 → z.im = 0 := by
    intro z h0
    obtain ⟨t, ht⟩ := u.boundary_surjective (u.w z).re
    have htz : u.w (t : ℂ) = u.w z := by
      rw [u.w_ofReal t, ht]
      exact Complex.ext (by simp) (by simp [h0])
    have hz := hwinj htz
    rw [← hz]
    simp
  -- The winding point: a sense-preserving centre in the upper half plane.
  have hsp : SensePreserving u.w := SensePreserving.of_orientationPreservingHomeo hwqc.1
  set Ω : Set ℂ := {z : ℂ | 0 < z.im} with hΩdef
  have hΩopen : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_im
  have hΩpos : (0:ℝ≥0∞) < volume Ω := by
    refine hΩopen.measure_pos volume ⟨Complex.I, ?_⟩
    simp [hΩdef]
  obtain ⟨z₀, hz₀Ω, hz₀P⟩ : ∃ z₀ : ℂ, z₀ ∈ Ω ∧
      (∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), ∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ)
          = u.w (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - u.w z₀) ∧
        L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I) := by
    have h1 := hsp.2
    set Nset : Set ℂ := {z₀ : ℂ | ¬ (∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ)
          = u.w (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - u.w z₀) ∧
        L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I)} with hNdef
    have h2 : volume Nset = 0 := MeasureTheory.ae_iff.mp h1
    have h3 : (Ω \ Nset).Nonempty := by
      refine MeasureTheory.nonempty_of_measure_ne_zero (μ := volume) ?_
      intro h0
      have h4 : volume Ω ≤ volume (Ω \ Nset) + volume Nset := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro z hz
        by_cases hzN : z ∈ Nset
        · exact Or.inr hzN
        · exact Or.inl ⟨hz, hzN⟩
      rw [h0, h2, add_zero] at h4
      exact absurd (le_antisymm h4 (zero_le _)) (ne_of_gt hΩpos)
    obtain ⟨z₀, hz₀Ω, hz₀N⟩ := h3
    exact ⟨z₀, hz₀Ω, not_not.mp hz₀N⟩
  have hz₀im : 0 < z₀.im := hz₀Ω
  -- The radius for the reference circle.
  obtain ⟨r, ⟨hLpack, hrlt⟩, hrpos'⟩ :=
    ((hz₀P.and (nhdsWithin_le_nhds (gt_mem_nhds hz₀im))).and
      self_mem_nhdsWithin).exists
  have hrpos : (0:ℝ) < r := hrpos'
  obtain ⟨L₀, hL₀c, hL₀e, hL₀inc⟩ := hLpack
  -- The image point and its preimage on the real axis.
  set p : ℂ := u.w z₀ with hpdef
  have hpim : p.im < 0 := hneg z₀ hz₀im
  set qhat : ℂ := (p.re : ℂ) with hqhatdef
  set qstar : ℂ := winv qhat with hqstardef
  have hqstarW : u.w qstar = qhat := hwinv2 qhat
  have hqstarim : qstar.im = 0 := by
    refine hreal qstar ?_
    rw [hqstarW, hqhatdef]
    simp
  have hqstarne : qstar - z₀ ≠ 0 := by
    intro h0
    have h1 : qstar = z₀ := by
      have := sub_eq_zero.mp h0
      exact this
    rw [h1] at hqstarim
    rw [hqstarim] at hz₀im
    exact lt_irrefl 0 hz₀im
  -- The outer radius: far points have far images.
  obtain ⟨R₀, hR₀⟩ := (((isCompact_closedBall (0:ℂ) (‖p‖ + 1)).image
    h.symm.continuous).isBounded).subset_closedBall 0
  set R : ℝ := max (max (R₀ + 1) (‖z₀‖ + 2)) (‖qstar‖ + 1) with hRdef
  have hRz₀ : ‖z₀‖ + 1 < R := by
    have h1 : ‖z₀‖ + 2 ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hRq : ‖qstar‖ < R := by
    have h1 : ‖qstar‖ + 1 ≤ R := le_max_right _ _
    linarith
  have hfar : ∀ w : ℂ, ‖w‖ = R → ‖p‖ + 1 < ‖u.w w‖ := by
    intro w hw
    by_contra hle
    push Not at hle
    have h1 : u.w w ∈ Metric.closedBall (0:ℂ) (‖p‖ + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hle
    have h2 : w ∈ ⇑h.symm '' Metric.closedBall (0:ℂ) (‖p‖ + 1) := by
      refine ⟨u.w w, h1, ?_⟩
      exact hwinv1 w
    have h3 := hR₀ h2
    rw [Metric.mem_closedBall, dist_zero_right] at h3
    have h4 : R₀ + 1 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hw] at h3
    linarith
  -- The half-disc contour.
  obtain ⟨rad, hradc, hradpos, hradfr, hraduniq⟩ := halfdisc_radial z₀ hz₀im R hRz₀
  set γ1 : ℝ → ℂ := fun ϑ => z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I) with hγ1def
  set Λ : ℝ → ℂ := fun ϑ => u.w (γ1 ϑ) with hΛdef
  -- The interpolating family and its lift.
  set H : ℝ → ℝ → ℂ := fun s ϑ =>
    u.w (z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)) - p
    with hHdef
  have hρpos : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ ϑ : ℝ, 0 < (1-s)*r + s*rad ϑ := by
    intro s hs ϑ
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0]
      simpa using hrpos
    · have h1 : 0 < s * rad ϑ := mul_pos h0 (hradpos ϑ)
      have h2 : 0 ≤ (1-s)*r := mul_nonneg (by linarith [hs.2]) (le_of_lt hrpos)
      linarith
  have hHcont : ContinuousOn (Function.uncurry H)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2*Real.pi)) := by
    refine Continuous.continuousOn ?_
    refine Continuous.sub ?_ continuous_const
    refine hwcont.comp ?_
    refine Continuous.add continuous_const ?_
    refine Continuous.mul ?_ ?_
    · refine Complex.continuous_ofReal.comp ?_
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub continuous_fst).mul continuous_const
      · exact continuous_fst.mul (hradc.comp continuous_snd)
    · refine Complex.continuous_exp.comp ?_
      exact (Complex.continuous_ofReal.comp continuous_snd).mul continuous_const
  have hHne : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), H s ϑ ≠ 0 := by
    intro s hs ϑ _
    rw [hHdef]
    intro h0
    have h1 : u.w (z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I))
        = u.w z₀ := by
      rw [← hpdef]
      exact sub_eq_zero.mp h0
    have h2 := hwinj h1
    have h3 : (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I) = 0 := by
      have h4 : z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)
          - z₀ = 0 := by
        rw [h2]
        ring
      calc (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)
          = z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I) - z₀ := by
            ring
        _ = 0 := h4
    rcases mul_eq_zero.mp h3 with h5 | h5
    · have h6 : ((1-s)*r + s*rad ϑ : ℝ) = 0 := by exact_mod_cast h5
      have h7 := hρpos s hs ϑ
      rw [h6] at h7
      exact lt_irrefl 0 h7
    · exact Complex.exp_ne_zero _ h5
  obtain ⟨L, hLc, hLe⟩ := continuous_log_lift_param_of_continuous_ne_zero
    (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ 2*Real.pi) H hHcont hHne
  -- The endpoint increments are constant in the parameter.
  have hmemθ : ∀ ϑ : ℝ, ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi) → True := fun _ _ => trivial
  have h2πmem : (2*Real.pi : ℝ) ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    Set.right_mem_Icc.mpr (by positivity)
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    Set.left_mem_Icc.mpr (by positivity)
  have hexp02π : Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((0:ℝ) : ℂ) * Complex.I) := by
    push_cast
    rw [Complex.exp_two_pi_mul_I]
    simp
  have hradper : rad 0 = rad (2*Real.pi) := by
    obtain ⟨ha1, ha2, ha3⟩ := hradfr (2*Real.pi)
    refine hraduniq 0 (rad (2*Real.pi)) (hradpos _) ?_ ?_ ?_
    · rw [show Complex.exp (((0:ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I) from hexp02π.symm]
      exact ha1
    · rw [show Complex.exp (((0:ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I) from hexp02π.symm]
      exact ha2
    · rw [show Complex.exp (((0:ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I) from hexp02π.symm]
      intro hstrict
      rcases ha3 with h | h
      · exact absurd h (ne_of_lt hstrict.1)
      · exact absurd h (ne_of_gt hstrict.2)
  have hHper : ∀ s ∈ Set.Icc (0:ℝ) 1, H s (2*Real.pi) = H s 0 := by
    intro s _
    change u.w (z₀ + (((1-s)*r + s*rad (2*Real.pi) : ℝ) : ℂ)
        * Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I)) - p
      = u.w (z₀ + (((1-s)*r + s*rad 0 : ℝ) : ℂ)
        * Complex.exp (((0:ℝ) : ℂ) * Complex.I)) - p
    rw [hexp02π, ← hradper]
  have h0mem1 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
  have h1mem1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.right_mem_Icc.mpr (by norm_num)
  -- The endpoint increment is constant along the interpolation.
  set Inc : ℝ → ℂ := fun s => L s (2*Real.pi) - L s 0 with hIncdef
  have hIncint : ∀ s ∈ Set.Icc (0:ℝ) 1, ∃ K : ℤ,
      Inc s = (K : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    have h1 : Complex.exp (L s 0) = Complex.exp (L s (2*Real.pi)) := by
      rw [hLe s hs 0 h0mem, hLe s hs _ h2πmem, hHper s hs]
    exact winding_lift_integer_coeff (L s) h1
  have hInccont : ContinuousOn Inc (Set.Icc (0:ℝ) 1) := by
    refine Continuous.continuousOn ?_
    refine Continuous.sub ?_ ?_
    · exact hLc.comp (continuous_id.prodMk continuous_const)
    · exact hLc.comp (continuous_id.prodMk continuous_const)
  have hIncconst : Inc 0 = Inc 1 :=
    disc_const (by norm_num) hInccont hIncint
  -- The base increment is `2πi`, by uniqueness of lifts against the reference lift.
  have hH0 : ∀ ϑ : ℝ, H 0 ϑ
      = u.w (z₀ + (r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)) - u.w z₀ := by
    intro ϑ
    change u.w (z₀ + (((1-0)*r + 0*rad ϑ : ℝ) : ℂ) * Complex.exp (↑ϑ * Complex.I)) - p
      = u.w (z₀ + (r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)) - u.w z₀
    rw [hpdef]
    norm_num
  have hI0 : Inc 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    have hd_int : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), ∃ K : ℤ,
        (L 0 ϑ - L₀ ϑ) = (K : ℂ) * (2 * Real.pi * Complex.I) := by
      intro ϑ hϑ
      have h1 : Complex.exp (L₀ ϑ) = Complex.exp (L 0 ϑ) := by
        rw [hLe 0 h0mem1 ϑ hϑ, hL₀e ϑ, hH0 ϑ]
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
      refine ⟨-n, ?_⟩
      rw [hn]
      push_cast
      ring
    have hdc : ContinuousOn (fun ϑ => L 0 ϑ - L₀ ϑ) (Set.Icc (0:ℝ) (2*Real.pi)) := by
      refine Continuous.continuousOn ?_
      exact (hLc.comp (continuous_const.prodMk continuous_id)).sub hL₀c
    have hd := disc_const (by positivity) hdc hd_int
    have h2 : Inc 0 = (L 0 (2*Real.pi) - L₀ (2*Real.pi)) - (L 0 0 - L₀ 0)
        + (L₀ (2*Real.pi) - L₀ 0) := by
      rw [hIncdef]
      ring
    rw [h2, ← hd, hL₀inc]
    ring
  -- The crossing angle, from the window lemma.
  obtain ⟨ϑstar, ϑminus, ϑplus, hϑstarmem, hwinb, hradstar0, hγ1stareq, hpolar0,
    hwinim, hwinmono⟩ :=
    halfdisc_window z₀ hz₀im R rad hradpos hraduniq qstar hqstarim hRq hqstarne
  set tstar : ℝ := ‖qstar - z₀‖ with htstardef
  have htstarpos : 0 < tstar := norm_pos_iff.mpr hqstarne
  have hradstar : rad ϑstar = tstar := hradstar0
  have hpolar : qstar - z₀ = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) :=
    hpolar0
  have hγ1star : γ1 ϑstar = qstar := hγ1stareq
  have hΛstar : Λ ϑstar = qhat := by
    change u.w (γ1 ϑstar) = qhat
    rw [hγ1star]
    exact hqstarW
  have hγpos : ∀ ϑ : ℝ, 0 ≤ (γ1 ϑ).im ∧ ‖γ1 ϑ‖ ≤ R ∧
      ((γ1 ϑ).im = 0 ∨ ‖γ1 ϑ‖ = R) := by
    intro ϑ
    obtain ⟨h1, h2, h3⟩ := hradfr ϑ
    refine ⟨h2, h1, ?_⟩
    rcases h3 with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hΛim : ∀ ϑ : ℝ, (Λ ϑ).im ≤ 0 := by
    intro ϑ
    rcases lt_or_eq_of_le (hγpos ϑ).1 with h | h
    · exact le_of_lt (hneg _ h)
    · have h1 : γ1 ϑ = ((γ1 ϑ).re : ℂ) := Complex.ext (by simp) (by simp [h.symm])
      rw [hΛdef]
      change (u.w (γ1 ϑ)).im ≤ 0
      rw [h1]
      rw [u.w_real (γ1 ϑ).re]
  have hΛreal : ∀ ϑ : ℝ, (γ1 ϑ).im = 0 → (Λ ϑ).im = 0 := by
    intro ϑ h
    have h1 : γ1 ϑ = ((γ1 ϑ).re : ℂ) := Complex.ext (by simp) (by simp [h.symm])
    rw [hΛdef]
    change (u.w (γ1 ϑ)).im = 0
    rw [h1]
    exact u.w_real (γ1 ϑ).re
  have hΛfar : ∀ ϑ : ℝ, ‖γ1 ϑ‖ = R → ‖p‖ + 1 < ‖Λ ϑ‖ := fun ϑ h => hfar _ h
  -- Off-ray characterization: the ray only meets the image at the crossing angle.
  have honray : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), ϑ ≠ ϑstar →
      ¬((Λ ϑ - p).re = 0 ∧ 0 ≤ (Λ ϑ - p).im) := by
    intro ϑ hϑ hne hray
    have him : 0 ≤ (Λ ϑ).im - p.im := by
      have := hray.2
      rwa [Complex.sub_im] at this
    have hre : (Λ ϑ).re = p.re := by
      have := hray.1
      rw [Complex.sub_re] at this
      linarith
    rcases (hγpos ϑ).2.2 with hγreal | hγfar
    · -- Real piece: forces the crossing point, contradicting `ϑ ≠ ϑstar`.
      have hΛr : (Λ ϑ).im = 0 := hΛreal ϑ hγreal
      have hΛeq : Λ ϑ = qhat := by
        refine Complex.ext ?_ ?_
        · rw [hre, hqhatdef]
          simp
        · rw [hΛr, hqhatdef]
          simp
      have hγeq : γ1 ϑ = qstar := by
        refine hwinj ?_
        have h1 : u.w (γ1 ϑ) = qhat := hΛeq
        rw [h1, hqstarW]
      have hprod : (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)
          = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := by
        have h2 : z₀ + (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) = qstar := hγeq
        calc (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)
            = z₀ + (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) - z₀ := by ring
          _ = qstar - z₀ := by rw [h2]
          _ = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := hpolar
      have hradt : rad ϑ = tstar := by
        have h3 := congrArg norm hprod
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
          mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (hradpos ϑ), abs_of_pos htstarpos] at h3
        exact h3
      have hexpeq : Complex.exp ((ϑ : ℂ) * Complex.I)
          = Complex.exp ((ϑstar : ℂ) * Complex.I) := by
        rw [hradt] at hprod
        refine mul_left_cancel₀ ?_ hprod
        exact_mod_cast ne_of_gt htstarpos
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexpeq
      have h5 : ϑ = ϑstar + n * (2*Real.pi) := by
        have h6 := congrArg Complex.im hn
        simpa [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] using h6
      have hn0 : n = 0 := by
        rcases lt_trichotomy n 0 with h | h | h
        · exfalso
          have h7 : (n:ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
          have h8 := hϑ.1
          nlinarith [hϑstarmem.2, hπ]
        · exact h
        · exfalso
          have h7 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
          have h8 := hϑ.2
          nlinarith [hϑstarmem.1, hπ]
      rw [hn0] at h5
      push_cast at h5
      have h9 : ϑ = ϑstar := by linarith [h5]
      exact hne h9
    · -- Far piece: the ray segment lies inside the ball of radius `‖p‖`.
      have hf := hΛfar ϑ hγfar
      have h1 : ‖Λ ϑ‖^2 = (Λ ϑ).re^2 + (Λ ϑ).im^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have h2 : ‖p‖^2 = p.re^2 + p.im^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have h3 := hΛim ϑ
      have h4 : p.im ≤ (Λ ϑ).im := by linarith [him]
      have h5 : (Λ ϑ).im^2 ≤ p.im^2 := by nlinarith
      have hb : (0:ℝ) < ‖p‖ + 1 := by positivity
      have h6 : (‖p‖+1)^2 < ‖Λ ϑ‖^2 := by nlinarith
      have h7 : ‖Λ ϑ‖^2 ≤ ‖p‖^2 := by
        rw [h1, h2, hre]
        linarith
      nlinarith [norm_nonneg p]
  -- The real-hit window around the crossing angle.
  -- Consequences of the window structure for the image curve.
  have hΛwinim : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus → (Λ ϑ).im = 0 := by
    intro ϑ h1 h2
    exact hΛreal ϑ (hwinim ϑ h1 h2)
  have hγre : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
      Λ ϑ = ((u.boundary ((γ1 ϑ).re) : ℝ) : ℂ) := by
    intro ϑ h1 h2
    have h3 : γ1 ϑ = (((γ1 ϑ).re : ℝ) : ℂ) := by
      refine Complex.ext (by simp) ?_
      have h4 : (γ1 ϑ).im = 0 := hwinim ϑ h1 h2
      rw [h4]
      simp
    change u.w (γ1 ϑ) = ((u.boundary ((γ1 ϑ).re) : ℝ) : ℂ)
    conv_lhs => rw [h3]
    rw [u.w_ofReal]
  have hsw1 : ϑminus ≤ ϑstar := le_of_lt hwinb.2.1
  have hsw2 : ϑstar ≤ ϑplus := le_of_lt hwinb.2.2.1
  have hbstar : u.boundary ((γ1 ϑstar).re) = p.re := by
    have h1 : ((u.boundary ((γ1 ϑstar).re) : ℝ) : ℂ) = qhat := by
      rw [← hγre ϑstar hsw1 hsw2, hΛstar]
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re, hqhatdef] at h2
    simpa using h2
  have hxileft : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ < ϑstar → (Λ ϑ).re < p.re := by
    intro ϑ h1 h2
    have h3 := hwinmono ϑ ϑstar h1 h2 hsw2
    have h4 : (γ1 ϑ).re < (γ1 ϑstar).re := h3
    have h5 := u.boundary_strictMono h4
    rw [hγre ϑ h1 (by linarith), Complex.ofReal_re, ← hbstar]
    exact h5
  have hxiright : ∀ ϑ : ℝ, ϑstar < ϑ → ϑ ≤ ϑplus → p.re < (Λ ϑ).re := by
    intro ϑ h1 h2
    have h3 := hwinmono ϑstar ϑ hsw1 h1 h2
    have h4 : (γ1 ϑstar).re < (γ1 ϑ).re := h3
    have h5 := u.boundary_strictMono h4
    rw [hγre ϑ (by linarith) h2, Complex.ofReal_re, ← hbstar]
    exact h5
  have hϑminus0 : 0 < ϑminus := hwinb.1
  have hϑplus2π : ϑplus < 2*Real.pi := hwinb.2.2.2
  -- The lift at `s = 1` and the branch logarithms.
  have hH1 : ∀ ϑ : ℝ, H 1 ϑ = Λ ϑ - p := by
    intro ϑ
    change u.w (z₀ + (((1-1)*r + 1*rad ϑ : ℝ) : ℂ) * Complex.exp (↑ϑ * Complex.I)) - p
      = Λ ϑ - p
    have h1 : ((1-1)*r + 1*rad ϑ : ℝ) = rad ϑ := by ring
    rw [h1]
  have hΛcont : Continuous Λ := by
    change Continuous fun ϑ => u.w (γ1 ϑ)
    refine hwcont.comp ?_
    refine Continuous.add continuous_const ?_
    exact (Complex.continuous_ofReal.comp hradc).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
  have hL1cont : Continuous (fun ϑ => L 1 ϑ) :=
    hLc.comp (continuous_const.prodMk continuous_id)
  have hL1exp : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (L 1 ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    rw [hLe 1 h1mem1 ϑ hϑ, hH1 ϑ]
  have hΛne : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), Λ ϑ - p ≠ 0 := by
    intro ϑ hϑ
    rw [← hH1 ϑ]
    exact hHne 1 h1mem1 ϑ hϑ
  have hslit : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), ϑ ≠ ϑstar →
      Complex.I * (Λ ϑ - p) ∈ Complex.slitPlane := by
    intro ϑ hϑ hne
    rw [Complex.mem_slitPlane_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h3 : (Complex.I * (Λ ϑ - p)).re = -(Λ ϑ - p).im := by
      rw [Complex.mul_re]
      simp
    have h4 : (Complex.I * (Λ ϑ - p)).im = (Λ ϑ - p).re := by
      rw [Complex.mul_im]
      simp
    refine honray ϑ hϑ hne ⟨?_, ?_⟩
    · rw [← h4]
      exact h2
    · rw [h3] at h1
      linarith
  set ℓb : ℝ → ℂ := fun ϑ =>
    Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I with hℓbdef
  set ℓp : ℝ → ℂ := fun ϑ =>
    Complex.log (-(Complex.I * (Λ ϑ - p))) + Real.pi * Complex.I
      - Complex.log Complex.I with hℓpdef
  set ℓm : ℝ → ℂ := fun ϑ =>
    Complex.log (-(Complex.I * (Λ ϑ - p))) - Real.pi * Complex.I
      - Complex.log Complex.I with hℓmdef
  have hexpℓb : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (ℓb ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    change Complex.exp (Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I)
      = Λ ϑ - p
    rw [Complex.exp_sub, Complex.exp_log (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ)),
      Complex.exp_log Complex.I_ne_zero]
    field_simp
  have hexpℓp : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (ℓp ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    change Complex.exp (Complex.log (-(Complex.I * (Λ ϑ - p))) + Real.pi * Complex.I
      - Complex.log Complex.I) = Λ ϑ - p
    rw [Complex.exp_sub, Complex.exp_add,
      Complex.exp_log (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ))),
      Complex.exp_log Complex.I_ne_zero]
    have h1 : Complex.exp (Real.pi * Complex.I) = -1 := by
      have := Complex.exp_pi_mul_I
      exact_mod_cast this
    rw [h1]
    field_simp
  have hexpℓm : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (ℓm ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    change Complex.exp (Complex.log (-(Complex.I * (Λ ϑ - p))) - Real.pi * Complex.I
      - Complex.log Complex.I) = Λ ϑ - p
    rw [Complex.exp_sub, Complex.exp_sub,
      Complex.exp_log (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ))),
      Complex.exp_log Complex.I_ne_zero]
    have h1 : Complex.exp (Real.pi * Complex.I) = -1 := by
      have := Complex.exp_pi_mul_I
      exact_mod_cast this
    rw [h1]
    field_simp
  -- Branch matching on the two half-windows.
  have hbranchp : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      0 < (Complex.I * (Λ ϑ - p)).im → ℓb ϑ = ℓp ϑ := by
    intro ϑ hϑ him
    have h1 := log_branch_plus
      (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ)) him
    change Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I
      = Complex.log (-(Complex.I * (Λ ϑ - p))) + Real.pi * Complex.I
        - Complex.log Complex.I
    rw [h1]
  have hbranchm : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      (Complex.I * (Λ ϑ - p)).im < 0 → ℓb ϑ = ℓm ϑ := by
    intro ϑ hϑ him
    have h1 := log_branch_minus
      (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ)) him
    change Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I
      = Complex.log (-(Complex.I * (Λ ϑ - p))) - Real.pi * Complex.I
        - Complex.log Complex.I
    rw [h1]
  have hIim : ∀ ϑ : ℝ, (Complex.I * (Λ ϑ - p)).im = (Λ ϑ).re - p.re := by
    intro ϑ
    rw [Complex.mul_im]
    simp [Complex.sub_re]
  have hmIcc : ϑminus ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    ⟨le_of_lt hϑminus0, by linarith [hsw1, hsw2, hϑplus2π]⟩
  have hpIcc : ϑplus ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    ⟨by linarith [hϑminus0, hsw1, hsw2], le_of_lt hϑplus2π⟩
  have hsubp : ℓb ϑplus = ℓp ϑplus := by
    refine hbranchp ϑplus hpIcc ?_
    rw [hIim]
    linarith [hxiright ϑplus hwinb.2.2.1 (le_refl ϑplus)]
  have hsubm : ℓb ϑminus = ℓm ϑminus := by
    refine hbranchm ϑminus hmIcc ?_
    rw [hIim]
    linarith [hxileft ϑminus (le_refl ϑminus) hwinb.2.1]
  -- Continuity of the branch pieces.
  have hℓbcont : ∀ (a b : ℝ), 0 ≤ a → b ≤ 2*Real.pi →
      (∀ ϑ, a ≤ ϑ → ϑ ≤ b → ϑ ≠ ϑstar) → ContinuousOn ℓb (Set.Icc a b) := by
    intro a b ha hb hne ϑ hϑ
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun ϑ => Complex.I * (Λ ϑ - p)) ϑ :=
      (continuous_const.mul (hΛcont.sub continuous_const)).continuousAt
    have h2 := ContinuousAt.clog h1
      (hslit ϑ ⟨le_trans ha hϑ.1, le_trans hϑ.2 hb⟩ (hne ϑ hϑ.1 hϑ.2))
    exact h2.sub continuousAt_const
  have hslitm : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
      -(Complex.I * (Λ ϑ - p)) ∈ Complex.slitPlane := by
    intro ϑ h1 h2
    rw [Complex.mem_slitPlane_iff]
    left
    have h3 : (-(Complex.I * (Λ ϑ - p))).re = (Λ ϑ - p).im := by
      rw [Complex.neg_re, Complex.mul_re]
      simp
    rw [h3, Complex.sub_im, hΛwinim ϑ h1 h2]
    linarith [hpim]
  have hℓpcont : ContinuousOn ℓp (Set.Icc ϑstar ϑplus) := by
    intro ϑ hϑ
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun ϑ => -(Complex.I * (Λ ϑ - p))) ϑ :=
      ((continuous_const.mul (hΛcont.sub continuous_const)).neg).continuousAt
    have h2 := ContinuousAt.clog h1 (hslitm ϑ (le_trans hsw1 hϑ.1) hϑ.2)
    exact (h2.add continuousAt_const).sub continuousAt_const
  have hℓmcont : ContinuousOn ℓm (Set.Icc ϑminus ϑstar) := by
    intro ϑ hϑ
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun ϑ => -(Complex.I * (Λ ϑ - p))) ϑ :=
      ((continuous_const.mul (hΛcont.sub continuous_const)).neg).continuousAt
    have h2 := ContinuousAt.clog h1 (hslitm ϑ hϑ.1 (le_trans hϑ.2 hsw2))
    exact (h2.sub continuousAt_const).sub continuousAt_const
  -- Integer-valued quotients against the lift.
  have hint4 : ∀ (G : ℝ → ℂ) (a b : ℝ), 0 ≤ a → b ≤ 2*Real.pi →
      (∀ ϑ, a ≤ ϑ → ϑ ≤ b → Complex.exp (G ϑ) = Λ ϑ - p) →
      ∀ s ∈ Set.Icc a b, ∃ K : ℤ, L 1 s - G s = (K:ℂ) * (2 * Real.pi * Complex.I) := by
    intro G a b ha hb hG s hs
    have hsIcc : s ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
      ⟨le_trans ha hs.1, le_trans hs.2 hb⟩
    have h1 : Complex.exp (L 1 s - G s) = 1 := by
      rw [Complex.exp_sub, hL1exp s hsIcc, hG s hs.1 hs.2]
      exact div_self (hΛne s hsIcc)
    exact Complex.exp_eq_one_iff.mp h1
  -- The four piece constancies.
  have hp1 : L 1 0 - ℓb 0 = L 1 ϑminus - ℓb ϑminus := by
    refine disc_const (le_of_lt hϑminus0)
      ((hL1cont.continuousOn).sub (hℓbcont 0 ϑminus (le_refl 0) hmIcc.2 ?_)) ?_
    · intro ϑ h1 h2 h3
      rw [h3] at h2
      linarith [hwinb.2.1]
    · exact hint4 ℓb 0 ϑminus (le_refl 0) hmIcc.2
        (fun ϑ h1 h2 => hexpℓb ϑ ⟨h1, by linarith [hmIcc.2]⟩)
  have hp2 : L 1 ϑminus - ℓm ϑminus = L 1 ϑstar - ℓm ϑstar := by
    refine disc_const hsw1 ((hL1cont.continuousOn).sub hℓmcont) ?_
    exact hint4 ℓm ϑminus ϑstar (le_of_lt hϑminus0)
      (by linarith [hϑstarmem.2])
      (fun ϑ h1 h2 => hexpℓm ϑ ⟨by linarith [hϑminus0], by linarith [hϑstarmem.2]⟩)
  have hp3 : L 1 ϑstar - ℓp ϑstar = L 1 ϑplus - ℓp ϑplus := by
    refine disc_const hsw2 ((hL1cont.continuousOn).sub hℓpcont) ?_
    exact hint4 ℓp ϑstar ϑplus (by linarith [hϑminus0, hsw1])
      (le_of_lt hϑplus2π)
      (fun ϑ h1 h2 => hexpℓp ϑ ⟨by linarith [hϑminus0, hsw1], by linarith [hϑplus2π]⟩)
  have hp4 : L 1 ϑplus - ℓb ϑplus = L 1 (2*Real.pi) - ℓb (2*Real.pi) := by
    refine disc_const (le_of_lt hϑplus2π)
      ((hL1cont.continuousOn).sub (hℓbcont ϑplus (2*Real.pi) hpIcc.1 (le_refl _) ?_)) ?_
    · intro ϑ h1 h2 h3
      rw [h3] at h1
      linarith [hwinb.2.2.1]
    · exact hint4 ℓb ϑplus (2*Real.pi) hpIcc.1 (le_refl _)
        (fun ϑ h1 h2 => hexpℓb ϑ ⟨le_trans hpIcc.1 h1, h2⟩)
  -- Periodicity of the base branch.
  have hΛper : Λ (2*Real.pi) = Λ 0 := by
    change u.w (γ1 (2*Real.pi)) = u.w (γ1 0)
    have h1 : γ1 (2*Real.pi) = γ1 0 := by
      change z₀ + (rad (2*Real.pi) : ℂ) * Complex.exp (((2*Real.pi:ℝ) : ℂ) * Complex.I)
        = z₀ + (rad 0 : ℂ) * Complex.exp (((0:ℝ) : ℂ) * Complex.I)
      rw [hexp02π, ← hradper]
    rw [h1]
  have hℓbper : ℓb (2*Real.pi) = ℓb 0 := by
    change Complex.log (Complex.I * (Λ (2*Real.pi) - p)) - Complex.log Complex.I
      = Complex.log (Complex.I * (Λ 0 - p)) - Complex.log Complex.I
    rw [hΛper]
  -- The endpoint increment at `s = 1`.
  have hInc1 : Inc 1 = -(2 * (Real.pi:ℂ) * Complex.I) := by
    have e5 : ℓm ϑstar - ℓp ϑstar = -(2*(Real.pi:ℂ)*Complex.I) := by
      change (Complex.log (-(Complex.I * (Λ ϑstar - p))) - Real.pi * Complex.I
          - Complex.log Complex.I)
        - (Complex.log (-(Complex.I * (Λ ϑstar - p))) + Real.pi * Complex.I
          - Complex.log Complex.I) = -(2*(Real.pi:ℂ)*Complex.I)
      ring
    have hIncdef1 : Inc 1 = L 1 (2*Real.pi) - L 1 0 := rfl
    rw [hIncdef1]
    linear_combination -hp4 - hp1 - hp3 - hp2 - hsubp + hℓbper + hsubm + e5
  -- The contradiction.
  have hcontra : (2 : ℂ) * Real.pi * Complex.I = -(2 * (Real.pi:ℂ) * Complex.I) := by
    calc (2 : ℂ) * Real.pi * Complex.I = Inc 0 := hI0.symm
      _ = Inc 1 := hIncconst
      _ = -(2 * (Real.pi:ℂ) * Complex.I) := hInc1
  have him2 := congrArg Complex.im hcontra
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_im, Complex.re_ofNat,
    Complex.im_ofNat] at him2
  nlinarith [hπ, him2]

/-- **Factorization.** If the normalized solution of a Teichmüller representative and an
upper-half-plane quasiconformal map solve the same Beltrami equation almost everywhere on
the upper half plane, they differ by a real Möbius map: their quotient is conformal by the
Weyl lemma and is a holomorphic self-homeomorphism of the upper half plane, hence Möbius. -/
theorem exists_sl2_factorization_of_eq_coeff
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (u : TeichRep Γ₀)
    {v vinv : ℂ → ℂ} {κ : ℝ} (_hκ : κ < 1) (hv : IsQCUpper v vinv κ)
    (hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar v z = u.b.μ z * dz v z) :
    ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → u.w z = moebiusMap R (v z) := by
  classical
  have hpos : ∀ z : ℂ, 0 < z.im → 0 < (u.w z).im := teichRep_w_im_pos u
  have hwqc : IsQCAnalytic u.w u.b := u.w_isQCAnalytic
  have hwcont : Continuous u.w := hwqc.1.1.continuous
  have hwinj : Function.Injective u.w := hwqc.injective
  set h : ℂ ≃ₜ ℂ := hwqc.1.1.homeomorph u.w with hhdef
  have hhap : ∀ z : ℂ, h z = u.w z := fun z =>
    IsHomeomorph.homeomorph_apply u.w hwqc.1.1 z
  set uinv : ℂ → ℂ := ⇑h.symm with huinvdef
  have huinvc : Continuous uinv := h.symm.continuous
  have hui2 : ∀ z : ℂ, u.w (uinv z) = z := by
    intro z
    rw [huinvdef, ← hhap (h.symm z)]
    exact h.apply_symm_apply z
  have hui1 : ∀ z : ℂ, uinv (u.w z) = z := by
    intro z
    refine hwinj ?_
    rw [hui2 (u.w z)]
  -- The inverse preserves the open upper half plane.
  have huinvpos : ∀ z : ℂ, 0 < z.im → 0 < (uinv z).im := by
    intro z hz
    rcases lt_trichotomy (uinv z).im 0 with hlt | heq | hgt
    · exfalso
      have h1 : 0 < (starRingEnd ℂ (uinv z)).im := by
        rw [Complex.conj_im]; linarith
      have h2 := hpos _ h1
      rw [u.w_conj, hui2 z, Complex.conj_im] at h2
      linarith
    · exfalso
      have h1 : ((uinv z).re : ℂ) = uinv z :=
        Complex.ext (by simp) (by simp [heq])
      have h4 := u.w_ofReal ((uinv z).re)
      rw [h1, hui2 z] at h4
      have h5 : z.im = 0 := by rw [h4]; simp
      linarith
    · exact hgt
  -- The composite `v ∘ uinv` is holomorphic on the upper half plane by the Weyl lemma.
  have hψholo : DifferentiableOn ℂ (fun w => v (uinv w)) {z : ℂ | 0 < z.im} :=
    composite_holomorphic u hv hcoeff hpos huinvc hui1 hui2
  have hψmaps : ∀ z : ℂ, 0 < z.im → 0 < (v (uinv z)).im := fun z hz =>
    hv.mapsTo _ (huinvpos z hz)
  have hθmaps : ∀ z : ℂ, 0 < z.im → 0 < (u.w (vinv z)).im := fun z hz =>
    hpos _ (hv.mapsTo' z hz)
  have hθψ : ∀ z : ℂ, 0 < z.im → u.w (vinv (v (uinv z))) = z := by
    intro z hz
    rw [hv.left_inv _ (huinvpos z hz), hui2 z]
  have hψθ : ∀ z : ℂ, 0 < z.im → v (uinv (u.w (vinv z))) = z := by
    intro z hz
    rw [hui1 (vinv z)]
    exact hv.right_inv z hz
  have hθcont : ContinuousOn (fun w => u.w (vinv w)) {z : ℂ | 0 < z.im} := by
    intro w hw
    exact (hwcont.continuousAt).comp_continuousWithinAt (hv.cont' w hw)
  obtain ⟨A, hA⟩ := holo_upper_selfmap_moebius (ψ := fun w => v (uinv w))
    (θ := fun w => u.w (vinv w)) hψholo hψmaps hθmaps hθψ hψθ hθcont
  refine ⟨A⁻¹, ?_⟩
  intro z hz
  have h1 : 0 < (u.w z).im := hpos z hz
  have h3 : v z = moebiusMap A (u.w z) := by
    have h4 := hA (u.w z) h1
    have h5 : (fun w => v (uinv w)) (u.w z) = v z := by
      change v (uinv (u.w z)) = v z
      rw [hui1 z]
    rw [← h5]
    exact h4
  have hden : moebiusDenom A (u.w z) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero A (ne_of_gt h1)
  rw [h3, moebiusMap_mul A⁻¹ A (u.w z) hden, inv_mul_cancel, moebiusMap_one]

end RiemannDynamics

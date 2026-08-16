/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Symmetry.Slicing

/-!
# The tangent winding number of a simple closed loop

The secant map and its band estimates, the tangent winding number at a lowest point, the
basepoint rotation, and the free-basepoint Umlaufsatz in the form consumed by the bigon
exclusion.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

section WindingBricks

open unitInterval

/-- The quarter-turn exponential: `exp (±iπ/2) = ±i`. -/
theorem exp_quarter {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (Complex.I * (ε : ℂ) * ((Real.pi : ℂ) / 2)) = (ε : ℂ) * Complex.I := by
  have hcast : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rcases hε with h | h <;> subst h
  · rw [show Complex.I * ((1 : ℝ) : ℂ) * ((Real.pi : ℂ) / 2)
        = ((Real.pi : ℂ) / 2) * Complex.I by push_cast; ring, hcast, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    norm_num
  · rw [show Complex.I * ((-1 : ℝ) : ℂ) * ((Real.pi : ℂ) / 2)
        = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring

/-- **Continuity of the secant map**: for a curve with continuous derivative on the
unit interval, the difference quotient extended by the derivative on the diagonal is
continuous on the square. -/
theorem secant_continuous {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      if p.1 = p.2 then g p.1 else (γ p.2 - γ p.1) / (p.2 - p.1))
      (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
  set S : ℝ × ℝ → ℂ := fun p =>
    if p.1 = p.2 then g p.1 else (γ p.2 - γ p.1) / (p.2 - p.1) with hSdef
  have hγc : ContinuousOn γ (Set.Icc 0 1) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := hab
  by_cases h : a = b
  · -- diagonal point
    subst h
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hga := hg a ha
    rw [Metric.continuousWithinAt_iff] at hga
    obtain ⟨δ, hδ, hδ'⟩ := hga (ε / 2) (by positivity)
    refine ⟨δ / 2, by positivity, ?_⟩
    rintro ⟨s, t⟩ hst hdist
    obtain ⟨hs, ht⟩ := hst
    have hds : dist s a < δ := by
      have h1 : dist s a ≤ dist (s, t) (a, a) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      linarith [hdist, h1]
    have hdt : dist t a < δ := by
      have h1 : dist t a ≤ dist (s, t) (a, a) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      linarith [hdist, h1]
    have hSaa : S (a, a) = g a := if_pos rfl
    rw [hSaa]
    by_cases hst' : s = t
    · have hval : S (s, t) = g s := if_pos hst'
      rw [hval]
      exact lt_trans (hδ' hs hds) (by linarith)
    · have hval : S (s, t) = (γ t - γ s) / ((t : ℂ) - (s : ℂ)) := if_neg hst'
      rw [hval]
      -- FTC over the segment
      have huIcc : Set.uIcc s t ⊆ Set.Icc (0:ℝ) 1 := Set.uIcc_subset_Icc hs ht
      have hint : IntervalIntegrable g volume s t :=
        (hg.mono huIcc).intervalIntegrable
      have hftc : ∫ v in s..t, g v = γ t - γ s :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun v hv => hd v (huIcc hv)) hint
      have hconst : ∫ v in s..t, g a = (t - s) • g a :=
        intervalIntegral.integral_const _
      have hsub : ∫ v in s..t, (g v - g a) = (γ t - γ s) - (t - s) • g a := by
        rw [intervalIntegral.integral_sub hint
          (intervalIntegrable_const), hftc, hconst]
      have hbound : ‖∫ v in s..t, (g v - g a)‖ ≤ ε / 2 * |t - s| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro v hv
        have hv' : v ∈ Set.uIcc s t := Set.uIoc_subset_uIcc hv
        have hvI : v ∈ Set.Icc (0:ℝ) 1 := huIcc hv'
        have hvd : dist v a < δ := by
          rw [Real.dist_eq]
          rw [Set.mem_uIcc] at hv'
          rw [Real.dist_eq] at hds hdt
          rcases hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            · rw [abs_lt] at hds hdt ⊢
              constructor <;> linarith [hds.1, hds.2, hdt.1, hdt.2]
        have h5 := (hδ' hvI hvd).le
        rwa [dist_eq_norm] at h5
      have htsne : t - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hst')
      have hcast : ((t : ℂ) - (s : ℂ)) = (((t - s : ℝ)) : ℂ) := by
        push_cast
        ring
      have htsneC : ((t : ℂ) - (s : ℂ)) ≠ 0 := by
        rw [hcast]
        exact_mod_cast htsne
      have hquot : (γ t - γ s) / ((t : ℂ) - (s : ℂ)) - g a
          = (∫ v in s..t, (g v - g a)) / ((t : ℂ) - (s : ℂ)) := by
        rw [hsub, Complex.real_smul, ← hcast]
        field_simp
      rw [dist_eq_norm, hquot, norm_div]
      have h2 : ‖(t : ℂ) - (s : ℂ)‖ = |t - s| := by
        rw [hcast, Complex.norm_real]
        exact Real.norm_eq_abs _
      rw [h2]
      have h3 : |t - s| > 0 := abs_pos.mpr htsne
      rw [div_lt_iff₀ h3]
      calc ‖∫ v in s..t, (g v - g a)‖ ≤ ε / 2 * |t - s| := hbound
        _ < ε * |t - s| := by
          have := mul_lt_mul_of_pos_right (by linarith : ε / 2 < ε) h3
          linarith [this]
  · -- off-diagonal point
    have hopen : {p : ℝ × ℝ | p.1 ≠ p.2} ∈ nhds ((a, b) : ℝ × ℝ) := by
      refine IsOpen.mem_nhds ?_ h
      exact isOpen_ne_fun continuous_fst continuous_snd
    have hnum : ContinuousOn (fun p : ℝ × ℝ => γ p.2 - γ p.1)
        (Set.Icc 0 1 ×ˢ Set.Icc 0 1) :=
      (hγc.comp continuous_snd.continuousOn fun p hp => hp.2).sub
        (hγc.comp continuous_fst.continuousOn fun p hp => hp.1)
    have hden : (((b : ℂ)) - ((a : ℂ))) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast Ne.symm h
    have hquot : ContinuousWithinAt
        (fun p : ℝ × ℝ => (γ p.2 - γ p.1) / (((p.2 : ℝ) : ℂ) - ((p.1 : ℝ) : ℂ)))
        (Set.Icc 0 1 ×ˢ Set.Icc 0 1) (a, b) := by
      refine ContinuousWithinAt.div (hnum _ ⟨ha, hb⟩) ?_ hden
      exact ((Complex.continuous_ofReal.comp continuous_snd).sub
        (Complex.continuous_ofReal.comp continuous_fst)).continuousWithinAt
  -- the if-function agrees with the quotient near the off-diagonal point
    refine hquot.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds hopen] with p hp
      rw [hSdef]
      exact if_neg hp
    · rw [hSdef]
      exact if_neg h

/-- **Chords of a simple closed curve do not degenerate**: distinct parameters of the
fundamental interval, other than the endpoint pair, have distinct values. -/
theorem simple_chord_ne {γ : ℝ → ℂ} (hinj : Set.InjOn γ (Set.Ico 0 1))
    (hcl : γ 0 = γ 1) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hst : s < t) (hne : ¬(s = 0 ∧ t = 1)) : γ s ≠ γ t := by
  intro heq
  rcases lt_or_eq_of_le ht.2 with ht1 | ht1
  · exact absurd (hinj ⟨hs.1, lt_trans hst ht1⟩ ⟨le_trans hs.1 hst.le, ht1⟩ heq) hst.ne
  · rw [ht1, ← hcl] at heq
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · exact hne ⟨hs0.symm, ht1⟩
    · have h1 : s = 0 :=
        hinj ⟨hs.1, lt_of_lt_of_le hst ht.2⟩ ⟨le_refl 0, zero_lt_one⟩ heq
      exact absurd h1 hs0.ne'

/-- **Corner continuity of the rescaled secant**: for a closed curve with continuous
matching derivative, the reversed chord divided by the wrapped gap `s + 1 - t` extends
continuously to the corner `(0, 1)` with value `g 0`. -/
theorem rescaled_secant_corner {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0) :
    ContinuousWithinAt (fun p : ℝ × ℝ =>
        if p = ((0:ℝ), (1:ℝ)) then g 0
        else (γ p.1 - γ p.2) / (((p.1 + 1 - p.2 : ℝ)) : ℂ))
      (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ((0:ℝ), (1:ℝ)) := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have h0 := hg 0 (by norm_num)
  rw [Metric.continuousWithinAt_iff] at h0
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := h0 (ε / 2) (by positivity)
  have h1 := hg 1 (by norm_num)
  rw [Metric.continuousWithinAt_iff] at h1
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := h1 (ε / 2) (by positivity)
  refine ⟨min δ₀ δ₁, by positivity, ?_⟩
  rintro ⟨s, t⟩ ⟨hs, ht⟩ hdist
  by_cases hc : ((s, t) : ℝ × ℝ) = ((0:ℝ), (1:ℝ))
  · rw [hc]
    simpa using hε
  · rw [if_neg hc, if_pos rfl]
    have hds : |s| < δ₀ := by
      have h2 : dist s 0 ≤ dist ((s, t) : ℝ × ℝ) ((0:ℝ), (1:ℝ)) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      have h3 : dist ((s, t) : ℝ × ℝ) ((0:ℝ), (1:ℝ)) < δ₀ :=
        lt_of_lt_of_le hdist (min_le_left _ _)
      rw [Real.dist_eq, sub_zero] at h2
      linarith
    have hdt : |t - 1| < δ₁ := by
      have h2 : dist t 1 ≤ dist ((s, t) : ℝ × ℝ) ((0:ℝ), (1:ℝ)) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      have h3 : dist ((s, t) : ℝ × ℝ) ((0:ℝ), (1:ℝ)) < δ₁ :=
        lt_of_lt_of_le hdist (min_le_right _ _)
      rw [Real.dist_eq] at h2
      linarith
    set lam : ℝ := s + 1 - t with hlamdef
    have hlam0 : 0 ≤ lam := by
      rw [hlamdef]
      linarith [hs.1, ht.2]
    have hlampos : 0 < lam := by
      rcases lt_or_eq_of_le hlam0 with h | h
      · exact h
      · exfalso
        have hs0 : s = 0 := by
          have := hs.1
          have := ht.2
          rw [hlamdef] at h
          linarith [hs.1, ht.2, le_antisymm (by linarith [ht.2] : s ≤ 0) hs.1]
        have ht1 : t = 1 := by
          rw [hlamdef] at h
          linarith [hs.1]
        exact hc (by rw [hs0, ht1])
    have hints : IntervalIntegrable g volume 0 s :=
      (hg.mono (Set.uIcc_subset_Icc (by norm_num) hs)).intervalIntegrable
    have hintt : IntervalIntegrable g volume t 1 :=
      (hg.mono (Set.uIcc_subset_Icc ht (by norm_num))).intervalIntegrable
    have hftc1 : ∫ v in (0:ℝ)..s, g v = γ s - γ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun v hv => hd v (Set.uIcc_subset_Icc (by norm_num) hs hv)) hints
    have hftc2 : ∫ v in t..(1:ℝ), g v = γ 1 - γ t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun v hv => hd v (Set.uIcc_subset_Icc ht (by norm_num) hv)) hintt
    have hchord : γ s - γ t = (∫ v in (0:ℝ)..s, g v) + ∫ v in t..(1:ℝ), g v := by
      rw [hftc1, hftc2, ← hcl]
      ring
    have hconst1 : ∫ _ in (0:ℝ)..s, g 0 = ((s : ℝ) : ℂ) * g 0 := by
      rw [intervalIntegral.integral_const, sub_zero]
      exact Complex.real_smul
    have hconst2 : ∫ _ in t..(1:ℝ), g 1 = ((1 - t : ℝ) : ℂ) * g 1 := by
      rw [intervalIntegral.integral_const]
      exact Complex.real_smul
    have hE : γ s - γ t - (lam : ℂ) * g 0
        = (∫ v in (0:ℝ)..s, (g v - g 0)) + ∫ v in t..(1:ℝ), (g v - g 1) := by
      rw [intervalIntegral.integral_sub hints intervalIntegrable_const,
        intervalIntegral.integral_sub hintt intervalIntegrable_const,
        hconst1, hconst2, hchord, hgcl, hlamdef]
      push_cast
      ring
    have hb1 : ‖∫ v in (0:ℝ)..s, (g v - g 0)‖ ≤ ε / 2 * |s - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro v hv
      have hv' : v ∈ Set.uIcc (0:ℝ) s := Set.uIoc_subset_uIcc hv
      rw [Set.uIcc_of_le hs.1] at hv'
      have hvI : v ∈ Set.Icc (0:ℝ) 1 := ⟨hv'.1, hv'.2.trans hs.2⟩
      have hvd : dist v 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hv'.1]
        have : s < δ₀ := by
          rw [abs_of_nonneg hs.1] at hds
          exact hds
        linarith [hv'.2]
      have h5 := (hδ₀' hvI hvd).le
      rwa [dist_eq_norm] at h5
    have hb2 : ‖∫ v in t..(1:ℝ), (g v - g 1)‖ ≤ ε / 2 * |1 - t| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro v hv
      have hv' : v ∈ Set.uIcc t 1 := Set.uIoc_subset_uIcc hv
      rw [Set.uIcc_of_le ht.2] at hv'
      have hvI : v ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.trans hv'.1, hv'.2⟩
      have hvd : dist v 1 < δ₁ := by
        rw [Real.dist_eq]
        have h6 : |t - 1| = 1 - t := by
          rw [abs_of_nonpos (by linarith [ht.2])]
          ring
        rw [h6] at hdt
        rw [abs_of_nonpos (by linarith [hv'.2])]
        have := hv'.1
        linarith
      have h5 := (hδ₁' hvI hvd).le
      rwa [dist_eq_norm] at h5
    have hlamne : ((lam : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hlampos.ne'
    have hplam : ((s + 1 - t : ℝ) : ℂ) = ((lam : ℝ) : ℂ) := by
      rw [hlamdef]
    have hquot : (γ s - γ t) / ((lam : ℝ) : ℂ) - g 0
        = (γ s - γ t - (lam : ℂ) * g 0) / ((lam : ℝ) : ℂ) := by
      field_simp
    rw [dist_eq_norm, hplam, hquot, hE, norm_div]
    have hnl : ‖((lam : ℝ) : ℂ)‖ = lam := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlampos]
    rw [hnl, div_lt_iff₀ hlampos]
    have habs1 : |s - 0| = s := by
      rw [sub_zero, abs_of_nonneg hs.1]
    have habs2 : |1 - t| = 1 - t := by
      rw [abs_of_nonneg (by linarith [ht.2])]
    calc ‖(∫ v in (0:ℝ)..s, (g v - g 0)) + ∫ v in t..(1:ℝ), (g v - g 1)‖
        ≤ ‖∫ v in (0:ℝ)..s, (g v - g 0)‖ + ‖∫ v in t..(1:ℝ), (g v - g 1)‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 * |s - 0| + ε / 2 * |1 - t| := add_le_add hb1 hb2
      _ = ε / 2 * lam := by
          rw [habs1, habs2, hlamdef]
          ring
      _ < ε * lam := by
          have := mul_lt_mul_of_pos_right (by linarith : ε / 2 < ε) hlampos
          linarith

/-- **The doubly rescaled secant map** of a closed curve: the chord divided by the
product of the parameter gap and the wrapped gap, extended by the derivative on the
diagonal and by its negative at the wrap-around corner. -/
noncomputable def secantMap (γ g : ℝ → ℂ) : ℝ × ℝ → ℂ := fun p =>
  if p = ((0:ℝ), (1:ℝ)) then -(g 0)
  else if p.1 = p.2 then g p.1
  else (γ p.2 - γ p.1) / ((((p.2 - p.1) * (p.1 + 1 - p.2) : ℝ)) : ℂ)

/-- The secant map restricts to the derivative on the diagonal. -/
theorem secantMap_diag (γ g : ℝ → ℂ) (u : ℝ) :
    secantMap γ g (u, u) = g u := by
  unfold secantMap
  rw [if_neg, if_pos rfl]
  intro h
  rw [Prod.mk.injEq] at h
  rw [h.1] at h
  exact zero_ne_one h.2

/-- The secant map takes the reversed derivative at the wrap-around corner. -/
theorem secantMap_corner (γ g : ℝ → ℂ) :
    secantMap γ g ((0:ℝ), (1:ℝ)) = -(g 0) := if_pos rfl

/-- The secant map is the rescaled chord off the diagonal and the corner. -/
theorem secantMap_off (γ g : ℝ → ℂ) {p : ℝ × ℝ}
    (hne : p ≠ ((0 : ℝ), (1 : ℝ))) (hd : p.1 ≠ p.2) :
    secantMap γ g p
      = (γ p.2 - γ p.1) / ((((p.2 - p.1) * (p.1 + 1 - p.2) : ℝ)) : ℂ) := by
  unfold secantMap
  rw [if_neg hne, if_neg hd]

/-- **The secant map of a simple closed curve does not vanish** on the parameter
triangle when the derivative does not vanish. -/
theorem secantMap_ne {γ g : ℝ → ℂ} (hinj : Set.InjOn γ (Set.Ico 0 1))
    (hcl : γ 0 = γ 1) (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0) :
    ∀ p ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2},
      secantMap γ g p ≠ 0 := by
  rintro ⟨s, t⟩ ⟨⟨hs, ht⟩, hle⟩
  by_cases hc : ((s, t) : ℝ × ℝ) = ((0:ℝ), (1:ℝ))
  · rw [hc, secantMap_corner]
    exact neg_ne_zero.mpr (hgne 0 (by norm_num))
  · by_cases hdg : s = t
    · subst hdg
      rw [secantMap_diag]
      exact hgne s hs
    · rw [secantMap_off _ _ hc hdg]
      have hst : s < t := lt_of_le_of_ne hle hdg
      have hchord : γ s ≠ γ t := by
        refine simple_chord_ne hinj hcl hs ht hst ?_
        rintro ⟨h1, h2⟩
        exact hc (by rw [h1, h2])
      refine div_ne_zero (sub_ne_zero.mpr (Ne.symm hchord)) ?_
      have hlam : 0 < s + 1 - t := by
        rcases lt_or_eq_of_le (by linarith [hs.1, ht.2] : (0:ℝ) ≤ s + 1 - t) with h | h
        · exact h
        · exfalso
          have hs0 : s = 0 := by linarith [hs.1, ht.2]
          have ht1 : t = 1 := by linarith [hs.1]
          exact hc (by rw [hs0, ht1])
      have h7 : (0:ℝ) < (t - s) * (s + 1 - t) := mul_pos (by linarith) hlam
      exact_mod_cast h7.ne'

/-- **Continuity of the secant map** on the parameter triangle: the diagonal chart is
the plain secant over the unit wrapped gap, the corner chart is the reversed rescaled
secant over the unit parameter gap, and the generic chart is a quotient of continuous
functions. -/
theorem secantMap_continuousOn {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0) :
    ContinuousOn (secantMap γ g)
      ((Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) := by
  set T : Set (ℝ × ℝ) :=
    (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2} with hTdef
  have hγc : ContinuousOn γ (Set.Icc 0 1) :=
    fun v hv => (hd v hv).continuousAt.continuousWithinAt
  have hdiagfar : ∀ u : ℝ,
      (1/2 : ℝ) ≤ dist ((u, u) : ℝ × ℝ) (((0:ℝ), (1:ℝ)) : ℝ × ℝ) := by
    intro u
    rw [Prod.dist_eq]
    rcases le_total u (1/2) with h | h
    · refine le_trans ?_ (le_max_right _ _)
      rw [Real.dist_eq]
      calc (1/2 : ℝ) ≤ 1 - u := by linarith
        _ ≤ |u - 1| := by
            rw [abs_sub_comm]
            exact le_abs_self _
    · refine le_trans ?_ (le_max_left _ _)
      rw [Real.dist_eq, sub_zero]
      exact h.trans (le_abs_self u)
  have hlampos : ∀ p : ℝ × ℝ, p ∈ T → p ≠ ((0:ℝ), (1:ℝ)) → 0 < p.1 + 1 - p.2 := by
    rintro ⟨s, t⟩ ⟨⟨hs, ht⟩, -⟩ hne
    rcases lt_or_eq_of_le (by linarith [hs.1, ht.2] : (0:ℝ) ≤ s + 1 - t) with h | h
    · exact h
    · exfalso
      have hs0 : s = 0 := by linarith [hs.1, ht.2]
      have ht1 : t = 1 := by linarith [hs.1]
      exact hne (by rw [hs0, ht1])
  rintro ⟨a, b⟩ hab
  have habT : ((a, b) : ℝ × ℝ) ∈ T := hab
  obtain ⟨⟨ha, hb⟩, hle⟩ := hab
  by_cases hcorner : ((a, b) : ℝ × ℝ) = ((0:ℝ), (1:ℝ))
  · -- corner chart
    rw [hcorner]
    set Wt : ℝ × ℝ → ℂ := fun p =>
      if p = ((0:ℝ), (1:ℝ)) then g 0
      else (γ p.1 - γ p.2) / (((p.1 + 1 - p.2 : ℝ)) : ℂ) with hWtdef
    have hW := rescaled_secant_corner hd hg hcl hgcl
    have hWT : ContinuousWithinAt Wt T (((0:ℝ), (1:ℝ))) :=
      hW.mono Set.inter_subset_left
    have hdenc : ContinuousWithinAt (fun p : ℝ × ℝ => (((p.2 - p.1 : ℝ)) : ℂ))
        T (((0:ℝ), (1:ℝ))) :=
      (Complex.continuous_ofReal.comp
        (continuous_snd.sub continuous_fst)).continuousWithinAt
    have hq : ContinuousWithinAt
        (fun p : ℝ × ℝ => -(Wt p / (((p.2 - p.1 : ℝ)) : ℂ))) T (((0:ℝ), (1:ℝ))) := by
      refine ContinuousWithinAt.neg (hWT.div hdenc ?_)
      norm_num
    refine hq.congr_of_eventuallyEq ?_ ?_
    · have hball : Metric.ball (((0:ℝ), (1:ℝ)) : ℝ × ℝ) (1/4) ∈
          nhdsWithin (((0:ℝ), (1:ℝ)) : ℝ × ℝ) T :=
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (by norm_num))
      filter_upwards [hball, self_mem_nhdsWithin] with p hpball hpT
      by_cases hpc : p = ((0:ℝ), (1:ℝ))
      · rw [hpc, secantMap_corner]
        have hWc : Wt (((0:ℝ), (1:ℝ))) = g 0 := if_pos rfl
        rw [hWc]
        norm_num
      · have hpne : p.1 ≠ p.2 := by
          intro he
          have h1 := hdiagfar p.1
          have hp2 : p = ((p.1, p.1) : ℝ × ℝ) := by
            rw [Prod.ext_iff]
            exact ⟨rfl, he.symm⟩
          rw [hp2] at hpball
          rw [Metric.mem_ball] at hpball
          linarith
        rw [secantMap_off _ _ hpc hpne]
        have hWp : Wt p = (γ p.1 - γ p.2) / (((p.1 + 1 - p.2 : ℝ)) : ℂ) :=
          if_neg hpc
        rw [hWp]
        have hgap : ((p.2 - p.1 : ℝ) : ℂ) ≠ 0 := by
          rw [Ne, Complex.ofReal_eq_zero, sub_eq_zero]
          exact fun he => hpne he.symm
        have hlam : ((p.1 + 1 - p.2 : ℝ) : ℂ) ≠ 0 := by
          rw [Ne, Complex.ofReal_eq_zero]
          exact (hlampos p hpT hpc).ne'
        have hsplit : ((((p.2 - p.1) * (p.1 + 1 - p.2) : ℝ)) : ℂ)
            = ((p.2 - p.1 : ℝ) : ℂ) * ((p.1 + 1 - p.2 : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hsplit]
        field_simp
        ring
    · rw [secantMap_corner]
      have hWc : Wt (((0:ℝ), (1:ℝ))) = g 0 := if_pos rfl
      rw [hWc]
      norm_num
  · by_cases hdiag : a = b
    · -- diagonal chart
      subst hdiag
      have hS := secant_continuous hd hg
      have hST : ContinuousWithinAt (fun p : ℝ × ℝ =>
          if p.1 = p.2 then g p.1 else (γ p.2 - γ p.1) / (p.2 - p.1))
          T ((a, a)) :=
        (hS _ ⟨ha, hb⟩).mono Set.inter_subset_left
      have hlamc : ContinuousWithinAt
          (fun p : ℝ × ℝ => (((p.1 + 1 - p.2 : ℝ)) : ℂ)) T ((a, a)) :=
        (Complex.continuous_ofReal.comp
          ((continuous_fst.add continuous_const).sub continuous_snd)).continuousWithinAt
      have hq : ContinuousWithinAt (fun p : ℝ × ℝ =>
          (if p.1 = p.2 then g p.1 else (γ p.2 - γ p.1) / (p.2 - p.1))
            / (((p.1 + 1 - p.2 : ℝ)) : ℂ)) T ((a, a)) := by
        refine hST.div hlamc ?_
        norm_num
      refine hq.congr_of_eventuallyEq ?_ ?_
      · have hball : Metric.ball ((a, a) : ℝ × ℝ) (1/4) ∈
            nhdsWithin ((a, a) : ℝ × ℝ) T :=
          mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (by norm_num))
        filter_upwards [hball, self_mem_nhdsWithin] with p hpball hpT
        have hpc : p ≠ ((0:ℝ), (1:ℝ)) := by
          intro he
          have h1 := hdiagfar a
          rw [he, Metric.mem_ball, dist_comm] at hpball
          linarith
        by_cases hpd : p.1 = p.2
        · have hp2 : p = ((p.1, p.1) : ℝ × ℝ) := by
            rw [Prod.ext_iff]
            exact ⟨rfl, hpd.symm⟩
          rw [hp2, secantMap_diag]
          have h3 : ((p.1 + 1 - p.1 : ℝ) : ℂ) = 1 := by
            norm_num
          rw [h3, div_one]
          simp
        · rw [secantMap_off _ _ hpc hpd]
          simp only [if_neg hpd]
          rw [div_div]
          congr 1
          push_cast
          ring
      · rw [secantMap_diag]
        have h3 : ((a + 1 - a : ℝ) : ℂ) = 1 := by norm_num
        rw [h3, div_one]
        simp
    · -- generic chart
      have hltab : a < b := lt_of_le_of_ne hle hdiag
      have hlamab : 0 < a + 1 - b := hlampos _ habT hcorner
      have hquot : ContinuousWithinAt (fun p : ℝ × ℝ =>
          (γ p.2 - γ p.1) / ((((p.2 - p.1) * (p.1 + 1 - p.2) : ℝ)) : ℂ))
          T ((a, b)) := by
        refine ContinuousWithinAt.div ?_ ?_ ?_
        · exact ((hγc.comp continuous_snd.continuousOn fun p hp => hp.1.2).sub
            (hγc.comp continuous_fst.continuousOn fun p hp => hp.1.1)) _ habT
        · exact (Complex.continuous_ofReal.comp
            (((continuous_snd.sub continuous_fst)).mul
              ((continuous_fst.add continuous_const).sub
                continuous_snd))).continuousWithinAt
        · rw [Ne, Complex.ofReal_eq_zero]
          exact (mul_pos (by linarith) hlamab).ne'
      refine hquot.congr_of_eventuallyEq ?_ ?_
      · have hopen : {p : ℝ × ℝ | p ≠ ((0:ℝ), (1:ℝ)) ∧ p.1 ≠ p.2} ∈
            nhds ((a, b) : ℝ × ℝ) := by
          refine IsOpen.mem_nhds (IsOpen.inter isOpen_ne ?_) ⟨hcorner, hdiag⟩
          exact isOpen_ne_fun continuous_fst continuous_snd
        filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with p hp
        exact secantMap_off _ _ hp.1 hp.2
      · exact secantMap_off _ _ hcorner hdiag

/-- **Band confinement**: a continuous function with nonnegative sine starting at the
even multiple `2πk` of `π` stays in the band `[2πk, 2πk + π]`. -/
theorem theta_band {θ : ℝ → ℝ} {a b : ℝ} {k : ℤ}
    (hθ : ContinuousOn θ (Set.Icc a b))
    (hsin : ∀ u ∈ Set.Icc a b, 0 ≤ Real.sin (θ u))
    (hstart : θ a = 2 * Real.pi * k) :
    ∀ u ∈ Set.Icc a b, θ u ∈ Set.Icc (2 * Real.pi * k) (2 * Real.pi * k + Real.pi) := by
  intro u hu
  set c : ℝ := 2 * Real.pi * k with hcdef
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsub : Set.Icc a u ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hu.2
  have hper : ∀ y : ℝ, Real.sin y = Real.sin (y - c) := by
    intro y
    rw [hcdef, show y - 2 * Real.pi * k = y - k * (2 * Real.pi) by ring,
      Real.sin_sub_int_mul_two_pi]
  constructor
  · by_contra hlt
    have hlt' : θ u < c := not_le.mp hlt
    set y : ℝ := max (c - Real.pi / 2) (θ u) with hydef
    have hy1 : θ u ≤ y := le_max_right _ _
    have hy2 : y ≤ θ a := by
      rw [hstart]
      exact max_le (by linarith) hlt'.le
    obtain ⟨v, hv, hvy⟩ := intermediate_value_Icc' hu.1 (hθ.mono hsub) ⟨hy1, hy2⟩
    have hygap1 : c - Real.pi < y :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hygap2 : y < c := max_lt (by linarith) hlt'
    have hsiny : Real.sin y < 0 := by
      rw [hper y]
      have h1 : 0 < c - y := by linarith
      have h2 : c - y < Real.pi := by linarith
      have h3 : Real.sin (y - c) = -Real.sin (c - y) := by
        rw [show y - c = -(c - y) by ring, Real.sin_neg]
      rw [h3]
      linarith [Real.sin_pos_of_pos_of_lt_pi h1 h2]
    have := hsin v (hsub hv)
    rw [hvy] at this
    linarith
  · by_contra hgt
    have hgt' : c + Real.pi < θ u := not_le.mp hgt
    set y : ℝ := min (c + 3 * Real.pi / 2) (θ u) with hydef
    have hy1 : θ a ≤ y := by
      rw [hstart]
      exact le_min (by linarith) (by linarith)
    have hy2 : y ≤ θ u := min_le_right _ _
    obtain ⟨v, hv, hvy⟩ := intermediate_value_Icc hu.1 (hθ.mono hsub) ⟨hy1, hy2⟩
    have hygap1 : c + Real.pi < y := lt_min (by linarith) hgt'
    have hygap2 : y < c + 2 * Real.pi :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsiny : Real.sin y < 0 := by
      rw [hper y]
      have h1 : 0 < y - c - Real.pi := by linarith
      have h2 : y - c - Real.pi < Real.pi := by linarith
      have h3 := Real.sin_sub_pi (y - c)
      have h4 := Real.sin_pos_of_pos_of_lt_pi h1 h2
      rw [show y - c - Real.pi = y - c - Real.pi from rfl] at h4
      have h5 : Real.sin (y - c - Real.pi) = -Real.sin (y - c) := by
        rw [show y - c - Real.pi = (y - c) - Real.pi by ring, h3]
      rw [h5] at h4
      linarith
    have := hsin v (hsub hv)
    rw [hvy] at this
    linarith

/-- **Band confinement, lower half**: a continuous function with nonpositive sine
starting at the odd multiple `2πk + π` stays in the band `[2πk + π, 2πk + 2π]`. -/
theorem theta_band_neg {θ : ℝ → ℝ} {a b : ℝ} {k : ℤ}
    (hθ : ContinuousOn θ (Set.Icc a b))
    (hsin : ∀ u ∈ Set.Icc a b, Real.sin (θ u) ≤ 0)
    (hstart : θ a = 2 * Real.pi * k + Real.pi) :
    ∀ u ∈ Set.Icc a b,
      θ u ∈ Set.Icc (2 * Real.pi * k + Real.pi) (2 * Real.pi * k + 2 * Real.pi) := by
  have hshift := theta_band (θ := fun u => θ u - Real.pi) (k := k)
    (hθ.sub continuousOn_const) ?_ ?_
  · intro u hu
    obtain ⟨h1, h2⟩ := hshift u hu
    constructor <;> [linarith; linarith]
  · intro u hu
    rw [Real.sin_sub_pi]
    linarith [hsin u hu]
  · rw [hstart]
    ring

/-- **The one-crossing winding count**: a closed nonvanishing curve starting on the
positive real axis, confined to the closed upper half plane until it meets the
negative real axis at the half parameter, and returning through the closed lower half
plane, winds exactly once about the origin. -/
theorem upper_lower_winding {γ : C(I, ℂ)} (hne : ∀ t : I, γ t ≠ 0)
    (hcl : γ 0 = γ 1)
    (h0re : 0 < (γ 0).re) (h0im : (γ 0).im = 0)
    (hhre : (γ ⟨1/2, by norm_num⟩).re < 0) (hhim : (γ ⟨1/2, by norm_num⟩).im = 0)
    (hup : ∀ t : I, (t : ℝ) ≤ 1/2 → 0 ≤ (γ t).im)
    (hdown : ∀ t : I, 1/2 ≤ (t : ℝ) → (γ t).im ≤ 0) :
    windingNumber γ 0 = 1 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδne : ∀ t : I, shiftedCurve γ 0 t ≠ 0 := by
    intro t
    simpa [shiftedCurve] using hne t
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ 0) hδne
  have hlift : ∀ t : I, Complex.exp (L t) = γ t := by
    intro t
    have h1 := hL t
    simpa [shiftedCurve] using h1
  have hspec := windingNumber_spec hcl (fun t => hne t) hL
  have him : ∀ t : I, (γ t).im = Real.exp ((L t).re) * Real.sin ((L t).im) := by
    intro t
    rw [← hlift t]
    exact Complex.exp_im _
  have hre : ∀ t : I, (γ t).re = Real.exp ((L t).re) * Real.cos ((L t).im) := by
    intro t
    rw [← hlift t]
    exact Complex.exp_re _
  have hsin0 : ∀ t : I, (γ t).im = 0 → Real.sin ((L t).im) = 0 := by
    intro t h
    have h1 := him t
    rw [h] at h1
    have h2 := Real.exp_pos ((L t).re)
    nlinarith [h1]
  have hcospos : ∀ t : I, 0 < (γ t).re → 0 < Real.cos ((L t).im) := by
    intro t h
    have h1 := hre t
    have h2 := Real.exp_pos ((L t).re)
    nlinarith
  have hcosneg : ∀ t : I, (γ t).re < 0 → Real.cos ((L t).im) < 0 := by
    intro t h
    have h1 := hre t
    have h2 := Real.exp_pos ((L t).re)
    nlinarith
  have hsinsign : ∀ t : I, 0 ≤ (γ t).im → 0 ≤ Real.sin ((L t).im) := by
    intro t h
    have h1 := him t
    have h2 := Real.exp_pos ((L t).re)
    nlinarith
  have hsinsign' : ∀ t : I, (γ t).im ≤ 0 → Real.sin ((L t).im) ≤ 0 := by
    intro t h
    have h1 := him t
    have h2 := Real.exp_pos ((L t).re)
    nlinarith
  -- the angle function over the real parameter
  set θ : ℝ → ℝ := fun u => (L (Set.projIcc 0 1 zero_le_one u)).im with hθdef
  have hθc : ContinuousOn θ (Set.Icc 0 1) :=
    (Complex.continuous_im.comp (L.continuous.comp continuous_projIcc)).continuousOn
  have hθval : ∀ t : I, θ ((t : ℝ)) = (L t).im := by
    intro t
    change (L (Set.projIcc 0 1 zero_le_one ((t : ℝ)))).im = (L t).im
    rw [Set.projIcc_val zero_le_one t]
  -- the start pins to an even multiple
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, θ 0 = 2 * Real.pi * k₀ := by
    have h1 : θ 0 = (L 0).im := by
      have := hθval 0
      simpa using this
    have h2 : Real.sin ((L 0).im) = 0 := hsin0 0 h0im
    have h3 : 0 < Real.cos ((L 0).im) := hcospos 0 h0re
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h2
    rcases Int.even_or_odd n with he | ho
    · obtain ⟨m, hm⟩ := he
      refine ⟨m, ?_⟩
      rw [h1, ← hn, hm]
      push_cast
      ring
    · exfalso
      rw [← hn, Real.cos_int_mul_pi, Odd.neg_one_zpow ho] at h3
      linarith
  -- the half-time pins to the next odd multiple
  have hhalfmem : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  set th : I := ⟨1/2, by norm_num⟩ with hthdef
  have hθhalf : θ (1/2) = (L th).im := hθval th
  have hband1 : ∀ u ∈ Set.Icc (0:ℝ) (1/2),
      θ u ∈ Set.Icc (2 * Real.pi * k₀) (2 * Real.pi * k₀ + Real.pi) := by
    refine theta_band (hθc.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) ?_ hk₀
    intro u hu
    have humem : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1, hu.2.trans (by norm_num)⟩
    set t : I := ⟨u, humem⟩ with htdef
    have h1 : θ u = (L t).im := hθval t
    rw [h1]
    exact hsinsign t (hup t hu.2)
  have hθh : θ (1/2) = 2 * Real.pi * k₀ + Real.pi := by
    have h2 : Real.sin ((L th).im) = 0 := hsin0 th hhim
    have h3 : Real.cos ((L th).im) < 0 := hcosneg th hhre
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h2
    have h4 := hband1 (1/2) (by norm_num)
    rw [hθhalf, ← hn] at h4 ⊢
    obtain ⟨h5, h6⟩ := h4
    have h7 : (2 * k₀ : ℝ) ≤ n := by
      have := h5
      nlinarith
    have h8 : (n : ℝ) ≤ 2 * k₀ + 1 := by nlinarith
    have h9 : 2 * k₀ ≤ n := by exact_mod_cast h7
    have h10 : n ≤ 2 * k₀ + 1 := by exact_mod_cast h8
    have h11 : n = 2 * k₀ ∨ n = 2 * k₀ + 1 := by omega
    rcases h11 with h | h
    · exfalso
      rw [← hn, Real.cos_int_mul_pi,
        Even.neg_one_zpow ⟨k₀, by omega⟩] at h3
      linarith
    · rw [h]
      push_cast
      ring
  -- the end pins to the following even multiple
  have hband2 : ∀ u ∈ Set.Icc (1/2 : ℝ) 1,
      θ u ∈ Set.Icc (2 * Real.pi * k₀ + Real.pi)
        (2 * Real.pi * k₀ + 2 * Real.pi) := by
    refine theta_band_neg (hθc.mono (Set.Icc_subset_Icc (by norm_num) le_rfl))
      ?_ hθh
    intro u hu
    have humem : u ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans (by norm_num) hu.1, hu.2⟩
    set t : I := ⟨u, humem⟩ with htdef
    have h1 : θ u = (L t).im := hθval t
    rw [h1]
    exact hsinsign' t (hdown t hu.1)
  have hθ1 : θ 1 = 2 * Real.pi * k₀ + 2 * Real.pi := by
    have h1 : θ 1 = (L 1).im := by
      have := hθval 1
      simpa using this
    have him1 : (γ 1).im = 0 := by rw [← hcl]; exact h0im
    have hre1 : 0 < (γ 1).re := by rw [← hcl]; exact h0re
    have h2 : Real.sin ((L 1).im) = 0 := hsin0 1 him1
    have h3 : 0 < Real.cos ((L 1).im) := hcospos 1 hre1
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h2
    have h4 := hband2 1 (by norm_num)
    rw [h1, ← hn] at h4 ⊢
    obtain ⟨h5, h6⟩ := h4
    have h7 : (2 * k₀ + 1 : ℝ) ≤ n := by nlinarith
    have h8 : (n : ℝ) ≤ 2 * k₀ + 2 := by nlinarith
    have h9 : 2 * k₀ + 1 ≤ n := by exact_mod_cast h7
    have h10 : n ≤ 2 * k₀ + 2 := by exact_mod_cast h8
    have h11 : n = 2 * k₀ + 1 ∨ n = 2 * k₀ + 2 := by omega
    rcases h11 with h | h
    · exfalso
      rw [← hn, Real.cos_int_mul_pi,
        Odd.neg_one_zpow ⟨k₀, by omega⟩] at h3
      linarith
    · rw [h]
      push_cast
      ring
  -- conclude from the lift increment
  have hinc := congrArg Complex.im hspec
  have h1 : (L 1 - L 0).im = 2 * Real.pi := by
    rw [Complex.sub_im]
    have ha : (L 1).im = θ 1 := by
      have := hθval 1
      simpa using this.symm
    have hb : (L 0).im = θ 0 := by
      have := hθval 0
      simpa using this.symm
    rw [ha, hb, hθ1, hk₀]
    ring
  rw [h1] at hinc
  have h2 : ((2 : ℂ) * Real.pi * Complex.I * (windingNumber γ 0 : ℂ)).im
      = 2 * Real.pi * (windingNumber γ 0 : ℝ) := by
    simp [Complex.mul_im, Complex.mul_re]
  rw [h2] at hinc
  have h4 : (2 * Real.pi) * 1 = (2 * Real.pi) * (windingNumber γ 0 : ℝ) := by
    linarith
  have h5 := mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h4
  exact_mod_cast h5.symm

/-- **Horizontality at a minimum**: the derivative of a closed curve at a basepoint of
minimal imaginary part, matching at the wrap-around, has vanishing imaginary part. -/
theorem min_im_deriv_zero {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ 0).im ≤ (γ t).im) :
    (g 0).im = 0 := by
  have him_deriv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun u => (γ u).im) ((g t).im) t := by
    intro t ht
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd t ht)
    simpa using! h2
  have hge : 0 ≤ (g 0).im := by
    have h1 : HasDerivWithinAt (fun u => (γ u).im) ((g 0).im) (Set.Ioc 0 1) 0 :=
      (him_deriv 0 (by norm_num)).hasDerivWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope] at h1
    have h2 : Set.Ioc (0:ℝ) 1 \ {0} = Set.Ioc 0 1 := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by linarith [h.1]⟩
    rw [h2] at h1
    have := left_nhdsWithin_Ioc_neBot (by norm_num : (0:ℝ) < 1)
    refine ge_of_tendsto h1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    have h3 : (γ 0).im ≤ (γ t).im := hmin t ⟨ht.1.le, ht.2⟩
    have h4 : 0 < t - 0 := by linarith [ht.1]
    exact div_nonneg (by linarith) (by linarith)
  have hle : (g 1).im ≤ 0 := by
    have h1 : HasDerivWithinAt (fun u => (γ u).im) ((g 1).im) (Set.Ico 0 1) 1 :=
      (him_deriv 1 (by norm_num)).hasDerivWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope] at h1
    have h2 : Set.Ico (0:ℝ) 1 \ {1} = Set.Ico 0 1 := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by linarith [h.2]⟩
    rw [h2] at h1
    have := right_nhdsWithin_Ico_neBot (by norm_num : (0:ℝ) < 1)
    refine le_of_tendsto h1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    have h3 : (γ 0).im ≤ (γ t).im := hmin t ⟨ht.1, ht.2.le⟩
    have h4 : t - 1 < 0 := by linarith [ht.2]
    have h5 : (γ 1).im = (γ 0).im := by rw [← hcl]
    refine div_nonpos_of_nonneg_of_nonpos ?_ (by linarith)
    rw [h5]
    linarith
  rw [hgcl] at hle
  linarith

/-- The legs path of the parameter triangle: up the left edge, then along the top
edge. -/
noncomputable def legsPath : ℝ → ℝ × ℝ := fun u =>
  if u ≤ 1/2 then ((0:ℝ), 2*u) else (2*u - 1, (1:ℝ))

/-- The two-legs boundary path of the triangle is continuous. -/
theorem legsPath_continuous : Continuous legsPath := by
  unfold legsPath
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
  · exact continuous_const.prodMk (continuous_const.mul continuous_id)
  · exact ((continuous_const.mul continuous_id).sub continuous_const).prodMk
      continuous_const
  · intro t ht
    have ht' : t = 1/2 := ht
    subst ht'
    norm_num [Prod.ext_iff]

/-- The two-legs path stays in the ordered unit square. -/
theorem legsPath_mem {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (legsPath u).1 ∈ Set.Icc (0:ℝ) 1 ∧ (legsPath u).2 ∈ Set.Icc (0:ℝ) 1 ∧
      (legsPath u).1 ≤ (legsPath u).2 := by
  unfold legsPath
  by_cases h : u ≤ 1/2
  · rw [if_pos h]
    refine ⟨⟨le_refl 0, by norm_num⟩, ⟨by linarith [hu.1], by linarith⟩, ?_⟩
    change (0:ℝ) ≤ 2 * u
    linarith [hu.1]
  · rw [if_neg h]
    have h' : 1/2 < u := not_le.mp h
    exact ⟨⟨by linarith, by linarith [hu.2]⟩, ⟨by norm_num, le_refl 1⟩,
      by change 2*u - 1 ≤ (1:ℝ); linarith [hu.2]⟩

/-- The two-legs path starts at the diagonal corner `(0, 0)`. -/
theorem legsPath_zero : legsPath 0 = ((0:ℝ), (0:ℝ)) := by
  unfold legsPath
  norm_num

/-- The two-legs path ends at the diagonal corner `(1, 1)`. -/
theorem legsPath_one : legsPath 1 = ((1:ℝ), (1:ℝ)) := by
  unfold legsPath
  norm_num [Prod.ext_iff]

/-- At half time the two-legs path sits at the off-diagonal corner `(0, 1)`. -/
theorem legsPath_half : legsPath (1/2) = ((0:ℝ), (1:ℝ)) := by
  unfold legsPath
  norm_num [Prod.ext_iff]

/-- Division by a positive real scales the imaginary part. -/
theorem div_real_im (w : ℂ) (r : ℝ) :
    (w / ((r : ℝ) : ℂ)).im = r⁻¹ * w.im := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.im_ofReal_mul]

/-- **The tangent loop winds once**: for a simple closed continuously differentiable
curve whose basepoint has minimal imaginary part and whose basepoint tangent points in
the positive real direction, the tangent loop winds exactly once about the origin. -/
theorem tangent_winding_pos {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (hinj : Set.InjOn γ (Set.Ico 0 1))
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ 0).im ≤ (γ t).im)
    (hre : 0 < (g 0).re) :
    windingNumber ⟨fun t : I => g ((t : ℝ)),
      hg.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = 1 := by
  classical
  have him0 : (g 0).im = 0 := min_im_deriv_zero hd hcl hgcl hmin
  have hSne := secantMap_ne hinj hcl hgne
  have hSc := secantMap_continuousOn hd hg hcl hgcl
  have hdiagT : ∀ u : I, (((u : ℝ)), ((u : ℝ))) ∈
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2} :=
    fun u => ⟨⟨u.2, u.2⟩, le_refl ((u : ℝ))⟩
  have hlegT : ∀ u : I, legsPath ((u : ℝ)) ∈
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    intro u
    obtain ⟨h1, h2, h3⟩ := legsPath_mem u.2
    exact ⟨⟨h1, h2⟩, h3⟩
  set Dcur : C(I, ℂ) := ⟨fun u => secantMap γ g (((u : ℝ)), ((u : ℝ))),
    hSc.comp_continuous
      (continuous_subtype_val.prodMk continuous_subtype_val) hdiagT⟩ with hDdef
  set LL : C(I, ℂ) := ⟨fun u => secantMap γ g (legsPath ((u : ℝ))),
    hSc.comp_continuous
      (legsPath_continuous.comp continuous_subtype_val) hlegT⟩ with hLLdef
  set Hm : I × I → ℝ × ℝ := fun p =>
    ((1 - ((p.1 : ℝ))) * ((p.2 : ℝ)) + ((p.1 : ℝ)) * (legsPath ((p.2 : ℝ))).1,
     (1 - ((p.1 : ℝ))) * ((p.2 : ℝ)) + ((p.1 : ℝ)) * (legsPath ((p.2 : ℝ))).2)
    with hHmdef
  have hcoe1 : Continuous fun p : I × I => ((p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hcoe2 : Continuous fun p : I × I => ((p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hlegc : Continuous fun p : I × I => legsPath ((p.2 : ℝ)) :=
    legsPath_continuous.comp hcoe2
  have hHmc : Continuous Hm := by
    refine Continuous.prodMk ?_ ?_
    · exact ((continuous_const.sub hcoe1).mul hcoe2).add
        (hcoe1.mul (continuous_fst.comp hlegc))
    · exact ((continuous_const.sub hcoe1).mul hcoe2).add
        (hcoe1.mul (continuous_snd.comp hlegc))
  have hHmT : ∀ p : I × I, Hm p ∈
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    rintro ⟨τ, u⟩
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hab⟩ := legsPath_mem u.2
    have hτ0 : 0 ≤ ((τ : ℝ)) := τ.2.1
    have hτ1 : ((τ : ℝ)) ≤ 1 := τ.2.2
    have hu0 : 0 ≤ ((u : ℝ)) := u.2.1
    have hu1 : ((u : ℝ)) ≤ 1 := u.2.2
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ((τ:ℝ))) hu0
      have := mul_nonneg hτ0 ha1
      change (0:ℝ) ≤ _
      linarith
    · have h1 := mul_le_mul_of_nonneg_left hu1 (by linarith : (0:ℝ) ≤ 1 - ((τ:ℝ)))
      have h2 := mul_le_mul_of_nonneg_left ha2 hτ0
      change _ ≤ (1:ℝ)
      linarith
    · have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ((τ:ℝ))) hu0
      have := mul_nonneg hτ0 hb1
      change (0:ℝ) ≤ _
      linarith
    · have h1 := mul_le_mul_of_nonneg_left hu1 (by linarith : (0:ℝ) ≤ 1 - ((τ:ℝ)))
      have h2 := mul_le_mul_of_nonneg_left hb2 hτ0
      change _ ≤ (1:ℝ)
      linarith
    · have := mul_le_mul_of_nonneg_left hab hτ0
      change (1 - ((τ:ℝ))) * ((u:ℝ)) + ((τ:ℝ)) * (legsPath ((u:ℝ))).1
        ≤ (1 - ((τ:ℝ))) * ((u:ℝ)) + ((τ:ℝ)) * (legsPath ((u:ℝ))).2
      linarith
  have hDval : ∀ u : I, Dcur u = g ((u : ℝ)) := fun u => secantMap_diag γ g _
  have hcoe0 : (((0 : I) : ℝ)) = 0 := rfl
  have hcoeone : (((1 : I) : ℝ)) = 1 := rfl
  have hDcl : Dcur 0 = Dcur 1 := by
    rw [hDval, hDval, hcoe0, hcoeone, hgcl]
  have hmapzero : ∀ u : I, secantMap γ g (Hm (0, u)) = Dcur u := by
    intro u
    have h1 : Hm (0, u) = (((u : ℝ)), ((u : ℝ))) := by
      rw [hHmdef]
      change ((1 - ((0:I):ℝ)) * _ + ((0:I):ℝ) * _,
        (1 - ((0:I):ℝ)) * _ + ((0:I):ℝ) * _) = _
      rw [hcoe0, Prod.ext_iff]
      constructor <;> ring
    rw [h1]
    rfl
  have hmapone : ∀ u : I, secantMap γ g (Hm (1, u)) = LL u := by
    intro u
    have h1 : Hm (1, u) = legsPath ((u : ℝ)) := by
      rw [hHmdef]
      change ((1 - ((1:I):ℝ)) * _ + ((1:I):ℝ) * _,
        (1 - ((1:I):ℝ)) * _ + ((1:I):ℝ) * _) = _
      rw [hcoeone, Prod.ext_iff]
      constructor <;> ring
    rw [h1]
    rfl
  have hmaprel : ∀ (τ : I), ∀ u ∈ ({0, 1} : Set I),
      secantMap γ g (Hm (τ, u)) = Dcur u := by
    intro τ u hu
    rcases hu with h | h
    · subst h
      have h1 : Hm (τ, 0) = ((0 : ℝ), (0 : ℝ)) := by
        rw [hHmdef]
        change ((1 - ((τ:I):ℝ)) * ((0:I):ℝ) + _ * (legsPath ((0:I):ℝ)).1,
          (1 - ((τ:I):ℝ)) * ((0:I):ℝ) + _ * (legsPath ((0:I):ℝ)).2) = _
        rw [hcoe0, legsPath_zero, Prod.ext_iff]
        constructor <;> ring
      rw [h1, hDval]
      change secantMap γ g ((0:ℝ), (0:ℝ)) = g ((0:I):ℝ)
      rw [hcoe0]
      exact secantMap_diag γ g 0
    · rw [Set.mem_singleton_iff] at h
      subst h
      have h1 : Hm (τ, 1) = ((1 : ℝ), (1 : ℝ)) := by
        rw [hHmdef]
        change ((1 - ((τ:I):ℝ)) * ((1:I):ℝ) + _ * (legsPath ((1:I):ℝ)).1,
          (1 - ((τ:I):ℝ)) * ((1:I):ℝ) + _ * (legsPath ((1:I):ℝ)).2) = _
        rw [hcoeone, legsPath_one, Prod.ext_iff]
        constructor <;> ring
      rw [h1, hDval]
      change secantMap γ g ((1:ℝ), (1:ℝ)) = g ((1:I):ℝ)
      rw [hcoeone]
      exact secantMap_diag γ g 1
  have hHne : ∀ p : I × I, secantMap γ g (Hm p) ≠ 0 :=
    fun p => hSne _ (hHmT p)
  have hwind1 : windingNumber Dcur 0 = windingNumber LL 0 :=
    windingNumber_eq_of_homotopicRel hDcl
      (⟨⟨⟨fun p => secantMap γ g (Hm p),
          hSc.comp_continuous hHmc hHmT⟩, hmapzero, hmapone⟩, hmaprel⟩ :
        ContinuousMap.HomotopyRel Dcur LL {0, 1})
      (fun t s => hHne (t, s))
  have hLL0 : LL 0 = g 0 := by
    change secantMap γ g (legsPath (((0:I) : ℝ))) = g 0
    rw [hcoe0, legsPath_zero]
    exact secantMap_diag γ g 0
  have hLL1 : LL 1 = g 1 := by
    change secantMap γ g (legsPath (((1:I) : ℝ))) = g 1
    rw [hcoeone, legsPath_one]
    exact secantMap_diag γ g 1
  have hLLhalf : LL ⟨1/2, by norm_num⟩ = -(g 0) := by
    change secantMap γ g (legsPath (((⟨1/2, by norm_num⟩ : I)) : ℝ)) = -(g 0)
    rw [show (((⟨1/2, by norm_num⟩ : I)) : ℝ) = 1/2 from rfl, legsPath_half]
    exact secantMap_corner γ g
  have hup : ∀ t : I, ((t : ℝ)) ≤ 1/2 → 0 ≤ (LL t).im := by
    intro t htle
    have hu0 : 0 ≤ ((t:ℝ)) := t.2.1
    change 0 ≤ (secantMap γ g (legsPath ((t:ℝ)))).im
    have hLg : legsPath ((t:ℝ)) = ((0:ℝ), 2*((t:ℝ))) := if_pos htle
    rcases eq_or_lt_of_le hu0 with h0 | h0
    · rw [← h0, legsPath_zero, secantMap_diag, him0]
    · rcases eq_or_lt_of_le htle with hh | hh
      · rw [hh, legsPath_half, secantMap_corner, Complex.neg_im, him0]
        norm_num
      · have hne1 : ((0:ℝ), 2*((t:ℝ))) ≠ ((0:ℝ), (1:ℝ)) := by
          intro he
          rw [Prod.mk.injEq] at he
          have := he.2
          linarith
        have hne2 : ((0:ℝ), 2*((t:ℝ))).1 ≠ ((0:ℝ), 2*((t:ℝ))).2 := by
          change (0:ℝ) ≠ 2*((t:ℝ))
          intro he
          linarith
        rw [hLg, secantMap_off γ g hne1 hne2]
        have hmem2t : 2*((t:ℝ)) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
        have hch : 0 ≤ (γ (2*((t:ℝ))) - γ 0).im := by
          rw [Complex.sub_im]
          linarith [hmin _ hmem2t]
        have hrpos : (0:ℝ) < (2*((t:ℝ)) - 0) * (0 + 1 - 2*((t:ℝ))) := by nlinarith
        change 0 ≤ ((γ (2*((t:ℝ))) - γ 0)
          / ((((2*((t:ℝ)) - 0) * (0 + 1 - 2*((t:ℝ))) : ℝ)) : ℂ)).im
        rw [div_real_im]
        exact mul_nonneg (inv_nonneg.mpr hrpos.le) hch
  have hdown : ∀ t : I, 1/2 ≤ ((t : ℝ)) → (LL t).im ≤ 0 := by
    intro t htge
    have hu1 : ((t:ℝ)) ≤ 1 := t.2.2
    change (secantMap γ g (legsPath ((t:ℝ)))).im ≤ 0
    rcases eq_or_lt_of_le htge with hh | hh
    · rw [← hh, legsPath_half, secantMap_corner, Complex.neg_im, him0]
      norm_num
    · have hLg : legsPath ((t:ℝ)) = (2*((t:ℝ)) - 1, (1:ℝ)) := if_neg (not_le.mpr hh)
      have hs0 : (0:ℝ) < 2*((t:ℝ)) - 1 := by linarith
      have hs1 : 2*((t:ℝ)) - 1 ≤ 1 := by linarith
      rcases eq_or_lt_of_le hs1 with hseq | hslt
      · rw [hLg, hseq, secantMap_diag, hgcl, him0]
      · have hne1 : ((2*((t:ℝ)) - 1 : ℝ), (1:ℝ)) ≠ ((0:ℝ), (1:ℝ)) := by
          intro he
          rw [Prod.mk.injEq] at he
          have := he.1
          linarith
        have hne2 : ((2*((t:ℝ)) - 1 : ℝ), (1:ℝ)).1 ≠ ((2*((t:ℝ)) - 1 : ℝ), (1:ℝ)).2 := by
          change (2*((t:ℝ)) - 1 : ℝ) ≠ 1
          intro he
          linarith
        rw [hLg, secantMap_off γ g hne1 hne2]
        have hch : (γ 1 - γ (2*((t:ℝ)) - 1)).im ≤ 0 := by
          rw [Complex.sub_im]
          have h5 : (γ 1).im = (γ 0).im := by rw [← hcl]
          rw [h5]
          linarith [hmin (2*((t:ℝ)) - 1) ⟨hs0.le, hs1⟩]
        have hrpos : (0:ℝ) < (1 - (2*((t:ℝ)) - 1)) * ((2*((t:ℝ)) - 1) + 1 - 1) := by
          nlinarith
        change ((γ 1 - γ (2*((t:ℝ)) - 1))
          / ((((1 - (2*((t:ℝ)) - 1)) * ((2*((t:ℝ)) - 1) + 1 - 1) : ℝ)) : ℂ)).im ≤ 0
        rw [div_real_im]
        refine mul_nonpos_iff.mpr (Or.inl ⟨inv_nonneg.mpr hrpos.le, hch⟩)
  have hLLne : ∀ t : I, LL t ≠ 0 := fun t => hSne _ (hlegT t)
  have hLLcl : LL 0 = LL 1 := by rw [hLL0, hLL1, hgcl]
  have hw2 : windingNumber LL 0 = 1 := by
    refine upper_lower_winding hLLne hLLcl ?_ ?_ ?_ ?_ hup hdown
    · rw [hLL0]
      exact hre
    · rw [hLL0]
      exact him0
    · rw [hLLhalf, Complex.neg_re]
      linarith
    · rw [hLLhalf, Complex.neg_im, him0]
      norm_num
  have hGD : (⟨fun t : I => g ((t : ℝ)),
      hg.comp_continuous continuous_subtype_val fun t => t.2⟩ : C(I, ℂ)) = Dcur :=
    ContinuousMap.ext fun u => (hDval u).symm
  rw [hGD, hwind1, hw2]

/-- **Reversal negates winding**: precomposition with the interval reflection negates
the winding number of a closed curve about any avoided point. -/
theorem winding_reverse {γ : C(I, ℂ)} {q : ℂ} (hcl : γ 0 = γ 1)
    (hne : ∀ t : I, γ t ≠ q) :
    windingNumber (γ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) q
      = -windingNumber γ q := by
  have hδne : ∀ t : I, shiftedCurve γ q t ≠ 0 := by
    intro t
    simpa [shiftedCurve, sub_eq_zero] using hne t
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ q) hδne
  have hspec := windingNumber_spec hcl hne hL
  set R : C(I, ℂ) := γ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩
    with hRdef
  have hRval : ∀ t : I, R t = γ (unitInterval.symm t) := fun t => rfl
  have hRcl : R 0 = R 1 := by
    rw [hRval, hRval, unitInterval.symm_zero, unitInterval.symm_one, hcl]
  have hRne : ∀ t : I, R t ≠ q := fun t => hne _
  have hLR : IsLogLiftOf (L.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩)
      (shiftedCurve R q) := by
    intro t
    have h1 := hL (unitInterval.symm t)
    simpa [shiftedCurve] using! h1
  have hspecR := windingNumber_spec hRcl hRne hLR
  have h2 : (L.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) 1
      - (L.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) 0
      = -(L 1 - L 0) := by
    change L (unitInterval.symm 1) - L (unitInterval.symm 0) = -(L 1 - L 0)
    rw [unitInterval.symm_zero, unitInterval.symm_one]
    ring
  rw [h2, hspec] at hspecR
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have h3 : 2 * (Real.pi : ℂ) * Complex.I * (-(windingNumber γ q) : ℂ)
      = 2 * (Real.pi : ℂ) * Complex.I * (windingNumber R q : ℂ) := by
    rw [← hspecR]
    ring
  have h4 := mul_left_cancel₀ hπ h3
  exact_mod_cast h4.symm

/-- **Negation preserves winding about the origin.** -/
theorem winding_neg {γ : C(I, ℂ)} (hcl : γ 0 = γ 1) (hne : ∀ t : I, γ t ≠ 0) :
    windingNumber (-γ) 0 = windingNumber γ 0 := by
  have h1 : (-γ : C(I, ℂ)) = ContinuousMap.const I (-1 : ℂ) * γ := by
    ext t
    change -(γ t) = -1 * γ t
    ring
  have hccl : (ContinuousMap.const I (-1 : ℂ)) 0 = (ContinuousMap.const I (-1 : ℂ)) 1 :=
    rfl
  have hcne : ∀ t : I, (ContinuousMap.const I (-1 : ℂ)) t ≠ 0 := by
    intro t
    change (-1 : ℂ) ≠ 0
    norm_num
  rw [h1, windingNumber_mul _ _ hccl hcl hcne hne,
    windingNumber_const (-1) 0 (by norm_num), zero_add]

/-- **The tangent loop of a negatively directed basepoint winds minus once.** -/
theorem tangent_winding_neg {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (hinj : Set.InjOn γ (Set.Ico 0 1))
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ 0).im ≤ (γ t).im)
    (hre : (g 0).re < 0) :
    windingNumber ⟨fun t : I => g ((t : ℝ)),
      hg.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = -1 := by
  set γ' : ℝ → ℂ := fun u => γ (1 - u) with hγ'def
  set g' : ℝ → ℂ := fun u => -(g (1 - u)) with hg'def
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t) ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hd' : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ' (g' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h2 := HasDerivAt.scomp t (hd (1 - t) (hmem t ht)) h1
    simpa [hγ'def, hg'def] using! h2
  have hg'c : ContinuousOn g' (Set.Icc 0 1) := by
    refine ContinuousOn.neg (hg.comp ?_ hmem)
    exact (continuous_const.sub continuous_id).continuousOn
  have hcl' : γ' 0 = γ' 1 := by
    change γ (1 - 0) = γ (1 - 1)
    norm_num
    rw [hcl]
  have hgcl' : g' 1 = g' 0 := by
    change -(g (1 - 1)) = -(g (1 - 0))
    norm_num
    rw [hgcl]
  have hinj' : Set.InjOn γ' (Set.Ico 0 1) := by
    intro x hx y hy hxy
    have hxy' : γ (1 - x) = γ (1 - y) := hxy
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0 <;> rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · rw [← hx0, ← hy0]
    · exfalso
      rw [← hx0] at hxy'
      norm_num at hxy'
      rw [← hcl] at hxy'
      have h3 := hinj ⟨by linarith [hy.2], by linarith⟩
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Set.Ico (0:ℝ) 1) hxy'.symm
      linarith [hy.2]
    · exfalso
      rw [← hy0] at hxy'
      norm_num at hxy'
      rw [← hcl] at hxy'
      have h3 := hinj ⟨by linarith [hx.2], by linarith⟩
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Set.Ico (0:ℝ) 1) hxy'
      linarith [hx.2]
    · have h3 := hinj ⟨by linarith [hx.2], by linarith⟩
        ⟨by linarith [hy.2], by linarith⟩ hxy'
      linarith
  have hg'ne : ∀ u ∈ Set.Icc (0:ℝ) 1, g' u ≠ 0 := by
    intro u hu
    exact neg_ne_zero.mpr (hgne _ (hmem u hu))
  have hmin' : ∀ t ∈ Set.Icc (0:ℝ) 1, (γ' 0).im ≤ (γ' t).im := by
    intro t ht
    change (γ (1 - 0)).im ≤ (γ (1 - t)).im
    norm_num
    rw [← hcl]
    exact hmin _ (hmem t ht)
  have hre' : 0 < (g' 0).re := by
    change 0 < (-(g (1 - 0))).re
    norm_num
    rw [hgcl]
    linarith
  have hpos := tangent_winding_pos hd' hg'c hcl' hgcl' hinj' hg'ne hmin' hre'
  -- identify the primed tangent curve with the negated reversed curve
  set G : C(I, ℂ) := ⟨fun t : I => g ((t : ℝ)),
    hg.comp_continuous continuous_subtype_val fun t => t.2⟩ with hGdef
  have hGcl : G 0 = G 1 := by
    change g (((0:I) : ℝ)) = g (((1:I) : ℝ))
    rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl, hgcl]
  have hGne : ∀ t : I, G t ≠ 0 := fun t => hgne _ t.2
  have hRcl : (G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) 0
      = (G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) 1 := by
    change G (unitInterval.symm 0) = G (unitInterval.symm 1)
    rw [unitInterval.symm_zero, unitInterval.symm_one, hGcl]
  have hRne : ∀ t : I, (G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) t
      ≠ 0 := fun t => hGne _
  have hident : (⟨fun t : I => g' ((t : ℝ)),
      hg'c.comp_continuous continuous_subtype_val fun t => t.2⟩ : C(I, ℂ))
      = -(G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) := by
    ext t
    change -(g (1 - ((t : ℝ)))) = -(g ((unitInterval.symm t : ℝ)))
    rw [unitInterval.coe_symm_eq]
  rw [hident] at hpos
  rw [winding_neg hRcl hRne, winding_reverse hGcl hGne] at hpos
  linarith [hpos]

/-- The cyclic rotation of a closed curve: traverse from the new basepoint `c` to the
end, then wrap around from the start. -/
noncomputable def rotateLoop (γ : C(I, ℂ)) (c : ℝ) : ℝ → ℂ := fun u =>
  if u + c ≤ 1 then γ (Set.projIcc 0 1 zero_le_one (u + c))
  else γ (Set.projIcc 0 1 zero_le_one (u + c - 1))

/-- The basepoint-rotated loop of a closed continuous loop is continuous. -/
theorem rotateLoop_continuous (γ : C(I, ℂ)) {c : ℝ} (hcl : γ 0 = γ 1) :
    Continuous (rotateLoop γ c) := by
  unfold rotateLoop
  refine Continuous.if_le ?_ ?_ (continuous_id.add continuous_const)
    continuous_const ?_
  · exact γ.continuous.comp (continuous_projIcc.comp
      (continuous_id.add continuous_const))
  · exact γ.continuous.comp (continuous_projIcc.comp
      ((continuous_id.add continuous_const).sub continuous_const))
  · intro u hu
    rw [hu]
    norm_num
    exact hcl.symm

/-- Values of the rotated curve below the seam. -/
theorem rotateLoop_apply_le (γ : C(I, ℂ)) {c u : ℝ} (h : u + c ≤ 1) :
    rotateLoop γ c u = γ (Set.projIcc 0 1 zero_le_one (u + c)) := if_pos h

/-- Values of the rotated curve beyond the seam. -/
theorem rotateLoop_apply_gt (γ : C(I, ℂ)) {c u : ℝ} (h : ¬ u + c ≤ 1) :
    rotateLoop γ c u = γ (Set.projIcc 0 1 zero_le_one (u + c - 1)) := if_neg h

/-- **Cyclic reparametrization preserves winding**: the rotated closed curve has the
same winding number about every avoided point. -/
theorem winding_rotate {γ : C(I, ℂ)} {q : ℂ} (hcl : γ 0 = γ 1)
    (hne : ∀ t : I, γ t ≠ q) {c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1) :
    windingNumber ⟨fun t : I => rotateLoop γ c ((t : ℝ)),
        (rotateLoop_continuous γ hcl).comp continuous_subtype_val⟩ q
      = windingNumber γ q := by
  have hδne : ∀ t : I, shiftedCurve γ q t ≠ 0 := by
    intro t
    simpa [shiftedCurve, sub_eq_zero] using hne t
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ q) hδne
  have hspec := windingNumber_spec hcl hne hL
  have hexp1 : Complex.exp (L 1 - L 0) = 1 := by
    rw [hspec, show (2:ℂ) * Real.pi * Complex.I * (windingNumber γ q : ℂ)
      = (windingNumber γ q : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  set R : C(I, ℂ) := ⟨fun t : I => rotateLoop γ c ((t : ℝ)),
    (rotateLoop_continuous γ hcl).comp continuous_subtype_val⟩ with hRdef
  set LrotF : ℝ → ℂ := fun u =>
    if u + c ≤ 1 then L (Set.projIcc 0 1 zero_le_one (u + c))
    else L (Set.projIcc 0 1 zero_le_one (u + c - 1)) + (L 1 - L 0) with hLrdef
  have hLrc : Continuous LrotF := by
    rw [hLrdef]
    refine Continuous.if_le ?_ ?_ (continuous_id.add continuous_const)
      continuous_const ?_
    · exact L.continuous.comp (continuous_projIcc.comp
        (continuous_id.add continuous_const))
    · exact (L.continuous.comp (continuous_projIcc.comp
        ((continuous_id.add continuous_const).sub continuous_const))).add
        continuous_const
    · intro u hu
      rw [hu]
      norm_num
  set Lrot : C(I, ℂ) := ⟨fun t : I => LrotF ((t : ℝ)),
    hLrc.comp continuous_subtype_val⟩ with hLrotdef
  have hRcl : R 0 = R 1 := by
    change rotateLoop γ c (((0:I) : ℝ)) = rotateLoop γ c (((1:I) : ℝ))
    rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl]
    rcases le_or_gt (1 + c) 1 with h | h
    · have hc0 : c = 0 := by linarith [hc.1]
      rw [rotateLoop_apply_le γ (by linarith : (0:ℝ) + c ≤ 1),
        rotateLoop_apply_le γ h, hc0]
      norm_num
      exact hcl
    · rw [rotateLoop_apply_le γ (by linarith [hc.2] : (0:ℝ) + c ≤ 1),
        rotateLoop_apply_gt γ (not_le.mpr h)]
      norm_num
  have hRne : ∀ t : I, R t ≠ q := by
    intro t
    change rotateLoop γ c ((t : ℝ)) ≠ q
    unfold rotateLoop
    split_ifs <;> exact hne _
  have hLrlift : IsLogLiftOf Lrot (shiftedCurve R q) := by
    intro t
    have hval : shiftedCurve R q t = rotateLoop γ c ((t : ℝ)) - q := by
      simp [shiftedCurve, hRdef]
    change Complex.exp (LrotF ((t : ℝ))) = shiftedCurve R q t
    rw [hval]
    change Complex.exp (if ((t : ℝ)) + c ≤ 1
        then L (Set.projIcc 0 1 zero_le_one (((t : ℝ)) + c))
        else L (Set.projIcc 0 1 zero_le_one (((t : ℝ)) + c - 1)) + (L 1 - L 0))
      = rotateLoop γ c ((t : ℝ)) - q
    unfold rotateLoop
    split_ifs with h
    · have h1 := hL (Set.projIcc 0 1 zero_le_one (((t : ℝ)) + c))
      simpa [shiftedCurve] using h1
    · rw [Complex.exp_add, hexp1, mul_one]
      have h1 := hL (Set.projIcc 0 1 zero_le_one (((t : ℝ)) + c - 1))
      simpa [shiftedCurve] using h1
  have hspecR := windingNumber_spec hRcl hRne hLrlift
  have hinc : Lrot 1 - Lrot 0 = L 1 - L 0 := by
    change LrotF (((1:I) : ℝ)) - LrotF (((0:I) : ℝ)) = L 1 - L 0
    rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl, hLrdef]
    rcases le_or_gt (1 + c) 1 with h | h
    · have hc0 : c = 0 := by linarith [hc.1]
      simp only [hc0]
      norm_num
    · simp only [if_pos (by linarith [hc.2] : (0:ℝ) + c ≤ 1),
        if_neg (not_le.mpr h)]
      norm_num
  rw [hinc, hspec] at hspecR
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have h4 := mul_left_cancel₀ hπ hspecR
  exact_mod_cast h4.symm

/-- The chart pullback takes values in the chart domain and develops to the target. -/
theorem chart_pullback_dev {Φ : ℂ → ℂ} {S : Set ℂ}
    {y : ℂ} (hy : y ∈ Φ '' S) :
    Function.invFunOn Φ S y ∈ S ∧ Φ (Function.invFunOn Φ S y) = y := by
  obtain ⟨x, hxS, hxy⟩ := hy
  subst hxy
  exact ⟨Function.invFunOn_mem ⟨x, hxS, rfl⟩, Function.invFunOn_eq ⟨x, hxS, rfl⟩⟩

/-- **Differentiating the chart pullback**: a differentiable target curve through the
developed image of an injective holomorphic chart pulls back to a curve differentiable
with the reciprocal chart derivative, wherever the chart derivative does not vanish. -/
theorem chart_pullback_hasDerivAt {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    {w : ℝ → ℂ} {w' : ℂ} {t : ℝ}
    (hw : HasDerivAt w w' t)
    (htr : ∀ᶠ u in nhds t, w u ∈ Φ '' S)
    (hder : deriv Φ (Function.invFunOn Φ S (w t)) ≠ 0) :
    HasDerivAt (fun u => Function.invFunOn Φ S (w u))
      (w' / deriv Φ (Function.invFunOn Φ S (w t))) t := by
  have hwt : w t ∈ Φ '' S := htr.self_of_nhds
  set p : ℂ := Function.invFunOn Φ S (w t) with hpdef
  obtain ⟨hpS, hΦp⟩ := chart_pullback_dev hwt
  have han : AnalyticAt ℂ Φ p := (hΦ.analyticOnNhd hS) p hpS
  have hstrict : HasStrictDerivAt Φ (deriv Φ p) p :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  set g : ℂ → ℂ := hstrict.localInverse Φ (deriv Φ p) p hder with hgdef
  have hgleft : g (Φ p) = p := (hstrict.eventually_left_inverse hder).self_of_nhds
  have hgcont : ContinuousAt g (Φ p) :=
    (hstrict.to_localInverse hder).hasDerivAt.continuousAt
  have hgS : ∀ᶠ y in nhds (Φ p), g y ∈ S := by
    rw [ContinuousAt, hgleft] at hgcont
    exact hgcont (hS.mem_nhds hpS)
  have hgright : ∀ᶠ y in nhds (Φ p), Φ (g y) = y :=
    hstrict.eventually_right_inverse hder
  have hι : Filter.Tendsto w (nhds t) (nhds (Φ p)) := by
    rw [hΦp]
    exact hw.continuousAt
  have heq : (fun u => Function.invFunOn Φ S (w u)) =ᶠ[nhds t] fun u => g (w u) := by
    filter_upwards [htr, hι hgS, hι hgright] with u hu h1u h2u
    obtain ⟨hmem, hdev⟩ := chart_pullback_dev hu
    exact hinj hmem h1u (by rw [hdev, h2u])
  have hg' : HasDerivAt g ((deriv Φ p)⁻¹) (w t) :=
    hΦp ▸ (hstrict.to_localInverse hder).hasDerivAt
  have hcomp : HasDerivAt (fun u => g (w u)) ((deriv Φ p)⁻¹ * w') t :=
    HasDerivAt.comp (h := w) t hg' hw
  have hfinal : HasDerivAt (fun u => Function.invFunOn Φ S (w u))
      ((deriv Φ p)⁻¹ * w') t := hcomp.congr_of_eventuallyEq heq
  rw [div_eq_mul_inv, mul_comm]
  exact hfinal

/-- **Derivative of a circular arc**: the parametrized circle differentiates to the
rotated radius times the angular speed. -/
theorem circle_hasDerivAt (c : ℂ) (r α ω t : ℝ) :
    HasDerivAt (fun u : ℝ => c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ)
        + (ω : ℂ) * u)))
      ((r : ℂ) * Complex.I * (ω : ℂ)
        * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * t))) t := by
  have hinner : HasDerivAt (fun u : ℝ => Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      (Complex.I * (ω : ℂ)) t := by
    have h1 : HasDerivAt (fun z : ℂ => Complex.I * ((α : ℂ) + (ω : ℂ) * z))
        (Complex.I * (ω : ℂ)) ((t : ℝ) : ℂ) := by
      have h2 : HasDerivAt (fun z : ℂ => (α : ℂ) + (ω : ℂ) * z) ((ω : ℂ))
          ((t : ℝ) : ℂ) := by
        simpa using ((hasDerivAt_id (((t : ℝ)) : ℂ)).const_mul ((ω : ℂ))).const_add
          ((α : ℂ))
      simpa using h2.const_mul Complex.I
    exact h1.comp_ofReal
  have hexp := hinner.cexp
  have h3 := (hexp.const_mul ((r : ℂ))).const_add c
  convert! h3 using 1
  ring

/-- **The chart phase identity**: along any curve, the chart velocity squares to the
negated differential times the squared curve velocity. -/
theorem pullback_phase {q Φ : ℂ → ℂ} {S : Set ℂ}
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z) {z : ℂ} (hz : z ∈ S) {ρ' w' : ℂ}
    (hchain : deriv Φ z * ρ' = w') :
    q z * ρ' ^ 2 = -(w' ^ 2) := by
  have h1 := hsq z hz
  calc q z * ρ' ^ 2 = -(deriv Φ z ^ 2 * ρ' ^ 2) := by
        rw [h1]
        ring
    _ = -((deriv Φ z * ρ') ^ 2) := by ring
    _ = -(w' ^ 2) := by rw [hchain]

/-- The unclamped quarter-schedule concatenation of four globally defined curves. -/
noncomputable def quarterPW (f₀ f₁ f₂ f₃ : ℝ → ℂ) : ℝ → ℂ := fun t =>
  if t ≤ 1/4 then f₀ (4*t)
  else if t ≤ 1/2 then f₁ (4*t - 1)
  else if t ≤ 3/4 then f₂ (4*t - 2)
  else f₃ (4*t - 3)

/-- Differentiability transported along agreement on an open set. -/
theorem open_congr {F f : ℝ → ℂ} {d : ℂ} {t : ℝ} {O : Set ℝ}
    (hO : IsOpen O) (ht : t ∈ O) (hd : HasDerivAt f d t)
    (heq : ∀ u ∈ O, F u = f u) : HasDerivAt F d t := by
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds ht] with u hu
  exact heq u hu

/-- **Seam gluing with windowed agreements**: a function agreeing with a left piece on
a left half-open window ending at the seam and with a right piece on a right half-open
window, the pieces meeting with equal velocity, differentiates at the seam. -/
theorem seam_glue {F fL fR : ℝ → ℂ} {dL dR : ℂ} {a s b : ℝ}
    (has : a < s) (hsb : s < b)
    (hdL : HasDerivAt fL dL s) (hdR : HasDerivAt fR dR s) (hd : dL = dR)
    (hLeq : ∀ u ∈ Set.Ioc a s, F u = fL u) (hReq : ∀ u ∈ Set.Ico s b, F u = fR u) :
    HasDerivAt F dL s := by
  have hFs : F s = fL s := hLeq s ⟨has, le_rfl⟩
  have hFs' : F s = fR s := hReq s ⟨le_rfl, hsb⟩
  have hL : HasDerivWithinAt F dL (Set.Iic s) s := by
    refine hdL.hasDerivWithinAt.congr_of_eventuallyEq ?_ hFs
    have ha : Set.Ioi a ∈ nhds s := Ioi_mem_nhds has
    filter_upwards [nhdsWithin_le_nhds ha, self_mem_nhdsWithin] with u hua hus
    exact hLeq u ⟨hua, hus⟩
  have hR : HasDerivWithinAt F dL (Set.Ici s) s := by
    rw [hd]
    refine hdR.hasDerivWithinAt.congr_of_eventuallyEq ?_ hFs'
    have hb : Set.Iio b ∈ nhds s := Iio_mem_nhds hsb
    filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with u hub hus
    exact hReq u ⟨hus, hub⟩
  have hunion := hL.union hR
  rw [Set.Iic_union_Ici] at hunion
  exact hasDerivWithinAt_univ.mp hunion

/-- Branch values of the quarter-schedule concatenation. -/
theorem quarterPW_eval₀ {f₀ f₁ f₂ f₃ : ℝ → ℂ} {t : ℝ} (h : t ≤ 1 / 4) :
    quarterPW f₀ f₁ f₂ f₃ t = f₀ (4*t) := by
  unfold quarterPW
  exact if_pos h

end WindingBricks

end RiemannDynamics

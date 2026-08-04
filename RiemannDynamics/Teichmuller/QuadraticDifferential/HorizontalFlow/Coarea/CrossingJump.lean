/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Leaf.Exclusion

/-!
# The winding jump across a transversal crossing

Single crossings of a vertical segment, the winding jump across a transversal crossing,
the tracked vertical arcs through a chart, and the quadrilateral loop of the
monotonicity argument.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

section PrincipleTwo

open unitInterval

/-- **Orientation transport**: the sign-constancy principle yields both
orientation hypotheses of the bigon exclusion in either traversal. -/
theorem nonnegWinding_transport₂ (hW : NonnegWindingPrinciple₂) {ρ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ρ (g t) t)
    (hgc : ContinuousOn g (Set.Icc 0 1))
    (hcl : ρ 0 = ρ 1) (hgcl : g 1 = g 0)
    (hinj : Set.InjOn ρ (Set.Ico 0 1))
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0) :
    (∀ (hgw : Continuous fun t : I => g ((t : ℝ))),
      windingNumber ⟨fun t : I => g ((t : ℝ)), hgw⟩ 0 = 1 →
      ∀ (hc' : Continuous fun t : I => ρ ((t : ℝ))),
      ∀ ζ : ℂ, (∀ t : I, ρ ((t : ℝ)) ≠ ζ) →
        0 ≤ windingNumber ⟨fun t : I => ρ ((t : ℝ)), hc'⟩ ζ)
    ∧ (∀ (hgw : Continuous fun t : I => -(g (1 - ((t : ℝ))))),
      windingNumber ⟨fun t : I => -(g (1 - ((t : ℝ)))), hgw⟩ 0 = 1 →
      ∀ (hc' : Continuous fun t : I => ρ (1 - ((t : ℝ)))),
      ∀ ζ : ℂ, (∀ t : I, ρ (1 - ((t : ℝ))) ≠ ζ) →
        0 ≤ windingNumber ⟨fun t : I => ρ (1 - ((t : ℝ))), hc'⟩ ζ) := by
  constructor
  · exact hW ρ g hd hgc hcl hgcl hinj hgne
  · have hd' : ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivAt (fun u => ρ (1 - u)) (-(g (1 - t))) t := by
      intro t ht
      have hin : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub 1
      have hmem : 1 - t ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have h := (hd (1 - t) hmem).scomp t hin
      convert h using 1
      rw [neg_smul, one_smul]
    have hgc' : ContinuousOn (fun u : ℝ => -(g (1 - u))) (Set.Icc 0 1) := by
      refine ContinuousOn.neg ?_
      refine hgc.comp (Continuous.continuousOn (by fun_prop)) ?_
      intro u hu
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hcl' : ρ (1 - (0:ℝ)) = ρ (1 - (1:ℝ)) := by
      rw [show (1:ℝ) - 0 = 1 by norm_num, show (1:ℝ) - 1 = 0 by norm_num]
      exact hcl.symm
    have hgcl' : -(g (1 - (1:ℝ))) = -(g (1 - (0:ℝ))) := by
      rw [show (1:ℝ) - 0 = 1 by norm_num, show (1:ℝ) - 1 = 0 by norm_num, hgcl]
    have hinj' : Set.InjOn (fun u : ℝ => ρ (1 - u)) (Set.Ico 0 1) := by
      intro x hx y hy heq0
      have heq : ρ (1 - x) = ρ (1 - y) := heq0
      by_cases hx0 : x = 0
      · by_cases hy0 : y = 0
        · rw [hx0, hy0]
        · exfalso
          have hy' : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
          rw [hx0, show (1:ℝ) - 0 = 1 by norm_num] at heq
          have h1 : ρ 0 = ρ (1 - y) := by rw [hcl]; exact heq
          have h2 := hinj (Set.mem_Ico.mpr ⟨le_refl 0, by norm_num⟩)
            (Set.mem_Ico.mpr ⟨by linarith [hy.2], by linarith⟩) h1
          linarith [hy.2]
      · by_cases hy0 : y = 0
        · exfalso
          have hx' : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
          rw [hy0, show (1:ℝ) - 0 = 1 by norm_num] at heq
          have h1 : ρ 0 = ρ (1 - x) := by rw [hcl]; exact heq.symm
          have h2 := hinj (Set.mem_Ico.mpr ⟨le_refl 0, by norm_num⟩)
            (Set.mem_Ico.mpr ⟨by linarith [hx.2], by linarith⟩) h1
          linarith [hx.2]
        · have hx' : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
          have hy' : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
          have h := hinj (Set.mem_Ico.mpr ⟨by linarith [hx.2], by linarith⟩)
            (Set.mem_Ico.mpr ⟨by linarith [hy.2], by linarith⟩) heq
          linarith
    have hgne' : ∀ u ∈ Set.Icc (0:ℝ) 1, -(g (1 - u)) ≠ 0 := by
      intro u hu
      simp only [ne_eq, neg_eq_zero]
      exact hgne (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    exact hW (fun u => ρ (1 - u)) (fun u => -(g (1 - u))) hd' hgc' hcl' hgcl'
      hinj' hgne'

end PrincipleTwo

/-- **Every interior-level leaf is crossed**: under the no-bigon principles, a
competitor path joining the ends of a vertical trajectory meets every all-time
transverse leaf anchored at an interior level. -/
theorem level_crossing {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} (hϑ : IsTrajOn q ϑ (Set.Ici (-1))) {T : ℝ} (hT : 0 < T)
    {τ : ℝ → ℂ} (hτ : IsTrajOn (fun z => -q z) τ Set.univ)
    {tstar : ℝ} (hts : tstar ∈ Set.Ioo 0 T) (hτ0 : τ 0 = ϑ tstar)
    (p : C(unitInterval, ℂ)) (hp0 : p 0 = ϑ 0) (hp1 : p 1 = ϑ T)
    (hpim : ∀ s : unitInterval, 0 < (p s).im) :
    ∃ (s : unitInterval) (u : ℝ), p s = τ u :=
  competitor_crosses_leaf hq hbigon hbigonH hϑ (by norm_num) hT hτ hts hτ0
    p hp0 hp1 hpim
    (hjump_of_bigons hq hbigon hbigonH ϑ (-1) hϑ (by norm_num) T hT τ hτ
      tstar hts hτ0 p hp0 hp1 hpim)

/-- **Piece height-count**: heights attained by an absolutely continuous curve piece
tracked in a natural chart form a set of measure at most the piece's horizontal
variation. -/
theorem piece_lambda_bound {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V)
    (hΨsq : ∀ w ∈ V, deriv Ψ w ^ 2 = -(-q w))
    {p : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hpc : ContinuousOn p (Set.Icc a b))
    (hpac : AbsolutelyContinuousOnInterval p a b)
    (htrk : ∀ s ∈ Set.Icc a b, p s ∈ V)
    {Λ : Set ℝ} (hΛ : ∀ l ∈ Λ, ∃ s ∈ Set.Icc a b, (Ψ (p s)).im = l) :
    volume Λ ≤ ∫⁻ s in Set.Icc a b, horizontalDensity q p s := by
  set g : ℝ → ℝ := fun s => (Ψ (p s)).im with hgdef
  have hgc : ContinuousOn g (Set.Icc a b) :=
    Complex.continuous_im.comp_continuousOn (hΨd.continuousOn.comp hpc htrk)
  have hne : (Set.Icc a b).Nonempty := ⟨a, Set.left_mem_Icc.mpr hab⟩
  obtain ⟨u₁, hu₁, hmin⟩ := isCompact_Icc.exists_isMinOn hne hgc
  obtain ⟨u₂, hu₂, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hgc
  have hΛsub : Λ ⊆ Set.Icc (g u₁) (g u₂) := by
    intro l hl
    obtain ⟨s, hs, hlv⟩ := hΛ l hl
    exact ⟨by rw [← hlv]; exact isMinOn_iff.mp hmin s hs,
      by rw [← hlv]; exact isMaxOn_iff.mp hmax s hs⟩
  have hv1 : volume Λ ≤ ENNReal.ofReal (g u₂ - g u₁) := by
    refine le_trans (measure_mono hΛsub) (le_of_eq ?_)
    rw [Real.volume_Icc]
  refine le_trans hv1 ?_
  rcases eq_or_ne u₁ u₂ with heq | hne'
  · rw [heq]
    simp
  · set a' : ℝ := min u₁ u₂ with ha'def
    set b' : ℝ := max u₁ u₂ with hb'def
    have hab' : a' < b' := min_lt_max.mpr hne'
    have hsub' : Set.Icc a' b' ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc (le_min hu₁.1 hu₂.1) (max_le hu₁.2 hu₂.2)
    have h6 := im_segment_variation_lb hV hΨd hΨsq hab' (hpc.mono hsub')
      (hpac.mono (by
        rw [Set.uIcc_of_le hab'.le, Set.uIcc_of_le hab]
        exact hsub'))
      (fun s hs => htrk s (hsub' hs))
    have h7 : g u₂ - g u₁ ≤ |g b' - g a'| := by
      rcases le_total u₁ u₂ with h | h
      · rw [ha'def, hb'def, min_eq_left h, max_eq_right h]
        exact le_abs_self _
      · rw [ha'def, hb'def, min_eq_right h, max_eq_left h, abs_sub_comm]
        exact le_abs_self _
    exact le_trans (ENNReal.ofReal_le_ofReal h7)
      (le_trans h6 (lintegral_mono_set hsub'))

section FinalFeedTwo

open unitInterval

/-- **Monogon exclusion**: under the nonnegative-winding principle, no trajectory of a
nontrivial holomorphic field closes up injectively over an interior interval. -/
theorem no_monogon₂ {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hW : NonnegWindingPrinciple₂)
    {γ : ℝ → ℂ} {sdom : Set ℝ} (hγ : IsTrajOn q γ sdom) {c d : ℝ} (hcd : c < d)
    (hnh : ∀ w ∈ Set.Icc c d, sdom ∈ nhds w)
    (hcl : γ c = γ d) (hinj : Set.InjOn γ (Set.Ico c d)) : False := by
  set ℓ : ℝ := (d - c)/4 with hℓdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; linarith
  have hd4 : c + 4*ℓ = d := by rw [hℓdef]; ring
  have h3 : ℓ < 3*ℓ := by linarith
  have hcl4 : γ c = γ (c + 4*ℓ) := by rw [hd4]; exact hcl
  have hnh4 : ∀ w ∈ Set.Icc c (c + 4*ℓ), sdom ∈ nhds w := by
    rw [hd4]; exact hnh
  have hinj4 : Set.InjOn γ (Set.Ico c (c + 4*ℓ)) := by
    rw [hd4]; exact hinj
  obtain ⟨hdA, hdC, hqγ⟩ := arc_prep hγ hnh4
  have hclv : deriv γ c = deriv γ (c + 4*ℓ) :=
    monogon_closed hγ (by linarith) hnh4 hcl4 hinj4
  obtain ⟨hd1, hv01, hv12, hv23, hv30, hg01, hg12, hg23, hg30⟩ :=
    monogon_bundle hℓ hdA hdC hqγ hcl4 hclv
  have hmemdom : ∀ w ∈ Set.Icc c (c + 4*ℓ), w ∈ sdom := fun w hw =>
    mem_of_mem_nhds (hnh4 w hw)
  -- window maps for the four quarters
  have hmaps₀ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp c ℓ ℓ u ∈ Set.Icc c (c + 4*ℓ) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := c) hℓ h3 u hu
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmaps₁ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp (c + ℓ) ℓ ℓ u ∈ Set.Icc c (c + 4*ℓ) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := c + ℓ) hℓ h3 u hu
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmaps₂ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp (c + 2*ℓ) ℓ ℓ u ∈ Set.Icc c (c + 4*ℓ) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := c + 2*ℓ) hℓ h3 u hu
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmaps₃ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp (c + 3*ℓ) ℓ ℓ u ∈ Set.Icc c (c + 4*ℓ) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := c + 3*ℓ) hℓ h3 u hu
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- speed continuities from the arc packages
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have hq₀ : ∀ w ∈ Set.Icc c (c + ℓ),
      q (γ w) * (deriv γ w) ^ 2 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [hE]
    exact fun w hw => hqγ w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hq₁ : ∀ w ∈ Set.Icc (c + ℓ) ((c + ℓ) + ℓ),
      q (γ w) * (deriv γ w) ^ 2 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [hE]
    exact fun w hw => hqγ w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hq₂ : ∀ w ∈ Set.Icc (c + 2*ℓ) ((c + 2*ℓ) + ℓ),
      q (γ w) * (deriv γ w) ^ 2 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [hE]
    exact fun w hw => hqγ w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hq₃ : ∀ w ∈ Set.Icc (c + 3*ℓ) ((c + 3*ℓ) + ℓ),
      q (γ w) * (deriv γ w) ^ 2 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [hE]
    exact fun w hw => hqγ w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hd₀ : ∀ w ∈ Set.Icc c (c + ℓ), HasDerivAt γ (deriv γ w) w := fun w hw =>
    hdA w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hd₁ : ∀ w ∈ Set.Icc (c + ℓ) ((c + ℓ) + ℓ), HasDerivAt γ (deriv γ w) w :=
    fun w hw => hdA w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hd₂ : ∀ w ∈ Set.Icc (c + 2*ℓ) ((c + 2*ℓ) + ℓ), HasDerivAt γ (deriv γ w) w :=
    fun w hw => hdA w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hd₃ : ∀ w ∈ Set.Icc (c + 3*ℓ) ((c + 3*ℓ) + ℓ), HasDerivAt γ (deriv γ w) w :=
    fun w hw => hdA w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hc₀ : ContinuousOn (deriv γ) (Set.Icc c (c + ℓ)) :=
    hdC.mono fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hc₁ : ContinuousOn (deriv γ) (Set.Icc (c + ℓ) ((c + ℓ) + ℓ)) :=
    hdC.mono fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hc₂ : ContinuousOn (deriv γ) (Set.Icc (c + 2*ℓ) ((c + 2*ℓ) + ℓ)) :=
    hdC.mono fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hc₃ : ContinuousOn (deriv γ) (Set.Icc (c + 3*ℓ) ((c + 3*ℓ) + ℓ)) :=
    hdC.mono fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨hA1, -, -, -, -, -, hA7, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₀ hc₀ hq₀
  obtain ⟨hB1, -, -, -, -, -, hB7, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₁ hc₁ hq₁
  obtain ⟨hC1, -, -, -, -, -, hC7, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₂ hc₂ hq₂
  obtain ⟨hD1, -, -, -, -, -, hD7, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₃ hc₃ hq₃
  -- nonvanishing velocities
  have hdne : ∀ w ∈ Set.Icc c (c + 4*ℓ), deriv γ w ≠ 0 := by
    intro w hw h0
    have h1 := hqγ w hw
    rw [h0] at h1
    simp at h1
  have hgne : ∀ u ∈ Set.Icc (0:ℝ) 1, (4:ℂ) * quarterPW (rampArcSpeed γ c ℓ ℓ)
      (rampArcSpeed γ (c + ℓ) ℓ ℓ) (rampArcSpeed γ (c + 2*ℓ) ℓ ℓ)
      (rampArcSpeed γ (c + 3*ℓ) ℓ ℓ) u ≠ 0 :=
    quarterPW_ne
      (rampSpeed_ne hℓ h3 fun w hw =>
        hdne w ⟨by linarith [hw.1], by linarith [hw.2]⟩)
      (rampSpeed_ne hℓ h3 fun w hw =>
        hdne w ⟨by linarith [hw.1], by linarith [hw.2]⟩)
      (rampSpeed_ne hℓ h3 fun w hw =>
        hdne w ⟨by linarith [hw.1], by linarith [hw.2]⟩)
      (rampSpeed_ne hℓ h3 fun w hw =>
        hdne w ⟨by linarith [hw.1], by linarith [hw.2]⟩)
  -- the track factorization through the arc
  have hfact : ∀ u ∈ Set.Icc (0:ℝ) 1, ∃ w ∈ Set.Icc c (c + 4*ℓ),
      quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
        (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ) u = γ w := by
    intro u hu
    by_cases h1 : u ≤ 1/4
    · exact ⟨cubicRamp c ℓ ℓ (4*u), hmaps₀ _ ⟨by linarith [hu.1], by linarith⟩,
        by rw [quarterPW_eval₀ h1, rampArc_apply]⟩
    · by_cases h2 : u ≤ 1/2
      · exact ⟨cubicRamp (c + ℓ) ℓ ℓ (4*u - 1),
          hmaps₁ _ ⟨by linarith [not_le.mp h1], by linarith⟩,
          by rw [quarterPW_eval₁ h1 h2, rampArc_apply]⟩
      · by_cases h3' : u ≤ 3/4
        · exact ⟨cubicRamp (c + 2*ℓ) ℓ ℓ (4*u - 2),
            hmaps₂ _ ⟨by linarith [not_le.mp h2], by linarith⟩,
            by rw [quarterPW_eval₂ h1 h2 h3', rampArc_apply]⟩
        · exact ⟨cubicRamp (c + 3*ℓ) ℓ ℓ (4*u - 3),
            hmaps₃ _ ⟨by linarith [not_le.mp h3'], by linarith [hu.2]⟩,
            by rw [quarterPW_eval₃ h1 h2 h3', rampArc_apply]⟩
  have hρH : ∀ u ∈ Set.Icc (0:ℝ) 1,
      0 < (quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
        (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ) u).im := by
    intro u hu
    obtain ⟨w, hw, heq⟩ := hfact u hu
    rw [heq]
    exact (traj_regular hγ (hmemdom w hw)).1
  have hqneρ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      q (quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
        (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ) u) ≠ 0 := by
    intro u hu
    obtain ⟨w, hw, heq⟩ := hfact u hu
    rw [heq]
    exact (traj_regular hγ (hmemdom w hw)).2
  have hρc : ContinuousOn (quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
      (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ)) (Set.Icc 0 1) :=
    fun v hv => (hd1 v hv).continuousAt.continuousWithinAt
  obtain ⟨U, hUo, hUconv, hUH, hfin, htrU⟩ := loop_hull hq hq0 hρc hρH
  -- piece continuity and upper-half membership for the composed continuity
  have hPc₀ : ContinuousOn (rampArc γ c ℓ ℓ) (Set.Icc 0 1) :=
    fun v hv => (hA1 v hv).continuousAt.continuousWithinAt
  have hPc₁ : ContinuousOn (rampArc γ (c + ℓ) ℓ ℓ) (Set.Icc 0 1) :=
    fun v hv => (hB1 v hv).continuousAt.continuousWithinAt
  have hPc₂ : ContinuousOn (rampArc γ (c + 2*ℓ) ℓ ℓ) (Set.Icc 0 1) :=
    fun v hv => (hC1 v hv).continuousAt.continuousWithinAt
  have hPc₃ : ContinuousOn (rampArc γ (c + 3*ℓ) ℓ ℓ) (Set.Icc 0 1) :=
    fun v hv => (hD1 v hv).continuousAt.continuousWithinAt
  have hW₀ : ∀ u ∈ Set.Icc (0:ℝ) 1, rampArc γ c ℓ ℓ u ∈ {z : ℂ | 0 < z.im} := by
    intro u hu
    rw [rampArc_apply]
    exact (traj_regular hγ (hmemdom _ (hmaps₀ u hu))).1
  have hW₁ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      rampArc γ (c + ℓ) ℓ ℓ u ∈ {z : ℂ | 0 < z.im} := by
    intro u hu
    rw [rampArc_apply]
    exact (traj_regular hγ (hmemdom _ (hmaps₁ u hu))).1
  have hW₂ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      rampArc γ (c + 2*ℓ) ℓ ℓ u ∈ {z : ℂ | 0 < z.im} := by
    intro u hu
    rw [rampArc_apply]
    exact (traj_regular hγ (hmemdom _ (hmaps₂ u hu))).1
  have hW₃ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      rampArc γ (c + 3*ℓ) ℓ ℓ u ∈ {z : ℂ | 0 < z.im} := by
    intro u hu
    rw [rampArc_apply]
    exact (traj_regular hγ (hmemdom _ (hmaps₃ u hu))).1
  have hqρc := loop_q_continuous hq.continuousOn hPc₀ hPc₁ hPc₂ hPc₃
    hv01 hv12 hv23 hW₀ hW₁ hW₂ hW₃
  -- closure and velocity closure of the assembled loop
  have hclρ : quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
      (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ) 0
      = quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
        (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ) 1 := by
    rw [quarterPW_eval₀ (by norm_num),
      quarterPW_eval₃ (by norm_num) (by norm_num) (by norm_num),
      show (4:ℝ)*0 = 0 by norm_num, show (4:ℝ)*1 - 3 = 1 by norm_num, hv30]
  have hgclρ : (4:ℂ) * quarterPW (rampArcSpeed γ c ℓ ℓ) (rampArcSpeed γ (c + ℓ) ℓ ℓ)
      (rampArcSpeed γ (c + 2*ℓ) ℓ ℓ) (rampArcSpeed γ (c + 3*ℓ) ℓ ℓ) 1
      = 4 * quarterPW (rampArcSpeed γ c ℓ ℓ) (rampArcSpeed γ (c + ℓ) ℓ ℓ)
        (rampArcSpeed γ (c + 2*ℓ) ℓ ℓ) (rampArcSpeed γ (c + 3*ℓ) ℓ ℓ) 0 := by
    rw [quarterPW_eval₃ (by norm_num) (by norm_num) (by norm_num),
      quarterPW_eval₀ (by norm_num),
      show (4:ℝ)*1 - 3 = 1 by norm_num, show (4:ℝ)*0 = 0 by norm_num, hg30]
  have hgcρ : ContinuousOn (fun t : ℝ => (4:ℂ) * quarterPW (rampArcSpeed γ c ℓ ℓ)
      (rampArcSpeed γ (c + ℓ) ℓ ℓ) (rampArcSpeed γ (c + 2*ℓ) ℓ ℓ)
      (rampArcSpeed γ (c + 3*ℓ) ℓ ℓ) t) (Set.Icc 0 1) :=
    continuousOn_const.mul
      (quarterPW_continuousOn_Icc hA7 hB7 hC7 hD7 hg01 hg12 hg23)
  have hinjρ := monogon_injOn hℓ hinj4
  have hcount := monogon_count hℓ hdA hdC hqγ hcl4 hclv hqρc
    (hgcρ.comp_continuous continuous_subtype_val fun t => t.2)
  obtain ⟨hnnP, hnnR⟩ := nonnegWinding_transport₂ hW hd1 hgcρ hclρ hgclρ hinjρ hgne
  exact no_bigon_loop hUconv hUH hq hq0 hfin hd1 hgcρ hclρ hgclρ hinjρ hgne
    htrU hqneρ hqρc hcount (Or.inr (Or.inl rfl)) (hnnP _) hnnR

/-- **Bigon exclusion, transverse case**: under the nonnegative-winding principle, an
injective vertical and horizontal trajectory pair cannot meet exactly at two corners. -/
theorem no_bigon3₂ {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hW : NonnegWindingPrinciple₂)
    {γ τ : ℝ → ℂ} {a T b μ s : ℝ}
    (hμ : 0 < μ) (ha0 : 0 ≤ a) (haT : a < T) (hb0 : 0 < b) (hbs : b ≤ s)
    (hγ : IsTrajOn q γ (Set.Icc (-μ) (T + μ)))
    (hτ : IsTrajOn (fun z => -q z) τ (Set.Icc (-μ) (s + μ)))
    (hc1 : τ 0 = γ T) (hc2 : τ b = γ a)
    (hγinj : Set.InjOn γ (Set.Icc a T)) (hτinj : Set.InjOn τ (Set.Icc 0 b))
    (hcross : ∀ x ∈ Set.Icc a T, ∀ u ∈ Set.Icc 0 b,
      γ x = τ u → (x = T ∧ u = 0) ∨ (x = a ∧ u = b)) : False := by
  obtain ⟨S₁, S₂, Φ₁, Φ₂, ε₁, ε₂, r, r₀, η₁, η₂, hr, hrr₀, hε₁, hε₂, h3γ, h3τ,
    hS₁o, hΦ₁d, hΦ₁inj, hΦ₁sq, hq₁ne, hS₂o, hΦ₂d, hΦ₂inj, hΦ₂sq, hq₂ne,
    hball₁, hball₂, htr₁, htr₂, hdevγ₁, hdevτ₁, hdevγ₂, hdevτ₂, hκ₁b, hκ₂b,
    hfar₁γ, hfar₁τ, hfar₂γ, hfar₂τ, hηd, hη₁im, hη₂im⟩ :=
    discharge_pack₂ hμ ha0 haT hb0 hbs hγ hτ hc1 hc2 hγinj hτinj
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hv : (0:ℝ) < r * (Real.pi/2) := mul_pos hr (by linarith)
  have haTr : a + r ≤ T - r := by nlinarith
  have hrbr : r ≤ b - r := by nlinarith
  -- arc data on the truncated windows
  have hnhγ : ∀ w ∈ Set.Icc (a + r) (T - r), Set.Icc (-μ) (T + μ) ∈ nhds w := by
    intro w hw
    exact Icc_mem_nhds (by linarith [hw.1]) (by linarith [hw.2])
  have hnhτ : ∀ w ∈ Set.Icc r (b - r), Set.Icc (-μ) (s + μ) ∈ nhds w := by
    intro w hw
    exact Icc_mem_nhds (by linarith [hw.1]) (by linarith [hw.2])
  obtain ⟨hdγA, hdγC, hqγ⟩ := arc_prep hγ hnhγ
  obtain ⟨hdτA, hdτC, hqτ0⟩ := arc_prep hτ hnhτ
  have hqτ : ∀ w ∈ Set.Icc r (b - r), q (τ w) * (deriv τ w) ^ 2 = 1 := by
    intro w hw
    have h : -q (τ w) * (deriv τ w) ^ 2 = -1 := hqτ0 w hw
    linear_combination -h
  -- the count integer
  obtain ⟨m, hm, hm3⟩ : ∃ m : ℤ, 2 * (m : ℝ) = ε₂ - ε₁
      ∧ (m = -1 ∨ m = 0 ∨ m = 1) := by
    rcases hε₁ with h1 | h1 <;> rcases hε₂ with h2 | h2
    · exact ⟨0, by rw [h1, h2]; norm_num, Or.inr (Or.inl rfl)⟩
    · exact ⟨-1, by rw [h1, h2]; norm_num, Or.inl rfl⟩
    · exact ⟨1, by rw [h1, h2]; norm_num, Or.inr (Or.inr rfl)⟩
    · exact ⟨0, by rw [h1, h2]; norm_num, Or.inr (Or.inl rfl)⟩
  -- the four-piece bundle at the literal pins
  obtain ⟨hd1, hv01, hv12, hv23, hv30, hg01, hg12, hg23, hg30⟩ :=
    four_piece_bundle hr hrr₀ hε₁ hε₂ rfl rfl rfl rfl rfl rfl h3γ h3τ
      hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hball₁ hball₂
      hdevγ₁ hdevτ₁ hdevγ₂ hdevτ₂ hdγA hdγC hqγ hdτA hdτC hqτ
  -- corner packages at the literal pins
  have hω₁ne : (1 * (-ε₁) * (Real.pi / 2)) ≠ 0 := by
    rcases hε₁ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hω₂ne : (ε₂ * (Real.pi / 2)) ≠ 0 := by
    rcases hε₂ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hpk₁ := cornerPiece_package hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne htr₁
  have hpk₂ := cornerPiece_package hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne htr₂
  -- arc packages for speed continuity
  have heγ : (a + r) + (T - a - 2*r) = T - r := by ring
  have heτ : r + (b - 2*r) = b - r := by ring
  have hdA' : ∀ w ∈ Set.Icc (a + r) ((a + r) + (T - a - 2*r)),
      HasDerivAt γ (deriv γ w) w := by
    rw [heγ]; exact hdγA
  have hdC' : ContinuousOn (deriv γ) (Set.Icc (a + r) ((a + r) + (T - a - 2*r))) := by
    rw [heγ]; exact hdγC
  have hqγ' : ∀ w ∈ Set.Icc (a + r) ((a + r) + (T - a - 2*r)),
      q (γ w) * (deriv γ w) ^ 2 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [heγ, Complex.exp_pi_mul_I]
    exact hqγ
  have hdτA' : ∀ w ∈ Set.Icc r (r + (b - 2*r)), HasDerivAt τ (deriv τ w) w := by
    rw [heτ]; exact hdτA
  have hdτC' : ContinuousOn (deriv τ) (Set.Icc r (r + (b - 2*r))) := by
    rw [heτ]; exact hdτC
  have hqτ' : ∀ w ∈ Set.Icc r (r + (b - 2*r)),
      q (τ w) * (deriv τ w) ^ 2 = Complex.exp 0 := by
    rw [heτ, Complex.exp_zero]
    exact hqτ
  obtain ⟨hA1, -, -, -, -, -, hA7, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hv h3γ hdA' hdC' hqγ'
  obtain ⟨hB1, -, -, -, -, -, hB7, -⟩ :=
    arc_piece (f := τ) (df := deriv τ) hv h3τ hdτA' hdτC' hqτ'
  -- per-piece track facts
  have hdomγ : ∀ w ∈ Set.Icc (a + r) (T - r), w ∈ Set.Icc (-μ) (T + μ) :=
    fun w hw => mem_of_mem_nhds (hnhγ w hw)
  have hdomτ : ∀ w ∈ Set.Icc r (b - r), w ∈ Set.Icc (-μ) (s + μ) :=
    fun w hw => mem_of_mem_nhds (hnhτ w hw)
  have hmapsγ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) u
        ∈ Set.Icc (a + r) (T - r) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := a + r) hv h3γ u hu
    rwa [heγ] at h
  have hmapsτ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp r (r * (Real.pi/2)) (b - 2*r) u ∈ Set.Icc r (b - r) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := r) hv h3τ u hu
    rwa [heτ] at h
  have hballim : ∀ (p : ℂ) (η : ℝ), η ≤ p.im →
      ∀ z ∈ Metric.ball p η, 0 < z.im := by
    intro p η hη z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : |(z - p).im| ≤ ‖z - p‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    have h2 := abs_le.mp h1
    linarith [h2.1]
  have hW₀ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) u
        ∈ {z : ℂ | 0 < z.im} := by
    intro u hu
    rw [rampArc_apply]
    exact (traj_regular hγ (hdomγ _ (hmapsγ u hu))).1
  have hW₁ : ∀ u ∈ Set.Icc (0:ℝ) 1, cornerPiece Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
      (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)) u
      ∈ {z : ℂ | 0 < z.im} :=
    fun u _ => hballim _ _ hη₁im _ (hκ₁b u)
  have hW₂ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      rampArc τ r (r * (Real.pi/2)) (b - 2*r) u ∈ {z : ℂ | 0 < z.im} := by
    intro u hu
    rw [rampArc_apply]
    exact (traj_regular hτ (hdomτ _ (hmapsτ u hu))).1
  have hW₃ : ∀ u ∈ Set.Icc (0:ℝ) 1, cornerPiece Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
      (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2)) u
      ∈ {z : ℂ | 0 < z.im} :=
    fun u _ => hballim _ _ hη₂im _ (hκ₂b u)
  have hqne₀ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      q (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) u) ≠ 0 := by
    intro u hu
    rw [rampArc_apply]
    exact (traj_regular hγ (hdomγ _ (hmapsγ u hu))).2
  have hqne₁ : ∀ u ∈ Set.Icc (0:ℝ) 1, q (cornerPiece Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
      (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)) u) ≠ 0 :=
    fun u _ => hq₁ne _ (hpk₁ u).1
  have hqne₂ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      q (rampArc τ r (r * (Real.pi/2)) (b - 2*r) u) ≠ 0 := by
    intro u hu
    rw [rampArc_apply]
    intro h0
    have h : -q (τ (cubicRamp r (r * (Real.pi/2)) (b - 2*r) u)) ≠ 0 :=
      (traj_regular hτ (hdomτ _ (hmapsτ u hu))).2
    exact h (by rw [h0, neg_zero])
  have hqne₃ : ∀ u ∈ Set.Icc (0:ℝ) 1, q (cornerPiece Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
      (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2)) u) ≠ 0 :=
    fun u _ => hq₂ne _ (hpk₂ u).1
  -- the quarter transfer
  have hquarter : ∀ Pr : ℂ → Prop,
      (∀ u ∈ Set.Icc (0:ℝ) 1,
        Pr (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) u)) →
      (∀ u ∈ Set.Icc (0:ℝ) 1, Pr (cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)) u)) →
      (∀ u ∈ Set.Icc (0:ℝ) 1, Pr (rampArc τ r (r * (Real.pi/2)) (b - 2*r) u)) →
      (∀ u ∈ Set.Icc (0:ℝ) 1, Pr (cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2)) u)) →
      ∀ u ∈ Set.Icc (0:ℝ) 1, Pr (quarterPW
        (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
        (cornerPiece Φ₁ S₁
          (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
          (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
        (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
        (cornerPiece Φ₂ S₂
          (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
          (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) u) := by
    intro Pr h₀ h₁ h₂ h₃ u hu
    by_cases hu1 : u ≤ 1/4
    · rw [quarterPW_eval₀ hu1]
      exact h₀ _ ⟨by linarith [hu.1], by linarith⟩
    · by_cases hu2 : u ≤ 1/2
      · rw [quarterPW_eval₁ hu1 hu2]
        exact h₁ _ ⟨by linarith [not_le.mp hu1], by linarith⟩
      · by_cases hu3 : u ≤ 3/4
        · rw [quarterPW_eval₂ hu1 hu2 hu3]
          exact h₂ _ ⟨by linarith [not_le.mp hu2], by linarith⟩
        · rw [quarterPW_eval₃ hu1 hu2 hu3]
          exact h₃ _ ⟨by linarith [not_le.mp hu3], by linarith [hu.2]⟩
  have hρH := hquarter (fun z => 0 < z.im) hW₀ hW₁ hW₂ hW₃
  have hqneρ := hquarter (fun z => q z ≠ 0) hqne₀ hqne₁ hqne₂ hqne₃
  have hρc : ContinuousOn (quarterPW
      (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
      (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2)))) (Set.Icc 0 1) :=
    fun v hv' => (hd1 v hv').continuousAt.continuousWithinAt
  obtain ⟨U, hUo, hUconv, hUH, hfin, htrU⟩ := loop_hull hq hq0 hρc hρH
  -- piece and speed continuity
  have hPc₀ : ContinuousOn (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (Set.Icc 0 1) := fun v hv' => (hA1 v hv').continuousAt.continuousWithinAt
  have hPc₁ : ContinuousOn (cornerPiece Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
      (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2))) (Set.Icc 0 1) :=
    fun v _ => ((hpk₁ v).2.2.1).continuousAt.continuousWithinAt
  have hPc₂ : ContinuousOn (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
      (Set.Icc 0 1) := fun v hv' => (hB1 v hv').continuousAt.continuousWithinAt
  have hPc₃ : ContinuousOn (cornerPiece Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
      (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) (Set.Icc 0 1) :=
    fun v _ => ((hpk₂ v).2.2.1).continuousAt.continuousWithinAt
  have hqρc := loop_q_continuous hq.continuousOn hPc₀ hPc₁ hPc₂ hPc₃
    hv01 hv12 hv23 hW₀ hW₁ hW₂ hW₃
  have hG₁ := (cornerSpeed_continuous hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne
    htr₁).continuousOn (s := Set.Icc 0 1)
  have hG₃ := (cornerSpeed_continuous hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne
    htr₂).continuousOn (s := Set.Icc 0 1)
  have hgcρ : ContinuousOn (fun t : ℝ => (4:ℂ) * quarterPW
      (rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerSpeed Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
      (rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerSpeed Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) t) (Set.Icc 0 1) :=
    continuousOn_const.mul
      (quarterPW_continuousOn_Icc hA7 hG₁ hB7 hG₃ hg01 hg12 hg23)
  -- nonvanishing velocities
  have hdneγ : ∀ w ∈ Set.Icc (a + r) ((a + r) + (T - a - 2*r)),
      deriv γ w ≠ 0 := by
    rw [heγ]
    intro w hw h0
    have h1 := hqγ w hw
    rw [h0] at h1
    simp at h1
  have hdneτ : ∀ w ∈ Set.Icc r (r + (b - 2*r)), deriv τ w ≠ 0 := by
    rw [heτ]
    intro w hw h0
    have h1 := hqτ w hw
    rw [h0] at h1
    simp at h1
  have hgne : ∀ u ∈ Set.Icc (0:ℝ) 1, (4:ℂ) * quarterPW
      (rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerSpeed Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
      (rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerSpeed Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) u ≠ 0 :=
    quarterPW_ne (rampSpeed_ne hv h3γ hdneγ)
      (fun u _ => cornerSpeed_ne hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne htr₁ u)
      (rampSpeed_ne hv h3τ hdneτ)
      (fun u _ => cornerSpeed_ne hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne htr₂ u)
  -- loop closure
  have hclρ : quarterPW
      (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
      (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) 0
      = quarterPW
      (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
      (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) 1 := by
    rw [quarterPW_eval₀ (by norm_num),
      quarterPW_eval₃ (by norm_num) (by norm_num) (by norm_num),
      show (4:ℝ)*0 = 0 by norm_num, show (4:ℝ)*1 - 3 = 1 by norm_num, hv30]
  have hgclρ : (4:ℂ) * quarterPW
      (rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerSpeed Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
      (rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerSpeed Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) 1
      = 4 * quarterPW
      (rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerSpeed Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)))
      (rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerSpeed Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2))) 0 := by
    rw [quarterPW_eval₃ (by norm_num) (by norm_num) (by norm_num),
      quarterPW_eval₀ (by norm_num),
      show (4:ℝ)*1 - 3 = 1 by norm_num, show (4:ℝ)*0 = 0 by norm_num, hg30]
  have hinjρ := rounded_injOn₃ hr hrr₀ hε₁ hε₂ rfl rfl rfl rfl h3γ h3τ
    hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne htr₁ htr₂
    hdevγ₁ hdevτ₁ hdevγ₂ hdevτ₂ hγinj hτinj hcross hκ₁b hκ₂b
    hfar₁γ hfar₁τ hfar₂γ hfar₂τ hηd
  have hcount := four_piece_count hr hrr₀ hε₁ hε₂ rfl rfl rfl rfl rfl rfl hm
    h3γ h3τ hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne
    hball₁ hball₂ hdevγ₁ hdevτ₁ hdevγ₂ hdevτ₂ hdγA hdγC hqγ hdτA hdτC hqτ
    hqρc (hgcρ.comp_continuous continuous_subtype_val fun t => t.2)
  obtain ⟨hnnP, hnnR⟩ := nonnegWinding_transport₂ hW hd1 hgcρ hclρ hgclρ hinjρ hgne
  exact no_bigon_loop hUconv hUH hq hq0 hfin hd1 hgcρ hclρ hgclρ hinjρ hgne
    htrU hqneρ hqρc hcount hm3 (hnnP _) hnnR

/-- **The bigon principle**: under the nonnegative-winding principle, a vertical and a
horizontal trajectory of a nontrivial holomorphic field never bound a bigon. -/
theorem bigon_principle₂ {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hW : NonnegWindingPrinciple₂) :
    ∀ (sv th : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q sv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) th (Set.Icc (-μ) (s + μ)) →
      th 0 = sv T → th s = sv 0 → False := by
  intro sv th T s μ hT hs hμ hσ hτ hc1 hc2
  rcases bigon_extract hT hs hμ hσ hτ hc1 hc2 with
    ⟨a, b, ha0, hab, hbT, hcl, hinj⟩ | ⟨a, b, ha0, hab, hbs', hcl, hinj⟩ |
    ⟨a, b, ha0, haT, hb0, hbs', hcl, hγinj, hτinj, hcross⟩
  · exact no_monogon₂ hq hq0 hW hσ hab
      (fun w hw => Icc_mem_nhds (by linarith [hw.1]) (by linarith [hw.2]))
      hcl hinj
  · obtain ⟨z₀, hz₀, hz₀ne⟩ := hq0
    exact no_monogon₂ hq.neg ⟨z₀, hz₀, neg_ne_zero.mpr hz₀ne⟩ hW hτ hab
      (fun w hw => Icc_mem_nhds (by linarith [hw.1]) (by linarith [hw.2]))
      hcl hinj
  · exact no_bigon3₂ hq hq0 hW hμ ha0 haT hb0 hbs' hσ hτ hc1 hcl
      hγinj hτinj hcross

/-- **The bigon principle, opposite chirality**: the bigon principle with the roles of the
vertical and horizontal fields exchanged. -/
theorem bigon_principleH₂ {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hW : NonnegWindingPrinciple₂) :
    ∀ (sv th : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) sv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q th (Set.Icc (-μ) (s + μ)) →
      th 0 = sv T → th s = sv 0 → False := by
  intro sv th T s μ hT hs hμ hσ hτ hc1 hc2
  obtain ⟨z₀, hz₀, hz₀ne⟩ := hq0
  exact bigon_principle₂ hq.neg ⟨z₀, hz₀, neg_ne_zero.mpr hz₀ne⟩ hW sv th T s μ
    hT hs hμ hσ (isTrajOn_congr (fun w => (neg_neg (q w)).symm) hτ) hc1 hc2

end FinalFeedTwo

/-- **A trajectory segment as a path**: a curve continuous on a compact parameter
interval yields a path between its endpoint values whose range is the segment
image. -/
theorem traj_path {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Set.Icc a b)) :
    ∃ p : Path (γ a) (γ b), Set.range p = γ '' Set.Icc a b := by
  have hmaps : ∀ s : unitInterval, a + (s : ℝ) * (b - a) ∈ Set.Icc a b := by
    intro s
    have h1 := s.2.1
    have h2 := s.2.2
    constructor
    · nlinarith
    · nlinarith
  refine ⟨⟨⟨fun s => γ (a + (s : ℝ) * (b - a)), ?_⟩, ?_, ?_⟩, ?_⟩
  · refine hc.comp_continuous ?_ hmaps
    fun_prop
  · simp
  · simp only [Set.Icc.coe_one, one_mul]
    rw [show a + (b - a) = b from by ring]
  · ext w
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨a + (s : ℝ) * (b - a), hmaps s, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rcases eq_or_lt_of_le hab with heq | hlt
      · refine ⟨0, ?_⟩
        change γ (a + ((0 : unitInterval) : ℝ) * (b - a)) = γ u
        have huq : u = a := le_antisymm (by rw [heq]; exact hu.2) hu.1
        rw [huq]
        simp
      · refine ⟨⟨(u - a) / (b - a), ?_, ?_⟩, ?_⟩
        · apply div_nonneg (by linarith [hu.1]) (by linarith)
        · rw [div_le_one (by linarith)]
          linarith [hu.2]
        · change γ (a + (u - a) / (b - a) * (b - a)) = γ u
          rw [div_mul_cancel₀ _ (by linarith : b - a ≠ 0),
            show a + (u - a) = u from by ring]

/-- **Leaves through a common point coincide as sets**: two all-time transverse
trajectories sharing a plane point have equal ranges. -/
theorem leaf_range_eq {q : ℂ → ℂ} {γ₁ γ₂ : ℝ → ℂ}
    (h₁ : IsTrajOn (fun z => -q z) γ₁ Set.univ)
    (h₂ : IsTrajOn (fun z => -q z) γ₂ Set.univ)
    {u₁ u₂ : ℝ} (hshare : γ₁ u₁ = γ₂ u₂) :
    Set.range γ₁ = Set.range γ₂ := by
  set δ₂ : ℝ → ℂ := fun v => γ₂ (v + (u₂ - u₁)) with hδ₂def
  have hδ₂traj : IsTrajOn (fun z => -q z) δ₂ Set.univ := by
    have h3 := traj_shift (u₂ - u₁) h₂
    rwa [Set.preimage_univ] at h3
  have hδshare : γ₁ u₁ = δ₂ u₁ := by
    rw [hδ₂def]
    simp only
    rw [show u₁ + (u₂ - u₁) = u₂ from by ring]
    exact hshare
  have hδ₂range : Set.range δ₂ = Set.range γ₂ := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v + (u₂ - u₁), rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v - (u₂ - u₁), by rw [hδ₂def]; simp only; rw [sub_add_cancel]⟩
  have hagree_univ : ∀ (τ₁ τ₂ : ℝ → ℂ),
      IsTrajOn (fun z => -q z) τ₁ Set.univ →
      IsTrajOn (fun z => -q z) τ₂ Set.univ →
      (∀ᶠ v in 𝓝 u₁, τ₁ v = τ₂ v) → ∀ v, τ₁ v = τ₂ v := by
    intro τ₁ τ₂ k₁ k₂ kgerm v
    set Rr : ℝ := |v - u₁| + 1 with hRdef
    have habs : |v - u₁| < Rr := by rw [hRdef]; linarith [abs_nonneg (v - u₁)]
    have hvmem := abs_lt.mp habs
    have hu₁mem : u₁ ∈ Set.Ioo (u₁ - Rr) (u₁ + Rr) :=
      ⟨by linarith [abs_nonneg (v - u₁)], by linarith [abs_nonneg (v - u₁)]⟩
    refine traj_agree_of_germ (traj_mono k₁ (Set.subset_univ _))
      (traj_mono k₂ (Set.subset_univ _)) hu₁mem hu₁mem kgerm v ?_ ?_
    · rw [max_self]
      linarith [hvmem.1]
    · rw [min_self]
      linarith [hvmem.2]
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev₁⟩ :=
    h₁.chart u₁ (Set.mem_univ u₁)
  rw [nhdsWithin_univ] at hev₁
  have hδU : δ₂ u₁ ∈ U := by rw [← hδshare]; exact hpU
  obtain ⟨ε, hε, hev₂⟩ := traj_ambient_local hUo hΦd hΦsq hδ₂traj
    (Set.subset_univ (Set.Icc (u₁ - 1) (u₁ + 1)))
    (⟨by linarith, by linarith⟩ : u₁ ∈ Set.Icc (u₁ - 1) (u₁ + 1)) hδU
  have hfilter₂ : nhdsWithin u₁ (Set.Icc (u₁ - 1) (u₁ + 1)) = 𝓝 u₁ :=
    nhdsWithin_eq_nhds.mpr (Icc_mem_nhds (by linarith) (by linarith))
  rw [hfilter₂] at hev₂
  have hδUev : ∀ᶠ v in 𝓝 u₁, δ₂ v ∈ U :=
    (hδ₂traj.cont.continuousAt (by simp : Set.univ ∈ 𝓝 u₁)).eventually_mem
      (hUo.mem_nhds hδU)
  rcases hε with hε1 | hε1
  · have hgerm : ∀ᶠ v in 𝓝 u₁, γ₁ v = δ₂ v := by
      filter_upwards [hev₁, hev₂, hδUev] with v h1v h2v hUv
      refine hΦinj h1v.1 hUv ?_
      rw [h1v.2, h2v, hε1, hδshare]
      push_cast
      ring
    have hall := hagree_univ γ₁ δ₂ h₁ hδ₂traj hgerm
    rw [show γ₁ = δ₂ from funext hall]
    exact hδ₂range
  · have hρtraj : IsTrajOn (fun z => -q z) (fun v => γ₁ (2 * u₁ - v))
        Set.univ := by
      have hsh := traj_shift (-(2 * u₁)) (traj_reverse h₁)
      rw [Set.preimage_univ, Set.preimage_univ] at hsh
      have hfun : (fun v : ℝ => (fun x : ℝ => γ₁ (-x)) (v + -(2 * u₁)))
          = fun v => γ₁ (2 * u₁ - v) := by
        funext v
        change γ₁ (-(v + -(2 * u₁))) = γ₁ (2 * u₁ - v)
        congr 1
        ring
      rwa [hfun] at hsh
    have hmap : Filter.Tendsto (fun v : ℝ => 2 * u₁ - v) (𝓝 u₁) (𝓝 u₁) := by
      have hc : Continuous fun v : ℝ => 2 * u₁ - v := by fun_prop
      have h5 := hc.tendsto u₁
      rwa [show 2 * u₁ - u₁ = u₁ from by ring] at h5
    have hgerm : ∀ᶠ v in 𝓝 u₁, δ₂ v = (fun v => γ₁ (2 * u₁ - v)) v := by
      filter_upwards [hmap.eventually hev₁, hev₂, hδUev] with v h1v h2v hUv
      refine (hΦinj h1v.1 hUv ?_).symm
      rw [h1v.2, h2v, hε1, hδshare]
      push_cast
      ring
    have hall := hagree_univ δ₂ (fun v => γ₁ (2 * u₁ - v)) hδ₂traj hρtraj hgerm
    rw [← hδ₂range, show δ₂ = fun v => γ₁ (2 * u₁ - v) from funext hall]
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨2 * u₁ - v, ?_⟩
      change γ₁ (2 * u₁ - (2 * u₁ - v)) = γ₁ v
      rw [show 2 * u₁ - (2 * u₁ - v) = v from by ring]
    · rintro ⟨v, rfl⟩
      change γ₁ (2 * u₁ - v) ∈ Set.range γ₁
      exact ⟨2 * u₁ - v, rfl⟩

/-- **Distinct-height leaves are disjoint**: two all-time transverse leaves visiting
the inner ball of a margined chart at distinct heights never meet. -/
theorem leaf_disjoint_of_heights {q Ψ : ℂ → ℂ} {W : Set ℂ} (hWo : IsOpen W)
    (hWd : DifferentiableOn ℂ Ψ W) (hWinj : Set.InjOn Ψ W)
    (hWH : W ⊆ {z : ℂ | 0 < z.im}) (hWne : ∀ w ∈ W, q w ≠ 0)
    (hWsq : ∀ x ∈ W, deriv Ψ x ^ 2 = -(-q x))
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψ '' W)
    {σ₁ σ₂ : ℝ → ℂ}
    (hσ₁ : IsTrajOn (fun z => -q z) σ₁ Set.univ)
    (hσ₂ : IsTrajOn (fun z => -q z) σ₂ Set.univ)
    {v₁ v₂ : ℝ} (h₁W : σ₁ v₁ ∈ W) (h₂W : σ₂ v₂ ∈ W)
    (h₁b : Ψ (σ₁ v₁) ∈ Metric.ball c₀ R) (h₂b : Ψ (σ₂ v₂) ∈ Metric.ball c₀ R)
    (hne : (Ψ (σ₁ v₁)).im ≠ (Ψ (σ₂ v₂)).im) :
    ∀ v w : ℝ, σ₁ v ≠ σ₂ w := by
  intro v w hEq
  have hrange := leaf_range_eq hσ₁ hσ₂ hEq
  have h2mem : σ₂ v₂ ∈ Set.range σ₁ := by
    rw [hrange]
    exact Set.mem_range_self v₂
  obtain ⟨v₂', hv₂'⟩ := h2mem
  have h₂W' : σ₁ v₂' ∈ W := by rw [hv₂']; exact h₂W
  have h₂b' : Ψ (σ₁ v₂') ∈ Metric.ball c₀ R := by rw [hv₂']; exact h₂b
  have hvis := leaf_visit_height hWo hWd hWinj hWH hWne hWsq hbigon hR hmarg
    hσ₁ h₁W h₂W' h₁b h₂b'
  rw [hv₂'] at hvis
  exact hne hvis

/-- **Single crossing of a vertical segment**: an all-time transverse leaf meets a
margined vertical trajectory segment at most once. -/
theorem arc_cross_once {q : ℂ → ℂ}
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {A : ℝ → ℂ} {L μ : ℝ} (hμ : 0 < μ)
    (hA : IsTrajOn q A (Set.Icc (-μ) (L + μ)))
    {σ : ℝ → ℂ} (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    {a₁ a₂ v₁ v₂ : ℝ} (ha₁ : a₁ ∈ Set.Icc 0 L) (ha₂ : a₂ ∈ Set.Icc 0 L)
    (h₁ : σ v₁ = A a₁) (h₂ : σ v₂ = A a₂) :
    a₁ = a₂ ∧ v₁ = v₂ := by
  have key : ∀ al ar ul ur : ℝ, al ∈ Set.Icc 0 L → ar ∈ Set.Icc 0 L →
      al < ar → σ ul = A al → σ ur = A ar → False := by
    intro al ar ul ur hal har halr hl hr
    set T' : ℝ := ar - al with hT'def
    have hT' : 0 < T' := by rw [hT'def]; linarith
    have hσv : IsTrajOn q (fun w => A (w + al)) (Set.Icc (-μ) (T' + μ)) := by
      refine traj_mono (traj_shift al hA) ?_
      intro w hw
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor
      · linarith [hw.1, hal.1]
      · have := hw.2
        rw [hT'def] at this
        linarith [har.2]
    rcases lt_trichotomy ur ul with hu | hu | hu
    · refine hbigon (fun w => A (w + al)) (fun w => σ (w + ur)) T' (ul - ur) μ
        hT' (by linarith) hμ hσv ?_ ?_ ?_
      · refine traj_mono ?_ (Set.subset_univ _)
        have h3 := traj_shift ur hσ
        rwa [Set.preimage_univ] at h3
      · change σ (0 + ur) = A (T' + al)
        rw [zero_add, hT'def, sub_add_cancel]
        exact hr
      · change σ (ul - ur + ur) = A (0 + al)
        rw [sub_add_cancel, zero_add]
        exact hl
    · have hAeq : A ar = A al := by
        rw [← hr, hu, hl]
      refine hbigon (fun w => A (w + al)) (fun w => σ (w + ul)) T' 0 μ
        hT' le_rfl hμ hσv ?_ ?_ ?_
      · refine traj_mono ?_ (Set.subset_univ _)
        have h3 := traj_shift ul hσ
        rwa [Set.preimage_univ] at h3
      · change σ (0 + ul) = A (T' + al)
        rw [zero_add, hT'def, sub_add_cancel, hl, ← hAeq]
      · change σ (0 + ul) = A (0 + al)
        rw [zero_add, zero_add]
        exact hl
    · refine hbigonH (fun w => σ (w + ul)) (fun w => A (ar - w)) (ur - ul)
        (ar - al) μ (by linarith) (by linarith) hμ ?_ ?_ ?_ ?_
      · refine traj_mono ?_ (Set.subset_univ _)
        have h3 := traj_shift ul hσ
        rwa [Set.preimage_univ] at h3
      · have h4 := traj_shift (-ar) (traj_reverse hA)
        have hfun : (fun w : ℝ => (fun x : ℝ => A (-x)) (w + -ar))
            = fun w => A (ar - w) := by
          funext w
          change A (-(w + -ar)) = A (ar - w)
          congr 1
          ring
        rw [hfun] at h4
        refine traj_mono h4 ?_
        intro w hw
        simp only [Set.mem_preimage, Set.mem_Icc] at hw ⊢
        constructor
        · linarith [hw.2, hal.1]
        · linarith [hw.1, har.2]
      · change A (ar - 0) = σ (ur - ul + ul)
        rw [sub_zero, sub_add_cancel]
        exact hr.symm
      · change A (ar - (ar - al)) = σ (0 + ul)
        rw [show ar - (ar - al) = al from by ring, zero_add]
        exact hl.symm
  have haa : a₁ = a₂ := by
    rcases lt_trichotomy a₁ a₂ with h | h | h
    · exact absurd (key a₁ a₂ v₁ v₂ ha₁ ha₂ h h₁ h₂) not_false
    · exact h
    · exact absurd (key a₂ a₁ v₂ v₁ ha₂ ha₁ h h₂ h₁) not_false
  refine ⟨haa, ?_⟩
  by_contra hvv
  rcases lt_or_gt_of_ne hvv with hv | hv
  · refine hbigonH (fun w => σ (w + v₁)) (fun w => A (w + a₁)) (v₂ - v₁) 0 μ
      (by linarith) le_rfl hμ ?_ ?_ ?_ ?_
    · refine traj_mono ?_ (Set.subset_univ _)
      have h3 := traj_shift v₁ hσ
      rwa [Set.preimage_univ] at h3
    · refine traj_mono (traj_shift a₁ hA) ?_
      intro w hw
      simp only [Set.mem_preimage, Set.mem_Icc] at hw ⊢
      constructor
      · linarith [hw.1, ha₁.1]
      · linarith [hw.2, ha₁.2]
    · change A (0 + a₁) = σ (v₂ - v₁ + v₁)
      rw [zero_add, sub_add_cancel, h₂, haa]
    · change A (0 + a₁) = σ (0 + v₁)
      rw [zero_add, zero_add]
      exact h₁.symm
  · refine hbigonH (fun w => σ (w + v₂)) (fun w => A (w + a₁)) (v₁ - v₂) 0 μ
      (by linarith) le_rfl hμ ?_ ?_ ?_ ?_
    · refine traj_mono ?_ (Set.subset_univ _)
      have h3 := traj_shift v₂ hσ
      rwa [Set.preimage_univ] at h3
    · refine traj_mono (traj_shift a₁ hA) ?_
      intro w hw
      simp only [Set.mem_preimage, Set.mem_Icc] at hw ⊢
      constructor
      · linarith [hw.1, ha₁.1]
      · linarith [hw.2, ha₁.2]
    · change A (0 + a₁) = σ (v₁ - v₂ + v₂)
      rw [zero_add, sub_add_cancel]
      exact h₁.symm
    · change A (0 + a₁) = σ (0 + v₂)
      rw [zero_add, zero_add, h₂, haa]
  -- both orientations of the repeated parameter close a loop against the seed

/-- **Evaluation of the four-sided loop**: the concatenated closed loop agrees with
the last side on the upper parameter half, and its lower half lies in the union of
the first three sides. -/
theorem quad_eval {z₀ z₁ z₂ z₃ : ℂ} (p₁ : Path z₀ z₁) (p₂ : Path z₁ z₂)
    (p₃ : Path z₂ z₃) (p₄ : Path z₃ z₀) :
    ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧
      Set.range γ = Set.range p₁ ∪ Set.range p₂ ∪ Set.range p₃ ∪ Set.range p₄ ∧
      (∀ s : unitInterval, (s : ℝ) ≤ 1 / 2 →
        γ s ∈ Set.range p₁ ∪ Set.range p₂ ∪ Set.range p₃) ∧
      ∀ (s : unitInterval) (hs : 1 / 2 < (s : ℝ)),
        γ s = p₄ ⟨2 * (s : ℝ) - 1, by
          constructor
          · linarith
          · linarith [s.2.2]⟩ := by
  set P : Path z₀ z₀ := ((p₁.trans p₂).trans p₃).trans p₄ with hPdef
  refine ⟨P.toContinuousMap, ?_, ?_, ?_, ?_⟩
  · change P 0 = P 1
    rw [P.source, P.target]
  · change Set.range P = _
    rw [hPdef, Path.trans_range, Path.trans_range, Path.trans_range]
  · intro s hs
    change P s ∈ _
    rw [hPdef, Path.trans_apply, dif_pos hs,
      show Set.range p₁ ∪ Set.range p₂ ∪ Set.range p₃
          = Set.range ((p₁.trans p₂).trans p₃) from by
        rw [Path.trans_range, Path.trans_range]]
    exact Set.mem_range_self _
  · intro s hs
    change P s = _
    rw [hPdef, Path.trans_apply, dif_neg (not_le.mpr hs)]

section OfflineZero

open unitInterval

/-- **Off-line winding vanishing**: a closed curve avoiding the horizontal line through
a point has winding number zero about it. -/
theorem winding_offline_zero {γ : C(I, ℂ)} {ζ : ℂ}
    (hcl : γ 0 = γ 1) (hoff : ∀ t : I, (γ t).im ≠ ζ.im) :
    windingNumber γ ζ = 0 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hne : ∀ t : I, γ t ≠ ζ := fun t h => hoff t (by rw [h])
  have hsne : ∀ t : I, shiftedCurve γ ζ t ≠ 0 := by
    intro t
    have h1 : shiftedCurve γ ζ t = γ t - ζ := by simp [shiftedCurve]
    rw [h1]
    exact sub_ne_zero.mpr (hne t)
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ ζ) hsne
  have hspec := windingNumber_spec hcl hne hL
  have hsin : ∀ t : I, Real.sin ((L t).im) ≠ 0 := by
    intro t hs
    have h1 : Real.exp ((L t).re) * Real.sin ((L t).im)
        = (shiftedCurve γ ζ t).im := by
      rw [← Complex.exp_im, hL t]
    have h2 : (shiftedCurve γ ζ t).im = (γ t).im - ζ.im := by simp [shiftedCurve]
    rw [hs, mul_zero, h2] at h1
    exact hoff t (by linarith)
  by_contra hw
  have him : (L 1).im - (L 0).im = 2 * Real.pi * ((windingNumber γ ζ : ℤ) : ℝ) := by
    have h := congrArg Complex.im hspec
    simpa using h
  have hθc : Continuous fun t : I => (L t).im := by fun_prop
  set n : ℤ := windingNumber γ ζ with hndef
  have hn : n ≠ 0 := hw
  have hkey : ∃ t : I, ∃ k : ℤ, (L t).im = k * Real.pi := by
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · -- θ 1 ≤ θ 0 − 2π: scan downward from θ 0
      have hbound : (L 1).im ≤ (L 0).im - 2 * Real.pi := by
        have h1 : ((n : ℝ)) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
        nlinarith [him]
      set k : ℤ := ⌈(L 1).im / Real.pi⌉ with hkdef
      have hk1 : (L 1).im ≤ (k : ℝ) * Real.pi := by
        have h := Int.le_ceil ((L 1).im / Real.pi)
        rw [← hkdef] at h
        rw [div_le_iff₀ hπ] at h
        linarith
      have hk2 : (k : ℝ) * Real.pi ≤ (L 0).im := by
        have h := Int.ceil_lt_add_one ((L 1).im / Real.pi)
        rw [← hkdef] at h
        have h2 : (k : ℝ) < (L 1).im / Real.pi + 1 := h
        have h3 : (k : ℝ) * Real.pi < (L 1).im + Real.pi := by
          rw [div_add' _ _ _ hπ.ne'] at h2
          rw [lt_div_iff₀ hπ] at h2
          linarith
        linarith [hbound]
      have hmem : (k : ℝ) * Real.pi ∈ Set.Icc ((L 1).im) ((L 0).im) := ⟨hk1, hk2⟩
      obtain ⟨t, ht⟩ := intermediate_value_univ (1 : I) (0 : I) hθc hmem
      exact ⟨t, k, by exact ht⟩
    · -- θ 0 + 2π ≤ θ 1: scan upward from θ 0
      have hbound : (L 0).im + 2 * Real.pi ≤ (L 1).im := by
        have h1 : (1:ℝ) ≤ ((n : ℝ)) := by exact_mod_cast hpos
        nlinarith [him]
      set k : ℤ := ⌈(L 0).im / Real.pi⌉ with hkdef
      have hk1 : (L 0).im ≤ (k : ℝ) * Real.pi := by
        have h := Int.le_ceil ((L 0).im / Real.pi)
        rw [← hkdef] at h
        rw [div_le_iff₀ hπ] at h
        linarith
      have hk2 : (k : ℝ) * Real.pi ≤ (L 1).im := by
        have h := Int.ceil_lt_add_one ((L 0).im / Real.pi)
        rw [← hkdef] at h
        have h2 : (k : ℝ) < (L 0).im / Real.pi + 1 := h
        have h3 : (k : ℝ) * Real.pi < (L 0).im + Real.pi := by
          rw [div_add' _ _ _ hπ.ne'] at h2
          rw [lt_div_iff₀ hπ] at h2
          linarith
        linarith [hbound]
      have hmem : (k : ℝ) * Real.pi ∈ Set.Icc ((L 0).im) ((L 1).im) := ⟨hk1, hk2⟩
      obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) (1 : I) hθc hmem
      exact ⟨t, k, by exact ht⟩
  obtain ⟨t, k, htk⟩ := hkey
  refine hsin t ?_
  rw [htk]
  exact Real.sin_int_mul_pi k

end OfflineZero

set_option maxHeartbeats 400000 in
-- Heartbeats: the deep local-definition tower needs an enlarged elaboration budget.
/-- **The winding jump across a transversal crossing**: for a closed loop developing
vertically through the chart value of a crossing point on a parameter window, staying
clear of the point off the window, the winding numbers about the two nearby
horizontal probes of the crossing curve differ. -/
theorem winding_jump {Ψ : ℂ → ℂ}
    {σ : ℝ → ℂ} (hσc : Continuous σ) {vc : ℝ}
    {dΨ : ℂ} (hdΨ : dΨ ≠ 0) {δb : ℝ} (hδb : 0 < δb)
    (hdd : ∀ w z : ℂ, w ∈ Metric.ball (σ vc) δb → z ∈ Metric.ball (σ vc) δb →
      w ≠ z → ‖(Ψ w - Ψ z) / (w - z) - dΨ‖ < ‖dΨ‖ / 4)
    {γ : C(unitInterval, ℂ)} (hcl : γ 0 = γ 1)
    {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₁₂ : b₁ < b₂) (hb₂ : b₂ ≤ 1)
    {c₁ c₂ : ℝ}
    (hwin : ∀ s : unitInterval, b₁ ≤ (s : ℝ) → (s : ℝ) ≤ b₂ →
      γ s ∈ Metric.ball (σ vc) δb ∧
      Ψ (γ s) = Ψ (σ vc) + Complex.I * ((c₁ + c₂ * (s : ℝ) : ℝ) : ℂ))
    (hyy : (c₁ + c₂ * b₁) * (c₁ + c₂ * b₂) < 0)
    {h ε₂ : ℝ} (hh : 0 < h) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hσdev : ∀ u : ℝ, |u| ≤ h → σ (vc + u) ∈ Metric.ball (σ vc) δb ∧
      Ψ (σ (vc + u)) = Ψ (σ vc) + (ε₂ : ℂ) * (u : ℂ))
    (hmiss : ∀ (s : unitInterval) (u : ℝ), u ≠ 0 → γ s ≠ σ (vc + u))
    {d₀ : ℝ} (hd₀ : 0 < d₀)
    (hoff : ∀ s : unitInterval, ((s : ℝ) ≤ b₁ ∨ b₂ ≤ (s : ℝ)) →
      γ s ∉ Metric.ball (σ vc) d₀) :
    ∃ η : ℝ, 0 < η ∧
      windingNumber γ (σ (vc + η)) ≠ windingNumber γ (σ (vc - η)) := by
  set x : ℂ := σ vc with hxdef
  set y₁ : ℝ := c₁ + c₂ * b₁ with hy₁def
  set y₂ : ℝ := c₁ + c₂ * b₂ with hy₂def
  have hy₁ne : y₁ ≠ 0 := by
    intro h0
    rw [h0] at hyy
    simp at hyy
  have hy₂ne : y₂ ≠ 0 := by
    intro h0
    rw [h0] at hyy
    simp at hyy
  set cc : ℝ := -ε₂ with hccdef
  have hccpm : cc = 1 ∨ cc = -1 := by
    rcases hε₂ with h' | h'
    · exact Or.inr (by rw [hccdef, h'])
    · exact Or.inl (by rw [hccdef, h']; norm_num)
  have hccne : cc ≠ 0 := by rcases hccpm with h' | h' <;> rw [h'] <;> norm_num
  have hε₂cc : ε₂ = -cc := by rw [hccdef]; ring
  -- the window endpoints as unit-interval points
  have hb₁01 : b₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨hb₁, by linarith⟩
  have hb₂01 : b₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, hb₂⟩
  set s₁ : unitInterval := ⟨b₁, hb₁01⟩ with hs₁def
  set s₂ : unitInterval := ⟨b₂, hb₂01⟩ with hs₂def
  set g₁ : ℂ := γ s₁ with hg₁def
  set g₂ : ℂ := γ s₂ with hg₂def
  have hg₁x : g₁ ∉ Metric.ball x d₀ := hoff s₁ (Or.inl le_rfl)
  have hg₂x : g₂ ∉ Metric.ball x d₀ := hoff s₂ (Or.inr le_rfl)
  have hg₁P : g₁ ≠ x := fun hE => hg₁x (hE ▸ Metric.mem_ball_self hd₀)
  have hg₂P : g₂ ≠ x := fun hE => hg₂x (hE ▸ Metric.mem_ball_self hd₀)
  -- probes approach the crossing point
  have hτcont : Continuous fun u : ℝ => σ (vc + u) := by fun_prop
  obtain ⟨η₁, hη₁, hτcball⟩ := Metric.eventually_nhds_iff.mp
    ((hτcont.tendsto 0).eventually_mem
      (Metric.ball_mem_nhds _ (lt_min hδb hd₀)) |>.mono (by
        intro u hu
        simpa using hu))
  have hτball : ∀ u : ℝ, |u| < η₁ → σ (vc + u) ∈ Metric.ball x (min δb d₀) := by
    intro u hu
    have h2 := hτcball (show dist u 0 < η₁ by rwa [Real.dist_eq, sub_zero])
    simpa [hxdef] using h2
  set Mv : ℝ → ℝ → ℂ := fun ξ t =>
    ((ξ : ℂ) - ((cc * t : ℝ) : ℂ) * Complex.I)
      / ((ξ : ℂ) + ((cc * t : ℝ) : ℂ) * Complex.I) with hMvdef
  set E : ℝ → ℂ := fun t =>
    (-(2 * ((Complex.arg (((y₂ : ℝ) : ℂ)
          + ((cc * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I
      + (2 * ((Complex.arg (((y₁ : ℝ) : ℂ)
          + ((cc * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I)
    + (Complex.log (((g₂ - σ (vc + t)) / (g₂ - σ (vc - t))) / Mv y₂ t)
        - Complex.log (((g₁ - σ (vc + t)) / (g₁ - σ (vc - t))) / Mv y₁ t))
    + (Complex.log ((g₁ - σ (vc + t)) / (g₁ - σ (vc - t)))
        - Complex.log ((g₂ - σ (vc + t)) / (g₂ - σ (vc - t)))) with hEdef
  have hsub : ∀ t : ℝ, vc - t = vc + -t := fun t => by ring
  have hkey : ∀ η : ℝ, 0 < η → η ≤ h → η < η₁ →
      2 * (Real.pi : ℂ) * Complex.I *
        ((windingNumber γ (σ (vc + η)) : ℂ)
          - (windingNumber γ (σ (vc - η)) : ℂ)) = E η := by
    intro η hη hηa hηb
    have hηne : η ≠ 0 := hη.ne'
    have hprp := hσdev η (by rw [abs_of_pos hη]; exact hηa)
    have hprm := hσdev (-η) (by rw [abs_neg, abs_of_pos hη]; exact hηa)
    have hzpF : Ψ (σ (vc + η)) = Ψ x + (ε₂ : ℂ) * (η : ℂ) := hprp.2
    have hzmF : Ψ (σ (vc - η)) = Ψ x + (ε₂ : ℂ) * ((-η : ℝ) : ℂ) := by
      rw [hsub η]
      exact hprm.2
    have hzpb : σ (vc + η) ∈ Metric.ball x δb :=
      Metric.ball_subset_ball (min_le_left _ _) (hτball η (by rwa [abs_of_pos hη]))
    have hzmb : σ (vc - η) ∈ Metric.ball x δb := by
      rw [hsub η]
      exact Metric.ball_subset_ball (min_le_left _ _)
        (hτball (-η) (by rwa [abs_neg, abs_of_pos hη]))
    have hsegb : segment ℝ (σ (vc - η)) (σ (vc + η)) ⊆ Metric.ball x d₀ := by
      refine (convex_ball x d₀).segment_subset ?_ ?_
      · rw [hsub η]
        exact Metric.ball_subset_ball (min_le_right _ _)
          (hτball (-η) (by rwa [abs_neg, abs_of_pos hη]))
      · exact Metric.ball_subset_ball (min_le_right _ _)
          (hτball η (by rwa [abs_of_pos hη]))
    have hpp : ∀ t : unitInterval, γ t ≠ σ (vc + η) := fun t => hmiss t η hηne
    have hmm : ∀ t : unitInterval, γ t ≠ σ (vc - η) := fun t => by
      rw [hsub η]
      exact hmiss t (-η) (neg_ne_zero.mpr hηne)
    have hppz : ∀ t : unitInterval, γ t - σ (vc + η) ≠ 0 :=
      fun t => sub_ne_zero.mpr (hpp t)
    have hmmz : ∀ t : unitInterval, γ t - σ (vc - η) ≠ 0 :=
      fun t => sub_ne_zero.mpr (hmm t)
    set r : C(unitInterval, ℂ) :=
      ⟨fun t => (γ t - σ (vc + η)) / (γ t - σ (vc - η)),
        ((map_continuous γ).sub continuous_const).div
          ((map_continuous γ).sub continuous_const) fun t => hmmz t⟩ with hrdef
    have hr : ∀ t : unitInterval,
        r t = (γ t - σ (vc + η)) / (γ t - σ (vc - η)) := fun t => rfl
    have hwr := winding_sub_eq_ratio hcl hpp hmm r hr
    have hrne : ∀ t : unitInterval, r t ≠ 0 := fun t => div_ne_zero (hppz t) (hmmz t)
    have hshiftne : ∀ t : unitInterval, shiftedCurve r 0 t ≠ 0 := by
      intro t
      have h2 : shiftedCurve r 0 t = r t := by simp [shiftedCurve]
      rw [h2]
      exact hrne t
    obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve r 0) hshiftne
    have hrcl : r 0 = r 1 := by rw [hr 0, hr 1, hcl]
    have hspec := windingNumber_spec hrcl hrne hL
    set Lr : ℝ → ℂ := fun u => L (Set.projIcc 0 1 zero_le_one u) with hLrdef
    set rr : ℝ → ℂ := fun u => r (Set.projIcc 0 1 zero_le_one u) with hrrdef
    have hLrlift : ∀ u : ℝ, Complex.exp (Lr u) = rr u := by
      intro u
      have h2 := hL (Set.projIcc 0 1 zero_le_one u)
      rw [hLrdef]
      simp only
      rw [h2]
      rw [hrrdef]
      simp [shiftedCurve]
    have hLrc : Continuous Lr := (map_continuous L).comp continuous_projIcc
    have hrrc : Continuous rr := (map_continuous r).comp continuous_projIcc
    have hproj : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 →
        ((Set.projIcc 0 1 zero_le_one u : unitInterval) : ℝ) = u := by
      intro u hu
      rw [Set.projIcc_of_mem zero_le_one hu]
    have hpr0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) :=
      Subtype.ext (hproj 0 ⟨le_refl 0, zero_le_one⟩)
    have hpr1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) :=
      Subtype.ext (hproj 1 ⟨zero_le_one, le_refl 1⟩)
    have hprb₁ : Set.projIcc (0 : ℝ) 1 zero_le_one b₁ = s₁ :=
      Subtype.ext (hproj b₁ hb₁01)
    have hprb₂ : Set.projIcc (0 : ℝ) 1 zero_le_one b₂ = s₂ :=
      Subtype.ext (hproj b₂ hb₂01)
    have hrreq : ∀ u : ℝ, rr u
        = (γ (Set.projIcc 0 1 zero_le_one u) - σ (vc + η))
          / (γ (Set.projIcc 0 1 zero_le_one u) - σ (vc - η)) := by
      intro u
      rw [hrrdef]
      simp only
      rw [hr]
    have hspecr : Lr 1 - Lr 0
        = 2 * (Real.pi : ℂ) * Complex.I * (windingNumber r 0 : ℂ) := by
      rw [hLrdef]
      simp only
      rw [hpr0, hpr1]
      exact hspec
    have hslitOff : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → (u ≤ b₁ ∨ b₂ ≤ u) →
        rr u ∈ Complex.slitPlane := by
      intro u hu01 hcase
      have htc : ((Set.projIcc 0 1 zero_le_one u : unitInterval) : ℝ) = u :=
        hproj u hu01
      have hoffm := hoff (Set.projIcc 0 1 zero_le_one u) (by rw [htc]; exact hcase)
      have hseg : γ (Set.projIcc 0 1 zero_le_one u)
          ∉ segment ℝ (σ (vc - η)) (σ (vc + η)) :=
        fun hsg => hoffm (hsegb hsg)
      have h3 := ratio_slitPlane (w := γ (Set.projIcc 0 1 zero_le_one u))
        (zp := σ (vc + η)) (zm := σ (vc - η)) hseg
      rw [hrreq u]
      exact h3
    have hpiece₁ : Lr b₁ - Lr 0 = Complex.log (rr b₁) - Complex.log (rr 0) :=
      loglift_increment_slit hb₁ hLrc.continuousOn hrrc.continuousOn
        (fun u _ => hLrlift u)
        (fun u hu => hslitOff u ⟨hu.1, le_trans hu.2 (by linarith)⟩ (Or.inl hu.2))
    have hpiece₂ : Lr 1 - Lr b₂ = Complex.log (rr 1) - Complex.log (rr b₂) :=
      loglift_increment_slit hb₂ hLrc.continuousOn hrrc.continuousOn
        (fun u _ => hLrlift u)
        (fun u hu => hslitOff u ⟨le_trans (by linarith) hu.1, hu.2⟩ (Or.inr hu.1))
    -- the crossing window
    have hccη : cc * η ≠ 0 := mul_ne_zero hccne hηne
    have hε₂η : ε₂ * η ≠ 0 :=
      mul_ne_zero (by rcases hε₂ with h' | h' <;> rw [h'] <;> norm_num) hηne
    have hwin' : ∀ u : ℝ, u ∈ Set.Icc b₁ b₂ →
        γ (Set.projIcc 0 1 zero_le_one u) ∈ Metric.ball x δb ∧
        Ψ (γ (Set.projIcc 0 1 zero_le_one u))
          = Ψ x + Complex.I * ((c₁ + c₂ * u : ℝ) : ℂ) := by
      intro u hu
      have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hb₁ hu.1, le_trans hu.2 hb₂⟩
      have htc := hproj u hu01
      have h2 := hwin (Set.projIcc 0 1 zero_le_one u) (by rw [htc]; exact hu.1)
        (by rw [htc]; exact hu.2)
      rw [htc] at h2
      exact h2
    have hnum' : ∀ u : ℝ, u ∈ Set.Icc b₁ b₂ →
        Ψ (γ (Set.projIcc 0 1 zero_le_one u)) - Ψ (σ (vc + η))
          = Complex.I * ((c₁ + c₂ * u : ℝ) : ℂ) - ((ε₂ * η : ℝ) : ℂ) := by
      intro u hu
      rw [(hwin' u hu).2, hzpF]
      push_cast
      ring
    have hden' : ∀ u : ℝ, u ∈ Set.Icc b₁ b₂ →
        Ψ (γ (Set.projIcc 0 1 zero_le_one u)) - Ψ (σ (vc - η))
          = Complex.I * ((c₁ + c₂ * u : ℝ) : ℂ) + ((ε₂ * η : ℝ) : ℂ) := by
      intro u hu
      rw [(hwin' u hu).2, hzmF]
      push_cast
      ring
    have hnumne : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) - ((cc * η : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro ξ h0
      have h2 := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.zero_im, mul_zero,
        mul_one, zero_sub, add_zero] at h2
      exact hccη (by linarith)
    have hdenne : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) + ((cc * η : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro ξ h0
      have h2 := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.zero_im, mul_zero,
        mul_one, zero_add, add_zero] at h2
      exact hccη (by linarith)
    have hInumne : ∀ ξ : ℝ, Complex.I * ((ξ : ℝ) : ℂ) - ((ε₂ * η : ℝ) : ℂ) ≠ 0 := by
      intro ξ h0
      have h2 := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, zero_mul, mul_zero,
        zero_sub, sub_zero] at h2
      exact hε₂η (by linarith)
    have hIdenne : ∀ ξ : ℝ, Complex.I * ((ξ : ℝ) : ℂ) + ((ε₂ * η : ℝ) : ℂ) ≠ 0 := by
      intro ξ h0
      have h2 := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, zero_mul, mul_zero] at h2
      exact hε₂η (by linarith)
    have hMvne : ∀ ξ : ℝ, Mv ξ η ≠ 0 := by
      intro ξ
      rw [hMvdef]
      simp only
      exact div_ne_zero (hnumne ξ) (hdenne ξ)
    have hMraw : ∀ ξ : ℝ, Mv ξ η
        = (Complex.I * ((ξ : ℝ) : ℂ) - ((ε₂ * η : ℝ) : ℂ))
          / (Complex.I * ((ξ : ℝ) : ℂ) + ((ε₂ * η : ℝ) : ℂ)) := by
      intro ξ
      rw [hMvdef]
      simp only
      rw [div_eq_div_iff (hdenne ξ) (hIdenne ξ)]
      rw [hε₂cc]
      push_cast
      linear_combination (-2 * (cc : ℂ) * (η : ℂ) * (ξ : ℂ)) * Complex.I_sq
    set Qf : ℝ → ℂ := fun u => rr u / Mv (c₁ + c₂ * u) η with hQfdef
    have hfact : ∀ u : ℝ, rr u = Mv (c₁ + c₂ * u) η * Qf u := by
      intro u
      rw [hQfdef]
      simp only
      rw [mul_comm, div_mul_cancel₀ _ (hMvne _)]
    have hQslit : ∀ u ∈ Set.Icc b₁ b₂, Qf u ∈ Complex.slitPlane := by
      intro u hu
      have hFnep : Ψ (γ (Set.projIcc 0 1 zero_le_one u)) - Ψ (σ (vc + η)) ≠ 0 := by
        rw [hnum' u hu]
        exact hInumne _
      have hFnem : Ψ (γ (Set.projIcc 0 1 zero_le_one u)) - Ψ (σ (vc - η)) ≠ 0 := by
        rw [hden' u hu]
        exact hIdenne _
      have hnep := hppz (Set.projIcc 0 1 zero_le_one u)
      have hnem := hmmz (Set.projIcc 0 1 zero_le_one u)
      have halg : Qf u = ((Ψ (γ (Set.projIcc 0 1 zero_le_one u)) - Ψ (σ (vc - η)))
            / (γ (Set.projIcc 0 1 zero_le_one u) - σ (vc - η)))
          / ((Ψ (γ (Set.projIcc 0 1 zero_le_one u)) - Ψ (σ (vc + η)))
            / (γ (Set.projIcc 0 1 zero_le_one u) - σ (vc + η))) := by
        rw [hQfdef]
        simp only
        rw [hrreq u, hMraw, ← hnum' u hu, ← hden' u hu]
        field_simp
      rw [halg]
      exact ratio_near_one hdΨ
        (hdd _ _ (hwin' u hu).1 hzmb (hmm _)) (hdd _ _ (hwin' u hu).1 hzpb (hpp _))
    set L₁ : ℝ → ℂ := fun u =>
      -(2 * ((Complex.arg (((c₁ + c₂ * u : ℝ) : ℂ)
          + ((cc * η : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I with hL₁def
    have hlift₁ : ∀ u ∈ Set.Icc b₁ b₂,
        Complex.exp (L₁ u) = Mv (c₁ + c₂ * u) η := by
      intro u _
      rw [hL₁def, hMvdef]
      simp only
      exact (conj_pair_exp hccη).symm
    have hL₁c : ContinuousOn L₁ (Set.Icc b₁ b₂) := by
      have hinner : Continuous fun u : ℝ =>
          ((c₁ + c₂ * u : ℝ) : ℂ) + ((cc * η : ℝ) : ℂ) * Complex.I := by
        fun_prop
      have hargc : ∀ u : ℝ, ContinuousAt (fun v : ℝ =>
          Complex.arg (((c₁ + c₂ * v : ℝ) : ℂ)
            + ((cc * η : ℝ) : ℂ) * Complex.I)) u := by
        intro u
        refine ContinuousAt.comp (Complex.continuousAt_arg ?_) hinner.continuousAt
        refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
          zero_add, add_zero]
        exact hccη
      rw [hL₁def]
      refine ContinuousOn.mul (ContinuousOn.neg ?_) continuousOn_const
      refine ContinuousOn.mul continuousOn_const ?_
      exact (Complex.continuous_ofReal.comp
        (continuous_iff_continuousAt.mpr hargc)).continuousOn
    have hMc : ContinuousOn (fun u : ℝ => Mv (c₁ + c₂ * u) η) (Set.Icc b₁ b₂) := by
      rw [hMvdef]
      simp only
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro u _
        exact hdenne _
    have hQfc : ContinuousOn Qf (Set.Icc b₁ b₂) := by
      rw [hQfdef]
      exact ContinuousOn.div hrrc.continuousOn hMc fun u _ => hMvne _
    have hlift₂ : ∀ u ∈ Set.Icc b₁ b₂,
        Complex.exp (Complex.log (Qf u)) = Qf u :=
      fun u hu => Complex.exp_log (Complex.slitPlane_ne_zero (hQslit u hu))
    have hL₂c : ContinuousOn (fun u => Complex.log (Qf u)) (Set.Icc b₁ b₂) := by
      intro u hu
      exact (continuousAt_clog (hQslit u hu)).comp_continuousWithinAt (hQfc u hu)
    have hpiece₃ : Lr b₂ - Lr b₁
        = (L₁ b₂ - L₁ b₁) + (Complex.log (Qf b₂) - Complex.log (Qf b₁)) :=
      loglift_increment_mul hb₁₂.le hLrc.continuousOn hL₁c hL₂c
        (fun u hu => by rw [hLrlift u]; exact hfact u) hlift₁ hlift₂
    -- assembly
    have hZ : (windingNumber r 0 : ℂ)
        = (windingNumber γ (σ (vc + η)) : ℂ)
          - (windingNumber γ (σ (vc - η)) : ℂ) := by
      rw [← hwr]
      push_cast
      ring
    have htot : 2 * (Real.pi : ℂ) * Complex.I *
        ((windingNumber γ (σ (vc + η)) : ℂ)
          - (windingNumber γ (σ (vc - η)) : ℂ))
        = (Complex.log (rr 1) - Complex.log (rr b₂))
          + ((L₁ b₂ - L₁ b₁) + (Complex.log (Qf b₂) - Complex.log (Qf b₁)))
          + (Complex.log (rr b₁) - Complex.log (rr 0)) := by
      rw [← hZ, ← hspecr, ← hpiece₁, ← hpiece₂, ← hpiece₃]
      ring
    have hrr10 : rr 1 = rr 0 := by
      rw [hrreq 1, hrreq 0, hpr0, hpr1, hcl]
    have hrrb₁ : rr b₁ = (g₁ - σ (vc + η)) / (g₁ - σ (vc - η)) := by
      rw [hrreq b₁, hprb₁, ← hg₁def]
    have hrrb₂ : rr b₂ = (g₂ - σ (vc + η)) / (g₂ - σ (vc - η)) := by
      rw [hrreq b₂, hprb₂, ← hg₂def]
    have hL₁ends : L₁ b₂ - L₁ b₁
        = -(2 * ((Complex.arg (((y₂ : ℝ) : ℂ)
              + ((cc * η : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I
          + (2 * ((Complex.arg (((y₁ : ℝ) : ℂ)
              + ((cc * η : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I := by
      rw [hL₁def]
      simp only
      rw [hy₁def, hy₂def]
      ring
    have hQb₁ : Qf b₁ = ((g₁ - σ (vc + η)) / (g₁ - σ (vc - η))) / Mv y₁ η := by
      rw [hQfdef]
      simp only
      rw [hrrb₁, hy₁def]
    have hQb₂ : Qf b₂ = ((g₂ - σ (vc + η)) / (g₂ - σ (vc - η))) / Mv y₂ η := by
      rw [hQfdef]
      simp only
      rw [hrrb₂, hy₂def]
    rw [htot, hrr10, hEdef]
    simp only
    rw [hL₁ends, hQb₁, hQb₂, hrrb₁, hrrb₂]
    ring
  -- the limit of the increment expression
  have hcastl : Filter.Tendsto (fun t : ℝ => ((cc * t : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h1 : Continuous fun t : ℝ => ((cc * t : ℝ) : ℂ) := by fun_prop
    have h2 := (h1.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h2
  have hτpl : Filter.Tendsto (fun t : ℝ => σ (vc + t))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 x) := by
    have h1 : Continuous fun t : ℝ => σ (vc + t) := by fun_prop
    have h2 := (h1.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hxdef] using h2
  have hτml : Filter.Tendsto (fun t : ℝ => σ (vc - t))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 x) := by
    have h1 : Continuous fun t : ℝ => σ (vc - t) := by fun_prop
    have h2 := (h1.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hxdef] using h2
  have hRlim : ∀ g : ℂ, g ≠ x → Filter.Tendsto
      (fun t : ℝ => (g - σ (vc + t)) / (g - σ (vc - t)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    intro g hg
    have hgP : g - x ≠ 0 := sub_ne_zero.mpr hg
    have h4 := ((tendsto_const_nhds (x := g)).sub hτpl).div
      ((tendsto_const_nhds (x := g)).sub hτml) hgP
    rwa [div_self hgP] at h4
  have hMlim : ∀ ξ : ℝ, ξ ≠ 0 → Filter.Tendsto (fun t : ℝ => Mv ξ t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    intro ξ hξ
    have hξC : ((ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    rw [hMvdef]
    simp only
    have h4 := ((tendsto_const_nhds (x := ((ξ : ℝ) : ℂ))).sub
        (hcastl.mul_const Complex.I)).div
      ((tendsto_const_nhds (x := ((ξ : ℝ) : ℂ))).add
        (hcastl.mul_const Complex.I)) (by simpa using hξC)
    have h5 : ((ξ : ℝ) : ℂ) - 0 * Complex.I = ((ξ : ℝ) : ℂ) := by ring
    have h6 : ((ξ : ℝ) : ℂ) + 0 * Complex.I = ((ξ : ℝ) : ℂ) := by ring
    rw [h5, h6, div_self hξC] at h4
    exact h4
  have hlog1 : ContinuousAt Complex.log 1 :=
    continuousAt_clog (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simp : (0 : ℝ) < (1 : ℂ).re)))
  have hlogc : ∀ {f : ℝ → ℂ}, Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) →
      Filter.Tendsto (fun t => Complex.log (f t))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    intro f hf
    have h2 := hlog1.tendsto.comp hf
    rwa [Complex.log_one] at h2
  have hQlim : ∀ (g : ℂ), g ≠ x → ∀ ξ : ℝ, ξ ≠ 0 → Filter.Tendsto
      (fun t : ℝ => ((g - σ (vc + t)) / (g - σ (vc - t))) / Mv ξ t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    intro g hg ξ hξ
    have h2 := (hRlim g hg).div (hMlim ξ hξ) one_ne_zero
    rwa [div_one] at h2
  have hofr : ∀ {A : ℝ → ℝ} {v : ℝ},
      Filter.Tendsto A (nhdsWithin 0 (Set.Ioi 0)) (𝓝 v) →
      Filter.Tendsto (fun t => (2 * ((A t : ℝ) : ℂ)) * Complex.I)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((2 * ((v : ℝ) : ℂ)) * Complex.I)) := by
    intro A v hA
    have h2 : Filter.Tendsto (fun t => ((A t : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((v : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto v).comp hA
    exact (h2.const_mul 2).mul_const Complex.I
  have hofrn : ∀ {A : ℝ → ℝ} {v : ℝ},
      Filter.Tendsto A (nhdsWithin 0 (Set.Ioi 0)) (𝓝 v) →
      Filter.Tendsto (fun t => -(2 * ((A t : ℝ) : ℂ)) * Complex.I)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (-(2 * ((v : ℝ) : ℂ)) * Complex.I)) := by
    intro A v hA
    have h2 : Filter.Tendsto (fun t => ((A t : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((v : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto v).comp hA
    exact ((h2.const_mul 2).neg).mul_const Complex.I
  obtain ⟨ςv, hςv, hFlim⟩ : ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧
      Filter.Tendsto (fun t : ℝ =>
        -(2 * ((Complex.arg (((y₂ : ℝ) : ℂ)
              + ((cc * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I
          + (2 * ((Complex.arg (((y₁ : ℝ) : ℂ)
              + ((cc * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (((ς : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) := by
    rcases lt_or_gt_of_ne hy₁ne with hy₁s | hy₁s
    · have hy₂s : 0 < y₂ := by nlinarith
      have hA₁ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((y₁ : ℝ) : ℂ) + ((cc * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (cc * Real.pi)) := by
        refine (arg_limit_neg (δ := -y₁) (by linarith) hccpm).congr fun t => ?_
        congr 2
        push_cast
        ring
      have hA₂ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((y₂ : ℝ) : ℂ) + ((cc * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := arg_limit_pos hy₂s
      have h2 := (hofrn hA₂).add (hofr hA₁)
      have h3 : -(2 * ((0 : ℝ) : ℂ)) * Complex.I
            + (2 * ((cc * Real.pi : ℝ) : ℂ)) * Complex.I
          = ((cc : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      exact ⟨cc, hccpm, by rw [← h3]; exact h2⟩
    · have hy₂s : y₂ < 0 := by nlinarith
      have hA₁ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((y₁ : ℝ) : ℂ) + ((cc * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := arg_limit_pos hy₁s
      have hA₂ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((y₂ : ℝ) : ℂ) + ((cc * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (cc * Real.pi)) := by
        refine (arg_limit_neg (δ := -y₂) (by linarith) hccpm).congr fun t => ?_
        congr 2
        push_cast
        ring
      have h2 := (hofrn hA₂).add (hofr hA₁)
      have h3 : -(2 * ((cc * Real.pi : ℝ) : ℂ)) * Complex.I
            + (2 * ((0 : ℝ) : ℂ)) * Complex.I
          = ((-cc : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      refine ⟨-cc, ?_, by rw [← h3]; exact h2⟩
      rcases hccpm with h' | h'
      · exact Or.inr (by rw [h'])
      · exact Or.inl (by rw [h']; norm_num)
  have hGlim : Filter.Tendsto (fun t : ℝ =>
      Complex.log (((g₂ - σ (vc + t)) / (g₂ - σ (vc - t))) / Mv y₂ t)
        - Complex.log (((g₁ - σ (vc + t)) / (g₁ - σ (vc - t))) / Mv y₁ t))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h2 := (hlogc (hQlim g₂ hg₂P y₂ hy₂ne)).sub
      (hlogc (hQlim g₁ hg₁P y₁ hy₁ne))
    simpa using h2
  have hHlim : Filter.Tendsto (fun t : ℝ =>
      Complex.log ((g₁ - σ (vc + t)) / (g₁ - σ (vc - t)))
        - Complex.log ((g₂ - σ (vc + t)) / (g₂ - σ (vc - t))))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h2 := (hlogc (hRlim g₁ hg₁P)).sub (hlogc (hRlim g₂ hg₂P))
    simpa using h2
  have hElim : Filter.Tendsto E (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (((ςv : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) := by
    rw [hEdef]
    have h2 := (hFlim.add hGlim).add hHlim
    simpa using h2
  -- selection of the probe height and conclusion
  have hev₀ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  have hevh : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < h :=
    nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hh)
  have hevη₁ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < η₁ :=
    nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hη₁)
  have hevnear := Metric.tendsto_nhds.mp hElim 1 one_pos
  obtain ⟨η, hη0, hηa, hηb, hηd⟩ :=
    (hev₀.and (hevh.and (hevη₁.and hevnear))).exists
  refine ⟨η, hη0, ?_⟩
  intro hEQ
  have hid := hkey η hη0 hηa.le hηb
  rw [hEQ] at hid
  simp only [sub_self, mul_zero] at hid
  rw [← hid, dist_eq_norm, zero_sub, norm_neg] at hηd
  have h4 : |ςv| = 1 := by rcases hςv with h' | h' <;> rw [h'] <;> norm_num
  have h5 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have h3 : ‖((ςv : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, h4, one_mul, h5]
  rw [h3] at hηd
  linarith [Real.pi_gt_three]

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Leaf.Leaves

/-!
# Corridors, the winding jump, and chart alignment

The logarithmic lift increments across a slit, the winding jump across a single
crossing, the corridor steps, and the alignment of leaves visiting a common chart.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **The crossing theorem**: under the no-bigon principle in both chiralities and the
winding jump at the single trajectory–leaf crossing, every competitor path between the
endpoints of a vertical trajectory arc meets each all-time transverse leaf through an
interior trajectory point. -/
theorem competitor_crosses_leaf {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Ici a)) (ha : a < 0)
    {T : ℝ} (hT : 0 < T)
    {τ : ℝ → ℂ} (hτ : IsTrajOn (fun z => -q z) τ Set.univ)
    {tstar : ℝ} (htstar : tstar ∈ Set.Ioo 0 T) (hτ0 : τ 0 = σ tstar)
    (p : C(unitInterval, ℂ)) (hp0 : p 0 = σ 0) (hp1 : p 1 = σ T)
    (hpim : ∀ s : unitInterval, 0 < (p s).im)
    (hjump : (∀ (s : unitInterval) (u : ℝ), p s ≠ τ u) →
      ∃ η : ℝ, 0 < η ∧
        (windingNumber (leafLoopC p σ T
            (hσ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1) (τ η) ≠ 0 ∨
         windingNumber (leafLoopC p σ T
            (hσ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1)
              (τ (-η)) ≠ 0)) :
    ∃ (s : unitInterval) (u : ℝ), p s = τ u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨η, hη, hor⟩ := hjump hcon
  set L : C(unitInterval, ℂ) := leafLoopC p σ T
    (hσ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1 with hLdef
  have hcl : L 0 = L 1 := leafLoop_closed p σ T _ hT.le hp1 hp0
  have hLs : ∀ s : unitInterval, L s = leafLoop p σ T (s : ℝ) := fun s => rfl
  have hmiss : ∀ (s : unitInterval) (u : ℝ), u ≠ 0 → L s ≠ τ u := by
    intro s u hu hLeq
    rcases leafLoop_cases p σ T hT.le s with ⟨s', hs'⟩ | ⟨v, hv, hveq⟩
    · refine hcon s' u ?_
      rw [← hs', ← hLs s]
      exact hLeq
    · have hσv : σ v = τ u := by
        rw [← hveq, ← hLs s]
        exact hLeq
      have hcr := leaf_cross_once hq hbigon hbigonH hσ hτ
        (lt_of_lt_of_le ha hv.1) (lt_trans ha htstar.1) hσv hτ0.symm
      exact hu hcr.2
  have hLim : ∀ s : unitInterval, 0 < (L s).im := by
    intro s
    rcases leafLoop_cases p σ T hT.le s with ⟨s', hs'⟩ | ⟨v, hv, hveq⟩
    · rw [hLs s, hs']
      exact hpim s'
    · rw [hLs s, hveq]
      exact (traj_regular hσ (Set.mem_Ici.mpr (le_trans ha.le hv.1))).1
  have hKc : IsCompact (Set.range L) := isCompact_range L.continuous
  obtain ⟨z₀, hz₀mem, hz₀min⟩ := hKc.exists_isMinOn (Set.range_nonempty _)
    Complex.continuous_im.continuousOn
  set β : ℝ := z₀.im with hβdef
  have hβ : 0 < β := by
    obtain ⟨s, hs⟩ := hz₀mem
    rw [hβdef, ← hs]
    exact hLim s
  have hfloor : ∀ s : unitInterval, β ≤ (L s).im := fun s =>
    hz₀min (Set.mem_range_self s)
  have hlow : ∀ z : ℂ, z.im < β → windingNumber L z = 0 := by
    intro z hz
    obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
    set z₁ : ℂ := Complex.I * (-(max R 0 + 1) : ℝ) with hz₁def
    have hz₁im : z₁.im = -(max R 0 + 1) := by
      rw [hz₁def]
      simp
    have h0 : windingNumber L z₁ = 0 := by
      refine windingNumber_eq_zero_of_ball (c := 0) (r := max R 0 + 1) hcl ?_ ?_
      · intro t
        have := hR (Set.mem_range_self t)
        rw [Metric.mem_closedBall] at this
        rw [Metric.mem_ball]
        have hRm : R ≤ max R 0 := le_max_left _ _
        linarith
      · rw [Metric.mem_ball, dist_zero_right, hz₁def]
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonpos (by
          have := le_max_right R 0
          linarith : -(max R 0 + 1) ≤ 0)]
        simp only [neg_neg]
        exact not_lt.mpr le_rfl
    have hCconv : Convex ℝ {w : ℂ | w.im < β} := by
      intro x hx y hy c d hc hd hcd
      simp only [Set.mem_setOf_eq] at *
      have him : (c • x + d • y).im = c * x.im + d * y.im := by
        simp [Complex.add_im]
      rcases eq_or_lt_of_le hc with hc0 | hc0
      · have hd1 : d = 1 := by linarith
        rw [him, ← hc0, hd1]
        simpa using hy
      · have h1 : c * x.im < c * β := mul_lt_mul_of_pos_left hx hc0
        have h2 : d * y.im ≤ d * β := mul_le_mul_of_nonneg_left hy.le hd
        rw [him]
        nlinarith
    have hdisj : ∀ t : unitInterval, L t ∉ {w : ℂ | w.im < β} := by
      intro t hmem
      simp only [Set.mem_setOf_eq] at hmem
      exact absurd hmem (not_lt.mpr (hfloor t))
    have hz₁mem : z₁ ∈ {w : ℂ | w.im < β} := by
      simp only [Set.mem_setOf_eq, hz₁im]
      have : (0 : ℝ) ≤ max R 0 := le_max_right _ _
      linarith
    exact (windingNumber_eq_of_preconnected hcl hCconv.isPreconnected hdisj
      hz hz₁mem).trans h0
  have hτcont : Continuous τ := continuousOn_univ.mp hτ.cont
  have hconstpos : ∀ u₁ u₂ : ℝ, 0 < u₁ → 0 < u₂ →
      windingNumber L (τ u₁) = windingNumber L (τ u₂) := by
    intro u₁ u₂ h1 h2
    refine windingNumber_eq_of_preconnected hcl
      (isPreconnected_Ioi.image τ hτcont.continuousOn) ?_ ⟨u₁, h1, rfl⟩ ⟨u₂, h2, rfl⟩
    rintro t ⟨u, hu, heq⟩
    exact hmiss t u (ne_of_gt hu) heq.symm
  have hconstneg : ∀ u₁ u₂ : ℝ, u₁ < 0 → u₂ < 0 →
      windingNumber L (τ u₁) = windingNumber L (τ u₂) := by
    intro u₁ u₂ h1 h2
    refine windingNumber_eq_of_preconnected hcl
      (isPreconnected_Iio.image τ hτcont.continuousOn) ?_ ⟨u₁, h1, rfl⟩ ⟨u₂, h2, rfl⟩
    rintro t ⟨u, hu, heq⟩
    exact hmiss t u (ne_of_lt hu) heq.symm
  obtain ⟨Rw, hRw⟩ := (isBounded_windingRegion hcl).subset_closedBall 0
  set Kconf : Set ℂ := Metric.closedBall 0 Rw ∩ {z : ℂ | β ≤ z.im} with hKconfdef
  have hKconfc : IsCompact Kconf := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hKconfH : Kconf ⊆ {z : ℂ | 0 < z.im} := fun z hz =>
    lt_of_lt_of_le hβ hz.2
  have hmem : ∀ u : ℝ, u ≠ 0 → windingNumber L (τ u) ≠ 0 → τ u ∈ Kconf := by
    intro u hu hw
    have hnr : τ u ∉ Set.range L := by
      rintro ⟨t, ht⟩
      exact hmiss t u hu ht
    refine ⟨hRw ⟨hnr, hw⟩, ?_⟩
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    push Not at hlt
    exact hw (hlow _ hlt)
  have hbigon' : ∀ (σv τh : ℝ → ℂ) (T' s' μ' : ℝ), 0 < T' → 0 ≤ s' → 0 < μ' →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ') (T' + μ')) →
      IsTrajOn (fun z => -(fun z => -q z) z) τh (Set.Icc (-μ') (s' + μ')) →
      τh 0 = σv T' → τh s' = σv 0 → False := by
    intro σv τh T' s' μ' hT' hs' hμ' hσv hτh hc1 hc2
    have hqq : (fun z => -(fun z => -q z) z) = q := funext fun z => neg_neg (q z)
    rw [hqq] at hτh
    exact hbigonH σv τh T' s' μ' hT' hs' hμ' hσv hτh hc1 hc2
  rcases hor with hnz | hnz
  · refine confined_tail_false (q := fun z => -q z) hq.neg hbigon'
      (traj_mono hτ (Set.subset_univ _) : IsTrajOn _ τ (Set.Ici 0))
      hKconfc hKconfH (T₀ := η) ?_
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hη hu
    refine hmem u (ne_of_gt hu0) ?_
    rw [hconstpos u η hu0 hη]
    exact hnz
  · refine confined_tail_false_bwd (q := fun z => -q z) hq.neg hbigon'
      (traj_mono hτ (Set.subset_univ _) : IsTrajOn _ τ (Set.Iic 0))
      hKconfc hKconfH (T₀ := -η) ?_
    intro u hu
    have hu0 : u < 0 := lt_of_le_of_lt hu (by linarith)
    refine hmem u (ne_of_lt hu0) ?_
    rw [hconstneg u (-η) hu0 (by linarith)]
    exact hnz

/-- **Trajectory arcs are injective**: a vertical trajectory with interior margin cannot
revisit a point — a return would close a vertical loop, a degenerate bigon. -/
theorem traj_injOn {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {σ : ℝ → ℂ} {a b m : ℝ} (hm : 0 < m)
    (hσ : IsTrajOn q σ (Set.Icc (a - m) (b + m))) :
    Set.InjOn σ (Set.Icc a b) := by
  have key : ∀ t₁ t₂, t₁ ∈ Set.Icc a b → t₂ ∈ Set.Icc a b → t₁ < t₂ →
      σ t₁ = σ t₂ → False := by
    intro t₁ t₂ h₁ h₂ hlt heq
    have hmem : t₁ ∈ Set.Icc (a - m) (b + m) := ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
    obtain ⟨him, hne⟩ := traj_regular hσ hmem
    obtain ⟨δ, hδ, τ₀, hτ₀0, hτ₀⟩ := exists_traj_seed (q := fun z => -q z)
      hq.neg him (neg_ne_zero.mpr hne)
    set μ : ℝ := min m δ with hμdef
    have hμ : 0 < μ := lt_min hm hδ
    have hσv : IsTrajOn q (fun v => σ (v + t₁)) (Set.Icc (-μ) (t₂ - t₁ + μ)) := by
      refine traj_mono (traj_shift t₁ hσ) ?_
      intro v hv
      have h3 : μ ≤ m := min_le_left _ _
      simp only [Set.mem_preimage, Set.mem_Icc] at hv ⊢
      constructor
      · linarith [hv.1, h₁.1]
      · linarith [hv.2, h₂.2]
    have hτh : IsTrajOn (fun z => -q z) τ₀ (Set.Icc (-μ) (0 + μ)) := by
      refine traj_mono hτ₀ ?_
      intro v hv
      have h3 : μ ≤ δ := min_le_right _ _
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine hbigon _ τ₀ (t₂ - t₁) 0 μ (by linarith) le_rfl hμ hσv hτh ?_ ?_
    · show τ₀ 0 = σ (t₂ - t₁ + t₁)
      rw [hτ₀0, sub_add_cancel, heq]
    · show τ₀ 0 = σ (0 + t₁)
      rw [hτ₀0, zero_add]
  intro t₁ h₁ t₂ h₂ heq
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact absurd (key t₁ t₂ h₁ h₂ h heq) (fun hf => hf)
  · exact h
  · exact absurd (key t₂ t₁ h₂ h₁ h heq.symm) (fun hf => hf)

/-- **Anchored trajectories realize a flow orientation**: an anchored vertical
trajectory follows the atlas flow forward or backward throughout its window. -/
theorem traj_flow_eval {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hzim : 0 < z.im) (hz0 : q z ≠ 0)
    {T : ℝ} (hT : 0 < T) {σ : ℝ → ℂ} (hσ0 : σ 0 = z)
    (hσ : IsTrajOn q σ (Set.Icc 0 T)) :
    (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) ∨
    (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) := by
  obtain ⟨hact, hmem⟩ := A.sel_spec hzim hz0
  have hrpos : 0 < A.r (A.sel z) := A.hr _ hact
  have hzS : z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) :=
    Metric.ball_subset_ball (by linarith) hmem
  obtain ⟨ε, hε, hgerm⟩ := traj_ambient_local Metric.isOpen_ball
    (A.hd _ hact) (A.hsq _ hact) hσ (Set.Subset.rfl : Set.Icc 0 T ⊆ Set.Icc 0 T)
    (Set.left_mem_Icc.mpr hT.le) (by rw [hσ0]; exact hzS)
  have hslope : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 T) 0 ε := by
    rw [hσ0]
    exact hgerm
  have hslopeu : ∀ u, 0 < u → u ≤ T →
      SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 u) 0 ε := by
    intro u h0 huT
    rw [SlopeAt] at hslope ⊢
    exact hslope.filter_mono (nhdsWithin_mono 0 (Set.Icc_subset_Icc le_rfl huT))
  rcases hε with h1 | h1
  · left
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · rw [← h0, flow_zero A hzim hz0, hσ0]
    · have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
        traj_mono hσ (Set.Icc_subset_Icc le_rfl hu.2)
      have := flow_eq_traj hq A h0 hσu (h1 ▸ hslopeu u h0 hu.2)
      rw [hσ0] at this
      exact this
  · right
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · rw [← h0, neg_zero, flow_zero A hzim hz0, hσ0]
    · have hσu : IsTrajOn q σ (Set.Icc 0 (- -u)) := by
        rw [neg_neg]
        exact traj_mono hσ (Set.Icc_subset_Icc le_rfl hu.2)
      have hsl : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (- -u)) 0 (-1) := by
        rw [neg_neg]
        exact h1 ▸ hslopeu u h0 hu.2
      have := flow_eq_traj_neg hq A (show -u < 0 by linarith) hσu hsl
      rw [neg_neg, hσ0] at this
      exact this

/-- **The all-time flow trajectory**: through a two-sided regular point the atlas flow
is a vertical trajectory on the whole line, gluing the per-window realizers of the two
orientations across the anchor. -/
theorem flow_alltime {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) :
    IsTrajOn q (fun u => A.flow u z) Set.univ := by
  have hzim : 0 < z.im := hz.1
  have hz0 : q z ≠ 0 := hz.2.1
  have hnegR : ∀ T : ℝ, 0 < T → ∃ ρ : ℝ → ℂ, IsTrajOn q ρ (Set.Icc (-T) 0) ∧
      ∀ u ∈ Set.Icc (-T) (0 : ℝ), A.flow u z = ρ u := by
    intro T hT
    obtain ⟨σ, h0, htr, -, hev⟩ := flow_traj_eval_neg hq A hz hT
    have hrev := traj_reverse htr
    have hset : (fun u : ℝ => -u) ⁻¹' Set.Icc 0 T = Set.Icc (-T) 0 := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> rintro ⟨a1, a2⟩ <;> constructor <;> linarith
    rw [hset] at hrev
    refine ⟨fun u => σ (-u), hrev, ?_⟩
    intro u hu
    have := hev (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rwa [neg_neg] at this
  have hposR : ∀ T : ℝ, 0 < T → ∃ σ : ℝ → ℂ, IsTrajOn q σ (Set.Icc 0 T) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) T, A.flow u z = σ u := by
    intro T hT
    obtain ⟨σ, -, htr, -, hev⟩ := flow_traj_eval_pos hq A hz hT
    exact ⟨σ, htr, hev⟩
  constructor
  · -- continuity
    refine Continuous.continuousOn ?_
    rw [continuous_iff_continuousAt]
    intro u₀
    rcases lt_trichotomy u₀ 0 with hu₀ | hu₀ | hu₀
    · obtain ⟨ρ, htr, hev⟩ := hnegR (-u₀ + 1) (by linarith)
      have hmem : Set.Icc (-(-u₀ + 1)) (0 : ℝ) ∈ 𝓝 u₀ :=
        Icc_mem_nhds (by linarith) hu₀
      exact (htr.cont.continuousAt hmem).congr
        (by filter_upwards [hmem] with u hu using (hev u hu).symm)
    · subst hu₀
      obtain ⟨σp, hptr, hpev⟩ := hposR 1 one_pos
      obtain ⟨ρm, hmtr, hmev⟩ := hnegR 1 one_pos
      have h₁ : ContinuousWithinAt (fun u => A.flow u z) (Set.Icc (0 : ℝ) 1) 0 := by
        refine (hptr.cont 0 ⟨le_rfl, zero_le_one⟩).congr ?_ ?_
        · intro u hu
          exact hpev u hu
        · exact hpev 0 ⟨le_rfl, zero_le_one⟩
      have h₂ : ContinuousWithinAt (fun u => A.flow u z) (Set.Icc (-1 : ℝ) 0) 0 := by
        refine (hmtr.cont 0 ⟨by norm_num, le_rfl⟩).congr ?_ ?_
        · intro u hu
          exact hmev u hu
        · exact hmev 0 ⟨by norm_num, le_rfl⟩
      have h₃ := h₂.union h₁
      rw [Set.Icc_union_Icc_eq_Icc (by norm_num : (-1:ℝ) ≤ 0) zero_le_one] at h₃
      exact h₃.continuousAt (Icc_mem_nhds (by norm_num) one_pos)
    · obtain ⟨σp, htr, hev⟩ := hposR (u₀ + 1) (by linarith)
      have hmem : Set.Icc (0 : ℝ) (u₀ + 1) ∈ 𝓝 u₀ :=
        Icc_mem_nhds hu₀ (by linarith)
      exact (htr.cont.continuousAt hmem).congr
        (by filter_upwards [hmem] with u hu using (hev u hu).symm)
  · -- charts
    intro t₀ _
    rw [nhdsWithin_univ]
    rcases lt_trichotomy t₀ 0 with ht₀ | ht₀ | ht₀
    · obtain ⟨ρ, htr, hev⟩ := hnegR (-t₀ + 1) (by linarith)
      have ht₀mem : t₀ ∈ Set.Icc (-(-t₀ + 1)) (0 : ℝ) := ⟨by linarith, ht₀.le⟩
      obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevd⟩ :=
        htr.chart t₀ ht₀mem
      have hfilter : nhdsWithin t₀ (Set.Icc (-(-t₀ + 1)) (0 : ℝ)) = 𝓝 t₀ :=
        nhdsWithin_eq_nhds.mpr (Icc_mem_nhds (by linarith) ht₀)
      rw [hfilter] at hevd
      refine ⟨U, hUo, by rw [hev t₀ ht₀mem]; exact hpU, hUH, hUne,
        Φ, hΦd, hΦinj, hΦsq, ?_⟩
      filter_upwards [hevd, Icc_mem_nhds (by linarith : -(-t₀ + 1) < t₀) ht₀]
        with u hu huI
      rw [hev u huI, hev t₀ ht₀mem]
      exact hu
    · subst ht₀
      obtain ⟨σp, -, hptr, hpsl, hpev⟩ := flow_traj_eval_pos hq A hz one_pos
      obtain ⟨σm, -, hmtr, hmsl, hmev⟩ := flow_traj_eval_neg hq A hz one_pos
      obtain ⟨hact, hmem⟩ := A.sel_spec hzim hz0
      have hrpos : 0 < A.r (A.sel z) := A.hr _ hact
      have hzS : z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) :=
        Metric.ball_subset_ball (by linarith) hmem
      have hp0' : σp 0 = z := by
        have := hpev 0 ⟨le_rfl, zero_le_one⟩
        rw [flow_zero A hzim hz0] at this
        exact this.symm
      have hm0' : σm 0 = z := by
        have := hmev 0 ⟨le_rfl, zero_le_one⟩
        rw [neg_zero, flow_zero A hzim hz0] at this
        exact this.symm
      have hfR : nhdsWithin (0 : ℝ) (Set.Icc 0 1) = nhdsWithin 0 (Set.Ici 0) :=
        nhdsWithin_Icc_eq_nhdsGE one_pos
      set Φ0 : ℂ → ℂ := A.Φ (A.sel z) with hΦ0def
      have hGR : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ici 0),
          A.flow u z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) ∧
          Φ0 (A.flow u z) = Φ0 (A.flow 0 z) + ((u - 0 : ℝ) : ℂ) := by
        rw [← hfR]
        have hUσ : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Icc 0 1),
            σp u ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) := by
          refine (hptr.cont 0 ⟨le_rfl, zero_le_one⟩) ?_
          rw [hp0']
          exact Metric.isOpen_ball.mem_nhds hzS
        have hpsl' := hpsl
        rw [SlopeAt, hp0'] at hpsl'
        filter_upwards [hpsl', hUσ, eventually_mem_nhdsWithin] with u hdev hU huI
        refine ⟨by rw [hpev u huI]; exact hU, ?_⟩
        rw [hpev u huI, flow_zero A hzim hz0, hdev]
        push_cast
        ring
      have hmapneg : Filter.Tendsto (fun u : ℝ => -u)
          (nhdsWithin (0 : ℝ) (Set.Iic 0)) (nhdsWithin (0 : ℝ) (Set.Icc 0 1)) := by
        rw [hfR]
        refine Filter.Tendsto.inf (by simpa using continuous_neg.tendsto (0 : ℝ)) ?_
        exact Filter.tendsto_principal_principal.mpr fun u hu => by
          simp only [Set.mem_Iic] at hu
          simpa using hu
      have hGL : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Iic 0),
          A.flow u z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) ∧
          Φ0 (A.flow u z) = Φ0 (A.flow 0 z) + ((u - 0 : ℝ) : ℂ) := by
        have hUσ : ∀ᶠ v in nhdsWithin (0 : ℝ) (Set.Icc 0 1),
            σm v ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) := by
          refine (hmtr.cont 0 ⟨le_rfl, zero_le_one⟩) ?_
          rw [hm0']
          exact Metric.isOpen_ball.mem_nhds hzS
        have hmsl' := hmsl
        rw [SlopeAt, hm0'] at hmsl'
        filter_upwards [hmapneg.eventually hmsl', hmapneg.eventually hUσ,
          hmapneg.eventually eventually_mem_nhdsWithin] with u hdev hU huI
        have hflip : A.flow u z = σm (-u) := by
          have := hmev (-u) huI
          rwa [neg_neg] at this
        refine ⟨by rw [hflip]; exact hU, ?_⟩
        rw [hflip, flow_zero A hzim hz0, hdev]
        push_cast
        ring
      have hGN : ∀ᶠ u in 𝓝 (0 : ℝ),
          A.flow u z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) ∧
          Φ0 (A.flow u z) = Φ0 (A.flow 0 z) + ((u - 0 : ℝ) : ℂ) := by
        rw [← nhdsLE_sup_nhdsGE (0 : ℝ), eventually_sup]
        exact ⟨hGL, hGR⟩
      exact ⟨Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)), Metric.isOpen_ball,
        by rw [flow_zero A hzim hz0]; exact hzS, A.hH _ hact, A.hne _ hact,
        Φ0, A.hd _ hact, A.hinj _ hact, A.hsq _ hact, hGN⟩
    · obtain ⟨σp, htr, hev⟩ := hposR (t₀ + 1) (by linarith)
      have ht₀mem : t₀ ∈ Set.Icc (0 : ℝ) (t₀ + 1) := ⟨ht₀.le, by linarith⟩
      obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevd⟩ :=
        htr.chart t₀ ht₀mem
      have hfilter : nhdsWithin t₀ (Set.Icc (0 : ℝ) (t₀ + 1)) = 𝓝 t₀ :=
        nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht₀ (by linarith))
      rw [hfilter] at hevd
      refine ⟨U, hUo, by rw [hev t₀ ht₀mem]; exact hpU, hUH, hUne,
        Φ, hΦd, hΦinj, hΦsq, ?_⟩
      filter_upwards [hevd, Icc_mem_nhds ht₀ (by linarith : t₀ < t₀ + 1)]
        with u hu huI
      rw [hev u huI, hev t₀ ht₀mem]
      exact hu

/-- **Congruence of the trajectory predicate in the differential**: trajectories only
read the differential pointwise. -/
theorem isTrajOn_congr {q₁ q₂ : ℂ → ℂ} (h : ∀ w, q₁ w = q₂ w)
    {σ : ℝ → ℂ} {s : Set ℝ} (hσ : IsTrajOn q₁ σ s) : IsTrajOn q₂ σ s := by
  constructor
  · exact hσ.cont
  · intro t ht
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hσ.chart t ht
    exact ⟨U, hUo, hpU, hUH, fun w hw => h w ▸ hUne w hw, Φ, hΦd, hΦinj,
      fun w hw => h w ▸ hΦsq w hw, hev⟩

/-- **Transverse tails are proper**: under the no-bigon principle in both chiralities
an all-time transverse leaf leaves every compact subset of the upper half plane at
arbitrarily late times. -/
theorem leaf_tail_proper {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {τ : ℝ → ℂ} {a : ℝ} (hτ : IsTrajOn (fun z => -q z) τ (Set.Ici a))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ {z : ℂ | 0 < z.im}) :
    ∀ T₀ : ℝ, ∃ t : ℝ, T₀ ≤ t ∧ τ t ∉ K := by
  intro T₀
  by_contra hcon
  push Not at hcon
  have hbigon' : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -(fun w => -q w) z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False := by
    intro σv τh T s μ hT hs hμ hσv hτh hc1 hc2
    exact hbigonH σv τh T s μ hT hs hμ hσv
      (isTrajOn_congr (fun w => neg_neg (q w)) hτh) hc1 hc2
  exact confined_tail_false hq.neg hbigon' hτ hK hKH (fun t ht => hcon t ht)

/-- **Germ propagation on the common interval**: trajectories of one differential on
open intervals that agree near a common interior parameter agree on the intersection. -/
theorem traj_agree_of_germ {qL : ℂ → ℂ} {σ₁ σ₂ : ℝ → ℂ}
    {α₁ β₁ α₂ β₂ u : ℝ}
    (h₁ : IsTrajOn qL σ₁ (Set.Ioo α₁ β₁)) (h₂ : IsTrajOn qL σ₂ (Set.Ioo α₂ β₂))
    (hu₁ : u ∈ Set.Ioo α₁ β₁) (hu₂ : u ∈ Set.Ioo α₂ β₂)
    (hgerm : ∀ᶠ v in 𝓝 u, σ₁ v = σ₂ v) :
    ∀ v, max α₁ α₂ < v → v < min β₁ β₂ → σ₁ v = σ₂ v := by
  -- the forward engine, universally over trajectory pairs sharing the germ point
  have hfwd : ∀ (τ₁ τ₂ : ℝ → ℂ) (A₁ B₁ A₂ B₂ : ℝ),
      IsTrajOn qL τ₁ (Set.Ioo A₁ B₁) → IsTrajOn qL τ₂ (Set.Ioo A₂ B₂) →
      u ∈ Set.Ioo A₁ B₁ → u ∈ Set.Ioo A₂ B₂ →
      (∀ᶠ v in 𝓝 u, τ₁ v = τ₂ v) →
      ∀ v, u ≤ v → v < min B₁ B₂ → τ₁ v = τ₂ v := by
    intro τ₁ τ₂ A₁ B₁ A₂ B₂ k₁ k₂ ku₁ ku₂ kgerm v huv hv
    set c : ℝ := (v + min B₁ B₂) / 2 with hcdef
    have hvc : v < c := by rw [hcdef]; linarith
    have hcB : c < min B₁ B₂ := by rw [hcdef]; linarith
    have hsub₁ : Set.Icc u c ⊆ Set.Ioo A₁ B₁ := fun x hx =>
      ⟨lt_of_lt_of_le ku₁.1 hx.1,
        lt_of_le_of_lt hx.2 (lt_of_lt_of_le hcB (min_le_left _ _))⟩
    have hsub₂ : Set.Icc u c ⊆ Set.Ioo A₂ B₂ := fun x hx =>
      ⟨lt_of_lt_of_le ku₂.1 hx.1,
        lt_of_le_of_lt hx.2 (lt_of_lt_of_le hcB (min_le_right _ _))⟩
    have huc : u ≤ c := le_trans huv hvc.le
    have := traj_unique huc (traj_mono k₁ hsub₁) (traj_mono k₂ hsub₂)
      (kgerm.filter_mono nhdsWithin_le_nhds)
    exact this ⟨huv, hvc.le⟩
  intro v hvl hvr
  rcases le_or_gt u v with huv | huv
  · exact hfwd σ₁ σ₂ α₁ β₁ α₂ β₂ h₁ h₂ hu₁ hu₂ hgerm v huv hvr
  · -- the reflected pair about `u`
    have hrev : ∀ (τ : ℝ → ℂ) (A B : ℝ), IsTrajOn qL τ (Set.Ioo A B) →
        IsTrajOn qL (fun wv => τ (2 * u - wv))
          (Set.Ioo (2 * u - B) (2 * u - A)) := by
      intro τ A B k
      have hsh := traj_shift (-(2 * u)) (traj_reverse k)
      have hset : (fun wv : ℝ => wv + -(2 * u)) ⁻¹'
          ((fun wv : ℝ => -wv) ⁻¹' Set.Ioo A B)
          = Set.Ioo (2 * u - B) (2 * u - A) := by
        ext wv
        simp only [Set.mem_preimage, Set.mem_Ioo]
        constructor <;> rintro ⟨p1, p2⟩ <;> constructor <;> linarith
      rw [hset] at hsh
      have hfun : (fun wv : ℝ => (fun x : ℝ => τ (-x)) (wv + -(2 * u)))
          = fun wv => τ (2 * u - wv) := by
        funext wv
        change τ (-(wv + -(2 * u))) = τ (2 * u - wv)
        congr 1
        ring
      rwa [hfun] at hsh
    have hρ₁ := hrev σ₁ α₁ β₁ h₁
    have hρ₂ := hrev σ₂ α₂ β₂ h₂
    have hρu₁ : u ∈ Set.Ioo (2 * u - β₁) (2 * u - α₁) :=
      ⟨by linarith [hu₁.2], by linarith [hu₁.1]⟩
    have hρu₂ : u ∈ Set.Ioo (2 * u - β₂) (2 * u - α₂) :=
      ⟨by linarith [hu₂.2], by linarith [hu₂.1]⟩
    have hρgerm : ∀ᶠ wv in 𝓝 u,
        (fun wv => σ₁ (2 * u - wv)) wv = (fun wv => σ₂ (2 * u - wv)) wv := by
      have hmap : Filter.Tendsto (fun wv : ℝ => 2 * u - wv) (𝓝 u) (𝓝 u) := by
        have h1 : Continuous fun wv : ℝ => 2 * u - wv := by fun_prop
        have h2 := h1.tendsto u
        rwa [show 2 * u - u = u from by ring] at h2
      filter_upwards [hmap.eventually hgerm] with wv hwv
      exact hwv
    have := hfwd _ _ _ _ _ _ hρ₁ hρ₂ hρu₁ hρu₂ hρgerm (2 * u - v)
      (by linarith) (by
        have h1 : max α₁ α₂ < v := hvl
        have h2 := le_max_left α₁ α₂
        have h3 := le_max_right α₁ α₂
        exact lt_min (by linarith) (by linarith))
    have hval : 2 * u - (2 * u - v) = v := by ring
    simpa [hval] using this

/-- **Anchored leaves meeting forces equal levels**: all-time transverse trajectories
anchored on a vertical trajectory that share a point are anchored at the same level. -/
theorem leaves_meet_level {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} {a : ℝ} (hϑ : IsTrajOn q ϑ (Set.Ici a))
    {γ₁ γ₂ : ℝ → ℂ}
    (h₁ : IsTrajOn (fun z => -q z) γ₁ Set.univ)
    (h₂ : IsTrajOn (fun z => -q z) γ₂ Set.univ)
    {t₁ t₂ : ℝ} (ht₁ : a < t₁) (ht₂ : a < t₂)
    (ha₁ : γ₁ 0 = ϑ t₁) (ha₂ : γ₂ 0 = ϑ t₂)
    {u₁ u₂ : ℝ} (hshare : γ₁ u₁ = γ₂ u₂) :
    t₁ = t₂ := by
  set δ₂ : ℝ → ℂ := fun v => γ₂ (v + (u₂ - u₁)) with hδ₂def
  have hδ₂traj : IsTrajOn (fun z => -q z) δ₂ Set.univ := by
    have := traj_shift (u₂ - u₁) h₂
    rwa [Set.preimage_univ] at this
  have hδshare : γ₁ u₁ = δ₂ u₁ := by
    rw [hδ₂def]
    simp only
    rw [show u₁ + (u₂ - u₁) = u₂ from by ring]
    exact hshare
  -- agreement everywhere from a germ, for all-time transverse trajectories
  have hagree_univ : ∀ (τ₁ τ₂ : ℝ → ℂ),
      IsTrajOn (fun z => -q z) τ₁ Set.univ →
      IsTrajOn (fun z => -q z) τ₂ Set.univ →
      (∀ᶠ v in 𝓝 u₁, τ₁ v = τ₂ v) → ∀ v, τ₁ v = τ₂ v := by
    intro τ₁ τ₂ k₁ k₂ kgerm v
    set R : ℝ := |v - u₁| + 1 with hRdef
    have habs : |v - u₁| < R := by rw [hRdef]; linarith [abs_nonneg (v - u₁)]
    have hvmem := abs_lt.mp habs
    have hu₁mem : u₁ ∈ Set.Ioo (u₁ - R) (u₁ + R) :=
      ⟨by linarith [abs_nonneg (v - u₁)], by linarith [abs_nonneg (v - u₁)]⟩
    refine traj_agree_of_germ (traj_mono k₁ (Set.subset_univ _))
      (traj_mono k₂ (Set.subset_univ _)) hu₁mem hu₁mem kgerm v ?_ ?_
    · rw [max_self]
      linarith [hvmem.1]
    · rw [min_self]
      linarith [hvmem.2]
  -- the germ dichotomy at the shared point
  have hu₁univ : u₁ ∈ Set.univ := Set.mem_univ u₁
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev₁⟩ := h₁.chart u₁ hu₁univ
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
  -- in either orientation the second anchor lies on the first leaf
  have hkey : ∃ w : ℝ, γ₁ w = ϑ t₂ := by
    rcases hε with hε1 | hε1
    · -- same orientation: δ₂ = γ₁ everywhere
      have hgerm : ∀ᶠ v in 𝓝 u₁, γ₁ v = δ₂ v := by
        filter_upwards [hev₁, hev₂, hδUev] with v h1v h2v hUv
        refine hΦinj h1v.1 hUv ?_
        rw [h1v.2, h2v, hε1, hδshare]
        push_cast
        ring
      have hall := hagree_univ γ₁ δ₂ h₁ hδ₂traj hgerm
      refine ⟨-(u₂ - u₁), ?_⟩
      rw [hall (-(u₂ - u₁)), hδ₂def]
      simp only
      rw [show -(u₂ - u₁) + (u₂ - u₁) = 0 from by ring]
      exact ha₂
    · -- opposite orientation: δ₂ is the reflected first leaf
      have hρtraj : IsTrajOn (fun z => -q z) (fun v => γ₁ (2 * u₁ - v))
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
        have := hc.tendsto u₁
        rwa [show 2 * u₁ - u₁ = u₁ from by ring] at this
      have hgerm : ∀ᶠ v in 𝓝 u₁, δ₂ v = (fun v => γ₁ (2 * u₁ - v)) v := by
        filter_upwards [hmap.eventually hev₁, hev₂, hδUev] with v h1v h2v hUv
        refine (hΦinj h1v.1 hUv ?_).symm
        rw [h1v.2, h2v, hε1, hδshare]
        push_cast
        ring
      have hall := hagree_univ δ₂ (fun v => γ₁ (2 * u₁ - v)) hδ₂traj hρtraj hgerm
      refine ⟨2 * u₁ - -(u₂ - u₁), ?_⟩
      have := hall (-(u₂ - u₁))
      rw [hδ₂def] at this
      simp only at this
      rw [show -(u₂ - u₁) + (u₂ - u₁) = 0 from by ring] at this
      rw [← this]
      exact ha₂
  -- one leaf crossing the vertical trajectory at both levels
  obtain ⟨w, hw⟩ := hkey
  exact (leaf_cross_once hq hbigon hbigonH hϑ h₁ ht₁ ht₂ ha₁.symm hw.symm).1

/-- **Winding difference is the ratio winding**: for a closed curve avoiding two base
points, `w(γ, zp) − w(γ, zm)` is the winding of `(γ − zp)/(γ − zm)` about `0`. -/
theorem winding_sub_eq_ratio {γ : C(unitInterval, ℂ)} (hcl : γ 0 = γ 1)
    {zp zm : ℂ} (hpp : ∀ t, γ t ≠ zp) (hmm : ∀ t, γ t ≠ zm)
    (r : C(unitInterval, ℂ)) (hr : ∀ t, r t = (γ t - zp) / (γ t - zm)) :
    windingNumber γ zp - windingNumber γ zm = windingNumber r 0 := by
  have hsubp : ∀ t, shiftedCurve γ zp t = γ t - zp := by
    intro t
    simp [shiftedCurve]
  have hsubm : ∀ t, shiftedCurve γ zm t = γ t - zm := by
    intro t
    simp [shiftedCurve]
  have hnep : ∀ t, shiftedCurve γ zp t ≠ 0 := fun t => by
    rw [hsubp t]
    exact sub_ne_zero.mpr (hpp t)
  have hnem : ∀ t, shiftedCurve γ zm t ≠ 0 := fun t => by
    rw [hsubm t]
    exact sub_ne_zero.mpr (hmm t)
  obtain ⟨Lp, hLp⟩ := exists_isLogLiftOf (shiftedCurve γ zp) hnep
  obtain ⟨Lm, hLm⟩ := exists_isLogLiftOf (shiftedCurve γ zm) hnem
  -- the difference of the lifts lifts the ratio
  have hLr : IsLogLiftOf (Lp - Lm) (shiftedCurve r 0) := by
    intro t
    change Complex.exp (Lp t - Lm t) = shiftedCurve r 0 t
    rw [Complex.exp_sub, hLp t, hLm t, hsubp t, hsubm t]
    have : shiftedCurve r 0 t = r t := by simp [shiftedCurve]
    rw [this, hr t]
  have hrcl : r 0 = r 1 := by
    rw [hr 0, hr 1, hcl]
  have hrne : ∀ t, r t ≠ (0 : ℂ) := fun t => by
    rw [hr t]
    exact div_ne_zero (sub_ne_zero.mpr (hpp t)) (sub_ne_zero.mpr (hmm t))
  have hspecp := windingNumber_spec hcl hpp hLp
  have hspecm := windingNumber_spec hcl hmm hLm
  have hspecr := windingNumber_spec hrcl hrne hLr
  have hval : (Lp - Lm) 1 - (Lp - Lm) 0 = (Lp 1 - Lp 0) - (Lm 1 - Lm 0) := by
    simp only [ContinuousMap.sub_apply]
    ring
  rw [hval, hspecp, hspecm] at hspecr
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hkey : (2 * (Real.pi : ℂ) * Complex.I)
      * ((windingNumber γ zp : ℂ) - (windingNumber γ zm : ℂ))
      = (2 * (Real.pi : ℂ) * Complex.I) * (windingNumber r 0 : ℂ) := by
    linear_combination hspecr
  have := mul_left_cancel₀ hπ hkey
  exact_mod_cast this
/-- **Off-segment ratios avoid the slit**: for a point off the closed segment between
the base points, the displacement ratio lies in the slit plane. -/
theorem ratio_slitPlane {w zp zm : ℂ} (h : w ∉ segment ℝ zm zp) :
    (w - zp) / (w - zm) ∈ Complex.slitPlane := by
  have hwm : w ≠ zm := by
    intro he
    exact h (he ▸ left_mem_segment ℝ zm zp)
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push Not at hcon
  set ζ : ℂ := (w - zp) / (w - zm) with hζdef
  have hζre : ζ.re ≤ 0 := hcon.1
  have hζim : ζ.im = 0 := hcon.2
  have hζreal : ζ = ((ζ.re : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · simp
    · simp [hζim]
  set x : ℝ := ζ.re with hxdef
  have hx : x ≤ 0 := hζre
  have hd : w - zm ≠ 0 := sub_ne_zero.mpr hwm
  have hsolve : w - zp = (x : ℂ) * (w - zm) := by
    have h1 : ζ * (w - zm) = w - zp := by
      rw [hζdef, div_mul_cancel₀ _ hd]
    rw [← h1, hζreal]
  have hxden : (0 : ℝ) < 1 - x := by linarith
  have h3' : (1 : ℂ) - (x : ℂ) ≠ 0 := by
    have := Complex.ofReal_ne_zero.mpr (ne_of_gt hxden)
    push_cast at this
    exact this
  have hcomb : w = ((-x / (1 - x) : ℝ)) • zm + ((1 / (1 - x) : ℝ)) • zp := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h3']
    linear_combination hsolve
  refine h ?_
  rw [hcomb]
  refine ⟨-x / (1 - x), 1 / (1 - x), ?_, ?_, ?_, rfl⟩
  · exact div_nonneg (by linarith) hxden.le
  · exact div_nonneg zero_le_one hxden.le
  · have h5 : (-x + 1) / (1 - x) = 1 := by
      rw [div_eq_one_iff_eq (ne_of_gt hxden)]
      ring
    calc -x / (1 - x) + 1 / (1 - x) = (-x + 1) / (1 - x) := by ring
      _ = 1 := h5

/-- **Quantified divided-difference control**: near an interior point the difference
quotient of a holomorphic function is uniformly close to the derivative. -/
theorem divided_diff_ball {Φ : ℂ → ℂ} {P : ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hPS : P ∈ S) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w z : ℂ,
      w ∈ Metric.ball P δ → z ∈ Metric.ball P δ → w ≠ z →
      ‖(Φ w - Φ z) / (w - z) - deriv Φ P‖ < ε := by
  have han : AnalyticAt ℂ Φ P := (hΦd.analyticOnNhd hS) P hPS
  have hstrict : HasStrictDerivAt Φ (deriv Φ P) P :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  intro ε hε
  have hlittle := hstrict.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlittle
  have hev := hlittle (show (0 : ℝ) < ε / 2 by linarith)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨δ / 2, by linarith, ?_⟩
  intro w z hw hz hwz
  have hpair : dist ((w, z) : ℂ × ℂ) (P, P) < δ := by
    rw [Prod.dist_eq]
    have h1 := Metric.mem_ball.mp hw
    have h2 := Metric.mem_ball.mp hz
    exact max_lt (by linarith) (by linarith)
  have hkey := hball hpair
  have hne : w - z ≠ 0 := sub_ne_zero.mpr hwz
  have hquot : (Φ w - Φ z) / (w - z) - deriv Φ P
      = (Φ w - Φ z - (w - z) * deriv Φ P) / (w - z) := by
    field_simp
  rw [hquot, norm_div]
  rw [div_lt_iff₀ (norm_pos_iff.mpr hne)]
  have hkey' : ‖Φ w - Φ z - (w - z) * deriv Φ P‖ ≤ ε / 2 * ‖w - z‖ := by
    have h4 : (ContinuousLinearMap.toSpanSingleton ℂ (deriv Φ P)) (w - z)
        = (w - z) * deriv Φ P := by
      simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    have h5 : ‖Φ w - Φ z
        - (ContinuousLinearMap.toSpanSingleton ℂ (deriv Φ P)) (w - z)‖
        ≤ ε / 2 * ‖w - z‖ := hkey
    rwa [h4] at h5
  refine lt_of_le_of_lt hkey' ?_
  have hpos : 0 < ‖w - z‖ := norm_pos_iff.mpr hne
  nlinarith

/-- **The conjugate-pair ratio as a unit exponential**: for real `y` and nonzero real
`c`, the ratio `(y − ci)/(y + ci)` is `exp(−2·arg(y + ci)·i)`. -/
theorem conj_pair_exp {y c : ℝ} (hc : c ≠ 0) :
    ((y : ℂ) - (c : ℂ) * Complex.I) / ((y : ℂ) + (c : ℂ) * Complex.I)
      = Complex.exp
          (-(2 * ((Complex.arg ((y : ℂ) + (c : ℂ) * Complex.I) : ℝ) : ℂ))
            * Complex.I) := by
  set w : ℂ := (y : ℂ) + (c : ℂ) * Complex.I with hwdef
  have hwim : w.im = c := by
    rw [hwdef]
    simp
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hwim
    exact hc (by simpa using hwim.symm)
  have hrep : ((‖w‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I)
      = w := Complex.norm_mul_exp_arg_mul_I w
  have hconj : (starRingEnd ℂ) w = (y : ℂ) - (c : ℂ) * Complex.I := by
    rw [hwdef]
    simp [Complex.ext_iff]
  have hconjrep : (starRingEnd ℂ) w
      = ((‖w‖ : ℝ) : ℂ) * Complex.exp (-(Complex.arg w : ℂ) * Complex.I) := by
    rw [← hrep]
    rw [map_mul]
    congr 1
    · simp
    · rw [← Complex.exp_conj]
      congr 1
      simp
  have hnorm0 : ((‖w‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw0)
  rw [show ((y : ℂ) - (c : ℂ) * Complex.I) = (starRingEnd ℂ) w from hconj.symm]
  calc (starRingEnd ℂ) w / w
      = (((‖w‖ : ℝ) : ℂ) * Complex.exp (-(Complex.arg w : ℂ) * Complex.I))
        / (((‖w‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I)) := by
        rw [hconjrep]
        congr 1
        exact hrep.symm
    _ = Complex.exp (-(Complex.arg w : ℂ) * Complex.I)
        / Complex.exp ((Complex.arg w : ℂ) * Complex.I) :=
        mul_div_mul_left _ _ hnorm0
    _ = Complex.exp (-(2 * ((Complex.arg w : ℝ) : ℂ)) * Complex.I) := by
        rw [← Complex.exp_sub]
        congr 1
        ring

/-- **The loop's second half**: past the junction the competitor–trajectory loop is
the clamped reversed trajectory arc. -/
theorem leafLoop_second_half (p : C(unitInterval, ℂ)) (f : ℝ → ℂ) (T : ℝ)
    {s : ℝ} (hs : ¬ s ≤ 1 / 2) (hs2 : 2 - 2 * s ≤ 1) :
    leafLoop p f T s = f ((2 - 2 * s) * T) := by
  rw [leafLoop, if_neg hs, min_eq_right hs2]

/-- **The trajectory's chart development from the crossing point**: within the chart
window the trajectory's chart value moves affinely with a single sign. -/
theorem box_arc_dev {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ w ∈ S, q w ≠ 0)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {ϑ : ℝ → ℂ} {a : ℝ} (hϑ : IsTrajOn q ϑ (Set.Ici a))
    {tstar h : ℝ} (hh : 0 < h) (hta : a ≤ tstar - h) (htS : ϑ tstar ∈ S)
    (hdev : ∀ x : ℝ, |x| ≤ h → Φ (ϑ tstar) + (x : ℂ) ∈ Φ '' S) :
    ∃ ε₀ : ℝ, (ε₀ = 1 ∨ ε₀ = -1) ∧ ∀ x : ℝ, |x| ≤ h →
      ϑ (tstar + x) ∈ S ∧
      Φ (ϑ (tstar + x)) = Φ (ϑ tstar) + (ε₀ : ℂ) * (x : ℂ) := by
  obtain ⟨ε₀, hε₀, hfollow⟩ := leaf_follow hS hΦd hΦinj hSH hSne hΦsq hϑ hh
    hta htS hdev
  refine ⟨ε₀, hε₀, ?_⟩
  intro x hx
  have habs : |ε₀ * x| = |x| := by
    rw [abs_mul]
    rcases hε₀ with h1 | h1 <;> rw [h1] <;> simp
  have hmem : Φ (ϑ tstar) + ((ε₀ * x : ℝ) : ℂ) ∈ Φ '' S := by
    refine hdev _ ?_
    rw [habs]
    exact hx
  rw [hfollow x hx]
  refine ⟨localFlow_mem hmem, ?_⟩
  rw [localFlow_dev hmem]
  push_cast
  ring

/-- **The leaf's re-anchored vertical development**: an all-time transverse leaf
through a chart point develops vertically from the point on a symmetric window. -/
theorem box_leaf_dev {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {τ : ℝ → ℂ} (hτ : IsTrajOn (fun w => -q w) τ Set.univ)
    (hτS : τ 0 ∈ S) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ ε₁ : ℝ, (ε₁ = 1 ∨ ε₁ = -1) ∧
      ∀ u : ℝ, |u| ≤ η₀ → τ u ∈ S ∧
        Φ (τ u) = Φ (τ 0) - Complex.I * (ε₁ : ℂ) * (u : ℂ) := by
  have hcont : ContinuousAt τ 0 :=
    hτ.cont.continuousAt (by simp : Set.univ ∈ 𝓝 (0 : ℝ))
  obtain ⟨η₀, hη₀, hball⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually_mem (hS.mem_nhds hτS))
  set η : ℝ := η₀ / 2 with hηdef
  have hη : 0 < η := by linarith
  have htrack : ∀ u ∈ Set.Icc (-η) η, τ u ∈ S := by
    intro u hu
    refine hball ?_
    rw [Real.dist_eq, sub_zero]
    have := abs_le.mpr ⟨hu.1, hu.2⟩
    linarith [abs_le.mpr hu]
  obtain ⟨ε₁, hε₁, hdev⟩ := horizontal_level hS hΦd hΦsq hτ
    (by linarith : -η ≤ η) (Set.subset_univ _) htrack
  have h0mem : (0 : ℝ) ∈ Set.Icc (-η) η := ⟨by linarith, hη.le⟩
  have hanchor := hdev 0 h0mem
  refine ⟨η, hη, ε₁, hε₁, ?_⟩
  intro u hu
  have humem : u ∈ Set.Icc (-η) η := abs_le.mp hu
  refine ⟨htrack u humem, ?_⟩
  have hu' := hdev u humem
  rw [hu', hanchor]
  push_cast
  ring

/-- **Slit-plane lift increment**: a logarithm lift of a slit-plane-valued curve
increments by the principal-logarithm difference. -/
theorem loglift_increment_slit {r L : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hLc : ContinuousOn L (Set.Icc c d)) (hrc : ContinuousOn r (Set.Icc c d))
    (hlift : ∀ t ∈ Set.Icc c d, Complex.exp (L t) = r t)
    (hslit : ∀ t ∈ Set.Icc c d, r t ∈ Complex.slitPlane) :
    L d - L c = Complex.log (r d) - Complex.log (r c) := by
  have hcmem : c ∈ Set.Icc c d := Set.left_mem_Icc.mpr hcd
  have hdmem : d ∈ Set.Icc c d := Set.right_mem_Icc.mpr hcd
  set L' : ℝ → ℂ := fun t => Complex.log (r t) + (L c - Complex.log (r c))
    with hL'def
  have hL'c : ContinuousOn L' (Set.Icc c d) := by
    refine ContinuousOn.add ?_ continuousOn_const
    intro t ht
    exact (continuousAt_clog (hslit t ht)).comp_continuousWithinAt (hrc t ht)
  have hL'lift : ∀ t ∈ Set.Icc c d, Complex.exp (L' t) = r t := by
    intro t ht
    rw [hL'def]
    simp only
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hslit t ht)),
      Complex.exp_sub, hlift c hcmem,
      Complex.exp_log (Complex.slitPlane_ne_zero (hslit c hcmem)),
      div_self (Complex.slitPlane_ne_zero (hslit c hcmem)), mul_one]
  have hanchor : L c = L' c := by
    rw [hL'def]
    ring
  have heq := loglift_unique (f := r) hLc hL'c hlift hL'lift hanchor
  have hd := heq hdmem
  rw [hd, hL'def]
  ring

/-- **Product lift increments split**: a logarithm lift of a product increments by the
sum of the increments of lifts of the factors. -/
theorem loglift_increment_mul {r₁ r₂ L L₁ L₂ : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hLc : ContinuousOn L (Set.Icc c d))
    (hL₁c : ContinuousOn L₁ (Set.Icc c d)) (hL₂c : ContinuousOn L₂ (Set.Icc c d))
    (hlift : ∀ t ∈ Set.Icc c d, Complex.exp (L t) = r₁ t * r₂ t)
    (hlift₁ : ∀ t ∈ Set.Icc c d, Complex.exp (L₁ t) = r₁ t)
    (hlift₂ : ∀ t ∈ Set.Icc c d, Complex.exp (L₂ t) = r₂ t) :
    L d - L c = (L₁ d - L₁ c) + (L₂ d - L₂ c) := by
  have hcmem : c ∈ Set.Icc c d := Set.left_mem_Icc.mpr hcd
  have hdmem : d ∈ Set.Icc c d := Set.right_mem_Icc.mpr hcd
  set L' : ℝ → ℂ := fun t => L₁ t + L₂ t + (L c - L₁ c - L₂ c) with hL'def
  have hL'c : ContinuousOn L' (Set.Icc c d) :=
    (hL₁c.add hL₂c).add continuousOn_const
  have hL'lift : ∀ t ∈ Set.Icc c d, Complex.exp (L' t) = r₁ t * r₂ t := by
    intro t ht
    rw [hL'def]
    simp only
    rw [Complex.exp_add, Complex.exp_add, hlift₁ t ht, hlift₂ t ht]
    rw [show L c - L₁ c - L₂ c = L c - (L₁ c + L₂ c) from by ring,
      Complex.exp_sub, Complex.exp_add, hlift₁ c hcmem, hlift₂ c hcmem,
      hlift c hcmem]
    have hne : r₁ c * r₂ c ≠ 0 := by
      rw [← hlift c hcmem]
      exact Complex.exp_ne_zero _
    rw [div_self hne, mul_one]
  have hanchor : L c = L' c := by
    rw [hL'def]
    ring
  have heq := loglift_unique (f := fun t => r₁ t * r₂ t) hLc hL'c hlift
    hL'lift hanchor
  have hd := heq hdmem
  rw [hd, hL'def]
  ring

/-- **Argument limit at the positive real**: the argument of `δ + cη·i` vanishes as
`η` decreases to zero. -/
theorem arg_limit_pos {δ c : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun η : ℝ => Complex.arg ((δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hδS : ((δ : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hδ
  have hcont : ContinuousAt Complex.arg ((δ : ℝ) : ℂ) := Complex.continuousAt_arg hδS
  have hmap : Filter.Tendsto
      (fun η : ℝ => (δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((δ : ℝ) : ℂ)) := by
    have h1 : Continuous fun η : ℝ =>
        (δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I := by fun_prop
    have h2 := (h1.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h2
  have := hcont.tendsto.comp hmap
  rwa [Complex.arg_ofReal_of_nonneg hδ.le] at this

/-- **Argument limit at the negative real from the signed side**: the argument of
`−δ + cη·i` tends to `±π` according to the sign of `c` as `η` decreases to zero. -/
theorem arg_limit_neg {δ c : ℝ} (hδ : 0 < δ) (hc : c = 1 ∨ c = -1) :
    Filter.Tendsto (fun η : ℝ => Complex.arg (-(δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (c * Real.pi)) := by
  rcases hc with hc1 | hc1
  · -- upper approach: continuity within the closed upper half plane
    have hcw : ContinuousWithinAt Complex.arg {z : ℂ | 0 ≤ z.im} (-(δ : ℂ)) := by
      refine Complex.continuousWithinAt_arg_of_re_neg_of_im_zero ?_ ?_
      · simpa using hδ
      · simp
    have hmap : Filter.Tendsto
        (fun η : ℝ => -(δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (-(δ : ℂ)) {z : ℂ | 0 ≤ z.im}) := by
      refine Filter.Tendsto.inf ?_ ?_
      · have h1 : Continuous fun η : ℝ =>
            -(δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I := by fun_prop
        have h2 := h1.tendsto 0
        simpa using h2
      · refine Filter.tendsto_principal_principal.mpr ?_
        intro η hη
        simp only [Set.mem_setOf_eq, Complex.add_im, Complex.neg_im,
          Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.I_re]
        rw [hc1]
        simp only [Set.mem_Ioi] at hη
        nlinarith
    have := hcw.tendsto.comp hmap
    have harg : Complex.arg (-(δ : ℂ)) = Real.pi := by
      rw [show -(δ : ℂ) = ((-δ : ℝ) : ℂ) from by push_cast; ring]
      exact Complex.arg_ofReal_of_neg (by linarith)
    rw [harg] at this
    simpa [hc1] using this
  · -- lower approach: the one-sided limit into the lower half plane
    have hlim := Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (show (-(δ : ℂ)).re < 0 by simpa using hδ)
      (show (-(δ : ℂ)).im = 0 by simp)
    have hmap : Filter.Tendsto
        (fun η : ℝ => -(δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (-(δ : ℂ)) {z : ℂ | z.im < 0}) := by
      refine Filter.Tendsto.inf ?_ ?_
      · have h1 : Continuous fun η : ℝ =>
            -(δ : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I := by fun_prop
        have h2 := h1.tendsto 0
        simpa using h2
      · refine Filter.tendsto_principal_principal.mpr ?_
        intro η hη
        simp only [Set.mem_setOf_eq, Complex.add_im, Complex.neg_im,
          Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.I_re]
        rw [hc1]
        simp only [Set.mem_Ioi] at hη
        nlinarith
    have := hlim.comp hmap
    simpa [hc1] using this

/-- **Loop avoidance of the transverse leaf off the crossing instant**: under the
no-bigon principles the bundled competitor-trajectory loop misses every leaf point
with nonzero leaf parameter. -/
theorem jump_avoid {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} {a : ℝ} (hϑ : IsTrajOn q ϑ (Set.Ici a)) (ha : a < 0)
    {T : ℝ} (hT : 0 < T) {τ : ℝ → ℂ}
    (hτ : IsTrajOn (fun z => -q z) τ Set.univ)
    {tstar : ℝ} (htstar : tstar ∈ Set.Ioo 0 T) (hτ0 : τ 0 = ϑ tstar)
    {p : C(unitInterval, ℂ)}
    (hmiss : ∀ (s : unitInterval) (u : ℝ), p s ≠ τ u)
    {u : ℝ} (hu : u ≠ 0) (s : unitInterval) :
    leafLoop p ϑ T s ≠ τ u := by
  intro hEq
  rcases leafLoop_cases p ϑ T hT.le s with ⟨s', hs'⟩ | ⟨v, hv, hvE⟩
  · exact hmiss s' u (hs' ▸ hEq)
  · rw [hvE] at hEq
    have hcross := leaf_cross_once hq hbigon hbigonH hϑ hτ
      (lt_of_lt_of_le ha hv.1) (ha.trans htstar.1) hEq hτ0.symm
    exact hu hcross.2

/-- **Uniform clearance of the loop from the crossing point off the window**: outside
an open parameter window around the crossing preimage the loop stays outside a fixed
ball about the crossing point. -/
theorem jump_offwindow {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} {a : ℝ} (hϑ : IsTrajOn q ϑ (Set.Ici a)) (ha : a < 0)
    {T : ℝ} (hT : 0 < T) {τ : ℝ → ℂ}
    (hτ : IsTrajOn (fun z => -q z) τ Set.univ)
    {tstar : ℝ} (htstar : tstar ∈ Set.Ioo 0 T) (hτ0 : τ 0 = ϑ tstar)
    {p : C(unitInterval, ℂ)} (hp1 : p 1 = ϑ T)
    (hmiss : ∀ (s : unitInterval) (u : ℝ), p s ≠ τ u)
    {δ : ℝ} (hδ : 0 < δ) (hδT : tstar + δ < T) (hδ0 : δ < tstar) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ s : unitInterval,
      ((s : ℝ) ≤ 1 - (tstar + δ) / (2 * T) ∨ 1 - (tstar - δ) / (2 * T) ≤ (s : ℝ)) →
      leafLoop p ϑ T s ∉ Metric.ball (ϑ tstar) d₀ := by
  have hcont : ContinuousOn ϑ (Set.Icc 0 T) :=
    hϑ.cont.mono fun _ hx => le_trans ha.le hx.1
  set γ : C(unitInterval, ℂ) := leafLoopC p ϑ T hcont hT.le hp1 with hγdef
  set C : Set unitInterval := {s : unitInterval |
    (s : ℝ) ≤ 1 - (tstar + δ) / (2 * T) ∨ 1 - (tstar - δ) / (2 * T) ≤ (s : ℝ)}
    with hCdef
  have hCclosed : IsClosed C :=
    (isClosed_le continuous_subtype_val continuous_const).union
      (isClosed_le continuous_const continuous_subtype_val)
  have hKcomp : IsCompact (γ '' C) :=
    (hCclosed.isCompact).image γ.continuous
  have hPK : ϑ tstar ∉ γ '' C := by
    rintro ⟨s, hsC, hsE⟩
    have hγs : leafLoop p ϑ T s = τ 0 := by
      rw [hτ0]
      exact hsE
    by_cases hhalf : (s : ℝ) ≤ 1 / 2
    · rw [leafLoop, if_pos hhalf] at hγs
      exact hmiss _ 0 hγs
    · rw [leafLoop, if_neg hhalf] at hγs
      set v : ℝ := min 1 (2 - 2 * (s : ℝ)) * T with hvdef
      have hs1 := s.2.2
      have hv0 : 0 ≤ v := by
        have h1 : (0 : ℝ) ≤ min 1 (2 - 2 * (s : ℝ)) := le_min (by norm_num)
          (by linarith)
        positivity
      have hcross := leaf_cross_once hq hbigon hbigonH hϑ hτ
        (lt_of_lt_of_le ha hv0) (ha.trans htstar.1) hγs hτ0.symm
      have hvne : v ≠ tstar := by
        rcases hsC with hle | hge
        · have h2 : (tstar + δ) / T ≤ 2 - 2 * (s : ℝ) := by
            rw [div_le_iff₀ hT]
            have h3 : (tstar + δ) / (2 * T) ≤ 1 - (s : ℝ) := by linarith
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * T)] at h3
            linarith
          have h4 : (tstar + δ) / T ≤ min 1 (2 - 2 * (s : ℝ)) :=
            le_min (by rw [div_le_one hT]; linarith) h2
          have h5 : tstar + δ ≤ v := by
            rw [hvdef]
            calc tstar + δ = (tstar + δ) / T * T := by field_simp
              _ ≤ min 1 (2 - 2 * (s : ℝ)) * T :=
                mul_le_mul_of_nonneg_right h4 hT.le
          intro hE
          rw [hE] at h5
          linarith
        · have h2 : 2 - 2 * (s : ℝ) ≤ (tstar - δ) / T := by
            rw [le_div_iff₀ hT]
            have h3 : 1 - (s : ℝ) ≤ (tstar - δ) / (2 * T) := by linarith
            rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * T)] at h3
            linarith
          have h5 : v ≤ tstar - δ := by
            rw [hvdef]
            calc min 1 (2 - 2 * (s : ℝ)) * T ≤ (2 - 2 * (s : ℝ)) * T :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hT.le
              _ ≤ (tstar - δ) / T * T := mul_le_mul_of_nonneg_right h2 hT.le
              _ = tstar - δ := by field_simp
          intro hE
          rw [hE] at h5
          linarith
      exact hvne hcross.1
  obtain ⟨d₀, hd₀, hball⟩ := Metric.mem_nhds_iff.mp
    (hKcomp.isClosed.isOpen_compl.mem_nhds hPK)
  refine ⟨d₀, hd₀, ?_⟩
  intro s hsC hmem
  exact hball hmem (Set.mem_image_of_mem γ hsC)

/-- **Near-unit quotients avoid the slit**: two points within a quarter norm-radius of
a nonzero center have their quotient in the slit plane. -/
theorem ratio_near_one {A B d : ℂ} (hd : d ≠ 0)
    (hA : ‖A - d‖ < ‖d‖ / 4) (hB : ‖B - d‖ < ‖d‖ / 4) :
    A / B ∈ Complex.slitPlane := by
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hBlow : 3 / 4 * ‖d‖ < ‖B‖ := by
    have h1 : ‖d‖ - ‖B‖ ≤ ‖d - B‖ := norm_sub_norm_le d B
    rw [norm_sub_rev] at h1
    linarith
  have hBpos : 0 < ‖B‖ := by linarith
  have hBne : B ≠ 0 := norm_pos_iff.mp hBpos
  have hAB : ‖A - B‖ < ‖d‖ / 2 := by
    rw [show A - B = (A - d) - (B - d) from by ring]
    calc ‖(A - d) - (B - d)‖ ≤ ‖A - d‖ + ‖B - d‖ := norm_sub_le _ _
      _ < ‖d‖ / 2 := by linarith
  have hQ1 : ‖A / B - 1‖ < 2 / 3 := by
    rw [show A / B - 1 = (A - B) / B from by field_simp, norm_div,
      div_lt_iff₀ hBpos]
    nlinarith
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have habs := Complex.abs_re_le_norm (A / B - 1)
  have hre : (A / B).re = 1 + (A / B - 1).re := by
    simp [Complex.sub_re]
  rw [hre]
  have := abs_le.mp (le_of_lt (lt_of_le_of_lt habs hQ1))
  linarith [this.1]

set_option maxHeartbeats 400000 in
-- Heartbeats: the deep local-definition tower needs an enlarged elaboration budget.
/-- **The winding jump across a leaf crossing**: a competitor path joining the ends of
a vertical trajectory while missing an all-time transverse leaf through an interior
trajectory point forces, at some pair of nearby leaf probes, a nonzero winding of the
bundled loop about one of the probes. -/
theorem hjump_of_bigons {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False) :
    ∀ (ϑ : ℝ → ℂ) (a : ℝ) (hϑ : IsTrajOn q ϑ (Set.Ici a)) (ha : a < 0)
      (T : ℝ) (hT : 0 < T) (τ : ℝ → ℂ),
      IsTrajOn (fun z => -q z) τ Set.univ →
      ∀ tstar : ℝ, tstar ∈ Set.Ioo 0 T → τ 0 = ϑ tstar →
      ∀ (p : C(unitInterval, ℂ)), p 0 = ϑ 0 → ∀ hp1 : p 1 = ϑ T,
      (∀ s : unitInterval, 0 < (p s).im) →
      (∀ (s : unitInterval) (u : ℝ), p s ≠ τ u) →
      ∃ η : ℝ, 0 < η ∧
        (windingNumber (leafLoopC p ϑ T
            (hϑ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1) (τ η) ≠ 0 ∨
         windingNumber (leafLoopC p ϑ T
            (hϑ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1)
              (τ (-η)) ≠ 0) := by
  intro ϑ a hϑ ha T hT τ hτ tstar htstar hτ0 p hp0 hp1 _hpim hmiss
  set γ : C(unitInterval, ℂ) :=
    leafLoopC p ϑ T (hϑ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1 with hγdef
  have hγeval : ∀ t : unitInterval, γ t = leafLoop p ϑ T (t : ℝ) := fun t => rfl
  have hγcl : γ 0 = γ 1 :=
    leafLoop_closed p ϑ T (hϑ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1 hp0
  -- chart data at the crossing point
  have hts0 := htstar.1
  have htsT := htstar.2
  have htsIci : tstar ∈ Set.Ici a := le_of_lt (ha.trans hts0)
  obtain ⟨U, -, htsU, hUH, hUne, -⟩ := hϑ.chart tstar htsIci
  have hPim : 0 < (ϑ tstar).im := hUH htsU
  have hPq : q (ϑ tstar) ≠ 0 := hUne _ htsU
  obtain ⟨S, Φ, ρ₀, hρ₀, hSopen, hPS, hSH, hSne, hΦd, hΦinj, hΦsq, himg⟩ :=
    box_data hq hPim hPq
  set P : ℂ := ϑ tstar with hPdef
  have hdΦ : deriv Φ P ≠ 0 := by
    intro h0
    have h1 := hΦsq P hPS
    rw [h0] at h1
    exact hPq (by simpa using h1.symm)
  have hdΦn : 0 < ‖deriv Φ P‖ := norm_pos_iff.mpr hdΦ
  obtain ⟨δb, hδb, hdd⟩ := divided_diff_ball hSopen hΦd hPS (‖deriv Φ P‖ / 4)
    (by linarith)
  -- transverse development of the leaf
  have hτS : τ 0 ∈ S := by rw [hτ0]; exact hPS
  obtain ⟨η₀, hη₀, ε₁, hε₁, hleafdev⟩ := box_leaf_dev hSopen hΦd hΦsq hτ hτS
  -- window for the arc development
  set h₁ : ℝ := min (ρ₀ / 2) (min tstar (T - tstar) / 2) with hh₁def
  have hh₁ : 0 < h₁ := lt_min (by linarith) (by
    have h2 : 0 < min tstar (T - tstar) := lt_min hts0 (by linarith)
    linarith)
  have hh₁ρ : h₁ ≤ ρ₀ / 2 := min_le_left _ _
  have hh₁t : h₁ ≤ tstar / 2 := le_trans (min_le_right _ _) (by
    have h2 := min_le_left tstar (T - tstar)
    linarith)
  have hh₁T : h₁ ≤ (T - tstar) / 2 := le_trans (min_le_right _ _) (by
    have h2 := min_le_right tstar (T - tstar)
    linarith)
  have hdev : ∀ x : ℝ, |x| ≤ h₁ → Φ P + (x : ℂ) ∈ Φ '' S := by
    intro x hx
    refine himg (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    linarith
  obtain ⟨ε₀, hε₀, harcdev⟩ := box_arc_dev hSopen hΦd hΦinj hSH hSne hΦsq hϑ
    hh₁ (by linarith : a ≤ tstar - h₁) hPS hdev
  -- choice of the half-width of the crossing window
  have hϑcont : ContinuousAt ϑ tstar :=
    hϑ.cont.continuousAt (Ici_mem_nhds (ha.trans hts0))
  obtain ⟨δc, hδc, hδcball⟩ := Metric.eventually_nhds_iff.mp
    (hϑcont.eventually_mem (Metric.ball_mem_nhds P hδb))
  set δ : ℝ := min h₁ (δc / 2) with hδdef
  have hδpos : 0 < δ := lt_min hh₁ (by linarith)
  have hδh : δ ≤ h₁ := min_le_left _ _
  have hδT : tstar + δ < T := by linarith
  have hδ0 : δ < tstar := by linarith
  have hδball : ∀ x : ℝ, |x| ≤ δ → ϑ (tstar + x) ∈ Metric.ball P δb := by
    intro x hx
    refine hδcball ?_
    rw [Real.dist_eq, add_sub_cancel_left]
    have h2 : δ ≤ δc / 2 := min_le_right _ _
    linarith
  -- clearance off the window and the leaf-probe scale
  have hτcont : ContinuousAt τ 0 :=
    hτ.cont.continuousAt (by simp : Set.univ ∈ 𝓝 (0 : ℝ))
  obtain ⟨d₀, hd₀, hoff⟩ := jump_offwindow hq hbigon hbigonH hϑ ha hT hτ
    htstar hτ0 hp1 hmiss hδpos hδT hδ0
  rw [← hPdef] at hoff
  obtain ⟨η₁, hη₁, hτcball⟩ := Metric.eventually_nhds_iff.mp
    (hτcont.eventually_mem (Metric.ball_mem_nhds (τ 0) (lt_min hδb hd₀)))
  have hτball : ∀ u : ℝ, |u| < η₁ → τ u ∈ Metric.ball P (min δb d₀) := by
    intro u hu
    have h2 := hτcball (show dist u 0 < η₁ by rwa [Real.dist_eq, sub_zero])
    rwa [hτ0] at h2
  -- window endpoints in the loop parameter
  have hTne : T ≠ 0 := hT.ne'
  set a₁ : ℝ := 1 - (tstar + δ) / (2 * T) with ha₁def
  set a₂ : ℝ := 1 - (tstar - δ) / (2 * T) with ha₂def
  have hT2 : (0 : ℝ) < 2 * T := by linarith
  have ha₁half : 1 / 2 < a₁ := by
    rw [ha₁def]
    have h2 : (tstar + δ) / (2 * T) < 1 / 2 := by
      rw [div_lt_iff₀ hT2]
      linarith
    linarith
  have ha₂1 : a₂ < 1 := by
    rw [ha₂def]
    have h2 : 0 < (tstar - δ) / (2 * T) := div_pos (by linarith) hT2
    linarith
  have hgap : a₂ - a₁ = δ / T := by
    rw [ha₁def, ha₂def]
    field_simp
    ring
  have ha₁₂ : a₁ < a₂ := by
    have h2 : 0 < δ / T := div_pos hδpos hT
    linarith
  have ha₁0 : 0 ≤ a₁ := by linarith
  have hxa₁ : (2 - 2 * a₁) * T = tstar + δ := by
    rw [ha₁def]
    field_simp
    ring
  have hxa₂ : (2 - 2 * a₂) * T = tstar - δ := by
    rw [ha₂def]
    field_simp
    ring
  -- signed leaf parameter and window image points
  set c : ℝ := -ε₁ with hcdef
  have hcpm : c = 1 ∨ c = -1 := by
    rcases hε₁ with h | h
    · exact Or.inr (by rw [hcdef, h])
    · exact Or.inl (by rw [hcdef, h]; norm_num)
  have hcne : c ≠ 0 := by rcases hcpm with h | h <;> rw [h] <;> norm_num
  have hε₁c : ε₁ = -c := by rw [hcdef]; ring
  have hε₀ne : ε₀ ≠ 0 := by rcases hε₀ with h | h <;> rw [h] <;> norm_num
  set g₁ : ℂ := ϑ (tstar + δ) with hg₁def
  set g₂ : ℂ := ϑ (tstar - δ) with hg₂def
  have habsδ : |δ| ≤ h₁ := by rw [abs_of_pos hδpos]; exact hδh
  have habsδ' : |(-δ)| ≤ h₁ := by rw [abs_neg, abs_of_pos hδpos]; exact hδh
  have hg₁dat := harcdev δ habsδ
  have hg₂dat := harcdev (-δ) habsδ'
  rw [show tstar + -δ = tstar - δ from by ring] at hg₂dat
  have hg₁Φ : Φ g₁ = Φ P + (ε₀ : ℂ) * (δ : ℂ) := hg₁dat.2
  have hg₂Φ : Φ g₂ = Φ P + (ε₀ : ℂ) * ((-δ : ℝ) : ℂ) := hg₂dat.2
  have hg₁P : g₁ ≠ P := by
    intro hE
    rw [hE] at hg₁Φ
    have h2 : ((ε₀ * δ : ℝ) : ℂ) = 0 := by push_cast; linear_combination -hg₁Φ
    exact mul_ne_zero hε₀ne hδpos.ne' (by exact_mod_cast h2)
  have hg₂P : g₂ ≠ P := by
    intro hE
    rw [hE] at hg₂Φ
    push_cast at hg₂Φ
    have h2 : ((ε₀ * -δ : ℝ) : ℂ) = 0 := by push_cast; linear_combination -hg₂Φ
    exact mul_ne_zero hε₀ne (neg_ne_zero.mpr hδpos.ne') (by exact_mod_cast h2)
  -- the exponential main factor and the increment expression
  set Mv : ℝ → ℝ → ℂ := fun ξ t =>
    ((ξ : ℂ) - ((c * t : ℝ) : ℂ) * Complex.I)
      / ((ξ : ℂ) + ((c * t : ℝ) : ℂ) * Complex.I) with hMvdef
  set E : ℝ → ℂ := fun t =>
    (-(2 * ((Complex.arg (((ε₀ * -δ : ℝ) : ℂ)
          + ((c * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I
      + (2 * ((Complex.arg (((ε₀ * δ : ℝ) : ℂ)
          + ((c * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I)
    + (Complex.log (((g₂ - τ t) / (g₂ - τ (-t))) / Mv (ε₀ * -δ) t)
        - Complex.log (((g₁ - τ t) / (g₁ - τ (-t))) / Mv (ε₀ * δ) t))
    + (Complex.log ((g₁ - τ t) / (g₁ - τ (-t)))
        - Complex.log ((g₂ - τ t) / (g₂ - τ (-t)))) with hEdef
  -- the per-probe winding identity
  have hkey : ∀ η : ℝ, 0 < η → η ≤ η₀ → η < η₁ →
      2 * (Real.pi : ℂ) * Complex.I *
        ((windingNumber γ (τ η) : ℂ) - (windingNumber γ (τ (-η)) : ℂ)) = E η := by
    intro η hη hηa hηb
    have hηne : η ≠ 0 := hη.ne'
    have hηnne : -η ≠ 0 := neg_ne_zero.mpr hηne
    -- probe developments and positions
    have hprp := hleafdev η (by rw [abs_of_pos hη]; exact hηa)
    have hprm := hleafdev (-η) (by rw [abs_neg, abs_of_pos hη]; exact hηa)
    have hzpF : Φ (τ η) = Φ P - Complex.I * (ε₁ : ℂ) * (η : ℂ) := by
      have h2 := hprp.2
      rwa [hτ0] at h2
    have hzmF : Φ (τ (-η)) = Φ P - Complex.I * (ε₁ : ℂ) * ((-η : ℝ) : ℂ) := by
      have h2 := hprm.2
      rwa [hτ0] at h2
    have hzpb : τ η ∈ Metric.ball P δb :=
      Metric.ball_subset_ball (min_le_left _ _)
        (hτball η (by rwa [abs_of_pos hη]))
    have hzmb : τ (-η) ∈ Metric.ball P δb :=
      Metric.ball_subset_ball (min_le_left _ _)
        (hτball (-η) (by rwa [abs_neg, abs_of_pos hη]))
    have hsegb : segment ℝ (τ (-η)) (τ η) ⊆ Metric.ball P d₀ := by
      refine (convex_ball P d₀).segment_subset ?_ ?_
      · exact Metric.ball_subset_ball (min_le_right _ _)
          (hτball (-η) (by rwa [abs_neg, abs_of_pos hη]))
      · exact Metric.ball_subset_ball (min_le_right _ _)
          (hτball η (by rwa [abs_of_pos hη]))
    -- loop avoidance of the probes
    have hpp : ∀ t : unitInterval, γ t ≠ τ η := by
      intro t
      rw [hγeval t]
      exact jump_avoid hq hbigon hbigonH hϑ ha hT hτ htstar hτ0 hmiss hηne t
    have hmm : ∀ t : unitInterval, γ t ≠ τ (-η) := by
      intro t
      rw [hγeval t]
      exact jump_avoid hq hbigon hbigonH hϑ ha hT hτ htstar hτ0 hmiss hηnne t
    have hppz : ∀ t : unitInterval, γ t - τ η ≠ 0 := fun t => sub_ne_zero.mpr (hpp t)
    have hmmz : ∀ t : unitInterval, γ t - τ (-η) ≠ 0 :=
      fun t => sub_ne_zero.mpr (hmm t)
    -- the ratio curve and its lift
    set r : C(unitInterval, ℂ) :=
      ⟨fun t => (γ t - τ η) / (γ t - τ (-η)),
        ((map_continuous γ).sub continuous_const).div
          ((map_continuous γ).sub continuous_const) fun t => hmmz t⟩ with hrdef
    have hr : ∀ t : unitInterval, r t = (γ t - τ η) / (γ t - τ (-η)) := fun t => rfl
    have hwr := winding_sub_eq_ratio hγcl hpp hmm r hr
    have hrne : ∀ t : unitInterval, r t ≠ 0 := fun t => div_ne_zero (hppz t) (hmmz t)
    have hshiftne : ∀ t : unitInterval, shiftedCurve r 0 t ≠ 0 := by
      intro t
      have h2 : shiftedCurve r 0 t = r t := by simp [shiftedCurve]
      rw [h2]
      exact hrne t
    obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve r 0) hshiftne
    have hrcl : r 0 = r 1 := by rw [hr 0, hr 1, hγcl]
    have hspec := windingNumber_spec hrcl hrne hL
    -- transfer to the real parameter
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
    have hrreq : ∀ u : ℝ, rr u
        = (γ (Set.projIcc 0 1 zero_le_one u) - τ η)
          / (γ (Set.projIcc 0 1 zero_le_one u) - τ (-η)) := by
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
    -- slit-plane pieces off the window
    have hslitOff : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → (u ≤ a₁ ∨ a₂ ≤ u) →
        rr u ∈ Complex.slitPlane := by
      intro u hu01 hcase
      have htc : ((Set.projIcc 0 1 zero_le_one u : unitInterval) : ℝ) = u :=
        hproj u hu01
      have hoffm := hoff (Set.projIcc 0 1 zero_le_one u) (by rw [htc]; exact hcase)
      rw [← hγeval] at hoffm
      have hseg : γ (Set.projIcc 0 1 zero_le_one u) ∉ segment ℝ (τ (-η)) (τ η) :=
        fun hsg => hoffm (hsegb hsg)
      have h3 := ratio_slitPlane (w := γ (Set.projIcc 0 1 zero_le_one u))
        (zp := τ η) (zm := τ (-η)) hseg
      rw [hrreq u]
      exact h3
    have hpiece₁ : Lr a₁ - Lr 0 = Complex.log (rr a₁) - Complex.log (rr 0) :=
      loglift_increment_slit ha₁0 hLrc.continuousOn hrrc.continuousOn
        (fun u _ => hLrlift u)
        (fun u hu => hslitOff u ⟨hu.1, le_trans hu.2 (by linarith)⟩ (Or.inl hu.2))
    have hpiece₂ : Lr 1 - Lr a₂ = Complex.log (rr 1) - Complex.log (rr a₂) :=
      loglift_increment_slit ha₂1.le hLrc.continuousOn hrrc.continuousOn
        (fun u _ => hLrlift u)
        (fun u hu => hslitOff u ⟨le_trans (by linarith) hu.1, hu.2⟩ (Or.inr hu.1))
    -- the crossing window: chart development of the loop
    set xf : ℝ → ℝ := fun u => (2 - 2 * u) * T - tstar with hxfdef
    have hxf₁ : xf a₁ = δ := by
      rw [hxfdef]
      simp only
      linarith
    have hxf₂ : xf a₂ = -δ := by
      rw [hxfdef]
      simp only
      linarith
    have hxfabs : ∀ u ∈ Set.Icc a₁ a₂, |xf u| ≤ δ := by
      intro u hu
      rw [hxfdef]
      simp only
      rw [abs_le]
      constructor
      · nlinarith [hxa₂, mul_nonneg (sub_nonneg.mpr hu.2) hT.le]
      · nlinarith [hxa₁, mul_nonneg (sub_nonneg.mpr hu.1) hT.le]
    have hwinS : ∀ u ∈ Set.Icc a₁ a₂,
        γ (Set.projIcc 0 1 zero_le_one u) = ϑ (tstar + xf u) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := hu
      have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have htc := hproj u hu01
      rw [hγeval, htc, leafLoop_second_half p ϑ T (not_le.mpr (by linarith))
        (by linarith)]
      congr 1
      rw [hxfdef]
      simp only
      ring
    have hΦwin : ∀ u ∈ Set.Icc a₁ a₂,
        Φ (γ (Set.projIcc 0 1 zero_le_one u))
          = Φ P + (ε₀ : ℂ) * ((xf u : ℝ) : ℂ) := by
      intro u hu
      rw [hwinS u hu]
      exact (harcdev (xf u) (le_trans (hxfabs u hu) hδh)).2
    have hwinb : ∀ u ∈ Set.Icc a₁ a₂,
        γ (Set.projIcc 0 1 zero_le_one u) ∈ Metric.ball P δb := by
      intro u hu
      rw [hwinS u hu]
      exact hδball (xf u) (hxfabs u hu)
    -- numerator and denominator identities on the window
    have hcη : c * η ≠ 0 := mul_ne_zero hcne hηne
    have hnum : ∀ u ∈ Set.Icc a₁ a₂,
        Φ (γ (Set.projIcc 0 1 zero_le_one u)) - Φ (τ η)
          = ((ε₀ * xf u : ℝ) : ℂ) - ((c * η : ℝ) : ℂ) * Complex.I := by
      intro u hu
      rw [hΦwin u hu, hzpF, hε₁c]
      push_cast
      ring
    have hden : ∀ u ∈ Set.Icc a₁ a₂,
        Φ (γ (Set.projIcc 0 1 zero_le_one u)) - Φ (τ (-η))
          = ((ε₀ * xf u : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I := by
      intro u hu
      rw [hΦwin u hu, hzmF, hε₁c]
      push_cast
      ring
    have hnumne : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) - ((c * η : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro ξ h0
      have h2 := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.zero_im, mul_zero,
        mul_one, zero_sub, add_zero] at h2
      exact hcη (by linarith)
    have hdenne : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro ξ h0
      have h2 := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.zero_im, mul_zero,
        mul_one, zero_add, add_zero] at h2
      exact hcη (by linarith)
    have hMvne : ∀ ξ : ℝ, Mv ξ η ≠ 0 := by
      intro ξ
      rw [hMvdef]
      simp only
      exact div_ne_zero (hnumne ξ) (hdenne ξ)
    -- the correction quotient and its slit-plane bound
    set Qf : ℝ → ℂ := fun u => rr u / Mv (ε₀ * xf u) η with hQfdef
    have hfact : ∀ u ∈ Set.Icc a₁ a₂, rr u = Mv (ε₀ * xf u) η * Qf u := by
      intro u _
      rw [hQfdef]
      simp only
      rw [mul_comm, div_mul_cancel₀ _ (hMvne _)]
    have hQslit : ∀ u ∈ Set.Icc a₁ a₂, Qf u ∈ Complex.slitPlane := by
      intro u hu
      have hFnep : Φ (γ (Set.projIcc 0 1 zero_le_one u)) - Φ (τ η) ≠ 0 := by
        rw [hnum u hu]
        exact hnumne _
      have hFnem : Φ (γ (Set.projIcc 0 1 zero_le_one u)) - Φ (τ (-η)) ≠ 0 := by
        rw [hden u hu]
        exact hdenne _
      have hnep := hppz (Set.projIcc 0 1 zero_le_one u)
      have hnem := hmmz (Set.projIcc 0 1 zero_le_one u)
      have halg : Qf u = ((Φ (γ (Set.projIcc 0 1 zero_le_one u)) - Φ (τ (-η)))
            / (γ (Set.projIcc 0 1 zero_le_one u) - τ (-η)))
          / ((Φ (γ (Set.projIcc 0 1 zero_le_one u)) - Φ (τ η))
            / (γ (Set.projIcc 0 1 zero_le_one u) - τ η)) := by
        rw [hQfdef]
        simp only
        rw [hrreq u, hMvdef]
        simp only
        rw [← hnum u hu, ← hden u hu]
        field_simp
      rw [halg]
      exact ratio_near_one hdΦ
        (hdd _ _ (hwinb u hu) hzmb (hmm _)) (hdd _ _ (hwinb u hu) hzpb (hpp _))
    -- the exponential lift on the window
    set L₁ : ℝ → ℂ := fun u =>
      -(2 * ((Complex.arg (((ε₀ * xf u : ℝ) : ℂ)
          + ((c * η : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I with hL₁def
    have hlift₁ : ∀ u ∈ Set.Icc a₁ a₂, Complex.exp (L₁ u) = Mv (ε₀ * xf u) η := by
      intro u _
      rw [hL₁def, hMvdef]
      simp only
      exact (conj_pair_exp hcη).symm
    have hL₁c : ContinuousOn L₁ (Set.Icc a₁ a₂) := by
      have hinner : Continuous fun u : ℝ =>
          ((ε₀ * xf u : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I := by
        rw [hxfdef]
        fun_prop
      have hargc : ∀ u : ℝ, ContinuousAt (fun v : ℝ =>
          Complex.arg (((ε₀ * xf v : ℝ) : ℂ)
            + ((c * η : ℝ) : ℂ) * Complex.I)) u := by
        intro u
        refine ContinuousAt.comp (Complex.continuousAt_arg ?_) hinner.continuousAt
        refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
          zero_add, add_zero]
        exact hcη
      rw [hL₁def]
      refine ContinuousOn.mul (ContinuousOn.neg ?_) continuousOn_const
      refine ContinuousOn.mul continuousOn_const ?_
      exact (Complex.continuous_ofReal.comp
        (continuous_iff_continuousAt.mpr hargc)).continuousOn
    -- the correction lift on the window
    have hMc : ContinuousOn (fun u : ℝ => Mv (ε₀ * xf u) η) (Set.Icc a₁ a₂) := by
      rw [hMvdef, hxfdef]
      simp only
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro u _
        exact hdenne _
    have hQfc : ContinuousOn Qf (Set.Icc a₁ a₂) := by
      rw [hQfdef]
      exact ContinuousOn.div hrrc.continuousOn hMc fun u _ => hMvne _
    have hlift₂ : ∀ u ∈ Set.Icc a₁ a₂, Complex.exp (Complex.log (Qf u)) = Qf u :=
      fun u hu => Complex.exp_log (Complex.slitPlane_ne_zero (hQslit u hu))
    have hL₂c : ContinuousOn (fun u => Complex.log (Qf u)) (Set.Icc a₁ a₂) := by
      intro u hu
      exact (continuousAt_clog (hQslit u hu)).comp_continuousWithinAt (hQfc u hu)
    have hpiece₃ : Lr a₂ - Lr a₁
        = (L₁ a₂ - L₁ a₁) + (Complex.log (Qf a₂) - Complex.log (Qf a₁)) :=
      loglift_increment_mul ha₁₂.le hLrc.continuousOn hL₁c hL₂c
        (fun u hu => by rw [hLrlift u]; exact hfact u hu) hlift₁ hlift₂
    -- assembly of the increment identity
    have hZ : (windingNumber r 0 : ℂ)
        = (windingNumber γ (τ η) : ℂ) - (windingNumber γ (τ (-η)) : ℂ) := by
      rw [← hwr]
      push_cast
      ring
    have htot : 2 * (Real.pi : ℂ) * Complex.I *
        ((windingNumber γ (τ η) : ℂ) - (windingNumber γ (τ (-η)) : ℂ))
        = (Complex.log (rr 1) - Complex.log (rr a₂))
          + ((L₁ a₂ - L₁ a₁) + (Complex.log (Qf a₂) - Complex.log (Qf a₁)))
          + (Complex.log (rr a₁) - Complex.log (rr 0)) := by
      rw [← hZ, ← hspecr, ← hpiece₁, ← hpiece₂, ← hpiece₃]
      ring
    have hrr10 : rr 1 = rr 0 := by
      rw [hrreq 1, hrreq 0, hpr0, hpr1, hγcl]
    have hrra₁ : rr a₁ = (g₁ - τ η) / (g₁ - τ (-η)) := by
      rw [hrreq a₁, hwinS a₁ (Set.left_mem_Icc.mpr ha₁₂.le), hxf₁, ← hg₁def]
    have hrra₂ : rr a₂ = (g₂ - τ η) / (g₂ - τ (-η)) := by
      rw [hrreq a₂, hwinS a₂ (Set.right_mem_Icc.mpr ha₁₂.le), hxf₂,
        show tstar + -δ = tstar - δ from by ring, ← hg₂def]
    have hL₁ends : L₁ a₂ - L₁ a₁
        = -(2 * ((Complex.arg (((ε₀ * -δ : ℝ) : ℂ)
              + ((c * η : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I
          + (2 * ((Complex.arg (((ε₀ * δ : ℝ) : ℂ)
              + ((c * η : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I := by
      rw [hL₁def]
      simp only
      rw [hxf₁, hxf₂]
      ring
    have hQa₁ : Qf a₁ = ((g₁ - τ η) / (g₁ - τ (-η))) / Mv (ε₀ * δ) η := by
      rw [hQfdef]
      simp only
      rw [hrra₁, hxf₁]
    have hQa₂ : Qf a₂ = ((g₂ - τ η) / (g₂ - τ (-η))) / Mv (ε₀ * -δ) η := by
      rw [hQfdef]
      simp only
      rw [hrra₂, hxf₂]
    rw [htot, hrr10, hEdef]
    simp only
    rw [hL₁ends, hQa₁, hQa₂, hrra₁, hrra₂]
    ring
  -- the limit of the increment expression
  have hcastl : Filter.Tendsto (fun t : ℝ => ((c * t : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h1 : Continuous fun t : ℝ => ((c * t : ℝ) : ℂ) := by fun_prop
    have h2 := (h1.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h2
  have hτpl : Filter.Tendsto (fun t : ℝ => τ t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 P) := by
    have h1 : Filter.Tendsto τ (𝓝 0) (𝓝 (τ 0)) := hτcont
    rw [hτ0] at h1
    exact h1.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hτml : Filter.Tendsto (fun t : ℝ => τ (-t))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 P) := by
    have hneg : Filter.Tendsto (fun t : ℝ => -t)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      have h2 := (continuous_neg.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h2
    have h1 : Filter.Tendsto τ (𝓝 0) (𝓝 P) := by
      have h2 : Filter.Tendsto τ (𝓝 0) (𝓝 (τ 0)) := hτcont
      rwa [hτ0] at h2
    exact h1.comp hneg
  have hRlim : ∀ g : ℂ, g ≠ P → Filter.Tendsto
      (fun t : ℝ => (g - τ t) / (g - τ (-t)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    intro g hg
    have hgP : g - P ≠ 0 := sub_ne_zero.mpr hg
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
  have hQlim : ∀ (g : ℂ), g ≠ P → ∀ ξ : ℝ, ξ ≠ 0 → Filter.Tendsto
      (fun t : ℝ => ((g - τ t) / (g - τ (-t))) / Mv ξ t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    intro g hg ξ hξ
    have h2 := (hRlim g hg).div (hMlim ξ hξ) one_ne_zero
    rwa [div_one] at h2
  -- endpoint argument limits
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
  have hFlim : Filter.Tendsto (fun t : ℝ =>
      -(2 * ((Complex.arg (((ε₀ * -δ : ℝ) : ℂ)
            + ((c * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I
        + (2 * ((Complex.arg (((ε₀ * δ : ℝ) : ℂ)
            + ((c * t : ℝ) : ℂ) * Complex.I) : ℝ) : ℂ)) * Complex.I)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (((ε₀ * ε₁ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) := by
    rcases hε₀ with hε | hε
    · have hA₁ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((ε₀ * δ : ℝ) : ℂ) + ((c * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
        simp only [hε, one_mul]
        exact arg_limit_pos hδpos
      have hA₂ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((ε₀ * -δ : ℝ) : ℂ) + ((c * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (c * Real.pi)) := by
        simp only [hε, one_mul, Complex.ofReal_neg]
        exact arg_limit_neg hδpos hcpm
      have h2 := (hofrn hA₂).add (hofr hA₁)
      have h3 : -(2 * ((c * Real.pi : ℝ) : ℂ)) * Complex.I
            + (2 * ((0 : ℝ) : ℂ)) * Complex.I
          = ((ε₀ * ε₁ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [hε, hε₁c]
        push_cast
        ring
      rw [← h3]
      exact h2
    · have hA₁ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((ε₀ * δ : ℝ) : ℂ) + ((c * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (c * Real.pi)) := by
        simp only [hε, neg_one_mul, Complex.ofReal_neg]
        exact arg_limit_neg hδpos hcpm
      have hA₂ : Filter.Tendsto (fun t : ℝ =>
          Complex.arg (((ε₀ * -δ : ℝ) : ℂ) + ((c * t : ℝ) : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
        simp only [hε, neg_one_mul, neg_neg]
        exact arg_limit_pos hδpos
      have h2 := (hofrn hA₂).add (hofr hA₁)
      have h3 : -(2 * ((0 : ℝ) : ℂ)) * Complex.I
            + (2 * ((c * Real.pi : ℝ) : ℂ)) * Complex.I
          = ((ε₀ * ε₁ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [hε, hε₁c]
        push_cast
        ring
      rw [← h3]
      exact h2
  have hGlim : Filter.Tendsto (fun t : ℝ =>
      Complex.log (((g₂ - τ t) / (g₂ - τ (-t))) / Mv (ε₀ * -δ) t)
        - Complex.log (((g₁ - τ t) / (g₁ - τ (-t))) / Mv (ε₀ * δ) t))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h2 := (hlogc (hQlim g₂ hg₂P (ε₀ * -δ)
        (mul_ne_zero hε₀ne (neg_ne_zero.mpr hδpos.ne')))).sub
      (hlogc (hQlim g₁ hg₁P (ε₀ * δ) (mul_ne_zero hε₀ne hδpos.ne')))
    simpa using h2
  have hHlim : Filter.Tendsto (fun t : ℝ =>
      Complex.log ((g₁ - τ t) / (g₁ - τ (-t)))
        - Complex.log ((g₂ - τ t) / (g₂ - τ (-t))))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h2 := (hlogc (hRlim g₁ hg₁P)).sub (hlogc (hRlim g₂ hg₂P))
    simpa using h2
  have hElim : Filter.Tendsto E (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (((ε₀ * ε₁ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) := by
    rw [hEdef]
    have h2 := (hFlim.add hGlim).add hHlim
    simpa using h2
  -- selection of the probe height and conclusion
  have hev₀ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  have hevη₀ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < η₀ :=
    nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hη₀)
  have hevη₁ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < η₁ :=
    nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hη₁)
  have hevnear := Metric.tendsto_nhds.mp hElim 1 one_pos
  obtain ⟨η, hη0, hηa, hηb, hηd⟩ :=
    (hev₀.and (hevη₀.and (hevη₁.and hevnear))).exists
  refine ⟨η, hη0, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hWp, hWm⟩ := hcon
  have hid := hkey η hη0 hηa.le hηb
  rw [hWp, hWm] at hid
  simp only [Int.cast_zero, sub_zero, mul_zero] at hid
  rw [← hid, dist_eq_norm, zero_sub, norm_neg] at hηd
  have h4 : |ε₀ * ε₁| = 1 := by
    rcases hε₀ with h | h <;> rcases hε₁ with h' | h' <;> rw [h, h'] <;> norm_num
  have h5 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have h3 : ‖((ε₀ * ε₁ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖
      = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, h4, one_mul, h5]
  rw [h3] at hηd
  linarith [Real.pi_gt_three]

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Leaf.Corridors

/-!
# The bigon exclusion principles

The discharge pack of the rounded-loop data, the affine certificate along a leaf, the
nonnegative-winding principle, and the exclusion of monogons and bigons in either
chirality.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **A natural chart image is open**: a holomorphic map with nonvanishing derivative
on an open set has open image. -/
theorem image_open_of_deriv_ne {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦne : ∀ z ∈ S, deriv Φ z ≠ 0) :
    IsOpen (Φ '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro ζ ⟨z, hzS, rfl⟩
  have han : AnalyticAt ℂ Φ z := (hΦd.analyticOnNhd hS) z hzS
  have hstrict : HasStrictDerivAt Φ (deriv Φ z) z :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  rw [← hstrict.map_nhds_eq (hΦne z hzS)]
  exact Filter.image_mem_map (hS.mem_nhds hzS)

/-- **Uniform ball margin**: a compact subset of an open set admits a uniform radius
whose balls about its points stay inside the open set. -/
theorem chart_margin {U : Set ℂ} (hU : IsOpen U) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ m : ℝ, 0 < m ∧ ∀ ζ ∈ K, Metric.ball ζ m ⊆ U := by
  obtain ⟨m, hm, hth⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨m, hm, fun ζ hζ => subset_trans (fun y hy => ?_) hth⟩
  rw [Metric.mem_thickening_iff]
  exact ⟨ζ, hζ, hy⟩

/-- **Transverse crossing of a fixed chart**: an all-time transverse leaf meeting a
natural chart whose image has horizontal margins develops affinely across the whole
margin window, staying in the chart. -/
theorem leaf_cross_chart {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ w ∈ S, q w ≠ 0)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -(-q w))
    {σ : ℝ → ℂ} (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    {t h : ℝ} (hh : 0 < h) (htS : σ t ∈ S)
    (hdev : ∀ x : ℝ, |x| ≤ h → Φ (σ t) + (x : ℂ) ∈ Φ '' S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x : ℝ, |x| ≤ h →
      σ (t + x) ∈ S ∧ Φ (σ (t + x)) = Φ (σ t) + (ε : ℂ) * (x : ℂ) :=
  box_arc_dev hS hΦd hΦinj hSH (fun w hw => neg_ne_zero.mpr (hSne w hw))
    hΦsq (traj_mono hσ (Set.subset_univ (Set.Ici (t - h)))) hh le_rfl htS hdev

/-- **Chart inverse continuity at a point**: for an injective holomorphic map with
nonvanishing derivative, chart-value closeness to the value at an interior point
forces plane closeness, uniformly over the whole open set. -/
theorem chart_preimage_near_open {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    {x : ℂ} (hx : x ∈ S) (hΦne : deriv Φ x ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ S, dist (Φ y) (Φ x) < δ → dist y x < r := by
  have han : AnalyticAt ℂ Φ x := (hΦd.analyticOnNhd hS) x hx
  have hstrict : HasStrictDerivAt Φ (deriv Φ x) x :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  have hB : S ∩ Metric.ball x r ∈ 𝓝 x :=
    Filter.inter_mem (hS.mem_nhds hx) (Metric.ball_mem_nhds x hr)
  have himg : Φ '' (S ∩ Metric.ball x r) ∈ 𝓝 (Φ x) := by
    rw [← hstrict.map_nhds_eq hΦne]
    exact Filter.image_mem_map hB
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨δ, hδ, fun y hyS hdist => ?_⟩
  obtain ⟨z, hzB, hzy⟩ := hball (Metric.mem_ball.mpr hdist)
  rw [← hΦinj hzB.1 hyS hzy]
  exact Metric.mem_ball.mp hzB.2

/-- **Corridor crossing of one chart**: a leaf entering a natural chart at a purely
imaginary offset from the base leaf's entry exits at the same offset from the base
leaf's exit, tracked in the chart throughout. -/
theorem corridor_cross {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V) (hΨinj : Set.InjOn Ψ V)
    (hVH : V ⊆ {z : ℂ | 0 < z.im}) (hVne : ∀ w ∈ V, q w ≠ 0)
    (hΨsq : ∀ x ∈ V, deriv Ψ x ^ 2 = -(-q x))
    {τb σ : ℝ → ℂ}
    (hτb : IsTrajOn (fun z => -q z) τb Set.univ)
    (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    {α β : ℝ} (hαβ : α < β)
    (htrk : ∀ w ∈ Set.Icc α β, τb w ∈ V)
    {m : ℝ} (hmarg : Metric.ball (Ψ (τb α)) m ⊆ Ψ '' V)
    (hmesh : β - α < m / 2)
    {d w₀ : ℝ} (hd : |d| < m / 2) (hw₀ : σ w₀ ∈ V)
    (hoff : Ψ (σ w₀) = Ψ (τb α) + Complex.I * (d : ℂ)) :
    ∃ w₁ : ℝ, σ w₁ ∈ V ∧ Ψ (σ w₁) = Ψ (τb β) + Complex.I * (d : ℂ) ∧
      ∀ w ∈ Set.uIcc w₀ w₁, σ w ∈ V := by
  obtain ⟨εb, hεb, hbase⟩ := traj_ambient_affine hV hΨd hΨsq hτb hαβ.le
    (Set.subset_univ _) htrk
  have hβdev : Ψ (τb β) = Ψ (τb α) + (εb : ℂ) * ((β - α : ℝ) : ℂ) :=
    hbase β (Set.right_mem_Icc.mpr hαβ.le)
  have hdev : ∀ x : ℝ, |x| ≤ β - α → Ψ (σ w₀) + (x : ℂ) ∈ Ψ '' V := by
    intro x hx
    refine hmarg (Metric.mem_ball.mpr ?_)
    rw [hoff, dist_eq_norm]
    have h1 : Ψ (τb α) + Complex.I * (d : ℂ) + (x : ℂ) - Ψ (τb α)
        = Complex.I * (d : ℂ) + (x : ℂ) := by ring
    rw [h1]
    calc ‖Complex.I * (d : ℂ) + (x : ℂ)‖
        ≤ ‖Complex.I * (d : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ = |d| + |x| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ < m := by linarith
  obtain ⟨ε, hε, hcross⟩ := leaf_cross_chart hV hΨd hΨinj hVH hVne hΨsq hσ
    (by linarith : 0 < β - α) hw₀ hdev
  have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεbabs : |εb| = 1 := by rcases hεb with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  set xs : ℝ := ε * εb * (β - α) with hxsdef
  have hxsabs : |xs| ≤ β - α := by
    rw [hxsdef, abs_mul, abs_mul, hεabs, hεbabs]
    rw [abs_of_pos (by linarith : (0 : ℝ) < β - α)]
    norm_num
  obtain ⟨hmem, hval⟩ := hcross xs hxsabs
  refine ⟨w₀ + xs, hmem, ?_, ?_⟩
  · rw [hval, hoff, hβdev, hxsdef]
    push_cast
    have h2 : (ε : ℂ) * ((ε : ℂ) * (εb : ℂ) * ((β : ℂ) - (α : ℂ)))
        = ((ε * ε : ℝ) : ℂ) * (εb : ℂ) * ((β : ℂ) - (α : ℂ)) := by
      push_cast
      ring
    rw [h2, hεsq]
    push_cast
    ring
  · intro w hw
    have hwd : |w - w₀| ≤ β - α := by
      rw [Set.uIcc_eq_union] at hw
      rcases hw with h | h
      · rw [abs_le]
        constructor
        · have := h.1
          have h3 := abs_le.mp hxsabs
          linarith [h3.1]
        · have := h.2
          have h3 := abs_le.mp hxsabs
          linarith [h3.2]
      · rw [abs_le]
        constructor
        · have := h.1
          have h3 := abs_le.mp hxsabs
          linarith [h3.1]
        · have := h.2
          have h3 := abs_le.mp hxsabs
          linarith [h3.2]
    have h4 := (hcross (w - w₀) hwd).1
    rwa [show w₀ + (w - w₀) = w from by ring] at h4

/-- **Offset transfer at a node**: across a chart change on a ball inside the overlap,
a purely imaginary chart offset from the node transforms by the branch sign of the
chart pair, a datum of the node alone. -/
theorem corridor_node {Ψ₁ Ψ₂ : ℂ → ℂ} {V₁ V₂ : Set ℂ}
    (hΨd₁ : DifferentiableOn ℂ Ψ₁ V₁) (hΨd₂ : DifferentiableOn ℂ Ψ₂ V₂)
    (hsq : ∀ z ∈ V₁ ∩ V₂, deriv Ψ₂ z ^ 2 = deriv Ψ₁ z ^ 2)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ V₁ ∩ V₂) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ y ∈ Metric.ball x r, ∀ d : ℝ,
      Ψ₁ y = Ψ₁ x + Complex.I * (d : ℂ) →
      Ψ₂ y = Ψ₂ x + Complex.I * ((s * d : ℝ) : ℂ) := by
  have hxmem : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  rcases open_branch_classification Metric.isOpen_ball
    (convex_ball x r).isPreconnected hxmem
    (hΨd₁.mono fun z hz => (hball hz).1)
    (hΨd₂.mono fun z hz => (hball hz).2)
    (fun z hz => hsq z (hball hz)) with hb | hb
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro y hy d hΨ₁y
    rw [hb y hy, hΨ₁y]
    push_cast
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro y hy d hΨ₁y
    rw [hb y hy, hΨ₁y]
    push_cast
    ring

/-- **Central alignment of a leaf point**: a leaf visiting the inner ball of a
margined chart develops within the chart to a point on the central vertical line at
its own height. -/
theorem leaf_align {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V) (hΨinj : Set.InjOn Ψ V)
    (hVH : V ⊆ {z : ℂ | 0 < z.im}) (hVne : ∀ w ∈ V, q w ≠ 0)
    (hΨsq : ∀ x ∈ V, deriv Ψ x ^ 2 = -(-q x))
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψ '' V)
    {σ : ℝ → ℂ} (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    {w : ℝ} (hwV : σ w ∈ V) (hwb : Ψ (σ w) ∈ Metric.ball c₀ R) :
    ∃ u : ℝ, σ u ∈ V ∧
      Ψ (σ u) = (c₀.re : ℂ) + ((Ψ (σ w)).im : ℝ) * Complex.I := by
  have hnorm : ‖Ψ (σ w) - c₀‖ < R := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hwb
  set x₀ : ℝ := c₀.re - (Ψ (σ w)).re with hx₀def
  have hx₀ : |x₀| < R := by
    rw [hx₀def, abs_sub_comm]
    calc |(Ψ (σ w)).re - c₀.re| = |(Ψ (σ w) - c₀).re| := by rw [Complex.sub_re]
      _ ≤ ‖Ψ (σ w) - c₀‖ := Complex.abs_re_le_norm _
      _ < R := hnorm
  have hdev : ∀ x : ℝ, |x| ≤ R → Ψ (σ w) + (x : ℂ) ∈ Ψ '' V := by
    intro x hx
    refine hmarg (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm]
    calc ‖Ψ (σ w) + (x : ℂ) - c₀‖ ≤ ‖Ψ (σ w) - c₀‖ + ‖(x : ℂ)‖ := by
          rw [show Ψ (σ w) + (x : ℂ) - c₀ = (Ψ (σ w) - c₀) + (x : ℂ) from by ring]
          exact norm_add_le _ _
      _ < R + R := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_lt_add_of_lt_of_le hnorm hx
      _ < 5 * R := by linarith
  obtain ⟨ε, hε, hcross⟩ := leaf_cross_chart hV hΨd hΨinj hVH hVne hΨsq hσ
    hR hwV hdev
  have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hxs : |ε * x₀| ≤ R := by
    rw [abs_mul, hεabs, one_mul]
    exact hx₀.le
  obtain ⟨hmem, hval⟩ := hcross (ε * x₀) hxs
  refine ⟨w + ε * x₀, hmem, ?_⟩
  rw [hval]
  have h2 : (ε : ℂ) * ((ε * x₀ : ℝ) : ℂ) = ((x₀ : ℝ) : ℂ) := by
    push_cast
    rw [show (ε : ℂ) * ((ε : ℂ) * (x₀ : ℂ)) = ((ε * ε : ℝ) : ℂ) * (x₀ : ℂ) from by
      push_cast; ring, hεsq]
    push_cast
    ring
  rw [h2]
  refine Complex.ext ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_sub]
    rw [hx₀def]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]

/-- **Equal-height leaves meet**: two leaves visiting the inner ball of a margined
chart at the same chart height share a plane point. -/
theorem equal_height_meet {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V) (hΨinj : Set.InjOn Ψ V)
    (hVH : V ⊆ {z : ℂ | 0 < z.im}) (hVne : ∀ w ∈ V, q w ≠ 0)
    (hΨsq : ∀ x ∈ V, deriv Ψ x ^ 2 = -(-q x))
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψ '' V)
    {σ σ' : ℝ → ℂ}
    (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    (hσ' : IsTrajOn (fun z => -q z) σ' Set.univ)
    {w w' : ℝ} (hwV : σ w ∈ V) (hw'V : σ' w' ∈ V)
    (hwb : Ψ (σ w) ∈ Metric.ball c₀ R) (hw'b : Ψ (σ' w') ∈ Metric.ball c₀ R)
    (hht : (Ψ (σ w)).im = (Ψ (σ' w')).im) :
    ∃ u u' : ℝ, σ u = σ' u' := by
  obtain ⟨u, huV, huval⟩ := leaf_align hV hΨd hΨinj hVH hVne hΨsq hR
    hmarg hσ hwV hwb
  obtain ⟨u', hu'V, hu'val⟩ := leaf_align hV hΨd hΨinj hVH hVne hΨsq hR
    hmarg hσ' hw'V hw'b
  refine ⟨u, u', hΨinj huV hu'V ?_⟩
  rw [huval, hu'val, hht]

/-- **Visit-height coherence of a leaf**: under the vertical-horizontal no-bigon
principle, an all-time transverse leaf visiting the inner ball of a margined chart at
two parameters has equal chart heights at the two visits. -/
theorem leaf_visit_height {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V) (hΨinj : Set.InjOn Ψ V)
    (hVH : V ⊆ {z : ℂ | 0 < z.im}) (hVne : ∀ w ∈ V, q w ≠ 0)
    (hΨsq : ∀ x ∈ V, deriv Ψ x ^ 2 = -(-q x))
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψ '' V)
    {τ : ℝ → ℂ} (hτ : IsTrajOn (fun z => -q z) τ Set.univ)
    {u₁ u₂ : ℝ} (h₁V : τ u₁ ∈ V) (h₂V : τ u₂ ∈ V)
    (h₁b : Ψ (τ u₁) ∈ Metric.ball c₀ R) (h₂b : Ψ (τ u₂) ∈ Metric.ball c₀ R) :
    (Ψ (τ u₁)).im = (Ψ (τ u₂)).im := by
  by_contra hne
  obtain ⟨w₁, hw₁V, hw₁val⟩ := leaf_align hV hΨd hΨinj hVH hVne hΨsq hR
    hmarg hτ h₁V h₁b
  obtain ⟨w₂, hw₂V, hw₂val⟩ := leaf_align hV hΨd hΨinj hVH hVne hΨsq hR
    hmarg hτ h₂V h₂b
  have hbound : ∀ u : ℝ, Ψ (τ u) ∈ Metric.ball c₀ R →
      |(Ψ (τ u)).im - c₀.im| < 5 * R / 4 := by
    intro u hu
    have h3 : |(Ψ (τ u)).im - c₀.im| ≤ ‖Ψ (τ u) - c₀‖ := by
      rw [show (Ψ (τ u)).im - c₀.im = (Ψ (τ u) - c₀).im from by
        rw [Complex.sub_im]]
      exact Complex.abs_im_le_norm _
    have h4 : ‖Ψ (τ u) - c₀‖ < R := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hu
    linarith
  obtain ⟨arc, harc, harc0, harcT⟩ := vertical_connect (q := fun z => -q z)
    hV hΨd hΨinj hVH (fun z hz => neg_ne_zero.mpr (hVne z hz)) hΨsq
    (by positivity : (0 : ℝ) < 5 * R) hmarg hw₁V hw₂V hw₁val hw₂val
    (hbound u₁ h₁b) (hbound u₂ h₂b) hne
  have harcq : IsTrajOn q arc
      (Set.Icc (-(5 * R / 4)) (|(Ψ (τ u₁)).im - (Ψ (τ u₂)).im| + 5 * R / 4)) :=
    isTrajOn_congr (fun w => neg_neg (q w)) harc
  set T : ℝ := |(Ψ (τ u₁)).im - (Ψ (τ u₂)).im| with hTdef
  have hT : 0 < T := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hμ : (0 : ℝ) < 5 * R / 4 := by positivity
  rcases le_total w₁ w₂ with hw | hw
  · have hτh : IsTrajOn (fun z => -q z) (fun v => τ (v + w₁)) Set.univ := by
      have h5 := traj_shift w₁ hτ
      rwa [Set.preimage_univ] at h5
    refine hbigon arc (fun v => τ (v + w₁)) T (w₂ - w₁) (5 * R / 4) hT
      (by linarith) hμ harcq (traj_mono hτh (Set.subset_univ _)) ?_ ?_
    · rw [zero_add, hTdef]
      exact harcT.symm
    · rw [show w₂ - w₁ + w₁ = w₂ from by ring]
      exact harc0.symm
  · have hτh : IsTrajOn (fun z => -q z) (fun v => τ (w₁ - v)) Set.univ := by
      have h5 := traj_shift (-w₁) (traj_reverse hτ)
      rw [Set.preimage_univ, Set.preimage_univ] at h5
      have hfun : (fun u : ℝ => (fun v : ℝ => τ (-v)) (u + -w₁))
          = fun u : ℝ => τ (w₁ - u) := by
        funext u
        simp only
        congr 1
        ring
      rwa [hfun] at h5
    refine hbigon arc (fun v => τ (w₁ - v)) T (w₁ - w₂) (5 * R / 4) hT
      (by linarith) hμ harcq (traj_mono hτh (Set.subset_univ _)) ?_ ?_
    · rw [sub_zero, hTdef]
      exact harcT.symm
    · rw [show w₁ - (w₁ - w₂) = w₂ from by ring]
      exact harc0.symm

/-- **Long corridor crossing of one chart**: under a uniform image margin along the
base piece, a leaf entering at a purely imaginary offset crosses the whole piece,
exiting at the same offset from the base exit. -/
theorem corridor_cross_long {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V) (hΨinj : Set.InjOn Ψ V)
    (hVH : V ⊆ {z : ℂ | 0 < z.im}) (hVne : ∀ w ∈ V, q w ≠ 0)
    (hΨsq : ∀ x ∈ V, deriv Ψ x ^ 2 = -(-q x))
    {τb σ : ℝ → ℂ}
    (hτb : IsTrajOn (fun z => -q z) τb Set.univ)
    (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    {α β : ℝ} (hαβ : α < β)
    (htrk : ∀ w ∈ Set.Icc α β, τb w ∈ V)
    {m : ℝ} (hm : 0 < m)
    (hmargU : ∀ w ∈ Set.Icc α β, Metric.ball (Ψ (τb w)) m ⊆ Ψ '' V)
    {d w₀ : ℝ} (hd : |d| < m / 2) (hw₀ : σ w₀ ∈ V)
    (hoff : Ψ (σ w₀) = Ψ (τb α) + Complex.I * (d : ℂ)) :
    ∃ w₁ : ℝ, σ w₁ ∈ V ∧ Ψ (σ w₁) = Ψ (τb β) + Complex.I * (d : ℂ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((β - α) / (m / 2))
  have hstep : (β - α) / ((N : ℝ) + 1) < m / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < m / 2)] at hN
    nlinarith [hm]
  have hstep0 : 0 < (β - α) / ((N : ℝ) + 1) := by
    have : (0 : ℝ) < β - α := by linarith
    positivity
  set st : ℝ := (β - α) / ((N : ℝ) + 1) with hstdef
  have hkey : ∀ j : ℕ, j ≤ N + 1 → ∃ w' : ℝ, σ w' ∈ V ∧
      Ψ (σ w') = Ψ (τb (α + (j : ℝ) * st)) + Complex.I * (d : ℂ) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨w₀, hw₀, ?_⟩
      rw [show α + (0 : ℕ) * st = α from by push_cast; ring]
      exact hoff
    | succ k ih =>
      intro hk1
      obtain ⟨w', hw'V, hw'off⟩ := ih (le_trans (Nat.le_succ k) hk1)
      have hkN : (k : ℝ) + 1 ≤ (N : ℝ) + 1 := by
        have := (Nat.cast_le (α := ℝ)).mpr hk1
        push_cast at this
        linarith
      have hsub : Set.Icc (α + (k : ℝ) * st) (α + ((k : ℝ) + 1) * st)
          ⊆ Set.Icc α β := by
        refine Set.Icc_subset_Icc ?_ ?_
        · nlinarith [Nat.cast_nonneg (α := ℝ) k, hstep0]
        · have h3 : ((k : ℝ) + 1) * st ≤ ((N : ℝ) + 1) * st :=
            mul_le_mul_of_nonneg_right hkN hstep0.le
          have h4 : ((N : ℝ) + 1) * st = β - α := by
            rw [hstdef]
            field_simp
          linarith
      have hmem : α + (k : ℝ) * st ∈ Set.Icc α β :=
        hsub (Set.left_mem_Icc.mpr (by linarith [hstep0]))
      obtain ⟨w'', hw''V, hw''off, -⟩ := corridor_cross hV hΨd hΨinj hVH
        hVne hΨsq hτb hσ (by linarith : α + (k : ℝ) * st < α + ((k : ℝ) + 1) * st)
        (fun w hw => htrk w (hsub hw)) (hmargU _ hmem)
        (by rw [show α + ((k : ℝ) + 1) * st - (α + (k : ℝ) * st) = st from by ring]
            exact hstep)
        hd hw'V hw'off
      refine ⟨w'', hw''V, ?_⟩
      rw [hw''off]
      congr 2
      push_cast
      ring
  obtain ⟨w₁, hw₁V, hw₁off⟩ := hkey (N + 1) le_rfl
  refine ⟨w₁, hw₁V, ?_⟩
  rw [hw₁off]
  push_cast
  rw [show α + ((N : ℝ) + 1) * st = β from by
    rw [hstdef]
    have hne : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring]

/-- **The corridor fold**: along a finite full-package chart chain of the base leaf,
every all-time leaf entering the first chart at a small purely imaginary offset exits
the last chart at the chain's signed image of that offset. -/
theorem corridor_fold {q : ℂ → ℂ} {τb : ℝ → ℂ}
    (hτb : IsTrajOn (fun z => -q z) τb Set.univ)
    {n : ℕ} {v : ℕ → ℝ} {V : ℕ → Set ℂ} {Ψ : ℕ → ℂ → ℂ}
    (hVo : ∀ i, i ≤ n → IsOpen (V i))
    (hVH : ∀ i, i ≤ n → V i ⊆ {z : ℂ | 0 < z.im})
    (hVne : ∀ i, i ≤ n → ∀ w ∈ V i, q w ≠ 0)
    (hΨd : ∀ i, i ≤ n → DifferentiableOn ℂ (Ψ i) (V i))
    (hΨinj : ∀ i, i ≤ n → Set.InjOn (Ψ i) (V i))
    (hΨsq : ∀ i, i ≤ n → ∀ x ∈ V i, deriv (Ψ i) x ^ 2 = -(-q x))
    (hvlt : ∀ i, i ≤ n → v i < v (i + 1))
    (htrk : ∀ i, i ≤ n → ∀ w ∈ Set.Icc (v i) (v (i + 1)), τb w ∈ V i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
      ∀ σ : ℝ → ℂ, IsTrajOn (fun z => -q z) σ Set.univ →
      ∀ d w₀ : ℝ, |d| < ρ → σ w₀ ∈ V 0 →
      Ψ 0 (σ w₀) = Ψ 0 (τb (v 0)) + Complex.I * (d : ℂ) →
      ∃ w₁ : ℝ, σ w₁ ∈ V n ∧
        Ψ n (σ w₁) = Ψ n (τb (v (n + 1))) + Complex.I * ((η * d : ℝ) : ℂ) := by
  have hτbc : Continuous τb := continuousOn_univ.mp hτb.cont
  have hdne : ∀ i, i ≤ n → ∀ x ∈ V i, deriv (Ψ i) x ≠ 0 := by
    intro i hi x hx h0
    have h1 := hΨsq i hi x hx
    rw [h0] at h1
    exact hVne i hi x hx (by simpa using h1.symm)
  have hmdata : ∀ i : ℕ, ∃ m : ℝ, 0 < m ∧ (i ≤ n →
      ∀ w ∈ Set.Icc (v i) (v (i + 1)),
        Metric.ball (Ψ i (τb w)) m ⊆ Ψ i '' V i) := by
    intro i
    by_cases hi : i ≤ n
    · have hopen : IsOpen (Ψ i '' V i) :=
        image_open_of_deriv_ne (hVo i hi) (hΨd i hi) (hdne i hi)
      have hKsub0 : τb '' Set.Icc (v i) (v (i + 1)) ⊆ V i := by
        rintro z ⟨w, hw, rfl⟩
        exact htrk i hi w hw
      have hKc : IsCompact ((Ψ i) '' (τb '' Set.Icc (v i) (v (i + 1)))) :=
        (isCompact_Icc.image hτbc).image_of_continuousOn
          ((hΨd i hi).continuousOn.mono hKsub0)
      obtain ⟨m, hm, hmball⟩ := chart_margin hopen hKc (Set.image_mono hKsub0)
      refine ⟨m, hm, fun _ w hw => hmball _ ?_⟩
      exact Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hw)
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose mv hmv hmarg using hmdata
  have hndata : ∀ i : ℕ, ∃ r : ℝ, 0 < r ∧ (i < n →
      Metric.ball (τb (v (i + 1))) r ⊆ V i ∩ V (i + 1)) := by
    intro i
    by_cases hi : i < n
    · have hx₁ : τb (v (i + 1)) ∈ V i :=
        htrk i hi.le _ (Set.right_mem_Icc.mpr (hvlt i hi.le).le)
      have hx₂ : τb (v (i + 1)) ∈ V (i + 1) :=
        htrk (i + 1) hi _ (Set.left_mem_Icc.mpr (hvlt (i + 1) hi).le)
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
        (((hVo i hi.le).inter (hVo (i + 1) hi)).mem_nhds ⟨hx₁, hx₂⟩)
      exact ⟨r, hr, fun _ => hball⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose rv hrv hrball using hndata
  have hsdata : ∀ i : ℕ, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ (i < n →
      ∀ y ∈ Metric.ball (τb (v (i + 1))) (rv i), ∀ d : ℝ,
        Ψ i y = Ψ i (τb (v (i + 1))) + Complex.I * (d : ℂ) →
        Ψ (i + 1) y = Ψ (i + 1) (τb (v (i + 1)))
          + Complex.I * ((s * d : ℝ) : ℂ)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨s, hs, htr⟩ := corridor_node (hΨd i hi.le) (hΨd (i + 1) hi)
        (fun z hz => by rw [hΨsq (i + 1) hi z hz.2, hΨsq i hi.le z hz.1])
        (hrv i) (hrball i hi)
      exact ⟨s, hs, fun _ => htr⟩
    · exact ⟨1, Or.inl rfl, fun h => absurd h hi⟩
  choose sv hsv htrans using hsdata
  have hδdata : ∀ i : ℕ, ∃ δ : ℝ, 0 < δ ∧ (i < n → ∀ y ∈ V i,
      dist (Ψ i y) (Ψ i (τb (v (i + 1)))) < δ →
      dist y (τb (v (i + 1))) < rv i) := by
    intro i
    by_cases hi : i < n
    · have hx₁ : τb (v (i + 1)) ∈ V i :=
        htrk i hi.le _ (Set.right_mem_Icc.mpr (hvlt i hi.le).le)
      obtain ⟨δ, hδ, hnear⟩ := chart_preimage_near_open (hVo i hi.le)
        (hΨd i hi.le) (hΨinj i hi.le) hx₁ (hdne i hi.le _ hx₁) (hrv i)
      exact ⟨δ, hδ, fun _ => hnear⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose δv hδv hδnear using hδdata
  have hfold : ∀ k : ℕ, k ≤ n → ∃ ρ : ℝ, 0 < ρ ∧ ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
      ∀ σ : ℝ → ℂ, IsTrajOn (fun z => -q z) σ Set.univ →
      ∀ d w₀ : ℝ, |d| < ρ → σ w₀ ∈ V 0 →
      Ψ 0 (σ w₀) = Ψ 0 (τb (v 0)) + Complex.I * (d : ℂ) →
      ∃ w₁ : ℝ, σ w₁ ∈ V k ∧
        Ψ k (σ w₁) = Ψ k (τb (v k)) + Complex.I * ((η * d : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1, one_pos, 1, Or.inl rfl, ?_⟩
      intro σ hσ d w₀ hd hw₀ hoff
      refine ⟨w₀, hw₀, ?_⟩
      rw [hoff]
      norm_num
    | succ k ih =>
      intro hk1
      have hk : k ≤ n := le_trans (Nat.le_succ k) hk1
      have hkn : k < n := hk1
      obtain ⟨ρk, hρk, ηk, hηk, hIH⟩ := ih hk
      have hηabs : |ηk| = 1 := by rcases hηk with h | h <;> rw [h] <;> norm_num
      refine ⟨min ρk (min (mv k / 2) (δv k)),
        lt_min hρk (lt_min (by linarith [hmv k]) (hδv k)), sv k * ηk, ?_, ?_⟩
      · rcases hsv k with h | h <;> rcases hηk with h' | h'
        · exact Or.inl (by rw [h, h']; norm_num)
        · exact Or.inr (by rw [h, h']; norm_num)
        · exact Or.inr (by rw [h, h']; norm_num)
        · exact Or.inl (by rw [h, h']; norm_num)
      intro σ hσ d w₀ hd hw₀ hoff
      have hd1 : |d| < ρk := lt_of_lt_of_le hd (min_le_left _ _)
      have hd2 : |d| < mv k / 2 :=
        lt_of_lt_of_le hd (le_trans (min_le_right _ _) (min_le_left _ _))
      have hd3 : |d| < δv k :=
        lt_of_lt_of_le hd (le_trans (min_le_right _ _) (min_le_right _ _))
      obtain ⟨wk, hwkV, hwkoff⟩ := hIH σ hσ d w₀ hd1 hw₀ hoff
      have hdk : |ηk * d| < mv k / 2 := by
        rw [abs_mul, hηabs, one_mul]
        exact hd2
      obtain ⟨we, hweV, hweoff⟩ := corridor_cross_long (hVo k hk)
        (hΨd k hk) (hΨinj k hk) (hVH k hk) (hVne k hk) (hΨsq k hk) hτb hσ
        (hvlt k hk) (htrk k hk) (hmv k) (hmarg k hk) hdk hwkV hwkoff
      have hdist : dist (Ψ k (σ we)) (Ψ k (τb (v (k + 1)))) < δv k := by
        rw [hweoff, dist_eq_norm,
          show Ψ k (τb (v (k + 1))) + Complex.I * ((ηk * d : ℝ) : ℂ)
              - Ψ k (τb (v (k + 1))) = Complex.I * ((ηk * d : ℝ) : ℂ) from by
            ring,
          norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, hηabs, one_mul]
        exact hd3
      have hballmem : σ we ∈ Metric.ball (τb (v (k + 1))) (rv k) :=
        Metric.mem_ball.mpr (hδnear k hkn _ hweV hdist)
      have hval2 := htrans k hkn _ hballmem (ηk * d) hweoff
      refine ⟨we, (hrball k hkn hballmem).2, ?_⟩
      rw [hval2]
      congr 2
      push_cast
      ring
  obtain ⟨ρn, hρn, ηn, hηn, hfoldn⟩ := hfold n le_rfl
  have hηnabs : |ηn| = 1 := by rcases hηn with h | h <;> rw [h] <;> norm_num
  refine ⟨min ρn (mv n / 2), lt_min hρn (by linarith [hmv n]), ηn, hηn, ?_⟩
  intro σ hσ d w₀ hd hw₀ hoff
  obtain ⟨wn, hwnV, hwnoff⟩ := hfoldn σ hσ d w₀
    (lt_of_lt_of_le hd (min_le_left _ _)) hw₀ hoff
  have hdn : |ηn * d| < mv n / 2 := by
    rw [abs_mul, hηnabs, one_mul]
    exact lt_of_lt_of_le hd (min_le_right _ _)
  exact corridor_cross_long (hVo n le_rfl) (hΨd n le_rfl)
    (hΨinj n le_rfl) (hVH n le_rfl) (hVne n le_rfl) (hΨsq n le_rfl) hτb hσ
    (hvlt n le_rfl) (htrk n le_rfl) (hmv n) (hmarg n le_rfl) hdn hwnV hwnoff

section FinalFeed

open unitInterval

set_option maxHeartbeats 400000 in
-- Heartbeats: the conclusion bundles dozens of conjuncts in one elaboration.
/-- **The rounded-bigon data pack**: a trajectory bigon carries natural charts at its two
corners together with rounding radii, corner circles, developments, confinement
thresholds, and the separation bounds consumed by the four-piece loop. -/
theorem discharge_pack₂ {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {a T b μ s : ℝ}
    (hμ : 0 < μ) (ha0 : 0 ≤ a) (haT : a < T) (hb0 : 0 < b) (hbs : b ≤ s)
    (hγ : IsTrajOn q γ (Set.Icc (-μ) (T + μ)))
    (hτ : IsTrajOn (fun z => -q z) τ (Set.Icc (-μ) (s + μ)))
    (hc1 : τ 0 = γ T) (hc2 : τ b = γ a)
    (hγinj : Set.InjOn γ (Set.Icc a T)) (hτinj : Set.InjOn τ (Set.Icc 0 b)) :
    ∃ (S₁ S₂ : Set ℂ) (Φ₁ Φ₂ : ℂ → ℂ) (ε₁ ε₂ r r₀ η₁ η₂ : ℝ),
      0 < r ∧ r < r₀ ∧
      (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
      r * (Real.pi/2) < 3 * (T - a - 2*r) ∧
      r * (Real.pi/2) < 3 * (b - 2*r) ∧
      IsOpen S₁ ∧ DifferentiableOn ℂ Φ₁ S₁ ∧ Set.InjOn Φ₁ S₁ ∧
      (∀ z ∈ S₁, deriv Φ₁ z ^ 2 = -q z) ∧ (∀ z ∈ S₁, q z ≠ 0) ∧
      IsOpen S₂ ∧ DifferentiableOn ℂ Φ₂ S₂ ∧ Set.InjOn Φ₂ S₂ ∧
      (∀ z ∈ S₂, deriv Φ₂ z ^ 2 = -q z) ∧ (∀ z ∈ S₂, q z ≠ 0) ∧
      Metric.ball (Φ₁ (γ T)) (4 * r₀) ⊆ Φ₁ '' S₁ ∧
      Metric.ball (Φ₂ (γ a)) (4 * r₀) ⊆ Φ₂ '' S₂ ∧
      (∀ u : ℝ, (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
        + (r : ℂ) * Complex.exp (Complex.I * (((-(-ε₁) * (Real.pi / 2) : ℝ) : ℂ)
          + ((1 * (-ε₁) * (Real.pi / 2) : ℝ) : ℂ) * (u : ℂ)))
        ∈ Φ₁ '' S₁) ∧
      (∀ u : ℝ, (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
        + (r : ℂ) * Complex.exp (Complex.I * (((-ε₂ * Real.pi : ℝ) : ℂ)
          + ((ε₂ * (Real.pi / 2) : ℝ) : ℂ) * (u : ℂ)))
        ∈ Φ₂ '' S₂) ∧
      (∀ u ∈ Set.Icc (T - r₀) (T + r₀),
        γ u ∈ S₁ ∧ Φ₁ (γ u) = Φ₁ (γ T) + ((u - T : ℝ) : ℂ)) ∧
      (∀ v ∈ Set.Icc (-r₀) r₀,
        τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v : ℝ) : ℂ)) ∧
      (∀ u ∈ Set.Icc (a - r₀) (a + r₀),
        γ u ∈ S₂ ∧ Φ₂ (γ u) = Φ₂ (γ a) + ((u - a : ℝ) : ℂ)) ∧
      (∀ v ∈ Set.Icc (b - r₀) (b + r₀),
        τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ)) ∧
      (∀ t : ℝ, cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r
        (-(-ε₁) * (Real.pi / 2)) (1 * (-ε₁) * (Real.pi / 2)) t
        ∈ Metric.ball (γ T) η₁) ∧
      (∀ t : ℝ, cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r
        (-ε₂ * Real.pi) (ε₂ * (Real.pi / 2)) t
        ∈ Metric.ball (γ a) η₂) ∧
      (∀ x, a + r ≤ x → x < T - r₀ → η₁ ≤ ‖γ x - γ T‖) ∧
      (∀ v, r₀ < v → v ≤ b - r → η₁ ≤ ‖τ v - γ T‖) ∧
      (∀ x, a + r₀ < x → x ≤ T - r → η₂ ≤ ‖γ x - γ a‖) ∧
      (∀ v, r ≤ v → v < b - r₀ → η₂ ≤ ‖τ v - γ a‖) ∧
      (∀ z, z ∈ Metric.ball (γ T) η₁ → z ∈ Metric.ball (γ a) η₂ → False) ∧
      η₁ ≤ (γ T).im ∧ η₂ ≤ (γ a).im := by
  obtain ⟨S₁, S₂, Φ₁, Φ₂, ε₁, ε₂, r₀ₖ, hr₀ₖ, hε₁, hε₂, hS₁o, hΦ₁d, hΦ₁inj, hΦ₁sq,
    hq₁ne, hS₂o, hΦ₂d, hΦ₂inj, hΦ₂sq, hq₂ne, hball₁, hball₂, hdevγ₁k, hdevτ₁k,
    hdevγ₂k, hdevτ₂k⟩ := bigon_corner_kits hμ ha0 haT hb0 hbs hγ hτ hc1 hc2
  have hγT₁ : γ T ∈ S₁ :=
    (hdevγ₁k T ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩).1
  have hγa₂ : γ a ∈ S₂ :=
    (hdevγ₂k a ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩).1
  obtain ⟨rB₁, C₁, hrB₁, hC₁, hB₁sub, hB₁d, hB₁sq, hB₁C⟩ :=
    ball_chart_at hS₁o hΦ₁d hΦ₁sq hγT₁
  obtain ⟨rB₂, C₂, hrB₂, hC₂, hB₂sub, hB₂d, hB₂sq, hB₂C⟩ :=
    ball_chart_at hS₂o hΦ₂d hΦ₂sq hγa₂
  -- continuity windows into the two balls
  have hTd : Set.Icc (-μ) (T + μ) ∈ nhds T := Icc_mem_nhds (by linarith) (by linarith)
  have had : Set.Icc (-μ) (T + μ) ∈ nhds a := Icc_mem_nhds (by linarith) (by linarith)
  have h0d : Set.Icc (-μ) (s + μ) ∈ nhds 0 := Icc_mem_nhds (by linarith) (by linarith)
  have hbd : Set.Icc (-μ) (s + μ) ∈ nhds b := Icc_mem_nhds (by linarith) (by linarith)
  have hγTc : ContinuousAt γ T := (hγ.cont T (mem_of_mem_nhds hTd)).continuousAt hTd
  have hγac : ContinuousAt γ a := (hγ.cont a (mem_of_mem_nhds had)).continuousAt had
  have hτ0c : ContinuousAt τ 0 := (hτ.cont 0 (mem_of_mem_nhds h0d)).continuousAt h0d
  have hτbc : ContinuousAt τ b := (hτ.cont b (mem_of_mem_nhds hbd)).continuousAt hbd
  obtain ⟨δ₁γ, hδ₁γ, hwγT⟩ := Metric.eventually_nhds_iff.mp
    (hγTc.eventually_mem (Metric.ball_mem_nhds _ hrB₁))
  obtain ⟨δ₁τ, hδ₁τ, hwτ0⟩ := Metric.eventually_nhds_iff.mp
    (hτ0c.eventually_mem (by rw [hc1]; exact Metric.ball_mem_nhds _ hrB₁))
  obtain ⟨δ₂γ, hδ₂γ, hwγa⟩ := Metric.eventually_nhds_iff.mp
    (hγac.eventually_mem (Metric.ball_mem_nhds _ hrB₂))
  obtain ⟨δ₂τ, hδ₂τ, hwτb⟩ := Metric.eventually_nhds_iff.mp
    (hτbc.eventually_mem (by rw [hc2]; exact Metric.ball_mem_nhds _ hrB₂))
  set w : ℝ := min (min (min (δ₁γ/2) (δ₁τ/2)) (min (δ₂γ/2) (δ₂τ/2))) μ with hwdef
  have hw : 0 < w := lt_min (lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by linarith) (by linarith))) hμ
  have hwa : w ≤ δ₁γ/2 := le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _))
  have hwb : w ≤ δ₁τ/2 := le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hwc : w ≤ δ₂γ/2 := le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hwd : w ≤ δ₂τ/2 := le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hwμ : w ≤ μ := min_le_right _ _
  -- the four near-diagonal lower separations
  have hlsγT := traj_lower_sep hB₁d hB₁sq hB₁C hγ
    (show T - w ≤ T + w by linarith)
    (fun u hu => Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu => hwγT (show dist u T < δ₁γ by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2]))
  have hlsτ0 := lower_sep_neg hB₁d hB₁sq hB₁C hτ
    (show -w ≤ w by linarith)
    (fun u hu => Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu => hwτ0 (show dist u 0 < δ₁τ by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2]))
  have hlsγa := traj_lower_sep hB₂d hB₂sq hB₂C hγ
    (show a - w ≤ a + w by linarith)
    (fun u hu => Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu => hwγa (show dist u a < δ₂γ by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2]))
  have hlsτb := lower_sep_neg hB₂d hB₂sq hB₂C hτ
    (show b - w ≤ b + w by linarith)
    (fun u hu => Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu => hwτb (show dist u b < δ₂τ by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2]))
  -- the far track separations
  obtain ⟨sepγ, hsepγ, hsγ⟩ := track_sep_shift
    (hγ.cont.mono fun u hu => Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    hγinj hw
  obtain ⟨sepτ, hsepτ, hsτ⟩ := track_sep_shift
    (hτ.cont.mono fun u hu => Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    hτinj hw
  -- corner distinctness and margins
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hne : γ T ≠ γ a := by
    intro h
    have h1 := hγinj (Set.mem_Icc.mpr ⟨le_of_lt haT, le_refl T⟩)
      (Set.mem_Icc.mpr ⟨le_refl a, le_of_lt haT⟩) h
    linarith
  have hdTa : 0 < ‖γ T - γ a‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  have himT : 0 < (γ T).im := (traj_regular hγ (mem_of_mem_nhds hTd)).1
  have hima : 0 < (γ a).im := (traj_regular hγ (mem_of_mem_nhds had)).1
  -- the window radius and the confinement thresholds
  set r₀f : ℝ := min r₀ₖ w with hr₀fdef
  have hr₀f : 0 < r₀f := lt_min hr₀ₖ hw
  have hr₀fk : r₀f ≤ r₀ₖ := min_le_left _ _
  have hr₀fw : r₀f ≤ w := min_le_right _ _
  set η₁ : ℝ := min (min sepγ sepτ) (min (min (r₀f/C₁) (‖γ T - γ a‖/2)) ((γ T).im))
    with hη₁def
  have hη₁ : 0 < η₁ := lt_min (lt_min hsepγ hsepτ)
    (lt_min (lt_min (div_pos hr₀f hC₁) (by linarith)) himT)
  set η₂ : ℝ := min (min sepγ sepτ) (min (min (r₀f/C₂) (‖γ T - γ a‖/2)) ((γ a).im))
    with hη₂def
  have hη₂ : 0 < η₂ := lt_min (lt_min hsepγ hsepτ)
    (lt_min (lt_min (div_pos hr₀f hC₂) (by linarith)) hima)
  have hη₁sepγ : η₁ ≤ sepγ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη₁sepτ : η₁ ≤ sepτ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη₁C : η₁ ≤ r₀f/C₁ := le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _))
  have hη₁d : η₁ ≤ ‖γ T - γ a‖/2 := le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hη₁im : η₁ ≤ (γ T).im := le_trans (min_le_right _ _) (min_le_right _ _)
  have hη₂sepγ : η₂ ≤ sepγ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη₂sepτ : η₂ ≤ sepτ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη₂C : η₂ ≤ r₀f/C₂ := le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _))
  have hη₂d : η₂ ≤ ‖γ T - γ a‖/2 := le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hη₂im : η₂ ≤ (γ a).im := le_trans (min_le_right _ _) (min_le_right _ _)
  have hCη₁ : C₁ * η₁ ≤ r₀f := by
    have h1 := mul_le_mul_of_nonneg_left hη₁C hC₁.le
    rwa [mul_div_cancel₀ _ hC₁.ne'] at h1
  have hCη₂ : C₂ * η₂ ≤ r₀f := by
    have h1 := mul_le_mul_of_nonneg_left hη₂C hC₂.le
    rwa [mul_div_cancel₀ _ hC₂.ne'] at h1
  -- the chart shrinkages
  have hΦ₁ne : deriv Φ₁ (γ T) ≠ 0 := by
    intro h0
    have h1 := hΦ₁sq _ hγT₁
    rw [h0] at h1
    exact hq₁ne _ hγT₁ (by simpa using h1.symm)
  have hΦ₂ne : deriv Φ₂ (γ a) ≠ 0 := by
    intro h0
    have h1 := hΦ₂sq _ hγa₂
    rw [h0] at h1
    exact hq₂ne _ hγa₂ (by simpa using h1.symm)
  obtain ⟨ρ₁, hρ₁, hshr₁⟩ := chart_shrink hS₁o hΦ₁d hγT₁ hΦ₁ne hη₁
  obtain ⟨ρ₂, hρ₂, hshr₂⟩ := chart_shrink hS₂o hΦ₂d hγa₂ hΦ₂ne hη₂
  -- the rounding radius
  set r : ℝ := min (min (r₀f/2) ((T - a)/8)) (min (b/8) (min (ρ₁/4) (ρ₂/4)))
    with hrdef
  have hr : 0 < r := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hrf : r ≤ r₀f/2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hrTa : r ≤ (T - a)/8 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrb8 : r ≤ b/8 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrρ₁ : r ≤ ρ₁/4 := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrρ₂ : r ≤ ρ₂/4 := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrr₀ : r < r₀f := by linarith
  have h3γ : r * (Real.pi/2) < 3 * (T - a - 2*r) := by
    nlinarith only [Real.pi_le_four, hrTa, hr, hπ]
  have h3τ : r * (Real.pi/2) < 3 * (b - 2*r) := by
    nlinarith only [Real.pi_le_four, hrb8, hr, hπ]
  -- the corner circles, containments, and confinements
  have hεv₁ : (-ε₁ : ℝ) = 1 ∨ (-ε₁ : ℝ) = -1 := by
    rcases hε₁ with h | h
    · right; rw [h]
    · left; rw [h]; norm_num
  obtain ⟨-, -, -, -, -, hg6₁⟩ := corner_geometry (εh := (1:ℝ)) (εv := (-ε₁ : ℝ))
    (Or.inl rfl) hεv₁ hr (α := -(-ε₁) * (Real.pi / 2)) (ω := 1 * (-ε₁) * (Real.pi / 2))
    rfl rfl (Φ₁ (γ T))
  obtain ⟨-, -, -, -, -, hg6₂⟩ := corner_geometry (εh := (-1:ℝ)) (εv := ε₂)
    (Or.inr rfl) hε₂ hr (α := -ε₂ * (Real.pi / 2)) (ω := (-1) * ε₂ * (Real.pi / 2))
    rfl rfl (Φ₂ (γ a))
  have hcirc₁ : ∀ u : ℝ, (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * (((-(-ε₁) * (Real.pi / 2) : ℝ) : ℂ)
        + ((1 * (-ε₁) * (Real.pi / 2) : ℝ) : ℂ) * (u : ℂ)))
      ∈ Metric.ball (Φ₁ (γ T)) ρ₁ := by
    intro u
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (hg6₁ u) (by linarith)
  have hcirc₂ : ∀ u : ℝ, (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * (((-ε₂ * Real.pi : ℝ) : ℂ)
        + ((ε₂ * (Real.pi / 2) : ℝ) : ℂ) * (u : ℂ)))
      ∈ Metric.ball (Φ₂ (γ a)) ρ₂ := by
    intro u
    have heu : Complex.I * (((-ε₂ * Real.pi : ℝ) : ℂ)
        + ((ε₂ * (Real.pi / 2) : ℝ) : ℂ) * (u : ℂ))
        = Complex.I * (((-ε₂ * (Real.pi / 2) : ℝ) : ℂ)
          + (((-1) * ε₂ * (Real.pi / 2) : ℝ) : ℂ) * ((1 - u : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [Metric.mem_ball, heu]
    exact lt_of_le_of_lt (hg6₂ (1 - u)) (by linarith)
  have htr₁ : ∀ u : ℝ, (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * (((-(-ε₁) * (Real.pi / 2) : ℝ) : ℂ)
        + ((1 * (-ε₁) * (Real.pi / 2) : ℝ) : ℂ) * (u : ℂ)))
      ∈ Φ₁ '' S₁ := fun u =>
    (Set.image_mono Set.inter_subset_left) (hshr₁ (hcirc₁ u))
  have htr₂ : ∀ u : ℝ, (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * (((-ε₂ * Real.pi : ℝ) : ℂ)
        + ((ε₂ * (Real.pi / 2) : ℝ) : ℂ) * (u : ℂ)))
      ∈ Φ₂ '' S₂ := fun u =>
    (Set.image_mono Set.inter_subset_left) (hshr₂ (hcirc₂ u))
  have hω₁Lne : (1 * (-ε₁) * (Real.pi / 2)) ≠ 0 := by
    rcases hε₁ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hω₂Lne : (ε₂ * (Real.pi / 2)) ≠ 0 := by
    rcases hε₂ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hκ₁b := corner_in_ball hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁Lne htr₁
    hshr₁ hcirc₁
  have hκ₂b := corner_in_ball hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂Lne htr₂
    hshr₂ hcirc₂
  -- the developments at the final window radius
  have hdevγ₁f : ∀ u ∈ Set.Icc (T - r₀f) (T + r₀f),
      γ u ∈ S₁ ∧ Φ₁ (γ u) = Φ₁ (γ T) + ((u - T : ℝ) : ℂ) := fun u hu =>
    hdevγ₁k u ⟨Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hdevτ₁f : ∀ v ∈ Set.Icc (-r₀f) r₀f,
      τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v : ℝ) : ℂ) := fun v hv =>
    hdevτ₁k v (Set.mem_Icc.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩)
  have hdevγ₂f : ∀ u ∈ Set.Icc (a - r₀f) (a + r₀f),
      γ u ∈ S₂ ∧ Φ₂ (γ u) = Φ₂ (γ a) + ((u - a : ℝ) : ℂ) := fun u hu =>
    hdevγ₂k u ⟨Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hdevτ₂f : ∀ v ∈ Set.Icc (b - r₀f) (b + r₀f),
      τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ) :=
    fun v hv =>
    hdevτ₂k v (Set.mem_Icc.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩)
  -- the far separation packs
  have hfar₁γ : ∀ x, a + r ≤ x → x < T - r₀f → η₁ ≤ ‖γ x - γ T‖ := by
    intro x hx1 hx2
    rcases le_or_gt (T - x) w with hcase | hcase
    · have h := hlsγT x (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        T (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
      have h2 : r₀f ≤ |x - T| := by
        rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < T - x)]
        linarith
      nlinarith only [h, h2, norm_nonneg (γ x - γ T), hCη₁, hC₁, hη₁]
    · have h := hsγ x (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        T (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        (by rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < T - x)]; linarith)
      linarith [hη₁sepγ]
  have hfar₁τ : ∀ v, r₀f < v → v ≤ b - r → η₁ ≤ ‖τ v - γ T‖ := by
    intro v hv1 hv2
    rw [← hc1]
    rcases le_or_gt v w with hcase | hcase
    · have h := hlsτ0 v (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        0 (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
      have h2 : r₀f ≤ |v - 0| := by
        rw [sub_zero, abs_of_pos (by linarith : (0:ℝ) < v)]
        linarith
      nlinarith only [h, h2, norm_nonneg (τ v - τ 0), hCη₁, hC₁, hη₁]
    · have h := hsτ v (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        0 (Set.mem_Icc.mpr ⟨le_refl 0, by linarith⟩)
        (by rw [sub_zero, abs_of_pos (by linarith : (0:ℝ) < v)]; linarith)
      linarith [hη₁sepτ]
  have hfar₂γ : ∀ x, a + r₀f < x → x ≤ T - r → η₂ ≤ ‖γ x - γ a‖ := by
    intro x hx1 hx2
    rcases le_or_gt (x - a) w with hcase | hcase
    · have h := hlsγa x (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
      have h2 : r₀f ≤ |x - a| := by
        rw [abs_of_pos (by linarith : (0:ℝ) < x - a)]
        linarith
      nlinarith only [h, h2, norm_nonneg (γ x - γ a), hCη₂, hC₂, hη₂]
    · have h := hsγ x (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        a (Set.mem_Icc.mpr ⟨le_refl a, by linarith⟩)
        (by rw [abs_of_pos (by linarith : (0:ℝ) < x - a)]; linarith)
      linarith [hη₂sepγ]
  have hfar₂τ : ∀ v, r ≤ v → v < b - r₀f → η₂ ≤ ‖τ v - γ a‖ := by
    intro v hv1 hv2
    rw [← hc2]
    rcases le_or_gt (b - v) w with hcase | hcase
    · have h := hlsτb v (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
      have h2 : r₀f ≤ |v - b| := by
        rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < b - v)]
        linarith
      nlinarith only [h, h2, norm_nonneg (τ v - τ b), hCη₂, hC₂, hη₂]
    · have h := hsτ v (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        b (Set.mem_Icc.mpr ⟨by linarith, le_refl b⟩)
        (by rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < b - v)]; linarith)
      linarith [hη₂sepτ]
  have hηd : ∀ z, z ∈ Metric.ball (γ T) η₁ → z ∈ Metric.ball (γ a) η₂ → False := by
    intro z h1 h2
    rw [Metric.mem_ball] at h1 h2
    have h3 : dist (γ T) (γ a) ≤ dist z (γ T) + dist z (γ a) := dist_triangle_left _ _ _
    rw [dist_eq_norm] at h3
    linarith [hη₁d, hη₂d]
  have hball₁f : Metric.ball (Φ₁ (γ T)) (4 * r₀f) ⊆ Φ₁ '' S₁ :=
    (Metric.ball_subset_ball (by linarith)).trans hball₁
  have hball₂f : Metric.ball (Φ₂ (γ a)) (4 * r₀f) ⊆ Φ₂ '' S₂ :=
    (Metric.ball_subset_ball (by linarith)).trans hball₂
  exact ⟨S₁, S₂, Φ₁, Φ₂, ε₁, ε₂, r, r₀f, η₁, η₂, hr, hrr₀, hε₁, hε₂, h3γ, h3τ,
    hS₁o, hΦ₁d, hΦ₁inj, hΦ₁sq, hq₁ne, hS₂o, hΦ₂d, hΦ₂inj, hΦ₂sq, hq₂ne,
    hball₁f, hball₂f, htr₁, htr₂, hdevγ₁f, hdevτ₁f, hdevγ₂f, hdevτ₂f, hκ₁b, hκ₂b,
    hfar₁γ, hfar₁τ, hfar₂γ, hfar₂τ, hηd, hη₁im, hη₂im⟩

end FinalFeed

/-- **Vertical development at the anchor**: near a chart point of an all-time vertical
trajectory, the trajectory stays in the chart and its chart value moves purely
vertically, affinely in the time offset with a single sign. -/
theorem anchor_dev {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V) (hΨsq : ∀ x ∈ V, deriv Ψ x ^ 2 = -(-q x))
    {ϑ : ℝ → ℂ} (hϑ : IsTrajOn q ϑ Set.univ) {tb : ℝ} (hmem : ϑ tb ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε₀ : ℝ, (ε₀ = 1 ∨ ε₀ = -1) ∧
      ∀ t : ℝ, |t - tb| < ρ → ϑ t ∈ V ∧
        Ψ (ϑ t) = Ψ (ϑ tb) + Complex.I * ((-ε₀ * (t - tb) : ℝ) : ℂ) := by
  have hϑc : ContinuousAt ϑ tb :=
    hϑ.cont.continuousAt (by simp : Set.univ ∈ 𝓝 tb)
  obtain ⟨ρ₂, hρ₂, hwin⟩ := Metric.eventually_nhds_iff.mp
    (hϑc.eventually_mem (hV.mem_nhds hmem))
  set ρ : ℝ := ρ₂ / 2 with hρdef
  have hρ : 0 < ρ := by linarith
  have htrk : ∀ t ∈ Set.Icc (tb - ρ) (tb + ρ), ϑ t ∈ V := by
    intro t ht
    refine hwin ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  set Φ : ℂ → ℂ := fun z => Complex.I * Ψ z with hΦdef
  have hΦd : DifferentiableOn ℂ Φ V := hΨd.const_mul _
  have hΦsq : ∀ w ∈ V, deriv Φ w ^ 2 = -q w := by
    intro w hw
    have hat : DifferentiableAt ℂ Ψ w := hΨd.differentiableAt (hV.mem_nhds hw)
    rw [hΦdef]
    rw [deriv_const_mul _ hat, mul_pow, Complex.I_sq, hΨsq w hw]
    ring
  obtain ⟨ε₀, hε₀, haff⟩ := traj_ambient_affine hV hΦd hΦsq hϑ
    (by linarith : tb - ρ ≤ tb + ρ) (Set.subset_univ _) htrk
  have hbmem : tb ∈ Set.Icc (tb - ρ) (tb + ρ) := ⟨by linarith, by linarith⟩
  have hbval := haff tb hbmem
  refine ⟨ρ, hρ, ε₀, hε₀, ?_⟩
  intro t ht
  have htmem : t ∈ Set.Icc (tb - ρ) (tb + ρ) := by
    rw [abs_lt] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨htrk t htmem, ?_⟩
  have htval := haff t htmem
  have hkey : Complex.I * Ψ (ϑ t) - Complex.I * Ψ (ϑ tb)
      = (ε₀ : ℂ) * ((t - tb : ℝ) : ℂ) := by
    have h1 : Φ (ϑ t) - Φ (ϑ tb)
        = (ε₀ : ℂ) * ((t - (tb - ρ) : ℝ) : ℂ) - (ε₀ : ℂ) * ((tb - (tb - ρ) : ℝ) : ℂ) := by
      rw [htval, hbval]
      ring
    rw [hΦdef] at h1
    simp only at h1
    rw [h1]
    push_cast
    ring
  have h2 : Ψ (ϑ t) - Ψ (ϑ tb) = -Complex.I * ((ε₀ : ℂ) * ((t - tb : ℝ) : ℂ)) := by
    have h3 := congrArg (fun z => -Complex.I * z) hkey
    try simp only at h3
    rw [show -Complex.I * (Complex.I * Ψ (ϑ t) - Complex.I * Ψ (ϑ tb))
        = -(Complex.I * Complex.I) * (Ψ (ϑ t) - Ψ (ϑ tb)) from by ring,
      Complex.I_mul_I] at h3
    simpa using h3
  rw [show Ψ (ϑ t) = Ψ (ϑ tb) + (Ψ (ϑ t) - Ψ (ϑ tb)) from by ring, h2]
  push_cast
  ring

/-- **The strict Skolemized chart chain along a leaf segment**: for a nondegenerate
compact parameter interval the chain has strictly increasing nodes and its full
chart packages are carried by functions of the piece index. -/
theorem leaf_chain_pos {q : ℂ → ℂ} {τ : ℝ → ℂ}
    (hτ : IsTrajOn (fun z => -q z) τ Set.univ) {a b : ℝ} (hab : a < b) :
    ∃ n : ℕ, ∃ v : ℕ → ℝ, ∃ V : ℕ → Set ℂ, ∃ Ψ : ℕ → ℂ → ℂ,
      v 0 = a ∧ v (n + 1) = b ∧ (∀ i, i ≤ n → v i < v (i + 1)) ∧
      (∀ i, i ≤ n → IsOpen (V i) ∧ V i ⊆ {z : ℂ | 0 < z.im} ∧
        (∀ w ∈ V i, q w ≠ 0) ∧ DifferentiableOn ℂ (Ψ i) (V i) ∧
        Set.InjOn (Ψ i) (V i) ∧ (∀ x ∈ V i, deriv (Ψ i) x ^ 2 = -(-q x)) ∧
        ∀ u ∈ Set.Icc (v i) (v (i + 1)), τ u ∈ V i) := by
  have hch : ∀ u : ℝ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, IsOpen V ∧
      V ⊆ {z : ℂ | 0 < z.im} ∧ (∀ w ∈ V, q w ≠ 0) ∧
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧
      (∀ x ∈ V, deriv Ψ x ^ 2 = -(-q x)) ∧
      ∀ u' : ℝ, |u' - u| < ρ → τ u' ∈ V := by
    intro u
    obtain ⟨V, hVo, -, hVH, hVne, Ψ, hΨd, hΨinj, hΨsq, hev⟩ :=
      hτ.chart u (Set.mem_univ u)
    rw [nhdsWithin_univ] at hev
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ρ, hρ, V, Ψ, hVo, hVH, ?_, hΨd, hΨinj, hΨsq,
      fun u' hu' => (hball (by rwa [Real.dist_eq])).1⟩
    intro w hw h0
    exact hVne w hw (by rw [h0]; exact neg_zero)
  choose ρc hρc Vc Ψc hVoc hVHc hVnec hΨdc hΨinjc hΨsqc htrkc using hch
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc (a := a) (b := b)) (fun u => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hρc x)⟩)
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt ((b - a) / δ)
  set n : ℕ := m₁ with hndef
  have hstep : (b - a) / ((n : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hm₁
    nlinarith [hδ]
  have hstep0 : 0 < (b - a) / ((n : ℝ) + 1) := by
    have h1 : (0 : ℝ) < b - a := by linarith
    positivity
  set v : ℕ → ℝ := fun i => a + (i : ℝ) * ((b - a) / ((n : ℝ) + 1)) with hvdef
  have h5 : ∀ i : ℕ, v (i + 1) - v i = (b - a) / ((n : ℝ) + 1) := by
    intro i
    rw [hvdef]
    simp only
    push_cast
    ring
  have hvmem : ∀ i : ℕ, i ≤ n + 1 → v i ∈ Set.Icc a b := by
    intro i hi
    have hprod : 0 ≤ (i : ℝ) * ((b - a) / ((n : ℝ) + 1)) :=
      mul_nonneg (Nat.cast_nonneg _) hstep0.le
    rw [hvdef]
    simp only
    constructor
    · linarith
    · have h2 : (i : ℝ) ≤ (n : ℝ) + 1 := by
        have h1 := (Nat.cast_le (α := ℝ)).mpr hi
        push_cast at h1
        linarith
      have h3 : (i : ℝ) * ((b - a) / ((n : ℝ) + 1))
          ≤ ((n : ℝ) + 1) * ((b - a) / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right h2 hstep0.le
      have h4 : ((n : ℝ) + 1) * ((b - a) / ((n : ℝ) + 1)) = b - a := by
        field_simp
      linarith
  have husel : ∀ i : ℕ, ∃ u : ℝ, i ≤ n →
      ∀ w ∈ Set.Icc (v i) (v (i + 1)), τ w ∈ Vc u := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨u, hu⟩ := hleb (v i) (hvmem i (le_trans hi (Nat.le_succ n)))
      refine ⟨u, fun _ w hw => ?_⟩
      have hwball : w ∈ Metric.ball (v i) δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith [hw.1, hδ]
        · linarith [hw.2, h5 i, hstep]
      have h7 := hu hwball
      rw [Metric.mem_ball, Real.dist_eq] at h7
      exact htrkc u w h7
    · exact ⟨0, fun h => absurd h hi⟩
  choose uw huw using husel
  refine ⟨n, v, fun i => Vc (uw i), fun i => Ψc (uw i), by simp [hvdef], ?_, ?_, ?_⟩
  · rw [hvdef]
    simp only
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · intro i _
    have := h5 i
    linarith [hstep0]
  · intro i hi
    exact ⟨hVoc _, hVHc _, hVnec _, hΨdc _, hΨinjc _, hΨsqc _, huw i hi⟩

/-- **Affinity of the leaf-family heights in a certificate chart**: near a reference
level, every visit of the level-`t` leaf to the inner ball of a margined chart at the
base leaf's target point has chart height affine in `t` with unit slope. -/
theorem cert_affine {q : ℂ → ℂ}
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} (hϑ : IsTrajOn q ϑ Set.univ)
    {τb : ℝ → ℂ} (hτb : IsTrajOn (fun z => -q z) τb Set.univ)
    {tb : ℝ} (hanch : τb 0 = ϑ tb) {ub : ℝ} (hub : 0 < ub)
    {W : Set ℂ} {Ψw : ℂ → ℂ} (hWo : IsOpen W)
    (hWd : DifferentiableOn ℂ Ψw W) (hWinj : Set.InjOn Ψw W)
    (hWH : W ⊆ {z : ℂ | 0 < z.im}) (hWne : ∀ w ∈ W, q w ≠ 0)
    (hWsq : ∀ x ∈ W, deriv Ψw x ^ 2 = -(-q x))
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψw '' W)
    (htW : τb ub ∈ W) (htWb : Ψw (τb ub) ∈ Metric.ball c₀ (R / 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ c : ℝ,
      ∀ t : ℝ, |t - tb| < ρ →
      ∀ τ : ℝ → ℂ, IsTrajOn (fun z => -q z) τ Set.univ → τ 0 = ϑ t →
      ∀ u : ℝ, τ u ∈ W → Ψw (τ u) ∈ Metric.ball c₀ R →
      (Ψw (τ u)).im = c - ε * t := by
  obtain ⟨n, v, V, Ψ, hv0, hvend, hvlt, hpack⟩ := leaf_chain_pos hτb hub
  have hVo : ∀ i, i ≤ n → IsOpen (V i) := fun i hi => (hpack i hi).1
  have hVH : ∀ i, i ≤ n → V i ⊆ {z : ℂ | 0 < z.im} :=
    fun i hi => (hpack i hi).2.1
  have hVne : ∀ i, i ≤ n → ∀ w ∈ V i, q w ≠ 0 := fun i hi => (hpack i hi).2.2.1
  have hΨd : ∀ i, i ≤ n → DifferentiableOn ℂ (Ψ i) (V i) :=
    fun i hi => (hpack i hi).2.2.2.1
  have hΨinj : ∀ i, i ≤ n → Set.InjOn (Ψ i) (V i) :=
    fun i hi => (hpack i hi).2.2.2.2.1
  have hΨsq : ∀ i, i ≤ n → ∀ x ∈ V i, deriv (Ψ i) x ^ 2 = -(-q x) :=
    fun i hi => (hpack i hi).2.2.2.2.2.1
  have htrk : ∀ i, i ≤ n → ∀ w ∈ Set.Icc (v i) (v (i + 1)), τb w ∈ V i :=
    fun i hi => (hpack i hi).2.2.2.2.2.2
  -- anchor development in the first chart
  have hanchV : ϑ tb ∈ V 0 := by
    rw [← hanch, ← hv0]
    exact htrk 0 (Nat.zero_le n) (v 0) (Set.left_mem_Icc.mpr (hvlt 0 (Nat.zero_le n)).le)
  obtain ⟨ρ₁, hρ₁, ε₀, hε₀, hdev⟩ := anchor_dev (hVo 0 (Nat.zero_le n))
    (hΨd 0 (Nat.zero_le n)) (hΨsq 0 (Nat.zero_le n)) hϑ hanchV
  -- the corridor fold
  obtain ⟨ρf, hρf, η, hη, hfold⟩ := corridor_fold hτb hVo hVH hVne hΨd
    hΨinj hΨsq hvlt htrk
  -- target-side node data between the last chart and the certificate chart
  have htVn : τb ub ∈ V n := by
    rw [← hvend]
    exact htrk n le_rfl (v (n + 1)) (Set.right_mem_Icc.mpr (hvlt n le_rfl).le)
  obtain ⟨rW, hrW, hrball⟩ := Metric.mem_nhds_iff.mp
    (((hVo n le_rfl).inter hWo).mem_nhds ⟨htVn, htW⟩)
  obtain ⟨sW, hsW, htransW⟩ := corridor_node (hΨd n le_rfl) hWd
    (fun z hz => by rw [hWsq z hz.2, hΨsq n le_rfl z hz.1]) hrW hrball
  have hdneW : deriv (Ψ n) (τb ub) ≠ 0 := by
    intro h0
    have h1 := hΨsq n le_rfl _ htVn
    rw [h0] at h1
    exact hVne n le_rfl _ htVn (by simpa using h1.symm)
  obtain ⟨δW, hδW, hδnear⟩ := chart_preimage_near_open (hVo n le_rfl)
    (hΨd n le_rfl) (hΨinj n le_rfl) htVn hdneW hrW
  refine ⟨min ρ₁ (min ρf (min δW (R / 2))),
    lt_min hρ₁ (lt_min hρf (lt_min hδW (by linarith))), sW * η * ε₀, ?_,
    (Ψw (τb ub)).im + sW * η * ε₀ * tb, ?_⟩
  · refine (abs_eq zero_le_one).mp ?_
    rw [abs_mul, abs_mul]
    rcases hsW with h | h <;> rcases hη with h' | h' <;> rcases hε₀ with h'' | h'' <;>
      rw [h, h', h''] <;> norm_num
  intro t ht τ hτ hτ0 u huW huball
  have ht1 : |t - tb| < ρ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : |t - tb| < ρf :=
    lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht3 : |t - tb| < δW := lt_of_lt_of_le ht
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have ht4 : |t - tb| < R / 2 := lt_of_lt_of_le ht
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨hϑtV, hϑtval⟩ := hdev t ht1
  set d : ℝ := -ε₀ * (t - tb) with hddef
  have hdabs : |d| = |t - tb| := by
    rw [hddef, abs_mul, abs_neg]
    rcases hε₀ with h | h <;> rw [h] <;> norm_num
  have hentry : Ψ 0 (τ 0) = Ψ 0 (τb (v 0)) + Complex.I * (d : ℂ) := by
    rw [hτ0, hv0, hanch]
    exact hϑtval
  have hentrymem : τ 0 ∈ V 0 := by
    rw [hτ0]
    exact hϑtV
  obtain ⟨w₁, hw₁V, hw₁off⟩ := hfold τ hτ d 0 (by rw [hdabs]; exact ht2)
    hentrymem hentry
  rw [hvend] at hw₁off
  -- transfer into the certificate chart
  have hdist : dist (Ψ n (τ w₁)) (Ψ n (τb ub)) < δW := by
    rw [hw₁off, dist_eq_norm,
      show Ψ n (τb ub) + Complex.I * ((η * d : ℝ) : ℂ) - Ψ n (τb ub)
          = Complex.I * ((η * d : ℝ) : ℂ) from by ring,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    have hηabs : |η| = 1 := by rcases hη with h | h <;> rw [h] <;> norm_num
    rw [hηabs, one_mul, hdabs]
    exact ht3
  have hballW : τ w₁ ∈ Metric.ball (τb ub) rW :=
    Metric.mem_ball.mpr (hδnear _ hw₁V hdist)
  have hvalW := htransW _ hballW (η * d) hw₁off
  have hw₁W : τ w₁ ∈ W := (hrball hballW).2
  -- the transfer point lies in the inner certificate ball
  have hw₁ball : Ψw (τ w₁) ∈ Metric.ball c₀ R := by
    rw [hvalW, Metric.mem_ball]
    have h6 : dist (Ψw (τb ub) + Complex.I * ((sW * (η * d) : ℝ) : ℂ)) c₀
        ≤ dist (Ψw (τb ub)) c₀ + |sW * (η * d)| := by
      rw [dist_eq_norm, dist_eq_norm,
        show Ψw (τb ub) + Complex.I * ((sW * (η * d) : ℝ) : ℂ) - c₀
            = (Ψw (τb ub) - c₀) + Complex.I * ((sW * (η * d) : ℝ) : ℂ) from by
          ring]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h7 : |sW * (η * d)| = |t - tb| := by
      rw [abs_mul, abs_mul, hdabs]
      rcases hsW with h | h <;> rcases hη with h' | h' <;> rw [h, h'] <;> norm_num
    have h8 : dist (Ψw (τb ub)) c₀ < R / 2 := Metric.mem_ball.mp htWb
    rw [h7] at h6
    linarith
  -- visit-height coherence and the affine value
  have hvis := leaf_visit_height hWo hWd hWinj hWH hWne hWsq hbigon hR
    hmarg hτ huW hw₁W huball hw₁ball
  rw [hvis, hvalW, Complex.add_im]
  have h9 : (Complex.I * ((sW * (η * d) : ℝ) : ℂ)).im = sW * (η * d) := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [h9, hddef]
  ring

section PrincipleTwo

open unitInterval

/-- **The nonnegative-winding principle**: a simple closed `C¹` loop with
nonvanishing derivative and tangent winding one has nonnegative winding about
every point off its track. -/
def NonnegWindingPrinciple₂ : Prop :=
  ∀ (ρ g : ℝ → ℂ),
    (∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ρ (g t) t) →
    ContinuousOn g (Set.Icc 0 1) →
    ρ 0 = ρ 1 → g 1 = g 0 →
    Set.InjOn ρ (Set.Ico 0 1) →
    (∀ u ∈ Set.Icc (0:ℝ) 1, g u ≠ 0) →
    ∀ (hgw : Continuous fun t : I => g ((t : ℝ))),
      windingNumber ⟨fun t : I => g ((t : ℝ)), hgw⟩ 0 = 1 →
    ∀ (hc' : Continuous fun t : I => ρ ((t : ℝ))),
    ∀ ζ : ℂ, (∀ t : I, ρ ((t : ℝ)) ≠ ζ) →
      0 ≤ windingNumber ⟨fun t : I => ρ ((t : ℝ)), hc'⟩ ζ

end PrincipleTwo

end RiemannDynamics

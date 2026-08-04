/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Winding.FourPiece

/-!
# Injectivity, separation, and the modified competitor

Injectivity of the rounded loop, the separation estimates between the tracks of a bigon,
the modified competitor, and the reduction of the main inequality to a separation
hypothesis.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

section WindingBricks

open unitInterval

/-- **First-corner vertical pinning**: a point of the first corner circle with purely
transverse chart increment is the transverse junction. -/
theorem corner1_vert {ε₁ r α ω t Y : ℝ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hr : 0 < r)
    (hα : α = -(-ε₁) * (Real.pi / 2)) (hω : ω = 1 * (-ε₁) * (Real.pi / 2))
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : -(Complex.I * (ε₁ : ℂ) * ((Y : ℝ) : ℂ)) = -((1 : ℝ) : ℂ) * r
      + Complex.I * ((-ε₁ : ℝ) : ℂ) * r
      + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ)))) :
    t = 1 ∧ Y = r := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hph : Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ))
      = Complex.I * ((α + ω * t : ℝ) : ℂ) := by push_cast; ring
  rw [hph, exp_circle] at heq
  push_cast at heq
  have hkey : ((r - r * Real.cos (α + ω*t) : ℝ) : ℂ)
      = Complex.I * ((-ε₁*r + r * Real.sin (α + ω*t) + ε₁*Y : ℝ) : ℂ) := by
    push_cast
    linear_combination heq
  obtain ⟨hre0, him0⟩ := real_eq_I_mul hkey
  have hcos : Real.cos (α + ω*t) = 1 := by
    have h1 : r * Real.cos (α + ω*t) = r * 1 := by linarith
    exact mul_left_cancel₀ hr.ne' h1
  have hφ : α + ω * t = ε₁ * ((1 - t) * (Real.pi/2)) := by rw [hα, hω]; ring
  have hφ0 : ε₁ * ((1 - t) * (Real.pi/2)) = 0 := by
    rw [hφ] at hcos
    refine cos_pin ?_ ?_ hcos <;> rcases hε₁ with h | h <;> rw [h] <;>
      nlinarith [ht.1, ht.2]
  have ht1 : t = 1 := by
    have h1 : (1 - t) * (Real.pi/2) = 0 := by
      rcases hε₁ with h | h <;> rw [h] at hφ0 <;> linarith
    rcases mul_eq_zero.mp h1 with h3 | h3
    · linarith
    · exfalso; linarith
  refine ⟨ht1, ?_⟩
  have hs0 : Real.sin (α + ω*t) = 0 := by
    rw [hφ, hφ0]
    exact Real.sin_zero
  rw [hs0] at him0
  have hε₁ne : ε₁ ≠ 0 := by rcases hε₁ with h | h <;> rw [h] <;> norm_num
  have h1 : ε₁ * Y = ε₁ * r := by linarith
  exact mul_left_cancel₀ hε₁ne h1

/-- **Second-corner vertical pinning**: a point of the second corner circle with purely
transverse chart increment is the transverse junction. -/
theorem corner2_vert {ε₂ r α ω t Z : ℝ}
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hr : 0 < r)
    (hα : α = -ε₂ * Real.pi) (hω : ω = ε₂ * (Real.pi / 2))
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : -(Complex.I * (ε₂ : ℂ) * ((Z : ℝ) : ℂ)) = -((-1 : ℝ) : ℂ) * r
      + Complex.I * (ε₂ : ℂ) * r
      + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ)))) :
    t = 0 ∧ Z = -r := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hph : Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ))
      = Complex.I * ((α + ω * t : ℝ) : ℂ) := by push_cast; ring
  rw [hph, exp_circle] at heq
  push_cast at heq
  have hkey : ((-r - r * Real.cos (α + ω*t) : ℝ) : ℂ)
      = Complex.I * ((ε₂*r + r * Real.sin (α + ω*t) + ε₂*Z : ℝ) : ℂ) := by
    push_cast
    linear_combination heq
  obtain ⟨hre0, him0⟩ := real_eq_I_mul hkey
  have hcos : Real.cos (α + ω*t) = -1 := by
    have h1 : r * Real.cos (α + ω*t) = r * (-1) := by linarith
    exact mul_left_cancel₀ hr.ne' h1
  have hφ : α + ω * t = ε₂ * (Real.pi * (t/2 - 1)) := by rw [hα, hω]; ring
  have hd1 : -Real.pi ≤ α + ω*t := by
    rw [hφ]; rcases hε₂ with h | h <;> rw [h] <;> nlinarith [ht.1, ht.2]
  have hd2 : α + ω*t ≤ Real.pi := by
    rw [hφ]; rcases hε₂ with h | h <;> rw [h] <;> nlinarith [ht.1, ht.2]
  have ht0 : t = 0 := by
    rcases cos_neg_pin hd1 hd2 hcos with hp | hp <;> rw [hφ] at hp <;>
      rcases hε₂ with h | h <;> rw [h] at hp
    · exfalso; nlinarith [ht.1, ht.2]
    · have h2 : Real.pi * (t/2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; linarith
      · linarith
    · have h2 : Real.pi * (t/2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; linarith
      · linarith
    · exfalso; nlinarith [ht.1, ht.2]
  refine ⟨ht0, ?_⟩
  have hs0 : Real.sin (α + ω*t) = 0 := by
    rw [hφ, ht0]
    rcases hε₂ with h | h <;> rw [h]
    · rw [show (1:ℝ) * (Real.pi * (0/2 - 1)) = -Real.pi by ring, Real.sin_neg,
        Real.sin_pi]
      norm_num
    · rw [show ((-1:ℝ)) * (Real.pi * (0/2 - 1)) = Real.pi by ring]
      exact Real.sin_pi
  rw [hs0] at him0
  have hε₂ne : ε₂ ≠ 0 := by rcases hε₂ with h | h <;> rw [h] <;> norm_num
  have h1 : ε₂ * Z = ε₂ * (-r) := by linarith
  exact mul_left_cancel₀ hε₂ne h1

/-- **Second-corner horizontal pinning**: a point of the second corner circle with
purely real chart increment is the horizontal junction. -/
theorem corner2_horiz {ε₂ r α ω t X : ℝ}
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hr : 0 < r)
    (hα : α = -ε₂ * Real.pi) (hω : ω = ε₂ * (Real.pi / 2))
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : ((X : ℝ) : ℂ) = -((-1 : ℝ) : ℂ) * r + Complex.I * (ε₂ : ℂ) * r
      + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ)))) :
    t = 1 ∧ X = r := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hph : Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ))
      = Complex.I * ((α + ω * t : ℝ) : ℂ) := by push_cast; ring
  rw [hph, exp_circle] at heq
  push_cast at heq
  have hkey : ((X - (r + r * Real.cos (α + ω*t)) : ℝ) : ℂ)
      = Complex.I * ((ε₂*r + r * Real.sin (α + ω*t) : ℝ) : ℂ) := by
    push_cast
    linear_combination heq
  obtain ⟨hre0, him0⟩ := real_eq_I_mul hkey
  have hsin : Real.sin (α + ω*t) = -ε₂ := by
    have h1 : r * Real.sin (α + ω*t) = r * (-ε₂) := by linarith
    exact mul_left_cancel₀ hr.ne' h1
  have hφ : α + ω * t = ε₂ * (Real.pi * (t/2 - 1)) := by rw [hα, hω]; ring
  have ht1 : t = 1 := by
    rcases hε₂ with h | h
    · rw [hφ, h, one_mul, show Real.pi * (t/2 - 1) = -(Real.pi * (1 - t/2)) by ring,
        Real.sin_neg] at hsin
      have hsin' : Real.sin (Real.pi * (1 - t/2)) = 1 := by linarith
      have hp := sin_pin (by nlinarith [ht.1, ht.2]) (by nlinarith [ht.1, ht.2])
        hsin'
      have h2 : Real.pi * ((1 - t)/2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; linarith
      · linarith
    · rw [hφ, h, show ((-1:ℝ)) * (Real.pi * (t/2 - 1)) = Real.pi * (1 - t/2)
          by ring] at hsin
      have hsin' : Real.sin (Real.pi * (1 - t/2)) = 1 := by linarith
      have hp := sin_pin (by nlinarith [ht.1, ht.2]) (by nlinarith [ht.1, ht.2])
        hsin'
      have h2 : Real.pi * ((1 - t)/2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; linarith
      · linarith
  refine ⟨ht1, ?_⟩
  rw [hφ, ht1] at hre0
  have hcos : Real.cos (ε₂ * (Real.pi * (1/2 - 1))) = 0 := by
    rcases hε₂ with h | h <;> rw [h]
    · rw [show (1:ℝ) * (Real.pi * (1/2 - 1)) = -(Real.pi/2) by ring, Real.cos_neg]
      exact Real.cos_pi_div_two
    · rw [show ((-1:ℝ)) * (Real.pi * (1/2 - 1)) = Real.pi/2 by ring]
      exact Real.cos_pi_div_two
  rw [hcos] at hre0
  linarith

set_option maxHeartbeats 400000 in
-- Heartbeats: the loop-hull convexity check unfolds the four-piece parametrization.
/-- **The loop hull**: a continuous loop in the upper half plane lies in a convex open
set contained in the upper half plane in which the quadratic differential has finitely
many zeros. -/
theorem loop_hull {q : ℂ → ℂ} {ρ : ℝ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hρc : ContinuousOn ρ (Set.Icc 0 1))
    (hρH : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (ρ u).im) :
    ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ U ⊆ {z : ℂ | 0 < z.im}
      ∧ {z ∈ U | q z = 0}.Finite ∧ ∀ u ∈ Set.Icc (0:ℝ) 1, ρ u ∈ U := by
  have hK : IsCompact (ρ '' Set.Icc 0 1) := isCompact_Icc.image_of_continuousOn hρc
  have hKne : (ρ '' Set.Icc 0 1).Nonempty :=
    ⟨ρ 0, ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩⟩
  have hKH : ρ '' Set.Icc 0 1 ⊆ {z : ℂ | 0 < z.im} := by
    rintro z ⟨u, hu, rfl⟩
    exact hρH u hu
  obtain ⟨U, hUo, hUconv, hKU, hclc, hclH⟩ := rectangle_hull hK hKne hKH
  refine ⟨U, hUo, hUconv, fun z hz => hclH (subset_closure hz),
    (zeros_finite_in_compact hq hq0 hclc hclH).subset ?_,
    fun u hu => hKU ⟨u, hu, rfl⟩⟩
  intro z hz
  exact ⟨subset_closure hz.1, hz.2⟩

/-- **Ramped-arc speed nonvanishing**: the ramp speed is positive and the trajectory
velocity is nonvanishing, so the ramped velocity field has no zeros. -/
theorem rampSpeed_ne {f : ℝ → ℂ} {c v L : ℝ} (hv : 0 < v) (h3 : v < 3 * L)
    (hd : ∀ w ∈ Set.Icc c (c + L), deriv f w ≠ 0) :
    ∀ u ∈ Set.Icc (0:ℝ) 1, rampArcSpeed f c v L u ≠ 0 := by
  intro u hu
  rw [rampArcSpeed_apply]
  refine mul_ne_zero ?_ (hd _ (cubicRamp_mapsTo (a := c) hv h3 u hu))
  have h := cubicRampSpeed_pos hv h3 u hu
  exact_mod_cast h.ne'

/-- **Corner speed nonvanishing**: the circle numerator and the chart derivative are
both nonvanishing. -/
theorem cornerSpeed_ne {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z) (hqne : ∀ z ∈ S, q z ≠ 0)
    {c : ℂ} {r α ω : ℝ} (hr : 0 < r) (hω : ω ≠ 0)
    (htr : ∀ u : ℝ, c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      ∈ Φ '' S) :
    ∀ u : ℝ, cornerSpeed Φ S c r α ω u ≠ 0 := by
  intro u
  have hpk := cornerPiece_package hS hΦ hinj hsq hqne hr hω htr u
  have hden : deriv Φ (cornerPiece Φ S c r α ω u) ≠ 0 := by
    intro h0
    have h1 := hsq _ hpk.1
    rw [h0] at h1
    exact hqne _ hpk.1 (by simpa using h1.symm)
  have hnum : (r : ℂ) * Complex.I * (ω : ℂ)
      * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (u : ℂ))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ Complex.I_ne_zero) ?_)
      (Complex.exp_ne_zero _)
    · exact_mod_cast hr.ne'
    · exact_mod_cast hω
  exact div_ne_zero hnum hden

/-- **Assembled velocity nonvanishing**: the quarter-schedule velocity loop of four
nonvanishing fields has no zeros. -/
theorem quarterPW_ne {g₀ g₁ g₂ g₃ : ℝ → ℂ}
    (h₀ : ∀ u ∈ Set.Icc (0 : ℝ) 1, g₀ u ≠ 0) (h₁ : ∀ u ∈ Set.Icc (0 : ℝ) 1, g₁ u ≠ 0)
    (h₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, g₂ u ≠ 0)
    (h₃ : ∀ u ∈ Set.Icc (0 : ℝ) 1, g₃ u ≠ 0) :
    ∀ u ∈ Set.Icc (0:ℝ) 1, (4:ℂ) * quarterPW g₀ g₁ g₂ g₃ u ≠ 0 := by
  intro u hu
  refine mul_ne_zero (by norm_num) ?_
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

/-- **Chart shrinkage**: near a point with nonvanishing chart derivative, every spatial
shrinkage of the chart still covers an image ball. -/
theorem chart_shrink {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) {p : ℂ} (hp : p ∈ S)
    (hΦne : deriv Φ p ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, Metric.ball (Φ p) ρ ⊆ Φ '' (S ∩ Metric.ball p η) := by
  have han : AnalyticAt ℂ Φ p := (hΦd.analyticOnNhd hS) p hp
  have hst : HasStrictDerivAt Φ (deriv Φ p) p := han.hasStrictDerivAt
  have hmap := hst.map_nhds_eq hΦne
  have h1 : Φ '' (S ∩ Metric.ball p η) ∈ 𝓝 (Φ p) := by
    rw [← hmap]
    exact Filter.image_mem_map
      (Filter.inter_mem (hS.mem_nhds hp) (Metric.ball_mem_nhds p hη))
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp h1
  exact ⟨ρ, hρ, hsub⟩

set_option maxHeartbeats 400000 in
-- Heartbeats: the closure matching elaborates all four corner transitions.
/-- **Monogon closure**: a simple closed trajectory loop is `C¹`-closed — the canonical
velocities at the two endpoints agree. -/
theorem monogon_closed {q : ℂ → ℂ} {γ : ℝ → ℂ} {s : Set ℝ} {c d : ℝ}
    (hγ : IsTrajOn q γ s) (hcd : c < d)
    (hs : ∀ w ∈ Set.Icc c d, s ∈ nhds w)
    (hcl : γ c = γ d) (hinj : Set.InjOn γ (Set.Ico c d)) :
    deriv γ c = deriv γ d := by
  have hcmem : c ∈ s := mem_of_mem_nhds (hs c ⟨le_refl c, le_of_lt hcd⟩)
  have hdmem : d ∈ s := mem_of_mem_nhds (hs d ⟨le_of_lt hcd, le_refl d⟩)
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hγ.chart d hdmem
  rw [nhdsWithin_eq_nhds.mpr (hs d ⟨le_of_lt hcd, le_refl d⟩)] at hev
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.eventually_nhds_iff.mp hev
  have hγcU : γ c ∈ U := by rw [hcl]; exact hpU
  have hcont : ContinuousAt γ c :=
    (hγ.cont c hcmem).continuousAt (hs c ⟨le_refl c, le_of_lt hcd⟩)
  have hUc : ∀ᶠ u in 𝓝 c, γ u ∈ U := hcont.eventually_mem (hUo.mem_nhds hγcU)
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.eventually_nhds_iff.mp hUc
  set δ₀ : ℝ := min (δ₂/2) ((d - c)/3) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by linarith)
  have hδ₀a : δ₀ ≤ δ₂/2 := min_le_left _ _
  have hδ₀b : δ₀ ≤ (d - c)/3 := min_le_right _ _
  have hIsub : Set.Icc c (c + δ₀) ⊆ s := by
    intro w hw
    exact mem_of_mem_nhds (hs w ⟨hw.1, by linarith [hw.2]⟩)
  have htrack : ∀ u ∈ Set.Icc c (c + δ₀), γ u ∈ U := by
    intro u hu
    refine hball₂ ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  obtain ⟨ε, hε, haff⟩ := traj_ambient_affine hUo hΦd hΦsq hγ
    (by linarith : c ≤ c + δ₀) hIsub htrack
  -- the canonical velocities and the incoming chart velocity
  have hdd := (traj_deriv_continuous hγ d hdmem (hs d ⟨le_of_lt hcd, le_refl d⟩)).1
  have hdc := (traj_deriv_continuous hγ c hcmem (hs c ⟨le_refl c, le_of_lt hcd⟩)).1
  have hdev₁ : ∀ u ∈ Set.Icc (d - δ₁/2) (d + δ₁/2),
      γ u ∈ U ∧ Φ (γ u) = Φ (γ d) + ((u - d : ℝ) : ℂ) := by
    intro u hu
    refine hball₁ ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  have hveld : deriv Φ (γ d) * deriv γ d = 1 :=
    dev_velocity hUo hΦd hdd (by linarith : (0:ℝ) < δ₁/2) hdev₁
  -- the outgoing one-sided slope
  have hΦat : DifferentiableAt ℂ Φ (γ c) := hΦd.differentiableAt (hUo.mem_nhds hγcU)
  have hchain : HasDerivAt (fun u => Φ (γ u)) (deriv Φ (γ c) * deriv γ c) c :=
    HasDerivAt.comp (h := γ) c hΦat.hasDerivAt hdc
  have haffd : HasDerivAt (fun t : ℝ => Φ (γ c) + (ε : ℂ) * ((t - c : ℝ) : ℂ))
      ((ε : ℂ)) c := by
    have h1 : HasDerivAt (fun z : ℂ => Φ (γ c) + (ε : ℂ) * (z - (c : ℂ)))
        ((ε : ℂ)) ((c : ℝ) : ℂ) := by
      simpa using (((hasDerivAt_id ((c : ℝ) : ℂ)).sub_const
        ((c : ℝ) : ℂ)).const_mul ((ε : ℂ))).const_add (Φ (γ c))
    have h2 := h1.comp_ofReal
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with u
    push_cast
    ring
  have hEqEv : (fun u => Φ (γ u))
      =ᶠ[nhdsWithin c (Set.Ici c)]
      (fun t : ℝ => Φ (γ c) + (ε : ℂ) * ((t - c : ℝ) : ℂ)) := by
    filter_upwards [Icc_mem_nhdsGE (by linarith : c < c + δ₀)] with u hu
    exact haff u hu
  have hB : HasDerivWithinAt (fun u => Φ (γ u)) ((ε : ℂ)) (Set.Ici c) c :=
    haffd.hasDerivWithinAt.congr_of_eventuallyEq hEqEv (by norm_num)
  have huniq : deriv Φ (γ c) * deriv γ c = (ε : ℂ) := by
    have h1 := hchain.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici c)
    have h2 := hB.derivWithin (uniqueDiffWithinAt_Ici c)
    rw [← h1, ← h2]
  rcases hε with hε1 | hε1
  · rw [hε1] at huniq
    rw [hcl] at huniq
    have hne : deriv Φ (γ d) ≠ 0 := left_ne_zero_of_mul_eq_one hveld
    have h3 : deriv Φ (γ d) * deriv γ c = deriv Φ (γ d) * deriv γ d := by
      rw [hveld]
      exact_mod_cast huniq
    exact mul_left_cancel₀ hne h3
  · exfalso
    set t : ℝ := min δ₀ (δ₁/2) with htdef
    have ht : 0 < t := lt_min hδ₀ (by linarith)
    have hta : t ≤ δ₀ := min_le_left _ _
    have htb : t ≤ δ₁/2 := min_le_right _ _
    have hout : Φ (γ (c + t)) = Φ (γ c) + (ε : ℂ) * ((c + t - c : ℝ) : ℂ) :=
      haff (c + t) ⟨by linarith, by linarith⟩
    have hin := (hdev₁ (d - t) ⟨by linarith, by linarith⟩).2
    have hΦeq : Φ (γ (c + t)) = Φ (γ (d - t)) := by
      rw [hout, hin, hcl, hε1]
      push_cast
      ring
    have hmem1 : γ (c + t) ∈ U := by
      refine hball₂ ?_
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hmem2 : γ (d - t) ∈ U := (hdev₁ (d - t) ⟨by linarith, by linarith⟩).1
    have hpteq := hΦinj hmem1 hmem2 hΦeq
    have hij := hinj
      (Set.mem_Ico.mpr ⟨by linarith, by linarith⟩)
      (Set.mem_Ico.mpr ⟨by linarith, by linarith⟩) hpteq
    linarith

/-- **The monogon four-quarter bundle**: the four ramped quarters of a closed trajectory
arc assemble to a piecewise-`C¹` loop; all junction positions and velocities match, the
wrap through the closure point and the closure velocity. -/
theorem monogon_bundle {q : ℂ → ℂ} {γ : ℝ → ℂ} {c ℓ : ℝ} (hℓ : 0 < ℓ)
    (hdA : ∀ w ∈ Set.Icc c (c + 4 * ℓ), HasDerivAt γ (deriv γ w) w)
    (hdC : ContinuousOn (deriv γ) (Set.Icc c (c + 4 * ℓ)))
    (hqγ : ∀ w ∈ Set.Icc c (c + 4 * ℓ), q (γ w) * (deriv γ w) ^ 2 = -1)
    (hcl : γ c = γ (c + 4 * ℓ)) (hclv : deriv γ c = deriv γ (c + 4 * ℓ)) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt
      (quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
        (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ))
      (4 * quarterPW (rampArcSpeed γ c ℓ ℓ) (rampArcSpeed γ (c + ℓ) ℓ ℓ)
        (rampArcSpeed γ (c + 2*ℓ) ℓ ℓ) (rampArcSpeed γ (c + 3*ℓ) ℓ ℓ) t) t)
    ∧ rampArc γ c ℓ ℓ 1 = rampArc γ (c + ℓ) ℓ ℓ 0
    ∧ rampArc γ (c + ℓ) ℓ ℓ 1 = rampArc γ (c + 2*ℓ) ℓ ℓ 0
    ∧ rampArc γ (c + 2*ℓ) ℓ ℓ 1 = rampArc γ (c + 3*ℓ) ℓ ℓ 0
    ∧ rampArc γ (c + 3*ℓ) ℓ ℓ 1 = rampArc γ c ℓ ℓ 0
    ∧ rampArcSpeed γ c ℓ ℓ 1 = rampArcSpeed γ (c + ℓ) ℓ ℓ 0
    ∧ rampArcSpeed γ (c + ℓ) ℓ ℓ 1 = rampArcSpeed γ (c + 2*ℓ) ℓ ℓ 0
    ∧ rampArcSpeed γ (c + 2*ℓ) ℓ ℓ 1 = rampArcSpeed γ (c + 3*ℓ) ℓ ℓ 0
    ∧ rampArcSpeed γ (c + 3*ℓ) ℓ ℓ 1 = rampArcSpeed γ c ℓ ℓ 0 := by
  have h3 : ℓ < 3*ℓ := by linarith
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
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
  obtain ⟨hA1, -, -, -, -, -, -, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₀ hc₀ hq₀
  obtain ⟨hB1, -, -, -, -, -, -, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₁ hc₁ hq₁
  obtain ⟨hC1, -, -, -, -, -, -, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₂ hc₂ hq₂
  obtain ⟨hD1, -, -, -, -, -, -, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₃ hc₃ hq₃
  refine ⟨quarterPW_hasDerivAt_Icc (fun u hu => hA1 u hu) (fun u hu => hB1 u hu)
      (fun u hu => hC1 u hu) (fun u hu => hD1 u hu)
      ?hv01 ?hv12 ?hv23 ?hg01 ?hg12 ?hg23,
    ?hv01, ?hv12, ?hv23, ?hv30, ?hg01, ?hg12, ?hg23, ?hg30⟩
  case hv01 =>
    rw [rampArc_apply, rampArc_apply, cubicRamp_one, cubicRamp_zero]
  case hv12 =>
    rw [rampArc_apply, rampArc_apply, cubicRamp_one, cubicRamp_zero,
      show (c + ℓ) + ℓ = c + 2*ℓ by ring]
  case hv23 =>
    rw [rampArc_apply, rampArc_apply, cubicRamp_one, cubicRamp_zero,
      show (c + 2*ℓ) + ℓ = c + 3*ℓ by ring]
  case hv30 =>
    rw [rampArc_apply, rampArc_apply, cubicRamp_one, cubicRamp_zero,
      show (c + 3*ℓ) + ℓ = c + 4*ℓ by ring, ← hcl]
  case hg01 =>
    rw [rampArcSpeed_apply, rampArcSpeed_apply, cubicRampSpeed_one,
      cubicRampSpeed_zero, cubicRamp_one, cubicRamp_zero]
  case hg12 =>
    rw [rampArcSpeed_apply, rampArcSpeed_apply, cubicRampSpeed_one,
      cubicRampSpeed_zero, cubicRamp_one, cubicRamp_zero,
      show (c + ℓ) + ℓ = c + 2*ℓ by ring]
  case hg23 =>
    rw [rampArcSpeed_apply, rampArcSpeed_apply, cubicRampSpeed_one,
      cubicRampSpeed_zero, cubicRamp_one, cubicRamp_zero,
      show (c + 2*ℓ) + ℓ = c + 3*ℓ by ring]
  case hg30 =>
    rw [rampArcSpeed_apply, rampArcSpeed_apply, cubicRampSpeed_one,
      cubicRampSpeed_zero, cubicRamp_one, cubicRamp_zero,
      show (c + 3*ℓ) + ℓ = c + 4*ℓ by ring, ← hclv]

/-- **The monogon winding count**: the assembled four-quarter loop of a `C¹`-closed
trajectory arc has argument-principle count zero, for any continuity witnesses of the
two winding curves. -/
theorem monogon_count {q : ℂ → ℂ} {γ : ℝ → ℂ} {c ℓ : ℝ} (hℓ : 0 < ℓ)
    (hdA : ∀ w ∈ Set.Icc c (c + 4 * ℓ), HasDerivAt γ (deriv γ w) w)
    (hdC : ContinuousOn (deriv γ) (Set.Icc c (c + 4 * ℓ)))
    (hqγ : ∀ w ∈ Set.Icc c (c + 4 * ℓ), q (γ w) * (deriv γ w) ^ 2 = -1)
    (hcl : γ c = γ (c + 4 * ℓ)) (hclv : deriv γ c = deriv γ (c + 4 * ℓ)) :
    ∀ (hqc : Continuous fun t : I => q (quarterPW
        (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
        (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ) ((t : ℝ))))
      (hgc : Continuous fun t : I => 4 * quarterPW
        (rampArcSpeed γ c ℓ ℓ) (rampArcSpeed γ (c + ℓ) ℓ ℓ)
        (rampArcSpeed γ (c + 2*ℓ) ℓ ℓ) (rampArcSpeed γ (c + 3*ℓ) ℓ ℓ) ((t : ℝ))),
      windingNumber ⟨_, hqc⟩ 0 + 2 * windingNumber ⟨_, hgc⟩ 0 = (0 : ℤ) := by
  intro hqc hgc
  have h3 : ℓ < 3*ℓ := by linarith
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
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
  obtain ⟨-, -, -, -, hv30, hg01, hg12, hg23, hg30⟩ :=
    monogon_bundle hℓ hdA hdC hqγ hcl hclv
  obtain ⟨-, -, -, -, -, hA6, hA7, hA8⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₀ hc₀ hq₀
  obtain ⟨-, -, -, -, -, hB6, hB7, hB8⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₁ hc₁ hq₁
  obtain ⟨-, -, -, -, -, hC6, hC7, hC8⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₂ hc₂ hq₂
  obtain ⟨-, -, -, -, -, hD6, hD7, hD8⟩ :=
    arc_piece (f := γ) (df := deriv γ) hℓ h3 hd₃ hc₃ hq₃
  have hcl1 : max 0 (min 1 (1:ℝ)) = 1 := by norm_num
  have hcl0 : max 0 (min 1 (0:ℝ)) = 0 := by norm_num
  have hLj : ((Real.log ((cubicRampSpeed ℓ ℓ (max 0 (min 1 (1:ℝ))))^2) : ℝ) : ℂ)
        + (Real.pi : ℂ) * Complex.I
      = ((Real.log ((cubicRampSpeed ℓ ℓ (max 0 (min 1 (0:ℝ))))^2) : ℝ) : ℂ)
        + (Real.pi : ℂ) * Complex.I := by
    rw [hcl1, hcl0, cubicRampSpeed_one, cubicRampSpeed_zero]
  have hLm : (((Real.log ((cubicRampSpeed ℓ ℓ (max 0 (min 1 (1:ℝ))))^2) : ℝ) : ℂ)
        + (Real.pi : ℂ) * Complex.I)
      - (((Real.log ((cubicRampSpeed ℓ ℓ (max 0 (min 1 (0:ℝ))))^2) : ℝ) : ℂ)
        + (Real.pi : ℂ) * Complex.I)
      = 2 * Real.pi * Complex.I * ((0 : ℤ) : ℂ) := by
    rw [hcl1, hcl0, cubicRampSpeed_one, cubicRampSpeed_zero]
    push_cast
    ring
  exact rounded_count_Icc (q := q)
    (p₀ := rampArc γ c ℓ ℓ) (p₁ := rampArc γ (c + ℓ) ℓ ℓ)
    (p₂ := rampArc γ (c + 2*ℓ) ℓ ℓ) (p₃ := rampArc γ (c + 3*ℓ) ℓ ℓ)
    (g₀ := rampArcSpeed γ c ℓ ℓ) (g₁ := rampArcSpeed γ (c + ℓ) ℓ ℓ)
    (g₂ := rampArcSpeed γ (c + 2*ℓ) ℓ ℓ) (g₃ := rampArcSpeed γ (c + 3*ℓ) ℓ ℓ)
    (m := 0)
    hA7 hB7 hC7 hD7 hA8.continuousOn hB8.continuousOn hC8.continuousOn hD8.continuousOn
    hv30 hg01 hg12 hg23 hg30 hLj hLj hLj hLm
    hA6 hB6 hC6 hD6 hqc

set_option maxHeartbeats 400000 in
-- Heartbeats: the four-quarter reparametrization splits into many interval cases.
/-- **Monogon loop injectivity**: the four-quarter reparametrization of an injective
closed arc is injective on the fundamental domain. -/
theorem monogon_injOn {γ : ℝ → ℂ} {c ℓ : ℝ} (hℓ : 0 < ℓ)
    (hinj : Set.InjOn γ (Set.Ico c (c + 4 * ℓ))) :
    Set.InjOn (quarterPW (rampArc γ c ℓ ℓ) (rampArc γ (c + ℓ) ℓ ℓ)
      (rampArc γ (c + 2*ℓ) ℓ ℓ) (rampArc γ (c + 3*ℓ) ℓ ℓ)) (Set.Ico 0 1) := by
  have h3 : ℓ < 3*ℓ := by linarith
  have hlt₃ : ∀ s ∈ Set.Icc (0:ℝ) 1, s < 1 →
      cubicRamp (c + 3*ℓ) ℓ ℓ s < c + 4*ℓ := by
    intro s hs hs1
    have h1 := (cubicRamp_strictMono (a := c + 3*ℓ) hℓ h3) hs
      (Set.right_mem_Icc.mpr zero_le_one) hs1
    rw [cubicRamp_one] at h1
    linarith
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) 1, cubicRamp c ℓ ℓ s ∈ Set.Ico c (c + 4*ℓ) := by
    intro s hs
    have h := cubicRamp_mapsTo (a := c) hℓ h3 s hs
    exact ⟨h.1, by linarith [h.2]⟩
  have hmem₁ : ∀ s ∈ Set.Icc (0:ℝ) 1,
      cubicRamp (c + ℓ) ℓ ℓ s ∈ Set.Ico c (c + 4*ℓ) := by
    intro s hs
    have h := cubicRamp_mapsTo (a := c + ℓ) hℓ h3 s hs
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmem₂ : ∀ s ∈ Set.Icc (0:ℝ) 1,
      cubicRamp (c + 2*ℓ) ℓ ℓ s ∈ Set.Ico c (c + 4*ℓ) := by
    intro s hs
    have h := cubicRamp_mapsTo (a := c + 2*ℓ) hℓ h3 s hs
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmem₃ : ∀ s ∈ Set.Icc (0:ℝ) 1, s < 1 →
      cubicRamp (c + 3*ℓ) ℓ ℓ s ∈ Set.Ico c (c + 4*ℓ) := by
    intro s hs hs1
    have h := cubicRamp_mapsTo (a := c + 3*ℓ) hℓ h3 s hs
    exact ⟨by linarith [h.1], hlt₃ s hs hs1⟩
  have hsame : ∀ base : ℝ, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      cubicRamp base ℓ ℓ s ∈ Set.Ico c (c + 4*ℓ)
      → cubicRamp base ℓ ℓ t ∈ Set.Ico c (c + 4*ℓ)
      → rampArc γ base ℓ ℓ s = rampArc γ base ℓ ℓ t → s = t := by
    intro base s hs t ht hms hmt heq
    rw [rampArc_apply, rampArc_apply] at heq
    exact (cubicRamp_strictMono (a := base) hℓ h3).injOn hs ht (hinj hms hmt heq)
  have hadj : ∀ b₁ b₂ : ℝ, b₂ = b₁ + ℓ → ∀ s ∈ Set.Icc (0:ℝ) 1,
      ∀ t ∈ Set.Icc (0:ℝ) 1,
      cubicRamp b₁ ℓ ℓ s ∈ Set.Ico c (c + 4*ℓ)
      → cubicRamp b₂ ℓ ℓ t ∈ Set.Ico c (c + 4*ℓ)
      → rampArc γ b₁ ℓ ℓ s = rampArc γ b₂ ℓ ℓ t → s = 1 ∧ t = 0 := by
    intro b₁ b₂ hb s hs t ht hms hmt heq
    rw [rampArc_apply, rampArc_apply] at heq
    have harg := hinj hms hmt heq
    have h1 := cubicRamp_mapsTo (a := b₁) hℓ h3 s hs
    have h2 := cubicRamp_mapsTo (a := b₂) hℓ h3 t ht
    have hs1 : cubicRamp b₁ ℓ ℓ s = b₁ + ℓ := by
      refine le_antisymm h1.2 ?_
      rw [harg]
      linarith [h2.1]
    have ht0 : cubicRamp b₂ ℓ ℓ t = b₂ := by
      refine le_antisymm ?_ h2.1
      rw [← harg]
      linarith [h1.2]
    constructor
    · refine (cubicRamp_strictMono (a := b₁) hℓ h3).injOn hs
        (Set.right_mem_Icc.mpr zero_le_one) ?_
      rw [cubicRamp_one]
      exact hs1
    · refine (cubicRamp_strictMono (a := b₂) hℓ h3).injOn ht
        (Set.left_mem_Icc.mpr zero_le_one) ?_
      rw [cubicRamp_zero]
      exact ht0
  have hdisj : ∀ b₁ b₂ : ℝ, b₁ + ℓ < b₂ → ∀ s ∈ Set.Icc (0:ℝ) 1,
      ∀ t ∈ Set.Icc (0:ℝ) 1,
      cubicRamp b₁ ℓ ℓ s ∈ Set.Ico c (c + 4*ℓ)
      → cubicRamp b₂ ℓ ℓ t ∈ Set.Ico c (c + 4*ℓ)
      → rampArc γ b₁ ℓ ℓ s ≠ rampArc γ b₂ ℓ ℓ t := by
    intro b₁ b₂ hgap s hs t ht hms hmt heq
    rw [rampArc_apply, rampArc_apply] at heq
    have harg := hinj hms hmt heq
    have h1 := cubicRamp_mapsTo (a := b₁) hℓ h3 s hs
    have h2 := cubicRamp_mapsTo (a := b₂) hℓ h3 t ht
    linarith [h1.2, h2.1]
  intro x hx y hy heq
  by_cases hx1 : x ≤ 1/4
  · rw [quarterPW_eval₀ hx1] at heq
    have hxm : 4*x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith⟩
    by_cases hy1 : y ≤ 1/4
    · rw [quarterPW_eval₀ hy1] at heq
      have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
      have h := hsame c _ hxm _ hym (hmem₀ _ hxm) (hmem₀ _ hym) heq
      linarith
    · by_cases hy2 : y ≤ 1/2
      · rw [quarterPW_eval₁ hy1 hy2] at heq
        have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith [not_le.mp hy1], by linarith⟩
        obtain ⟨h1, h2⟩ := hadj c (c + ℓ) rfl _ hxm _ hym
          (hmem₀ _ hxm) (hmem₁ _ hym) heq
        linarith
      · by_cases hy3 : y ≤ 3/4
        · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
          have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by linarith [not_le.mp hy2], by linarith⟩
          exact absurd heq (hdisj c (c + 2*ℓ) (by linarith) _ hxm _ hym
            (hmem₀ _ hxm) (hmem₂ _ hym))
        · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
          have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
          exact absurd heq (hdisj c (c + 3*ℓ) (by linarith) _ hxm _ hym
            (hmem₀ _ hxm) (hmem₃ _ hym (by linarith [hy.2])))
  · by_cases hx2 : x ≤ 1/2
    · rw [quarterPW_eval₁ hx1 hx2] at heq
      have hxm : 4*x - 1 ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by linarith [not_le.mp hx1], by linarith⟩
      by_cases hy1 : y ≤ 1/4
      · rw [quarterPW_eval₀ hy1] at heq
        have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
        obtain ⟨h1, h2⟩ := hadj c (c + ℓ) rfl _ hym _ hxm
          (hmem₀ _ hym) (hmem₁ _ hxm) heq.symm
        linarith
      · by_cases hy2 : y ≤ 1/2
        · rw [quarterPW_eval₁ hy1 hy2] at heq
          have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by linarith [not_le.mp hy1], by linarith⟩
          have h := hsame (c + ℓ) _ hxm _ hym (hmem₁ _ hxm) (hmem₁ _ hym) heq
          linarith
        · by_cases hy3 : y ≤ 3/4
          · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
            have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy2], by linarith⟩
            obtain ⟨h1, h2⟩ := hadj (c + ℓ) (c + 2*ℓ) (by ring) _ hxm _ hym
              (hmem₁ _ hxm) (hmem₂ _ hym) heq
            exfalso; linarith [not_le.mp hy2]
          · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
            have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
            exact absurd heq (hdisj (c + ℓ) (c + 3*ℓ) (by linarith) _ hxm _ hym
              (hmem₁ _ hxm) (hmem₃ _ hym (by linarith [hy.2])))
    · by_cases hx3 : x ≤ 3/4
      · rw [quarterPW_eval₂ hx1 hx2 hx3] at heq
        have hxm : 4*x - 2 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith [not_le.mp hx2], by linarith⟩
        by_cases hy1 : y ≤ 1/4
        · rw [quarterPW_eval₀ hy1] at heq
          have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
          exact absurd heq.symm (hdisj c (c + 2*ℓ) (by linarith) _ hym _ hxm
            (hmem₀ _ hym) (hmem₂ _ hxm))
        · by_cases hy2 : y ≤ 1/2
          · rw [quarterPW_eval₁ hy1 hy2] at heq
            have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy1], by linarith⟩
            obtain ⟨h1, h2⟩ := hadj (c + ℓ) (c + 2*ℓ) (by ring) _ hym _ hxm
              (hmem₁ _ hym) (hmem₂ _ hxm) heq.symm
            exfalso; linarith [not_le.mp hx2]
          · by_cases hy3 : y ≤ 3/4
            · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
              have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy2], by linarith⟩
              have h := hsame (c + 2*ℓ) _ hxm _ hym (hmem₂ _ hxm) (hmem₂ _ hym) heq
              linarith
            · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
              have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
              obtain ⟨h1, h2⟩ := hadj (c + 2*ℓ) (c + 3*ℓ) (by ring) _ hxm _ hym
                (hmem₂ _ hxm) (hmem₃ _ hym (by linarith [hy.2])) heq
              exfalso; linarith [not_le.mp hy3]
      · rw [quarterPW_eval₃ hx1 hx2 hx3] at heq
        have hxm : 4*x - 3 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith [not_le.mp hx3], by linarith [hx.2]⟩
        by_cases hy1 : y ≤ 1/4
        · rw [quarterPW_eval₀ hy1] at heq
          have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
          exact absurd heq.symm (hdisj c (c + 3*ℓ) (by linarith) _ hym _ hxm
            (hmem₀ _ hym) (hmem₃ _ hxm (by linarith [hx.2])))
        · by_cases hy2 : y ≤ 1/2
          · rw [quarterPW_eval₁ hy1 hy2] at heq
            have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy1], by linarith⟩
            exact absurd heq.symm (hdisj (c + ℓ) (c + 3*ℓ) (by linarith) _ hym _ hxm
              (hmem₁ _ hym) (hmem₃ _ hxm (by linarith [hx.2])))
          · by_cases hy3 : y ≤ 3/4
            · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
              have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy2], by linarith⟩
              obtain ⟨h1, h2⟩ := hadj (c + 2*ℓ) (c + 3*ℓ) (by ring) _ hym _ hxm
                (hmem₂ _ hym) (hmem₃ _ hxm (by linarith [hx.2])) heq.symm
              exfalso; linarith [not_le.mp hx3]
            · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
              have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
              have h := hsame (c + 3*ℓ) _ hxm _ hym
                (hmem₃ _ hxm (by linarith [hx.2])) (hmem₃ _ hym (by linarith [hy.2]))
                heq
              linarith

/-- **Corner-track confinement**: if the chart image ball of a spatial shrinkage covers
the corner circle, the corner piece lies in the spatial ball. -/
theorem corner_in_ball {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z) (hqne : ∀ z ∈ S, q z ≠ 0)
    {c : ℂ} {r α ω : ℝ} (hr : 0 < r) (hω : ω ≠ 0)
    (htr : ∀ u : ℝ, c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      ∈ Φ '' S)
    {p : ℂ} {η ρ : ℝ}
    (hshr : Metric.ball (Φ p) ρ ⊆ Φ '' (S ∩ Metric.ball p η))
    (hcirc : ∀ u : ℝ, c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      ∈ Metric.ball (Φ p) ρ) :
    ∀ t : ℝ, cornerPiece Φ S c r α ω t ∈ Metric.ball p η := by
  intro t
  obtain ⟨hmem, hdev, -, -⟩ := cornerPiece_package hS hΦd hinj hsq hqne hr hω htr t
  obtain ⟨z, ⟨hzS, hzball⟩, hzval⟩ := hshr (hcirc t)
  have hzeq : cornerPiece Φ S c r α ω t = z := hinj hmem hzS (by rw [hdev, hzval])
  rw [hzeq]
  exact hzball

set_option maxHeartbeats 400000 in
-- Heartbeats: the corner-confinement case split multiplies the four-piece analysis.
/-- **Rounded-loop injectivity, corner-confinement form**: the assembled four-piece
rounded bigon is injective on `[0, 1)`, with the corner tracks confined to disjoint
spatial balls around the corner points and the far arc segments separated from the
corner points by curve distance — the charts themselves are unconstrained. -/
theorem rounded_injOn₃ {γ τ : ℝ → ℂ} {a b T : ℝ}
    {S₁ S₂ : Set ℂ} {Φ₁ Φ₂ : ℂ → ℂ} {q : ℂ → ℂ} {ε₁ ε₂ r r₀ α₁ ω₁ α₂ ω₂ η₁ η₂ : ℝ}
    (hr : 0 < r) (hrr₀ : r < r₀)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hα₁ : α₁ = -(-ε₁) * (Real.pi / 2)) (hω₁ : ω₁ = 1 * (-ε₁) * (Real.pi / 2))
    (hα₂ : α₂ = -ε₂ * Real.pi) (hω₂ : ω₂ = ε₂ * (Real.pi / 2))
    (h3γ : r * (Real.pi / 2) < 3 * (T - a - 2 * r))
    (h3τ : r * (Real.pi / 2) < 3 * (b - 2 * r))
    (hS₁o : IsOpen S₁) (hΦ₁d : DifferentiableOn ℂ Φ₁ S₁) (hΦ₁inj : Set.InjOn Φ₁ S₁)
    (hΦ₁sq : ∀ z ∈ S₁, deriv Φ₁ z ^ 2 = -q z) (hq₁ne : ∀ z ∈ S₁, q z ≠ 0)
    (hS₂o : IsOpen S₂) (hΦ₂d : DifferentiableOn ℂ Φ₂ S₂) (hΦ₂inj : Set.InjOn Φ₂ S₂)
    (hΦ₂sq : ∀ z ∈ S₂, deriv Φ₂ z ^ 2 = -q z) (hq₂ne : ∀ z ∈ S₂, q z ≠ 0)
    (htr₁ : ∀ u : ℝ, (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * ((α₁ : ℂ) + (ω₁ : ℂ) * (u : ℂ)))
      ∈ Φ₁ '' S₁)
    (htr₂ : ∀ u : ℝ, (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * ((α₂ : ℂ) + (ω₂ : ℂ) * (u : ℂ)))
      ∈ Φ₂ '' S₂)
    (hdevγ₁ : ∀ u ∈ Set.Icc (T - r₀) (T + r₀),
      γ u ∈ S₁ ∧ Φ₁ (γ u) = Φ₁ (γ T) + ((u - T : ℝ) : ℂ))
    (hdevτ₁ : ∀ v ∈ Set.Icc (-r₀) r₀,
      τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v : ℝ) : ℂ))
    (hdevγ₂ : ∀ u ∈ Set.Icc (a - r₀) (a + r₀),
      γ u ∈ S₂ ∧ Φ₂ (γ u) = Φ₂ (γ a) + ((u - a : ℝ) : ℂ))
    (hdevτ₂ : ∀ v ∈ Set.Icc (b - r₀) (b + r₀),
      τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ))
    (hγinj : Set.InjOn γ (Set.Icc a T)) (hτinj : Set.InjOn τ (Set.Icc 0 b))
    (hcross : ∀ x ∈ Set.Icc a T, ∀ u ∈ Set.Icc 0 b,
      γ x = τ u → (x = T ∧ u = 0) ∨ (x = a ∧ u = b))
    (hκ₁b : ∀ t : ℝ, cornerPiece Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁ t
      ∈ Metric.ball (γ T) η₁)
    (hκ₂b : ∀ t : ℝ, cornerPiece Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂ t
      ∈ Metric.ball (γ a) η₂)
    (hfar₁γ : ∀ x, a + r ≤ x → x < T - r₀ → η₁ ≤ ‖γ x - γ T‖)
    (hfar₁τ : ∀ v, r₀ < v → v ≤ b - r → η₁ ≤ ‖τ v - γ T‖)
    (hfar₂γ : ∀ x, a + r₀ < x → x ≤ T - r → η₂ ≤ ‖γ x - γ a‖)
    (hfar₂τ : ∀ v, r ≤ v → v < b - r₀ → η₂ ≤ ‖τ v - γ a‖)
    (hηd : ∀ z, z ∈ Metric.ball (γ T) η₁ → z ∈ Metric.ball (γ a) η₂ → False) :
    Set.InjOn (quarterPW
      (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
      (cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁)
      (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
      (cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂))
      (Set.Ico 0 1) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hv : (0:ℝ) < r * (Real.pi/2) := mul_pos hr (by linarith)
  have heγ : (a + r) + (T - a - 2*r) = T - r := by ring
  have heτ : r + (b - 2*r) = b - r := by ring
  have hmapsγ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) u ∈ Set.Icc (a+r) (T-r) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := a + r) hv h3γ u hu
    rwa [heγ] at h
  have hmapsτ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      cubicRamp r (r * (Real.pi/2)) (b - 2*r) u ∈ Set.Icc r (b-r) := by
    intro u hu
    have h := cubicRamp_mapsTo (a := r) hv h3τ u hu
    rwa [heτ] at h
  have hω₁ne : ω₁ ≠ 0 := by
    rw [hω₁]
    rcases hε₁ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hω₂ne : ω₂ ≠ 0 := by
    rw [hω₂]
    rcases hε₂ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hω₁abs : |ω₁| = Real.pi/2 := by
    rcases hε₁ with h | h <;> rw [hω₁, h]
    · rw [show (1:ℝ) * -1 * (Real.pi/2) = -(Real.pi/2) by ring, abs_neg,
        abs_of_pos (by linarith)]
    · rw [show (1:ℝ) * - -1 * (Real.pi/2) = Real.pi/2 by ring,
        abs_of_pos (by linarith)]
  have hω₂abs : |ω₂| = Real.pi/2 := by
    rcases hε₂ with h | h <;> rw [hω₂, h]
    · rw [show (1:ℝ) * (Real.pi/2) = Real.pi/2 by ring, abs_of_pos (by linarith)]
    · rw [show (-1:ℝ) * (Real.pi/2) = -(Real.pi/2) by ring, abs_neg,
        abs_of_pos (by linarith)]
  have hpk₁ := cornerPiece_package hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne htr₁
  have hpk₂ := cornerPiece_package hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne htr₂
  have hinj₀ : Set.InjOn
      (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r)) (Set.Icc 0 1) := by
    refine rampArc_injOn hv h3γ ?_
    rw [heγ]
    exact hγinj.mono fun x hx =>
      Set.mem_Icc.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hinj₂ : Set.InjOn
      (rampArc τ r (r * (Real.pi/2)) (b - 2*r)) (Set.Icc 0 1) := by
    refine rampArc_injOn hv h3τ ?_
    rw [heτ]
    exact hτinj.mono fun x hx =>
      Set.mem_Icc.mpr ⟨by linarith [hx.1, hr], by linarith [hx.2, hr]⟩
  have hinj₁ := cornerPiece_injOn hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne htr₁
    (by rw [hω₁abs]; linarith)
  have hinj₃ := cornerPiece_injOn hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne htr₂
    (by rw [hω₂abs]; linarith)
  have hX01 : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) s
        = cornerPiece Φ₁ S₁
            (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁ t
      → s = 1 ∧ t = 0 := by
    intro s hs t ht heq
    rw [rampArc_apply] at heq
    have hX := hmapsγ s hs
    by_cases hw : T - r₀ ≤ cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) s
    · have hdev := (hdevγ₁ _ ⟨hw, by linarith [hX.2]⟩).2
      rw [heq, (hpk₁ t).2.1] at hdev
      have hinc : ((cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) s - T : ℝ) : ℂ)
          = -((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r
            + (r : ℂ) * Complex.exp (Complex.I * ((α₁ : ℂ) + (ω₁ : ℂ) * (t : ℂ))) := by
        linear_combination -hdev
      have hpin := corner1_horiz hε₁ hr hα₁ hω₁ ht hinc
      refine ⟨?_, hpin.1⟩
      refine (cubicRamp_strictMono (a := a + r) hv h3γ).injOn hs
        (Set.right_mem_Icc.mpr zero_le_one) ?_
      rw [cubicRamp_one, heγ]
      linarith [hpin.2]
    · exfalso
      have h1 : γ (cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) s)
          ∈ Metric.ball (γ T) η₁ := by
        rw [heq]
        exact hκ₁b t
      rw [Metric.mem_ball, dist_eq_norm] at h1
      linarith [hfar₁γ _ hX.1 (not_le.mp hw)]
  have hX12 : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      cornerPiece Φ₁ S₁
          (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁ s
        = rampArc τ r (r * (Real.pi/2)) (b - 2*r) t
      → s = 1 ∧ t = 0 := by
    intro s hs t ht heq
    rw [rampArc_apply] at heq
    have hY := hmapsτ t ht
    by_cases hw : cubicRamp r (r * (Real.pi/2)) (b - 2*r) t ≤ r₀
    · have hdev := (hdevτ₁ _ ⟨by linarith [hY.1], hw⟩).2
      rw [← heq, (hpk₁ s).2.1] at hdev
      have hinc : -(Complex.I * (ε₁ : ℂ)
            * ((cubicRamp r (r * (Real.pi/2)) (b - 2*r) t : ℝ) : ℂ))
          = -((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r
            + (r : ℂ) * Complex.exp (Complex.I * ((α₁ : ℂ) + (ω₁ : ℂ) * (s : ℂ))) := by
        linear_combination -hdev
      have hpin := corner1_vert hε₁ hr hα₁ hω₁ hs hinc
      refine ⟨hpin.1, ?_⟩
      refine (cubicRamp_strictMono (a := r) hv h3τ).injOn ht
        (Set.left_mem_Icc.mpr zero_le_one) ?_
      rw [cubicRamp_zero]
      linarith [hpin.2]
    · exfalso
      have h1 : τ (cubicRamp r (r * (Real.pi/2)) (b - 2*r) t)
          ∈ Metric.ball (γ T) η₁ := by
        rw [← heq]
        exact hκ₁b s
      rw [Metric.mem_ball, dist_eq_norm] at h1
      linarith [hfar₁τ _ (not_le.mp hw) hY.2]
  have hX23 : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      rampArc τ r (r * (Real.pi/2)) (b - 2*r) s
        = cornerPiece Φ₂ S₂
            (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂ t
      → s = 1 ∧ t = 0 := by
    intro s hs t ht heq
    rw [rampArc_apply] at heq
    have hY := hmapsτ s hs
    by_cases hw : b - r₀ ≤ cubicRamp r (r * (Real.pi/2)) (b - 2*r) s
    · have hdev := (hdevτ₂ _ ⟨hw, by linarith [hY.2]⟩).2
      rw [heq, (hpk₂ t).2.1] at hdev
      have hinc : -(Complex.I * (ε₂ : ℂ)
            * ((cubicRamp r (r * (Real.pi/2)) (b - 2*r) s - b : ℝ) : ℂ))
          = -((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r
            + (r : ℂ) * Complex.exp (Complex.I * ((α₂ : ℂ) + (ω₂ : ℂ) * (t : ℂ))) := by
        linear_combination -hdev
      have hpin := corner2_vert hε₂ hr hα₂ hω₂ ht hinc
      refine ⟨?_, hpin.1⟩
      refine (cubicRamp_strictMono (a := r) hv h3τ).injOn hs
        (Set.right_mem_Icc.mpr zero_le_one) ?_
      rw [cubicRamp_one, heτ]
      linarith [hpin.2]
    · exfalso
      have h1 : τ (cubicRamp r (r * (Real.pi/2)) (b - 2*r) s)
          ∈ Metric.ball (γ a) η₂ := by
        rw [heq]
        exact hκ₂b t
      rw [Metric.mem_ball, dist_eq_norm] at h1
      linarith [hfar₂τ _ hY.1 (not_le.mp hw)]
  have hX30 : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      cornerPiece Φ₂ S₂
          (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂ s
        = rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) t
      → s = 1 ∧ t = 0 := by
    intro s hs t ht heq
    rw [rampArc_apply] at heq
    have hX := hmapsγ t ht
    by_cases hw : cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) t ≤ a + r₀
    · have hdev := (hdevγ₂ _ ⟨by linarith [hX.1], hw⟩).2
      rw [← heq, (hpk₂ s).2.1] at hdev
      have hinc : ((cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) t - a : ℝ) : ℂ)
          = -((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r
            + (r : ℂ) * Complex.exp (Complex.I * ((α₂ : ℂ) + (ω₂ : ℂ) * (s : ℂ))) := by
        linear_combination -hdev
      have hpin := corner2_horiz hε₂ hr hα₂ hω₂ hs hinc
      refine ⟨hpin.1, ?_⟩
      refine (cubicRamp_strictMono (a := a + r) hv h3γ).injOn ht
        (Set.left_mem_Icc.mpr zero_le_one) ?_
      rw [cubicRamp_zero]
      linarith [hpin.2]
    · exfalso
      have h1 : γ (cubicRamp (a + r) (r * (Real.pi/2)) (T - a - 2*r) t)
          ∈ Metric.ball (γ a) η₂ := by
        rw [← heq]
        exact hκ₂b s
      rw [Metric.mem_ball, dist_eq_norm] at h1
      linarith [hfar₂γ _ (not_le.mp hw) hX.2]
  have hX02 : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) s
        ≠ rampArc τ r (r * (Real.pi/2)) (b - 2*r) t := by
    intro s hs t ht heq
    rw [rampArc_apply, rampArc_apply] at heq
    have hX := hmapsγ s hs
    have hY := hmapsτ t ht
    rcases hcross _ ⟨by linarith [hX.1], by linarith [hX.2]⟩
        _ ⟨by linarith [hY.1], by linarith [hY.2]⟩ heq with h | h
    · linarith [hX.2, h.1]
    · linarith [hX.1, h.1]
  have hX13 : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      cornerPiece Φ₁ S₁
          (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁ s
        ≠ cornerPiece Φ₂ S₂
          (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂ t := by
    intro s _ t _ heq
    refine hηd _ (hκ₁b s) ?_
    rw [heq]
    exact hκ₂b t
  intro x hx y hy heq
  by_cases hx1 : x ≤ 1/4
  · rw [quarterPW_eval₀ hx1] at heq
    have hxm : 4*x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith⟩
    by_cases hy1 : y ≤ 1/4
    · rw [quarterPW_eval₀ hy1] at heq
      have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
      have h := hinj₀ hxm hym heq
      linarith
    · by_cases hy2 : y ≤ 1/2
      · rw [quarterPW_eval₁ hy1 hy2] at heq
        have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith [not_le.mp hy1], by linarith⟩
        obtain ⟨h1, h2⟩ := hX01 _ hxm _ hym heq
        linarith
      · by_cases hy3 : y ≤ 3/4
        · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
          have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by linarith [not_le.mp hy2], by linarith⟩
          exact absurd heq (hX02 _ hxm _ hym)
        · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
          have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
          obtain ⟨h1, h2⟩ := hX30 _ hym _ hxm heq.symm
          exfalso; linarith [hy.2]
  · by_cases hx2 : x ≤ 1/2
    · rw [quarterPW_eval₁ hx1 hx2] at heq
      have hxm : 4*x - 1 ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by linarith [not_le.mp hx1], by linarith⟩
      by_cases hy1 : y ≤ 1/4
      · rw [quarterPW_eval₀ hy1] at heq
        have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
        obtain ⟨h1, h2⟩ := hX01 _ hym _ hxm heq.symm
        linarith
      · by_cases hy2 : y ≤ 1/2
        · rw [quarterPW_eval₁ hy1 hy2] at heq
          have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by linarith [not_le.mp hy1], by linarith⟩
          have h := hinj₁ hxm hym heq
          linarith
        · by_cases hy3 : y ≤ 3/4
          · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
            have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy2], by linarith⟩
            obtain ⟨h1, h2⟩ := hX12 _ hxm _ hym heq
            exfalso; linarith [not_le.mp hy2]
          · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
            have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
            exact absurd heq (hX13 _ hxm _ hym)
    · by_cases hx3 : x ≤ 3/4
      · rw [quarterPW_eval₂ hx1 hx2 hx3] at heq
        have hxm : 4*x - 2 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith [not_le.mp hx2], by linarith⟩
        by_cases hy1 : y ≤ 1/4
        · rw [quarterPW_eval₀ hy1] at heq
          have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
          exact absurd heq.symm (hX02 _ hym _ hxm)
        · by_cases hy2 : y ≤ 1/2
          · rw [quarterPW_eval₁ hy1 hy2] at heq
            have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy1], by linarith⟩
            obtain ⟨h1, h2⟩ := hX12 _ hym _ hxm heq.symm
            exfalso; linarith [not_le.mp hx2]
          · by_cases hy3 : y ≤ 3/4
            · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
              have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy2], by linarith⟩
              have h := hinj₂ hxm hym heq
              linarith
            · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
              have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
              obtain ⟨h1, h2⟩ := hX23 _ hxm _ hym heq
              exfalso; linarith [not_le.mp hy3]
      · rw [quarterPW_eval₃ hx1 hx2 hx3] at heq
        have hxm : 4*x - 3 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith [not_le.mp hx3], by linarith [hx.2]⟩
        by_cases hy1 : y ≤ 1/4
        · rw [quarterPW_eval₀ hy1] at heq
          have hym : 4*y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith⟩
          obtain ⟨h1, h2⟩ := hX30 _ hxm _ hym heq
          exfalso; linarith [hx.2]
        · by_cases hy2 : y ≤ 1/2
          · rw [quarterPW_eval₁ hy1 hy2] at heq
            have hym : 4*y - 1 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [not_le.mp hy1], by linarith⟩
            exact absurd heq.symm (hX13 _ hym _ hxm)
          · by_cases hy3 : y ≤ 3/4
            · rw [quarterPW_eval₂ hy1 hy2 hy3] at heq
              have hym : 4*y - 2 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy2], by linarith⟩
              obtain ⟨h1, h2⟩ := hX23 _ hym _ hxm heq.symm
              exfalso; linarith [not_le.mp hx3]
            · rw [quarterPW_eval₃ hy1 hy2 hy3] at heq
              have hym : 4*y - 3 ∈ Set.Icc (0:ℝ) 1 :=
                ⟨by linarith [not_le.mp hy3], by linarith [hy.2]⟩
              have h := hinj₃ hxm hym heq
              linarith

/-- **Transverse lower separation**: the near-diagonal lower separation holds for a
trajectory of the negated differential inside a chart of the original one, through the
rotated chart `i·Φ`. -/
theorem lower_sep_neg {q Φ : ℂ → ℂ} {x₀ : ℂ} {rB C : ℝ}
    (hΦd : DifferentiableOn ℂ Φ (Metric.ball x₀ rB))
    (hΦsq : ∀ w ∈ Metric.ball x₀ rB, deriv Φ w ^ 2 = -q w)
    (hC : ∀ w ∈ Metric.ball x₀ rB, ‖deriv Φ w‖ ≤ C)
    {τ : ℝ → ℂ} {I' : Set ℝ} (hτ : IsTrajOn (fun z => -q z) τ I')
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ I')
    (htrack : ∀ t ∈ Set.Icc a b, τ t ∈ Metric.ball x₀ rB) :
    ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, |t - t'| ≤ C * ‖τ t - τ t'‖ := by
  have hΨd : DifferentiableOn ℂ (fun z => Complex.I * Φ z) (Metric.ball x₀ rB) :=
    hΦd.const_mul Complex.I
  have hΨsq : ∀ w ∈ Metric.ball x₀ rB,
      deriv (fun z => Complex.I * Φ z) w ^ 2 = -((fun z => -q z) w) := by
    intro w hw
    have hd : DifferentiableAt ℂ Φ w :=
      hΦd.differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    rw [deriv_const_mul Complex.I hd, mul_pow, Complex.I_sq, hΦsq w hw]
    ring
  have hΨC : ∀ w ∈ Metric.ball x₀ rB,
      ‖deriv (fun z => Complex.I * Φ z) w‖ ≤ C := by
    intro w hw
    have hd : DifferentiableAt ℂ Φ w :=
      hΦd.differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    rw [deriv_const_mul Complex.I hd, norm_mul, Complex.norm_I, one_mul]
    exact hC w hw
  exact traj_lower_sep hΨd hΨsq hΨC hτ hab hI htrack

/-- **Shifted track separation**: mesh-separated times of an injective continuous curve
on a general closed interval have spatially separated values. -/
theorem track_sep_shift {f : ℝ → ℂ} {lo hi : ℝ}
    (hc : ContinuousOn f (Set.Icc lo hi)) (hinj : Set.InjOn f (Set.Icc lo hi))
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ sep > 0, ∀ t ∈ Set.Icc lo hi, ∀ t' ∈ Set.Icc lo hi,
      mesh ≤ |t - t'| → sep ≤ ‖f t - f t'‖ := by
  have hc' : ContinuousOn (fun t => f (lo + t)) (Set.Icc 0 (hi - lo)) := by
    refine hc.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hinj' : Set.InjOn (fun t => f (lo + t)) (Set.Icc 0 (hi - lo)) := by
    intro s hs t ht heq
    have h := hinj (Set.mem_Icc.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (Set.mem_Icc.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) heq
    linarith
  obtain ⟨sep, hsep, hbound⟩ := track_separation hc' hinj' hmesh
  refine ⟨sep, hsep, fun t ht t' ht' hd => ?_⟩
  have h := hbound (t - lo) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    (t' - lo) ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    (by rw [show t - lo - (t' - lo) = t - t' by ring]; exact hd)
  rw [show lo + (t - lo) = t by ring, show lo + (t' - lo) = t' by ring] at h
  exact h

/-- **Ball chart extraction**: an open chart around a point contains a ball on which the
chart data restricts and the chart derivative is bounded. -/
theorem ball_chart_at {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    {p : ℂ} (hp : p ∈ S) :
    ∃ rB C : ℝ, 0 < rB ∧ 0 < C ∧ Metric.ball p rB ⊆ S
      ∧ DifferentiableOn ℂ Φ (Metric.ball p rB)
      ∧ (∀ w ∈ Metric.ball p rB, deriv Φ w ^ 2 = -q w)
      ∧ ∀ w ∈ Metric.ball p rB, ‖deriv Φ w‖ ≤ C := by
  obtain ⟨rb, hrb, hball⟩ := Metric.isOpen_iff.mp hS p hp
  have hcb : Metric.closedBall p (rb/2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hdc : ContinuousOn (deriv Φ) S := ((hΦd.analyticOnNhd hS).deriv).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_closedBall p (rb/2)).exists_bound_of_continuousOn
    (hdc.mono hcb)
  have hsub : Metric.ball p (rb/2) ⊆ S := Metric.ball_subset_closedBall.trans hcb
  refine ⟨rb/2, max C 1, by linarith, lt_of_lt_of_le one_pos (le_max_right C 1),
    hsub, hΦd.mono hsub, fun w hw => hΦsq w (hsub hw), fun w hw => ?_⟩
  exact le_trans (hC w (Metric.ball_subset_closedBall hw)) (le_max_left C 1)

end WindingBricks

/-- The flat distance is dominated by its reversal. -/
theorem qdDist_symm_le {q : ℂ → ℂ} (hqm : Measurable q) (z w : ℂ) :
    qdDist q w z ≤ qdDist q z w := by
  refine le_iInf₂ fun γ hγ => ?_
  have hρm : Measurable fun z : ℂ => ENNReal.ofReal (Real.sqrt ‖q z‖) :=
    (hqm.norm.sqrt).ennreal_ofReal
  set γ' : ℝ → ℂ := fun t => γ (max 0 (min 1 t)) with hγ'def
  have hid : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ' t = γ t := by
    intro t ht
    change γ (max 0 (min 1 t)) = γ t
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hγ'cont : Continuous γ' := by
    have hclamp : Continuous fun t : ℝ => max 0 (min 1 t) :=
      continuous_const.max (continuous_const.min continuous_id)
    refine hγ.cont.comp_continuous hclamp fun t => ?_
    exact ⟨le_max_left 0 _, max_le (by norm_num) (min_le_left 1 t)⟩
  have hγ'ac : AbsolutelyContinuousOnInterval γ' 0 1 := by
    refine AbsolutelyContinuousOnInterval.congr hγ.ac fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact (hid t ht).symm
  have hγ'flat : IsFlatPath γ' z w := by
    refine ⟨?_, ?_, hγ'cont.continuousOn, hγ'ac, ?_⟩
    · rw [hid 0 ⟨le_refl 0, zero_le_one⟩]
      exact hγ.init
    · rw [hid 1 ⟨zero_le_one, le_refl 1⟩]
      exact hγ.final
    · intro t ht
      rw [hid t ht]
      exact hγ.upper t ht
  have hlen_eq : qdLength q γ' = qdLength q γ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_Ioo01] with t htI
    have hev : γ' =ᶠ[nhds t] γ := by
      filter_upwards [Ioo_mem_nhds htI.1 htI.2] with u hu
      exact hid u ⟨hu.1.le, hu.2.le⟩
    rw [hid t ⟨htI.1.le, htI.2.le⟩, hev.deriv_eq]
  have hrev : IsFlatPath (reversePath γ') w z := by
    have hacη := acOn_reflect hγ'ac
    rw [neg_zero] at hacη
    have hacη' : AbsolutelyContinuousOnInterval (fun u => γ' (-u))
        ((1 : ℝ) * 0 + (-1)) ((1 : ℝ) * 1 + (-1)) := by
      have h0 : (1 : ℝ) * 0 + (-1) = -1 := by norm_num
      have h1 : (1 : ℝ) * 1 + (-1) = 0 := by norm_num
      rw [h0, h1]
      exact hacη
    have h2 := acOn_comp_affine one_pos hacη'
    have hac : AbsolutelyContinuousOnInterval (reversePath γ') 0 1 := by
      refine AbsolutelyContinuousOnInterval.congr h2 fun t ht => ?_
      change γ' (-(1 * t + -1)) = γ' (1 - t)
      congr 1
      ring
    refine ⟨?_, ?_, ?_, hac, ?_⟩
    · rw [reversePath_zero]
      exact hγ'flat.final
    · rw [reversePath_one]
      exact hγ'flat.init
    · have h3 : ContinuousOn (reversePath γ') (Set.uIcc 0 1) :=
        AbsolutelyContinuousOnInterval.continuousOn hac
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h3
    · intro t ht
      change 0 < (γ' (1 - t)).im
      exact hγ'flat.upper (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  calc qdDist q w z ≤ qdLength q (reversePath γ') := qdDist_le_qdLength hrev
    _ = qdLength q γ' := arcLengthLineIntegral_reversePath _ hρm hγ'ac hγ'cont
    _ = qdLength q γ := hlen_eq

/-- Almost-everywhere properties pull back along time reversal. -/
theorem ae_neg_volume {P : ℝ → Prop} (hP : ∀ᵐ t ∂(volume : Measure ℝ), P t) :
    ∀ᵐ t ∂(volume : Measure ℝ), P (-t) := by
  have hE0 : volume {t : ℝ | ¬ P t} = 0 := ae_iff.mp hP
  set E : Set ℝ := toMeasurable volume {t : ℝ | ¬ P t} with hEdef
  have hEm : MeasurableSet E := measurableSet_toMeasurable _ _
  have hE : volume E = 0 := by
    rw [hEdef, measure_toMeasurable]
    exact hE0
  have hEsub := subset_toMeasurable volume {t : ℝ | ¬ P t}
  refine ae_iff.mpr (measure_mono_null (t := (fun t : ℝ => -t) ⁻¹' E)
    (fun t ht => hEsub ht) ?_)
  rw [← Measure.map_apply measurable_neg hEm,
    Measure.map_neg_eq_self (volume : Measure ℝ)]
  exact hE

/-- **The backward reparametrization bound**: the mirror of `sym_hrepar` along the
reversely oriented flow realization. -/
theorem sym_hrepar_neg {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ) (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) →
      horizontalVariation (q : ℂ → ℂ) (fun s => h (σ (s * T)))
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity (q : ℂ → ℂ) h (A.flow (-t) z) := by
  filter_upwards [flow_diff_ae hΓ hcc q hq0 hqc A] with z hz
  intro hzg T hT σ hσtraj hσev
  have hpull := ae_scale_pos (ae_neg_volume (hz hzg)) hT
  have haes : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      horizontalDensity (q : ℂ → ℂ) (fun s' => h (σ (s' * T))) s
        = ENNReal.ofReal T * rsDensity (q : ℂ → ℂ) h (A.flow (-(s * T)) z) := by
    filter_upwards [ae_restrict_of_ae hpull, ae_mem_Ioo01] with s hs hsIoo
    have hvIoo : s * T ∈ Set.Ioo 0 T :=
      ⟨mul_pos hsIoo.1 hT, by nlinarith [hsIoo.2]⟩
    have hvIcc : s * T ∈ Set.Icc 0 T := ⟨hvIoo.1.le, hvIoo.2.le⟩
    have hflowe : A.flow (-(s * T)) z = σ (s * T) := hσev _ hvIcc
    rw [hflowe] at hs
    obtain ⟨hdh, hbelt, him⟩ := hs
    obtain ⟨d, hdAt, hd2⟩ := traj_hasDerivAt_interior hσtraj hvIoo
    have hqw0 : (q : ℂ → ℂ) (σ (s * T)) ≠ 0 := (traj_regular hσtraj hvIcc).2
    have hmulT : HasDerivAt (fun x : ℝ => x * T) T s := hasDerivAt_mul_const T
    have hp : HasDerivAt (fun s' : ℝ => σ (s' * T)) (T • d) s :=
      hdAt.scomp s hmulT
    have hγ : HasDerivAt (fun s' : ℝ => h (σ (s' * T)))
        ((fderiv ℝ h (σ (s * T))) (T • d)) s :=
      hdh.hasFDerivAt.comp_hasDerivAt s hp
    have hγd : deriv (fun s' : ℝ => h (σ (s' * T))) s
        = (fderiv ℝ h (σ (s * T))) (((T : ℝ) : ℂ) * d) := by
      rw [hγ.deriv]
      congr 1
    rw [hflowe]
    exact image_density_eq hT hqw0 hd2 hbelt rfl hγd
  change (∫⁻ s in Set.Icc (0 : ℝ) 1,
      horizontalDensity (q : ℂ → ℂ) (fun s' => h (σ (s' * T))) s)
    ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity (q : ℂ → ℂ) h (A.flow (-t) z)
  rw [lintegral_congr_ae haes,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hcov := setLIntegral_affine
    (fun t => rsDensity (q : ℂ → ℂ) h (A.flow (-t) z)) hT 0 (Set.Icc 0 1)
  have himg : (fun s : ℝ => T * s + 0) '' Set.Icc 0 1 = Set.Icc (0 : ℝ) T := by
    rw [image_affine_Icc hT 0 0 1]
    norm_num
  rw [himg] at hcov
  have hcomm : ∫⁻ s in Set.Icc (0 : ℝ) 1,
      rsDensity (q : ℂ → ℂ) h (A.flow (-(s * T)) z)
      = ∫⁻ s in Set.Icc (0 : ℝ) 1,
        rsDensity (q : ℂ → ℂ) h (A.flow (-(T * s + 0)) z) := by
    refine lintegral_congr fun s => ?_
    rw [add_zero, mul_comm]
  rw [hcomm, hcov, ← mul_assoc, ← ENNReal.ofReal_mul hT.le,
    mul_inv_cancel₀ hT.ne', ENNReal.ofReal_one, one_mul]

/-- **Backward leafwise absolute continuity**: the mirror of `sym_hacl` along the
reversely oriented flow realization. -/
theorem sym_hacl_neg {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) →
      AbsolutelyContinuousOnInterval (fun s => h (σ (s * T))) 0 1 := by
  classical
  have hACL := sym_chart_slicing A hqc
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  set P : ℕ → ℝ → Prop := fun j y => ∀ a b : ℝ,
    (∀ x ∈ Set.uIcc a b,
      (x : ℂ) + (y : ℝ) * Complex.I
        ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) →
    AbsolutelyContinuousOnInterval
      (fun x => h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j))
        ((x : ℂ) + (y : ℝ) * Complex.I))) a b with hPdef
  set E : ℕ → Set ℝ := fun j => toMeasurable volume {y : ℝ | ¬ P j y} with hEdef
  have hEnull : ∀ j, A.active j → volume (E j) = 0 := by
    intro j hj
    rw [show E j = toMeasurable volume {y : ℝ | ¬ P j y} from rfl,
      measure_toMeasurable]
    exact ae_iff.mp (hACL j hj)
  set BP : Set ℂ := toMeasurable volume (⋃ j : ℕ,
    {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (2 * A.r j)
      ∧ (A.Φ j z).im ∈ E j}) with hBPdef
  have hBPm : MeasurableSet BP := measurableSet_toMeasurable _ _
  have hBP0 : volume BP = 0 := by
    rw [hBPdef, measure_toMeasurable]
    refine measure_iUnion_null fun j => ?_
    by_cases hj : A.active j
    · exact measure_mono_null
        (t := {z : ℂ | z ∈ Metric.ball (A.c j) (2 * A.r j)
          ∧ (A.Φ j z).im ∈ E j})
        (fun z hz => ⟨hz.2.1, hz.2.2⟩)
        (chartline_heights_null q.measurable A hj (hEnull j hj))
    · exact measure_mono_null (t := (∅ : Set ℂ))
        (fun z hz => (hj hz.1).elim) (measure_empty (μ := volume))
  have hBPsub := subset_toMeasurable volume (⋃ j : ℕ,
    {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (2 * A.r j)
      ∧ (A.Φ j z).im ∈ E j})
  have hsec : ∀ t : ℝ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      z ∈ good (q : ℂ → ℂ) A → A.flow t z ∉ BP := by
    intro t
    rcases lt_trichotomy t 0 with htn | ht0 | htp
    · have hminus : (0 : ℝ) < -t := by linarith
      have hb := flow_preimage_ae q A (mirrorAtlas A)
        (fun z => A.flow (-(-t)) z) hminus
        (fun n z hz => flow_eq_pos_bwd q.holo A hminus hz)
        (fun z hz => good_slegal_bwd q.holo A hminus hz) hBPm hBP0
      simpa only [neg_neg] using hb
    · subst ht0
      have hnotN : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∉ BP := by
        refine ae_iff.mpr ?_
        have hset : {a : ℂ | ¬ a ∉ BP} = BP := by
          ext a
          simp
        rw [hset, Measure.restrict_apply' hUm]
        exact measure_mono_null Set.inter_subset_left hBP0
      filter_upwards [hnotN, q.ae_ne_zero hq0, ae_restrict_mem hUm]
        with z hzN hqz hzU
      intro _ hflowN
      rw [flow_zero A hzU hqz] at hflowN
      exact hzN hflowN
    · exact flow_preimage_ae q A A (fun z => A.flow t z) htp
        (fun n z hz => flow_eq_pos_fwd q.holo A htp hz)
        (fun z hz => good_slegal_fwd q.holo A htp hz) hBPm hBP0
  have havoid : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ∀ r : ℚ, z ∈ good (q : ℂ → ℂ) A → A.flow (r : ℝ) z ∉ BP :=
    ae_all_iff.mpr fun r => hsec (r : ℝ)
  filter_upwards [havoid] with z hz
  intro hzg T hT σ hσtraj hσev
  have hACfull : AbsolutelyContinuousOnInterval (fun u => h (σ u)) 0 T := by
    refine ac_of_local_windows hT fun v hv => ?_
    have hreg := traj_regular hσtraj hv
    have hact : A.active (A.sel (σ v)) := (A.sel_spec hreg.1 hreg.2).1
    have hin : σ v ∈ Metric.ball (A.c (A.sel (σ v))) (2 * A.r (A.sel (σ v))) :=
      Metric.ball_subset_ball (by linarith [A.hr _ hact])
        (A.sel_spec hreg.1 hreg.2).2
    have hyv : (A.Φ (A.sel (σ v)) (σ v)).im ∉ E (A.sel (σ v)) := by
      intro hbad
      obtain ⟨r, hr1, hr2, hr3⟩ := leaf_height_hit_rational hT hσtraj hv
        Metric.isOpen_ball (A.hd _ hact) (A.hsq _ hact) hin
      have hflow : A.flow (-(r : ℝ)) z ∈ BP := by
        have hmem : A.flow (-(r : ℝ)) z ∈ ⋃ j : ℕ,
            {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (2 * A.r j)
              ∧ (A.Φ j z).im ∈ E j} := by
          refine Set.mem_iUnion.mpr ⟨A.sel (σ v), hact, ?_, ?_⟩
          · rw [hσev _ hr1]
            exact hr2
          · rw [hσev _ hr1, hr3]
            exact hbad
        exact hBPsub hmem
      have hz' := hz (-r) hzg
      rw [Rat.cast_neg] at hz'
      exact hz' hflow
    have hP : P (A.sel (σ v)) ((A.Φ (A.sel (σ v)) (σ v)).im) := by
      by_contra hnP
      exact hyv (subset_toMeasurable volume _ hnP)
    obtain ⟨δ, hδ, hAC⟩ := leaf_window_ac hσtraj hv Metric.isOpen_ball
      (A.hd _ hact) (A.hinj _ hact) (A.hsq _ hact) hin hP
    exact ⟨δ, hδ, hAC⟩
  have hmaps : ∀ t ∈ Set.uIcc (0 : ℝ) 1, T * t + 0 ∈ Set.uIcc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Set.uIcc_of_le hT.le]
    rw [add_zero]
    exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hAC1 := AbsolutelyContinuousOnInterval.comp_affine hT hACfull hmaps
  refine AbsolutelyContinuousOnInterval.congr hAC1 fun t ht => ?_
  show h (σ (T * t + 0)) = h (σ (t * T))
  rw [add_zero, mul_comm]

/-- **Backward flat-path field**: the mirror of `sym_hpath_full` along the reversely
oriented flow realization. -/
theorem sym_hpath_neg {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) →
      IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)) := by
  filter_upwards [sym_hacl_neg q hq0 hqc A] with z hz
  intro hzg T hT σ hσ hσev
  exact image_flatPath hqc hT hσ (hz hzg T hT σ hσ hσev)

/-- The measurable upper-half-plane modification of a map: the identity below the
real axis. -/
noncomputable def hMod (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if 0 < z.im then h z else z

/-- The modified competitor agrees with the competitor on the upper half plane. -/
theorem hMod_eq {h : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im) :
    hMod h z = h z := if_pos hz

/-- The modified competitor agrees with the competitor near every upper half plane
point. -/
theorem hMod_eventuallyEq {h : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im) :
    hMod h =ᶠ[nhds z] h := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz]
    with w hw
  exact hMod_eq hw

/-- The modified competitor of an upper quasiconformal map is measurable. -/
theorem hMod_meas {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ) :
    Measurable (hMod h) := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  refine measurable_of_isOpen fun V hV => ?_
  have hset : hMod h ⁻¹' V
      = ({z : ℂ | 0 < z.im} ∩ h ⁻¹' V)
        ∪ ({z : ℂ | 0 < z.im}ᶜ ∩ V) := by
    ext z
    by_cases hz : 0 < z.im
    · simp [hMod, hz]
    · simp [hMod, hz]
  rw [hset]
  exact ((hqc.cont.isOpen_inter_preimage hUopen hV).measurableSet).union
    (hUopen.measurableSet.compl.inter hV.measurableSet)

/-- Weak directional derivatives on the upper half plane pass to the modified
competitor. -/
theorem hMod_weak {v : ℂ} {g h : ℂ → ℂ}
    (hwd : HasWeakDirDeriv v g h {z : ℂ | 0 < z.im}) :
    HasWeakDirDeriv v g (hMod h) {z : ℂ | 0 < z.im} := by
  intro φ hφ hcs hts
  have hL : ∀ z, ((fderiv ℝ φ z) v) • hMod h z
      = ((fderiv ℝ φ z) v) • h z := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [hMod_eq (hts hz)]
    · have hfd : fderiv ℝ φ z = 0 := by
        have hloc : φ =ᶠ[nhds z] fun _ => (0 : ℝ) := by
          filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        rw [hloc.fderiv_eq]
        simp
      rw [hfd]
      simp
  calc ∫ z, ((fderiv ℝ φ z) v) • hMod h z
      = ∫ z, ((fderiv ℝ φ z) v) • h z :=
        integral_congr_ae (Filter.Eventually.of_forall hL)
    _ = - ∫ z, φ z • g z := hwd φ hφ hcs hts

end RiemannDynamics

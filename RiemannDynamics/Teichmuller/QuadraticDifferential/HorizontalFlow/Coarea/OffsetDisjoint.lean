/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Coarea.CrossingJump

/-!
# Offset curves, order-separated summation, and dyadic covers

The uniform first-order modulus of a C1 loop, disjointness of its offset curves, the
monotonicity of leaf levels against chart heights, the order-separated summation
inequality, and the exact dyadic cover of an open corridor union.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Local-flow matching on a margined domain**: a trajectory whose domain contains a
symmetric parameter window about a chart point follows the local flow of the chart
throughout the window. -/
theorem leaf_follow_on {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ w ∈ S, q w ≠ 0)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {D : Set ℝ} (hσ : IsTrajOn q σ D)
    {t h : ℝ} (hh : 0 < h) (hD : Set.Icc (t - h) (t + h) ⊆ D) (htS : σ t ∈ S)
    (hdev : ∀ x : ℝ, |x| ≤ h → Φ (σ t) + (x : ℂ) ∈ Φ '' S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ u : ℝ, |u| ≤ h → σ (t + u) = localFlow Φ S (ε * u) (σ t) := by
  obtain ⟨ε, hε, hev⟩ := traj_ambient_local hS hΦd hΦsq hσ hD
    (⟨by linarith, by linarith⟩ : t ∈ Set.Icc (t - h) (t + h)) htS
  have hevn : ∀ᶠ u in 𝓝 t, Φ (σ u) = Φ (σ t) + ε * ((u - t : ℝ) : ℂ) := by
    rwa [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds (by linarith) (by linarith))] at hev
  have hεsq : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  have hside : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      (∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
        Φ (σ (t + sgn * u)) = Φ (σ t) + (ε * sgn) * (u : ℂ)) →
      IsTrajOn q (fun u => σ (t + sgn * u)) (Set.Icc 0 h) →
      ∀ u ∈ Set.Icc (0 : ℝ) h, σ (t + sgn * u)
        = localFlow Φ S ((ε * sgn) * u) (σ t) := by
    intro sgn hsgn hdevε hτ
    have hεs : ε * sgn = 1 ∨ ε * sgn = -1 := by
      rcases hε with h1 | h1 <;> rcases hsgn with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
    have hsegm : ∀ u ∈ Set.Icc (0 : ℝ) h,
        Φ (σ t) + (((ε * sgn) * u : ℝ) : ℂ) ∈ Φ '' S := by
      intro u hu
      refine hdev _ ?_
      have h3 : |(ε * sgn) * u| = |u| := by
        rw [abs_mul, abs_mul]
        rcases hε with h1 | h1 <;> rcases hsgn with h2 | h2 <;>
          rw [h1, h2] <;> simp
      rw [h3, abs_of_nonneg hu.1]
      exact hu.2
    obtain ⟨hflow0, hflowτ, -⟩ := seg_traj hS hΦd hΦinj hSH hSne hΦsq htS
      hεs hh hsegm
    have hgerm : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
        σ (t + sgn * u) = localFlow Φ S ((ε * sgn) * u) (σ t) := by
      have hcS : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h), σ (t + sgn * u) ∈ S := by
        have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) h := Set.left_mem_Icc.mpr hh.le
        have hc := hτ.cont 0 h0m
        have h4 := hc (hS.mem_nhds (by simpa using htS))
        simpa using! h4
      filter_upwards [hdevε, hcS, eventually_mem_nhdsWithin] with u hd hcSu hum
      refine hΦinj hcSu (localFlow_mem (hsegm u hum)) ?_
      rw [hd, localFlow_dev (hsegm u hum)]
      push_cast
      ring
    have h5 := traj_unique hh.le hτ hflowτ hgerm
    intro u hu
    exact h5 hu
  have hτfwd : IsTrajOn q (fun u => σ (t + 1 * u)) (Set.Icc 0 h) := by
    have h1 := traj_shift t hσ
    have h2 : Set.Icc (0 : ℝ) h ⊆ (fun u : ℝ => u + t) ⁻¹' D := by
      intro u hu
      simp only [Set.mem_preimage]
      exact hD ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h3 := traj_mono h1 h2
    have hfun : (fun u => σ (u + t)) = fun u => σ (t + 1 * u) := by
      funext u
      ring_nf
    rwa [hfun] at h3
  have hdevfwd : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
      Φ (σ (t + 1 * u)) = Φ (σ t) + (ε * 1) * (u : ℂ) := by
    have hmap : Filter.Tendsto (fun u : ℝ => t + 1 * u)
        (nhdsWithin 0 (Set.Icc 0 h)) (𝓝 t) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have h6 : Continuous fun u : ℝ => t + 1 * u := by continuity
      simpa using h6.tendsto 0
    filter_upwards [hmap.eventually hevn] with u hu
    rw [hu]
    push_cast
    ring
  have hfwd := hside 1 (Or.inl rfl) hdevfwd hτfwd
  have hτbwd : IsTrajOn q (fun u => σ (t + (-1) * u)) (Set.Icc 0 h) := by
    have hshift := traj_shift (t - h) hσ
    have hsub : Set.Icc (0 : ℝ) h ⊆ (fun u : ℝ => u + (t - h)) ⁻¹' D := by
      intro u hu
      simp only [Set.mem_preimage]
      exact hD ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hbase := traj_mono hshift hsub
    have hrev := traj_reverse hbase
    have hset : (fun u : ℝ => -u) ⁻¹' Set.Icc (0 : ℝ) h = Set.Icc (-h) 0 := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hset] at hrev
    have hshift2 := traj_shift (-h) hrev
    have hset2 : (fun u : ℝ => u + -h) ⁻¹' Set.Icc (-h) (0 : ℝ) = Set.Icc 0 h := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hset2] at hshift2
    have hfun : (fun u : ℝ => (fun v : ℝ =>
        (fun y : ℝ => σ (y + (t - h))) (-v)) (u + -h))
        = fun u => σ (t + (-1) * u) := by
      funext u
      change σ (-(u + -h) + (t - h)) = σ (t + (-1) * u)
      ring_nf
    rwa [hfun] at hshift2
  have hdevbwd : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
      Φ (σ (t + (-1) * u)) = Φ (σ t) + (ε : ℂ) * ((-1 : ℝ) : ℂ) * (u : ℂ) := by
    have hmap : Filter.Tendsto (fun u : ℝ => t + (-1) * u)
        (nhdsWithin 0 (Set.Icc 0 h)) (𝓝 t) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have h6 : Continuous fun u : ℝ => t + (-1) * u := by continuity
      simpa using h6.tendsto 0
    filter_upwards [hmap.eventually hevn] with u hu
    rw [hu]
    push_cast
    ring
  have hbwd := hside (-1) (Or.inr rfl) hdevbwd hτbwd
  refine ⟨ε, hε, ?_⟩
  intro u hu
  rcases le_or_gt 0 u with h0 | h0
  · have h7 := hfwd u ⟨h0, by rwa [abs_of_nonneg h0] at hu⟩
    simpa using h7
  · have hmem : -u ∈ Set.Icc (0 : ℝ) h :=
      ⟨by linarith, by rwa [abs_of_neg h0] at hu⟩
    have h7 := hbwd (-u) hmem
    have hl : t + (-1) * (-u) = t + u := by ring
    have hr : (ε * (-1)) * (-u) = ε * u := by ring
    rwa [hl, hr] at h7

/-- **Vertical development with tracking of a chart-transverse arc**: a vertical
trajectory arc through a point of a transverse natural chart stays in the chart on a
margined symmetric window and its chart value moves purely vertically with a single
sign. -/
theorem arc_vert_dev {q Ψ : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hΨd : DifferentiableOn ℂ Ψ W) (hΨinj : Set.InjOn Ψ W)
    (hWH : W ⊆ {z : ℂ | 0 < z.im}) (hWne : ∀ w ∈ W, q w ≠ 0)
    (hΨsq : ∀ x ∈ W, deriv Ψ x ^ 2 = -(-q x))
    {A : ℝ → ℂ} {D : Set ℝ} (hA : IsTrajOn q A D)
    {t h : ℝ} (hh : 0 < h) (hD : Set.Icc (t - h) (t + h) ⊆ D) (htW : A t ∈ W)
    (hdev : ∀ x : ℝ, |x| ≤ h → Ψ (A t) - Complex.I * (x : ℂ) ∈ Ψ '' W) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ u : ℝ, |u| ≤ h →
      A (t + u) ∈ W ∧ Ψ (A (t + u)) = Ψ (A t) - Complex.I * (ε : ℂ) * (u : ℂ) := by
  set Φ : ℂ → ℂ := fun z => Complex.I * Ψ z with hΦdef
  have hΦd : DifferentiableOn ℂ Φ W := hΨd.const_mul _
  have hΦinj : Set.InjOn Φ W := by
    intro a ha b hb hab
    refine hΨinj ha hb ?_
    have h2 : Complex.I * Ψ a = Complex.I * Ψ b := hab
    exact mul_left_cancel₀ Complex.I_ne_zero h2
  have hΦsq : ∀ w ∈ W, deriv Φ w ^ 2 = -q w := by
    intro w hw
    have hat : DifferentiableAt ℂ Ψ w := hΨd.differentiableAt (hW.mem_nhds hw)
    rw [hΦdef]
    rw [deriv_const_mul _ hat, mul_pow, Complex.I_sq, hΨsq w hw]
    ring
  have hdev' : ∀ x : ℝ, |x| ≤ h → Φ (A t) + (x : ℂ) ∈ Φ '' W := by
    intro x hx
    obtain ⟨w, hwW, hwval⟩ := hdev x hx
    refine ⟨w, hwW, ?_⟩
    rw [hΦdef]
    simp only
    rw [hwval]
    linear_combination (-(x : ℂ)) * Complex.I_sq
  obtain ⟨ε, hε, hfollow⟩ := leaf_follow_on hW hΦd hΦinj hWH hWne hΦsq
    hA hh hD htW hdev'
  refine ⟨ε, hε, ?_⟩
  intro u hu
  have hεu : |ε * u| = |u| := by
    rw [abs_mul]
    rcases hε with h1 | h1 <;> rw [h1] <;> simp
  have hmem : Φ (A t) + ((ε * u : ℝ) : ℂ) ∈ Φ '' W := by
    refine hdev' _ ?_
    rw [hεu]
    exact hu
  rw [hfollow u hu]
  refine ⟨localFlow_mem hmem, ?_⟩
  have hval := localFlow_dev hmem
  rw [hΦdef] at hval
  simp only at hval
  push_cast at hval
  linear_combination (-Complex.I) * hval
    + (Ψ (localFlow (fun z => Complex.I * Ψ z) W (ε * u) (A t)) - Ψ (A t))
      * Complex.I_sq

/-- **The vertical arc through the middle level**: two central-line chart points at
close heights are joined by a margined vertical trajectory arc, tracked in the chart,
whose chart value descends at unit speed and which passes through the central-line
point of every strictly intermediate height. -/
theorem arc_through {q Ψ : ℂ → ℂ} {W : Set ℂ} (hWo : IsOpen W)
    (hWd : DifferentiableOn ℂ Ψ W) (hWinj : Set.InjOn Ψ W)
    (hWH : W ⊆ {z : ℂ | 0 < z.im}) (hWne : ∀ w ∈ W, q w ≠ 0)
    (hWsq : ∀ x ∈ W, deriv Ψ x ^ 2 = -(-q x))
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψ '' W)
    {z z' x'' : ℂ} (hzW : z ∈ W) (hz'W : z' ∈ W) (hxW : x'' ∈ W)
    {hh hh' hh'' : ℝ}
    (hΨz : Ψ z = (c₀.re : ℂ) + (hh : ℂ) * Complex.I)
    (hΨz' : Ψ z' = (c₀.re : ℂ) + (hh' : ℂ) * Complex.I)
    (hΨx : Ψ x'' = (c₀.re : ℂ) + (hh'' : ℂ) * Complex.I)
    (hbz : |hh - c₀.im| < R / 4) (hbz' : |hh' - c₀.im| < R / 4)
    (hlt1 : hh < hh'') (hlt2 : hh'' < hh') :
    ∃ A : ℝ → ℂ,
      IsTrajOn q A (Set.Icc (-(5 * R / 4)) ((hh' - hh) + 5 * R / 4)) ∧
      A 0 = z' ∧ A (hh' - hh) = z ∧ A (hh' - hh'') = x'' ∧
      (∀ u ∈ Set.Icc (0 : ℝ) (hh' - hh), A u ∈ W) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (hh' - hh),
        Ψ (A u) = (c₀.re : ℂ) + ((hh' - u : ℝ) : ℂ) * Complex.I := by
  set L : ℝ := hh' - hh with hLdef
  have hL : 0 < L := by rw [hLdef]; linarith
  have habsb : |hh - c₀.im| < 5 * R / 4 := by linarith [abs_nonneg (hh - c₀.im)]
  have habsb' : |hh' - c₀.im| < 5 * R / 4 := by linarith [abs_nonneg (hh' - c₀.im)]
  obtain ⟨A, harc, harc0, harcL⟩ := vertical_connect (q := fun w => -q w) hWo hWd
    hWinj hWH (fun w hw => neg_ne_zero.mpr (hWne w hw)) hWsq
    (by positivity : (0 : ℝ) < 5 * R) hmarg hzW hz'W hΨz hΨz' habsb habsb'
    (by linarith : hh ≠ hh')
  have habsL : |hh - hh'| = L := by
    rw [hLdef, abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < hh' - hh)]
  rw [habsL] at harc harcL
  have harcq : IsTrajOn q A (Set.Icc (-(5 * R / 4)) (L + 5 * R / 4)) := by
    have h2 := isTrajOn_congr (fun w => neg_neg (q w)) harc
    have h3 : (5 : ℝ) * R / 4 = 5 * R / 4 := rfl
    exact h2
  -- the single anchored development window
  set hwin : ℝ := L + R / 2 with hwindef
  have hwinL : L ≤ hwin := by rw [hwindef]; linarith
  have hwin54 : hwin ≤ 5 * R / 4 := by
    have hL2 : L < R / 2 := by
      rw [hLdef]
      have h4 := abs_lt.mp hbz
      have h5 := abs_lt.mp hbz'
      linarith [h4.1, h5.2]
    rw [hwindef]
    linarith
  have hD : Set.Icc (0 - hwin) (0 + hwin)
      ⊆ Set.Icc (-(5 * R / 4)) (L + 5 * R / 4) := by
    intro u hu
    constructor
    · have := hu.1
      linarith [hwin54]
    · have := hu.2
      linarith [hwin54, hL.le]
  have hz'mem : A 0 ∈ W := by rw [harc0]; exact hz'W
  have hdevm : ∀ x : ℝ, |x| ≤ hwin → Ψ (A 0) - Complex.I * (x : ℂ) ∈ Ψ '' W := by
    intro x hx
    refine hmarg (Metric.mem_ball.mpr ?_)
    rw [harc0, hΨz', dist_eq_norm]
    have h7 : (c₀.re : ℂ) + (hh' : ℂ) * Complex.I - Complex.I * (x : ℂ) - c₀
        = ((hh' - x - c₀.im : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ext_iff]
      constructor
      · simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
      · simp [Complex.add_im, Complex.sub_im, Complex.mul_im]
    rw [h7, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    have h8 := abs_lt.mp hbz'
    have h9 := abs_le.mp hx
    rw [abs_lt]
    constructor <;> [linarith [h8.1, h9.2, hwin54]; linarith [h8.2, h9.1, hwin54]]
  obtain ⟨ε, hε, hdevall⟩ := arc_vert_dev hWo hWd hWinj hWH hWne hWsq harcq
    (by positivity : (0 : ℝ) < hwin) hD hz'mem hdevm
  -- the development sign is forced by the endpoints
  have hε1 : ε = 1 := by
    rcases hε with h1 | h1
    · exact h1
    · exfalso
      have h2 := (hdevall L (by rw [abs_of_pos hL]; exact hwinL)).2
      rw [show (0 : ℝ) + L = L from by rw [zero_add], harcL, harc0, hΨz, hΨz',
        h1] at h2
      have h3 := congrArg Complex.im h2
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.sub_im,
        mul_zero, mul_one, zero_add, add_zero] at h3
      rw [hLdef] at h3
      nlinarith [h3]
  have htrack : ∀ u ∈ Set.Icc (0 : ℝ) L, A u ∈ W := by
    intro u hu
    have h2 := (hdevall u (by
      rw [abs_of_nonneg hu.1]
      exact le_trans hu.2 hwinL)).1
    rwa [zero_add] at h2
  have hheight : ∀ u ∈ Set.Icc (0 : ℝ) L,
      Ψ (A u) = (c₀.re : ℂ) + ((hh' - u : ℝ) : ℂ) * Complex.I := by
    intro u hu
    have h2 := (hdevall u (by
      rw [abs_of_nonneg hu.1]
      exact le_trans hu.2 hwinL)).2
    rw [zero_add] at h2
    rw [h2, harc0, hΨz', hε1]
    push_cast
    ring
  have ha'' : A (hh' - hh'') = x'' := by
    have hmem : hh' - hh'' ∈ Set.Icc (0 : ℝ) L :=
      ⟨by linarith, by rw [hLdef]; linarith⟩
    refine hWinj (htrack _ hmem) hxW ?_
    rw [hheight _ hmem, hΨx]
    push_cast
    ring
  exact ⟨A, harcq, harc0, harcL, ha'', htrack, hheight⟩

/-- **The monotonicity quadrilateral**: the loop formed by an outer-leaf leg, the
vertical trajectory segment, the other outer-leaf leg, and the connecting arc is
closed, meets the middle leaf only at the arc crossing, evaluates to the arc on the
upper parameter half, and stays on the three legs on the lower half. -/
theorem mono_loop {q : ℂ → ℂ}
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} (hϑc : Continuous ϑ)
    {σ σ' σ'' : ℝ → ℂ} (hσc : Continuous σ) (hσ'c : Continuous σ')
    (hσ'' : IsTrajOn (fun z => -q z) σ'' Set.univ)
    {t t' : ℝ} (ha : σ 0 = ϑ t) (ha' : σ' 0 = ϑ t')
    {A : ℝ → ℂ} {L μA : ℝ} (hμA : 0 < μA) (hL : 0 < L)
    (hA : IsTrajOn q A (Set.Icc (-μA) (L + μA)))
    {a'' vc : ℝ} (haI : a'' ∈ Set.Ioo 0 L)
    {uz uz' : ℝ} (hAz' : A 0 = σ' uz') (hAz : A L = σ uz)
    (hAx : A a'' = σ'' vc)
    (hd1 : ∀ v w : ℝ, σ v ≠ σ'' w) (hd2 : ∀ v w : ℝ, σ' v ≠ σ'' w)
    (hϑmiss : ∀ r ∈ Set.uIcc t t', ∀ w : ℝ, ϑ r ≠ σ'' w) :
    ∃ γloop : C(unitInterval, ℂ), γloop 0 = γloop 1 ∧
      (∀ (s : unitInterval) (u : ℝ), u ≠ 0 → γloop s ≠ σ'' (vc + u)) ∧
      (∀ (s : unitInterval), 1 / 2 < (s : ℝ) →
        γloop s = A (L * (2 - 2 * (s : ℝ)))) ∧
      ∀ s : unitInterval, (s : ℝ) ≤ 1 / 2 →
        γloop s ∈ σ' '' Set.uIcc 0 uz' ∪ ϑ '' Set.uIcc t t' ∪ σ '' Set.uIcc 0 uz := by
  -- generic leg: a path from the base point to a parameter value along a curve
  have hleg : ∀ (τ : ℝ → ℂ), Continuous τ → ∀ w : ℝ,
      ∃ p : Path (τ 0) (τ w), Set.range p ⊆ τ '' Set.uIcc 0 w := by
    intro τ hτc w
    rcases le_total 0 w with hw | hw
    · obtain ⟨p, hp⟩ := traj_path hw hτc.continuousOn
      refine ⟨p, ?_⟩
      rw [Set.uIcc_of_le hw]
      exact hp.le
    · obtain ⟨p, hp⟩ := traj_path hw hτc.continuousOn
      refine ⟨p.symm, ?_⟩
      rw [Set.uIcc_of_ge hw]
      intro ζ hζ
      obtain ⟨s, hs⟩ := hζ
      refine hp.le ⟨unitInterval.symm s, ?_⟩
      rw [← hs]
      rfl
  -- the arc as the fourth side, reversed to run from the σ-leg end to the σ'-leg end
  obtain ⟨pA, hpA⟩ := traj_path hL.le (hA.cont.mono (by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩))
  -- the three legs
  obtain ⟨pσ', hpσ'⟩ := hleg σ' hσ'c uz'
  obtain ⟨pϑ, hpϑ⟩ := hleg (fun r => ϑ (t' + r)) (by fun_prop) (t - t')
  obtain ⟨pσ, hpσ⟩ := hleg σ hσc uz
  -- the arc side with an explicit reversed parameterization
  have hAsub : Set.Icc (0 : ℝ) L ⊆ Set.Icc (-μA) (L + μA) := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hAmaps : ∀ r : unitInterval, L * (1 - (r : ℝ)) ∈ Set.Icc (0 : ℝ) L := by
    intro r
    have h1 := r.2.1
    have h2 := r.2.2
    constructor
    · nlinarith
    · nlinarith
  set pA : Path (A L) (A 0) := ⟨⟨fun r => A (L * (1 - (r : ℝ))), by
      refine (hA.cont.mono hAsub).comp_continuous ?_ hAmaps
      fun_prop⟩, by
      change A (L * (1 - ((0 : unitInterval) : ℝ))) = A L
      norm_num, by
      change A (L * (1 - ((1 : unitInterval) : ℝ))) = A 0
      norm_num⟩ with hpAdef
  -- corner casts
  have hc₁ : σ' 0 = ϑ (t' + 0) := by rw [add_zero]; exact ha'
  have hc₂ : σ 0 = ϑ (t' + (t - t')) := by
    rw [show t' + (t - t') = t from by ring]
    exact ha
  set P₂ : Path (σ' 0) (σ 0) := pϑ.cast hc₁ hc₂ with hP₂def
  set P₃ : Path (σ 0) (A L) := pσ.cast rfl hAz with hP₃def
  set P₄ : Path (A L) (σ' uz') := pA.cast rfl hAz'.symm with hP₄def
  obtain ⟨γloop, hcl, hrange, hlow, hup⟩ := quad_eval pσ'.symm P₂ P₃ P₄
  have hupeval : ∀ (s : unitInterval), 1 / 2 < (s : ℝ) →
      γloop s = A (L * (2 - 2 * (s : ℝ))) := by
    intro s hs
    rw [hup s hs]
    change A (L * (1 - (2 * (s : ℝ) - 1))) = A (L * (2 - 2 * (s : ℝ)))
    congr 1
    ring
  have hlow' : ∀ s : unitInterval, (s : ℝ) ≤ 1 / 2 →
      γloop s ∈ σ' '' Set.uIcc 0 uz' ∪ ϑ '' Set.uIcc t t'
        ∪ σ '' Set.uIcc 0 uz := by
    intro s hs
    have h2 := hlow s hs
    rcases h2 with (h3 | h3) | h3
    · left; left
      obtain ⟨r, hr⟩ := h3
      have h4 : pσ'.symm r ∈ Set.range (pσ' : C(unitInterval, ℂ)) :=
        ⟨unitInterval.symm r, rfl⟩
      rw [hr] at h4
      exact hpσ' h4
    · left; right
      obtain ⟨r, hr⟩ := h3
      rw [← hr]
      obtain ⟨w, hw, hval⟩ := hpϑ (⟨r, rfl⟩ : ∃ i, pϑ i = P₂ r)
      refine ⟨t' + w, ?_, hval⟩
      rw [Set.uIcc_comm]
      rcases Set.mem_uIcc.mp hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
      · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    · right
      obtain ⟨r, hr⟩ := h3
      rw [← hr]
      exact hpσ (⟨r, rfl⟩ : ∃ i, pσ i = P₃ r)
  refine ⟨γloop, hcl, ?_, hupeval, hlow'⟩
  intro s u hu hEq
  rcases le_or_gt (s : ℝ) (1 / 2) with hhalf | hhalf
  · have h2 := hlow' s hhalf
    rcases h2 with (h3 | h3) | h3
    · obtain ⟨w, -, hval⟩ := h3
      exact hd2 w (vc + u) (hval.symm ▸ hEq)
    · obtain ⟨w, hwmem, hval⟩ := h3
      exact hϑmiss w hwmem (vc + u) (hval.symm ▸ hEq)
    · obtain ⟨w, -, hval⟩ := h3
      exact hd1 w (vc + u) (hval.symm ▸ hEq)
  · have h2 := hupeval s hhalf
    rw [h2] at hEq
    have hmem : L * (2 - 2 * (s : ℝ)) ∈ Set.Icc (0 : ℝ) L := by
      have h1 := s.2.2
      constructor
      · nlinarith
      · nlinarith [hhalf]
    have h4 := arc_cross_once hbigon hbigonH hμA hA hσ'' hmem
      ⟨haI.1.le, haI.2.le⟩ hEq.symm hAx.symm
    exact hu (by linarith [h4.2])

/-- **Uniform first-order modulus**: for every `η` there is a mesh below which the
curve deviates from its tangent model by at most `η` times the parameter gap. -/
theorem c1_modulus {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hgc : ContinuousOn g (Set.Icc 0 1)) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |t - s| ≤ δ →
      ‖γ t - γ s - ((t - s : ℝ) : ℂ) * g s‖ ≤ η * |t - s| := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hgc
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ', hδ', hmod⟩ := huc η hη
  refine ⟨δ'/2, by linarith, ?_⟩
  intro s hs t ht hst
  have hbound : ∀ u ∈ Set.Icc (min s t) (max s t), ‖g u - g s‖ ≤ η := by
    intro u hu
    have humem : u ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact le_trans (le_min hs.1 ht.1) hu.1
      · exact le_trans hu.2 (max_le hs.2 ht.2)
    have hdist : dist u s < δ' := by
      rw [Real.dist_eq, abs_lt]
      have h1 := hu.1
      have h2 := hu.2
      rw [abs_le] at hst
      rcases le_total s t with h | h
      · rw [min_eq_left h] at h1
        rw [max_eq_right h] at h2
        constructor <;> linarith only [h1, h2, hst.1, hst.2, hδ']
      · rw [min_eq_right h] at h1
        rw [max_eq_left h] at h2
        constructor <;> linarith only [h1, h2, hst.1, hst.2, hδ']
    exact le_of_lt (by
      have := hmod u humem s hs hdist
      rwa [dist_eq_norm] at this)
  have hφd : ∀ u ∈ Set.Icc (min s t) (max s t),
      HasDerivWithinAt (fun u : ℝ => γ u - (u : ℂ) * g s) (g u - g s)
        (Set.Icc (min s t) (max s t)) u := by
    intro u hu
    have humem : u ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact le_trans (le_min hs.1 ht.1) hu.1
      · exact le_trans hu.2 (max_le hs.2 ht.2)
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * g s) (g s) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (g s)
    exact ((hd u humem).sub h1).hasDerivWithinAt
  rcases le_total s t with h | h
  · have hkey := norm_image_sub_le_of_norm_deriv_le_segment' hφd
      (fun u hu => hbound u ⟨hu.1, le_of_lt hu.2⟩) t
      (by rw [min_eq_left h, max_eq_right h]; exact ⟨h, le_refl t⟩)
    have hval : (fun u : ℝ => γ u - (u : ℂ) * g s) t
        - (fun u : ℝ => γ u - (u : ℂ) * g s) (min s t)
        = γ t - γ s - ((t - s : ℝ) : ℂ) * g s := by
      rw [min_eq_left h]
      push_cast
      ring
    rw [hval] at hkey
    calc ‖γ t - γ s - ((t - s : ℝ) : ℂ) * g s‖ ≤ η * (t - min s t) := hkey
      _ = η * |t - s| := by rw [min_eq_left h, abs_of_nonneg (by linarith)]
  · have hkey := norm_image_sub_le_of_norm_deriv_le_segment' hφd
      (fun u hu => hbound u ⟨hu.1, le_of_lt hu.2⟩) s
      (by rw [min_eq_right h, max_eq_left h]; exact ⟨h, le_refl s⟩)
    have hval : (fun u : ℝ => γ u - (u : ℂ) * g s) s
        - (fun u : ℝ => γ u - (u : ℂ) * g s) (min s t)
        = -(γ t - γ s - ((t - s : ℝ) : ℂ) * g s) := by
      rw [min_eq_right h]
      push_cast
      ring
    rw [hval, norm_neg] at hkey
    calc ‖γ t - γ s - ((t - s : ℝ) : ℂ) * g s‖ ≤ η * (s - min s t) := hkey
      _ = η * |t - s| := by
        rw [min_eq_right h, abs_of_nonpos (by linarith), neg_sub]

/-- **Tail vanishing of the winding along a leaf**: for a closed loop with range in
the upper half plane and an all-time transverse leaf meeting it at exactly one
parameter, the winding number about every other leaf point vanishes. -/
theorem tails_zero {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {σ : ℝ → ℂ} (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    {γ : C(unitInterval, ℂ)} (hcl : γ 0 = γ 1)
    (hγim : ∀ s : unitInterval, 0 < (γ s).im)
    {vs : ℝ} (hmiss : ∀ (s : unitInterval) (u : ℝ), u ≠ vs → γ s ≠ σ u) :
    ∀ u : ℝ, u ≠ vs → windingNumber γ (σ u) = 0 := by
  -- the loop's imaginary floor
  obtain ⟨s₀, -, hs₀min⟩ := isCompact_univ.exists_isMinOn ⟨0, Set.mem_univ _⟩
    ((Complex.continuous_im.comp (map_continuous γ)).continuousOn)
  set δγ : ℝ := (γ s₀).im with hδγdef
  have hδγ : 0 < δγ := hγim s₀
  have hfloor : ∀ s : unitInterval, δγ ≤ (γ s).im := by
    intro s
    exact isMinOn_iff.mp hs₀min s (Set.mem_univ s)
  -- the compact region carrying all nonzero windings of leaf points
  obtain ⟨R₀, hR₀⟩ := (isBounded_windingRegion hcl).subset_closedBall 0
  set K : Set ℂ := Metric.closedBall 0 R₀ ∩ {z : ℂ | δγ / 2 ≤ z.im} with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 R₀).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  have hKH : K ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have h2 := hz.2
    simp only [Set.mem_ofPred_eq] at h2 ⊢
    linarith
  -- a leaf point outside the region has zero winding
  have hzero : ∀ u : ℝ, u ≠ vs → σ u ∉ K → windingNumber γ (σ u) = 0 := by
    intro u hu hK
    rcases lt_or_ge (σ u).im (δγ / 2) with him | him
    · refine winding_offline_zero hcl ?_
      intro s hEq
      have h2 := hfloor s
      rw [hEq] at h2
      linarith
    · by_contra hw
      have hmem : σ u ∈ {ζ : ℂ | ζ ∉ Set.range γ ∧ windingNumber γ ζ ≠ 0} := by
        refine ⟨?_, hw⟩
        rintro ⟨s, hs⟩
        exact hmiss s u hu hs
      exact hK ⟨hR₀ hmem, him⟩
  -- both tails escape the region
  have hfwd : ∃ uf : ℝ, vs < uf ∧ σ uf ∉ K := by
    obtain ⟨t₁, ht₁, htK⟩ := leaf_tail_proper hq hbigonH
      (traj_mono hσ (Set.subset_univ (Set.Ici 0))) hKc hKH (vs + 1)
    exact ⟨t₁, by linarith, htK⟩
  have hbwd : ∃ ub : ℝ, ub < vs ∧ σ ub ∉ K := by
    have hσr : IsTrajOn (fun z => -q z) (fun u => σ (-u)) (Set.Ici 0) := by
      have h2 := traj_reverse hσ
      rw [Set.preimage_univ] at h2
      exact traj_mono h2 (Set.subset_univ _)
    obtain ⟨t₁, ht₁, htK⟩ := leaf_tail_proper hq hbigonH hσr hKc hKH (-vs + 1)
    exact ⟨-t₁, by linarith, htK⟩
  -- constancy along each branch
  intro u hu
  rcases lt_or_gt_of_ne hu with hult | hugt
  · obtain ⟨ub, hub, hubK⟩ := hbwd
    have hC : IsPreconnected (σ '' Set.Iio vs) :=
      (isPreconnected_Iio).image σ (hσ.cont.mono (Set.subset_univ _))
    have hdisj : ∀ s : unitInterval, γ s ∉ σ '' Set.Iio vs := by
      rintro s ⟨w, hw, hval⟩
      exact hmiss s w (ne_of_lt hw) hval.symm
    have hconst := windingNumber_eq_of_preconnected hcl hC hdisj
      (Set.mem_image_of_mem σ (show u ∈ Set.Iio vs from hult))
      (Set.mem_image_of_mem σ (show ub ∈ Set.Iio vs from hub))
    rw [hconst]
    exact hzero ub (ne_of_lt hub) hubK
  · obtain ⟨uf, huf, hufK⟩ := hfwd
    have hC : IsPreconnected (σ '' Set.Ioi vs) :=
      (isPreconnected_Ioi).image σ (hσ.cont.mono (Set.subset_univ _))
    have hdisj : ∀ s : unitInterval, γ s ∉ σ '' Set.Ioi vs := by
      rintro s ⟨w, hw, hval⟩
      exact hmiss s w (ne_of_gt hw) hval.symm
    have hconst := windingNumber_eq_of_preconnected hcl hC hdisj
      (Set.mem_image_of_mem σ (show u ∈ Set.Ioi vs from hugt))
      (Set.mem_image_of_mem σ (show uf ∈ Set.Ioi vs from huf))
    rw [hconst]
    exact hzero uf (ne_of_gt huf) hufK

/-- **The offset core**: if `D = τ·G + E` with `‖E‖ ≤ (m/2)|τ|` and `m ≤ ‖G‖`, then
`D + ε'·i·G = 0` forces `ε' = 0`. -/
theorem offset_core {D E G : ℂ} {τ ε' m : ℝ}
    (hm : 0 < m) (hG : m ≤ ‖G‖)
    (hdec : D = (τ : ℂ) * G + E) (hE : ‖E‖ ≤ m / 2 * |τ|)
    (heq : D + (ε' : ℂ) * (Complex.I * G) = 0) (hε' : ε' ≠ 0) : False := by
  have hG0 : G ≠ 0 := by
    intro h
    rw [h, norm_zero] at hG
    linarith
  have hmc : G * (starRingEnd ℂ) G = ((‖G‖^2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq G
  rw [hdec] at heq
  have h1 : ((τ : ℂ) * G + E + (ε' : ℂ) * (Complex.I * G)) * (starRingEnd ℂ) G
      = 0 := by
    rw [heq, zero_mul]
  have hmc' : G * (starRingEnd ℂ) G = ((‖G‖ : ℝ) : ℂ)^2 := by
    rw [hmc]
    push_cast
    ring
  set P : ℂ := E * (starRingEnd ℂ) G with hPdef
  have hkey : ((τ * ‖G‖^2 : ℝ) : ℂ) + P
      + ((ε' * ‖G‖^2 : ℝ) : ℂ) * Complex.I = 0 := by
    rw [hPdef]
    push_cast
    linear_combination h1 - ((τ : ℂ) + (ε' : ℂ) * Complex.I) * hmc'
  have hre := congrArg Complex.re hkey
  have him := congrArg Complex.im hkey
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.zero_re,
    Complex.zero_im, mul_zero, mul_one, sub_zero, zero_add, add_zero] at hre him
  -- hre : τ*‖G‖^2 + P.re = 0 ; him : P.im + ε'*‖G‖^2 = 0
  have hPn : ‖P‖ = ‖E‖ * ‖G‖ := by
    rw [hPdef, norm_mul, RCLike.norm_conj]
  have hPre : |P.re| ≤ m/2 * |τ| * ‖G‖ := by
    calc |P.re| ≤ ‖P‖ := Complex.abs_re_le_norm _
      _ = ‖E‖ * ‖G‖ := hPn
      _ ≤ m/2 * |τ| * ‖G‖ := by
          nlinarith only [hE, norm_nonneg G, norm_nonneg E]
  have hPim : |P.im| ≤ m/2 * |τ| * ‖G‖ := by
    calc |P.im| ≤ ‖P‖ := Complex.abs_im_le_norm _
      _ = ‖E‖ * ‖G‖ := hPn
      _ ≤ m/2 * |τ| * ‖G‖ := by
          nlinarith only [hE, norm_nonneg G, norm_nonneg E]
  have hτ0 : τ = 0 := by
    have h2 : |τ| * ‖G‖^2 ≤ m/2 * |τ| * ‖G‖ := by
      have h3 : |τ * ‖G‖^2| = |P.re| := by
        rw [abs_eq_abs]
        right
        linarith only [hre]
      have h4 : |τ * ‖G‖^2| = |τ| * ‖G‖^2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖G‖^2)]
      linarith only [hPre, h3, h4]
    have h5 : |τ| * (‖G‖ * (m/2)) ≤ 0 := by
      nlinarith only [h2, hG, hm, abs_nonneg τ, norm_nonneg G]
    have h6 : 0 ≤ |τ| * (‖G‖ * (m/2)) := by positivity
    have h7 : |τ| * (‖G‖ * (m/2)) = 0 := le_antisymm h5 h6
    rcases mul_eq_zero.mp h7 with h | h
    · exact abs_eq_zero.mp h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · rw [h'] at hG; linarith
      · linarith
  have hE0 : E = 0 := by
    rw [hτ0, abs_zero, mul_zero] at hE
    exact norm_eq_zero.mp (le_antisymm hE (norm_nonneg E))
  have hP0 : P = 0 := by
    rw [hPdef, hE0, zero_mul]
  have hεG : ε' * ‖G‖^2 = 0 := by
    rw [hP0] at him
    simp only [Complex.zero_im, zero_add] at him
    linarith only [him]
  rcases mul_eq_zero.mp hεG with h | h
  · exact hε' h
  · have : ‖G‖ = 0 := by
      have := sq_eq_zero_iff.mp h
      exact this
    rw [this] at hG
    linarith

/-- **The forward wrap offset**: a pair wrapping through the closure with `t` past the
seam reduces to the offset core with gap `t + 1 - s`. -/
theorem offset_wrap {γ g : ℝ → ℂ} {s t ε' m : ℝ}
    (hm : 0 < m) (hgs : m ≤ ‖g s‖)
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (ht0 : 0 ≤ t) (hs1 : s ≤ 1)
    (hE₁ : ‖γ t - γ 0 - ((t - 0 : ℝ) : ℂ) * g 0‖ ≤ m / 4 * |t - 0|)
    (hE₂ : ‖γ 1 - γ s - ((1 - s : ℝ) : ℂ) * g s‖ ≤ m / 4 * |1 - s|)
    (hg1s : ‖g 1 - g s‖ ≤ m / 4)
    (heq : γ t - γ s + (ε' : ℂ) * (Complex.I * g s) = 0) (hε' : ε' ≠ 0) : False := by
  refine offset_core (D := γ t - γ s)
    (E := γ t - γ s - ((t + 1 - s : ℝ) : ℂ) * g s)
    (G := g s) (τ := t + 1 - s) hm hgs (by push_cast; ring) ?_ heq hε'
  have hτ : |t + 1 - s| = t + 1 - s := abs_of_nonneg (by linarith only [ht0, hs1])
  have ht' : |t - 0| = t := by rw [sub_zero, abs_of_nonneg ht0]
  have hs' : |1 - s| = 1 - s := abs_of_nonneg (by linarith only [hs1])
  rw [hτ]
  have hdec : γ t - γ s - ((t + 1 - s : ℝ) : ℂ) * g s
      = (γ t - γ 0 - ((t - 0 : ℝ) : ℂ) * g 0)
        + (γ 1 - γ s - ((1 - s : ℝ) : ℂ) * g s)
        + ((t : ℝ) : ℂ) * (g 1 - g s) := by
    rw [hcl, hgcl]
    push_cast
    ring
  rw [hdec]
  calc ‖(γ t - γ 0 - ((t - 0 : ℝ) : ℂ) * g 0)
        + (γ 1 - γ s - ((1 - s : ℝ) : ℂ) * g s)
        + ((t : ℝ) : ℂ) * (g 1 - g s)‖
      ≤ ‖γ t - γ 0 - ((t - 0 : ℝ) : ℂ) * g 0‖
        + ‖γ 1 - γ s - ((1 - s : ℝ) : ℂ) * g s‖
        + ‖((t : ℝ) : ℂ) * (g 1 - g s)‖ := norm_add₃_le
    _ ≤ m/4 * t + m/4 * (1 - s) + t * (m/4) := by
        have h3 : ‖((t : ℝ) : ℂ) * (g 1 - g s)‖ ≤ t * (m/4) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
          exact mul_le_mul_of_nonneg_left hg1s ht0
        rw [ht'] at hE₁
        rw [hs'] at hE₂
        linarith only [hE₁, hE₂, h3]
    _ ≤ m/2 * (t + 1 - s) := by nlinarith only [hs1, ht0, hm]

/-- **The backward wrap offset**: the mirror pair with `s` past the seam reduces to the
offset core with gap `t - 1 - s`. -/
theorem offset_wrap' {γ g : ℝ → ℂ} {s t ε' m : ℝ}
    (hm : 0 < m) (hgs : m ≤ ‖g s‖)
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (ht1 : t ≤ 1) (hs0 : 0 ≤ s)
    (hE₁ : ‖γ t - γ 1 - ((t - 1 : ℝ) : ℂ) * g 1‖ ≤ m / 4 * |t - 1|)
    (hE₂ : ‖γ 0 - γ s - ((0 - s : ℝ) : ℂ) * g s‖ ≤ m / 4 * |0 - s|)
    (hg1s : ‖g 1 - g s‖ ≤ m / 4)
    (heq : γ t - γ s + (ε' : ℂ) * (Complex.I * g s) = 0) (hε' : ε' ≠ 0) : False := by
  refine offset_core (D := γ t - γ s)
    (E := γ t - γ s - ((t - 1 - s : ℝ) : ℂ) * g s)
    (G := g s) (τ := t - 1 - s) hm hgs (by push_cast; ring) ?_ heq hε'
  have hτ : |t - 1 - s| = 1 - t + s := by
    rw [abs_of_nonpos (by linarith only [ht1, hs0])]
    ring
  have ht' : |t - 1| = 1 - t := by
    rw [abs_of_nonpos (by linarith only [ht1])]
    ring
  have hs' : |0 - s| = s := by
    rw [abs_of_nonpos (by linarith only [hs0])]
    ring
  rw [hτ]
  have hdec : γ t - γ s - ((t - 1 - s : ℝ) : ℂ) * g s
      = (γ t - γ 1 - ((t - 1 : ℝ) : ℂ) * g 1)
        + (γ 0 - γ s - ((0 - s : ℝ) : ℂ) * g s)
        + ((t - 1 : ℝ) : ℂ) * (g 1 - g s) := by
    rw [hcl, hgcl]
    push_cast
    ring
  rw [hdec]
  calc ‖(γ t - γ 1 - ((t - 1 : ℝ) : ℂ) * g 1)
        + (γ 0 - γ s - ((0 - s : ℝ) : ℂ) * g s)
        + ((t - 1 : ℝ) : ℂ) * (g 1 - g s)‖
      ≤ ‖γ t - γ 1 - ((t - 1 : ℝ) : ℂ) * g 1‖
        + ‖γ 0 - γ s - ((0 - s : ℝ) : ℂ) * g s‖
        + ‖((t - 1 : ℝ) : ℂ) * (g 1 - g s)‖ := norm_add₃_le
    _ ≤ m/4 * (1 - t) + m/4 * s + (1 - t) * (m/4) := by
        have h3 : ‖((t - 1 : ℝ) : ℂ) * (g 1 - g s)‖ ≤ (1 - t) * (m/4) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ht']
          exact mul_le_mul_of_nonneg_left hg1s (by linarith only [ht1])
        rw [ht'] at hE₁
        rw [hs'] at hE₂
        linarith only [hE₁, hE₂, h3]
    _ ≤ m/2 * (1 - t + s) := by nlinarith only [ht1, hs0, hm]

/-- **Far-diagonal separation**: on the compact annulus of parameter pairs away from
the diagonal and the wrap, a simple closed curve is spatially separated. -/
theorem far_sep {γ : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hγc : ContinuousOn γ (Set.Icc 0 1))
    (hcl : γ 0 = γ 1) (hinj : Set.InjOn γ (Set.Ico 0 1)) :
    ∃ sep > 0, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      δ ≤ |t - s| → |t - s| ≤ 1 - δ → sep ≤ ‖γ t - γ s‖ := by
  set P : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc 0 1 ∧ p.2 ∈ Set.Icc 0 1 ∧
    δ ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ 1 - δ} with hPdef
  by_cases hPne : P.Nonempty
  case neg =>
    refine ⟨1, one_pos, fun s hs t ht hd1 hd2 => ?_⟩
    exact absurd ⟨(s, t), hs, ht, hd1, hd2⟩ hPne
  case pos =>
  have hPclosed : IsClosed P := by
    have h1 : IsClosed {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 1} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {p : ℝ × ℝ | p.2 ∈ Set.Icc 0 1} :=
      isClosed_Icc.preimage continuous_snd
    have h3 : IsClosed {p : ℝ × ℝ | δ ≤ |p.2 - p.1|} :=
      isClosed_le continuous_const ((continuous_snd.sub continuous_fst).abs)
    have h4 : IsClosed {p : ℝ × ℝ | |p.2 - p.1| ≤ 1 - δ} :=
      isClosed_le ((continuous_snd.sub continuous_fst).abs) continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  have hPc : IsCompact P :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hPclosed
      fun p hp => ⟨hp.1, hp.2.1⟩
  have hfc : ContinuousOn (fun p : ℝ × ℝ => ‖γ p.2 - γ p.1‖) P := by
    refine ContinuousOn.norm (ContinuousOn.sub ?_ ?_)
    · exact hγc.comp continuous_snd.continuousOn fun p hp => hp.2.1
    · exact hγc.comp continuous_fst.continuousOn fun p hp => hp.1
  obtain ⟨p₀, hp₀, hmin⟩ := hPc.exists_isMinOn hPne hfc
  refine ⟨‖γ p₀.2 - γ p₀.1‖, ?_, ?_⟩
  · rw [gt_iff_lt, norm_pos_iff, sub_ne_zero]
    intro heq
    obtain ⟨hp1, hp2, hpd1, hpd2⟩ := hp₀
    rcases lt_or_ge p₀.1 1 with hlt1 | hge1
    · rcases lt_or_ge p₀.2 1 with hlt2 | hge2
      · have h5 := hinj ⟨hp2.1, hlt2⟩ ⟨hp1.1, hlt1⟩ heq
        rw [h5] at hpd1
        simp only [sub_self, abs_zero] at hpd1
        linarith only [hpd1, hδ]
      · have hp2e : p₀.2 = 1 := le_antisymm hp2.2 hge2
        have hlt1' : p₀.1 < 1 := hlt1
        have heq2 : γ p₀.1 = γ 0 := by
          rw [← heq, hp2e, ← hcl]
        have h5 := hinj ⟨hp1.1, hlt1'⟩
          (Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩) heq2
        rw [h5, hp2e] at hpd2
        simp only [sub_zero, abs_one] at hpd2
        linarith only [hpd2, hδ]
    · have hp1e : p₀.1 = 1 := le_antisymm hp1.2 hge1
      have hlt2' : p₀.2 < 1 := by
        rcases eq_or_lt_of_le hp2.2 with he | hl
        · exfalso
          rw [hp1e, he, sub_self, abs_zero] at hpd1
          linarith only [hpd1, hδ]
        · exact hl
      have heq2 : γ p₀.2 = γ 0 := by
        rw [heq, hp1e, ← hcl]
      have h5 := hinj ⟨hp2.1, hlt2'⟩
        (Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩) heq2
      rw [h5, hp1e] at hpd2
      simp only [zero_sub, abs_neg, abs_one] at hpd2
      linarith only [hpd2, hδ]
  · intro s hs t ht hd1 hd2
    exact hmin (⟨hs, ht, hd1, hd2⟩ : (s, t) ∈ P)

/-- **Offset disjointness**: below a positive threshold, normal offsets of the loop
miss the track. -/
theorem offset_disjoint {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hgc : ContinuousOn g (Set.Icc 0 1))
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (hinj : Set.InjOn γ (Set.Ico 0 1))
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0) :
    ∃ ε₀ > 0, ∀ ε' : ℝ, 0 < |ε'| → |ε'| ≤ ε₀ →
      ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      γ t ≠ γ s - (ε' : ℂ) * (Complex.I * g s) := by
  obtain ⟨u₀, hu₀, hminOn⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one) hgc.norm
  obtain ⟨u₁, hu₁, hmaxOn⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hgc.norm
  set m := ‖g u₀‖ with hmdef
  set M := ‖g u₁‖ with hMdef
  have hm : 0 < m := norm_pos_iff.mpr (hgne u₀ hu₀)
  have hmg : ∀ u ∈ Set.Icc (0:ℝ) 1, m ≤ ‖g u‖ := fun u hu =>
    isMinOn_iff.mp hminOn u hu
  have hMg : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖g u‖ ≤ M := fun u hu =>
    isMaxOn_iff.mp hmaxOn u hu
  have hM : 0 < M := lt_of_lt_of_le hm (hMg u₀ hu₀)
  obtain ⟨δ₁, hδ₁, hmod⟩ := c1_modulus hd hgc
    (show (0:ℝ) < m/4 by linarith only [hm])
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hgc
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₂, hδ₂, hgmod⟩ := huc (m/4) (by linarith only [hm])
  set δ : ℝ := min (min δ₁ (δ₂/2)) (1/4) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ₁ (by linarith only [hδ₂])) (by norm_num)
  have hδa : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδb : δ ≤ δ₂/2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδc : δ ≤ 1/4 := min_le_right _ _
  obtain ⟨sep, hsep, hfarb⟩ := far_sep hδ
    (fun v hv => (hd v hv).continuousAt.continuousWithinAt) hcl hinj
  refine ⟨sep/(2*M), by positivity, ?_⟩
  intro ε' hε'p hε'b s hs t ht heq0
  have hε' : ε' ≠ 0 := abs_pos.mp hε'p
  have heq : γ t - γ s + (ε' : ℂ) * (Complex.I * g s) = 0 := by
    rw [heq0]
    ring
  rcases le_or_gt |t - s| δ with hnear | hfar1
  · have hE := hmod s hs t ht (le_trans hnear hδa)
    exact offset_core (D := γ t - γ s)
      (E := γ t - γ s - ((t - s : ℝ) : ℂ) * g s) (G := g s) (τ := t - s)
      hm (hmg s hs) (by ring)
      (le_trans hE (by nlinarith only [abs_nonneg (t - s), hm])) heq hε'
  · rcases le_or_gt (1 - δ) |t - s| with hwrap | hmid
    · rcases le_total t s with hts | hst
      · have habs : 1 - δ ≤ s - t := by
          rw [abs_of_nonpos (by linarith only [hts])] at hwrap
          linarith only [hwrap]
        have ht' : t ≤ δ := by linarith only [habs, hs.2]
        have hs' : 1 - δ ≤ s := by linarith only [habs, ht.1]
        have hE₁ := hmod 0 ⟨le_refl 0, zero_le_one⟩ t ht
          (by rw [sub_zero, abs_of_nonneg ht.1]; linarith only [ht', hδa])
        have hE₂ := hmod s hs 1 ⟨zero_le_one, le_refl 1⟩
          (by rw [abs_of_nonneg (by linarith only [hs.2] : (0:ℝ) ≤ 1 - s)]
              linarith only [hs', hδa])
        have hg1s : ‖g 1 - g s‖ ≤ m/4 := by
          have h := hgmod 1 ⟨zero_le_one, le_refl 1⟩ s hs
            (by rw [Real.dist_eq, abs_of_nonneg (by linarith only [hs.2] : (0:ℝ) ≤ 1 - s)]
                linarith only [hs', hδb, hδ₂])
          rw [dist_eq_norm] at h
          exact le_of_lt h
        exact offset_wrap hm (hmg s hs) hcl hgcl ht.1 hs.2 hE₁ hE₂ hg1s heq hε'
      · have habs : 1 - δ ≤ t - s := by
          rw [abs_of_nonneg (by linarith only [hst])] at hwrap
          linarith only [hwrap]
        have hs' : s ≤ δ := by linarith only [habs, ht.2]
        have ht' : 1 - δ ≤ t := by linarith only [habs, hs.1]
        have hE₁ := hmod 1 ⟨zero_le_one, le_refl 1⟩ t ht
          (by rw [abs_of_nonpos (by linarith only [ht.2] : t - 1 ≤ 0)]
              linarith only [ht', hδa])
        have hE₂ := hmod s hs 0 ⟨le_refl 0, zero_le_one⟩
          (by rw [zero_sub, abs_neg, abs_of_nonneg hs.1]
              linarith only [hs', hδa])
        have hg1s : ‖g 1 - g s‖ ≤ m/4 := by
          rw [hgcl]
          have h := hgmod 0 ⟨le_refl 0, zero_le_one⟩ s hs
            (by rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hs.1]
                linarith only [hs', hδb, hδ₂])
          rw [dist_eq_norm] at h
          exact le_of_lt h
        exact offset_wrap' hm (hmg s hs) hcl hgcl ht.2 hs.1 hE₁ hE₂ hg1s heq hε'
    · have hsepb := hfarb s hs t ht (le_of_lt hfar1) (le_of_lt hmid)
      have hnorm : ‖γ t - γ s‖ = |ε'| * ‖g s‖ := by
        rw [show γ t - γ s = -((ε' : ℂ) * (Complex.I * g s)) by
          linear_combination heq]
        rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, one_mul]
      have h1 : |ε'| * ‖g s‖ ≤ sep/(2*M) * M := by
        have h2 := hMg s hs
        nlinarith only [hε'b, h2, abs_nonneg ε', hM, norm_nonneg (g s)]
      have h3 : sep/(2*M) * M = sep/2 := by
        field_simp
      rw [hnorm] at hsepb
      linarith only [hsepb, h1, h3, hsep]

set_option maxHeartbeats 400000 in
-- Heartbeats: the deep local-definition tower needs an enlarged elaboration budget.
/-- **Monotonicity of levels against chart heights**: three anchored all-time
transverse leaves visiting the inner ball of a margined chart with the third height
strictly between the first two have the third anchor level strictly between the first
two levels. -/
theorem level_monotone {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} (hϑ : IsTrajOn q ϑ Set.univ)
    {W : Set ℂ} {Ψ : ℂ → ℂ} (hWo : IsOpen W) (hWd : DifferentiableOn ℂ Ψ W)
    (hWinj : Set.InjOn Ψ W) (hWH : W ⊆ {z : ℂ | 0 < z.im})
    (hWne : ∀ w ∈ W, q w ≠ 0) (hWsq : ∀ x ∈ W, deriv Ψ x ^ 2 = -(-q x))
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψ '' W)
    {σ σ' σ'' : ℝ → ℂ}
    (hσ : IsTrajOn (fun z => -q z) σ Set.univ)
    (hσ' : IsTrajOn (fun z => -q z) σ' Set.univ)
    (hσ'' : IsTrajOn (fun z => -q z) σ'' Set.univ)
    {t t' t'' : ℝ} (ha : σ 0 = ϑ t) (ha' : σ' 0 = ϑ t') (ha'' : σ'' 0 = ϑ t'')
    {v v' v'' : ℝ} (hvW : σ v ∈ W) (hv'W : σ' v' ∈ W) (hv''W : σ'' v'' ∈ W)
    (hvb : Ψ (σ v) ∈ Metric.ball c₀ (R / 4))
    (hv'b : Ψ (σ' v') ∈ Metric.ball c₀ (R / 4))
    (hv''b : Ψ (σ'' v'') ∈ Metric.ball c₀ (R / 4))
    (hlt1 : (Ψ (σ v)).im < (Ψ (σ'' v'')).im)
    (hlt2 : (Ψ (σ'' v'')).im < (Ψ (σ' v')).im) :
    t'' ∈ Set.Ioo (min t t') (max t t') := by
  have hquarter : (0 : ℝ) < R / 4 := by linarith
  have hsub4 : Metric.ball c₀ (R / 4) ⊆ Metric.ball c₀ R :=
    Metric.ball_subset_ball (by linarith)
  -- aligned points
  obtain ⟨uz, huzW, huzval⟩ := leaf_align hWo hWd hWinj hWH hWne hWsq hR hmarg
    hσ hvW (hsub4 hvb)
  obtain ⟨uz', huz'W, huz'val⟩ := leaf_align hWo hWd hWinj hWH hWne hWsq hR hmarg
    hσ' hv'W (hsub4 hv'b)
  obtain ⟨uz'', huz''W, huz''val⟩ := leaf_align hWo hWd hWinj hWH hWne hWsq hR
    hmarg hσ'' hv''W (hsub4 hv''b)
  -- height bounds
  have hb : |(Ψ (σ v)).im - c₀.im| < R / 4 := by
    calc |(Ψ (σ v)).im - c₀.im| = |(Ψ (σ v) - c₀).im| := by rw [Complex.sub_im]
      _ ≤ ‖Ψ (σ v) - c₀‖ := Complex.abs_im_le_norm _
      _ < R / 4 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hvb
  have hb' : |(Ψ (σ' v')).im - c₀.im| < R / 4 := by
    calc |(Ψ (σ' v')).im - c₀.im| = |(Ψ (σ' v') - c₀).im| := by
          rw [Complex.sub_im]
      _ ≤ ‖Ψ (σ' v') - c₀‖ := Complex.abs_im_le_norm _
      _ < R / 4 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hv'b
  -- the arc through the middle level
  obtain ⟨A, harcq, hA0, hAL, hAx, htrack, hheight⟩ := arc_through hWo hWd hWinj
    hWH hWne hWsq hR hmarg huzW huz'W huz''W huzval huz'val huz''val hb hb'
    hlt1 hlt2
  set hh : ℝ := (Ψ (σ v)).im with hhdef
  set hh'' : ℝ := (Ψ (σ'' v'')).im with hh''def
  set hh' : ℝ := (Ψ (σ' v')).im with hh'def
  set L : ℝ := hh' - hh with hLdef
  have hL : 0 < L := by rw [hLdef]; linarith
  have haI : hh' - hh'' ∈ Set.Ioo 0 L := ⟨by linarith, by rw [hLdef]; linarith⟩
  -- level distinctness and the contradiction hypothesis
  have hd1 : ∀ w u : ℝ, σ w ≠ σ'' u := by
    intro w u
    exact leaf_disjoint_of_heights hWo hWd hWinj hWH hWne hWsq hbigon hR hmarg
      hσ hσ'' hvW hv''W (hsub4 hvb) (hsub4 hv''b) (by linarith) w u
  have hd2 : ∀ w u : ℝ, σ' w ≠ σ'' u := by
    intro w u
    exact leaf_disjoint_of_heights hWo hWd hWinj hWH hWne hWsq hbigon hR hmarg
      hσ' hσ'' hv'W hv''W (hsub4 hv'b) (hsub4 hv''b) (by linarith) w u
  have htne : t'' ≠ t := by
    intro hE
    refine hd1 0 0 ?_
    rw [ha, ha'', hE]
  have htne' : t'' ≠ t' := by
    intro hE
    refine hd2 0 0 ?_
    rw [ha', ha'', hE]
  by_contra hcon
  rw [Set.mem_Ioo] at hcon
  push Not at hcon
  have hout : t'' < min t t' ∨ max t t' < t'' := by
    rcases lt_or_ge t'' (min t t') with h1 | h1
    · exact Or.inl h1
    · right
      have h2 : min t t' < t'' := by
        rcases eq_or_lt_of_le h1 with h3 | h3
        · exfalso
          rcases min_cases t t' with ⟨h4, -⟩ | ⟨h4, -⟩
          · exact htne (by rw [← h3, h4])
          · exact htne' (by rw [← h3, h4])
        · exact h3
      have h5 := hcon h2
      rcases eq_or_lt_of_le h5 with h6 | h6
      · exfalso
        rcases max_cases t t' with ⟨h4, -⟩ | ⟨h4, -⟩
        · exact htne (by rw [← h6, h4])
        · exact htne' (by rw [← h6, h4])
      · exact h6
  have hϑmiss : ∀ r ∈ Set.uIcc t t', ∀ w : ℝ, ϑ r ≠ σ'' w := by
    intro r hr w hEq
    have hrIcc : r ∈ Set.Icc (min t t') (max t t') := by
      rwa [Set.uIcc, Set.Icc] at hr
    set a₀ : ℝ := min (min t t') t'' - 1 with ha₀def
    have hϑI : IsTrajOn q ϑ (Set.Ici a₀) := traj_mono hϑ (Set.subset_univ _)
    have hcr := leaf_cross_once hq hbigon hbigonH hϑI hσ''
      (show a₀ < r from by
        have h7 := min_le_left (min t t') t''
        have h8 := hrIcc.1
        rw [ha₀def]
        linarith)
      (show a₀ < t'' from by
        have h7 := min_le_right (min t t') t''
        rw [ha₀def]
        linarith)
      hEq ha''.symm
    rcases hout with h9 | h9
    · have h10 := hrIcc.1
      rw [hcr.1] at h10
      linarith
    · have h10 := hrIcc.2
      rw [hcr.1] at h10
      linarith
  -- the quadrilateral
  have hϑc : Continuous ϑ := continuousOn_univ.mp hϑ.cont
  have hσc : Continuous σ := continuousOn_univ.mp hσ.cont
  have hσ'c : Continuous σ' := continuousOn_univ.mp hσ'.cont
  have hσ''c : Continuous σ'' := continuousOn_univ.mp hσ''.cont
  obtain ⟨γloop, hcl, hloopmiss, hupeval, hlow⟩ := mono_loop hbigon hbigonH hϑc
    hσc hσ'c hσ'' ha ha' (by positivity : (0 : ℝ) < 5 * R / 4) hL harcq haI
    hA0 hAL hAx hd1 hd2 hϑmiss
  -- the loop lies in the upper half plane
  have htraj_upper : ∀ (τ : ℝ → ℂ), IsTrajOn (fun z => -q z) τ Set.univ →
      ∀ w : ℝ, 0 < (τ w).im := by
    intro τ hτ w
    obtain ⟨U, -, hpU, hUH, -, -⟩ := hτ.chart w (Set.mem_univ w)
    exact hUH hpU
  have hϑupper : ∀ w : ℝ, 0 < (ϑ w).im := by
    intro w
    obtain ⟨U, -, hpU, hUH, -, -⟩ := hϑ.chart w (Set.mem_univ w)
    exact hUH hpU
  have hparam : ∀ s : unitInterval, 1 / 2 < (s : ℝ) →
      L * (2 - 2 * (s : ℝ)) ∈ Set.Icc (0 : ℝ) L := by
    intro s hs
    have h1 : (0 : ℝ) ≤ 2 - 2 * (s : ℝ) := by linarith only [s.2.2]
    have h2 : (0 : ℝ) ≤ 2 * (s : ℝ) - 1 := by linarith only [hs]
    constructor
    · exact mul_nonneg hL.le h1
    · nlinarith only [mul_nonneg hL.le h2]
  have hγim : ∀ s : unitInterval, 0 < (γloop s).im := by
    intro s
    rcases le_or_gt (s : ℝ) (1 / 2) with hs | hs
    · rcases hlow s hs with (h3 | h3) | h3
      · obtain ⟨w, -, hval⟩ := h3
        rw [← hval]
        exact htraj_upper σ' hσ' w
      · obtain ⟨w, -, hval⟩ := h3
        rw [← hval]
        exact hϑupper w
      · obtain ⟨w, -, hval⟩ := h3
        rw [← hval]
        exact htraj_upper σ hσ w
    · rw [hupeval s hs]
      exact hWH (htrack _ (hparam s hs))
  -- divided-difference and chart-inverse data at the crossing point
  have hdne : deriv Ψ (σ'' uz'') ≠ 0 := by
    intro h0
    have h1 := hWsq _ huz''W
    rw [h0] at h1
    exact hWne _ huz''W (by simpa using h1.symm)
  have hdnorm : 0 < ‖deriv Ψ (σ'' uz'')‖ := norm_pos_iff.mpr hdne
  obtain ⟨δb, hδb, hdd⟩ := divided_diff_ball hWo hWd huz''W
    (‖deriv Ψ (σ'' uz'')‖ / 4) (by linarith)
  obtain ⟨δc, hδc, hnear⟩ := chart_preimage_near_open hWo hWd hWinj huz''W
    hdne hδb
  -- the middle aligned point's chart distance to the center
  have hb'' : |(Ψ (σ'' v'')).im - c₀.im| < R / 4 := by
    calc |(Ψ (σ'' v'')).im - c₀.im| = |(Ψ (σ'' v'') - c₀).im| := by
          rw [Complex.sub_im]
      _ ≤ ‖Ψ (σ'' v'') - c₀‖ := Complex.abs_im_le_norm _
      _ < R / 4 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hv''b
  have hx''dist : ‖Ψ (σ'' uz'') - c₀‖ < R / 4 := by
    rw [huz''val, show (c₀.re : ℂ) + ((Ψ (σ'' v'')).im : ℝ) * Complex.I - c₀
        = (((Ψ (σ'' v'')).im - c₀.im : ℝ) : ℂ) * Complex.I from by
      rw [Complex.ext_iff]
      constructor
      · simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
      · simp [Complex.add_im, Complex.sub_im, Complex.mul_im],
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hb''
  -- horizontal probe development along the middle leaf
  have hpm : ∀ x : ℝ, |x| ≤ R → Ψ (σ'' uz'') + (x : ℂ) ∈ Ψ '' W := by
    intro x hx
    refine hmarg (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, show Ψ (σ'' uz'') + (x : ℂ) - c₀
        = (Ψ (σ'' uz'') - c₀) + (x : ℂ) from by ring]
    calc ‖(Ψ (σ'' uz'') - c₀) + (x : ℂ)‖
        ≤ ‖Ψ (σ'' uz'') - c₀‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ < R / 4 + R := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_lt_add_of_lt_of_le hx''dist hx
      _ < 5 * R := by linarith
  obtain ⟨ε₂, hε₂, hprobes⟩ := leaf_cross_chart hWo hWd hWinj hWH hWne hWsq
    hσ'' hR huz''W hpm
  set hp : ℝ := min R (δc / 2) with hpdef
  have hppos : 0 < hp := lt_min hR (by linarith)
  have hσdev : ∀ u : ℝ, |u| ≤ hp → σ'' (uz'' + u) ∈ Metric.ball (σ'' uz'') δb ∧
      Ψ (σ'' (uz'' + u)) = Ψ (σ'' uz'') + (ε₂ : ℂ) * (u : ℂ) := by
    intro u hu
    have hu1 : |u| ≤ R := le_trans hu (min_le_left _ _)
    obtain ⟨hmem, hval⟩ := hprobes u hu1
    refine ⟨Metric.mem_ball.mpr (hnear _ hmem ?_), hval⟩
    rw [hval, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    have h2 : |ε₂| = 1 := by rcases hε₂ with h' | h' <;> rw [h'] <;> norm_num
    rw [h2, one_mul]
    have h3 : |u| ≤ δc / 2 := le_trans hu (min_le_right _ _)
    linarith
  -- the parameter window around the crossing
  have hLne : L ≠ 0 := hL.ne'
  set aa : ℝ := hh' - hh'' with haadef
  set sstar : ℝ := 1 - aa / (2 * L) with hsstardef
  set ρw : ℝ := min ((L - aa) / (4 * L)) (min (aa / (4 * L)) (δc / (8 * L)))
    with hρwdef
  have haa1 : 0 < aa := haI.1
  have haa2 : aa < L := haI.2
  have hρw : 0 < ρw := by
    refine lt_min (div_pos (by linarith only [haa2]) (by positivity))
      (lt_min (div_pos haa1 (by positivity)) (div_pos hδc (by positivity)))
  have hρw1 : ρw ≤ (L - aa) / (4 * L) := min_le_left _ _
  have hρw2 : ρw ≤ aa / (4 * L) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρw3 : ρw ≤ δc / (8 * L) := le_trans (min_le_right _ _) (min_le_right _ _)
  set b₁ : ℝ := sstar - ρw with hb₁def
  set b₂ : ℝ := sstar + ρw with hb₂def
  have hb₁half : 1 / 2 < b₁ := by
    rw [hb₁def, hsstardef]
    have h2 : aa / (2 * L) + (L - aa) / (4 * L) < 1 / 2 := by
      rw [div_add_div _ _ (by positivity : (2 : ℝ) * L ≠ 0)
        (by positivity : (4 : ℝ) * L ≠ 0), div_lt_iff₀ (by positivity)]
      ring_nf
      nlinarith only [haa2, hL]
    nlinarith only [h2, hρw1]
  have hb₂1 : b₂ ≤ 1 := by
    rw [hb₂def, hsstardef]
    have h2 : ρw ≤ aa / (2 * L) := by
      refine le_trans hρw2 ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [haa1, hL]
    linarith
  have hb₁₂ : b₁ < b₂ := by
    rw [hb₁def, hb₂def]
    linarith
  set c₁ : ℝ := hh' - 2 * L - hh'' with hc₁def
  set c₂ : ℝ := 2 * L with hc₂def
  have hstarzero : c₁ + c₂ * sstar = 0 := by
    rw [hc₁def, hsstardef, haadef, hc₂def]
    field_simp
    ring
  have hlin : ∀ s : ℝ, c₁ + c₂ * s = 2 * L * (s - sstar) := by
    intro s
    have h2 : c₁ + c₂ * s = (c₁ + c₂ * sstar) + c₂ * (s - sstar) := by ring
    rw [h2, hstarzero, hc₂def]
    ring
  have hwinfinal : ∀ s : unitInterval, b₁ ≤ (s : ℝ) → (s : ℝ) ≤ b₂ →
      γloop s ∈ Metric.ball (σ'' uz'') δb ∧
      Ψ (γloop s) = Ψ (σ'' uz'') + Complex.I * ((c₁ + c₂ * (s : ℝ) : ℝ) : ℂ) := by
    intro s hs1 hs2
    have hshalf : 1 / 2 < (s : ℝ) := lt_of_lt_of_le hb₁half hs1
    have hval : Ψ (γloop s) = (c₀.re : ℂ)
        + ((hh' - L * (2 - 2 * (s : ℝ)) : ℝ) : ℂ) * Complex.I := by
      rw [hupeval s hshalf]
      exact hheight _ (hparam s hshalf)
    have hΨdiff : Ψ (γloop s) = Ψ (σ'' uz'')
        + Complex.I * ((c₁ + c₂ * (s : ℝ) : ℝ) : ℂ) := by
      rw [hval, huz''val, hc₁def, hc₂def, hLdef]
      push_cast
      ring
    refine ⟨Metric.mem_ball.mpr (hnear _ ?_ ?_), hΨdiff⟩
    · rw [hupeval s hshalf]
      exact htrack _ (hparam s hshalf)
    · rw [hΨdiff, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, hlin]
      have h3 : |(s : ℝ) - sstar| ≤ ρw := by
        rw [hb₁def] at hs1
        rw [hb₂def] at hs2
        rw [abs_le]
        constructor
        · linarith only [hs1]
        · linarith only [hs2]
      rw [abs_mul, abs_mul]
      have h4 : |(2 : ℝ)| = 2 := by norm_num
      have h5 : |L| = L := abs_of_pos hL
      rw [h4, h5]
      have h6 : 2 * L * ρw ≤ δc / 4 := by
        have h7 : 2 * L * ρw ≤ 2 * L * (δc / (8 * L)) :=
          mul_le_mul_of_nonneg_left hρw3 (by positivity)
        have h8 : 2 * L * (δc / (8 * L)) = δc / 4 := by
          field_simp
          ring
        linarith only [h7, h8]
      have h9 : 2 * L * |(s : ℝ) - sstar| ≤ 2 * L * ρw :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith only [h6, h9, hδc]
  have hyy : (c₁ + c₂ * b₁) * (c₁ + c₂ * b₂) < 0 := by
    rw [hlin b₁, hlin b₂, hb₁def, hb₂def]
    have h2 : sstar - ρw - sstar = -ρw := by ring
    have h3 : sstar + ρw - sstar = ρw := by ring
    rw [h2, h3]
    have hpos : 0 < 2 * L * ρw := by positivity
    nlinarith only [hpos, mul_pos hpos hpos]
  -- clearance of the crossing point off the window
  have hoffK : ∀ s : unitInterval, ((s : ℝ) ≤ b₁ ∨ b₂ ≤ (s : ℝ)) →
      γloop s ≠ σ'' uz'' := by
    intro s hcase hEq
    rcases le_or_gt (s : ℝ) (1 / 2) with hs | hs
    · rcases hlow s hs with (h3 | h3) | h3
      · obtain ⟨w, -, hval⟩ := h3
        exact hd2 w uz'' (hval.trans hEq)
      · obtain ⟨w, hwmem, hval⟩ := h3
        exact hϑmiss w hwmem uz'' (hval.trans hEq)
      · obtain ⟨w, -, hval⟩ := h3
        exact hd1 w uz'' (hval.trans hEq)
    · rw [hupeval s hs] at hEq
      have h4 : Ψ (A (L * (2 - 2 * (s : ℝ)))) = Ψ (σ'' uz'') := by rw [hEq]
      rw [hheight _ (hparam s hs), huz''val] at h4
      have h5 := congrArg Complex.im h4
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_zero, mul_one,
        zero_add, add_zero] at h5
      have h6 : (s : ℝ) = sstar := by
        have hne2 : hh' - hh ≠ 0 := by
          rw [← hLdef]
          exact hL.ne'
        rw [hsstardef, haadef, hc₂def, hLdef]
        rw [hLdef] at h5
        field_simp [hne2]
        linear_combination h5
      rcases hcase with h7 | h7
      · rw [hb₁def] at h7
        rw [h6] at h7
        linarith only [h7, hρw]
      · rw [hb₂def] at h7
        rw [h6] at h7
        linarith only [h7, hρw]
  have hCoffc : IsClosed {s : unitInterval | (s : ℝ) ≤ b₁ ∨ b₂ ≤ (s : ℝ)} :=
    (isClosed_le continuous_subtype_val continuous_const).union
      (isClosed_le continuous_const continuous_subtype_val)
  have hKcomp : IsCompact (γloop '' {s : unitInterval |
      (s : ℝ) ≤ b₁ ∨ b₂ ≤ (s : ℝ)}) :=
    (hCoffc.isCompact).image (map_continuous γloop)
  have hxnotin : σ'' uz'' ∉ γloop '' {s : unitInterval |
      (s : ℝ) ≤ b₁ ∨ b₂ ≤ (s : ℝ)} := by
    rintro ⟨s, hsC, hsE⟩
    exact hoffK s hsC hsE
  obtain ⟨d₀, hd₀, hball⟩ := Metric.mem_nhds_iff.mp
    (hKcomp.isClosed.isOpen_compl.mem_nhds hxnotin)
  have hofffinal : ∀ s : unitInterval, ((s : ℝ) ≤ b₁ ∨ b₂ ≤ (s : ℝ)) →
      γloop s ∉ Metric.ball (σ'' uz'') d₀ := by
    intro s hsC hmem
    exact hball hmem (Set.mem_image_of_mem γloop hsC)
  -- the winding jump against the vanishing tails
  obtain ⟨η, hη, hwne⟩ := winding_jump hσ''c hdne hδb hdd hcl
    (by linarith only [hb₁half] : (0 : ℝ) ≤ b₁) hb₁₂ hb₂1 hwinfinal hyy hppos
    hε₂ hσdev hloopmiss hd₀ hofffinal
  have hmissabs : ∀ (s : unitInterval) (u : ℝ), u ≠ uz'' → γloop s ≠ σ'' u := by
    intro s u hu
    have h2 := hloopmiss s (u - uz'') (sub_ne_zero.mpr hu)
    rwa [show uz'' + (u - uz'') = u from by ring] at h2
  have hzp := tails_zero hq hbigonH hσ'' hcl hγim hmissabs (uz'' + η)
    (by intro h2; exact hη.ne' (by linarith only [h2.symm.le, h2.le]))
  have hzm := tails_zero hq hbigonH hσ'' hcl hγim hmissabs (uz'' - η)
    (by intro h2; exact hη.ne' (by linarith only [h2.symm.le, h2.le]))
  exact hwne (hzp.trans hzm.symm)

section OffsetTransport

open unitInterval

/-- **Offset transport**: the winding of a closed curve is constant along a connected
disjoint track. -/
theorem offset_transport {γ ρ : ℝ → ℂ}
    (hρc : ContinuousOn ρ (Set.Icc 0 1))
    (hcl : γ 0 = γ 1)
    (hdisj : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ ρ s)
    (hc' : Continuous fun t : I => γ ((t : ℝ))) {s₀ s₁ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Set.Icc (0 : ℝ) 1) :
    windingNumber ⟨fun t : I => γ ((t : ℝ)), hc'⟩ (ρ s₀)
      = windingNumber ⟨fun t : I => γ ((t : ℝ)), hc'⟩ (ρ s₁) := by
  refine windingNumber_eq_of_preconnected ?_ (C := ρ '' Set.Icc 0 1)
    (isPreconnected_Icc.image ρ hρc) ?_ ⟨s₀, hs₀, rfl⟩ ⟨s₁, hs₁, rfl⟩
  · change γ (((0 : I) : ℝ)) = γ (((1 : I) : ℝ))
    rw [show (((0 : I) : ℝ)) = 0 from rfl, show (((1 : I) : ℝ)) = 1 from rfl]
    exact hcl
  · rintro t ⟨s, hsm, hval⟩
    exact hdisj s hsm ((t : ℝ)) t.2 hval.symm

/-- **The tangent identity**: a nonzero constant multiple of the velocity loop winds as
the velocity loop. -/
theorem winding_const_mul {g : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hgw : Continuous fun t : I => g ((t : ℝ))) (hgcl : g 1 = g 0)
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0)
    (hw : Continuous fun t : I => c * g ((t : ℝ))) :
    windingNumber ⟨fun t : I => c * g ((t : ℝ)), hw⟩ 0
      = windingNumber ⟨fun t : I => g ((t : ℝ)), hgw⟩ 0 := by
  have hclg : (⟨fun t : I => g ((t : ℝ)), hgw⟩ : C(I, ℂ)) 0
      = (⟨fun t : I => g ((t : ℝ)), hgw⟩ : C(I, ℂ)) 1 := by
    change g (((0 : I) : ℝ)) = g (((1 : I) : ℝ))
    rw [show (((0 : I) : ℝ)) = 0 from rfl, show (((1 : I) : ℝ)) = 1 from rfl]
    exact hgcl.symm
  have hgne' : ∀ t : I, (⟨fun t : I => g ((t : ℝ)), hgw⟩ : C(I, ℂ)) t ≠ 0 :=
    fun t => hgne _ t.2
  have hmul := windingNumber_mul (ContinuousMap.const I c)
    (⟨fun t : I => g ((t : ℝ)), hgw⟩ : C(I, ℂ)) rfl hclg
    (fun _ => hc) hgne'
  have hext : (⟨fun t : I => c * g ((t : ℝ)), hw⟩ : C(I, ℂ))
      = ContinuousMap.const I c * ⟨fun t : I => g ((t : ℝ)), hgw⟩ :=
    ContinuousMap.ext fun t => rfl
  rw [hext, hmul, windingNumber_const c 0 hc, zero_add]

end OffsetTransport

end RiemannDynamics

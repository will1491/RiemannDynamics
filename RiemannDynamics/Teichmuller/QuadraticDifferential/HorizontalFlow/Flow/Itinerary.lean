/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Flow.Atlas

/-!
# Deck translates, zeros, and chart itineraries

Deck invariance of trajectories, isolation and finiteness of the zeros, reach estimates
on a chart ball, and the itinerary encoding of a trajectory as a legal step sequence.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- Points of a small euclidean ball high in the half plane are hyperbolically close:
euclidean radius an eighth of the height gives hyperbolic diameter at most one. -/
theorem ball_hyp_diam {x : ℂ} (hx : 0 < x.im) {e : ℝ} (he : 0 < e)
    (hee : e ≤ x.im / 8) {z w : ℂ} (hz : z ∈ Metric.ball x e) (hw : w ∈ Metric.ball x e)
    (hzim : 0 < z.im) (hwim : 0 < w.im) :
    dist (⟨z, hzim⟩ : UpperHalfPlane) (⟨w, hwim⟩ : UpperHalfPlane) ≤ 1 := by
  have him : ∀ u : ℂ, u ∈ Metric.ball x e → x.im / 2 ≤ u.im := by
    intro u hu
    have h1 : |u.im - x.im| ≤ dist u x := by
      rw [dist_eq_norm, ← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have h2 : dist u x < e := hu
    have := abs_le.mp (le_trans h1 h2.le)
    linarith
  have hd : dist z w ≤ 2 * e := by
    calc dist z w ≤ dist z x + dist x w := dist_triangle _ _ _
      _ ≤ e + e := add_le_add hz.le (by rw [dist_comm]; exact hw.le)
      _ = 2 * e := by ring
  have hsq : x.im / 2 ≤ Real.sqrt (z.im * w.im) := by
    have h1 := him z hz
    have h2 := him w hw
    have : (x.im / 2) ^ 2 ≤ z.im * w.im := by nlinarith
    calc x.im / 2 = Real.sqrt ((x.im / 2) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (z.im * w.im) := Real.sqrt_le_sqrt this
  calc dist (⟨z, hzim⟩ : UpperHalfPlane) (⟨w, hwim⟩ : UpperHalfPlane)
      ≤ dist z w / Real.sqrt (z.im * w.im) := hyp_dist_le _ _
    _ ≤ (2 * e) / (x.im / 2) := by
        gcongr
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith

/-- **A zero-free annulus with positive flat density**: around every point of the upper
half plane there is a small annulus, below an eighth of the height, on which `√‖q‖` has
a positive minimum. -/
theorem exists_annulus {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0) {x : ℂ} (hx : 0 < x.im) :
    ∃ e c : ℝ, 0 < e ∧ 0 < c ∧ e ≤ x.im / 8 ∧
      ∀ w : ℂ, e / 2 ≤ ‖w - x‖ → ‖w - x‖ ≤ e → c ≤ Real.sqrt ‖q w‖ := by
  obtain ⟨V, hVo, hxV, hVsub⟩ := mem_nhdsWithin.mp (zeros_isolated hq hq0 hx)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hVo x hxV
  set e : ℝ := min (r₁ / 2) (x.im / 8) with hedef
  have he : 0 < e := lt_min (by linarith) (by linarith)
  have heim : e ≤ x.im / 8 := min_le_right _ _
  set A : Set ℂ := Metric.closedBall x e ∩ {w : ℂ | e / 2 ≤ ‖w - x‖} with hAdef
  have hmemA : ∀ w ∈ A, e / 2 ≤ ‖w - x‖ ∧ ‖w - x‖ ≤ e := by
    intro w hw
    refine ⟨hw.2, ?_⟩
    have := hw.1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hAH : A ⊆ {z : ℂ | 0 < z.im} := by
    intro w hw
    have h1 : |w.im - x.im| ≤ ‖w - x‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have h2 := abs_le.mp (le_trans h1 (hmemA w hw).2)
    change 0 < w.im
    linarith [h2.1]
  have hAne : ∀ w ∈ A, q w ≠ 0 := by
    intro w hw
    refine hVsub ⟨hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      calc ‖w - x‖ ≤ e := (hmemA w hw).2
        _ ≤ r₁ / 2 := min_le_left _ _
        _ < r₁ := by linarith
    · intro hwx
      rw [Set.mem_singleton_iff] at hwx
      have := (hmemA w hw).1
      rw [hwx, sub_self, norm_zero] at this
      linarith
  have hAclosed : IsClosed A := by
    refine Metric.isClosed_closedBall.inter ?_
    have : {w : ℂ | e / 2 ≤ ‖w - x‖} = (fun w => ‖w - x‖) ⁻¹' Set.Ici (e / 2) := rfl
    rw [this]
    exact IsClosed.preimage ((continuous_id.sub continuous_const).norm)
      isClosed_Ici
  have hAc : IsCompact A :=
    (isCompact_closedBall x e).of_isClosed_subset hAclosed
      Set.inter_subset_left
  have hAnonempty : A.Nonempty := by
    refine ⟨x + ((e / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · rw [Set.mem_setOf_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
  have hcont : ContinuousOn (fun w => Real.sqrt ‖q w‖) A :=
    ((hq.continuousOn.mono hAH).norm).sqrt
  obtain ⟨w₀, hw₀A, hw₀min⟩ := hAc.exists_isMinOn hAnonempty hcont
  refine ⟨e, Real.sqrt ‖q w₀‖, he, ?_, heim, ?_⟩
  · exact Real.sqrt_pos.mpr (norm_pos_iff.mpr (hAne w₀ hw₀A))
  · intro w h1 h2
    exact hw₀min ⟨Metric.mem_closedBall.mpr (by rwa [dist_eq_norm]), h1⟩

/-- Mean value bound from interior derivatives and continuity on the closed segment. -/
theorem seg_bound {σ : ℝ → ℂ} {v u : ℝ} (hvu : v < u) {C : ℝ} (_hC : 0 ≤ C)
    (hσcont : ContinuousOn σ (Set.Icc v u))
    (hderiv : ∀ w ∈ Set.Ioo v u, HasDerivAt σ (deriv σ w) w)
    (hbnd : ∀ w ∈ Set.Ioo v u, ‖deriv σ w‖ ≤ C) :
    ‖σ u - σ v‖ ≤ C * (u - v) := by
  set δ : ℝ := (u - v) / 3 with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    linarith
  set vn : ℕ → ℝ := fun n => v + δ / (n + 1) with hvndef
  set un : ℕ → ℝ := fun n => u - δ / (n + 1) with hundef
  have hstep : ∀ n : ℕ, ‖σ (un n) - σ (vn n)‖ ≤ C * (un n - vn n) := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have hle : δ / (n + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
    have h1 : v < vn n := by rw [hvndef]; simp only; linarith
    have h2 : vn n ≤ un n := by
      rw [hvndef, hundef]
      simp only
      rw [hδdef] at hle
      linarith
    have h3 : un n < u := by rw [hundef]; simp only; linarith
    have hsub : Set.Icc (vn n) (un n) ⊆ Set.Ioo v u := fun w hw =>
      ⟨lt_of_lt_of_le h1 hw.1, lt_of_le_of_lt hw.2 h3⟩
    have hf : ∀ w ∈ Set.Icc (vn n) (un n),
        HasDerivWithinAt σ (deriv σ w) (Set.Icc (vn n) (un n)) w := fun w hw =>
      (hderiv w (hsub hw)).hasDerivWithinAt
    have hb : ∀ w ∈ Set.Ico (vn n) (un n), ‖deriv σ w‖ ≤ C := fun w hw =>
      hbnd w (hsub ⟨hw.1, hw.2.le⟩)
    have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb (un n)
      (Set.right_mem_Icc.mpr h2)
    linarith [this]
  have hvmem : ∀ n, vn n ∈ Set.Icc v u := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have hle : δ / (n + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
    rw [hδdef] at hle
    exact ⟨by rw [hvndef]; simp only; linarith, by rw [hvndef]; simp only; linarith⟩
  have humem : ∀ n, un n ∈ Set.Icc v u := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have hle : δ / (n + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
    rw [hδdef] at hle
    exact ⟨by rw [hundef]; simp only; linarith, by rw [hundef]; simp only; linarith⟩
  have htend : Filter.Tendsto (fun n : ℕ => δ / (n + 1)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => δ * (1 / ((n : ℝ) + 1))) Filter.atTop
        (nhds (δ * 0)) := h0.const_mul δ
    simpa [div_eq_mul_inv, mul_zero] using h2
  have hvt : Filter.Tendsto vn Filter.atTop (nhds v) := by
    have := htend.const_add v
    simpa [hvndef] using this
  have hut : Filter.Tendsto un Filter.atTop (nhds u) := by
    have h2 := (htend.const_mul (-1 : ℝ)).const_add u
    have h3 : (fun n : ℕ => u + (-1) * (δ / (n + 1))) = un := by
      funext n
      rw [hundef]
      ring
    rw [h3] at h2
    simpa using h2
  have hσv : Filter.Tendsto (fun n => σ (vn n)) Filter.atTop (nhds (σ v)) := by
    refine (hσcont v (Set.left_mem_Icc.mpr hvu.le)).tendsto.comp ?_
    exact tendsto_nhdsWithin_iff.mpr ⟨hvt, Filter.Eventually.of_forall hvmem⟩
  have hσu : Filter.Tendsto (fun n => σ (un n)) Filter.atTop (nhds (σ u)) := by
    refine (hσcont u (Set.right_mem_Icc.mpr hvu.le)).tendsto.comp ?_
    exact tendsto_nhdsWithin_iff.mpr ⟨hut, Filter.Eventually.of_forall humem⟩
  refine le_of_tendsto_of_tendsto' ((hσu.sub hσv).norm) ?_ hstep
  exact (hut.sub hvt).const_mul C

/-- **Flat exit cost**: a trajectory piece starting well inside a zero-free annulus ball
and of flat time span below the annulus cost stays inside the ball. -/
theorem traj_stay {q : ℂ → ℂ} {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T)) {x : ℂ} {e c : ℝ} (he : 0 < e) (hc : 0 < c)
    (hann : ∀ w : ℂ, e / 2 ≤ ‖w - x‖ → ‖w - x‖ ≤ e → c ≤ Real.sqrt ‖q w‖)
    {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b) (hbT : b ≤ T)
    (hstart : ‖σ a - x‖ < e / 4) (hspan : b - a < c * (e / 4)) :
    ∀ u ∈ Set.Icc a b, ‖σ u - x‖ < e := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀mem, hu₀⟩ := hcon
  have hIccsub : Set.Icc a b ⊆ Set.Icc 0 T := fun w hw =>
    ⟨le_trans ha hw.1, le_trans hw.2 hbT⟩
  have hcont : ContinuousOn (fun u => ‖σ u - x‖) (Set.Icc a b) :=
    ((hσ.cont.mono hIccsub).sub continuousOn_const).norm
  set S : Set ℝ := Set.Icc a b ∩ (fun u => ‖σ u - x‖) ⁻¹' Set.Ici e with hSdef
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨u₀, hu₀mem, hu₀⟩
  have hSbdd : BddBelow S := ⟨a, fun w hw => hw.1.1⟩
  set ustar : ℝ := sInf S with hustardef
  have hustarS : ustar ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hustarb : ustar ≤ b := hustarS.1.2
  have haustar : a < ustar := by
    rcases eq_or_lt_of_le hustarS.1.1 with heq | h
    · exfalso
      have := hustarS.2
      rw [← heq] at this
      have : e ≤ ‖σ a - x‖ := this
      linarith
    · exact h
  have hcont2 : ContinuousOn (fun u => ‖σ u - x‖) (Set.Icc a ustar) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl hustarb)
  set S₂ : Set ℝ := Set.Icc a ustar ∩ (fun u => ‖σ u - x‖) ⁻¹' Set.Iic (e / 2)
    with hS₂def
  have hS₂closed : IsClosed S₂ :=
    hcont2.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS₂ne : S₂.Nonempty :=
    ⟨a, Set.left_mem_Icc.mpr haustar.le, by
      change ‖σ a - x‖ ≤ e / 2
      linarith⟩
  have hS₂bdd : BddAbove S₂ := ⟨ustar, fun w hw => hw.1.2⟩
  set v : ℝ := sSup S₂ with hvdef
  have hvS₂ : v ∈ S₂ := hS₂closed.csSup_mem hS₂ne hS₂bdd
  have hvustar : v < ustar := by
    rcases eq_or_lt_of_le hvS₂.1.2 with heq | h
    · exfalso
      have h1 := hvS₂.2
      rw [heq] at h1
      have h2 : e ≤ ‖σ ustar - x‖ := hustarS.2
      have : (‖σ ustar - x‖ : ℝ) ≤ e / 2 := h1
      linarith
    · exact h
  have hmid : ∀ w ∈ Set.Ioo v ustar, e / 2 ≤ ‖σ w - x‖ ∧ ‖σ w - x‖ ≤ e := by
    intro w hw
    have hwmem : w ∈ Set.Icc a b :=
      ⟨le_trans hvS₂.1.1 hw.1.le, le_trans hw.2.le hustarb⟩
    constructor
    · by_contra hlt
      push Not at hlt
      have : w ∈ S₂ := ⟨⟨le_trans hvS₂.1.1 hw.1.le, hw.2.le⟩, hlt.le⟩
      have := le_csSup hS₂bdd this
      linarith [hw.1]
    · by_contra hgt
      push Not at hgt
      have : w ∈ S := ⟨hwmem, hgt.le⟩
      have := csInf_le hSbdd this
      linarith [hw.2]
  have hbnd : ∀ w ∈ Set.Ioo v ustar,
      HasDerivAt σ (deriv σ w) w ∧ ‖deriv σ w‖ ≤ 1 / c := by
    intro w hw
    have hw0 : 0 < w := lt_of_le_of_lt (le_trans ha hvS₂.1.1) hw.1
    have hwT : w ≤ T := le_trans (le_trans hw.2.le hustarb) hbT
    have hwmem : w ∈ Set.Icc 0 T := ⟨hw0.le, hwT⟩
    have hnhds : Set.Icc 0 T ∈ nhds w := by
      rcases eq_or_lt_of_le hwT with heq | hlt
      · exfalso
        have := hw.2
        have h2 := hustarb
        have h3 := hbT
        linarith [heq ▸ (lt_of_lt_of_le hw.2 (le_trans hustarb hbT))]
      · exact Icc_mem_nhds hw0 hlt
    obtain ⟨d, hd, hdq⟩ := traj_hasDerivAt hσ hwmem hnhds
    have hderiv : deriv σ w = d := hd.deriv
    obtain ⟨h1, h2⟩ := hmid w hw
    refine ⟨hderiv ▸ hd, ?_⟩
    rw [hderiv]
    have hsq : (c * ‖d‖) ^ 2 ≤ 1 := by
      have hc2 : c ^ 2 ≤ ‖q (σ w)‖ := by
        have := Real.sq_sqrt (norm_nonneg (q (σ w)))
        nlinarith [hann (σ w) h1 h2, Real.sqrt_nonneg ‖q (σ w)‖]
      calc (c * ‖d‖) ^ 2 = c ^ 2 * ‖d‖ ^ 2 := by ring
        _ ≤ ‖q (σ w)‖ * ‖d‖ ^ 2 := by nlinarith [sq_nonneg ‖d‖]
        _ = 1 := by rw [mul_comm]; exact hdq
    have hcd : c * ‖d‖ ≤ 1 := by
      nlinarith [mul_nonneg hc.le (norm_nonneg d)]
    rw [le_div_iff₀ hc]
    linarith [mul_comm c ‖d‖ ▸ hcd]
  have hMV := seg_bound hvustar (by positivity : (0:ℝ) ≤ 1 / c)
    ((hσ.cont.mono hIccsub).mono (Set.Icc_subset_Icc hvS₂.1.1 hustarb))
    (fun w hw => (hbnd w hw).1) (fun w hw => (hbnd w hw).2)
  have hdisp : e / 2 ≤ ‖σ ustar - σ v‖ := by
    have h1 : e ≤ ‖σ ustar - x‖ := hustarS.2
    have h2 : ‖σ v - x‖ ≤ e / 2 := hvS₂.2
    calc e / 2 ≤ ‖σ ustar - x‖ - ‖σ v - x‖ := by linarith
      _ ≤ ‖(σ ustar - x) - (σ v - x)‖ := norm_sub_norm_le _ _
      _ = ‖σ ustar - σ v‖ := by rw [sub_sub_sub_cancel_right]
  have hfinal : c * (e / 2) ≤ ustar - v := by
    have := le_trans hdisp hMV
    rw [div_mul_eq_mul_div, le_div_iff₀ hc] at this
    linarith [this]
  have hint : ustar - v ≤ b - a := by
    have := hvS₂.1.1
    linarith [hustarb]
  linarith [hspan, hfinal, hint, mul_pos hc (by linarith : (0:ℝ) < e / 4)]

/-- **Deck transport of vertical trajectories**: postcomposition with a deck Möbius map
of an automorphic differential carries trajectories to trajectories. -/
theorem traj_deck {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ}
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hauto : ∀ z : ℂ, 0 < z.im → q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hσ : IsTrajOn q σ s) :
    IsTrajOn q (fun u => moebiusMap γ (σ u)) s := by
  constructor
  · intro t ht
    have him : 0 < (σ t).im := (traj_regular hσ ht).1
    exact (moebius_diffAt γ him).continuousAt.comp_continuousWithinAt (hσ.cont t ht)
  · intro t ht
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hσ.chart t ht
    refine ⟨moebiusMap γ '' U, isOpen_moebius_image γ hUo hUH, ⟨σ t, hpU, rfl⟩,
      ?_, ?_, fun w => Φ (moebiusMap γ⁻¹ w), ?_, ?_, ?_, ?_⟩
    · rintro w ⟨z, hzU, rfl⟩
      exact moebiusMap_im_pos γ (hUH hzU)
    · rintro w ⟨z, hzU, rfl⟩
      have hzim : 0 < z.im := hUH hzU
      rw [hauto z hzim]
      exact mul_ne_zero (pow_ne_zero 4
        (moebiusDenom_ne_zero_of_im_ne_zero γ hzim.ne')) (hUne z hzU)
    · intro w hw
      obtain ⟨z, hzU, rfl⟩ := hw
      have hzim : 0 < z.im := hUH hzU
      have hinvd : DifferentiableWithinAt ℂ (moebiusMap γ⁻¹) (moebiusMap γ '' U)
          (moebiusMap γ z) :=
        ((hasDerivAt_moebiusMap_of_im_pos γ⁻¹
          (moebiusMap_im_pos γ hzim)).differentiableAt).differentiableWithinAt
      have hmaps : Set.MapsTo (moebiusMap γ⁻¹) (moebiusMap γ '' U) U := by
        rintro w' ⟨z', hz'U, rfl⟩
        rw [moebius_cancel γ (hUH hz'U)]
        exact hz'U
      have hg : DifferentiableWithinAt ℂ Φ U (moebiusMap γ⁻¹ (moebiusMap γ z)) := by
        rw [moebius_cancel γ hzim]
        exact hΦd z hzU
      exact hg.comp (moebiusMap γ z) hinvd hmaps
    · rintro w₁ ⟨z₁, hz₁U, rfl⟩ w₂ ⟨z₂, hz₂U, rfl⟩ heq
      have h1 : 0 < z₁.im := hUH hz₁U
      have h2 : 0 < z₂.im := hUH hz₂U
      beta_reduce at heq
      rw [moebius_cancel γ h1, moebius_cancel γ h2] at heq
      rw [hΦinj hz₁U hz₂U heq]
    · rintro w ⟨z, hzU, rfl⟩
      have hzim : 0 < z.im := hUH hzU
      have hwim : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hzim
      have hdz : moebiusDenom γ z ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero γ hzim.ne'
      have hΦz : DifferentiableAt ℂ Φ z := hΦd.differentiableAt (hUo.mem_nhds hzU)
      have hinner : HasDerivAt (moebiusMap γ⁻¹)
          ((moebiusDenom γ⁻¹ (moebiusMap γ z) ^ 2)⁻¹) (moebiusMap γ z) :=
        hasDerivAt_moebiusMap_of_im_pos γ⁻¹ hwim
      have houter : HasDerivAt Φ (deriv Φ z) (moebiusMap γ⁻¹ (moebiusMap γ z)) := by
        rw [moebius_cancel γ hzim]
        exact hΦz.hasDerivAt
      have hcomp := HasDerivAt.comp (moebiusMap γ z) houter hinner
      have hd : deriv (fun w => Φ (moebiusMap γ⁻¹ w)) (moebiusMap γ z)
          = deriv Φ z * (moebiusDenom γ⁻¹ (moebiusMap γ z) ^ 2)⁻¹ := hcomp.deriv
      have hcocycle : moebiusDenom γ⁻¹ (moebiusMap γ z) * moebiusDenom γ z = 1 := by
        rw [moebiusDenom_mul γ⁻¹ γ z hdz, inv_mul_cancel, moebiusDenom_one]
      have hΦsqz := hΦsq z hzU
      have hqw := hauto z hzim
      rw [hd]
      have he : moebiusDenom γ⁻¹ (moebiusMap γ z) = (moebiusDenom γ z)⁻¹ :=
        eq_inv_of_mul_eq_one_left hcocycle
      calc (deriv Φ z * (moebiusDenom γ⁻¹ (moebiusMap γ z) ^ 2)⁻¹) ^ 2
          = deriv Φ z ^ 2 * ((moebiusDenom γ⁻¹ (moebiusMap γ z) ^ 2)⁻¹) ^ 2 := by
            ring
        _ = -q z * (((moebiusDenom γ z)⁻¹ ^ 2)⁻¹) ^ 2 := by rw [hΦsqz, he]
        _ = -(moebiusDenom γ z ^ 4 * q z) := by
            field_simp
        _ = -q (moebiusMap γ z) := by rw [← hqw]
    · filter_upwards [hev] with u hu
      have huim : 0 < (σ u).im := hUH hu.1
      have htim : 0 < (σ t).im := hUH hpU
      refine ⟨⟨σ u, hu.1, rfl⟩, ?_⟩
      beta_reduce
      rw [moebius_cancel γ huim, moebius_cancel γ htim]
      exact hu.2

/-- **Uniform flat step cost on a compact**: below a uniform flat time span, trajectory
pieces starting in a fixed compact of the upper half plane move hyperbolic distance at
most one. -/
theorem uniform_step {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0) {K' : Set ℂ} (hK'c : IsCompact K')
    (hK'H : ∀ x ∈ K', 0 < x.im) :
    ∃ η : ℝ, 0 < η ∧ ∀ (σ : ℝ → ℂ) (T a b : ℝ), IsTrajOn q σ (Set.Icc 0 T) →
      0 ≤ a → a ≤ b → b ≤ T → b - a < η → σ a ∈ K' →
      ∀ u ∈ Set.Icc a b, ∀ him : 0 < (σ u).im, ∀ him' : 0 < (σ a).im,
        dist (⟨σ u, him⟩ : UpperHalfPlane) (⟨σ a, him'⟩ : UpperHalfPlane) ≤ 1 := by
  have hloc : ∀ x : K', ∃ e c : ℝ, 0 < e ∧ 0 < c ∧ e ≤ (x : ℂ).im / 8 ∧
      ∀ w : ℂ, e / 2 ≤ ‖w - (x : ℂ)‖ → ‖w - (x : ℂ)‖ ≤ e →
        c ≤ Real.sqrt ‖q w‖ := fun x =>
    exists_annulus hq hq0 (hK'H x x.2)
  choose e c he hc hei hann using hloc
  obtain ⟨F, hF⟩ := hK'c.elim_finite_subcover
    (fun x : K' => Metric.ball (x : ℂ) (e x / 4))
    (fun x => Metric.isOpen_ball) (fun w hw => Set.mem_iUnion.mpr
      ⟨⟨w, hw⟩, Metric.mem_ball_self (by linarith [he ⟨w, hw⟩])⟩)
  by_cases hFne : F.Nonempty
  · set η : ℝ := F.inf' hFne (fun x => c x * (e x / 4)) with hηdef
    have hη : 0 < η := by
      rw [hηdef, Finset.lt_inf'_iff]
      intro x _
      have := hc x
      have := he x
      positivity
    refine ⟨η, hη, ?_⟩
    intro σ T a b hσ ha hab hbT hspan haK
    obtain ⟨x, hxF, hax⟩ := Set.mem_iUnion₂.mp (hF haK)
    have hηle : η ≤ c x * (e x / 4) := Finset.inf'_le _ hxF
    have hstay := traj_stay hσ (he x) (hc x) (hann x) ha hab hbT
      (by rwa [← dist_eq_norm]) (by linarith)
    intro u hu him him'
    have hu' : ‖σ u - (x : ℂ)‖ < e x := hstay u hu
    have ha' : ‖σ a - (x : ℂ)‖ < e x := hstay a (Set.left_mem_Icc.mpr hab)
    exact ball_hyp_diam (hK'H x x.2) (he x) (hei x)
      (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
      (Metric.mem_ball.mpr (by rwa [dist_eq_norm])) him him'
  · refine ⟨1, one_pos, ?_⟩
    intro σ T a b hσ ha hab hbT hspan haK
    exfalso
    obtain ⟨x, hxF, -⟩ := Set.mem_iUnion₂.mp (hF haK)
    exact hFne ⟨x, hxF⟩

/-- The zeros of a not identically vanishing differential are finite in every compact
subset of the upper half plane. -/
theorem zeros_finite {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0) {L : Set ℂ} (hL : IsCompact L)
    (hLH : L ⊆ {z : ℂ | 0 < z.im}) :
    Set.Finite {z ∈ L | q z = 0} := by
  have hloc : ∀ x : L, ∃ V : Set ℂ, IsOpen V ∧ (x : ℂ) ∈ V ∧
      ∀ w ∈ V, q w = 0 → w = (x : ℂ) := by
    intro x
    have hev := zeros_isolated hq hq0 (hLH x.2)
    obtain ⟨V, hVo, hxV, hVsub⟩ := mem_nhdsWithin.mp hev
    refine ⟨V, hVo, hxV, fun w hwV hw0 => ?_⟩
    by_contra hne
    exact hVsub ⟨hwV, hne⟩ hw0
  choose V hVo hVmem hVone using hloc
  obtain ⟨F, hF⟩ := hL.elim_finite_subcover V hVo
    (fun w hw => Set.mem_iUnion.mpr ⟨⟨w, hw⟩, hVmem ⟨w, hw⟩⟩)
  refine Set.Finite.subset (Set.Finite.image (fun x : ↥L => (x : ℂ))
    F.finite_toSet) ?_
  rintro z ⟨hzL, hz0⟩
  obtain ⟨x, hxF, hzV⟩ := Set.mem_iUnion₂.mp (hF hzL)
  exact ⟨x, hxF, (hVone x z hzV hz0).symm⟩

/-- **Two-sided power bounds at a zero**: near an isolated zero the modulus of the
differential is comparable to the order power of the distance. -/
theorem zero_order_bounds {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₁ : ℂ, 0 < z₁.im ∧ q z₁ ≠ 0) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    ∃ (M : ℕ) (r C₁ C₂ : ℝ), 0 < r ∧ 0 < C₁ ∧ 0 < C₂ ∧
      Metric.ball z₀ r ⊆ {z : ℂ | 0 < z.im} ∧
      ∀ w ∈ Metric.ball z₀ r,
        C₁ * ‖w - z₀‖ ^ M ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ * ‖w - z₀‖ ^ M := by
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hnc : ¬ ∀ᶠ z in nhds z₀, q z = 0 := by
    intro hev
    have hacc := zeros_isolated hq hq0 hz₀
    have hcomb := hacc.and (hev.filter_mono nhdsWithin_le_nhds)
    haveI : (nhdsWithin z₀ ({z₀}ᶜ : Set ℂ)).NeBot :=
      Module.punctured_nhds_neBot ℝ ℂ z₀
    obtain ⟨w, hw1, hw2⟩ := hcomb.exists
    exact hw1 hw2
  obtain ⟨M, g, hg, hg0, hfac, -⟩ := exists_order_factorization hH hq hz₀ hnc
  have hgc : ContinuousAt g z₀ := hg.continuousAt
  have hgball : ∀ᶠ w in nhds z₀, ‖g w - g z₀‖ < ‖g z₀‖ / 2 := by
    have h := hgc (Metric.ball_mem_nhds (g z₀) (by positivity : (0:ℝ) < ‖g z₀‖ / 2))
    filter_upwards [h] with w hw
    rw [← dist_eq_norm]
    exact hw
  have hmem : {w | q w = (w - z₀) ^ M * g w}
      ∩ ({w | ‖g w - g z₀‖ < ‖g z₀‖ / 2} ∩ {z : ℂ | 0 < z.im}) ∈ nhds z₀ :=
    Filter.inter_mem hfac (Filter.inter_mem hgball (hH.mem_nhds hz₀))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨M, r, ‖g z₀‖ / 2, 2 * ‖g z₀‖, hr, by positivity, by positivity,
    fun w hw => (hball hw).2.2, ?_⟩
  intro w hw
  obtain ⟨hfacw, hgw, -⟩ := hball hw
  have hgw' : ‖g w - g z₀‖ < ‖g z₀‖ / 2 := hgw
  have hlow : ‖g z₀‖ / 2 ≤ ‖g w‖ := by
    have h1 : ‖g z₀‖ - ‖g w‖ ≤ ‖g z₀ - g w‖ := norm_sub_norm_le (g z₀) (g w)
    rw [norm_sub_rev] at h1
    linarith
  have hup : ‖g w‖ ≤ 2 * ‖g z₀‖ := by
    have h1 : ‖g w‖ - ‖g z₀‖ ≤ ‖g w - g z₀‖ := norm_sub_norm_le (g w) (g z₀)
    linarith
  rw [hfacw, norm_mul, norm_pow]
  constructor
  · have := mul_le_mul_of_nonneg_left hlow (pow_nonneg (norm_nonneg (w - z₀)) M)
    calc ‖g z₀‖ / 2 * ‖w - z₀‖ ^ M = ‖w - z₀‖ ^ M * (‖g z₀‖ / 2) := by ring
      _ ≤ ‖w - z₀‖ ^ M * ‖g w‖ := this
  · have := mul_le_mul_of_nonneg_left hup (pow_nonneg (norm_nonneg (w - z₀)) M)
    calc ‖w - z₀‖ ^ M * ‖g w‖ ≤ ‖w - z₀‖ ^ M * (2 * ‖g z₀‖) := this
      _ = 2 * ‖g z₀‖ * ‖w - z₀‖ ^ M := by ring

/-- Time translation of a vertical trajectory. -/
theorem traj_shift {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ} (t₀ : ℝ)
    (h : IsTrajOn q σ s) :
    IsTrajOn q (fun u => σ (u + t₀)) ((fun u : ℝ => u + t₀) ⁻¹' s) := by
  have hmap : ∀ t : ℝ, Filter.Tendsto (fun u : ℝ => u + t₀)
      (nhdsWithin t ((fun u : ℝ => u + t₀) ⁻¹' s)) (nhdsWithin (t + t₀) s) := by
    intro t
    refine Filter.Tendsto.inf ((continuous_add_const t₀).tendsto t) ?_
    exact Filter.tendsto_principal_principal.mpr fun u hu => hu
  constructor
  · intro t ht
    exact ContinuousWithinAt.comp (h.cont (t + t₀) ht)
      ((continuous_add_const t₀).continuousWithinAt) (fun u hu => hu)
  · intro t ht
    obtain ⟨U, hUo, hmem, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := h.chart (t + t₀) ht
    refine ⟨U, hUo, hmem, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
    filter_upwards [(hmap t).eventually hev] with u hu
    refine ⟨hu.1, ?_⟩
    rw [hu.2]
    push_cast
    ring

/-- **Flat reach of a zero**: a trajectory running from the sphere of euclidean radius
`s` into the ball of radius `s/8` around a point needs flat time at least
`c(s) · s/4`, where `c(s)` is the annulus flat density floor. -/
theorem traj_reach {q : ℂ → ℂ} {σ : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hσ : IsTrajOn q σ (Set.Icc 0 T)) {z₀ : ℂ} {s cs : ℝ} (hs : 0 < s) (hcs : 0 < cs)
    (hann : ∀ w : ℂ, s / 2 ≤ ‖w - z₀‖ → ‖w - z₀‖ ≤ s → cs ≤ Real.sqrt ‖q w‖)
    (hout : s ≤ ‖σ 0 - z₀‖) (hin : ‖σ T - z₀‖ ≤ s / 8) :
    cs * (s / 4) ≤ T := by
  by_contra hlt
  push Not at hlt
  set σ' : ℝ → ℂ := fun u => σ (T - u) with hσ'def
  have hσ'traj : IsTrajOn q σ' (Set.Icc 0 T) := by
    have h1 := traj_reverse (traj_shift T hσ)
    have hset : (fun u : ℝ => -u) ⁻¹' ((fun u : ℝ => u + T) ⁻¹' Set.Icc 0 T)
        = Set.Icc 0 T := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        constructor <;> linarith
      · rintro ⟨h1, h2⟩
        constructor <;> linarith
    rw [hset] at h1
    have hfun : (fun u : ℝ => (fun v => σ (v + T)) (-u)) = σ' := by
      funext u
      rw [hσ'def]
      simp only
      ring_nf
    rwa [hfun] at h1
  have hstart : ‖σ' 0 - z₀‖ < s / 4 := by
    rw [hσ'def]
    simp only [sub_zero]
    calc ‖σ T - z₀‖ ≤ s / 8 := hin
      _ < s / 4 := by linarith
  have hstay := traj_stay hσ'traj hs hcs hann (le_refl 0) hT (le_refl T) hstart
    (by linarith) T (Set.right_mem_Icc.mpr hT)
  rw [hσ'def] at hstay
  simp only [sub_self] at hstay
  linarith [hout, hstay]

/-- **Squared flat reach**: a trajectory of time span at most `ε` from `z'` into the
deep eighth-ball of a zero forces the integer-power radius bound
`C₁/(2^M · 16) · min(‖z' − z₀‖, r₀/2)^(M+2) ≤ ε²`. -/
theorem reach_radius_sq {q : ℂ → ℂ} {σ : ℝ → ℂ} {T ε : ℝ}
    (hT : 0 ≤ T) (hTε : T ≤ ε) (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {z₀ : ℂ} {M : ℕ} {r₀ C₁ C₂ : ℝ} (hr₀ : 0 < r₀) (hC₁ : 0 < C₁)
    (hbounds : ∀ w ∈ Metric.ball z₀ r₀,
      C₁ * ‖w - z₀‖ ^ M ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ * ‖w - z₀‖ ^ M)
    (hz' : 0 < ‖σ 0 - z₀‖)
    (hin : ‖σ T - z₀‖ ≤ min ‖σ 0 - z₀‖ (r₀ / 2) / 8) :
    C₁ / (2 ^ M * 16) * min ‖σ 0 - z₀‖ (r₀ / 2) ^ (M + 2) ≤ ε ^ 2 := by
  set s : ℝ := min ‖σ 0 - z₀‖ (r₀ / 2) with hsdef
  have hs : 0 < s := lt_min hz' (by linarith)
  set cs : ℝ := Real.sqrt (C₁ * (s / 2) ^ M) with hcsdef
  have hcs : 0 < cs := Real.sqrt_pos.mpr (by positivity)
  have hann : ∀ w : ℂ, s / 2 ≤ ‖w - z₀‖ → ‖w - z₀‖ ≤ s → cs ≤ Real.sqrt ‖q w‖ := by
    intro w h1 h2
    have hwball : w ∈ Metric.ball z₀ r₀ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : s ≤ r₀ / 2 := min_le_right _ _
      linarith
    have hpow : C₁ * (s / 2) ^ M ≤ C₁ * ‖w - z₀‖ ^ M := by
      have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ s / 2) h1 M
      nlinarith
    exact Real.sqrt_le_sqrt (le_trans hpow (hbounds w hwball).1)
  have hreach : cs * (s / 4) ≤ T :=
    traj_reach hT hσ hs hcs hann (min_le_left _ _) hin
  have hsq : (cs * (s / 4)) ^ 2 ≤ ε ^ 2 := by
    have h1 : cs * (s / 4) ≤ ε := le_trans hreach hTε
    nlinarith [mul_pos hcs (by linarith : (0:ℝ) < s / 4)]
  have hexpand : (cs * (s / 4)) ^ 2 = C₁ / (2 ^ M * 16) * s ^ (M + 2) := by
    have hcs2 : cs ^ 2 = C₁ * (s / 2) ^ M := Real.sq_sqrt (by positivity)
    have hdiv : (s / 2) ^ M = s ^ M / 2 ^ M := div_pow s 2 M
    calc (cs * (s / 4)) ^ 2 = cs ^ 2 * (s ^ 2 / 16) := by ring
      _ = C₁ * (s ^ M / 2 ^ M) * (s ^ 2 / 16) := by rw [hcs2, hdiv]
      _ = C₁ / (2 ^ M * 16) * (s ^ M * s ^ 2) := by
          field_simp
      _ = C₁ / (2 ^ M * 16) * s ^ (M + 2) := by rw [pow_add]
  linarith [hexpand ▸ hsq]

/-- **The ball mass bound**: the `|q|` mass of a small ball at a zero is controlled by
the order power of its radius times its area. -/
theorem ball_mass {q : ℂ → ℂ} {z₀ : ℂ} {M : ℕ} {r₀ C₁ C₂ : ℝ} (hρr : 0 < r₀)
    (hbounds : ∀ w ∈ Metric.ball z₀ r₀,
      C₁ * ‖w - z₀‖ ^ M ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ * ‖w - z₀‖ ^ M)
    {ρ : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ r₀) :
    ∫⁻ w in Metric.ball z₀ ρ, ‖q w‖ₑ
      ≤ ENNReal.ofReal (C₂ * ρ ^ M) * volume (Metric.ball z₀ ρ) := by
  have hpt : ∀ w ∈ Metric.ball z₀ ρ, ‖q w‖ₑ ≤ ENNReal.ofReal (C₂ * ρ ^ M) := by
    intro w hw
    have hwr : ‖w - z₀‖ < ρ := by
      rwa [Metric.mem_ball, dist_eq_norm] at hw
    have hwball : w ∈ Metric.ball z₀ r₀ := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have hup := (hbounds w hwball).2
    have hpow : ‖w - z₀‖ ^ M ≤ ρ ^ M := pow_le_pow_left₀ (norm_nonneg _) hwr.le M
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hC₂pos : 0 ≤ C₂ := by
      set w' : ℂ := z₀ + ((ρ / 2 : ℝ) : ℂ) with hw'def
      have hw'n : ‖w' - z₀‖ = ρ / 2 := by
        rw [hw'def, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      have hw'ball : w' ∈ Metric.ball z₀ r₀ := by
        rw [Metric.mem_ball, dist_eq_norm, hw'n]
        linarith
      have h := (hbounds w' hw'ball).2
      rw [hw'n] at h
      nlinarith [norm_nonneg (q w'), pow_pos (by linarith : (0:ℝ) < ρ / 2) M]
    nlinarith
  calc ∫⁻ w in Metric.ball z₀ ρ, ‖q w‖ₑ
      ≤ ∫⁻ _ in Metric.ball z₀ ρ, ENNReal.ofReal (C₂ * ρ ^ M) := by
        refine setLIntegral_mono_ae' measurableSet_ball ?_
        filter_upwards with w hw using hpt w hw
    _ = ENNReal.ofReal (C₂ * ρ ^ M) * volume (Metric.ball z₀ ρ) := by
        rw [setLIntegral_const]

/-- **Compact track on the maximal window**: the track of a trajectory on `[0, c)` over a
cocompact group stays in one compact subset of the upper half plane. -/
theorem traj_track_compact_Ico {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (_hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hσ : IsTrajOn q σ (Set.Ico 0 c)) :
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ {z : ℂ | 0 < z.im} ∧
      ∀ u ∈ Set.Ico 0 c, σ u ∈ L := by
  have hreg : ∀ u ∈ Set.Ico 0 c, 0 < (σ u).im := fun u hu => (traj_regular hσ hu).1
  have h0mem : (0 : ℝ) ∈ Set.Ico 0 c := ⟨le_refl 0, hc⟩
  set τ₀ : UpperHalfPlane := ⟨σ 0, hreg 0 h0mem⟩ with hτ₀def
  obtain ⟨K, hK, hcov⟩ := exists_compact_covering Γ hcc
  set K' : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' K with hK'def
  have hK'c : IsCompact K' := hK.image UpperHalfPlane.continuous_coe
  have hK'H : ∀ x ∈ K', 0 < x.im := by
    rintro x ⟨τ, hτ, rfl⟩
    exact τ.2
  obtain ⟨η, hη, hstep⟩ := uniform_step q.holo hq0 hK'c hK'H
  have key : ∀ k : ℕ, ∀ u, ∀ hu : u ∈ Set.Ico 0 c, u ≤ k * (η / 2) →
      dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane) τ₀ ≤ k := by
    intro k
    induction k with
    | zero =>
      intro u hu hle
      have hu0 : u = 0 := le_antisymm (by simpa using hle) hu.1
      subst hu0
      simp [hτ₀def]
    | succ k ih =>
      intro u hu hle
      by_cases hcase : u ≤ k * (η / 2)
      · calc dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane) τ₀ ≤ k := ih u hu hcase
          _ ≤ (k + 1 : ℕ) := by push_cast; linarith
      · push Not at hcase
        set a : ℝ := k * (η / 2) with hadef
        have ha0 : 0 ≤ a := by positivity
        have hau : a ≤ u := hcase.le
        have haI : a ∈ Set.Ico 0 c := ⟨ha0, lt_of_le_of_lt hau hu.2⟩
        have hspan : u - a < η := by
          have := hle
          push_cast at this
          rw [hadef]
          linarith
        have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
          traj_mono hσ (fun v hv => ⟨hv.1, lt_of_le_of_lt hv.2 hu.2⟩)
        obtain ⟨γ, hγK⟩ := hcov ⟨σ a, hreg a haI⟩
        set σ' : ℝ → ℂ := fun v => moebiusMap (↑γ) (σ v) with hσ'def
        have hσ' : IsTrajOn q σ' (Set.Icc 0 u) :=
          traj_deck (↑γ) (q.automorphy (↑γ) γ.2) hσu
        have hσ'a : σ' a ∈ K' := by
          refine ⟨γ • ⟨σ a, hreg a haI⟩, hγK, ?_⟩
          exact coe_smul_moebius γ ⟨σ a, hreg a haI⟩
        have him : 0 < (σ' u).im := moebiusMap_im_pos _ (hreg u hu)
        have him' : 0 < (σ' a).im := moebiusMap_im_pos _ (hreg a haI)
        have hd1 := hstep σ' u a u hσ' ha0 hau (le_refl u) hspan hσ'a u
          (Set.right_mem_Icc.mpr hau) him him'
        have hlift : (⟨σ' u, him⟩ : UpperHalfPlane)
            = (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ⟨σ u, hreg u hu⟩ :=
          UpperHalfPlane.ext (coe_smul_eq_moebiusMap (↑γ) ⟨σ u, hreg u hu⟩).symm
        have hlift' : (⟨σ' a, him'⟩ : UpperHalfPlane)
            = (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ⟨σ a, hreg a haI⟩ :=
          UpperHalfPlane.ext (coe_smul_eq_moebiusMap (↑γ) ⟨σ a, hreg a haI⟩).symm
        rw [hlift, hlift'] at hd1
        have hd2 : dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane)
            (⟨σ a, hreg a haI⟩ : UpperHalfPlane) ≤ 1 := by
          rwa [dist_smul] at hd1
        calc dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane) τ₀
            ≤ dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane)
                (⟨σ a, hreg a haI⟩ : UpperHalfPlane)
              + dist (⟨σ a, hreg a haI⟩ : UpperHalfPlane) τ₀ := dist_triangle _ _ _
          _ ≤ 1 + k := add_le_add hd2 (ih a haI (le_of_eq hadef))
          _ = (k + 1 : ℕ) := by push_cast; ring
  set N : ℕ := Nat.ceil (c / (η / 2)) with hNdef
  refine ⟨(fun τ : UpperHalfPlane => (τ : ℂ)) '' Metric.closedBall τ₀ N,
    (isCompact_closedBall τ₀ N).image UpperHalfPlane.continuous_coe, ?_, ?_⟩
  · rintro x ⟨τ, -, rfl⟩
    exact τ.2
  · intro u hu
    have hle : u ≤ N * (η / 2) := by
      have h1 : c / (η / 2) ≤ N := Nat.le_ceil _
      have h2 : c ≤ N * (η / 2) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < η / 2)] at h1
        linarith
      linarith [hu.2]
    exact ⟨⟨σ u, hreg u hu⟩, Metric.mem_closedBall.mpr (key N u hu hle), rfl⟩

/-- **Dying trajectories approach the zeros**: a trajectory on a maximal finite window
that does not close at its endpoint enters every neighborhood of the zero set. -/
theorem dying_near_zero {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hσ : IsTrajOn q σ (Set.Ico 0 c))
    (hmax : ¬∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Ico 0 c) ∧
      IsTrajOn q σ' (Set.Icc 0 c)) :
    ∀ ρ, 0 < ρ → ∃ u ∈ Set.Ico 0 c, ∃ z₀ : ℂ,
      0 < z₀.im ∧ q z₀ = 0 ∧ ‖σ u - z₀‖ < ρ := by
  intro ρ hρ
  by_contra hcon
  push Not at hcon
  obtain ⟨L, hLc, hLH, hLtrack⟩ := traj_track_compact_Ico hΓ hcc q hq0 hc hσ
  set Z : Set ℂ := {z ∈ L | q z = 0} with hZdef
  have hZfin : Set.Finite Z := zeros_finite q.holo hq0 hLc hLH
  set L' : Set ℂ := L \ ⋃ z₀ ∈ Z, Metric.ball z₀ ρ with hL'def
  have hL'c : IsCompact L' := by
    refine hLc.of_isClosed_subset (hLc.isClosed.sdiff ?_) Set.diff_subset
    exact isOpen_biUnion fun z₀ _ => Metric.isOpen_ball
  have hL'H : L' ⊆ {z : ℂ | 0 < z.im} := Set.diff_subset.trans hLH
  have htrack' : ∀ u ∈ Set.Ico 0 c, σ u ∈ L' := by
    intro u hu
    refine ⟨hLtrack u hu, ?_⟩
    intro hmem
    obtain ⟨z₀, hz₀Z, hz₀ball⟩ := Set.mem_iUnion₂.mp hmem
    have hz₀L : z₀ ∈ L := hz₀Z.1
    have h1 : ρ ≤ ‖σ u - z₀‖ := hcon u hu z₀ (hLH hz₀L) hz₀Z.2
    have h2 : ‖σ u - z₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hz₀ball
    linarith
  have hL'ne : ∀ w ∈ L', q w ≠ 0 := by
    intro w hw hw0
    have hwZ : w ∈ Z := ⟨hw.1, hw0⟩
    exact hw.2 (Set.mem_iUnion₂.mpr ⟨w, hwZ, Metric.mem_ball_self hρ⟩)
  have hL'nonempty : L'.Nonempty := ⟨σ 0, htrack' 0 ⟨le_refl 0, hc⟩⟩
  have hqcont : ContinuousOn (fun w => ‖q w‖) L' :=
    (q.continuousOn_upper.mono hL'H).norm
  obtain ⟨w₀, hw₀L', hw₀min⟩ := hL'c.exists_isMinOn hL'nonempty hqcont
  have hm : 0 < ‖q w₀‖ := norm_pos_iff.mpr (hL'ne w₀ hw₀L')
  have hbound : ∀ u ∈ Set.Ico 0 c, ‖q w₀‖ ≤ ‖q (σ u)‖ := fun u hu =>
    hw₀min (htrack' u hu)
  obtain ⟨w, hlim⟩ := traj_limit hc hσ hm hbound
  haveI hne : (nhdsWithin c (Set.Ico 0 c)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico hc.ne]
    exact ⟨hc.le, le_refl c⟩
  have hwL' : w ∈ L' := hL'c.isClosed.mem_of_tendsto hlim
    (eventually_mem_nhdsWithin.mono fun u hu => htrack' u hu)
  obtain ⟨σ', hE', hσ'c, hT'⟩ := traj_close q.holo hc hσ (hL'H hwL')
    (hL'ne w hwL') hlim
  exact hmax ⟨σ', hE', hT'⟩

/-- **Arrival uniqueness**: two trajectories reaching the same endpoint with the same
chart slope there have the same start — arrivals at a point carry at most two starts,
one per orientation. -/
theorem arrival_unique {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦinj : Set.InjOn Φ S)
    {σ₁ σ₂ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h₁ : IsTrajOn q σ₁ (Set.Icc 0 a)) (h₂ : IsTrajOn q σ₂ (Set.Icc 0 a))
    (hend : σ₁ a = σ₂ a) (hyS : σ₁ a ∈ S) {s : ℝ}
    (hs₁ : SlopeAt Φ σ₁ (Set.Icc 0 a) a s) (hs₂ : SlopeAt Φ σ₂ (Set.Icc 0 a) a s) :
    σ₁ 0 = σ₂ 0 := by
  have hamem : a ∈ Set.Icc 0 a := Set.right_mem_Icc.mpr ha
  have hσ₁S : ∀ᶠ u in nhdsWithin a (Set.Icc 0 a), σ₁ u ∈ S :=
    (h₁.cont a hamem) (hS.mem_nhds hyS)
  have hσ₂S : ∀ᶠ u in nhdsWithin a (Set.Icc 0 a), σ₂ u ∈ S := by
    refine (h₂.cont a hamem) ?_
    rw [← hend] at *
    exact hS.mem_nhds hyS
  have hgerm : ∀ᶠ u in nhdsWithin a (Set.Icc 0 a), σ₁ u = σ₂ u := by
    filter_upwards [hs₁, hs₂, hσ₁S, hσ₂S] with u e₁ e₂ m₁ m₂
    refine hΦinj m₁ m₂ ?_
    rw [e₁, e₂, hend]
  -- reversed trajectories with germ at zero
  set σ₁' : ℝ → ℂ := fun u => σ₁ (a - u) with hσ₁'def
  set σ₂' : ℝ → ℂ := fun u => σ₂ (a - u) with hσ₂'def
  have hrev : ∀ σ : ℝ → ℂ, IsTrajOn q σ (Set.Icc 0 a) →
      IsTrajOn q (fun u => σ (a - u)) (Set.Icc 0 a) := by
    intro σ hσ
    have h1 := traj_reverse (traj_shift a hσ)
    have hset : (fun u : ℝ => -u) ⁻¹' ((fun u : ℝ => u + a) ⁻¹' Set.Icc 0 a)
        = Set.Icc 0 a := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor
      · rintro ⟨hh1, hh2⟩
        constructor <;> linarith
      · rintro ⟨hh1, hh2⟩
        constructor <;> linarith
    rw [hset] at h1
    have hfun : (fun u : ℝ => (fun v : ℝ => σ (v + a)) (-u)) = fun u => σ (a - u) := by
      funext u
      change σ (-u + a) = σ (a - u)
      rw [neg_add_eq_sub]
    rwa [hfun] at h1
  have hmap : Filter.Tendsto (fun u : ℝ => a - u)
      (nhdsWithin 0 (Set.Icc 0 a)) (nhdsWithin a (Set.Icc 0 a)) := by
    refine Filter.Tendsto.inf ?_ ?_
    · have h : Continuous fun u : ℝ => a - u := continuous_const.sub continuous_id
      have h2 := h.tendsto (0 : ℝ)
      simpa using h2
    · refine Filter.tendsto_principal_principal.mpr fun u hu => ?_
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hgerm' : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 a), σ₁' u = σ₂' u :=
    hmap.eventually hgerm
  have hEq := traj_unique ha (hrev σ₁ h₁) (hrev σ₂ h₂) hgerm'
  have := hEq (Set.right_mem_Icc.mpr ha)
  simpa [hσ₁'def, hσ₂'def] using this

/-- **Measurable single-step change of variables**: a legal chart move sends measurable
pieces to measurable pieces of equal `|q|` mass. -/
theorem step_cov {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hne : ∀ w ∈ S, q w ≠ 0) (hsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {P : Set ℂ} (hP : MeasurableSet P) (hPS : P ⊆ S) {t : ℝ}
    (hmove : ∀ w ∈ P, Φ w + (t : ℂ) ∈ Φ '' S) :
    MeasurableSet (localFlow Φ S t '' P) ∧
      ∫⁻ w in localFlow Φ S t '' P, ‖q w‖ₑ = ∫⁻ w in P, ‖q w‖ₑ := by
  have himgopen : IsOpen (Φ '' S) := chart_image_open hS hΦd hne hsq
  have hΦP : MeasurableSet (Φ '' P) :=
    hP.image_of_continuousOn_injOn ((hΦd.continuousOn).mono hPS) (hΦinj.mono hPS)
  have htrans : MeasurableSet ((fun ζ : ℂ => ζ + (t : ℂ)) '' (Φ '' P)) := by
    have hpre : (fun ζ : ℂ => ζ + (t : ℂ)) '' (Φ '' P)
        = (fun ζ : ℂ => ζ - (t : ℂ)) ⁻¹' (Φ '' P) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨y - (t : ℂ), hy, by ring⟩
    rw [hpre]
    exact hΦP.preimage (measurable_id.sub measurable_const)
  have hinv_pre : ∀ U : Set ℂ,
      (Function.invFunOn Φ S) ⁻¹' U ∩ (Φ '' S) = Φ '' (U ∩ S) := by
    intro U
    ext b
    constructor
    · rintro ⟨hbU, a, haS, rfl⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, haS, rfl⟩
      have hval : Function.invFunOn Φ S (Φ a) = a :=
        hΦinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
      refine ⟨a, ⟨?_, haS⟩, rfl⟩
      rwa [Set.mem_preimage, hval] at hbU
    · rintro ⟨a, ⟨haU, haS⟩, rfl⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, haS, rfl⟩
      have hval : Function.invFunOn Φ S (Φ a) = a :=
        hΦinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
      exact ⟨by rw [Set.mem_preimage, hval]; exact haU, ⟨a, haS, rfl⟩⟩
  have hinvcont : ContinuousOn (Function.invFunOn Φ S) (Φ '' S) := by
    rw [continuousOn_iff']
    intro U hU
    refine ⟨Φ '' (U ∩ S), chart_image_open (hU.inter hS)
      (hΦd.mono Set.inter_subset_right) (fun w hw => hne w hw.2)
      (fun w hw => hsq w hw.2), ?_⟩
    rw [hinv_pre U]
    exact (Set.inter_eq_self_of_subset_left
      (Set.image_mono Set.inter_subset_right)).symm
  have hinvinj : Set.InjOn (Function.invFunOn Φ S) (Φ '' S) := by
    rintro b₁ ⟨a₁, ha₁, rfl⟩ b₂ ⟨a₂, ha₂, rfl⟩ heq
    have hex₁ : ∃ x ∈ S, Φ x = Φ a₁ := ⟨a₁, ha₁, rfl⟩
    have hex₂ : ∃ x ∈ S, Φ x = Φ a₂ := ⟨a₂, ha₂, rfl⟩
    rw [hΦinj (Function.invFunOn_mem hex₁) ha₁ (Function.invFunOn_eq hex₁),
      hΦinj (Function.invFunOn_mem hex₂) ha₂ (Function.invFunOn_eq hex₂)] at heq
    rw [heq]
  have hdecomp : localFlow Φ S t '' P
      = Function.invFunOn Φ S '' ((fun ζ : ℂ => ζ + (t : ℂ)) '' (Φ '' P)) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Φ w + t, ⟨Φ w, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨x, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  have hsub : (fun ζ : ℂ => ζ + (t : ℂ)) '' (Φ '' P) ⊆ Φ '' S := by
    rintro b ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact hmove w hw
  have hBmeas : MeasurableSet (localFlow Φ S t '' P) := by
    rw [hdecomp]
    exact htrans.image_of_continuousOn_injOn (hinvcont.mono hsub) (hinvinj.mono hsub)
  exact ⟨hBmeas, chart_flow_lintegral hS hΦd hΦinj hsq hP hPS hmove hBmeas⟩

/-- The stepper position after `k` moves of size `h` from unit sign. -/
noncomputable def pos {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ((A.step2)^[k] (h, z, 1)).2.1

/-- The stepper sign after `k` moves of size `h` from unit sign. -/
noncomputable def sgn {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (k : ℕ) (z : ℂ) : ℝ :=
  ((A.step2)^[k] (h, z, 1)).2.2

/-- The iterated stepper position is measurable. -/
theorem measurable_pos {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (k : ℕ) :
    Measurable (pos A h k) := by
  have h1 : Measurable (fun z : ℂ => (h, z, (1 : ℝ))) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have h2 : Measurable (fun z : ℂ => (A.step2)^[k] (h, z, 1)) :=
    (A.measurable_step2.iterate k).comp h1
  exact measurable_fst.comp (measurable_snd.comp h2)

/-- The iterated stepper sign is measurable. -/
theorem measurable_sgn {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (k : ℕ) :
    Measurable (sgn A h k) := by
  have h1 : Measurable (fun z : ℂ => (h, z, (1 : ℝ))) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have h2 : Measurable (fun z : ℂ => (A.step2)^[k] (h, z, 1)) :=
    (A.measurable_step2.iterate k).comp h1
  exact measurable_snd.comp (measurable_snd.comp h2)

/-- The stepper preserves the time increment in its first component. -/
theorem step2_fst {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (k : ℕ) (z : ℂ) :
    ((A.step2)^[k] (h, z, 1)).1 = h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih

/-- The stepper position recursion through the chart-translation flow. -/
theorem pos_succ {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (k : ℕ) (z : ℂ) :
    pos A h (k + 1) z
      = Function.invFunOn (A.Φ (A.sel (pos A h k z)))
        (Metric.ball (A.c (A.sel (pos A h k z)))
          (2 * A.r (A.sel (pos A h k z))))
        (A.mchart (A.sel (pos A h k z)) (pos A h k z)
          + ((sgn A h k z * ((A.step2)^[k] (h, z, 1)).1 : ℝ) : ℂ)) := by
  rw [pos, Function.iterate_succ_apply']
  rfl

/-- The stepper position at step zero is the start point. -/
theorem pos_zero {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (z : ℂ) :
    pos A h 0 z = z := rfl

/-- **The itinerary chain change of variables**: on a measurable piece with constant
legal itinerary, the iterated stepper transports measurably and preserves `|q|` mass. -/
theorem chain_cov {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} {N : ℕ}
    {E : Set ℂ} (hE : MeasurableSet E) (c : ℕ → ℕ) (ε : ℕ → ℝ)
    (hleg : ∀ k, k ≤ N → ∀ z ∈ E,
      A.sel (pos A h k z) = c k ∧
      sgn A h k z = ε k ∧
      A.active (c k) ∧
      pos A h k z ∈ Metric.ball (A.c (c k)) (A.r (c k)) ∧
      A.Φ (c k) (pos A h k z) + ((ε k * h : ℝ) : ℂ)
        ∈ A.Φ (c k) '' Metric.ball (A.c (c k)) (2 * A.r (c k))) :
    ∀ k, k ≤ N + 1 → MeasurableSet (pos A h k '' E) ∧
      ∫⁻ w in pos A h k '' E, ‖q w‖ₑ = ∫⁻ w in E, ‖q w‖ₑ := by
  rcases Set.eq_empty_or_nonempty E with hemp | ⟨z₀, hz₀⟩
  · intro k _
    subst hemp
    simp
  intro k
  induction k with
  | zero =>
    intro _
    rw [show pos A h 0 '' E = E from by
      rw [show pos A h 0 = id from funext fun z => pos_zero A h z,
        Set.image_id]]
    exact ⟨hE, rfl⟩
  | succ k ih =>
    intro hk1
    have hk : k ≤ N := by omega
    obtain ⟨ihm, ihe⟩ := ih (by omega)
    have hact : A.active (c k) := (hleg k hk z₀ hz₀).2.2.1
    have himg : pos A h (k + 1) '' E
        = localFlow (A.Φ (c k)) (Metric.ball (A.c (c k)) (2 * A.r (c k)))
            (ε k * h) '' (pos A h k '' E) := by
      rw [← Set.image_comp]
      refine Set.image_congr fun z hz => ?_
      obtain ⟨hsel, hsgn, -, hmem, -⟩ := hleg k hk z hz
      rw [pos_succ, step2_fst, hsel, hsgn]
      change Function.invFunOn (A.Φ (c k))
          (Metric.ball (A.c (c k)) (2 * A.r (c k)))
          (A.mchart (c k) (pos A h k z) + ((ε k * h : ℝ) : ℂ))
        = Function.invFunOn (A.Φ (c k))
          (Metric.ball (A.c (c k)) (2 * A.r (c k)))
          (A.Φ (c k) (pos A h k z) + ((ε k * h : ℝ) : ℂ))
      rw [A.mchart_eq hact
        (Metric.ball_subset_ball (by linarith [A.hr _ hact]) hmem)]
    have hPS : pos A h k '' E
        ⊆ Metric.ball (A.c (c k)) (2 * A.r (c k)) := by
      rintro w ⟨z, hz, rfl⟩
      exact Metric.ball_subset_ball (by linarith [A.hr _ hact])
        (hleg k hk z hz).2.2.2.1
    have hmove : ∀ w ∈ pos A h k '' E,
        A.Φ (c k) w + ((ε k * h : ℝ) : ℂ)
          ∈ A.Φ (c k) '' Metric.ball (A.c (c k)) (2 * A.r (c k)) := by
      rintro w ⟨z, hz, rfl⟩
      exact (hleg k hk z hz).2.2.2.2
    obtain ⟨hm, he⟩ := step_cov Metric.isOpen_ball (A.hd _ hact)
      (A.hinj _ hact) (A.hne _ hact) (A.hsq _ hact) ihm hPS hmove
    rw [himg]
    exact ⟨hm, he.trans ihe⟩

/-- A pointwise indicator sum over a family hitting each point through at most two
indices is bounded by two. -/
theorem tsum_indicator_pair {ι : Type*} [Countable ι] {A : ι → Set ℂ} {x : ℂ}
    {i₁ i₂ : ι} (hpair : ∀ i, x ∈ A i → i = i₁ ∨ i = i₂) :
    (∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ 2 := by
  classical
  have hle : ∀ i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x
      ≤ (if i = i₁ then (1 : ℝ≥0∞) else 0) + (if i = i₂ then (1 : ℝ≥0∞) else 0) := by
    intro i
    by_cases hx : x ∈ A i
    · rcases hpair i hx with h | h
      · rw [Set.indicator_of_mem hx, if_pos h]
        exact le_add_right (le_refl 1)
      · rw [Set.indicator_of_mem hx, if_pos h]
        exact le_add_left (le_refl 1)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le _
  calc (∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x)
      ≤ ∑' i, ((if i = i₁ then (1 : ℝ≥0∞) else 0)
          + (if i = i₂ then (1 : ℝ≥0∞) else 0)) := ENNReal.tsum_le_tsum hle
    _ = (∑' i, (if i = i₁ then (1 : ℝ≥0∞) else 0))
          + ∑' i, (if i = i₂ then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_add
    _ ≤ 1 + 1 := by
        refine add_le_add ?_ ?_ <;>
          · rw [tsum_eq_single _ (fun b hb => if_neg hb)]
            split_ifs <;> simp
    _ = 2 := by norm_num

/-- Countably-indexed bounded-multiplicity summation over an arbitrary countable index
type. -/
theorem lintegral_mult_le' {ι : Type*} [Countable ι] {A : ι → Set ℂ}
    (hA : ∀ i, MeasurableSet (A i)) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hmult : ∀ x : ℂ, (∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ 2) :
    (∑' i, ∫⁻ x in A i, f x) ≤ 2 * ∫⁻ x in ⋃ i, A i, f x := by
  have h1 : ∀ i, ∫⁻ x in A i, f x = ∫⁻ x, (A i).indicator f x := fun i =>
    (lintegral_indicator (hA i) f).symm
  have h2 : (∑' i, ∫⁻ x in A i, f x) = ∫⁻ x, ∑' i, (A i).indicator f x := by
    rw [tsum_congr h1]
    exact (lintegral_tsum fun i => (hf.indicator (hA i)).aemeasurable).symm
  rw [h2]
  have h3 : ∀ x, (∑' i, (A i).indicator f x)
      ≤ (⋃ i, A i).indicator (fun y => 2 * f y) x := by
    intro x
    by_cases hx : x ∈ ⋃ i, A i
    · rw [Set.indicator_of_mem hx]
      have hpt : ∀ i, (A i).indicator f x
          = f x * (A i).indicator (fun _ => (1 : ℝ≥0∞)) x := by
        intro i
        by_cases hxi : x ∈ A i
        · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem hxi, mul_one]
        · rw [Set.indicator_of_notMem hxi, Set.indicator_of_notMem hxi, mul_zero]
      rw [tsum_congr hpt, ENNReal.tsum_mul_left]
      calc f x * ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x
          ≤ f x * 2 := mul_le_mul_right (hmult x) _
        _ = 2 * f x := by ring
    · have hzero : ∀ i, (A i).indicator f x = 0 := fun i =>
        Set.indicator_of_notMem (fun hxi => hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)) f
      rw [tsum_congr hzero]
      simp [Set.indicator_of_notMem hx]
  calc ∫⁻ x, ∑' i, (A i).indicator f x
      ≤ ∫⁻ x, (⋃ i, A i).indicator (fun y => 2 * f y) x := lintegral_mono h3
    _ = ∫⁻ x in ⋃ i, A i, 2 * f x :=
        lintegral_indicator (MeasurableSet.iUnion hA) _
    _ = 2 * ∫⁻ x in ⋃ i, A i, f x := lintegral_const_mul 2 hf

/-- The `N`-legal set of the stepper: each step up to `N` selects an active chart with
the position in its unit ball, carries a unit sign, and moves legally in the chart. -/
def legal {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (N : ℕ) : Set ℂ :=
  {z | ∀ k, k ≤ N → A.active (A.sel (pos A h k z)) ∧
    pos A h k z ∈ Metric.ball (A.c (A.sel (pos A h k z)))
      (A.r (A.sel (pos A h k z))) ∧
    (sgn A h k z = 1 ∨ sgn A h k z = -1) ∧
    A.Φ (A.sel (pos A h k z)) (pos A h k z)
        + ((sgn A h k z * h : ℝ) : ℂ)
      ∈ A.Φ (A.sel (pos A h k z)) ''
        Metric.ball (A.c (A.sel (pos A h k z)))
          (2 * A.r (A.sel (pos A h k z)))}

/-- The itinerary itinPiece of a set: the members realizing a prescribed selector-and-sign
sequence. -/
def itinPiece {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (N : ℕ) (E : Set ℂ)
    (c : Fin (N + 1) → ℕ × Bool) : Set ℂ :=
  {z ∈ E | ∀ k : Fin (N + 1), A.sel (pos A h (k : ℕ) z) = (c k).1 ∧
    sgn A h (k : ℕ) z = (if (c k).2 then (1 : ℝ) else -1)}

/-- Each itinerary piece is a measurable set. -/
theorem piece_measurable {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (N : ℕ)
    {E : Set ℂ} (hE : MeasurableSet E) (c : Fin (N + 1) → ℕ × Bool) :
    MeasurableSet (itinPiece A h N E c) := by
  have hset : itinPiece A h N E c = E ∩ ⋂ k : Fin (N + 1),
      ((pos A h (k : ℕ)) ⁻¹' (A.sel ⁻¹' {(c k).1})
        ∩ (sgn A h (k : ℕ)) ⁻¹' {(if (c k).2 then (1 : ℝ) else -1)}) := by
    ext z
    simp only [itinPiece, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
  rw [hset]
  refine hE.inter (MeasurableSet.iInter fun k => ?_)
  exact ((A.measurable_sel.comp (measurable_pos A h k))
      (measurableSet_singleton _)).inter
    ((measurable_sgn A h k) (measurableSet_singleton _))

open Classical in
/-- The canonical itinerary of a point. -/
noncomputable def itin {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (N : ℕ) (z : ℂ) :
    Fin (N + 1) → ℕ × Bool := fun k =>
  (A.sel (pos A h (k : ℕ) z), if sgn A h (k : ℕ) z = 1 then true else false)

/-- Membership in a itinPiece pins the itinerary. -/
theorem itin_eq {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} {N : ℕ} {E : Set ℂ}
    (hEL : E ⊆ legal A h N) {c : Fin (N + 1) → ℕ × Bool} {z : ℂ}
    (hz : z ∈ itinPiece A h N E c) : c = itin A h N z := by
  classical
  funext k
  obtain ⟨hzE, hcl⟩ := hz
  obtain ⟨hsel, hsgn⟩ := hcl k
  have hpm : (sgn A h (k : ℕ) z = 1 ∨ sgn A h (k : ℕ) z = -1) :=
    ((hEL hzE) (k : ℕ) (by omega)).2.2.1
  refine Prod.ext hsel.symm ?_
  change (c k).2 = (if sgn A h (k : ℕ) z = 1 then true else false)
  cases hcb : (c k).2
  · simp only [hcb, Bool.false_eq_true, if_false] at hsgn
    rw [if_neg (by rw [hsgn]; norm_num)]
  · simp only [hcb, if_true] at hsgn
    rw [if_pos hsgn]

/-- **The segment trajectory of a legal move**: if the developed segment of one signed
step stays in the developed chart image, the local translation flow is a vertical
trajectory with that chart slope. -/
theorem seg_traj {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ w ∈ S, q w ≠ 0)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {z : ℂ} (hz : z ∈ S) {sgn h : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) (_hh : 0 < h)
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) h, Φ z + ((sgn * u : ℝ) : ℂ) ∈ Φ '' S) :
    (fun u => localFlow Φ S (sgn * u) z) 0 = z ∧
    IsTrajOn q (fun u => localFlow Φ S (sgn * u) z) (Set.Icc 0 h) ∧
    SlopeAt Φ (fun u => localFlow Φ S (sgn * u) z) (Set.Icc 0 h) 0 sgn := by
  have hder : ∀ w ∈ S, deriv Φ w ≠ 0 := by
    intro w hw h0
    apply hSne w hw
    have := hΦsq w hw
    rw [h0] at this
    simpa using this.symm
  set σ : ℝ → ℂ := fun u => localFlow Φ S (sgn * u) z with hσdef
  have hσdev : ∀ u ∈ Set.Icc (0 : ℝ) h, Φ (σ u) = Φ z + ((sgn * u : ℝ) : ℂ) :=
    fun u hu => localFlow_dev (hseg u hu)
  have hσS : ∀ u ∈ Set.Icc (0 : ℝ) h, σ u ∈ S := fun u hu =>
    localFlow_mem (hseg u hu)
  have hσ0 : σ 0 = z := by
    rw [hσdef]
    simp only [mul_zero]
    exact localFlow_zero hΦinj hz
  have hσcont : ContinuousOn σ (Set.Icc 0 h) := by
    intro u hu
    have hd := localFlow_hasDerivAt hS hΦd hΦinj (hseg u hu)
      (hder _ (hσS u hu))
    have hcont : ContinuousAt (fun t : ℝ => localFlow Φ S t z) (sgn * u) :=
      hd.continuousAt
    have hmul : ContinuousAt (fun u : ℝ => sgn * u) u :=
      (continuous_const.mul continuous_id).continuousAt
    exact (hcont.comp hmul).continuousWithinAt
  refine ⟨hσ0, ⟨hσcont, ?_⟩, ?_⟩
  · intro t ht
    have hsne : (sgn : ℂ) ≠ 0 := by
      rcases hsgn with h1 | h1 <;> rw [h1] <;> norm_num
    have hs2 : ((sgn : ℝ) : ℂ) ^ 2 = 1 := by
      rcases hsgn with h1 | h1 <;> rw [h1] <;> norm_num
    refine ⟨S, hS, hσS t ht, hSH, hSne, fun w => ((sgn : ℝ) : ℂ) * Φ w,
      fun w hw => ((hΦd w hw).const_mul _), ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hΦinj hx hy (mul_left_cancel₀ hsne hxy)
    · intro w hw
      have hdiff : DifferentiableAt ℂ Φ w := hΦd.differentiableAt (hS.mem_nhds hw)
      rw [deriv_const_mul _ hdiff, mul_pow, hs2, one_mul]
      exact hΦsq w hw
    · filter_upwards [eventually_mem_nhdsWithin] with u hu
      refine ⟨hσS u hu, ?_⟩
      show ((sgn : ℝ) : ℂ) * Φ (σ u) = ((sgn : ℝ) : ℂ) * Φ (σ t) + _
      rw [hσdev u hu, hσdev t ht]
      push_cast
      rcases hsgn with h1 | h1 <;> rw [h1] <;> push_cast <;> ring
  · change ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h), Φ (σ u) = Φ (σ 0) + sgn * ((u - 0 : ℝ) : ℂ)
    filter_upwards [eventually_mem_nhdsWithin] with u hu
    rw [hσdev u hu, hσ0]
    push_cast
    ring

/-- The rational parameter grid of a closed segment. -/
def ratGrid (h : ℝ) : Set ℚ := {u : ℚ | 0 ≤ (u : ℝ) ∧ (u : ℝ) ≤ h}

/-- **Lower bound direction**: a segment inside an open set keeps a positive distance
floor at all rational parameters. -/
theorem seg_inf_pos {O : Set ℂ} (hO : IsOpen O) {p : ℝ → ℂ}
    (hp : Continuous p) {h : ℝ}
    (hin : ∀ u ∈ Set.Icc (0 : ℝ) h, p u ∈ O) :
    0 < ⨅ u : ratGrid h, Metric.infEDist (p (u : ℚ)) Oᶜ := by
  have hcomp : IsCompact (p '' Set.Icc 0 h) := isCompact_Icc.image hp
  have hsubO : p '' Set.Icc 0 h ⊆ O := by
    rintro w ⟨u, hu, rfl⟩
    exact hin u hu
  obtain ⟨ε, hε, hthick⟩ := hcomp.exists_thickening_subset_open hO hsubO
  have hlb : ∀ u : ratGrid h,
      ENNReal.ofReal ε ≤ Metric.infEDist (p ((u : ℚ) : ℝ)) Oᶜ := by
    intro u
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hyO, hyd⟩ := Metric.infEDist_lt_iff.mp hlt
    have hpK : p ((u : ℚ) : ℝ) ∈ p '' Set.Icc 0 h :=
      ⟨((u : ℚ) : ℝ), ⟨u.2.1, u.2.2⟩, rfl⟩
    have hymem : y ∈ Metric.thickening ε (p '' Set.Icc 0 h) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨p ((u : ℚ) : ℝ), hpK, ?_⟩
      rw [dist_comm]
      exact edist_lt_ofReal.mp hyd
    exact hyO (hthick hymem)
  calc (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    _ ≤ ⨅ u : ratGrid h, Metric.infEDist (p ((u : ℚ) : ℝ)) Oᶜ := le_iInf hlb

/-- **Upper bound direction**: a positive rational distance floor keeps the whole
segment inside the open set. -/
theorem seg_inf_mem {O : Set ℂ} {g : ℂ} {s : ℝ} {h : ℝ} (hh : 0 < h)
    (hpos : 0 < ⨅ u : ratGrid h,
      Metric.infEDist (g + ((s * ((u : ℚ) : ℝ) : ℝ) : ℂ)) Oᶜ)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) h) : g + ((s * u : ℝ) : ℂ) ∈ O := by
  by_contra hout
  have hzero : Metric.infEDist (g + ((s * u : ℝ) : ℂ)) Oᶜ = 0 :=
    Metric.infEDist_zero_of_mem hout
  set c : ℝ≥0∞ := min (⨅ v : ratGrid h,
    Metric.infEDist (g + ((s * ((v : ℚ) : ℝ) : ℝ) : ℂ)) Oᶜ) 1 with hcdef
  have hc0 : 0 < c := lt_min hpos one_pos
  have hcne : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hctr : 0 < c.toReal := ENNReal.toReal_pos hc0.ne' hcne
  set δ : ℝ := c.toReal / (2 * (|s| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  -- a rational parameter within δ of u inside the grid
  have hrat : ∃ v : ratGrid h, |((v : ℚ) : ℝ) - u| < δ := by
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · refine ⟨⟨0, by norm_num, by norm_num; linarith⟩, ?_⟩
      rw [← h0]
      simpa using hδ
    · obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn (show max 0 (u - δ) < u from
        max_lt h0 (by linarith))
      have hv0 : (0 : ℝ) ≤ (v : ℝ) := le_trans (le_max_left _ _) hv1.le
      have hvh : ((v : ℝ) : ℝ) ≤ h := le_trans hv2.le hu.2
      refine ⟨⟨v, hv0, hvh⟩, ?_⟩
      have := le_max_right 0 (u - δ)
      rw [abs_sub_lt_iff]
      constructor <;> linarith [hv1, hv2]
  obtain ⟨v, hv⟩ := hrat
  have htri : (⨅ w : ratGrid h,
        Metric.infEDist (g + ((s * ((w : ℚ) : ℝ) : ℝ) : ℂ)) Oᶜ)
      ≤ ENNReal.ofReal (|s| * δ) := by
    refine le_trans (iInf_le _ v) ?_
    calc Metric.infEDist (g + ((s * ((v : ℚ) : ℝ) : ℝ) : ℂ)) Oᶜ
        ≤ Metric.infEDist (g + ((s * u : ℝ) : ℂ)) Oᶜ
          + edist (g + ((s * ((v : ℚ) : ℝ) : ℝ) : ℂ)) (g + ((s * u : ℝ) : ℂ)) :=
          Metric.infEDist_le_infEDist_add_edist
      _ = edist (g + ((s * ((v : ℚ) : ℝ) : ℝ) : ℂ)) (g + ((s * u : ℝ) : ℂ)) := by
          rw [hzero, zero_add]
      _ ≤ ENNReal.ofReal (|s| * δ) := by
          rw [edist_dist, dist_eq_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          have hnorm : (g + ((s * ((v : ℚ) : ℝ) : ℝ) : ℂ)) - (g + ((s * u : ℝ) : ℂ))
              = (((s * ((v : ℚ) : ℝ) - s * u : ℝ)) : ℂ) := by
            push_cast
            ring
          rw [hnorm, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left hv.le (abs_nonneg s)
  have hfin : c ≤ ENNReal.ofReal (|s| * δ) := le_trans (min_le_left _ _) htri
  have hcontra : ENNReal.ofReal (|s| * δ) < c := by
    have h1 : |s| * δ < c.toReal := by
      rw [hδdef]
      rw [div_eq_mul_inv]
      have hpos1 : (0 : ℝ) < |s| + 1 := by positivity
      calc |s| * (c.toReal * (2 * (|s| + 1))⁻¹)
          ≤ (|s| + 1) * (c.toReal * (2 * (|s| + 1))⁻¹) := by
            refine mul_le_mul_of_nonneg_right (by linarith [abs_nonneg s]) ?_
            positivity
        _ = c.toReal / 2 := by
            field_simp
        _ < c.toReal := by linarith
    calc ENNReal.ofReal (|s| * δ) < ENNReal.ofReal c.toReal := by
          refine ENNReal.ofReal_lt_ofReal_iff ?_ |>.mpr h1
          exact hctr
      _ = c := ENNReal.ofReal_toReal hcne
  exact absurd hfin (not_le.mpr hcontra)

/-- **Segment-condition measurability**: staying in an open set along a measurable
family of developed segments is a measurable condition. -/
theorem seg_cond_measurable {O : Set ℂ} (hO : IsOpen O) {g : ℂ → ℂ} {s : ℂ → ℝ}
    (hg : Measurable g) (hs : Measurable s) {h : ℝ} (hh : 0 < h) :
    MeasurableSet {z : ℂ | ∀ u ∈ Set.Icc (0 : ℝ) h,
      g z + ((s z * u : ℝ) : ℂ) ∈ O} := by
  have hkey : {z : ℂ | ∀ u ∈ Set.Icc (0 : ℝ) h, g z + ((s z * u : ℝ) : ℂ) ∈ O}
      = {z : ℂ | 0 < ⨅ u : ratGrid h,
          Metric.infEDist (g z + ((s z * ((u : ℚ) : ℝ) : ℝ) : ℂ)) Oᶜ} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hz
      have hcont : Continuous fun u : ℝ => g z + ((s z * u : ℝ) : ℂ) :=
        continuous_const.add (Complex.continuous_ofReal.comp
          (continuous_const.mul continuous_id))
      exact seg_inf_pos hO hcont hz
    · intro hz u hu
      exact seg_inf_mem hh hz hu
  rw [hkey]
  refine measurableSet_lt measurable_const ?_
  refine Measurable.iInf fun u => ?_
  have hpt : Measurable fun z => g z + ((s z * ((u : ℚ) : ℝ) : ℝ) : ℂ) :=
    hg.add (Complex.measurable_ofReal.comp (hs.mul_const _))
  exact (Metric.continuous_infEDist).measurable.comp hpt

/-- The **strong-legal set**: every step up to `N` selects an active chart holding the
position in its unit ball, carries a unit sign, and its whole developed segment stays
in the developed chart image. -/
def slegal {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (N : ℕ) : Set ℂ :=
  {z | ∀ k, k ≤ N → A.active (A.sel (pos A h k z)) ∧
    pos A h k z ∈ Metric.ball (A.c (A.sel (pos A h k z)))
      (A.r (A.sel (pos A h k z))) ∧
    (sgn A h k z = 1 ∨ sgn A h k z = -1) ∧
    ∀ u ∈ Set.Icc (0 : ℝ) h,
      A.Φ (A.sel (pos A h k z)) (pos A h k z) + ((sgn A h k z * u : ℝ) : ℂ)
        ∈ A.Φ (A.sel (pos A h k z)) ''
          Metric.ball (A.c (A.sel (pos A h k z))) (2 * A.r (A.sel (pos A h k z)))}

/-- Measurability of the strong-legal set. -/
theorem slegal_measurable {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} (hh : 0 < h)
    (N : ℕ) : MeasurableSet (slegal A h N) := by
  classical
  have hset : slegal A h N = ⋂ k ∈ Set.Iic N, ⋃ j : ℕ,
      ((pos A h k) ⁻¹' (A.sel ⁻¹' {j})
        ∩ ({z | A.active j}
        ∩ ((pos A h k) ⁻¹' Metric.ball (A.c j) (A.r j)
        ∩ (((sgn A h k) ⁻¹' {1} ∪ (sgn A h k) ⁻¹' {-1})
        ∩ {z | ∀ u ∈ Set.Icc (0 : ℝ) h,
            A.mchart j (pos A h k z) + ((sgn A h k z * u : ℝ) : ℂ)
              ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)})))) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_Iic]
    constructor
    · intro hz k hk
      obtain ⟨hact, hball, hsgn, hseg⟩ := hz k hk
      refine ⟨A.sel (pos A h k z), rfl, hact, hball, hsgn, ?_⟩
      intro u hu
      have hmem2 : pos A h k z ∈ Metric.ball (A.c (A.sel (pos A h k z)))
          (2 * A.r (A.sel (pos A h k z))) :=
        Metric.ball_subset_ball (by linarith [A.hr _ hact]) hball
      rw [A.mchart_eq hact hmem2]
      exact hseg u hu
    · intro hz k hk
      obtain ⟨j, hsel, hact, hball, hsgn, hseg⟩ := hz k hk
      subst hsel
      refine ⟨hact, hball, hsgn, ?_⟩
      intro u hu
      have hmem2 : pos A h k z ∈ Metric.ball (A.c (A.sel (pos A h k z)))
          (2 * A.r (A.sel (pos A h k z))) :=
        Metric.ball_subset_ball (by linarith [A.hr _ hact]) hball
      have := hseg u hu
      rwa [A.mchart_eq hact hmem2] at this
  rw [hset]
  refine MeasurableSet.biInter ((Set.finite_Iic N).countable) fun k _ => ?_
  refine MeasurableSet.iUnion fun j => ?_
  refine ((A.measurable_sel.comp (measurable_pos A h k))
    (measurableSet_singleton j)).inter ?_
  refine MeasurableSet.inter ?_ ?_
  · by_cases hact : A.active j
    · have : {z : ℂ | A.active j} = Set.univ := by
        ext z
        simp [hact]
      rw [this]
      exact MeasurableSet.univ
    · have : {z : ℂ | A.active j} = ∅ := by
        ext z
        simp [hact]
      rw [this]
      exact MeasurableSet.empty
  refine MeasurableSet.inter ((measurable_pos A h k) measurableSet_ball) ?_
  refine MeasurableSet.inter (((measurable_sgn A h k) (measurableSet_singleton 1)).union
    ((measurable_sgn A h k) (measurableSet_singleton (-1)))) ?_
  by_cases hact : A.active j
  · exact seg_cond_measurable
      (chart_image_open Metric.isOpen_ball (A.hd j hact) (A.hne j hact) (A.hsq j hact))
      ((A.measurable_mchart j).comp (measurable_pos A h k)) (measurable_sgn A h k) hh
  · have hjunk : A.Φ j = id := A.hjunk j hact
    have hopen : IsOpen (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) := by
      rw [hjunk, Set.image_id]
      exact Metric.isOpen_ball
    exact seg_cond_measurable hopen
      ((A.measurable_mchart j).comp (measurable_pos A h k)) (measurable_sgn A h k) hh

/-- The stepper sign recursion. -/
theorem sgn_succ {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (k : ℕ) (z : ℂ) :
    sgn A h (k + 1) z
      = sgn A h k z * ((deriv (A.Φ (A.sel (pos A h (k + 1) z))) (pos A h (k + 1) z))
        * (deriv (A.Φ (A.sel (pos A h k z))) (pos A h (k + 1) z))⁻¹).re := by
  rw [sgn, Function.iterate_succ_apply']
  have hpos : (A.step2 ((A.step2)^[k] (h, z, 1))).2.1 = pos A h (k + 1) z := by
    rw [pos, Function.iterate_succ_apply']
  change ((A.step2)^[k] (h, z, 1)).2.2
      * ((deriv (A.Φ (A.sel (A.step2 ((A.step2)^[k] (h, z, 1))).2.1))
          ((A.step2 ((A.step2)^[k] (h, z, 1))).2.1))
        * (deriv (A.Φ (A.sel ((A.step2)^[k] (h, z, 1)).2.1))
          ((A.step2 ((A.step2)^[k] (h, z, 1))).2.1))⁻¹).re = _
  rw [hpos]
  rfl

/-- **The step unit**: the k-th strong-legal clause produces a segment trajectory from
the k-th position to the (k+1)-st, arriving with the updated sign as chart slope. -/
theorem slegal_step {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} (hh : 0 < h)
    {z : ℂ} {k : ℕ}
    (hact : A.active (A.sel (pos A h k z)))
    (hball : pos A h k z ∈ Metric.ball (A.c (A.sel (pos A h k z)))
      (A.r (A.sel (pos A h k z))))
    (hsgn : sgn A h k z = 1 ∨ sgn A h k z = -1)
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) h,
      A.Φ (A.sel (pos A h k z)) (pos A h k z) + ((sgn A h k z * u : ℝ) : ℂ)
        ∈ A.Φ (A.sel (pos A h k z)) ''
          Metric.ball (A.c (A.sel (pos A h k z)))
            (2 * A.r (A.sel (pos A h k z)))) :
    ∃ τ : ℝ → ℂ, τ 0 = pos A h k z ∧ IsTrajOn q τ (Set.Icc 0 h) ∧
      SlopeAt (A.Φ (A.sel (pos A h k z))) τ (Set.Icc 0 h) 0 (sgn A h k z) ∧
      τ h = pos A h (k + 1) z ∧
      (sgn A h (k + 1) z = 1 ∨ sgn A h (k + 1) z = -1) ∧
      SlopeAt (A.Φ (A.sel (pos A h (k + 1) z))) τ (Set.Icc 0 h) h
        (sgn A h (k + 1) z) := by
  set j : ℕ := A.sel (pos A h k z) with hjdef
  set x : ℂ := pos A h k z with hxdef
  set s : ℝ := sgn A h k z with hsdef
  set S : Set ℂ := Metric.ball (A.c j) (2 * A.r j) with hSdef
  have hxS : x ∈ S := Metric.ball_subset_ball (by linarith [A.hr j hact]) hball
  obtain ⟨hτ0, hτtraj, hτslope⟩ := seg_traj Metric.isOpen_ball (A.hd j hact)
    (A.hinj j hact) (A.hH j hact) (A.hne j hact) (A.hsq j hact) hxS hsgn hh hseg
  set τ : ℝ → ℂ := fun u => localFlow (A.Φ j) S (s * u) x with hτdef
  have hτh : τ h = pos A h (k + 1) z := by
    rw [pos_succ, step2_fst]
    change Function.invFunOn (A.Φ j) S (A.Φ j x + ((s * h : ℝ) : ℂ)) = _
    rw [← A.mchart_eq hact hxS]
  have hhmem : h ∈ Set.Icc (0 : ℝ) h := Set.right_mem_Icc.mpr hh.le
  have hτhS : τ h ∈ S := localFlow_mem (hseg h hhmem)
  have him' : 0 < (pos A h (k + 1) z).im := by
    rw [← hτh]
    exact A.hH j hact hτhS
  have hne' : q (pos A h (k + 1) z) ≠ 0 := by
    rw [← hτh]
    exact A.hne j hact _ hτhS
  obtain ⟨hact', hball'⟩ := A.sel_spec him' hne'
  set j' : ℕ := A.sel (pos A h (k + 1) z) with hj'def
  have hx'S : pos A h (k + 1) z ∈ S := hτh ▸ hτhS
  have hx'S' : pos A h (k + 1) z ∈ Metric.ball (A.c j') (2 * A.r j') :=
    Metric.ball_subset_ball (by linarith [A.hr j' hact']) hball'
  have haff : ∀ v ∈ Set.Icc (0 : ℝ) h,
      A.Φ j (τ v) = A.Φ j (τ 0) + s * ((v - 0 : ℝ) : ℂ) := by
    intro v hv
    have hdev : A.Φ j (τ v) = A.Φ j x + ((s * v : ℝ) : ℂ) :=
      localFlow_dev (hseg v hv)
    rw [hdev, hτ0]
    push_cast
    ring
  have hslope₁ : SlopeAt (A.Φ j) τ (Set.Icc 0 h) h s :=
    slope_transport Metric.isOpen_ball (A.hd j hact) (A.hsq j hact) hτtraj
      (le_refl 0) hh (le_refl h) hτhS haff
  obtain ⟨ε', hε'pm, hderiv', hrel'⟩ := chart_ratio (q := q) Metric.isOpen_ball
    Metric.isOpen_ball (A.hd j hact) (A.hd j' hact') (A.hsq j hact)
    (A.hsq j' hact') hx'S hx'S'
  have hdne : deriv (A.Φ j) (pos A h (k + 1) z) ≠ 0 := by
    intro h0
    apply hne'
    have hsq := A.hsq j hact _ hx'S
    rw [h0] at hsq
    simpa using hsq.symm
  have hratio : ((deriv (A.Φ j') (pos A h (k + 1) z))
      * (deriv (A.Φ j) (pos A h (k + 1) z))⁻¹).re = ε' := by
    rw [hderiv', mul_assoc, mul_inv_cancel₀ hdne, mul_one, Complex.ofReal_re]
  have hsucc : sgn A h (k + 1) z = s * ε' := by
    rw [sgn_succ, hratio]
  have hpm' : sgn A h (k + 1) z = 1 ∨ sgn A h (k + 1) z = -1 := by
    rw [hsucc]
    rcases hsgn with h1 | h1 <;> rcases hε'pm with h2 | h2 <;>
      rw [show s = sgn A h k z from rfl] at * <;> rw [h1, h2] <;> norm_num
  have hslope₂ : SlopeAt (A.Φ j') τ (Set.Icc 0 h) h (ε' * s) := by
    refine slope_ratio ((Metric.isOpen_ball.inter Metric.isOpen_ball).connectedComponentIn)
      hhmem (hτtraj.cont h hhmem) ?_ hrel' hslope₁
    rw [hτh]
    exact mem_connectedComponentIn ⟨hx'S, hx'S'⟩
  refine ⟨τ, hτ0, hτtraj, hτslope, hτh, hpm', ?_⟩
  rw [hsucc, mul_comm s ε']
  exact hslope₂

end RiemannDynamics

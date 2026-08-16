/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Flow.Trajectories

/-!
# The countable atlas of natural charts and the stepper

A countable atlas of natural charts covering the regular set, the measurable chart
selector, and the slope calculus by which a trajectory is followed from chart to chart.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- Restriction of a vertical trajectory to a smaller time set. -/
theorem traj_mono {q : ℂ → ℂ} {σ : ℝ → ℂ} {s s' : Set ℝ}
    (h : IsTrajOn q σ s) (hsub : s' ⊆ s) : IsTrajOn q σ s' := by
  constructor
  · exact h.cont.mono hsub
  · intro t ht
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := h.chart t (hsub ht)
    exact ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq,
      hev.filter_mono (nhdsWithin_mono t hsub)⟩

/-- Two trajectories sharing the seed coincide on the common time interval. -/
theorem traj_coherent {q : ℂ → ℂ} {σ₀ σ₁ σ₂ : ℝ → ℂ} {δ₀ b₁ b₂ : ℝ}
    (hδ₀ : 0 < δ₀) (hδb : δ₀ ≤ b₁) (hb : b₁ ≤ b₂)
    (h₁ : IsTrajOn q σ₁ (Set.Icc 0 b₁)) (h₂ : IsTrajOn q σ₂ (Set.Icc 0 b₂))
    (hE₁ : Set.EqOn σ₁ σ₀ (Set.Icc 0 δ₀)) (hE₂ : Set.EqOn σ₂ σ₀ (Set.Icc 0 δ₀)) :
    Set.EqOn σ₁ σ₂ (Set.Icc 0 b₁) := by
  have h0b : (0 : ℝ) ≤ b₁ := le_trans hδ₀.le hδb
  refine traj_unique h0b h₁ (traj_mono h₂ (Set.Icc_subset_Icc le_rfl hb)) ?_
  refine mem_nhdsWithin.mpr ⟨Set.Iio δ₀, isOpen_Iio, hδ₀, ?_⟩
  rintro u ⟨hu1, hu2⟩
  have huδ : u ∈ Set.Icc 0 δ₀ := ⟨hu2.1, le_of_lt hu1⟩
  change σ₁ u = σ₂ u
  rw [hE₁ huδ, hE₂ huδ]

/-- Below an inner cutoff the long half-open and short closed time intervals induce the
same within-filter. -/
theorem nhdsWithin_agree {b c t : ℝ} (ht : t < b) (hbc : b ≤ c) :
    nhdsWithin t (Set.Ico 0 c) = nhdsWithin t (Set.Icc 0 b) := by
  have hio : Set.Iio b ∈ nhds t := Iio_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Icc 0 b) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico, Set.mem_Iio]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h3.le⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, lt_of_lt_of_le h3 hbc⟩, h3⟩

/-- **The coherent family below the supremum**: coherent trajectories on every closed
interval strictly below `c` assemble into one trajectory on `[0, c)`. -/
theorem traj_family {q : ℂ → ℂ} {σ₀ : ℝ → ℂ} {δ₀ c : ℝ}
    (hδ₀ : 0 < δ₀) (hδc : δ₀ < c)
    (hA : ∀ b ∈ Set.Ico δ₀ c, ∃ σ : ℝ → ℂ,
      Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧ IsTrajOn q σ (Set.Icc 0 b)) :
    ∃ σ : ℝ → ℂ, Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧ IsTrajOn q σ (Set.Ico 0 c) := by
  choose! F hF1 hF2 using hA
  set pick : ℝ → ℝ := fun t => if t < c then max δ₀ ((t + c) / 2) else δ₀ with hpickdef
  have hpick_mem : ∀ t, pick t ∈ Set.Ico δ₀ c := by
    intro t
    by_cases h : t < c
    · rw [hpickdef]
      simp only [if_pos h]
      exact ⟨le_max_left _ _, max_lt hδc (by linarith)⟩
    · rw [hpickdef]
      simp only [if_neg h]
      exact ⟨le_refl _, hδc⟩
  have hpick_gt : ∀ t, 0 ≤ t → t < c → t < pick t := by
    intro t ht htc
    rw [hpickdef]
    simp only [if_pos htc]
    exact lt_max_of_lt_right (by linarith)
  set σ : ℝ → ℂ := fun t => F (pick t) t with hσdef
  have hcoh : ∀ b ∈ Set.Ico δ₀ c, ∀ u ∈ Set.Icc 0 b, σ u = F b u := by
    intro b hb u hu
    have huc : u < c := lt_of_le_of_lt hu.2 hb.2
    have hup : u < pick u := hpick_gt u hu.1 huc
    have hpu := hpick_mem u
    rcases le_total (pick u) b with hpb | hpb
    · exact traj_coherent hδ₀ hpu.1 hpb (hF2 (pick u) hpu) (hF2 b hb)
        (hF1 (pick u) hpu) (hF1 b hb) ⟨hu.1, hup.le⟩
    · exact (traj_coherent hδ₀ hb.1 hpb (hF2 b hb) (hF2 (pick u) hpu)
        (hF1 b hb) (hF1 (pick u) hpu) hu).symm
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro u hu
    have hδmem : δ₀ ∈ Set.Ico δ₀ c := ⟨le_refl _, hδc⟩
    rw [hcoh δ₀ hδmem u hu]
    exact hF1 δ₀ hδmem hu
  · intro t ht
    have hb := hpick_mem t
    have htb : t < pick t := hpick_gt t ht.1 ht.2
    have hσt : σ t = F (pick t) t := hcoh (pick t) hb t ⟨ht.1, htb.le⟩
    change Filter.Tendsto σ (nhdsWithin t (Set.Ico 0 c)) (nhds (σ t))
    rw [nhdsWithin_agree htb hb.2.le, hσt]
    refine Filter.Tendsto.congr' ?_ ((hF2 (pick t) hb).cont t ⟨ht.1, htb.le⟩)
    exact eventually_mem_nhdsWithin.mono fun u hu => (hcoh (pick t) hb u hu).symm
  · intro t ht
    have hb := hpick_mem t
    have htb : t < pick t := hpick_gt t ht.1 ht.2
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ :=
      (hF2 (pick t) hb).chart t ⟨ht.1, htb.le⟩
    have hσt : σ t = F (pick t) t := hcoh (pick t) hb t ⟨ht.1, htb.le⟩
    refine ⟨U, hUo, by rw [hσt]; exact hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
    rw [nhdsWithin_agree htb hb.2.le]
    filter_upwards [hev, eventually_mem_nhdsWithin] with u hu huI
    rw [hcoh (pick t) hb u huI, hσt]
    exact hu

/-- A rational complex point within any prescribed distance of a given point. -/
theorem exists_rat_near_complex (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℚ × ℚ, ‖z - (((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I)‖ < δ := by
  obtain ⟨q₁, hq₁⟩ := exists_rat_near z.re (by positivity : (0 : ℝ) < δ / 2)
  obtain ⟨q₂, hq₂⟩ := exists_rat_near z.im (by positivity : (0 : ℝ) < δ / 2)
  refine ⟨(q₁, q₂), ?_⟩
  set w : ℂ := z - (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I) with hwdef
  have hre : w.re = z.re - (q₁ : ℝ) := by
    simp [hwdef, Complex.sub_re, Complex.add_re, Complex.mul_re]
  have him : w.im = z.im - (q₂ : ℝ) := by
    simp [hwdef, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have h1 : |w.re| < δ / 2 := by rw [hre]; exact hq₁
  have h2 : |w.im| < δ / 2 := by rw [him]; exact hq₂
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ < δ := by linarith

/-- **A countable atlas of natural charts with margins**: countably many chart balls,
each with doubled radius inside the regular part of the upper half plane, whose unit
radii cover every regular point. -/
theorem exists_countable_atlas {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) :
    ∃ (c : ℕ → ℂ) (r : ℕ → ℝ) (Φ : ℕ → ℂ → ℂ) (active : ℕ → Prop),
      (∀ j, active j → 0 < r j) ∧
      (∀ j, active j → Metric.ball (c j) (2 * r j) ⊆ {z : ℂ | 0 < z.im}) ∧
      (∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), q w ≠ 0) ∧
      (∀ j, active j → DifferentiableOn ℂ (Φ j) (Metric.ball (c j) (2 * r j))) ∧
      (∀ j, active j → Set.InjOn (Φ j) (Metric.ball (c j) (2 * r j))) ∧
      (∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), deriv (Φ j) w ^ 2 = -q w) ∧
      (∀ z, 0 < z.im → q z ≠ 0 → ∃ j, active j ∧ z ∈ Metric.ball (c j) (r j)) ∧
      (∀ j, ¬ active j → Φ j = id) := by
  classical
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  -- the chartability predicate on rational data
  set embed : (ℚ × ℚ) × ℚ → ℂ × ℝ := fun p =>
    ((((p.1.1 : ℝ) : ℂ) + ((p.1.2 : ℝ) : ℂ) * Complex.I), (p.2 : ℝ)) with hembdef
  set P : (ℚ × ℚ) × ℚ → Prop := fun p =>
    0 < (embed p).2 ∧ Metric.ball (embed p).1 (2 * (embed p).2) ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ w ∈ Metric.ball (embed p).1 (2 * (embed p).2), q w ≠ 0) ∧
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (Metric.ball (embed p).1 (2 * (embed p).2)) ∧
      Set.InjOn Ψ (Metric.ball (embed p).1 (2 * (embed p).2)) ∧
      ∀ w ∈ Metric.ball (embed p).1 (2 * (embed p).2), deriv Ψ w ^ 2 = -q w with hPdef
  obtain ⟨e, he⟩ := exists_surjective_nat ((ℚ × ℚ) × ℚ)
  refine ⟨fun j => (embed (e j)).1, fun j => (embed (e j)).2,
    fun j => if h : P (e j) then h.2.2.2.choose else id, fun j => P (e j),
    fun j hj => hj.1, fun j hj => hj.2.1, fun j hj => hj.2.2.1, ?_, ?_, ?_, ?_,
    fun j hj => dif_neg hj⟩
  · intro j hj
    simp only [dif_pos hj]
    exact hj.2.2.2.choose_spec.1
  · intro j hj
    simp only [dif_pos hj]
    exact hj.2.2.2.choose_spec.2.1
  · intro j hj
    simp only [dif_pos hj]
    exact hj.2.2.2.choose_spec.2.2
  · intro z hz hq0
    -- a chart ball around `z` avoiding the zeros
    obtain ⟨R₀, hR₀, hsubH, Ψ, hΨd, hΨinj, hΨsq⟩ :=
      exists_natural_chart (q := fun w => -q w) hH hq.neg hz (neg_ne_zero.mpr hq0)
    have hqc : ContinuousAt q z := hq.continuousOn.continuousAt (hH.mem_nhds hz)
    obtain ⟨R₁, hR₁, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (hqc (isOpen_ne.mem_nhds hq0) : q ⁻¹' {x | x ≠ 0} ∈ nhds z)
        (Metric.ball_mem_nhds z hR₀))
    set R : ℝ := min R₁ R₀ with hRdef
    have hR : 0 < R := lt_min hR₁ hR₀
    obtain ⟨a, ha⟩ := exists_rat_near_complex z (by positivity : (0 : ℝ) < R / 8)
    obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn (by linarith : R / 8 < R / 4)
    obtain ⟨j, hj⟩ := he (a, ρ)
    set A : ℂ := ((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I with hAdef
    have hsub2 : Metric.ball A (2 * (ρ : ℝ)) ⊆ Metric.ball z R := by
      intro w hw
      rw [Metric.mem_ball] at hw ⊢
      have hzA : dist z A < R / 8 := by rw [dist_eq_norm]; exact ha
      calc dist w z ≤ dist w A + dist A z := dist_triangle _ _ _
        _ < 2 * (ρ : ℝ) + R / 8 := by
            rw [dist_comm A z]
            linarith
        _ < R := by linarith
    have hsubR : Metric.ball z R ⊆ Metric.ball z R₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hPa : P (a, ρ) := by
      refine ⟨by exact_mod_cast lt_trans (by linarith) hρ1, ?_, ?_, Ψ, ?_, ?_, ?_⟩
      · exact (hsub2.trans hsubR).trans hsubH
      · intro w hw
        exact (hball (Metric.ball_subset_ball (min_le_left _ _) (hsub2 hw))).1
      · exact hΨd.mono (hsub2.trans hsubR)
      · exact hΨinj.mono (hsub2.trans hsubR)
      · exact fun w hw => hΨsq w (hsubR (hsub2 hw))
    refine ⟨j, ?_, ?_⟩
    · change P (e j)
      rw [hj]
      exact hPa
    · change z ∈ Metric.ball (embed (e j)).1 (embed (e j)).2
      rw [hj]
      change z ∈ Metric.ball A ((ρ : ℚ) : ℝ)
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖z - A‖ < R / 8 := ha
        _ < (ρ : ℝ) := hρ1

/-- **Chart-branch ratio**: on the connected component of a chart overlap two natural
charts differ by an affine map `z ↦ ε z + k`, and the sign is read off the derivative
ratio at the base point. -/
theorem chart_ratio {q Φ₁ Φ₂ : ℂ → ℂ} {S₁ S₂ : Set ℂ}
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂)
    (h₁d : DifferentiableOn ℂ Φ₁ S₁) (h₂d : DifferentiableOn ℂ Φ₂ S₂)
    (h₁sq : ∀ w ∈ S₁, deriv Φ₁ w ^ 2 = -q w) (h₂sq : ∀ w ∈ S₂, deriv Φ₂ w ^ 2 = -q w)
    {x : ℂ} (hx₁ : x ∈ S₁) (hx₂ : x ∈ S₂) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ deriv Φ₂ x = ε * deriv Φ₁ x ∧
      ∀ z ∈ connectedComponentIn (S₁ ∩ S₂) x,
        Φ₂ z = ε * Φ₁ z + (Φ₂ x - ε * Φ₁ x) := by
  set Ω : Set ℂ := connectedComponentIn (S₁ ∩ S₂) x with hΩdef
  have hΩo : IsOpen Ω := (hS₁.inter hS₂).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hxΩ : x ∈ Ω := mem_connectedComponentIn ⟨hx₁, hx₂⟩
  have hΩsub : Ω ⊆ S₁ ∩ S₂ := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φ₂ z ^ 2 = deriv Φ₁ z ^ 2 := fun z hz => by
    rw [h₂sq z (hΩsub hz).2, h₁sq z (hΩsub hz).1]
  have hΩnhds : Ω ∈ nhds x := hΩo.mem_nhds hxΩ
  rcases open_branch_classification hΩo hΩconn hxΩ
      (h₁d.mono (hΩsub.trans Set.inter_subset_left))
      (h₂d.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · have hev : Φ₂ =ᶠ[nhds x] fun z => Φ₁ z + (Φ₂ x - Φ₁ x) := by
        filter_upwards [hΩnhds] with z hz
        exact hplus z hz
      rw [hev.deriv_eq]
      have hd₁ : DifferentiableAt ℂ Φ₁ x := h₁d.differentiableAt (hS₁.mem_nhds hx₁)
      rw [deriv_add_const]
      push_cast
      ring
    · intro z hz
      rw [hplus z hz]
      push_cast
      ring
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · have hev : Φ₂ =ᶠ[nhds x] fun z => (Φ₂ x + Φ₁ x) - Φ₁ z := by
        filter_upwards [hΩnhds] with z hz
        exact hminus z hz
      rw [hev.deriv_eq, deriv_const_sub]
      push_cast
      ring
    · intro z hz
      rw [hminus z hz]
      push_cast
      ring

/-- A **countable natural-chart atlas with margins** for `q`: chart balls with doubled
radius inside the regular upper half plane whose unit radii cover every regular point. -/
structure Atlas (q : ℂ → ℂ) where
  c : ℕ → ℂ
  r : ℕ → ℝ
  Φ : ℕ → ℂ → ℂ
  active : ℕ → Prop
  hr : ∀ j, active j → 0 < r j
  hH : ∀ j, active j → Metric.ball (c j) (2 * r j) ⊆ {z : ℂ | 0 < z.im}
  hne : ∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), q w ≠ 0
  hd : ∀ j, active j → DifferentiableOn ℂ (Φ j) (Metric.ball (c j) (2 * r j))
  hinj : ∀ j, active j → Set.InjOn (Φ j) (Metric.ball (c j) (2 * r j))
  hsq : ∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), deriv (Φ j) w ^ 2 = -q w
  hcover : ∀ z, 0 < z.im → q z ≠ 0 → ∃ j, active j ∧ z ∈ Metric.ball (c j) (r j)
  hjunk : ∀ j, ¬ active j → Φ j = id

/-- Every holomorphic `q` admits a countable margin atlas. -/
theorem exists_atlas {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) : Nonempty (Atlas q) := by
  obtain ⟨c, r, Φ, active, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_countable_atlas hq
  exact ⟨⟨c, r, Φ, active, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

open Classical in
/-- The measurable chart selector: the least active atlas index whose unit ball contains
the point. -/
noncomputable def Atlas.sel {q : ℂ → ℂ} (A : Atlas q) (z : ℂ) : ℕ :=
  if h : ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j) then Nat.find h else 0

/-- The selected chart is active and its ball contains the given regular point. -/
theorem Atlas.sel_spec {q : ℂ → ℂ} (A : Atlas q) {z : ℂ}
    (hz : 0 < z.im) (hq0 : q z ≠ 0) :
    A.active (A.sel z) ∧ z ∈ Metric.ball (A.c (A.sel z)) (A.r (A.sel z)) := by
  classical
  have h : ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j) := A.hcover z hz hq0
  rw [Atlas.sel, dif_pos h]
  exact Nat.find_spec h

/-- Measurability of the chart selector. -/
theorem Atlas.measurable_sel {q : ℂ → ℂ} (A : Atlas q) :
    Measurable A.sel := by
  classical
  have hpset : ∀ i, MeasurableSet {z : ℂ | A.active i ∧
      z ∈ Metric.ball (A.c i) (A.r i)} := by
    intro i
    by_cases hi : A.active i
    · have : {z : ℂ | A.active i ∧ z ∈ Metric.ball (A.c i) (A.r i)}
          = Metric.ball (A.c i) (A.r i) := by
        ext z
        simp [hi]
      rw [this]
      exact measurableSet_ball
    · have : {z : ℂ | A.active i ∧ z ∈ Metric.ball (A.c i) (A.r i)} = ∅ := by
        ext z
        simp [hi]
      rw [this]
      exact MeasurableSet.empty
  have hE : MeasurableSet {z : ℂ | ∃ j, A.active j ∧
      z ∈ Metric.ball (A.c j) (A.r j)} := by
    have : {z : ℂ | ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)}
        = ⋃ j, {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)} := by
      ext z
      simp
    rw [this]
    exact MeasurableSet.iUnion hpset
  refine measurable_to_countable' fun n => ?_
  have hfib : A.sel ⁻¹' {n} = ({z : ℂ | ∃ j, A.active j ∧
        z ∈ Metric.ball (A.c j) (A.r j)} ∩ ({z : ℂ | A.active n ∧
        z ∈ Metric.ball (A.c n) (A.r n)} ∩ ⋂ i ∈ Set.Iio n, {z : ℂ | A.active i ∧
        z ∈ Metric.ball (A.c i) (A.r i)}ᶜ))
      ∪ ({z : ℂ | ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)}ᶜ
        ∩ (if n = 0 then Set.univ else ∅)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iInter, Set.mem_Iio]
    constructor
    · intro hsel
      by_cases h : ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)
      · rw [Atlas.sel, dif_pos h] at hsel
        refine Or.inl ⟨h, ?_, ?_⟩
        · rw [← hsel]
          exact Nat.find_spec h
        · intro i hi
          rw [← hsel] at hi
          exact Nat.find_min h hi
      · rw [Atlas.sel, dif_neg h] at hsel
        refine Or.inr ⟨h, ?_⟩
        rw [← hsel]
        simp
    · rintro (⟨h, hn, hmin⟩ | ⟨h, hn⟩)
      · rw [Atlas.sel, dif_pos h]
        exact (Nat.find_eq_iff h).mpr ⟨hn, fun i hi => hmin i hi⟩
      · rw [Atlas.sel, dif_neg h]
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exact h0.symm
        · rw [if_neg h0.ne'] at hn
          exact absurd hn (Set.notMem_empty z)
  rw [hfib]
  refine (hE.inter ((hpset n).inter ?_)).union (hE.compl.inter ?_)
  · exact MeasurableSet.biInter ((Set.finite_Iio n).countable) fun i _ => (hpset i).compl
  · by_cases h0 : n = 0
    · rw [if_pos h0]
      exact MeasurableSet.univ
    · rw [if_neg h0]
      exact MeasurableSet.empty

/-- The developed image of a zero-free natural chart domain is open. -/
theorem chart_image_open {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hd : DifferentiableOn ℂ Φ S) (hne : ∀ w ∈ S, q w ≠ 0)
    (hsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w) : IsOpen (Φ '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨p, hpS, rfl⟩
  have hder : deriv Φ p ≠ 0 := by
    intro h0
    apply hne p hpS
    have := hsq p hpS
    rw [h0] at this
    simpa using this.symm
  have han : AnalyticAt ℂ Φ p := (hd.analyticOnNhd hS) p hpS
  have hstrict : HasStrictDerivAt Φ (deriv Φ p) p :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  rw [← hstrict.map_nhds_eq hder]
  exact Filter.image_mem_map (hS.mem_nhds hpS)

/-- **Measurability of the chart inverse**: the set inverse of an injective map with open
image, continuous inverse on the image, and constant junk off the image. -/
theorem invFunOn_measurable {Φ : ℂ → ℂ} {S : Set ℂ} (_hS : IsOpen S)
    (himg : IsOpen (Φ '' S)) (hinj : Set.InjOn Φ S)
    (hopenmap : ∀ U : Set ℂ, IsOpen U → IsOpen (Φ '' (U ∩ S))) :
    Measurable (Function.invFunOn Φ S) := by
  classical
  refine measurable_of_isOpen fun U hU => ?_
  have hsplit : Function.invFunOn Φ S ⁻¹' U
      = (Φ '' S ∩ Function.invFunOn Φ S ⁻¹' U)
        ∪ ((Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U) := by
    ext b
    by_cases hb : b ∈ Φ '' S <;> simp [hb]
  have hin : Φ '' S ∩ Function.invFunOn Φ S ⁻¹' U = Φ '' (U ∩ S) := by
    ext b
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hbU⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, ha, rfl⟩
      have hmem := Function.invFunOn_mem hex
      have heq := Function.invFunOn_eq hex
      have hval : Function.invFunOn Φ S (Φ a) = a := hinj hmem ha heq
      exact ⟨a, ⟨by rwa [← hval], ha⟩, rfl⟩
    · rintro ⟨a, ⟨haU, haS⟩, rfl⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, haS, rfl⟩
      have hval : Function.invFunOn Φ S (Φ a) = a :=
        hinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
      exact ⟨⟨a, haS, rfl⟩, by rw [Set.mem_preimage, hval]; exact haU⟩
  have hconst : ∀ b ∉ Φ '' S, ∀ b' ∉ Φ '' S,
      Function.invFunOn Φ S b = Function.invFunOn Φ S b' := by
    intro b hb b' hb'
    have h1 : ¬∃ x ∈ S, Φ x = b := fun ⟨x, hx, he⟩ => hb ⟨x, hx, he⟩
    have h2 : ¬∃ x ∈ S, Φ x = b' := fun ⟨x, hx, he⟩ => hb' ⟨x, hx, he⟩
    rw [Function.invFunOn_neg h1, Function.invFunOn_neg h2]
  have hout : MeasurableSet ((Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U) := by
    by_cases hex : ∃ b, b ∉ Φ '' S ∧ Function.invFunOn Φ S b ∈ U
    · obtain ⟨b₀, hb₀, hb₀U⟩ := hex
      have : (Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U = (Φ '' S)ᶜ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
          and_iff_left_iff_imp]
        intro hb
        rwa [hconst b hb b₀ hb₀]
      rw [this]
      exact himg.measurableSet.compl
    · push Not at hex
      have : (Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U = ∅ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨hb, hbU⟩
        exact hex b hb hbU
      rw [this]
      exact MeasurableSet.empty
  rw [hsplit, hin]
  exact (hopenmap U hU).measurableSet.union hout

/-- Measurability of the inverse of an atlas chart. -/
theorem Atlas.measurable_inv {q : ℂ → ℂ} (A : Atlas q) (j : ℕ) :
    Measurable (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))) := by
  classical
  by_cases hj : A.active j
  · refine invFunOn_measurable Metric.isOpen_ball
      (chart_image_open Metric.isOpen_ball (A.hd j hj) (A.hne j hj) (A.hsq j hj))
      (A.hinj j hj) (fun U hU => ?_)
    have hopen : IsOpen (U ∩ Metric.ball (A.c j) (2 * A.r j)) :=
      hU.inter Metric.isOpen_ball
    have himg := chart_image_open (q := q) hopen
      ((A.hd j hj).mono Set.inter_subset_right)
      (fun w hw => A.hne j hj w hw.2)
      (fun w hw => A.hsq j hj w hw.2)
    exact himg
  · rw [A.hjunk j hj]
    refine invFunOn_measurable Metric.isOpen_ball ?_ ?_ (fun U hU => ?_)
    · rw [Set.image_id]
      exact Metric.isOpen_ball
    · exact Function.injective_id.injOn
    · rw [Set.image_id]
      exact hU.inter Metric.isOpen_ball

open Classical in
/-- A function continuous on an open set and constant outside is measurable. -/
theorem measurable_piecewise_open {f : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hf : ContinuousOn f S) (k : ℂ) :
    Measurable (S.piecewise f fun _ => k) := by
  classical
  refine measurable_of_isOpen fun U hU => ?_
  have hsplit : (S.piecewise f fun _ => k) ⁻¹' U
      = (S ∩ f ⁻¹' U) ∪ (Sᶜ ∩ (if k ∈ U then Set.univ else ∅)) := by
    ext x
    by_cases hx : x ∈ S
    · simp only [Set.mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx, Set.mem_union,
        Set.mem_inter_iff, Set.mem_compl_iff, hx, not_true, false_and, or_false,
        true_and]
    · simp only [Set.mem_preimage, Set.piecewise_eq_of_notMem _ _ _ hx, Set.mem_union,
        Set.mem_inter_iff, hx, false_and, false_or, Set.mem_compl_iff, not_false_iff,
        true_and]
      split_ifs with hk
      · simp [hk]
      · simp [hk]
  rw [hsplit]
  refine (hf.isOpen_inter_preimage hS hU).measurableSet.union
    (hS.measurableSet.compl.inter ?_)
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

open Classical in
/-- The masked atlas chart: the chart on its doubled ball, zero elsewhere and for
inactive indices. -/
noncomputable def Atlas.mchart {q : ℂ → ℂ} (A : Atlas q) (j : ℕ) : ℂ → ℂ :=
  if _h : A.active j then
    (Metric.ball (A.c j) (2 * A.r j)).piecewise (A.Φ j) fun _ => 0
  else fun _ => 0

/-- The truncated chart maps of the atlas are measurable. -/
theorem Atlas.measurable_mchart {q : ℂ → ℂ} (A : Atlas q) (j : ℕ) :
    Measurable (A.mchart j) := by
  classical
  rw [Atlas.mchart]
  split_ifs with hj
  · exact measurable_piecewise_open Metric.isOpen_ball
      ((A.hd j hj).continuousOn) 0
  · exact measurable_const

/-- The masked chart agrees with the chart on the doubled ball of an active index. -/
theorem Atlas.mchart_eq {q : ℂ → ℂ} (A : Atlas q) {j : ℕ} (hj : A.active j)
    {z : ℂ} (hz : z ∈ Metric.ball (A.c j) (2 * A.r j)) : A.mchart j z = A.Φ j z := by
  classical
  rw [Atlas.mchart, dif_pos hj, Set.piecewise_eq_of_mem _ _ _ hz]

/-- The chart derivative in the selected chart, as one measurable function. -/
theorem Atlas.measurable_derivSel {q : ℂ → ℂ} (A : Atlas q) :
    Measurable (fun y : ℂ => deriv (A.Φ (A.sel y)) y) := by
  have hG : Measurable (fun jy : ℕ × ℂ => deriv (A.Φ jy.1) jy.2) :=
    measurable_from_prod_countable_right fun j => measurable_deriv (A.Φ j)
  exact hG.comp (A.measurable_sel.prodMk measurable_id)

open Classical in
/-- **One stepper move**: transport by the signed step in the selected chart and update
the sign by the chart-branch derivative ratio at the new position. -/
noncomputable def Atlas.step {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (p : ℂ × ℝ) :
    ℂ × ℝ :=
  let j := A.sel p.1
  let x' := Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
    (A.mchart j p.1 + ((p.2 * h : ℝ) : ℂ))
  (x', p.2 * ((deriv (A.Φ (A.sel x')) x') * (deriv (A.Φ j) x')⁻¹).re)

/-- Joint measurability of the stepper move. -/
theorem Atlas.measurable_step {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) :
    Measurable (A.step h) := by
  have hX : ∀ j : ℕ, Measurable (fun p : ℂ × ℝ =>
      Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j p.1 + ((p.2 * h : ℝ) : ℂ))) := by
    intro j
    exact (A.measurable_inv j).comp
      (((A.measurable_mchart j).comp measurable_fst).add
        (Complex.measurable_ofReal.comp (measurable_snd.mul_const h)))
  have hcomp : A.step h = (fun jp : ℕ × (ℂ × ℝ) =>
      (Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
          (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ)),
        jp.2.2 * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ)))))
            (Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ))))
          * (deriv (A.Φ jp.1) (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ))))⁻¹).re))
      ∘ (fun p : ℂ × ℝ => (A.sel p.1, p)) := rfl
  rw [hcomp]
  refine Measurable.comp ?_
    ((A.measurable_sel.comp measurable_fst).prodMk measurable_id)
  refine measurable_from_prod_countable_right fun j => ?_
  refine Measurable.prodMk (hX j) ?_
  refine measurable_snd.mul ?_
  refine (Complex.measurable_re).comp ?_
  exact (A.measurable_derivSel.comp (hX j)).mul
    (((measurable_deriv (A.Φ j)).comp (hX j)).inv)

open Classical in
/-- The stepper move carrying its step size: jointly measurable in size and state. -/
noncomputable def Atlas.step2 {q : ℂ → ℂ} (A : Atlas q)
    (p : ℝ × ℂ × ℝ) : ℝ × ℂ × ℝ :=
  let j := A.sel p.2.1
  let x' := Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
    (A.mchart j p.2.1 + ((p.2.2 * p.1 : ℝ) : ℂ))
  (p.1, x', p.2.2 * ((deriv (A.Φ (A.sel x')) x') * (deriv (A.Φ j) x')⁻¹).re)

/-- Joint measurability of the size-carrying stepper move. -/
theorem Atlas.measurable_step2 {q : ℂ → ℂ} (A : Atlas q) :
    Measurable A.step2 := by
  have hX : ∀ j : ℕ, Measurable (fun p : ℝ × ℂ × ℝ =>
      Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j p.2.1 + ((p.2.2 * p.1 : ℝ) : ℂ))) := by
    intro j
    exact (A.measurable_inv j).comp
      (((A.measurable_mchart j).comp (measurable_fst.comp measurable_snd)).add
        (Complex.measurable_ofReal.comp
          ((measurable_snd.comp measurable_snd).mul measurable_fst)))
  have hcomp : A.step2 = (fun jp : ℕ × (ℝ × ℂ × ℝ) =>
      (jp.2.1, Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
          (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ)),
        jp.2.2.2 * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ)))))
            (Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ))))
          * (deriv (A.Φ jp.1) (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ))))⁻¹).re))
      ∘ (fun p : ℝ × ℂ × ℝ => (A.sel p.2.1, p)) := rfl
  rw [hcomp]
  refine Measurable.comp ?_
    ((A.measurable_sel.comp (measurable_fst.comp measurable_snd)).prodMk measurable_id)
  refine measurable_from_prod_countable_right fun j => ?_
  refine Measurable.prodMk measurable_fst (Measurable.prodMk (hX j) ?_)
  refine (measurable_snd.comp measurable_snd).mul ?_
  refine (Complex.measurable_re).comp ?_
  exact (A.measurable_derivSel.comp (hX j)).mul
    (((measurable_deriv (A.Φ j)).comp (hX j)).inv)

/-- The `n`-th stepper approximant of the flow: `n + 1` exact chart steps of size
`t/(n+1)` started with unit sign. -/
noncomputable def Atlas.flowApprox {q : ℂ → ℂ} (A : Atlas q) (n : ℕ)
    (p : ℝ × ℂ) : ℂ :=
  ((A.step2)^[n + 1] (p.1 / (n + 1), p.2, 1)).2.1

/-- The approximate flow steps of the atlas are measurable. -/
theorem Atlas.measurable_flowApprox {q : ℂ → ℂ} (A : Atlas q) (n : ℕ) :
    Measurable (A.flowApprox n) := by
  have h1 : Measurable (fun p : ℝ × ℂ => (p.1 / (n + 1), p.2, (1 : ℝ))) :=
    (measurable_fst.div_const _).prodMk (measurable_snd.prodMk measurable_const)
  exact (measurable_fst.comp measurable_snd).comp
    ((A.measurable_step2.iterate (n + 1)).comp h1)

open Classical in
/-- **The measurable flow candidate**: the stabilized limit of the stepper approximants,
with junk value the start point. -/
noncomputable def Atlas.flow {q : ℂ → ℂ} (A : Atlas q) (t : ℝ) (z : ℂ) : ℂ :=
  if h : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (t, z)) Filter.atTop (nhds L)
  then h.choose else z

/-- Joint measurability of the flow candidate. -/
theorem Atlas.measurable_flow {q : ℂ → ℂ} (A : Atlas q) :
    Measurable (fun p : ℝ × ℂ => A.flow p.1 p.2) := by
  classical
  set E : Set (ℝ × ℂ) := {p | ∃ L, Filter.Tendsto (fun n => A.flowApprox n p)
    Filter.atTop (nhds L)} with hEdef
  have hE : MeasurableSet E :=
    MeasureTheory.measurableSet_exists_tendsto fun n => A.measurable_flowApprox n
  set g : ℕ → ℝ × ℂ → ℂ := fun n => E.piecewise (A.flowApprox n) Prod.snd with hgdef
  have hgmeas : ∀ n, Measurable (g n) := fun n =>
    Measurable.piecewise hE (A.measurable_flowApprox n) measurable_snd
  have hglim : ∀ p : ℝ × ℂ, Filter.Tendsto (fun n => g n p) Filter.atTop
      (nhds (A.flow p.1 p.2)) := by
    intro p
    by_cases hp : p ∈ E
    · have hg' : (fun n => g n p) = fun n => A.flowApprox n p := by
        funext n
        exact Set.piecewise_eq_of_mem _ _ _ hp
      have hp' : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (p.1, p.2))
          Filter.atTop (nhds L) := hp
      rw [hg', Atlas.flow, dif_pos hp']
      exact hp'.choose_spec
    · have hg' : (fun n => g n p) = fun _ => p.2 := by
        funext n
        exact Set.piecewise_eq_of_notMem _ _ _ hp
      have hp' : ¬∃ L, Filter.Tendsto (fun n => A.flowApprox n (p.1, p.2))
          Filter.atTop (nhds L) := hp
      rw [hg', Atlas.flow, dif_neg hp']
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable' Filter.atTop hgmeas
    (tendsto_pi_nhds.mpr hglim)

/-- Points on a vertical trajectory are regular. -/
theorem traj_regular {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ}
    (hσ : IsTrajOn q σ s) {u : ℝ} (hu : u ∈ s) : 0 < (σ u).im ∧ q (σ u) ≠ 0 := by
  obtain ⟨U, -, hpU, hUH, hUne, -, -, -, -, -⟩ := hσ.chart u hu
  exact ⟨hUH hpU, hUne _ hpU⟩

/-- The flat-speed Lipschitz bound on the closed time interval, endpoints included. -/
theorem traj_dist_le_Icc {q : ℂ → ℂ} {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T)) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u ≤ T) :
    ‖σ u - σ s‖ ≤ Real.sqrt m⁻¹ * (u - s) := by
  rcases eq_or_lt_of_le hsu with heq | hlt
  · rw [← heq]
    simp
  have hσ' : IsTrajOn q σ (Set.Ico 0 T) := traj_mono hσ Set.Ico_subset_Icc_self
  have hbound' : ∀ v ∈ Set.Ico 0 T, m ≤ ‖q (σ v)‖ := fun v hv =>
    hbound v ⟨hv.1, hv.2.le⟩
  set δ : ℝ := (u - s) / 3 with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    linarith
  set sn : ℕ → ℝ := fun n => s + δ / (n + 1) with hsndef
  set un : ℕ → ℝ := fun n => u - δ / (n + 1) with hundef
  have hstep : ∀ n : ℕ, ‖σ (un n) - σ (sn n)‖ ≤ Real.sqrt m⁻¹ * (un n - sn n) := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have h1 : 0 < sn n := by
      rw [hsndef]
      simp only
      linarith
    have h2 : sn n ≤ un n := by
      rw [hsndef, hundef]
      simp only
      have : δ / (n + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
        nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
      rw [hδdef] at this ⊢
      linarith
    have h3 : un n < T := by
      rw [hundef]
      simp only
      linarith
    exact traj_dist_le hσ' hm hbound' h1 h2 h3
  have hsn_mem : ∀ n, sn n ∈ Set.Icc 0 T := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have : δ / (n + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
      nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
    constructor
    · rw [hsndef]; simp only; linarith
    · rw [hsndef]; simp only; rw [hδdef] at this ⊢; linarith
  have hun_mem : ∀ n, un n ∈ Set.Icc 0 T := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have : δ / (n + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
      nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
    constructor
    · rw [hundef]; simp only; rw [hδdef] at this ⊢; linarith
    · rw [hundef]; simp only; linarith
  have htend : Filter.Tendsto (fun n : ℕ => δ / (n + 1)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => δ * (1 / ((n : ℝ) + 1))) Filter.atTop
        (nhds (δ * 0)) := h0.const_mul δ
    simpa [div_eq_mul_inv, mul_zero] using h2
  have hsn_tend : Filter.Tendsto sn Filter.atTop (nhds s) := by
    have := htend.const_add s
    simpa [hsndef] using this
  have hun_tend : Filter.Tendsto un Filter.atTop (nhds u) := by
    have h2 := (htend.const_mul (-1 : ℝ)).const_add u
    have h3 : (fun n : ℕ => u + (-1) * (δ / (n + 1))) = un := by
      funext n
      rw [hundef]
      ring
    rw [h3] at h2
    simpa using h2
  have hσs : Filter.Tendsto (fun n => σ (sn n)) Filter.atTop (nhds (σ s)) := by
    refine (hσ.cont s ⟨hs, le_trans hsu hu⟩).tendsto.comp ?_
    rw [Filter.tendsto_iff_comap, ← Filter.tendsto_iff_comap]
    exact tendsto_nhdsWithin_iff.mpr ⟨hsn_tend, Filter.Eventually.of_forall hsn_mem⟩
  have hσu : Filter.Tendsto (fun n => σ (un n)) Filter.atTop (nhds (σ u)) := by
    refine (hσ.cont u ⟨le_trans hs hsu, hu⟩).tendsto.comp ?_
    rw [Filter.tendsto_iff_comap, ← Filter.tendsto_iff_comap]
    exact tendsto_nhdsWithin_iff.mpr ⟨hun_tend, Filter.Eventually.of_forall hun_mem⟩
  refine le_of_tendsto_of_tendsto' ((hσu.sub hσs).norm) ?_ hstep
  exact (hun_tend.sub hsn_tend).const_mul (Real.sqrt m⁻¹)

/-- A point in an active atlas unit ball bounds the selector from above. -/
theorem sel_le {q : ℂ → ℂ} (A : Atlas q) {z : ℂ} {j : ℕ}
    (hj : A.active j) (hz : z ∈ Metric.ball (A.c j) (A.r j)) : A.sel z ≤ j := by
  classical
  have h : ∃ i, A.active i ∧ z ∈ Metric.ball (A.c i) (A.r i) := ⟨j, hj, hz⟩
  rw [Atlas.sel, dif_pos h]
  exact Nat.find_min' h ⟨hj, hz⟩

/-- The selector is bounded along a compact track of regular points. -/
theorem sel_bound {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσc : ContinuousOn σ (Set.Icc 0 T))
    (hreg : ∀ u ∈ Set.Icc 0 T, 0 < (σ u).im ∧ q (σ u) ≠ 0) :
    ∃ J : ℕ, ∀ u ∈ Set.Icc 0 T, A.sel (σ u) ≤ J := by
  have hloc : ∀ u : Set.Icc (0 : ℝ) T, ∃ V : Set ℝ, IsOpen V ∧ (u : ℝ) ∈ V ∧
      ∀ v ∈ V ∩ Set.Icc 0 T, A.sel (σ v) ≤ A.sel (σ (u : ℝ)) := by
    intro u
    obtain ⟨hact, hmem⟩ := A.sel_spec (hreg u u.2).1 (hreg u u.2).2
    have hpre : σ ⁻¹' Metric.ball (A.c (A.sel (σ u))) (A.r (A.sel (σ u)))
        ∈ nhdsWithin (u : ℝ) (Set.Icc 0 T) :=
      (hσc (u : ℝ) u.2) (Metric.isOpen_ball.mem_nhds hmem)
    obtain ⟨V, hVo, hVmem, hVsub⟩ := mem_nhdsWithin.mp hpre
    exact ⟨V, hVo, hVmem, fun v hv => sel_le A hact (hVsub ⟨hv.1, hv.2⟩)⟩
  choose V hVo hVmem hVsel using hloc
  obtain ⟨F, hF⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).elim_finite_subcover V hVo
    (fun v hv => Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hVmem ⟨v, hv⟩⟩)
  refine ⟨F.sup (fun u => A.sel (σ (u : ℝ))), ?_⟩
  intro v hv
  obtain ⟨u, huF, hvV⟩ := Set.mem_iUnion₂.mp (hF hv)
  have hsup : A.sel (σ (u : ℝ)) ≤ F.sup (fun u => A.sel (σ (u : ℝ))) :=
    Finset.le_sup (f := fun u : Set.Icc (0 : ℝ) T => A.sel (σ (u : ℝ))) huF
  exact le_trans (hVsel u v ⟨hvV, hv⟩) hsup

/-- A uniform positive lower bound on the radii of the first `J` active charts. -/
theorem atlas_radius_min {q : ℂ → ℂ} (A : Atlas q) (J : ℕ) :
    ∃ ρ > 0, ∀ j ≤ J, A.active j → ρ ≤ A.r j := by
  induction J with
  | zero =>
    by_cases h : A.active 0
    · refine ⟨A.r 0, A.hr 0 h, fun j hj hact => ?_⟩
      rw [Nat.le_zero.mp hj]
    · refine ⟨1, one_pos, fun j hj hact => ?_⟩
      rw [Nat.le_zero.mp hj] at hact
      exact absurd hact h
  | succ n ih =>
    obtain ⟨ρ, hρ, hle⟩ := ih
    by_cases h : A.active (n + 1)
    · refine ⟨min ρ (A.r (n + 1)), lt_min hρ (A.hr _ h), fun j hj hact => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
      · exact le_trans (min_le_left _ _) (hle j (Nat.lt_succ_iff.mp hlt) hact)
      · rw [heq]
        exact min_le_right _ _
    · refine ⟨ρ, hρ, fun j hj hact => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
      · exact hle j (Nat.lt_succ_iff.mp hlt) hact
      · rw [heq] at hact
        exact absurd hact h

/-- The trajectory develops in the chart `Φ` with slope `s` at time `u`. -/
def SlopeAt (Φ : ℂ → ℂ) (σ : ℝ → ℂ) (I : Set ℝ) (u : ℝ) (s : ℝ) : Prop :=
  ∀ᶠ v in nhdsWithin u I, Φ (σ v) = Φ (σ u) + s * ((v - u : ℝ) : ℂ)

/-- **Forward pinning**: an affine identity on a nondegenerate forward interval forces
its slope to agree with the germ slope. -/
theorem slope_pin_forward {Φ : ℂ → ℂ} {σ : ℝ → ℂ} {T u u' s ε : ℝ}
    (hsub : Set.Icc u u' ⊆ Set.Icc 0 T) (huu' : u < u')
    (hslope : SlopeAt Φ σ (Set.Icc 0 T) u s)
    (haff : ∀ v ∈ Set.Icc u u', Φ (σ v) = Φ (σ u) + ε * ((v - u : ℝ) : ℂ)) :
    ε = s := by
  have hne : (nhdsWithin u (Set.Ioc u u')).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ioc huu'.ne]
    exact ⟨le_refl u, huu'.le⟩
  have hmono : nhdsWithin u (Set.Ioc u u') ≤ nhdsWithin u (Set.Icc 0 T) :=
    nhdsWithin_mono u (fun v hv => hsub ⟨hv.1.le, hv.2⟩)
  obtain ⟨v, hv, e₁⟩ := (eventually_mem_nhdsWithin.and
    (hslope.filter_mono hmono)).exists
  have e₂ := haff v ⟨hv.1.le, hv.2⟩
  have hvne : ((v - u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hv.1))
  have hmul : (ε : ℂ) * ((v - u : ℝ) : ℂ) = s * ((v - u : ℝ) : ℂ) := by
    rw [e₁] at e₂
    linear_combination -e₂
  exact_mod_cast mul_right_cancel₀ hvne hmul

/-- **Slope transport to the segment endpoint**: an affine development on `[u, u']`
extends to a two-sided germ of the same slope at `u'`. -/
theorem slope_transport {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {T : ℝ} (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {u u' s : ℝ} (hu0 : 0 ≤ u) (huu' : u < u') (hu'T : u' ≤ T)
    (hxS : σ u' ∈ S)
    (haff : ∀ v ∈ Set.Icc u u', Φ (σ v) = Φ (σ u) + s * ((v - u : ℝ) : ℂ)) :
    SlopeAt Φ σ (Set.Icc 0 T) u' s := by
  have hu'mem : u' ∈ Set.Icc 0 T := ⟨le_trans hu0 huu'.le, hu'T⟩
  obtain ⟨ε, hε, hgerm⟩ := traj_ambient_local hS hΦd hΦsq hσ
    (Set.Subset.refl _) hu'mem hxS
  have hne : (nhdsWithin u' (Set.Ico u u')).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico huu'.ne]
    exact ⟨huu'.le, le_refl u'⟩
  have hmono : nhdsWithin u' (Set.Ico u u') ≤ nhdsWithin u' (Set.Icc 0 T) :=
    nhdsWithin_mono u' (fun v hv => ⟨le_trans hu0 hv.1, le_trans hv.2.le hu'T⟩)
  obtain ⟨v, hv, e₁⟩ := (eventually_mem_nhdsWithin.and
    (hgerm.filter_mono hmono)).exists
  have e₂ := haff v ⟨hv.1, hv.2.le⟩
  have e₃ := haff u' (Set.right_mem_Icc.mpr huu'.le)
  have hvne : ((v - u' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt hv.2))
  have hεs : (ε : ℂ) = (s : ℂ) := by
    have hmul : (ε : ℂ) * ((v - u' : ℝ) : ℂ) = s * ((v - u' : ℝ) : ℂ) := by
      rw [e₂, e₃] at e₁
      push_cast at e₁ ⊢
      linear_combination -e₁
    exact mul_right_cancel₀ hvne hmul
  have hεs' : ε = s := by exact_mod_cast hεs
  rw [← hεs']
  exact hgerm

/-- **Chart change of the slope**: through an affine branch relation the slope
multiplies by the branch sign. -/
theorem slope_ratio {Φ₁ Φ₂ : ℂ → ℂ} {Ω : Set ℂ} (hΩo : IsOpen Ω)
    {σ : ℝ → ℂ} {T u s ε : ℝ} {k : ℂ} (_hu : u ∈ Set.Icc 0 T)
    (hcont : ContinuousWithinAt σ (Set.Icc 0 T) u) (hxΩ : σ u ∈ Ω)
    (hrel : ∀ z ∈ Ω, Φ₂ z = (ε : ℂ) * Φ₁ z + k)
    (hslope : SlopeAt Φ₁ σ (Set.Icc 0 T) u s) :
    SlopeAt Φ₂ σ (Set.Icc 0 T) u (ε * s) := by
  have hev : ∀ᶠ v in nhdsWithin u (Set.Icc 0 T), σ v ∈ Ω :=
    hcont (hΩo.mem_nhds hxΩ)
  filter_upwards [hslope, hev] with v hv hvΩ
  rw [hrel _ hvΩ, hrel _ hxΩ, hv]
  push_cast
  ring

/-- **The stepper move lands on the trajectory**: within the margin threshold, the
selected chart contains the coming segment, the development is affine with the germ
slope, and the chart inverse of the stepped development is the trajectory point. -/
theorem step_position {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ)
    {u : ℝ} (hu0 : 0 ≤ u) (huh : u + h ≤ T) {sgn : ℝ}
    (hslope : SlopeAt (A.Φ (A.sel (σ u))) σ (Set.Icc 0 T) u sgn) :
    (∀ v ∈ Set.Icc u (u + h), σ v ∈ Metric.ball (A.c (A.sel (σ u)))
      (2 * A.r (A.sel (σ u)))) ∧
    (∀ v ∈ Set.Icc u (u + h), A.Φ (A.sel (σ u)) (σ v)
      = A.Φ (A.sel (σ u)) (σ u) + sgn * ((v - u : ℝ) : ℂ)) ∧
    Function.invFunOn (A.Φ (A.sel (σ u)))
      (Metric.ball (A.c (A.sel (σ u))) (2 * A.r (A.sel (σ u))))
      (A.mchart (A.sel (σ u)) (σ u) + ((sgn * h : ℝ) : ℂ)) = σ (u + h) := by
  have humem : u ∈ Set.Icc 0 T := ⟨hu0, by linarith⟩
  obtain ⟨him, hq0⟩ := traj_regular hσ humem
  obtain ⟨hact, hmem⟩ := A.sel_spec him hq0
  set j : ℕ := A.sel (σ u) with hjdef
  have hsubI : Set.Icc u (u + h) ⊆ Set.Icc 0 T := fun v hv =>
    ⟨le_trans hu0 hv.1, le_trans hv.2 huh⟩
  have htrack : ∀ v ∈ Set.Icc u (u + h), σ v ∈ Metric.ball (A.c j) (2 * A.r j) := by
    intro v hv
    have hd1 : ‖σ v - σ u‖ ≤ Real.sqrt m⁻¹ * (v - u) :=
      traj_dist_le_Icc hσ hm hbound hu0 hv.1 (le_trans hv.2 huh)
    have hd2 : Real.sqrt m⁻¹ * (v - u) ≤ Real.sqrt m⁻¹ * h := by
      have := hv.2
      have hM : 0 ≤ Real.sqrt m⁻¹ := Real.sqrt_nonneg _
      nlinarith [hv.1]
    have hd3 : ‖σ v - σ u‖ < ρ := lt_of_le_of_lt (le_trans hd1 hd2) hsmall
    have hd4 : ρ ≤ A.r j := hrad u humem
    rw [Metric.mem_ball] at hmem ⊢
    calc dist (σ v) (A.c j) ≤ dist (σ v) (σ u) + dist (σ u) (A.c j) :=
          dist_triangle _ _ _
      _ < A.r j + A.r j := by
          rw [dist_eq_norm]
          exact add_lt_add (lt_of_lt_of_le hd3 hd4) hmem
      _ = 2 * A.r j := by ring
  obtain ⟨ε₀, hε₀, haff₀⟩ := traj_ambient_affine Metric.isOpen_ball (A.hd j hact)
    (A.hsq j hact) hσ (by linarith : u ≤ u + h) hsubI htrack
  have hε₀sgn : ε₀ = sgn :=
    slope_pin_forward hsubI (by linarith) hslope haff₀
  have haff : ∀ v ∈ Set.Icc u (u + h), A.Φ j (σ v)
      = A.Φ j (σ u) + sgn * ((v - u : ℝ) : ℂ) := by
    intro v hv
    rw [← hε₀sgn]
    exact haff₀ v hv
  refine ⟨htrack, haff, ?_⟩
  have hmem2 : σ u ∈ Metric.ball (A.c j) (2 * A.r j) :=
    Metric.ball_subset_ball (by linarith [A.hr j hact]) hmem
  have htarget : A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ)
      = A.Φ j (σ (u + h)) := by
    rw [A.mchart_eq hact hmem2, haff (u + h) (Set.right_mem_Icc.mpr (by linarith))]
    push_cast
    ring
  rw [htarget]
  have hex : ∃ a ∈ Metric.ball (A.c j) (2 * A.r j), A.Φ j a = A.Φ j (σ (u + h)) :=
    ⟨σ (u + h), htrack (u + h) (Set.right_mem_Icc.mpr (by linarith)), rfl⟩
  exact (A.hinj j hact) (Function.invFunOn_mem hex)
    (htrack (u + h) (Set.right_mem_Icc.mpr (by linarith)))
    (Function.invFunOn_eq hex)

/-- **One stepper move follows the trajectory** and carries the slope into the newly
selected chart. -/
theorem step_follows {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ)
    {u : ℝ} (hu0 : 0 ≤ u) (huh : u + h ≤ T) {sgn : ℝ}
    (hslope : SlopeAt (A.Φ (A.sel (σ u))) σ (Set.Icc 0 T) u sgn) :
    (A.step2 (h, σ u, sgn)).1 = h ∧
    (A.step2 (h, σ u, sgn)).2.1 = σ (u + h) ∧
    SlopeAt (A.Φ (A.sel (σ (u + h)))) σ (Set.Icc 0 T) (u + h)
      ((A.step2 (h, σ u, sgn)).2.2) := by
  obtain ⟨htrack, haff, hinv⟩ := step_position A hσ hm hbound hrad hh0 hsmall
    hu0 huh hslope
  set j : ℕ := A.sel (σ u) with hjdef
  have humem : u ∈ Set.Icc 0 T := ⟨hu0, by linarith⟩
  have huhmem : u + h ∈ Set.Icc 0 T := ⟨by linarith, huh⟩
  obtain ⟨him, hq0⟩ := traj_regular hσ humem
  obtain ⟨him', hq0'⟩ := traj_regular hσ huhmem
  obtain ⟨hact, hmem⟩ := A.sel_spec him hq0
  obtain ⟨hact', hmem'⟩ := A.sel_spec him' hq0'
  set j' : ℕ := A.sel (σ (u + h)) with hj'def
  have hx'S₁ : σ (u + h) ∈ Metric.ball (A.c j) (2 * A.r j) :=
    htrack (u + h) (Set.right_mem_Icc.mpr (by linarith))
  have hx'S₂ : σ (u + h) ∈ Metric.ball (A.c j') (2 * A.r j') :=
    Metric.ball_subset_ball (by linarith [A.hr j' hact']) hmem'
  have h21 : (A.step2 (h, σ u, sgn)).2.1 = σ (u + h) := hinv
  have h22 : (A.step2 (h, σ u, sgn)).2.2
      = sgn * ((deriv (A.Φ j') (σ (u + h)))
        * (deriv (A.Φ j) (σ (u + h)))⁻¹).re := by
    change sgn * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ)))))
        (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ))))
      * (deriv (A.Φ j) (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ))))⁻¹).re = _
    rw [hinv]
  obtain ⟨ε', hε', hderiv', hrel'⟩ := chart_ratio (q := q) Metric.isOpen_ball
    Metric.isOpen_ball (A.hd j hact) (A.hd j' hact') (A.hsq j hact) (A.hsq j' hact')
    hx'S₁ hx'S₂
  have hd : deriv (A.Φ j) (σ (u + h)) ≠ 0 := by
    intro h0
    apply hq0'
    have hsq := A.hsq j hact _ hx'S₁
    rw [h0] at hsq
    simpa using hsq.symm
  have hratio : ((deriv (A.Φ j') (σ (u + h)))
      * (deriv (A.Φ j) (σ (u + h)))⁻¹).re = ε' := by
    rw [hderiv', mul_assoc, mul_inv_cancel₀ hd, mul_one, Complex.ofReal_re]
  have hslope₁ : SlopeAt (A.Φ j) σ (Set.Icc 0 T) (u + h) sgn :=
    slope_transport Metric.isOpen_ball (A.hd j hact) (A.hsq j hact) hσ hu0
      (by linarith) huh hx'S₁ haff
  have hslope₂ : SlopeAt (A.Φ j') σ (Set.Icc 0 T) (u + h) (ε' * sgn) :=
    slope_ratio ((Metric.isOpen_ball.inter Metric.isOpen_ball).connectedComponentIn)
      huhmem (hσ.cont _ huhmem) (mem_connectedComponentIn ⟨hx'S₁, hx'S₂⟩)
      hrel' hslope₁
  refine ⟨rfl, h21, ?_⟩
  rw [h22, hratio, mul_comm sgn ε']
  exact hslope₂

/-- **The stepper follows the trajectory for all steps** below the margin threshold. -/
theorem stepper_follows {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ)
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 T) 0 1) :
    ∀ k : ℕ, (k : ℝ) * h ≤ T →
      ((A.step2)^[k] (h, σ 0, 1)).1 = h ∧
      ((A.step2)^[k] (h, σ 0, 1)).2.1 = σ ((k : ℝ) * h) ∧
      SlopeAt (A.Φ (A.sel (σ ((k : ℝ) * h)))) σ (Set.Icc 0 T) ((k : ℝ) * h)
        (((A.step2)^[k] (h, σ 0, 1)).2.2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, ?_, ?_⟩
    · change σ 0 = σ ((0 : ℕ) * h)
      norm_num
    · change SlopeAt (A.Φ (A.sel (σ ((0 : ℕ) * h)))) σ (Set.Icc 0 T)
        ((0 : ℕ) * h) (1 : ℝ)
      norm_num
      exact hslope0
  | succ k ih =>
    intro hkT
    have hkh : (k : ℝ) * h ≤ T := by
      push_cast at hkT
      nlinarith [hh0.le, Nat.cast_nonneg (α := ℝ) k]
    have hk0 : 0 ≤ (k : ℝ) * h := by positivity
    have hkh1 : (k : ℝ) * h + h ≤ T := by
      push_cast at hkT
      linarith
    obtain ⟨ih1, ih2, ih3⟩ := ih hkh
    have hstate : (A.step2)^[k] (h, σ 0, 1)
        = (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, 1)).2.2) := by
      refine Prod.ext ih1 (Prod.ext ih2 rfl)
    obtain ⟨hs1, hs2, hs3⟩ := step_follows A hσ hm hbound hrad hh0 hsmall
      hk0 hkh1 ih3
    have hiter : (A.step2)^[k + 1] (h, σ 0, 1)
        = A.step2 (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, 1)).2.2) := by
      rw [Function.iterate_succ_apply', hstate]
    have hcast : ((k : ℝ) + 1) * h = (k : ℝ) * h + h := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hiter]
      exact hs1
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs2
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs3

/-- **Stepper stabilization**: for a trajectory with unit initial chart slope, the
stepper approximants eventually equal the trajectory endpoint. -/
theorem flowApprox_eq {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (A : Atlas q) {σ : ℝ → ℂ} {t : ℝ} (ht : 0 < t)
    (hσ : IsTrajOn q σ (Set.Icc 0 t))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 t) 0 1) :
    ∃ N : ℕ, ∀ n ≥ N, A.flowApprox n (t, σ 0) = σ t := by
  have hreg : ∀ v ∈ Set.Icc 0 t, 0 < (σ v).im ∧ q (σ v) ≠ 0 := fun v hv =>
    traj_regular hσ hv
  have hqcont : ContinuousOn (fun v => ‖q (σ v)‖) (Set.Icc 0 t) := by
    refine ContinuousOn.norm (hq.continuousOn.comp hσ.cont ?_)
    exact fun v hv => (hreg v hv).1
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, Set.left_mem_Icc.mpr ht.le⟩ hqcont
  set m : ℝ := ‖q (σ v₀)‖ with hmdef
  have hm : 0 < m := norm_pos_iff.mpr (hreg v₀ hv₀mem).2
  have hbound : ∀ v ∈ Set.Icc 0 t, m ≤ ‖q (σ v)‖ := fun v hv => hv₀min hv
  obtain ⟨J, hJ⟩ := sel_bound A hσ.cont hreg
  obtain ⟨ρ, hρ, hρle⟩ := atlas_radius_min A J
  have hrad : ∀ v ∈ Set.Icc 0 t, ρ ≤ A.r (A.sel (σ v)) := by
    intro v hv
    exact hρle _ (hJ v hv) (A.sel_spec (hreg v hv).1 (hreg v hv).2).1
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt m⁻¹ * t / ρ)
  refine ⟨N, fun n hn => ?_⟩
  set h : ℝ := t / (n + 1) with hhdef
  have hnn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh0 : 0 < h := by
    rw [hhdef]
    positivity
  have hsmall : Real.sqrt m⁻¹ * h < ρ := by
    have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : Real.sqrt m⁻¹ * t / ρ < (n : ℝ) + 1 := by linarith
    have h2 : Real.sqrt m⁻¹ * t < ρ * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hρ] at h1
      linarith
    rw [hhdef, ← mul_div_assoc, div_lt_iff₀ hnn]
    linarith
  have hth : ((n + 1 : ℕ) : ℝ) * h = t := by
    rw [hhdef]
    push_cast
    field_simp
  obtain ⟨-, hpos, -⟩ := stepper_follows A hσ hm hbound hrad hh0 hsmall hslope0
    (n + 1) (le_of_eq hth)
  rw [hth] at hpos
  exact hpos

/-- **The measurable flow candidate follows the trajectory**: at a positive time with a
trajectory of unit initial chart slope, the flow equals the trajectory endpoint. -/
theorem flow_eq_traj {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (A : Atlas q) {σ : ℝ → ℂ} {t : ℝ} (ht : 0 < t)
    (hσ : IsTrajOn q σ (Set.Icc 0 t))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 t) 0 1) :
    A.flow t (σ 0) = σ t := by
  classical
  obtain ⟨N, hN⟩ := flowApprox_eq hq A ht hσ hslope0
  have hconv : Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds (σ t)) := by
    refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
    exact fun n hn => hN n hn
  have hex : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds L) := ⟨σ t, hconv⟩
  rw [Atlas.flow, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec hconv

/-- The stepper move conjugated by simultaneous time-and-sign reversal. -/
theorem step2_neg {q : ℂ → ℂ} (A : Atlas q) (p : ℝ × ℂ × ℝ) :
    A.step2 (-p.1, p.2.1, -p.2.2)
      = (-(A.step2 p).1, (A.step2 p).2.1, -(A.step2 p).2.2) := by
  have harg : ((-p.2.2 * -p.1 : ℝ) : ℂ) = ((p.2.2 * p.1 : ℝ) : ℂ) := by
    push_cast
    ring
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ))
      = Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((p.2.2 * p.1 : ℝ) : ℂ))
    rw [harg]
  · change (-p.2.2) * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ)))))
        (Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ))))
      * (deriv (A.Φ (A.sel p.2.1)) (Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ))))⁻¹).re = _
    rw [harg, neg_mul]
    rfl

/-- The stepper iterate conjugated by time-and-sign reversal. -/
theorem step2_iterate_neg {q : ℂ → ℂ} (A : Atlas q) (k : ℕ) :
    ∀ p : ℝ × ℂ × ℝ, (A.step2)^[k] (-p.1, p.2.1, -p.2.2)
      = (-((A.step2)^[k] p).1, ((A.step2)^[k] p).2.1, -((A.step2)^[k] p).2.2) := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step2_neg,
      ih (A.step2 p)]

/-- The stepper follows the trajectory for any initial chart slope. -/
theorem stepper_follows_gen {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ) {s₀ : ℝ}
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 T) 0 s₀) :
    ∀ k : ℕ, (k : ℝ) * h ≤ T →
      ((A.step2)^[k] (h, σ 0, s₀)).1 = h ∧
      ((A.step2)^[k] (h, σ 0, s₀)).2.1 = σ ((k : ℝ) * h) ∧
      SlopeAt (A.Φ (A.sel (σ ((k : ℝ) * h)))) σ (Set.Icc 0 T) ((k : ℝ) * h)
        (((A.step2)^[k] (h, σ 0, s₀)).2.2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, ?_, ?_⟩
    · change σ 0 = σ ((0 : ℕ) * h)
      norm_num
    · change SlopeAt (A.Φ (A.sel (σ ((0 : ℕ) * h)))) σ (Set.Icc 0 T) ((0 : ℕ) * h) s₀
      norm_num
      exact hslope0
  | succ k ih =>
    intro hkT
    have hkh : (k : ℝ) * h ≤ T := by
      push_cast at hkT
      nlinarith [hh0.le, Nat.cast_nonneg (α := ℝ) k]
    have hk0 : 0 ≤ (k : ℝ) * h := by positivity
    have hkh1 : (k : ℝ) * h + h ≤ T := by
      push_cast at hkT
      linarith
    obtain ⟨ih1, ih2, ih3⟩ := ih hkh
    have hstate : (A.step2)^[k] (h, σ 0, s₀)
        = (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, s₀)).2.2) :=
      Prod.ext ih1 (Prod.ext ih2 rfl)
    obtain ⟨hs1, hs2, hs3⟩ := step_follows A hσ hm hbound hrad hh0 hsmall
      hk0 hkh1 ih3
    have hiter : (A.step2)^[k + 1] (h, σ 0, s₀)
        = A.step2 (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, s₀)).2.2) := by
      rw [Function.iterate_succ_apply', hstate]
    have hcast : ((k : ℝ) + 1) * h = (k : ℝ) * h + h := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hiter]
      exact hs1
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs2
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs3

/-- **Negative-time stabilization**: for a backward trajectory with slope `−1` in its
initial chart the stepper approximants at negative time eventually equal its endpoint. -/
theorem flowApprox_eq_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {σ : ℝ → ℂ} {t : ℝ} (ht : t < 0) (hσ : IsTrajOn q σ (Set.Icc 0 (-t)))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (-t)) 0 (-1)) :
    ∃ N : ℕ, ∀ n ≥ N, A.flowApprox n (t, σ 0) = σ (-t) := by
  have ht' : 0 < -t := by linarith
  have hreg : ∀ v ∈ Set.Icc 0 (-t), 0 < (σ v).im ∧ q (σ v) ≠ 0 := fun v hv =>
    traj_regular hσ hv
  have hqcont : ContinuousOn (fun v => ‖q (σ v)‖) (Set.Icc 0 (-t)) := by
    refine ContinuousOn.norm (hq.continuousOn.comp hσ.cont ?_)
    exact fun v hv => (hreg v hv).1
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, Set.left_mem_Icc.mpr ht'.le⟩ hqcont
  set m : ℝ := ‖q (σ v₀)‖ with hmdef
  have hm : 0 < m := norm_pos_iff.mpr (hreg v₀ hv₀mem).2
  have hbound : ∀ v ∈ Set.Icc 0 (-t), m ≤ ‖q (σ v)‖ := fun v hv => hv₀min hv
  obtain ⟨J, hJ⟩ := sel_bound A hσ.cont hreg
  obtain ⟨ρ, hρ, hρle⟩ := atlas_radius_min A J
  have hrad : ∀ v ∈ Set.Icc 0 (-t), ρ ≤ A.r (A.sel (σ v)) := fun v hv =>
    hρle _ (hJ v hv) (A.sel_spec (hreg v hv).1 (hreg v hv).2).1
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt m⁻¹ * (-t) / ρ)
  refine ⟨N, fun n hn => ?_⟩
  set ĥ : ℝ := -t / (n + 1) with hhdef
  have hnn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh0 : 0 < ĥ := by
    rw [hhdef]
    positivity
  have hsmall : Real.sqrt m⁻¹ * ĥ < ρ := by
    have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : Real.sqrt m⁻¹ * (-t) / ρ < (n : ℝ) + 1 := by linarith
    have h2 : Real.sqrt m⁻¹ * (-t) < ρ * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hρ] at h1
      linarith
    rw [hhdef, ← mul_div_assoc, div_lt_iff₀ hnn]
    linarith
  have hth : ((n + 1 : ℕ) : ℝ) * ĥ = -t := by
    rw [hhdef]
    push_cast
    field_simp
  obtain ⟨-, hpos, -⟩ := stepper_follows_gen A hσ hm hbound hrad hh0 hsmall
    hslope0 (n + 1) (le_of_eq hth)
  rw [hth] at hpos
  have hneg : (t / ((n : ℝ) + 1), σ 0, (1 : ℝ)) = (-ĥ, σ 0, -(-1 : ℝ)) := by
    rw [hhdef]
    refine Prod.ext (by ring) (Prod.ext rfl (by norm_num))
  calc A.flowApprox n (t, σ 0)
      = ((A.step2)^[n + 1] (t / ((n : ℝ) + 1), σ 0, (1 : ℝ))).2.1 := rfl
    _ = ((A.step2)^[n + 1] (-ĥ, σ 0, -(-1 : ℝ))).2.1 := by rw [hneg]
    _ = ((A.step2)^[n + 1] (ĥ, σ 0, (-1 : ℝ))).2.1 := by
        rw [show ((-ĥ : ℝ), σ 0, -(-1 : ℝ))
          = (-(ĥ, σ 0, (-1 : ℝ)).1, (ĥ, σ 0, (-1 : ℝ)).2.1,
            -(ĥ, σ 0, (-1 : ℝ)).2.2) from rfl,
          step2_iterate_neg A (n + 1) (ĥ, σ 0, (-1 : ℝ))]
    _ = σ (-t) := hpos

/-- The measurable flow follows the backward trajectory at negative times. -/
theorem flow_eq_traj_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {σ : ℝ → ℂ} {t : ℝ} (ht : t < 0) (hσ : IsTrajOn q σ (Set.Icc 0 (-t)))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (-t)) 0 (-1)) :
    A.flow t (σ 0) = σ (-t) := by
  classical
  obtain ⟨N, hN⟩ := flowApprox_eq_neg hq A ht hσ hslope0
  have hconv : Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds (σ (-t))) := by
    refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
    exact fun n hn => hN n hn
  have hex : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds L) := ⟨σ (-t), hconv⟩
  rw [Atlas.flow, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec hconv

/-- The **two-sided regular set**: points with coherently oriented vertical trajectories
of both orientations for every time horizon, in the stepper's initial chart. -/
def good (q : ℂ → ℂ) (A : Atlas q) : Set ℂ :=
  {z | 0 < z.im ∧ q z ≠ 0 ∧
    (∀ T, 0 < T → ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1) ∧
    (∀ T, 0 < T → ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 (-1))}

/-- On the two-sided regular set the flow at positive times is realized by a coherently
oriented trajectory. -/
theorem flow_follows_pos {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : 0 < t) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 t) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 ∧ A.flow t z = σ t := by
  obtain ⟨σ, hz0, hσ, hslope⟩ := hz.2.2.1 t ht
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  have hslope' : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 t) 0 1 := by
    rw [hz0]
    exact hslope
  rw [← hz0]
  exact flow_eq_traj hq A ht hσ hslope'

/-- On the two-sided regular set the flow at negative times is realized by a reversely
oriented trajectory. -/
theorem flow_follows_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : t < 0) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (-t)) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (-t)) 0 (-1) ∧ A.flow t z = σ (-t) := by
  obtain ⟨σ, hz0, hσ, hslope⟩ := hz.2.2.2 (-t) (by linarith)
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  have hslope' : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (-t)) 0 (-1) := by
    rw [hz0]
    exact hslope
  rw [← hz0]
  exact flow_eq_traj_neg hq A ht hσ hslope'

/-- The stepper move fixes regular points at step size zero. -/
theorem step2_zero {q : ℂ → ℂ} (A : Atlas q) {z : ℂ} (hz : 0 < z.im)
    (hq0 : q z ≠ 0) (s : ℝ) : A.step2 (0, z, s) = (0, z, s) := by
  obtain ⟨hact, hmem⟩ := A.sel_spec hz hq0
  set j : ℕ := A.sel z with hjdef
  have hmem2 : z ∈ Metric.ball (A.c j) (2 * A.r j) :=
    Metric.ball_subset_ball (by linarith [A.hr j hact]) hmem
  have harg : A.mchart j z + ((s * 0 : ℝ) : ℂ) = A.Φ j z := by
    rw [A.mchart_eq hact hmem2]
    push_cast
    ring
  have hex : ∃ a ∈ Metric.ball (A.c j) (2 * A.r j), A.Φ j a = A.Φ j z :=
    ⟨z, hmem2, rfl⟩
  have hinv : Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
      (A.mchart j z + ((s * 0 : ℝ) : ℂ)) = z := by
    rw [harg]
    exact (A.hinj j hact) (Function.invFunOn_mem hex) hmem2 (Function.invFunOn_eq hex)
  have hd : deriv (A.Φ j) z ≠ 0 := by
    intro h0
    apply hq0
    have hsq := A.hsq j hact z hmem2
    rw [h0] at hsq
    simpa using hsq.symm
  refine Prod.ext rfl (Prod.ext hinv ?_)
  change s * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) (A.mchart j z + ((s * 0 : ℝ) : ℂ)))))
      (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
      (A.mchart j z + ((s * 0 : ℝ) : ℂ))))
    * (deriv (A.Φ j) (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
      (A.mchart j z + ((s * 0 : ℝ) : ℂ))))⁻¹).re = s
  rw [hinv, mul_inv_cancel₀ hd, Complex.one_re, mul_one]

/-- The flow fixes regular points at time zero. -/
theorem flow_zero {q : ℂ → ℂ} (A : Atlas q) {z : ℂ} (hz : 0 < z.im)
    (hq0 : q z ≠ 0) : A.flow 0 z = z := by
  classical
  have happrox : ∀ n : ℕ, A.flowApprox n ((0 : ℝ), z) = z := by
    intro n
    have hstep : ∀ k : ℕ, (A.step2)^[k] ((0 : ℝ) / (n + 1), z, 1)
        = ((0 : ℝ) / (n + 1), z, (1 : ℝ)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih,
          show ((0 : ℝ) / (n + 1), z, (1 : ℝ)) = ((0 : ℝ), z, (1 : ℝ)) by norm_num,
          step2_zero A hz hq0 1]
    change ((A.step2)^[n + 1] ((0 : ℝ) / (n + 1), z, 1)).2.1 = z
    rw [hstep (n + 1)]
  have hconv : Filter.Tendsto (fun n => A.flowApprox n ((0 : ℝ), z)) Filter.atTop
      (nhds z) := by
    refine tendsto_atTop_of_eventually_const (i₀ := 0) ?_
    exact fun n _ => happrox n
  have hex : ∃ L, Filter.Tendsto (fun n => A.flowApprox n ((0 : ℝ), z)) Filter.atTop
      (nhds L) := ⟨z, hconv⟩
  rw [Atlas.flow, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec hconv

/-- **Flow evaluation along the whole forward window**: on the two-sided regular set the
flow restricted to `[0, t]` is a coherently oriented trajectory. -/
theorem flow_traj_eval_pos {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : 0 < t) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 t) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 ∧
      ∀ u ∈ Set.Icc 0 t, A.flow u z = σ u := by
  obtain ⟨σ, hz0, hσ, hslope, -⟩ := flow_follows_pos hq A hz ht
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0, flow_zero A hz.1 hz.2.1, hz0]
  · have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
      traj_mono hσ (Set.Icc_subset_Icc le_rfl hu.2)
    have hslopeu : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 u) 0 1 := by
      rw [hz0]
      have h := hslope
      rw [SlopeAt] at h ⊢
      exact h.filter_mono (nhdsWithin_mono 0 (Set.Icc_subset_Icc le_rfl hu.2))
    rw [← hz0]
    exact flow_eq_traj hq A h0 hσu hslopeu

/-- **Flow evaluation along the whole backward window**: on the two-sided regular set
the flow at negative times is the reversely oriented trajectory. -/
theorem flow_traj_eval_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : 0 < t) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 t) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 (-1) ∧
      ∀ u ∈ Set.Icc 0 t, A.flow (-u) z = σ u := by
  obtain ⟨σ, hz0, hσ, hslope, -⟩ := flow_follows_neg hq A hz
    (show -t < 0 by linarith)
  rw [neg_neg] at hσ hslope
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0, neg_zero, flow_zero A hz.1 hz.2.1, hz0]
  · have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
      traj_mono hσ (Set.Icc_subset_Icc le_rfl hu.2)
    have hslopeu : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 u) 0 (-1) := by
      rw [hz0]
      have h := hslope
      rw [SlopeAt] at h ⊢
      exact h.filter_mono (nhdsWithin_mono 0 (Set.Icc_subset_Icc le_rfl hu.2))
    have hnu : -u < 0 := by linarith
    have hσu' : IsTrajOn q σ (Set.Icc 0 (- -u)) := by
      rw [neg_neg]
      exact hσu
    have hslopeu' : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (- -u)) 0 (-1) := by
      rw [neg_neg]
      exact hslopeu
    have := flow_eq_traj_neg hq A hnu hσu' hslopeu'
    rw [neg_neg] at this
    rw [← hz0]
    exact this

/-- A not identically vanishing holomorphic differential has isolated zeros on the
upper half plane. -/
theorem zeros_isolated {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0) {x : ℂ} (hx : 0 < x.im) :
    ∀ᶠ w in nhdsWithin x {x}ᶜ, q w ≠ 0 := by
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpre : IsPreconnected {z : ℂ | 0 < z.im} := by
    have hconv : Convex ℝ {z : ℂ | 0 < z.im} := by
      intro a ha b hb s t hs ht hst
      have him : (s • a + t • b).im = s * a.im + t * b.im := by
        simp [Complex.add_im]
      rw [Set.mem_ofPred_eq, him]
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · rw [← hs0] at hst ⊢
        simp only [zero_mul, zero_add] at hst ⊢
        rw [hst]
        simpa using hb
      · have ha' : (0 : ℝ) < a.im := ha
        have hb' : (0 : ℝ) < b.im := hb
        nlinarith [mul_pos hs0 ha', mul_nonneg ht hb'.le]
    exact hconv.isPreconnected
  have hAn : AnalyticOnNhd ℂ q {z : ℂ | 0 < z.im} := hq.analyticOnNhd hH
  rcases (hAn x hx).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    obtain ⟨z₀, hz₀, hqz₀⟩ := hq0
    exact hqz₀ (hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hx hzero hz₀)
  · exact hne

/-- The hyperbolic distance is dominated by the euclidean distance divided by the
geometric mean of the heights. -/
theorem hyp_dist_le (z w : UpperHalfPlane) :
    dist z w ≤ dist (z : ℂ) (w : ℂ) / Real.sqrt (z.im * w.im) := by
  rw [UpperHalfPlane.dist_eq]
  have hu : 0 ≤ dist (z : ℂ) (w : ℂ) / (2 * Real.sqrt (z.im * w.im)) := by positivity
  have h1 : Real.arsinh (dist (z : ℂ) (w : ℂ) / (2 * Real.sqrt (z.im * w.im)))
      ≤ dist (z : ℂ) (w : ℂ) / (2 * Real.sqrt (z.im * w.im)) := by
    calc Real.arsinh (dist (z : ℂ) (w : ℂ) / (2 * Real.sqrt (z.im * w.im)))
        ≤ Real.arsinh (Real.sinh (dist (z : ℂ) (w : ℂ)
            / (2 * Real.sqrt (z.im * w.im)))) :=
          Real.arsinh_le_arsinh.mpr (Real.self_le_sinh_iff.mpr hu)
      _ = dist (z : ℂ) (w : ℂ) / (2 * Real.sqrt (z.im * w.im)) := Real.arsinh_sinh _
  calc 2 * Real.arsinh (dist (z : ℂ) (w : ℂ) / (2 * Real.sqrt (z.im * w.im)))
      ≤ 2 * (dist (z : ℂ) (w : ℂ) / (2 * Real.sqrt (z.im * w.im))) := by linarith
    _ = dist (z : ℂ) (w : ℂ) / Real.sqrt (z.im * w.im) := by ring

end RiemannDynamics

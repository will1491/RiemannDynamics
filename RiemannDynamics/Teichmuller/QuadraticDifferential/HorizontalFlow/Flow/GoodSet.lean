/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Flow.Dying

/-!
# The good set, the horizontal pseudodistance, and the symmetrized tiling

Almost-everywhere existence of two-sided trajectories, the horizontal pseudodistance
with its comparison to the flat distance, and the symmetrized tiling of a fundamental
domain used to average the flow.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Window mass bound**: the seeds of a compact set surviving to `a` but not to
`a + ε` carry `|q|`-mass at most twice the pool-ball mass. -/
theorem window_bound {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hqm : Measurable (q : ℂ → ℂ)) (A : Atlas (q : ℂ → ℂ))
    {η : ℝ} (hη : 0 < η)
    (htrack : ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ))
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀)
    {K : Set ℂ} (hKm : MeasurableSet K) (hKH : K ⊆ {z : ℂ | 0 < z.im})
    {Z : Finset ℂ} {δ : ℂ → ℝ} {T a ε Cmass : ℝ}
    (ha : 0 < a) (haT : a ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcapture : ∀ z₀ : ℂ, ∀ hz₀ : 0 < z₀.im, q z₀ = 0 →
      (∃ z ∈ K, ∃ hz : 0 < z.im, dist (⟨z₀, hz₀⟩ : UpperHalfPlane)
        (⟨z, hz⟩ : UpperHalfPlane)
        ≤ (Nat.ceil (T / (η / 2)) : ℝ) + (Nat.ceil (1 / (η / 2)) : ℝ) + 1) →
      z₀ ∈ Z ∧ ∀ w : ℂ,
        C₁ z₀ / (2 ^ M z₀ * 16)
            * min ‖w - z₀‖ (r₀ z₀ / 2) ^ (M z₀ + 2) ≤ ε ^ 2 →
        w ∈ Metric.ball z₀ (δ z₀))
    (hmassB : ∫⁻ v in ⋃ z₀ ∈ Z, Metric.ball z₀ (δ z₀), ‖(q : ℂ → ℂ) v‖ₑ
      ≤ ENNReal.ofReal (Cmass * ε ^ 2)) :
    ∫⁻ w in {z ∈ K | q z ≠ 0 ∧
        (∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 a) ∧
          SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 a) 0 1) ∧
        ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (a + ε)) ∧
          SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (a + ε)) 0 1},
      ‖(q : ℂ → ℂ) w‖ₑ ≤ 2 * ENNReal.ofReal (Cmass * ε ^ 2) := by
  classical
  set W : Set ℂ := {z ∈ K | q z ≠ 0 ∧
      (∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 a) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 a) 0 1) ∧
      ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (a + ε)) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (a + ε)) 0 1} with hWdef
  have hgrid : ∀ N : ℕ, (0 : ℝ) < a / (N + 1) := fun N => by positivity
  have hTeq : ∀ N : ℕ, ((N + 1 : ℕ) : ℝ) * (a / (N + 1)) = a := fun N => by
    push_cast
    field_simp
  have hset : W = K ∩ ({z : ℂ | q z ≠ 0} ∩
      ({z : ℂ | ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 a) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 a) 0 1} ∩
      {z : ℂ | ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (a + ε)) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (a + ε)) 0 1}ᶜ)) := by
    ext z
    simp only [hWdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  have hWm : MeasurableSet W := by
    rw [hset]
    exact hKm.inter (((hqm (measurableSet_singleton 0)).compl).inter
      ((traj_exists_measurable q.holo A ha).inter
        (traj_exists_measurable q.holo A
          (by linarith : (0 : ℝ) < a + ε)).compl))
  set WL : ℕ → Set ℂ := fun N => (W ∩ slegal A (a / (N + 1)) N)
    \ ⋃ N' ∈ Finset.range N, slegal A (a / (N' + 1)) N' with hWLdef
  have hWLm : ∀ N, MeasurableSet (WL N) := by
    intro N
    refine (hWm.inter (slegal_measurable A (hgrid N) N)).diff ?_
    exact MeasurableSet.biUnion (Finset.range N).countable_toSet
      fun N' _ => slegal_measurable A (hgrid N') N'
  have hWLs : ∀ N, WL N ⊆ slegal A (a / (N + 1)) N := fun N z hz => hz.1.2
  have hWLd : Pairwise (Function.onFun Disjoint WL) := by
    intro N N' hNN
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    rcases lt_or_gt_of_ne hNN with hlt | hlt
    · exact hz'.2 (Set.mem_iUnion₂.mpr ⟨N, Finset.mem_range.mpr hlt, hz.1.2⟩)
    · exact hz.2 (Set.mem_iUnion₂.mpr ⟨N', Finset.mem_range.mpr hlt, hz'.1.2⟩)
  have hWLu : (⋃ N, WL N) = W := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨N, hz⟩
      exact hz.1.1
    · intro hz
      have hex : ∃ N : ℕ, z ∈ slegal A (a / (N + 1)) N := by
        obtain ⟨hzK, hq0z, ⟨σ, hσ0, hσtraj, hσS⟩, hno⟩ := hz
        rw [← hσ0] at hσS
        obtain ⟨N, hN⟩ := slegal_of_traj q.holo A ha hσtraj hσS
        rw [hσ0] at hN
        exact ⟨N, hN⟩
      refine ⟨Nat.find hex, ⟨hz, Nat.find_spec hex⟩, ?_⟩
      intro hmem
      obtain ⟨N', hN'mem, hN'⟩ := Set.mem_iUnion₂.mp hmem
      exact Nat.find_min hex (Finset.mem_range.mp hN'mem) hN'
  have hB : ∀ N : ℕ, ∀ z ∈ WL N, pos A (a / (N + 1)) (N + 1) z
      ∈ ⋃ z₀ ∈ Z, Metric.ball z₀ (δ z₀) := by
    intro N z hz
    obtain ⟨hzK, hq0z, hyes, hno⟩ := hz.1.1
    have hzim : 0 < z.im := hKH hzK
    obtain ⟨z₀, hz₀im, hz₀0, hz₀dist, σa, hpre, hreach⟩ :=
      window_endpoint_located hΓ hcc q hq0 A hη htrack hzim hq0z ha haT hε hε1
        hyes hno hdata
    obtain ⟨hz₀Z, hcap⟩ := hcapture z₀ hz₀im hz₀0 ⟨z, hzK, hzim, hz₀dist⟩
    have hball : σa a ∈ Metric.ball z₀ (δ z₀) := hcap (σa a) hreach
    obtain ⟨hσa0, hσatraj, hσaS⟩ := hpre
    have htraj' : IsTrajOn q σa
        (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * (a / (N + 1)))) := by
      rw [hTeq N]
      exact hσatraj
    have hS' : SlopeAt (A.Φ (A.sel z)) σa
        (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * (a / (N + 1)))) 0 1 := by
      rw [hTeq N]
      exact hσaS
    have hposeq : pos A (a / (N + 1)) (N + 1) z = σa a := by
      have h1 := pos_eq_traj A (hgrid N) hz.1.2 hσa0 htraj' hS'
      rw [hTeq N] at h1
      exact h1
    rw [hposeq]
    exact Set.mem_iUnion₂.mpr ⟨z₀, hz₀Z, hball⟩
  calc ∫⁻ w in W, ‖(q : ℂ → ℂ) w‖ₑ
      = ∫⁻ w in ⋃ N, WL N, ‖(q : ℂ → ℂ) w‖ₑ := by rw [hWLu]
    _ ≤ 2 * ∫⁻ w in ⋃ z₀ ∈ Z, Metric.ball z₀ (δ z₀), ‖(q : ℂ → ℂ) w‖ₑ :=
        grid_union_push hqm A ha hWLm hWLs hWLd hB
    _ ≤ 2 * ENNReal.ofReal (Cmass * ε ^ 2) := mul_le_mul_right hmassB 2

/-- **Zeroth window bound**: the seeds of a compact set dying before time `ε` lie in the
pool balls, so their `|q|`-mass is at most the pool-ball mass. -/
theorem window0_bound {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (A : Atlas (q : ℂ → ℂ)) {η : ℝ} (hη : 0 < η)
    (htrack : ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ))
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀)
    {K : Set ℂ} (hKH : K ⊆ {z : ℂ | 0 < z.im})
    {Z : Finset ℂ} {δ : ℂ → ℝ} {T ε Cmass : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcapture : ∀ z₀ : ℂ, ∀ hz₀ : 0 < z₀.im, q z₀ = 0 →
      (∃ z ∈ K, ∃ hz : 0 < z.im, dist (⟨z₀, hz₀⟩ : UpperHalfPlane)
        (⟨z, hz⟩ : UpperHalfPlane)
        ≤ (Nat.ceil (T / (η / 2)) : ℝ) + (Nat.ceil (1 / (η / 2)) : ℝ) + 1) →
      z₀ ∈ Z ∧ ∀ w : ℂ,
        C₁ z₀ / (2 ^ M z₀ * 16)
            * min ‖w - z₀‖ (r₀ z₀ / 2) ^ (M z₀ + 2) ≤ ε ^ 2 →
        w ∈ Metric.ball z₀ (δ z₀))
    (hmassB : ∫⁻ v in ⋃ z₀ ∈ Z, Metric.ball z₀ (δ z₀), ‖(q : ℂ → ℂ) v‖ₑ
      ≤ ENNReal.ofReal (Cmass * ε ^ 2)) :
    ∫⁻ w in {z ∈ K | q z ≠ 0 ∧
        ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 ε) ∧
          SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ε) 0 1},
      ‖(q : ℂ → ℂ) w‖ₑ ≤ ENNReal.ofReal (Cmass * ε ^ 2) := by
  refine le_trans (lintegral_mono_set ?_) hmassB
  rintro z ⟨hzK, hq0z, hno⟩
  have hzim : 0 < z.im := hKH hzK
  obtain ⟨c, σ, hc0, hcε, hσ0, hσ, hσS, hmax⟩ :=
    dying_data q.holo A hzim hq0z hε hno
  obtain ⟨z₀, hz₀im, hz₀0, ⟨u, hu, hunear⟩, hreach⟩ :=
    dying_seed_located hΓ hcc q hq0 hc0 hcε hσ hmax hdata
  rw [hσ0] at hreach
  have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
    traj_mono hσ fun v hv => ⟨hv.1, lt_of_le_of_lt hv.2 hu.2⟩
  have himu : 0 < (σ u).im :=
    (traj_regular hσu (Set.right_mem_Icc.mpr hu.1)).1
  have him0 : 0 < (σ 0).im := (traj_regular hσu (Set.left_mem_Icc.mpr hu.1)).1
  have hd1 : dist (⟨z₀, hz₀im⟩ : UpperHalfPlane)
      (⟨σ u, himu⟩ : UpperHalfPlane) ≤ 1 := by
    refine near_height_dist himu ?_ hz₀im
    rw [norm_sub_rev]
    exact hunear
  have hu1 : u ≤ 1 := le_trans hu.2.le (le_trans hcε hε1)
  have hd2 : dist (⟨σ u, himu⟩ : UpperHalfPlane) (⟨σ 0, him0⟩ : UpperHalfPlane)
      ≤ (Nat.ceil (1 / (η / 2)) : ℝ) := by
    refine le_trans
      (htrack σ u hu.1 hσu u (Set.right_mem_Icc.mpr hu.1) himu him0) ?_
    have hcle : Nat.ceil (u / (η / 2)) ≤ Nat.ceil (1 / (η / 2)) :=
      Nat.ceil_le_ceil (by gcongr)
    exact_mod_cast hcle
  have he0 : (⟨σ 0, him0⟩ : UpperHalfPlane) = ⟨z, hzim⟩ :=
    UpperHalfPlane.ext hσ0
  have hdist : dist (⟨z₀, hz₀im⟩ : UpperHalfPlane) (⟨z, hzim⟩ : UpperHalfPlane)
      ≤ (Nat.ceil (T / (η / 2)) : ℝ) + (Nat.ceil (1 / (η / 2)) : ℝ) + 1 := by
    rw [← he0]
    have htri := dist_triangle (⟨z₀, hz₀im⟩ : UpperHalfPlane)
      (⟨σ u, himu⟩ : UpperHalfPlane) (⟨σ 0, him0⟩ : UpperHalfPlane)
    have hTnn : (0 : ℝ) ≤ (Nat.ceil (T / (η / 2)) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨hz₀Z, hcap⟩ := hcapture z₀ hz₀im hz₀0 ⟨z, hzK, hzim, hdist⟩
  exact Set.mem_iUnion₂.mpr ⟨z₀, hz₀Z, hcap z hreach⟩

/-- **Dying-set mass bound**: over a compact seed set, for every fine enough
subdivision the dying-set mass is at most `n · 2 · Cp · (T/n)²`. -/
theorem dying_mass_bound {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hqm : Measurable (q : ℂ → ℂ)) (A : Atlas (q : ℂ → ℂ))
    {η : ℝ} (hη : 0 < η)
    (htrack : ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ))
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      0 ≤ C₂ z₀ ∧ ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀)
    {K : Set ℂ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKH : K ⊆ {z : ℂ | 0 < z.im}) {T : ℝ} (hT : 0 < T) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
      ∫⁻ w in {z ∈ K | q z ≠ 0 ∧
          ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
            SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1},
        ‖(q : ℂ → ℂ) w‖ₑ
        ≤ (n : ℝ≥0∞) * (2 * ENNReal.ofReal (Cp * (T / n) ^ 2)) := by
  classical
  have hdata' : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      ∀ w ∈ Metric.ball z₀ (r₀ z₀), C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧
        ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀ := fun z₀ h1 h2 =>
    ⟨(hdata z₀ h1 h2).1, (hdata z₀ h1 h2).2.1, (hdata z₀ h1 h2).2.2.2⟩
  obtain ⟨Z, ε₀, Cp, hε₀, hCp, hpool⟩ := pool q hq0 hKc hKne hKH
    ((Nat.ceil (T / (η / 2)) : ℝ) + (Nat.ceil (1 / (η / 2)) : ℝ) + 1) hdata
  have hmin : (0 : ℝ) < min 1 ε₀ := lt_min one_pos hε₀
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (T / min 1 ε₀)
  refine ⟨Cp, hCp, n₀, fun n hn hn1 => ?_⟩
  set ε : ℝ := T / n with hεdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεmin : ε ≤ min 1 ε₀ := by
    rw [div_lt_iff₀ hmin] at hn₀
    have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    rw [hεdef, div_le_iff₀ hnpos]
    nlinarith [mul_le_mul_of_nonneg_right hn' hmin.le]
  have hε1 : ε ≤ 1 := le_trans hεmin (min_le_left _ _)
  have hεε₀ : ε ≤ ε₀ := le_trans hεmin (min_le_right _ _)
  obtain ⟨δ, hcapture, hmassB⟩ := hpool ε hε hεε₀
  have hnε : (n : ℝ) * ε = T := by
    rw [hεdef]
    field_simp
  set W0 : Set ℂ := {z ∈ K | q z ≠ 0 ∧
      ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 ε) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ε) 0 1} with hW0def
  set Wk : ℕ → Set ℂ := fun k => {z ∈ K | q z ≠ 0 ∧
      (∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 ((k : ℝ) * ε)) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ((k : ℝ) * ε)) 0 1) ∧
      ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 ((k : ℝ) * ε + ε)) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ((k : ℝ) * ε + ε)) 0 1} with hWkdef
  have hcover : {z ∈ K | q z ≠ 0 ∧
      ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1}
      ⊆ W0 ∪ ⋃ k ∈ Finset.Icc 1 (n - 1), Wk k := by
    rintro z ⟨hzK, hq0z, hno⟩
    set P : ℕ → Prop := fun k => 0 < k ∧ ∃ σ : ℝ → ℂ, σ 0 = z ∧
      IsTrajOn q σ (Set.Icc 0 ((k : ℝ) * ε)) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ((k : ℝ) * ε)) 0 1 with hPdef
    by_cases hPex : ∃ m, m ≤ n - 1 ∧ P m
    · right
      obtain ⟨m, hm, hPm⟩ := hPex
      have hPk₀ : P (Nat.findGreatest P (n - 1)) := Nat.findGreatest_spec hm hPm
      set k₀ : ℕ := Nat.findGreatest P (n - 1) with hk₀def
      have hk₀1 : 1 ≤ k₀ := hPk₀.1
      have hk₀le : k₀ ≤ n - 1 := Nat.findGreatest_le _
      have hnocert : ¬∃ σ : ℝ → ℂ, σ 0 = z ∧
          IsTrajOn q σ (Set.Icc 0 ((k₀ : ℝ) * ε + ε)) ∧
          SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ((k₀ : ℝ) * ε + ε)) 0 1 := by
        have hcast : (k₀ : ℝ) * ε + ε = ((k₀ + 1 : ℕ) : ℝ) * ε := by
          push_cast
          ring
        rw [hcast]
        by_cases hk₀n : k₀ + 1 ≤ n - 1
        · have hnP := Nat.findGreatest_is_greatest (Nat.lt_succ_self k₀) hk₀n
          intro hcert
          exact hnP ⟨Nat.succ_pos k₀, hcert⟩
        · have hk₀eq : k₀ + 1 = n := by omega
          rw [hk₀eq, show ((n : ℕ) : ℝ) * ε = T from hnε]
          exact hno
      exact Set.mem_iUnion₂.mpr ⟨k₀, Finset.mem_Icc.mpr ⟨hk₀1, hk₀le⟩,
        ⟨hzK, hq0z, hPk₀.2, hnocert⟩⟩
    · left
      refine ⟨hzK, hq0z, ?_⟩
      rintro ⟨σ, hσ0, hσtraj, hσS⟩
      by_cases hn1' : n = 1
      · have hTε : T = ε := by
          rw [hεdef, hn1']
          norm_num
        exact hno ⟨σ, hσ0, by rw [hTε]; exact hσtraj, by rw [hTε]; exact hσS⟩
      · refine hPex ⟨1, by omega, one_pos, σ, hσ0, ?_, ?_⟩
        · rw [show ((1 : ℕ) : ℝ) * ε = ε by push_cast; ring]
          exact hσtraj
        · rw [show ((1 : ℕ) : ℝ) * ε = ε by push_cast; ring]
          exact hσS
  refine le_trans (lintegral_mono_set hcover) ?_
  refine le_trans (lintegral_union_le _ _ _) ?_
  have h0 : ∫⁻ w in W0, ‖(q : ℂ → ℂ) w‖ₑ ≤ ENNReal.ofReal (Cp * ε ^ 2) :=
    window0_bound hΓ hcc q hq0 A hη htrack hdata' hKH hε hε1
      hcapture hmassB
  have hk : ∀ k ∈ Finset.Icc 1 (n - 1), ∫⁻ w in Wk k, ‖(q : ℂ → ℂ) w‖ₑ
      ≤ 2 * ENNReal.ofReal (Cp * ε ^ 2) := by
    intro k hkmem
    obtain ⟨hk1, hkle⟩ := Finset.mem_Icc.mp hkmem
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hka : (0 : ℝ) < (k : ℝ) * ε := by nlinarith
    have hkaT : (k : ℝ) * ε ≤ T := by
      rw [← hnε]
      have h1 : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : k ≤ n)
      nlinarith
    exact window_bound hΓ hcc q hq0 hqm A hη htrack hdata'
      hKc.measurableSet hKH hka hkaT hε hε1 hcapture hmassB
  have hsub : ∫⁻ w in ⋃ k ∈ Finset.Icc 1 (n - 1), Wk k, ‖(q : ℂ → ℂ) w‖ₑ
      ≤ ∑ k ∈ Finset.Icc 1 (n - 1), ∫⁻ w in Wk k, ‖(q : ℂ → ℂ) w‖ₑ := by
    have hconv : (⋃ k ∈ Finset.Icc 1 (n - 1), Wk k)
        = ⋃ k : {x // x ∈ Finset.Icc 1 (n - 1)}, Wk (k : ℕ) := by
      ext v
      simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
    rw [hconv]
    refine le_trans (lintegral_iUnion_le _ _) ?_
    rw [tsum_fintype]
    exact le_of_eq (Finset.sum_coe_sort _
      fun k => ∫⁻ w in Wk k, ‖(q : ℂ → ℂ) w‖ₑ)
  have hksum : ∑ k ∈ Finset.Icc 1 (n - 1), ∫⁻ w in Wk k, ‖(q : ℂ → ℂ) w‖ₑ
      ≤ ((n - 1 : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal (Cp * ε ^ 2)) := by
    refine le_trans (Finset.sum_le_sum hk) ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  refine le_trans (add_le_add h0 (le_trans hsub hksum)) ?_
  have hle2 : ENNReal.ofReal (Cp * ε ^ 2) ≤ 2 * ENNReal.ofReal (Cp * ε ^ 2) :=
    le_mul_of_one_le_left (zero_le _) one_le_two
  have hcast : ((n - 1 : ℕ) : ℝ≥0∞) + 1 = (n : ℝ≥0∞) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ≥0∞) (Nat.sub_add_cancel hn1)
  calc ENNReal.ofReal (Cp * ε ^ 2)
        + ((n - 1 : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal (Cp * ε ^ 2))
      ≤ 2 * ENNReal.ofReal (Cp * ε ^ 2)
        + ((n - 1 : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal (Cp * ε ^ 2)) :=
        add_le_add hle2 le_rfl
    _ = (((n - 1 : ℕ) : ℝ≥0∞) + 1) * (2 * ENNReal.ofReal (Cp * ε ^ 2)) := by
        ring
    _ = (n : ℝ≥0∞) * (2 * ENNReal.ofReal (Cp * ε ^ 2)) := by rw [hcast]

/-- **Dying-set nullity on a compact**: the seeds of a compact set with no unit-slope
trajectory of duration `T` form a volume-null set. -/
theorem dying_null {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hqm : Measurable (q : ℂ → ℂ)) (A : Atlas (q : ℂ → ℂ))
    {η : ℝ} (hη : 0 < η)
    (htrack : ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ))
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      0 ≤ C₂ z₀ ∧ ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀)
    {K : Set ℂ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKH : K ⊆ {z : ℂ | 0 < z.im}) {T : ℝ} (hT : 0 < T) :
    volume {z ∈ K | q z ≠ 0 ∧
      ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1} = 0 := by
  obtain ⟨Cp, hCp, n₀, hbound⟩ := dying_mass_bound hΓ hcc q hq0 hqm A hη
    htrack hdata hKc hKne hKH hT
  set D : Set ℂ := {z ∈ K | q z ≠ 0 ∧
    ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1} with hDdef
  have hmass : ∫⁻ w in D, ‖(q : ℂ → ℂ) w‖ₑ = 0 := by
    have hreal : Filter.Tendsto (fun n : ℕ => 2 * Cp * T ^ 2 / n)
        Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have htend : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal (2 * Cp * T ^ 2 / n))
        Filter.atTop (nhds 0) := by
      have := ENNReal.tendsto_ofReal hreal
      rwa [ENNReal.ofReal_zero] at this
    have htend' : Filter.Tendsto
        (fun n : ℕ => (n : ℝ≥0∞) * (2 * ENNReal.ofReal (Cp * (T / n) ^ 2)))
        Filter.atTop (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ htend
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
        rw [ENNReal.ofReal_ofNat]
      have hn : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by
        rw [ENNReal.ofReal_natCast]
      rw [hn, h2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      field_simp
    refine le_antisymm ?_ (zero_le _)
    refine ge_of_tendsto htend' ?_
    filter_upwards [Filter.eventually_ge_atTop n₀, Filter.eventually_ge_atTop 1]
      with n h1 h2
    exact hbound n h1 h2
  have hDsub : D ⊆ {w : ℂ | ‖(q : ℂ → ℂ) w‖ₑ ≠ 0} := by
    rintro z ⟨-, hq0z, -⟩
    simpa using hq0z
  have hae := (lintegral_eq_zero_iff hqm.enorm).mp hmass
  have hnull : volume.restrict D {w : ℂ | ‖(q : ℂ → ℂ) w‖ₑ ≠ 0} = 0 := by
    have := ae_iff.mp hae
    simpa using this
  refine le_antisymm ?_ (zero_le _)
  calc volume D = volume.restrict D D := by rw [Measure.restrict_apply_self]
    _ ≤ volume.restrict D {w : ℂ | ‖(q : ℂ → ℂ) w‖ₑ ≠ 0} := measure_mono hDsub
    _ = 0 := hnull

/-- **Forward almost-everywhere completeness**: almost every point of the upper half
plane with `q ≠ 0` admits a unit-slope trajectory of every duration. -/
theorem forward_good_ae {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hqm : Measurable (q : ℂ → ℂ)) (A : Atlas (q : ℂ → ℂ))
    {η : ℝ} (hη : 0 < η)
    (htrack : ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ))
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      0 ≤ C₂ z₀ ∧ ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), q z ≠ 0 →
      ∀ T : ℝ, 0 < T → ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1 := by
  have hSm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  rw [ae_restrict_iff' hSm, ae_iff]
  set K : ℕ → Set ℂ := fun m => Metric.closedBall 0 ((m : ℝ) + 1)
    ∩ {z : ℂ | 1 / ((m : ℝ) + 1) ≤ z.im} with hKdef
  have hKc : ∀ m, IsCompact (K m) := fun m =>
    (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  have hKne : ∀ m, (K m).Nonempty := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    refine ⟨Complex.I, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_I]
      linarith
    · change 1 / ((m : ℝ) + 1) ≤ Complex.I.im
      rw [Complex.I_im, div_le_one (by positivity)]
      linarith
  have hKH : ∀ m, K m ⊆ {z : ℂ | 0 < z.im} := fun m z hz => by
    have h1 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    exact lt_of_lt_of_le h1 hz.2
  refine measure_mono_null ?_ (measure_iUnion_null fun m : ℕ =>
    measure_iUnion_null fun j : ℕ =>
      dying_null hΓ hcc q hq0 hqm A hη htrack hdata (hKc m) (hKne m)
        (hKH m) (by positivity : (0 : ℝ) < (j : ℝ) + 1))
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  push Not at hz
  obtain ⟨hzS, hq0z, T, hT, hno⟩ := hz
  have him : 0 < z.im := hzS
  obtain ⟨m₁, hm₁⟩ := exists_nat_ge ‖z‖
  obtain ⟨m₂, hm₂⟩ := exists_nat_ge (1 / z.im)
  have hzK : z ∈ K (max m₁ m₂) := by
    have hc1 : (m₁ : ℝ) ≤ ((max m₁ m₂ : ℕ) : ℝ) := by
      exact_mod_cast le_max_left m₁ m₂
    have hc2 : (m₂ : ℝ) ≤ ((max m₁ m₂ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right m₁ m₂
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    · change 1 / (((max m₁ m₂ : ℕ) : ℝ) + 1) ≤ z.im
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ him] at hm₂
      nlinarith
  obtain ⟨j, hj⟩ := exists_nat_ge T
  have hno' : ¬∃ σ : ℝ → ℂ, σ 0 = z ∧
      IsTrajOn q σ (Set.Icc 0 ((j : ℝ) + 1)) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ((j : ℝ) + 1)) 0 1 := by
    rintro ⟨σ, hσ0, hσtraj, hσS⟩
    have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 ((j : ℝ) + 1)),
        A.Φ (A.sel z) (σ v)
        = A.Φ (A.sel z) (σ 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσS
    rw [nhdsWithin_left (by linarith : T ≤ (j : ℝ) + 1) hT] at h1
    exact hno σ hσ0
      (traj_mono hσtraj (Set.Icc_subset_Icc le_rfl (by linarith))) h1
  exact Set.mem_iUnion.mpr ⟨max m₁ m₂,
    Set.mem_iUnion.mpr ⟨j, hzK, hq0z, hno'⟩⟩

open Classical in
/-- **The mirror atlas**: the same margin atlas with reversed development orientation on
the active charts. -/
noncomputable def mirrorAtlas {q : ℂ → ℂ} (A : Atlas q) : Atlas q where
  c := A.c
  r := A.r
  Φ := fun j => if A.active j then fun w => -(A.Φ j w) else id
  active := A.active
  hr := A.hr
  hH := A.hH
  hne := A.hne
  hd := fun j hj => by
    rw [if_pos hj]
    exact (A.hd j hj).neg
  hinj := fun j hj => by
    rw [if_pos hj]
    intro x hx y hy hxy
    exact A.hinj j hj hx hy (neg_injective hxy)
  hsq := fun j hj w hw => by
    rw [if_pos hj]
    have h1 : deriv (fun v => -(A.Φ j v)) w = -deriv (A.Φ j) w := deriv.neg
    rw [h1, neg_sq]
    exact A.hsq j hj w hw
  hcover := A.hcover
  hjunk := fun j hj => if_neg hj

/-- The mirror atlas has the same chart selector. -/
theorem mirror_sel {q : ℂ → ℂ} (A : Atlas q) :
    (mirrorAtlas A).sel = A.sel := rfl

/-- On active indices the mirror chart is the negated chart. -/
theorem mirror_Φ {q : ℂ → ℂ} (A : Atlas q) {j : ℕ} (hj : A.active j) :
    (mirrorAtlas A).Φ j = fun w => -(A.Φ j w) := if_pos hj

/-- **Backward almost-everywhere completeness**: almost every point with `q ≠ 0` admits
a reversely oriented trajectory of every duration, by mirroring the atlas. -/
theorem backward_good_ae {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hqm : Measurable (q : ℂ → ℂ)) (A : Atlas (q : ℂ → ℂ))
    {η : ℝ} (hη : 0 < η)
    (htrack : ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ))
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      0 ≤ C₂ z₀ ∧ ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), q z ≠ 0 →
      ∀ T : ℝ, 0 < T → ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 (-1) := by
  have hfwd := forward_good_ae hΓ hcc q hq0 hqm (mirrorAtlas A) hη htrack hdata
  have hSm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  filter_upwards [hfwd, ae_restrict_mem hSm] with z hz hzS
  intro hq0z T hT
  obtain ⟨σ, hσ0, hσtraj, hσS⟩ := hz hq0z T hT
  refine ⟨σ, hσ0, hσtraj, ?_⟩
  obtain ⟨hact, -⟩ := A.sel_spec hzS hq0z
  rw [mirror_sel, mirror_Φ A hact] at hσS
  have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 T),
      -(A.Φ (A.sel z) (σ v))
        = -(A.Φ (A.sel z) (σ 0)) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσS
  filter_upwards [h1] with v hv
  show A.Φ (A.sel z) (σ v)
    = A.Φ (A.sel z) (σ 0) + ((-1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
  push_cast at hv ⊢
  linear_combination -hv

/-- **The full-measure two-sided regular set**: almost every point of the upper half
plane lies in the good set of the atlas. -/
theorem good_ae {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A := by
  obtain ⟨η, hη, htrack⟩ := track_unif hΓ hcc q hq0
  have hchoice : ∀ z₀ : ℂ, ∃ (Mz : ℕ) (rz C1z C2z : ℝ), 0 < z₀.im → q z₀ = 0 →
      0 < rz ∧ 0 < C1z ∧ 0 ≤ C2z ∧ ∀ w ∈ Metric.ball z₀ rz,
        C1z * ‖w - z₀‖ ^ Mz ≤ ‖q w‖ ∧ ‖q w‖ ≤ C2z * ‖w - z₀‖ ^ Mz := by
    intro z₀
    by_cases h : 0 < z₀.im ∧ q z₀ = 0
    · obtain ⟨Mz, rz, C1z, C2z, hr, h1, h2, -, hb⟩ :=
        zero_order_bounds q.holo hq0 h.1
      exact ⟨Mz, rz, C1z, C2z, fun _ _ => ⟨hr, h1, h2.le, hb⟩⟩
    · exact ⟨0, 1, 1, 1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose M r₀ C₁ C₂ hdata using hchoice
  have hfwd := forward_good_ae hΓ hcc q hq0 q.measurable A hη htrack
    (fun z₀ h1 h2 => hdata z₀ h1 h2)
  have hbwd := backward_good_ae hΓ hcc q hq0 q.measurable A hη htrack
    (fun z₀ h1 h2 => hdata z₀ h1 h2)
  have hne := q.ae_ne_zero hq0
  have hSm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  filter_upwards [hfwd, hbwd, hne, ae_restrict_mem hSm] with z h1 h2 h3 h4
  exact ⟨h4, h3, h1 h3, h2 h3⟩

/-- The **horizontal pseudodistance**: the infimum of the horizontal variation over all
connecting flat paths. -/
noncomputable def horizontalDist (q : ℂ → ℂ) (a b : ℂ) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → ℂ) (_ : IsFlatPath γ a b), horizontalVariation q γ

/-- The horizontal pseudodistance is bounded by the horizontal variation of any
connecting flat path. -/
theorem horizontalDist_le {q : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℂ} (hγ : IsFlatPath γ a b) :
    horizontalDist q a b ≤ horizontalVariation q γ :=
  iInf₂_le γ hγ

/-- The horizontal pseudodistance is bounded by the flat distance. -/
theorem horizontalDist_le_qdDist (q : ℂ → ℂ) (a b : ℂ) :
    horizontalDist q a b ≤ qdDist q a b := by
  refine iInf₂_mono fun γ hγ => ?_
  exact horizontalVariation_le_qdLength q γ

/-- **Unit vertical speed, complex form**: at an interior time the trajectory has a
derivative whose `q`-square is `-1`. -/
theorem traj_deriv_qsq {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ} {t : ℝ}
    (hσ : IsTrajOn q σ s) (ht : t ∈ s) (hnhds : s ∈ nhds t) :
    ∃ d : ℂ, HasDerivAt σ d t ∧ q (σ t) * d ^ 2 = -1 := by
  obtain ⟨d, hd, -⟩ := traj_hasDerivAt hσ ht hnhds
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hσ.chart t ht
  rw [nhdsWithin_eq_nhds.mpr hnhds] at hev
  have hq0 : q (σ t) ≠ 0 := hUne _ hpU
  have hΦat : DifferentiableAt ℂ Φ (σ t) :=
    hΦd.differentiableAt (hUo.mem_nhds hpU)
  have haff : HasDerivAt (Φ ∘ σ) 1 t := by
    have hF : HasDerivAt (fun z : ℂ => Φ (σ t) + (z - (t : ℂ))) 1 (t : ℂ) := by
      simpa using (((hasDerivAt_id (t : ℂ)).sub_const (t : ℂ)).const_add
        (Φ (σ t)))
    have h1 : HasDerivAt (fun u : ℝ => Φ (σ t) + ((u : ℂ) - (t : ℂ))) 1 t :=
      hF.comp_ofReal
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with u hu
    change Φ (σ u) = Φ (σ t) + ((u : ℂ) - (t : ℂ))
    rw [hu.2]
    push_cast
    ring
  have hchain : HasDerivAt (Φ ∘ σ) (deriv Φ (σ t) * d) t := by
    have hΦat' : HasDerivAt Φ (deriv Φ (σ t)) (σ t) := hΦat.hasDerivAt
    exact HasDerivAt.comp (h := σ) t hΦat' hd
  have hone : deriv Φ (σ t) * d = 1 := hchain.unique haff
  refine ⟨d, hd, ?_⟩
  have hsq := hΦsq _ hpU
  have h4 : (deriv Φ (σ t) * d) ^ 2 = 1 := by rw [hone]; norm_num
  have h5 : deriv Φ (σ t) ^ 2 * d ^ 2 = 1 := by
    rw [← mul_pow]
    exact h4
  rw [hsq] at h5
  linear_combination -h5

/-- **Affine reparametrization of absolute continuity**: precomposition with a
positively sloped affine map carries absolute continuity on the image interval to the
parameter interval. -/
theorem acOn_comp_affine {X : Type*} [PseudoMetricSpace X] {f : ℝ → X}
    {c d a b : ℝ} (hc : 0 < c)
    (hf : AbsolutelyContinuousOnInterval f (c * a + d) (c * b + d)) :
    AbsolutelyContinuousOnInterval (fun t => f (c * t + d)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hf ε hε
  refine ⟨δ / c, by positivity, ?_⟩
  rintro ⟨n, I⟩ hE hlen
  have hmin : ∀ x y : ℝ, min (c * x + d) (c * y + d) = c * min x y + d := by
    intro x y
    rcases le_total x y with h | h
    · rw [min_eq_left (by nlinarith), min_eq_left h]
    · rw [min_eq_right (by nlinarith), min_eq_right h]
  have hmax : ∀ x y : ℝ, max (c * x + d) (c * y + d) = c * max x y + d := by
    intro x y
    rcases le_total x y with h | h
    · rw [max_eq_right (by nlinarith), max_eq_right h]
    · rw [max_eq_left (by nlinarith), max_eq_left h]
  have hmemIoc : ∀ s x y : ℝ, s ∈ Set.uIoc (c * x + d) (c * y + d) →
      (s - d) / c ∈ Set.uIoc x y := by
    intro s x y hs
    rw [Set.uIoc] at hs ⊢
    have h1 : min (c * x + d) (c * y + d) < s := hs.1
    have h2 : s ≤ max (c * x + d) (c * y + d) := hs.2
    rw [hmin] at h1
    rw [hmax] at h2
    constructor
    · change min x y < (s - d) / c
      rw [lt_div_iff₀ hc]
      nlinarith
    · change (s - d) / c ≤ max x y
      rw [div_le_iff₀ hc]
      nlinarith
  have hmemIcc : ∀ t : ℝ, t ∈ Set.uIcc a b →
      c * t + d ∈ Set.uIcc (c * a + d) (c * b + d) := by
    intro t ht
    rw [Set.uIcc] at ht ⊢
    obtain ⟨h1, h2⟩ := ht
    constructor
    · change min (c * a + d) (c * b + d) ≤ c * t + d
      rw [hmin]
      have h3 : (min a b : ℝ) ≤ t := h1
      nlinarith
    · change c * t + d ≤ max (c * a + d) (c * b + d)
      rw [hmax]
      have h3 : t ≤ (max a b : ℝ) := h2
      nlinarith
  have hE' : ((n, fun i => (c * (I i).1 + d, c * (I i).2 + d)) :
      ℕ × (ℕ → ℝ × ℝ))
      ∈ AbsolutelyContinuousOnInterval.disjWithin (c * a + d) (c * b + d) := by
    obtain ⟨hEm, hEd⟩ := hE
    constructor
    · intro i hi
      exact ⟨hmemIcc _ (hEm i hi).1, hmemIcc _ (hEm i hi).2⟩
    · intro i hi j hj hij
      have hdis := hEd hi hj hij
      rw [Function.onFun, Set.disjoint_left]
      intro s hs₁ hs₂
      have h1 := hmemIoc s _ _ hs₁
      have h2 := hmemIoc s _ _ hs₂
      exact Set.disjoint_left.mp hdis h1 h2
  have hlen' : ∑ i ∈ Finset.range n,
      dist (c * (I i).1 + d) (c * (I i).2 + d) < δ := by
    have heq : ∀ i, dist (c * (I i).1 + d) (c * (I i).2 + d)
        = c * dist (I i).1 (I i).2 := by
      intro i
      rw [Real.dist_eq, Real.dist_eq,
        show c * (I i).1 + d - (c * (I i).2 + d)
          = c * ((I i).1 - (I i).2) by ring,
        abs_mul, abs_of_pos hc]
    rw [Finset.sum_congr rfl fun i _ => heq i, ← Finset.mul_sum]
    rw [lt_div_iff₀ hc] at hlen
    nlinarith [hlen]
  have := hδ' _ hE' hlen'
  simpa using this

/-- Clamping below is a contraction of the line. -/
theorem dist_min_le (b x y : ℝ) : dist (min x b) (min y b) ≤ dist x y := by
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x b with hx | hx <;> rcases le_total y b with hy | hy <;>
    rw [abs_le] <;> constructor <;>
    simp [hx, hy] <;>
    cases abs_cases (x - y) <;> linarith

/-- Clamping above is a contraction of the line. -/
theorem dist_max_le (b x y : ℝ) : dist (max x b) (max y b) ≤ dist x y := by
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x b with hx | hx <;> rcases le_total y b with hy | hy <;>
    rw [abs_le] <;> constructor <;>
    simp [hx, hy] <;>
    cases abs_cases (x - y) <;> linarith

/-- The lower clamp shrinks signed intervals. -/
theorem uIoc_min_subset (b x y : ℝ) :
    Set.uIoc (min x b) (min y b) ⊆ Set.uIoc x y := by
  intro s hs
  rw [Set.uIoc] at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  rcases le_total b (min x y) with hb | hb
  · exfalso
    rw [min_eq_right (le_trans hb (min_le_left x y)),
      min_eq_right (le_trans hb (min_le_right x y))] at hs1 hs2
    simp at hs1 hs2
    linarith
  · constructor
    · have heq : min (min x b) (min y b) = min x y := by
        rw [min_min_min_comm, min_self, min_eq_left hb]
      rw [heq] at hs1
      exact hs1
    · exact le_trans hs2 (max_le_max (min_le_left x b) (min_le_left y b))

/-- The upper clamp shrinks signed intervals. -/
theorem uIoc_max_subset (b x y : ℝ) :
    Set.uIoc (max x b) (max y b) ⊆ Set.uIoc x y := by
  intro s hs
  rw [Set.uIoc] at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  rcases le_total (max x y) b with hb | hb
  · exfalso
    rw [max_eq_right (le_trans (le_max_left x y) hb),
      max_eq_right (le_trans (le_max_right x y) hb)] at hs1 hs2
    simp at hs1 hs2
    linarith
  · constructor
    · exact lt_of_le_of_lt (min_le_min (le_max_left x b) (le_max_left y b)) hs1
    · have heq : max (max x b) (max y b) = max x y := by
        rw [max_max_max_comm, max_self, max_eq_left hb]
      rw [heq] at hs2
      exact hs2

/-- **Gluing absolute continuity at an interior point**: absolute continuity on the two
halves of an interval combines across the junction. -/
theorem ac_glue {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : AbsolutelyContinuousOnInterval f a b)
    (h₂ : AbsolutelyContinuousOnInterval f b c) :
    AbsolutelyContinuousOnInterval f a c := by
  rw [absolutelyContinuousOnInterval_iff] at h₁ h₂ ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := h₁ (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := h₂ (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  rintro ⟨n, I⟩ hE hlen
  obtain ⟨hEm, hEd⟩ := hE
  have hac : a ≤ c := le_trans hab hbc
  have hE₁ : ((n, fun i => (min (I i).1 b, min (I i).2 b)) : ℕ × (ℕ → ℝ × ℝ))
      ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
    constructor
    · intro i hi
      obtain ⟨hx, hy⟩ := hEm i hi
      rw [Set.uIcc_of_le hac] at hx hy
      rw [Set.uIcc_of_le hab]
      exact ⟨⟨le_min hx.1 hab, min_le_right _ _⟩,
        ⟨le_min hy.1 hab, min_le_right _ _⟩⟩
    · intro i hi j hj hij
      exact Disjoint.mono (uIoc_min_subset b _ _)
        (uIoc_min_subset b _ _) (hEd hi hj hij)
  have hE₂ : ((n, fun i => (max (I i).1 b, max (I i).2 b)) : ℕ × (ℕ → ℝ × ℝ))
      ∈ AbsolutelyContinuousOnInterval.disjWithin b c := by
    constructor
    · intro i hi
      obtain ⟨hx, hy⟩ := hEm i hi
      rw [Set.uIcc_of_le hac] at hx hy
      rw [Set.uIcc_of_le hbc]
      exact ⟨⟨le_max_right _ _, max_le hx.2 hbc⟩,
        ⟨le_max_right _ _, max_le hy.2 hbc⟩⟩
    · intro i hi j hj hij
      exact Disjoint.mono (uIoc_max_subset b _ _)
        (uIoc_max_subset b _ _) (hEd hi hj hij)
  have hlen₁ : ∑ i ∈ Finset.range n,
      dist (min (I i).1 b) (min (I i).2 b) < δ₁ := by
    refine lt_of_le_of_lt
      (Finset.sum_le_sum fun i _ => dist_min_le b (I i).1 (I i).2) ?_
    exact lt_of_lt_of_le hlen (min_le_left _ _)
  have hlen₂ : ∑ i ∈ Finset.range n,
      dist (max (I i).1 b) (max (I i).2 b) < δ₂ := by
    refine lt_of_le_of_lt
      (Finset.sum_le_sum fun i _ => dist_max_le b (I i).1 (I i).2) ?_
    exact lt_of_lt_of_le hlen (min_le_right _ _)
  have hs₁ := hδ₁' _ hE₁ hlen₁
  have hs₂ := hδ₂' _ hE₂ hlen₂
  have hsplit : ∀ i, dist (f (I i).1) (f (I i).2)
      ≤ dist (f (min (I i).1 b)) (f (min (I i).2 b))
        + dist (f (max (I i).1 b)) (f (max (I i).2 b)) := by
    intro i
    rcases le_total (I i).1 b with hx | hx <;>
      rcases le_total (I i).2 b with hy | hy
    · rw [min_eq_left hx, min_eq_left hy, max_eq_right hx, max_eq_right hy]
      simp
    · rw [min_eq_left hx, min_eq_right hy, max_eq_right hx, max_eq_left hy]
      exact dist_triangle _ _ _
    · rw [min_eq_right hx, min_eq_left hy, max_eq_left hx, max_eq_right hy]
      linarith [dist_triangle (f (I i).1) (f b) (f (I i).2)]
    · rw [min_eq_right hx, min_eq_right hy, max_eq_left hx, max_eq_left hy]
      simp
  calc ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)
      ≤ ∑ i ∈ Finset.range n,
        (dist (f (min (I i).1 b)) (f (min (I i).2 b))
          + dist (f (max (I i).1 b)) (f (max (I i).2 b))) :=
        Finset.sum_le_sum fun i _ => hsplit i
    _ = (∑ i ∈ Finset.range n, dist (f (min (I i).1 b)) (f (min (I i).2 b)))
        + ∑ i ∈ Finset.range n, dist (f (max (I i).1 b)) (f (max (I i).2 b)) :=
        Finset.sum_add_distrib
    _ < ε / 2 + ε / 2 := add_lt_add hs₁ hs₂
    _ = ε := by ring

/-- Absolute continuity only depends on the values on the interval. -/
theorem ac_congr {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X} {a b : ℝ}
    (hfg : ∀ t ∈ Set.uIcc a b, f t = g t)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨n, I⟩ hE hlen
  have := hδ' _ hE hlen
  refine lt_of_le_of_lt (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hfg _ (hE.1 i hi).1, hfg _ (hE.1 i hi).2]

/-- The **concatenation** of two flat paths through a common junction point. -/
noncomputable def pathJoin (γ₁ γ₂ : ℝ → ℂ) : ℝ → ℂ := fun s =>
  if s ≤ 1 / 2 then γ₁ (2 * s) else γ₂ (2 * s - 1)

/-- The concatenation of flat paths is a flat path. -/
theorem pathJoin_isFlatPath {γ₁ γ₂ : ℝ → ℂ} {a b c : ℂ}
    (h₁ : IsFlatPath γ₁ a b) (h₂ : IsFlatPath γ₂ b c) :
    IsFlatPath (pathJoin γ₁ γ₂) a c := by
  have hEq₁ : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), pathJoin γ₁ γ₂ s = γ₁ (2 * s) :=
    fun s hs => if_pos hs.2
  have hEq₂ : ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, pathJoin γ₁ γ₂ s = γ₂ (2 * s - 1) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with heq | hlt
    · rw [pathJoin, if_pos (le_of_eq heq.symm), ← heq]
      rw [show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, h₁.final, h₂.init]
    · exact if_neg (not_le.mpr hlt)
  have hc₁ : ContinuousOn (fun s => γ₁ (2 * s)) (Set.Icc (0 : ℝ) (1 / 2)) := by
    refine h₁.cont.comp (continuous_const.mul continuous_id).continuousOn ?_
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hc₂ : ContinuousOn (fun s => γ₂ (2 * s - 1)) (Set.Icc (1 / 2 : ℝ) 1) := by
    refine h₂.cont.comp
      ((continuous_const.mul continuous_id).sub continuous_const).continuousOn ?_
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pathJoin, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show 2 * (0 : ℝ) = 0 by norm_num, h₁.init]
  · rw [pathJoin, if_neg (by norm_num : ¬(1 : ℝ) ≤ 1 / 2)]
    rw [show 2 * (1 : ℝ) - 1 = 1 by norm_num, h₂.final]
  · intro s hs
    change Filter.Tendsto (pathJoin γ₁ γ₂) (nhdsWithin s (Set.Icc (0 : ℝ) 1))
      (nhds (pathJoin γ₁ γ₂ s))
    rcases lt_trichotomy s (1 / 2) with hlt | heq | hgt
    · have hsI : s ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hs.1, hlt.le⟩
      rw [nhdsWithin_left (by norm_num : (1 / 2 : ℝ) ≤ 1) hlt, hEq₁ s hsI]
      refine Filter.Tendsto.congr' ?_ (hc₁ s hsI)
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hEq₁ u hu).symm
    · subst heq
      have hsplit := nhdsWithin_split (t := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at hsplit
      have hval : pathJoin γ₁ γ₂ (1 / 2 : ℝ) = γ₁ 1 := by
        rw [pathJoin, if_pos (le_refl _)]
        norm_num
      rw [hsplit, hval, Filter.tendsto_sup]
      constructor
      · have h0 := hc₁ (1 / 2 : ℝ) (Set.right_mem_Icc.mpr (by norm_num))
        have h1 : Filter.Tendsto (fun s' => γ₁ (2 * s'))
            (nhdsWithin (1 / 2 : ℝ) (Set.Icc (0 : ℝ) (1 / 2)))
            (nhds (γ₁ 1)) := by
          have h2 : γ₁ (2 * (1 / 2 : ℝ)) = γ₁ 1 := by norm_num
          rw [← h2]
          exact h0
        refine Filter.Tendsto.congr' ?_ h1
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact (hEq₁ u hu).symm
      · have h0 := hc₂ (1 / 2 : ℝ) (Set.left_mem_Icc.mpr (by norm_num))
        have h1 : Filter.Tendsto (fun s' => γ₂ (2 * s' - 1))
            (nhdsWithin (1 / 2 : ℝ) (Set.Icc (1 / 2 : ℝ) 1))
            (nhds (γ₁ 1)) := by
          have h2 : γ₂ (2 * (1 / 2 : ℝ) - 1) = γ₁ 1 := by
            rw [show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, h₂.init, h₁.final]
          rw [← h2]
          exact h0
        refine Filter.Tendsto.congr' ?_ h1
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact (hEq₂ u hu).symm
    · have hsI : s ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨hgt.le, hs.2⟩
      have hflt := nhdsWithin_right (t := s) (b := (1 / 2 : ℝ))
        (δ := (1 / 2 : ℝ)) (by norm_num) hgt
      rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at hflt
      rw [hflt, hEq₂ s hsI]
      refine Filter.Tendsto.congr' ?_ (hc₂ s hsI)
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hEq₂ u hu).symm
  · have hac₁ : AbsolutelyContinuousOnInterval (pathJoin γ₁ γ₂) 0 (1 / 2) := by
      have h0 : AbsolutelyContinuousOnInterval γ₁ (2 * 0 + 0) (2 * (1 / 2) + 0) := by
        norm_num
        exact h₁.ac
      refine ac_congr ?_ (acOn_comp_affine two_pos h0)
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
      rw [hEq₁ t ht, add_zero]
    have hac₂ : AbsolutelyContinuousOnInterval (pathJoin γ₁ γ₂) (1 / 2) 1 := by
      have h0 : AbsolutelyContinuousOnInterval γ₂
          (2 * (1 / 2) + -1) (2 * 1 + -1) := by
        norm_num
        exact h₂.ac
      refine ac_congr ?_ (acOn_comp_affine two_pos h0)
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
      rw [hEq₂ t ht]
      ring_nf
    exact ac_glue (by norm_num) (by norm_num) hac₁ hac₂
  · intro s hs
    rcases le_total s (1 / 2) with hle | hge
    · rw [hEq₁ s ⟨hs.1, hle⟩]
      exact h₁.upper _ ⟨by linarith [hs.1], by linarith⟩
    · rw [hEq₂ s ⟨hge, hs.2⟩]
      exact h₂.upper _ ⟨by linarith, by linarith [hs.2]⟩

/-- Junk-safe derivative of an affine reparametrization. -/
theorem deriv_affine (γ : ℝ → ℂ) (c d s : ℝ) (hc : c ≠ 0) :
    deriv (fun t => γ (c * t + d)) s = c • deriv γ (c * s + d) := by
  by_cases hdiff : DifferentiableAt ℝ γ (c * s + d)
  · have hin : HasDerivAt (fun t : ℝ => c * t + d) c s := by
      simpa using ((hasDerivAt_id s).const_mul c).add_const d
    exact (HasDerivAt.scomp s hdiff.hasDerivAt hin).deriv
  · have h1 : ¬DifferentiableAt ℝ (fun t => γ (c * t + d)) s := by
      intro hcomp
      apply hdiff
      have h2 : DifferentiableAt ℝ (fun u : ℝ => (u - d) / c) (c * s + d) :=
        ((differentiable_id.sub_const d).div_const c).differentiableAt
      have hval : (c * s + d - d) / c = s := by
        rw [show c * s + d - d = c * s by ring]
        field_simp
      have h3 : DifferentiableAt ℝ
          ((fun t => γ (c * t + d)) ∘ fun u => (u - d) / c) (c * s + d) := by
        refine DifferentiableAt.comp _ ?_ h2
        rw [hval]
        exact hcomp
      have h4 : ((fun t => γ (c * t + d)) ∘ fun u => (u - d) / c) = γ := by
        funext u
        simp only [Function.comp]
        congr 1
        field_simp
        ring
      rwa [h4] at h3
    rw [deriv_zero_of_not_differentiableAt hdiff,
      deriv_zero_of_not_differentiableAt h1]
    simp

/-- Affine scaling of the horizontal density. -/
theorem horizontalDensity_affine (q : ℂ → ℂ) (γ : ℝ → ℂ) {c : ℝ} (d s : ℝ)
    (hc : 0 < c) :
    horizontalDensity q (fun t => γ (c * t + d)) s
      = ENNReal.ofReal c * horizontalDensity q γ (c * s + d) := by
  unfold horizontalDensity
  rw [deriv_affine γ c d s hc.ne']
  rw [Complex.real_smul]
  have hQ : q (γ (c * s + d)) * ((c : ℂ) * deriv γ (c * s + d)) ^ 2
      = (c : ℂ) ^ 2 * (q (γ (c * s + d)) * deriv γ (c * s + d) ^ 2) := by
    ring
  rw [hQ]
  set Q : ℂ := q (γ (c * s + d)) * deriv γ (c * s + d) ^ 2 with hQdef
  have h1 : ‖(c : ℂ) ^ 2 * Q‖ = c ^ 2 * ‖Q‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have h2 : ((c : ℂ) ^ 2 * Q).re = c ^ 2 * Q.re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rw [h1, h2]
  have h3 : (c ^ 2 * ‖Q‖ - c ^ 2 * Q.re) / 2 = c ^ 2 * ((‖Q‖ - Q.re) / 2) := by
    ring
  rw [h3, Real.sqrt_mul (by positivity) _, Real.sqrt_sq hc.le,
    ENNReal.ofReal_mul hc.le]

/-- On a strong-legal seed of grid `t / (N + 1)` the flow at time `t > 0` is the stepper
arrival. -/
theorem flow_eq_pos_fwd {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {t : ℝ}
    (ht : 0 < t) {N : ℕ} {z : ℂ} (hz : z ∈ slegal A (t / (N + 1)) N) :
    A.flow t z = pos A (t / (N + 1)) (N + 1) z := by
  obtain ⟨σ, hσ0, hσtraj, hσS⟩ := traj_of_slegal A ht hz
  have hh : (0 : ℝ) < t / (N + 1) := by positivity
  have hcast : (((N + 1 : ℕ) : ℝ)) * (t / (N + 1)) = t := by
    push_cast
    field_simp
  have hpos := pos_eq_traj A hh hz hσ0 (by rw [hcast]; exact hσtraj)
    (by rw [hcast]; exact hσS)
  rw [hcast] at hpos
  have hflow : A.flow t (σ 0) = σ t :=
    flow_eq_traj hq A ht hσtraj (by rw [hσ0]; exact hσS)
  rw [hσ0] at hflow
  rw [hflow, hpos]

/-- On a strong-legal seed of the mirror atlas the flow at time `-t` is the mirror
stepper arrival. -/
theorem flow_eq_pos_bwd {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {t : ℝ}
    (ht : 0 < t) {N : ℕ} {z : ℂ}
    (hz : z ∈ slegal (mirrorAtlas A) (t / (N + 1)) N) :
    A.flow (-t) z = pos (mirrorAtlas A) (t / (N + 1)) (N + 1) z := by
  obtain ⟨σ, hσ0, hσtraj, hσS⟩ := traj_of_slegal (mirrorAtlas A) ht hz
  have hh : (0 : ℝ) < t / (N + 1) := by positivity
  have hcast : (((N + 1 : ℕ) : ℝ)) * (t / (N + 1)) = t := by
    push_cast
    field_simp
  have hreg : 0 < z.im ∧ q z ≠ 0 := by
    have := traj_regular hσtraj (Set.left_mem_Icc.mpr ht.le)
    rwa [hσ0] at this
  have hact : A.active (A.sel z) := (A.sel_spec hreg.1 hreg.2).1
  have hσS' : SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 (-1) := by
    have h1 : SlopeAt ((mirrorAtlas A).Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 := hσS
    rw [mirror_Φ A hact] at h1
    change ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 t),
      A.Φ (A.sel z) (σ v) = A.Φ (A.sel z) (σ 0) + ((-1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
    filter_upwards [h1] with v hv
    have hv' : -(A.Φ (A.sel z) (σ v))
        = -(A.Φ (A.sel z) (σ 0)) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hv
    push_cast at hv' ⊢
    linear_combination -hv'
  have hσtraj' : IsTrajOn q σ (Set.Icc 0 (- -t)) := by rwa [neg_neg]
  have hσS'' : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (- -t)) 0 (-1) := by
    rw [hσ0, neg_neg]
    exact hσS'
  have hflow := flow_eq_traj_neg hq A (by linarith : -t < 0) hσtraj' hσS''
  rw [hσ0, neg_neg] at hflow
  have hpos := pos_eq_traj (mirrorAtlas A) hh hz hσ0 (by rw [hcast]; exact hσtraj)
    (by rw [hcast]; exact hσS)
  rw [hcast] at hpos
  rw [hflow, hpos]

/-- Every two-sided regular point is a strong-legal seed of some forward grid. -/
theorem good_slegal_fwd {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {t : ℝ}
    (ht : 0 < t) {z : ℂ} (hz : z ∈ good q A) :
    ∃ N : ℕ, z ∈ slegal A (t / (N + 1)) N := by
  obtain ⟨σ, hσ0, hσtraj, hσS⟩ := hz.2.2.1 t ht
  have h := slegal_of_traj hq A ht hσtraj (by rw [hσ0]; exact hσS)
  rwa [hσ0] at h

/-- Every two-sided regular point is a strong-legal seed of some mirror grid. -/
theorem good_slegal_bwd {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {t : ℝ}
    (ht : 0 < t) {z : ℂ} (hz : z ∈ good q A) :
    ∃ N : ℕ, z ∈ slegal (mirrorAtlas A) (t / (N + 1)) N := by
  obtain ⟨σ, hσ0, hσtraj, hσS⟩ := hz.2.2.2 t ht
  have hact : A.active (A.sel z) := (A.sel_spec hz.1 hz.2.1).1
  have hσS' : SlopeAt ((mirrorAtlas A).Φ ((mirrorAtlas A).sel (σ 0))) σ
      (Set.Icc 0 t) 0 1 := by
    have h1 : SlopeAt ((mirrorAtlas A).Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 := by
      rw [mirror_Φ A hact]
      change ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 t),
        -(A.Φ (A.sel z) (σ v))
          = -(A.Φ (A.sel z) (σ 0)) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
      have hσS0 : SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 (-1) := hσS
      filter_upwards [hσS0] with v hv
      have hv' : A.Φ (A.sel z) (σ v)
          = A.Φ (A.sel z) (σ 0) + ((-1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hv
      push_cast at hv' ⊢
      linear_combination -hv'
    rw [hσ0]
    exact h1
  have h := slegal_of_traj hq (mirrorAtlas A) ht hσtraj hσS'
  rwa [hσ0] at h

/-- The stepper arrival of a strong-legal seed is a regular point. -/
theorem pos_regular {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} (hh : 0 < h) {N : ℕ}
    {z : ℂ} (hz : z ∈ slegal A h N) :
    0 < (pos A h (N + 1) z).im ∧ q (pos A h (N + 1) z) ≠ 0 := by
  obtain ⟨σ, hσ0, hσtraj, -, -, hσend⟩ := slegal_traj A hh N z hz
  have hT : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) * h := by push_cast; positivity
  have := traj_regular hσtraj (Set.right_mem_Icc.mpr hT.le)
  rwa [hσend] at this

/-- The unit-window trajectory of a strong-legal seed for total duration `t`. -/
theorem slegal_traj_t {q : ℂ → ℂ} (A : Atlas q) {t : ℝ} (ht : 0 < t) {N : ℕ}
    {z : ℂ} (hz : z ∈ slegal A (t / (N + 1)) N) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 t) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 ∧
      σ t = pos A (t / (N + 1)) (N + 1) z := by
  have hh : (0 : ℝ) < t / (N + 1) := by positivity
  obtain ⟨σ, h0, htraj, hS0, -, hend⟩ := slegal_traj A hh N z hz
  have hcast : (((N + 1 : ℕ) : ℝ)) * (t / (N + 1)) = t := by
    push_cast
    field_simp
  rw [hcast] at htraj hS0 hend
  exact ⟨σ, h0, htraj, hS0, hend⟩

/-- **Weighted itinerary transport**: on a measurable strong-legal piece with constant
itinerary, the stepper arrival map transports any measurable weight against the `|q|`
area with equal mass — the arrival measure is the pushforward of the seed measure. -/
theorem piece_cov {q : ℂ → ℂ} (hqm : Measurable q) (A : Atlas q) {h : ℝ}
    (hh : 0 < h) {N : ℕ} {P : Set ℂ} (hP : MeasurableSet P)
    (hPs : P ⊆ slegal A h N) (c : Fin (N + 1) → ℕ × Bool)
    (hPc : ∀ z ∈ P, ∀ k : Fin (N + 1), A.sel (pos A h (k : ℕ) z) = (c k).1 ∧
      sgn A h (k : ℕ) z = (if (c k).2 then (1 : ℝ) else -1))
    {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    MeasurableSet (pos A h (N + 1) '' P) ∧
    ∫⁻ w in pos A h (N + 1) '' P, G w * ‖q w‖ₑ
      = ∫⁻ z in P, G (pos A h (N + 1) z) * ‖q z‖ₑ := by
  classical
  have hEL : P ⊆ legal A h N := hPs.trans (slegal_legal A hh.le N)
  have key : ∀ X : Set ℂ, MeasurableSet X → X ⊆ P →
      MeasurableSet (pos A h (N + 1) '' X) ∧
      ∫⁻ w in pos A h (N + 1) '' X, ‖q w‖ₑ = ∫⁻ z in X, ‖q z‖ₑ := by
    intro X hXm hXP
    refine chain_cov A hXm
      (fun k => if hk : k < N + 1 then (c ⟨k, hk⟩).1 else 0)
      (fun k => if hk : k < N + 1 then
        (if (c ⟨k, hk⟩).2 then (1 : ℝ) else -1) else 0)
      ?_ (N + 1) (le_refl _)
    intro k hk z hz
    have hk' : k < N + 1 := by omega
    obtain ⟨hsel, hsgn⟩ := hPc z (hXP hz) ⟨k, hk'⟩
    obtain ⟨hact, hball, hpm, hmove⟩ := hEL (hXP hz) k hk
    beta_reduce
    rw [dif_pos hk', dif_pos hk']
    refine ⟨hsel, hsgn, ?_, ?_, ?_⟩
    · rw [← hsel]
      exact hact
    · rw [← hsel]
      exact hball
    · rw [← hsel, ← hsgn]
      exact hmove
  set S : ℂ → ℂ := pos A h (N + 1) with hSdef
  have hSm : Measurable S := measurable_pos A h (N + 1)
  obtain ⟨hPim, -⟩ := key P hP Set.Subset.rfl
  set μq : Measure ℂ := volume.withDensity fun z => ‖q z‖ₑ with hμqdef
  have e1 : ∀ G' : ℂ → ℝ≥0∞, Measurable G' → ∀ X : Set ℂ, MeasurableSet X →
      ∫⁻ w, G' w ∂(μq.restrict X) = ∫⁻ w in X, G' w * ‖q w‖ₑ := by
    intro G' hG' X hX
    rw [hμqdef, restrict_withDensity hX,
      lintegral_withDensity_eq_lintegral_mul _ hqm.enorm hG']
    exact lintegral_congr fun w => mul_comm _ _
  have hmap : Measure.map S (μq.restrict P) = μq.restrict (S '' P) := by
    ext B hB
    rw [Measure.map_apply hSm hB, hμqdef, Measure.restrict_apply' hP,
      Measure.restrict_apply' hPim,
      withDensity_apply _ ((hSm hB).inter hP), withDensity_apply _ (hB.inter hPim)]
    have himg : S '' (P ∩ S ⁻¹' B) = S '' P ∩ B := by
      ext w
      constructor
      · rintro ⟨z, ⟨hzP, hzB⟩, rfl⟩
        exact ⟨⟨z, hzP, rfl⟩, hzB⟩
      · rintro ⟨⟨z, hzP, rfl⟩, hwB⟩
        exact ⟨z, ⟨hzP, hwB⟩, rfl⟩
    have h2 := (key (P ∩ S ⁻¹' B) (hP.inter (hSm hB)) Set.inter_subset_left).2
    rw [himg] at h2
    calc ∫⁻ z in S ⁻¹' B ∩ P, ‖q z‖ₑ = ∫⁻ z in P ∩ S ⁻¹' B, ‖q z‖ₑ := by
          rw [Set.inter_comm]
      _ = ∫⁻ w in S '' P ∩ B, ‖q w‖ₑ := h2.symm
      _ = ∫⁻ w in B ∩ S '' P, ‖q w‖ₑ := by rw [Set.inter_comm]
  refine ⟨hPim, ?_⟩
  calc ∫⁻ w in S '' P, G w * ‖q w‖ₑ
      = ∫⁻ w, G w ∂(μq.restrict (S '' P)) := (e1 G hG _ hPim).symm
    _ = ∫⁻ w, G w ∂(Measure.map S (μq.restrict P)) := by rw [hmap]
    _ = ∫⁻ z, G (S z) ∂(μq.restrict P) := lintegral_map hG hSm
    _ = ∫⁻ z in P, G (S z) * ‖q z‖ₑ := e1 (fun z => G (S z)) (hG.comp hSm) P hP

/-- **Weighted invariance of the area density**: for a weight-4 automorphic `q` and an
almost-everywhere Möbius-invariant weight `G`, the mass `∫⁻ G |q|` is preserved by the
Möbius image of a measurable subset of the upper half plane. -/
theorem lintegral_mul_moebius (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {q : ℂ → ℂ}
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γ z) = (moebiusDenom γ z) ^ 4 * q z)
    {V : Set ℂ} (hVm : MeasurableSet V) (hV : V ⊆ {z : ℂ | 0 < z.im})
    {G : ℂ → ℝ≥0∞}
    (hGinv : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      G (moebiusMap γ z) = G z) :
    ∫⁻ w in moebiusMap γ '' V, G w * ‖q w‖ₑ = ∫⁻ z in V, G z * ‖q z‖ₑ := by
  have hfd : ∀ z ∈ V, HasFDerivWithinAt (moebiusMap γ)
      (fderiv ℝ (moebiusMap γ) z) V z := by
    intro z hzS
    have hd : moebiusDenom γ z ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero γ (hV hzS).ne'
    have hda : DifferentiableAt ℝ (moebiusMap γ) z :=
      ((hasDerivAt_moebiusMap γ hd).complexToReal_fderiv).differentiableAt
    exact hda.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn (moebiusMap γ) V := (moebius_injOn γ).mono hV
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hVm hfd hinj
    (fun w => G w * ‖q w‖ₑ)]
  have h1 : ∀ᵐ z ∂(volume.restrict V), G (moebiusMap γ z) = G z :=
    ae_restrict_of_ae_restrict_of_subset hV hGinv
  have h2 : ∀ᵐ z ∂(volume.restrict V), z ∈ V := ae_restrict_mem hVm
  refine lintegral_congr_ae ?_
  filter_upwards [h1, h2] with z hzG hzV
  have hzim : 0 < z.im := hV hzV
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hzim.ne'
  have hnd : ‖moebiusDenom γ z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  rw [det_fderiv_moebiusMap_of_im_pos γ hzim, abs_of_nonneg (by positivity), hzG,
    hq z hzim]
  have hscal : ENNReal.ofReal ((‖moebiusDenom γ z‖ ^ 4)⁻¹)
      * ‖moebiusDenom γ z ^ 4 * q z‖ₑ = ‖q z‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, norm_pow]
    field_simp
  calc ENNReal.ofReal ((‖moebiusDenom γ z‖ ^ 4)⁻¹)
      * (G z * ‖moebiusDenom γ z ^ 4 * q z‖ₑ)
      = G z * (ENNReal.ofReal ((‖moebiusDenom γ z‖ ^ 4)⁻¹)
        * ‖moebiusDenom γ z ^ 4 * q z‖ₑ) := by ring
    _ = G z * ‖q z‖ₑ := by rw [hscal]

/-- The Möbius map of the coset representative agrees with that of the group element on
the upper half plane. -/
theorem symRep {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (γ : ↥Γ) (z : ℂ) (hz : 0 < z.im) :
    moebiusMap ↑(Quotient.out (QuotientGroup.mk γ : ↥Γ ⧸ MulAction.stabilizer ↥Γ
      UpperHalfPlane.I)) z = moebiusMap ↑γ z := by
  set γ' : ↥Γ := Quotient.out (QuotientGroup.mk γ : ↥Γ ⧸ MulAction.stabilizer ↥Γ
    UpperHalfPlane.I) with hγ'def
  have hδ : γ⁻¹ * γ' ∈ MulAction.stabilizer ↥Γ UpperHalfPlane.I := by
    rw [← QuotientGroup.eq]
    exact (QuotientGroup.out_eq' _).symm
  have hfact : γ' = γ * (γ⁻¹ * γ') := by group
  have hid : moebiusMap ↑(γ⁻¹ * γ') z = z :=
    stab_moebius_id hfree (MulAction.mem_stabilizer_iff.mp hδ) hz
  conv_lhs => rw [hfact]
  have hcoe : ((↑(γ * (γ⁻¹ * γ')) : Matrix.SpecialLinearGroup (Fin 2) ℝ))
      = ↑γ * ↑(γ⁻¹ * γ') := rfl
  rw [hcoe, ← moebiusMap_mul ↑γ ↑(γ⁻¹ * γ') z
    (moebiusDenom_ne_zero_of_im_ne_zero _ hz.ne'), hid]

/-- A regular point off the orbit of the planar frontier lies in a representative tile. -/
theorem cover_rep {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {w : ℂ} (hw : 0 < w.im)
    (hnb : w ∉ ⋃ γ : ↥Γ, moebiusMap ↑γ ''
      (UpperHalfPlane.coe '' frontier (dirichletDomain Γ UpperHalfPlane.I))) :
    ∃ cq : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I,
      w ∈ moebiusMap ↑(Quotient.out cq) ''
        (UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I)) := by
  obtain ⟨γ, hγ⟩ := cover hΓ hw hnb
  refine ⟨QuotientGroup.mk γ, ?_⟩
  have himeq : moebiusMap ↑(Quotient.out (QuotientGroup.mk γ : ↥Γ ⧸
        MulAction.stabilizer ↥Γ UpperHalfPlane.I)) ''
        (UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I))
      = moebiusMap ↑γ ''
        (UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I)) := by
    refine Set.image_congr fun z hz => ?_
    obtain ⟨τ, -, rfl⟩ := hz
    exact symRep hfree γ _ τ.im_pos
  rw [himeq]
  exact hγ

/-- A fundamental-domain point off the frontier orbit lies in the open tile. -/
theorem notBad_interior {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {w : ℂ}
    (hw : w ∈ UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)
    (hnb : w ∉ ⋃ γ : ↥Γ, moebiusMap ↑γ ''
      (UpperHalfPlane.coe '' frontier (dirichletDomain Γ UpperHalfPlane.I))) :
    w ∈ UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I) := by
  obtain ⟨τ, hτD, rfl⟩ := hw
  refine ⟨τ, ?_, rfl⟩
  by_contra hint
  apply hnb
  refine Set.mem_iUnion.mpr ⟨1, (τ : ℂ), ⟨τ, ?_, rfl⟩, ?_⟩
  · rw [(isClosed_dirichletDomain Γ UpperHalfPlane.I).frontier_eq]
    exact ⟨hτD, hint⟩
  · have h1 : ((1 : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 := rfl
    rw [h1, moebiusMap_one]

/-- Distinct representative tiles are disjoint. -/
theorem tile_disjoint {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    {c c' : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I} (hne : c ≠ c') :
    Disjoint
      (moebiusMap ↑(Quotient.out c) ''
        (UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I)))
      (moebiusMap ↑(Quotient.out c') ''
        (UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I))) := by
  rw [Set.disjoint_left]
  rintro w ⟨u, ⟨τ, hτ, rfl⟩, rfl⟩ ⟨u', ⟨τ', hτ', rfl⟩, huw⟩
  set g : ↥Γ := Quotient.out c with hgdef
  set g' : ↥Γ := Quotient.out c' with hg'def
  have h1 : ((g' • τ' : UpperHalfPlane) : ℂ) = ((g • τ : UpperHalfPlane) : ℂ) := by
    rw [coe_smul_moebius, coe_smul_moebius]
    exact huw
  have h2 : g' • τ' = g • τ := UpperHalfPlane.coe_injective h1
  have h3 : (g⁻¹ * g') • τ' = τ := by rw [mul_smul, h2, inv_smul_smul]
  by_cases hfix : (g⁻¹ * g') • UpperHalfPlane.I = UpperHalfPlane.I
  · apply hne
    have hK : g⁻¹ * g' ∈ MulAction.stabilizer ↥Γ UpperHalfPlane.I :=
      MulAction.mem_stabilizer_iff.mpr hfix
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    exact QuotientGroup.eq.mpr hK
  · have hd := disjoint_smul_interior_dirichletDomain hΓ hdense
      (γ := g⁻¹ * g') hfix
    have hτδ : (g⁻¹ * g') • τ' ∈ interior (dirichletDomain Γ UpperHalfPlane.I) := by
      rw [h3]
      exact hτ
    exact absurd ⟨τ', hτ', rfl⟩ (Set.disjoint_left.mp hd hτδ)

/-- The planar fundamental tile of the Dirichlet domain at `i`. -/
def symOmega (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ℂ :=
  UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I

/-- The orbit of the planar frontier of the Dirichlet tile. -/
def symBad (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ℂ :=
  ⋃ γ : ↥Γ, moebiusMap ↑γ ''
    (UpperHalfPlane.coe '' frontier (dirichletDomain Γ UpperHalfPlane.I))

/-- The open representative tile of a stabilizer coset. -/
def symTile (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (cq : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) : Set ℂ :=
  moebiusMap ↑(Quotient.out cq) ''
    (UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I))

/-- The `N`-th strong-legal seed layer of duration `t` inside the trimmed tile. -/
def symSeed {q : ℂ → ℂ} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (B : Atlas q) (t : ℝ) (N : ℕ) : Set ℂ :=
  (symOmega Γ \ symBad Γ)
    ∩ (slegal B (t / (N + 1)) N \ ⋃ M : ℕ, ⋃ _ : M < N, slegal B (t / (M + 1)) M)

/-- The constant-itinerary piece of a seed layer. -/
def symPiece {q : ℂ → ℂ} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (B : Atlas q) (t : ℝ) (N : ℕ) (c : Fin (N + 1) → ℕ × Bool) : Set ℂ :=
  itinPiece B (t / (N + 1)) N (symSeed Γ B t N) c

/-- The stepper arrival set of a constant-itinerary piece. -/
def symArr {q : ℂ → ℂ} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (B : Atlas q) (t : ℝ) (j : Σ N : ℕ, Fin (N + 1) → ℕ × Bool) : Set ℂ :=
  pos B (t / (j.1 + 1)) (j.1 + 1) '' symPiece Γ B t j.1 j.2

/-- The arrival set retiled into the open fundamental tile through one coset. -/
def symRet {q : ℂ → ℂ} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (B : Atlas q) (t : ℝ)
    (i : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
      × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I)) : Set ℂ :=
  moebiusMap (↑(Quotient.out i.2))⁻¹ ''
    ((symArr Γ B t i.1 \ symBad Γ) ∩ symTile Γ i.2)

/-- The frontier orbit is measurable and Lebesgue-null. -/
theorem symBad_facts {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R) :
    MeasurableSet (symBad Γ) ∧ volume (symBad Γ) = 0 := by
  haveI : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  set F : Set ℂ :=
    UpperHalfPlane.coe '' frontier (dirichletDomain Γ UpperHalfPlane.I) with hFdef
  have hFU : F ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hFcomp : IsCompact F :=
    ((isCompact_dirichletDomain hdense).of_isClosed_subset isClosed_frontier
      (isClosed_dirichletDomain Γ UpperHalfPlane.I).frontier_subset).image
      UpperHalfPlane.continuous_coe
  have hFmeas : MeasurableSet F := hFcomp.measurableSet
  have hFnull : volume F = 0 := frontier_image_null hΓ hdense
  constructor
  · exact MeasurableSet.iUnion fun γ =>
      (hFcomp.image_of_continuousOn ((moebius_contOn ↑γ).mono hFU)).measurableSet
  · rw [show symBad Γ = ⋃ γ : ↥Γ, moebiusMap ↑γ '' F from rfl,
      measure_iUnion_null_iff]
    intro γ
    exact image_null hFmeas hFnull (fun z hz => moebius_diffAt ↑γ (hFU hz))
      ((moebius_injOn ↑γ).mono hFU)

/-- Points of the planar tile have positive imaginary part. -/
theorem symOmega_upper {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} :
    symOmega Γ ⊆ {z : ℂ | 0 < z.im} := by
  rintro w ⟨τ, -, rfl⟩
  simpa using τ.im_pos

/-- Points of a representative tile have positive imaginary part. -/
theorem symTile_upper {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (cq : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) :
    symTile Γ cq ⊆ {z : ℂ | 0 < z.im} := by
  rintro w ⟨v, ⟨τ, -, rfl⟩, rfl⟩
  exact moebiusMap_im_pos _ (by simpa using τ.im_pos)

/-- **Arrival retiling**: the weighted `|q|` mass of an arrival set is the coset sum of
the masses of its retiled images in the open fundamental tile. -/
theorem symArr_retile {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    (q : QuadraticDifferential Γ) (B : Atlas (q : ℂ → ℂ)) {t : ℝ}
    (j : Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
    (harrm : MeasurableSet (symArr Γ B t j))
    (harrU : ∀ w ∈ symArr Γ B t j, 0 < w.im)
    {G : ℂ → ℝ≥0∞}
    (hGinv : ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      G (moebiusMap ↑γ z) = G z) :
    ∫⁻ w in symArr Γ B t j, G w * ‖q w‖ₑ
      = ∑' cq : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I,
          ∫⁻ w in symRet Γ B t (j, cq), G w * ‖q w‖ₑ := by
  haveI : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  haveI : Countable (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) :=
    QuotientGroup.mk_surjective.countable
  obtain ⟨hBadm, hBadnull⟩ := symBad_facts hΓ hdense
  set Arr : Set ℂ := symArr Γ B t j with hArrdef
  have hIntU : UpperHalfPlane.coe ''
      interior (dirichletDomain Γ UpperHalfPlane.I) ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have h1 : ∫⁻ w in Arr, G w * ‖q w‖ₑ
      = ∫⁻ w in Arr \ symBad Γ, G w * ‖q w‖ₑ := by
    refine setLIntegral_congr (MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null (fun w hw => by
        by_contra hb
        exact hw.2 ⟨hw.1, hb⟩) hBadnull
    · exact measure_mono_null (fun w hw => (hw.2 hw.1.1).elim)
        (measure_empty (μ := volume))
  have hcov : Arr \ symBad Γ
      = ⋃ cq, ((Arr \ symBad Γ) ∩ symTile Γ cq) := by
    refine Set.Subset.antisymm (fun w hw => ?_)
      (Set.iUnion_subset fun cq => Set.inter_subset_left)
    obtain ⟨cq, hcq⟩ := cover_rep hΓ hfree (harrU w hw.1) hw.2
    exact Set.mem_iUnion.mpr ⟨cq, hw, hcq⟩
  have hm : ∀ cq, MeasurableSet ((Arr \ symBad Γ) ∩ symTile Γ cq) := by
    intro cq
    refine (harrm.diff hBadm).inter ?_
    have hopen : IsOpen (symTile Γ cq) := isOpen_moebius_image _
      (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ isOpen_interior) hIntU
    exact hopen.measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint
      fun cq => (Arr \ symBad Γ) ∩ symTile Γ cq) := fun c c' hne =>
    (tile_disjoint hΓ hdense hne).mono Set.inter_subset_right
      Set.inter_subset_right
  have h2 : ∫⁻ w in Arr \ symBad Γ, G w * ‖q w‖ₑ
      = ∑' cq, ∫⁻ w in (Arr \ symBad Γ) ∩ symTile Γ cq, G w * ‖q w‖ₑ := by
    conv_lhs => rw [hcov]
    exact lintegral_iUnion hm hdisj _
  rw [h1, h2]
  refine tsum_congr fun cq => ?_
  set γg : ↥Γ := Quotient.out cq with hγgdef
  set X : Set ℂ := (Arr \ symBad Γ) ∩ symTile Γ cq with hXdef
  have hXU : X ⊆ {z : ℂ | 0 < z.im} :=
    Set.inter_subset_right.trans (symTile_upper cq)
  have hretU : symRet Γ B t (j, cq) ⊆ {z : ℂ | 0 < z.im} := by
    rintro v ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hw.2
    rw [moebius_cancel _ (hIntU hu)]
    exact hIntU hu
  have hretm : MeasurableSet (symRet Γ B t (j, cq)) :=
    (hm cq).image_of_continuousOn_injOn ((moebius_contOn _).mono hXU)
      ((moebius_injOn _).mono hXU)
  have himg : moebiusMap ↑γg '' symRet Γ B t (j, cq) = X := by
    ext w
    constructor
    · rintro ⟨v, ⟨w', hw', rfl⟩, rfl⟩
      rwa [moebius_cancel' _ (hXU hw')]
    · intro hw
      exact ⟨moebiusMap (↑γg)⁻¹ w, Set.mem_image_of_mem _ hw,
        moebius_cancel' _ (hXU hw)⟩
  calc ∫⁻ w in X, G w * ‖q w‖ₑ
      = ∫⁻ w in moebiusMap ↑γg '' symRet Γ B t (j, cq), G w * ‖q w‖ₑ := by
        rw [himg]
    _ = ∫⁻ w in symRet Γ B t (j, cq), G w * ‖q w‖ₑ :=
        lintegral_mul_moebius ↑γg (fun z hz => q.automorphy ↑γg γg.2 z hz)
          hretm hretU (hGinv γg)

end RiemannDynamics

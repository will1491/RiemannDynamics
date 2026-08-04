/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Coarea.OffsetDisjoint

/-!
# The two-point displacement estimate and the conditional main inequality

The homotopy chain computing the winding number about a near-offset point, the per-piece
counting of leaf levels, the two-point leaf-displacement estimate, and the main
inequality conditional on the nonnegative-winding principle.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Order-separated summation**: countably many pairwise order-separated subsets of
a set of reals have summed outer measures dominated by the ambient measure. -/
theorem ordered_sum {Λ : Set ℝ} {H : ℕ → Set ℝ}
    (hsub : ∀ n, H n ⊆ Λ)
    (hsep : ∀ m n, m ≠ n → (∀ x ∈ H m, ∀ y ∈ H n, x < y) ∨
      (∀ x ∈ H m, ∀ y ∈ H n, y < x)) :
    ∑' n, volume (H n) ≤ volume Λ := by
  have key : ∀ F : Finset ℕ, ∀ Λ' : Set ℝ, (∀ n ∈ F, H n ⊆ Λ') →
      ∑ n ∈ F, volume (H n) ≤ volume Λ' := by
    intro F
    induction F using Finset.strongInduction with
    | _ F ih =>
      intro Λ' hsub'
      classical
      rcases Finset.eq_empty_or_nonempty F with rfl | hFne
      · simp
      by_cases hex : ∃ n ∈ F, H n = ∅
      · obtain ⟨n₀, hn₀F, hn₀e⟩ := hex
        rw [← Finset.sum_erase_add F _ hn₀F, hn₀e]
        simp only [measure_empty, add_zero]
        exact ih (F.erase n₀) (Finset.erase_ssubset hn₀F) Λ'
          fun n hn => hsub' n (Finset.mem_of_mem_erase hn)
      push Not at hex
      have hne : ∀ n ∈ F, (H n).Nonempty := hex
      set f : ℕ → ℝ := fun n => if h : (H n).Nonempty then h.choose else 0
        with hfdef
      have hfmem : ∀ n ∈ F, f n ∈ H n := by
        intro n hn
        rw [hfdef]
        simp only
        rw [dif_pos (hne n hn)]
        exact (hne n hn).choose_spec
      obtain ⟨ns, hnsF, hnsmax⟩ := F.exists_max_image f hFne
      have hmaxside : ∀ m ∈ F.erase ns, ∀ x ∈ H m, ∀ y ∈ H ns, x < y := by
        intro m hm
        have hmne : m ≠ ns := Finset.ne_of_mem_erase hm
        have hmF : m ∈ F := Finset.mem_of_mem_erase hm
        rcases hsep m ns hmne with h2 | h2
        · exact h2
        · exfalso
          have h3 := h2 (f m) (hfmem m hmF) (f ns) (hfmem ns hnsF)
          have h4 := hnsmax m hmF
          linarith only [h3, h4]
      rcases Finset.eq_empty_or_nonempty (F.erase ns) with herase | herase
      · have hFsingle : F = {ns} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hnsF, fun m hm => ?_⟩
          by_contra hmne
          have h9 : m ∈ F.erase ns := Finset.mem_erase.mpr ⟨hmne, hm⟩
          rw [herase] at h9
          exact absurd h9 (by simp)
        rw [hFsingle, Finset.sum_singleton]
        exact measure_mono (hsub' ns hnsF)
      -- the cut point at the infimum of the maximal member
      obtain ⟨m₀, hm₀⟩ := herase
      have hm₀F : m₀ ∈ F := Finset.mem_of_mem_erase hm₀
      have hbdd : BddBelow (H ns) :=
        ⟨f m₀, fun y hy => (hmaxside m₀ hm₀ _ (hfmem m₀ hm₀F) y hy).le⟩
      set qc : ℝ := sInf (H ns) with hqcdef
      have hrestle : ∀ m ∈ F.erase ns, ∀ x ∈ H m, x ≤ qc := by
        intro m hm x hx
        exact le_csInf (hne ns hnsF) fun y hy => (hmaxside m hm x hx y hy).le
      by_cases hq : ∀ y ∈ H ns, qc < y
      · -- the maximal member avoids the cut point
        have hsplit := measure_inter_add_diff (μ := volume) Λ'
          (measurableSet_Iic (a := qc))
        have hrest : ∑ n ∈ F.erase ns, volume (H n)
            ≤ volume (Λ' ∩ Set.Iic qc) := by
          refine ih (F.erase ns) (Finset.erase_ssubset hnsF) _ ?_
          intro n hn x hx
          exact ⟨hsub' n (Finset.mem_of_mem_erase hn) hx, hrestle n hn x hx⟩
        have hmax : volume (H ns) ≤ volume (Λ' \ Set.Iic qc) := by
          refine measure_mono ?_
          intro y hy
          exact ⟨hsub' ns hnsF hy, by
            simp only [Set.mem_Iic, not_le]
            exact hq y hy⟩
        calc ∑ n ∈ F, volume (H n)
            = ∑ n ∈ F.erase ns, volume (H n) + volume (H ns) := by
              rw [Finset.sum_erase_add]
              exact hnsF
          _ ≤ volume (Λ' ∩ Set.Iic qc) + volume (Λ' \ Set.Iic qc) :=
              add_le_add hrest hmax
          _ = volume Λ' := hsplit
      · -- the cut point is attained in the maximal member
        push Not at hq
        obtain ⟨y₀, hy₀, hy₀le⟩ := hq
        have hy₀eq : y₀ = qc := le_antisymm hy₀le (csInf_le hbdd hy₀)
        have hrestlt : ∀ m ∈ F.erase ns, ∀ x ∈ H m, x < qc := by
          intro m hm x hx
          have h2 := hmaxside m hm x hx y₀ hy₀
          rwa [hy₀eq] at h2
        have hsplit := measure_inter_add_diff (μ := volume) Λ'
          (measurableSet_Iio (a := qc))
        have hrest : ∑ n ∈ F.erase ns, volume (H n)
            ≤ volume (Λ' ∩ Set.Iio qc) := by
          refine ih (F.erase ns) (Finset.erase_ssubset hnsF) _ ?_
          intro n hn x hx
          exact ⟨hsub' n (Finset.mem_of_mem_erase hn) hx, hrestlt n hn x hx⟩
        have hmax : volume (H ns) ≤ volume (Λ' \ Set.Iio qc) := by
          refine measure_mono ?_
          intro y hy
          exact ⟨hsub' ns hnsF hy, by
            simp only [Set.mem_Iio, not_lt]
            exact csInf_le hbdd hy⟩
        calc ∑ n ∈ F, volume (H n)
            = ∑ n ∈ F.erase ns, volume (H n) + volume (H ns) := by
              rw [Finset.sum_erase_add]
              exact hnsF
          _ ≤ volume (Λ' ∩ Set.Iio qc) + volume (Λ' \ Set.Iio qc) :=
              add_le_add hrest hmax
          _ = volume Λ' := hsplit
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun F => key F Λ fun n _ => hsub n

section WindingRayZero

open unitInterval

/-- **Ray omission**: a closed curve avoiding the upward vertical ray from `ζ` has
winding number zero about `ζ`. -/
theorem winding_ray_zero {γ : C(I, ℂ)} {ζ : ℂ}
    (hcl : γ 0 = γ 1) (hne : ∀ t : I, γ t ≠ ζ)
    (hray : ∀ t : I, ¬((γ t - ζ).re = 0 ∧ 0 < (γ t - ζ).im)) :
    windingNumber γ ζ = 0 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsne : ∀ t : I, shiftedCurve γ ζ t ≠ 0 := by
    intro t
    have h1 : shiftedCurve γ ζ t = γ t - ζ := by simp [shiftedCurve]
    rw [h1]
    exact sub_ne_zero.mpr (hne t)
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ ζ) hsne
  have hspec := windingNumber_spec hcl hne hL
  have hval : ∀ t : I, shiftedCurve γ ζ t = γ t - ζ := by
    intro t
    simp [shiftedCurve]
  have hpin : ∀ (t : I) (k : ℤ), (L t).im ≠ Real.pi/2 + k * (2 * Real.pi) := by
    intro t k hk
    have hre : (γ t - ζ).re = Real.exp ((L t).re)
        * Real.cos ((L t).im) := by
      rw [← hval t, ← hL t, Complex.exp_re]
    have him : (γ t - ζ).im = Real.exp ((L t).re)
        * Real.sin ((L t).im) := by
      rw [← hval t, ← hL t, Complex.exp_im]
    rw [hk] at hre him
    have hcos : Real.cos (Real.pi/2 + (k : ℝ) * (2 * Real.pi)) = 0 := by
      rw [Real.cos_add_int_mul_two_pi, Real.cos_pi_div_two]
    have hsin : Real.sin (Real.pi/2 + (k : ℝ) * (2 * Real.pi)) = 1 := by
      rw [Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
    refine hray t ⟨?_, ?_⟩
    · rw [hre, hcos, mul_zero]
    · rw [him, hsin, mul_one]
      exact Real.exp_pos _
  by_contra hw
  have him : (L 1).im - (L 0).im = 2 * Real.pi * ((windingNumber γ ζ : ℤ) : ℝ) := by
    have h := congrArg Complex.im hspec
    simpa using h
  have hθc : Continuous fun t : I => (L t).im := by fun_prop
  set n : ℤ := windingNumber γ ζ with hndef
  have hn : n ≠ 0 := hw
  have hkey : ∃ t : I, ∃ k : ℤ,
      (L t).im = Real.pi/2 + k * (2 * Real.pi) := by
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have hbound : (L 1).im ≤ (L 0).im - 2 * Real.pi := by
        have h1 : ((n : ℝ)) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
        nlinarith only [him, hπ, h1]
      set k : ℤ := ⌈((L 1).im - Real.pi/2) / (2 * Real.pi)⌉ with hkdef
      have hk1 : (L 1).im ≤ Real.pi/2 + (k : ℝ) * (2 * Real.pi) := by
        have h := Int.le_ceil (((L 1).im - Real.pi/2) / (2 * Real.pi))
        rw [← hkdef, div_le_iff₀ (by linarith only [hπ])] at h
        linarith only [h]
      have hk2 : Real.pi/2 + (k : ℝ) * (2 * Real.pi) ≤ (L 0).im := by
        have h := Int.ceil_lt_add_one (((L 1).im - Real.pi/2) / (2 * Real.pi))
        rw [← hkdef] at h
        have h3 : (k : ℝ) * (2 * Real.pi) < (L 1).im - Real.pi/2 + 2 * Real.pi := by
          have h2 : (k : ℝ) < ((L 1).im - Real.pi/2) / (2 * Real.pi) + 1 := h
          rw [div_add' _ _ _ (by linarith only [hπ] : (2 * Real.pi) ≠ 0)] at h2
          rw [lt_div_iff₀ (by linarith only [hπ])] at h2
          linarith only [h2]
        linarith only [h3, hbound]
      have hmem : Real.pi/2 + (k : ℝ) * (2 * Real.pi)
          ∈ Set.Icc ((L 1).im) ((L 0).im) := ⟨hk1, hk2⟩
      obtain ⟨t, ht⟩ := intermediate_value_univ (1 : I) (0 : I) hθc hmem
      exact ⟨t, k, by exact ht⟩
    · have hbound : (L 0).im + 2 * Real.pi ≤ (L 1).im := by
        have h1 : (1 : ℝ) ≤ ((n : ℝ)) := by exact_mod_cast hpos
        nlinarith only [him, hπ, h1]
      set k : ℤ := ⌈((L 0).im - Real.pi/2) / (2 * Real.pi)⌉ with hkdef
      have hk1 : (L 0).im ≤ Real.pi/2 + (k : ℝ) * (2 * Real.pi) := by
        have h := Int.le_ceil (((L 0).im - Real.pi/2) / (2 * Real.pi))
        rw [← hkdef, div_le_iff₀ (by linarith only [hπ])] at h
        linarith only [h]
      have hk2 : Real.pi/2 + (k : ℝ) * (2 * Real.pi) ≤ (L 1).im := by
        have h := Int.ceil_lt_add_one (((L 0).im - Real.pi/2) / (2 * Real.pi))
        rw [← hkdef] at h
        have h3 : (k : ℝ) * (2 * Real.pi) < (L 0).im - Real.pi/2 + 2 * Real.pi := by
          have h2 : (k : ℝ) < ((L 0).im - Real.pi/2) / (2 * Real.pi) + 1 := h
          rw [div_add' _ _ _ (by linarith only [hπ] : (2 * Real.pi) ≠ 0)] at h2
          rw [lt_div_iff₀ (by linarith only [hπ])] at h2
          linarith only [h2]
        linarith only [h3, hbound]
      have hmem : Real.pi/2 + (k : ℝ) * (2 * Real.pi)
          ∈ Set.Icc ((L 0).im) ((L 1).im) := ⟨hk1, hk2⟩
      obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) (1 : I) hθc hmem
      exact ⟨t, k, by exact ht⟩
  obtain ⟨t, k, htk⟩ := hkey
  exact hpin t k htk

end WindingRayZero

/-- **The basepoint sign window**: if the rotated velocity has negative vertical
component at the basepoint, it keeps it at every parameter whose image is close enough
to the basepoint. -/
theorem assertion_ii {γ g : ℝ → ℂ}
    (hγc : ContinuousOn γ (Set.Icc 0 1))
    (hgc : ContinuousOn g (Set.Icc 0 1))
    (hgcl : g 1 = g 0)
    (hinj : Set.InjOn γ (Set.Ico 0 1))
    (hneg : (Complex.I * g 0).im < 0) :
    ∃ ε > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Metric.closedBall (γ 0) ε →
      (Complex.I * g t).im < 0 := by
  have himc : ContinuousOn (fun t => (Complex.I * g t).im) (Set.Icc 0 1) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_const.mul hgc)
  -- endpoint windows
  have hev0 : ∀ᶠ t in nhdsWithin 0 (Set.Icc 0 1), (Complex.I * g t).im < 0 :=
    (himc 0 ⟨le_refl 0, zero_le_one⟩).eventually_lt_const hneg
  have hneg1 : (Complex.I * g 1).im < 0 := by
    rw [hgcl]
    exact hneg
  have hev1 : ∀ᶠ t in nhdsWithin 1 (Set.Icc 0 1), (Complex.I * g t).im < 0 :=
    (himc 1 ⟨zero_le_one, le_refl 1⟩).eventually_lt_const hneg1
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev0 hev1
  obtain ⟨δ₀, hδ₀, hwin0⟩ := hev0
  obtain ⟨δ₁, hδ₁, hwin1⟩ := hev1
  set δ : ℝ := min (min δ₀ δ₁) (1/2) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ₀ hδ₁) (by norm_num)
  have hδ0 : δ ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ1 : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδh : δ ≤ 1/2 := min_le_right _ _
  -- the middle arc stays away from the basepoint
  by_cases hKne : (Set.Icc (δ/2) (1 - δ/2)).Nonempty
  · obtain ⟨u₂, hu₂, hminOn⟩ := (isCompact_Icc (a := δ/2) (b := 1 - δ/2)).exists_isMinOn
      hKne ((hγc.mono (fun u hu => ⟨by linarith only [hu.1, hδ],
        by linarith only [hu.2, hδ]⟩)).sub continuousOn_const).norm
    set d₀ := ‖γ u₂ - γ 0‖ with hd₀def
    have hd₀ : 0 < d₀ := by
      rw [hd₀def, norm_pos_iff, sub_ne_zero]
      intro h
      have hu₂m : u₂ ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith only [hu₂.1, hδ],
        by linarith only [hu₂.2, hδ]⟩
      have h5 := hinj hu₂m (Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩) h
      linarith only [h5, hu₂.1, hδ]
    refine ⟨d₀/2, by positivity, ?_⟩
    intro t htm hball
    rw [Metric.mem_closedBall, dist_eq_norm] at hball
    have htK : t ∉ Set.Icc (δ/2) (1 - δ/2) := by
      intro htK
      have h6 := isMinOn_iff.mp hminOn t htK
      simp only at h6
      linarith only [h6, hball, hd₀]
    rw [Set.mem_Icc, not_and_or] at htK
    rcases htK with h | h
    · rw [not_le] at h
      refine hwin0 ⟨?_, htm⟩
      rw [Metric.mem_ball, Real.dist_eq,
        abs_of_nonneg (by linarith only [htm.1] : (0 : ℝ) ≤ t - 0)]
      linarith only [h, hδ0, hδ]
    · rw [not_le] at h
      refine hwin1 ⟨?_, htm⟩
      rw [Metric.mem_ball, Real.dist_eq,
        abs_of_nonpos (by linarith only [htm.2] : t - 1 ≤ 0)]
      linarith only [h, hδ1, hδ]
  · -- the middle interval is empty: the endpoint windows cover everything
    refine ⟨1, one_pos, ?_⟩
    intro t htm _
    exfalso
    rw [Set.nonempty_Icc, not_le] at hKne
    linarith only [hKne, hδh]

/-- **Affine unit maps preserve outer measure**: the image of an arbitrary set of
reals under `t ↦ c − εt` with `ε = ±1` has the same volume. -/
theorem affine_vol (c : ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (S : Set ℝ) :
    volume ((fun t => c - ε * t) '' S) = volume S := by
  rcases hε with h | h
  · have hinv : (fun t : ℝ => c - ε * t) '' S = (fun t : ℝ => c - t) ⁻¹' S := by
      rw [h]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨c - x, hx, by ring⟩
    rw [hinv]
    exact (Measure.measurePreserving_sub_left volume c).measure_preimage_emb
      (Homeomorph.measurableEmbedding (Homeomorph.subLeft c)) S
  · have hinv : (fun t : ℝ => c - ε * t) '' S = (fun t : ℝ => t + -c) ⁻¹' S := by
      rw [h]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x + -c, hx, by ring⟩
    rw [hinv]
    exact (measurePreserving_add_right volume (-c)).measure_preimage_emb
      (Homeomorph.measurableEmbedding (Homeomorph.addRight (-c))) S

/-- **The corridor interval cover**: a set of reals with positive corridor radii is
covered up to a null set by countably many pairwise disjoint closed intervals, each
centered at a member with radius below the corridor radius there. -/
theorem corridor_icov {E : Set ℝ} {ρ : ℝ → ℝ} (hρ : ∀ t ∈ E, 0 < ρ t) :
    ∃ A : ℕ → Set ℝ, ∃ c : ℕ → ℝ, ∃ r : ℕ → ℝ,
      (∀ n, A n = ∅ ∨ (c n ∈ E ∧ A n = Set.Icc (c n - r n) (c n + r n) ∧
        0 < r n ∧ r n < ρ (c n))) ∧
      volume (E \ ⋃ n, A n) = 0 ∧
      ∀ m n, m ≠ n → Disjoint (A m) (A n) := by
  classical
  obtain ⟨t, r₀, htc, hts, hr₀, hae, hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae volume
      (fun x => Set.Ioo 0 (ρ x)) E
      (fun x hx δ hδ => ⟨min (ρ x / 2) (δ / 2),
        ⟨lt_min (by linarith [hρ x hx]) (by linarith),
          lt_of_le_of_lt (min_le_left _ _) (by linarith [hρ x hx])⟩,
        ⟨lt_min (by linarith [hρ x hx]) (by linarith),
          lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩⟩)
      ρ hρ
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injective.mp htc
  set A : ℕ → Set ℝ := fun n =>
    if h : ∃ x : t, f x = n then
      Metric.closedBall (h.choose : ℝ) (r₀ (h.choose : ℝ)) else ∅ with hAdef
  set cf : ℕ → ℝ := fun n =>
    if h : ∃ x : t, f x = n then (h.choose : ℝ) else 0 with hcfdef
  refine ⟨A, cf, fun n => r₀ (cf n), ?_, ?_, ?_⟩
  · intro n
    rw [hAdef, hcfdef]
    simp only
    by_cases h : ∃ x : t, f x = n
    · rw [dif_pos h, dif_pos h]
      right
      have hmem : (h.choose : ℝ) ∈ t := h.choose.2
      have hr := hr₀ _ hmem
      exact ⟨hts hmem, Real.closedBall_eq_Icc, hr.1.1, hr.1.2⟩
    · rw [dif_neg h]
      exact Or.inl rfl
  · have hsub : (⋃ x ∈ t, Metric.closedBall x (r₀ x)) ⊆ ⋃ n, A n := by
      intro y hy
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp hy
      refine Set.mem_iUnion.mpr ⟨f ⟨x, hx⟩, ?_⟩
      rw [hAdef]
      simp only
      have hex : ∃ z : t, f z = f ⟨x, hx⟩ := ⟨⟨x, hx⟩, rfl⟩
      rw [dif_pos hex]
      have hchoose : hex.choose = ⟨x, hx⟩ := hf hex.choose_spec
      rw [hchoose]
      exact hyx
    refine measure_mono_null ?_ hae
    intro y hy
    exact ⟨hy.1, fun h2 => hy.2 (hsub h2)⟩
  · intro m n hmn
    rw [hAdef]
    simp only
    by_cases hm : ∃ x : t, f x = m
    · by_cases hn : ∃ x : t, f x = n
      · rw [dif_pos hm, dif_pos hn]
        refine hdisj hm.choose.2 hn.choose.2 ?_
        intro hEq
        refine hmn ?_
        rw [← hm.choose_spec, ← hn.choose_spec]
        congr 1
        exact Subtype.ext hEq
      · rw [dif_pos hm, dif_neg hn]
        exact Set.disjoint_empty _
    · rw [dif_neg hm]
      exact Set.empty_disjoint _

section SquareChain

open unitInterval

/-- **The square chain**: the left loop and the top loop wind together as the diagonal
loop. -/
theorem square_chain {γ gε : ℝ → ℂ}
    (hγc : ContinuousOn γ (Set.Icc 0 1)) (hεc : ContinuousOn gε (Set.Icc 0 1))
    (hclγ : γ 0 = γ 1) (hclε : gε 0 = gε 1)
    (hdisj : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ gε s) :
    ∃ pA pT pD : Path (γ 0 - gε 0) (γ 0 - gε 0),
      (∀ u : I, pA u = γ ((u : ℝ)) - gε 0)
      ∧ (∀ u : I, pT u = γ 0 - gε ((u : ℝ)))
      ∧ (∀ u : I, pD u = γ ((u : ℝ)) - gε ((u : ℝ)))
      ∧ windingNumber pA.toContinuousMap 0 + windingNumber pT.toContinuousMap 0
        = windingNumber pD.toContinuousMap 0 := by
  have hAc : Continuous fun u : I => γ ((u : ℝ)) - gε 0 :=
    (hγc.comp_continuous continuous_subtype_val fun u => u.2).sub continuous_const
  have hTc : Continuous fun u : I => γ 0 - gε ((u : ℝ)) :=
    continuous_const.sub (hεc.comp_continuous continuous_subtype_val fun u => u.2)
  have hDc : Continuous fun u : I => γ ((u : ℝ)) - gε ((u : ℝ)) :=
    (hγc.comp_continuous continuous_subtype_val fun u => u.2).sub
      (hεc.comp_continuous continuous_subtype_val fun u => u.2)
  set pA : Path (γ 0 - gε 0) (γ 0 - gε 0) :=
    ⟨⟨fun u : I => γ ((u : ℝ)) - gε 0, hAc⟩,
      by norm_num, by norm_num [← hclγ]⟩ with hpAdef
  set pT : Path (γ 0 - gε 0) (γ 0 - gε 0) :=
    ⟨⟨fun u : I => γ 0 - gε ((u : ℝ)), hTc⟩,
      by norm_num, by norm_num [← hclε]⟩ with hpTdef
  set pD : Path (γ 0 - gε 0) (γ 0 - gε 0) :=
    ⟨⟨fun u : I => γ ((u : ℝ)) - gε ((u : ℝ)), hDc⟩,
      by norm_num, by norm_num [← hclγ, ← hclε]⟩ with hpDdef
  refine ⟨pA, pT, pD, fun u => rfl, fun u => rfl, fun u => rfl, ?_⟩
  -- the square coordinates of the blended homotopy
  set Sv : I × I → ℝ :=
    fun p => (1 - (p.1 : ℝ)) * max 0 (2 * (p.2 : ℝ) - 1) + (p.1 : ℝ) * (p.2 : ℝ)
    with hSvdef
  set Tv : I × I → ℝ :=
    fun p => (1 - (p.1 : ℝ)) * min (2 * (p.2 : ℝ)) 1 + (p.1 : ℝ) * (p.2 : ℝ)
    with hTvdef
  have hSvc : Continuous Sv := by
    rw [hSvdef]
    fun_prop
  have hTvc : Continuous Tv := by
    rw [hTvdef]
    fun_prop
  have hSvmem : ∀ p : I × I, Sv p ∈ Set.Icc (0 : ℝ) 1 := by
    intro ⟨a, u⟩
    have ha := a.2
    have hu := u.2
    constructor
    · have h1 : (0 : ℝ) ≤ max 0 (2 * (u : ℝ) - 1) := le_max_left _ _
      nlinarith only [ha.1, ha.2, hu.1, hu.2, h1]
    · have h1 : max 0 (2 * (u : ℝ) - 1) ≤ 1 := by
        rw [max_le_iff]
        constructor <;> nlinarith only [hu.1, hu.2]
      nlinarith only [ha.1, ha.2, hu.1, hu.2, h1]
  have hTvmem : ∀ p : I × I, Tv p ∈ Set.Icc (0 : ℝ) 1 := by
    intro ⟨a, u⟩
    have ha := a.2
    have hu := u.2
    constructor
    · have h1 : (0 : ℝ) ≤ min (2 * (u : ℝ)) 1 := by
        rw [le_min_iff]
        constructor <;> nlinarith only [hu.1, hu.2]
      nlinarith only [ha.1, ha.2, hu.1, hu.2, h1]
    · have h1 : min (2 * (u : ℝ)) 1 ≤ 1 := min_le_right _ _
      nlinarith only [ha.1, ha.2, hu.1, hu.2, h1]
  have hHc : Continuous fun p : I × I => γ (Tv p) - gε (Sv p) :=
    (hγc.comp_continuous hTvc hTvmem).sub (hεc.comp_continuous hSvc hSvmem)
  have hHne : ∀ p : I × I, γ (Tv p) - gε (Sv p) ≠ 0 := fun p =>
    sub_ne_zero.mpr (hdisj (Sv p) (hSvmem p) (Tv p) (hTvmem p))
  have hface0 : ∀ u : I, γ (Tv (0, u)) - gε (Sv (0, u)) = (pA.trans pT) u := by
    intro u
    rw [Path.trans_apply]
    split_ifs with h
    · have hS : Sv (0, u) = 0 := by
        rw [hSvdef]
        simp only [Set.Icc.coe_zero]
        rw [max_eq_left (by nlinarith only [h] : 2 * (u : ℝ) - 1 ≤ 0)]
        ring
      have hT : Tv (0, u) = 2 * (u : ℝ) := by
        rw [hTvdef]
        simp only [Set.Icc.coe_zero]
        rw [min_eq_left (by nlinarith only [h] : 2 * (u : ℝ) ≤ 1)]
        ring
      rw [hS, hT]
      rfl
    · rw [not_le] at h
      have hS : Sv (0, u) = 2 * (u : ℝ) - 1 := by
        rw [hSvdef]
        simp only [Set.Icc.coe_zero]
        rw [max_eq_right (by nlinarith only [h] : (0 : ℝ) ≤ 2 * (u : ℝ) - 1)]
        ring
      have hT : Tv (0, u) = 1 := by
        rw [hTvdef]
        simp only [Set.Icc.coe_zero]
        rw [min_eq_right (by nlinarith only [h] : (1 : ℝ) ≤ 2 * (u : ℝ))]
        ring
      rw [hS, hT, ← hclγ]
      rfl
  have hface1 : ∀ u : I, γ (Tv (1, u)) - gε (Sv (1, u)) = pD u := by
    intro u
    have hS : Sv (1, u) = (u : ℝ) := by
      rw [hSvdef]
      simp only [Set.Icc.coe_one]
      ring
    have hT : Tv (1, u) = (u : ℝ) := by
      rw [hTvdef]
      simp only [Set.Icc.coe_one]
      ring
    rw [hS, hT]
    rfl
  have hend : ∀ (a : I) (u : I), u = 0 ∨ u = 1 →
      γ (Tv (a, u)) - gε (Sv (a, u)) = (pA.trans pT) u := by
    intro a u hu
    rcases hu with hu | hu
    · subst hu
      have hS : Sv (a, (0 : I)) = 0 := by
        rw [hSvdef]
        simp only [Set.Icc.coe_zero]
        rw [max_eq_left (by norm_num : (2 : ℝ) * 0 - 1 ≤ 0)]
        ring
      have hT : Tv (a, (0 : I)) = 0 := by
        rw [hTvdef]
        simp only [Set.Icc.coe_zero]
        rw [min_eq_left (by norm_num : (2 : ℝ) * 0 ≤ 1)]
        ring
      rw [hS, hT]
      have h2 : (pA.trans pT) 0 = γ 0 - gε 0 := (pA.trans pT).source
      rw [h2]
    · subst hu
      have hS : Sv (a, (1 : I)) = 1 := by
        rw [hSvdef]
        simp only [Set.Icc.coe_one]
        rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 2 * 1 - 1)]
        ring
      have hT : Tv (a, (1 : I)) = 1 := by
        rw [hTvdef]
        simp only [Set.Icc.coe_one]
        rw [min_eq_right (by norm_num : (1 : ℝ) ≤ 2 * 1)]
        ring
      rw [hS, hT]
      have h2 : (pA.trans pT) 1 = γ 0 - gε 0 := (pA.trans pT).target
      rw [h2, ← hclγ, ← hclε]
  set HH : ContinuousMap.HomotopyRel (pA.trans pT).toContinuousMap
      pD.toContinuousMap {0, 1} :=
    ⟨⟨⟨fun p : I × I => γ (Tv p) - gε (Sv p), hHc⟩, hface0, hface1⟩,
      fun a u hu => hend a u (by
        rcases hu with hu | hu
        · exact Or.inl hu
        · exact Or.inr hu)⟩ with hHHdef
  have hclAT : (pA.trans pT).toContinuousMap 0 = (pA.trans pT).toContinuousMap 1 := by
    have h1 : (pA.trans pT).toContinuousMap 0 = γ 0 - gε 0 := (pA.trans pT).source
    have h2 : (pA.trans pT).toContinuousMap 1 = γ 0 - gε 0 := (pA.trans pT).target
    rw [h1, h2]
  have hchain := windingNumber_eq_of_homotopicRel (q := 0) hclAT HH
    (fun t s => hHne (t, s))
  have hAne : ∀ t : I, pA t ≠ (0 : ℂ) := by
    intro t
    exact sub_ne_zero.mpr (hdisj 0 ⟨le_refl 0, zero_le_one⟩ ((t : ℝ)) t.2)
  have hTne : ∀ t : I, pT t ≠ (0 : ℂ) := by
    intro t
    exact sub_ne_zero.mpr (hdisj ((t : ℝ)) t.2 0 ⟨le_refl 0, zero_le_one⟩)
  have htrans := windingNumber_trans pA pT hAne hTne
  rw [← hchain, htrans]

end SquareChain

/-- **The per-piece level count**: a set of levels with corridor radii and a height
map that is affine of unit slope on each corridor, injective, betweenness-preserving,
and valued in an attained set has outer measure at most that of the attained set. -/
theorem piece_count {E : Set ℝ} {F : ℝ → ℝ} {Λ : Set ℝ} {ρ : ℝ → ℝ}
    (hρ : ∀ t ∈ E, 0 < ρ t)
    (haff : ∀ c ∈ E, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ k : ℝ,
      ∀ t ∈ E, |t - c| < ρ c → F t = k - ε * t)
    (hatt : ∀ t ∈ E, F t ∈ Λ)
    (hinj : ∀ t ∈ E, ∀ t' ∈ E, F t = F t' → t = t')
    (hmono : ∀ t ∈ E, ∀ t' ∈ E, ∀ t'' ∈ E,
      min (F t) (F t') < F t'' → F t'' < max (F t) (F t') →
      min t t' < t'' ∧ t'' < max t t') :
    volume E ≤ volume Λ := by
  obtain ⟨A, cA, rA, hAcases, hAnull, hAdisj⟩ := corridor_icov hρ
  -- split the level set along the carriers
  have hsplit : volume E ≤ ∑' n, volume (E ∩ A n) := by
    have h1 : E = (E \ ⋃ n, A n) ∪ (E ∩ ⋃ n, A n) := by
      rw [Set.diff_union_inter]
    calc volume E = volume ((E \ ⋃ n, A n) ∪ (E ∩ ⋃ n, A n)) := by rw [← h1]
      _ ≤ volume (E \ ⋃ n, A n) + volume (E ∩ ⋃ n, A n) := measure_union_le _ _
      _ = volume (E ∩ ⋃ n, A n) := by rw [hAnull, zero_add]
      _ = volume (⋃ n, E ∩ A n) := by rw [Set.inter_iUnion]
      _ ≤ ∑' n, volume (E ∩ A n) := measure_iUnion_le _
  -- the height images of the carrier pieces
  set H : ℕ → Set ℝ := fun n => F '' (E ∩ A n) with hHdef
  have hvol : ∀ n, volume (E ∩ A n) = volume (H n) := by
    intro n
    rcases hAcases n with hempty | ⟨hcE, hAe, hrpos, hrρ⟩
    · rw [hHdef]
      simp only
      rw [hempty]
      simp
    · obtain ⟨ε, hε, k, hk⟩ := haff (cA n) hcE
      have himg : H n = (fun t => k - ε * t) '' (E ∩ A n) := by
        rw [hHdef]
        simp only
        refine Set.image_congr ?_
        intro t ht
        refine hk t ht.1 ?_
        have h2 := ht.2
        rw [hAe] at h2
        rw [abs_lt]
        exact ⟨by linarith [h2.1, hrρ], by linarith [h2.2, hrρ]⟩
      rw [himg, affine_vol k hε]
  -- the images sit in the attained set
  have hsub : ∀ n, H n ⊆ Λ := by
    rintro n y ⟨t, ht, rfl⟩
    exact hatt t ht.1
  -- carrier order separation in the levels
  have htsep : ∀ m n, m ≠ n → ∀ x ∈ E ∩ A m, ∀ y ∈ E ∩ A n, x ≠ y := by
    intro m n hmn x hx y hy hEq
    have h2 := hAdisj m n hmn
    exact (Set.disjoint_left.mp h2 hx.2) (hEq ▸ hy.2)
  have hosep : ∀ m n, m ≠ n →
      (∀ x ∈ E ∩ A m, ∀ y ∈ E ∩ A n, x < y) ∨
      (∀ x ∈ E ∩ A m, ∀ y ∈ E ∩ A n, y < x) := by
    intro m n hmn
    rcases hAcases m with hm | ⟨-, hAm, hrm, -⟩
    · left
      intro x hx
      rw [hm] at hx
      exact absurd hx.2 (Set.notMem_empty x)
    rcases hAcases n with hn | ⟨-, hAn, hrn, -⟩
    · left
      intro x hx y hy
      rw [hn] at hy
      exact absurd hy.2 (Set.notMem_empty y)
    have hkey : cA m + rA m < cA n - rA n ∨ cA n + rA n < cA m - rA m := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h3, h4⟩ := hcon
      have hw1 : max (cA m - rA m) (cA n - rA n) ∈ A m := by
        rw [hAm]
        refine ⟨le_max_left _ _, ?_⟩
        rcases max_cases (cA m - rA m) (cA n - rA n) with ⟨h5, -⟩ | ⟨h5, -⟩ <;>
          rw [h5]
        · linarith only [hrm]
        · linarith only [h3]
      have hw2 : max (cA m - rA m) (cA n - rA n) ∈ A n := by
        rw [hAn]
        refine ⟨le_max_right _ _, ?_⟩
        rcases max_cases (cA m - rA m) (cA n - rA n) with ⟨h5, -⟩ | ⟨h5, -⟩ <;>
          rw [h5]
        · linarith only [h4]
        · linarith only [hrn]
      exact Set.disjoint_left.mp (hAdisj m n hmn) hw1 hw2
    rcases hkey with h5 | h5
    · left
      intro x hx y hy
      have hx2 := hx.2
      have hy2 := hy.2
      rw [hAm] at hx2
      rw [hAn] at hy2
      linarith only [hx2.2, hy2.1, h5]
    · right
      intro x hx y hy
      have hx2 := hx.2
      have hy2 := hy.2
      rw [hAm] at hx2
      rw [hAn] at hy2
      linarith only [hx2.1, hy2.2, h5]
  -- transport of the order separation through the height map
  have hcore : ∀ P Q : Set ℝ, P ⊆ E → Q ⊆ E →
      (∀ x ∈ P, ∀ y ∈ Q, x < y) →
      ∀ a ∈ P, ∀ b ∈ Q, F a < F b → ∀ u ∈ P, ∀ v ∈ Q, F u < F v := by
    intro P Q hPE hQE hPQ a ha b hb hab u hu v hv
    rcases lt_trichotomy (F u) (F v) with h6 | h6 | h6
    · exact h6
    · exact absurd (hinj u (hPE hu) v (hQE hv) h6)
        (ne_of_lt (hPQ u hu v hv))
    · exfalso
      rcases lt_trichotomy (F v) (F a) with h7 | h7 | h7
      · have h8 := hmono v (hQE hv) b (hQE hb) a (hPE ha)
          (by rw [min_def]; split_ifs with hif <;> linarith only [h7, hab, hif])
          (by rw [max_def]; split_ifs with hif <;> linarith only [h7, hab, hif])
        have h9 := hPQ a ha v hv
        have h10 := hPQ a ha b hb
        rcases min_cases v b with ⟨h11, -⟩ | ⟨h11, -⟩ <;>
          rw [h11] at h8 <;> linarith only [h8.1, h9, h10]
      · exact absurd (hinj v (hQE hv) a (hPE ha) h7)
          (ne_of_gt (hPQ a ha v hv))
      · have h8 := hmono a (hPE ha) u (hPE hu) v (hQE hv)
          (by rw [min_def]; split_ifs with hif <;> linarith only [h7, h6, hif])
          (by rw [max_def]; split_ifs with hif <;> linarith only [h7, h6, hif])
        have h9 := hPQ a ha v hv
        have h10 := hPQ u hu v hv
        rcases max_cases a u with ⟨h11, -⟩ | ⟨h11, -⟩ <;>
          rw [h11] at h8 <;> linarith only [h8.2, h9, h10]
  have hFsep : ∀ m n, m ≠ n →
      (∀ x ∈ H m, ∀ y ∈ H n, x < y) ∨ (∀ x ∈ H m, ∀ y ∈ H n, y < x) := by
    intro m n hmn
    rcases Set.eq_empty_or_nonempty (E ∩ A m) with hEm | ⟨a, ha⟩
    · left
      rintro x ⟨t, ht, rfl⟩
      rw [hEm] at ht
      exact absurd ht (Set.notMem_empty t)
    rcases Set.eq_empty_or_nonempty (E ∩ A n) with hEn | ⟨b, hb⟩
    · left
      rintro x hx y ⟨t, ht, rfl⟩
      rw [hEn] at ht
      exact absurd ht (Set.notMem_empty t)
    have hPE : E ∩ A m ⊆ E := Set.inter_subset_left
    have hQE : E ∩ A n ⊆ E := Set.inter_subset_left
    have hcore2 : ∀ P Q : Set ℝ, P ⊆ E → Q ⊆ E →
        (∀ x ∈ P, ∀ y ∈ Q, x < y) →
        ∀ a ∈ P, ∀ b ∈ Q, F b < F a → ∀ u ∈ P, ∀ v ∈ Q, F v < F u := by
      intro P Q hPE hQE hPQ a ha b hb hab u hu v hv
      rcases lt_trichotomy (F v) (F u) with h6 | h6 | h6
      · exact h6
      · exact absurd (hinj v (hQE hv) u (hPE hu) h6)
          (ne_of_gt (hPQ u hu v hv))
      · exfalso
        rcases lt_trichotomy (F a) (F v) with h7 | h7 | h7
        · have h8 := hmono v (hQE hv) b (hQE hb) a (hPE ha)
            (by rw [min_def]; split_ifs with hif <;> linarith only [h7, hab, hif])
            (by rw [max_def]; split_ifs with hif <;> linarith only [h7, hab, hif])
          have h9 := hPQ a ha v hv
          have h10 := hPQ a ha b hb
          rcases min_cases v b with ⟨h11, -⟩ | ⟨h11, -⟩ <;>
            rw [h11] at h8 <;> linarith only [h8.1, h9, h10]
        · exact absurd (hinj a (hPE ha) v (hQE hv) h7)
            (ne_of_lt (hPQ a ha v hv))
        · have h8 := hmono a (hPE ha) u (hPE hu) v (hQE hv)
            (by rw [min_def]; split_ifs with hif <;> linarith only [h7, h6, hif])
            (by rw [max_def]; split_ifs with hif <;> linarith only [h7, h6, hif])
          have h9 := hPQ a ha v hv
          have h10 := hPQ u hu v hv
          rcases max_cases a u with ⟨h11, -⟩ | ⟨h11, -⟩ <;>
            rw [h11] at h8 <;> linarith only [h8.2, h9, h10]
    rcases hosep m n hmn with hlr | hlr
    · rcases lt_trichotomy (F a) (F b) with hc | hc | hc
      · left
        rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
        exact hcore _ _ hPE hQE hlr a ha b hb hc u hu v hv
      · exact absurd (hinj a (hPE ha) b (hQE hb) hc) (ne_of_lt (hlr a ha b hb))
      · right
        rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
        exact hcore2 _ _ hPE hQE hlr a ha b hb hc u hu v hv
    · have hlr' : ∀ y ∈ E ∩ A n, ∀ x ∈ E ∩ A m, y < x :=
        fun y hy x hx => hlr x hx y hy
      rcases lt_trichotomy (F a) (F b) with hc | hc | hc
      · left
        rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
        exact hcore2 _ _ hQE hPE hlr' b hb a ha hc v hv u hu
      · exact absurd (hinj a (hPE ha) b (hQE hb) hc) (ne_of_gt (hlr a ha b hb))
      · right
        rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
        exact hcore _ _ hQE hPE hlr' b hb a ha hc v hv u hu
  calc volume E ≤ ∑' n, volume (E ∩ A n) := hsplit
    _ = ∑' n, volume (H n) := tsum_congr hvol
    _ ≤ volume Λ := ordered_sum hsub hFsep

/-- The half-open dyadic interval at scale `k` and position `i`. -/
noncomputable def dyadic (k : ℕ) (i : ℤ) : Set ℝ :=
  Set.Ico ((i : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k)

/-- **Dyadic nesting**: two intersecting dyadic intervals with ordered scales are
nested. -/
theorem dyadic_nested {k k' : ℕ} {i i' : ℤ} (hk : k ≤ k')
    (hmeet : (dyadic k i ∩ dyadic k' i').Nonempty) :
    dyadic k' i' ⊆ dyadic k i := by
  obtain ⟨x, hx1, hx2⟩ := hmeet
  rw [dyadic, Set.mem_Ico] at hx1 hx2
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h2k' : (0 : ℝ) < 2 ^ k' := by positivity
  set d : ℕ := k' - k with hddef
  have hpow : (2 : ℝ) ^ k' = 2 ^ k * 2 ^ d := by
    rw [← pow_add]
    congr 1
    omega
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hy1 : (i : ℝ) ≤ x * 2 ^ k := (div_le_iff₀ h2k).mp hx1.1
  have hy2 : x * 2 ^ k < (i : ℝ) + 1 := by
    have h3 := hx1.2
    rw [lt_div_iff₀ h2k] at h3
    linarith only [h3]
  have hy3 : (i' : ℝ) ≤ x * 2 ^ k' := (div_le_iff₀ h2k').mp hx2.1
  have hy4 : x * 2 ^ k' < (i' : ℝ) + 1 := by
    have h3 := hx2.2
    rw [lt_div_iff₀ h2k'] at h3
    linarith only [h3]
  have hz1 : (i : ℝ) * 2 ^ d < (i' : ℝ) + 1 := by
    calc (i : ℝ) * 2 ^ d ≤ x * 2 ^ k * 2 ^ d :=
          mul_le_mul_of_nonneg_right hy1 h2d.le
      _ = x * 2 ^ k' := by rw [hpow]; ring
      _ < (i' : ℝ) + 1 := hy4
  have hz2 : (i' : ℝ) < ((i : ℝ) + 1) * 2 ^ d := by
    calc (i' : ℝ) ≤ x * 2 ^ k' := hy3
      _ = x * 2 ^ k * 2 ^ d := by rw [hpow]; ring
      _ < ((i : ℝ) + 1) * 2 ^ d := mul_lt_mul_of_pos_right hy2 h2d
  have hzz1 : (i * 2 ^ d : ℤ) < i' + 1 := by
    have h3 : ((i * 2 ^ d : ℤ) : ℝ) < ((i' + 1 : ℤ) : ℝ) := by
      push_cast
      linarith only [hz1]
    exact_mod_cast h3
  have hzz2 : (i' : ℤ) < (i + 1) * 2 ^ d := by
    have h3 : ((i' : ℤ) : ℝ) < (((i + 1) * 2 ^ d : ℤ) : ℝ) := by
      push_cast
      linarith only [hz2]
    exact_mod_cast h3
  have hw1 : ((i * 2 ^ d : ℤ) : ℝ) ≤ (i' : ℝ) := by
    have h4 : (i * 2 ^ d : ℤ) ≤ i' := by omega
    exact_mod_cast h4
  have hw2 : ((i' + 1 : ℤ) : ℝ) ≤ (((i + 1) * 2 ^ d : ℤ) : ℝ) := by
    have h4 : (i' : ℤ) + 1 ≤ (i + 1) * 2 ^ d := by omega
    exact_mod_cast h4
  intro z hz
  rw [dyadic, Set.mem_Ico] at hz ⊢
  constructor
  · calc (i : ℝ) / 2 ^ k = (i : ℝ) * 2 ^ d / 2 ^ k' := by
          rw [hpow]
          field_simp
      _ ≤ (i' : ℝ) / 2 ^ k' := by
          have h5 : (i : ℝ) * 2 ^ d ≤ (i' : ℝ) := by
            have h6 := hw1
            push_cast at h6
            linarith only [h6]
          gcongr
      _ ≤ z := hz.1
  · calc z < ((i' : ℝ) + 1) / 2 ^ k' := hz.2
      _ ≤ ((i : ℝ) + 1) * 2 ^ d / 2 ^ k' := by
          have h5 : (i' : ℝ) + 1 ≤ ((i : ℝ) + 1) * 2 ^ d := by
            have h6 := hw2
            push_cast at h6
            linarith only [h6]
          gcongr
      _ = ((i : ℝ) + 1) / 2 ^ k := by
          rw [hpow]
          field_simp

section InnerDegree

open unitInterval

/-- **The ray-hit exclusion**: at a minimum-height basepoint with the negative normal
window, no point of the cross loop lies on the upward vertical ray. -/
theorem top_kill {γ g : ℝ → ℂ} {ε ς M εA : ℝ}
    (hε : 0 < ε) (hς : ς = 1 ∨ ς = -1)
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖g u‖ ≤ M)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ 0).im ≤ (γ t).im)
    (hwin : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Metric.closedBall (γ 0) εA →
      (Complex.I * (((ς : ℝ) : ℂ) * g t)).im < 0)
    (hεA : ε * M ≤ εA)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ¬((γ 0 - (γ t - ((ς * ε : ℝ) : ℂ) * (Complex.I * g t))).re = 0
      ∧ 0 < (γ 0 - (γ t - ((ς * ε : ℝ) : ℂ) * (Complex.I * g t))).im) := by
  rintro ⟨hre, him⟩
  set W : ℂ := ((ς * ε : ℝ) : ℂ) * (Complex.I * g t) with hWdef
  set V : ℂ := γ 0 - (γ t - W) with hVdef
  set d : ℝ := V.im with hddef
  have hns : ∀ z : ℂ, ‖z‖^2 = z.re^2 + z.im^2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h1 : d = (γ 0).im - (γ t).im + W.im := by
    rw [hddef, hVdef]
    simp only [Complex.sub_im]
    ring
  have hWim : d ≤ W.im := by
    have h2 := hmin t ht
    linarith only [h1, h2]
  have hdist : ‖γ 0 - γ t‖^2 = ‖W‖^2 + d^2 - 2*d*W.im := by
    have hval : γ 0 - γ t = V - W := by
      rw [hVdef]
      ring
    rw [hval, hns (V - W), hns W]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [hre]
    ring
  have hWn : ‖W‖ ≤ ε * M := by
    rw [hWdef, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have habs : |ς * ε| = ε := by
      rcases hς with h | h <;> rw [h]
      · rw [one_mul, abs_of_pos hε]
      · rw [neg_one_mul, abs_neg, abs_of_pos hε]
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hM t ht) hε.le
  have hMnn : (0 : ℝ) ≤ ε * M :=
    le_trans (norm_nonneg W) hWn
  have hball : γ t ∈ Metric.closedBall (γ 0) εA := by
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    have h2 : ‖γ 0 - γ t‖^2 ≤ (ε*M)^2 := by
      nlinarith only [hdist, hWim, him, hWn, norm_nonneg W]
    have h3 : ‖γ 0 - γ t‖ ≤ ε * M := by
      by_contra hc
      rw [not_le] at hc
      nlinarith only [h2, hc, hMnn]
    linarith only [h3, hεA]
  have hwin' := hwin t ht hball
  have hWeq : W = (ε : ℂ) * (Complex.I * (((ς : ℝ) : ℂ) * g t)) := by
    rw [hWdef]
    push_cast
    ring
  have hWim2 : W.im = ε * (Complex.I * (((ς : ℝ) : ℂ) * g t)).im := by
    rw [hWeq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  nlinarith only [hwin', hWim, him, hWim2, hε]

/-- **The inner degree**: the winding of the loop about the inward offset basepoint
equals the winding of its velocity loop about the origin. -/
theorem inner_degree {γ g : ℝ → ℂ} {ε ς M εA : ℝ}
    (hγc : ContinuousOn γ (Set.Icc 0 1)) (hclγ : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (hε : 0 < ε) (hς : ς = 1 ∨ ς = -1)
    (hgc : ContinuousOn g (Set.Icc 0 1))
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0)
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖g u‖ ≤ M)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ 0).im ≤ (γ t).im)
    (hwin : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Metric.closedBall (γ 0) εA →
      (Complex.I * (((ς : ℝ) : ℂ) * g t)).im < 0)
    (hεA : ε * M ≤ εA)
    (hdisj : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t ≠ γ s - ((ς * ε : ℝ) : ℂ) * (Complex.I * g s))
    (A : C(I, ℂ))
    (hA : ∀ u : I, A u = γ ((u : ℝ)) - (γ 0 - ((ς * ε : ℝ) : ℂ) * (Complex.I * g 0)))
    (hgw : Continuous fun t : I => g ((t : ℝ))) :
    windingNumber A 0 = windingNumber ⟨fun t : I => g ((t : ℝ)), hgw⟩ 0 := by
  set gε : ℝ → ℂ := fun s => γ s - ((ς * ε : ℝ) : ℂ) * (Complex.I * g s) with hgεdef
  have hgεapp : ∀ s, gε s = γ s - ((ς * ε : ℝ) : ℂ) * (Complex.I * g s) := fun s => rfl
  have hεc : ContinuousOn gε (Set.Icc 0 1) :=
    hγc.sub (continuousOn_const.mul (continuousOn_const.mul hgc))
  have hclε : gε 0 = gε 1 := by
    rw [hgεapp, hgεapp, hclγ, ← hgcl]
  have hdisj' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ gε s := hdisj
  obtain ⟨pA, pT, pD, hpA, hpT, hpD, hsum⟩ := square_chain hγc hεc hclγ hclε hdisj'
  -- the top loop avoids the upward vertical ray, so its winding vanishes
  have hTcl : pT.toContinuousMap 0 = pT.toContinuousMap 1 := by
    have h1 : pT.toContinuousMap 0 = γ 0 - gε 0 := pT.source
    have h2 : pT.toContinuousMap 1 = γ 0 - gε 0 := pT.target
    rw [h1, h2]
  have hTne : ∀ u : I, pT.toContinuousMap u ≠ (0 : ℂ) := by
    intro u
    have h1 : pT.toContinuousMap u = pT u := rfl
    rw [h1, hpT u]
    exact sub_ne_zero.mpr (hdisj' ((u : ℝ)) u.2 0 ⟨le_refl 0, zero_le_one⟩)
  have hTray : ∀ u : I,
      ¬((pT.toContinuousMap u - 0).re = 0 ∧ 0 < (pT.toContinuousMap u - 0).im) := by
    intro u
    have h1 : pT.toContinuousMap u = pT u := rfl
    rw [sub_zero, h1, hpT u, hgεapp]
    exact top_kill hε hς hM hmin hwin hεA u.2
  have hT0 : windingNumber pT.toContinuousMap 0 = 0 :=
    winding_ray_zero hTcl hTne hTray
  -- the diagonal loop is the constant multiple of the velocity loop
  set c : ℂ := ((ς * ε : ℝ) : ℂ) * Complex.I with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    apply mul_ne_zero
    · rw [Ne, Complex.ofReal_eq_zero]
      rcases hς with h | h <;> rw [h]
      · rw [one_mul]
        exact ne_of_gt hε
      · rw [neg_one_mul, neg_eq_zero]
        exact ne_of_gt hε
    · exact Complex.I_ne_zero
  have hDval : ∀ u : I, pD u = c * g ((u : ℝ)) := by
    intro u
    rw [hpD u, hgεapp, hcdef]
    ring
  have hw : Continuous fun t : I => c * g ((t : ℝ)) := continuous_const.mul hgw
  have hcm := winding_const_mul hc hgw hgcl hgne hw
  have hDeq : pD.toContinuousMap = (⟨fun t : I => c * g ((t : ℝ)), hw⟩ : C(I, ℂ)) := by
    apply ContinuousMap.ext
    intro u
    exact hDval u
  have hAeq : A = pA.toContinuousMap := by
    apply ContinuousMap.ext
    intro u
    have h1 : pA.toContinuousMap u = pA u := rfl
    rw [hA u, h1, hpA u, hgεapp]
  rw [hAeq]
  rw [hT0, add_zero] at hsum
  rw [hsum, hDeq]
  exact hcm

end InnerDegree

/-- **Dyadic membership pins the position**: a point lies in the scale-`k` dyadic at
position `i` exactly when `i` is the floor of `x·2^k`. -/
theorem dyadic_mem_iff {k : ℕ} {i : ℤ} {x : ℝ} :
    x ∈ dyadic k i ↔ i = ⌊x * 2 ^ k⌋ := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [dyadic, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ h2k] at h1
    rw [lt_div_iff₀ h2k] at h2
    symm
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast h1
    · linarith only [h2]
  · rintro rfl
    constructor
    · rw [div_le_iff₀ h2k]
      exact Int.floor_le _
    · rw [lt_div_iff₀ h2k]
      linarith only [Int.lt_floor_add_one (x * 2 ^ k)]
/-- **The dyadic locator**: every point sits in a dyadic interval of some scale that
fits inside any prescribed neighborhood. -/
theorem dyadic_locate (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, dyadic k ⌊x * 2 ^ k⌋ ⊆ Set.Ioo (x - δ) (x + δ) := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hδ)
    (by norm_num : (1 : ℝ) / 2 < 1)
  refine ⟨k, ?_⟩
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hk' : 1 / 2 ^ k < δ / 2 := by
    calc (1 : ℝ) / 2 ^ k = (1 / 2) ^ k := by rw [div_pow, one_pow]
      _ < δ / 2 := hk
  have hfl : (⌊x * 2 ^ k⌋ : ℝ) ≤ x * 2 ^ k := Int.floor_le _
  have hfl2 : x * 2 ^ k < (⌊x * 2 ^ k⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  intro z hz
  rw [dyadic, Set.mem_Ico] at hz
  have hz1 := hz.1
  have hz2 := hz.2
  rw [div_le_iff₀ h2k] at hz1
  rw [lt_div_iff₀ h2k] at hz2
  constructor
  · have h3 : x * 2 ^ k - 1 < z * 2 ^ k := by linarith only [hfl2, hz1]
    have h4 : (x * 2 ^ k - 1) / 2 ^ k < z := by
      rw [div_lt_iff₀ h2k]
      linarith only [h3]
    have h5 : (x * 2 ^ k - 1) / 2 ^ k = x - 1 / 2 ^ k := by
      field_simp
    rw [h5] at h4
    linarith only [h4, hk', hδ]
  · have h3 : z * 2 ^ k < x * 2 ^ k + 1 := by linarith only [hfl, hz2]
    have h4 : z < (x * 2 ^ k + 1) / 2 ^ k := by
      rw [lt_div_iff₀ h2k]
      linarith only [h3]
    have h5 : (x * 2 ^ k + 1) / 2 ^ k = x + 1 / 2 ^ k := by
      field_simp
    rw [h5] at h4
    linarith only [h4, hk', hδ]

/-- **The exact dyadic corridor cover**: an open-free set with positive corridor
radii is exactly covered by countably many pairwise disjoint dyadic intervals, each
fitted inside the corridor of one of its points. -/
theorem dyadic_cover {U : Set ℝ} {δf : ℝ → ℝ} (hδf : ∀ x ∈ U, 0 < δf x) :
    ∃ I : ℕ → Set ℝ,
      (∀ n, I n = ∅ ∨ ∃ k : ℕ, ∃ i : ℤ, I n = dyadic k i ∧
        ∃ x ∈ U, dyadic k i ⊆ Set.Ioo (x - δf x) (x + δf x)) ∧
      (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
      U ⊆ ⋃ n, I n := by
  classical
  set P : ℕ → ℤ → Prop := fun k i => ∃ x ∈ U,
    dyadic k i ⊆ Set.Ioo (x - δf x) (x + δf x) with hPdef
  set M : ℕ → ℤ → Prop := fun k i => P k i ∧
    ∀ k' i', k' < k → dyadic k i ⊆ dyadic k' i' → ¬ P k' i' with hMdef
  have hxmem : ∀ (x : ℝ) (k : ℕ), x ∈ dyadic k ⌊x * 2 ^ k⌋ := fun x k =>
    dyadic_mem_iff.mpr rfl
  have hcover : ∀ x ∈ U, ∃ k i, M k i ∧ x ∈ dyadic k i := by
    intro x hx
    obtain ⟨k₀, hk₀⟩ := dyadic_locate x (hδf x hx)
    have hex : ∃ k, P k ⌊x * 2 ^ k⌋ := ⟨k₀, x, hx, hk₀⟩
    have hPks : P (Nat.find hex) ⌊x * 2 ^ Nat.find hex⌋ := Nat.find_spec hex
    refine ⟨Nat.find hex, ⌊x * 2 ^ Nat.find hex⌋, ⟨hPks, ?_⟩,
      hxmem x (Nat.find hex)⟩
    intro k' i' hk' hsub hP'
    have hx' : x ∈ dyadic k' i' := hsub (hxmem x (Nat.find hex))
    have hi' : i' = ⌊x * 2 ^ k'⌋ := dyadic_mem_iff.mp hx'
    rw [hi'] at hP'
    exact absurd hP' (Nat.find_min hex hk')
  have hdisj : ∀ k i k' i', M k i → M k' i' → ¬(k = k' ∧ i = i') →
      Disjoint (dyadic k i) (dyadic k' i') := by
    intro k i k' i' hM hM' hne
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hcon
    have hmeet : (dyadic k i ∩ dyadic k' i').Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hcon
    rcases lt_trichotomy k k' with hlt | rfl | hlt
    · exact (hM'.2 k i hlt (dyadic_nested hlt.le hmeet)) hM.1
    · obtain ⟨y, hy⟩ := hmeet
      have h3 := dyadic_mem_iff.mp hy.1
      have h4 := dyadic_mem_iff.mp hy.2
      exact hne ⟨rfl, h3.trans h4.symm⟩
    · have hmeet' : (dyadic k' i' ∩ dyadic k i).Nonempty := by
        obtain ⟨y, hy⟩ := hmeet
        exact ⟨y, hy.2, hy.1⟩
      exact (hM.2 k' i' hlt (dyadic_nested hlt.le hmeet')) hM'.1
  set I : ℕ → Set ℝ := fun n =>
    if h : ∃ p : ℕ × ℤ, Encodable.encode p = n ∧ M p.1 p.2 then
      dyadic h.choose.1 h.choose.2 else ∅ with hIdef
  refine ⟨I, ?_, ?_, ?_⟩
  · intro n
    rw [hIdef]
    simp only
    by_cases h : ∃ p : ℕ × ℤ, Encodable.encode p = n ∧ M p.1 p.2
    · rw [dif_pos h]
      exact Or.inr ⟨h.choose.1, h.choose.2, rfl, h.choose_spec.2.1⟩
    · rw [dif_neg h]
      exact Or.inl rfl
  · intro m n hmn
    rw [hIdef]
    simp only
    by_cases hm : ∃ p : ℕ × ℤ, Encodable.encode p = m ∧ M p.1 p.2
    · by_cases hn : ∃ p : ℕ × ℤ, Encodable.encode p = n ∧ M p.1 p.2
      · rw [dif_pos hm, dif_pos hn]
        refine hdisj _ _ _ _ hm.choose_spec.2 hn.choose_spec.2 ?_
        rintro ⟨h1, h2⟩
        refine hmn ?_
        rw [← hm.choose_spec.1, ← hn.choose_spec.1]
        congr 1
        exact Prod.ext h1 h2
      · rw [dif_pos hm, dif_neg hn]
        exact Set.disjoint_empty _
    · rw [dif_neg hm]
      exact Set.empty_disjoint _
  · intro x hx
    obtain ⟨k, i, hM, hmem⟩ := hcover x hx
    refine Set.mem_iUnion.mpr ⟨Encodable.encode ((k, i) : ℕ × ℤ), ?_⟩
    rw [hIdef]
    simp only
    have hex : ∃ p : ℕ × ℤ, Encodable.encode p = Encodable.encode ((k, i) : ℕ × ℤ)
        ∧ M p.1 p.2 := ⟨(k, i), rfl, hM⟩
    rw [dif_pos hex]
    have hch : hex.choose = ((k, i) : ℕ × ℤ) :=
      Encodable.encode_injective hex.choose_spec.1
    rw [hch]
    exact hmem

/-- **Margined affinity in a given chart**: at any parameter of an anchored all-time
leaf whose point lies in the inner half ball of a prescribed margined chart, the
inner-ball visits of nearby-level leaves have heights affine in the level. -/
theorem cert_at_crossing_in {q Ψw : ℂ → ℂ} {W : Set ℂ}
    (hWo : IsOpen W) (hWd : DifferentiableOn ℂ Ψw W) (hWinj : Set.InjOn Ψw W)
    (hWH : W ⊆ {z : ℂ | 0 < z.im}) (hWne : ∀ w ∈ W, q w ≠ 0)
    (hWsq : ∀ x ∈ W, deriv Ψw x ^ 2 = -(-q x))
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {ϑ : ℝ → ℂ} (hϑ : IsTrajOn q ϑ Set.univ)
    {τ : ℝ → ℂ} (hτ : IsTrajOn (fun z => -q z) τ Set.univ)
    {tb : ℝ} (hanch : τ 0 = ϑ tb) (ub : ℝ)
    {c₀ : ℂ} {R : ℝ} (hR : 0 < R) (hmarg : Metric.ball c₀ (5 * R) ⊆ Ψw '' W)
    (hxW : τ ub ∈ W) (hcen : Ψw (τ ub) ∈ Metric.ball c₀ (R / 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ c : ℝ,
      ∀ t : ℝ, |t - tb| < ρ →
      ∀ σ : ℝ → ℂ, IsTrajOn (fun z => -q z) σ Set.univ → σ 0 = ϑ t →
      ∀ u : ℝ, σ u ∈ W → Ψw (σ u) ∈ Metric.ball c₀ R →
      (Ψw (σ u)).im = c - ε * t := by
  rcases lt_trichotomy ub 0 with hub | hub | hub
  · have hτr : IsTrajOn (fun z => -q z) (fun w => τ (-w)) Set.univ := by
      have h1 := traj_reverse hτ
      rwa [show (fun u : ℝ => -u) ⁻¹' Set.univ = Set.univ from
        Set.preimage_univ] at h1
    have hanchr : (fun w => τ (-w)) 0 = ϑ tb := by
      simp only [neg_zero]
      exact hanch
    have htWr : (fun w => τ (-w)) (-ub) ∈ W := by
      simp only [neg_neg]
      exact hxW
    have hcenr : Ψw ((fun w => τ (-w)) (-ub)) ∈ Metric.ball c₀ (R / 2) := by
      simp only [neg_neg]
      exact hcen
    obtain ⟨ρ, hρ, ε, hε, c, hcert⟩ := cert_affine hbigon hϑ hτr hanchr
      (by linarith : (0 : ℝ) < -ub) hWo hWd hWinj hWH hWne hWsq hR hmarg
      htWr hcenr
    exact ⟨ρ, hρ, ε, hε, c, hcert⟩
  · have hanchW : ϑ tb ∈ W := by
      rw [← hanch, ← hub]
      exact hxW
    obtain ⟨ρ₁, hρ₁, ε₀, hε₀, hdev⟩ := anchor_dev hWo hWd hWsq hϑ hanchW
    have hcenb : Ψw (ϑ tb) ∈ Metric.ball c₀ (R / 2) := by
      rw [← hanch, ← hub]
      exact hcen
    refine ⟨min ρ₁ (R / 2), lt_min hρ₁ (by linarith), ε₀, hε₀,
      (Ψw (ϑ tb)).im + ε₀ * tb, ?_⟩
    intro t ht σ hσ hσ0 u huW huball
    have ht1 : |t - tb| < ρ₁ := lt_of_lt_of_le ht (min_le_left _ _)
    have ht2 : |t - tb| < R / 2 := lt_of_lt_of_le ht (min_le_right _ _)
    obtain ⟨hϑtW, hϑtval⟩ := hdev t ht1
    have hσ0W : σ 0 ∈ W := by
      rw [hσ0]
      exact hϑtW
    have hσ0ball : Ψw (σ 0) ∈ Metric.ball c₀ R := by
      rw [hσ0, hϑtval, Metric.mem_ball]
      have h6 : dist (Ψw (ϑ tb) + Complex.I * ((-ε₀ * (t - tb) : ℝ) : ℂ)) c₀
          ≤ dist (Ψw (ϑ tb)) c₀ + |(-ε₀ * (t - tb) : ℝ)| := by
        rw [dist_eq_norm, dist_eq_norm,
          show Ψw (ϑ tb) + Complex.I * ((-ε₀ * (t - tb) : ℝ) : ℂ) - c₀
              = (Ψw (ϑ tb) - c₀) + Complex.I * ((-ε₀ * (t - tb) : ℝ) : ℂ) from by
            ring]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]
      have h7 : |(-ε₀ * (t - tb) : ℝ)| = |t - tb| := by
        rw [abs_mul, abs_neg]
        rcases hε₀ with h' | h' <;> rw [h'] <;> norm_num
      have h8 : dist (Ψw (ϑ tb)) c₀ < R / 2 := Metric.mem_ball.mp hcenb
      rw [h7] at h6
      linarith [h6, h8, ht2]
    have hvis := leaf_visit_height hWo hWd hWinj hWH hWne hWsq hbigon hR
      hmarg hσ huW hσ0W huball hσ0ball
    rw [hvis, hσ0, hϑtval, Complex.add_im]
    have h9 : (Complex.I * ((-ε₀ * (t - tb) : ℝ) : ℂ)).im = -ε₀ * (t - tb) := by
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [h9]
    ring
  · obtain ⟨ρ, hρ, ε, hε, c, hcert⟩ := cert_affine hbigon hϑ hτ hanch hub
      hWo hWd hWinj hWH hWne hWsq hR hmarg hxW hcen
    exact ⟨ρ, hρ, ε, hε, c, hcert⟩

/-- **A margined transverse chart at a regular point**: every regular point of the
upper half plane carries an injective transverse natural chart whose development
contains a five-fold margined ball about the point's value. -/
theorem margined_chart {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    {w : ℂ} (hw : 0 < w.im) (hq0 : q w ≠ 0) :
    ∃ W : Set ℂ, ∃ Ψ : ℂ → ℂ, ∃ R : ℝ, 0 < R ∧ IsOpen W ∧
      DifferentiableOn ℂ Ψ W ∧ Set.InjOn Ψ W ∧ W ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ z ∈ W, q z ≠ 0) ∧ (∀ x ∈ W, deriv Ψ x ^ 2 = -(-q x)) ∧
      Metric.ball (Ψ w) (5 * R) ⊆ Ψ '' W ∧ w ∈ W := by
  obtain ⟨W, Ψ, ρ₀, hρ₀, hWo, hwW, hWH, hWne', hΨd, hΨinj, hΨsq, himg⟩ :=
    box_data (q := fun z => -q z) hq.neg hw (neg_ne_zero.mpr hq0)
  refine ⟨W, Ψ, ρ₀ / 5, by linarith, hWo, hΨd, hΨinj, hWH, ?_, hΨsq, ?_, hwW⟩
  · intro z hz h0
    exact hWne' z hz (by rw [h0]; exact neg_zero)
  · rw [show 5 * (ρ₀ / 5) = ρ₀ from by ring]
    exact himg

set_option maxHeartbeats 400000 in
-- Heartbeats: the deep local-definition tower needs an enlarged elaboration budget.
/-- **The two-point leaf-displacement estimate**: the level gap between two leaf
crossings of a connecting flat path is at most the path's horizontal variation. -/
theorem hcoarea_of_bigons {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ)
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (q : ℂ → ℂ) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (q : ℂ → ℂ) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False) :
    ∀ ϑ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) ϑ Set.univ →
    ∀ B : Atlas (qdNeg q : ℂ → ℂ),
    (∀ᵐ t ∂(volume : Measure ℝ), ϑ t ∈ good (qdNeg q : ℂ → ℂ) B) →
    ∀ T : ℝ, 0 < T → Set.InjOn ϑ (Set.Icc 0 T) →
    ∀ p : ℝ → ℂ, IsFlatPath p (ϑ 0) (ϑ T) →
    ∀ (t₀ t₁ s₀ s₁ : ℝ) (τ₀ τ₁ : ℝ → ℂ),
    IsTrajOn (fun z => -(q : ℂ → ℂ) z) τ₀ Set.univ →
    IsTrajOn (fun z => -(q : ℂ → ℂ) z) τ₁ Set.univ →
    τ₀ 0 = ϑ t₀ → τ₁ 0 = ϑ t₁ →
    t₀ ∈ Set.Ioo 0 T → t₁ ∈ Set.Ioo 0 T →
    s₀ ∈ Set.Icc (0 : ℝ) 1 → s₁ ∈ Set.Icc (0 : ℝ) 1 →
    (∃ u, p s₀ = τ₀ u) → (∃ u, p s₁ = τ₁ u) →
    ENNReal.ofReal |t₁ - t₀| ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1,
      horizontalDensity (q : ℂ → ℂ) p s := by
  intro ϑ hϑ B hae T hT hinjT p hp t₀ t₁ s₀ s₁ τ₀ τ₁ hτ₀ hτ₁ ha₀ ha₁ ht₀ ht₁
    hs₀ hs₁ hx₀ hx₁
  rcases eq_or_ne t₀ t₁ with rfl | htne
  · simp
  -- the level window and its good part
  set J : Set ℝ := Set.Ioo (min t₀ t₁) (max t₀ t₁) with hJdef
  have hJvol : ENNReal.ofReal |t₁ - t₀| = volume J := by
    rw [hJdef, Real.volume_Ioo]
    congr 1
    rcases le_total t₀ t₁ with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (by linarith)]
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (by linarith)]
      ring
  set D : Set ℝ := J ∩ {t | ϑ t ∈ good (qdNeg q : ℂ → ℂ) B} with hDdef
  have hDJ : D ⊆ J := Set.inter_subset_left
  have hDIoo : D ⊆ Set.Ioo 0 T := by
    intro t ht
    have h2 := hDJ ht
    rw [hJdef] at h2
    constructor
    · rcases min_cases t₀ t₁ with ⟨h3, -⟩ | ⟨h3, -⟩ <;> rw [h3] at h2
      · linarith [h2.1, ht₀.1]
      · linarith [h2.1, ht₁.1]
    · rcases max_cases t₀ t₁ with ⟨h3, -⟩ | ⟨h3, -⟩ <;> rw [h3] at h2
      · linarith [h2.2, ht₀.2]
      · linarith [h2.2, ht₁.2]
  have hvolJD : volume J ≤ volume D := by
    have h2 : J ⊆ D ∪ {t | ¬ ϑ t ∈ good (qdNeg q : ℂ → ℂ) B} := by
      intro t ht
      by_cases h3 : ϑ t ∈ good (qdNeg q : ℂ → ℂ) B
      · exact Or.inl ⟨ht, h3⟩
      · exact Or.inr h3
    calc volume J ≤ volume (D ∪ {t | ¬ ϑ t ∈ good (qdNeg q : ℂ → ℂ) B}) :=
          measure_mono h2
      _ ≤ volume D + volume {t | ¬ ϑ t ∈ good (qdNeg q : ℂ → ℂ) B} :=
          measure_union_le _ _
      _ = volume D := by rw [ae_iff.mp hae, add_zero]
  -- the leaf family and its crossings
  set τfam : ℝ → ℝ → ℂ := fun t u => B.flow u (ϑ t) with hτfamdef
  have hτfam : ∀ t ∈ D, IsTrajOn (fun w => -(q : ℂ → ℂ) w) (τfam t) Set.univ ∧
      τfam t 0 = ϑ t := by
    intro t ht
    have hgood : ϑ t ∈ good (qdNeg q : ℂ → ℂ) B := ht.2
    exact ⟨isTrajOn_congr (fun w => qdNeg_apply q w)
      (flow_alltime (qdNeg q).holo B hgood), flow_zero B hgood.1 hgood.2.1⟩
  set pC : C(unitInterval, ℂ) := ⟨fun s => p s,
    hp.cont.comp_continuous continuous_subtype_val (fun s => s.2)⟩ with hpCdef
  have hϑIci : IsTrajOn (q : ℂ → ℂ) ϑ (Set.Ici (-1 : ℝ)) :=
    traj_mono hϑ (Set.subset_univ _)
  have hcrossx : ∀ t : ℝ, ∃ (s : unitInterval) (u : ℝ), t ∈ D →
      p s = τfam t u := by
    intro t
    by_cases ht : t ∈ D
    · obtain ⟨s, u, hsu⟩ := level_crossing q.holo hbigon hbigonH hϑIci hT
        (hτfam t ht).1 (hDIoo ht) (hτfam t ht).2 pC hp.init hp.final
        (fun s => hp.upper s s.2)
      exact ⟨s, u, fun _ => hsu⟩
    · exact ⟨0, 0, fun h => absurd h ht⟩
  choose sc uc hscuc using hcrossx
  -- the regular parameter set with its chart corridors
  set U : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < (p s).im ∧
    (q : ℂ → ℂ) (p s) ≠ 0} with hUdef
  have hUdata : ∀ x : ℝ, ∃ (W : Set ℂ) (Ψ : ℂ → ℂ) (R δ : ℝ), x ∈ U →
      0 < R ∧ 0 < δ ∧ IsOpen W ∧ DifferentiableOn ℂ Ψ W ∧ Set.InjOn Ψ W ∧
      W ⊆ {z : ℂ | 0 < z.im} ∧ (∀ z ∈ W, (q : ℂ → ℂ) z ≠ 0) ∧
      (∀ y ∈ W, deriv Ψ y ^ 2 = -(-(q : ℂ → ℂ) y)) ∧
      Metric.ball (Ψ (p x)) (5 * R) ⊆ Ψ '' W ∧
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, |s' - x| ≤ δ →
        p s' ∈ W ∧ Ψ (p s') ∈ Metric.ball (Ψ (p x)) (R / 8) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨W, Ψ, R, hR, hWo, hWd, hWinj, hWH, hWne, hWsq, hmarg, hmem⟩ :=
        margined_chart q.holo hx.2.1 hx.2.2
      have hcont : ContinuousWithinAt p (Set.Icc (0 : ℝ) 1) x :=
        hp.cont x hx.1
      have hev : ∀ᶠ s' in nhdsWithin x (Set.Icc (0 : ℝ) 1),
          p s' ∈ W ∧ Ψ (p s') ∈ Metric.ball (Ψ (p x)) (R / 8) := by
        have h2 : {z : ℂ | z ∈ W ∧ Ψ z ∈ Metric.ball (Ψ (p x)) (R / 8)}
            ∈ 𝓝 (p x) := by
          refine Filter.inter_mem (hWo.mem_nhds hmem) ?_
          have h3 : ContinuousAt Ψ (p x) :=
            (hWd.continuousOn.continuousAt (hWo.mem_nhds hmem))
          exact h3 (Metric.ball_mem_nhds _ (by linarith))
        exact hcont.eventually_mem h2
      rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
      obtain ⟨δ₂, hδ₂, hball⟩ := hev
      refine ⟨W, Ψ, R, δ₂ / 2, fun _ => ⟨hR, by linarith, hWo, hWd, hWinj,
        hWH, hWne, hWsq, hmarg, ?_⟩⟩
      intro s' hs' hd
      exact hball ⟨by rw [Metric.mem_ball, Real.dist_eq]; linarith [hd], hs'⟩
    · exact ⟨∅, id, 1, 1, fun h => absurd h hx⟩
  choose Wf Ψf Rf δf hUpack using hUdata
  obtain ⟨Ipc, hIcases, hIdisj, hIcov⟩ := dyadic_cover
    (U := U) (δf := δf) (fun x hx => ((hUpack x hx).2.1))
  -- the level classes per piece
  set E : ℕ → Set ℝ := fun n => {t ∈ D | ((sc t : ℝ)) ∈ Ipc n} with hEdef
  have hscU : ∀ t ∈ D, ((sc t : ℝ)) ∈ U := by
    intro t ht
    refine ⟨(sc t).2, hp.upper _ (sc t).2, ?_⟩
    have h2 := hscuc t ht
    obtain ⟨V₂, -, hpV₂, -, hV₂ne, -⟩ :=
      ((hτfam t ht).1).chart (uc t) (Set.mem_univ (uc t))
    intro h0
    refine hV₂ne _ hpV₂ ?_
    rw [← h2] at hpV₂ ⊢
    rw [h0]
    exact neg_zero
  have hDE : D ⊆ ⋃ n, E n := by
    intro t ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hIcov (hscU t ht))
    exact Set.mem_iUnion.mpr ⟨n, ht, hn⟩
  have hvolDE : volume D ≤ ∑' n, volume (E n) :=
    le_trans (measure_mono hDE) (measure_iUnion_le _)
  -- the per-piece bound
  have hpieces : ∀ n : ℕ, ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ipc n ∧
      G ⊆ Set.Icc (0 : ℝ) 1 ∧
      volume (E n) ≤ ∫⁻ s in G, horizontalDensity (q : ℂ → ℂ) p s := by
    intro n
    rcases Set.eq_empty_or_nonempty (E n) with hEe | ⟨tw, htw⟩
    · exact ⟨∅, MeasurableSet.empty, Set.empty_subset _, Set.empty_subset _,
        by rw [hEe]; simp⟩
    rcases hIcases n with hIe | ⟨k, i, hIeq, xn, hxnU, hfit⟩
    · exfalso
      have h2 := htw.2
      rw [hIe] at h2
      exact Set.notMem_empty _ h2
    obtain ⟨hRpos, hδpos, hWo, hWd, hWinj, hWH, hWne, hWsq, hmarg, hcorr⟩ :=
      hUpack xn hxnU
    -- the corridor bound on the closed hull of the piece
    set av : ℝ := (i : ℝ) / 2 ^ k with havdef
    set bv : ℝ := ((i : ℝ) + 1) / 2 ^ k with hbvdef
    have hIab : Ipc n = Set.Ico av bv := hIeq
    have havbv : av < bv := by
      rw [havdef, hbvdef]
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      rw [div_lt_div_iff_of_pos_right h2k]
      linarith
    have hcorrIcc : ∀ s' ∈ Set.Icc av bv, |s' - xn| ≤ δf xn := by
      intro s' hs'
      have hbfit : bv ≤ xn + δf xn := by
        by_contra hcon
        push Not at hcon
        have h3 : max av (xn + δf xn) ∈ Ipc n := by
          rw [hIab]
          exact ⟨le_max_left _ _, by
            rcases max_cases av (xn + δf xn) with ⟨h4, -⟩ | ⟨h4, -⟩ <;>
              rw [h4]
            · exact havbv
            · exact hcon⟩
        have h5 := hfit (hIeq ▸ h3)
        rw [Set.mem_Ioo] at h5
        rcases max_cases av (xn + δf xn) with ⟨h4, h6⟩ | ⟨h4, -⟩ <;>
          rw [h4] at h5
        · linarith [h5.2, h6]
        · linarith [h5.2]
      have hafit : xn - δf xn < av := by
        have h3 : av ∈ Ipc n := by rw [hIab]; exact ⟨le_rfl, havbv⟩
        have h5 := hfit (hIeq ▸ h3)
        rw [Set.mem_Ioo] at h5
        exact h5.1
      rw [abs_le]
      exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    -- the trimmed interval inside the unit domain
    set a' : ℝ := max av 0 with ha'def
    set b' : ℝ := min bv 1 with hb'def
    have hsc01 : (sc tw : ℝ) ∈ Set.Icc (0 : ℝ) 1 := (sc tw).2
    have hscIn : ((sc tw : ℝ)) ∈ Set.Ico av bv := hIab ▸ htw.2
    have hsca' : a' ≤ ((sc tw : ℝ)) := max_le hscIn.1 hsc01.1
    have hscb' : ((sc tw : ℝ)) ≤ b' := le_min hscIn.2.le hsc01.2
    have ha'b' : a' ≤ b' := le_trans hsca' hscb'
    have hIccsub : Set.Icc a' b' ⊆ Set.Icc av bv :=
      Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hIcc01 : Set.Icc a' b' ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    have htrkW : ∀ s' ∈ Set.Icc a' b', p s' ∈ Wf xn ∧
        Ψf xn (p s') ∈ Metric.ball (Ψf xn (p xn)) (Rf xn / 8) :=
      fun s' hs' => hcorr s' (hIcc01 hs') (hcorrIcc s' (hIccsub hs'))
    -- the corridor membership of the crossings of piece levels
    have hscmem : ∀ t ∈ E n, ((sc t : ℝ)) ∈ Set.Icc a' b' := by
      intro t ht
      have h2 : ((sc t : ℝ)) ∈ Set.Ico av bv := hIab ▸ ht.2
      exact ⟨max_le h2.1 (sc t).2.1, le_min h2.2.le (sc t).2.2⟩
    have hvisit : ∀ t ∈ E n, τfam t (uc t) ∈ Wf xn ∧
        Ψf xn (τfam t (uc t)) ∈ Metric.ball (Ψf xn (p xn)) (Rf xn / 8) := by
      intro t ht
      have h2 := htrkW _ (hscmem t ht)
      rw [hscuc t ht.1] at h2
      exact h2
    have hball8R : Metric.ball (Ψf xn (p xn)) (Rf xn / 8)
        ⊆ Metric.ball (Ψf xn (p xn)) (Rf xn) :=
      Metric.ball_subset_ball (by linarith)
    have hball82 : Metric.ball (Ψf xn (p xn)) (Rf xn / 8)
        ⊆ Metric.ball (Ψf xn (p xn)) (Rf xn / 2) :=
      Metric.ball_subset_ball (by linarith)
    have hball84 : Metric.ball (Ψf xn (p xn)) (Rf xn / 8)
        ⊆ Metric.ball (Ψf xn (p xn)) (Rf xn / 4) :=
      Metric.ball_subset_ball (by linarith)
    have hcertdata : ∀ c : ℝ, ∃ ρv εv kv : ℝ, c ∈ E n → 0 < ρv ∧
        (εv = 1 ∨ εv = -1) ∧ ∀ t ∈ E n, |t - c| < ρv →
        (Ψf xn (p ((sc t : ℝ)))).im = kv - εv * t := by
      intro c
      by_cases hc : c ∈ E n
      · obtain ⟨ρv, hρv, εv, hεv, kv, hlaw⟩ := cert_at_crossing_in hWo hWd
          hWinj hWH hWne hWsq hbigon hϑ (hτfam c hc.1).1 (hτfam c hc.1).2
          (uc c) hRpos hmarg (hvisit c hc).1 (hball82 (hvisit c hc).2)
        refine ⟨ρv, εv, kv, fun _ => ⟨hρv, hεv, ?_⟩⟩
        intro t ht hnear
        have h5 := hlaw t hnear (τfam t) (hτfam t ht.1).1 (hτfam t ht.1).2
          (uc t) (hvisit t ht).1 (hball8R (hvisit t ht).2)
        rw [← hscuc t ht.1] at h5
        exact h5
      · exact ⟨1, 1, 0, fun h => absurd h hc⟩
    choose ρf εff kff hcert using hcertdata
    have hheq : ∀ t ∈ E n, (Ψf xn (p ((sc t : ℝ)))).im
        = (Ψf xn (τfam t (uc t))).im := by
      intro t ht
      rw [hscuc t ht.1]
    have hinjE : ∀ t ∈ E n, ∀ t' ∈ E n,
        (Ψf xn (p ((sc t : ℝ)))).im = (Ψf xn (p ((sc t' : ℝ)))).im → t = t' := by
      intro t ht t' ht' hFeq
      rw [hheq t ht, hheq t' ht'] at hFeq
      obtain ⟨u, u', hshare⟩ := equal_height_meet hWo hWd hWinj hWH hWne hWsq
        hRpos hmarg (hτfam t ht.1).1 (hτfam t' ht'.1).1
        (hvisit t ht).1 (hvisit t' ht').1 (hball8R (hvisit t ht).2)
        (hball8R (hvisit t' ht').2) hFeq
      exact leaves_meet_level q.holo hbigon hbigonH hϑIci
        (hτfam t ht.1).1 (hτfam t' ht'.1).1
        (by linarith [(hDIoo ht.1).1] : (-1 : ℝ) < t)
        (by linarith [(hDIoo ht'.1).1] : (-1 : ℝ) < t')
        (hτfam t ht.1).2 (hτfam t' ht'.1).2 hshare
    have hmonoE : ∀ t ∈ E n, ∀ t' ∈ E n, ∀ t'' ∈ E n,
        min ((Ψf xn (p ((sc t : ℝ)))).im) ((Ψf xn (p ((sc t' : ℝ)))).im)
          < (Ψf xn (p ((sc t'' : ℝ)))).im →
        (Ψf xn (p ((sc t'' : ℝ)))).im
          < max ((Ψf xn (p ((sc t : ℝ)))).im) ((Ψf xn (p ((sc t' : ℝ)))).im) →
        min t t' < t'' ∧ t'' < max t t' := by
      intro t ht t' ht' t'' ht'' hlo hhi
      rw [hheq t ht, hheq t' ht', hheq t'' ht''] at hlo hhi
      rcases le_total ((Ψf xn (τfam t (uc t))).im)
          ((Ψf xn (τfam t' (uc t'))).im) with hor | hor
      · rw [min_eq_left hor] at hlo
        rw [max_eq_right hor] at hhi
        have h6 := level_monotone q.holo hbigon hbigonH hϑ hWo hWd hWinj hWH
          hWne hWsq hRpos hmarg (hτfam t ht.1).1 (hτfam t' ht'.1).1
          (hτfam t'' ht''.1).1 (hτfam t ht.1).2 (hτfam t' ht'.1).2
          (hτfam t'' ht''.1).2 (hvisit t ht).1 (hvisit t' ht').1
          (hvisit t'' ht'').1 (hball84 (hvisit t ht).2)
          (hball84 (hvisit t' ht').2) (hball84 (hvisit t'' ht'').2) hlo hhi
        rw [Set.mem_Ioo] at h6
        exact h6
      · rw [min_eq_right hor] at hlo
        rw [max_eq_left hor] at hhi
        have h6 := level_monotone q.holo hbigon hbigonH hϑ hWo hWd hWinj hWH
          hWne hWsq hRpos hmarg (hτfam t' ht'.1).1 (hτfam t ht.1).1
          (hτfam t'' ht''.1).1 (hτfam t' ht'.1).2 (hτfam t ht.1).2
          (hτfam t'' ht''.1).2 (hvisit t' ht').1 (hvisit t ht).1
          (hvisit t'' ht'').1 (hball84 (hvisit t' ht').2)
          (hball84 (hvisit t ht).2) (hball84 (hvisit t'' ht'').2) hlo hhi
        rw [Set.mem_Ioo, min_comm, max_comm] at h6
        exact h6
    have hcount := piece_count (E := E n)
      (F := fun t => (Ψf xn (p ((sc t : ℝ)))).im)
      (Λ := {h : ℝ | ∃ s' ∈ Set.Icc a' b', (Ψf xn (p s')).im = h})
      (ρ := ρf) (fun t ht => (hcert t ht).1)
      (fun c hc => ⟨εff c, (hcert c hc).2.1, kff c,
        fun t ht hn => (hcert c hc).2.2 t ht hn⟩)
      (fun t ht => ⟨(sc t : ℝ), hscmem t ht, rfl⟩) hinjE hmonoE
    have hΛbound := piece_lambda_bound hWo hWd hWsq ha'b'
      (hp.cont.mono hIcc01)
      (hp.ac.mono (by
        rw [Set.uIcc_of_le ha'b', Set.uIcc_of_le zero_le_one]
        exact hIcc01))
      (fun s' hs' => (htrkW s' hs').1)
      (fun l hl => hl)
    refine ⟨Set.Ioo a' b', measurableSet_Ioo, ?_, ?_, ?_⟩
    · intro z hz
      rw [hIab]
      exact ⟨le_trans (le_max_left _ _) hz.1.le,
        lt_of_lt_of_le hz.2 (min_le_left _ _)⟩
    · exact fun z hz => ⟨le_trans (le_max_right _ _) hz.1.le,
        le_trans hz.2.le (min_le_right _ _)⟩
    · calc volume (E n) ≤ volume {h : ℝ | ∃ s' ∈ Set.Icc a' b',
            (Ψf xn (p s')).im = h} := hcount
        _ ≤ ∫⁻ s in Set.Icc a' b', horizontalDensity (q : ℂ → ℂ) p s :=
            hΛbound
        _ = ∫⁻ s in Set.Ioo a' b', horizontalDensity (q : ℂ → ℂ) p s :=
            (setLIntegral_congr Ioo_ae_eq_Icc).symm
  choose Gf hGmeas hGIpc hG01 hGbound using hpieces
  have hGdisj : Pairwise (Function.onFun Disjoint Gf) := fun m n hmn =>
    Set.disjoint_of_subset (hGIpc m) (hGIpc n) (hIdisj m n hmn)
  calc ENNReal.ofReal |t₁ - t₀| = volume J := hJvol
    _ ≤ volume D := hvolJD
    _ ≤ ∑' n, volume (E n) := hvolDE
    _ ≤ ∑' n, ∫⁻ s in Gf n, horizontalDensity (q : ℂ → ℂ) p s :=
        ENNReal.tsum_le_tsum hGbound
    _ = ∫⁻ s in ⋃ n, Gf n, horizontalDensity (q : ℂ → ℂ) p s :=
        (lintegral_iUnion hGmeas hGdisj _).symm
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1, horizontalDensity (q : ℂ → ℂ) p s :=
        lintegral_mono_set (Set.iUnion_subset hG01)

end RiemannDynamics

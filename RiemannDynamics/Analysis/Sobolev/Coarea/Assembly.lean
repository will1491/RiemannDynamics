/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.Coarea.PerPiece

/-!
# The planar co-area formula — the assembly

Final of three files for the sharp planar co-area inequality (see `Coarea.Foundations` and
`Coarea.PerPiece` for the ingredients). The per-piece core `coarea_piece_le` is assembled over the
critical and regular sets into the headline result:

* `coarea_critical_le` — the `{∇u = 0}` set contributes nothing (via the scalar Lusin partition —
  *not* Sard, which fails for merely Lipschitz maps);
* `coarea_regular_le` — the area-formula assembly over `{∇u ≠ 0}` (Lusin decomposition with the
  square maps `(u, im)` / `(u, re)` + `coarea_piece_le` per piece);
* `coarea_set_sharp` — the unweighted set form `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ ∫⁻ z in A, ‖∇u‖`;
* `eilenberg_coarea_grad_le` — the gradient-weighted Eilenberg inequality (the headline result,
  consumed by `QC/GeometricDifferentiable.lean`), obtained from `coarea_set_sharp` by layer-cake.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RiemannDynamics.Coarea

/-- **Critical part of the co-area inequality: the `{∇u = 0}` set contributes nothing.**

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0})) = 0`.

NOT via Sard (which fails for merely Lipschitz `u`). Proof: the non-differentiability set is
`volume`-null (Rademacher), contributing `0` by `coarea_null_le`. For the genuine critical points,
apply the **scalar** Lusin partition `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` to
`u` (with tolerance `δ`): every piece `tₙ` that *contains* a point `z` with `fderiv ℝ u z = 0`
satisfies `‖Aₙ‖ ≤ δ` (since `‖fderiv ℝ u z - Aₙ‖ ≤ δ` and `fderiv ℝ u z = 0`), so `u` is
`2δ`-Lipschitz on `tₙ ∩ A` and `eilenberg_coarea_planar_metric_meas` bounds its contribution by
`2δ · c₀ · volume (tₙ ∩ A)`; pieces with no critical point contribute `0` (empty level-set
intersection). Summing the disjoint pieces gives `≤ 2δ · c₀ · volume A`; let `δ → 0`. (For
`volume A = ∞`, exhaust `A` by finite-measure pieces.) -/
theorem coarea_critical_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0})) = 0 := by
  classical
  have hucont : Continuous u := hu.continuous
  -- The proportionality constant `μH[2] = c₀ • volume`.
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- ===================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets `A'`.
  --      (Dynkin on each compact ball + closed-ball exhaustion; same proof
  --      as in `coarea_set_sharp`.)
  -- ===================================================================
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        rw [hc₀v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- ===================================================================
  -- (1)  CORE finite-volume lemma.  For any measurable `E` contained in the
  --      DIFFERENTIABLE critical set with finite area, the level-set integral
  --      vanishes.  (Lusin partition with `Aₙ = fderiv u yₙ = 0`.)
  -- ===================================================================
  have hfin_case : ∀ {E : Set ℂ}, MeasurableSet E → volume E ≠ ∞ →
      E ⊆ {z | fderiv ℝ u z = 0} → E ⊆ {z | DifferentiableAt ℝ u z} →
      ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ E) = 0 := by
    intro E hEmeas hEfin hEcrit hEdiff
    rw [← nonpos_iff_eq_zero]
    -- It suffices to bound the integral by `c₀ * volume E * δ` for every `δ > 0`.
    have key : ∀ δ : ℝ≥0, 0 < δ →
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ E) ≤ (δ : ℝ≥0∞) * (c₀ * volume E) := by
      intro δ δpos
      -- Lusin partition of `E` (as the `s`-set) with tolerance `δ`.
      have hf' : ∀ x ∈ E, HasFDerivWithinAt u (fderiv ℝ u x) E x := by
        intro x hx
        exact (hEdiff hx).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, A, hdisj, htmeas, hsub, happrox, hAval⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
          u E (fun z => fderiv ℝ u z) hf' (fun _ => δ) (fun _ => δpos.ne')
      -- For each `n`, `u` is `δ`-Lipschitz on `E ∩ t n`.
      have hpiece_meas : ∀ n, MeasurableSet (E ∩ t n) :=
        fun n => hEmeas.inter (htmeas n)
      have hpiece_lip : ∀ n, LipschitzOnWith δ u (E ∩ t n) := by
        intro n
        rcases eq_or_ne E ∅ with hEempty | hEne
        · -- `E = ∅`: piece empty.
          rw [hEempty]; simp only [Set.empty_inter]
          exact lipschitzOnWith_empty δ u
        · -- `A n = fderiv u y n = 0` for `y n ∈ E ⊆ Crit`.
          obtain ⟨y, hyE, hAy⟩ := hAval (Set.nonempty_iff_ne_empty.2 hEne) n
          have hA0 : A n = 0 := by rw [hAy]; exact hEcrit hyE
          -- `ApproximatesLinearOn u 0 (E ∩ t n) δ` ⟹ `LipschitzOnWith δ u (E ∩ t n)`.
          have hap : ApproximatesLinearOn u (A n) (E ∩ t n) δ := happrox n
          rw [hA0] at hap
          have hlip := hap.lipschitzOnWith
          have hsub0 : (u - ⇑(0 : ℂ →L[ℝ] ℝ)) = u := by
            funext z; simp
          rwa [hsub0] at hlip
      -- Per-piece Eilenberg bound.
      have hpiece_bound : ∀ n,
          ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n))
            ≤ (δ : ℝ≥0∞) * (c₀ * volume (E ∩ t n)) := by
        intro n
        have hb := eilenberg_coarea_planar_metric_meas (hpiece_lip n) (hpiece_meas n)
        rw [hc₀v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hb
        exact hb
      -- Assemble via disjoint additivity of the slice measure.
      have hslice_eq : ∀ c : ℝ,
          μH[1] (u ⁻¹' {c} ∩ E) = ∑' n, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n)) := by
        intro c
        have hcover_c : u ⁻¹' {c} ∩ E = ⋃ n, u ⁻¹' {c} ∩ (E ∩ t n) := by
          rw [← Set.inter_iUnion]
          congr 1
          apply Set.Subset.antisymm
          · intro z hz
            obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hsub hz)
            exact Set.mem_iUnion.2 ⟨n, hz, hn⟩
          · exact Set.iUnion_subset (fun n => Set.inter_subset_left)
        rw [hcover_c]
        refine measure_iUnion ?_ ?_
        · intro i j hij
          refine (hdisj hij).mono ?_ ?_ <;>
            exact fun z hz => hz.2.2
        · intro n
          exact (hucont.measurable (measurableSet_singleton c)).inter (hpiece_meas n)
      calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ E)
          = ∫⁻ c, ∑' n, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n)) := by
            apply lintegral_congr; exact hslice_eq
        _ = ∑' n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n)) :=
            lintegral_tsum (fun n => slice_aemeas (hpiece_meas n))
        _ ≤ ∑' n, (δ : ℝ≥0∞) * (c₀ * volume (E ∩ t n)) :=
            ENNReal.tsum_le_tsum hpiece_bound
        _ = (δ : ℝ≥0∞) * (c₀ * ∑' n, volume (E ∩ t n)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        _ = (δ : ℝ≥0∞) * (c₀ * volume E) := by
            congr 2
            rw [← measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_right
              Set.inter_subset_right) (fun n => hpiece_meas n)]
            congr 1
            apply Set.Subset.antisymm
            · exact Set.iUnion_subset (fun n => Set.inter_subset_left)
            · intro z hz
              obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hsub hz)
              exact Set.mem_iUnion.2 ⟨n, hz, hn⟩
    -- Let `δ → 0`:  if the integral were positive, pick `δ` with `δ * C < integral`.
    have hconst_fin : c₀ * volume E ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hEfin
    by_contra hpos
    rw [nonpos_iff_eq_zero] at hpos
    obtain ⟨δ, δpos, hδlt⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt hconst_fin hpos
    exact absurd (key δ δpos) (not_le_of_gt hδlt)
  -- ===================================================================
  -- (2)  Assembly.  Split the critical set into the differentiable core `D`
  --      and the (volume-null) non-differentiable part `ND`.
  -- ===================================================================
  set Crit : Set ℂ := {z | fderiv ℝ u z = 0} with hCrit_def
  set Diff : Set ℂ := {z | DifferentiableAt ℝ u z} with hDiff_def
  have hCrit_meas : MeasurableSet Crit :=
    measurable_fderiv ℝ u (measurableSet_singleton _)
  have hDiff_meas : MeasurableSet Diff := measurableSet_of_differentiableAt ℝ u
  -- Non-differentiable part is `volume`-null (Rademacher).
  have hND0 : volume (A ∩ Diffᶜ) = 0 := by
    have hDiffc0 : volume (Diffᶜ) = 0 := by
      have hae : ∀ᵐ z, DifferentiableAt ℝ u z := hu.ae_differentiableAt
      have hae' : ∀ᵐ z, z ∉ (Diffᶜ : Set ℂ) := by
        filter_upwards [hae] with z hz
        simp only [hDiff_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
        exact hz
      have := (MeasureTheory.ae_iff).1 hae'
      simpa only [not_not, Set.setOf_mem_eq] using this
    exact measure_mono_null Set.inter_subset_right hDiffc0
  -- On `Diffᶜ`, `fderiv u = 0`, so `Diffᶜ ⊆ Crit` and `A ∩ Crit = D ∪ (A ∩ Diffᶜ)`.
  have hNDsubCrit : Diffᶜ ⊆ Crit := by
    intro z hz
    simp only [hCrit_def, Set.mem_setOf_eq]
    exact fderiv_zero_of_not_differentiableAt hz
  have hsplit : A ∩ Crit = (A ∩ Crit ∩ Diff) ∪ (A ∩ Diffᶜ) := by
    apply Set.Subset.antisymm
    · intro z ⟨hzA, hzC⟩
      by_cases hzD : z ∈ Diff
      · exact Or.inl ⟨⟨hzA, hzC⟩, hzD⟩
      · exact Or.inr ⟨hzA, hzD⟩
    · rintro z (⟨⟨hzA, hzC⟩, _⟩ | ⟨hzA, hzD⟩)
      · exact ⟨hzA, hzC⟩
      · exact ⟨hzA, hNDsubCrit hzD⟩
  -- The non-differentiable contribution vanishes.
  have hND_int : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Diffᶜ)) = 0 :=
    coarea_null_le hu (hA.inter hDiff_meas.compl) hND0
  -- The differentiable critical contribution vanishes (exhaust by balls).
  set D : Set ℂ := A ∩ Crit ∩ Diff with hD_def
  have hD_meas : MeasurableSet D := (hA.inter hCrit_meas).inter hDiff_meas
  have hD_int : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ D) = 0 := by
    -- Exhaust `D` by `Dₘ := D ∩ closedBall 0 m`, each of finite measure.
    set Dm : ℕ → Set ℂ := fun m => D ∩ Metric.closedBall (0:ℂ) m with hDm_def
    have hDm_meas : ∀ m, MeasurableSet (Dm m) :=
      fun m => hD_meas.inter measurableSet_closedBall
    have hDm_fin : ∀ m, volume (Dm m) ≠ ∞ := by
      intro m
      refine ne_top_of_le_ne_top ?_ (measure_mono (Set.inter_subset_right))
      exact (isCompact_closedBall (0:ℂ) (m:ℝ)).measure_lt_top.ne
    have hDm_crit : ∀ m, Dm m ⊆ Crit := by
      intro m z hz; exact hz.1.1.2
    have hDm_diff : ∀ m, Dm m ⊆ Diff := by
      intro m z hz; exact hz.1.2
    have hDm_zero : ∀ m, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Dm m) = 0 :=
      fun m => hfin_case (hDm_meas m) (hDm_fin m) (hDm_crit m) (hDm_diff m)
    -- `μH[1] (u⁻¹{c} ∩ D) = ⨆ m, μH[1] (u⁻¹{c} ∩ Dₘ)` (monotone union).
    have hball_mono : Monotone (fun m : ℕ => Metric.closedBall (0:ℂ) (m:ℝ)) :=
      fun a b hab => Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
    have hpt : ∀ c : ℝ,
        μH[1] (u ⁻¹' {c} ∩ D) = ⨆ m : ℕ, μH[1] (u ⁻¹' {c} ∩ Dm m) := by
      intro c
      have hmono : Monotone (fun m : ℕ => u ⁻¹' {c} ∩ Dm m) :=
        fun a b hab => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hab))
      have hunion : (⋃ m : ℕ, u ⁻¹' {c} ∩ Dm m) = u ⁻¹' {c} ∩ D := by
        apply Set.Subset.antisymm
        · refine Set.iUnion_subset (fun m => ?_)
          intro z ⟨hzc, hzD, _⟩
          exact ⟨hzc, hzD⟩
        · intro z ⟨hzc, hzD⟩
          obtain ⟨N, hN⟩ : ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
            obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
            exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
          exact Set.mem_iUnion.2 ⟨N, hzc, hzD, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ D)
        = ∫⁻ c, ⨆ m : ℕ, μH[1] (u ⁻¹' {c} ∩ Dm m) := by
          apply lintegral_congr; exact hpt
      _ = ⨆ m : ℕ, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Dm m) := by
          refine lintegral_iSup' (fun m => slice_aemeas (hDm_meas m)) ?_
          filter_upwards with c
          intro a b hab
          exact measure_mono (Set.inter_subset_inter_right _
            (Set.inter_subset_inter_right _ (hball_mono hab)))
      _ = 0 := by simp only [hDm_zero, iSup_const]
  -- Combine.  Each level slice of `A ∩ Crit` splits into the `D`-slice and the `ND`-slice.
  have hslice_split : ∀ c : ℝ, u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0})
      = (u ⁻¹' {c} ∩ D) ∪ (u ⁻¹' {c} ∩ (A ∩ Diffᶜ)) := by
    intro c
    rw [← Set.inter_union_distrib_left, ← hsplit]
  have hbound : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0}))
      ≤ ∫⁻ c, (μH[1] (u ⁻¹' {c} ∩ D) + μH[1] (u ⁻¹' {c} ∩ (A ∩ Diffᶜ))) := by
    refine lintegral_mono (fun c => ?_)
    rw [hslice_split c]
    exact measure_union_le _ _
  rw [← nonpos_iff_eq_zero]
  refine le_trans hbound (le_of_eq ?_)
  -- Both slice integrals vanish, so each slice is `0` a.e., hence the sum-integral is `0`.
  have hD_ae : (fun c => μH[1] (u ⁻¹' {c} ∩ D)) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff' (slice_aemeas hD_meas)).1 hD_int
  have hND_ae : (fun c => μH[1] (u ⁻¹' {c} ∩ (A ∩ Diffᶜ))) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff' (slice_aemeas (hA.inter hDiff_meas.compl))).1 hND_int
  rw [lintegral_eq_zero_iff'
    ((slice_aemeas hD_meas).add (slice_aemeas (hA.inter hDiff_meas.compl)))]
  filter_upwards [hD_ae, hND_ae] with c hc hcn
  simp only [Pi.zero_apply] at hc hcn ⊢
  rw [hc, hcn, add_zero]

/-- **Regular part of the co-area inequality (the area-formula assembly over `{∇u ≠ 0}`).**

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) ≤ ∫⁻ z in A, ‖fderiv ℝ u z‖₊`.

Proof: split `{∇u ≠ 0} = {∂u/∂x ≠ 0} ∪ ({∂u/∂x = 0} ∩ {∂u/∂y ≠ 0})`. On the first, the square map
`Ψ = (u, im)` has `det Ψ' = ∂u/∂x ≠ 0`; on the second use `Ψ = (u, re)`. Partition each via the
Lusin decomposition `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` of `Ψ` into
DISJOINT measurable pieces on which `Ψ` is `ApproximatesLinearOn` an invertible `Aₙ` with tolerance
`δ < ‖Aₙ.symm‖₊⁻¹`, apply `coarea_piece_le` per piece (`∫⁻ c, μH[1] (u⁻¹{c} ∩ Sₙ) ≤ ∫⁻ Sₙ ‖∇u‖`),
and sum the disjoint pieces (`lintegral_tsum`, `μH[1]` additivity) to `∫⁻ z in A, ‖∇u z‖₊` (the
integrand vanishes on `{∇u = 0}`, so integrating over `A` not `A ∩ {∇u ≠ 0}` is harmless). -/
theorem coarea_regular_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0}))
      ≤ ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
  classical
  have hucont : Continuous u := hu.continuous
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- =====================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets `A'`.
  --      (Dynkin on each compact ball + closed-ball exhaustion; copied from
  --      `coarea_set_sharp` / `coarea_critical_le`.)
  -- =====================================================================
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        rw [hc₀v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- =====================================================================
  -- (1)  The per-bounded-piece coordinate engine.  Given a square map `Ψ` with
  --      global derivative `Ψ'` at differentiable points, `.re = u`, and
  --      nonzero determinant on a bounded measurable `s` of differentiability,
  --      the slice integral over `s` is bounded by `∫⁻ s ‖∇u‖`, by the Lusin
  --      partition into invertible `ApproximatesLinearOn` pieces + `coarea_piece_le`.
  -- =====================================================================
  have hcoord_core : ∀ (Ψ : ℂ → ℂ) (Ψ' : ℂ → (ℂ →L[ℝ] ℂ)),
      (∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψ (Ψ' z) z) →
      (∀ z, (Ψ z).re = u z) →
      ∀ (s : Set ℂ), MeasurableSet s → Bornology.IsBounded s →
        (∀ z ∈ s, DifferentiableAt ℝ u z) → (∀ z ∈ s, (Ψ' z).det ≠ 0) →
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ s) ≤ ∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    intro Ψ Ψ' hΨfd hΨre s hsmeas hsb hsdiff hsdet
    have hΨ'_s : ∀ z ∈ s, HasFDerivWithinAt Ψ (Ψ' z) s z :=
      fun z hz => (hΨfd z (hsdiff z hz)).hasFDerivWithinAt
    set r : (ℂ →L[ℝ] ℂ) → NNReal := fun A' =>
      if h : A'.det ≠ 0 then
        ‖((A'.toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
      else 1 with hr
    have hrpos : ∀ A', r A' ≠ 0 := by
      intro A'
      simp only [hr]
      split_ifs with h
      · set B := A'.toContinuousLinearEquivOfDetNeZero h
        have hBsymm : (B.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
          intro hz
          have h1 : B.symm (B 1) = 1 := B.symm_apply_apply 1
          rw [show B.symm (B 1) = (B.symm : ℂ →L[ℝ] ℂ) (B 1) from rfl, hz] at h1
          simp at h1
        have hnorm_pos : 0 < ‖(B.symm : ℂ →L[ℝ] ℂ)‖₊ := by
          rw [pos_iff_ne_zero]; simpa [nnnorm_eq_zero] using hBsymm
        positivity
      · exact one_ne_zero
    obtain ⟨t, A, hdisj, htmeas, hsub, happrox, hAval⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
        Ψ s Ψ' hΨ'_s r (fun A' => hrpos A')
    have hpiece_meas : ∀ n, MeasurableSet (s ∩ t n) := fun n => hsmeas.inter (htmeas n)
    have hpiece_bd : ∀ n, Bornology.IsBounded (s ∩ t n) :=
      fun n => hsb.subset Set.inter_subset_left
    have hpiece_bound : ∀ n,
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) ≤ ∫⁻ z in s ∩ t n, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
      intro n
      rcases Set.eq_empty_or_nonempty (s ∩ t n) with hempty | hne
      · rw [show (fun c : ℝ => μH[1] (u ⁻¹' {c} ∩ (s ∩ t n))) = fun _ => 0 by
          funext c; rw [hempty]; simp]
        simp
      · obtain ⟨y, hy, hAy⟩ := hAval ⟨hne.choose, hne.choose_spec.1⟩ n
        have hAdet : (A n).det ≠ 0 := by rw [hAy]; exact hsdet y hy
        set Bequiv := (A n).toContinuousLinearEquivOfDetNeZero hAdet
        have hAeq : ((A n) : ℂ →L[ℝ] ℂ) = (Bequiv : ℂ →L[ℝ] ℂ) :=
          ((A n).coe_toContinuousLinearEquivOfDetNeZero hAdet).symm
        have hrlt : r (A n) < ‖(Bequiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
          simp only [hr, dif_pos hAdet]
          have hBsymm : (Bequiv.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
            intro hz
            have h1 : Bequiv.symm (Bequiv 1) = 1 := Bequiv.symm_apply_apply 1
            rw [show Bequiv.symm (Bequiv 1) = (Bequiv.symm : ℂ →L[ℝ] ℂ) (Bequiv 1) from rfl, hz]
              at h1
            simp at h1
          have hnorm_pos : (0 : NNReal) < ‖(Bequiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
            rw [inv_pos, pos_iff_ne_zero]; simpa [nnnorm_eq_zero] using hBsymm
          exact NNReal.half_lt_self (ne_of_gt hnorm_pos)
        have happrox' : ApproximatesLinearOn Ψ (Bequiv : ℂ →L[ℝ] ℂ) (s ∩ t n) (r (A n)) := by
          rw [← hAeq]; exact happrox n
        exact coarea_piece_le (hpiece_meas n) (hpiece_bd n) hrlt happrox'
          (fun z hz => (hΨfd z (hsdiff z hz.1)).hasFDerivWithinAt)
          (fun z _ => hΨre z)
          (fun z hz => hsdiff z hz.1)
    have hslice_eq : ∀ c : ℝ,
        μH[1] (u ⁻¹' {c} ∩ s) = ∑' n, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) := by
      intro c
      have hcover_c : u ⁻¹' {c} ∩ s = ⋃ n, u ⁻¹' {c} ∩ (s ∩ t n) := by
        rw [← Set.inter_iUnion]
        congr 1
        apply Set.Subset.antisymm
        · intro z hz
          obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hsub hz)
          exact Set.mem_iUnion.2 ⟨n, hz, hn⟩
        · exact Set.iUnion_subset (fun n => Set.inter_subset_left)
      rw [hcover_c]
      refine measure_iUnion ?_ ?_
      · intro i j hij
        refine (hdisj hij).mono ?_ ?_ <;> exact fun z hz => hz.2.2
      · intro n
        exact (hucont.measurable (measurableSet_singleton c)).inter (hpiece_meas n)
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ s)
        = ∫⁻ c, ∑' n, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) := by
          apply lintegral_congr; exact hslice_eq
      _ = ∑' n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) :=
          lintegral_tsum (fun n => slice_aemeas (hpiece_meas n))
      _ ≤ ∑' n, ∫⁻ z in s ∩ t n, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
          ENNReal.tsum_le_tsum hpiece_bound
      _ = ∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
          have hcvr : s = ⋃ n, (s ∩ t n) := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.2 hsub).symm
          rw [show (∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞))
              = ∫⁻ z in ⋃ n, (s ∩ t n), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) from by rw [← hcvr]]
          rw [lintegral_iUnion (fun n => hpiece_meas n)
            (fun i j hij => (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right)]
  -- =====================================================================
  -- (2)  The per-coordinate full bound (exhaust the unbounded `A ∩ Q` by balls,
  --      apply `hcoord_core` on each bounded piece, sum via monotone convergence).
  -- =====================================================================
  have hcoord_full : ∀ (Ψ : ℂ → ℂ) (Ψ' : ℂ → (ℂ →L[ℝ] ℂ)),
      (∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψ (Ψ' z) z) →
      (∀ z, (Ψ z).re = u z) →
      ∀ (Q : Set ℂ), MeasurableSet Q →
        (∀ z ∈ A ∩ Q, DifferentiableAt ℝ u z) → (∀ z ∈ A ∩ Q, (Ψ' z).det ≠ 0) →
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Q)) ≤ ∫⁻ z in A ∩ Q, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    intro Ψ Ψ' hΨfd hΨre Q hQmeas hAQdiff hAQdet
    set R : Set ℂ := A ∩ Q with hR_def
    have hRmeas : MeasurableSet R := hA.inter hQmeas
    set Rm : ℕ → Set ℂ := fun m => R ∩ Metric.closedBall (0:ℂ) m with hRm_def
    have hRm_meas : ∀ m, MeasurableSet (Rm m) := fun m => hRmeas.inter measurableSet_closedBall
    have hRm_bd : ∀ m, Bornology.IsBounded (Rm m) :=
      fun m => (Metric.isBounded_closedBall).subset Set.inter_subset_right
    have hball_mono : Monotone (fun m : ℕ => Metric.closedBall (0:ℂ) (m:ℝ)) :=
      fun a b hab => Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
    have hRm_mono : Monotone Rm :=
      fun a b hab => Set.inter_subset_inter_right _ (hball_mono hab)
    have hRcover : (⋃ m, Rm m) = R := by
      apply Set.Subset.antisymm (Set.iUnion_subset (fun m => Set.inter_subset_left))
      intro z hz
      obtain ⟨N, hN⟩ : ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
        exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
      exact Set.mem_iUnion.2 ⟨N, hz, hN⟩
    have hRm_diff : ∀ m, ∀ z ∈ Rm m, DifferentiableAt ℝ u z :=
      fun m z hz => hAQdiff z hz.1
    have hRm_det : ∀ m, ∀ z ∈ Rm m, (Ψ' z).det ≠ 0 :=
      fun m z hz => hAQdet z hz.1
    have hLHS : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ R)
        = ⨆ m, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Rm m) := by
      have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ R)
          = ⨆ m, μH[1] (u ⁻¹' {c} ∩ Rm m) := by
        intro c
        have hmono : Monotone (fun m : ℕ => u ⁻¹' {c} ∩ Rm m) :=
          fun a b hab => Set.inter_subset_inter_right _ (hRm_mono hab)
        have hu2 : (⋃ m, u ⁻¹' {c} ∩ Rm m) = u ⁻¹' {c} ∩ R := by
          rw [← Set.inter_iUnion, hRcover]
        rw [← hu2, hmono.measure_iUnion]
      calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ R)
          = ∫⁻ c, ⨆ m, μH[1] (u ⁻¹' {c} ∩ Rm m) := by apply lintegral_congr; exact hpt
        _ = ⨆ m, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Rm m) := by
            refine lintegral_iSup' (fun m => slice_aemeas (hRm_meas m)) ?_
            filter_upwards with c
            intro a b hab
            exact measure_mono (Set.inter_subset_inter_right _ (hRm_mono hab))
    rw [hLHS]
    apply iSup_le
    intro m
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Rm m)
        ≤ ∫⁻ z in Rm m, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
          hcoord_core Ψ Ψ' hΨfd hΨre (Rm m) (hRm_meas m) (hRm_bd m)
            (hRm_diff m) (hRm_det m)
      _ ≤ ∫⁻ z in R, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := lintegral_mono_set Set.inter_subset_left
  -- =====================================================================
  -- (3)  Build the two coordinate maps (`Ψ_im` over `∂u/∂x ≠ 0`, `Ψ_re` over
  --      `∂u/∂x = 0 ∧ ∂u/∂y ≠ 0`) and apply `hcoord_full`.
  -- =====================================================================
  set Diff : Set ℂ := {z | DifferentiableAt ℝ u z} with hDiff_def
  have hDiff_meas : MeasurableSet Diff := measurableSet_of_differentiableAt ℝ u
  set P1 : Set ℂ := {z | (fderiv ℝ u z) (1:ℂ) ≠ 0} with hP1_def
  set P2 : Set ℂ := {z | (fderiv ℝ u z) (1:ℂ) = 0 ∧ (fderiv ℝ u z) Complex.I ≠ 0} with hP2_def
  have hP1_meas : MeasurableSet P1 :=
    (measurableSet_singleton (0:ℝ)).compl.preimage
      ((measurable_fderiv ℝ u).apply_continuousLinearMap (1:ℂ))
  have hP2_meas : MeasurableSet P2 := by
    apply MeasurableSet.inter
    · exact (measurableSet_singleton (0:ℝ)).preimage
        ((measurable_fderiv ℝ u).apply_continuousLinearMap (1:ℂ))
    · exact (measurableSet_singleton (0:ℝ)).compl.preimage
        ((measurable_fderiv ℝ u).apply_continuousLinearMap Complex.I)
  have hNECrit_meas : MeasurableSet {z : ℂ | fderiv ℝ u z ≠ 0} :=
    (measurable_fderiv ℝ u) (measurableSet_singleton (0)).compl
  -- `Ψ_im z = u z • 1 + z.im • I`, derivative `(∇u).smulRight 1 + imCLM.smulRight I`,
  -- `det = ∂u/∂x = (∇u) 1`.
  set Ψim : ℂ → ℂ := fun w => (u w : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I with hΨim
  set Ψim' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    ((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I with hΨim'
  have hΨim_fd : ∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψim (Ψim' z) z := by
    intro z hu_z
    have hPG : HasFDerivAt (fun w : ℂ => u w) (fderiv ℝ u z) z := hu_z.hasFDerivAt
    set LP1 : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℂ) with hLP1
    have hcomp1 : HasFDerivAt (fun w : ℂ => (u w : ℝ) • (1 : ℂ))
        (LP1.comp (fderiv ℝ u z)) z := by
      have := LP1.hasFDerivAt.comp z hPG; convert this using 1
    set LQI : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I with hLQI
    have hcomp2 : HasFDerivAt (fun w : ℂ => (w.im : ℝ) • Complex.I)
        (LQI.comp Complex.imCLM) z := by
      have := LQI.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt; convert this using 1
    have hsum := hcomp1.add hcomp2
    rw [hΨim, hΨim']; convert hsum using 1
  have hΨim_re : ∀ z, (Ψim z).re = u z := by
    intro z; rw [hΨim]; simp [Complex.real_smul]
  have hΨim_det : ∀ z, (Ψim' z).det = (fderiv ℝ u z) (1:ℂ) := by
    intro z
    rw [hΨim']
    set D : ℂ →L[ℝ] ℂ :=
      (((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I) with hD
    rw [show D.det
        = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (D : ℂ →ₗ[ℝ] ℂ)) from
      (LinearMap.det_toMatrix Complex.basisOneI _).symm]
    rw [Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : D 1 = ((fderiv ℝ u z) (1:ℂ) : ℂ) := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.one_im, zero_smul,
        add_zero]
      change ((fderiv ℝ u z) (1:ℂ) : ℝ) • (1 : ℂ) = (((fderiv ℝ u z) (1:ℂ) : ℝ) : ℂ); simp
    have h2 : D Complex.I = ((fderiv ℝ u z) Complex.I : ℂ) + Complex.I := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.I_im, one_smul]
      change ((fderiv ℝ u z) Complex.I : ℝ) • (1 : ℂ) + Complex.I
        = (((fderiv ℝ u z) Complex.I : ℝ) : ℂ) + Complex.I; simp
    change (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im = (fderiv ℝ u z) (1:ℂ)
    rw [h1, h2]; simp
  -- `Ψ_re z = u z • 1 + z.re • I`, derivative `(∇u).smulRight 1 + reCLM.smulRight I`,
  -- `det = -∂u/∂y = -(∇u) I`.
  set Ψre : ℂ → ℂ := fun w => (u w : ℝ) • (1 : ℂ) + (w.re : ℝ) • Complex.I with hΨre_def
  set Ψre' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    ((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.reCLM.smulRight Complex.I with hΨre'
  have hΨre_fd : ∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψre (Ψre' z) z := by
    intro z hu_z
    have hPG : HasFDerivAt (fun w : ℂ => u w) (fderiv ℝ u z) z := hu_z.hasFDerivAt
    set LP1 : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℂ) with hLP1
    have hcomp1 : HasFDerivAt (fun w : ℂ => (u w : ℝ) • (1 : ℂ))
        (LP1.comp (fderiv ℝ u z)) z := by
      have := LP1.hasFDerivAt.comp z hPG; convert this using 1
    set LQI : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I with hLQI
    have hcomp2 : HasFDerivAt (fun w : ℂ => (w.re : ℝ) • Complex.I)
        (LQI.comp Complex.reCLM) z := by
      have := LQI.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt; convert this using 1
    have hsum := hcomp1.add hcomp2
    rw [hΨre_def, hΨre']; convert hsum using 1
  have hΨre_re : ∀ z, (Ψre z).re = u z := by
    intro z; rw [hΨre_def]; simp [Complex.real_smul]
  have hΨre_det : ∀ z, (Ψre' z).det = - (fderiv ℝ u z) Complex.I := by
    intro z
    rw [hΨre']
    set D : ℂ →L[ℝ] ℂ :=
      (((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.reCLM.smulRight Complex.I) with hD
    rw [show D.det
        = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (D : ℂ →ₗ[ℝ] ℂ)) from
      (LinearMap.det_toMatrix Complex.basisOneI _).symm]
    rw [Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : D 1 = ((fderiv ℝ u z) (1:ℂ) : ℂ) + Complex.I := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.one_re, one_smul]
      change ((fderiv ℝ u z) (1:ℂ) : ℝ) • (1 : ℂ) + Complex.I
        = (((fderiv ℝ u z) (1:ℂ) : ℝ) : ℂ) + Complex.I; simp
    have h2 : D Complex.I = ((fderiv ℝ u z) Complex.I : ℂ) := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.I_re, zero_smul, add_zero]
      change ((fderiv ℝ u z) Complex.I : ℝ) • (1 : ℂ) = (((fderiv ℝ u z) Complex.I : ℝ) : ℂ); simp
    change (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im = - (fderiv ℝ u z) Complex.I
    rw [h1, h2]; simp
  -- Membership in `P1`/`P2` (with nonzero partial) forces differentiability.
  have hP1diff : ∀ z ∈ A ∩ P1, DifferentiableAt ℝ u z := by
    rintro z ⟨_, hz1⟩
    by_contra hnd
    apply hz1
    rw [fderiv_zero_of_not_differentiableAt hnd]; simp
  have hP2diff : ∀ z ∈ A ∩ P2, DifferentiableAt ℝ u z := by
    rintro z ⟨_, _, hz2⟩
    by_contra hnd
    apply hz2
    rw [fderiv_zero_of_not_differentiableAt hnd]; simp
  have hP1det : ∀ z ∈ A ∩ P1, (Ψim' z).det ≠ 0 := by
    rintro z ⟨_, hz1⟩; rw [hΨim_det]; exact hz1
  have hP2det : ∀ z ∈ A ∩ P2, (Ψre' z).det ≠ 0 := by
    rintro z ⟨_, _, hz2⟩
    rw [hΨre_det]
    simp only [neg_ne_zero]; exact hz2
  have hbound_P1 : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P1))
      ≤ ∫⁻ z in A ∩ P1, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
    hcoord_full Ψim Ψim' hΨim_fd hΨim_re P1 hP1_meas hP1diff hP1det
  have hbound_P2 : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P2))
      ≤ ∫⁻ z in A ∩ P2, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
    hcoord_full Ψre Ψre' hΨre_fd hΨre_re P2 hP2_meas hP2diff hP2det
  -- =====================================================================
  -- (4)  Assemble the reduction.  The non-differentiable part is `volume`-null
  --      (Rademacher) and contributes `0`; the differentiable part of `{∇u ≠ 0}`
  --      splits into the (disjoint) `P1`/`P2` pieces, each bounded above.
  -- =====================================================================
  have hND0 : volume (A ∩ Diffᶜ) = 0 := by
    have hDiffc0 : volume (Diffᶜ) = 0 := by
      have hae : ∀ᵐ z, DifferentiableAt ℝ u z := hu.ae_differentiableAt
      have hae' : ∀ᵐ z, z ∉ (Diffᶜ : Set ℂ) := by
        filter_upwards [hae] with z hz
        simp only [hDiff_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]; exact hz
      have := (MeasureTheory.ae_iff).1 hae'
      simpa only [not_not, Set.setOf_mem_eq] using this
    exact measure_mono_null Set.inter_subset_right hDiffc0
  have hND_int : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) = 0 := by
    apply coarea_null_le hu ((hA.inter hNECrit_meas).inter hDiff_meas.compl)
    exact measure_mono_null (by intro z hz; exact ⟨hz.1.1, hz.2⟩) hND0
  have hsplit_slice : ∀ c : ℝ,
      μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0}))
        ≤ μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
          + μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) := by
    intro c
    rw [show u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})
        = (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
          ∪ (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) from by
      rw [← Set.inter_union_distrib_left]
      congr 1
      rw [Set.inter_union_compl]]
    exact measure_union_le _ _
  have hDiffsub : ∀ c : ℝ,
      μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
        ≤ μH[1] (u ⁻¹' {c} ∩ (A ∩ P1)) + μH[1] (u ⁻¹' {c} ∩ (A ∩ P2)) := by
    intro c
    have hsub : u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff)
        ⊆ (u ⁻¹' {c} ∩ (A ∩ P1)) ∪ (u ⁻¹' {c} ∩ (A ∩ P2)) := by
      rintro z ⟨hzc, ⟨hzA, hzne⟩, hzD⟩
      by_cases hp1 : (fderiv ℝ u z) (1:ℂ) ≠ 0
      · exact Or.inl ⟨hzc, hzA, hp1⟩
      · have hp1' : (fderiv ℝ u z) (1:ℂ) = 0 := not_not.mp hp1
        have hI : (fderiv ℝ u z) Complex.I ≠ 0 := by
          intro hI0
          apply hzne
          ext w
          have hw : w = w.re • (1:ℂ) + w.im • Complex.I := by
            apply Complex.ext <;> simp [Complex.real_smul]
          rw [hw, map_add, map_smul, map_smul, hp1', hI0]; simp
        exact Or.inr ⟨hzc, hzA, hp1', hI⟩
    exact le_trans (measure_mono hsub) (measure_union_le _ _)
  have hdisjP : Disjoint (A ∩ P1) (A ∩ P2) := by
    rw [Set.disjoint_left]
    rintro z ⟨_, hz1⟩ ⟨_, hz2, _⟩
    exact hz1 hz2
  calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0}))
      ≤ ∫⁻ c, (μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
            + μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ))) :=
        lintegral_mono hsplit_slice
    _ = (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff)))
          + ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) := by
        rw [lintegral_add_left' (slice_aemeas ((hA.inter hNECrit_meas).inter hDiff_meas))]
    _ = ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff)) := by
        rw [hND_int, add_zero]
    _ ≤ ∫⁻ c, (μH[1] (u ⁻¹' {c} ∩ (A ∩ P1)) + μH[1] (u ⁻¹' {c} ∩ (A ∩ P2))) :=
        lintegral_mono hDiffsub
    _ = (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P1))) + ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P2)) := by
        rw [lintegral_add_left' (slice_aemeas (hA.inter hP1_meas))]
    _ ≤ (∫⁻ z in A ∩ P1, (‖fderiv ℝ u z‖₊ : ℝ≥0∞))
          + ∫⁻ z in A ∩ P2, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
        add_le_add hbound_P1 hbound_P2
    _ ≤ ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
        rw [← lintegral_union (hA.inter hP2_meas) hdisjP]
        apply lintegral_mono_set
        rw [← Set.inter_union_distrib_left]
        exact Set.inter_subset_left

/-- **Sharp planar co-area inequality, unweighted set form (the area-formula assembly).**

For a `K`-Lipschitz `u : ℂ → ℝ` and a measurable set `A ⊆ ℂ`,
`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ ∫⁻ z in A, ‖fderiv ℝ u z‖₊ ∂volume`.

This is the gradient-sharp co-area inequality for indicator weights; the general gradient form
`eilenberg_coarea_grad_le` follows from it by the layer-cake / monotone-class approximation of `g`.

## Truth and proof

One-sided `≤`. Split `A` along `Crit = {z | fderiv ℝ u z = 0}` and `Reg = Critᶜ`. The
critical slice `c ↦ μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit))` integrates to `0` (`coarea_critical_le`) and is
`≥ 0`, hence vanishes for a.e. `c`; so for a.e. `c` the level set restricted to `A` reduces to its
regular part, and `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) = ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Reg))`, which is
bounded by `∫⁻ z in A, ‖fderiv ℝ u z‖₊` (`coarea_regular_le`, the area-formula assembly over the
non-critical set). The Besicovitch-differentiation route is avoided: the sharp local density is not
controlled by mere differentiability (`|z|² sin (1/|z|)` is a counterexample), so the genuine proof
is the Lusin-decomposition + area-formula one carried by `coarea_piece_le`. -/
theorem coarea_set_sharp {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)
      ≤ ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume := by
  classical
  have hucont : Continuous u := hu.continuous
  -- ===================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets.
  -- Built by Dynkin (closed-set pi-system) on each compact ball, with the
  -- complement step legitimized a.e. by the finiteness of the level-length on a
  -- compact ball (`eilenberg_coarea_planar_metric`), then by the closed-ball
  -- exhaustion of `ℂ`.
  -- ===================================================================
  -- (0a)  On a fixed compact ball `B = closedBall 0 N`.
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        -- `μH[2] B = (c • volume) B = c * volume B < ∞` since `B` is compact.
        obtain ⟨c, hc, hcv⟩ := hausdorffMeasure_two_complex_smul_volume
        rw [hcv, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    -- Dynkin predicate.
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · -- empty
      simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · -- basic: closed `T`, `T ∩ B` compact
      intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · -- complement (a.e. by finiteness of `gB`)
      intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · -- countable disjoint union
      intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  -- (0b)  Full measurable `A'` via the closed-ball exhaustion.
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- ===================================================================
  -- (1)  Critical / regular partition of `A`.
  -- `Crit = (fderiv u)⁻¹{0}` is measurable, `Reg = {fderiv u ≠ 0} = Critᶜ`.
  -- For each `c` the level slice splits DISJOINTLY:
  --   `u⁻¹{c} ∩ A = (u⁻¹{c} ∩ (A ∩ Crit)) ∪ (u⁻¹{c} ∩ (A ∩ Reg))`.
  -- ===================================================================
  set Crit : Set ℂ := {z | fderiv ℝ u z = 0} with hCrit_def
  have hCrit_meas : MeasurableSet Crit :=
    measurable_fderiv ℝ u (measurableSet_singleton _)
  -- The critical-slice integral vanishes (proven, axiom-clean).
  have hcrit0 : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit)) = 0 :=
    coarea_critical_le hu hA
  -- The critical slice is a.e. `0` (AEmeasurable via the `slice_aemeas` block above).
  have hae0 : ∀ᵐ c ∂(volume : Measure ℝ),
      μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit)) = 0 := by
    have := (lintegral_eq_zero_iff' (slice_aemeas (hA.inter hCrit_meas))).1 hcrit0
    filter_upwards [this] with c hc
    simpa only [Pi.zero_apply] using hc
  -- ===================================================================
  -- (2)  A.e. rewrite of the integrand to the regular slice.
  -- ===================================================================
  have hslice_split : ∀ c : ℝ,
      μH[1] (u ⁻¹' {c} ∩ A)
        = μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit))
          + μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
    intro c
    have hsetsplit : u ⁻¹' {c} ∩ A
        = (u ⁻¹' {c} ∩ (A ∩ Crit))
          ∪ (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
      ext z
      simp only [hCrit_def, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hzc, hzA⟩
        by_cases hz : fderiv ℝ u z = 0
        · exact Or.inl ⟨hzc, hzA, hz⟩
        · exact Or.inr ⟨hzc, hzA, hz⟩
      · rintro (⟨hzc, hzA, _⟩ | ⟨hzc, hzA, _⟩) <;> exact ⟨hzc, hzA⟩
    rw [hsetsplit]
    refine measure_union ?_ ?_
    · -- `Crit` and `{∇u ≠ 0}` are disjoint, so the two slices are disjoint.
      refine Set.disjoint_left.2 ?_
      rintro z ⟨_, _, hzCrit⟩ ⟨_, _, hzReg⟩
      exact hzReg hzCrit
    · have hReg_meas : MeasurableSet {z : ℂ | fderiv ℝ u z ≠ 0} := by
        have : {z : ℂ | fderiv ℝ u z ≠ 0} = Critᶜ := by
          ext z; simp only [hCrit_def, Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [this]; exact hCrit_meas.compl
      exact (hucont.measurable (measurableSet_singleton c)).inter (hA.inter hReg_meas)
  have hcongr : (fun c => μH[1] (u ⁻¹' {c} ∩ A))
      =ᵐ[volume] fun c => μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
    filter_upwards [hae0] with c hc
    rw [hslice_split c, hc, zero_add]
  -- ===================================================================
  -- (3)  Finish:  rewrite a.e., then apply the regular co-area bound.
  -- ===================================================================
  rw [lintegral_congr_ae hcongr]
  exact coarea_regular_le hu hA

/-- **Sharp planar co-area (Eilenberg) inequality, gradient-weighted form (the isolated GMT
residual that the length–area assembly consumes).**

For a `K`-Lipschitz `u : ℂ → ℝ` (Lipschitz, hence `fderiv ℝ u` exists a.e. by Rademacher) and a
nonnegative measurable weight `g : ℂ → ℝ≥0∞`,

`∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[1]) dc ≤ ∫⁻ z, g z * ‖fderiv ℝ u z‖₊ ∂volume`.

## Truth and direction

One-sided (`≤`). This is the genuine Eilenberg inequality (Evans–Gariepy §3.4.2,
Theorem 1: for Lipschitz `u : ℝⁿ → ℝ`, `∫_ℝ (∫_{u⁻¹{c}} g dμH^{n-1}) dc ≤ ∫ g |∇u| dx`; equality
is the co-area *formula*, the deeper two-sided statement, which is **not** claimed). The pointwise
gradient `‖∇u‖` is sharper than any Lipschitz-constant bound (since `‖∇u‖ ≤ K` a.e.); this is the
*primitive* co-area atom that the length–area lower bound consumes.

## Affine sanity check

For `u(z) = z.re` (so `fderiv ℝ u = reCLM`, `‖∇u‖ = 1`), the right side is `∫⁻ g dvol`; the left
side is `∫⁻ c (∫_{re = c} g dμH[1]) dc`, and co-area for the affine `u` is the Fubini equality
`∫ g = ∫_c ∫_{re=c} g`, so `≤` holds with equality — exactly the affine length–area case in
`lengthArea_modulus_lower_bound`.

## Proof

By the layer-cake (monotone simple-function approximation of `g`) this reduces to the unweighted
set form `coarea_set_sharp` (`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ ∫⁻ z in A, ‖∇u‖₊`), which is the
area-formula assembly `coarea_critical_le + coarea_regular_le`, the latter built from the per-piece
core `coarea_piece_le` (Lusin decomposition into approximately-linear injective pieces + the area
formula + the fiber arc-length bound). The constant is the sharp `1` (Evans–Gariepy), not `K`. -/
theorem eilenberg_coarea_grad_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ))
      ≤ ∫⁻ z, g z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume := by
  classical
  have hucont : Continuous u := hu.continuous
  set w : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) with hw_def
  have hw_meas : Measurable w := (measurable_fderiv ℝ u).nnnorm.coe_nnreal_ennreal
  -- ===================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets.
  -- Reproduced inline from `coarea_set_sharp` (Dynkin on closed sets per
  -- compact ball, legitimized a.e. by `eilenberg_coarea_planar_metric`, then
  -- the closed-ball exhaustion of `ℂ`).
  -- ===================================================================
  -- (0a)  On a fixed compact ball `B = closedBall 0 N`.
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        -- `μH[2] B = (c • volume) B = c * volume B < ∞` since `B` is compact.
        obtain ⟨c, hc, hcv⟩ := hausdorffMeasure_two_complex_smul_volume
        rw [hcv, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    -- Dynkin predicate.
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · -- empty
      simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · -- basic: closed `T`, `T ∩ B` compact
      intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · -- complement (a.e. by finiteness of `gB`)
      intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · -- countable disjoint union
      intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  -- (0b)  Full measurable `A'` via the closed-ball exhaustion.
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- A convenience: AEMeasurability of `c ↦ μH[1] (A' ∩ u⁻¹{c})` (intersection
  -- with the roles swapped), which is how the slices appear below.
  have slice_aemeas' : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (A' ∩ u ⁻¹' {c})) := by
    intro A' hA'
    refine (slice_aemeas hA').congr ?_
    filter_upwards with c
    rw [Set.inter_comm]
  -- ===================================================================
  -- (A)  The key inequality for a SIMPLE function `s`:
  --      `∫⁻ c, (∫⁻ z in u⁻¹{c}, s z ∂μH[1]) ≤ ∫⁻ z, w z * s z`.
  -- The slice integral of a simple function is a finite range-sum, each term
  -- of which is bounded by `coarea_set_sharp`; the right side reassembles via
  -- `withDensity`.
  -- ===================================================================
  have hsimple : ∀ s : SimpleFunc ℂ ℝ≥0∞,
      ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, s z ∂(μH[1] : Measure ℂ))
        ≤ ∫⁻ z, w z * s z ∂volume := by
    intro s
    -- LHS slice as a finite sum over the range of `s`.
    have hslice_sum : ∀ c : ℝ,
        (∫⁻ z in u ⁻¹' {c}, s z ∂(μH[1] : Measure ℂ))
          = ∑ x ∈ s.range, x * μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}) := by
      intro c
      rw [SimpleFunc.lintegral_eq_lintegral]
      show s.lintegral ((μH[1] : Measure ℂ).restrict (u ⁻¹' {c})) = _
      rw [SimpleFunc.lintegral]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Measure.restrict_apply (s.measurableSet_preimage {x})]
    rw [lintegral_congr hslice_sum]
    rw [lintegral_finset_sum']
    · -- Bound each term by `coarea_set_sharp`.
      have hbound : ∀ x ∈ s.range,
          (∫⁻ c, x * μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}))
            ≤ x * ∫⁻ z in s ⁻¹' {x}, w z ∂volume := by
        intro x _
        rw [lintegral_const_mul'' x (slice_aemeas' (s.measurableSet_preimage {x}))]
        refine mul_le_mul' le_rfl ?_
        have hcomm : ∀ c : ℝ,
            μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}) = μH[1] (u ⁻¹' {c} ∩ s ⁻¹' {x}) := by
          intro c; rw [Set.inter_comm]
        rw [lintegral_congr hcomm]
        exact coarea_set_sharp hu (s.measurableSet_preimage {x})
      refine le_trans (Finset.sum_le_sum hbound) ?_
      -- Reassemble `∑ x, x * ∫⁻ in s⁻¹{x}, w = ∫⁻ z, w z * s z` via `withDensity`.
      have hRHS : ∫⁻ z, w z * s z ∂volume = ∫⁻ z, s z ∂(volume.withDensity w) := by
        rw [lintegral_withDensity_eq_lintegral_mul volume hw_meas s.measurable]
        simp only [Pi.mul_apply]
      rw [hRHS, SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
      refine Finset.sum_le_sum ?_
      intro x _
      refine mul_le_mul' le_rfl ?_
      rw [withDensity_apply w (s.measurableSet_preimage {x})]
    · -- AEMeasurability in `c` of each summand.
      intro x _
      exact (slice_aemeas' (s.measurableSet_preimage {x})).const_mul x
  -- ===================================================================
  -- (B)  Monotone convergence: `g = ⨆ n, eapprox g n`.
  -- ===================================================================
  set sn : ℕ → SimpleFunc ℂ ℝ≥0∞ := fun n => SimpleFunc.eapprox g n with hsn_def
  -- Pull the supremum out of the inner (slice) integral.
  have hLHS_pt : ∀ c : ℝ,
      (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ))
        = ⨆ n, ∫⁻ z in u ⁻¹' {c}, sn n z ∂(μH[1] : Measure ℂ) := by
    intro c
    rw [← lintegral_iSup]
    · refine lintegral_congr fun z => ?_
      exact (SimpleFunc.iSup_eapprox_apply hg z).symm
    · intro n; exact (sn n).measurable
    · intro m n hmn z
      exact SimpleFunc.monotone_eapprox g hmn z
  rw [lintegral_congr hLHS_pt]
  -- Pull the supremum out of the outer integral (in `c`).
  rw [lintegral_iSup']
  · -- `⨆ n, ∫⁻ c, slice(sₙ) ≤ ∫⁻ z, g z * w z`.
    refine iSup_le fun n => ?_
    refine le_trans (hsimple (sn n)) ?_
    refine lintegral_mono fun z => ?_
    rw [mul_comm (g z)]
    refine mul_le_mul' le_rfl ?_
    calc (sn n) z ≤ ⨆ k, (sn k) z := le_iSup (fun k => (sn k) z) n
      _ = g z := SimpleFunc.iSup_eapprox_apply hg z
  · -- AEMeasurability in `c` of `c ↦ ∫⁻ z in u⁻¹{c}, sₙ z`.
    intro n
    have hsum : (fun c => ∫⁻ z in u ⁻¹' {c}, sn n z ∂(μH[1] : Measure ℂ))
        = (fun c => ∑ x ∈ (sn n).range, x * μH[1] ((sn n) ⁻¹' {x} ∩ u ⁻¹' {c})) := by
      funext c
      rw [SimpleFunc.lintegral_eq_lintegral]
      show (sn n).lintegral ((μH[1] : Measure ℂ).restrict (u ⁻¹' {c})) = _
      rw [SimpleFunc.lintegral]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Measure.restrict_apply ((sn n).measurableSet_preimage {x})]
    rw [hsum]
    refine Finset.aemeasurable_fun_sum _ ?_
    intro x _
    exact (slice_aemeas' ((sn n).measurableSet_preimage {x})).const_mul x
  · -- Monotonicity in `n` (everywhere, hence a.e.).
    filter_upwards with c
    intro m n hmn
    refine lintegral_mono fun z => ?_
    exact SimpleFunc.monotone_eapprox g hmn z


end RiemannDynamics.Coarea

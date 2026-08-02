/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.PathCover
import RiemannDynamics.Uniformization.Perron.GreenSymmetry.Symmetry

/-!
# The deck-sum formula and symmetry of the Green's function

The Green's function of a surface is the sum of the Green's functions of its
universal path cover over a fiber, and is therefore symmetric: the cover is
simply connected, so its Green's function is symmetric, and the deck action
reindexes the fiber sums for the two poles into one another.

Main results:
* `mharmonicOn_iSup_directed` — a directed, locally bounded supremum of
  harmonic functions is harmonic;
* `hasGreenFunction_pathCover` — the cover of a hyperbolic surface is
  hyperbolic;
* `greenEnvelope_deckSum` — the deck-sum formula: the Green's envelope at a
  pole equals the supremum of the finite fiber sums of the envelopes of the
  cover;
* `greenEnvelope_symm` — **symmetry of the Green's function** on an arbitrary
  connected hyperbolic surface.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff unitInterval

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **A directed supremum of harmonic functions is harmonic** wherever it is
locally bounded: the supremum commutes with the Poisson integral by monotone
convergence along the directed order. -/
theorem mharmonicOn_iSup_directed {ι : Type*} [Nonempty ι] {s : Set M}
    (hs : IsOpen s) {u : ι → M → ℝ} (hu : ∀ i, MHarmonicOn (u i) s)
    (hdir : Directed (· ≤ ·) u)
    (hbdd : ∀ x ∈ s, BddAbove (Set.range fun i => u i x)) :
    MHarmonicOn (fun x => ⨆ i, u i x) s := by
  -- A choice function realizing directedness.
  have hdir' : ∀ i j : ι, ∃ l, u i ≤ u l ∧ u j ≤ u l := fun i j => hdir i j
  choose f hf₁ hf₂ using hdir'
  intro x hx
  -- Indices approximating the supremum at `x`.
  have happrox : ∀ n : ℕ, ∃ i : ι, (⨆ i, u i x) - 1 / ((n : ℝ) + 1) < u i x := by
    intro n
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact exists_lt_of_lt_ciSup (sub_lt_self _ h1)
  choose iseq hiseq using happrox
  -- A sequence monotone in the pointwise order and dominating the approximating indices.
  obtain ⟨k, hk0, hkS⟩ : ∃ k : ℕ → ι, k 0 = iseq 0 ∧
      ∀ n, k (n + 1) = f (k n) (iseq (n + 1)) :=
    ⟨fun n => Nat.rec (iseq 0) (fun m km => f km (iseq (m + 1))) n, rfl, fun _ => rfl⟩
  have hkmono : ∀ y : M, Monotone fun n => u (k n) y := fun y =>
    monotone_nat_of_le_succ fun n => by
      rw [hkS n]; exact hf₁ (k n) (iseq (n + 1)) y
  have hik : ∀ n : ℕ, u (iseq n) x ≤ u (k n) x := by
    intro n
    cases n with
    | zero => rw [hk0]
    | succ m => rw [hkS m]; exact hf₂ (k m) (iseq (m + 1)) x
  have hbddk : ∀ y ∈ s, BddAbove (Set.range fun n => u (k n) y) := fun y hy =>
    (hbdd y hy).mono (Set.range_comp_subset_range k fun i => u i y)
  -- The monotone limit is harmonic on `s` and below the directed supremum.
  have hVlim_harm : MHarmonicOn (fun y => ⨆ n, u (k n) y) s :=
    mharmonicOn_of_monotone_tendsto (V := fun n => u (k n))
      (Vlim := fun y => ⨆ n, u (k n) y) hs (fun n => hu (k n)) (fun y _ => hkmono y)
      (fun y hy => tendsto_atTop_ciSup (hkmono y) (hbddk y hy))
  have hVlim_le : ∀ y ∈ s, (⨆ n, u (k n) y) ≤ ⨆ i, u i y := fun y hy =>
    ciSup_le fun n => le_ciSup (hbdd y hy) (k n)
  -- At `x` the monotone limit attains the directed supremum.
  have hUx_le : (⨆ i, u i x) ≤ ⨆ n, u (k n) x := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have h1 := hiseq n
    have h2 := hik n
    have h3 : u (k n) x ≤ ⨆ m, u (k m) x := le_ciSup (hbddk x hx) n
    linarith
  -- A chart ball around `x` reading back into `s`.
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' s) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm hs
  have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' s := by
    refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
    rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
    exact hx
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.1 hopen _ hmem
  have hmem' : ∀ z ∈ ball (chartAt ℂ x x) ρ, (chartAt ℂ x).symm z ∈ s := by
    intro z hz
    have h := (hρsub hz).2
    rwa [Set.mem_preimage] at h
  -- Transport: the reading in `x`'s chart of any function harmonic on `s` is
  -- harmonic at every point of the ball, via the analytic transition map to
  -- the preferred chart of the read-back point.
  have htrans : ∀ v : M → ℝ, MHarmonicOn v s →
      ∀ w ∈ ball (chartAt ℂ x x) ρ, HarmonicAt (v ∘ (chartAt ℂ x).symm) w := by
    intro v hv w hw
    have hwt : w ∈ (chartAt ℂ x).target := (hρsub hw).1
    have hws : (chartAt ℂ x).symm w ∈ s := hmem' w hw
    have hMH : HarmonicAt (v ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w)) := hv _ hws
    have hcompat : (chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w) ∈
        contDiffGroupoid ω 𝓘(ℂ) :=
      StructureGroupoid.compatible_of_mem_maximalAtlas
        (StructureGroupoid.chart_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ)) x)
        (StructureGroupoid.chart_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ)) _)
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hcompat
    have hprop := hcompat.1
    simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
      Set.inter_univ] at hprop
    have hwτ :
        w ∈ ((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w)).source := by
      rw [OpenPartialHomeomorph.trans_source, (chartAt ℂ x).symm_source]
      exact ⟨hwt, by rw [Set.mem_preimage]; exact mem_chart_source ℂ _⟩
    have hana : AnalyticAt ℂ
        (⇑((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w))) w :=
      (hprop.contDiffAt
        (((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w)).open_source.mem_nhds
          hwτ)).analyticAt
    have hcomp : HarmonicAt ((v ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        ⇑((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w))) w := by
      refine harmonicAt_comp_analyticAt ?_ hana
      rw [OpenPartialHomeomorph.trans_apply]
      exact hMH
    have hev : ((v ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        ⇑((chartAt ℂ x).symm ≫ₕ chartAt ℂ ((chartAt ℂ x).symm w))) =ᶠ[𝓝 w]
        (v ∘ (chartAt ℂ x).symm) := by
      have hcont : ContinuousAt (chartAt ℂ x).symm w := (chartAt ℂ x).continuousAt_symm hwt
      have hnb : ∀ᶠ z in 𝓝 w, (chartAt ℂ x).symm z ∈
          (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
        hcont.eventually_mem
          ((chartAt ℂ ((chartAt ℂ x).symm w)).open_source.mem_nhds (mem_chart_source ℂ _))
      filter_upwards [hnb] with z hz
      simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hz]
    exact (harmonicAt_congr_nhds hev).1 hcomp
  -- Every member of the family is dominated by the monotone limit on the
  -- half ball: enlarge the sequence past the given index and compare the two
  -- limits by the Harnack inequality, using equality at the center.
  have hkey : ∀ j : ι, ∀ z ∈ ball (chartAt ℂ x x) (ρ / 2),
      u j ((chartAt ℂ x).symm z) ≤ ⨆ n, u (k n) ((chartAt ℂ x).symm z) := by
    intro j
    obtain ⟨k', hk'0, hk'S⟩ : ∃ k' : ℕ → ι, k' 0 = f (k 0) j ∧
        ∀ n, k' (n + 1) = f (k' n) (k (n + 1)) :=
      ⟨fun n => Nat.rec (f (k 0) j) (fun m km => f km (k (m + 1))) n, rfl, fun _ => rfl⟩
    have hk'mono : ∀ y : M, Monotone fun n => u (k' n) y := fun y =>
      monotone_nat_of_le_succ fun n => by
        rw [hk'S n]; exact hf₁ (k' n) (k (n + 1)) y
    have hkk' : ∀ n : ℕ, ∀ y : M, u (k n) y ≤ u (k' n) y := by
      intro n y
      cases n with
      | zero => rw [hk'0]; exact hf₁ (k 0) j y
      | succ m => rw [hk'S m]; exact hf₂ (k' m) (k (m + 1)) y
    have hjk' : ∀ n : ℕ, ∀ y : M, u j y ≤ u (k' n) y := by
      intro n y
      induction n with
      | zero => rw [hk'0]; exact hf₂ (k 0) j y
      | succ m ih => exact ih.trans (hk'mono y (Nat.le_succ m))
    have hbddk' : ∀ y ∈ s, BddAbove (Set.range fun n => u (k' n) y) := fun y hy =>
      (hbdd y hy).mono (Set.range_comp_subset_range k' fun i => u i y)
    have hV'lim_harm : MHarmonicOn (fun y => ⨆ n, u (k' n) y) s :=
      mharmonicOn_of_monotone_tendsto (V := fun n => u (k' n))
        (Vlim := fun y => ⨆ n, u (k' n) y) hs (fun n => hu (k' n)) (fun y _ => hk'mono y)
        (fun y hy => tendsto_atTop_ciSup (hk'mono y) (hbddk' y hy))
    have hVleV' : ∀ y ∈ s, (⨆ n, u (k n) y) ≤ ⨆ n, u (k' n) y := fun y hy =>
      ciSup_le fun n => (hkk' n y).trans (le_ciSup (hbddk' y hy) n)
    have hjleV' : ∀ y ∈ s, u j y ≤ ⨆ n, u (k' n) y := fun y hy =>
      (hjk' 0 y).trans (le_ciSup (hbddk' y hy) 0)
    have hV'x : (⨆ n, u (k' n) x) ≤ ⨆ n, u (k n) x :=
      le_trans (ciSup_le fun n => le_ciSup (hbdd x hx) (k' n)) hUx_le
    -- Harnack comparison of the two limits on the chart ball.
    have hρ2 : (0 : ℝ) < ρ / 2 := by positivity
    have h2ρ : 2 * (ρ / 2) = ρ := by ring
    have hdiff : HarmonicOnNhd
        (((fun y => ⨆ n, u (k' n) y) ∘ (chartAt ℂ x).symm) -
          ((fun y => ⨆ n, u (k n) y) ∘ (chartAt ℂ x).symm))
        (ball (chartAt ℂ x x) (2 * (ρ / 2))) := by
      rw [h2ρ]
      exact fun z hz => (htrans _ hV'lim_harm z hz).sub (htrans _ hVlim_harm z hz)
    have hpos : ∀ z ∈ ball (chartAt ℂ x x) (2 * (ρ / 2)),
        0 ≤ (((fun y => ⨆ n, u (k' n) y) ∘ (chartAt ℂ x).symm) -
          ((fun y => ⨆ n, u (k n) y) ∘ (chartAt ℂ x).symm)) z := by
      rw [h2ρ]
      intro z hz
      simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
      exact hVleV' _ (hmem' z hz)
    intro z hz
    obtain ⟨-, hup⟩ := harnack_inequality_ball hρ2 hdiff hpos z hz
    have hcx : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv hxsrc
    simp only [Pi.sub_apply, Function.comp_apply, hcx] at hup
    have hzs : (chartAt ℂ x).symm z ∈ s :=
      hmem' z (ball_subset_ball (by linarith) hz)
    have hle := hjleV' _ hzs
    have h0 : (⨆ n, u (k' n) x) - (⨆ n, u (k n) x) ≤ 0 := sub_nonpos.mpr hV'x
    linarith
  -- On the half ball the directed supremum agrees with the monotone limit.
  have hfinal : ∀ z ∈ ball (chartAt ℂ x x) (ρ / 2),
      (⨆ n, u (k n) ((chartAt ℂ x).symm z)) = ⨆ i, u i ((chartAt ℂ x).symm z) := by
    intro z hz
    have hzs : (chartAt ℂ x).symm z ∈ s :=
      hmem' z (ball_subset_ball (by linarith) hz)
    exact le_antisymm (hVlim_le _ hzs) (ciSup_le fun j => hkey j z hz)
  -- Transport the local identity through the chart.
  have hVlimAt : HarmonicAt ((fun y => ⨆ n, u (k n) y) ∘ (chartAt ℂ x).symm)
      (chartAt ℂ x x) := hVlim_harm x hx
  have hev : ((fun y => ⨆ n, u (k n) y) ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      ((fun y => ⨆ i, u i y) ∘ (chartAt ℂ x).symm) := by
    have hρ2 : (0 : ℝ) < ρ / 2 := by positivity
    filter_upwards [Metric.ball_mem_nhds (chartAt ℂ x x) hρ2] with z hz
    exact hfinal z hz
  exact (harmonicAt_congr_nhds hev).1 hVlimAt

/-- **The universal path cover of a hyperbolic surface is hyperbolic**: the
pullback of the Green's function dominates the Perron family of the cover at
each fiber point. -/
theorem hasGreenFunction_pathCover [T2Space M] [ConnectedSpace M]
    [NoncompactSpace M] (x₀ : M) {p₀ : M} (hG : HasGreenFunction p₀)
    {pc : PathCover x₀} (hpc : pathCoverProj x₀ pc = p₀) :
    HasGreenFunction pc := by
  classical
  -- ### Instances on the cover.
  haveI : T2Space (PathCover x₀) := t2space_pathCover x₀
  haveI : PathConnectedSpace (PathCover x₀) := pathConnectedSpace_pathCover x₀
  haveI : ConnectedSpace (PathCover x₀) := PathConnectedSpace.connectedSpace
  haveI : NoncompactSpace (PathCover x₀) := noncompactSpace_pathCover x₀
  -- ### Plane-side transfer of subharmonicity along a pointwise equality.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  -- ### Downstairs data: the envelope is harmonic and bounded off the pole.
  have hg := mharmonicOn_greenEnvelope hG
  have hp₀src : p₀ ∈ (chartAt ℂ p₀).source := mem_chart_source ℂ p₀
  -- The zero function belongs to the family downstairs.
  have hzero_mem : (fun _ : M => (0 : ℝ)) ∈ greenFamily p₀ := by
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpcc : ContinuousAt (poleCoord p₀) p₀ := by
      have h1 : ContinuousAt (chartAt ℂ p₀) p₀ :=
        (chartAt ℂ p₀).continuousAt hp₀src
      exact h1.sub continuousAt_const
    have h0 : ‖poleCoord p₀ p₀‖ < 1 := by simp [poleCoord]
    have h5 := (hpcc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have hx1 : ‖poleCoord p₀ x‖ < 1 := hx
    have h6 : Real.log ‖poleCoord p₀ x‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hx1.le
    simpa using h6
  -- ### The patched envelope downstairs and the pulled-back majorant.
  set gd : M → ℝ := fun y => if y = p₀ then 1 else greenEnvelope p₀ y with hgddef
  have hgd_eq : ∀ y : M, y ≠ p₀ → gd y = greenEnvelope p₀ y := by
    intro y hy
    rw [hgddef]
    exact if_neg hy
  have hgd_p₀ : gd p₀ = 1 := by
    rw [hgddef]
    exact if_pos rfl
  set G : PathCover x₀ → ℝ := fun q => gd (pathCoverProj x₀ q) with hGdef
  have hgd_nonneg : ∀ y : M, 0 ≤ gd y := by
    intro y
    by_cases hy : y = p₀
    · rw [hy, hgd_p₀]
      norm_num
    · rw [hgd_eq y hy]
      have henv : greenEnvelope p₀ y = sSup ((fun v => v y) '' greenFamily p₀) := rfl
      rw [henv]
      exact le_csSup (hg.2 y hy) ⟨fun _ => 0, hzero_mem, rfl⟩
  have hGnn : ∀ q : PathCover x₀, 0 ≤ G q := fun q => hgd_nonneg (pathCoverProj x₀ q)
  -- ### The projection is continuous and the off-fiber set is open.
  have hproj_cont : Continuous (pathCoverProj x₀) := (pathCoverProj_isCoveringMap x₀).continuous
  have hOfib_open : IsOpen (pathCoverProj x₀ ⁻¹' ({p₀}ᶜ : Set M)) :=
    isOpen_compl_singleton.preimage hproj_cont
  -- ### The pulled-back majorant is harmonic off the fiber.
  have hGharm : ∀ q : PathCover x₀, pathCoverProj x₀ q ≠ p₀ → MHarmonicAt G q := by
    intro q hq
    obtain ⟨e₂, he₂, f₂, hf₂, hqe₂, hpqf₂, hmap₂, hcomm₂⟩ :=
      exists_charts_pathCoverProj_comm x₀ q
    rw [mharmonicAt_iff_of_mem_maximalAtlas he₂ hqe₂]
    have hgh : MHarmonicAt (greenEnvelope p₀) (pathCoverProj x₀ q) :=
      hg.1 _ (Set.mem_compl_singleton_iff.mpr hq)
    have hdown : HarmonicAt ((greenEnvelope p₀) ∘ ⇑f₂.symm) (f₂ (pathCoverProj x₀ q)) :=
      (mharmonicAt_iff_of_mem_maximalAtlas hf₂ hpqf₂).mp hgh
    have hcv : f₂ (pathCoverProj x₀ q) = e₂ q := hcomm₂ q hqe₂
    rw [hcv] at hdown
    have hqmem : q ∈ pathCoverProj x₀ ⁻¹' ({p₀}ᶜ : Set M) := by
      rw [Set.mem_preimage, Set.mem_compl_singleton_iff]
      exact hq
    have hOmem : pathCoverProj x₀ ⁻¹' ({p₀}ᶜ : Set M) ∈ 𝓝 (e₂.symm (e₂ q)) := by
      rw [e₂.left_inv hqe₂]
      exact hOfib_open.mem_nhds hqmem
    have hev : (greenEnvelope p₀) ∘ ⇑f₂.symm =ᶠ[𝓝 (e₂ q)] G ∘ ⇑e₂.symm := by
      filter_upwards [e₂.open_target.mem_nhds (e₂.map_source hqe₂),
        (e₂.continuousAt_symm (e₂.map_source hqe₂)).preimage_mem_nhds hOmem] with z hz1 hz2
      have hq2 : e₂.symm z ∈ e₂.source := e₂.map_target hz1
      have h5 : f₂ (pathCoverProj x₀ (e₂.symm z)) = e₂ (e₂.symm z) := hcomm₂ _ hq2
      have h6 : e₂ (e₂.symm z) = z := e₂.right_inv hz1
      have h7 : pathCoverProj x₀ (e₂.symm z) ∈ f₂.source := hmap₂ _ hq2
      have h8 : f₂.symm z = pathCoverProj x₀ (e₂.symm z) := by
        have h9 := f₂.left_inv h7
        rw [h5, h6] at h9
        exact h9
      have h10 : pathCoverProj x₀ (e₂.symm z) ≠ p₀ := hz2
      calc ((greenEnvelope p₀) ∘ ⇑f₂.symm) z
          = greenEnvelope p₀ (f₂.symm z) := rfl
        _ = greenEnvelope p₀ (pathCoverProj x₀ (e₂.symm z)) := by rw [h8]
        _ = gd (pathCoverProj x₀ (e₂.symm z)) := (hgd_eq _ h10).symm
        _ = (G ∘ ⇑e₂.symm) z := rfl
    exact (harmonicAt_congr_nhds hev).mp hdown
  -- ### The explicit logarithmic form of the envelope near the pole downstairs.
  obtain ⟨r, hr0, -, hext, hextharm, hextval⟩ := exists_harmonic_pole_extension hG
  have hext_cont : ContinuousAt hext (chartAt ℂ p₀ p₀) :=
    (hextharm _ (mem_ball_self hr0)).1.continuousAt
  set δ : ℝ := min r (Real.exp (hext (chartAt ℂ p₀ p₀) - 2)) with hδdef
  have hδpos : 0 < δ := lt_min hr0 (Real.exp_pos _)
  have hnear : ∀ᶠ y in 𝓝 p₀, y ∈ (chartAt ℂ p₀).source ∧
      chartAt ℂ p₀ y ∈ ball (chartAt ℂ p₀ p₀) δ ∧
      hext (chartAt ℂ p₀ p₀) - 1 ≤ hext (chartAt ℂ p₀ y) := by
    have hφcont : ContinuousAt (chartAt ℂ p₀) p₀ := (chartAt ℂ p₀).continuousAt hp₀src
    have e1 : (chartAt ℂ p₀).source ∈ 𝓝 p₀ :=
      (chartAt ℂ p₀).open_source.mem_nhds hp₀src
    have e2 : ⇑(chartAt ℂ p₀) ⁻¹' ball (chartAt ℂ p₀ p₀) δ ∈ 𝓝 p₀ :=
      hφcont.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hδpos))
    have e3 : (hext ∘ ⇑(chartAt ℂ p₀)) ⁻¹'
        Set.Ioi (hext (chartAt ℂ p₀ p₀) - 1) ∈ 𝓝 p₀ := by
      refine (hext_cont.comp hφcont).preimage_mem_nhds (Ioi_mem_nhds ?_)
      change hext (chartAt ℂ p₀ p₀) - 1 < hext (chartAt ℂ p₀ p₀)
      linarith
    filter_upwards [e1, e2, e3] with y hy1 hy2 hy3
    have hy2' : chartAt ℂ p₀ y ∈ ball (chartAt ℂ p₀ p₀) δ := hy2
    have hy3' : hext (chartAt ℂ p₀ p₀) - 1 < hext (chartAt ℂ p₀ y) := hy3
    exact ⟨hy1, hy2', hy3'.le⟩
  have hform : ∀ y : M, y ≠ p₀ → y ∈ (chartAt ℂ p₀).source →
      chartAt ℂ p₀ y ∈ ball (chartAt ℂ p₀ p₀) δ →
      greenEnvelope p₀ y =
        hext (chartAt ℂ p₀ y) - Real.log ‖chartAt ℂ p₀ y - chartAt ℂ p₀ p₀‖ := by
    intro y hy h1 h2
    have hne : chartAt ℂ p₀ y ≠ chartAt ℂ p₀ p₀ := by
      intro hcon
      exact hy ((chartAt ℂ p₀).injOn h1 hp₀src hcon)
    have h3 : chartAt ℂ p₀ y ∈ ball (chartAt ℂ p₀ p₀) r \ {chartAt ℂ p₀ p₀} := by
      refine ⟨ball_subset_ball (min_le_left _ _) h2, ?_⟩
      rw [Set.mem_singleton_iff]
      exact hne
    have h4 := hextval _ h3
    rw [(chartAt ℂ p₀).left_inv h1] at h4
    linarith
  -- Near the pole the patched envelope is at least one.
  have hgd_ge_one : ∀ᶠ y in 𝓝 p₀, 1 ≤ gd y := by
    filter_upwards [hnear] with y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    by_cases hyp : y = p₀
    · rw [hyp, hgd_p₀]
    · rw [hgd_eq y hyp, hform y hyp hy1 hy2]
      have hpos : 0 < ‖chartAt ℂ p₀ y - chartAt ℂ p₀ p₀‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        intro hcon
        exact hyp ((chartAt ℂ p₀).injOn hy1 hp₀src hcon)
      have hltδ : ‖chartAt ℂ p₀ y - chartAt ℂ p₀ p₀‖ < δ := by
        have h5 := mem_ball.mp hy2
        rwa [dist_eq_norm] at h5
      have hle2 : ‖chartAt ℂ p₀ y - chartAt ℂ p₀ p₀‖ ≤
          Real.exp (hext (chartAt ℂ p₀ p₀) - 2) := by
        have h6 : δ ≤ Real.exp (hext (chartAt ℂ p₀ p₀) - 2) := min_le_right _ _
        linarith
      have hlog : Real.log ‖chartAt ℂ p₀ y - chartAt ℂ p₀ p₀‖ ≤
          hext (chartAt ℂ p₀ p₀) - 2 := by
        have h7 := Real.log_le_log hpos hle2
        rwa [Real.log_exp] at h7
      linarith
  -- ### The trivializing neighborhood of the distinguished lift.
  obtain ⟨e₀, hpce₀, he₀eq, -⟩ := exists_pathCover_openPartialHomeomorph x₀ pc
  -- ### Charts commuting with the projection at the distinguished lift.
  obtain ⟨e₁, he₁, f₁, hf₁, hpce₁, hppf₁, hmap₁, hcomm₁⟩ :=
    exists_charts_pathCoverProj_comm x₀ pc
  rw [hpc] at hppf₁
  -- The upstairs transition from the preferred chart to `e₁` is analytic.
  have ht1 : AnalyticAt ℂ (⇑((chartAt ℂ pc).symm ≫ₕ e₁)) (chartAt ℂ pc pc) := by
    have hcd : ContDiffOn ℂ ω (⇑((chartAt ℂ pc).symm ≫ₕ e₁))
        ((chartAt ℂ pc).symm ≫ₕ e₁).source := by
      have h1 := (IsManifold.compatible_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas pc) he₁).1
      simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
        Set.inter_univ] at h1
      exact h1
    have hsrc : chartAt ℂ pc pc ∈ ((chartAt ℂ pc).symm ≫ₕ e₁).source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨mem_chart_target ℂ pc, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ pc).left_inv (mem_chart_source ℂ pc)]
      exact hpce₁
    exact (hcd.differentiableOn (by simp)).analyticAt
      (((chartAt ℂ pc).symm ≫ₕ e₁).open_source.mem_nhds hsrc)
  -- The downstairs transition from `f₁` to the preferred chart is analytic.
  have ht2 : AnalyticAt ℂ (⇑(f₁.symm ≫ₕ chartAt ℂ p₀)) (f₁ p₀) := by
    have hcd : ContDiffOn ℂ ω (⇑(f₁.symm ≫ₕ chartAt ℂ p₀))
        (f₁.symm ≫ₕ chartAt ℂ p₀).source := by
      have h1 := (IsManifold.compatible_of_mem_maximalAtlas hf₁
        (IsManifold.chart_mem_maximalAtlas p₀)).1
      simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
        Set.inter_univ] at h1
      exact h1
    have hsrc : f₁ p₀ ∈ (f₁.symm ≫ₕ chartAt ℂ p₀).source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨f₁.map_source hppf₁, ?_⟩
      rw [Set.mem_preimage, f₁.left_inv hppf₁]
      exact hp₀src
    exact (hcd.differentiableOn (by simp)).analyticAt
      ((f₁.symm ≫ₕ chartAt ℂ p₀).open_source.mem_nhds hsrc)
  have hΘ1 : (⇑((chartAt ℂ pc).symm ≫ₕ e₁)) (chartAt ℂ pc pc) = f₁ p₀ := by
    have h1 : (⇑((chartAt ℂ pc).symm ≫ₕ e₁)) (chartAt ℂ pc pc)
        = e₁ ((chartAt ℂ pc).symm (chartAt ℂ pc pc)) := rfl
    rw [h1, (chartAt ℂ pc).left_inv (mem_chart_source ℂ pc), ← hcomm₁ pc hpce₁, hpc]
  set Θ : ℂ → ℂ := ⇑(f₁.symm ≫ₕ chartAt ℂ p₀) ∘ ⇑((chartAt ℂ pc).symm ≫ₕ e₁) with hΘdef
  have hΘana : AnalyticAt ℂ Θ (chartAt ℂ pc pc) := by
    rw [hΘdef]
    have h2 : AnalyticAt ℂ (⇑(f₁.symm ≫ₕ chartAt ℂ p₀))
        ((⇑((chartAt ℂ pc).symm ≫ₕ e₁)) (chartAt ℂ pc pc)) := by
      rw [hΘ1]
      exact ht2
    exact h2.comp ht1
  obtain ⟨cb, hcb⟩ := Asymptotics.isBigO_iff.mp hΘana.differentiableAt.hasFDerivAt.isBigO_sub
  set cc : ℝ := max cb 1 with hccdef
  have hcc1 : (1 : ℝ) ≤ cc := le_max_right _ _
  have hcc0 : (0 : ℝ) < cc := lt_of_lt_of_le one_pos hcc1
  have hcb' : ∀ᶠ z in 𝓝 (chartAt ℂ pc pc),
      ‖Θ z - Θ (chartAt ℂ pc pc)‖ ≤ cc * ‖z - chartAt ℂ pc pc‖ := by
    filter_upwards [hcb] with z hz
    have h1 : cb * ‖z - chartAt ℂ pc pc‖ ≤ cc * ‖z - chartAt ℂ pc pc‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    linarith
  have hψtend : Tendsto (⇑(chartAt ℂ pc)) (𝓝 pc) (𝓝 (chartAt ℂ pc pc)) :=
    (chartAt ℂ pc).continuousAt (mem_chart_source ℂ pc)
  have hprojpc : Tendsto (pathCoverProj x₀) (𝓝 pc) (𝓝 (pathCoverProj x₀ pc)) :=
    hproj_cont.continuousAt
  rw [hpc] at hprojpc
  -- ### Near the lift the majorant matches the candidate pole growth.
  have hnearpc : ∀ᶠ q in 𝓝[≠] pc, pathCoverProj x₀ q ≠ p₀ ∧
      -Real.log ‖poleCoord pc q‖ -
        (1 - hext (chartAt ℂ p₀ p₀) + Real.log cc) ≤ G q := by
    filter_upwards [nhdsWithin_le_nhds (e₀.open_source.mem_nhds hpce₀),
      nhdsWithin_le_nhds ((chartAt ℂ pc).open_source.mem_nhds (mem_chart_source ℂ pc)),
      nhdsWithin_le_nhds (e₁.open_source.mem_nhds hpce₁),
      nhdsWithin_le_nhds (hprojpc.eventually hnear),
      nhdsWithin_le_nhds (hψtend.eventually hcb'),
      self_mem_nhdsWithin] with q hq0 hqψ hqe₁ hq4 hq5 hqmem
    obtain ⟨hq4a, hq4b, hq4c⟩ := hq4
    have hqne : q ≠ pc := Set.mem_compl_singleton_iff.mp hqmem
    have hprojne : pathCoverProj x₀ q ≠ p₀ := by
      intro hcon
      have h1 : e₀ q = pathCoverProj x₀ q := he₀eq q hq0
      have h2 : e₀ pc = pathCoverProj x₀ pc := he₀eq pc hpce₀
      have h3 : e₀ q = e₀ pc := by rw [h1, h2, hcon, hpc]
      exact hqne (e₀.injOn hq0 hpce₀ h3)
    have hprojf₁ : pathCoverProj x₀ q ∈ f₁.source := hmap₁ q hqe₁
    have hid1 : Θ (chartAt ℂ pc q) = chartAt ℂ p₀ (pathCoverProj x₀ q) := by
      have h1 : Θ (chartAt ℂ pc q)
          = chartAt ℂ p₀ (f₁.symm (e₁ ((chartAt ℂ pc).symm (chartAt ℂ pc q)))) := rfl
      rw [h1, (chartAt ℂ pc).left_inv hqψ, ← hcomm₁ q hqe₁, f₁.left_inv hprojf₁]
    have hid2 : Θ (chartAt ℂ pc pc) = chartAt ℂ p₀ p₀ := by
      have h1 : Θ (chartAt ℂ pc pc)
          = chartAt ℂ p₀ (f₁.symm ((⇑((chartAt ℂ pc).symm ≫ₕ e₁)) (chartAt ℂ pc pc))) := rfl
      rw [h1, hΘ1, f₁.left_inv hppf₁]
    have hpole1 : poleCoord p₀ (pathCoverProj x₀ q)
        = chartAt ℂ p₀ (pathCoverProj x₀ q) - chartAt ℂ p₀ p₀ := rfl
    have hpole2 : poleCoord pc q = chartAt ℂ pc q - chartAt ℂ pc pc := rfl
    have hpos1 : 0 < ‖poleCoord p₀ (pathCoverProj x₀ q)‖ := by
      rw [hpole1, norm_pos_iff, sub_ne_zero]
      intro hcon
      exact hprojne ((chartAt ℂ p₀).injOn hq4a hp₀src hcon)
    have hpos2 : 0 < ‖poleCoord pc q‖ := by
      rw [hpole2, norm_pos_iff, sub_ne_zero]
      intro hcon
      exact hqne ((chartAt ℂ pc).injOn hqψ (mem_chart_source ℂ pc) hcon)
    have hcmp : ‖poleCoord p₀ (pathCoverProj x₀ q)‖ ≤ cc * ‖poleCoord pc q‖ := by
      rw [hpole1, hpole2, ← hid1, ← hid2]
      exact hq5
    have hlogcmp : Real.log ‖poleCoord p₀ (pathCoverProj x₀ q)‖ ≤
        Real.log cc + Real.log ‖poleCoord pc q‖ := by
      have h1 := Real.log_le_log hpos1 hcmp
      rwa [Real.log_mul (ne_of_gt hcc0) (ne_of_gt (hpole2 ▸ hpos2))] at h1
    have hgq : G q = hext (chartAt ℂ p₀ (pathCoverProj x₀ q)) -
        Real.log ‖chartAt ℂ p₀ (pathCoverProj x₀ q) - chartAt ℂ p₀ p₀‖ := by
      have h1 : G q = gd (pathCoverProj x₀ q) := rfl
      rw [h1, hgd_eq _ hprojne, hform _ hprojne hq4a hq4b]
    refine ⟨hprojne, ?_⟩
    rw [hgq, ← hpole1]
    linarith [hq4c, hlogcmp]
  -- ### Every candidate of the cover family lies below the majorant off the fiber.
  have hle : ∀ v ∈ greenFamily pc, ∀ q : PathCover x₀,
      pathCoverProj x₀ q ≠ p₀ → v q ≤ G q := by
    intro v hv q hqfib
    obtain ⟨hsub, hcont, ⟨Kv, hKvc, -, hKv0⟩, C, hC⟩ := hv
    have hfin : (pathCoverProj x₀ ⁻¹' {p₀} ∩ Kv).Finite :=
      finite_fiber_inter_compact x₀ hKvc p₀
    set F : Finset (PathCover x₀) := insert pc hfin.toFinset with hFdef
    set w : PathCover x₀ → ℝ := fun y => max (v y - G y) (-1) with hwdef
    -- Subharmonicity off the punctures.
    have hwsub : MSubharmonicOn w ((↑F : Set (PathCover x₀))ᶜ) := by
      intro y hy
      have hyF : y ∉ F := fun hcon => hy (Finset.mem_coe.mpr hcon)
      have hyne : y ≠ pc := by
        intro hcon
        apply hyF
        rw [hFdef, hcon]
        exact Finset.mem_insert_self pc hfin.toFinset
      by_cases hyfib : pathCoverProj x₀ y = p₀
      · -- Fiber points off the support: locally the constant `-1`.
        have hyK : y ∉ Kv := by
          intro hyK
          apply hyF
          rw [hFdef]
          exact Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨hyfib, hyK⟩)
        have hprojy : Tendsto (pathCoverProj x₀) (𝓝 y) (𝓝 (pathCoverProj x₀ y)) :=
          hproj_cont.continuousAt
        rw [hyfib] at hprojy
        have hA : ∀ᶠ x in 𝓝 y, w x = -1 := by
          filter_upwards [hKvc.isClosed.isOpen_compl.mem_nhds hyK,
            hprojy.eventually hgd_ge_one] with x hx1 hx2
          have h1 : v x = 0 := hKv0 x hx1
          have h2 : (1 : ℝ) ≤ G x := hx2
          have h3 : v x - G x ≤ -1 := by rw [h1]; linarith
          exact max_eq_right h3
        obtain ⟨r₀, hr₀, hb₀, hs₀⟩ :=
          (mharmonicAt_const (x := y) (a := (-1 : ℝ))).msubharmonicAt
        have hAn : {x | w x = -1} ∈ 𝓝 ((chartAt ℂ y).symm (chartAt ℂ y y)) := by
          rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
          exact hA
        obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
          (((chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)).preimage_mem_nhds hAn)
        refine ⟨min r₀ ε, lt_min hr₀ hε, (ball_subset_ball (min_le_left _ _)).trans hb₀, ?_⟩
        refine transfer _ _ _ _ hs₀ (ball_subset_ball (min_le_left _ _)) ?_
        intro z hz
        have h1 : (chartAt ℂ y).symm z ∈ {x | w x = -1} :=
          hεsub (ball_subset_ball (min_le_right _ _) hz)
        calc ((fun _ => (-1 : ℝ)) ∘ ⇑(chartAt ℂ y).symm) z = -1 := rfl
          _ = (w ∘ ⇑(chartAt ℂ y).symm) z := h1.symm
      · -- Off the fiber: subharmonic minus harmonic, then max with a constant.
        have h1 : MSubharmonicAt v y := hsub y (Set.mem_compl_singleton_iff.mpr hyne)
        have h2 : MHarmonicAt G y := hGharm y hyfib
        have h3 : MSubharmonicAt (fun x => v x - G x) y := h1.sub_mharmonicAt h2
        have h4 : MSubharmonicAt (fun _ : PathCover x₀ => (-1 : ℝ)) y :=
          mharmonicAt_const.msubharmonicAt
        exact h3.max h4
    -- Nonpositivity off the support.
    have hwsupp : ∃ K : Set (PathCover x₀), IsCompact K ∧ ∀ x ∉ K, w x ≤ 0 := by
      refine ⟨Kv, hKvc, fun x hx => ?_⟩
      have h1 : v x = 0 := hKv0 x hx
      have h2 : v x - G x ≤ 0 := by rw [h1]; linarith [hGnn x]
      exact max_le h2 (by norm_num)
    -- Boundedness near each puncture.
    have hwpole : ∀ p ∈ F, ∃ C', ∀ᶠ x in 𝓝[≠] p, w x ≤ C' := by
      intro p hp
      by_cases hppc : p = pc
      · subst hppc
        refine ⟨max (C + (1 - hext (chartAt ℂ p₀ p₀) + Real.log cc)) (-1), ?_⟩
        filter_upwards [hC, hnearpc] with x h1 h2
        have h3 : v x - G x ≤ C + (1 - hext (chartAt ℂ p₀ p₀) + Real.log cc) := by
          have h4 := h2.2
          linarith
        exact max_le_max h3 (le_refl (-1))
      · have hcv : ContinuousAt v p :=
          hcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hppc))
        refine ⟨max (v p + 1) (-1), ?_⟩
        have h1 : ∀ᶠ x in 𝓝 p, v x < v p + 1 := hcv.eventually_lt_const (lt_add_one _)
        filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with x hx
        have h2 : v x - G x ≤ v p + 1 := by linarith [hGnn x]
        exact max_le_max h2 (le_refl (-1))
    have hfinal := msubharmonic_le_zero_of_finite_punctures hwsub hwsupp hwpole
    have hqF : q ∉ F := by
      intro hq
      rw [hFdef] at hq
      rcases Finset.mem_insert.mp hq with h | h
      · exact hqfib (h ▸ hpc)
      · exact hqfib (hfin.mem_toFinset.mp h).1
    have h5 : w q ≤ 0 := hfinal q hqF
    have h6 : v q - G q ≤ w q := le_max_left _ _
    linarith
  -- ### A witness point of the cover off the fiber.
  obtain ⟨y, hytgt, hyne⟩ : ∃ y : M, y ∈ e₀.target ∧ y ≠ p₀ := by
    have hp₀tgt : p₀ ∈ e₀.target := by
      have h1 := e₀.map_source hpce₀
      rw [he₀eq pc hpce₀, hpc] at h1
      exact h1
    have hW : IsOpen ((chartAt ℂ p₀).target ∩ ⇑(chartAt ℂ p₀).symm ⁻¹' e₀.target) :=
      (chartAt ℂ p₀).isOpen_inter_preimage_symm e₀.open_target
    have hmem : chartAt ℂ p₀ p₀ ∈
        (chartAt ℂ p₀).target ∩ ⇑(chartAt ℂ p₀).symm ⁻¹' e₀.target := by
      refine ⟨mem_chart_target ℂ p₀, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ p₀).left_inv hp₀src]
      exact hp₀tgt
    obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hW _ hmem
    have hzball : chartAt ℂ p₀ p₀ + ((ρ / 2 : ℝ) : ℂ) ∈ ball (chartAt ℂ p₀ p₀) ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ρ / 2)]
      linarith
    have hzne : chartAt ℂ p₀ p₀ + ((ρ / 2 : ℝ) : ℂ) ≠ chartAt ℂ p₀ p₀ := by
      intro hcon
      have h1 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
        have h2 := congrArg (fun t => t - chartAt ℂ p₀ p₀) hcon
        simpa using h2
      have h3 : (ρ / 2 : ℝ) = 0 := by exact_mod_cast h1
      linarith
    obtain ⟨hz1, hz2⟩ := hρsub hzball
    refine ⟨(chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀ + ((ρ / 2 : ℝ) : ℂ)), hz2, ?_⟩
    intro hcon
    have h1 : chartAt ℂ p₀ ((chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀ + ((ρ / 2 : ℝ) : ℂ)))
        = chartAt ℂ p₀ p₀ + ((ρ / 2 : ℝ) : ℂ) := (chartAt ℂ p₀).right_inv hz1
    rw [hcon] at h1
    exact hzne h1.symm
  set xw : PathCover x₀ := e₀.symm y with hxwdef
  have hxwsrc : xw ∈ e₀.source := e₀.map_target hytgt
  have hxwproj : pathCoverProj x₀ xw = y := by
    rw [← he₀eq xw hxwsrc, hxwdef]
    exact e₀.right_inv hytgt
  have hxwfib : pathCoverProj x₀ xw ≠ p₀ := by
    rw [hxwproj]
    exact hyne
  have hxwne : xw ≠ pc := by
    intro hcon
    rw [hcon, hpc] at hxwfib
    exact hxwfib rfl
  refine ⟨xw, hxwne, G xw, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  exact hle v hv xw hxwfib

/-- **The deck-sum formula**: the Green's envelope of the base at a pole is
the supremum of the finite fiber sums of the Green's envelopes of the
universal path cover, evaluated at any lift; in particular the base is
hyperbolic at the pole as soon as the cover is hyperbolic at one of its
lifts. -/
theorem greenEnvelope_deckSum [T2Space M] [ConnectedSpace M]
    [NoncompactSpace M] (x₀ : M) {p₀ : M} {pc : PathCover x₀}
    (hG₀ : HasGreenFunction p₀)
    (hne : pathCoverProj x₀ pc ≠ p₀)
    (hfib : ∃ qc₀ : PathCover x₀, pathCoverProj x₀ qc₀ = p₀ ∧
      HasGreenFunction qc₀) :
    HasGreenFunction p₀ ∧
      greenEnvelope p₀ (pathCoverProj x₀ pc) =
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ qc ∈ F, greenEnvelope qc.1 pc := by
  classical
  -- ## Instances on the cover.
  haveI := pathConnectedSpace_pathCover x₀
  haveI : ConnectedSpace (PathCover x₀) := PathConnectedSpace.connectedSpace
  haveI := t2space_pathCover x₀
  haveI := noncompactSpace_pathCover x₀
  haveI := simplyConnectedSpace_pathCover x₀
  haveI : Nonempty (PathCover x₀) := ⟨pc⟩
  haveI : Nonempty (Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀}) := ⟨∅⟩
  obtain ⟨qc₀, hqc₀, hGqc₀⟩ := hfib
  -- ## Generic toolkit.
  have hproj_cont : Continuous (pathCoverProj x₀) :=
    (pathCoverProj_isCoveringMap x₀).continuous
  have hfib_closed : IsClosed (pathCoverProj x₀ ⁻¹' {p₀}) :=
    isClosed_singleton.preimage hproj_cont
  -- Trivializing data at each cover point.
  have hloc : ∀ xc : PathCover x₀, ∃ e : OpenPartialHomeomorph (PathCover x₀) M,
      xc ∈ e.source ∧ (∀ qc ∈ e.source, e qc = pathCoverProj x₀ qc) ∧
      e.target ⊆ (chartAt ℂ (pathCoverProj x₀ xc)).source ∧
      chartAt ℂ xc = e ≫ₕ chartAt ℂ (pathCoverProj x₀ xc) := by
    intro xc
    obtain ⟨h1, h2, h3⟩ :=
      Classical.choose_spec (exists_pathCover_openPartialHomeomorph x₀ xc)
    exact ⟨Classical.choose (exists_pathCover_openPartialHomeomorph x₀ xc), h1, h2, h3, rfl⟩
  -- Transfer of subharmonicity along a pointwise equality on a subdomain.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  -- ## The zero function and nonnegativity of envelopes.
  have hzero_memU : ∀ qc : PathCover x₀,
      (fun _ : PathCover x₀ => (0 : ℝ)) ∈ greenFamily qc := by
    intro qc
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord qc) qc :=
      ((chartAt ℂ qc).continuousAt (mem_chart_source ℂ qc)).sub continuousAt_const
    have h0 : ‖poleCoord qc qc‖ < 1 := by simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have h6 : Real.log ‖poleCoord qc x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (le_of_lt hx)
    simpa using h6
  have hzero_memD : (fun _ : M => (0 : ℝ)) ∈ greenFamily p₀ := by
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord p₀) p₀ :=
      ((chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)).sub continuousAt_const
    have h0 : ‖poleCoord p₀ p₀‖ < 1 := by simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have h6 : Real.log ‖poleCoord p₀ x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (le_of_lt hx)
    simpa using h6
  have henvU : ∀ (qc xc : PathCover x₀), 0 ≤ greenEnvelope qc xc := by
    intro qc xc
    by_cases hbb : BddAbove ((fun v => v xc) '' greenFamily qc)
    · exact le_csSup hbb ⟨_, hzero_memU qc, rfl⟩
    · have h1 : greenEnvelope qc xc = 0 := Real.sSup_of_not_bddAbove hbb
      rw [h1]
  have henvD : ∀ y : M, 0 ≤ greenEnvelope p₀ y := by
    intro y
    by_cases hbb : BddAbove ((fun v => v y) '' greenFamily p₀)
    · exact le_csSup hbb ⟨_, hzero_memD, rfl⟩
    · have h1 : greenEnvelope p₀ y = 0 := Real.sSup_of_not_bddAbove hbb
      rw [h1]
  -- ## Hyperbolicity upstairs and the harmonic envelopes.
  have hGup : ∀ qc : PathCover x₀, HasGreenFunction qc :=
    fun _ => hasGreenFunction_of_simplyConnected hGqc₀
  have hup : ∀ qc : PathCover x₀, MHarmonicOn (greenEnvelope qc) {qc}ᶜ ∧
      ∀ xc, xc ≠ qc → BddAbove ((fun v => v xc) '' greenFamily qc) :=
    fun qc => mharmonicOn_greenEnvelope (hGup qc)
  obtain ⟨hgharm, hgbdd⟩ := mharmonicOn_greenEnvelope hG₀
  -- ## Chart transfer bricks.
  -- Reading a function through the projection in the cover chart agrees with its
  -- reading downstairs, near the chart image of the point.
  have hread : ∀ (xc : PathCover x₀) (f : PathCover x₀ → ℝ) (w : M → ℝ),
      (∀ yc, w (pathCoverProj x₀ yc) = f yc) →
      (chartAt ℂ xc xc = chartAt ℂ (pathCoverProj x₀ xc) (pathCoverProj x₀ xc)) ∧
      (f ∘ (chartAt ℂ xc).symm) =ᶠ[𝓝 (chartAt ℂ xc xc)]
        (w ∘ (chartAt ℂ (pathCoverProj x₀ xc)).symm) := by
    intro xc f w hdesc
    obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc xc
    have hex : e xc = pathCoverProj x₀ xc := heq xc hmem
    have hbase : chartAt ℂ xc xc =
        chartAt ℂ (pathCoverProj x₀ xc) (pathCoverProj x₀ xc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, hex]
    refine ⟨hbase, ?_⟩
    have hcm : pathCoverProj x₀ xc ∈ (chartAt ℂ (pathCoverProj x₀ xc)).source :=
      mem_chart_source ℂ (pathCoverProj x₀ xc)
    have hcont : ContinuousAt (chartAt ℂ (pathCoverProj x₀ xc)).symm
        (chartAt ℂ (pathCoverProj x₀ xc) (pathCoverProj x₀ xc)) :=
      (chartAt ℂ (pathCoverProj x₀ xc)).continuousAt_symm
        ((chartAt ℂ (pathCoverProj x₀ xc)).map_source hcm)
    have hetgt : e.target ∈ 𝓝 ((chartAt ℂ (pathCoverProj x₀ xc)).symm
        (chartAt ℂ (pathCoverProj x₀ xc) (pathCoverProj x₀ xc))) := by
      rw [(chartAt ℂ (pathCoverProj x₀ xc)).left_inv hcm]
      refine e.open_target.mem_nhds ?_
      rw [← hex]
      exact e.map_source hmem
    have hnb : ∀ᶠ z in 𝓝 (chartAt ℂ xc xc),
        (chartAt ℂ (pathCoverProj x₀ xc)).symm z ∈ e.target := by
      rw [hbase]
      exact hcont.eventually_mem hetgt
    filter_upwards [hnb] with z hz
    have hzs : (chartAt ℂ xc).symm z =
        e.symm ((chartAt ℂ (pathCoverProj x₀ xc)).symm z) := by
      rw [hch]
      rfl
    have hmem2 : e.symm ((chartAt ℂ (pathCoverProj x₀ xc)).symm z) ∈ e.source :=
      e.map_target hz
    calc (f ∘ (chartAt ℂ xc).symm) z
        = f (e.symm ((chartAt ℂ (pathCoverProj x₀ xc)).symm z)) := by
          rw [Function.comp_apply, hzs]
      _ = w (pathCoverProj x₀ (e.symm ((chartAt ℂ (pathCoverProj x₀ xc)).symm z))) :=
          (hdesc _).symm
      _ = w (e (e.symm ((chartAt ℂ (pathCoverProj x₀ xc)).symm z))) := by
          rw [heq _ hmem2]
      _ = (w ∘ (chartAt ℂ (pathCoverProj x₀ xc)).symm) z := by
          rw [e.right_inv hz, Function.comp_apply]
  have hup_harm : ∀ (w : M → ℝ) (xc : PathCover x₀),
      MHarmonicAt w (pathCoverProj x₀ xc) → MHarmonicAt (w ∘ pathCoverProj x₀) xc := by
    intro w xc hw
    obtain ⟨hbase, hev⟩ := hread xc (w ∘ pathCoverProj x₀) w (fun _ => rfl)
    have hw' : HarmonicAt (w ∘ (chartAt ℂ (pathCoverProj x₀ xc)).symm)
        (chartAt ℂ (pathCoverProj x₀ xc) (pathCoverProj x₀ xc)) := hw
    have hgoal : HarmonicAt ((w ∘ pathCoverProj x₀) ∘ (chartAt ℂ xc).symm)
        (chartAt ℂ xc xc) := by
      refine (harmonicAt_congr_nhds hev).mpr ?_
      rw [hbase]
      exact hw'
    exact hgoal
  have hdown_harm : ∀ (W : PathCover x₀ → ℝ) (w : M → ℝ) (xc : PathCover x₀),
      (∀ yc, w (pathCoverProj x₀ yc) = W yc) → MHarmonicAt W xc →
      MHarmonicAt w (pathCoverProj x₀ xc) := by
    intro W w xc hdesc hW
    obtain ⟨hbase, hev⟩ := hread xc W w hdesc
    have hW' : HarmonicAt (W ∘ (chartAt ℂ xc).symm) (chartAt ℂ xc xc) := hW
    have hgoal : HarmonicAt (w ∘ (chartAt ℂ (pathCoverProj x₀ xc)).symm)
        (chartAt ℂ (pathCoverProj x₀ xc) (pathCoverProj x₀ xc)) := by
      rw [← hbase]
      exact (harmonicAt_congr_nhds hev).mp hW'
    exact hgoal
  have hsub_congr : ∀ (f g : PathCover x₀ → ℝ) (xc : PathCover x₀), f =ᶠ[𝓝 xc] g →
      MSubharmonicAt f xc → MSubharmonicAt g xc := by
    intro f g xc hev hf
    obtain ⟨r, hr, hrsub, hsh⟩ := hf
    have hcont : ContinuousAt (chartAt ℂ xc).symm (chartAt ℂ xc xc) :=
      (chartAt ℂ xc).continuousAt_symm
        ((chartAt ℂ xc).map_source (mem_chart_source ℂ xc))
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ xc xc),
        f ((chartAt ℂ xc).symm z) = g ((chartAt ℂ xc).symm z) := by
      have h3 : {yc | f yc = g yc} ∈ 𝓝 ((chartAt ℂ xc).symm (chartAt ℂ xc xc)) := by
        rw [(chartAt ℂ xc).left_inv (mem_chart_source ℂ xc)]
        exact hev
      exact hcont.eventually_mem h3
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.mp h2
    refine ⟨min r r₂, lt_min hr hr₂,
      (ball_subset_ball (min_le_left _ _)).trans hrsub, ?_⟩
    refine transfer _ _ _ _ hsh (ball_subset_ball (min_le_left _ _)) ?_
    intro z hz
    exact hball₂ z (ball_subset_ball (min_le_right _ _) hz)
  have hharm_congrD : ∀ (f g : M → ℝ) (y : M), f =ᶠ[𝓝 y] g →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm
        ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
    have h2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : {z | f z = g z} ∈ 𝓝 ((chartAt ℂ y).symm (chartAt ℂ y y)) := by
        rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
        exact hev
      filter_upwards [hcont.eventually_mem h3] with z hz
      exact hz
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds h2).mp hf'
  have hpolecoord : ∀ zc : PathCover x₀, pathCoverProj x₀ zc = p₀ →
      ∀ yc ∈ (chartAt ℂ zc).source,
        poleCoord zc yc = poleCoord p₀ (pathCoverProj x₀ yc) := by
    intro zc hzc yc hyc
    obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc zc
    have h1 : yc ∈ e.source := by
      rw [hch, OpenPartialHomeomorph.trans_source] at hyc
      exact hyc.1
    have h2 : chartAt ℂ zc yc =
        chartAt ℂ (pathCoverProj x₀ zc) (pathCoverProj x₀ yc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, heq yc h1]
    have h3 : chartAt ℂ zc zc =
        chartAt ℂ (pathCoverProj x₀ zc) (pathCoverProj x₀ zc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, heq zc hmem]
    simp only [poleCoord]
    rw [h2, h3, hzc]
  have hproj_tendsto : ∀ zc : PathCover x₀, pathCoverProj x₀ zc = p₀ →
      Tendsto (pathCoverProj x₀) (𝓝[≠] zc) (𝓝[≠] p₀) := by
    intro zc hzc
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Tendsto (pathCoverProj x₀) (𝓝 zc) (𝓝 (pathCoverProj x₀ zc)) :=
        hproj_cont.tendsto zc
      rw [hzc] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc zc
      have h2 : ∀ᶠ yc in 𝓝 zc, yc ∈ e.source := e.open_source.mem_nhds hmem
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h2] with yc h3 h4
      have h5 : yc ≠ zc := h4
      have h6 : pathCoverProj x₀ yc ≠ p₀ := by
        intro hcon
        apply h5
        refine e.injOn h3 hmem ?_
        rw [heq yc h3, heq zc hmem, hcon, hzc]
      exact h6
  -- ## The pole behaviour of the envelope downstairs.
  obtain ⟨B₀, hg_repr, hg_lower, hg_large⟩ : ∃ B₀ : ℝ,
      (∀ᶠ y in 𝓝[≠] p₀, greenEnvelope p₀ y + Real.log ‖poleCoord p₀ y‖ ≤ B₀) ∧
      (∀ᶠ y in 𝓝[≠] p₀, -Real.log ‖poleCoord p₀ y‖ - B₀ ≤ greenEnvelope p₀ y) ∧
      (∀ᶠ y in 𝓝[≠] p₀, 1 ≤ greenEnvelope p₀ y) := by
    obtain ⟨r₀, hr₀, hr₀sub, h₀, hh₀harm, hh₀eq⟩ := exists_harmonic_pole_extension hG₀
    have hc₀ : ContinuousAt h₀ (chartAt ℂ p₀ p₀) :=
      (hh₀harm _ (mem_ball_self hr₀)).1.continuousAt
    set B₀ : ℝ := |h₀ (chartAt ℂ p₀ p₀)| + 1 with hB₀def
    have hB₀ : ∀ᶠ w in 𝓝 (chartAt ℂ p₀ p₀), |h₀ w| ≤ B₀ := by
      have h1 := hc₀ (Metric.ball_mem_nhds (h₀ (chartAt ℂ p₀ p₀)) one_pos)
      filter_upwards [h1] with w hw
      have h2 : |h₀ w - h₀ (chartAt ℂ p₀ p₀)| < 1 := by
        simpa [Real.dist_eq] using hw
      have h3 := abs_sub_abs_le_abs_sub (h₀ w) (h₀ (chartAt ℂ p₀ p₀))
      rw [hB₀def]
      linarith
    -- The chart-image conditions hold eventually near the pole.
    have hcp : ContinuousAt (chartAt ℂ p₀) p₀ :=
      (chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)
    have hev_src : ∀ᶠ y in 𝓝[≠] p₀, y ∈ (chartAt ℂ p₀).source :=
      nhdsWithin_le_nhds
        ((chartAt ℂ p₀).open_source.mem_nhds (mem_chart_source ℂ p₀))
    have hev_ball : ∀ᶠ y in 𝓝[≠] p₀,
        chartAt ℂ p₀ y ∈ ball (chartAt ℂ p₀ p₀) r₀ ∧ |h₀ (chartAt ℂ p₀ y)| ≤ B₀ := by
      have h0 : ∀ᶠ w in 𝓝 (chartAt ℂ p₀ p₀), w ∈ ball (chartAt ℂ p₀ p₀) r₀ :=
        isOpen_ball.eventually_mem (mem_ball_self hr₀)
      have h1 : ∀ᶠ w in 𝓝 (chartAt ℂ p₀ p₀),
          w ∈ ball (chartAt ℂ p₀ p₀) r₀ ∧ |h₀ w| ≤ B₀ := h0.and hB₀
      exact nhdsWithin_le_nhds (hcp.eventually_mem h1)
    have hg_repr' : ∀ᶠ y in 𝓝[≠] p₀,
        greenEnvelope p₀ y = h₀ (chartAt ℂ p₀ y) - Real.log ‖poleCoord p₀ y‖ := by
      filter_upwards [hev_src, hev_ball, self_mem_nhdsWithin] with y h1 h2 h3
      have hyne : y ≠ p₀ := h3
      have hne0 : chartAt ℂ p₀ y ≠ chartAt ℂ p₀ p₀ := by
        intro hcon
        exact hyne ((chartAt ℂ p₀).injOn h1 (mem_chart_source ℂ p₀) hcon)
      have hmem2 : chartAt ℂ p₀ y ∈ ball (chartAt ℂ p₀ p₀) r₀ \ {chartAt ℂ p₀ p₀} :=
        ⟨h2.1, hne0⟩
      have h4 := hh₀eq _ hmem2
      rw [(chartAt ℂ p₀).left_inv h1] at h4
      have h5 : Real.log ‖chartAt ℂ p₀ y - chartAt ℂ p₀ p₀‖ =
          Real.log ‖poleCoord p₀ y‖ := rfl
      rw [h5] at h4
      linarith
    have hpc0 : ContinuousAt (fun y => ‖poleCoord p₀ y‖) p₀ := by
      have h1 : ContinuousAt (poleCoord p₀) p₀ :=
        ((chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)).sub continuousAt_const
      exact h1.norm
    have hpc0v : ‖poleCoord p₀ p₀‖ = 0 := by simp [poleCoord]
    have hev_small : ∀ᶠ y in 𝓝[≠] p₀,
        ‖poleCoord p₀ y‖ < Real.exp (-(B₀ + 1)) ∧ 0 < ‖poleCoord p₀ y‖ := by
      have h1 : ∀ᶠ y in 𝓝 p₀, ‖poleCoord p₀ y‖ < Real.exp (-(B₀ + 1)) := by
        refine hpc0.eventually_lt_const ?_
        change ‖poleCoord p₀ p₀‖ < Real.exp (-(B₀ + 1))
        rw [hpc0v]
        positivity
      filter_upwards [nhdsWithin_le_nhds h1, hev_src, self_mem_nhdsWithin]
        with y h2 h3 h4
      refine ⟨h2, ?_⟩
      have hyne : y ≠ p₀ := h4
      have hne0 : poleCoord p₀ y ≠ 0 := by
        intro hcon
        apply hyne
        refine (chartAt ℂ p₀).injOn h3 (mem_chart_source ℂ p₀) ?_
        have h6 : chartAt ℂ p₀ y - chartAt ℂ p₀ p₀ = 0 := hcon
        linear_combination (norm := module) h6
      exact norm_pos_iff.mpr hne0
    refine ⟨B₀, ?_, ?_, ?_⟩
    · filter_upwards [hg_repr', hev_ball] with y h1 h2
      have h3 := (abs_le.mp h2.2).2
      rw [h1]
      linarith
    · filter_upwards [hg_repr', hev_ball] with y h1 h2
      have h3 := (abs_le.mp h2.2).1
      rw [h1]
      linarith
    · filter_upwards [hg_repr', hev_ball, hev_small] with y h1 h2 h3
      have h4 := (abs_le.mp h2.2).1
      have h5 : Real.log ‖poleCoord p₀ y‖ < -(B₀ + 1) :=
        (Real.log_lt_iff_lt_exp h3.2).mpr h3.1
      rw [h1]
      linarith
  -- ## Sums of subharmonic and harmonic functions on the cover.
  have hplane_add : ∀ (f g : ℂ → ℝ) (U : Set ℂ), SubharmonicOn f U → SubharmonicOn g U →
      SubharmonicOn (fun z => f z + g z) U := by
    intro f g U hf hg
    refine ⟨fun x hx => (hf.1 x hx).add (hg.1 x hx), ?_⟩
    intro c hc r hr hsub
    have hsphere : Metric.sphere c r ⊆ U :=
      Metric.sphere_subset_closedBall.trans hsub
    have hfci : CircleIntegrable f c r := (hf.1.mono hsphere).circleIntegrable hr.le
    have hgci : CircleIntegrable g c r := (hg.1.mono hsphere).circleIntegrable hr.le
    have hadd : Real.circleAverage (fun z => f z + g z) c r =
        Real.circleAverage f c r + Real.circleAverage g c r :=
      Real.circleAverage_fun_add hfci hgci
    rw [hadd]
    exact add_le_add (hf.2 c hc r hr hsub) (hg.2 c hc r hr hsub)
  have hmsub_add : ∀ (f g : PathCover x₀ → ℝ) (xc : PathCover x₀), MSubharmonicAt f xc →
      MSubharmonicAt g xc → MSubharmonicAt (fun yc => f yc + g yc) xc := by
    intro f g xc hf hg
    obtain ⟨r₁, hr₁, hb₁, hs₁⟩ := hf
    obtain ⟨r₂, hr₂, -, hs₂⟩ := hg
    have hmono : ∀ (F : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn F U → V ⊆ U →
        SubharmonicOn F V := fun F U V hF hVU =>
      ⟨hF.1.mono hVU, fun c hc ρ hρ hball => hF.2 c (hVU hc) ρ hρ (hball.trans hVU)⟩
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (ball_subset_ball (min_le_left r₁ r₂)).trans hb₁, ?_⟩
    exact hplane_add _ _ _
      (hmono _ _ _ hs₁ (ball_subset_ball (min_le_left r₁ r₂)))
      (hmono _ _ _ hs₂ (ball_subset_ball (min_le_right r₁ r₂)))
  have hmsub_sum : ∀ (w : {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀} →
      PathCover x₀ → ℝ) (G : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀})
      (xc : PathCover x₀), (∀ q ∈ G, MSubharmonicAt (w q) xc) →
      MSubharmonicAt (fun yc => ∑ q ∈ G, w q yc) xc := by
    intro w G
    induction G using Finset.cons_induction with
    | empty =>
      intro xc _
      have h0 : (fun yc : PathCover x₀ => ∑ q ∈ (∅ : Finset
          {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀}), w q yc) =
          fun _ => (0 : ℝ) := by
        funext yc
        simp
      rw [h0]
      exact mharmonicAt_const.msubharmonicAt
    | cons a G' ha IH =>
      intro xc hall
      have h1 : (fun yc : PathCover x₀ => ∑ q ∈ Finset.cons a G' ha, w q yc) =
          fun yc => w a yc + ∑ q ∈ G', w q yc := by
        funext yc
        rw [Finset.sum_cons]
      rw [h1]
      exact hmsub_add _ _ xc (hall a (Finset.mem_cons_self a G'))
        (IH xc fun q hq => hall q (Finset.mem_cons_of_mem hq))
  have hmharm_sum : ∀ (G : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀})
      (xc : PathCover x₀), (∀ q ∈ G, MHarmonicAt (greenEnvelope q.1) xc) →
      MHarmonicAt (fun yc => ∑ q ∈ G, greenEnvelope q.1 yc) xc := by
    intro G
    induction G using Finset.cons_induction with
    | empty =>
      intro xc _
      have h0 : (fun yc : PathCover x₀ => ∑ q ∈ (∅ : Finset
          {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀}), greenEnvelope q.1 yc) =
          fun _ => (0 : ℝ) := by
        funext yc
        simp
      rw [h0]
      exact mharmonicAt_const
    | cons a G' ha IH =>
      intro xc hall
      have h1 : (fun yc : PathCover x₀ => ∑ q ∈ Finset.cons a G' ha, greenEnvelope q.1 yc) =
          fun yc => greenEnvelope a.1 yc + ∑ q ∈ G', greenEnvelope q.1 yc := by
        funext yc
        rw [Finset.sum_cons]
      rw [h1]
      exact MHarmonicAt.add (hall a (Finset.mem_cons_self a G'))
        (IH xc fun q hq => hall q (Finset.mem_cons_of_mem hq))
  -- ## Part 1: finite fiber sums are dominated by the pulled-back envelope.
  have hpart1 : ∀ (F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀})
      (xc : PathCover x₀), pathCoverProj x₀ xc ≠ p₀ →
      (∑ q ∈ F, greenEnvelope q.1 xc) ≤ greenEnvelope p₀ (pathCoverProj x₀ xc) := by
    intro F xc hxc
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hεn : (0 : ℝ) < ε / (F.card + 1) := by positivity
    -- Near-optimal members of the fiber families at the evaluation point.
    have hex : ∀ q : {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∃ v : PathCover x₀ → ℝ, v ∈ greenFamily q.1 ∧
          greenEnvelope q.1 xc - ε / (F.card + 1) < v xc := by
      intro q
      have hne_im : ((fun v => v xc) '' greenFamily q.1).Nonempty :=
        ⟨0, ⟨fun _ => 0, hzero_memU q.1, rfl⟩⟩
      have hlt : greenEnvelope q.1 xc - ε / (F.card + 1) <
          sSup ((fun v => v xc) '' greenFamily q.1) := sub_lt_self _ hεn
      obtain ⟨b, hbmem, hb⟩ := exists_lt_of_lt_csSup hne_im hlt
      obtain ⟨v, hv, rfl⟩ := hbmem
      exact ⟨v, hv, hb⟩
    choose v hv hvx using hex
    have hvsub : ∀ q, MSubharmonicOn (v q) {q.1}ᶜ := fun q => (hv q).1
    have hvcont : ∀ q, ContinuousOn (v q) {q.1}ᶜ := fun q => (hv q).2.1
    choose K hKc hKne hKz using fun q => (hv q).2.2.1
    choose Cq hCq using fun q => (hv q).2.2.2
    -- The compact hull of the supports and the finite puncture set.
    set Khat : Set (PathCover x₀) := ⋃ q ∈ F, K q with hKhatdef
    have hKhatc : IsCompact Khat := F.isCompact_biUnion fun q _ => hKc q
    have hKhatcl : IsClosed Khat := hKhatc.isClosed
    have hfibK : (pathCoverProj x₀ ⁻¹' {p₀} ∩ Khat).Finite :=
      finite_fiber_inter_compact x₀ hKhatc p₀
    set F' : Finset (PathCover x₀) := F.image Subtype.val ∪ hfibK.toFinset with hF'def
    have hF'fib : ∀ zc ∈ F', pathCoverProj x₀ zc = p₀ := by
      intro zc hzc
      rw [hF'def, Finset.mem_union] at hzc
      rcases hzc with h | h
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp h
        exact q.2
      · exact ((Set.Finite.mem_toFinset hfibK).mp h).1
    -- The comparison majorant, adjusted at the pole.
    set G₁ : M → ℝ := fun y => if y = p₀ then 1 else greenEnvelope p₀ y with hG₁def
    have hG₁eq : ∀ y, y ≠ p₀ → G₁ y = greenEnvelope p₀ y := by
      intro y hy
      simp only [hG₁def]
      rw [if_neg hy]
    have hG₁nonneg : ∀ y, 0 ≤ G₁ y := by
      intro y
      by_cases hy : y = p₀
      · simp only [hG₁def]
        rw [if_pos hy]
        norm_num
      · rw [hG₁eq y hy]
        exact henvD y
    have hG₁one : ∀ᶠ y in 𝓝 p₀, 1 ≤ G₁ y := by
      have h1 := eventually_nhdsWithin_iff.mp hg_large
      filter_upwards [h1] with y hy
      by_cases hyp : y = p₀
      · simp only [hG₁def]
        rw [if_pos hyp]
      · rw [hG₁eq y hyp]
        exact hy hyp
    have hG₁harm : ∀ y, y ≠ p₀ → MHarmonicAt G₁ y := by
      intro y hy
      have hev : greenEnvelope p₀ =ᶠ[𝓝 y] G₁ := by
        have h1 : ({p₀}ᶜ : Set M) ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds hy
        filter_upwards [h1] with z hz
        exact (hG₁eq z hz).symm
      exact hharm_congrD _ _ y hev (hgharm y hy)
    obtain ⟨O₀, hO₀p, hO₀open, hO₀mem⟩ := eventually_nhds_iff.mp hG₁one
    -- The comparison function on the cover.
    set wt : PathCover x₀ → ℝ :=
      fun yc => max ((∑ q ∈ F, v q yc) - G₁ (pathCoverProj x₀ yc)) (-1) with hwtdef
    -- Subharmonicity off the punctures.
    have hwsub : MSubharmonicOn wt ((↑F' : Set (PathCover x₀)))ᶜ := by
      intro yc hyc
      by_cases hproj : pathCoverProj x₀ yc = p₀
      · -- A fiber point outside the punctures: locally the constant `-1`.
        have hycK : yc ∉ Khat := by
          intro hK
          apply hyc
          rw [Finset.mem_coe, hF'def, Finset.mem_union]
          right
          rw [Set.Finite.mem_toFinset]
          exact ⟨hproj, hK⟩
        have hnb : ∀ᶠ zc in 𝓝 yc, wt zc = -1 := by
          have h1 : IsOpen (Khatᶜ ∩ pathCoverProj x₀ ⁻¹' O₀) :=
            hKhatcl.isOpen_compl.inter (hO₀open.preimage hproj_cont)
          have h2 : yc ∈ Khatᶜ ∩ pathCoverProj x₀ ⁻¹' O₀ := by
            refine ⟨hycK, ?_⟩
            rw [Set.mem_preimage, hproj]
            exact hO₀mem
          filter_upwards [h1.eventually_mem h2] with zc hzc
          have hsum0 : (∑ q ∈ F, v q zc) = 0 := Finset.sum_eq_zero fun q hq =>
            hKz q zc fun hK => hzc.1 (Set.mem_biUnion hq hK)
          have hG1 : 1 ≤ G₁ (pathCoverProj x₀ zc) := hO₀p _ hzc.2
          simp only [hwtdef]
          rw [hsum0, max_eq_right (by linarith)]
        have hconst : MSubharmonicAt (fun _ : PathCover x₀ => (-1 : ℝ)) yc :=
          mharmonicAt_const.msubharmonicAt
        refine hsub_congr _ _ yc ?_ hconst
        filter_upwards [hnb] with zc h
        exact h.symm
      · -- Off the fiber: the maximum of a subharmonic difference and a constant.
        have hsum_sub : MSubharmonicAt (fun zc => ∑ q ∈ F, v q zc) yc :=
          hmsub_sum v F yc fun q hq => hvsub q yc
            (fun h => hproj (by rw [h]; exact q.2))
        have hGproj : MHarmonicAt (G₁ ∘ pathCoverProj x₀) yc :=
          hup_harm G₁ yc (hG₁harm _ hproj)
        have hconst : MSubharmonicAt (fun _ : PathCover x₀ => (-1 : ℝ)) yc :=
          mharmonicAt_const.msubharmonicAt
        have hmax := (hsum_sub.sub_mharmonicAt hGproj).max hconst
        simp only [hwtdef]
        exact hmax
    -- The comparison function vanishes off the compact hull.
    have hsupp : ∀ zc, zc ∉ Khat → wt zc ≤ 0 := by
      intro zc hzc
      have hsum0 : (∑ q ∈ F, v q zc) = 0 := Finset.sum_eq_zero fun q hq =>
        hKz q zc fun hK => hzc (Set.mem_biUnion hq hK)
      have h1 := hG₁nonneg (pathCoverProj x₀ zc)
      simp only [hwtdef]
      rw [hsum0]
      exact max_le (by linarith) (by norm_num)
    -- Boundedness above near each puncture.
    have hpole : ∀ zc ∈ F', ∃ C, ∀ᶠ yc in 𝓝[≠] zc, wt yc ≤ C := by
      intro zc hzc
      have hzcp : pathCoverProj x₀ zc = p₀ := hF'fib zc hzc
      have hG₁log : ∀ᶠ yc in 𝓝[≠] zc,
          -G₁ (pathCoverProj x₀ yc) ≤ Real.log ‖poleCoord zc yc‖ + B₀ := by
        have h1 : ∀ᶠ y in 𝓝[≠] p₀, -Real.log ‖poleCoord p₀ y‖ - B₀ ≤ G₁ y := by
          filter_upwards [hg_lower, self_mem_nhdsWithin] with y h2 h3
          rw [hG₁eq y h3]
          exact h2
        have hpcev : ∀ᶠ yc in 𝓝[≠] zc,
            poleCoord zc yc = poleCoord p₀ (pathCoverProj x₀ yc) := by
          have h4 : ∀ᶠ yc in 𝓝 zc, yc ∈ (chartAt ℂ zc).source :=
            (chartAt ℂ zc).open_source.eventually_mem (mem_chart_source ℂ zc)
          filter_upwards [nhdsWithin_le_nhds h4] with yc h5
          exact hpolecoord zc hzcp yc h5
        filter_upwards [(hproj_tendsto zc hzcp).eventually h1, hpcev] with yc h2 h3
        rw [h3]
        linarith
      by_cases hzF : ∃ q ∈ F, q.1 = zc
      · obtain ⟨q₀, hq₀F, hq₀⟩ := hzF
        have hhead : ∀ᶠ yc in 𝓝[≠] zc,
            v q₀ yc ≤ Cq q₀ - Real.log ‖poleCoord zc yc‖ := by
          have h1 := hCq q₀
          rw [hq₀] at h1
          filter_upwards [h1] with yc h2
          linarith
        have hrest : ∀ᶠ yc in 𝓝[≠] zc, ∀ q ∈ F.erase q₀,
            v q yc ≤ v q zc + 1 := by
          rw [eventually_all_finset]
          intro q hq
          have hqne : q.1 ≠ zc := by
            intro hcon
            exact (Finset.mem_erase.mp hq).1 (Subtype.ext (by rw [hcon, hq₀]))
          have hcont : ContinuousAt (v q) zc :=
            (hvcont q).continuousAt (isOpen_compl_singleton.mem_nhds
              fun h => hqne (id (Eq.symm h)))
          have h3 : ∀ᶠ yc in 𝓝 zc, v q yc < v q zc + 1 :=
            hcont.eventually_lt_const (lt_add_one _)
          exact nhdsWithin_le_nhds (h3.mono fun yc h => h.le)
        refine ⟨max (Cq q₀ + (∑ q ∈ F.erase q₀, (v q zc + 1)) + B₀) (-1), ?_⟩
        filter_upwards [hhead, hrest, hG₁log] with yc h1 h2 h3
        have hsplit : (∑ q ∈ F, v q yc) = v q₀ yc + ∑ q ∈ F.erase q₀, v q yc :=
          (Finset.add_sum_erase F (fun q => v q yc) hq₀F).symm
        have h4 : (∑ q ∈ F.erase q₀, v q yc) ≤ ∑ q ∈ F.erase q₀, (v q zc + 1) :=
          Finset.sum_le_sum h2
        simp only [hwtdef]
        refine max_le ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_left _ _)
        rw [hsplit]
        linarith
      · have hall : ∀ᶠ yc in 𝓝[≠] zc, ∀ q ∈ F, v q yc ≤ v q zc + 1 := by
          rw [eventually_all_finset]
          intro q hq
          have hqne : q.1 ≠ zc := fun hcon => hzF ⟨q, hq, hcon⟩
          have hcont : ContinuousAt (v q) zc :=
            (hvcont q).continuousAt (isOpen_compl_singleton.mem_nhds
              fun h => hqne (id (Eq.symm h)))
          have h3 : ∀ᶠ yc in 𝓝 zc, v q yc < v q zc + 1 :=
            hcont.eventually_lt_const (lt_add_one _)
          exact nhdsWithin_le_nhds (h3.mono fun yc h => h.le)
        refine ⟨max (∑ q ∈ F, (v q zc + 1)) (-1), ?_⟩
        filter_upwards [hall] with yc h1
        have h2 : (∑ q ∈ F, v q yc) ≤ ∑ q ∈ F, (v q zc + 1) := Finset.sum_le_sum h1
        have h3 := hG₁nonneg (pathCoverProj x₀ yc)
        simp only [hwtdef]
        refine max_le ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_left _ _)
        linarith
    -- The finitely-punctured maximum principle on the cover.
    have hle := msubharmonic_le_zero_of_finite_punctures (F := F') hwsub
      ⟨Khat, hKhatc, hsupp⟩ hpole
    have hxcF' : xc ∉ F' := fun h => hxc (hF'fib xc h)
    have h1 : wt xc ≤ 0 := hle xc hxcF'
    simp only [hwtdef] at h1
    have h2 : (∑ q ∈ F, v q xc) - G₁ (pathCoverProj x₀ xc) ≤ 0 :=
      le_trans (le_max_left _ _) h1
    have h3 : (∑ q ∈ F, v q xc) ≤ greenEnvelope p₀ (pathCoverProj x₀ xc) := by
      rw [← hG₁eq _ hxc]
      linarith
    have h4 : (∑ q ∈ F, (greenEnvelope q.1 xc - ε / (F.card + 1))) ≤
        ∑ q ∈ F, v q xc := Finset.sum_le_sum fun q _ => (hvx q).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h4
    have h5 : (F.card : ℝ) * (ε / (F.card + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (Nat.cast_add_one_pos F.card)]
      nlinarith [hε.le]
    linarith
  have hSbdd : ∀ xc : PathCover x₀, pathCoverProj x₀ xc ≠ p₀ →
      BddAbove (Set.range fun F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀} =>
        ∑ q ∈ F, greenEnvelope q.1 xc) := by
    intro xc hxc
    refine ⟨greenEnvelope p₀ (pathCoverProj x₀ xc), ?_⟩
    rintro b ⟨F, rfl⟩
    exact hpart1 F xc hxc
  -- ## The deck sum is harmonic off the fiber.
  have hSharm : MHarmonicOn
      (fun xc => ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 xc) (pathCoverProj x₀ ⁻¹' {p₀})ᶜ := by
    have hu : ∀ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        MHarmonicOn (fun xc => ∑ q ∈ F, greenEnvelope q.1 xc)
          (pathCoverProj x₀ ⁻¹' {p₀})ᶜ := by
      intro F xc hxc
      have hxcp : pathCoverProj x₀ xc ≠ p₀ := by
        simpa [Set.mem_preimage] using hxc
      exact hmharm_sum F xc fun q _ =>
        (hup q.1).1 xc (fun h => hxcp (by rw [h]; exact q.2))
    have hdir : Directed (· ≤ ·)
        (fun (F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀})
          (xc : PathCover x₀) => ∑ q ∈ F, greenEnvelope q.1 xc) := by
      intro F₁ F₂
      refine ⟨F₁ ∪ F₂, fun xc => ?_, fun xc => ?_⟩
      · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          fun q _ _ => henvU q.1 xc
      · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          fun q _ _ => henvU q.1 xc
    have hbdd : ∀ xc ∈ (pathCoverProj x₀ ⁻¹' {p₀})ᶜ,
        BddAbove (Set.range
          fun F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀} =>
            ∑ q ∈ F, greenEnvelope q.1 xc) := by
      intro xc hxc
      have hxcp : pathCoverProj x₀ xc ≠ p₀ := by
        simpa [Set.mem_preimage] using hxc
      exact hSbdd xc hxcp
    exact mharmonicOn_iSup_directed hfib_closed.isOpen_compl hu hdir hbdd
  -- ## Path connectivity downstairs and the canonical lifts.
  have hjoin : ∀ y : M, Nonempty (Path x₀ y) := by
    -- Every point has a chart-ball neighborhood whose points are joined to it.
    have hVnb : ∀ y : M, ∃ V : Set M, IsOpen V ∧ y ∈ V ∧
        ∀ z ∈ V, Nonempty (Path y z) := by
      intro y
      set φ := chartAt ℂ y with hφ
      have hy : y ∈ φ.source := mem_chart_source ℂ y
      obtain ⟨r, hr0, hball⟩ :=
        Metric.isOpen_iff.mp φ.open_target (φ y) (φ.map_source hy)
      refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ y) r,
        φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball,
        ⟨hy, by rw [Set.mem_preimage]; exact Metric.mem_ball_self hr0⟩, ?_⟩
      intro z hz
      have hcm : ∀ t : I, (1 - (t : ℝ)) • φ y + (t : ℝ) • φ z ∈ Metric.ball (φ y) r := by
        intro t
        have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by
          have := t.2.2
          linarith
        exact (convex_ball (φ y) r) (Metric.mem_ball_self hr0) hz.2 h1 t.2.1 (by ring)
      have hcombo : Continuous fun t : I => (1 - (t : ℝ)) • φ y + (t : ℝ) • φ z := by
        have hcoe : Continuous fun t : I => (t : ℝ) := continuous_subtype_val
        have h2 : Continuous fun t : I =>
            ((1 - (t : ℝ) : ℝ) : ℂ) * φ y + ((t : ℝ) : ℂ) * φ z :=
          ((Complex.continuous_ofReal.comp (continuous_const.sub hcoe)).mul
            continuous_const).add
            ((Complex.continuous_ofReal.comp hcoe).mul continuous_const)
        refine h2.congr fun t => ?_
        rw [Complex.real_smul, Complex.real_smul]
      refine ⟨⟨⟨fun t => φ.symm ((1 - (t : ℝ)) • φ y + (t : ℝ) • φ z), ?_⟩, ?_, ?_⟩⟩
      · exact φ.continuousOn_symm.comp_continuous hcombo fun t => hball (hcm t)
      · change φ.symm ((1 - ((0 : I) : ℝ)) • φ y + ((0 : I) : ℝ) • φ z) = y
        norm_num
        exact φ.left_inv hy
      · change φ.symm ((1 - ((1 : I) : ℝ)) • φ y + ((1 : I) : ℝ) • φ z) = z
        norm_num
        exact φ.left_inv hz.1
    -- The set of points joined to the basepoint is clopen and nonempty.
    have hopen : IsOpen {y : M | Nonempty (Path x₀ y)} := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨V, hVo, hyV, hVp⟩ := hVnb y
      exact ⟨V, fun z hz => ⟨(hy.some).trans (hVp z hz).some⟩, hVo, hyV⟩
    have hclosed : IsClosed {y : M | Nonempty (Path x₀ y)} := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨V, hVo, hyV, hVp⟩ := hVnb y
      refine ⟨V, fun z hz hzA => hy ?_, hVo, hyV⟩
      exact ⟨(hzA.some).trans (hVp z hz).some.symm⟩
    have hclopen : IsClopen {y : M | Nonempty (Path x₀ y)} := ⟨hclosed, hopen⟩
    have huniv : {y : M | Nonempty (Path x₀ y)} = Set.univ :=
      IsClopen.eq_univ hclopen ⟨x₀, ⟨Path.refl x₀⟩⟩
    intro y
    exact Set.eq_univ_iff_forall.mp huniv y
  have hcls : ∀ y : M, ∃ qc : PathCover x₀, pathCoverProj x₀ qc = y :=
    fun y => ⟨⟨y, ⟦(hjoin y).some⟧⟩, rfl⟩
  choose lift hlift using hcls
  -- ## Deck invariance of the deck sum.
  have hdeck : ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (xc : PathCover x₀),
      (⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 (pathCoverDeck x₀ γ xc)) =
      ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 xc := by
    intro γ xc
    obtain ⟨E, hE⟩ := exists_pathCoverDeck_diffeomorph x₀ γ
    have hprojE : ∀ yc, pathCoverProj x₀ (E yc) = pathCoverProj x₀ yc := by
      intro yc
      rw [hE yc]
      exact pathCoverProj_deck x₀ γ yc
    have hprojEsymm : ∀ yc, pathCoverProj x₀ (E.symm yc) = pathCoverProj x₀ yc := by
      intro yc
      have h1 := hprojE (E.symm yc)
      rw [E.apply_symm_apply] at h1
      exact h1.symm
    -- The two fiber reindexing embeddings.
    have hinj₁ : Function.Injective
        (fun q : {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀} =>
          (⟨E.symm q.1, by rw [hprojEsymm]; exact q.2⟩ :
            {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀})) := by
      intro a b h
      have h1 : E.symm a.1 = E.symm b.1 := congrArg Subtype.val h
      have h2 : E (E.symm a.1) = E (E.symm b.1) := congrArg (⇑E) h1
      rw [E.apply_symm_apply, E.apply_symm_apply] at h2
      exact Subtype.ext h2
    have hinj₂ : Function.Injective
        (fun q : {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀} =>
          (⟨E q.1, by rw [hprojE]; exact q.2⟩ :
            {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀})) := by
      intro a b h
      have h1 : E a.1 = E b.1 := congrArg Subtype.val h
      have h2 : E.symm (E a.1) = E.symm (E b.1) := congrArg (⇑E.symm) h1
      rw [E.symm_apply_apply, E.symm_apply_apply] at h2
      exact Subtype.ext h2
    -- Termwise conformal invariance along the deck diffeomorphism.
    have hterm : ∀ q : {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        greenEnvelope q.1 (pathCoverDeck x₀ γ xc) = greenEnvelope (E.symm q.1) xc := by
      intro q
      have h1 := greenEnvelope_comp_diffeomorph E (E.symm q.1) xc
      rw [E.apply_symm_apply, hE xc] at h1
      exact h1
    have hterm' : ∀ q : {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        greenEnvelope (E q.1) (pathCoverDeck x₀ γ xc) = greenEnvelope q.1 xc := by
      intro q
      have h1 := greenEnvelope_comp_diffeomorph E q.1 xc
      rw [hE xc] at h1
      exact h1
    -- The two families of finite sums have identical ranges.
    have hrange : (Set.range
        fun F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀} =>
          ∑ q ∈ F, greenEnvelope q.1 (pathCoverDeck x₀ γ xc)) =
        Set.range fun F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀} =>
          ∑ q ∈ F, greenEnvelope q.1 xc := by
      ext b
      constructor
      · rintro ⟨F, rfl⟩
        refine ⟨F.map ⟨_, hinj₁⟩, ?_⟩
        beta_reduce
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl fun q _ => (hterm q).symm
      · rintro ⟨F, rfl⟩
        refine ⟨F.map ⟨_, hinj₂⟩, ?_⟩
        beta_reduce
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl fun q _ => hterm' q
    exact congrArg sSup hrange
  have hS_desc : ∀ yc : PathCover x₀,
      (⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 (lift (pathCoverProj x₀ yc))) =
      ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 yc := by
    intro yc
    obtain ⟨γ, hγ⟩ := pathCoverDeck_transitive x₀ yc (lift (pathCoverProj x₀ yc))
      (hlift (pathCoverProj x₀ yc)).symm
    rw [← hγ]
    exact hdeck γ yc
  -- ## The descended deck sum: nonnegativity, harmonicity, pole bound.
  have hs_nonneg : ∀ z : M,
      (0 : ℝ) ≤ ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 (lift z) :=
    fun z => Real.iSup_nonneg fun F => Finset.sum_nonneg fun q _ => henvU q.1 (lift z)
  have hs_harm : MHarmonicOn
      (fun z => ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 (lift z)) {p₀}ᶜ := by
    intro z hz
    have hzp : z ≠ p₀ := hz
    have hlnf : lift z ∈ (pathCoverProj x₀ ⁻¹' {p₀})ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hlift z]
      exact hzp
    have hSat := hSharm (lift z) hlnf
    have h2 := hdown_harm
      (fun xc => ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 xc)
      (fun z' => ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 (lift z'))
      (lift z) (fun yc => hS_desc yc) hSat
    rwa [hlift z] at h2
  have hspole : ∃ C, ∀ᶠ y in 𝓝[≠] p₀,
      -Real.log ‖poleCoord p₀ y‖ - C ≤
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ q ∈ F, greenEnvelope q.1 (lift y) := by
    obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc (lift p₀)
    obtain ⟨ρ, hρ, hρsub, ht, htharm, hteq⟩ :=
      exists_harmonic_pole_extension (hGup (lift p₀))
    -- A bound for the harmonic extension near the chart image of the pole lift.
    have htc : ContinuousAt ht (chartAt ℂ (lift p₀) (lift p₀)) :=
      (htharm _ (mem_ball_self hρ)).1.continuousAt
    set B : ℝ := |ht (chartAt ℂ (lift p₀) (lift p₀))| + 1 with hBdef
    have hB : ∀ᶠ w in 𝓝 (chartAt ℂ (lift p₀) (lift p₀)), |ht w| ≤ B := by
      have h1 := htc (Metric.ball_mem_nhds (ht (chartAt ℂ (lift p₀) (lift p₀))) one_pos)
      filter_upwards [h1] with w hw
      have h2 : |ht w - ht (chartAt ℂ (lift p₀) (lift p₀))| < 1 := by
        simpa [Real.dist_eq] using hw
      have h3 := abs_sub_abs_le_abs_sub (ht w) (ht (chartAt ℂ (lift p₀) (lift p₀)))
      rw [hBdef]
      linarith
    -- The pole is the projection of its lift, and sits in the section target.
    have hp₀tgt : p₀ ∈ e.target := by
      have h1 := e.map_source hmem
      rwa [heq _ hmem, hlift p₀] at h1
    have hesymm_cont : ContinuousAt e.symm p₀ := e.continuousAt_symm hp₀tgt
    have hesymm_val : e.symm p₀ = lift p₀ := by
      have h1 : e (lift p₀) = p₀ := by rw [heq _ hmem, hlift p₀]
      have h2 := e.left_inv hmem
      rw [h1] at h2
      exact h2
    -- The section lands eventually in the chart of the pole lift.
    have hev_sec : ∀ᶠ y in 𝓝[≠] p₀,
        e.symm y ∈ (chartAt ℂ (lift p₀)).source ∧
        chartAt ℂ (lift p₀) (e.symm y) ∈ ball (chartAt ℂ (lift p₀) (lift p₀)) ρ ∧
        |ht (chartAt ℂ (lift p₀) (e.symm y))| ≤ B := by
      have h1 : ∀ᶠ y in 𝓝 p₀, e.symm y ∈ (chartAt ℂ (lift p₀)).source := by
        refine hesymm_cont.eventually_mem ?_
        rw [hesymm_val]
        exact (chartAt ℂ (lift p₀)).open_source.mem_nhds (mem_chart_source ℂ (lift p₀))
      have hcc : ContinuousAt (chartAt ℂ (lift p₀)) (e.symm p₀) := by
        rw [hesymm_val]
        exact (chartAt ℂ (lift p₀)).continuousAt (mem_chart_source ℂ (lift p₀))
      have h2 : ContinuousAt (fun y => chartAt ℂ (lift p₀) (e.symm y)) p₀ :=
        hcc.comp hesymm_cont
      have h3 : ∀ᶠ w in 𝓝 (chartAt ℂ (lift p₀) (e.symm p₀)),
          w ∈ ball (chartAt ℂ (lift p₀) (lift p₀)) ρ ∧ |ht w| ≤ B := by
        rw [hesymm_val]
        exact (isOpen_ball.eventually_mem (mem_ball_self hρ)).and hB
      have h4 := h2.eventually_mem h3
      exact nhdsWithin_le_nhds (h1.and h4)
    have hev_tgt : ∀ᶠ y in 𝓝[≠] p₀, y ∈ e.target :=
      nhdsWithin_le_nhds (e.open_target.mem_nhds hp₀tgt)
    have hev_src₀ : ∀ᶠ y in 𝓝[≠] p₀, y ∈ (chartAt ℂ p₀).source :=
      nhdsWithin_le_nhds
        ((chartAt ℂ p₀).open_source.mem_nhds (mem_chart_source ℂ p₀))
    refine ⟨B, ?_⟩
    filter_upwards [hev_sec, hev_tgt, hev_src₀, self_mem_nhdsWithin]
      with y hsec hbt hsrc₀ hyne'
    have hyne : y ≠ p₀ := hyne'
    have hxs : e.symm y ∈ e.source := e.map_target hbt
    have hprojxy : pathCoverProj x₀ (e.symm y) = y := by
      rw [← heq _ hxs]
      exact e.right_inv hbt
    -- The pole coordinate downstairs does not vanish.
    have hpc_ne : poleCoord p₀ y ≠ 0 := by
      intro hcon
      apply hyne
      refine (chartAt ℂ p₀).injOn hsrc₀ (mem_chart_source ℂ p₀) ?_
      have h6 : chartAt ℂ p₀ y - chartAt ℂ p₀ p₀ = 0 := hcon
      linear_combination (norm := module) h6
    -- The pole coordinates upstairs and downstairs agree through the section.
    have hpc_eq : poleCoord (lift p₀) (e.symm y) = poleCoord p₀ y := by
      have h1 := hpolecoord (lift p₀) (hlift p₀) (e.symm y) hsec.1
      rw [h1, hprojxy]
    -- The head term has the exact logarithmic pole.
    have hne_ctr : chartAt ℂ (lift p₀) (e.symm y) ≠ chartAt ℂ (lift p₀) (lift p₀) := by
      intro hcon
      apply hpc_ne
      rw [← hpc_eq]
      have h7 : poleCoord (lift p₀) (e.symm y) =
          chartAt ℂ (lift p₀) (e.symm y) - chartAt ℂ (lift p₀) (lift p₀) := rfl
      rw [h7, hcon, sub_self]
    have hmem3 : chartAt ℂ (lift p₀) (e.symm y) ∈
        ball (chartAt ℂ (lift p₀) (lift p₀)) ρ \ {chartAt ℂ (lift p₀) (lift p₀)} :=
      ⟨hsec.2.1, hne_ctr⟩
    have h8 := hteq _ hmem3
    rw [(chartAt ℂ (lift p₀)).left_inv hsec.1] at h8
    have h9 : Real.log ‖chartAt ℂ (lift p₀) (e.symm y) -
        chartAt ℂ (lift p₀) (lift p₀)‖ = Real.log ‖poleCoord p₀ y‖ := by
      have h10 : chartAt ℂ (lift p₀) (e.symm y) - chartAt ℂ (lift p₀) (lift p₀) =
          poleCoord (lift p₀) (e.symm y) := rfl
      rw [h10, hpc_eq]
    rw [h9] at h8
    have hhead : greenEnvelope (lift p₀) (e.symm y) =
        ht (chartAt ℂ (lift p₀) (e.symm y)) - Real.log ‖poleCoord p₀ y‖ := by
      linarith [h8]
    have hband := (abs_le.mp hsec.2.2).1
    -- The head term is dominated by the deck sum at the section point.
    have hsingle : greenEnvelope (lift p₀) (e.symm y) ≤
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ q ∈ F, greenEnvelope q.1 (e.symm y) := by
      have hb1 : pathCoverProj x₀ (e.symm y) ≠ p₀ := by
        rw [hprojxy]
        exact hyne
      have hb2 := le_ciSup (hSbdd (e.symm y) hb1)
        ({⟨lift p₀, hlift p₀⟩} : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀})
      rw [Finset.sum_singleton] at hb2
      exact hb2
    -- Transport along the descent identity.
    have hdesc := hS_desc (e.symm y)
    rw [hprojxy] at hdesc
    rw [hdesc]
    rw [hhead] at hsingle
    linarith
  -- ## Part 2: every candidate downstairs is dominated by the descended sum.
  have hpart2 : ∀ y : M, y ≠ p₀ →
      greenEnvelope p₀ y ≤
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ q ∈ F, greenEnvelope q.1 (lift y) := by
    intro y hy
    change sSup ((fun v => v y) '' greenFamily p₀) ≤ _
    refine Real.sSup_le ?_ (hs_nonneg y)
    rintro b ⟨v, hv, rfl⟩
    obtain ⟨hvsub, hvcont, ⟨Kv, hKvc, -, hKvz⟩, Cv, hCv⟩ := hv
    have hwsub : MSubharmonicOn (fun z => v z -
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ q ∈ F, greenEnvelope q.1 (lift z)) {p₀}ᶜ :=
      fun z hz => (hvsub z hz).sub_mharmonicAt (hs_harm z hz)
    have hsupp2 : ∃ K : Set M, IsCompact K ∧ ∀ z ∉ K, (v z -
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ q ∈ F, greenEnvelope q.1 (lift z)) ≤ 0 := by
      refine ⟨Kv ∪ {p₀}, hKvc.union isCompact_singleton, fun z hz => ?_⟩
      have h1 : v z = 0 := hKvz z fun h => hz (Set.mem_union_left _ h)
      have h2 := hs_nonneg z
      rw [h1]
      linarith
    have hpole2 : ∃ C, ∀ᶠ z in 𝓝[≠] p₀, (v z -
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ q ∈ F, greenEnvelope q.1 (lift z)) ≤ C := by
      obtain ⟨C₁, hC₁⟩ := hspole
      refine ⟨Cv + C₁, ?_⟩
      filter_upwards [hCv, hC₁] with z h1 h2
      linarith
    have h3 := msubharmonic_le_zero_of_puncture hwsub hsupp2 hpole2 y hy
    linarith
  -- ## Assembly.
  refine ⟨hG₀, ?_⟩
  have h1 : greenEnvelope p₀ (pathCoverProj x₀ pc) ≤
      ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
        ∑ q ∈ F, greenEnvelope q.1 pc := by
    have h2 := hpart2 (pathCoverProj x₀ pc) hne
    rwa [hS_desc pc] at h2
  have h3 : (⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
      ∑ q ∈ F, greenEnvelope q.1 pc) ≤ greenEnvelope p₀ (pathCoverProj x₀ pc) :=
    ciSup_le fun F => hpart1 F pc hne
  exact le_antisymm h1 h3

/-- **Pole independence of hyperbolicity**: a connected surface hyperbolic at
one pole is hyperbolic at every pole. The finite fiber sums of the cover at
the new pole are dominated, through the symmetry of the simply connected
cover and the deck reindexing, by the value of the Green's function at the
old pole, and their supremum descends to a harmonic majorant with the exact
logarithmic pole, bounding the Perron family at the new pole. -/
theorem hasGreenFunction_of_hasGreenFunction [T2Space M] [ConnectedSpace M]
    [NoncompactSpace M] {p q : M} (hG : HasGreenFunction p) :
    HasGreenFunction q := by
  classical
  by_cases hqp : q = p
  · rwa [hqp]
  have hpq : p ≠ q := fun h => hqp h.symm
  -- ## Downstairs path connectivity and the two distinguished lifts.
  haveI : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace ℂ M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  obtain ⟨sp⟩ := PathConnectedSpace.joined p q
  obtain ⟨pb, hpb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = p :=
    ⟨pathCoverBase p, rfl⟩
  obtain ⟨qb, hqb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = q :=
    ⟨⟨q, ⟦sp⟧⟩, rfl⟩
  -- ## Topology of the universal path cover.
  haveI : PathConnectedSpace (PathCover p) := pathConnectedSpace_pathCover p
  haveI : ConnectedSpace (PathCover p) := PathConnectedSpace.connectedSpace
  haveI : SimplyConnectedSpace (PathCover p) := simplyConnectedSpace_pathCover p
  haveI : T2Space (PathCover p) := t2space_pathCover p
  haveI : NoncompactSpace (PathCover p) := noncompactSpace_pathCover p
  haveI : Nonempty (PathCover p) := ⟨pb⟩
  haveI : Nonempty (Finset {qc : PathCover p // pathCoverProj p qc = q}) := ⟨∅⟩
  -- ## Green's functions upstairs: at the base lift, hence everywhere.
  have hGpb : HasGreenFunction pb := hasGreenFunction_pathCover p hG hpb_proj
  have hGup : ∀ rc : PathCover p, HasGreenFunction rc := fun rc =>
    hasGreenFunction_of_simplyConnected hGpb
  -- ## Generic toolkit.
  have hproj_cont : Continuous (pathCoverProj p) :=
    (pathCoverProj_isCoveringMap p).continuous
  have hfibq_closed : IsClosed (pathCoverProj p ⁻¹' {q}) :=
    isClosed_singleton.preimage hproj_cont
  have hΩopen : IsOpen ((pathCoverProj p ⁻¹' {q})ᶜ : Set (PathCover p)) :=
    hfibq_closed.isOpen_compl
  -- Trivializing data at each cover point.
  have hloc : ∀ xc : PathCover p, ∃ e : OpenPartialHomeomorph (PathCover p) M,
      xc ∈ e.source ∧ (∀ qc ∈ e.source, e qc = pathCoverProj p qc) ∧
      e.target ⊆ (chartAt ℂ (pathCoverProj p xc)).source ∧
      chartAt ℂ xc = e ≫ₕ chartAt ℂ (pathCoverProj p xc) := by
    intro xc
    obtain ⟨h1, h2, h3⟩ :=
      Classical.choose_spec (exists_pathCover_openPartialHomeomorph p xc)
    exact ⟨Classical.choose (exists_pathCover_openPartialHomeomorph p xc), h1, h2, h3, rfl⟩
  -- Canonical lifts of downstairs points.
  have hcls : ∀ y : M, ∃ qc : PathCover p, pathCoverProj p qc = y :=
    fun y => ⟨⟨y, ⟦PathConnectedSpace.somePath p y⟧⟩, rfl⟩
  choose lift hlift using hcls
  -- Transfer of subharmonicity along a pointwise equality on a subdomain.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  -- ## The zero function and nonnegativity of envelopes.
  have hzero_memU : ∀ qc : PathCover p,
      (fun _ : PathCover p => (0 : ℝ)) ∈ greenFamily qc := by
    intro qc
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord qc) qc :=
      ((chartAt ℂ qc).continuousAt (mem_chart_source ℂ qc)).sub continuousAt_const
    have h0 : ‖poleCoord qc qc‖ < 1 := by simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have h6 : Real.log ‖poleCoord qc x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (le_of_lt hx)
    simpa using h6
  have hzero_memD : ∀ y : M, (fun _ : M => (0 : ℝ)) ∈ greenFamily y := by
    intro y
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord y) y :=
      ((chartAt ℂ y).continuousAt (mem_chart_source ℂ y)).sub continuousAt_const
    have h0 : ‖poleCoord y y‖ < 1 := by simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have h6 : Real.log ‖poleCoord y x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (le_of_lt hx)
    simpa using h6
  have henvU : ∀ (qc xc : PathCover p), 0 ≤ greenEnvelope qc xc := by
    intro qc xc
    by_cases hbb : BddAbove ((fun v => v xc) '' greenFamily qc)
    · exact le_csSup hbb ⟨_, hzero_memU qc, rfl⟩
    · have h1 : greenEnvelope qc xc = 0 := Real.sSup_of_not_bddAbove hbb
      rw [h1]
  have henvD : ∀ y : M, 0 ≤ greenEnvelope p y := by
    intro y
    by_cases hbb : BddAbove ((fun v => v y) '' greenFamily p)
    · exact le_csSup hbb ⟨_, hzero_memD p, rfl⟩
    · have h1 : greenEnvelope p y = 0 := Real.sSup_of_not_bddAbove hbb
      rw [h1]
  -- ## Hyperbolicity upstairs and the harmonic envelopes.
  have hup : ∀ qc : PathCover p, MHarmonicOn (greenEnvelope qc) {qc}ᶜ ∧
      ∀ xc, xc ≠ qc → BddAbove ((fun v => v xc) '' greenFamily qc) :=
    fun qc => mharmonicOn_greenEnvelope (hGup qc)
  obtain ⟨hgharm, -⟩ := mharmonicOn_greenEnvelope hG
  -- ## Chart transfer bricks.
  have hread : ∀ (xc : PathCover p) (f : PathCover p → ℝ) (w : M → ℝ),
      (∀ yc, w (pathCoverProj p yc) = f yc) →
      (chartAt ℂ xc xc = chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) ∧
      (f ∘ (chartAt ℂ xc).symm) =ᶠ[𝓝 (chartAt ℂ xc xc)]
        (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm) := by
    intro xc f w hdesc
    obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc xc
    have hex : e xc = pathCoverProj p xc := heq xc hmem
    have hbase : chartAt ℂ xc xc =
        chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, hex]
    refine ⟨hbase, ?_⟩
    have hcm : pathCoverProj p xc ∈ (chartAt ℂ (pathCoverProj p xc)).source :=
      mem_chart_source ℂ (pathCoverProj p xc)
    have hcont : ContinuousAt (chartAt ℂ (pathCoverProj p xc)).symm
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) :=
      (chartAt ℂ (pathCoverProj p xc)).continuousAt_symm
        ((chartAt ℂ (pathCoverProj p xc)).map_source hcm)
    have hetgt : e.target ∈ 𝓝 ((chartAt ℂ (pathCoverProj p xc)).symm
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc))) := by
      rw [(chartAt ℂ (pathCoverProj p xc)).left_inv hcm]
      refine e.open_target.mem_nhds ?_
      rw [← hex]
      exact e.map_source hmem
    have hnb : ∀ᶠ z in 𝓝 (chartAt ℂ xc xc),
        (chartAt ℂ (pathCoverProj p xc)).symm z ∈ e.target := by
      rw [hbase]
      exact hcont.eventually_mem hetgt
    filter_upwards [hnb] with z hz
    have hzs : (chartAt ℂ xc).symm z =
        e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z) := by
      rw [hch]
      rfl
    have hmem2 : e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z) ∈ e.source :=
      e.map_target hz
    calc (f ∘ (chartAt ℂ xc).symm) z
        = f (e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z)) := by
          rw [Function.comp_apply, hzs]
      _ = w (pathCoverProj p (e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z))) :=
          (hdesc _).symm
      _ = w (e (e.symm ((chartAt ℂ (pathCoverProj p xc)).symm z))) := by
          rw [heq _ hmem2]
      _ = (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm) z := by
          rw [e.right_inv hz, Function.comp_apply]
  have hup_harm : ∀ (w : M → ℝ) (xc : PathCover p),
      MHarmonicAt w (pathCoverProj p xc) → MHarmonicAt (w ∘ pathCoverProj p) xc := by
    intro w xc hw
    obtain ⟨hbase, hev⟩ := hread xc (w ∘ pathCoverProj p) w (fun _ => rfl)
    have hw' : HarmonicAt (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm)
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) := hw
    have hgoal : HarmonicAt ((w ∘ pathCoverProj p) ∘ (chartAt ℂ xc).symm)
        (chartAt ℂ xc xc) := by
      refine (harmonicAt_congr_nhds hev).mpr ?_
      rw [hbase]
      exact hw'
    exact hgoal
  have hdown_harm : ∀ (W : PathCover p → ℝ) (w : M → ℝ) (xc : PathCover p),
      (∀ yc, w (pathCoverProj p yc) = W yc) → MHarmonicAt W xc →
      MHarmonicAt w (pathCoverProj p xc) := by
    intro W w xc hdesc hW
    obtain ⟨hbase, hev⟩ := hread xc W w hdesc
    have hW' : HarmonicAt (W ∘ (chartAt ℂ xc).symm) (chartAt ℂ xc xc) := hW
    have hgoal : HarmonicAt (w ∘ (chartAt ℂ (pathCoverProj p xc)).symm)
        (chartAt ℂ (pathCoverProj p xc) (pathCoverProj p xc)) := by
      rw [← hbase]
      exact (harmonicAt_congr_nhds hev).mp hW'
    exact hgoal
  have hsub_congr : ∀ (f g : PathCover p → ℝ) (xc : PathCover p), f =ᶠ[𝓝 xc] g →
      MSubharmonicAt f xc → MSubharmonicAt g xc := by
    intro f g xc hev hf
    obtain ⟨r, hr, hrsub, hsh⟩ := hf
    have hcont : ContinuousAt (chartAt ℂ xc).symm (chartAt ℂ xc xc) :=
      (chartAt ℂ xc).continuousAt_symm
        ((chartAt ℂ xc).map_source (mem_chart_source ℂ xc))
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ xc xc),
        f ((chartAt ℂ xc).symm z) = g ((chartAt ℂ xc).symm z) := by
      have h3 : {yc | f yc = g yc} ∈ 𝓝 ((chartAt ℂ xc).symm (chartAt ℂ xc xc)) := by
        rw [(chartAt ℂ xc).left_inv (mem_chart_source ℂ xc)]
        exact hev
      exact hcont.eventually_mem h3
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.mp h2
    refine ⟨min r r₂, lt_min hr hr₂,
      (ball_subset_ball (min_le_left _ _)).trans hrsub, ?_⟩
    refine transfer _ _ _ _ hsh (ball_subset_ball (min_le_left _ _)) ?_
    intro z hz
    exact hball₂ z (ball_subset_ball (min_le_right _ _) hz)
  have hharm_congrD : ∀ (f g : M → ℝ) (y : M), f =ᶠ[𝓝 y] g →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm
        ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
    have h2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : {z | f z = g z} ∈ 𝓝 ((chartAt ℂ y).symm (chartAt ℂ y y)) := by
        rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
        exact hev
      filter_upwards [hcont.eventually_mem h3] with z hz
      exact hz
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds h2).mp hf'
  have hpolecoord : ∀ zc : PathCover p, ∀ yc ∈ (chartAt ℂ zc).source,
      poleCoord zc yc = poleCoord (pathCoverProj p zc) (pathCoverProj p yc) := by
    intro zc yc hyc
    obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc zc
    have h1 : yc ∈ e.source := by
      rw [hch, OpenPartialHomeomorph.trans_source] at hyc
      exact hyc.1
    have h2 : chartAt ℂ zc yc =
        chartAt ℂ (pathCoverProj p zc) (pathCoverProj p yc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, heq yc h1]
    have h3 : chartAt ℂ zc zc =
        chartAt ℂ (pathCoverProj p zc) (pathCoverProj p zc) := by
      rw [hch, OpenPartialHomeomorph.trans_apply, heq zc hmem]
    simp only [poleCoord]
    rw [h2, h3]
  have hproj_tendsto : ∀ zc : PathCover p,
      Tendsto (pathCoverProj p) (𝓝[≠] zc) (𝓝[≠] (pathCoverProj p zc)) := by
    intro zc
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (hproj_cont.tendsto zc).mono_left nhdsWithin_le_nhds
    · obtain ⟨e, hmem, heq, htgt, hch⟩ := hloc zc
      have h2 : ∀ᶠ yc in 𝓝 zc, yc ∈ e.source := e.open_source.mem_nhds hmem
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h2] with yc h3 h4
      have h5 : yc ≠ zc := h4
      have h6 : pathCoverProj p yc ≠ pathCoverProj p zc := by
        intro hcon
        apply h5
        refine e.injOn h3 hmem ?_
        rw [heq yc h3, heq zc hmem]
        exact hcon
      exact h6
  -- ## The pole behaviour of the envelope downstairs at `p`.
  obtain ⟨B₀, hgp_lower, hgp_large⟩ : ∃ B₀ : ℝ,
      (∀ᶠ y in 𝓝[≠] p, -Real.log ‖poleCoord p y‖ - B₀ ≤ greenEnvelope p y) ∧
      (∀ᶠ y in 𝓝[≠] p, 1 ≤ greenEnvelope p y) := by
    obtain ⟨r₀, hr₀, -, h₀, hh₀harm, hh₀eq⟩ := exists_harmonic_pole_extension hG
    have hc₀ : ContinuousAt h₀ (chartAt ℂ p p) :=
      (hh₀harm _ (mem_ball_self hr₀)).1.continuousAt
    set B₀ : ℝ := |h₀ (chartAt ℂ p p)| + 1 with hB₀def
    have hB₀ : ∀ᶠ w in 𝓝 (chartAt ℂ p p), |h₀ w| ≤ B₀ := by
      have h1 := hc₀ (Metric.ball_mem_nhds (h₀ (chartAt ℂ p p)) one_pos)
      filter_upwards [h1] with w hw
      have h2 : |h₀ w - h₀ (chartAt ℂ p p)| < 1 := by
        simpa [Real.dist_eq] using hw
      have h3 := abs_sub_abs_le_abs_sub (h₀ w) (h₀ (chartAt ℂ p p))
      rw [hB₀def]
      linarith
    have hcp : ContinuousAt (chartAt ℂ p) p :=
      (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
    have hev_src : ∀ᶠ y in 𝓝[≠] p, y ∈ (chartAt ℂ p).source :=
      nhdsWithin_le_nhds
        ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hev_ball : ∀ᶠ y in 𝓝[≠] p,
        chartAt ℂ p y ∈ ball (chartAt ℂ p p) r₀ ∧ |h₀ (chartAt ℂ p y)| ≤ B₀ := by
      have h0 : ∀ᶠ w in 𝓝 (chartAt ℂ p p), w ∈ ball (chartAt ℂ p p) r₀ :=
        isOpen_ball.eventually_mem (mem_ball_self hr₀)
      have h1 : ∀ᶠ w in 𝓝 (chartAt ℂ p p),
          w ∈ ball (chartAt ℂ p p) r₀ ∧ |h₀ w| ≤ B₀ := h0.and hB₀
      exact nhdsWithin_le_nhds (hcp.eventually_mem h1)
    have hg_repr' : ∀ᶠ y in 𝓝[≠] p,
        greenEnvelope p y = h₀ (chartAt ℂ p y) - Real.log ‖poleCoord p y‖ := by
      filter_upwards [hev_src, hev_ball, self_mem_nhdsWithin] with y h1 h2 h3
      have hyne : y ≠ p := h3
      have hne0 : chartAt ℂ p y ≠ chartAt ℂ p p := by
        intro hcon
        exact hyne ((chartAt ℂ p).injOn h1 (mem_chart_source ℂ p) hcon)
      have hmem2 : chartAt ℂ p y ∈ ball (chartAt ℂ p p) r₀ \ {chartAt ℂ p p} :=
        ⟨h2.1, hne0⟩
      have h4 := hh₀eq _ hmem2
      rw [(chartAt ℂ p).left_inv h1] at h4
      have h5 : Real.log ‖chartAt ℂ p y - chartAt ℂ p p‖ =
          Real.log ‖poleCoord p y‖ := rfl
      rw [h5] at h4
      linarith
    have hpc0 : ContinuousAt (fun y => ‖poleCoord p y‖) p := by
      have h1 : ContinuousAt (poleCoord p) p :=
        ((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)).sub continuousAt_const
      exact h1.norm
    have hpc0v : ‖poleCoord p p‖ = 0 := by simp [poleCoord]
    have hev_small : ∀ᶠ y in 𝓝[≠] p,
        ‖poleCoord p y‖ < Real.exp (-(B₀ + 1)) ∧ 0 < ‖poleCoord p y‖ := by
      have h1 : ∀ᶠ y in 𝓝 p, ‖poleCoord p y‖ < Real.exp (-(B₀ + 1)) := by
        refine hpc0.eventually_lt_const ?_
        change ‖poleCoord p p‖ < Real.exp (-(B₀ + 1))
        rw [hpc0v]
        positivity
      filter_upwards [nhdsWithin_le_nhds h1, hev_src, self_mem_nhdsWithin]
        with y h2 h3 h4
      refine ⟨h2, ?_⟩
      have hyne : y ≠ p := h4
      have hne0 : poleCoord p y ≠ 0 := by
        intro hcon
        apply hyne
        refine (chartAt ℂ p).injOn h3 (mem_chart_source ℂ p) ?_
        have h6 : chartAt ℂ p y - chartAt ℂ p p = 0 := hcon
        linear_combination (norm := module) h6
      exact norm_pos_iff.mpr hne0
    refine ⟨B₀, ?_, ?_⟩
    · filter_upwards [hg_repr', hev_ball] with y h1 h2
      have h3 := (abs_le.mp h2.2).1
      rw [h1]
      linarith
    · filter_upwards [hg_repr', hev_ball, hev_small] with y h1 h2 h3
      have h4 := (abs_le.mp h2.2).1
      have h5 : Real.log ‖poleCoord p y‖ < -(B₀ + 1) :=
        (Real.log_lt_iff_lt_exp h3.2).mpr h3.1
      rw [h1]
      linarith
  -- ## Sums of subharmonic and harmonic functions on the cover.
  have hplane_add : ∀ (f g : ℂ → ℝ) (U : Set ℂ), SubharmonicOn f U → SubharmonicOn g U →
      SubharmonicOn (fun z => f z + g z) U := by
    intro f g U hf hg
    refine ⟨fun x hx => (hf.1 x hx).add (hg.1 x hx), ?_⟩
    intro c hc r hr hsub
    have hsphere : Metric.sphere c r ⊆ U :=
      Metric.sphere_subset_closedBall.trans hsub
    have hfci : CircleIntegrable f c r := (hf.1.mono hsphere).circleIntegrable hr.le
    have hgci : CircleIntegrable g c r := (hg.1.mono hsphere).circleIntegrable hr.le
    have hadd : Real.circleAverage (fun z => f z + g z) c r =
        Real.circleAverage f c r + Real.circleAverage g c r :=
      Real.circleAverage_fun_add hfci hgci
    rw [hadd]
    exact add_le_add (hf.2 c hc r hr hsub) (hg.2 c hc r hr hsub)
  have hmsub_add : ∀ (f g : PathCover p → ℝ) (xc : PathCover p), MSubharmonicAt f xc →
      MSubharmonicAt g xc → MSubharmonicAt (fun yc => f yc + g yc) xc := by
    intro f g xc hf hg
    obtain ⟨r₁, hr₁, hb₁, hs₁⟩ := hf
    obtain ⟨r₂, hr₂, -, hs₂⟩ := hg
    have hmono : ∀ (F : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn F U → V ⊆ U →
        SubharmonicOn F V := fun F U V hF hVU =>
      ⟨hF.1.mono hVU, fun c hc ρ hρ hball => hF.2 c (hVU hc) ρ hρ (hball.trans hVU)⟩
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (ball_subset_ball (min_le_left r₁ r₂)).trans hb₁, ?_⟩
    exact hplane_add _ _ _
      (hmono _ _ _ hs₁ (ball_subset_ball (min_le_left r₁ r₂)))
      (hmono _ _ _ hs₂ (ball_subset_ball (min_le_right r₁ r₂)))
  have hmsub_sum : ∀ (y : M) (w : {qc : PathCover p // pathCoverProj p qc = y} →
      PathCover p → ℝ) (G : Finset {qc : PathCover p // pathCoverProj p qc = y})
      (xc : PathCover p), (∀ j ∈ G, MSubharmonicAt (w j) xc) →
      MSubharmonicAt (fun yc => ∑ j ∈ G, w j yc) xc := by
    intro y w G
    induction G using Finset.cons_induction with
    | empty =>
      intro xc _
      have h0 : (fun yc : PathCover p => ∑ j ∈ (∅ : Finset
          {qc : PathCover p // pathCoverProj p qc = y}), w j yc) =
          fun _ => (0 : ℝ) := by
        funext yc
        simp
      rw [h0]
      exact mharmonicAt_const.msubharmonicAt
    | cons a G' ha IH =>
      intro xc hall
      have h1 : (fun yc : PathCover p => ∑ j ∈ Finset.cons a G' ha, w j yc) =
          fun yc => w a yc + ∑ j ∈ G', w j yc := by
        funext yc
        rw [Finset.sum_cons]
      rw [h1]
      exact hmsub_add _ _ xc (hall a (Finset.mem_cons_self a G'))
        (IH xc fun j hj => hall j (Finset.mem_cons_of_mem hj))
  have hmharm_sum : ∀ (y : M) (G : Finset {qc : PathCover p // pathCoverProj p qc = y})
      (xc : PathCover p), (∀ j ∈ G, MHarmonicAt (greenEnvelope j.1) xc) →
      MHarmonicAt (fun yc => ∑ j ∈ G, greenEnvelope j.1 yc) xc := by
    intro y G
    induction G using Finset.cons_induction with
    | empty =>
      intro xc _
      have h0 : (fun yc : PathCover p => ∑ j ∈ (∅ : Finset
          {qc : PathCover p // pathCoverProj p qc = y}), greenEnvelope j.1 yc) =
          fun _ => (0 : ℝ) := by
        funext yc
        simp
      rw [h0]
      exact mharmonicAt_const
    | cons a G' ha IH =>
      intro xc hall
      have h1 : (fun yc : PathCover p => ∑ j ∈ Finset.cons a G' ha, greenEnvelope j.1 yc) =
          fun yc => greenEnvelope a.1 yc + ∑ j ∈ G', greenEnvelope j.1 yc := by
        funext yc
        rw [Finset.sum_cons]
      rw [h1]
      exact MHarmonicAt.add (hall a (Finset.mem_cons_self a G'))
        (IH xc fun j hj => hall j (Finset.mem_cons_of_mem hj))
  -- ## Finite `p`-fiber sums are dominated by the pulled-back envelope at `p`.
  have hpart1p : ∀ (F : Finset {qc : PathCover p // pathCoverProj p qc = p})
      (xc : PathCover p), pathCoverProj p xc ≠ p →
      (∑ j ∈ F, greenEnvelope j.1 xc) ≤ greenEnvelope p (pathCoverProj p xc) := by
    intro F xc hxc
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hεn : (0 : ℝ) < ε / (F.card + 1) := by positivity
    have hex : ∀ j : {qc : PathCover p // pathCoverProj p qc = p},
        ∃ v : PathCover p → ℝ, v ∈ greenFamily j.1 ∧
          greenEnvelope j.1 xc - ε / (F.card + 1) < v xc := by
      intro j
      have hne_im : ((fun v => v xc) '' greenFamily j.1).Nonempty :=
        ⟨0, ⟨fun _ => 0, hzero_memU j.1, rfl⟩⟩
      have hlt : greenEnvelope j.1 xc - ε / (F.card + 1) <
          sSup ((fun v => v xc) '' greenFamily j.1) := sub_lt_self _ hεn
      obtain ⟨b, hbmem, hb⟩ := exists_lt_of_lt_csSup hne_im hlt
      obtain ⟨v, hv, rfl⟩ := hbmem
      exact ⟨v, hv, hb⟩
    choose v hv hvx using hex
    have hvsub : ∀ j, MSubharmonicOn (v j) {j.1}ᶜ := fun j => (hv j).1
    have hvcont : ∀ j, ContinuousOn (v j) {j.1}ᶜ := fun j => (hv j).2.1
    choose K hKc hKne hKz using fun j => (hv j).2.2.1
    choose Cj hCj using fun j => (hv j).2.2.2
    set Khat : Set (PathCover p) := ⋃ j ∈ F, K j with hKhatdef
    have hKhatc : IsCompact Khat := F.isCompact_biUnion fun j _ => hKc j
    have hKhatcl : IsClosed Khat := hKhatc.isClosed
    have hfibK : (pathCoverProj p ⁻¹' {p} ∩ Khat).Finite :=
      finite_fiber_inter_compact p hKhatc p
    set F' : Finset (PathCover p) := F.image Subtype.val ∪ hfibK.toFinset with hF'def
    have hF'fib : ∀ zc ∈ F', pathCoverProj p zc = p := by
      intro zc hzc
      rw [hF'def, Finset.mem_union] at hzc
      rcases hzc with h | h
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
        exact j.2
      · exact ((Set.Finite.mem_toFinset hfibK).mp h).1
    set G₁ : M → ℝ := fun y => if y = p then 1 else greenEnvelope p y with hG₁def
    have hG₁eq : ∀ y, y ≠ p → G₁ y = greenEnvelope p y := by
      intro y hy
      simp only [hG₁def]
      rw [if_neg hy]
    have hG₁nonneg : ∀ y, 0 ≤ G₁ y := by
      intro y
      by_cases hy : y = p
      · simp only [hG₁def]
        rw [if_pos hy]
        norm_num
      · rw [hG₁eq y hy]
        exact henvD y
    have hG₁one : ∀ᶠ y in 𝓝 p, 1 ≤ G₁ y := by
      have h1 := eventually_nhdsWithin_iff.mp hgp_large
      filter_upwards [h1] with y hy
      by_cases hyp : y = p
      · simp only [hG₁def]
        rw [if_pos hyp]
      · rw [hG₁eq y hyp]
        exact hy hyp
    have hG₁harm : ∀ y, y ≠ p → MHarmonicAt G₁ y := by
      intro y hy
      have hev : greenEnvelope p =ᶠ[𝓝 y] G₁ := by
        have h1 : ({p}ᶜ : Set M) ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds hy
        filter_upwards [h1] with z hz
        exact (hG₁eq z hz).symm
      exact hharm_congrD _ _ y hev (hgharm y hy)
    obtain ⟨O₀, hO₀p, hO₀open, hO₀mem⟩ := eventually_nhds_iff.mp hG₁one
    set wt : PathCover p → ℝ :=
      fun yc => max ((∑ j ∈ F, v j yc) - G₁ (pathCoverProj p yc)) (-1) with hwtdef
    have hwsub : MSubharmonicOn wt ((↑F' : Set (PathCover p)))ᶜ := by
      intro yc hyc
      by_cases hproj : pathCoverProj p yc = p
      · have hycK : yc ∉ Khat := by
          intro hK
          apply hyc
          rw [Finset.mem_coe, hF'def, Finset.mem_union]
          right
          rw [Set.Finite.mem_toFinset]
          exact ⟨hproj, hK⟩
        have hnb : ∀ᶠ zc in 𝓝 yc, wt zc = -1 := by
          have h1 : IsOpen (Khatᶜ ∩ pathCoverProj p ⁻¹' O₀) :=
            hKhatcl.isOpen_compl.inter (hO₀open.preimage hproj_cont)
          have h2 : yc ∈ Khatᶜ ∩ pathCoverProj p ⁻¹' O₀ := by
            refine ⟨hycK, ?_⟩
            rw [Set.mem_preimage, hproj]
            exact hO₀mem
          filter_upwards [h1.eventually_mem h2] with zc hzc
          have hsum0 : (∑ j ∈ F, v j zc) = 0 := Finset.sum_eq_zero fun j hj =>
            hKz j zc fun hK => hzc.1 (Set.mem_biUnion hj hK)
          have hG1 : 1 ≤ G₁ (pathCoverProj p zc) := hO₀p _ hzc.2
          simp only [hwtdef]
          rw [hsum0, max_eq_right (by linarith)]
        have hconst : MSubharmonicAt (fun _ : PathCover p => (-1 : ℝ)) yc :=
          mharmonicAt_const.msubharmonicAt
        refine hsub_congr _ _ yc ?_ hconst
        filter_upwards [hnb] with zc h
        exact h.symm
      · have hsum_sub : MSubharmonicAt (fun zc => ∑ j ∈ F, v j zc) yc :=
          hmsub_sum p v F yc fun j hj => hvsub j yc
            (fun h => hproj (by rw [h]; exact j.2))
        have hGproj : MHarmonicAt (G₁ ∘ pathCoverProj p) yc :=
          hup_harm G₁ yc (hG₁harm _ hproj)
        have hconst : MSubharmonicAt (fun _ : PathCover p => (-1 : ℝ)) yc :=
          mharmonicAt_const.msubharmonicAt
        have hmax := (hsum_sub.sub_mharmonicAt hGproj).max hconst
        simp only [hwtdef]
        exact hmax
    have hsupp : ∀ zc, zc ∉ Khat → wt zc ≤ 0 := by
      intro zc hzc
      have hsum0 : (∑ j ∈ F, v j zc) = 0 := Finset.sum_eq_zero fun j hj =>
        hKz j zc fun hK => hzc (Set.mem_biUnion hj hK)
      have h1 := hG₁nonneg (pathCoverProj p zc)
      simp only [hwtdef]
      rw [hsum0]
      exact max_le (by linarith) (by norm_num)
    have hpole : ∀ zc ∈ F', ∃ C, ∀ᶠ yc in 𝓝[≠] zc, wt yc ≤ C := by
      intro zc hzc
      have hzcp : pathCoverProj p zc = p := hF'fib zc hzc
      have hG₁log : ∀ᶠ yc in 𝓝[≠] zc,
          -G₁ (pathCoverProj p yc) ≤ Real.log ‖poleCoord zc yc‖ + B₀ := by
        have h1 : ∀ᶠ y in 𝓝[≠] p, -Real.log ‖poleCoord p y‖ - B₀ ≤ G₁ y := by
          filter_upwards [hgp_lower, self_mem_nhdsWithin] with y h2 h3
          rw [hG₁eq y h3]
          exact h2
        have hpcev : ∀ᶠ yc in 𝓝[≠] zc,
            poleCoord zc yc = poleCoord p (pathCoverProj p yc) := by
          have h4 : ∀ᶠ yc in 𝓝 zc, yc ∈ (chartAt ℂ zc).source :=
            (chartAt ℂ zc).open_source.eventually_mem (mem_chart_source ℂ zc)
          filter_upwards [nhdsWithin_le_nhds h4] with yc h5
          have h6 := hpolecoord zc yc h5
          rw [hzcp] at h6
          exact h6
        have htz := hproj_tendsto zc
        rw [hzcp] at htz
        filter_upwards [htz.eventually h1, hpcev] with yc h2 h3
        rw [h3]
        linarith
      by_cases hzF : ∃ j ∈ F, j.1 = zc
      · obtain ⟨j₀, hj₀F, hj₀⟩ := hzF
        have hhead : ∀ᶠ yc in 𝓝[≠] zc,
            v j₀ yc ≤ Cj j₀ - Real.log ‖poleCoord zc yc‖ := by
          have h1 := hCj j₀
          rw [hj₀] at h1
          filter_upwards [h1] with yc h2
          linarith
        have hrest : ∀ᶠ yc in 𝓝[≠] zc, ∀ j ∈ F.erase j₀,
            v j yc ≤ v j zc + 1 := by
          rw [eventually_all_finset]
          intro j hj
          have hjne : j.1 ≠ zc := by
            intro hcon
            exact (Finset.mem_erase.mp hj).1 (Subtype.ext (by rw [hcon, hj₀]))
          have hcont : ContinuousAt (v j) zc :=
            (hvcont j).continuousAt (isOpen_compl_singleton.mem_nhds
              fun h => hjne (id (Eq.symm h)))
          have h3 : ∀ᶠ yc in 𝓝 zc, v j yc < v j zc + 1 :=
            hcont.eventually_lt_const (lt_add_one _)
          exact nhdsWithin_le_nhds (h3.mono fun yc h => h.le)
        refine ⟨max (Cj j₀ + (∑ j ∈ F.erase j₀, (v j zc + 1)) + B₀) (-1), ?_⟩
        filter_upwards [hhead, hrest, hG₁log] with yc h1 h2 h3
        have hsplit : (∑ j ∈ F, v j yc) = v j₀ yc + ∑ j ∈ F.erase j₀, v j yc :=
          (Finset.add_sum_erase F (fun j => v j yc) hj₀F).symm
        have h4 : (∑ j ∈ F.erase j₀, v j yc) ≤ ∑ j ∈ F.erase j₀, (v j zc + 1) :=
          Finset.sum_le_sum h2
        simp only [hwtdef]
        refine max_le ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_left _ _)
        rw [hsplit]
        linarith
      · have hall : ∀ᶠ yc in 𝓝[≠] zc, ∀ j ∈ F, v j yc ≤ v j zc + 1 := by
          rw [eventually_all_finset]
          intro j hj
          have hjne : j.1 ≠ zc := fun hcon => hzF ⟨j, hj, hcon⟩
          have hcont : ContinuousAt (v j) zc :=
            (hvcont j).continuousAt (isOpen_compl_singleton.mem_nhds
              fun h => hjne (id (Eq.symm h)))
          have h3 : ∀ᶠ yc in 𝓝 zc, v j yc < v j zc + 1 :=
            hcont.eventually_lt_const (lt_add_one _)
          exact nhdsWithin_le_nhds (h3.mono fun yc h => h.le)
        refine ⟨max (∑ j ∈ F, (v j zc + 1)) (-1), ?_⟩
        filter_upwards [hall] with yc h1
        have h2 : (∑ j ∈ F, v j yc) ≤ ∑ j ∈ F, (v j zc + 1) := Finset.sum_le_sum h1
        have h3 := hG₁nonneg (pathCoverProj p yc)
        simp only [hwtdef]
        refine max_le ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_left _ _)
        linarith
    have hle := msubharmonic_le_zero_of_finite_punctures (F := F') hwsub
      ⟨Khat, hKhatc, hsupp⟩ hpole
    have hxcF' : xc ∉ F' := fun h => hxc (hF'fib xc h)
    have h1 : wt xc ≤ 0 := hle xc hxcF'
    simp only [hwtdef] at h1
    have h2 : (∑ j ∈ F, v j xc) - G₁ (pathCoverProj p xc) ≤ 0 :=
      le_trans (le_max_left _ _) h1
    have h3 : (∑ j ∈ F, v j xc) ≤ greenEnvelope p (pathCoverProj p xc) := by
      rw [← hG₁eq _ hxc]
      linarith
    have h4 : (∑ j ∈ F, (greenEnvelope j.1 xc - ε / (F.card + 1))) ≤
        ∑ j ∈ F, v j xc := Finset.sum_le_sum fun j _ => (hvx j).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h4
    have h5 : (F.card : ℝ) * (ε / (F.card + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (Nat.cast_add_one_pos F.card)]
      nlinarith [hε.le]
    linarith
  -- ## Groupoid algebra of the deck action.
  have hdeck_comp : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ (pathCoverDeck p δ pc) = pathCoverDeck p (γ.trans δ) pc := by
    intro γ δ pc
    change (⟨pc.pt, γ.trans (δ.trans pc.cls)⟩ : PathCover p)
      = ⟨pc.pt, (γ.trans δ).trans pc.cls⟩
    exact congrArg (PathCover.mk pc.pt)
      (Path.Homotopic.Quotient.trans_assoc γ δ pc.cls).symm
  have hdeck_refl : ∀ pc : PathCover p,
      pathCoverDeck p (Path.Homotopic.Quotient.refl p) pc = pc := by
    intro pc
    change (⟨pc.pt, (Path.Homotopic.Quotient.refl p).trans pc.cls⟩ : PathCover p) = pc
    exact congrArg (PathCover.mk pc.pt) (Path.Homotopic.Quotient.refl_trans pc.cls)
  have hdeck_free : ∀ (δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p δ pc = pc → δ = Path.Homotopic.Quotient.refl p := by
    intro δ pc h
    have h' : (⟨pc.pt, δ.trans pc.cls⟩ : PathCover p) = ⟨pc.pt, pc.cls⟩ := h
    rw [PathCover.mk.injEq] at h'
    have h1 : δ.trans pc.cls = pc.cls := eq_of_heq h'.2
    calc δ = δ.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl δ).symm
      _ = δ.trans (pc.cls.trans pc.cls.symm) := by
          rw [Path.Homotopic.Quotient.trans_symm]
      _ = (δ.trans pc.cls).trans pc.cls.symm :=
          (Path.Homotopic.Quotient.trans_assoc δ pc.cls pc.cls.symm).symm
      _ = pc.cls.trans pc.cls.symm := by rw [h1]
      _ = Path.Homotopic.Quotient.refl p := Path.Homotopic.Quotient.trans_symm pc.cls
  have hdeck_inj : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ pc = pathCoverDeck p δ pc → γ = δ := by
    intro γ δ pc h
    have h2 : pathCoverDeck p (δ.symm.trans γ) pc = pc := by
      rw [← hdeck_comp, h, hdeck_comp, Path.Homotopic.Quotient.symm_trans, hdeck_refl]
    have h3 := hdeck_free _ _ h2
    calc γ = (Path.Homotopic.Quotient.refl p).trans γ :=
          (Path.Homotopic.Quotient.refl_trans γ).symm
      _ = (δ.trans δ.symm).trans γ := by rw [Path.Homotopic.Quotient.trans_symm]
      _ = δ.trans (δ.symm.trans γ) := Path.Homotopic.Quotient.trans_assoc δ δ.symm γ
      _ = δ.trans (Path.Homotopic.Quotient.refl p) := by rw [h3]
      _ = δ := Path.Homotopic.Quotient.trans_refl δ
  have hsymm_symm : ∀ γ : Path.Homotopic.Quotient p p, γ.symm.symm = γ := by
    intro γ
    calc γ.symm.symm = γ.symm.symm.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl γ.symm.symm).symm
      _ = γ.symm.symm.trans (γ.symm.trans γ) := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = (γ.symm.symm.trans γ.symm).trans γ :=
          (Path.Homotopic.Quotient.trans_assoc γ.symm.symm γ.symm γ).symm
      _ = (Path.Homotopic.Quotient.refl p).trans γ := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = γ := Path.Homotopic.Quotient.refl_trans γ
  -- ## Choices: fiber loops and deck diffeomorphisms.
  have hfibA : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      ∃ γ : Path.Homotopic.Quotient p p, pathCoverDeck p γ pb = a.1 := fun a =>
    pathCoverDeck_transitive p pb a.1 (hpb_proj.trans a.2.symm)
  choose γfn hγfn using hfibA
  choose Efn hEfn using fun γ : Path.Homotopic.Quotient p p =>
    exists_pathCoverDeck_diffeomorph p γ
  -- ## The fiber reindexing map: conjugate `p`-fiber points into the `q`-fiber.
  obtain ⟨Φ, hΦspec⟩ : ∃ Φ : {qc : PathCover p // pathCoverProj p qc = p} →
      {qc : PathCover p // pathCoverProj p qc = q},
      ∀ a, (Φ a).1 = pathCoverDeck p (γfn a).symm qb :=
    ⟨fun a => ⟨pathCoverDeck p (γfn a).symm qb,
      (pathCoverProj_deck p (γfn a).symm qb).trans hqb_proj⟩, fun _ => rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro a₁ a₂ h
    have h1 : pathCoverDeck p (γfn a₁).symm qb = pathCoverDeck p (γfn a₂).symm qb := by
      rw [← hΦspec a₁, ← hΦspec a₂, h]
    have h2 : (γfn a₁).symm = (γfn a₂).symm := hdeck_inj _ _ _ h1
    have h3 : γfn a₁ = γfn a₂ := by
      rw [← hsymm_symm (γfn a₁), h2, hsymm_symm]
    apply Subtype.ext
    rw [← hγfn a₁, ← hγfn a₂, h3]
  have hΦsurj : Function.Surjective Φ := by
    intro b
    obtain ⟨δ, hδ⟩ := pathCoverDeck_transitive p qb b.1 (hqb_proj.trans b.2.symm)
    have hmem : pathCoverProj p (pathCoverDeck p δ.symm pb) = p :=
      (pathCoverProj_deck p δ.symm pb).trans hpb_proj
    refine ⟨⟨pathCoverDeck p δ.symm pb, hmem⟩, ?_⟩
    have hloop : γfn ⟨pathCoverDeck p δ.symm pb, hmem⟩ = δ.symm := by
      apply hdeck_inj _ _ pb
      exact hγfn ⟨pathCoverDeck p δ.symm pb, hmem⟩
    apply Subtype.ext
    rw [hΦspec, hloop, hsymm_symm, hδ]
  obtain ⟨e, he⟩ : ∃ e : {qc : PathCover p // pathCoverProj p qc = p} ≃
      {qc : PathCover p // pathCoverProj p qc = q}, ∀ a, e a = Φ a :=
    ⟨Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩, fun _ => rfl⟩
  -- ## Termwise symmetry: cover symmetry plus conformal invariance of the deck maps.
  have hterm : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      greenEnvelope a.1 qb = greenEnvelope (pathCoverDeck p (γfn a).symm qb) pb := by
    intro a
    have hne : a.1 ≠ qb := by
      intro h
      apply hpq
      rw [← a.2, h, hqb_proj]
    have h1 : greenEnvelope a.1 qb = greenEnvelope qb a.1 :=
      greenEnvelope_symm_of_simplyConnected (hGup a.1) hne
    have hEpb : Efn (γfn a) pb = a.1 := (hEfn (γfn a) pb).trans (hγfn a)
    have hEsymm_a : (Efn (γfn a)).symm a.1 = pb := by
      rw [← hEpb, Diffeomorph.symm_apply_apply]
    have h2 : Efn (γfn a) (pathCoverDeck p (γfn a).symm qb) = qb := by
      rw [hEfn (γfn a) (pathCoverDeck p (γfn a).symm qb), hdeck_comp,
        Path.Homotopic.Quotient.trans_symm, hdeck_refl]
    have hEsymm_q : (Efn (γfn a)).symm qb = pathCoverDeck p (γfn a).symm qb := by
      calc (Efn (γfn a)).symm qb
          = (Efn (γfn a)).symm (Efn (γfn a) (pathCoverDeck p (γfn a).symm qb)) := by
            rw [h2]
        _ = pathCoverDeck p (γfn a).symm qb := Diffeomorph.symm_apply_apply _ _
    have h3 : greenEnvelope ((Efn (γfn a)).symm qb) ((Efn (γfn a)).symm a.1)
        = greenEnvelope qb a.1 :=
      greenEnvelope_comp_diffeomorph (Efn (γfn a)).symm qb a.1
    rw [h1, ← h3, hEsymm_a, hEsymm_q]
  -- ## Reindexing of the `p`-fiber sums at `qb` into `q`-fiber sums at `pb`.
  have hFeq : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
      (∑ a ∈ F, greenEnvelope a.1 qb)
        = ∑ s ∈ e.finsetCongr F, greenEnvelope s.1 pb := by
    intro F
    rw [Equiv.finsetCongr_apply, Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [he a, hΦspec a]
    exact hterm a
  -- ## KEY BOUND: the `q`-fiber finite sums at the base lift are bounded.
  have hbdd_pb : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
      (∑ s ∈ F, greenEnvelope s.1 pb) ≤ greenEnvelope p q := by
    intro F
    have h1 := hFeq (e.finsetCongr.symm F)
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1]
    have h3 := hpart1p (e.finsetCongr.symm F) qb (by rw [hqb_proj]; exact Ne.symm hpq)
    rw [hqb_proj] at h3
    exact h3
  -- ## The `q`-fiber finite sums are harmonic off the `q`-fiber.
  have huq : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
      MHarmonicOn (fun xc => ∑ s ∈ F, greenEnvelope s.1 xc)
        (pathCoverProj p ⁻¹' {q})ᶜ := by
    intro F xc hxc
    have hxcp : pathCoverProj p xc ≠ q := by
      simpa [Set.mem_preimage] using hxc
    exact hmharm_sum q F xc fun j _ =>
      (hup j.1).1 xc (fun h => hxcp (by rw [h]; exact j.2))
  -- ## Local two-sided Harnack comparison for the `q`-fiber sums.
  have hlocH : ∀ xc : PathCover p, pathCoverProj p xc ≠ q →
      ∃ U : Set (PathCover p), IsOpen U ∧ xc ∈ U ∧
        (∀ yc ∈ U, pathCoverProj p yc ≠ q) ∧
        ∀ yc ∈ U, ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          (∑ s ∈ F, greenEnvelope s.1 yc) ≤ 3 * ∑ s ∈ F, greenEnvelope s.1 xc ∧
          (∑ s ∈ F, greenEnvelope s.1 xc) ≤ 3 * ∑ s ∈ F, greenEnvelope s.1 yc := by
    intro xc hxc
    set e₀ := chartAt ℂ xc with he₀def
    have hxsrc : xc ∈ e₀.source := mem_chart_source ℂ xc
    have hxcΩ : xc ∈ ((pathCoverProj p ⁻¹' {q})ᶜ : Set (PathCover p)) := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact hxc
    have hopen2 : IsOpen (e₀.target ∩ e₀.symm ⁻¹' (pathCoverProj p ⁻¹' {q})ᶜ) :=
      e₀.isOpen_inter_preimage_symm hΩopen
    have hmem2 : e₀ xc ∈ e₀.target ∩ e₀.symm ⁻¹' (pathCoverProj p ⁻¹' {q})ᶜ := by
      refine ⟨e₀.map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, e₀.left_inv hxsrc]
      exact hxcΩ
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    set r := ε / 4 with hrdef
    have hr0 : 0 < r := by rw [hrdef]; linarith
    have h2r : ball (e₀ xc) (2 * r) ⊆
        e₀.target ∩ e₀.symm ⁻¹' (pathCoverProj p ⁻¹' {q})ᶜ :=
      (ball_subset_ball (by rw [hrdef]; linarith)).trans hball
    have hread2 : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        HarmonicOnNhd ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘ ⇑e₀.symm)
          (ball (e₀ xc) (2 * r)) := by
      intro F w hw
      have hwt : w ∈ e₀.target := (h2r hw).1
      have hwΩ : e₀.symm w ∈ ((pathCoverProj p ⁻¹' {q})ᶜ : Set (PathCover p)) :=
        (h2r hw).2
      have hyy : e₀.symm w ∈ (chartAt ℂ (e₀.symm w)).source :=
        mem_chart_source ℂ (e₀.symm w)
      have htrans2 : AnalyticAt ℂ (⇑(chartAt ℂ (e₀.symm w)) ∘ ⇑e₀.symm) w := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e₀.symm) w :=
          contMDiffAt_symm_of_mem_maximalAtlas
            (IsManifold.chart_mem_maximalAtlas xc) hwt
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (e₀.symm w))) (e₀.symm w) :=
          contMDiffAt_of_mem_maximalAtlas
            (IsManifold.chart_mem_maximalAtlas (e₀.symm w)) hyy
        exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
      have hmh : HarmonicAt ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘
          ⇑(chartAt ℂ (e₀.symm w)).symm) ((⇑(chartAt ℂ (e₀.symm w)) ∘ ⇑e₀.symm) w) :=
        huq F (e₀.symm w) hwΩ
      have hcomp := harmonicAt_comp_analyticAt hmh htrans2
      have hev : ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘
          ⇑(chartAt ℂ (e₀.symm w)).symm) ∘ (⇑(chartAt ℂ (e₀.symm w)) ∘ ⇑e₀.symm)
          =ᶠ[𝓝 w] (fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘ ⇑e₀.symm := by
        have hS : IsOpen (e₀.target ∩ ⇑e₀.symm ⁻¹' (chartAt ℂ (e₀.symm w)).source) :=
          e₀.continuousOn_symm.isOpen_inter_preimage e₀.open_target
            (chartAt ℂ (e₀.symm w)).open_source
        filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with z hz
        simp only [Function.comp_apply]
        rw [(chartAt ℂ (e₀.symm w)).left_inv hz.2]
      exact (harmonicAt_congr_nhds hev).mp hcomp
    have hpos2 : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∀ z ∈ ball (e₀ xc) (2 * r),
          0 ≤ ((fun yc => ∑ s ∈ F, greenEnvelope s.1 yc) ∘ ⇑e₀.symm) z := by
      intro F z _
      exact Finset.sum_nonneg fun j _ => henvU j.1 (e₀.symm z)
    have hcx : e₀.symm (e₀ xc) = xc := e₀.left_inv hxsrc
    refine ⟨e₀.source ∩ ⇑e₀ ⁻¹' ball (e₀ xc) r,
      e₀.continuousOn.isOpen_inter_preimage e₀.open_source isOpen_ball,
      ⟨hxsrc, mem_ball_self hr0⟩, ?_, ?_⟩
    · intro yc hy
      have h1 : e₀ yc ∈ ball (e₀ xc) (2 * r) :=
        ball_subset_ball (by rw [hrdef]; linarith) hy.2
      have h2 := (h2r h1).2
      rw [Set.mem_preimage, e₀.left_inv hy.1] at h2
      simpa [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] using h2
    · intro yc hy F
      obtain ⟨hlow, hup2⟩ :=
        harnack_inequality_ball hr0 (hread2 F) (hpos2 F) (e₀ yc) hy.2
      have hcy : e₀.symm (e₀ yc) = yc := e₀.left_inv hy.1
      simp only [Function.comp_apply, hcx, hcy] at hlow hup2
      exact ⟨hup2, by linarith⟩
  -- ## Deck invariance of the `q`-fiber sum ranges along a fiber.
  have hrange_fib : ∀ xc yc : PathCover p,
      pathCoverProj p xc = pathCoverProj p yc →
      (Set.range fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 yc) =
      Set.range fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 xc := by
    intro xc yc hxy
    obtain ⟨γ, hγ⟩ := pathCoverDeck_transitive p xc yc hxy
    obtain ⟨E, hE⟩ := exists_pathCoverDeck_diffeomorph p γ
    have hprojE : ∀ zc, pathCoverProj p (E zc) = pathCoverProj p zc := by
      intro zc
      rw [hE zc]
      exact pathCoverProj_deck p γ zc
    have hprojEsymm : ∀ zc, pathCoverProj p (E.symm zc) = pathCoverProj p zc := by
      intro zc
      have h1 := hprojE (E.symm zc)
      rw [E.apply_symm_apply] at h1
      exact h1.symm
    have hinj₁ : Function.Injective
        (fun s : {qc : PathCover p // pathCoverProj p qc = q} =>
          (⟨E.symm s.1, by rw [hprojEsymm]; exact s.2⟩ :
            {qc : PathCover p // pathCoverProj p qc = q})) := by
      intro a b h
      have h1 : E.symm a.1 = E.symm b.1 := congrArg Subtype.val h
      have h2 : E (E.symm a.1) = E (E.symm b.1) := congrArg (⇑E) h1
      rw [E.apply_symm_apply, E.apply_symm_apply] at h2
      exact Subtype.ext h2
    have hinj₂ : Function.Injective
        (fun s : {qc : PathCover p // pathCoverProj p qc = q} =>
          (⟨E s.1, by rw [hprojE]; exact s.2⟩ :
            {qc : PathCover p // pathCoverProj p qc = q})) := by
      intro a b h
      have h1 : E a.1 = E b.1 := congrArg Subtype.val h
      have h2 : E.symm (E a.1) = E.symm (E b.1) := congrArg (⇑E.symm) h1
      rw [E.symm_apply_apply, E.symm_apply_apply] at h2
      exact Subtype.ext h2
    have hterm2 : ∀ s : {qc : PathCover p // pathCoverProj p qc = q},
        greenEnvelope s.1 (pathCoverDeck p γ xc) = greenEnvelope (E.symm s.1) xc := by
      intro s
      have h1 := greenEnvelope_comp_diffeomorph E (E.symm s.1) xc
      rw [E.apply_symm_apply, hE xc] at h1
      exact h1
    have hterm2' : ∀ s : {qc : PathCover p // pathCoverProj p qc = q},
        greenEnvelope (E s.1) (pathCoverDeck p γ xc) = greenEnvelope s.1 xc := by
      intro s
      have h1 := greenEnvelope_comp_diffeomorph E s.1 xc
      rw [hE xc] at h1
      exact h1
    have hrange : (Set.range
        fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
          ∑ s ∈ F, greenEnvelope s.1 (pathCoverDeck p γ xc)) =
        Set.range fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
          ∑ s ∈ F, greenEnvelope s.1 xc := by
      ext b
      constructor
      · rintro ⟨F, rfl⟩
        refine ⟨F.map ⟨_, hinj₁⟩, ?_⟩
        beta_reduce
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl fun s _ => (hterm2 s).symm
      · rintro ⟨F, rfl⟩
        refine ⟨F.map ⟨_, hinj₂⟩, ?_⟩
        beta_reduce
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl fun s _ => hterm2' s
    rw [hγ] at hrange
    exact hrange
  -- ## Boundedness at the base lift, transported to the canonical lift of `p`.
  have hApb : BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 pb) := by
    refine ⟨greenEnvelope p q, ?_⟩
    rintro t ⟨F, rfl⟩
    exact hbdd_pb F
  have hPp : BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift p)) := by
    rw [hrange_fib pb (lift p) (by rw [hpb_proj, hlift p])]
    exact hApb
  -- ## Downstairs neighborhoods propagating the boundedness both ways.
  have hkeyA : ∀ y : M, y ≠ q → ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ (∀ z ∈ V, z ≠ q) ∧
      ((BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)) →
        ∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z))) ∧
      (∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z)) →
        BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)))) := by
    intro y hy
    have hly : pathCoverProj p (lift y) ≠ q := by rw [hlift y]; exact hy
    obtain ⟨U, hUopen, hxU, hUne, hUcomp⟩ := hlocH (lift y) hly
    obtain ⟨e₁, hmem, heq, htgt, hch⟩ := hloc (lift y)
    have hytgt : y ∈ e₁.target := by
      have h1 := e₁.map_source hmem
      rwa [heq _ hmem, hlift y] at h1
    have hesymm_y : e₁.symm y = lift y := by
      have h1 : e₁ (lift y) = y := by rw [heq _ hmem, hlift y]
      have h2 := e₁.left_inv hmem
      rw [h1] at h2
      exact h2
    refine ⟨e₁.target ∩ e₁.symm ⁻¹' U,
      e₁.continuousOn_symm.isOpen_inter_preimage e₁.open_target hUopen,
      ⟨hytgt, by rw [Set.mem_preimage, hesymm_y]; exact hxU⟩, ?_, ?_, ?_⟩
    · intro z hz
      have h1 : pathCoverProj p (e₁.symm z) ≠ q := hUne _ hz.2
      have h2 : pathCoverProj p (e₁.symm z) = z := by
        rw [← heq _ (e₁.map_target hz.1)]
        exact e₁.right_inv hz.1
      rwa [h2] at h1
    · intro hb z hz
      obtain ⟨C, hC⟩ := hb
      have h2 : pathCoverProj p (e₁.symm z) = z := by
        rw [← heq _ (e₁.map_target hz.1)]
        exact e₁.right_inv hz.1
      have hbz : BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (e₁.symm z)) := by
        refine ⟨3 * C, ?_⟩
        rintro t ⟨F, rfl⟩
        have h3 := (hUcomp (e₁.symm z) hz.2 F).1
        have h4 : (∑ s ∈ F, greenEnvelope s.1 (lift y)) ≤ C :=
          hC (Set.mem_range_self F)
        linarith
      rw [hrange_fib (e₁.symm z) (lift z) (by rw [h2, hlift z])]
      exact hbz
    · intro z hz hb
      have h2 : pathCoverProj p (e₁.symm z) = z := by
        rw [← heq _ (e₁.map_target hz.1)]
        exact e₁.right_inv hz.1
      have hbz : BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (e₁.symm z)) := by
        rw [hrange_fib (lift z) (e₁.symm z) (by rw [h2, hlift z])]
        exact hb
      obtain ⟨C, hC⟩ := hbz
      refine ⟨3 * C, ?_⟩
      rintro t ⟨F, rfl⟩
      have h3 := (hUcomp (e₁.symm z) hz.2 F).2
      have h4 : (∑ s ∈ F, greenEnvelope s.1 (e₁.symm z)) ≤ C :=
        hC (Set.mem_range_self F)
      linarith
  have hkeyA' : ∀ y : M, ∃ V : Set M, y ≠ q → IsOpen V ∧ y ∈ V ∧ (∀ z ∈ V, z ≠ q) ∧
      ((BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)) →
        ∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z))) ∧
      (∀ z ∈ V, BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift z)) →
        BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y)))) := by
    intro y
    by_cases hy : y = q
    · exact ⟨∅, fun h => absurd hy h⟩
    · obtain ⟨V, hV⟩ := hkeyA y hy
      exact ⟨V, fun _ => hV⟩
  choose V hV using hkeyA'
  -- ## The boundedness locus is clopen in the punctured base, hence everything.
  have hopen₁ : IsOpen {y : M | y ≠ q ∧ BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift y))} := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hy, hb⟩
    obtain ⟨ho, hm, hne, hfwd, hbwd⟩ := hV y hy
    exact ⟨V y, fun z hz => ⟨hne z hz, hfwd hb z hz⟩, ho, hm⟩
  have hopen₂ : IsOpen {y : M | y ≠ q ∧ ¬ BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift y))} := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hy, hb⟩
    obtain ⟨ho, hm, hne, hfwd, hbwd⟩ := hV y hy
    exact ⟨V y, fun z hz => ⟨hne z hz, fun hbz => hb (hbwd z hz hbz)⟩, ho, hm⟩
  have hPall : ∀ y : M, y ≠ q → BddAbove (Set.range
      fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ s ∈ F, greenEnvelope s.1 (lift y)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₀, hz₀q, hz₀P⟩ := hcon
    have hconn : IsConnected ({q}ᶜ : Set M) :=
      isConnected_compl_singleton_of_connected ⟨p, q, hpq⟩ q
    have hcov : ({q}ᶜ : Set M) ⊆
        {y : M | y ≠ q ∧ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))} ∪
        {y : M | y ≠ q ∧ ¬ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))} := by
      intro y hy
      have hyq : y ≠ q := Set.mem_compl_singleton_iff.mp hy
      by_cases hb : BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))
      · exact Or.inl ⟨hyq, hb⟩
      · exact Or.inr ⟨hyq, hb⟩
    have hne₁ : (({q}ᶜ : Set M) ∩
        {y : M | y ≠ q ∧ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))}).Nonempty :=
      ⟨p, Set.mem_compl_singleton_iff.mpr hpq, hpq, hPp⟩
    have hne₂ : (({q}ᶜ : Set M) ∩
        {y : M | y ≠ q ∧ ¬ BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 (lift y))}).Nonempty :=
      ⟨z₀, Set.mem_compl_singleton_iff.mpr hz₀q, hz₀q, hz₀P⟩
    obtain ⟨w, -, ⟨-, hwb⟩, ⟨-, hwnb⟩⟩ :=
      hconn.2 _ _ hopen₁ hopen₂ hcov hne₁ hne₂
    exact hwnb hwb
  -- ## Boundedness of the `q`-fiber sums at every point off the fiber.
  have hSbdd_q : ∀ xc : PathCover p, pathCoverProj p xc ≠ q →
      BddAbove (Set.range
        fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
          ∑ s ∈ F, greenEnvelope s.1 xc) := by
    intro xc hxc
    have h1 := hPall (pathCoverProj p xc) hxc
    rw [hrange_fib (lift (pathCoverProj p xc)) xc (hlift (pathCoverProj p xc))]
    exact h1
  -- ## The deck sum is harmonic off the fiber.
  have hSharm : MHarmonicOn
      (fun xc => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 xc) (pathCoverProj p ⁻¹' {q})ᶜ := by
    have hdir : Directed (· ≤ ·)
        (fun (F : Finset {qc : PathCover p // pathCoverProj p qc = q})
          (xc : PathCover p) => ∑ s ∈ F, greenEnvelope s.1 xc) := by
      intro F₁ F₂
      refine ⟨F₁ ∪ F₂, fun xc => ?_, fun xc => ?_⟩
      · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          fun j _ _ => henvU j.1 xc
      · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          fun j _ _ => henvU j.1 xc
    have hbdd : ∀ xc ∈ (pathCoverProj p ⁻¹' {q})ᶜ,
        BddAbove (Set.range
          fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
            ∑ s ∈ F, greenEnvelope s.1 xc) := by
      intro xc hxc
      have hxcp : pathCoverProj p xc ≠ q := by
        simpa [Set.mem_preimage] using hxc
      exact hSbdd_q xc hxcp
    exact mharmonicOn_iSup_directed hΩopen huq hdir hbdd
  -- ## The descended deck sum: descent identity, nonnegativity, harmonicity.
  have hS_desc : ∀ yc : PathCover p,
      (⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift (pathCoverProj p yc))) =
      ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 yc := by
    intro yc
    exact congrArg sSup (hrange_fib yc (lift (pathCoverProj p yc)) (hlift _).symm)
  have hs_nonneg : ∀ z : M,
      (0 : ℝ) ≤ ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift z) :=
    fun z => Real.iSup_nonneg fun F => Finset.sum_nonneg fun j _ => henvU j.1 (lift z)
  have hs_harm : MHarmonicOn
      (fun z => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift z)) {q}ᶜ := by
    intro z hz
    have hzp : z ≠ q := hz
    have hlnf : lift z ∈ (pathCoverProj p ⁻¹' {q})ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hlift z]
      exact hzp
    have hSat := hSharm (lift z) hlnf
    have h2 := hdown_harm
      (fun xc => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 xc)
      (fun z' => ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift z'))
      (lift z) (fun yc => hS_desc yc) hSat
    rwa [hlift z] at h2
  -- ## The descended deck sum has the exact logarithmic pole at `q`.
  have hspole : ∃ C, ∀ᶠ y in 𝓝[≠] q,
      -Real.log ‖poleCoord q y‖ - C ≤
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift y) := by
    obtain ⟨e₂, hmem, heq, htgt, hch⟩ := hloc (lift q)
    obtain ⟨ρ, hρ, -, ht, htharm, hteq⟩ :=
      exists_harmonic_pole_extension (hGup (lift q))
    have htc : ContinuousAt ht (chartAt ℂ (lift q) (lift q)) :=
      (htharm _ (mem_ball_self hρ)).1.continuousAt
    set B : ℝ := |ht (chartAt ℂ (lift q) (lift q))| + 1 with hBdef
    have hB : ∀ᶠ w in 𝓝 (chartAt ℂ (lift q) (lift q)), |ht w| ≤ B := by
      have h1 := htc (Metric.ball_mem_nhds (ht (chartAt ℂ (lift q) (lift q))) one_pos)
      filter_upwards [h1] with w hw
      have h2 : |ht w - ht (chartAt ℂ (lift q) (lift q))| < 1 := by
        simpa [Real.dist_eq] using hw
      have h3 := abs_sub_abs_le_abs_sub (ht w) (ht (chartAt ℂ (lift q) (lift q)))
      rw [hBdef]
      linarith
    have hqtgt : q ∈ e₂.target := by
      have h1 := e₂.map_source hmem
      rwa [heq _ hmem, hlift q] at h1
    have hesymm_cont : ContinuousAt e₂.symm q := e₂.continuousAt_symm hqtgt
    have hesymm_val : e₂.symm q = lift q := by
      have h1 : e₂ (lift q) = q := by rw [heq _ hmem, hlift q]
      have h2 := e₂.left_inv hmem
      rw [h1] at h2
      exact h2
    have hev_sec : ∀ᶠ y in 𝓝[≠] q,
        e₂.symm y ∈ (chartAt ℂ (lift q)).source ∧
        chartAt ℂ (lift q) (e₂.symm y) ∈ ball (chartAt ℂ (lift q) (lift q)) ρ ∧
        |ht (chartAt ℂ (lift q) (e₂.symm y))| ≤ B := by
      have h1 : ∀ᶠ y in 𝓝 q, e₂.symm y ∈ (chartAt ℂ (lift q)).source := by
        refine hesymm_cont.eventually_mem ?_
        rw [hesymm_val]
        exact (chartAt ℂ (lift q)).open_source.mem_nhds (mem_chart_source ℂ (lift q))
      have hcc : ContinuousAt (chartAt ℂ (lift q)) (e₂.symm q) := by
        rw [hesymm_val]
        exact (chartAt ℂ (lift q)).continuousAt (mem_chart_source ℂ (lift q))
      have h2 : ContinuousAt (fun y => chartAt ℂ (lift q) (e₂.symm y)) q :=
        hcc.comp hesymm_cont
      have h3 : ∀ᶠ w in 𝓝 (chartAt ℂ (lift q) (e₂.symm q)),
          w ∈ ball (chartAt ℂ (lift q) (lift q)) ρ ∧ |ht w| ≤ B := by
        rw [hesymm_val]
        exact (isOpen_ball.eventually_mem (mem_ball_self hρ)).and hB
      have h4 := h2.eventually_mem h3
      exact nhdsWithin_le_nhds (h1.and h4)
    have hev_tgt : ∀ᶠ y in 𝓝[≠] q, y ∈ e₂.target :=
      nhdsWithin_le_nhds (e₂.open_target.mem_nhds hqtgt)
    have hev_src₀ : ∀ᶠ y in 𝓝[≠] q, y ∈ (chartAt ℂ q).source :=
      nhdsWithin_le_nhds
        ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q))
    refine ⟨B, ?_⟩
    filter_upwards [hev_sec, hev_tgt, hev_src₀, self_mem_nhdsWithin]
      with y hsec hbt hsrc₀ hyne'
    have hyne : y ≠ q := hyne'
    have hxs : e₂.symm y ∈ e₂.source := e₂.map_target hbt
    have hprojxy : pathCoverProj p (e₂.symm y) = y := by
      rw [← heq _ hxs]
      exact e₂.right_inv hbt
    have hpc_ne : poleCoord q y ≠ 0 := by
      intro hcon
      apply hyne
      refine (chartAt ℂ q).injOn hsrc₀ (mem_chart_source ℂ q) ?_
      have h6 : chartAt ℂ q y - chartAt ℂ q q = 0 := hcon
      linear_combination (norm := module) h6
    have hpc_eq : poleCoord (lift q) (e₂.symm y) = poleCoord q y := by
      have h1 := hpolecoord (lift q) (e₂.symm y) hsec.1
      rw [hlift q, hprojxy] at h1
      exact h1
    have hne_ctr : chartAt ℂ (lift q) (e₂.symm y) ≠ chartAt ℂ (lift q) (lift q) := by
      intro hcon
      apply hpc_ne
      rw [← hpc_eq]
      have h7 : poleCoord (lift q) (e₂.symm y) =
          chartAt ℂ (lift q) (e₂.symm y) - chartAt ℂ (lift q) (lift q) := rfl
      rw [h7, hcon, sub_self]
    have hmem3 : chartAt ℂ (lift q) (e₂.symm y) ∈
        ball (chartAt ℂ (lift q) (lift q)) ρ \ {chartAt ℂ (lift q) (lift q)} :=
      ⟨hsec.2.1, hne_ctr⟩
    have h8 := hteq _ hmem3
    rw [(chartAt ℂ (lift q)).left_inv hsec.1] at h8
    have h9 : Real.log ‖chartAt ℂ (lift q) (e₂.symm y) -
        chartAt ℂ (lift q) (lift q)‖ = Real.log ‖poleCoord q y‖ := by
      have h10 : chartAt ℂ (lift q) (e₂.symm y) - chartAt ℂ (lift q) (lift q) =
          poleCoord (lift q) (e₂.symm y) := rfl
      rw [h10, hpc_eq]
    rw [h9] at h8
    have hhead : greenEnvelope (lift q) (e₂.symm y) =
        ht (chartAt ℂ (lift q) (e₂.symm y)) - Real.log ‖poleCoord q y‖ := by
      linarith [h8]
    have hband := (abs_le.mp hsec.2.2).1
    have hsingle : greenEnvelope (lift q) (e₂.symm y) ≤
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (e₂.symm y) := by
      have hb1 : pathCoverProj p (e₂.symm y) ≠ q := by
        rw [hprojxy]
        exact hyne
      have hb2 := le_ciSup (hSbdd_q (e₂.symm y) hb1)
        ({⟨lift q, hlift q⟩} : Finset {qc : PathCover p // pathCoverProj p qc = q})
      rw [Finset.sum_singleton] at hb2
      exact hb2
    have hdesc := hS_desc (e₂.symm y)
    rw [hprojxy] at hdesc
    rw [hdesc]
    rw [hhead] at hsingle
    linarith
  -- ## Every candidate downstairs at `q` is dominated by the descended sum.
  have hpart2q : ∀ y : M, y ≠ q → ∀ v ∈ greenFamily q, v y ≤
      ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ s ∈ F, greenEnvelope s.1 (lift y) := by
    intro y hy v hv
    obtain ⟨hvsub, hvcont, ⟨Kv, hKvc, -, hKvz⟩, Cv, hCv⟩ := hv
    have hwsub : MSubharmonicOn (fun z => v z -
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift z)) {q}ᶜ :=
      fun z hz => (hvsub z hz).sub_mharmonicAt (hs_harm z hz)
    have hsupp2 : ∃ K : Set M, IsCompact K ∧ ∀ z ∉ K, (v z -
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift z)) ≤ 0 := by
      refine ⟨Kv ∪ {q}, hKvc.union isCompact_singleton, fun z hz => ?_⟩
      have h1 : v z = 0 := hKvz z fun h => hz (Set.mem_union_left _ h)
      have h2 := hs_nonneg z
      rw [h1]
      linarith
    have hpole2 : ∃ C, ∀ᶠ z in 𝓝[≠] q, (v z -
        ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
          ∑ s ∈ F, greenEnvelope s.1 (lift z)) ≤ C := by
      obtain ⟨C₁, hC₁⟩ := hspole
      refine ⟨Cv + C₁, ?_⟩
      filter_upwards [hCv, hC₁] with z h1 h2
      linarith
    have h3 := msubharmonic_le_zero_of_puncture hwsub hsupp2 hpole2 y hy
    linarith
  -- ## Assembly: the family at `q` is bounded above at the witness `p`.
  refine ⟨p, hpq, ⟨⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
    ∑ s ∈ F, greenEnvelope s.1 (lift p), ?_⟩⟩
  rintro t ⟨v, hv, rfl⟩
  exact hpart2q p hpq v hv

/-- **Symmetry of the Green's function**: on a connected hyperbolic surface
the Green's envelope is symmetric in the pole and the evaluation point. The
deck-sum formula reduces the identity to the simply connected cover, where it
holds by the Riemann map and the disc kernel, and the deck action reindexes
the two fiber sums into one another. -/
theorem greenEnvelope_symm [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p q : M} (hG : HasGreenFunction p) (hpq : p ≠ q) :
    greenEnvelope p q = greenEnvelope q p := by
  classical
  -- ## A path from `p` to `q` downstairs, and the two distinguished lifts.
  haveI : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace ℂ M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  obtain ⟨sp⟩ := PathConnectedSpace.joined p q
  obtain ⟨pb, hpb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = p :=
    ⟨pathCoverBase p, rfl⟩
  obtain ⟨qb, hqb_proj⟩ : ∃ pc : PathCover p, pathCoverProj p pc = q :=
    ⟨⟨q, ⟦sp⟧⟩, rfl⟩
  -- ## Topology of the universal path cover.
  haveI : PathConnectedSpace (PathCover p) := pathConnectedSpace_pathCover p
  haveI : SimplyConnectedSpace (PathCover p) := simplyConnectedSpace_pathCover p
  haveI : T2Space (PathCover p) := t2space_pathCover p
  haveI : NoncompactSpace (PathCover p) := noncompactSpace_pathCover p
  -- ## Green's functions upstairs: at the base lift, hence everywhere.
  have hGpb : HasGreenFunction pb := hasGreenFunction_pathCover p hG hpb_proj
  have hGall : ∀ rc : PathCover p, HasGreenFunction rc := fun rc =>
    hasGreenFunction_of_simplyConnected hGpb
  -- ## Groupoid algebra of the deck action.
  have hdeck_comp : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ (pathCoverDeck p δ pc) = pathCoverDeck p (γ.trans δ) pc := by
    intro γ δ pc
    change (⟨pc.pt, γ.trans (δ.trans pc.cls)⟩ : PathCover p)
      = ⟨pc.pt, (γ.trans δ).trans pc.cls⟩
    exact congrArg (PathCover.mk pc.pt)
      (Path.Homotopic.Quotient.trans_assoc γ δ pc.cls).symm
  have hdeck_refl : ∀ pc : PathCover p,
      pathCoverDeck p (Path.Homotopic.Quotient.refl p) pc = pc := by
    intro pc
    change (⟨pc.pt, (Path.Homotopic.Quotient.refl p).trans pc.cls⟩ : PathCover p) = pc
    exact congrArg (PathCover.mk pc.pt) (Path.Homotopic.Quotient.refl_trans pc.cls)
  have hdeck_free : ∀ (δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p δ pc = pc → δ = Path.Homotopic.Quotient.refl p := by
    intro δ pc h
    have h' : (⟨pc.pt, δ.trans pc.cls⟩ : PathCover p) = ⟨pc.pt, pc.cls⟩ := h
    rw [PathCover.mk.injEq] at h'
    have h1 : δ.trans pc.cls = pc.cls := eq_of_heq h'.2
    calc δ = δ.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl δ).symm
      _ = δ.trans (pc.cls.trans pc.cls.symm) := by
          rw [Path.Homotopic.Quotient.trans_symm]
      _ = (δ.trans pc.cls).trans pc.cls.symm :=
          (Path.Homotopic.Quotient.trans_assoc δ pc.cls pc.cls.symm).symm
      _ = pc.cls.trans pc.cls.symm := by rw [h1]
      _ = Path.Homotopic.Quotient.refl p := Path.Homotopic.Quotient.trans_symm pc.cls
  have hdeck_inj : ∀ (γ δ : Path.Homotopic.Quotient p p) (pc : PathCover p),
      pathCoverDeck p γ pc = pathCoverDeck p δ pc → γ = δ := by
    intro γ δ pc h
    have h2 : pathCoverDeck p (δ.symm.trans γ) pc = pc := by
      rw [← hdeck_comp, h, hdeck_comp, Path.Homotopic.Quotient.symm_trans, hdeck_refl]
    have h3 := hdeck_free _ _ h2
    calc γ = (Path.Homotopic.Quotient.refl p).trans γ :=
          (Path.Homotopic.Quotient.refl_trans γ).symm
      _ = (δ.trans δ.symm).trans γ := by rw [Path.Homotopic.Quotient.trans_symm]
      _ = δ.trans (δ.symm.trans γ) := Path.Homotopic.Quotient.trans_assoc δ δ.symm γ
      _ = δ.trans (Path.Homotopic.Quotient.refl p) := by rw [h3]
      _ = δ := Path.Homotopic.Quotient.trans_refl δ
  have hsymm_symm : ∀ γ : Path.Homotopic.Quotient p p, γ.symm.symm = γ := by
    intro γ
    calc γ.symm.symm = γ.symm.symm.trans (Path.Homotopic.Quotient.refl p) :=
          (Path.Homotopic.Quotient.trans_refl γ.symm.symm).symm
      _ = γ.symm.symm.trans (γ.symm.trans γ) := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = (γ.symm.symm.trans γ.symm).trans γ :=
          (Path.Homotopic.Quotient.trans_assoc γ.symm.symm γ.symm γ).symm
      _ = (Path.Homotopic.Quotient.refl p).trans γ := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = γ := Path.Homotopic.Quotient.refl_trans γ
  -- ## Choices: fiber loops and deck diffeomorphisms.
  have hfibA : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      ∃ γ : Path.Homotopic.Quotient p p, pathCoverDeck p γ pb = a.1 := fun a =>
    pathCoverDeck_transitive p pb a.1 (hpb_proj.trans a.2.symm)
  choose γfn hγfn using hfibA
  choose Efn hEfn using fun γ : Path.Homotopic.Quotient p p =>
    exists_pathCoverDeck_diffeomorph p γ
  -- ## The fiber reindexing map: conjugate `p`-fiber points into the `q`-fiber.
  obtain ⟨Φ, hΦspec⟩ : ∃ Φ : {qc : PathCover p // pathCoverProj p qc = p} →
      {qc : PathCover p // pathCoverProj p qc = q},
      ∀ a, (Φ a).1 = pathCoverDeck p (γfn a).symm qb :=
    ⟨fun a => ⟨pathCoverDeck p (γfn a).symm qb,
      (pathCoverProj_deck p (γfn a).symm qb).trans hqb_proj⟩, fun _ => rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro a₁ a₂ h
    have h1 : pathCoverDeck p (γfn a₁).symm qb = pathCoverDeck p (γfn a₂).symm qb := by
      rw [← hΦspec a₁, ← hΦspec a₂, h]
    have h2 : (γfn a₁).symm = (γfn a₂).symm := hdeck_inj _ _ _ h1
    have h3 : γfn a₁ = γfn a₂ := by
      rw [← hsymm_symm (γfn a₁), h2, hsymm_symm]
    apply Subtype.ext
    rw [← hγfn a₁, ← hγfn a₂, h3]
  have hΦsurj : Function.Surjective Φ := by
    intro b
    obtain ⟨δ, hδ⟩ := pathCoverDeck_transitive p qb b.1 (hqb_proj.trans b.2.symm)
    have hmem : pathCoverProj p (pathCoverDeck p δ.symm pb) = p :=
      (pathCoverProj_deck p δ.symm pb).trans hpb_proj
    refine ⟨⟨pathCoverDeck p δ.symm pb, hmem⟩, ?_⟩
    have hloop : γfn ⟨pathCoverDeck p δ.symm pb, hmem⟩ = δ.symm := by
      apply hdeck_inj _ _ pb
      exact hγfn ⟨pathCoverDeck p δ.symm pb, hmem⟩
    apply Subtype.ext
    rw [hΦspec, hloop, hsymm_symm, hδ]
  obtain ⟨e, he⟩ : ∃ e : {qc : PathCover p // pathCoverProj p qc = p} ≃
      {qc : PathCover p // pathCoverProj p qc = q}, ∀ a, e a = Φ a :=
    ⟨Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩, fun _ => rfl⟩
  -- ## Termwise symmetry: cover symmetry plus conformal invariance of the deck maps.
  have hterm : ∀ a : {qc : PathCover p // pathCoverProj p qc = p},
      greenEnvelope a.1 qb = greenEnvelope (pathCoverDeck p (γfn a).symm qb) pb := by
    intro a
    have hne : a.1 ≠ qb := by
      intro h
      apply hpq
      rw [← a.2, h, hqb_proj]
    have h1 : greenEnvelope a.1 qb = greenEnvelope qb a.1 :=
      greenEnvelope_symm_of_simplyConnected (hGall a.1) hne
    have hEpb : Efn (γfn a) pb = a.1 := (hEfn (γfn a) pb).trans (hγfn a)
    have hEsymm_a : (Efn (γfn a)).symm a.1 = pb := by
      rw [← hEpb, Diffeomorph.symm_apply_apply]
    have h2 : Efn (γfn a) (pathCoverDeck p (γfn a).symm qb) = qb := by
      rw [hEfn (γfn a) (pathCoverDeck p (γfn a).symm qb), hdeck_comp,
        Path.Homotopic.Quotient.trans_symm, hdeck_refl]
    have hEsymm_q : (Efn (γfn a)).symm qb = pathCoverDeck p (γfn a).symm qb := by
      calc (Efn (γfn a)).symm qb
          = (Efn (γfn a)).symm (Efn (γfn a) (pathCoverDeck p (γfn a).symm qb)) := by
            rw [h2]
        _ = pathCoverDeck p (γfn a).symm qb := Diffeomorph.symm_apply_apply _ _
    have h3 : greenEnvelope ((Efn (γfn a)).symm qb) ((Efn (γfn a)).symm a.1)
        = greenEnvelope qb a.1 :=
      greenEnvelope_comp_diffeomorph (Efn (γfn a)).symm qb a.1
    rw [h1, ← h3, hEsymm_a, hEsymm_q]
  -- ## The two deck-sum expansions and the reindexing of the fiber sums.
  have hne1 : pathCoverProj p qb ≠ p := by rw [hqb_proj]; exact Ne.symm hpq
  have hne2 : pathCoverProj p pb ≠ q := by rw [hpb_proj]; exact hpq
  have h1 := (greenEnvelope_deckSum p (p₀ := p) (pc := qb) hG hne1 ⟨pb, hpb_proj, hGpb⟩).2
  have hGq : HasGreenFunction q := hasGreenFunction_of_hasGreenFunction hG
  have h2 := (greenEnvelope_deckSum p (p₀ := q) (pc := pb) hGq hne2 ⟨qb, hqb_proj, hGall qb⟩).2
  rw [hqb_proj] at h1
  rw [hpb_proj] at h2
  have hFeq : ∀ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
      (∑ qc ∈ F, greenEnvelope qc.1 qb)
        = ∑ qc ∈ e.finsetCongr F, greenEnvelope qc.1 pb := by
    intro F
    rw [Equiv.finsetCongr_apply, Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [he a, hΦspec a]
    exact hterm a
  have hstep1 : (⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
        ∑ qc ∈ F, greenEnvelope qc.1 qb)
      = ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
        ∑ qc ∈ e.finsetCongr F, greenEnvelope qc.1 pb := iSup_congr hFeq
  have hstep2 : (⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = p},
        ∑ qc ∈ e.finsetCongr F, greenEnvelope qc.1 pb)
      = ⨆ F : Finset {qc : PathCover p // pathCoverProj p qc = q},
        ∑ qc ∈ F, greenEnvelope qc.1 pb :=
    Equiv.iSup_comp
      (g := fun F : Finset {qc : PathCover p // pathCoverProj p qc = q} =>
        ∑ qc ∈ F, greenEnvelope qc.1 pb) e.finsetCongr
  exact h1.trans ((hstep1.trans hstep2).trans h2.symm)

end RiemannDynamics

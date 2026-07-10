import RiemannDynamics.Uniformization.Perron.PathCover
import RiemannDynamics.Uniformization.Perron.GreenSymmetry

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
open scoped Manifold ContDiff

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
  sorry

/-- **The deck-sum formula**: the Green's envelope of the base at a pole is
the supremum of the finite fiber sums of the Green's envelopes of the
universal path cover, evaluated at any lift; in particular the base is
hyperbolic at the pole as soon as the cover is hyperbolic at one of its
lifts. -/
theorem greenEnvelope_deckSum [T2Space M] [ConnectedSpace M]
    [NoncompactSpace M] (x₀ : M) {p₀ : M} {pc : PathCover x₀}
    (hne : pathCoverProj x₀ pc ≠ p₀)
    (hfib : ∃ qc₀ : PathCover x₀, pathCoverProj x₀ qc₀ = p₀ ∧
      HasGreenFunction qc₀) :
    HasGreenFunction p₀ ∧
      greenEnvelope p₀ (pathCoverProj x₀ pc) =
        ⨆ F : Finset {qc : PathCover x₀ // pathCoverProj x₀ qc = p₀},
          ∑ qc ∈ F, greenEnvelope qc.1 pc := by
  sorry

/-- **Symmetry of the Green's function**: on a connected hyperbolic surface
the Green's envelope is symmetric in the pole and the evaluation point. The
deck-sum formula reduces the identity to the simply connected cover, where it
holds by the Riemann map and the disc kernel, and the deck action reindexes
the two fiber sums into one another. -/
theorem greenEnvelope_symm [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p q : M} (hG : HasGreenFunction p) (hpq : p ≠ q) :
    greenEnvelope p q = greenEnvelope q p := by
  sorry

end RiemannDynamics

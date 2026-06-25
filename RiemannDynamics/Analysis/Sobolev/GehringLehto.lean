/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import RiemannDynamics.Analysis.Sobolev.Stepanov
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import RiemannDynamics.Analysis.SingularIntegral.GehringHigherIntegrability.Sobolev

/-!
# The Gehring–Lehto a.e.-differentiability pivot (part ii): W^{1,2}_loc + homeomorphism ⟹ a.e. diff

This file builds the **roundness-free** route to almost-everywhere differentiability of a planar
homeomorphism `f : ℂ → ℂ` whose distributional gradient is locally square-integrable. It is the
classical Gehring–Lehto theorem (a homeomorphism in `W^{1,2}_loc` is differentiable almost
everywhere), proved at the critical exponent `p = 2` via the Courant–Lebesgue oscillation lemma and
monotonicity, feeding the project's proven Stepanov engine
`RiemannDynamics.Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top`.

Crucially this route reaches a.e. differentiability **directly** from the finite metric upper
derivative, so it does not use the conformal-modulus *roundness* estimate
`qc_image_ball_diam_sq_le_volume` (and hence not the Grötzsch/Teichmüller two-point-distortion
cluster). The leaves here take `W^{1,2}_loc` as a *hypothesis*, so they are independent of the
forward length–area energy inequality that supplies that hypothesis for a geometric quasiconformal
map.

## Leaves (part ii)

* `diam_image_closedBall_le_diam_image_sphere` (**MON**, this file) — for a homeomorphism the image
  of a closed ball has diameter at most that of the image of the bounding sphere. The monotonicity
  step: the oscillation of `f` over a disc is attained on its boundary circle.
-/

open Metric Set MeasureTheory Filter
open scoped Topology ENNReal NNReal Pointwise

namespace RiemannDynamics.GehringLehto

/-- The Dirichlet energy density `‖gx‖² + ‖gy‖²` of a weak gradient `(gx, gy)`, valued in `ℝ≥0∞`. -/
noncomputable def energyDensity (gx gy : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  (‖gx z‖₊ : ℝ≥0∞) ^ 2 + (‖gy z‖₊ : ℝ≥0∞) ^ 2

/-- **Monotonicity of the image oscillation (MON).**

For a homeomorphism `f : ℂ → ℂ`, the diameter of the image of a closed ball is at most the diameter
of the image of its bounding sphere:
`Metric.diam (f '' Metric.closedBall x ρ) ≤ Metric.diam (f '' Metric.sphere x ρ)`.

This is the planar "maximum principle for the oscillation" of a monotone (homeomorphic) map: the
extreme values of `f` over a disc are taken on the boundary circle. The image sphere is the frontier
of the image ball (`f '' sphere = frontier (f '' closedBall)`, since `f` is a homeomorphism and the
sphere is the frontier of the closed ball in `ℂ`), and the diameter of a compact set in a normed
space is realized between two of its frontier points (extend the realizing segment in both
directions to the last point of the compact set on each ray; those extreme points lie on the
frontier and are at least as far apart).

It depends only on `IsHomeomorph f` — no Sobolev regularity, no differentiability, no quasiconformal
hypothesis — and is exactly the monotonicity input the Courant–Lebesgue assembly needs. -/
theorem diam_image_closedBall_le_diam_image_sphere {f : ℂ → ℂ} (hf : IsHomeomorph f) (x : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Metric.diam (f '' Metric.closedBall x ρ) ≤ Metric.diam (f '' Metric.sphere x ρ) := by
  classical
  -- Notation for the image of the closed ball.
  set S : Set ℂ := f '' Metric.closedBall x ρ with hS_def
  -- `closedBall x ρ` is compact (`ℂ` is a proper space), so `S` is the continuous image of a
  -- compact set and hence compact, bounded and closed.
  have hball_cpt : IsCompact (Metric.closedBall x ρ) := isCompact_closedBall x ρ
  have hScompact : IsCompact S := hball_cpt.image hf.continuous
  have hSbounded : Bornology.IsBounded S := hScompact.isBounded
  have hSclosed : IsClosed S := hScompact.isClosed
  -- The closed ball is nonempty (it contains its center), hence so is `S`.
  have hxmem : x ∈ Metric.closedBall x ρ := by
    simp [Metric.mem_closedBall, hρ.le]
  have hSne : S.Nonempty := ⟨f x, x, hxmem, rfl⟩
  -- Identify the image sphere with the frontier of `S`.
  have himg_frontier : f '' Metric.sphere x ρ = frontier S := by
    have hcoe : (hf.homeomorph f) '' frontier (Metric.closedBall x ρ)
        = frontier ((hf.homeomorph f) '' Metric.closedBall x ρ) :=
      (hf.homeomorph f).image_frontier (Metric.closedBall x ρ)
    -- Rewrite the coercion `⇑(hf.homeomorph f)` to `f` and the frontier of the ball to the sphere.
    have hcoe' : f '' frontier (Metric.closedBall x ρ) = frontier (f '' Metric.closedBall x ρ) := by
      have e1 : (hf.homeomorph f) '' frontier (Metric.closedBall x ρ)
          = f '' frontier (Metric.closedBall x ρ) := by
        apply Set.image_congr'
        intro z; rfl
      have e2 : (hf.homeomorph f) '' Metric.closedBall x ρ = f '' Metric.closedBall x ρ := by
        apply Set.image_congr'
        intro z; rfl
      rw [e1, e2] at hcoe
      exact hcoe
    rw [frontier_closedBall' x ρ] at hcoe'
    rw [hcoe', hS_def]
  -- The frontier of `S` is bounded (it is the compact image of the compact sphere).
  have hsphere_cpt : IsCompact (Metric.sphere x ρ) :=
    (isCompact_closedBall x ρ).of_isClosed_subset Metric.isClosed_sphere
      Metric.sphere_subset_closedBall
  have hfrontier_cpt : IsCompact (frontier S) := by
    rw [← himg_frontier]; exact hsphere_cpt.image hf.continuous
  have hfrontier_bdd : Bornology.IsBounded (frontier S) := hfrontier_cpt.isBounded
  -- The diameter of `S` is attained by a pair of points `a₀, b₀ ∈ S`.
  have hprod_cpt : IsCompact (S ×ˢ S) := hScompact.prod hScompact
  have hprod_ne : (S ×ˢ S).Nonempty := hSne.prod hSne
  have hdist_cont : ContinuousOn (fun p : ℂ × ℂ => dist p.1 p.2) (S ×ˢ S) :=
    (continuous_fst.dist continuous_snd).continuousOn
  obtain ⟨p₀, hp₀mem, hp₀max⟩ := hprod_cpt.exists_isMaxOn hprod_ne hdist_cont
  obtain ⟨ha₀mem, hb₀mem⟩ := Set.mem_prod.mp hp₀mem
  set a₀ : ℂ := p₀.1 with ha₀_def
  set b₀ : ℂ := p₀.2 with hb₀_def
  set M : ℝ := dist a₀ b₀ with hM_def
  -- `M` is the maximum of the distance over `S × S`.
  have hMmax : ∀ a ∈ S, ∀ b ∈ S, dist a b ≤ M := by
    intro a ha b hb
    have : dist (a, b).1 (a, b).2 ≤ dist p₀.1 p₀.2 :=
      hp₀max (Set.mem_prod.mpr ⟨ha, hb⟩)
    simpa [ha₀_def, hb₀_def, hM_def] using this
  -- `M = diam S`.
  have hM_nonneg : 0 ≤ M := dist_nonneg
  have hdiam_le_M : Metric.diam S ≤ M := Metric.diam_le_of_forall_dist_le hM_nonneg hMmax
  have hM_le_diam : M ≤ Metric.diam S := Metric.dist_le_diam_of_mem hSbounded ha₀mem hb₀mem
  have hdiam_eq : Metric.diam S = M := le_antisymm hdiam_le_M hM_le_diam
  -- `S` has at least two points, so its diameter is positive.
  have hMpos : 0 < M := by
    -- Two distinct points in the ball map to two distinct points in `S`.
    have hx2 : x + (ρ / 2 : ℝ) ∈ Metric.closedBall x ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub : x + (ρ / 2 : ℝ) - x = ((ρ / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    have hne_pts : x ≠ x + (ρ / 2 : ℝ) := by
      intro h
      have h2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
        have hh : x + ((ρ / 2 : ℝ) : ℂ) = x + 0 := by rw [add_zero]; exact h.symm
        exact add_left_cancel hh
      rw [Complex.ofReal_eq_zero] at h2
      linarith
    have hfne : f x ≠ f (x + (ρ / 2 : ℝ)) := fun h => hne_pts (hf.injective h)
    have hfx_mem : f x ∈ S := ⟨x, hxmem, rfl⟩
    have hfx2_mem : f (x + (ρ / 2 : ℝ)) ∈ S := ⟨x + (ρ / 2 : ℝ), hx2, rfl⟩
    have hdist_pos : 0 < dist (f x) (f (x + (ρ / 2 : ℝ))) := dist_pos.mpr hfne
    have : dist (f x) (f (x + (ρ / 2 : ℝ))) ≤ M := hMmax _ hfx_mem _ hfx2_mem
    linarith
  -- `a₀ ≠ b₀` since `M = dist a₀ b₀ > 0`.
  have hab_ne : a₀ ≠ b₀ := by
    intro h
    rw [hM_def, h, dist_self] at hMpos
    exact lt_irrefl 0 hMpos
  -- The frontier equals `S \ interior S` (as `S` is closed).
  have hfrontier_eq : frontier S = S \ interior S := hSclosed.frontier_eq
  -- A point that maximizes the distance to some other point of `S` cannot lie in the interior.
  -- General claim: for `u, v ∈ S` with `u ≠ v` and `dist u v = M`, `u ∈ frontier S`.
  have key : ∀ u v : ℂ, u ∈ S → v ∈ S → u ≠ v → dist u v = M → u ∈ frontier S := by
    intro u v hu hv huv hdistuv
    rw [hfrontier_eq]
    refine ⟨hu, ?_⟩
    intro hu_int
    -- From `u ∈ interior S` get a ball `ball u r ⊆ S` with `r > 0`.
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hu_int
    obtain ⟨r, hr_pos, hr_sub⟩ := hu_int
    -- The vector `w := u - v` points from `v` to `u`; it is nonzero.
    set w : ℂ := u - v with hw_def
    have hw_ne : w ≠ 0 := sub_ne_zero.mpr huv
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    -- Push `u` a little further from `v` along the ray through `w`, by `r/2`.  We write everything
    -- with complex multiplication (`(t : ℝ) • z = (↑t) * z`) to dodge the missing `NormSMulClass`.
    set p : ℂ := u + ((r / 2 : ℝ) : ℂ) * (((‖w‖⁻¹ : ℝ) : ℂ) * w) with hp_def
    -- `dist p u = r/2 < r`, so `p ∈ ball u r ⊆ S`.
    have hdist_pu : dist p u = r / 2 := by
      rw [hp_def, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ r / 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖⁻¹)]
      field_simp
    have hp_in_ball : p ∈ Metric.ball u r := by
      rw [Metric.mem_ball, hdist_pu]; linarith
    have hp_in_S : p ∈ S := hr_sub hp_in_ball
    -- Now `p - v = (1 + (r/2)/‖w‖) * w`, a positive real multiple of `w = u - v`.
    have hpv_eq : p - v = ((1 + (r / 2 : ℝ) / ‖w‖ : ℝ) : ℂ) * w := by
      rw [hp_def, hw_def]; push_cast; field_simp; ring
    have hcoef_pos : (0 : ℝ) ≤ 1 + (r / 2 : ℝ) / ‖w‖ := by positivity
    have hdist_pv : dist p v = ‖w‖ + r / 2 := by
      rw [dist_eq_norm, hpv_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hcoef_pos, add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hw_norm_pos)]
    -- But `dist u v = ‖w‖ = M`, so `dist p v = M + r/2 > M`, contradicting `p, v ∈ S`.
    have hw_norm_eq_M : ‖w‖ = M := by rw [hw_def, ← dist_eq_norm, ← hdistuv]
    have hcontra : dist p v ≤ M := hMmax p hp_in_S v hv
    rw [hdist_pv, hw_norm_eq_M] at hcontra
    linarith
  -- Both `a₀` and `b₀` lie on the frontier.
  have ha₀_front : a₀ ∈ frontier S := key a₀ b₀ ha₀mem hb₀mem hab_ne rfl
  have hb₀_front : b₀ ∈ frontier S := key b₀ a₀ hb₀mem ha₀mem hab_ne.symm (by rw [dist_comm])
  -- Conclude:  diam S = M = dist a₀ b₀ ≤ diam (frontier S) = diam (f '' sphere x ρ).
  rw [hdiam_eq, himg_frontier]
  calc M = dist a₀ b₀ := rfl
    _ ≤ Metric.diam (frontier S) := Metric.dist_le_diam_of_mem hfrontier_bdd ha₀_front hb₀_front

/-- **Energy-density Lebesgue points (ED).**

For weak partials `gx, gy ∈ L²_loc`, the Dirichlet energy density `φ = ‖gx‖² + ‖gy‖²` is locally
integrable, so almost every point is a Lebesgue point of `φ`; equivalently, for a.e. `x` the energy
of a small disc of radius `2s` is `O(s²)` as `s → 0⁺` (the area scale), with a finite constant
`A` depending on `x`. This is the measure-theoretic input that converts the Courant–Lebesgue energy
bound into a genuine `O(1)` metric-derivative bound.

Proof: `gx, gy ∈ L²_loc ⟹ φ ∈ L¹_loc`; apply Lebesgue differentiation (the Besicovitch/Vitali family
of closed balls, `VitaliFamily.ae_tendsto_lintegral_div`) to get `(∫_{B(x,2s)} φ)/vol(B(x,2s)) → φ x
< ∞` a.e.; since `vol(B(x,2s)) = π(2s)² = 4π s²`, conclude `∫_{B(x,2s)} φ ≤ A·s²` for small `s` with
`A = (φ x).toReal·4π + 1` (say). -/
theorem ae_energyDensity_lebesgue_point {gx gy : ℂ → ℂ}
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∀ᵐ x : ℂ, ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      (∫⁻ z in Metric.closedBall x (2 * s), energyDensity gx gy z)
        ≤ ENNReal.ofReal (A * s ^ 2) := by
  classical
  set φ : ℂ → ℝ≥0∞ := energyDensity gx gy with hφ_def
  -- Step 1. The components `gx, gy` are globally `AEMeasurable` (patch the compact pieces of the
  -- σ-compact cover of `ℂ`), hence so is the energy density `φ`.
  have hgx_aem : AEMeasurable gx volume := by
    have hcover : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := iUnion_closedBall_nat 0
    have h : AEMeasurable gx (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) := by
      refine AEMeasurable.iUnion (fun n => ?_)
      exact ((hgx (Metric.closedBall 0 n) (Set.subset_univ _)
        (isCompact_closedBall 0 n)).aestronglyMeasurable).aemeasurable
    rwa [hcover, Measure.restrict_univ] at h
  have hgy_aem : AEMeasurable gy volume := by
    have hcover : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := iUnion_closedBall_nat 0
    have h : AEMeasurable gy (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) := by
      refine AEMeasurable.iUnion (fun n => ?_)
      exact ((hgy (Metric.closedBall 0 n) (Set.subset_univ _)
        (isCompact_closedBall 0 n)).aestronglyMeasurable).aemeasurable
    rwa [hcover, Measure.restrict_univ] at h
  have hgx_sq_aem : AEMeasurable (fun z => (‖gx z‖₊ : ℝ≥0∞) ^ 2) volume :=
    (hgx_aem.enorm.pow_const 2).congr (by filter_upwards with z using by rw [enorm_eq_nnnorm])
  have hgy_sq_aem : AEMeasurable (fun z => (‖gy z‖₊ : ℝ≥0∞) ^ 2) volume :=
    (hgy_aem.enorm.pow_const 2).congr (by filter_upwards with z using by rw [enorm_eq_nnnorm])
  have hφ_aem : AEMeasurable φ volume := by
    rw [hφ_def]; exact hgx_sq_aem.add hgy_sq_aem
  -- Step 2. `∫⁻_K φ < ∞` for every compact `K`: from `gx, gy ∈ L²(K)` the `L²`-finiteness of the
  -- squared norms rewrites to natural-power integrals.
  have hsq_fin : ∀ (h : ℂ → ℂ) (K : Set ℂ), MemLp h 2 (volume.restrict K) →
      (∫⁻ z in K, (‖h z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
    intro h K hmem
    have hlt : eLpNorm h 2 (volume.restrict K) < ∞ := hmem.eLpNorm_lt_top
    have key : ∫⁻ z, ‖h z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂(volume.restrict K) < ∞ :=
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := volume.restrict K)
        (f := h) (by norm_num) (by norm_num)).1 hlt
    have heq : (∫⁻ z in K, (‖h z‖₊ : ℝ≥0∞) ^ 2)
        = ∫⁻ z, ‖h z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂(volume.restrict K) := by
      refine lintegral_congr (fun z => ?_)
      rw [enorm_eq_nnnorm, show ((2 : ℝ≥0∞).toReal) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
    rw [heq]; exact key.ne
  have hφ_fin : ∀ n : ℕ, (∫⁻ z in Metric.closedBall (0 : ℂ) n, φ z) ≠ ∞ := by
    intro n
    have hKcpt : IsCompact (Metric.closedBall (0 : ℂ) n) := isCompact_closedBall 0 n
    have hgxK := hgx (Metric.closedBall 0 n) (Set.subset_univ _) hKcpt
    have hgyK := hgy (Metric.closedBall 0 n) (Set.subset_univ _) hKcpt
    have hsplit : (∫⁻ z in Metric.closedBall (0 : ℂ) n, φ z)
        = (∫⁻ z in Metric.closedBall (0 : ℂ) n, (‖gx z‖₊ : ℝ≥0∞) ^ 2)
          + (∫⁻ z in Metric.closedBall (0 : ℂ) n, (‖gy z‖₊ : ℝ≥0∞) ^ 2) := by
      simp only [hφ_def, energyDensity]
      exact lintegral_add_left' hgx_sq_aem.restrict _
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨hsq_fin gx _ hgxK, hsq_fin gy _ hgyK⟩
  -- Step 3. For each `n`, the Lebesgue differentiation theorem (Besicovitch / Vitali family of
  -- closed balls) gives, for a.e. `x` in `ball 0 n`, a finite limit `φ x` of the disc averages.
  have hgood : ∀ n : ℕ, ∀ᵐ x : ℂ, x ∈ Metric.ball (0 : ℂ) n →
      (φ x ≠ ∞ ∧ Tendsto (fun r => (∫⁻ y in Metric.closedBall x r, φ y)
          / volume (Metric.closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (φ x))) := by
    intro n
    set v := Besicovitch.vitaliFamily (volume : Measure ℂ) with hv_def
    set ψ : ℂ → ℝ≥0∞ := (Metric.closedBall (0 : ℂ) n).indicator φ with hψ_def
    have hψ_aem : AEMeasurable ψ volume := hφ_aem.indicator measurableSet_closedBall
    have hψ_fin : (∫⁻ z, ψ z) ≠ ∞ := by
      rw [hψ_def, lintegral_indicator measurableSet_closedBall]; exact hφ_fin n
    have hLeb := v.ae_tendsto_lintegral_div hψ_aem hψ_fin
    have hfin_ae : ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : ℂ) n)), φ x ≠ ∞ := by
      have hlt := ae_lt_top' (μ := volume.restrict (Metric.closedBall (0 : ℂ) n)) (f := φ)
        hφ_aem.restrict (hφ_fin n)
      filter_upwards [hlt] with x hx using hx.ne
    rw [ae_restrict_iff' measurableSet_closedBall] at hfin_ae
    filter_upwards [hLeb, hfin_ae] with x hx hxfin hmem
    have hxcb : x ∈ Metric.closedBall (0 : ℂ) n := ball_subset_closedBall hmem
    refine ⟨hxfin hxcb, ?_⟩
    have hψx : ψ x = φ x := by rw [hψ_def, indicator_of_mem hxcb]
    have hxr : Tendsto (fun r => (∫⁻ y in Metric.closedBall x r, ψ y)
        / volume (Metric.closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (ψ x)) :=
      hx.comp (Besicovitch.tendsto_filterAt (volume : Measure ℂ) x)
    rw [hψx] at hxr
    apply hxr.congr'
    obtain ⟨ε, hεpos, hεsub⟩ :
        ∃ ε > (0 : ℝ), Metric.closedBall x ε ⊆ Metric.closedBall (0 : ℂ) n := by
      rw [Metric.mem_ball, dist_zero_right] at hmem
      refine ⟨(n : ℝ) - ‖x‖, by linarith, ?_⟩
      apply Metric.closedBall_subset_closedBall'
      rw [dist_zero_right]; linarith
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε from hεpos)] with r hr
    have hrsub : Metric.closedBall x r ⊆ Metric.closedBall (0 : ℂ) n :=
      (Metric.closedBall_subset_closedBall hr.2.le).trans hεsub
    congr 1
    refine setLIntegral_congr_fun measurableSet_closedBall (fun y hy => ?_)
    rw [hψ_def, indicator_of_mem (hrsub hy)]
  -- Step 4. Patch the `n`-wise good sets over the cover `⋃ n, ball 0 n = univ`, then convert the
  -- finite disc-average limit into the desired `O(s²)` energy bound using `vol(B(x,2s)) = 4π s²`.
  filter_upwards [ae_all_iff.2 hgood] with x hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x ∈ Metric.ball (0 : ℂ) n := by
    have : x ∈ (⋃ n : ℕ, Metric.ball (0 : ℂ) n) := by rw [iUnion_ball_nat]; trivial
    simpa only [Set.mem_iUnion] using this
  obtain ⟨hfin, htend⟩ := hx n hn
  refine ⟨((φ x).toReal + 1) * (4 * Real.pi), by positivity, ?_⟩
  have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫⁻ y in Metric.closedBall x r, φ y) / volume (Metric.closedBall x r) < φ x + 1 :=
    htend.eventually_lt_const (ENNReal.lt_add_right hfin one_ne_zero)
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫⁻ y in Metric.closedBall x r, φ y) ≤ (φ x + 1) * volume (Metric.closedBall x r) := by
    filter_upwards [hlt, self_mem_nhdsWithin] with r hr hrpos
    rw [Set.mem_Ioi] at hrpos
    have hvol_ne0 : volume (Metric.closedBall x r) ≠ 0 := by
      rw [Complex.volume_closedBall]
      refine mul_ne_zero (pow_ne_zero _ ?_) ?_
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hrpos
      · rw [Ne, ENNReal.coe_eq_zero]; exact NNReal.pi_ne_zero
    have hvol_ne_top : volume (Metric.closedBall x r) ≠ ∞ := by
      rw [Complex.volume_closedBall]; finiteness
    calc (∫⁻ y in Metric.closedBall x r, φ y)
        = ((∫⁻ y in Metric.closedBall x r, φ y) / volume (Metric.closedBall x r))
            * volume (Metric.closedBall x r) :=
          (ENNReal.div_mul_cancel hvol_ne0 hvol_ne_top).symm
      _ ≤ (φ x + 1) * volume (Metric.closedBall x r) := mul_le_mul' hr.le le_rfl
  have hbound2 := eventually_nhdsGT_zero_mul_left (show (0 : ℝ) < 2 by norm_num) hbound
  filter_upwards [hbound2, self_mem_nhdsWithin] with s hs hspos
  rw [Set.mem_Ioi] at hspos
  refine hs.trans (le_of_eq ?_)
  rw [Complex.volume_closedBall]
  have hL1 : φ x + 1 = ENNReal.ofReal ((φ x).toReal + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_one]
  have h2s : ENNReal.ofReal (2 * s) ^ 2 = ENNReal.ofReal ((2 * s) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
  have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [hL1, h2s, hpi, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **Smooth Courant–Lebesgue (CL-smooth = Part A + Part B).**

For a `C¹` map `g` there is a radius `ρ ∈ [r, 2r]` whose image circle has small squared diameter
relative to the Dirichlet energy of the surrounding disc:
`diam (g '' sphere x ρ)² ≤ (π / (2 log 2)) · ∫_{closedBall x (2r)} (‖∂_x g‖² + ‖∂_y g‖²)`.

Part A (the analytic heart): for each `ρ`, the image circle has diameter at most half its arc length
`∫₀^{2π} ‖∂_θ g(x + ρe^{iθ})‖ dθ`, and `‖∂_θ g‖ ≤ ‖Dg‖·ρ` with `‖Dg‖² ≤ ‖Dg·1‖² + ‖Dg·I‖²`; by
Cauchy–Schwarz `diam² ≤ (π/2)·ρ²·∫₀^{2π} (‖Dg·1‖² + ‖Dg·I‖²)(x + ρe^{iθ}) dθ`. Part B (polar
averaging): the `dρ/ρ`-average of the right side over `[r, 2r]` (total weight `log 2`) equals
`(π/2)·(∫_{annulus} energy)/log 2`, so some `ρ` achieves the displayed bound. -/
theorem courantLebesgue_smooth {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ρ ∈ Set.Icc r (2 * r),
      ENNReal.ofReal ((Metric.diam (g '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal (Real.pi / (2 * Real.log 2))
          * ∫⁻ z in Metric.closedBall x (2 * r),
              energyDensity (fun w => (fderiv ℝ g w) 1) (fun w => (fderiv ℝ g w) Complex.I) z := by
  classical
  -- ===========================================================================================
  -- PART A: the smooth circular bound.  For every centre `c` and radius `ρ > 0`,
  --   diam(g '' sphere c ρ)² ≤ (π/2)·ρ²·∫₀^{2π} (‖Dg·1‖² + ‖Dg·I‖²)(circleMap c ρ θ) dθ.
  -- ===========================================================================================
  -- Frobenius bound on the operator norm of the derivative:  ‖Dg p‖ ≤ √(‖Dg·1‖² + ‖Dg·I‖²).
  have hfrob : ∀ p : ℂ,
      ‖fderiv ℝ g p‖ ≤ Real.sqrt (‖(fderiv ℝ g p) 1‖ ^ 2 + ‖(fderiv ℝ g p) Complex.I‖ ^ 2) := by
    intro p
    set a : ℂ := (fderiv ℝ g p) 1 with ha_def
    set b : ℂ := (fderiv ℝ g p) Complex.I with hb_def
    set R : ℝ := Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) with hR_def
    have hRnn : 0 ≤ R := Real.sqrt_nonneg _
    refine ContinuousLinearMap.opNorm_le_bound _ hRnn (fun v => ?_)
    -- Decompose `v = (v.re : ℂ) * 1 + (v.im : ℂ) * I` and use linearity of the derivative.
    -- We use complex multiplication throughout to dodge the missing `NormSMulClass ℝ ℂ`.
    have hdecomp : (fderiv ℝ g p) v
        = (v.re : ℂ) * a + (v.im : ℂ) * b := by
      have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
        rw [Complex.real_smul, Complex.real_smul, mul_one]
        exact (Complex.re_add_im v).symm
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul, ha_def, hb_def, Complex.real_smul, Complex.real_smul]
    rw [hdecomp]
    -- Triangle inequality:  ‖re·a + im·b‖ ≤ |re|·‖a‖ + |im|·‖b‖.
    have htri : ‖(v.re : ℂ) * a + (v.im : ℂ) * b‖ ≤ |v.re| * ‖a‖ + |v.im| * ‖b‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    refine htri.trans ?_
    -- Cauchy–Schwarz:  |v.re|·‖a‖ + |v.im|·‖b‖ ≤ √(re²+im²)·√(‖a‖²+‖b‖²) = ‖v‖·R.
    have hnormv : ‖v‖ = Real.sqrt (v.re ^ 2 + v.im ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]; ring_nf
    rw [hnormv, hR_def, ← Real.sqrt_mul (by positivity)]
    refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
    nlinarith [sq_nonneg (|v.re| * ‖b‖ - |v.im| * ‖a‖), sq_abs v.re, sq_abs v.im,
      abs_nonneg v.re, abs_nonneg v.im, norm_nonneg a, norm_nonneg b]
  -- The smooth circular bound, for every centre and positive radius.
  have hsmooth : ∀ (c : ℂ) (ρ : ℝ), 0 < ρ →
      (Metric.diam (g '' Metric.sphere c ρ)) ^ 2 ≤
        (Real.pi / 2) * ρ ^ 2 *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
    intro c ρ hρ
    -- The loop `γ := g ∘ circleMap c ρ`.
    set γ : ℝ → ℂ := g ∘ circleMap c ρ with hγ_def
    -- `g` is differentiable everywhere (it is `C¹`).
    have hg_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
    -- Loop chain rule:  `HasDerivAt γ ((Dg (circleMap c ρ θ)) (circleMap 0 ρ θ * I)) θ`.
    have hγ_deriv : ∀ θ : ℝ,
        HasDerivAt γ ((fderiv ℝ g (circleMap c ρ θ)) (circleMap 0 ρ θ * Complex.I)) θ := by
      intro θ
      have h1 : HasFDerivAt g (fderiv ℝ g (circleMap c ρ θ)) (circleMap c ρ θ) :=
        (hg_diff (circleMap c ρ θ)).hasFDerivAt
      have h2 : HasDerivAt (circleMap c ρ) (circleMap 0 ρ θ * Complex.I) θ :=
        hasDerivAt_circleMap c ρ θ
      exact h1.comp_hasDerivAt θ h2
    -- The derivative of `γ` is continuous (composite of continuous maps).
    have hγ_contDeriv : Continuous (deriv γ) := by
      have hcd : ContDiff ℝ 1 γ := hg.comp (contDiff_circleMap c ρ)
      have : Continuous (fun θ => deriv γ θ) := by
        have := hcd.continuous_deriv (le_rfl)
        simpa using this
      simpa using this
    -- Pointwise bound on the loop speed:  `‖deriv γ θ‖ ≤ ρ·√(‖Dg·1‖²+‖Dg·I‖²)`.
    have hspeed : ∀ θ : ℝ, ‖deriv γ θ‖
        ≤ ρ * Real.sqrt (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      intro θ
      rw [(hγ_deriv θ).deriv]
      have hle : ‖(fderiv ℝ g (circleMap c ρ θ)) (circleMap 0 ρ θ * Complex.I)‖
          ≤ ‖fderiv ℝ g (circleMap c ρ θ)‖ * ‖circleMap 0 ρ θ * Complex.I‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hnorm : ‖circleMap 0 ρ θ * Complex.I‖ = ρ := by
        rw [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ]
      rw [hnorm] at hle
      calc ‖(fderiv ℝ g (circleMap c ρ θ)) (circleMap 0 ρ θ * Complex.I)‖
          ≤ ‖fderiv ℝ g (circleMap c ρ θ)‖ * ρ := hle
        _ ≤ Real.sqrt (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) * ρ :=
            mul_le_mul_of_nonneg_right (hfrob _) hρ.le
        _ = ρ * Real.sqrt _ := by ring
    -- `γ` is periodic with period `2π`.
    have hγ_per : Function.Periodic γ (2 * Real.pi) := by
      intro θ
      simp only [hγ_def, Function.comp_apply]
      rw [periodic_circleMap c ρ θ]
    -- `g '' sphere c ρ = range γ`.
    have himg_range : g '' Metric.sphere c ρ = Set.range γ := by
      rw [hγ_def, Set.range_comp, range_circleMap, abs_of_pos hρ]
    -- The arc-length `L := ∫₀^{2π} ‖deriv γ‖`.
    set L : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv γ θ‖ with hL_def
    -- `‖deriv γ‖` is interval-integrable on any interval (it is continuous).
    have hint_norm : ∀ s t : ℝ, IntervalIntegrable (fun θ => ‖deriv γ θ‖) volume s t :=
      fun s t => (hγ_contDeriv.norm).intervalIntegrable s t
    have hint_deriv : ∀ s t : ℝ, IntervalIntegrable (deriv γ) volume s t :=
      fun s t => hγ_contDeriv.intervalIntegrable s t
    -- `deriv γ` is the derivative everywhere.
    have hderiv_eq : ∀ θ : ℝ, HasDerivAt γ (deriv γ θ) θ :=
      fun θ => ((hγ_deriv θ).deriv) ▸ (hγ_deriv θ)
    -- For `s ≤ t`, `dist (γ s) (γ t) ≤ ∫_s^t ‖deriv γ‖`.
    have harc : ∀ s t : ℝ, s ≤ t → dist (γ s) (γ t) ≤ ∫ θ in s..t, ‖deriv γ θ‖ := by
      intro s t hst
      have hFTC : ∫ θ in s..t, deriv γ θ = γ t - γ s :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv_eq θ) (hint_deriv s t)
      rw [dist_eq_norm, norm_sub_rev, ← hFTC]
      exact intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := deriv γ) hst
    -- The two complementary arcs sum to `L`.
    have hsum : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 2 * Real.pi →
        (∫ θ in s..t, ‖deriv γ θ‖) + ((∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖)
          + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖) = L := by
      intro s t hs hst htp
      have e1 : (∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖) + ∫ θ in s..t, ‖deriv γ θ‖
          = ∫ θ in (0 : ℝ)..t, ‖deriv γ θ‖ :=
        intervalIntegral.integral_add_adjacent_intervals (hint_norm 0 s) (hint_norm s t)
      have e2 : (∫ θ in (0 : ℝ)..t, ‖deriv γ θ‖) + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖
          = ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv γ θ‖ :=
        intervalIntegral.integral_add_adjacent_intervals (hint_norm 0 t) (hint_norm t (2*Real.pi))
      rw [hL_def, ← e2, ← e1]; ring
    -- `γ (2π) = γ 0`.
    have hγ_endpoint : γ (2 * Real.pi) = γ 0 := by
      have := hγ_per 0; rwa [zero_add] at this
    -- The complementary-arc bound:  `dist (γ s) (γ t) ≤ (∫_0^s + ∫_t^{2π}) ‖deriv γ‖`.
    have harc' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 2 * Real.pi →
        dist (γ s) (γ t) ≤ (∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖)
          + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖ := by
      intro s t hs hst htp
      have h1 : dist (γ t) (γ (2 * Real.pi)) ≤ ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖ :=
        harc t (2 * Real.pi) htp
      have h2 : dist (γ 0) (γ s) ≤ ∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖ := harc 0 s hs
      calc dist (γ s) (γ t) = dist (γ t) (γ s) := dist_comm _ _
        _ ≤ dist (γ t) (γ (2 * Real.pi)) + dist (γ (2 * Real.pi)) (γ s) := dist_triangle _ _ _
        _ = dist (γ t) (γ (2 * Real.pi)) + dist (γ 0) (γ s) := by rw [hγ_endpoint]
        _ ≤ (∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖) + ∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖ :=
            add_le_add h1 h2
        _ = (∫ θ in (0 : ℝ)..s, ‖deriv γ θ‖) + ∫ θ in t..(2 * Real.pi), ‖deriv γ θ‖ := by ring
    -- Every pair of points on the loop is within `L/2`.
    have hpair : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 2 * Real.pi → dist (γ s) (γ t) ≤ L / 2 := by
      intro s t hs hst htp
      -- `2 · dist ≤ arc1 + arc2 = L`.
      have hd1 := harc s t hst
      have hd2 := harc' s t hs hst htp
      have hsum' := hsum s t hs hst htp
      linarith
    -- The diameter of the loop is `≤ L/2`.
    have hL_nonneg : 0 ≤ L := by
      rw [hL_def]
      apply intervalIntegral.integral_nonneg (by positivity)
      intro θ _; exact norm_nonneg _
    have hdiam_le : Metric.diam (g '' Metric.sphere c ρ) ≤ L / 2 := by
      rw [himg_range]
      -- `range γ = γ '' Icc 0 (2π)`.
      have hrange_eq : Set.range γ = γ '' Set.Icc 0 (2 * Real.pi) := by
        rw [← hγ_per.image_Icc Real.two_pi_pos 0, zero_add]
      rw [hrange_eq]
      refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
      rintro p ⟨s, hs, rfl⟩ q ⟨t, ht, rfl⟩
      rw [Set.mem_Icc] at hs ht
      rcases le_total s t with hle | hle
      · exact hpair s t hs.1 hle ht.2
      · rw [dist_comm]; exact hpair t s ht.1 hle hs.2
    -- Interval Cauchy–Schwarz:  `L² ≤ 2π · ∫₀^{2π} ‖deriv γ‖²`.
    -- Work on the finite measure `μ := volume.restrict (Ioc 0 (2π))`.
    set μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi)) with hμ_def
    have hμ_fin : IsFiniteMeasure μ := by
      rw [hμ_def]
      apply isFiniteMeasure_restrict.mpr
      rw [Real.volume_Ioc]; finiteness
    -- `‖deriv γ‖` is bounded on the compact `Icc 0 (2π)`, hence `MemLp _ 2 μ`.
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖deriv γ θ‖ ≤ C :=
      (isCompact_Icc).exists_bound_of_continuousOn (hγ_contDeriv.continuousOn)
    have hae_bound : ∀ᵐ θ ∂μ, ‖‖deriv γ θ‖‖ ≤ C := by
      rw [hμ_def, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hC θ (Set.Ioc_subset_Icc_self hθ)
    have hmemLp_f : MemLp (fun θ => ‖deriv γ θ‖) 2 μ := by
      refine MemLp.of_bound ?_ C hae_bound
      exact (hγ_contDeriv.norm.aestronglyMeasurable)
    have hmemLp_one : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := by
      have : IsFiniteMeasure μ := hμ_fin
      exact memLp_const 1
    -- Apply Hölder with `p = q = 2`.
    have hholder : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hholder
      (f := fun θ => ‖deriv γ θ‖) (g := fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall fun θ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      (by simpa using hmemLp_f) (by simpa using hmemLp_one)
    -- Simplify the Hölder inequality:  `∫ f ≤ (∫ f²)^{1/2}·(2π)^{1/2}`.
    -- `∫ f ∂μ = L` and `∫ 1² ∂μ = 2π`.
    have hμ_univ : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
      rw [hμ_def, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    have hintf : ∫ θ, ‖deriv γ θ‖ ∂μ = L := by
      rw [hμ_def, hL_def, intervalIntegral.integral_of_le (by positivity)]
    have hint1 : ∫ (_ : ℝ), (1 : ℝ) ^ (2 : ℝ) ∂μ = 2 * Real.pi := by
      simp only [Real.one_rpow]
      rw [MeasureTheory.integral_const, smul_eq_mul, mul_one, Measure.real, hμ_univ,
        ENNReal.toReal_ofReal (by positivity)]
    simp only [mul_one] at hCS
    rw [hintf, hint1] at hCS
    -- Now `L ≤ (∫ f²)^{1/2}·(2π)^{1/2}`, so `L² ≤ 2π·∫ f²`.
    have hint_f2_nonneg : (0 : ℝ) ≤ ∫ θ, ‖deriv γ θ‖ ^ (2 : ℝ) ∂μ :=
      MeasureTheory.integral_nonneg (fun θ => by positivity)
    -- Abbreviate `J := ∫ f²`.
    set J : ℝ := ∫ θ, ‖deriv γ θ‖ ^ (2 : ℝ) ∂μ with hJ_def
    have hJ_nonneg : (0 : ℝ) ≤ J := hint_f2_nonneg
    have h2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hhalf1 : J ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) = J := by
      rw [← Real.rpow_add' hJ_nonneg (by norm_num)]; norm_num
    have hhalf2 : (2 * Real.pi) ^ (1 / 2 : ℝ) * (2 * Real.pi) ^ (1 / 2 : ℝ) = 2 * Real.pi := by
      rw [← Real.rpow_add' h2pi_nonneg (by norm_num)]; norm_num
    have hL_sq : L ^ 2 ≤ (2 * Real.pi) * J := by
      have hsq := mul_self_le_mul_self hL_nonneg hCS
      rw [← pow_two, mul_mul_mul_comm, hhalf1, hhalf2] at hsq
      linarith [hsq]
    -- The pointwise speed-square bound integrates:  `J ≤ ρ²·∫₀^{2π}(‖Dg·1‖²+‖Dg·I‖²)`.
    -- Convert `J` to an interval integral with a natural-power integrand.
    have hJ_eq : J = ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv γ θ‖ ^ 2 := by
      rw [hJ_def, hμ_def, intervalIntegral.integral_of_le (by positivity)]
      refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    -- The squared speed bound, pointwise.
    have hspeed_sq : ∀ θ : ℝ, ‖deriv γ θ‖ ^ 2
        ≤ ρ ^ 2 * (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      intro θ
      have h := hspeed θ
      have hsq := mul_self_le_mul_self (norm_nonneg _) h
      rw [← pow_two, mul_mul_mul_comm] at hsq
      rw [Real.mul_self_sqrt (by positivity)] at hsq
      calc ‖deriv γ θ‖ ^ 2 ≤ ρ * ρ * (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := hsq
        _ = ρ ^ 2 * (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
              + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by ring
    -- Integrate the pointwise bound over `[0, 2π]`.
    have hcont_lhs : Continuous (fun θ => ‖deriv γ θ‖ ^ 2) := hγ_contDeriv.norm.pow 2
    have hcdf : Continuous (fun θ : ℝ => fderiv ℝ g (circleMap c ρ θ)) :=
      (hg.continuous_fderiv (by norm_num)).comp (continuous_circleMap c ρ)
    have hcont_sum : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      have h1 : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2) :=
        ((hcdf.clm_apply continuous_const).norm.pow 2)
      have h2 : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) :=
        ((hcdf.clm_apply continuous_const).norm.pow 2)
      exact h1.add h2
    have hJ_le : J ≤ ρ ^ 2 *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by
      rw [hJ_eq, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by positivity)
      · exact hcont_lhs.intervalIntegrable _ _
      · exact (continuous_const.mul hcont_sum).intervalIntegrable _ _
      · intro θ _; exact hspeed_sq θ
    -- Assemble Part A:  diam² ≤ (L/2)² = L²/4 ≤ (2π·J)/4 = (π/2)·J ≤ (π/2)·ρ²·∫(...).
    have hdiam_sq : (Metric.diam (g '' Metric.sphere c ρ)) ^ 2 ≤ (L / 2) ^ 2 := by
      apply pow_le_pow_left₀ Metric.diam_nonneg hdiam_le
    calc (Metric.diam (g '' Metric.sphere c ρ)) ^ 2
        ≤ (L / 2) ^ 2 := hdiam_sq
      _ = L ^ 2 / 4 := by ring
      _ ≤ ((2 * Real.pi) * J) / 4 := by linarith [hL_sq]
      _ = (Real.pi / 2) * J := by ring
      _ ≤ (Real.pi / 2) * (ρ ^ 2 *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
                + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hJ_le (by positivity)
      _ = (Real.pi / 2) * ρ ^ 2 *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (‖(fderiv ℝ g (circleMap c ρ θ)) 1‖ ^ 2
                + ‖(fderiv ℝ g (circleMap c ρ θ)) Complex.I‖ ^ 2) := by ring
  -- ===========================================================================================
  -- PART B: polar averaging and radius selection.
  -- ===========================================================================================
  -- The energy density `Φ = energyDensity (Dg·1) (Dg·I)`.
  set Φ : ℂ → ℝ≥0∞ :=
    energyDensity (fun w => (fderiv ℝ g w) 1) (fun w => (fderiv ℝ g w) Complex.I) with hΦ_def
  -- `Φ z = ofReal (‖Dg z·1‖² + ‖Dg z·I‖²)`:  the real form of the energy density.
  have hcdf_glob : Continuous (fun z : ℂ => fderiv ℝ g z) := hg.continuous_fderiv (by norm_num)
  have hRcont : Continuous (fun z : ℂ => ‖(fderiv ℝ g z) 1‖ ^ 2
      + ‖(fderiv ℝ g z) Complex.I‖ ^ 2) := by
    have h1 : Continuous (fun z : ℂ => ‖(fderiv ℝ g z) 1‖ ^ 2) :=
      (hcdf_glob.clm_apply continuous_const).norm.pow 2
    have h2 : Continuous (fun z : ℂ => ‖(fderiv ℝ g z) Complex.I‖ ^ 2) :=
      (hcdf_glob.clm_apply continuous_const).norm.pow 2
    exact h1.add h2
  -- `Φ z = ofReal (‖Dg z·1‖² + ‖Dg z·I‖²)`:  the real form of the energy density.
  have hΦ_ofReal : ∀ z : ℂ,
      Φ z = ENNReal.ofReal (‖(fderiv ℝ g z) 1‖ ^ 2 + ‖(fderiv ℝ g z) Complex.I‖ ^ 2) := by
    intro z
    rw [hΦ_def, energyDensity]
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    have e : ∀ a : ℂ, (‖a‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖a‖ ^ 2) := by
      intro a
      rw [← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [e, e]
  -- `Φ` is continuous (since `g` is `C¹`), hence measurable.
  have hΦ_cont : Continuous Φ := by
    have hco : Continuous (fun z : ℂ => ENNReal.ofReal (‖(fderiv ℝ g z) 1‖ ^ 2
        + ‖(fderiv ℝ g z) Complex.I‖ ^ 2)) := ENNReal.continuous_ofReal.comp hRcont
    exact (funext hΦ_ofReal).symm ▸ hco
  have hΦ_meas : Measurable Φ := hΦ_cont.measurable
  -- The annular energy `E := ∫⁻_{closedBall x 2r} Φ`.
  set E : ℝ≥0∞ := ∫⁻ z in Metric.closedBall x (2 * r), Φ z with hE_def
  -- `E` is finite:  `Φ` is bounded on the compact `closedBall x 2r`.
  have hE_ne_top : E ≠ ∞ := by
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall x (2 * r),
        ‖(fderiv ℝ g z) 1‖ ^ 2 + ‖(fderiv ℝ g z) Complex.I‖ ^ 2 ≤ M := by
      obtain ⟨C, hC⟩ := (isCompact_closedBall x (2 * r)).exists_bound_of_continuousOn
        hRcont.continuousOn
      refine ⟨C, fun z hz => ?_⟩
      have := hC z hz
      rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    rw [hE_def]
    apply ne_top_of_le_ne_top (b := ENNReal.ofReal M * volume (Metric.closedBall x (2 * r)))
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      rw [Complex.volume_closedBall]; finiteness
    · rw [← setLIntegral_const]
      apply setLIntegral_mono_ae (aemeasurable_const (b := ENNReal.ofReal M))
      refine ae_of_all _ (fun z hz => ?_)
      rw [hΦ_ofReal]
      exact ENNReal.ofReal_le_ofReal (hM z hz)
  -- The circular energy `Gρ := ∫⁻ θ in Ioo (-π) π, Φ (circleMap x ρ θ)`.
  set Gρ : ℝ → ℝ≥0∞ := fun ρ => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
    Φ (circleMap x ρ θ) with hGρ_def
  -- `circleMap x ρ θ = x + Complex.polarCoord.symm (ρ, θ)`.
  have hcircle_polar : ∀ (ρ θ : ℝ), circleMap x ρ θ = x + Complex.polarCoord.symm (ρ, θ) := by
    intro ρ θ
    rw [Complex.polarCoord_symm_apply, circleMap]
    rw [Complex.exp_mul_I]
    push_cast
    ring
  -- The annulus/polar lower bound:  `∫⁻ ρ in Ioc r (2r), ofReal ρ * Gρ ≤ E`.
  -- Build it from the complex polar-coordinate change of variables.
  -- Translated indicator integrand `F z := indicator (closedBall x 2r) Φ (x + z)`.
  set F : ℂ → ℝ≥0∞ := fun z => (Metric.closedBall x (2 * r)).indicator Φ (x + z) with hF_def
  -- Translation:  `∫⁻ z, F z = E`.
  have htrans : ∫⁻ z, F z = E := by
    have hmp : MeasurePreserving (fun z : ℂ => x + z) volume volume :=
      measurePreserving_add_left volume x
    have hg_meas : Measurable ((Metric.closedBall x (2 * r)).indicator Φ) :=
      hΦ_meas.indicator measurableSet_closedBall
    have := hmp.lintegral_comp hg_meas
    rw [hF_def]
    rw [this]
    rw [hE_def, lintegral_indicator measurableSet_closedBall]
  -- `F` is measurable.
  have hF_meas : Measurable F := by
    rw [hF_def]
    exact (hΦ_meas.indicator measurableSet_closedBall).comp (measurable_const.add measurable_id)
  -- The complex polar identity:  `∫⁻ z, F z = ∫⁻ p in target, ofReal p.1 * F (symm p)`.
  have hpolar : E = ∫⁻ p in Complex.polarCoord.target,
      ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) := by
    rw [← htrans, ← Complex.lintegral_comp_polarCoord_symm F]
    refine setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet (fun p _ => ?_)
    rw [smul_eq_mul]
  -- Tonelli:  the polar integral is the iterated radius-then-angle integral.
  have htarget : Complex.polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi :=
    Complex.polarCoord_target
  -- The integrand of the polar identity.
  set H : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) with hH_def
  have hsymm_meas : Measurable (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
    have heq : (Complex.polarCoord.symm : ℝ × ℝ → ℂ)
        = fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; rw [Complex.polarCoord_symm_apply]
    rw [heq]
    fun_prop
  have hH_meas : Measurable H := by
    rw [hH_def]
    refine Measurable.mul ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp measurable_fst)
    · exact hF_meas.comp hsymm_meas
  -- Iterate via Tonelli over the product set.
  have hiter : E = ∫⁻ ρ in Set.Ioi (0 : ℝ),
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) := by
    rw [hpolar, htarget]
    rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hH_meas.aemeasurable]
  -- For `ρ ∈ Ioc r (2r)`, the inner integral equals `ofReal ρ * Gρ`.
  have hinner : ∀ ρ ∈ Set.Ioc r (2 * r),
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) = ENNReal.ofReal ρ * Gρ ρ := by
    intro ρ hρ
    obtain ⟨hρ1, hρ2⟩ := hρ
    have hρpos : 0 < ρ := lt_trans hr hρ1
    rw [hGρ_def]
    rw [hH_def]
    simp only
    rw [← lintegral_const_mul']
    · refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      -- `F (symm (ρ, θ)) = Φ (circleMap x ρ θ)` since the point lies in `closedBall x 2r`.
      have hpt : x + Complex.polarCoord.symm (ρ, θ) = circleMap x ρ θ := (hcircle_polar ρ θ).symm
      rw [hF_def]
      simp only
      rw [hpt]
      rw [Set.indicator_of_mem]
      · -- `circleMap x ρ θ ∈ closedBall x 2r`.
        rw [Metric.mem_closedBall, Complex.dist_eq, ← hpt, add_sub_cancel_left,
          Complex.norm_polarCoord_symm, abs_of_pos hρpos]
        exact hρ2
    · exact ENNReal.ofReal_ne_top
  -- The annulus lower bound:  `∫⁻ ρ in Ioc r (2r), ofReal ρ * Gρ ρ ≤ E`.
  have hannulus : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal ρ * Gρ ρ) ≤ E := by
    rw [hiter]
    -- Restrict the outer integral to `Ioc r 2r ⊆ Ioi 0`.
    have hsub : Set.Ioc r (2 * r) ⊆ Set.Ioi (0 : ℝ) :=
      fun ρ hρ => lt_trans hr hρ.1
    calc (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal ρ * Gρ ρ)
        = ∫⁻ ρ in Set.Ioc r (2 * r), (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) := by
          refine setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => ?_)
          rw [hinner ρ hρ]
      _ ≤ ∫⁻ ρ in Set.Ioi (0 : ℝ), (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, H (ρ, θ)) :=
          lintegral_mono_set hsub
  -- The bridge:  `Gρ ρ = ofReal (∫₀^{2π} R_ρ)` where `R_ρ` is the real circular energy.
  have hGρ_bridge : ∀ ρ : ℝ,
      Gρ ρ = ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
          + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2)) := by
    intro ρ
    -- `R_ρ` is continuous (composite of continuous maps).
    have hRρ_cont : Continuous (fun θ : ℝ => ‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) := by
      have hcdf : Continuous (fun θ : ℝ => fderiv ℝ g (circleMap x ρ θ)) :=
        hcdf_glob.comp (continuous_circleMap x ρ)
      exact ((hcdf.clm_apply continuous_const).norm.pow 2).add
        ((hcdf.clm_apply continuous_const).norm.pow 2)
    have hRρ_nonneg : ∀ θ : ℝ, 0 ≤ ‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2 := fun θ => by positivity
    -- `R_ρ` is `2π`-periodic.
    have hRρ_per : Function.Periodic (fun θ : ℝ => ‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
        + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) (2 * Real.pi) := by
      intro θ
      simp only
      rw [periodic_circleMap x ρ θ]
    -- `Gρ ρ = ∫⁻ θ in Ioo(-π)π, ofReal (R_ρ θ)`.
    have hGρ1 : Gρ ρ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
          + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) := by
      rw [hGρ_def]
      refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [hΦ_ofReal]
    rw [hGρ1]
    -- `∫⁻ ofReal R = ofReal (∫ R)` on `Ioo(-π)π` (R integrable, nonneg).
    rw [← ofReal_integral_eq_lintegral_ofReal
        ((hRρ_cont.integrableOn_Ioc).mono_set Set.Ioo_subset_Ioc_self)
        (ae_of_all _ (fun θ => hRρ_nonneg θ))]
    -- `∫ θ in Ioo(-π)π, R = ∫₀^{2π} R` (periodicity).
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    -- `∫_{-π}^{π} R = ∫_0^{2π} R`.
    have hper_eq : (∫ θ in (-Real.pi)..Real.pi,
          (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
            + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) := by
      have h := hRρ_per.intervalIntegral_add_eq (-Real.pi) 0
      rw [zero_add] at h
      rw [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi by ring] at h
      exact h
    exact hper_eq
  -- `log 2 > 0`.
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `∫⁻ ρ in Ioc r (2r), ofReal (1/ρ) = ofReal (log 2)`.
  have hlog_int : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ))
      = ENNReal.ofReal (Real.log 2) := by
    have hcont : ContinuousOn (fun ρ : ℝ => 1 / ρ) (Set.Icc r (2 * r)) := by
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro ρ hρ; exact (ne_of_gt (lt_of_lt_of_le hr hρ.1))
    have hint_on : IntegrableOn (fun ρ : ℝ => 1 / ρ) (Set.Ioc r (2 * r)) :=
      (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc r (2 * r))] fun ρ : ℝ => 1 / ρ := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact ae_of_all _ (fun ρ hρ => by
        have : 0 < ρ := lt_trans hr hρ.1
        positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hint_on hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le (by linarith : r ≤ 2 * r)]
    rw [integral_one_div_of_pos hr (by linarith : (0:ℝ) < 2 * r)]
    rw [show 2 * r / r = 2 by field_simp]
  -- The radius selection by contradiction.
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / Real.log 2) * E with hc_def
  -- There is `ρ ∈ Ioc r (2r)` with `ofReal (ρ²) * Gρ ρ ≤ c`.
  have hselect : ∃ ρ ∈ Set.Ioc r (2 * r), ENNReal.ofReal (ρ ^ 2) * Gρ ρ ≤ c := by
    by_contra hcon
    push Not at hcon
    -- For all `ρ ∈ Ioc r 2r`, `c < ofReal(ρ²) * Gρ ρ`.
    -- Define `f ρ := ofReal(1/ρ) * c`, `g ρ := ofReal ρ * Gρ ρ`.
    have hGρ_meas : Measurable Gρ := by
      have heq : Gρ = fun ρ => ∫⁻ θ, Φ (circleMap x ρ θ)
          ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
        rw [hGρ_def]
      rw [heq]
      have hmeas2 : Measurable (fun p : ℝ × ℝ => Φ (circleMap x p.1 p.2)) := by
        apply hΦ_meas.comp
        have : Continuous (fun p : ℝ × ℝ => circleMap x p.1 p.2) := by
          unfold circleMap; fun_prop
        exact this.measurable
      exact hmeas2.lintegral_prod_right'
    have hg_meas : Measurable (fun ρ => ENNReal.ofReal ρ * Gρ ρ) :=
      (ENNReal.measurable_ofReal.comp measurable_id).mul hGρ_meas
    have hμ_pos : (volume (Set.Ioc r (2 * r))) ≠ 0 := by
      rw [Real.volume_Ioc]
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hf_int_ne_top : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ) * c) ≠ ∞ := by
      rw [lintegral_mul_const' _ _ (by
        rw [hc_def]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE_ne_top)]
      rw [hlog_int]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by rw [hc_def]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE_ne_top)
    have hstrict : ∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ) * c
        < ∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal ρ * Gρ ρ := by
      refine setLIntegral_strict_mono measurableSet_Ioc hμ_pos hg_meas hf_int_ne_top ?_
      refine ae_of_all _ (fun ρ hρ => ?_)
      have hρpos : 0 < ρ := lt_trans hr hρ.1
      have hkey := hcon ρ hρ
      -- multiply `c < ofReal(ρ²)·Gρ ρ` by `ofReal(1/ρ)`.
      have hmul : ENNReal.ofReal (1 / ρ) * c
          < ENNReal.ofReal (1 / ρ) * (ENNReal.ofReal (ρ ^ 2) * Gρ ρ) := by
        refine ENNReal.mul_lt_mul_right ?_ ENNReal.ofReal_ne_top hkey
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
      rw [show ENNReal.ofReal (1 / ρ) * (ENNReal.ofReal (ρ ^ 2) * Gρ ρ)
          = (ENNReal.ofReal (1 / ρ) * ENNReal.ofReal (ρ ^ 2)) * Gρ ρ by ring] at hmul
      rw [← ENNReal.ofReal_mul (by positivity)] at hmul
      rw [show (1 / ρ * ρ ^ 2 : ℝ) = ρ by
        have hne : ρ ≠ 0 := ne_of_gt hρpos
        field_simp] at hmul
      exact hmul
    -- Compute `∫_s f = E` and contradict `∫_s g ≤ E`.
    have hf_eq : (∫⁻ ρ in Set.Ioc r (2 * r), ENNReal.ofReal (1 / ρ) * c) = E := by
      rw [lintegral_mul_const' _ _ (by
        rw [hc_def]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE_ne_top)]
      rw [hlog_int, hc_def]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [show (Real.log 2 * (1 / Real.log 2) : ℝ) = 1 by field_simp]
      rw [ENNReal.ofReal_one, one_mul]
    rw [hf_eq] at hstrict
    exact absurd (lt_of_lt_of_le hstrict hannulus) (lt_irrefl E)
  -- Final assembly:  the selected `ρ` gives the conclusion.
  obtain ⟨ρ, hρmem, hρle⟩ := hselect
  obtain ⟨hρ1, hρ2⟩ := hρmem
  have hρpos : 0 < ρ := lt_trans hr hρ1
  refine ⟨ρ, ⟨hρ1.le, hρ2⟩, ?_⟩
  -- `R-integral` over `[0, 2π]` (nonneg).
  set Ireal : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (‖(fderiv ℝ g (circleMap x ρ θ)) 1‖ ^ 2
      + ‖(fderiv ℝ g (circleMap x ρ θ)) Complex.I‖ ^ 2) with hIreal_def
  have hIreal_nonneg : 0 ≤ Ireal := by
    rw [hIreal_def]
    apply intervalIntegral.integral_nonneg (by positivity)
    intro θ _; positivity
  -- `diam² ≤ (π/2)·ρ²·Ireal`.
  have hsm := hsmooth x ρ hρpos
  -- `Gρ ρ = ofReal Ireal`.
  have hGρ_eq : Gρ ρ = ENNReal.ofReal Ireal := hGρ_bridge ρ
  -- Convert to `ℝ≥0∞`.
  calc ENNReal.ofReal ((Metric.diam (g '' Metric.sphere x ρ)) ^ 2)
      ≤ ENNReal.ofReal ((Real.pi / 2) * ρ ^ 2 * Ireal) :=
        ENNReal.ofReal_le_ofReal hsm
    _ = ENNReal.ofReal (Real.pi / 2) * (ENNReal.ofReal (ρ ^ 2) * Gρ ρ) := by
        rw [hGρ_eq]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (Real.pi / 2) * c :=
        mul_le_mul_of_nonneg_left hρle (zero_le _)
    _ = ENNReal.ofReal (Real.pi / (2 * Real.log 2)) * E := by
        rw [hc_def, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [div_mul_eq_div_div]
        ring

/-- **Local W^{1,2} mollification with L²-gradient convergence (CL-C1).**

A continuous `f` with weak gradient `(gx, gy) ∈ L²_loc` admits, for every disc `closedBall x R` and
tolerance `ε > 0`, a `C¹` map `g` that is uniformly `ε`-close to `f` on the disc and whose classical
gradient is `L²`-close to `(gx, gy)` there (the energy of the gradient difference is `≤ ε`).

This is the mollification step `g = η_δ ⋆ (χ·f)` with a cutoff `χ`: the weak derivative commutes
with the convolution (`fderiv (η_δ ⋆ u) v = η_δ ⋆ (∂_v u)`), and `η_δ ⋆ h → h` in `L²` for `h ∈ L²`;
the cutoff localizes the only-`L²_loc` data to a genuine `L²` function. -/
theorem exists_smooth_approx_L2grad_local {f gx gy : ℂ → ℂ}
    (hfcont : Continuous f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ)
    (x : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧
      (∀ z ∈ Metric.closedBall x R, ‖g z - f z‖ ≤ ε) ∧
      (∫⁻ z in Metric.closedBall x R,
          energyDensity (fun w => (fderiv ℝ g w) 1 - gx w)
            (fun w => (fderiv ℝ g w) Complex.I - gy w) z) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨hgxw, hgyw⟩ := hwg
  -- ====================================================================
  -- Degenerate radii: `R < 0` gives an empty ball; `R = 0` a null set.
  -- ====================================================================
  rcases lt_or_ge 0 R with hRpos | hR0
  case inr =>
    -- `closedBall x R` is either empty (`R < 0`) or a single point (`R = 0`): take the constant
    -- map `f x`, whose `C¹`-ness and closeness are immediate, and whose energy integral is over a
    -- null set.
    refine ⟨fun _ => f x, contDiff_const, ?_, ?_⟩
    · intro z hz
      rcases lt_or_eq_of_le hR0 with hRneg | hR0'
      · simp only [Metric.closedBall_eq_empty.mpr hRneg, Set.mem_empty_iff_false] at hz
      · rw [Metric.mem_closedBall, hR0', dist_le_zero] at hz
        subst hz; simp [le_of_lt hε]
    · have hnull : volume (Metric.closedBall x R) = 0 := by
        rcases lt_or_eq_of_le hR0 with hRneg | hR0'
        · rw [Metric.closedBall_eq_empty.mpr hRneg]; simp
        · rw [hR0', Metric.closedBall_zero]; simp
      rw [setLIntegral_measure_zero _ _ hnull]; exact zero_le _
  -- ====================================================================
  -- The genuine case `R > 0`.
  -- ====================================================================
  -- (Cut) A smooth cutoff `χ` adapted to `ball x (R+1) ⊇ closedBall x R`, with compact support.
  obtain ⟨χ, hχ_cd, hχ_cs, hχ_nonneg, hχ_le1, hχ_one, hχ_supp, -⟩ :=
    exists_cutoff_ball x (R + 1) (by positivity)
  have hχ_cont : Continuous χ := hχ_cd.continuous
  -- The localized function `u = χ • f` and its weak partials `Gx`, `Gy`.
  set u : ℂ → ℂ := fun z => (χ z : ℝ) • f z with hu_def
  set Gx : ℂ → ℂ := fun z => (χ z : ℝ) • gx z + ((fderiv ℝ χ z) 1) • f z with hGx_def
  set Gy : ℂ → ℂ := fun z => (χ z : ℝ) • gy z + ((fderiv ℝ χ z) Complex.I) • f z with hGy_def
  -- Local integrability of `f`, `gx`, `gy` on `univ`.
  have hfloc : LocallyIntegrableOn f Set.univ := by
    rw [locallyIntegrableOn_univ]; exact hfcont.locallyIntegrable
  have hlocOfMemLp : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ → LocallyIntegrableOn h Set.univ := by
    intro h hmem
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hmem k (Set.subset_univ _) hk).mono_exponent (by norm_num))
  have hgxloc : LocallyIntegrableOn gx Set.univ := hlocOfMemLp hgx
  have hgyloc : LocallyIntegrableOn gy Set.univ := hlocOfMemLp hgy
  -- (Leibniz) `Gx`, `Gy` are the weak partials of `u` on `univ`.
  have hGxw : HasWeakDirDeriv 1 Gx u Set.univ :=
    hgxw.smul_smooth hχ_cd hfloc hgxloc
  have hGyw : HasWeakDirDeriv Complex.I Gy u Set.univ :=
    hgyw.smul_smooth hχ_cd hfloc hgyloc
  -- The compact set `K = tsupport χ` carrying the supports of `u`, `Gx`, `Gy`.
  set K : Set ℂ := tsupport χ with hK_def
  have hK_compact : IsCompact K := hχ_cs
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  -- Global a.e.-measurability of `gx`, `gy` (patched over the cover by closed balls).
  have haem_of_loc : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ → AEMeasurable h volume := by
    intro h hmem
    have hcover : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := iUnion_closedBall_nat 0
    have hh : AEMeasurable h (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) := by
      refine AEMeasurable.iUnion (fun n => ?_)
      exact ((hmem (Metric.closedBall 0 n) (Set.subset_univ _)
        (isCompact_closedBall 0 n)).aestronglyMeasurable).aemeasurable
    rwa [hcover, Measure.restrict_univ] at hh
  have hgx_aem : AEMeasurable gx volume := haem_of_loc hgx
  have hgy_aem : AEMeasurable gy volume := haem_of_loc hgy
  -- The fderiv of `χ` is continuous (smoothness `≥ 1`) and vanishes off `K`.
  have hdχ_cont : Continuous (fderiv ℝ χ) := hχ_cd.continuous_fderiv (by simp)
  have hdχ1_cont : Continuous (fun z => (fderiv ℝ χ z) 1) := hdχ_cont.clm_apply continuous_const
  have hdχI_cont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    hdχ_cont.clm_apply continuous_const
  have hχ_off : ∀ z, z ∉ K → χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (by rwa [← hK_def])
  have hdχ_off : ∀ z, z ∉ K → fderiv ℝ χ z = 0 := fun z hz =>
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (by rwa [← hK_def])
  -- Supports of `u`, `Gx`, `Gy` are inside `K`.
  have hu_supp : Function.support u ⊆ K := by
    intro z hz
    by_contra hzK
    refine hz ?_
    simp [hu_def, hχ_off z hzK]
  have hGx_supp : Function.support Gx ⊆ K := by
    intro z hz
    by_contra hzK
    refine hz ?_
    simp [hGx_def, hχ_off z hzK, hdχ_off z hzK]
  have hGy_supp : Function.support Gy ⊆ K := by
    intro z hz
    by_contra hzK
    refine hz ?_
    simp [hGy_def, hχ_off z hzK, hdχ_off z hzK]
  -- `u` is continuous; `Gx`, `Gy` are a.e.-strongly measurable.  Real-smul = multiplication.
  have hu_cont : Continuous u := by
    have heq : u = fun z => (χ z : ℂ) * f z := by
      funext z; simp only [hu_def, Complex.real_smul]
    rw [heq]; exact (Complex.continuous_ofReal.comp hχ_cont).mul hfcont
  have hu_aesm : AEStronglyMeasurable u volume := hu_cont.aestronglyMeasurable
  have hGx_aesm : AEStronglyMeasurable Gx volume := by
    have heq : Gx = fun z => (χ z : ℂ) * gx z + ((fderiv ℝ χ z) 1 : ℂ) * f z := by
      funext z; simp only [hGx_def, Complex.real_smul]
    rw [heq]
    refine (((Complex.continuous_ofReal.comp hχ_cont).aemeasurable.mul hgx_aem).add
      (((Complex.continuous_ofReal.comp hdχ1_cont).aemeasurable).mul
        hfcont.aemeasurable)).aestronglyMeasurable
  have hGy_aesm : AEStronglyMeasurable Gy volume := by
    have heq : Gy = fun z => (χ z : ℂ) * gy z + ((fderiv ℝ χ z) Complex.I : ℂ) * f z := by
      funext z; simp only [hGy_def, Complex.real_smul]
    rw [heq]
    refine (((Complex.continuous_ofReal.comp hχ_cont).aemeasurable.mul hgy_aem).add
      (((Complex.continuous_ofReal.comp hdχI_cont).aemeasurable).mul
        hfcont.aemeasurable)).aestronglyMeasurable
  -- Compact support of `u`, `Gx`, `Gy`.
  have hu_cs : HasCompactSupport u :=
    HasCompactSupport.of_support_subset_isCompact hK_compact hu_supp
  have hGx_cs : HasCompactSupport Gx :=
    HasCompactSupport.of_support_subset_isCompact hK_compact hGx_supp
  have hGy_cs : HasCompactSupport Gy :=
    HasCompactSupport.of_support_subset_isCompact hK_compact hGy_supp
  -- Finite measure of the restriction to the compact `K`.
  haveI hKfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK_compact.measure_lt_top⟩
  -- `gx`, `gy` are `L²` on the compact `K`.
  have hgxK : MemLp gx 2 (volume.restrict K) := hgx K (Set.subset_univ _) hK_compact
  have hgyK : MemLp gy 2 (volume.restrict K) := hgy K (Set.subset_univ _) hK_compact
  -- Continuous functions are bounded on the compact `K`: `f` and the two partials of `χ`.
  obtain ⟨Mf, hMf⟩ := hK_compact.exists_bound_of_continuousOn hfcont.continuousOn
  obtain ⟨Mχ1, hMχ1⟩ := hK_compact.exists_bound_of_continuousOn hdχ1_cont.continuousOn
  obtain ⟨MχI, hMχI⟩ := hK_compact.exists_bound_of_continuousOn hdχI_cont.continuousOn
  -- `u`, `Gx`, `Gy` are globally `L²`.
  have hu2 : MemLp u 2 volume := hu_cont.memLp_of_hasCompactSupport hu_cs
  -- Helper: a function supported in `K` and `L²` on `restrict K` is globally `L²`.
  have memLp_of_restrict : ∀ {h : ℂ → ℂ}, AEStronglyMeasurable h volume →
      Function.support h ⊆ K → MemLp h 2 (volume.restrict K) → MemLp h 2 volume := by
    intro h haesm hsupp hmemK
    refine ⟨haesm, ?_⟩
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    exact hmemK.2
  -- a.e.-strong-measurability of the four `ℝ • ℂ` pieces, via the multiplication form.
  have aesm_smul : ∀ {a : ℂ → ℝ} {b : ℂ → ℂ}, Continuous a → AEMeasurable b volume →
      AEStronglyMeasurable (fun z => a z • b z) (volume.restrict K) := by
    intro a b ha hb
    have heq : (fun z => a z • b z) = fun z => (a z : ℂ) * b z := by
      funext z; rw [Complex.real_smul]
    rw [heq]
    exact (((Complex.continuous_ofReal.comp ha).aemeasurable).mul hb).aestronglyMeasurable.restrict
  have hGx2 : MemLp Gx 2 volume := by
    refine memLp_of_restrict hGx_aesm hGx_supp ?_
    -- On `K`: `Gx = χ•gx + ∂₁χ•f`, the first dominated by `gx`, the second bounded.
    refine MemLp.add ?_ ?_
    · refine MemLp.of_le hgxK (aesm_smul hχ_cont hgx_aem) ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ_nonneg z], hχ_le1 z⟩
      nlinarith [norm_nonneg (gx z), this]
    · refine MemLp.of_bound (aesm_smul hdχ1_cont hfcont.aemeasurable) (Mχ1 * Mf) ?_
      rw [ae_restrict_iff' hK_meas]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |(fderiv ℝ χ z) 1| ≤ Mχ1 := by
        have := hMχ1 z hz; rwa [Real.norm_eq_abs] at this
      have h2 : ‖f z‖ ≤ Mf := hMf z hz
      have hM10 : 0 ≤ Mχ1 := le_trans (abs_nonneg _) h1
      exact mul_le_mul h1 h2 (norm_nonneg _) hM10
  have hGy2 : MemLp Gy 2 volume := by
    refine memLp_of_restrict hGy_aesm hGy_supp ?_
    refine MemLp.add ?_ ?_
    · refine MemLp.of_le hgyK (aesm_smul hχ_cont hgy_aem) ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ_nonneg z], hχ_le1 z⟩
      nlinarith [norm_nonneg (gy z), this]
    · refine MemLp.of_bound (aesm_smul hdχI_cont hfcont.aemeasurable) (MχI * Mf) ?_
      rw [ae_restrict_iff' hK_meas]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |(fderiv ℝ χ z) Complex.I| ≤ MχI := by
        have := hMχI z hz; rwa [Real.norm_eq_abs] at this
      have h2 : ‖f z‖ ≤ Mf := hMf z hz
      have hM10 : 0 ≤ MχI := le_trans (abs_nonneg _) h1
      exact mul_le_mul h1 h2 (norm_nonneg _) hM10
  -- Local integrability of `u`, `Gx`, `Gy` (consumed by the convolution-derivative lemma).
  have hu_li : MeasureTheory.LocallyIntegrable u := hu2.locallyIntegrable (by norm_num)
  have hGx_li : MeasureTheory.LocallyIntegrable Gx := hGx2.locallyIntegrable (by norm_num)
  have hGy_li : MeasureTheory.LocallyIntegrable Gy := hGy2.locallyIntegrable (by norm_num)
  -- ====================================================================
  -- (F) Mollification commutes with the weak directional derivative:
  --   `(fderiv (ρ ⋆ G) z) v = (ρ ⋆ ∂ᵥG) z`.
  -- ====================================================================
  have fderiv_conv : ∀ {F gv : ℂ → ℂ} {v : ℂ},
      HasWeakDirDeriv v gv F Set.univ →
      MeasureTheory.LocallyIntegrable F → MeasureTheory.LocallyIntegrable gv →
      ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      HasCompactSupport ρ → ∀ (z : ℂ),
        (fderiv ℝ (MeasureTheory.convolution ρ F
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
          = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro F gv v hv hF hgv ρ hρ_smooth hρ_supp z
    have _hgv := hgv
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
    have hρ_diff : Differentiable ℝ ρ :=
      hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
    have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
    have hderiv :
        HasFDerivAt (MeasureTheory.convolution ρ F L volume)
          (MeasureTheory.convolution (fderiv ℝ ρ) F (L.precompL ℂ) volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hF z
    rw [hderiv.fderiv]
    have hconvexists :
        MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) F z (L.precompL ℂ) volume :=
      (hdρ_supp.convolutionExists_left (L.precompL ℂ)
        (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hF) z
    rw [MeasureTheory.convolution_def,
        ContinuousLinearMap.integral_apply hconvexists.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
    have hcv :
        (∫ t, ((fderiv ℝ ρ t) v) • F (z - t) ∂volume)
          = ∫ w, ((fderiv ℝ ρ (z - w)) v) • F w ∂volume := by
      have hself := MeasureTheory.integral_sub_left_eq_self
        (fun t => ((fderiv ℝ ρ t) v) • F (z - t)) volume z
      simp only [sub_sub_cancel] at hself
      exact hself.symm
    refine hcv.trans ?_
    set φz : ℂ → ℝ := fun w => ρ (z - w) with hφz
    have hφz_fderiv : ∀ w, (fderiv ℝ φz w) v = -((fderiv ℝ ρ (z - w)) v) := by
      intro w
      have hsub : HasFDerivAt (fun w : ℂ => z - w) (-ContinuousLinearMap.id ℝ ℂ) w := by
        simpa using (hasFDerivAt_id w).const_sub z
      have hcomp : HasFDerivAt φz
          ((fderiv ℝ ρ (z - w)).comp (-ContinuousLinearMap.id ℝ ℂ)) w :=
        (hρ_diff (z - w)).hasFDerivAt.comp w hsub
      rw [hcomp.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
    have hint_eq :
        (∫ w, ((fderiv ℝ ρ (z - w)) v) • F w ∂volume)
          = -∫ w, ((fderiv ℝ φz w) v) • F w ∂volume := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      change ((fderiv ℝ ρ (z - w)) v) • F w = -(((fderiv ℝ φz w) v) • F w)
      rw [hφz_fderiv w]
      rw [show (-(fderiv ℝ ρ (z - w)) v) • F w = -(((fderiv ℝ ρ (z - w)) v) • F w)
        from neg_smul _ _, neg_neg]
    rw [hint_eq]
    have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
      hρ_smooth.comp (contDiff_const.sub contDiff_id)
    have hφz_supp : HasCompactSupport φz :=
      hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
    have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
    rw [hwd, neg_neg]
    rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
        (fun t => (L (ρ t)) (gv (z - t))) volume z]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
    rfl
  -- ====================================================================
  -- (C) `L²` mollification convergence `‖ρ_n ⋆ G - G‖₂ → 0` for `G ∈ L²`.
  -- ====================================================================
  have conv_tendsto : ∀ {G : ℂ → ℂ},
      MemLp G 2 volume → ∀ (φ : ℕ → ContDiffBump (0 : ℂ)),
      Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) G
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - G) 2 volume)
        Filter.atTop (nhds 0) := by
    intro G hG φ hφrout
    set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
      G (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
    have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
        Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) h
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
          Filter.atTop (nhds 0) := by
      intro h hh_supp hh_smooth
      obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
      have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
      set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
      have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
      have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
      have hKfin' : volume Kset < ⊤ := hKcompact.measure_lt_top
      have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
      set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
        h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
      have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
        HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
        ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
      have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
        intro n x
        set ρ := (φ n).normed volume with hρ
        have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
        rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
        calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
            ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t, ρ t * M ∂volume := by
              have hint : Integrable ρ volume :=
                ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                  ((φ n).hasCompactSupport_normed)
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
              refine Filter.Eventually.of_forall (fun t => ?_)
              simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
              exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
          _ = (∫ t, ρ t ∂volume) * M := by rw [integral_mul_const]
          _ = M := by rw [(φ n).integral_normed]; ring
      have hMh : ∀ y, ‖h y‖ ≤ M := hM
      have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
        have hev : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
          have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
          filter_upwards [this] with n hn using hn
        filter_upwards [hev] with n hrout1
        have haddsub : Metric.closedBall (0 : ℂ) (φ n).rOut + tsupport h ⊆ Kset := by
          intro z hz
          obtain ⟨a, ha, b, hb, rfl⟩ := hz
          rw [Metric.mem_closedBall, dist_zero_right] at ha
          refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
          rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
        have hsub := MeasureTheory.support_convolution_subset (μ := volume)
          (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
          (f := (φ n).normed volume) (g := h)
        refine hsub.trans (le_trans ?_ haddsub)
        apply Set.add_subset_add _ (subset_tsupport h)
        intro z hz
        have h1 : z ∈ tsupport ((φ n).normed volume) := subset_tsupport _ hz
        rwa [(φ n).tsupport_normed_eq] at h1
      haveI : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
        constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin'
      set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
      have hrestrict : ∀ᶠ n in Filter.atTop,
          eLpNorm (D n) 2 volume = eLpNorm (D n) 2 (volume.restrict Kset) := by
        filter_upwards [hsupp_in_K] with n hn
        have hDsupp : Function.support (D n) ⊆ Kset := by
          intro x hx
          simp only [hD, Pi.sub_apply, Function.mem_support, ne_eq] at hx
          by_contra hxK
          have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
          have h2 : h x = 0 := Function.notMem_support.mp
            (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
          rw [h1, h2, sub_zero] at hx; exact hx rfl
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
      have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Kset))
          Filter.atTop (nhds 0) := by
        have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
          refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
            (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
          refine ⟨(M.toNNReal + 1), fun n => ?_⟩
          have hempty : {x | (M.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
            have hb' : ‖Cn n x‖₊ ≤ M.toNNReal := by
              rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM0]; exact hCnbd n x
            exact lt_of_le_of_lt hb' (by simp)
          rw [hempty, Set.indicator_empty]; simp
        have hhmem : MemLp h 2 (volume.restrict Kset) :=
          MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
            (Filter.Eventually.of_forall hMh)
        exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
          (Filter.Eventually.of_forall hptwise)
      exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
    have hP2 : ∀ (w : ℂ → ℂ), MemLp w 2 volume → ∀ (ε : ℝ),
        eLpNorm w 2 volume ≤ ENNReal.ofReal ε → ∀ n,
          eLpNorm (MeasureTheory.convolution ((φ n).normed volume) w
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
      intro w hw ε hclose n
      set ρc : ℂ → ℂ := fun z => (((φ n).normed volume z : ℝ) : ℂ) with hρc
      have hconv_eq : MeasureTheory.convolution ((φ n).normed volume) w
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          = MeasureTheory.convolution ρc w (ContinuousLinearMap.mul ℂ ℂ) volume := by
        funext xx
        rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
        exact (Complex.real_smul).symm
      rw [hconv_eq]
      have hρc_memLp : MemLp ρc 1 volume := by
        have hcont : Continuous ρc :=
          Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
        have hsupp : HasCompactSupport ρc :=
          ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
        exact hcont.memLp_of_hasCompactSupport hsupp
      have hρc_norm : eLpNorm ρc 1 volume = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hint : Integrable ((φ n).normed volume) volume :=
          ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
            ((φ n).hasCompactSupport_normed)
        have hnn : 0 ≤ᵐ[volume] (φ n).normed volume :=
          Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
        calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
            = ∫⁻ z, ENNReal.ofReal ((φ n).normed volume z) ∂volume := by
              refine lintegral_congr (fun z => ?_)
              rw [hρc,
                show ‖(((φ n).normed volume z : ℝ) : ℂ)‖ₑ
                    = ‖(φ n).normed volume z‖ₑ from by
                  rw [← enorm_norm, Complex.norm_real, enorm_norm],
                Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
          _ = ENNReal.ofReal (∫ z, (φ n).normed volume z ∂volume) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ = 1 := by rw [(φ n).integral_normed]; simp
      calc eLpNorm (MeasureTheory.convolution ρc w (ContinuousLinearMap.mul ℂ ℂ)
              volume) 2 volume
          ≤ eLpNorm ρc 1 volume * eLpNorm w 2 volume :=
            eLpNorm_convolution_le hρc_memLp hw
        _ = eLpNorm w 2 volume := by rw [hρc_norm, one_mul]
        _ ≤ ENNReal.ofReal ε := hclose
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε'
    by_cases htop : ε = ⊤
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [htop]; exact le_top
    set δ : ℝ := ε.toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hε'.ne' htop
    have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
    obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hG.exist_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ε := δ / 3) (by positivity)
    have hh_memLp : MemLp hh 2 volume :=
      hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
    have hgh_memLp : MemLp (G - hh) 2 volume := hG.sub hh_memLp
    have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      hP2 (G - hh) hgh_memLp (δ / 3) hh_close
    have hP3ev : ∀ᶠ n in Filter.atTop,
        eLpNorm (MeasureTheory.convolution ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
        (ENNReal.ofReal_pos.mpr (by positivity)))
    have hdecomp : ∀ n, Cg n - G = MeasureTheory.convolution ((φ n).normed volume)
          (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - G) := by
      intro n
      have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed volume) (G - hh)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous ?_
        exact (hG.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
      have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed volume)
            (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        rw [hCg]; simp only
        rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
        congr 1; abel
      rw [hsplit]; abel
    filter_upwards [hP3ev] with n hn3
    rw [hdecomp n]
    have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) volume :=
      (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        ((hG.locallyIntegrable (by norm_num)).sub
          hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
        volume - hh) volume :=
      ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (hh - G) volume :=
      (hh_memLp.sub hG).1
    have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - G)) 2
          volume
        ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
      refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
      refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
      · exact add_le_add (hP2gh n) hn3
      · rw [eLpNorm_sub_comm]; exact hh_close
    refine le_trans hkey ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
    apply le_of_eq; congr 1; ring
  -- ====================================================================
  -- On the closed ball `B = closedBall x R` the cutoff is identically `1`, hence `u = f`,
  -- `Gx = gx` and `Gy = gy` there.
  -- ====================================================================
  set B : Set ℂ := Metric.closedBall x R with hB_def
  have hB_sub : B ⊆ Metric.ball x (R + 1) := by
    refine Metric.closedBall_subset_ball ?_; linarith
  have hχ1_on_ball : Set.EqOn χ (fun _ => (1 : ℝ)) (Metric.ball x (R + 1)) :=
    fun z hz => hχ_one z hz
  -- On the open ball `χ` is locally constant `1`, so its Fréchet derivative vanishes there.
  have hdχ_zero_on_ball : ∀ z ∈ Metric.ball x (R + 1), fderiv ℝ χ z = 0 := by
    intro z hz
    have heqf : χ =ᶠ[nhds z] (fun _ => (1 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz) hχ1_on_ball
    rw [heqf.fderiv_eq]; simp
  -- `Gx = gx` and `Gy = gy` on `B`.
  have hGx_on_B : ∀ z ∈ B, Gx z = gx z := by
    intro z hz
    have hzb := hB_sub hz
    simp [hGx_def, hχ_one z hzb, hdχ_zero_on_ball z hzb]
  have hGy_on_B : ∀ z ∈ B, Gy z = gy z := by
    intro z hz
    have hzb := hB_sub hz
    simp [hGy_def, hχ_one z hzb, hdχ_zero_on_ball z hzb]
  have hu_on_B : ∀ z ∈ B, u z = f z := by
    intro z hz
    simp [hu_def, hχ_one z (hB_sub hz)]
  -- ====================================================================
  -- Choose the mollifier radius.  Sequence `φ₀ n` with `rOut = 2/(n+2) → 0`.
  -- ====================================================================
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- `u` is uniformly continuous (continuous with compact support), so the mollified family is
  -- uniformly `ε`-close once the support radius is small.
  have hu_uc : UniformContinuous u := hu_cs.uniformContinuous_of_continuous hu_cont
  obtain ⟨δu, hδu_pos, hδu⟩ : ∃ δ > 0, ∀ z z' : ℂ, dist z z' < δ → dist (u z) (u z') ≤ ε := by
    rw [Metric.uniformContinuous_iff] at hu_uc
    obtain ⟨δ, hδpos, hδ⟩ := hu_uc ε hε
    exact ⟨δ, hδpos, fun z z' hzz' => (hδ hzz').le⟩
  -- (Uniform) For every mollifier of `rOut < δu`, the mollification is `ε`-close to `u` everywhere.
  have hclose_of_rout : ∀ n, (φ₀ n).rOut < δu →
      ∀ z, ‖(MeasureTheory.convolution ((φ₀ n).normed volume) u
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) z - u z‖ ≤ ε := by
    intro n hn z
    have hsupp_ball : Function.support ((φ₀ n).normed volume) ⊆ Metric.ball (0 : ℂ) δu := by
      rw [(φ₀ n).support_normed_eq]
      exact Metric.ball_subset_ball hn.le
    have hgz : ∀ y ∈ Metric.ball z δu, dist (u y) (u z) ≤ ε := by
      intro y hy
      rw [Metric.mem_ball] at hy
      exact hδu y z hy
    have := dist_convolution_le (le_of_lt hε) hsupp_ball ((φ₀ n).nonneg_normed)
      ((φ₀ n).integral_normed) hu_cont.aestronglyMeasurable hgz
    rwa [dist_eq_norm] at this
  -- (L²) The gradient mollifications converge to `Gx`, `Gy` in `L²`.
  have hconvGx := conv_tendsto hGx2 φ₀ hφ₀rout
  have hconvGy := conv_tendsto hGy2 φ₀ hφ₀rout
  -- Pick a threshold `δ` for the `L²` gradient differences with `2 δ² ≤ ε`.
  set δ : ℝ := Real.sqrt (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδ_sq : δ ^ 2 = ε / 2 := Real.sq_sqrt (by positivity)
  -- Eventually-small `L²` gradient differences and small `rOut`.
  have hevGx : ∀ᶠ n in Filter.atTop, eLpNorm
      (MeasureTheory.convolution ((φ₀ n).normed volume) Gx
        (ContinuousLinearMap.lsmul ℝ ℝ) volume - Gx) 2 volume ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.mp hconvGx (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ_pos)
  have hevGy : ∀ᶠ n in Filter.atTop, eLpNorm
      (MeasureTheory.convolution ((φ₀ n).normed volume) Gy
        (ContinuousLinearMap.lsmul ℝ ℝ) volume - Gy) 2 volume ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.mp hconvGy (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ_pos)
  have hevRout : ∀ᶠ n in Filter.atTop, (φ₀ n).rOut < δu :=
    hφ₀rout.eventually (eventually_lt_nhds hδu_pos)
  obtain ⟨N, hNGx, hNGy, hNrout⟩ := (hevGx.and (hevGy.and hevRout)).exists
  -- ====================================================================
  -- The output map `g = ρ_N ⋆ u`.
  -- ====================================================================
  set ρ : ℂ → ℝ := (φ₀ N).normed volume with hρdef
  set g : ℂ → ℂ := MeasureTheory.convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgdef
  have hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := (φ₀ N).contDiff_normed
  have hρ_cs : HasCompactSupport ρ := (φ₀ N).hasCompactSupport_normed
  -- `g` is `C¹`.
  have hg_contDiff : ContDiff ℝ 1 g := by
    refine HasCompactSupport.contDiff_convolution_left _ hρ_cs ?_ hu_li
    exact hρ_smooth.of_le (by exact_mod_cast le_top)
  -- The two directional derivatives of `g` are the mollifications of `Gx`, `Gy`.
  have hdx : (fun z => (fderiv ℝ g z) 1)
      = MeasureTheory.convolution ρ Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext z; exact fderiv_conv hGxw hu_li hGx_li hρ_smooth hρ_cs z
  have hdy : (fun z => (fderiv ℝ g z) Complex.I)
      = MeasureTheory.convolution ρ Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext z; exact fderiv_conv hGyw hu_li hGy_li hρ_smooth hρ_cs z
  refine ⟨g, hg_contDiff, ?_, ?_⟩
  · -- (Closeness) On `B = closedBall x R`, `g` is `ε`-close to `f` (via `u = f` there).
    intro z hz
    have h1 : ‖g z - u z‖ ≤ ε := hclose_of_rout N hNrout z
    rw [hu_on_B z hz] at h1
    exact h1
  · -- (Energy) The gradient energy of `g - (gx, gy)` over `B`.
    -- On `B`, `gx = Gx`, `gy = Gy`, so the integrand is `‖ρ⋆Gx - Gx‖² + ‖ρ⋆Gy - Gy‖²`.
    set Dx : ℂ → ℂ := fun w =>
      MeasureTheory.convolution ρ Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume w - Gx w with hDx_def
    set Dy : ℂ → ℂ := fun w =>
      MeasureTheory.convolution ρ Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume w - Gy w with hDy_def
    -- Pointwise rewrite of the integrand on `B`.
    have hpt : ∀ z ∈ B,
        energyDensity (fun w => (fderiv ℝ g w) 1 - gx w)
          (fun w => (fderiv ℝ g w) Complex.I - gy w) z
        = energyDensity Dx Dy z := by
      intro z hz
      simp only [energyDensity, hDx_def, hDy_def]
      rw [show (fderiv ℝ g z) 1 = MeasureTheory.convolution ρ Gx
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z from congrFun hdx z,
          show (fderiv ℝ g z) Complex.I = MeasureTheory.convolution ρ Gy
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z from congrFun hdy z,
          hGx_on_B z hz, hGy_on_B z hz]
    -- Rewrite the integral over `B`.
    rw [setLIntegral_congr_fun (measurableSet_closedBall) (fun z hz => hpt z hz)]
    -- `energyDensity Dx Dy = ‖Dx‖² + ‖Dy‖²`; split the integral.
    have hDx_aem : AEMeasurable (fun z => (‖Dx z‖₊ : ℝ≥0∞) ^ 2) volume := by
      have : AEStronglyMeasurable Dx volume := by
        refine (HasCompactSupport.continuous_convolution_left _ hρ_cs hρ_smooth.continuous
          hGx_li).aestronglyMeasurable.sub hGx_aesm
      exact (this.aemeasurable.enorm.pow_const 2).congr
        (by filter_upwards with z using by rw [enorm_eq_nnnorm])
    -- The energy splits and each summand is bounded by the `L²` norm of the difference, squared.
    have hsplit : (∫⁻ z in B, energyDensity Dx Dy z)
        = (∫⁻ z in B, (‖Dx z‖₊ : ℝ≥0∞) ^ 2) + ∫⁻ z in B, (‖Dy z‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [energyDensity]
      exact lintegral_add_left' hDx_aem.restrict _
    rw [hsplit]
    -- Bound each restricted integral by the global `L²` norm squared.
    have hbound : ∀ (D : ℂ → ℂ), eLpNorm D 2 volume ≤ ENNReal.ofReal δ →
        (∫⁻ z in B, (‖D z‖₊ : ℝ≥0∞) ^ 2) ≤ (ENNReal.ofReal δ) ^ 2 := by
      intro D hD
      have hle : (∫⁻ z in B, (‖D z‖₊ : ℝ≥0∞) ^ 2) ≤ ∫⁻ z, (‖D z‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        setLIntegral_le_lintegral _ _
      refine le_trans hle ?_
      have heq : (∫⁻ z, (‖D z‖₊ : ℝ≥0∞) ^ 2 ∂volume) = (eLpNorm D 2 volume) ^ 2 := by
        have hbase : (∫⁻ z, ‖D z‖ₑ ^ (2 : ℝ) ∂volume) = eLpNorm' D 2 volume ^ (2 : ℝ) :=
          lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)
        have hlhs : (∫⁻ z, (‖D z‖₊ : ℝ≥0∞) ^ 2 ∂volume)
            = ∫⁻ z, ‖D z‖ₑ ^ (2 : ℝ) ∂volume := by
          refine lintegral_congr (fun z => ?_)
          rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖D z‖₊ : ℝ≥0∞) 2]; norm_num
        rw [hlhs, hbase, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
          ← ENNReal.rpow_natCast (eLpNorm' D (ENNReal.toReal 2) volume) 2]
        norm_num
      rw [heq]
      exact pow_le_pow_left' hD 2
    -- Assemble: each summand `≤ (ofReal δ)²`, and `2 δ² ≤ ε`.
    refine le_trans (add_le_add (hbound Dx hNGx) (hbound Dy hNGy)) ?_
    rw [← two_mul]
    rw [show (ENNReal.ofReal δ) ^ 2 = ENNReal.ofReal (δ ^ 2) by
      rw [← ENNReal.ofReal_pow hδ_pos.le]]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hδ_sq]; ring_nf; linarith

/-- **Continuity of the image-circle diameter in the radius (CL-C2).**

For a continuous `f`, the map `ρ ↦ diam (f '' sphere x ρ)` is continuous on `ρ > 0`. (The sphere
varies continuously in the Hausdorff metric, `f` is uniformly continuous on compacts, and `diam` is
`1`-Lipschitz for the Hausdorff distance on compacta.) Used to pass the radius selected for the
mollified maps to the limit. -/
theorem continuousOn_diam_image_sphere {f : ℂ → ℂ} (hfcont : Continuous f) (x : ℂ) :
    ContinuousOn (fun ρ : ℝ => Metric.diam (f '' Metric.sphere x ρ)) (Set.Ioi 0) := by
  -- Parametrize the circle by the angle `θ ∈ [0, 2π]` via `circleMap`, write the diameter of the
  -- image as the supremum of pairwise distances `Ψ ρ p`, and conclude by the parametric-supremum
  -- continuity lemma `IsCompact.continuous_sSup`.
  set K : Set (ℝ × ℝ) := (Set.Icc 0 (2 * Real.pi)) ×ˢ (Set.Icc 0 (2 * Real.pi)) with hK_def
  -- `Ψ ρ p = dist (f (circleMap x ρ p.1)) (f (circleMap x ρ p.2))`.
  set Ψ : ℝ → ℝ × ℝ → ℝ :=
    fun ρ p => dist (f (circleMap x ρ p.1)) (f (circleMap x ρ p.2)) with hΨ_def
  -- `K` is compact and nonempty.
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hK_compact : IsCompact K := (isCompact_Icc).prod (isCompact_Icc)
  have hK_ne : K.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    exact ⟨Set.left_mem_Icc.mpr hpi, Set.left_mem_Icc.mpr hpi⟩
  -- Joint continuity of `↿Ψ : ℝ × (ℝ × ℝ) → ℝ`.  The map `(ρ, θ) ↦ x + ρ·exp(θ·I)` is continuous.
  have hcircle : Continuous (fun q : ℝ × ℝ => circleMap x q.1 q.2) := by
    simp only [circleMap]
    refine continuous_const.add ?_
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp continuous_fst
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hΨ_cont : Continuous (Function.uncurry Ψ) := by
    -- `↿Ψ (ρ, p) = dist (f (circleMap x ρ p.1)) (f (circleMap x ρ p.2))`.
    have harg1 : Continuous (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1)) :=
      continuous_fst.prodMk (continuous_snd.fst)
    have harg2 : Continuous (fun q : ℝ × ℝ × ℝ => (q.1, q.2.2)) :=
      continuous_fst.prodMk (continuous_snd.snd)
    have hfst : Continuous (fun q : ℝ × ℝ × ℝ => f (circleMap x q.1 q.2.1)) :=
      hfcont.comp (hcircle.comp harg1)
    have hsnd : Continuous (fun q : ℝ × ℝ × ℝ => f (circleMap x q.1 q.2.2)) :=
      hfcont.comp (hcircle.comp harg2)
    exact hfst.dist hsnd
  -- For each `ρ > 0`, the diameter of the image equals `sSup (Ψ ρ '' K)`.
  have hEq : Set.EqOn (fun ρ : ℝ => Metric.diam (f '' Metric.sphere x ρ))
      (fun ρ : ℝ => sSup (Ψ ρ '' K)) (Set.Ioi 0) := by
    intro ρ hρ
    simp only [Set.mem_Ioi] at hρ
    -- The sphere is the image of `[0, 2π]` under `circleMap x ρ`.
    have hsphere : Metric.sphere x ρ = circleMap x ρ '' Set.Icc 0 (2 * Real.pi) := by
      have hper := (periodic_circleMap x ρ).image_Icc
        (show (0 : ℝ) < 2 * Real.pi by positivity) 0
      rw [zero_add, range_circleMap, abs_of_pos hρ] at hper
      exact hper.symm
    -- Image of the sphere under `f` is the image of `[0, 2π]` under `θ ↦ f (circleMap x ρ θ)`.
    have himg : f '' Metric.sphere x ρ
        = (fun θ => f (circleMap x ρ θ)) '' Set.Icc 0 (2 * Real.pi) := by
      rw [hsphere, Set.image_image]
    -- `Ψ ρ` is continuous (a slice of `↿Ψ`).
    have hΨρ_cont : Continuous (Ψ ρ) := by
      have : (Ψ ρ) = (fun p : ℝ × ℝ => Function.uncurry Ψ (ρ, p)) := rfl
      rw [this]
      exact hΨ_cont.comp (continuous_const.prodMk continuous_id)
    -- `Ψ ρ '' K` is nonempty and bounded above (continuous image of a compact set).
    have hΨimg_ne : (Ψ ρ '' K).Nonempty := hK_ne.image _
    have hΨimg_bdd : BddAbove (Ψ ρ '' K) :=
      hK_compact.bddAbove_image hΨρ_cont.continuousOn
    -- The image of the sphere under `f` is bounded (continuous image of a compact set).
    have hsphere_compact : IsCompact (Metric.sphere x ρ) := isCompact_sphere x ρ
    have himg_bounded : Bornology.IsBounded (f '' Metric.sphere x ρ) :=
      (hsphere_compact.image hfcont).isBounded
    -- `sSup (Ψ ρ '' K) ≥ 0`.
    have hsup_nonneg : 0 ≤ sSup (Ψ ρ '' K) := by
      obtain ⟨a, p, hp, hav⟩ := hΨimg_ne
      have hmem : a ∈ Ψ ρ '' K := ⟨p, hp, hav⟩
      exact le_trans (by rw [← hav]; exact dist_nonneg) (le_csSup hΨimg_bdd hmem)
    refine le_antisymm ?_ ?_
    · -- `diam ≤ sSup (Ψ ρ '' K)`.
      refine Metric.diam_le_of_forall_dist_le hsup_nonneg ?_
      rw [himg]
      rintro u ⟨θ₁, hθ₁, rfl⟩ v ⟨θ₂, hθ₂, rfl⟩
      refine le_csSup hΨimg_bdd ?_
      exact ⟨(θ₁, θ₂), ⟨hθ₁, hθ₂⟩, rfl⟩
    · -- `sSup (Ψ ρ '' K) ≤ diam`.
      refine csSup_le hΨimg_ne ?_
      rintro w ⟨⟨θ₁, θ₂⟩, ⟨hθ₁, hθ₂⟩, rfl⟩
      simp only [hΨ_def]
      refine Metric.dist_le_diam_of_mem himg_bounded ?_ ?_
      · rw [himg]; exact ⟨θ₁, hθ₁, rfl⟩
      · rw [himg]; exact ⟨θ₂, hθ₂, rfl⟩
  -- Conclude: the parametric supremum is continuous, and it agrees with the diameter on `Ioi 0`.
  refine (IsCompact.continuous_sSup hK_compact hΨ_cont).continuousOn.congr hEq

/-- **Courant–Lebesgue small-energy circle (CL) — the analytic core.**

For a continuous `f` with weak gradient `(gx, gy) ∈ L²_loc`, there is a universal constant `C₀`
(value `π / (2 log 2)`) such that for every centre `x` and radius `r > 0` there is a radius
`ρ ∈ [r, 2r]` whose image circle is small in diameter relative to the Dirichlet energy of the
surrounding disc:
`diam (f '' sphere x ρ)² ≤ C₀ · ∫_{closedBall x (2r)} (‖gx‖² + ‖gy‖²)`.

Assembled from `courantLebesgue_smooth` (CL-smooth) applied to a sequence of mollified maps
(`exists_smooth_approx_L2grad_local`, CL-C1), passing the selected radius to the limit via
`continuousOn_diam_image_sphere` (CL-C2) and `L²`-convergence of the mollified energy. -/
theorem courantLebesgue_smallEnergyCircle {f gx gy : ℂ → ℂ}
    (hfcont : Continuous f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∃ ρ ∈ Set.Icc r (2 * r),
        ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2)
          ≤ ENNReal.ofReal C₀ * ∫⁻ z in Metric.closedBall x (2 * r), energyDensity gx gy z := by
  classical
  set C₀ : ℝ := Real.pi / (2 * Real.log 2) with hC₀_def
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC₀_nonneg : 0 ≤ C₀ := by
    rw [hC₀_def]; positivity
  refine ⟨C₀, hC₀_nonneg, ?_⟩
  intro x r hr
  set B : Set ℂ := Metric.closedBall x (2 * r) with hB_def
  have hB_compact : IsCompact B := by rw [hB_def]; exact isCompact_closedBall x (2 * r)
  -- The target energy and its `L²`-pieces.
  set E : ℝ≥0∞ := ∫⁻ z in B, energyDensity gx gy z with hE_def
  -- `gx, gy ∈ L²(B)` (compact ⊆ univ), giving finite `L²` norms and a.e.-strong measurability.
  have hgx_mem : MemLp gx 2 (volume.restrict B) :=
    hgx B (Set.subset_univ _) hB_compact
  have hgy_mem : MemLp gy 2 (volume.restrict B) :=
    hgy B (Set.subset_univ _) hB_compact
  -- ============================================================================================
  -- A universal helper: for any `h : ℂ → ℂ`, `∫⁻_B ‖h‖₊² = (eLpNorm h 2 (volume.restrict B))²`.
  -- ============================================================================================
  have hsq : ∀ h : ℂ → ℂ,
      (∫⁻ z in B, (‖h z‖₊ : ℝ≥0∞) ^ 2)
        = (eLpNorm h 2 (volume.restrict B)) ^ 2 := by
    intro h
    have hbase : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(volume.restrict B))
        = eLpNorm' h 2 (volume.restrict B) ^ (2 : ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)
    have hlhs : (∫⁻ z, (‖h z‖₊ : ℝ≥0∞) ^ 2 ∂(volume.restrict B))
        = ∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(volume.restrict B) := by
      refine lintegral_congr (fun z => ?_)
      rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖h z‖₊ : ℝ≥0∞) 2]; norm_num
    rw [hlhs, hbase, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      ← ENNReal.rpow_natCast (eLpNorm' h (ENNReal.toReal 2) (volume.restrict B)) 2]
    norm_num
  -- `E` as a sum of squared `L²` norms.
  set Nx : ℝ≥0∞ := eLpNorm gx 2 (volume.restrict B) with hNx_def
  set Ny : ℝ≥0∞ := eLpNorm gy 2 (volume.restrict B) with hNy_def
  have hNx_lt : Nx < ⊤ := hgx_mem.eLpNorm_lt_top
  have hNy_lt : Ny < ⊤ := hgy_mem.eLpNorm_lt_top
  have hE_eq : E = Nx ^ 2 + Ny ^ 2 := by
    rw [hE_def]
    have hsplit : (∫⁻ z in B, energyDensity gx gy z)
        = (∫⁻ z in B, (‖gx z‖₊ : ℝ≥0∞) ^ 2) + ∫⁻ z in B, (‖gy z‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [energyDensity]
      refine lintegral_add_left' ?_ _
      exact (hgx_mem.aestronglyMeasurable.aemeasurable.enorm.pow_const 2).congr
        (by filter_upwards with z using by rw [enorm_eq_nnnorm])
    rw [hsplit, hsq gx, hsq gy, hNx_def, hNy_def]
  -- ============================================================================================
  -- Build a sequence of `C¹` approximations `G n` with `L²`-gradient error `≤ 1/(n+1)`.
  -- ============================================================================================
  have hchoose : ∀ n : ℕ, ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧
      (∀ z ∈ B, ‖g z - f z‖ ≤ 1 / (n + 1 : ℝ)) ∧
      (∫⁻ z in B, energyDensity (fun w => (fderiv ℝ g w) 1 - gx w)
          (fun w => (fderiv ℝ g w) Complex.I - gy w) z) ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have hεpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    obtain ⟨g, hgcd, hgclose, hgen⟩ :=
      exists_smooth_approx_L2grad_local hfcont hwg hgx hgy x (2 * r) hεpos
    exact ⟨g, hgcd, hgclose, hgen⟩
  choose G hG_cd hG_close hG_energy using hchoose
  -- Partial derivatives of `G n`.
  set Px : ℕ → ℂ → ℂ := fun n w => (fderiv ℝ (G n) w) 1 with hPx_def
  set Py : ℕ → ℂ → ℂ := fun n w => (fderiv ℝ (G n) w) Complex.I with hPy_def
  -- Continuity of the partials (since each `G n` is `C¹`).
  have hPx_cont : ∀ n, Continuous (Px n) := by
    intro n
    exact (hG_cd n).continuous_fderiv one_ne_zero |>.clm_apply continuous_const
  have hPy_cont : ∀ n, Continuous (Py n) := by
    intro n
    exact (hG_cd n).continuous_fderiv one_ne_zero |>.clm_apply continuous_const
  -- `L²` norms of the partials and of the gradient errors on `B`.
  set Nxn : ℕ → ℝ≥0∞ := fun n => eLpNorm (Px n) 2 (volume.restrict B) with hNxn_def
  set Nyn : ℕ → ℝ≥0∞ := fun n => eLpNorm (Py n) 2 (volume.restrict B) with hNyn_def
  set Dxn : ℕ → ℝ≥0∞ :=
    fun n => eLpNorm (fun w => Px n w - gx w) 2 (volume.restrict B) with hDxn_def
  set Dyn : ℕ → ℝ≥0∞ :=
    fun n => eLpNorm (fun w => Py n w - gy w) 2 (volume.restrict B) with hDyn_def
  -- The smooth energy on `B`.
  set En : ℕ → ℝ≥0∞ :=
    fun n => ∫⁻ z in B, energyDensity (Px n) (Py n) z with hEn_def
  have hEn_eq : ∀ n, En n = Nxn n ^ 2 + Nyn n ^ 2 := by
    intro n
    simp only [hEn_def]
    have hsplit : (∫⁻ z in B, energyDensity (Px n) (Py n) z)
        = (∫⁻ z in B, (‖Px n z‖₊ : ℝ≥0∞) ^ 2) + ∫⁻ z in B, (‖Py n z‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [energyDensity]
      refine lintegral_add_left' ?_ _
      exact ((hPx_cont n).aemeasurable.enorm.pow_const 2).congr
        (by filter_upwards with z using by rw [enorm_eq_nnnorm])
    rw [hsplit, hsq (Px n), hsq (Py n), hNxn_def, hNyn_def]
  -- The gradient-error energy on `B` bounds each squared error norm.
  have hDxy_bound : ∀ n, Dxn n ^ 2 ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
      Dyn n ^ 2 ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have hsplit : (∫⁻ z in B, energyDensity (fun w => Px n w - gx w)
          (fun w => Py n w - gy w) z)
        = Dxn n ^ 2 + Dyn n ^ 2 := by
      simp only [energyDensity, hDxn_def, hDyn_def]
      rw [← hsq (fun w => Px n w - gx w), ← hsq (fun w => Py n w - gy w)]
      refine lintegral_add_left' ?_ _
      exact (((hPx_cont n).aemeasurable.sub
        hgx_mem.aestronglyMeasurable.aemeasurable).enorm.pow_const 2).congr
        (by filter_upwards with z using by rw [enorm_eq_nnnorm])
    have htot : Dxn n ^ 2 + Dyn n ^ 2 ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      rw [← hsplit]; exact hG_energy n
    exact ⟨le_trans (self_le_add_right _ _) htot, le_trans (self_le_add_left _ _) htot⟩
  -- ============================================================================================
  -- Apply CL-smooth to each `G n` to select a radius `ρ n ∈ [r, 2r]`.
  -- ============================================================================================
  have hCL : ∀ n, ∃ ρ ∈ Set.Icc r (2 * r),
      ENNReal.ofReal ((Metric.diam (G n '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal C₀ * En n := by
    intro n
    obtain ⟨ρ, hρmem, hρle⟩ := courantLebesgue_smooth (hG_cd n) x hr
    refine ⟨ρ, hρmem, ?_⟩
    change ENNReal.ofReal ((Metric.diam (G n '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal C₀ * (∫⁻ z in B, energyDensity (Px n) (Py n) z)
    rw [hC₀_def]
    exact hρle
  choose ρ hρ_mem hρ_le using hCL
  -- ============================================================================================
  -- Convergence of the smooth energy: `En n ≤ bound n` and `bound n → E`.
  -- ============================================================================================
  -- The error norms tend to `0`.
  have hofReal_tendsto : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  -- Taking square roots: `a = (a²)^(1/2)`, so `Dxn n → 0` from `Dxn n ² → 0`.
  have hroot : ∀ a : ℝ≥0∞, (a ^ 2) ^ (1 / 2 : ℝ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast a 2, ← ENNReal.rpow_mul]
    norm_num
  have hDxn_zero : Tendsto Dxn atTop (𝓝 0) := by
    have hsq_zero : Tendsto (fun n => Dxn n ^ 2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hofReal_tendsto
        (fun n => zero_le _) (fun n => (hDxy_bound n).1)
    have := hsq_zero.ennrpow_const (1 / 2 : ℝ)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at this
    simpa only [hroot] using this
  have hDyn_zero : Tendsto Dyn atTop (𝓝 0) := by
    have hsq_zero : Tendsto (fun n => Dyn n ^ 2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hofReal_tendsto
        (fun n => zero_le _) (fun n => (hDxy_bound n).2)
    have := hsq_zero.ennrpow_const (1 / 2 : ℝ)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at this
    simpa only [hroot] using this
  -- ============================================================================================
  -- Triangle inequality: `Nxn n ≤ Nx + Dxn n` and `Nyn n ≤ Ny + Dyn n` (on `volume.restrict B`).
  -- ============================================================================================
  have hone_le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hNxn_le : ∀ n, Nxn n ≤ Nx + Dxn n := by
    intro n
    have htri := eLpNorm_add_le (μ := volume.restrict B) (p := 2)
      hgx_mem.aestronglyMeasurable
      ((hPx_cont n).aestronglyMeasurable.sub hgx_mem.aestronglyMeasurable) hone_le
    have heq : (gx + (Px n - gx)) = Px n := by funext w; simp
    rw [heq] at htri
    simpa only [hNxn_def, hNx_def, hDxn_def] using htri
  have hNyn_le : ∀ n, Nyn n ≤ Ny + Dyn n := by
    intro n
    have htri := eLpNorm_add_le (μ := volume.restrict B) (p := 2)
      hgy_mem.aestronglyMeasurable
      ((hPy_cont n).aestronglyMeasurable.sub hgy_mem.aestronglyMeasurable) hone_le
    have heq : (gy + (Py n - gy)) = Py n := by funext w; simp
    rw [heq] at htri
    simpa only [hNyn_def, hNy_def, hDyn_def] using htri
  -- The dominating bound `bound n := (Nx + Dxn n)² + (Ny + Dyn n)²` satisfies `En n ≤ bound n`
  -- and `bound n → E`.
  set bound : ℕ → ℝ≥0∞ := fun n => (Nx + Dxn n) ^ 2 + (Ny + Dyn n) ^ 2 with hbound_def
  have hEn_le_bound : ∀ n, En n ≤ bound n := by
    intro n
    rw [hEn_eq n, hbound_def]
    exact add_le_add (pow_le_pow_left' (hNxn_le n) 2) (pow_le_pow_left' (hNyn_le n) 2)
  have hbound_tendsto : Tendsto bound atTop (𝓝 E) := by
    have h1 : Tendsto (fun n => Nx + Dxn n) atTop (𝓝 (Nx + 0)) :=
      tendsto_const_nhds.add hDxn_zero
    have h2 : Tendsto (fun n => Ny + Dyn n) atTop (𝓝 (Ny + 0)) :=
      tendsto_const_nhds.add hDyn_zero
    have h1sq : Tendsto (fun n => (Nx + Dxn n) ^ 2) atTop (𝓝 ((Nx + 0) ^ 2)) :=
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h1
    have h2sq : Tendsto (fun n => (Ny + Dyn n) ^ 2) atTop (𝓝 ((Ny + 0) ^ 2)) :=
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h2
    have hadd : Tendsto bound atTop (𝓝 ((Nx + 0) ^ 2 + (Ny + 0) ^ 2)) := h1sq.add h2sq
    rwa [add_zero, add_zero, ← hE_eq] at hadd
  -- ============================================================================================
  -- One-sided diameter stability under uniform displacement.
  -- ============================================================================================
  have hstable : ∀ (g₁ g₂ : ℂ → ℂ), Continuous g₁ → Continuous g₂ → ∀ S : Set ℂ, IsCompact S →
      ∀ δ : ℝ, 0 ≤ δ → (∀ z ∈ S, ‖g₁ z - g₂ z‖ ≤ δ) →
      Metric.diam (g₁ '' S) ≤ Metric.diam (g₂ '' S) + 2 * δ := by
    intro g₁ g₂ hg₁ hg₂ S hScpt δ hδ hbnd
    have hb₂ : Bornology.IsBounded (g₂ '' S) := (hScpt.image hg₂).isBounded
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro u ⟨a, haS, rfl⟩ v ⟨b, hbS, rfl⟩
    have hd : dist (g₁ a) (g₁ b)
        ≤ dist (g₁ a) (g₂ a) + dist (g₂ a) (g₂ b) + dist (g₂ b) (g₁ b) :=
      dist_triangle4 (g₁ a) (g₂ a) (g₂ b) (g₁ b)
    have h1 : dist (g₁ a) (g₂ a) ≤ δ := by rw [dist_eq_norm]; exact hbnd a haS
    have h3 : dist (g₂ b) (g₁ b) ≤ δ := by
      rw [dist_eq_norm, norm_sub_rev]; exact hbnd b hbS
    have h2 : dist (g₂ a) (g₂ b) ≤ Metric.diam (g₂ '' S) :=
      Metric.dist_le_diam_of_mem hb₂ ⟨a, haS, rfl⟩ ⟨b, hbS, rfl⟩
    calc dist (g₁ a) (g₁ b) ≤ δ + Metric.diam (g₂ '' S) + δ := by
            exact le_trans hd (add_le_add (add_le_add h1 h2) h3)
      _ = Metric.diam (g₂ '' S) + 2 * δ := by ring
  -- ============================================================================================
  -- Select a subsequence of radii converging to `ρ* ∈ [r, 2r]`.
  -- ============================================================================================
  obtain ⟨ρstar, hρstar_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    isCompact_Icc.tendsto_subseq hρ_mem
  have hρstar_pos : 0 < ρstar := lt_of_lt_of_le hr hρstar_mem.1
  -- Convergence helpers.
  have hφ_atTop : Tendsto φ atTop atTop := hφ_mono.tendsto_atTop
  have hc_tendsto : Tendsto (fun k => 2 * (1 / (φ k + 1 : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hcomp := h0.comp hφ_atTop
    have := hcomp.const_mul (2 : ℝ)
    simpa using this
  -- `diam (f '' sphere x (ρ (φ k))) → diam (f '' sphere x ρ*)`.
  have hb_tendsto :
      Tendsto (fun k => Metric.diam (f '' Metric.sphere x (ρ (φ k)))) atTop
        (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
    have hwithin : Tendsto (fun k => ρ (φ k)) atTop (𝓝[Set.Ioi 0] ρstar) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ_tendsto ?_
      refine Filter.Eventually.of_forall (fun k => ?_)
      exact lt_of_lt_of_le hr (hρ_mem (φ k)).1
    have hcwa := (continuousOn_diam_image_sphere hfcont x).continuousWithinAt
      (Set.mem_Ioi.mpr hρstar_pos)
    exact hcwa.tendsto.comp hwithin
  -- `diam (G (φ k) '' sphere x (ρ (φ k))) → diam (f '' sphere x ρ*)` by squeeze.
  have ha_tendsto :
      Tendsto (fun k => Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) atTop
        (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
    -- lower and upper bracket both tend to the limit.
    have hlow : Tendsto (fun k => Metric.diam (f '' Metric.sphere x (ρ (φ k)))
        - 2 * (1 / (φ k + 1 : ℝ))) atTop (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
      have := hb_tendsto.sub hc_tendsto
      simpa using this
    have hupp : Tendsto (fun k => Metric.diam (f '' Metric.sphere x (ρ (φ k)))
        + 2 * (1 / (φ k + 1 : ℝ))) atTop (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
      have := hb_tendsto.add hc_tendsto
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp ?_ ?_
    · -- lower bound: `diam(f''S) - 2δ ≤ diam(G''S)`
      intro k
      have hsph_cpt : IsCompact (Metric.sphere x (ρ (φ k))) := isCompact_sphere x (ρ (φ k))
      have hbnd : ∀ z ∈ Metric.sphere x (ρ (φ k)),
          ‖f z - G (φ k) z‖ ≤ 1 / (φ k + 1 : ℝ) := by
        intro z hz
        have hzB : z ∈ B := by
          rw [hB_def]
          have : ρ (φ k) ≤ 2 * r := (hρ_mem (φ k)).2
          rw [Metric.mem_sphere] at hz
          rw [Metric.mem_closedBall, hz]; exact this
        rw [norm_sub_rev]; exact hG_close (φ k) z hzB
      have hst := hstable f (G (φ k)) hfcont (hG_cd (φ k)).continuous
        (Metric.sphere x (ρ (φ k))) hsph_cpt (1 / (φ k + 1 : ℝ)) (by positivity) hbnd
      have : Metric.diam (f '' Metric.sphere x (ρ (φ k)))
          ≤ Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k))) + 2 * (1 / (φ k + 1 : ℝ)) := by
        simpa using hst
      linarith
    · -- upper bound: `diam(G''S) ≤ diam(f''S) + 2δ`
      intro k
      have hsph_cpt : IsCompact (Metric.sphere x (ρ (φ k))) := isCompact_sphere x (ρ (φ k))
      have hbnd : ∀ z ∈ Metric.sphere x (ρ (φ k)),
          ‖G (φ k) z - f z‖ ≤ 1 / (φ k + 1 : ℝ) := by
        intro z hz
        have hzB : z ∈ B := by
          rw [hB_def]
          have : ρ (φ k) ≤ 2 * r := (hρ_mem (φ k)).2
          rw [Metric.mem_sphere] at hz
          rw [Metric.mem_closedBall, hz]; exact this
        exact hG_close (φ k) z hzB
      have hst := hstable (G (φ k)) f (hG_cd (φ k)).continuous hfcont
        (Metric.sphere x (ρ (φ k))) hsph_cpt (1 / (φ k + 1 : ℝ)) (by positivity) hbnd
      simpa using hst
  -- ============================================================================================
  -- Pass to the limit in `ℝ≥0∞`.
  -- ============================================================================================
  -- LHS along the subsequence converges to `ofReal (diam (f '' sphere x ρ*)²)`.
  have hLHS_tendsto :
      Tendsto (fun k => ENNReal.ofReal
        ((Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρstar)) ^ 2))) := by
    have hsq_t :
        Tendsto (fun k => (Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) ^ 2) atTop
          (𝓝 ((Metric.diam (f '' Metric.sphere x ρstar)) ^ 2)) :=
      (continuous_pow 2).continuousAt.tendsto.comp ha_tendsto
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hsq_t
  -- RHS along the subsequence is `≤ ofReal C₀ * bound (φ k)`, which converges to `ofReal C₀ * E`.
  have hRHS_tendsto :
      Tendsto (fun k => ENNReal.ofReal C₀ * bound (φ k)) atTop
        (𝓝 (ENNReal.ofReal C₀ * E)) := by
    have hbsub : Tendsto (fun k => bound (φ k)) atTop (𝓝 E) := hbound_tendsto.comp hφ_atTop
    exact ENNReal.Tendsto.const_mul hbsub (Or.inr ENNReal.ofReal_ne_top)
  -- The pointwise inequality along the subsequence.
  have hpt_le : ∀ k,
      ENNReal.ofReal ((Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) ^ 2)
        ≤ ENNReal.ofReal C₀ * bound (φ k) := by
    intro k
    refine le_trans (hρ_le (φ k)) ?_
    exact mul_le_mul' (le_refl _) (hEn_le_bound (φ k))
  -- Conclude.
  refine ⟨ρstar, hρstar_mem, ?_⟩
  have hfinal :
      ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρstar)) ^ 2)
        ≤ ENNReal.ofReal C₀ * E :=
    le_of_tendsto_of_tendsto' hLHS_tendsto hRHS_tendsto hpt_le
  exact hfinal

/-- **Finite metric derivative a.e. (ASM) — assembly of CL + MON + ED.**

A homeomorphism `f` with weak gradient `(gx, gy) ∈ L²_loc` has a finite metric upper derivative at
almost every point — verbatim the hypothesis the proven Stepanov engine
`ae_differentiableAt_of_ae_limsup_slope_lt_top` consumes.

Proof (per a.e. good `x`, an energy Lebesgue point from `ED`): for any small `s`, `CL` with `r = s`
gives `ρ ∈ [s, 2s]` with `diam (f '' sphere x ρ)² ≤ C₀·∫_{B(x,2s)} φ`; `MON` upgrades this to
`diam (f '' closedBall x ρ)`; since `closedBall x s ⊆ closedBall x ρ`, monotonicity of diameter and
`ED`'s `∫_{B(x,2s)} φ ≤ A·s²` give `diam (f '' closedBall x s) ≤ √(C₀·A)·s`; finally every `y` near
`x` lies in `closedBall x ‖y − x‖`, so
`‖f y − f x‖ ≤ diam (f '' closedBall x ‖y−x‖) ≤ √(C₀·A)·‖y − x‖` (exactly as
`GeometricDifferentiable.ae_differentiableAt'`, with the roundness input replaced by
`CL + MON + ED`). -/
theorem ae_finiteMetricDerivative_of_W12loc_homeomorph {f gx gy : ℂ → ℂ}
    (hhomeo : IsHomeomorph f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∀ᵐ x : ℂ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  classical
  have hfcont : Continuous f := hhomeo.continuous
  -- Courant–Lebesgue: a uniform constant `C₀` with a small-energy circle at every scale.
  obtain ⟨C₀, hC₀, hCL⟩ := courantLebesgue_smallEnergyCircle hfcont hwg hgx hgy
  -- Work at almost every energy Lebesgue point `x`.
  filter_upwards [ae_energyDensity_lebesgue_point hgx hgy] with x hx
  obtain ⟨A, hA, hED⟩ := hx
  -- The Stepanov constant.
  refine ⟨Real.sqrt (C₀ * A), ?_⟩
  set C : ℝ := Real.sqrt (C₀ * A) with hC_def
  have hC_nonneg : 0 ≤ C := Real.sqrt_nonneg _
  -- A `diam` bound at every small radius `s`.
  have hradius : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Metric.diam (f '' Metric.closedBall x s) ≤ C * s := by
    filter_upwards [hED, self_mem_nhdsWithin] with s hs hspos
    have hspos' : (0 : ℝ) < s := hspos
    -- Courant–Lebesgue at radius `r = s`: a sphere radius `ρ ∈ [s, 2s]` with small image diameter.
    obtain ⟨ρ, hρmem, hρdiam⟩ := hCL x s hspos'
    have hρge : s ≤ ρ := hρmem.1
    have hρpos : 0 < ρ := lt_of_lt_of_le hspos' hρge
    -- Combine CL with ED to get `ofReal((diam sphere)²) ≤ ofReal (C₀·A·s²)`.
    have hchain_ennreal : ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal (C₀ * A * s ^ 2) := by
      calc ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2)
          ≤ ENNReal.ofReal C₀ * ∫⁻ z in Metric.closedBall x (2 * s), energyDensity gx gy z :=
            hρdiam
        _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (A * s ^ 2) := by gcongr
        _ = ENNReal.ofReal (C₀ * (A * s ^ 2)) := (ENNReal.ofReal_mul hC₀).symm
        _ = ENNReal.ofReal (C₀ * A * s ^ 2) := by rw [mul_assoc]
    -- Pass to real numbers (both sides nonneg).
    have hsphere_nonneg : 0 ≤ Metric.diam (f '' Metric.sphere x ρ) := Metric.diam_nonneg
    have hCAs_nonneg : 0 ≤ C₀ * A * s ^ 2 := by positivity
    have hchain_real : (Metric.diam (f '' Metric.sphere x ρ)) ^ 2 ≤ C₀ * A * s ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff hCAs_nonneg).mp hchain_ennreal
    -- Take square roots: `diam (sphere) ≤ √(C₀·A)·s = C·s`.
    have hCA_nonneg : 0 ≤ C₀ * A := by positivity
    have hsphere_le : Metric.diam (f '' Metric.sphere x ρ) ≤ C * s := by
      have hsqrt : Metric.diam (f '' Metric.sphere x ρ)
          ≤ Real.sqrt (C₀ * A * s ^ 2) := by
        calc Metric.diam (f '' Metric.sphere x ρ)
            = Real.sqrt ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2) := by
              rw [Real.sqrt_sq hsphere_nonneg]
          _ ≤ Real.sqrt (C₀ * A * s ^ 2) := Real.sqrt_le_sqrt hchain_real
      calc Metric.diam (f '' Metric.sphere x ρ)
          ≤ Real.sqrt (C₀ * A * s ^ 2) := hsqrt
        _ = C * s := by
            rw [show C₀ * A * s ^ 2 = (C₀ * A) * s ^ 2 by ring, Real.sqrt_mul hCA_nonneg,
              Real.sqrt_sq hspos'.le, hC_def]
    -- MON: `diam (f '' closedBall x ρ) ≤ diam (f '' sphere x ρ)`.
    have hMON : Metric.diam (f '' Metric.closedBall x ρ)
        ≤ Metric.diam (f '' Metric.sphere x ρ) :=
      diam_image_closedBall_le_diam_image_sphere hhomeo x hρpos
    -- Monotonicity of diam in the radius: `closedBall x s ⊆ closedBall x ρ`.
    have hsub : Metric.closedBall x s ⊆ Metric.closedBall x ρ :=
      Metric.closedBall_subset_closedBall hρge
    have hball_bdd : Bornology.IsBounded (f '' Metric.closedBall x ρ) :=
      ((isCompact_closedBall x ρ).image hfcont).isBounded
    have hmono : Metric.diam (f '' Metric.closedBall x s)
        ≤ Metric.diam (f '' Metric.closedBall x ρ) :=
      Metric.diam_mono (Set.image_mono hsub) hball_bdd
    -- Assemble: `diam (f '' closedBall x s) ≤ C · s`.
    calc Metric.diam (f '' Metric.closedBall x s)
        ≤ Metric.diam (f '' Metric.closedBall x ρ) := hmono
      _ ≤ Metric.diam (f '' Metric.sphere x ρ) := hMON
      _ ≤ C * s := hsphere_le
  -- Translate the radius bound to the pointwise bound near `x`.
  rw [eventually_nhdsWithin_iff] at hradius
  rw [Metric.eventually_nhds_iff] at hradius ⊢
  obtain ⟨ε, hεpos, hε⟩ := hradius
  refine ⟨ε, hεpos, ?_⟩
  intro y hy
  rcases eq_or_ne y x with rfl | hyx
  · simp
  · -- `s = dist y x = ‖y - x‖ ∈ (0, ε)`.
    have hdist_pos : 0 < dist y x := dist_pos.2 hyx
    have hdist_lt : dist y x < ε := hy
    have hdist0 : dist (dist y x) 0 < ε := by
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    have hbound := hε hdist0 (Set.mem_Ioi.2 hdist_pos)
    -- `y, x ∈ closedBall x (dist y x)`.
    have hymem : y ∈ Metric.closedBall x (dist y x) := Metric.mem_closedBall.2 le_rfl
    have hxmem : x ∈ Metric.closedBall x (dist y x) := by
      rw [Metric.mem_closedBall, dist_self]; exact dist_nonneg
    have hdiam_bd : dist (f y) (f x) ≤ Metric.diam (f '' Metric.closedBall x (dist y x)) :=
      Metric.dist_le_diam_of_mem ((isCompact_closedBall x (dist y x)).image hfcont).isBounded
        (Set.mem_image_of_mem f hymem) (Set.mem_image_of_mem f hxmem)
    calc ‖f y - f x‖ = dist (f y) (f x) := (dist_eq_norm _ _).symm
      _ ≤ Metric.diam (f '' Metric.closedBall x (dist y x)) := hdiam_bd
      _ ≤ C * dist y x := hbound
      _ = C * ‖y - x‖ := by rw [dist_eq_norm]

/-- **Gehring–Lehto: roundness-free a.e. differentiability.**

A homeomorphism `f : ℂ → ℂ` with weak gradient `(gx, gy) ∈ L²_loc` (i.e. `f ∈ W^{1,2}_loc`) is
differentiable almost everywhere. This is the pivot: it supplies the a.e.-differentiability of a
geometric quasiconformal map **without** the conformal-modulus roundness estimate, by composing the
finite-metric-derivative assembly `ASM` with the proven Stepanov engine. -/
theorem ae_differentiableAt_of_W12loc_homeomorph {f gx gy : ℂ → ℂ}
    (hhomeo : IsHomeomorph f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x :=
  RiemannDynamics.Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top
    (ae_finiteMetricDerivative_of_W12loc_homeomorph hhomeo hwg hgx hgy)

end RiemannDynamics.GehringLehto

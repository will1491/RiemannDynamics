/-
Copyright (c) 2026 Will Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Li
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Primitives of Holomorphic Functions on Star-Shaped Domains

This file extends Mathlib's `IsExactOn_ball` (Morera's theorem for disks) to
star-shaped open sets in `ℂ`. The key construction is the **segment integral**

  `starPrimitive p f z := ∫ t in (0:ℝ)..1, (z - p) • f (p + t • (z - p))`

which is the line integral of `f` along the segment from a star center `p` to a
point `z`. For `f` complex-differentiable on a star-shaped open set `U` and
star center `p ∈ U`, this defines a primitive of `f` on `U`.

## Main results

* `Complex.starPrimitive`: the segment integral from a fixed base point `p`.
* `Complex.hasDerivAt_starPrimitive`: for `f` complex-differentiable on an
  open star-shaped set `U` with star center `p`, `starPrimitive p f` has
  complex derivative `f z` at every `z ∈ U`.
* `Complex.starShaped_isExactOn`: corollary packaging the above as
  `IsExactOn`.
* `Complex.intervalIntegral_eq_sub_of_starShaped`: fundamental theorem for
  line integrals over segments in a star-shaped open set.
* `Complex.triangleIntegral_eq_zero_of_starShaped`: Cauchy-Goursat for
  triangles with one vertex at the star center.

## Lune-specific support lemmas (consumed by `WindingNumber.lean`)

The following lemmas support the closed-form lune Cauchy-Goursat
identities in `RiemannDynamics/Hyperbolic/WindingNumber.lean`:

* `Complex.topLeftBoxMinusBall_starConvex`: the upper-left-of-`e` open box
  minus `closedBall e R₀` is star-convex from the outer corner
  `(e.re - R₀) + (e.im + R₀)·I`. Geometric content: for any point `Q` in
  this open set, the segment from the outer corner to `Q` stays outside
  `closedBall e R₀`. Proof factors through a quadratic non-negativity
  analysis.
* `Complex.topRightBoxMinusBall_starConvex`: mirror across `x = e.re`.
* `Complex.starPrimitive_horizontal_eq_intervalIntegral`: the segment
  integral from `xV + y·I` to `xZ + y·I` (same imaginary part) equals
  `∫_{xV}^{xZ} f(x + y·I) dx`. Direct change of variables in the segment
  parameter.
* `Complex.starPrimitive_vertical_eq_intervalIntegral`: the segment
  integral from `x + yV·I` to `x + yZ·I` (same real part) equals
  `Complex.I · ∫_{yV}^{yZ} f(x + y·I) dy`.
* `Complex.topLeftLune_arc_integral_eq_starPrimitive_sub`: for the
  top-left lune setup (open box minus closed disk, star-convex from outer
  corner), the arc integral over `[π/2, π]` of `f` along
  `circleMap e R₀ θ` (with the `dz/dθ = I·R₀·exp(I·θ)` factor) equals
  `starPrimitive V f B − starPrimitive V f T` where
  `V = (e.re − R₀) + (e.im + R₀)·I`, `T = e + R₀·I`, `B = e − R₀`. The
  proof factors through the ε-arc limit: for ε > 0, the slightly outer
  arc `circleMap e (R₀ + ε)` on `[π/2 + ε, π − ε]` lies in the
  star-convex open set, FTC applies via `hasDerivAt_starPrimitive` and
  the chain rule with `hasDerivAt_circleMap`, and ε → 0 recovers the
  full arc integral by dominated convergence and continuity of
  `starPrimitive` at the endpoints (which uses `Hc`'s continuity of `f`
  on the closed lune).
* `Complex.topRightLune_arc_integral_eq_starPrimitive_sub`: mirror.

## Implementation notes

The proof of `hasDerivAt_starPrimitive` uses a clean d/dt identity:
defining `G(t, z) := t · f(p + t·(z-p))`, the complex partial derivative
`∂_z [f(p + t·(z-p)) · (z-p)] = d/dt G(t, z)`, so the integral of the
integrand's `z`-derivative equals `G(1, z) - G(0, z) = f(z)`.
-/

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Interval

namespace Complex

variable {U : Set ℂ} {f : ℂ → ℂ} {p : ℂ}

/-- The **segment integral** from `p` to `z` of `f`. For a star-shaped open set
`U ⊆ ℂ` with star center `p`, this defines a primitive of `f` on `U`. -/
def starPrimitive (p : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (z - p) * f (p + (t : ℂ) * (z - p))

/-- **Star-shaped primitive: the segment integral defines a primitive.** For
`f` complex-differentiable on an open star-shaped set `U` with star center
`p ∈ U`, the segment integral `starPrimitive p f` has complex derivative
`f z` at every `z ∈ U`. The proof differentiates under the integral sign:
the `z`-partial of the integrand `(z-p)·f(p + t·(z-p))` equals
`d/dt [t·f(p + t·(z-p))]`, so by FTC the integral of the `z`-partial
evaluates to `f(z)`. -/
theorem hasDerivAt_starPrimitive
    (hU : IsOpen U) (hSC : StarConvex ℝ p U)
    (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (starPrimitive p f) (f z) z := by
  -- p ∈ U from star-convexity.
  have hp : p ∈ U := hSC.mem ⟨z, hz⟩
  -- Open ball s_nbhd ⊆ closedBall ⊆ U around z.
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU z hz
  set r' := r / 2 with hr'_def
  have hr'_pos : 0 < r' := half_pos hr_pos
  have h_cb_sub_U : Metric.closedBall z r' ⊆ U := fun w hw =>
    hr_sub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw)
      (half_lt_self hr_pos)))
  set s_nbhd := Metric.ball z r' with hs_nbhd_def
  have hs_mem : s_nbhd ∈ 𝓝 z := Metric.ball_mem_nhds z hr'_pos
  have hs_sub_cb : s_nbhd ⊆ Metric.closedBall z r' := Metric.ball_subset_closedBall
  -- Star-convexity: p + t·(w-p) ∈ U for w ∈ closedBall, t ∈ [0,1].
  have h_pt_in_U : ∀ w ∈ Metric.closedBall z r', ∀ t ∈ Set.Icc (0:ℝ) 1,
      p + (t : ℂ) * (w - p) ∈ U := by
    intro w hw t ht
    have hw_U := h_cb_sub_U hw
    apply hSC.segment_subset hw_U
    refine ⟨1 - t, t, by linarith [ht.2], ht.1, by linarith, ?_⟩
    simp only [Complex.real_smul]; push_cast; ring
  -- Compact K ⊆ U.
  set K : Set ℂ := (fun wt : ℂ × ℝ => p + (wt.2 : ℂ) * (wt.1 - p)) ''
    (Metric.closedBall z r' ×ˢ Set.Icc (0:ℝ) 1) with hK_def
  have hK_compact : IsCompact K := by
    refine IsCompact.image ((isCompact_closedBall z r').prod isCompact_Icc) ?_
    fun_prop
  have hK_sub_U : K ⊆ U := by
    rintro _ ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
    exact h_pt_in_U w hw t ht
  have h_pt_K : ∀ w ∈ Metric.closedBall z r', ∀ t ∈ Set.Icc (0:ℝ) 1,
      p + (t : ℂ) * (w - p) ∈ K := fun w hw t ht => ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
  -- f and deriv f are continuous on U, hence bounded on K.
  have hf_an : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hf_cont_U : ContinuousOn f U := hf.continuousOn
  have hf_cont_K : ContinuousOn f K := hf_cont_U.mono hK_sub_U
  have hdf_cont_U : ContinuousOn (deriv f) U := fun w hw =>
    ((hf_an w hw).deriv.continuousAt).continuousWithinAt
  have hdf_cont_K : ContinuousOn (deriv f) K := hdf_cont_U.mono hK_sub_U
  obtain ⟨Mf, hMf⟩ := hK_compact.exists_bound_of_continuousOn hf_cont_K
  obtain ⟨Mdf, hMdf⟩ := hK_compact.exists_bound_of_continuousOn hdf_cont_K
  -- Bound on ‖w - p‖ for w ∈ closedBall z r'.
  set Bwp := ‖z - p‖ + r' with hBwp_def
  have hBwp_bd : ∀ w ∈ Metric.closedBall z r', ‖w - p‖ ≤ Bwp := by
    intro w hw
    have h_w_z : ‖w - z‖ ≤ r' := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hw
    calc ‖w - p‖ = ‖(w - z) + (z - p)‖ := by congr 1; ring
      _ ≤ ‖w - z‖ + ‖z - p‖ := norm_add_le _ _
      _ ≤ r' + ‖z - p‖ := by linarith
      _ = Bwp := by rw [hBwp_def]; ring
  -- Bounds are nonneg.
  have hMf_nn : 0 ≤ Mf := by
    have hp_in_K : p ∈ K := by
      have h1 : z ∈ Metric.closedBall z r' := Metric.mem_closedBall_self hr'_pos.le
      have h2 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
      have h3 := h_pt_K z h1 0 h2
      have : p + ((0:ℝ):ℂ) * (z - p) = p := by push_cast; ring
      rwa [this] at h3
    exact le_trans (norm_nonneg _) (hMf p hp_in_K)
  have hMdf_nn : 0 ≤ Mdf := by
    have hp_in_K : p ∈ K := by
      have h1 : z ∈ Metric.closedBall z r' := Metric.mem_closedBall_self hr'_pos.le
      have h2 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
      have h3 := h_pt_K z h1 0 h2
      have : p + ((0:ℝ):ℂ) * (z - p) = p := by push_cast; ring
      rwa [this] at h3
    exact le_trans (norm_nonneg _) (hMdf p hp_in_K)
  have hBwp_nn : 0 ≤ Bwp := add_nonneg (norm_nonneg _) hr'_pos.le
  -- Constant bound on F'.
  set C := Mf + Bwp * Mdf with hC_def
  have hC_nn : 0 ≤ C := add_nonneg hMf_nn (mul_nonneg hBwp_nn hMdf_nn)
  -- Define F and F'.
  set F : ℂ → ℝ → ℂ := fun w t => (w - p) * f (p + (t : ℂ) * (w - p)) with hF_def
  set F' : ℂ → ℝ → ℂ := fun w t =>
    f (p + (t : ℂ) * (w - p)) +
    (w - p) * (t : ℂ) * deriv f (p + (t : ℂ) * (w - p)) with hF'_def
  -- Pointwise HasDerivAt of F (·, t) at each w ∈ s_nbhd, t ∈ [0,1].
  have h_pt_deriv : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ∈ Set.uIoc (0:ℝ) 1 → ∀ w ∈ s_nbhd, HasDerivAt (fun w => F w t) (F' w t) w := by
    refine Filter.Eventually.of_forall ?_
    intro t ht w hw
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
      rw [show Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 from Set.uIoc_of_le (by norm_num)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hw_cb := hs_sub_cb hw
    have h_pt_w_in_U := h_pt_in_U w hw_cb t ht_Icc
    -- HasDerivAt of (w ↦ w - p): derivative 1.
    have h_id_sub : HasDerivAt (fun w : ℂ => w - p) 1 w := (hasDerivAt_id w).sub_const p
    -- HasDerivAt of (w ↦ p + (t:ℂ)*(w-p)): derivative (t:ℂ).
    have h_inner : HasDerivAt (fun w : ℂ => p + (t : ℂ) * (w - p)) (t : ℂ) w := by
      have h2 := h_id_sub.const_mul (t : ℂ)
      simpa using h2.const_add p
    -- HasDerivAt of f at the inner point.
    have hf_at : HasDerivAt f (deriv f (p + (t : ℂ) * (w - p))) (p + (t : ℂ) * (w - p)) :=
      (hf.differentiableAt (hU.mem_nhds h_pt_w_in_U)).hasDerivAt
    -- Chain rule.
    have hf_at_inner : HasDerivAt f (deriv f (p + (t : ℂ) * (w - p)))
        ((fun w : ℂ => p + (t : ℂ) * (w - p)) w) := by simpa using hf_at
    have h_f_inner : HasDerivAt (fun w : ℂ => f (p + (t : ℂ) * (w - p)))
        ((t : ℂ) * deriv f (p + (t : ℂ) * (w - p))) w := by
      have h_c := HasDerivAt.comp w hf_at_inner h_inner
      simp only [Function.comp_def] at h_c
      rw [mul_comm]; exact h_c
    -- Product rule.
    have h_prod := h_id_sub.mul h_f_inner
    -- We need: HasDerivAt (fun w => F w t) (F' w t) w
    have h_func_eq : (fun w : ℂ => F w t) = fun w : ℂ => (w - p) * f (p + (t : ℂ) * (w - p)) := by
      funext w; simp only [hF_def]
    have h_deriv_eq : F' w t = 1 * f (p + (t : ℂ) * (w - p)) +
        (w - p) * ((t : ℂ) * deriv f (p + (t : ℂ) * (w - p))) := by
      simp only [hF'_def]; ring
    rw [h_func_eq, h_deriv_eq]
    exact h_prod
  -- Bound on F'.
  have h_bound : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ∈ Set.uIoc (0:ℝ) 1 → ∀ w ∈ s_nbhd, ‖F' w t‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro t ht w hw
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
      rw [show Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 from Set.uIoc_of_le (by norm_num)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hw_cb := hs_sub_cb hw
    have h_pt_K_wt := h_pt_K w hw_cb t ht_Icc
    have h_t_abs : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_Icc.1]; exact ht_Icc.2
    have h_wp : ‖w - p‖ ≤ Bwp := hBwp_bd w hw_cb
    have h_f_bd : ‖f (p + (t : ℂ) * (w - p))‖ ≤ Mf := hMf _ h_pt_K_wt
    have h_df_bd : ‖deriv f (p + (t : ℂ) * (w - p))‖ ≤ Mdf := hMdf _ h_pt_K_wt
    calc ‖F' w t‖
        = ‖f (p + (t : ℂ) * (w - p)) +
            (w - p) * (t : ℂ) * deriv f (p + (t : ℂ) * (w - p))‖ := by rw [hF'_def]
      _ ≤ ‖f (p + (t : ℂ) * (w - p))‖ +
          ‖(w - p) * (t : ℂ) * deriv f (p + (t : ℂ) * (w - p))‖ := norm_add_le _ _
      _ = ‖f (p + (t : ℂ) * (w - p))‖ +
          ‖w - p‖ * ‖(t : ℂ)‖ * ‖deriv f (p + (t : ℂ) * (w - p))‖ := by
            rw [norm_mul, norm_mul]
      _ ≤ Mf + Bwp * 1 * Mdf := by
            have h1 : ‖w - p‖ * ‖(t : ℂ)‖ * ‖deriv f (p + (t : ℂ) * (w - p))‖
                ≤ Bwp * 1 * Mdf := by
              apply mul_le_mul _ h_df_bd (norm_nonneg _) (mul_nonneg hBwp_nn (by norm_num))
              exact mul_le_mul h_wp h_t_abs (norm_nonneg _) hBwp_nn
            linarith [h_f_bd, h1]
      _ = C := by rw [hC_def]; ring
  -- F (w) is continuous on Icc 0 1 (for w ∈ closedBall z r').
  have h_F_cont_w_on : ∀ w ∈ Metric.closedBall z r', ContinuousOn (F w) (Set.Icc (0:ℝ) 1) := by
    intro w hw
    apply ContinuousOn.mul continuousOn_const
    have h_inner_cont : Continuous (fun t : ℝ => p + (t : ℂ) * (w - p)) := by fun_prop
    apply hf_cont_U.comp h_inner_cont.continuousOn
    intro t ht
    exact h_pt_in_U w hw t ht
  -- AEStronglyMeasurable of F x for x ∈ s_nbhd.
  have h_F_aemeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (F x)
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    filter_upwards [hs_mem] with x hx
    have h_cont := (h_F_cont_w_on x (hs_sub_cb hx)).mono
      (show Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 from by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Set.Ioc_subset_Icc_self)
    exact h_cont.aestronglyMeasurable measurableSet_uIoc
  -- IntervalIntegrable F z and F' z.
  have h_F_int : IntervalIntegrable (F z) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact h_F_cont_w_on z (Metric.mem_closedBall_self hr'_pos.le)
  have h_F'_aemeas : AEStronglyMeasurable (F' z)
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    rw [show Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 from Set.uIoc_of_le (by norm_num)]
    apply ContinuousOn.mono _ Set.Ioc_subset_Icc_self
    -- F' z continuous on Icc 0 1
    have h_inner_cont : Continuous (fun t : ℝ => p + (t : ℂ) * (z - p)) := by fun_prop
    have h_f_comp : ContinuousOn (fun t : ℝ => f (p + (t : ℂ) * (z - p)))
        (Set.Icc (0:ℝ) 1) := by
      apply hf_cont_U.comp h_inner_cont.continuousOn
      intro t ht
      exact h_pt_in_U z (Metric.mem_closedBall_self hr'_pos.le) t ht
    have h_df_comp : ContinuousOn (fun t : ℝ => deriv f (p + (t : ℂ) * (z - p)))
        (Set.Icc (0:ℝ) 1) := by
      apply hdf_cont_U.comp h_inner_cont.continuousOn
      intro t ht
      exact h_pt_in_U z (Metric.mem_closedBall_self hr'_pos.le) t ht
    apply ContinuousOn.add h_f_comp
    apply ContinuousOn.mul (ContinuousOn.mul continuousOn_const (by fun_prop)) h_df_comp
  -- IntervalIntegrable bound (constant).
  have h_bound_int : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  -- Apply diff-under-integral.
  have h_diff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (E := ℂ) (a := 0) (b := 1) (F := F) (F' := F') (x₀ := z) (s := s_nbhd)
    (bound := fun _ => C) hs_mem h_F_aemeas h_F_int h_F'_aemeas h_bound h_bound_int h_pt_deriv
  -- Compute ∫_0^1 F' z t dt = f z via FTC.
  -- Define g(t) := (t:ℂ) * f(p + (t:ℂ) * (z-p)), then g'(t) = F'(z, t).
  set g : ℝ → ℂ := fun t => (t : ℂ) * f (p + (t : ℂ) * (z - p)) with hg_def
  have hg_deriv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt g (F' z t) t := by
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have h_pt_z_in_U := h_pt_in_U z (Metric.mem_closedBall_self hr'_pos.le) t ht_Icc
    -- HasDerivAt of (t : ℂ).
    have h_t_id : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    -- HasDerivAt of f(p + (t:ℂ)*(z-p)).
    have h_inner_real : HasDerivAt (fun t : ℝ => p + (t : ℂ) * (z - p)) (z - p) t := by
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * (z - p)) ((1:ℂ) * (z - p)) t :=
        h_t_id.mul_const (z - p)
      simpa using h2.const_add p
    -- For chain rule with f : ℂ → ℂ, use HasDerivAt.comp_ofReal via complex inner.
    have h_inner_C : HasDerivAt (fun w : ℂ => p + w * (z - p)) (z - p) ((t : ℂ) : ℂ) := by
      have h1 : HasDerivAt (fun w : ℂ => w) (1 : ℂ) ((t : ℂ) : ℂ) := hasDerivAt_id _
      have h2 : HasDerivAt (fun w : ℂ => w * (z - p)) ((1 : ℂ) * (z - p)) ((t : ℂ) : ℂ) :=
        h1.mul_const (z - p)
      simpa using h2.const_add p
    have hf_at_pre : HasDerivAt f (deriv f (p + (t : ℂ) * (z - p)))
        ((fun w : ℂ => p + w * (z - p)) (t : ℂ)) := by
      simpa using (hf.differentiableAt (hU.mem_nhds h_pt_z_in_U)).hasDerivAt
    have hf_comp_C : HasDerivAt (fun w : ℂ => f (p + w * (z - p)))
        (deriv f (p + (t : ℂ) * (z - p)) * (z - p)) ((t : ℂ) : ℂ) := by
      have h_c := HasDerivAt.comp ((t : ℂ) : ℂ) hf_at_pre h_inner_C
      simp only [Function.comp_def] at h_c
      exact h_c
    have hf_comp_real : HasDerivAt (fun t : ℝ => f (p + (t : ℂ) * (z - p)))
        (deriv f (p + (t : ℂ) * (z - p)) * (z - p)) t := hf_comp_C.comp_ofReal
    -- Product rule: HasDerivAt (g) (1 · f(p+t(z-p)) + (t:ℂ) · (deriv f · (z-p))) t.
    have h_prod := h_t_id.mul hf_comp_real
    convert h_prod using 1
    simp only [hF'_def]
    ring
  -- IntervalIntegrable F' z (from the diff-under-integral conclusion or FTC compatibility).
  have h_F'_int : IntervalIntegrable (F' z) MeasureTheory.volume 0 1 := h_diff.1
  -- FTC: ∫_0^1 F' z t dt = g(1) - g(0) = f(z) - 0 = f(z).
  have h_ftc : ∫ t in (0:ℝ)..1, F' z t = g 1 - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv h_F'_int
  have h_g_endpoints : g 1 - g 0 = f z := by
    simp only [hg_def]
    have h1 : p + ((1 : ℝ) : ℂ) * (z - p) = z := by push_cast; ring
    have h0 : ((0 : ℝ) : ℂ) * f (p + ((0 : ℝ) : ℂ) * (z - p)) = 0 := by push_cast; ring
    rw [h0, h1]; push_cast; ring
  -- Combine: HasDerivAt (starPrimitive p f) (f z) z.
  have h_final : HasDerivAt (fun w => ∫ t in (0:ℝ)..1, F w t)
      (∫ t in (0:ℝ)..1, F' z t) z := h_diff.2
  rw [h_ftc, h_g_endpoints] at h_final
  -- starPrimitive p f w = ∫ t in 0..1, (w - p) * f(p + (t:ℂ) * (w - p)) = ∫ t in 0..1, F w t.
  have h_eq : (fun w => ∫ t in (0:ℝ)..1, F w t) = starPrimitive p f := by
    funext w
    simp only [hF_def, starPrimitive]
  rw [h_eq] at h_final
  exact h_final

/-- **`IsExactOn` for star-shaped open sets.** A function `f` complex-
differentiable on an open star-shaped set `U` with star center `p` is the
derivative of its segment integral from `p`. -/
theorem starShaped_isExactOn
    (hU : IsOpen U) (hSC : StarConvex ℝ p U) (_hp : p ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    IsExactOn f U :=
  ⟨starPrimitive p f, fun _ hz => (hasDerivAt_starPrimitive hU hSC hf hz)⟩

/-- **Fundamental theorem for segment line integrals in a star-shaped set.**
For `f` complex-differentiable on an open star-shaped set `U` with star
center `p ∈ U`, the segment integral from any point `z₀ ∈ U` to `z₁ ∈ U`
(provided the segment `[z₀, z₁]` lies in `U`) equals the difference of the
segment primitives:
`∫_0^1 (z₁ - z₀) · f(z₀ + t·(z₁ - z₀)) dt = starPrimitive p f z₁ − starPrimitive p f z₀`.
This is the line-integral form of the fundamental theorem of calculus. -/
theorem intervalIntegral_eq_sub_of_starShaped
    (hU : IsOpen U) (hSC : StarConvex ℝ p U) (_hp : p ∈ U)
    (hf : DifferentiableOn ℂ f U)
    {z₀ z₁ : ℂ} (_hz₀ : z₀ ∈ U) (_hz₁ : z₁ ∈ U)
    (hseg : segment ℝ z₀ z₁ ⊆ U) :
    (∫ t in (0:ℝ)..1, (z₁ - z₀) * f (z₀ + (t : ℂ) * (z₁ - z₀))) =
    starPrimitive p f z₁ - starPrimitive p f z₀ := by
  -- For s ∈ [0, 1], z₀ + s·(z₁-z₀) ∈ segment z₀ z₁ ⊆ U.
  have h_seg_mem : ∀ s ∈ Set.Icc (0:ℝ) 1, z₀ + (s : ℂ) * (z₁ - z₀) ∈ U := by
    intro s hs
    have h_in_seg : z₀ + (s : ℂ) * (z₁ - z₀) ∈ segment ℝ z₀ z₁ := by
      refine ⟨1 - s, s, by linarith [hs.2], hs.1, by linarith, ?_⟩
      simp only [Complex.real_smul]
      push_cast; ring
    exact hseg h_in_seg
  -- HasDerivAt of H(s) := starPrimitive p f (z₀ + s·(z₁-z₀)) at each s ∈ uIcc 0 1.
  have hH_deriv : ∀ s ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => starPrimitive p f (z₀ + (s : ℂ) * (z₁ - z₀)))
      ((z₁ - z₀) * f (z₀ + (s : ℂ) * (z₁ - z₀))) s := by
    intro s hs
    have hs_Icc : s ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    have h_pt_in_U := h_seg_mem s hs_Icc
    have h_sP_deriv : HasDerivAt (starPrimitive p f)
        (f (z₀ + (s : ℂ) * (z₁ - z₀))) (z₀ + (s : ℂ) * (z₁ - z₀)) :=
      hasDerivAt_starPrimitive hU hSC hf h_pt_in_U
    -- Chain rule via comp_ofReal: go through an intermediate complex function.
    have h_inner_C : HasDerivAt (fun w : ℂ => z₀ + w * (z₁ - z₀)) (z₁ - z₀) ((s : ℂ) : ℂ) := by
      have h1 : HasDerivAt (fun w : ℂ => w) (1 : ℂ) ((s : ℂ) : ℂ) := hasDerivAt_id _
      have h2 : HasDerivAt (fun w : ℂ => w * (z₁ - z₀)) ((1 : ℂ) * (z₁ - z₀)) ((s : ℂ) : ℂ) :=
        h1.mul_const (z₁ - z₀)
      simpa using h2.const_add z₀
    have hH_at : HasDerivAt (starPrimitive p f) (f (z₀ + (s : ℂ) * (z₁ - z₀)))
        ((fun w : ℂ => z₀ + w * (z₁ - z₀)) (s : ℂ)) := by simpa using h_sP_deriv
    have h_comp : HasDerivAt (fun w : ℂ => starPrimitive p f (z₀ + w * (z₁ - z₀)))
        ((z₁ - z₀) * f (z₀ + (s : ℂ) * (z₁ - z₀))) ((s : ℂ) : ℂ) := by
      have h_c := HasDerivAt.comp ((s : ℂ) : ℂ) hH_at h_inner_C
      simp only [Function.comp_def] at h_c
      rw [mul_comm]
      exact h_c
    exact h_comp.comp_ofReal
  -- IntervalIntegrable of (s ↦ (z₁-z₀) * f(z₀+s(z₁-z₀))) on [0, 1].
  have h_int : IntervalIntegrable
      (fun s : ℝ => (z₁ - z₀) * f (z₀ + (s : ℂ) * (z₁ - z₀)))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have h_inner_cont : Continuous (fun s : ℝ => z₀ + (s : ℂ) * (z₁ - z₀)) := by fun_prop
    have h_f_cont : ContinuousOn f U := hf.continuousOn
    have h_comp_cont : ContinuousOn (fun s : ℝ => f (z₀ + (s : ℂ) * (z₁ - z₀)))
        (Set.Icc (0:ℝ) 1) :=
      h_f_cont.comp h_inner_cont.continuousOn h_seg_mem
    exact continuousOn_const.mul h_comp_cont
  -- Apply FTC.
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hH_deriv h_int
  -- Simplify endpoints: H(1) = starPrimitive p f z₁, H(0) = starPrimitive p f z₀.
  have h_eq_1 : z₀ + ((1 : ℝ) : ℂ) * (z₁ - z₀) = z₁ := by push_cast; ring
  have h_eq_0 : z₀ + ((0 : ℝ) : ℂ) * (z₁ - z₀) = z₀ := by push_cast; ring
  rw [h_eq_1, h_eq_0] at h_ftc
  exact h_ftc

/-- **Cauchy-Goursat for a triangle with one vertex at the star center.** If
`f` is complex-differentiable on an open star-shaped set `U` with star center
`p ∈ U`, and the triangle with vertices `p`, `z₁`, `z₂` lies inside `U`,
then the contour integral around this triangle (traversed `p → z₁ → z₂ → p`)
equals zero. -/
theorem triangleIntegral_eq_zero_of_starShaped
    (hU : IsOpen U) (hSC : StarConvex ℝ p U) (hp : p ∈ U)
    (hf : DifferentiableOn ℂ f U)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ U) (hz₂ : z₂ ∈ U)
    (hseg : segment ℝ z₁ z₂ ⊆ U) :
    (∫ t in (0:ℝ)..1, (z₁ - p) * f (p + (t : ℂ) * (z₁ - p))) +
    (∫ t in (0:ℝ)..1, (z₂ - z₁) * f (z₁ + (t : ℂ) * (z₂ - z₁))) +
    (∫ t in (0:ℝ)..1, (p - z₂) * f (z₂ + (t : ℂ) * (p - z₂))) = 0 := by
  -- Each segment lies in U.
  have hseg_pz₁ : segment ℝ p z₁ ⊆ U := hSC.segment_subset hz₁
  have hseg_z₂p : segment ℝ z₂ p ⊆ U := by
    rw [segment_symm]
    exact hSC.segment_subset hz₂
  -- Apply intervalIntegral_eq_sub_of_starShaped to each segment.
  have h1 := intervalIntegral_eq_sub_of_starShaped (p := p) hU hSC hp hf hp hz₁ hseg_pz₁
  have h2 := intervalIntegral_eq_sub_of_starShaped (p := p) hU hSC hp hf hz₁ hz₂ hseg
  have h3 := intervalIntegral_eq_sub_of_starShaped (p := p) hU hSC hp hf hz₂ hp hseg_z₂p
  -- Sum: (starP z₁ - starP p) + (starP z₂ - starP z₁) + (starP p - starP z₂) = 0.
  linear_combination h1 + h2 + h3

/-! ## Lune-specific support lemmas for `WindingNumber.lean` -/

/-- **Star-convexity of the upper-left-of-`e` open box minus the closed
ball.** For `e : ℂ`, `R₀ > 0`, `a < e.re - R₀`, `e.im + R₀ < d`, the open
set `(Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀` is
star-convex from the outer corner
`V := (e.re - R₀ : ℝ) + (e.im + R₀ : ℝ)·I`.

Geometric content: with `q_x := Q.re - e.re ≤ 0` strict (since
`Q ∈ Ioo a e.re`) and `q_y := Q.im - e.im > 0` strict, the function
`g(t) := |V + t·(Q - V) - e|² - R₀²` is a quadratic in `t ∈ [0, 1]` whose
boundary values `g(0) = R₀² ≥ 0` and `g(1) = |Q - e|² - R₀² ≥ 0` are
non-negative, and whose vertex falls outside `(0, 1)` (or whose minimum
on `(0, 1)` is non-negative by discriminant analysis). -/
theorem topLeftBoxMinusBall_starConvex
    (e : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (a d : ℝ) (_h_a : a < e.re - R₀) (_h_d : e.im + R₀ < d) :
    StarConvex ℝ ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I)
      ((Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀) := by
  sorry

/-- **Star-convexity of the upper-right-of-`e` open box minus the closed
ball.** Mirror of `topLeftBoxMinusBall_starConvex` across `x = e.re`. -/
theorem topRightBoxMinusBall_starConvex
    (e : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (b d : ℝ) (_h_b : e.re + R₀ < b) (_h_d : e.im + R₀ < d) :
    StarConvex ℝ ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I)
      ((Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀) := by
  sorry

/-- **Horizontal segment integral via `starPrimitive`.** For
`V := xV + y·I` and `Z := xZ + y·I` (same imaginary part `y`), the
segment integral from `V` to `Z` of `f` equals
`∫_{xV}^{xZ} f(x + y·I) dx`. Direct change of variables
`x = xV + t·(xZ - xV)` in the segment parameter `t ∈ [0, 1]`. -/
theorem starPrimitive_horizontal_eq_intervalIntegral
    (f : ℂ → ℂ) (xV xZ y : ℝ) :
    Complex.starPrimitive ((xV : ℂ) + (y : ℂ) * Complex.I) f
        ((xZ : ℂ) + (y : ℂ) * Complex.I) =
      ∫ x in xV..xZ, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
  sorry

/-- **Vertical segment integral via `starPrimitive`.** For
`V := x + yV·I` and `Z := x + yZ·I` (same real part `x`), the segment
integral from `V` to `Z` of `f` equals
`Complex.I · ∫_{yV}^{yZ} f(x + y·I) dy`. Direct change of variables
`y = yV + t·(yZ - yV)`. The `Complex.I` factor comes from `Z - V = (yZ - yV)·I`. -/
theorem starPrimitive_vertical_eq_intervalIntegral
    (f : ℂ → ℂ) (x yV yZ : ℝ) :
    Complex.starPrimitive ((x : ℂ) + (yV : ℂ) * Complex.I) f
        ((x : ℂ) + (yZ : ℂ) * Complex.I) =
      Complex.I * ∫ y in yV..yZ, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
  sorry

/-- **Top-left lune arc identity via `starPrimitive`.** For `f` continuous
on the closed top-left lune and complex-differentiable on the upper-left
open box minus closed disk, the arc integral
`∫_{π/2}^π f(circleMap e R₀ θ) · (I·R₀·exp(I·θ)) dθ` equals
`starPrimitive V f B − starPrimitive V f T`, where
`V = (e.re − R₀) + (e.im + R₀)·I`, `T = e.re + (e.im + R₀)·I`,
`B = (e.re − R₀) + e.im·I`.

Proof factors through the ε-arc limit:
* For `ε > 0` small, the slightly outer arc
  `circleMap e (R₀ + ε) θ` on `[π/2 + ε, π − ε]` lies in the
  star-convex open set `U := (Ioo a e.re ×ℂ Ioo e.im d) \ closedBall e R₀`.
* `F := starPrimitive V f` has derivative `f` on `U`
  (`hasDerivAt_starPrimitive` + `topLeftBoxMinusBall_starConvex`).
* Chain rule + `hasDerivAt_circleMap` gives `(F ∘ z_ε)'(θ) = f(z_ε(θ)) · I · (R₀ + ε) · exp(I·θ)`.
* FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` over
  `[π/2 + ε, π − ε]` produces the ε-version of the identity.
* `ε → 0` limit recovers the full arc integral via dominated convergence
  (`f` bounded on a compact thickening of the arc) and continuity of
  `starPrimitive V f` at the endpoints `T` and `B` (which uses `Hc`'s
  continuity of `f` on the closed lune). -/
theorem topLeftLune_arc_integral_eq_starPrimitive_sub
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (a d : ℝ) (_h_a : a < e.re - R₀) (_h_d : e.im + R₀ < d)
    (_Hc : ContinuousOn f
      ((Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀))
    (_Hd : DifferentiableOn ℂ f
      ((Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀)) :
    (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      Complex.starPrimitive
          ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re - R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) -
      Complex.starPrimitive
          ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) := by
  sorry

/-- **Top-right lune arc identity via `starPrimitive`.** Mirror of
`topLeftLune_arc_integral_eq_starPrimitive_sub` across `x = e.re`. The
arc integral over `[0, π/2]` of `f` along `circleMap e R₀` equals
`starPrimitive V_R f T − starPrimitive V_R f W_R`, where
`V_R = (e.re + R₀) + (e.im + R₀)·I`, `T = e.re + (e.im + R₀)·I`,
`W_R = (e.re + R₀) + e.im·I`. -/
theorem topRightLune_arc_integral_eq_starPrimitive_sub
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (b d : ℝ) (_h_b : e.re + R₀ < b) (_h_d : e.im + R₀ < d)
    (_Hc : ContinuousOn f
      ((Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀))
    (_Hd : DifferentiableOn ℂ f
      ((Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀)) :
    (∫ θ in (0:ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) -
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re + R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) := by
  sorry

end Complex

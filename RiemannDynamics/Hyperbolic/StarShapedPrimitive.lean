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

## Lune-specific support lemmas (consumed by `WindingNumber.lean`)

The following lemmas support the closed-form lune Cauchy-Goursat
identities in `RiemannDynamics/Hyperbolic/WindingNumber.lean`:

* `Complex.topLeftBoxMinusBall_starConvex_of_subradius`: the upper-left-of-`e`
  open box minus `closedBall e R₀'` (with `R₀' ≤ R₀`) is star-convex from
  the outer corner `(e.re - R₀) + (e.im + R₀)·I` built from the original
  radius. Geometric content: for any point `Q` in this open set, the
  segment from the outer corner to `Q` stays outside `closedBall e R₀'`.
  Proof factors through a quadratic non-negativity analysis.
* `Complex.topRightBoxMinusBall_starConvex_of_subradius`: mirror across
  `x = e.re`.
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
  proof uses the **strengthened `_Hd`** (analyticity on a slight
  enlargement `closedBall e R₀'` with `R₀' < R₀`) to apply
  `hasDerivAt_starPrimitive` at every arc point, the chain rule with
  `hasDerivAt_circleMap`, and `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
  on `[π/2, π]`. Continuity of the parametrized integral at the arc
  endpoints `θ ∈ {π/2, π}` (where the arc meets the box boundary) is
  obtained via a clamped extension and
  `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`.
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

/-! ## Lune-specific support lemmas for `WindingNumber.lean` -/

/-- **Star-convexity of the upper-left-of-`e` open box minus a closed
ball of radius `R₀' ≤ R₀`.** For `e : ℂ`, `R₀ > 0`, `a < e.re - R₀`,
`e.im + R₀ < d`, and `0 < R₀' ≤ R₀`, the open set
`(Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀'` is
star-convex from the outer corner
`V = (e.re - R₀) + (e.im + R₀) I` (built from the original `R₀`, not
`R₀'`). The chord-avoidance argument: with `α := e.re − Q.re > 0` and
`β := Q.im − e.im > 0` for `Q ∈ Ioo a e.re × Ioo e.im d`, the squared
distance from `e` to a convex combination `sV + tQ` simplifies via the
identity
`(sR₀ + tα)² + (sR₀ + tβ)² − R₀'²
   = s²(2R₀² − R₀'²) + 2st(R₀(α+β) − R₀'²) + t²(α²+β² − R₀'²)`,
each term ≥ 0 with at least one strict (since `R₀ ≥ R₀' > 0` and
`α+β ≥ R₀'` forced by `α²+β² > R₀'²` with `α, β > 0`). -/
theorem topLeftBoxMinusBall_starConvex_of_subradius
    (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀) (R₀' : ℝ) (hR₀' : 0 < R₀')
    (hR₀'_le : R₀' ≤ R₀)
    (a d : ℝ) (h_a : a < e.re - R₀) (h_d : e.im + R₀ < d) :
    StarConvex ℝ ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I)
      ((Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀') := by
  intro Q hQ s t hs ht hst
  obtain ⟨hQ_box, hQ_not_ball⟩ := hQ
  rw [Complex.mem_reProdIm] at hQ_box
  obtain ⟨hQ_re, hQ_im⟩ := hQ_box
  rw [Set.mem_Ioo] at hQ_re hQ_im
  set α : ℝ := e.re - Q.re with hα_def
  set β : ℝ := Q.im - e.im with hβ_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith [hQ_re.2]
  have hβ_pos : 0 < β := by rw [hβ_def]; linarith [hQ_im.1]
  set P : ℂ := s • (((↑(e.re - R₀) : ℂ)) + ((↑(e.im + R₀) : ℂ)) * Complex.I) + t • Q with hP_def
  have hP_re : P.re = s * (e.re - R₀) + t * Q.re := by
    simp [hP_def, Complex.add_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.real_smul]
  have hP_im : P.im = s * (e.im + R₀) + t * Q.im := by
    simp [hP_def, Complex.add_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.real_smul]
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    have hV_re_in_Ioo : (e.re - R₀) ∈ Set.Ioo a e.re :=
      ⟨h_a, by linarith⟩
    have hV_im_in_Ioo : (e.im + R₀) ∈ Set.Ioo e.im d :=
      ⟨by linarith, h_d⟩
    refine ⟨?_, ?_⟩
    · rw [hP_re]
      exact convex_Ioo a e.re hV_re_in_Ioo hQ_re hs ht hst
    · rw [hP_im]
      exact convex_Ioo e.im d hV_im_in_Ioo hQ_im hs ht hst
  · intro hP_in_ball
    rw [Metric.mem_closedBall, Complex.dist_eq] at hP_in_ball
    have h_norm_sq_le : ‖P - e‖^2 ≤ R₀'^2 := by
      nlinarith [hP_in_ball, sq_nonneg (‖P - e‖ - R₀'), norm_nonneg (P - e), hR₀']
    have h_norm_sq_eq : ‖P - e‖^2 = (P.re - e.re)^2 + (P.im - e.im)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, sq]
    rw [h_norm_sq_eq] at h_norm_sq_le
    have h_diff_re : P.re - e.re = -(s * R₀ + t * α) := by
      rw [hP_re, hα_def]; linear_combination e.re * hst
    have h_diff_im : P.im - e.im = s * R₀ + t * β := by
      rw [hP_im, hβ_def]; linear_combination e.im * hst
    rw [h_diff_re, h_diff_im] at h_norm_sq_le
    have hQ_dist_gt : α^2 + β^2 > R₀'^2 := by
      have h_Q_gt : R₀' < ‖Q - e‖ := by
        rw [Metric.mem_closedBall, Complex.dist_eq] at hQ_not_ball
        push Not at hQ_not_ball
        exact hQ_not_ball
      have h_norm_Q_sq : ‖Q - e‖^2 = α^2 + β^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, sq, hα_def, hβ_def]
        ring
      nlinarith [h_Q_gt, sq_nonneg (‖Q - e‖ - R₀'), norm_nonneg (Q - e),
                 h_norm_Q_sq, hR₀']
    have h_σ_ge_R₀' : R₀' ≤ α + β := by
      by_contra h
      push Not at h
      have h_α_lt_R₀' : α < R₀' := by linarith [hβ_pos]
      have h_β_lt_R₀' : β < R₀' := by linarith [hα_pos]
      nlinarith [hQ_dist_gt, mul_pos hα_pos (sub_pos.mpr h_α_lt_R₀'),
                 mul_pos hβ_pos (sub_pos.mpr h_β_lt_R₀')]
    have h_st_pow : s^2 + 2 * s * t + t^2 = 1 := by
      have h_eq : s^2 + 2 * s * t + t^2 = (s + t)^2 := by ring
      rw [h_eq, hst]; norm_num
    have h_identity : (s * R₀ + t * α)^2 + (s * R₀ + t * β)^2 - R₀'^2 =
        s^2 * (2 * R₀^2 - R₀'^2) + 2 * s * t * (R₀ * (α + β) - R₀'^2) +
        t^2 * (α^2 + β^2 - R₀'^2) := by
      have hR' : R₀'^2 = R₀'^2 * (s^2 + 2 * s * t + t^2) := by rw [h_st_pow]; ring
      conv_lhs => rw [hR']
      ring
    have h_2R0_sq_gt : 0 < 2 * R₀^2 - R₀'^2 := by
      have h_sq_le : R₀'^2 ≤ R₀^2 := pow_le_pow_left₀ hR₀'.le hR₀'_le 2
      have h_pos : 0 < R₀^2 := by positivity
      linarith
    have h_cross_nn : 0 ≤ R₀ * (α + β) - R₀'^2 := by
      have h1 : R₀'^2 = R₀' * R₀' := by ring
      have h2 : R₀' * R₀' ≤ R₀ * R₀' := mul_le_mul_of_nonneg_right hR₀'_le hR₀'.le
      have h3 : R₀ * R₀' ≤ R₀ * (α + β) :=
        mul_le_mul_of_nonneg_left h_σ_ge_R₀' hR₀.le
      linarith
    have h_term1_nn : 0 ≤ s^2 * (2 * R₀^2 - R₀'^2) := by positivity
    have h_term2_nn : 0 ≤ 2 * s * t * (R₀ * (α + β) - R₀'^2) := by positivity
    have h_term3_nn : 0 ≤ t^2 * (α^2 + β^2 - R₀'^2) := by
      have : 0 ≤ α^2 + β^2 - R₀'^2 := by linarith [hQ_dist_gt]
      positivity
    have h_key : (s * R₀ + t * α)^2 + (s * R₀ + t * β)^2 > R₀'^2 := by
      rcases hs.lt_or_eq with hs_pos | hs_zero
      · have h_term1_pos : 0 < s^2 * (2 * R₀^2 - R₀'^2) := by positivity
        linarith [h_identity, h_term1_pos, h_term2_nn, h_term3_nn]
      · have ht_one : t = 1 := by linarith
        have h_term3_pos : 0 < t^2 * (α^2 + β^2 - R₀'^2) := by
          rw [ht_one]
          have : 0 < α^2 + β^2 - R₀'^2 := by linarith
          linarith
        linarith [h_identity, h_term1_nn, h_term2_nn, h_term3_pos]
    linarith [h_norm_sq_le, h_key]

/-- **Star-convexity of the upper-right-of-`e` open box minus a shrunken
closed ball.** Mirror of `topLeftBoxMinusBall_starConvex_of_subradius`
across `x = e.re`. -/
theorem topRightBoxMinusBall_starConvex_of_subradius
    (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀) (R₀' : ℝ) (hR₀' : 0 < R₀')
    (hR₀'_le : R₀' ≤ R₀)
    (b d : ℝ) (h_b : e.re + R₀ < b) (h_d : e.im + R₀ < d) :
    StarConvex ℝ ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I)
      ((Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀') := by
  intro Q hQ s t hs ht hst
  obtain ⟨hQ_box, hQ_not_ball⟩ := hQ
  rw [Complex.mem_reProdIm] at hQ_box
  obtain ⟨hQ_re, hQ_im⟩ := hQ_box
  rw [Set.mem_Ioo] at hQ_re hQ_im
  set α : ℝ := Q.re - e.re with hα_def
  set β : ℝ := Q.im - e.im with hβ_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith [hQ_re.1]
  have hβ_pos : 0 < β := by rw [hβ_def]; linarith [hQ_im.1]
  set P : ℂ := s • (((↑(e.re + R₀) : ℂ)) + ((↑(e.im + R₀) : ℂ)) * Complex.I) + t • Q with hP_def
  have hP_re : P.re = s * (e.re + R₀) + t * Q.re := by
    simp [hP_def, Complex.add_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.real_smul]
  have hP_im : P.im = s * (e.im + R₀) + t * Q.im := by
    simp [hP_def, Complex.add_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.real_smul]
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    have hV_re_in_Ioo : (e.re + R₀) ∈ Set.Ioo e.re b :=
      ⟨by linarith, h_b⟩
    have hV_im_in_Ioo : (e.im + R₀) ∈ Set.Ioo e.im d :=
      ⟨by linarith, h_d⟩
    refine ⟨?_, ?_⟩
    · rw [hP_re]
      exact convex_Ioo e.re b hV_re_in_Ioo hQ_re hs ht hst
    · rw [hP_im]
      exact convex_Ioo e.im d hV_im_in_Ioo hQ_im hs ht hst
  · intro hP_in_ball
    rw [Metric.mem_closedBall, Complex.dist_eq] at hP_in_ball
    have h_norm_sq_le : ‖P - e‖^2 ≤ R₀'^2 := by
      nlinarith [hP_in_ball, sq_nonneg (‖P - e‖ - R₀'), norm_nonneg (P - e), hR₀']
    have h_norm_sq_eq : ‖P - e‖^2 = (P.re - e.re)^2 + (P.im - e.im)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, sq]
    rw [h_norm_sq_eq] at h_norm_sq_le
    have h_diff_re : P.re - e.re = s * R₀ + t * α := by
      rw [hP_re, hα_def]; linear_combination e.re * hst
    have h_diff_im : P.im - e.im = s * R₀ + t * β := by
      rw [hP_im, hβ_def]; linear_combination e.im * hst
    rw [h_diff_re, h_diff_im] at h_norm_sq_le
    have hQ_dist_gt : α^2 + β^2 > R₀'^2 := by
      have h_Q_gt : R₀' < ‖Q - e‖ := by
        rw [Metric.mem_closedBall, Complex.dist_eq] at hQ_not_ball
        push Not at hQ_not_ball
        exact hQ_not_ball
      have h_norm_Q_sq : ‖Q - e‖^2 = α^2 + β^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, sq, hα_def, hβ_def]
      nlinarith [h_Q_gt, sq_nonneg (‖Q - e‖ - R₀'), norm_nonneg (Q - e),
                 h_norm_Q_sq, hR₀']
    have h_σ_ge_R₀' : R₀' ≤ α + β := by
      by_contra h
      push Not at h
      have h_α_lt_R₀' : α < R₀' := by linarith [hβ_pos]
      have h_β_lt_R₀' : β < R₀' := by linarith [hα_pos]
      nlinarith [hQ_dist_gt, mul_pos hα_pos (sub_pos.mpr h_α_lt_R₀'),
                 mul_pos hβ_pos (sub_pos.mpr h_β_lt_R₀')]
    have h_st_pow : s^2 + 2 * s * t + t^2 = 1 := by
      have h_eq : s^2 + 2 * s * t + t^2 = (s + t)^2 := by ring
      rw [h_eq, hst]; norm_num
    have h_identity : (s * R₀ + t * α)^2 + (s * R₀ + t * β)^2 - R₀'^2 =
        s^2 * (2 * R₀^2 - R₀'^2) + 2 * s * t * (R₀ * (α + β) - R₀'^2) +
        t^2 * (α^2 + β^2 - R₀'^2) := by
      have hR' : R₀'^2 = R₀'^2 * (s^2 + 2 * s * t + t^2) := by rw [h_st_pow]; ring
      conv_lhs => rw [hR']
      ring
    have h_2R0_sq_gt : 0 < 2 * R₀^2 - R₀'^2 := by
      have h_sq_le : R₀'^2 ≤ R₀^2 := pow_le_pow_left₀ hR₀'.le hR₀'_le 2
      have h_pos : 0 < R₀^2 := by positivity
      linarith
    have h_cross_nn : 0 ≤ R₀ * (α + β) - R₀'^2 := by
      have h1 : R₀'^2 = R₀' * R₀' := by ring
      have h2 : R₀' * R₀' ≤ R₀ * R₀' := mul_le_mul_of_nonneg_right hR₀'_le hR₀'.le
      have h3 : R₀ * R₀' ≤ R₀ * (α + β) :=
        mul_le_mul_of_nonneg_left h_σ_ge_R₀' hR₀.le
      linarith
    have h_term1_nn : 0 ≤ s^2 * (2 * R₀^2 - R₀'^2) := by positivity
    have h_term2_nn : 0 ≤ 2 * s * t * (R₀ * (α + β) - R₀'^2) := by positivity
    have h_term3_nn : 0 ≤ t^2 * (α^2 + β^2 - R₀'^2) := by
      have : 0 ≤ α^2 + β^2 - R₀'^2 := by linarith [hQ_dist_gt]
      positivity
    have h_key : (s * R₀ + t * α)^2 + (s * R₀ + t * β)^2 > R₀'^2 := by
      rcases hs.lt_or_eq with hs_pos | hs_zero
      · have h_term1_pos : 0 < s^2 * (2 * R₀^2 - R₀'^2) := by positivity
        linarith [h_identity, h_term1_pos, h_term2_nn, h_term3_nn]
      · have ht_one : t = 1 := by linarith
        have h_term3_pos : 0 < t^2 * (α^2 + β^2 - R₀'^2) := by
          rw [ht_one]
          have : 0 < α^2 + β^2 - R₀'^2 := by linarith
          linarith
        linarith [h_identity, h_term1_nn, h_term2_nn, h_term3_pos]
    linarith [h_norm_sq_le, h_key]

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
  unfold Complex.starPrimitive
  -- Rewrite the integrand into the form `(xZ - xV : ℝ) • g(xV + (xZ - xV) * t)`
  -- where `g(u) := f(↑u + ↑y · I)`. The `(z - p) = ↑(xZ - xV)` real coercion
  -- means the scalar multiplication is `(xZ - xV : ℝ) • · = ↑(xZ - xV) * ·`.
  have h_eq : ∀ t : ℝ,
      ((xZ : ℂ) + (y : ℂ) * Complex.I - ((xV : ℂ) + (y : ℂ) * Complex.I)) *
          f (((xV : ℂ) + (y : ℂ) * Complex.I) +
              (t : ℂ) * ((xZ : ℂ) + (y : ℂ) * Complex.I -
                ((xV : ℂ) + (y : ℂ) * Complex.I))) =
        (xZ - xV : ℝ) •
          f (((xV + (xZ - xV) * t : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    intro t
    rw [Complex.real_smul]
    have h1 : (xZ : ℂ) + (y : ℂ) * Complex.I - ((xV : ℂ) + (y : ℂ) * Complex.I) =
        ((xZ - xV : ℝ) : ℂ) := by push_cast; ring
    rw [h1]
    have h2 : ((xV : ℂ) + (y : ℂ) * Complex.I) +
        (t : ℂ) * ((xZ - xV : ℝ) : ℂ) =
        ((xV + (xZ - xV) * t : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2]
  rw [intervalIntegral.integral_congr (fun t _ => h_eq t)]
  -- Pull the real scalar out of the integral, then apply the affine substitution lemma.
  have h_smul : (∫ t in (0:ℝ)..1, (xZ - xV : ℝ) •
        f (((xV + (xZ - xV) * t : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      (xZ - xV : ℝ) • ∫ t in (0:ℝ)..1,
        f (((xV + (xZ - xV) * t : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_smul _ _
  have h_subst : ((xZ - xV : ℝ) • ∫ t in (0:ℝ)..1,
        f (((xV + (xZ - xV) * t : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ x in (xV + (xZ - xV) * 0)..(xV + (xZ - xV) * 1),
        f ((x : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.smul_integral_comp_add_mul
      (fun u : ℝ => f ((u : ℂ) + (y : ℂ) * Complex.I)) (xZ - xV) xV
  rw [h_smul, h_subst]
  -- Simplify the bounds.
  congr 1 <;> ring

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
  unfold Complex.starPrimitive
  -- Rewrite the integrand into `I * ((yZ - yV : ℝ) • g(yV + (yZ - yV) * t))`
  -- where `g(v) := f(↑x + ↑v · I)`. The `(z - p) = ↑(yZ - yV) · I` factor
  -- supplies both `I` and the real scalar `(yZ - yV)`.
  have h_eq : ∀ t : ℝ,
      ((x : ℂ) + (yZ : ℂ) * Complex.I - ((x : ℂ) + (yV : ℂ) * Complex.I)) *
          f (((x : ℂ) + (yV : ℂ) * Complex.I) +
              (t : ℂ) * ((x : ℂ) + (yZ : ℂ) * Complex.I -
                ((x : ℂ) + (yV : ℂ) * Complex.I))) =
        Complex.I * ((yZ - yV : ℝ) •
          f ((x : ℂ) + ((yV + (yZ - yV) * t : ℝ) : ℂ) * Complex.I)) := by
    intro t
    rw [Complex.real_smul]
    have h1 : (x : ℂ) + (yZ : ℂ) * Complex.I - ((x : ℂ) + (yV : ℂ) * Complex.I) =
        ((yZ - yV : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1]
    have h2 : ((x : ℂ) + (yV : ℂ) * Complex.I) +
        (t : ℂ) * (((yZ - yV : ℝ) : ℂ) * Complex.I) =
        ((x : ℂ) + ((yV + (yZ - yV) * t : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h2]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => h_eq t)]
  -- Pull `I` out of the integral.
  have h_pull_I : (∫ t in (0:ℝ)..1, Complex.I * ((yZ - yV : ℝ) •
          f ((x : ℂ) + ((yV + (yZ - yV) * t : ℝ) : ℂ) * Complex.I))) =
      Complex.I * ∫ t in (0:ℝ)..1, (yZ - yV : ℝ) •
          f ((x : ℂ) + ((yV + (yZ - yV) * t : ℝ) : ℂ) * Complex.I) :=
    intervalIntegral.integral_const_mul Complex.I _
  rw [h_pull_I]
  -- Pull the real scalar out, then apply the affine-substitution lemma.
  have h_smul : (∫ t in (0:ℝ)..1, (yZ - yV : ℝ) •
          f ((x : ℂ) + ((yV + (yZ - yV) * t : ℝ) : ℂ) * Complex.I)) =
      (yZ - yV : ℝ) • ∫ t in (0:ℝ)..1,
          f ((x : ℂ) + ((yV + (yZ - yV) * t : ℝ) : ℂ) * Complex.I) :=
    intervalIntegral.integral_smul _ _
  have h_subst : ((yZ - yV : ℝ) • ∫ t in (0:ℝ)..1,
          f ((x : ℂ) + ((yV + (yZ - yV) * t : ℝ) : ℂ) * Complex.I)) =
      ∫ y in (yV + (yZ - yV) * 0)..(yV + (yZ - yV) * 1),
          f ((x : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.smul_integral_comp_add_mul
      (fun v : ℝ => f ((x : ℂ) + (v : ℂ) * Complex.I)) (yZ - yV) yV
  rw [h_smul, h_subst]
  -- Bounds: `yV + (yZ - yV) * 0 = yV`, `yV + (yZ - yV) * 1 = yZ`.
  congr 2 <;> ring

/-- **Top-left lune arc identity via `starPrimitive`.** For `f` continuous
on the closed top-left lune and complex-differentiable on the upper-left
open box minus closed disk, the arc integral
`∫_{π/2}^π f(circleMap e R₀ θ) · (I·R₀·exp(I·θ)) dθ` equals
`starPrimitive V f B − starPrimitive V f T`, where
`V = (e.re − R₀) + (e.im + R₀)·I`, `T = e.re + (e.im + R₀)·I`,
`B = (e.re − R₀) + e.im·I`.

**Proof strategy.** Set `Z(θ) := circleMap e R₀ θ` and
`G(θ) := starPrimitive V f (Z(θ))`. The strengthened `_Hd` hypothesis
provides analyticity of `f` on a slightly enlarged set `U' := (Ioo box) \
closedBall e R₀'` with `R₀' < R₀`, which is star-convex from `V` via
`topLeftBoxMinusBall_starConvex_of_subradius`. For `θ ∈ (π/2, π)`, the
arc point `Z(θ)` lies strictly inside `U'` (sphere is at distance
`R₀ > R₀'` from `e`, and the open box constraints are strict), so
`hasDerivAt_starPrimitive` gives `HasDerivAt (starPrimitive V f) (f
(Z(θ))) (Z(θ))`; chain rule with `hasDerivAt_circleMap` yields
`HasDerivAt G (f(Z(θ)) · I·R₀·exp(I·θ)) θ`. For continuity of `G` on
the closed interval `[π/2, π]` (where the endpoint arc points `T, B`
sit on the box boundary, outside `U'`), we use star-convexity of the
**closed** lune `CL := (Icc box) \ ball e R₀` from `V` (proved inline by
the same quadratic identity) plus a clamped extension of the integrand
to `ℝ × ℝ`, then
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`.
Finally `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` on
`[π/2, π]` gives the claimed identity. -/
theorem topLeftLune_arc_integral_eq_starPrimitive_sub
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (a d : ℝ) (_h_a : a < e.re - R₀) (_h_d : e.im + R₀ < d)
    (_Hc : ContinuousOn f
      ((Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀))
    (_Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      Complex.starPrimitive
          ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re - R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) -
      Complex.starPrimitive
          ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) := by
  obtain ⟨R₀', hR₀'_pos, hR₀'_lt, _Hd'⟩ := _Hd
  set V : ℂ := (↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I with hV_def
  set T : ℂ := (↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I with hT_def
  set B : ℂ := (↑(e.re - R₀) : ℂ) + (↑e.im : ℂ) * Complex.I with hB_def
  set U' : Set ℂ :=
    (Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀' with hU'_def
  set CL : Set ℂ :=
    (Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀ with hCL_def
  have hSC' : StarConvex ℝ V U' :=
    topLeftBoxMinusBall_starConvex_of_subradius e R₀ _hR₀ R₀' hR₀'_pos hR₀'_lt.le
      a d _h_a _h_d
  have hU'_open : IsOpen U' :=
    ((isOpen_Ioo.reProdIm isOpen_Ioo).sdiff Metric.isClosed_closedBall)
  -- Circle map endpoint identities.
  have h_Z_pi : _root_.circleMap e R₀ Real.pi = B := by
    rw [hB_def, _root_.circleMap, Complex.exp_mul_I]
    rw [show Complex.cos (↑Real.pi : ℂ) = -1 by
          rw [← Complex.ofReal_cos, Real.cos_pi]; push_cast; ring]
    rw [show Complex.sin (↑Real.pi : ℂ) = 0 by
          rw [← Complex.ofReal_sin, Real.sin_pi]; push_cast; ring]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
    · simp [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_Z_pi_div_two : _root_.circleMap e R₀ (Real.pi / 2) = T := by
    rw [hT_def, _root_.circleMap, Complex.exp_mul_I]
    rw [show Complex.cos ((↑(Real.pi / 2) : ℂ)) = 0 by
          rw [← Complex.ofReal_cos, Real.cos_pi_div_two]; push_cast; ring]
    rw [show Complex.sin ((↑(Real.pi / 2) : ℂ)) = 1 by
          rw [← Complex.ofReal_sin, Real.sin_pi_div_two]; push_cast; ring]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
  -- Geometric: for `θ ∈ Ioo (π/2) π`, `circleMap e R₀ θ ∈ U'`.
  have h_Z_re : ∀ θ : ℝ,
      (_root_.circleMap e R₀ θ).re = e.re + R₀ * Real.cos θ := by
    intro θ
    rw [_root_.circleMap, Complex.exp_mul_I]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h_Z_im : ∀ θ : ℝ,
      (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
    intro θ
    rw [_root_.circleMap, Complex.exp_mul_I]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h_Z_norm : ∀ θ : ℝ, ‖_root_.circleMap e R₀ θ - e‖ = R₀ := by
    intro θ
    rw [_root_.circleMap, show e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
        (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg _hR₀.le,
        Complex.norm_exp_ofReal_mul_I]
    ring
  have h_Z_in_U' : ∀ θ ∈ Set.Ioo (Real.pi / 2) Real.pi,
      _root_.circleMap e R₀ θ ∈ U' := by
    intro θ hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [h_Z_re θ]
        rw [Set.mem_Ioo]
        have h_pi_pos := Real.pi_pos
        have h_cos_neg : Real.cos θ < 0 :=
          Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [hθ.2])
        have h_cos_ge : Real.cos θ ≥ -1 := Real.neg_one_le_cos θ
        refine ⟨?_, ?_⟩
        · have h1 : R₀ * Real.cos θ ≥ R₀ * (-1) :=
            mul_le_mul_of_nonneg_left h_cos_ge _hR₀.le
          linarith [_h_a]
        · have h2 : R₀ * Real.cos θ < 0 := mul_neg_of_pos_of_neg _hR₀ h_cos_neg
          linarith
      · rw [h_Z_im θ]
        rw [Set.mem_Ioo]
        have h_sin_pos : Real.sin θ > 0 :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) hθ.2
        have h_sin_lt : Real.sin θ ≤ 1 := Real.sin_le_one θ
        refine ⟨?_, ?_⟩
        · have h3 : R₀ * Real.sin θ > 0 := mul_pos _hR₀ h_sin_pos
          linarith
        · have h4 : R₀ * Real.sin θ ≤ R₀ * 1 :=
            mul_le_mul_of_nonneg_left h_sin_lt _hR₀.le
          linarith [_h_d]
    · intro h_in_cb
      rw [Metric.mem_closedBall, Complex.dist_eq, h_Z_norm] at h_in_cb
      linarith [hR₀'_lt]
  -- Star-convexity of CL from V.
  have hSC_CL : StarConvex ℝ V CL := by
    intro Q hQ s t hs ht hst
    obtain ⟨hQ_box, hQ_not_ball⟩ := hQ
    rw [Complex.mem_reProdIm] at hQ_box
    obtain ⟨hQ_re, hQ_im⟩ := hQ_box
    rw [Set.mem_Icc] at hQ_re hQ_im
    set α : ℝ := e.re - Q.re with hα_def
    set β : ℝ := Q.im - e.im with hβ_def
    have hα_nn : 0 ≤ α := by rw [hα_def]; linarith [hQ_re.2]
    have hβ_nn : 0 ≤ β := by rw [hβ_def]; linarith [hQ_im.1]
    set P : ℂ := s • V + t • Q with hP_def
    have hP_re : P.re = s * (e.re - R₀) + t * Q.re := by
      simp [hP_def, hV_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.real_smul]
    have hP_im : P.im = s * (e.im + R₀) + t * Q.im := by
      simp [hP_def, hV_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.real_smul]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      have hV_re_in_Icc : (e.re - R₀) ∈ Set.Icc (e.re - R₀) e.re :=
        ⟨le_refl _, by linarith [_hR₀]⟩
      have hV_im_in_Icc : (e.im + R₀) ∈ Set.Icc e.im (e.im + R₀) :=
        ⟨by linarith [_hR₀], le_refl _⟩
      refine ⟨?_, ?_⟩
      · rw [hP_re]
        exact (convex_Icc _ _).segment_subset hV_re_in_Icc hQ_re
          ⟨s, t, hs, ht, hst, rfl⟩
      · rw [hP_im]
        exact (convex_Icc _ _).segment_subset hV_im_in_Icc hQ_im
          ⟨s, t, hs, ht, hst, rfl⟩
    · intro hP_in_ball
      rw [Metric.mem_ball, Complex.dist_eq] at hP_in_ball
      have h_norm_sq_lt : ‖P - e‖^2 < R₀^2 := by
        nlinarith [hP_in_ball, sq_nonneg (R₀ - ‖P - e‖), norm_nonneg (P - e), _hR₀]
      have h_norm_sq_eq : ‖P - e‖^2 = (P.re - e.re)^2 + (P.im - e.im)^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, sq]
      rw [h_norm_sq_eq] at h_norm_sq_lt
      have h_diff_re : P.re - e.re = -(s * R₀ + t * α) := by
        rw [hP_re, hα_def]; linear_combination e.re * hst
      have h_diff_im : P.im - e.im = s * R₀ + t * β := by
        rw [hP_im, hβ_def]; linear_combination e.im * hst
      rw [h_diff_re, h_diff_im] at h_norm_sq_lt
      have hQ_norm_ge : α^2 + β^2 ≥ R₀^2 := by
        have h_Q_ge : R₀ ≤ ‖Q - e‖ := by
          rw [Metric.mem_ball, Complex.dist_eq] at hQ_not_ball
          push Not at hQ_not_ball
          exact hQ_not_ball
        have h_norm_Q_sq : ‖Q - e‖^2 = α^2 + β^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im, sq, hα_def, hβ_def]
          ring
        nlinarith [h_Q_ge, sq_nonneg (‖Q - e‖ - R₀), norm_nonneg (Q - e), h_norm_Q_sq]
      have h_σ_ge_R₀ : R₀ ≤ α + β := by
        by_contra h
        push Not at h
        rcases lt_or_ge α R₀ with hα_lt | hα_ge
        · rcases lt_or_ge β R₀ with hβ_lt | hβ_ge
          · nlinarith [hQ_norm_ge, mul_nonneg hα_nn (sub_nonneg.mpr hα_lt.le),
                       mul_nonneg hβ_nn (sub_nonneg.mpr hβ_lt.le)]
          · linarith
        · linarith
      have h_st_pow : s^2 + 2 * s * t + t^2 = 1 := by
        have h_eq : s^2 + 2 * s * t + t^2 = (s + t)^2 := by ring
        rw [h_eq, hst]; norm_num
      have h_identity : (s * R₀ + t * α)^2 + (s * R₀ + t * β)^2 - R₀^2 =
          s^2 * R₀^2 + 2 * s * t * R₀ * (α + β - R₀) + t^2 * (α^2 + β^2 - R₀^2) := by
        have hR' : R₀^2 = R₀^2 * (s^2 + 2 * s * t + t^2) := by rw [h_st_pow]; ring
        conv_lhs => rw [hR']
        ring
      have h_term1_nn : 0 ≤ s^2 * R₀^2 := by positivity
      have h_term2_nn : 0 ≤ 2 * s * t * R₀ * (α + β - R₀) := by
        have : 0 ≤ α + β - R₀ := by linarith
        positivity
      have h_term3_nn : 0 ≤ t^2 * (α^2 + β^2 - R₀^2) := by
        have : 0 ≤ α^2 + β^2 - R₀^2 := by linarith
        positivity
      linarith [h_identity, h_term1_nn, h_term2_nn, h_term3_nn, h_norm_sq_lt]
  -- For θ ∈ Icc (π/2) π, Z(θ) ∈ CL.
  have h_Z_in_CL : ∀ θ ∈ Set.Icc (Real.pi / 2) Real.pi,
      _root_.circleMap e R₀ θ ∈ CL := by
    intro θ hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [h_Z_re θ]
        rw [Set.mem_Icc]
        have h_pi_pos := Real.pi_pos
        have h_cos_le : Real.cos θ ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
        have h_cos_ge : Real.cos θ ≥ -1 := Real.neg_one_le_cos θ
        refine ⟨?_, ?_⟩
        · have h1 : R₀ * Real.cos θ ≥ R₀ * (-1) :=
            mul_le_mul_of_nonneg_left h_cos_ge _hR₀.le
          linarith
        · have h2 : R₀ * Real.cos θ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos _hR₀.le h_cos_le
          linarith
      · rw [h_Z_im θ]
        rw [Set.mem_Icc]
        have h_sin_nn : Real.sin θ ≥ 0 := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          · linarith [hθ.1, Real.pi_pos]
          · exact hθ.2
        have h_sin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
        exact ⟨by linarith [mul_nonneg _hR₀.le h_sin_nn],
               by linarith [mul_le_of_le_one_right _hR₀.le h_sin_le]⟩
    · intro h_in_ball
      rw [Metric.mem_ball, Complex.dist_eq, h_Z_norm] at h_in_ball
      exact lt_irrefl R₀ h_in_ball
  -- f continuous on CL.
  have hf_cont_CL : ContinuousOn f CL := _Hc
  -- f continuous on U' (subset of CL? No, U' uses Ioo box and closedBall e R₀'.
  -- U' ∩ box not necessarily in CL. But f differentiable on U' implies continuous on U').
  have hf_cont_U' : ContinuousOn f U' := _Hd'.continuousOn
  -- V ∈ U'.
  have hV_in_U' : V ∈ U' := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hV_def]
        simp only [Complex.ofReal_sub, Complex.add_re, Complex.sub_re,
          Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, add_zero, Complex.I_im,
          mul_one, sub_self, Set.mem_Ioo, sub_lt_self_iff]
        exact ⟨_h_a, by linarith [_hR₀]⟩
      · rw [hV_def]
        simp only [Complex.ofReal_sub, Complex.add_im, Complex.sub_im,
          Complex.ofReal_im, sub_self, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, add_zero, Complex.I_re,
          mul_zero, zero_add, Set.mem_Ioo, lt_add_iff_pos_right]
        exact ⟨by linarith [_hR₀], _h_d⟩
    · intro hV_ball
      rw [Metric.mem_closedBall, Complex.dist_eq] at hV_ball
      have h_V_e_sq : ‖V - e‖^2 = 2 * R₀^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        rw [hV_def]
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
              Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, sq]
        ring
      nlinarith [hV_ball, sq_nonneg (‖V - e‖ - R₀'), norm_nonneg (V - e), _hR₀,
                 hR₀'_pos, hR₀'_lt, h_V_e_sq]
  -- Define G(θ) := starPrimitive V f (Z(θ)).
  set G : ℝ → ℂ := fun θ => Complex.starPrimitive V f (_root_.circleMap e R₀ θ)
    with hG_def
  -- Derivative of `Z` (circleMap) at θ.
  have h_circle_deriv : ∀ θ : ℝ, HasDerivAt (_root_.circleMap e R₀)
      (_root_.circleMap 0 R₀ θ * Complex.I) θ := fun θ => hasDerivAt_circleMap _ _ _
  -- Derivative of G on Ioo (π/2) π.
  have h_G_deriv : ∀ θ ∈ Set.Ioo (Real.pi / 2) Real.pi,
      HasDerivAt G (f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) θ := by
    intro θ hθ
    have hZθ : _root_.circleMap e R₀ θ ∈ U' := h_Z_in_U' θ hθ
    have h_prim_deriv : HasDerivAt (Complex.starPrimitive V f)
        (f (_root_.circleMap e R₀ θ)) (_root_.circleMap e R₀ θ) :=
      Complex.hasDerivAt_starPrimitive hU'_open hSC' _Hd' hZθ
    have h_chain := h_prim_deriv.comp θ (h_circle_deriv θ)
    have h_circle0 : _root_.circleMap 0 R₀ θ * Complex.I =
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [_root_.circleMap,
          show ((θ : ℂ) * Complex.I) = Complex.I * (θ : ℂ) from mul_comm _ _]
      ring
    rw [h_circle0] at h_chain
    exact h_chain
  -- Continuity of G on Icc (π/2) π via parametric integral continuity.
  -- Define F(θ, t) := (Z(θ_c) - V) * f(V + t_c · (Z(θ_c) - V)) with clamped θ_c, t_c.
  set θ_clamp : ℝ → ℝ := fun θ => min Real.pi (max (Real.pi / 2) θ) with hθ_clamp_def
  set t_clamp : ℝ → ℝ := fun t => min 1 (max 0 t) with ht_clamp_def
  have h_θ_clamp_cont : Continuous θ_clamp := by
    apply Continuous.min continuous_const
    exact Continuous.max continuous_const continuous_id
  have h_t_clamp_cont : Continuous t_clamp := by
    apply Continuous.min continuous_const
    exact Continuous.max continuous_const continuous_id
  have h_θ_clamp_mem : ∀ θ, θ_clamp θ ∈ Set.Icc (Real.pi / 2) Real.pi := by
    intro θ
    refine ⟨?_, ?_⟩
    · have h_pi_le : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
      exact le_min h_pi_le (le_max_left _ _)
    · exact min_le_left _ _
  have h_θ_clamp_id : ∀ θ ∈ Set.Icc (Real.pi / 2) Real.pi, θ_clamp θ = θ := by
    intro θ hθ
    change min Real.pi (max (Real.pi / 2) θ) = θ
    rw [max_eq_right hθ.1, min_eq_right hθ.2]
  have h_t_clamp_mem : ∀ t, t_clamp t ∈ Set.Icc (0:ℝ) 1 := by
    intro t
    refine ⟨?_, ?_⟩
    · exact le_min zero_le_one (le_max_left _ _)
    · exact min_le_left _ _
  have h_t_clamp_id : ∀ t ∈ Set.Icc (0:ℝ) 1, t_clamp t = t := by
    intro t ht
    change min 1 (max 0 t) = t
    rw [max_eq_right ht.1, min_eq_right ht.2]
  -- Inner point V + t_c · (Z(θ_c) - V) lies in CL.
  set F_inner : ℝ × ℝ → ℂ :=
    fun p => V + (t_clamp p.2 : ℂ) * (_root_.circleMap e R₀ (θ_clamp p.1) - V)
    with hF_inner_def
  have hF_inner_cont : Continuous F_inner := by
    apply Continuous.add continuous_const
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (h_t_clamp_cont.comp continuous_snd)
    · apply Continuous.sub
      · exact (continuous_circleMap _ _).comp
          (h_θ_clamp_cont.comp continuous_fst)
      · exact continuous_const
  have hF_inner_mem : ∀ p : ℝ × ℝ, F_inner p ∈ CL := by
    intro p
    have hZ_mem : _root_.circleMap e R₀ (θ_clamp p.1) ∈ CL :=
      h_Z_in_CL _ (h_θ_clamp_mem p.1)
    have ht_mem : t_clamp p.2 ∈ Set.Icc (0:ℝ) 1 := h_t_clamp_mem p.2
    have h_sum : (1 - t_clamp p.2) + t_clamp p.2 = 1 := by ring
    have h_s_nn : (0 : ℝ) ≤ 1 - t_clamp p.2 := by linarith [ht_mem.2]
    have h_t_nn : (0 : ℝ) ≤ t_clamp p.2 := ht_mem.1
    have h_sc := hSC_CL hZ_mem h_s_nn h_t_nn h_sum
    -- h_sc : (1 - t_clamp p.2) • V + (t_clamp p.2) • (circleMap...) ∈ CL.
    -- Show F_inner p = (1 - t_clamp p.2) • V + (t_clamp p.2) • (circleMap...).
    change V + (t_clamp p.2 : ℂ) * (_root_.circleMap e R₀ (θ_clamp p.1) - V) ∈ CL
    have h_eq : V + (t_clamp p.2 : ℂ) * (_root_.circleMap e R₀ (θ_clamp p.1) - V) =
        (1 - t_clamp p.2 : ℝ) • V + (t_clamp p.2 : ℝ) •
          _root_.circleMap e R₀ (θ_clamp p.1) := by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
    rw [h_eq]
    exact h_sc
  -- F (full integrand) is continuous.
  set F : ℝ × ℝ → ℂ :=
    fun p => (_root_.circleMap e R₀ (θ_clamp p.1) - V) * f (F_inner p)
    with hF_def
  have hF_cont : Continuous F := by
    apply Continuous.mul
    · apply Continuous.sub
      · exact (continuous_circleMap _ _).comp
          (h_θ_clamp_cont.comp continuous_fst)
      · exact continuous_const
    · exact hf_cont_CL.comp_continuous hF_inner_cont hF_inner_mem
  -- Apply parametric integral continuity:
  -- `Continuous fun θ => ∫_0^1 F (θ, t) dt`.
  have h_G_global_cont :
      Continuous (fun θ : ℝ => ∫ t in (0:ℝ)..1, F (θ, t)) := by
    have h_uncurry : Function.uncurry (fun θ t => F (θ, t)) = F := rfl
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0) (f := fun θ t => F (θ, t))
      (by rw [h_uncurry]; exact hF_cont) (s := fun _ => 1) continuous_const
    exact this
  -- For θ ∈ Icc (π/2) π, the integral equals G θ (clamping is identity).
  have h_integral_eq_G : Set.EqOn (fun θ => ∫ t in (0:ℝ)..1, F (θ, t)) G
      (Set.Icc (Real.pi / 2) Real.pi) := by
    intro θ hθ
    have hθc : θ_clamp θ = θ := h_θ_clamp_id θ hθ
    change (∫ t in (0:ℝ)..1, F (θ, t)) = G θ
    have h_G_unfold : G θ =
        ∫ t in (0:ℝ)..1, (_root_.circleMap e R₀ θ - V) *
          f (V + (t : ℂ) * (_root_.circleMap e R₀ θ - V)) := by
      change Complex.starPrimitive V f (_root_.circleMap e R₀ θ) = _
      unfold Complex.starPrimitive
      rfl
    rw [h_G_unfold]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact ht
    change (_root_.circleMap e R₀ (θ_clamp θ) - V) *
        f (V + (t_clamp t : ℂ) * (_root_.circleMap e R₀ (θ_clamp θ) - V)) =
      (_root_.circleMap e R₀ θ - V) *
        f (V + (t : ℂ) * (_root_.circleMap e R₀ θ - V))
    rw [hθc, h_t_clamp_id t ht_Icc]
  -- G is continuous on Icc (π/2) π.
  have h_G_cont : ContinuousOn G (Set.Icc (Real.pi / 2) Real.pi) :=
    (h_G_global_cont.continuousOn).congr h_integral_eq_G.symm
  -- Integrability of G' on [π/2, π].
  have h_G'_cont_on : ContinuousOn (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      (Set.Icc (Real.pi / 2) Real.pi) := by
    apply ContinuousOn.mul
    · exact hf_cont_CL.comp (continuous_circleMap _ _).continuousOn h_Z_in_CL
    · exact (Continuous.mul (Continuous.mul continuous_const continuous_const)
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).continuousOn
  have h_pi_le_for_int : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h_G'_int : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume (Real.pi / 2) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_le_for_int]
    exact h_G'_cont_on
  -- Apply FTC.
  have h_pi_le : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    h_pi_le h_G_cont h_G_deriv h_G'_int
  rw [h_FTC]
  have h_G_at_pi : G Real.pi = Complex.starPrimitive V f B := by
    simp only [hG_def, h_Z_pi]
  have h_G_at_pi_div_two : G (Real.pi / 2) = Complex.starPrimitive V f T := by
    simp only [hG_def, h_Z_pi_div_two]
  rw [h_G_at_pi, h_G_at_pi_div_two]

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
    (_Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    (∫ θ in (0:ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) -
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re + R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) := by
  obtain ⟨R₀', hR₀'_pos, hR₀'_lt, _Hd'⟩ := _Hd
  set V_R : ℂ := (↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I with hV_R_def
  set T : ℂ := (↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I with hT_def
  set W_R : ℂ := (↑(e.re + R₀) : ℂ) + (↑e.im : ℂ) * Complex.I with hW_R_def
  set U' : Set ℂ :=
    (Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀' with hU'_def
  set CL_R : Set ℂ :=
    (Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀
    with hCL_R_def
  have hSC' : StarConvex ℝ V_R U' :=
    topRightBoxMinusBall_starConvex_of_subradius e R₀ _hR₀ R₀' hR₀'_pos hR₀'_lt.le
      b d _h_b _h_d
  have hU'_open : IsOpen U' :=
    ((isOpen_Ioo.reProdIm isOpen_Ioo).sdiff Metric.isClosed_closedBall)
  -- Circle map endpoint identities.
  have h_Z_0 : _root_.circleMap e R₀ 0 = W_R := by
    rw [hW_R_def, _root_.circleMap]
    have h_exp_0 : Complex.exp ((0 : ℝ) * Complex.I) = 1 := by
      rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    rw [h_exp_0]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_Z_pi_div_two : _root_.circleMap e R₀ (Real.pi / 2) = T := by
    rw [hT_def, _root_.circleMap, Complex.exp_mul_I]
    rw [show Complex.cos ((↑(Real.pi / 2) : ℂ)) = 0 by
          rw [← Complex.ofReal_cos, Real.cos_pi_div_two]; push_cast; ring]
    rw [show Complex.sin ((↑(Real.pi / 2) : ℂ)) = 1 by
          rw [← Complex.ofReal_sin, Real.sin_pi_div_two]; push_cast; ring]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
  have h_Z_re : ∀ θ : ℝ,
      (_root_.circleMap e R₀ θ).re = e.re + R₀ * Real.cos θ := by
    intro θ
    rw [_root_.circleMap, Complex.exp_mul_I]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h_Z_im : ∀ θ : ℝ,
      (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
    intro θ
    rw [_root_.circleMap, Complex.exp_mul_I]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h_Z_norm : ∀ θ : ℝ, ‖_root_.circleMap e R₀ θ - e‖ = R₀ := by
    intro θ
    rw [_root_.circleMap, show e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
        (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg _hR₀.le,
        Complex.norm_exp_ofReal_mul_I]
    ring
  -- For θ ∈ Ioo 0 (π/2), Z(θ) ∈ U'.
  have h_Z_in_U' : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      _root_.circleMap e R₀ θ ∈ U' := by
    intro θ hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [h_Z_re θ]
        rw [Set.mem_Ioo]
        have h_pi_pos := Real.pi_pos
        have h_cos_pos : Real.cos θ > 0 :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, h_pi_pos], hθ.2⟩
        have h_cos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
        refine ⟨?_, ?_⟩
        · have h1 : R₀ * Real.cos θ > 0 := mul_pos _hR₀ h_cos_pos
          linarith
        · have h2 : R₀ * Real.cos θ ≤ R₀ * 1 :=
            mul_le_mul_of_nonneg_left h_cos_le _hR₀.le
          linarith [_h_b]
      · rw [h_Z_im θ]
        rw [Set.mem_Ioo]
        have h_sin_pos : Real.sin θ > 0 :=
          Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
        have h_sin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
        refine ⟨?_, ?_⟩
        · have h3 : R₀ * Real.sin θ > 0 := mul_pos _hR₀ h_sin_pos
          linarith
        · have h4 : R₀ * Real.sin θ ≤ R₀ * 1 :=
            mul_le_mul_of_nonneg_left h_sin_le _hR₀.le
          linarith [_h_d]
    · intro h_in_cb
      rw [Metric.mem_closedBall, Complex.dist_eq, h_Z_norm] at h_in_cb
      linarith [hR₀'_lt]
  -- Star-convexity of CL_R from V_R.
  have hSC_CL_R : StarConvex ℝ V_R CL_R := by
    intro Q hQ s t hs ht hst
    obtain ⟨hQ_box, hQ_not_ball⟩ := hQ
    rw [Complex.mem_reProdIm] at hQ_box
    obtain ⟨hQ_re, hQ_im⟩ := hQ_box
    rw [Set.mem_Icc] at hQ_re hQ_im
    set α : ℝ := Q.re - e.re with hα_def
    set β : ℝ := Q.im - e.im with hβ_def
    have hα_nn : 0 ≤ α := by rw [hα_def]; linarith [hQ_re.1]
    have hβ_nn : 0 ≤ β := by rw [hβ_def]; linarith [hQ_im.1]
    set P : ℂ := s • V_R + t • Q with hP_def
    have hP_re : P.re = s * (e.re + R₀) + t * Q.re := by
      simp [hP_def, hV_R_def, Complex.add_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.real_smul]
    have hP_im : P.im = s * (e.im + R₀) + t * Q.im := by
      simp [hP_def, hV_R_def, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.real_smul]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      have hV_re_in_Icc : (e.re + R₀) ∈ Set.Icc e.re (e.re + R₀) :=
        ⟨by linarith [_hR₀], le_refl _⟩
      have hV_im_in_Icc : (e.im + R₀) ∈ Set.Icc e.im (e.im + R₀) :=
        ⟨by linarith [_hR₀], le_refl _⟩
      refine ⟨?_, ?_⟩
      · rw [hP_re]
        exact (convex_Icc _ _).segment_subset hV_re_in_Icc hQ_re
          ⟨s, t, hs, ht, hst, rfl⟩
      · rw [hP_im]
        exact (convex_Icc _ _).segment_subset hV_im_in_Icc hQ_im
          ⟨s, t, hs, ht, hst, rfl⟩
    · intro hP_in_ball
      rw [Metric.mem_ball, Complex.dist_eq] at hP_in_ball
      have h_norm_sq_lt : ‖P - e‖^2 < R₀^2 := by
        nlinarith [hP_in_ball, sq_nonneg (R₀ - ‖P - e‖), norm_nonneg (P - e), _hR₀]
      have h_norm_sq_eq : ‖P - e‖^2 = (P.re - e.re)^2 + (P.im - e.im)^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, sq]
      rw [h_norm_sq_eq] at h_norm_sq_lt
      have h_diff_re : P.re - e.re = s * R₀ + t * α := by
        rw [hP_re, hα_def]; linear_combination e.re * hst
      have h_diff_im : P.im - e.im = s * R₀ + t * β := by
        rw [hP_im, hβ_def]; linear_combination e.im * hst
      rw [h_diff_re, h_diff_im] at h_norm_sq_lt
      have hQ_norm_ge : α^2 + β^2 ≥ R₀^2 := by
        have h_Q_ge : R₀ ≤ ‖Q - e‖ := by
          rw [Metric.mem_ball, Complex.dist_eq] at hQ_not_ball
          push Not at hQ_not_ball
          exact hQ_not_ball
        have h_norm_Q_sq : ‖Q - e‖^2 = α^2 + β^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im, sq, hα_def, hβ_def]
        nlinarith [h_Q_ge, sq_nonneg (‖Q - e‖ - R₀), norm_nonneg (Q - e), h_norm_Q_sq]
      have h_σ_ge_R₀ : R₀ ≤ α + β := by
        by_contra h
        push Not at h
        rcases lt_or_ge α R₀ with hα_lt | hα_ge
        · rcases lt_or_ge β R₀ with hβ_lt | hβ_ge
          · nlinarith [hQ_norm_ge, mul_nonneg hα_nn (sub_nonneg.mpr hα_lt.le),
                       mul_nonneg hβ_nn (sub_nonneg.mpr hβ_lt.le)]
          · linarith
        · linarith
      have h_st_pow : s^2 + 2 * s * t + t^2 = 1 := by
        have h_eq : s^2 + 2 * s * t + t^2 = (s + t)^2 := by ring
        rw [h_eq, hst]; norm_num
      have h_identity : (s * R₀ + t * α)^2 + (s * R₀ + t * β)^2 - R₀^2 =
          s^2 * R₀^2 + 2 * s * t * R₀ * (α + β - R₀) + t^2 * (α^2 + β^2 - R₀^2) := by
        have hR' : R₀^2 = R₀^2 * (s^2 + 2 * s * t + t^2) := by rw [h_st_pow]; ring
        conv_lhs => rw [hR']
        ring
      have h_term1_nn : 0 ≤ s^2 * R₀^2 := by positivity
      have h_term2_nn : 0 ≤ 2 * s * t * R₀ * (α + β - R₀) := by
        have : 0 ≤ α + β - R₀ := by linarith
        positivity
      have h_term3_nn : 0 ≤ t^2 * (α^2 + β^2 - R₀^2) := by
        have : 0 ≤ α^2 + β^2 - R₀^2 := by linarith
        positivity
      linarith [h_identity, h_term1_nn, h_term2_nn, h_term3_nn, h_norm_sq_lt]
  -- For θ ∈ Icc 0 (π/2), Z(θ) ∈ CL_R.
  have h_Z_in_CL_R : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2),
      _root_.circleMap e R₀ θ ∈ CL_R := by
    intro θ hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [h_Z_re θ]
        rw [Set.mem_Icc]
        have h_pi_pos := Real.pi_pos
        have h_cos_nn : Real.cos θ ≥ 0 :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
        have h_cos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
        refine ⟨?_, ?_⟩
        · have h1 : R₀ * Real.cos θ ≥ 0 := mul_nonneg _hR₀.le h_cos_nn
          linarith
        · have h2 : R₀ * Real.cos θ ≤ R₀ * 1 :=
            mul_le_mul_of_nonneg_left h_cos_le _hR₀.le
          linarith
      · rw [h_Z_im θ]
        rw [Set.mem_Icc]
        have h_pi_pos := Real.pi_pos
        have h_sin_nn : Real.sin θ ≥ 0 :=
          Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
        have h_sin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
        refine ⟨?_, ?_⟩
        · have h3 : R₀ * Real.sin θ ≥ 0 := mul_nonneg _hR₀.le h_sin_nn
          linarith
        · have h4 : R₀ * Real.sin θ ≤ R₀ * 1 :=
            mul_le_mul_of_nonneg_left h_sin_le _hR₀.le
          linarith
    · intro h_in_ball
      rw [Metric.mem_ball, Complex.dist_eq, h_Z_norm] at h_in_ball
      exact lt_irrefl R₀ h_in_ball
  -- f continuous on CL_R.
  have hf_cont_CL_R : ContinuousOn f CL_R := _Hc
  -- f continuous on U'.
  have hf_cont_U' : ContinuousOn f U' := _Hd'.continuousOn
  -- V_R ∈ U'.
  have hV_R_in_U' : V_R ∈ U' := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hV_R_def]
        simp only [Complex.ofReal_add, Complex.add_re,
          Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im,
          mul_one, sub_self, Set.mem_Ioo, lt_add_iff_pos_right]
        exact ⟨_hR₀, _h_b⟩
      · rw [hV_R_def]
        simp only [Complex.ofReal_add, Complex.add_im,
          Complex.ofReal_im, Complex.mul_im, Complex.add_re,
          Complex.ofReal_re, Complex.I_im, mul_one, add_zero, Complex.I_re,
          mul_zero, zero_add, Set.mem_Ioo, lt_add_iff_pos_right]
        exact ⟨_hR₀, _h_d⟩
    · intro hV_R_ball
      rw [Metric.mem_closedBall, Complex.dist_eq] at hV_R_ball
      have h_V_R_e_sq : ‖V_R - e‖^2 = 2 * R₀^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        rw [hV_R_def]
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
              Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, sq]
        ring
      nlinarith [hV_R_ball, sq_nonneg (‖V_R - e‖ - R₀'), norm_nonneg (V_R - e),
                 _hR₀, hR₀'_pos, hR₀'_lt, h_V_R_e_sq]
  -- Define G(θ) := starPrimitive V_R f (Z(θ)).
  set G : ℝ → ℂ := fun θ => Complex.starPrimitive V_R f (_root_.circleMap e R₀ θ)
    with hG_def
  -- Derivative of `Z` (circleMap) at θ.
  have h_circle_deriv : ∀ θ : ℝ, HasDerivAt (_root_.circleMap e R₀)
      (_root_.circleMap 0 R₀ θ * Complex.I) θ := fun θ => hasDerivAt_circleMap _ _ _
  -- Derivative of G on Ioo 0 (π/2).
  have h_G_deriv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      HasDerivAt G (f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) θ := by
    intro θ hθ
    have hZθ : _root_.circleMap e R₀ θ ∈ U' := h_Z_in_U' θ hθ
    have h_prim_deriv : HasDerivAt (Complex.starPrimitive V_R f)
        (f (_root_.circleMap e R₀ θ)) (_root_.circleMap e R₀ θ) :=
      Complex.hasDerivAt_starPrimitive hU'_open hSC' _Hd' hZθ
    have h_chain := h_prim_deriv.comp θ (h_circle_deriv θ)
    have h_circle0 : _root_.circleMap 0 R₀ θ * Complex.I =
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [_root_.circleMap,
          show ((θ : ℂ) * Complex.I) = Complex.I * (θ : ℂ) from mul_comm _ _]
      ring
    rw [h_circle0] at h_chain
    exact h_chain
  -- Continuity of G on Icc 0 (π/2) via parametric integral continuity.
  set θ_clamp : ℝ → ℝ := fun θ => min (Real.pi / 2) (max 0 θ) with hθ_clamp_def
  set t_clamp : ℝ → ℝ := fun t => min 1 (max 0 t) with ht_clamp_def
  have h_θ_clamp_cont : Continuous θ_clamp := by
    apply Continuous.min continuous_const
    exact Continuous.max continuous_const continuous_id
  have h_t_clamp_cont : Continuous t_clamp := by
    apply Continuous.min continuous_const
    exact Continuous.max continuous_const continuous_id
  have h_pi_div_two_pos : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h_θ_clamp_mem : ∀ θ, θ_clamp θ ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
    intro θ
    refine ⟨?_, ?_⟩
    · exact le_min h_pi_div_two_pos (le_max_left _ _)
    · exact min_le_left _ _
  have h_θ_clamp_id : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2), θ_clamp θ = θ := by
    intro θ hθ
    change min (Real.pi / 2) (max 0 θ) = θ
    rw [max_eq_right hθ.1, min_eq_right hθ.2]
  have h_t_clamp_mem : ∀ t, t_clamp t ∈ Set.Icc (0:ℝ) 1 := by
    intro t
    refine ⟨?_, ?_⟩
    · exact le_min zero_le_one (le_max_left _ _)
    · exact min_le_left _ _
  have h_t_clamp_id : ∀ t ∈ Set.Icc (0:ℝ) 1, t_clamp t = t := by
    intro t ht
    change min 1 (max 0 t) = t
    rw [max_eq_right ht.1, min_eq_right ht.2]
  set F_inner : ℝ × ℝ → ℂ :=
    fun p => V_R + (t_clamp p.2 : ℂ) * (_root_.circleMap e R₀ (θ_clamp p.1) - V_R)
    with hF_inner_def
  have hF_inner_cont : Continuous F_inner := by
    apply Continuous.add continuous_const
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (h_t_clamp_cont.comp continuous_snd)
    · apply Continuous.sub
      · exact (continuous_circleMap _ _).comp
          (h_θ_clamp_cont.comp continuous_fst)
      · exact continuous_const
  have hF_inner_mem : ∀ p : ℝ × ℝ, F_inner p ∈ CL_R := by
    intro p
    have hZ_mem : _root_.circleMap e R₀ (θ_clamp p.1) ∈ CL_R :=
      h_Z_in_CL_R _ (h_θ_clamp_mem p.1)
    have ht_mem : t_clamp p.2 ∈ Set.Icc (0:ℝ) 1 := h_t_clamp_mem p.2
    have h_sum : (1 - t_clamp p.2) + t_clamp p.2 = 1 := by ring
    have h_s_nn : (0 : ℝ) ≤ 1 - t_clamp p.2 := by linarith [ht_mem.2]
    have h_t_nn : (0 : ℝ) ≤ t_clamp p.2 := ht_mem.1
    have h_sc := hSC_CL_R hZ_mem h_s_nn h_t_nn h_sum
    change V_R + (t_clamp p.2 : ℂ) * (_root_.circleMap e R₀ (θ_clamp p.1) - V_R) ∈ CL_R
    have h_eq : V_R + (t_clamp p.2 : ℂ) *
        (_root_.circleMap e R₀ (θ_clamp p.1) - V_R) =
        (1 - t_clamp p.2 : ℝ) • V_R + (t_clamp p.2 : ℝ) •
          _root_.circleMap e R₀ (θ_clamp p.1) := by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
    rw [h_eq]
    exact h_sc
  set F : ℝ × ℝ → ℂ :=
    fun p => (_root_.circleMap e R₀ (θ_clamp p.1) - V_R) * f (F_inner p)
    with hF_def
  have hF_cont : Continuous F := by
    apply Continuous.mul
    · apply Continuous.sub
      · exact (continuous_circleMap _ _).comp
          (h_θ_clamp_cont.comp continuous_fst)
      · exact continuous_const
    · exact hf_cont_CL_R.comp_continuous hF_inner_cont hF_inner_mem
  have h_G_global_cont :
      Continuous (fun θ : ℝ => ∫ t in (0:ℝ)..1, F (θ, t)) := by
    have h_uncurry : Function.uncurry (fun θ t => F (θ, t)) = F := rfl
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0) (f := fun θ t => F (θ, t))
      (by rw [h_uncurry]; exact hF_cont) (s := fun _ => 1) continuous_const
    exact this
  have h_integral_eq_G : Set.EqOn (fun θ => ∫ t in (0:ℝ)..1, F (θ, t)) G
      (Set.Icc (0:ℝ) (Real.pi / 2)) := by
    intro θ hθ
    have hθc : θ_clamp θ = θ := h_θ_clamp_id θ hθ
    change (∫ t in (0:ℝ)..1, F (θ, t)) = G θ
    have h_G_unfold : G θ =
        ∫ t in (0:ℝ)..1, (_root_.circleMap e R₀ θ - V_R) *
          f (V_R + (t : ℂ) * (_root_.circleMap e R₀ θ - V_R)) := by
      change Complex.starPrimitive V_R f (_root_.circleMap e R₀ θ) = _
      unfold Complex.starPrimitive
      rfl
    rw [h_G_unfold]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact ht
    change (_root_.circleMap e R₀ (θ_clamp θ) - V_R) *
        f (V_R + (t_clamp t : ℂ) *
          (_root_.circleMap e R₀ (θ_clamp θ) - V_R)) =
      (_root_.circleMap e R₀ θ - V_R) *
        f (V_R + (t : ℂ) * (_root_.circleMap e R₀ θ - V_R))
    rw [hθc, h_t_clamp_id t ht_Icc]
  have h_G_cont : ContinuousOn G (Set.Icc (0:ℝ) (Real.pi / 2)) :=
    (h_G_global_cont.continuousOn).congr h_integral_eq_G.symm
  -- Integrability of G' on [0, π/2].
  have h_G'_cont_on : ContinuousOn (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      (Set.Icc (0:ℝ) (Real.pi / 2)) := by
    apply ContinuousOn.mul
    · exact hf_cont_CL_R.comp (continuous_circleMap _ _).continuousOn h_Z_in_CL_R
    · exact (Continuous.mul (Continuous.mul continuous_const continuous_const)
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).continuousOn
  have h_G'_int : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume (0:ℝ) (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_div_two_pos]
    exact h_G'_cont_on
  -- Apply FTC.
  have h_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    h_pi_div_two_pos h_G_cont h_G_deriv h_G'_int
  rw [h_FTC]
  have h_G_at_0 : G 0 = Complex.starPrimitive V_R f W_R := by
    simp only [hG_def, h_Z_0]
  have h_G_at_pi_div_two : G (Real.pi / 2) = Complex.starPrimitive V_R f T := by
    simp only [hG_def, h_Z_pi_div_two]
  rw [h_G_at_0, h_G_at_pi_div_two]

end Complex

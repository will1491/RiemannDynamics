/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.FluxEnergy.SlitFlux
import RiemannDynamics.Analysis.GrotzschRing.GrotzschPotential

/-!
# Tip regularity of the Grötzsch potential

Let `v` be the harmonic potential of the Grötzsch ring `grotzschRing s` (`0 < s < 1`): harmonic on
the ring, continuous on the closed disk, `0` on the slit `[0, s]` and `1` on the unit circle. Near
each tip of the slit the potential has square-root behaviour. This file proves the tip bounds used
by the flux–energy assembly.

The proof unfolds the square-root singularity by the holomorphic square map. At the far tip `s` the
map `φ_s : ζ ↦ s + ζ²` sends the right half-disk `{Re ζ > 0} ∩ ball 0 ρ` into the ring minus the
slit, sends the imaginary diameter into the slit, and covers a punctured slit-neighbourhood of `s`.
The pullback `V := v ∘ φ_s` is therefore harmonic on the right half-disk, continuous up to the
imaginary diameter, and vanishes there. Rotating the imaginary diameter to the real axis
(`ζ ↦ i·ζ`) and applying the odd-reflection principle `harmonicOnNhd_of_odd_reflection` yields a
function `W` harmonic on a full ball with `W(0) = 0`. Harmonic functions are smooth, so `W` and its
gradient are bounded on a smaller closed ball, giving `v z ≤ C·√‖z − s‖` and
`‖gradC v z‖ ≤ C·‖z − s‖^(−1/2)`. The near tip `0` is handled by the reflected map `ζ ↦ −ζ²`, whose
branch cut lies along `[0, ∞)`, hence along the slit near `0`.

## Main results

* `harmonicOnNhd_comp_holomorph` — precomposition of a harmonic function with an entire map is
  harmonic on the preimage of the harmonicity domain.
* `grotzschPotential_tip_bound_far`, `grotzschPotential_tip_bound_near` — the `√‖z − s‖` and `√‖z‖`
  upper bounds for `v` near the far tip `s` and the near tip `0`.
* `grotzschPotential_grad_tip_bound_far`, `grotzschPotential_grad_tip_bound_near` — the
  `‖z − s‖^(−1/2)` and `‖z‖^(−1/2)` bounds for `‖gradC v‖` near the two tips.
* `grotzschPotential_flux_bound_far`, `grotzschPotential_flux_bound_near` — the product
  `v · ‖gradC v‖` is bounded near each tip, the deliverable the flux integrand needs there.
-/

open MeasureTheory Filter Metric Topology Complex

open scoped Real Topology

namespace RiemannDynamics

/-! ## Harmonicity along an entire chart -/

/-- **Harmonicity along an entire chart.** For `u` harmonic on an open set `V ⊆ ℂ` and `g` entire,
the composition `u ∘ g` is harmonic on `g ⁻¹' V`: locally `u` is the real part of a holomorphic
primitive `F`, so `u ∘ g` is locally the real part of the holomorphic `F ∘ g`. -/
theorem harmonicOnNhd_comp_holomorph {u : ℂ → ℝ} {V : Set ℂ} {g : ℂ → ℂ} (hV : IsOpen V)
    (hu : InnerProductSpace.HarmonicOnNhd u V) (hg : ∀ w : ℂ, AnalyticAt ℂ g w) :
    InnerProductSpace.HarmonicOnNhd (fun w => u (g w)) (g ⁻¹' V) := by
  intro w₀ hw₀
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.1 hV (g w₀) hw₀
  obtain ⟨F, hFanal, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (hu.mono hRsub)
  have hcomp := AnalyticAt.comp (g := F) (f := g)
    (hFanal _ (Metric.mem_ball_self hR)) (hg w₀)
  have hFg : InnerProductSpace.HarmonicAt (fun w => (F (g w)).re) w₀ :=
    AnalyticAt.harmonicAt_re hcomp
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hFg
  have hnhds : g ⁻¹' Metric.ball (g w₀) R ∈ 𝓝 w₀ :=
    (hg w₀).continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
  filter_upwards [hnhds] with w hw using hFeq hw

/-! ## The square-unfolding chart at the far tip `s`

The chart is `η ↦ s − η²`. Its diameter is the real axis, which maps into the slit; the interior
half `{Im η > 0}` maps into the ring off the slit. This aligns the reflection with the real axis,
matching `harmonicOnNhd_of_odd_reflection`. -/

/-- The imaginary part of `s − η²` is `−2·(Re η)·(Im η)`. -/
theorem tipFar_im (s : ℝ) (η : ℂ) : ((s : ℂ) - η ^ 2).im = -(2 * η.re * η.im) := by
  simp only [Complex.sub_im, Complex.ofReal_im, pow_two, Complex.mul_im]; ring

/-- The real part of `s − η²` is `s − (Re η)² + (Im η)²`. -/
theorem tipFar_re (s : ℝ) (η : ℂ) : ((s : ℂ) - η ^ 2).re = s - η.re ^ 2 + η.im ^ 2 := by
  simp only [Complex.sub_re, Complex.ofReal_re, pow_two, Complex.mul_re]; ring

/-- **The upper half-disk avoids the slit under the square chart.** For `Im η > 0`, the image
`s − η²` does not lie on the closed slit `[0, s]`: if it were real then `Re η = 0`, forcing
`Re (s − η²) = s + (Im η)² > s`. -/
theorem tipFar_notMem_slit {s : ℝ} (hs0 : 0 ≤ s) {η : ℂ} (hη : 0 < η.im) :
    ((s : ℂ) - η ^ 2) ∉ grotzschInner s := by
  intro hmem
  rw [grotzschInner_eq hs0] at hmem
  obtain ⟨him, _, hle⟩ := hmem
  rw [tipFar_im] at him
  have hre0 : η.re = 0 := by
    have h : 2 * η.re * η.im = 0 := by linarith [neg_eq_zero.mp him]
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact h2
    · exact absurd h1 (ne_of_gt hη)
  rw [tipFar_re, hre0] at hle
  nlinarith [hle, hη]

/-- **The square chart maps the small upper half-disk into the disk.** For `‖η‖² < 1 − s` (and
`0 ≤ s`), the image `s − η²` lies in the open unit disk. -/
theorem tipFar_mem_ball {s : ℝ} (hs0 : 0 ≤ s) {η : ℂ}
    (hη : ‖η‖ ^ 2 < 1 - s) : ((s : ℂ) - η ^ 2) ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  calc ‖(s : ℂ) - η ^ 2‖ ≤ ‖(s : ℂ)‖ + ‖η ^ 2‖ := norm_sub_le _ _
    _ = s + ‖η‖ ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, norm_pow]
    _ < s + (1 - s) := by linarith
    _ = 1 := by ring

/-- **The square chart maps the upper half-disk into the ring.** For `Im η > 0` and `‖η‖² < 1 − s`
(with `0 ≤ s`), the image `s − η²` lies in `grotzschRing s`. -/
theorem tipFar_mem_ring {s : ℝ} (hs0 : 0 ≤ s) {η : ℂ}
    (hη : 0 < η.im) (hηn : ‖η‖ ^ 2 < 1 - s) : ((s : ℂ) - η ^ 2) ∈ grotzschRing s :=
  ⟨tipFar_mem_ball hs0 hηn, tipFar_notMem_slit hs0 hη⟩

/-- **The real diameter maps into the slit under the square chart.** For `Im η = 0` and
`(Re η)² ≤ s`, the image `s − η²` lies on the closed slit `[0, s]` (it equals `s − (Re η)²`). -/
theorem tipFar_mem_slit {s : ℝ} (hs0 : 0 ≤ s) {η : ℂ} (him : η.im = 0)
    (hre : η.re ^ 2 ≤ s) : ((s : ℂ) - η ^ 2) ∈ grotzschInner s := by
  rw [grotzschInner_eq hs0]
  refine ⟨by rw [tipFar_im, him]; ring, ?_, ?_⟩
  · rw [tipFar_re, him]; nlinarith [hre, sq_nonneg η.re]
  · rw [tipFar_re, him]; nlinarith [sq_nonneg η.re]

/-! ## The square-unfolding chart at the near tip `0`

The chart is `η ↦ η²`. Its diameter is the real axis, which maps into the slit `[0, s]` (small
positive squares); the interior half `{Im η > 0}` maps into the ring off the slit. -/

/-- The imaginary part of `η²` is `2·(Re η)·(Im η)`. -/
theorem tipNear_im (η : ℂ) : (η ^ 2).im = 2 * η.re * η.im := by
  simp only [pow_two, Complex.mul_im]; ring

/-- The real part of `η²` is `(Re η)² − (Im η)²`. -/
theorem tipNear_re (η : ℂ) : (η ^ 2).re = η.re ^ 2 - η.im ^ 2 := by
  rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two]

/-- **The upper half-disk avoids the slit under the near-tip chart.** For `Im η > 0`, the image
`η²` does not lie on the closed slit `[0, s]`: if it were real then `Re η = 0`, forcing
`Re (η²) = −(Im η)² < 0`. -/
theorem tipNear_notMem_slit {s : ℝ} (hs0 : 0 ≤ s) {η : ℂ} (hη : 0 < η.im) :
    (η ^ 2) ∉ grotzschInner s := by
  intro hmem
  rw [grotzschInner_eq hs0] at hmem
  obtain ⟨him, hge, _⟩ := hmem
  rw [tipNear_im] at him
  have hre0 : η.re = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact h2
    · exact absurd h1 (ne_of_gt hη)
  rw [tipNear_re, hre0] at hge
  nlinarith [hge, hη]

/-- **The near-tip chart maps the small upper half-disk into the disk.** For `‖η‖² < 1`, the
image `η²` lies in the open unit disk. -/
theorem tipNear_mem_ball {η : ℂ} (hη : ‖η‖ ^ 2 < 1) : (η ^ 2) ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  calc ‖η ^ 2‖ = ‖η‖ ^ 2 := norm_pow η 2
    _ < 1 := hη

/-- **The near-tip chart maps the upper half-disk into the ring.** For `Im η > 0` and `‖η‖² < 1`
(with `0 ≤ s`), the image `η²` lies in `grotzschRing s`. -/
theorem tipNear_mem_ring {s : ℝ} (hs0 : 0 ≤ s) {η : ℂ}
    (hη : 0 < η.im) (hηn : ‖η‖ ^ 2 < 1) : (η ^ 2) ∈ grotzschRing s :=
  ⟨tipNear_mem_ball hηn, tipNear_notMem_slit hs0 hη⟩

/-- **The real diameter maps into the slit under the near-tip chart.** For `Im η = 0` and
`(Re η)² ≤ s`, the image `η²` lies on the closed slit `[0, s]` (it equals `(Re η)²`). -/
theorem tipNear_mem_slit {s : ℝ} (hs0 : 0 ≤ s) {η : ℂ} (him : η.im = 0)
    (hre : η.re ^ 2 ≤ s) : (η ^ 2) ∈ grotzschInner s := by
  rw [grotzschInner_eq hs0]
  refine ⟨by rw [tipNear_im, him]; ring, ?_, ?_⟩
  · rw [tipNear_re, him]; nlinarith [sq_nonneg η.re]
  · rw [tipNear_re, him]; nlinarith [hre, sq_nonneg η.re]

/-! ## An upper-half square root -/

/-- **Upper-half square root.** Every `w : ℂ` has a square root in the closed upper half-plane,
whose norm is `√‖w‖`. This provides, for each `z` near a tip, the chart preimage `η` with
`η² = s − z` (resp. `η² = z`) landing in the upper half-disk. -/
theorem exists_upperHalf_sqrt (w : ℂ) :
    ∃ η : ℂ, η ^ 2 = w ∧ 0 ≤ η.im ∧ ‖η‖ = Real.sqrt ‖w‖ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
  have hnorm : ‖z‖ = Real.sqrt ‖w‖ := by
    rw [← hz, norm_pow, Real.sqrt_sq (norm_nonneg z)]
  rcases le_or_gt 0 z.im with him | him
  · exact ⟨z, hz, him, hnorm⟩
  · refine ⟨-z, by rw [neg_pow, hz]; ring, by simp; linarith, by rw [norm_neg]; exact hnorm⟩

/-! ## Reflection across the far tip -/

/-- **The reflected pullback at the far tip `s`.** For the Grötzsch potential `v` there is a radius
`ρ > 0` and a function `W` harmonic on `ball 0 ρ` with `W 0 = 0` and `W η = v (s − η²)` for every
`η` in the closed upper half-disk of radius `ρ`. The function `W` is the odd reflection across the
real axis of the pullback `η ↦ v (s − η²)`, harmonic by the odd-reflection principle. -/
theorem exists_reflected_harmonic_far {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ W : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd W (Metric.ball (0 : ℂ) ρ) ∧ W 0 = 0 ∧
      (∀ η : ℂ, 0 ≤ η.im → ‖η‖ < ρ → W η = v ((s : ℂ) - η ^ 2)) := by
  -- chart, pullback and its odd reflection
  set g : ℂ → ℂ := fun η => (s : ℂ) - η ^ 2 with hg
  set V : ℂ → ℝ := fun η => v (g η) with hV
  -- radius `ρ` with `ρ² ≤ s` (real diameter stays in the slit) and `ρ² < 1 − s` (stay in the disk)
  set ρ : ℝ := Real.sqrt (min s (1 - s) / 2) with hρdef
  have hmin : 0 < min s (1 - s) := lt_min hs0 (by linarith)
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hρsq : ρ ^ 2 = min s (1 - s) / 2 := Real.sq_sqrt (by positivity)
  have hρs : ρ ^ 2 ≤ s := by rw [hρsq]; have := min_le_left s (1 - s); linarith
  have hρ1 : ρ ^ 2 < 1 - s := by rw [hρsq]; have := min_le_right s (1 - s); linarith
  have hg_entire : ∀ w : ℂ, AnalyticAt ℂ g w := fun w =>
    analyticAt_const.sub (analyticAt_id.pow 2)
  have hg_cont : Continuous g := by fun_prop
  -- norm / real-part control on the closed ball
  have hballnorm : ∀ η ∈ Metric.closedBall (0 : ℂ) ρ, ‖η‖ ^ 2 < 1 - s ∧ η.re ^ 2 ≤ s := by
    intro η hη
    rw [Metric.mem_closedBall, dist_zero_right] at hη
    have hnsq : ‖η‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [norm_nonneg η, hρpos.le]
    have hre : η.re ^ 2 ≤ ‖η‖ ^ 2 := by
      have := Complex.abs_re_le_norm η
      nlinarith [Complex.abs_re_le_norm η, abs_nonneg η.re, sq_abs η.re, norm_nonneg η]
    exact ⟨lt_of_le_of_lt hnsq hρ1, le_trans hre (le_trans hnsq hρs)⟩
  have hgcl : Metric.closedBall (0 : ℂ) 1 = closure (grotzschRing s) :=
    (closure_grotzschRing hs0.le).symm
  have hg_maps_disk : ∀ η ∈ Metric.closedBall (0 : ℂ) ρ, g η ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun η hη => Metric.ball_subset_closedBall (tipFar_mem_ball hs0.le (hballnorm η hη).1)
  -- `V` is continuous on the closed ball (chart into closed disk, `v` continuous there)
  have hVc : ContinuousOn V (Metric.closedBall (0 : ℂ) ρ) := by
    refine ContinuousOn.comp (t := closure (grotzschRing s)) (hvc.mono (le_refl _))
      hg_cont.continuousOn (fun η hη => ?_)
    rw [← hgcl]; exact hg_maps_disk η hη
  -- vanishing of `V` on the real diameter of the closed ball
  have hVzero : ∀ η ∈ Metric.closedBall (0 : ℂ) ρ, η.im = 0 → V η = 0 := by
    intro η hη hηim
    exact hv0 _ (tipFar_mem_slit hs0.le hηim (hballnorm η hη).2)
  -- continuity of the reflection on the closed ball, gluing the two half-balls
  have hVconjc : ContinuousOn (fun η => -V ((starRingEnd ℂ) η)) (Metric.closedBall (0 : ℂ) ρ) := by
    have hmaps : Set.MapsTo (starRingEnd ℂ) (Metric.closedBall (0 : ℂ) ρ)
        (Metric.closedBall (0 : ℂ) ρ) := fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right, RCLike.norm_conj]
      rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz
    exact (hVc.comp Complex.continuous_conj.continuousOn hmaps).neg
  have hcont : ContinuousOn (reflectReal V) (Metric.closedBall (0 : ℂ) ρ) := by
    have hup : ContinuousOn (reflectReal V)
        (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im}) :=
      (hVc.mono Set.inter_subset_left).congr fun z hz => reflectReal_of_im_nonneg hz.2
    have hlow : ContinuousOn (reflectReal V)
        (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
      refine (hVconjc.mono Set.inter_subset_left).congr fun z hz => ?_
      have hz2 : z.im ≤ 0 := hz.2
      rcases eq_or_lt_of_le hz2 with him | him
      · have hvz : V z = 0 := hVzero z hz.1 him
        rw [reflectReal_of_im_nonneg (le_of_eq him.symm), hvz]
        have hzfix : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr him
        simp only [hzfix, hvz, neg_zero]
      · rw [reflectReal, if_neg (by linarith)]
    have hcover : Metric.closedBall (0 : ℂ) ρ
        = (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im})
          ∪ (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
      rw [← Set.inter_union_distrib_left]
      ext z; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
      exact ⟨fun hz => ⟨hz, le_total 0 z.im⟩, fun hz => hz.1⟩
    rw [hcover]
    exact hup.union_of_isClosed hlow
      (Metric.isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im))
      (Metric.isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const))
  -- glue the reflection: apply the odd-reflection principle
  have hcfix : (starRingEnd ℂ) (0 : ℂ) = (0 : ℂ) := by simp
  refine ⟨ρ, hρpos, reflectReal V, ?_, ?_, ?_⟩
  · -- harmonicity of the reflection on the ball
    refine harmonicOnNhd_of_odd_reflection hcfix hρpos ?_ hcont ?_ ?_
    · -- off-axis harmonicity
      intro η hη
      obtain ⟨hηball, hηim⟩ := hη
      rw [Metric.mem_ball, dist_zero_right] at hηball
      have hηnormsq : ‖η‖ ^ 2 < 1 - s := by nlinarith [norm_nonneg η, hρpos.le]
      rcases lt_trichotomy η.im 0 with hneg | h0 | hpos
      · -- lower half: `reflectReal V = -V ∘ conj`, harmonic by conjugation
        have hconjupper : 0 < ((starRingEnd ℂ) η).im := by simp only [Complex.conj_im]; linarith
        have hconjnorm : ‖(starRingEnd ℂ) η‖ ^ 2 < 1 - s := by
          rw [RCLike.norm_conj]; exact hηnormsq
        have hVharm : InnerProductSpace.HarmonicAt V ((starRingEnd ℂ) η) :=
          (harmonicOnNhd_comp_holomorph (isOpen_grotzschRing hs0.le) hvh hg_entire) _
            (tipFar_mem_ring hs0.le hconjupper hconjnorm)
        have hconjharm : InnerProductSpace.HarmonicAt (fun w => V ((starRingEnd ℂ) w)) η := by
          have hpt : InnerProductSpace.HarmonicAt V (Complex.conjLIE η) := by
            rw [show Complex.conjLIE η = (starRingEnd ℂ) η from Complex.conjLIE_apply η]
            exact hVharm
          have h := harmonicAt_comp_linearIsometryEquiv Complex.conjLIE hpt
          refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp h
          exact Filter.Eventually.of_forall fun y => by
            simp [Function.comp_apply, Complex.conjLIE_apply]
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hconjharm.neg
        filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with y hy
        rw [Pi.neg_apply, reflectReal, if_neg (not_le.mpr hy)]
      · exact absurd h0 hηim
      · -- upper half: `reflectReal V = V`, harmonic on the ring pullback
        have hVharm : InnerProductSpace.HarmonicAt V η :=
          (harmonicOnNhd_comp_holomorph (isOpen_grotzschRing hs0.le) hvh hg_entire) _
            (tipFar_mem_ring hs0.le hpos hηnormsq)
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hVharm
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with y hy
        rw [reflectReal_of_im_nonneg hy.le]
    · -- vanishing on the real diameter
      intro η hηcl hηim
      rw [reflectReal_of_im_nonneg hηim.ge]; exact hVzero η hηcl hηim
    · -- oddness of the reflection on the closed ball
      intro η hηcl
      simp only [reflectReal, Complex.conj_im, Complex.conj_conj]
      rcases lt_trichotomy η.im 0 with h | h | h
      · rw [if_pos (by linarith : (0:ℝ) ≤ -η.im), if_neg (by linarith : ¬ (0:ℝ) ≤ η.im), neg_neg]
      · rw [if_pos (by rw [h, neg_zero]), if_pos (le_of_eq h.symm)]
        have hzfix : (starRingEnd ℂ) η = η := Complex.conj_eq_iff_im.mpr h
        rw [hzfix, hVzero η hηcl h, neg_zero]
      · rw [if_neg (by linarith : ¬ (0:ℝ) ≤ -η.im), if_pos h.le]
  · rw [reflectReal_of_im_nonneg (le_refl (0:ℂ).im)]
    exact hVzero 0 (Metric.mem_closedBall_self hρpos.le) rfl
  · intro η hηim hηnorm
    rw [reflectReal_of_im_nonneg hηim]

/-! ## Reflection across the near tip -/

/-- **The reflected pullback at the near tip `0`.** For the Grötzsch potential `v` there is a
radius `ρ > 0` and a function `W` harmonic on `ball 0 ρ` with `W 0 = 0` and `W η = v (η²)` for every
`η` in the closed upper half-disk of radius `ρ`. -/
theorem exists_reflected_harmonic_near {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ W : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd W (Metric.ball (0 : ℂ) ρ) ∧ W 0 = 0 ∧
      (∀ η : ℂ, 0 ≤ η.im → ‖η‖ < ρ → W η = v (η ^ 2)) := by
  -- chart, pullback and its odd reflection
  set g : ℂ → ℂ := fun η => η ^ 2 with hg
  set V : ℂ → ℝ := fun η => v (g η) with hV
  -- radius `ρ` with `ρ² ≤ s` (real diameter stays in the slit, and hence in the disk)
  set ρ : ℝ := Real.sqrt (s / 2) with hρdef
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hρsq : ρ ^ 2 = s / 2 := Real.sq_sqrt (by positivity)
  have hρs : ρ ^ 2 ≤ s := by rw [hρsq]; linarith
  have hg_entire : ∀ w : ℂ, AnalyticAt ℂ g w := fun w => analyticAt_id.pow 2
  have hg_cont : Continuous g := by fun_prop
  -- norm / real-part control on the closed ball
  have hballnorm : ∀ η ∈ Metric.closedBall (0 : ℂ) ρ, ‖η‖ ^ 2 < 1 ∧ η.re ^ 2 ≤ s := by
    intro η hη
    rw [Metric.mem_closedBall, dist_zero_right] at hη
    have hnsq : ‖η‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [norm_nonneg η, hρpos.le]
    have hre : η.re ^ 2 ≤ ‖η‖ ^ 2 := by
      nlinarith [Complex.abs_re_le_norm η, abs_nonneg η.re, sq_abs η.re, norm_nonneg η]
    exact ⟨lt_of_le_of_lt (le_trans hnsq hρs) hs1, le_trans hre (le_trans hnsq hρs)⟩
  have hgcl : Metric.closedBall (0 : ℂ) 1 = closure (grotzschRing s) :=
    (closure_grotzschRing hs0.le).symm
  have hg_maps_disk : ∀ η ∈ Metric.closedBall (0 : ℂ) ρ, g η ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun η hη => Metric.ball_subset_closedBall (tipNear_mem_ball (hballnorm η hη).1)
  -- `V` is continuous on the closed ball
  have hVc : ContinuousOn V (Metric.closedBall (0 : ℂ) ρ) := by
    refine ContinuousOn.comp (t := closure (grotzschRing s)) (hvc.mono (le_refl _))
      hg_cont.continuousOn (fun η hη => ?_)
    rw [← hgcl]; exact hg_maps_disk η hη
  -- vanishing of `V` on the real diameter
  have hVzero : ∀ η ∈ Metric.closedBall (0 : ℂ) ρ, η.im = 0 → V η = 0 := by
    intro η hη hηim
    exact hv0 _ (tipNear_mem_slit hs0.le hηim (hballnorm η hη).2)
  -- continuity of the reflection on the closed ball, gluing the two half-balls
  have hVconjc : ContinuousOn (fun η => -V ((starRingEnd ℂ) η)) (Metric.closedBall (0 : ℂ) ρ) := by
    have hmaps : Set.MapsTo (starRingEnd ℂ) (Metric.closedBall (0 : ℂ) ρ)
        (Metric.closedBall (0 : ℂ) ρ) := fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right, RCLike.norm_conj]
      rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz
    exact (hVc.comp Complex.continuous_conj.continuousOn hmaps).neg
  have hcont : ContinuousOn (reflectReal V) (Metric.closedBall (0 : ℂ) ρ) := by
    have hup : ContinuousOn (reflectReal V)
        (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im}) :=
      (hVc.mono Set.inter_subset_left).congr fun z hz => reflectReal_of_im_nonneg hz.2
    have hlow : ContinuousOn (reflectReal V)
        (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
      refine (hVconjc.mono Set.inter_subset_left).congr fun z hz => ?_
      have hz2 : z.im ≤ 0 := hz.2
      rcases eq_or_lt_of_le hz2 with him | him
      · have hvz : V z = 0 := hVzero z hz.1 him
        rw [reflectReal_of_im_nonneg (le_of_eq him.symm), hvz]
        have hzfix : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr him
        simp only [hzfix, hvz, neg_zero]
      · rw [reflectReal, if_neg (by linarith)]
    have hcover : Metric.closedBall (0 : ℂ) ρ
        = (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im})
          ∪ (Metric.closedBall (0 : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
      rw [← Set.inter_union_distrib_left]
      ext z; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
      exact ⟨fun hz => ⟨hz, le_total 0 z.im⟩, fun hz => hz.1⟩
    rw [hcover]
    exact hup.union_of_isClosed hlow
      (Metric.isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im))
      (Metric.isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const))
  have hcfix : (starRingEnd ℂ) (0 : ℂ) = (0 : ℂ) := by simp
  refine ⟨ρ, hρpos, reflectReal V, ?_, ?_, ?_⟩
  · refine harmonicOnNhd_of_odd_reflection hcfix hρpos ?_ hcont ?_ ?_
    · intro η hη
      obtain ⟨hηball, hηim⟩ := hη
      rw [Metric.mem_ball, dist_zero_right] at hηball
      have hηnormsq : ‖η‖ ^ 2 < 1 := by nlinarith [norm_nonneg η, hρpos.le, hρs, hs1]
      rcases lt_trichotomy η.im 0 with hneg | h0 | hpos
      · have hconjupper : 0 < ((starRingEnd ℂ) η).im := by simp only [Complex.conj_im]; linarith
        have hconjnorm : ‖(starRingEnd ℂ) η‖ ^ 2 < 1 := by rw [RCLike.norm_conj]; exact hηnormsq
        have hVharm : InnerProductSpace.HarmonicAt V ((starRingEnd ℂ) η) :=
          (harmonicOnNhd_comp_holomorph (isOpen_grotzschRing hs0.le) hvh hg_entire) _
            (tipNear_mem_ring hs0.le hconjupper hconjnorm)
        have hconjharm : InnerProductSpace.HarmonicAt (fun w => V ((starRingEnd ℂ) w)) η := by
          have hpt : InnerProductSpace.HarmonicAt V (Complex.conjLIE η) := by
            rw [show Complex.conjLIE η = (starRingEnd ℂ) η from Complex.conjLIE_apply η]
            exact hVharm
          have h := harmonicAt_comp_linearIsometryEquiv Complex.conjLIE hpt
          refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp h
          exact Filter.Eventually.of_forall fun y => by
            simp [Function.comp_apply, Complex.conjLIE_apply]
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hconjharm.neg
        filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with y hy
        rw [Pi.neg_apply, reflectReal, if_neg (not_le.mpr hy)]
      · exact absurd h0 hηim
      · have hVharm : InnerProductSpace.HarmonicAt V η :=
          (harmonicOnNhd_comp_holomorph (isOpen_grotzschRing hs0.le) hvh hg_entire) _
            (tipNear_mem_ring hs0.le hpos hηnormsq)
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hVharm
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with y hy
        rw [reflectReal_of_im_nonneg hy.le]
    · intro η hηcl hηim
      rw [reflectReal_of_im_nonneg hηim.ge]; exact hVzero η hηcl hηim
    · intro η hηcl
      simp only [reflectReal, Complex.conj_im, Complex.conj_conj]
      rcases lt_trichotomy η.im 0 with h | h | h
      · rw [if_pos (by linarith : (0:ℝ) ≤ -η.im), if_neg (by linarith : ¬ (0:ℝ) ≤ η.im), neg_neg]
      · rw [if_pos (by rw [h, neg_zero]), if_pos (le_of_eq h.symm)]
        have hzfix : (starRingEnd ℂ) η = η := Complex.conj_eq_iff_im.mpr h
        rw [hzfix, hVzero η hηcl h, neg_zero]
      · rw [if_neg (by linarith : ¬ (0:ℝ) ≤ -η.im), if_pos h.le]
  · rw [reflectReal_of_im_nonneg (le_refl (0:ℂ).im)]
    exact hVzero 0 (Metric.mem_closedBall_self hρpos.le) rfl
  · intro η hηim hηnorm
    rw [reflectReal_of_im_nonneg hηim]

/-! ## Local Lipschitz and gradient bounds for a harmonic function vanishing at the centre -/

/-- **Harmonic Lipschitz bound at a zero.** A function harmonic on `ball 0 ρ` with `W 0 = 0` obeys
`‖W η‖ ≤ C‖η‖` and `‖gradC W η‖ ≤ C` on the closed half-radius ball, for some `C ≥ 0`: `gradC W` is
holomorphic hence bounded on the compact closed ball, and integrating the gradient from the origin
bounds `W`. -/
theorem exists_harmonic_lipschitz_at_zero {ρ : ℝ} (hρ : 0 < ρ) {W : ℂ → ℝ}
    (hWh : InnerProductSpace.HarmonicOnNhd W (Metric.ball (0 : ℂ) ρ)) (hW0 : W 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ η ∈ Metric.closedBall (0 : ℂ) (ρ / 2), ‖W η‖ ≤ C * ‖η‖) ∧
      (∀ η ∈ Metric.closedBall (0 : ℂ) (ρ / 2), ‖gradC W η‖ ≤ C) := by
  have hρ2pos : 0 < ρ / 2 := by linarith
  have hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball (0 : ℂ) ρ :=
    fun z hz => Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
  -- `gradC W` is holomorphic on the ball, hence continuous on the compact closed half-ball
  have hgWcont : ContinuousOn (gradC W) (Metric.closedBall (0 : ℂ) (ρ / 2)) := fun z hz =>
    ((gradC_differentiableOn hWh).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn hgWcont
  refine ⟨max C₀ 0, le_max_right _ _, ?_, ?_⟩
  · intro η hη
    -- mean-value bound on the convex closed ball, using `‖fderiv W‖ = ‖gradC W‖`
    have hdiff : ∀ x ∈ Metric.closedBall (0 : ℂ) (ρ / 2), DifferentiableAt ℝ W x := fun x hx =>
      differentiableAt_of_harmonicOnNhd hWh (hsub hx)
    have hfC : ∀ x ∈ Metric.closedBall (0 : ℂ) (ρ / 2), ‖fderiv ℝ W x‖ ≤ max C₀ 0 := by
      intro x hx
      rw [← norm_gradC_eq_norm_fderiv]
      exact le_trans (hC₀ x hx) (le_max_left _ _)
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) hdiff hfC
      (convex_closedBall (0 : ℂ) (ρ / 2)) (Metric.mem_closedBall_self hρ2pos.le) hη
    rw [hW0, sub_zero, sub_zero] at hmvt
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hmvt
  · intro η hη
    exact le_trans (hC₀ η hη) (le_max_left _ _)

/-! ## Tip bounds for the potential -/

/-- **Square-root tip bound (far tip `s`).** Near the far tip `s`, the Grötzsch potential is
bounded by `C·√‖z − s‖`. -/
theorem grotzschPotential_tip_bound_far {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ C r₁ : ℝ, 0 < C ∧ 0 < r₁ ∧ ∀ z ∈ grotzschRing s, ‖z - (s : ℂ)‖ < r₁ →
      v z ≤ C * Real.sqrt ‖z - (s : ℂ)‖ := by
  obtain ⟨ρ, hρpos, W, hWh, hW0, hWeq⟩ := exists_reflected_harmonic_far hs0 hs1 hvh hvc hv0
  obtain ⟨C, hC0, hLip, _⟩ := exists_harmonic_lipschitz_at_zero hρpos hWh hW0
  refine ⟨C + 1, (ρ / 2) ^ 2, by linarith, by positivity, fun z _ hzr => ?_⟩
  -- upper-half root `η` of `s − z`, so `η² = s − z`, hence `s − η² = z`
  obtain ⟨η, hη2, hηim, hηnorm⟩ := exists_upperHalf_sqrt ((s : ℂ) - z)
  have hnormeq : ‖(s : ℂ) - z‖ = ‖z - (s : ℂ)‖ := by rw [← norm_neg]; ring_nf
  have hηsmall : ‖η‖ < ρ / 2 := by
    rw [hηnorm, hnormeq]
    calc Real.sqrt ‖z - (s : ℂ)‖ < Real.sqrt ((ρ / 2) ^ 2) :=
          Real.sqrt_lt_sqrt (norm_nonneg _) hzr
      _ = ρ / 2 := Real.sqrt_sq (by positivity)
  have hηball : η ∈ Metric.closedBall (0 : ℂ) (ρ / 2) :=
    Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hηsmall.le)
  have hzeq : (s : ℂ) - η ^ 2 = z := by rw [hη2]; ring
  have hveq : v z = W η := by
    rw [← hzeq]; exact (hWeq η hηim (lt_trans hηsmall (by linarith))).symm
  calc v z = W η := hveq
    _ ≤ ‖W η‖ := le_abs_self _
    _ ≤ C * ‖η‖ := hLip η hηball
    _ ≤ (C + 1) * ‖η‖ := by nlinarith [norm_nonneg η, hC0]
    _ = (C + 1) * Real.sqrt ‖z - (s : ℂ)‖ := by rw [hηnorm, hnormeq]

/-- **Square-root tip bound (near tip `0`).** Near the near tip `0`, the Grötzsch potential is
bounded by `C·√‖z‖`. -/
theorem grotzschPotential_tip_bound_near {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ C r₁ : ℝ, 0 < C ∧ 0 < r₁ ∧ ∀ z ∈ grotzschRing s, ‖z‖ < r₁ →
      v z ≤ C * Real.sqrt ‖z‖ := by
  obtain ⟨ρ, hρpos, W, hWh, hW0, hWeq⟩ := exists_reflected_harmonic_near hs0 hs1 hvh hvc hv0
  obtain ⟨C, hC0, hLip, _⟩ := exists_harmonic_lipschitz_at_zero hρpos hWh hW0
  refine ⟨C + 1, (ρ / 2) ^ 2, by linarith, by positivity, fun z _ hzr => ?_⟩
  obtain ⟨η, hη2, hηim, hηnorm⟩ := exists_upperHalf_sqrt z
  have hηsmall : ‖η‖ < ρ / 2 := by
    rw [hηnorm]
    calc Real.sqrt ‖z‖ < Real.sqrt ((ρ / 2) ^ 2) := Real.sqrt_lt_sqrt (norm_nonneg _) hzr
      _ = ρ / 2 := Real.sqrt_sq (by positivity)
  have hηball : η ∈ Metric.closedBall (0 : ℂ) (ρ / 2) :=
    Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hηsmall.le)
  have hveq : v z = W η := by
    rw [← hη2]; exact (hWeq η hηim (lt_trans hηsmall (by linarith))).symm
  calc v z = W η := hveq
    _ ≤ ‖W η‖ := le_abs_self _
    _ ≤ C * ‖η‖ := hLip η hηball
    _ ≤ (C + 1) * ‖η‖ := by nlinarith [norm_nonneg η, hC0]
    _ = (C + 1) * Real.sqrt ‖z‖ := by rw [hηnorm]

/-! ## Tip bounds for the gradient -/

/-- **Inverse square-root gradient bound (far tip `s`).** Near the far tip `s`, the holomorphic
gradient of the Grötzsch potential obeys `‖gradC v z‖ ≤ C·‖z − s‖^(−1/2)`. The bound comes from the
chain rule `gradC v z = gradC W η · (dη/dz)` with `η² = s − z` and `‖dη/dz‖ = 1 / (2‖η‖)`. -/
theorem grotzschPotential_grad_tip_bound_far {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ C r₁ : ℝ, 0 < C ∧ 0 < r₁ ∧ ∀ z ∈ grotzschRing s, ‖z - (s : ℂ)‖ < r₁ →
      ‖gradC v z‖ ≤ C / Real.sqrt ‖z - (s : ℂ)‖ := by
  obtain ⟨ρ, hρpos, W, hWh, hW0, hWeq⟩ := exists_reflected_harmonic_far hs0 hs1 hvh hvc hv0
  obtain ⟨C, hC0, _, hgrad⟩ := exists_harmonic_lipschitz_at_zero hρpos hWh hW0
  -- `r₁ = min ((ρ/2)²) s`: the second bound forces `η` into the open upper half-plane
  refine ⟨C + 1, min ((ρ / 2) ^ 2) s, by linarith, lt_min (by positivity) hs0, fun z hz hzr => ?_⟩
  have hzr1 : ‖z - (s : ℂ)‖ < (ρ / 2) ^ 2 := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzrs : ‖z - (s : ℂ)‖ < s := lt_of_lt_of_le hzr (min_le_right _ _)
  obtain ⟨η, hη2, hηim, hηnorm⟩ := exists_upperHalf_sqrt ((s : ℂ) - z)
  have hnormeq : ‖(s : ℂ) - z‖ = ‖z - (s : ℂ)‖ := by rw [← norm_neg]; ring_nf
  have hηnorm' : ‖η‖ = Real.sqrt ‖z - (s : ℂ)‖ := by rw [hηnorm, hnormeq]
  have hηsmall : ‖η‖ < ρ / 2 := by
    rw [hηnorm']
    calc Real.sqrt ‖z - (s : ℂ)‖ < Real.sqrt ((ρ / 2) ^ 2) :=
          Real.sqrt_lt_sqrt (norm_nonneg _) hzr1
      _ = ρ / 2 := Real.sqrt_sq (by positivity)
  have hzeq : (s : ℂ) - η ^ 2 = z := by rw [hη2]; ring
  -- `η ≠ 0` and in fact `Im η > 0`: `z ∈ ring` with `‖z − s‖ < s` excludes a real root
  have hηnorm_pos : 0 < ‖η‖ := by
    rw [hηnorm']; apply Real.sqrt_pos.mpr
    rcases eq_or_lt_of_le (norm_nonneg (z - (s : ℂ))) with h | h
    · exfalso; apply hz.2
      have hzs : z = (s : ℂ) := by rw [← sub_eq_zero]; exact norm_eq_zero.mp h.symm
      have hmem : z ∈ grotzschInner s := by
        rw [grotzschInner_eq hs0.le, hzs]; exact ⟨by simp, by simp [hs0.le], by simp⟩
      exact hmem
    · exact h
  have hηne : η ≠ 0 := fun h => by simp [h] at hηnorm_pos
  have hηimpos : 0 < η.im := by
    rcases eq_or_lt_of_le hηim with h | h
    · exfalso
      -- `η` real: then `z = s − η²` is real with `η.re² < s`, hence on the slit, excluding `z`
      have hηim0 : η.im = 0 := h.symm
      have hηnormre : ‖η‖ = |η.re| := by
        conv_lhs => rw [show η = ((η.re : ℝ) : ℂ) from Complex.ext rfl (by simp [hηim0])]
        rw [Complex.norm_real, Real.norm_eq_abs]
      have hznorm : ‖z - (s : ℂ)‖ = η.re ^ 2 := by
        have hne : ‖(s : ℂ) - z‖ = η.re ^ 2 := by
          rw [← hη2, norm_pow, hηnormre, sq_abs]
        rw [← hnormeq]; exact hne
      have hre2s : η.re ^ 2 ≤ s := by rw [← hznorm]; exact hzrs.le
      apply hz.2
      have hmem : z ∈ grotzschInner s := by
        rw [← hzeq]; exact tipFar_mem_slit hs0.le hηim0 hre2s
      exact hmem
    · exact h
  -- `W = v ∘ g` on the open upper half-ball, so their derivatives agree at `η`
  set g : ℂ → ℂ := fun η => (s : ℂ) - η ^ 2 with hg
  have hzring : z ∈ grotzschRing s := hz
  have hgη : g η = z := hzeq
  have hvdiff : DifferentiableAt ℝ v z := differentiableAt_of_harmonicOnNhd hvh hzring
  have hgfderiv : HasFDerivAt g (((-2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ) η := by
    have hd : HasDerivAt g (-(2 * η)) η := by
      simpa [hg] using ((hasDerivAt_pow 2 η).const_sub (s : ℂ))
    rw [hasFDerivAt_iff_isLittleO]
    refine hd.isLittleO.congr_left fun t => ?_
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  have hvfat : HasFDerivAt v (fderiv ℝ v z) (g η) := by rw [hgη]; exact hvdiff.hasFDerivAt
  have hcompfderiv : HasFDerivAt (fun w => v (g w))
      ((fderiv ℝ v z).comp (((-2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ)) η :=
    hvfat.comp η hgfderiv
  have hWeq_nhds : W =ᶠ[𝓝 η] (fun w => v (g w)) := by
    have hopen : IsOpen ({w : ℂ | 0 < w.im} ∩ Metric.ball (0 : ℂ) ρ) :=
      (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball
    have hmem : η ∈ {w : ℂ | 0 < w.im} ∩ Metric.ball (0 : ℂ) ρ :=
      ⟨hηimpos, Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith [hηsmall])⟩
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact hWeq w hw.1.le (mem_ball_zero_iff.mp hw.2)
  have hWfderiv : fderiv ℝ W η
      = (fderiv ℝ v z).comp (((-2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ) := by
    rw [(hcompfderiv.congr_of_eventuallyEq hWeq_nhds).fderiv]
  -- op-norm inversion: `‖fderiv v z‖ ≤ ‖fderiv W η‖ / (2‖η‖) ≤ C / (2‖η‖)`
  have hinv : fderiv ℝ v z
      = (fderiv ℝ W η).comp (((-1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ) := by
    rw [hWfderiv, ContinuousLinearMap.comp_assoc]
    have hid : (((-2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ).comp
        (((-1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ) = ContinuousLinearMap.id ℝ ℂ := by
      ext w
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply]
      field_simp
    rw [hid, ContinuousLinearMap.comp_id]
  have hgradbound : ‖gradC v z‖ ≤ C / (2 * ‖η‖) := by
    rw [norm_gradC_eq_norm_fderiv]
    calc ‖fderiv ℝ v z‖
        = ‖(fderiv ℝ W η).comp (((-1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ)‖ := by rw [hinv]
      _ ≤ ‖fderiv ℝ W η‖ * ‖(((-1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ W η‖ * (1 / (2 * ‖η‖)) := by
          rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, norm_div, norm_neg, norm_one,
            norm_mul, Complex.norm_ofNat]
      _ ≤ C * (1 / (2 * ‖η‖)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← norm_gradC_eq_norm_fderiv]
          exact hgrad η (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hηsmall.le))
      _ = C / (2 * ‖η‖) := by ring
  -- convert `1/(2‖η‖) = 1/(2√‖z−s‖)` and absorb into `C+1`
  rw [hηnorm'] at hgradbound
  have hsqrtpos : 0 < Real.sqrt ‖z - (s : ℂ)‖ := by rw [← hηnorm']; exact hηnorm_pos
  calc ‖gradC v z‖ ≤ C / (2 * Real.sqrt ‖z - (s : ℂ)‖) := hgradbound
    _ ≤ (C + 1) / Real.sqrt ‖z - (s : ℂ)‖ := by
        rw [div_le_div_iff₀ (by positivity) hsqrtpos]
        nlinarith [hsqrtpos, hC0]

/-- **Inverse square-root gradient bound (near tip `0`).** Near the near tip `0`, the holomorphic
gradient of the Grötzsch potential obeys `‖gradC v z‖ ≤ C·‖z‖^(−1/2)`. -/
theorem grotzschPotential_grad_tip_bound_near {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ C r₁ : ℝ, 0 < C ∧ 0 < r₁ ∧ ∀ z ∈ grotzschRing s, ‖z‖ < r₁ →
      ‖gradC v z‖ ≤ C / Real.sqrt ‖z‖ := by
  obtain ⟨ρ, hρpos, W, hWh, hW0, hWeq⟩ := exists_reflected_harmonic_near hs0 hs1 hvh hvc hv0
  obtain ⟨C, hC0, _, hgrad⟩ := exists_harmonic_lipschitz_at_zero hρpos hWh hW0
  refine ⟨C + 1, min ((ρ / 2) ^ 2) s, by linarith, lt_min (by positivity) hs0, fun z hz hzr => ?_⟩
  have hzr1 : ‖z‖ < (ρ / 2) ^ 2 := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzrs : ‖z‖ < s := lt_of_lt_of_le hzr (min_le_right _ _)
  obtain ⟨η, hη2, hηim, hηnorm⟩ := exists_upperHalf_sqrt z
  have hηsmall : ‖η‖ < ρ / 2 := by
    rw [hηnorm]
    calc Real.sqrt ‖z‖ < Real.sqrt ((ρ / 2) ^ 2) := Real.sqrt_lt_sqrt (norm_nonneg _) hzr1
      _ = ρ / 2 := Real.sqrt_sq (by positivity)
  have hηnorm_pos : 0 < ‖η‖ := by
    rw [hηnorm]; apply Real.sqrt_pos.mpr
    rcases eq_or_lt_of_le (norm_nonneg z) with h | h
    · exfalso; apply hz.2
      have hmem : z ∈ grotzschInner s := by
        rw [grotzschInner_eq hs0.le, show z = (0 : ℂ) from norm_eq_zero.mp h.symm]
        exact ⟨by simp, by simp, by simp [hs0.le]⟩
      exact hmem
    · exact h
  have hηimpos : 0 < η.im := by
    rcases eq_or_lt_of_le hηim with h | h
    · exfalso
      have hηim0 : η.im = 0 := h.symm
      have hηnormre : ‖η‖ = |η.re| := by
        conv_lhs => rw [show η = ((η.re : ℝ) : ℂ) from Complex.ext rfl (by simp [hηim0])]
        rw [Complex.norm_real, Real.norm_eq_abs]
      have hznorm : ‖z‖ = η.re ^ 2 := by rw [← hη2, norm_pow, hηnormre, sq_abs]
      have hre2s : η.re ^ 2 ≤ s := by rw [← hznorm]; exact hzrs.le
      apply hz.2
      have hmem : z ∈ grotzschInner s := by
        rw [← hη2]; exact tipNear_mem_slit hs0.le hηim0 hre2s
      exact hmem
    · exact h
  set g : ℂ → ℂ := fun η => η ^ 2 with hg
  have hgη : g η = z := hη2
  have hvdiff : DifferentiableAt ℝ v z := differentiableAt_of_harmonicOnNhd hvh hz
  have hgfderiv : HasFDerivAt g (((2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ) η := by
    have hd : HasDerivAt g (2 * η) η := by simpa [hg] using (hasDerivAt_pow 2 η)
    rw [hasFDerivAt_iff_isLittleO]
    refine hd.isLittleO.congr_left fun t => ?_
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  have hvfat : HasFDerivAt v (fderiv ℝ v z) (g η) := by rw [hgη]; exact hvdiff.hasFDerivAt
  have hcompfderiv : HasFDerivAt (fun w => v (g w))
      ((fderiv ℝ v z).comp (((2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ)) η :=
    hvfat.comp η hgfderiv
  have hWeq_nhds : W =ᶠ[𝓝 η] (fun w => v (g w)) := by
    have hopen : IsOpen ({w : ℂ | 0 < w.im} ∩ Metric.ball (0 : ℂ) ρ) :=
      (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball
    have hmem : η ∈ {w : ℂ | 0 < w.im} ∩ Metric.ball (0 : ℂ) ρ :=
      ⟨hηimpos, Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith [hηsmall])⟩
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact hWeq w hw.1.le (mem_ball_zero_iff.mp hw.2)
  have hWfderiv : fderiv ℝ W η
      = (fderiv ℝ v z).comp (((2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ) := by
    rw [(hcompfderiv.congr_of_eventuallyEq hWeq_nhds).fderiv]
  have hinv : fderiv ℝ v z
      = (fderiv ℝ W η).comp (((1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ) := by
    rw [hWfderiv, ContinuousLinearMap.comp_assoc]
    have hid : (((2 * η) : ℂ) • ContinuousLinearMap.id ℝ ℂ).comp
        (((1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ) = ContinuousLinearMap.id ℝ ℂ := by
      ext w
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply]
      have hη0 : η ≠ 0 := fun h => by simp [h] at hηnorm_pos
      field_simp
    rw [hid, ContinuousLinearMap.comp_id]
  have hgradbound : ‖gradC v z‖ ≤ C / (2 * ‖η‖) := by
    rw [norm_gradC_eq_norm_fderiv]
    calc ‖fderiv ℝ v z‖
        = ‖(fderiv ℝ W η).comp (((1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ)‖ := by rw [hinv]
      _ ≤ ‖fderiv ℝ W η‖ * ‖(((1 / (2 * η)) : ℂ) • ContinuousLinearMap.id ℝ ℂ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ W η‖ * (1 / (2 * ‖η‖)) := by
          rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, norm_div, norm_one, norm_mul,
            Complex.norm_ofNat]
      _ ≤ C * (1 / (2 * ‖η‖)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← norm_gradC_eq_norm_fderiv]
          exact hgrad η (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hηsmall.le))
      _ = C / (2 * ‖η‖) := by ring
  rw [hηnorm] at hgradbound
  have hsqrtpos : 0 < Real.sqrt ‖z‖ := by rw [← hηnorm]; exact hηnorm_pos
  calc ‖gradC v z‖ ≤ C / (2 * Real.sqrt ‖z‖) := hgradbound
    _ ≤ (C + 1) / Real.sqrt ‖z‖ := by
        rw [div_le_div_iff₀ (by positivity) hsqrtpos]
        nlinarith [hsqrtpos, hC0]

/-! ## Flux-integrand product bounds packaged for the seam assembly -/

/-- **Bounded flux integrand across the far tip.** On a punctured neighbourhood of the far tip `s`,
the product `v · ‖gradC v‖` is bounded: the `√‖z − s‖` bound on `v` and the `‖z − s‖^(−1/2)` bound
on `‖gradC v‖` multiply to a constant. -/
theorem grotzschPotential_flux_bound_far {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ z ∈ grotzschRing s, ‖z - (s : ℂ)‖ < r₁ →
      v z * ‖gradC v z‖ ≤ C := by
  obtain ⟨C₁, r₁, hC₁, hr₁, hb₁⟩ := grotzschPotential_tip_bound_far hs0 hs1 hvh hvc hv0
  obtain ⟨C₂, r₂, hC₂, hr₂, hb₂⟩ := grotzschPotential_grad_tip_bound_far hs0 hs1 hvh hvc hv0
  refine ⟨C₁ * C₂, min r₁ r₂, lt_min hr₁ hr₂, fun z hz hzr => ?_⟩
  have hzr1 : ‖z - (s : ℂ)‖ < r₁ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzr2 : ‖z - (s : ℂ)‖ < r₂ := lt_of_lt_of_le hzr (min_le_right _ _)
  have hvle : v z ≤ C₁ * Real.sqrt ‖z - (s : ℂ)‖ := hb₁ z hz hzr1
  have hgle : ‖gradC v z‖ ≤ C₂ / Real.sqrt ‖z - (s : ℂ)‖ := hb₂ z hz hzr2
  have hne : z ≠ (s : ℂ) := fun heq => hz.2 (by
    have : z ∈ grotzschInner s := by
      rw [grotzschInner_eq hs0.le, heq]; exact ⟨by simp, by simp [hs0.le], by simp⟩
    exact this)
  have hsqrtpos : 0 < Real.sqrt ‖z - (s : ℂ)‖ :=
    Real.sqrt_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  rcases le_or_gt (v z) 0 with hvneg | hvpos
  · calc v z * ‖gradC v z‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hvneg (norm_nonneg _)
      _ ≤ C₁ * C₂ := by positivity
  · calc v z * ‖gradC v z‖
        ≤ (C₁ * Real.sqrt ‖z - (s : ℂ)‖) * (C₂ / Real.sqrt ‖z - (s : ℂ)‖) :=
          mul_le_mul hvle hgle (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ := by field_simp

/-- **Bounded flux integrand across the near tip.** On a punctured neighbourhood of the near tip
`0`, the product `v · ‖gradC v‖` is bounded. -/
theorem grotzschPotential_flux_bound_near {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) :
    ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ z ∈ grotzschRing s, ‖z‖ < r₁ →
      v z * ‖gradC v z‖ ≤ C := by
  obtain ⟨C₁, r₁, hC₁, hr₁, hb₁⟩ := grotzschPotential_tip_bound_near hs0 hs1 hvh hvc hv0
  obtain ⟨C₂, r₂, hC₂, hr₂, hb₂⟩ := grotzschPotential_grad_tip_bound_near hs0 hs1 hvh hvc hv0
  refine ⟨C₁ * C₂, min r₁ r₂, lt_min hr₁ hr₂, fun z hz hzr => ?_⟩
  have hzr1 : ‖z‖ < r₁ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzr2 : ‖z‖ < r₂ := lt_of_lt_of_le hzr (min_le_right _ _)
  have hvle : v z ≤ C₁ * Real.sqrt ‖z‖ := hb₁ z hz hzr1
  have hgle : ‖gradC v z‖ ≤ C₂ / Real.sqrt ‖z‖ := hb₂ z hz hzr2
  have hne : z ≠ 0 := fun heq => hz.2 (by
    have hmem : z ∈ grotzschInner s := by
      rw [grotzschInner_eq hs0.le, heq]; exact ⟨by simp, by simp, by simp [hs0.le]⟩
    exact hmem)
  have hsqrtpos : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hne)
  rcases le_or_gt (v z) 0 with hvneg | hvpos
  · calc v z * ‖gradC v z‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hvneg (norm_nonneg _)
      _ ≤ C₁ * C₂ := by positivity
  · calc v z * ‖gradC v z‖
        ≤ (C₁ * Real.sqrt ‖z‖) * (C₂ / Real.sqrt ‖z‖) :=
          mul_le_mul hvle hgle (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ := by field_simp

end RiemannDynamics

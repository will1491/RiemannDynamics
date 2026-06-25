/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.SensePreserving
import RiemannDynamics.QC.ReverseLengthArea
import RiemannDynamics.QC.InverseQC
import RiemannDynamics.QC.GeometricDifferentiable
import RiemannDynamics.QC.InfinitesimalModulus
import RiemannDynamics.Analysis.Sobolev.AbsolutelyContinuousLines
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import RiemannDynamics.Analysis.Sobolev.DifferenceQuotient
import RiemannDynamics.Analysis.Sobolev.GehringLehto

/-!
# Forward reverse length–area: the four infinitesimal residuals

This file decomposes the single bundled residual `IsQCGeometric.reverseLengthArea_data`
(`QC/GeometricToAnalytic.lean`) — the heart of the hard direction
`isQCAnalytic_of_isQCGeometric` — into **four named, individually-attackable forward GMT
residuals**, from which `reverseLengthArea_data` is then assembled (in `GeometricToAnalytic`)
by fully-proven engines.

The classical Lehto–Virtanen / Väisälä reverse length–area theorem says a geometric
`K`-quasiconformal map `f` (a sense-preserving homeomorphism whose image-family modulus is
`≤ K·M(Q)` for every quadrilateral) has the complete infinitesimal structure: it is absolutely
continuous on almost every line, its line partials are locally square-integrable, its metric
upper derivative is finite almost everywhere, and the pointwise dilatation is bounded.  Those
facts are the four residuals below.  They are coupled (each presupposes some of the others in
the classical proof), so the honest granularity is the cluster, not a single fact; but isolating
them this way (i) makes the assembly axiom-clean modulo the cluster, and (ii) exposes each to
the repository's already-proven reverse length–area infrastructure
(`axisRect_imageModulus_le`, `rengel_area_lower_bound`).

## The four residuals and their downstream consumers

* `IsQCGeometric.ae_slice_absolutelyContinuous` — **forward ACL**: almost every horizontal and
  vertical slice of `f` is absolutely continuous.  Consumed (with a.e. differentiability and
  `L¹_loc` partials) by `hasWeakGradient_of_aeSliceAC` to produce the two weak directional
  derivatives.
* `IsQCGeometric.ae_finite_metric_derivative` — **finite metric upper derivative a.e.**: the
  Stepanov hypothesis.  Consumed by `Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top` to
  give almost-everywhere total differentiability.
* `IsQCGeometric.ae_dilatation_bound` — **pointwise dilatation + nondegeneracy**:
  `‖Df‖² ≤ K·det Df` and `det Df ≠ 0` almost everywhere.  Supplies the dilatation conjunct
  directly and (with differentiability) feeds `SensePreserving.ae_det_pos` for `0 < det Df`.
* `IsQCGeometric.memLpLocOn_partials` — **`L²_loc` line partials**: the two real-directional
  partials of `f` are locally square-integrable.  Supplies (via `L² ⟹ L¹` on compacts) the
  local integrability the weak-gradient bridge requires.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- **Difference-quotient `L²`-bound via quasiconformal roundness (non-circular).** For a geometric
`K`-quasiconformal map `f` and a unit real direction `v`, the difference quotients
`z ↦ (f (z + h • v) − f z)/h` are bounded in `L²` on every compact set, uniformly for small
`h ≠ 0`.

This is the geometric input that *bypasses the absolute-continuity circularity*: both `z` and
`z + h • v` lie in `closedBall z |h|`, so `‖f (z + h•v) − f z‖ ≤ diam (f (closedBall z |h|))`, and
quasiconformal roundness `diam (f (closedBall z r))² ≤ C · area (f (closedBall z r))`
(`qc_image_ball_diam_sq_le_volume`) bounds the integrand by `C · area(f(ball))/|h|²`. Fubini for the
pushforward measure `ν B = volume (f '' B)` gives `∫_{Kc} area(f(closedBall z |h|)) dz ≤ π|h|² ·
area(f(Kc^{|h|}))`, and the `|h|²` cancels, leaving the uniform bound `C π · area(f(Kc¹))`. -/
private theorem qc_differenceQuotient_setLIntegral_sq_le {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) {v : ℂ} (hv : ‖v‖ = 1) (Kc : Set ℂ) (hKc : IsCompact Kc) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ h : ℝ, 0 < |h| → |h| ≤ 1 →
      ∫⁻ z in Kc, ‖(f (z + h • v) - f z) / (h : ℂ)‖₊ ^ 2 ≤ M := by
  classical
  -- `f` is a homeomorphism (continuous, injective, open); set up the pushforward measure
  -- `ν B = volume (f '' B)` and record that it is locally finite.
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  have hfc : Continuous f := hhomeo.continuous
  obtain ⟨C, hC0, hround⟩ := qc_image_ball_diam_sq_le_volume hf
  set ν : Measure ℂ := Measure.map (hhomeo.homeomorph f).symm volume with hν
  have hmap : ∀ {B : Set ℂ}, MeasurableSet B → ν B = volume (f '' B) := by
    intro B hB
    rw [hν, Measure.map_apply ((hhomeo.homeomorph f).symm.continuous.measurable) hB]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      refine ⟨(hhomeo.homeomorph f).symm z, h, ?_⟩
      have : f ((hhomeo.homeomorph f).symm z)
          = (hhomeo.homeomorph f) ((hhomeo.homeomorph f).symm z) := rfl
      rw [this, (hhomeo.homeomorph f).apply_symm_apply]
    · rintro ⟨w, hw, rfl⟩
      have hfw : f w = (hhomeo.homeomorph f) w := rfl
      rw [hfw, (hhomeo.homeomorph f).symm_apply_apply]; exact hw
  have hνloc : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro Kc hK
    rw [hν, Measure.map_apply ((hhomeo.homeomorph f).symm.continuous.measurable) hK.measurableSet]
    have he : ⇑(hhomeo.homeomorph f).symm ⁻¹' Kc = ⇑(hhomeo.homeomorph f) '' Kc :=
      (congrFun (Set.image_eq_preimage_of_inverse (hhomeo.homeomorph f).symm_apply_apply
        (hhomeo.homeomorph f).apply_symm_apply) Kc).symm
    rw [he]
    exact ((hK.image (hhomeo.homeomorph f).continuous)).measure_lt_top
  -- the enlarged compact `Kc1 = cthickening 1 Kc`, on which `ν` is finite.
  set Kc1 : Set ℂ := Metric.cthickening 1 Kc with hKc1def
  have hKc1cpt : IsCompact Kc1 := hKc.cthickening
  have hνKc1 : ν Kc1 < ⊤ := hKc1cpt.measure_lt_top
  have hKc1meas : MeasurableSet Kc1 := hKc1cpt.measurableSet
  have hKcmeas : MeasurableSet Kc := hKc.measurableSet
  -- the uniform `L²` bound.
  refine ⟨ENNReal.ofReal (C * 4) * ν Kc1, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνKc1, ?_⟩
  intro h hpos hle
  have hh0 : |h| ≠ 0 := ne_of_gt hpos
  -- the closed-ball image-set roundness data, packaged for the integrand bound.
  set D : ℂ → ℝ := fun z => Metric.diam (f '' Metric.closedBall z |h|) with hDdef
  -- **Pointwise integrand bound.** `‖DQ‖₊² ≤ ofReal (C/|h|²) · ν (closedBall z |h|)`.
  have hpoint : ∀ z : ℂ,
      (‖(f (z + h • v) - f z) / (h : ℂ)‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (C / |h| ^ 2) * ν (Metric.closedBall z |h|) := by
    intro z
    -- both `z` and `z + h•v` lie in `closedBall z |h|`.
    have hmem1 : (z + h • v) ∈ Metric.closedBall z |h| := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.real_smul, norm_mul,
        Complex.norm_real, hv, mul_one, Real.norm_eq_abs]
    have hmem2 : z ∈ Metric.closedBall z |h| := by
      rw [Metric.mem_closedBall, dist_self]; exact abs_nonneg h
    have hbdd : Bornology.IsBounded (f '' Metric.closedBall z |h|) :=
      ((isCompact_closedBall z |h|).image hfc).isBounded
    have hnormle : ‖f (z + h • v) - f z‖ ≤ D z := by
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem hbdd (Set.mem_image_of_mem f hmem1)
        (Set.mem_image_of_mem f hmem2)
    have hDnn : 0 ≤ D z := Metric.diam_nonneg
    -- the squared difference-quotient norm in `ℝ`.
    have hDQnorm : ‖(f (z + h • v) - f z) / (h : ℂ)‖ = ‖f (z + h • v) - f z‖ / |h| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hDQsq : ‖(f (z + h • v) - f z) / (h : ℂ)‖ ^ 2 ≤ (D z) ^ 2 / |h| ^ 2 := by
      rw [hDQnorm, div_pow]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnormle 2) (by positivity)
    -- roundness at this ball: `D z ^ 2 ≤ C · (ν ball).toReal`.
    have hνtop : ν (Metric.closedBall z |h|) < ⊤ :=
      (isCompact_closedBall z |h|).measure_lt_top
    have hround_z : (D z) ^ 2 ≤ C * (ν (Metric.closedBall z |h|)).toReal := by
      rw [hDdef, hmap measurableSet_closedBall]
      exact hround z |h|
    -- nnnorm bridge.
    have hbridge : (‖(f (z + h • v) - f z) / (h : ℂ)‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal (‖(f (z + h • v) - f z) / (h : ℂ)‖ ^ 2) := by
      rw [ENNReal.ofReal, ← ENNReal.coe_pow]
      congr 1
      ext
      push_cast
      rw [Real.coe_toNNReal _ (by positivity)]
    rw [hbridge]
    have hstep : ‖(f (z + h • v) - f z) / (h : ℂ)‖ ^ 2
        ≤ (C / |h| ^ 2) * (ν (Metric.closedBall z |h|)).toReal := by
      calc ‖(f (z + h • v) - f z) / (h : ℂ)‖ ^ 2 ≤ (D z) ^ 2 / |h| ^ 2 := hDQsq
        _ ≤ (C * (ν (Metric.closedBall z |h|)).toReal) / |h| ^ 2 :=
            div_le_div_of_nonneg_right hround_z (by positivity)
        _ = (C / |h| ^ 2) * (ν (Metric.closedBall z |h|)).toReal := by ring
    calc ENNReal.ofReal (‖(f (z + h • v) - f z) / (h : ℂ)‖ ^ 2)
        ≤ ENNReal.ofReal ((C / |h| ^ 2) * (ν (Metric.closedBall z |h|)).toReal) :=
          ENNReal.ofReal_le_ofReal hstep
      _ = ENNReal.ofReal (C / |h| ^ 2) * ENNReal.ofReal (ν (Metric.closedBall z |h|)).toReal := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (C / |h| ^ 2) * ν (Metric.closedBall z |h|) := by
          rw [ENNReal.ofReal_toReal hνtop.ne]
  -- The measurable diagonal set for the Fubini swap.
  have hS : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 ≤ |h|} := by
    have hc : Continuous (fun p : ℂ × ℂ => dist p.2 p.1) :=
      continuous_dist.comp (continuous_snd.prodMk continuous_fst)
    exact measurableSet_le hc.measurable measurable_const
  set F : ℂ → ℂ → ℝ≥0∞ :=
    fun z w => {p : ℂ × ℂ | dist p.2 p.1 ≤ |h|}.indicator (fun _ => (1 : ℝ≥0∞)) (z, w) with hFdef
  -- inner identity: `∫⁻ w, F z w ∂ν = ν (closedBall z |h|)`.
  have hinner : ∀ z, ∫⁻ w, F z w ∂ν = ν (Metric.closedBall z |h|) := by
    intro z
    have hfun : (fun w => F z w) = (Metric.closedBall z |h|).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext w
      by_cases hw : dist w z ≤ |h|
      · rw [hFdef]; simp only
        rw [Set.indicator_of_mem (by simpa using hw),
          Set.indicator_of_mem (by simpa [Metric.mem_closedBall] using hw)]
      · rw [hFdef]; simp only
        rw [Set.indicator_of_notMem (by simpa using hw),
          Set.indicator_of_notMem (by simpa [Metric.mem_closedBall] using hw)]
    rw [hfun, lintegral_indicator_const measurableSet_closedBall, one_mul]
  -- measurability of `z ↦ ν (closedBall z |h|)`.
  have hmeasball : Measurable (fun z => ν (Metric.closedBall z |h|)) := by
    have heq : (fun z => ν (Metric.closedBall z |h|)) = fun z => ∫⁻ w, F z w ∂ν := by
      funext z; rw [hinner]
    rw [heq, hFdef]
    exact (measurable_const.indicator hS).lintegral_prod_right'
  -- **The Fubini swap bound.** `∫⁻ z in Kc, ν (closedBall z |h|) ≤ ofReal (4|h|²) · ν Kc1`.
  have hswap_bound : ∫⁻ z in Kc, ν (Metric.closedBall z |h|)
      ≤ ENNReal.ofReal (4 * |h| ^ 2) * ν Kc1 := by
    -- outer identity: `∫⁻ z in Kc, F z w ∂volume = volume (Kc ∩ closedBall w |h|)`.
    have houter : ∀ w, ∫⁻ z in Kc, F z w ∂volume = volume (Kc ∩ Metric.closedBall w |h|) := by
      intro w
      have hfun : (fun z => F z w) = (Metric.closedBall w |h|).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext z
        by_cases hz : dist w z ≤ |h|
        · rw [hFdef]; simp only
          rw [Set.indicator_of_mem (by simpa using hz),
            Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_comm] using hz)]
        · rw [hFdef]; simp only
          rw [Set.indicator_of_notMem (by simpa using hz),
            Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_comm] using hz)]
      rw [hfun, lintegral_indicator_const measurableSet_closedBall, one_mul,
        Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
    -- uncurry measurability for the swap.
    have hF_meas : AEMeasurable (Function.uncurry F) ((volume.restrict Kc).prod ν) := by
      have hfeq : Function.uncurry F
          = {p : ℂ × ℂ | dist p.2 p.1 ≤ |h|}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext p; rw [hFdef]; simp [Function.uncurry]
      rw [hfeq]; exact (measurable_const.indicator hS).aemeasurable
    have hswap : ∫⁻ z in Kc, (∫⁻ w, F z w ∂ν) = ∫⁻ w, (∫⁻ z in Kc, F z w ∂volume) ∂ν :=
      lintegral_lintegral_swap hF_meas
    rw [show (∫⁻ z in Kc, ν (Metric.closedBall z |h|)) = ∫⁻ z in Kc, (∫⁻ w, F z w ∂ν) from by
        apply lintegral_congr; intro z; rw [hinner]]
    rw [hswap, show (fun w => ∫⁻ z in Kc, F z w ∂volume)
        = fun w => volume (Kc ∩ Metric.closedBall w |h|) from by funext w; rw [houter]]
    -- bound the closed-ball area by a fixed square area.
    have hball_bd : ∀ w : ℂ, volume (Metric.closedBall w |h|) ≤ ENNReal.ofReal (4 * |h| ^ 2) := by
      intro w
      rw [Complex.volume_closedBall]
      have hpi : ((NNReal.pi : ℝ≥0∞)) ≤ ENNReal.ofReal 4 := by
        rw [show ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal (((NNReal.pi : ℝ≥0∞)).toReal) by
          rw [ENNReal.ofReal_toReal]; simp]
        rw [show ((NNReal.pi : ℝ≥0∞)).toReal = Real.pi by simp]
        exact ENNReal.ofReal_le_ofReal Real.pi_le_four
      calc ENNReal.ofReal |h| ^ 2 * ↑NNReal.pi
          ≤ ENNReal.ofReal |h| ^ 2 * ENNReal.ofReal 4 := mul_le_mul_right hpi _
        _ = ENNReal.ofReal (|h| ^ 2) * ENNReal.ofReal 4 := by rw [ENNReal.ofReal_pow (abs_nonneg h)]
        _ = ENNReal.ofReal (|h| ^ 2 * 4) := by rw [← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (4 * |h| ^ 2) := by rw [mul_comm]
    -- the integrand vanishes off `Kc1`.
    have hbd : ∀ w : ℂ, volume (Kc ∩ Metric.closedBall w |h|)
        ≤ Kc1.indicator (fun _ => ENNReal.ofReal (4 * |h| ^ 2)) w := by
      intro w
      by_cases hw : w ∈ Kc1
      · rw [Set.indicator_of_mem hw]
        calc volume (Kc ∩ Metric.closedBall w |h|) ≤ volume (Metric.closedBall w |h|) :=
              measure_mono Set.inter_subset_right
          _ ≤ ENNReal.ofReal (4 * |h| ^ 2) := hball_bd w
      · rw [Set.indicator_of_notMem hw]
        have hempty : Kc ∩ Metric.closedBall w |h| = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          apply hw
          rw [hKc1def]
          refine Metric.mem_cthickening_of_dist_le w z 1 Kc hz.1 ?_
          have hdwz : dist w z ≤ |h| := by rw [dist_comm]; exact hz.2
          linarith
        rw [hempty]; simp
    calc ∫⁻ w, volume (Kc ∩ Metric.closedBall w |h|) ∂ν
        ≤ ∫⁻ w, Kc1.indicator (fun _ => ENNReal.ofReal (4 * |h| ^ 2)) w ∂ν := lintegral_mono hbd
      _ = ENNReal.ofReal (4 * |h| ^ 2) * ν Kc1 := by
          rw [lintegral_indicator_const hKc1meas]
  -- **Integrate the pointwise bound.**
  calc ∫⁻ z in Kc, (‖(f (z + h • v) - f z) / (h : ℂ)‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ z in Kc, ENNReal.ofReal (C / |h| ^ 2) * ν (Metric.closedBall z |h|) :=
        lintegral_mono (fun z => hpoint z)
    _ = ENNReal.ofReal (C / |h| ^ 2) * ∫⁻ z in Kc, ν (Metric.closedBall z |h|) := by
        rw [lintegral_const_mul _ hmeasball]
    _ ≤ ENNReal.ofReal (C / |h| ^ 2) * (ENNReal.ofReal (4 * |h| ^ 2) * ν Kc1) :=
        mul_le_mul_right hswap_bound _
    _ = ENNReal.ofReal (C * 4) * ν Kc1 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

open Metric Set Filter Topology Real in
/-- **`L²_loc` line partials.** For a geometric `K`-quasiconformal map `f`, the two real-directional
partials `w ↦ Df w · 1` and `w ↦ Df w · I` are locally square-integrable.  This is the energy
half of the reverse length–area inequality: the geometric modulus bound, via the rectangle
length–area estimate, controls `∫∫ ‖∂f‖²` by `K·area(f(R))`.

It supplies (through `MemLp.mono_exponent`, `L² ⟹ L¹` on compacts) the local integrability of the
partials that the weak-gradient bridge `hasWeakGradient_of_aeSliceAC` requires. -/
theorem IsQCGeometric.memLpLocOn_partials {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    MemLpLocOn (fun w => (fderiv ℝ f w) 1) 2 Set.univ ∧
    MemLpLocOn (fun w => (fderiv ℝ f w) Complex.I) 2 Set.univ := by
  classical
  -- `f` is a homeomorphism (continuous, injective, open); set up the pushforward measure
  -- `ν B = volume (f '' B)` and record that it is locally finite.
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  have hfc : Continuous f := hhomeo.continuous
  obtain ⟨C, hC0, hround⟩ := qc_image_ball_diam_sq_le_volume hf
  set ν : Measure ℂ := Measure.map (hhomeo.homeomorph f).symm volume with hν
  have hmap : ∀ {B : Set ℂ}, MeasurableSet B → ν B = volume (f '' B) := by
    intro B hB
    rw [hν, Measure.map_apply ((hhomeo.homeomorph f).symm.continuous.measurable) hB]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      refine ⟨(hhomeo.homeomorph f).symm z, h, ?_⟩
      have : f ((hhomeo.homeomorph f).symm z)
          = (hhomeo.homeomorph f) ((hhomeo.homeomorph f).symm z) := rfl
      rw [this, (hhomeo.homeomorph f).apply_symm_apply]
    · rintro ⟨w, hw, rfl⟩
      have hfw : f w = (hhomeo.homeomorph f) w := rfl
      rw [hfw, (hhomeo.homeomorph f).symm_apply_apply]; exact hw
  have hνloc : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro Kc hK
    rw [hν, Measure.map_apply ((hhomeo.homeomorph f).symm.continuous.measurable) hK.measurableSet]
    have he : ⇑(hhomeo.homeomorph f).symm ⁻¹' Kc = ⇑(hhomeo.homeomorph f) '' Kc :=
      (congrFun (Set.image_eq_preimage_of_inverse (hhomeo.homeomorph f).symm_apply_apply
        (hhomeo.homeomorph f).apply_symm_apply) Kc).symm
    rw [he]
    exact ((hK.image (hhomeo.homeomorph f).continuous)).measure_lt_top
  have hνlfin : IsLocallyFiniteMeasure ν := by infer_instance
  -- **The quantitative roundness bound.** At a.e. `x`, `‖Df x‖² ≤ (C·π)·ρ(x)` with
  -- `ρ = ν.rnDeriv volume` the Radon–Nikodym density of the pushforward. This mirrors the
  -- metric/Stepanov argument of `IsQCGeometric.ae_differentiableAt'`: at a point of
  -- differentiability that is also a Lebesgue/RN point, the operator norm of `Df` is bounded by
  -- the metric upper derivative `limsupᵣ diam(f''closedBall x ρ)/ρ`, and roundness gives
  -- `diam² ≤ C·ν(B) ≤ C·M·vol(B) = C·M·π·ρ²` for every `M > ρ(x)`; squaring and letting
  -- `M → ρ(x)` yields the stated bound.
  have hkey : ∀ᵐ x : ℂ, ‖fderiv ℝ f x‖ ^ 2 ≤ (C * Real.pi) * (ν.rnDeriv volume x).toReal := by
    have hdiff := hf.ae_differentiableAt'
    have htend := Besicovitch.ae_tendsto_rnDeriv ν (volume : Measure ℂ)
    have hfin : ∀ᵐ x : ℂ, ν.rnDeriv volume x < ∞ := Measure.rnDeriv_lt_top ν volume
    filter_upwards [hdiff, htend, hfin] with x hxdiff hx hxfin
    set d : ℝ≥0∞ := ν.rnDeriv volume x with hd
    set L : ℂ →L[ℝ] ℂ := fderiv ℝ f x with hL
    have hLfd : HasFDerivAt f L x := hxdiff.hasFDerivAt
    -- For every real `m > ρ(x)` (`= d.toReal`), `‖Df x‖² ≤ (C·π)·m`.
    have hmbound : ∀ m : ℝ, d.toReal < m → ‖L‖ ^ 2 ≤ (C * Real.pi) * m := by
      intro m hm
      have hmpos : 0 ≤ m := le_trans ENNReal.toReal_nonneg hm.le
      set M : ℝ≥0∞ := ENNReal.ofReal m with hM
      have hMtop : M < ∞ := ENNReal.ofReal_lt_top
      have hMtoReal : M.toReal = m := ENNReal.toReal_ofReal hmpos
      have hdM : d < M := by
        rw [hM, ← ENNReal.ofReal_toReal hxfin.ne]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hm
      -- the density ratio is eventually `< M` near `0⁺` (Lebesgue/RN differentiation)
      have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
          ν (closedBall x r) / volume (closedBall x r) < M :=
        hx.eventually (eventually_lt_nhds hdM)
      have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
          (ν (closedBall x r)).toReal ≤ M.toReal * (volume (closedBall x r)).toReal := by
        filter_upwards [hev, self_mem_nhdsWithin] with r hr hrpos
        have hrpos' : (0 : ℝ) < r := hrpos
        have hvol_pos : 0 < volume (closedBall x r) := measure_closedBall_pos volume x hrpos'
        have hvol_top : volume (closedBall x r) < ∞ := measure_closedBall_lt_top
        have hle : ν (closedBall x r) ≤ M * volume (closedBall x r) := by
          rw [ENNReal.div_lt_iff (Or.inl hvol_pos.ne') (Or.inl hvol_top.ne)] at hr
          exact hr.le
        calc (ν (closedBall x r)).toReal
            ≤ (M * volume (closedBall x r)).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_lt_top hMtop hvol_top).ne hle
          _ = M.toReal * (volume (closedBall x r)).toReal := ENNReal.toReal_mul
      -- translate the ratio bound through roundness into a `diam ≤ √(C·M·π)·ρ` radius estimate
      have hradius : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
          Metric.diam (f '' closedBall x ρ) ≤ Real.sqrt (C * M.toReal * Real.pi) * ρ := by
        filter_upwards [hev2, self_mem_nhdsWithin] with ρ hρ hρpos
        have hρpos' : (0 : ℝ) < ρ := hρpos
        have hνeq : (ν (closedBall x ρ)).toReal = (volume (f '' closedBall x ρ)).toReal := by
          rw [hmap measurableSet_closedBall]
        have hdiam_sq : (Metric.diam (f '' closedBall x ρ)) ^ 2
            ≤ C * (ν (closedBall x ρ)).toReal := by
          rw [hνeq]; exact hround x ρ
        have hvolball : (volume (closedBall x ρ)).toReal = Real.pi * ρ ^ 2 := by
          rw [Complex.volume_closedBall, ENNReal.toReal_mul]
          rw [show ((NNReal.pi : ℝ≥0∞)).toReal = Real.pi by simp]
          rw [show ((ENNReal.ofReal ρ ^ 2).toReal) = ρ ^ 2 by
            rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hρpos'.le]]
          ring
        have hchain : (Metric.diam (f '' closedBall x ρ)) ^ 2
            ≤ C * M.toReal * Real.pi * ρ ^ 2 := by
          calc (Metric.diam (f '' closedBall x ρ)) ^ 2
              ≤ C * (ν (closedBall x ρ)).toReal := hdiam_sq
            _ ≤ C * (M.toReal * (volume (closedBall x ρ)).toReal) := by
                  apply mul_le_mul_of_nonneg_left hρ hC0
            _ = C * M.toReal * Real.pi * ρ ^ 2 := by rw [hvolball]; ring
        have hdiam_nonneg : 0 ≤ Metric.diam (f '' closedBall x ρ) := Metric.diam_nonneg
        have hconst_nonneg : 0 ≤ C * M.toReal * Real.pi := by positivity
        have hsqle : Metric.diam (f '' closedBall x ρ)
            ≤ Real.sqrt (C * M.toReal * Real.pi * ρ ^ 2) := by
          rw [show C * M.toReal * Real.pi * ρ ^ 2 = (C * M.toReal * Real.pi) * ρ ^ 2 by ring]
          calc Metric.diam (f '' closedBall x ρ)
              = Real.sqrt ((Metric.diam (f '' closedBall x ρ)) ^ 2) := by
                rw [Real.sqrt_sq hdiam_nonneg]
            _ ≤ Real.sqrt ((C * M.toReal * Real.pi) * ρ ^ 2) := by
                apply Real.sqrt_le_sqrt
                rw [show (C * M.toReal * Real.pi) * ρ ^ 2 = C * M.toReal * Real.pi * ρ ^ 2 by ring]
                exact hchain
        calc Metric.diam (f '' closedBall x ρ)
            ≤ Real.sqrt (C * M.toReal * Real.pi * ρ ^ 2) := hsqle
          _ = Real.sqrt (C * M.toReal * Real.pi) * ρ := by
              rw [show C * M.toReal * Real.pi * ρ ^ 2 = (C * M.toReal * Real.pi) * ρ ^ 2 by ring,
                Real.sqrt_mul hconst_nonneg, Real.sqrt_sq hρpos'.le]
      -- bound the operator norm `‖L‖ ≤ √(C·M·π)` by bounding `‖L v‖` on unit vectors
      set Cb : ℝ := Real.sqrt (C * M.toReal * Real.pi) with hCb
      have hCbnn : 0 ≤ Cb := Real.sqrt_nonneg _
      have hopbound : ∀ v : ℂ, ‖v‖ = 1 → ‖L v‖ ≤ Cb := by
        intro v hv
        -- near `0⁺`, the line increment is dominated: `‖f(x+tv) − f x‖ ≤ Cb·t`
        have hincr : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖f (x + t • v) - f x‖ ≤ Cb * t := by
          filter_upwards [hradius, self_mem_nhdsWithin] with t htdiam htpos
          have htpos' : (0:ℝ) < t := htpos
          have hmem1 : (x + t • v) ∈ closedBall x t := by
            rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
            calc ‖t • v‖ ≤ ‖t‖ * ‖v‖ := norm_smul_le _ _
              _ = t := by rw [hv, mul_one, Real.norm_eq_abs, abs_of_pos htpos']
          have hmem2 : x ∈ closedBall x t := by
            rw [Metric.mem_closedBall, dist_self]; exact htpos'.le
          have hdle : dist (f (x + t • v)) (f x) ≤ Metric.diam (f '' closedBall x t) :=
            Metric.dist_le_diam_of_mem ((isCompact_closedBall x t).image hfc).isBounded
              (mem_image_of_mem f hmem1) (mem_image_of_mem f hmem2)
          calc ‖f (x + t • v) - f x‖ = dist (f (x + t • v)) (f x) := (dist_eq_norm _ _).symm
            _ ≤ Metric.diam (f '' closedBall x t) := hdle
            _ ≤ Cb * t := htdiam
        -- the line derivative is `L v`; its norm is the limit of the slope norm, hence `≤ Cb`
        have hline : HasDerivAt (fun t : ℝ => f (x + t • v)) (L v) 0 := hLfd.hasLineDerivAt v
        have hslope := hline.tendsto_slope
        have hIoi : (Set.Ioi (0:ℝ)) ⊆ {(0:ℝ)}ᶜ := by
          intro u hu; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hu
        have hslope' : Filter.Tendsto (slope (fun t : ℝ => f (x + t • v)) 0)
            (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (L v)) :=
          hslope.mono_left (nhdsWithin_mono 0 hIoi)
        have hnorm : Filter.Tendsto (fun t => ‖slope (fun t : ℝ => f (x + t • v)) 0 t‖)
            (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ‖L v‖) := hslope'.norm
        refine le_of_tendsto hnorm ?_
        filter_upwards [hincr, self_mem_nhdsWithin] with t ht htpos
        have htpos' : (0:ℝ) < t := htpos
        have h0v : (0:ℝ) • v = 0 := zero_smul ℝ v
        rw [slope_def_module, sub_zero, h0v, add_zero]
        calc ‖t⁻¹ • (f (x + t • v) - f x)‖
            ≤ ‖t⁻¹‖ * ‖f (x + t • v) - f x‖ := norm_smul_le _ _
          _ = t⁻¹ * ‖f (x + t • v) - f x‖ := by
                rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
          _ ≤ t⁻¹ * (Cb * t) := by apply mul_le_mul_of_nonneg_left ht (by positivity)
          _ = Cb := by field_simp
      have hLnorm : ‖L‖ ≤ Cb := ContinuousLinearMap.opNorm_le_of_unit_norm hCbnn hopbound
      have hsq : ‖L‖ ^ 2 ≤ Cb ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hLnorm 2
      rw [hCb, Real.sq_sqrt (by positivity)] at hsq
      rw [hMtoReal] at hsq
      calc ‖L‖ ^ 2 ≤ C * m * Real.pi := hsq
        _ = (C * Real.pi) * m := by ring
    -- let `m → ρ(x)` in the family of bounds `‖L‖² ≤ (C·π)·m`
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    have hCπ : (0:ℝ) ≤ C * Real.pi := by positivity
    rcases eq_or_lt_of_le hCπ with hCπ0 | hCπpos
    · have hb : ‖L‖ ^ 2 ≤ (C * Real.pi) * (d.toReal + 1) := hmbound (d.toReal + 1) (by linarith)
      rw [← hCπ0, zero_mul] at hb
      rw [← hCπ0, zero_mul] at ha
      linarith
    · have hCπpos' : 0 < C * Real.pi := hCπpos
      set mm := a / (C * Real.pi) with hmm
      have hmgt : d.toReal < mm := by
        rw [hmm, lt_div_iff₀ hCπpos', mul_comm]
        exact ha
      have hb := hmbound mm hmgt
      rw [hmm, mul_div_cancel₀ _ (ne_of_gt hCπpos')] at hb
      exact hb
  -- **From the a.e. bound to `L²_loc`.** For a fixed real direction `v` with `‖L v‖ ≤ ‖L‖`
  -- (which holds for `v = 1` and `v = I` since both have norm `1`), the partial `w ↦ Df w · v`
  -- is `L²` on every compact `Kc`: its squared norm is dominated a.e. by the locally-integrable
  -- density `(C·π)·ρ`, whose integral over `Kc` is `≤ (C·π)·ν(Kc) < ∞`.
  have hpartial : ∀ v : ℂ, (∀ L : ℂ →L[ℝ] ℂ, ‖L v‖ ≤ ‖L‖) →
      MemLpLocOn (fun w => (fderiv ℝ f w) v) 2 Set.univ := by
    intro v hv Kc _ hKcpt
    have hKmeas : MeasurableSet Kc := hKcpt.measurableSet
    have hνfin : ν Kc < ∞ := hKcpt.measure_lt_top
    have hlint_ne : ∫⁻ x in Kc, ν.rnDeriv volume x ∂volume ≠ ⊤ :=
      ne_top_of_le_ne_top hνfin.ne (Measure.setLIntegral_rnDeriv_le Kc)
    have hρint : Integrable (fun x => (ν.rnDeriv volume x).toReal) (volume.restrict Kc) :=
      integrable_toReal_of_lintegral_ne_top
        (Measure.measurable_rnDeriv ν volume).aemeasurable hlint_ne
    have hgint : Integrable (fun x => (C * Real.pi) * (ν.rnDeriv volume x).toReal)
        (volume.restrict Kc) := hρint.const_mul (C * Real.pi)
    have hkeyR : ∀ᵐ x ∂(volume.restrict Kc),
        ‖fderiv ℝ f x‖ ^ 2 ≤ (C * Real.pi) * (ν.rnDeriv volume x).toReal :=
      ae_restrict_of_ae hkey
    have hmeasnorm : Measurable (fun w => ‖(fderiv ℝ f w) v‖) :=
      ((measurable_fderiv ℝ f).apply_continuousLinearMap v).norm
    have hmeas2 : AEStronglyMeasurable (fun w => ‖(fderiv ℝ f w) v‖ ^ 2) (volume.restrict Kc) :=
      (hmeasnorm.pow_const 2).aestronglyMeasurable
    have hsqint : Integrable (fun w => ‖(fderiv ℝ f w) v‖ ^ 2) (volume.restrict Kc) := by
      refine hgint.mono' hmeas2 ?_
      filter_upwards [hkeyR] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖(fderiv ℝ f x) v‖ ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hv (fderiv ℝ f x)) 2
        _ ≤ (C * Real.pi) * (ν.rnDeriv volume x).toReal := hx
    rw [memLp_two_iff_integrable_sq_norm
      (((measurable_fderiv ℝ f).apply_continuousLinearMap v).aestronglyMeasurable)]
    exact hsqint
  -- specialise to the two coordinate directions `v = 1` and `v = I` (each of norm `1`)
  refine ⟨hpartial 1 (fun L => ?_), hpartial Complex.I (fun L => ?_)⟩
  · calc ‖L (1:ℂ)‖ ≤ ‖L‖ * ‖(1:ℂ)‖ := L.le_opNorm 1
      _ = ‖L‖ := by rw [norm_one, mul_one]
  · calc ‖L Complex.I‖ ≤ ‖L‖ * ‖Complex.I‖ := L.le_opNorm _
      _ = ‖L‖ := by rw [Complex.norm_I, mul_one]

/-- **Forward no-singular-part of the slices (length–area equality residual, L3c).** For a geometric
`K`-quasiconformal map `f`, almost every horizontal slice of each real component has its total
variation dominated by the integral of its (a.e.-existing) slice derivative — the Banach–Zaretsky
"no singular part" condition `eVariationOn ≤ ∫⁻ ‖deriv‖₊` — and symmetrically for vertical slices.
This is the genuinely two-dimensional content: it is the length–area *equality* (Väisälä §31.2),
ruling out a singular part in the slice and upgrading bounded variation to absolute continuity.

It is FALSE for the area-preserving singular shear `g⟨x,y⟩ = x + i(y + s·x)` (whose horizontal
slice has `deriv = 1` a.e. but variation `> b − a` on singular intervals), so the hypothesis
`IsQCGeometric f K` is load-bearing here. It supplies the `hmaf` input to `ae_slice_AC_of_maf`. -/
theorem IsQCGeometric.ae_slice_noSingularPart {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).re) x‖₊ ∧
        eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).im) x‖₊) ∧
    (∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).re) y‖₊ ∧
        eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).im) y‖₊) := by
  -- `f` is a homeomorphism: continuous and locally integrable.
  have hfc : Continuous f := hf.2.1.isHomeomorph.continuous
  have hfloc : LocallyIntegrable f := hfc.locallyIntegrable
  -- Almost-everywhere differentiability and the `L²_loc` line partials.
  have hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z := hf.ae_differentiableAt'
  obtain ⟨hL2x, hL2y⟩ := hf.memLpLocOn_partials
  -- `L²_loc ⟹ L¹_loc` on compacts supplies the local integrability the ACL representative needs.
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict Kc) := hh Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hgxLI : LocallyIntegrable (fun w => (fderiv ℝ f w) 1) := hLIofL2 hL2x
  have hgyLI : LocallyIntegrable (fun w => (fderiv ℝ f w) Complex.I) := hLIofL2 hL2y
  -- The weak directional derivatives, via the non-circular difference-quotient bridge: the
  -- classical partials `(fderiv ℝ f ·) v` are the weak derivatives, fed by the roundness
  -- `L²`-bound.
  have hwx : HasWeakDirDeriv 1 (fun w => (fderiv ℝ f w) 1) f Set.univ :=
    hasWeakDirDeriv_of_ae_differentiable_of_differenceQuotient_L2
      (by simp) hfc hfloc hdiff
      (fun Kc hKc => qc_differenceQuotient_setLIntegral_sq_le hf (by simp) Kc hKc)
  have hwy : HasWeakDirDeriv Complex.I (fun w => (fderiv ℝ f w) Complex.I) f Set.univ :=
    hasWeakDirDeriv_of_ae_differentiable_of_differenceQuotient_L2
      (by rw [Complex.norm_I]) hfc hfloc hdiff
      (fun Kc hKc => qc_differenceQuotient_setLIntegral_sq_le hf (by rw [Complex.norm_I]) Kc hKc)
  -- The weak derivatives yield absolute continuity on almost every line, hence the
  -- per-component no-singular-part bound (horizontal from `v = 1`, vertical from `v = I`).
  exact ⟨ae_slice_re_im_eVariation_le_of_hasWeakDirDeriv_one hfc hgxLI hwx,
         ae_slice_re_im_eVariation_le_of_hasWeakDirDeriv_I hfc hgyLI hwy⟩

/-- **Forward a.e. slice bounded variation (length–area residual, L2).** For a geometric
`K`-quasiconformal map `f`, almost every horizontal slice `x ↦ f⟨x, y⟩` and almost every vertical
slice `y ↦ f⟨x, y⟩` has finite total variation on every compact interval. This is the bounded-
variation consequence of the reverse length–area *inequality*: the modulus bound, via the
rectangle length–area estimate `∫ ℓ_f(y)² dy ≤ K·area(f(R))` with `area(f(R)) < ∞`, forces the
slice variation `ℓ_f(y)` to be finite almost everywhere.

It supplies (with the no-singular-part bound) the a.e. slice differentiability and slice-derivative
integrability that the absolute-continuity engine `ae_slice_AC_of_maf` requires. -/
theorem IsQCGeometric.ae_slice_boundedVariation {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc a b) ≠ ⊤) ∧
    (∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun y : ℝ => f ⟨x, y⟩) (Set.Icc a b) ≠ ⊤) := by
  classical
  -- The two proven/available inputs.
  obtain ⟨hNSx, hNSy⟩ := hf.ae_slice_noSingularPart
  obtain ⟨hLp1, hLpI⟩ := hf.memLpLocOn_partials
  have hdiff := hf.ae_differentiableAt'
  -- **`L²_loc ⟹ L¹_loc`.** The two partials are locally integrable.
  have hLocInt : ∀ {H : ℂ → ℂ}, MemLpLocOn H 2 Set.univ → LocallyIntegrable H volume := by
    intro H h
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hMemLp := h Kc (Set.subset_univ Kc) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact hMemLp.integrable (by norm_num)
  have hLI1 : LocallyIntegrable (fun w => (fderiv ℝ f w) 1) volume := hLocInt hLp1
  have hLII : LocallyIntegrable (fun w => (fderiv ℝ f w) Complex.I) volume := hLocInt hLpI
  -- **Fubini box-integrability of a locally-integrable map's horizontal slices.**
  have hFubini_horiz : ∀ {H : ℂ → ℂ}, LocallyIntegrable H volume →
      ∀ᵐ y : ℝ, ∀ a b : ℝ,
        IntervalIntegrable (fun x => H (Complex.mk x y)) volume a b := by
    intro H hH
    set H' : ℝ × ℝ → ℂ := fun p => H (Complex.mk p.1 p.2) with hH'
    have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
    have hH'eq : H' = H ∘ Complex.measurableEquivRealProd.symm := by
      funext p; simp [hH', Complex.measurableEquivRealProd_symm_apply]
    have hslice' : ∀ n : ℕ, ∀ᵐ y : ℝ, y ∈ Set.Icc (-(n : ℝ)) n →
        IntegrableOn (fun x => H' (x, y)) (Set.Icc (-(n : ℝ)) n) volume := by
      intro n
      have hemb : MeasurableEmbedding (Complex.measurableEquivRealProd.symm) :=
        Complex.measurableEquivRealProd.symm.measurableEmbedding
      set box : Set (ℝ × ℝ) := Set.Icc (-(n : ℝ)) n ×ˢ Set.Icc (-(n : ℝ)) n with hbox_def
      have hbox : Integrable H' ((volume.restrict (Set.Icc (-(n : ℝ)) n)).prod
          (volume.restrict (Set.Icc (-(n : ℝ)) n))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← MeasureTheory.IntegrableOn]
        change IntegrableOn H' box volume
        rw [hH'eq]
        have hpre : Complex.measurableEquivRealProd.symm ⁻¹'
            (Complex.measurableEquivRealProd.symm '' box) = box :=
          hemb.injective.preimage_image box
        rw [← hpre, MeasureTheory.MeasurePreserving.integrableOn_comp_preimage hmpsymm hemb]
        apply hH.integrableOn_isCompact
        have hcont : Continuous (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ)) := by
          have : (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ))
              = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
            funext p; apply Complex.ext <;> simp
          rw [this]
          exact (Complex.continuous_ofReal.comp continuous_fst).add
            ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
        have himg : Complex.measurableEquivRealProd.symm '' box
            = (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ)) '' box := by
          apply Set.image_congr; intro p _
          simp [Complex.measurableEquivRealProd_symm_apply]
        rw [himg]
        exact (isCompact_Icc.prod isCompact_Icc).image hcont
      have := hbox.prod_left_ae
      rw [ae_restrict_iff' measurableSet_Icc] at this; exact this
    rw [← ae_all_iff] at hslice'
    filter_upwards [hslice'] with y hy a b
    obtain ⟨n, hn⟩ := exists_nat_ge (max (max (|a|) (|b|)) (|y|) + 1)
    have h1 := le_max_left (max (|a|) (|b|)) (|y|)
    have h2 := le_max_right (max (|a|) (|b|)) (|y|)
    have h3 := le_max_left (|a|) (|b|)
    have h4 := le_max_right (|a|) (|b|)
    have ha : |a| ≤ n := by linarith
    have hb : |b| ≤ n := by linarith
    have hyb : |y| ≤ n := by linarith
    rw [abs_le] at ha hb hyb
    have hyn : y ∈ Set.Icc (-(n : ℝ)) n := ⟨hyb.1, hyb.2⟩
    have hint := hy n hyn
    have hsub : Set.uIcc a b ⊆ Set.Icc (-(n : ℝ)) n := by
      intro t ht; rw [Set.mem_uIcc] at ht; rw [Set.mem_Icc]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [intervalIntegrable_iff]
    exact hint.mono_set (le_trans Set.uIoc_subset_uIcc hsub)
  -- **Fubini box-integrability of a locally-integrable map's vertical slices.**
  have hFubini_vert : ∀ {H : ℂ → ℂ}, LocallyIntegrable H volume →
      ∀ᵐ x : ℝ, ∀ a b : ℝ,
        IntervalIntegrable (fun s => H (Complex.mk x s)) volume a b := by
    intro H hH
    set H' : ℝ × ℝ → ℂ := fun p => H (Complex.mk p.1 p.2) with hH'
    have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
    have hH'eq : H' = H ∘ Complex.measurableEquivRealProd.symm := by
      funext p; simp [hH', Complex.measurableEquivRealProd_symm_apply]
    have hslice' : ∀ n : ℕ, ∀ᵐ x : ℝ, x ∈ Set.Icc (-(n : ℝ)) n →
        IntegrableOn (fun s => H' (x, s)) (Set.Icc (-(n : ℝ)) n) volume := by
      intro n
      have hemb : MeasurableEmbedding (Complex.measurableEquivRealProd.symm) :=
        Complex.measurableEquivRealProd.symm.measurableEmbedding
      set box : Set (ℝ × ℝ) := Set.Icc (-(n : ℝ)) n ×ˢ Set.Icc (-(n : ℝ)) n with hbox_def
      have hbox : Integrable H' ((volume.restrict (Set.Icc (-(n : ℝ)) n)).prod
          (volume.restrict (Set.Icc (-(n : ℝ)) n))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← MeasureTheory.IntegrableOn]
        change IntegrableOn H' box volume
        rw [hH'eq]
        have hpre : Complex.measurableEquivRealProd.symm ⁻¹'
            (Complex.measurableEquivRealProd.symm '' box) = box :=
          hemb.injective.preimage_image box
        rw [← hpre, MeasureTheory.MeasurePreserving.integrableOn_comp_preimage hmpsymm hemb]
        apply hH.integrableOn_isCompact
        have hcont : Continuous (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ)) := by
          have : (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ))
              = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
            funext p; apply Complex.ext <;> simp
          rw [this]
          exact (Complex.continuous_ofReal.comp continuous_fst).add
            ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
        have himg : Complex.measurableEquivRealProd.symm '' box
            = (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ)) '' box := by
          apply Set.image_congr; intro p _
          simp [Complex.measurableEquivRealProd_symm_apply]
        rw [himg]
        exact (isCompact_Icc.prod isCompact_Icc).image hcont
      have := hbox.prod_right_ae
      rw [ae_restrict_iff' measurableSet_Icc] at this; exact this
    rw [← ae_all_iff] at hslice'
    filter_upwards [hslice'] with x hx a b
    obtain ⟨n, hn⟩ := exists_nat_ge (max (max (|a|) (|b|)) (|x|) + 1)
    have h1 := le_max_left (max (|a|) (|b|)) (|x|)
    have h2 := le_max_right (max (|a|) (|b|)) (|x|)
    have h3 := le_max_left (|a|) (|b|)
    have h4 := le_max_right (|a|) (|b|)
    have ha : |a| ≤ n := by linarith
    have hb : |b| ≤ n := by linarith
    have hxb : |x| ≤ n := by linarith
    rw [abs_le] at ha hb hxb
    have hxn : x ∈ Set.Icc (-(n : ℝ)) n := ⟨hxb.1, hxb.2⟩
    have hint := hx n hxn
    have hsub : Set.uIcc a b ⊆ Set.Icc (-(n : ℝ)) n := by
      intro t ht; rw [Set.mem_uIcc] at ht; rw [Set.mem_Icc]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [intervalIntegrable_iff]
    exact hint.mono_set (le_trans Set.uIoc_subset_uIcc hsub)
  -- **a.e. fibered differentiability** of `f` in both coordinate directions (Fubini on the null
  -- set where `f` is not differentiable).
  have hslicediff : (∀ᵐ y : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ f (Complex.mk x y)) ∧
      (∀ᵐ x : ℝ, ∀ᵐ s : ℝ, DifferentiableAt ℝ f (Complex.mk x s)) := by
    set T : Set ℂ := {w | ¬ DifferentiableAt ℝ f w} with hT
    have hTnull : volume T = 0 := by rw [hT, ← ae_iff]; exact hdiff
    have hmp : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
    set T' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' T with hT'def
    have hT'null : volume T' = 0 := hmp.quasiMeasurePreserving.preimage_null hTnull
    have hT'mem : ∀ p : ℝ × ℝ, p ∈ T' ↔ (Complex.mk p.1 p.2) ∈ T := by
      intro p; simp only [hT'def, Set.mem_preimage, Complex.measurableEquivRealProd_symm_apply]
    have hprodnull : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), p ∉ T' := by
      rw [ae_iff]; simpa [Measure.volume_eq_prod] using hT'null
    refine ⟨?_, ?_⟩
    · set T'' : Set (ℝ × ℝ) := Prod.swap ⁻¹' T' with hT''def
      have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
        Measure.measurePreserving_swap
      have hT''null : volume T'' = 0 := hswap.quasiMeasurePreserving.preimage_null hT'null
      have hpn : ∀ᵐ q : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), q ∉ T'' := by
        rw [ae_iff]; simpa [Measure.volume_eq_prod] using hT''null
      have hae : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, (y, x) ∉ T'' := Measure.ae_ae_of_ae_prod hpn
      filter_upwards [hae] with y hy
      filter_upwards [hy] with x hx
      have hmem : (Complex.mk x y) ∉ T := by
        intro hmem; apply hx
        rw [hT''def, Set.mem_preimage, Prod.swap_prod_mk, hT'mem]; exact hmem
      rw [hT, Set.mem_setOf_eq, not_not] at hmem; exact hmem
    · have hae : ∀ᵐ x : ℝ, ∀ᵐ s : ℝ, (x, s) ∉ T' := Measure.ae_ae_of_ae_prod hprodnull
      filter_upwards [hae] with x hx
      filter_upwards [hx] with s hs
      have hmem : (Complex.mk x s) ∉ T := by
        intro hmem; apply hs; rw [hT'mem]; exact hmem
      rw [hT, Set.mem_setOf_eq, not_not] at hmem; exact hmem
  -- **Horizontal direction.**
  refine ⟨?_, ?_⟩
  · -- Pull out the per-component no-singular-part bounds.
    have hyre := hNSx
    have hyim := hNSx
    have hNS_re : ∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => (f (Complex.mk x y)).re) (Set.Icc a b)
          ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f (Complex.mk s y)).re) x‖₊ := by
      filter_upwards [hNSx] with y hy a b; exact (hy a b).1
    have hNS_im : ∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => (f (Complex.mk x y)).im) (Set.Icc a b)
          ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f (Complex.mk s y)).im) x‖₊ := by
      filter_upwards [hNSx] with y hy a b; exact (hy a b).2
    have hint := hFubini_horiz hLI1
    filter_upwards [hNS_re, hNS_im, hslicediff.1, hint] with y hyre hyim hydiff hyint
    have hembed : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (Complex.mk t y : ℂ)) (1 : ℂ) x := by
      intro x
      have he : (fun t : ℝ => (Complex.mk t y : ℂ))
          = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]; simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
    have hbound : ∀ᵐ x : ℝ,
        (‖deriv (fun s : ℝ => (f (Complex.mk s y)).re) x‖₊ : ℝ≥0∞)
            ≤ ‖(fderiv ℝ f (Complex.mk x y)) 1‖₊ ∧
        (‖deriv (fun s : ℝ => (f (Complex.mk s y)).im) x‖₊ : ℝ≥0∞)
            ≤ ‖(fderiv ℝ f (Complex.mk x y)) 1‖₊ := by
      filter_upwards [hydiff] with x hx
      have hcomp : HasDerivAt (fun s : ℝ => f (Complex.mk s y))
          (fderiv ℝ f (Complex.mk x y) 1) x := by
        have := (hx.hasFDerivAt).comp_hasDerivAt x (hembed x); simpa using this
      have hdre : deriv (fun s : ℝ => (f (Complex.mk s y)).re) x
          = ((fderiv ℝ f (Complex.mk x y)) 1).re :=
        (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomp).deriv
      have hdim : deriv (fun s : ℝ => (f (Complex.mk s y)).im) x
          = ((fderiv ℝ f (Complex.mk x y)) 1).im :=
        (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hcomp).deriv
      refine ⟨?_, ?_⟩
      · rw [hdre, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
          Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
      · rw [hdim, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
          Real.norm_eq_abs]
        exact Complex.abs_im_le_norm _
    intro a b
    have hpartfin : ∫⁻ x in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x y)) 1‖₊ ≠ ⊤ := by
      rcases le_total a b with hab | hba
      · have hI : IntegrableOn (fun x : ℝ => (fderiv ℝ f (Complex.mk x y)) 1)
            (Set.Icc a b) volume := by
          rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab]; exact hyint a b
        have h2 := hI.2
        rw [hasFiniteIntegral_iff_enorm] at h2
        have heq : ∫⁻ x in Set.Icc a b, (‖(fderiv ℝ f (Complex.mk x y)) 1‖₊ : ℝ≥0∞)
            = ∫⁻ x in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x y)) 1‖ₑ := by
          apply lintegral_congr; intro x; rw [enorm_eq_nnnorm]
        rw [heq]; exact h2.ne
      · rcases eq_or_lt_of_le hba with heq | hlt
        · subst heq; simp
        · rw [Set.Icc_eq_empty (not_le.2 hlt)]; simp
    have hbnd_re : ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f (Complex.mk s y)).re) x‖₊
        ≤ ∫⁻ x in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x y)) 1‖₊ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hbound] with x hx; exact hx.1
    have hbnd_im : ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f (Complex.mk s y)).im) x‖₊
        ≤ ∫⁻ x in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x y)) 1‖₊ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hbound] with x hx; exact hx.2
    have hre_fin : eVariationOn (fun x : ℝ => (f (Complex.mk x y)).re) (Set.Icc a b) ≠ ⊤ :=
      ne_top_of_le_ne_top hpartfin ((hyre a b).trans hbnd_re)
    have him_fin : eVariationOn (fun x : ℝ => (f (Complex.mk x y)).im) (Set.Icc a b) ≠ ⊤ :=
      ne_top_of_le_ne_top hpartfin ((hyim a b).trans hbnd_im)
    have hsub : eVariationOn (fun x : ℝ => f (Complex.mk x y)) (Set.Icc a b)
        ≤ eVariationOn (fun x : ℝ => (f (Complex.mk x y)).re) (Set.Icc a b)
          + eVariationOn (fun x : ℝ => (f (Complex.mk x y)).im) (Set.Icc a b) := by
      rw [eVariationOn]
      apply iSup_le
      rintro ⟨n, u, humono, husmem⟩
      simp only
      calc ∑ i ∈ Finset.range n,
              edist (f (Complex.mk (u (i+1)) y)) (f (Complex.mk (u i) y))
          ≤ ∑ i ∈ Finset.range n,
              (edist (f (Complex.mk (u (i+1)) y)).re (f (Complex.mk (u i) y)).re
              + edist (f (Complex.mk (u (i+1)) y)).im (f (Complex.mk (u i) y)).im) := by
            apply Finset.sum_le_sum
            intro i _
            rw [edist_dist, edist_dist, edist_dist,
              ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
            apply ENNReal.ofReal_le_ofReal
            rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
            calc ‖f (Complex.mk (u (i+1)) y) - f (Complex.mk (u i) y)‖
                ≤ |(f (Complex.mk (u (i+1)) y) - f (Complex.mk (u i) y)).re|
                  + |(f (Complex.mk (u (i+1)) y) - f (Complex.mk (u i) y)).im| :=
                  norm_le_abs_re_add_abs_im _
              _ = |(f (Complex.mk (u (i+1)) y)).re - (f (Complex.mk (u i) y)).re|
                  + |(f (Complex.mk (u (i+1)) y)).im - (f (Complex.mk (u i) y)).im| := by
                    rw [Complex.sub_re, Complex.sub_im]
        _ = (∑ i ∈ Finset.range n,
                edist (f (Complex.mk (u (i+1)) y)).re (f (Complex.mk (u i) y)).re)
            + ∑ i ∈ Finset.range n,
                edist (f (Complex.mk (u (i+1)) y)).im (f (Complex.mk (u i) y)).im := by
            rw [Finset.sum_add_distrib]
        _ ≤ eVariationOn (fun x : ℝ => (f (Complex.mk x y)).re) (Set.Icc a b)
            + eVariationOn (fun x : ℝ => (f (Complex.mk x y)).im) (Set.Icc a b) :=
            add_le_add (eVariationOn.sum_le humono husmem)
              (eVariationOn.sum_le humono husmem)
    intro htop
    rw [htop, top_le_iff, ENNReal.add_eq_top] at hsub
    rcases hsub with h | h
    · exact hre_fin h
    · exact him_fin h
  · -- **Vertical direction** (mirror).
    have hNS_re : ∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun s : ℝ => (f (Complex.mk x s)).re) (Set.Icc a b)
          ≤ ∫⁻ s in Set.Icc a b, ‖deriv (fun t : ℝ => (f (Complex.mk x t)).re) s‖₊ := by
      filter_upwards [hNSy] with x hx a b; exact (hx a b).1
    have hNS_im : ∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun s : ℝ => (f (Complex.mk x s)).im) (Set.Icc a b)
          ≤ ∫⁻ s in Set.Icc a b, ‖deriv (fun t : ℝ => (f (Complex.mk x t)).im) s‖₊ := by
      filter_upwards [hNSy] with x hx a b; exact (hx a b).2
    have hint := hFubini_vert hLII
    filter_upwards [hNS_re, hNS_im, hslicediff.2, hint] with x hxre hxim hxdiff hxint
    have hembed : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (Complex.mk x t : ℂ)) Complex.I s := by
      intro s
      have he : (fun t : ℝ => (Complex.mk x t : ℂ))
          = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I
      simpa using h1.const_add (x : ℂ)
    have hbound : ∀ᵐ s : ℝ,
        (‖deriv (fun t : ℝ => (f (Complex.mk x t)).re) s‖₊ : ℝ≥0∞)
            ≤ ‖(fderiv ℝ f (Complex.mk x s)) Complex.I‖₊ ∧
        (‖deriv (fun t : ℝ => (f (Complex.mk x t)).im) s‖₊ : ℝ≥0∞)
            ≤ ‖(fderiv ℝ f (Complex.mk x s)) Complex.I‖₊ := by
      filter_upwards [hxdiff] with s hs
      have hcomp : HasDerivAt (fun t : ℝ => f (Complex.mk x t))
          (fderiv ℝ f (Complex.mk x s) Complex.I) s := by
        have := (hs.hasFDerivAt).comp_hasDerivAt s (hembed s); simpa using this
      have hdre : deriv (fun t : ℝ => (f (Complex.mk x t)).re) s
          = ((fderiv ℝ f (Complex.mk x s)) Complex.I).re :=
        (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hcomp).deriv
      have hdim : deriv (fun t : ℝ => (f (Complex.mk x t)).im) s
          = ((fderiv ℝ f (Complex.mk x s)) Complex.I).im :=
        (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hcomp).deriv
      refine ⟨?_, ?_⟩
      · rw [hdre, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
          Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
      · rw [hdim, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
          Real.norm_eq_abs]
        exact Complex.abs_im_le_norm _
    intro a b
    have hpartfin : ∫⁻ s in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x s)) Complex.I‖₊ ≠ ⊤ := by
      rcases le_total a b with hab | hba
      · have hI : IntegrableOn (fun s : ℝ => (fderiv ℝ f (Complex.mk x s)) Complex.I)
            (Set.Icc a b) volume := by
          rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab]; exact hxint a b
        have h2 := hI.2
        rw [hasFiniteIntegral_iff_enorm] at h2
        have heq : ∫⁻ s in Set.Icc a b, (‖(fderiv ℝ f (Complex.mk x s)) Complex.I‖₊ : ℝ≥0∞)
            = ∫⁻ s in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x s)) Complex.I‖ₑ := by
          apply lintegral_congr; intro s; rw [enorm_eq_nnnorm]
        rw [heq]; exact h2.ne
      · rcases eq_or_lt_of_le hba with heq | hlt
        · subst heq; simp
        · rw [Set.Icc_eq_empty (not_le.2 hlt)]; simp
    have hbnd_re : ∫⁻ s in Set.Icc a b, ‖deriv (fun t : ℝ => (f (Complex.mk x t)).re) s‖₊
        ≤ ∫⁻ s in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x s)) Complex.I‖₊ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hbound] with s hs; exact hs.1
    have hbnd_im : ∫⁻ s in Set.Icc a b, ‖deriv (fun t : ℝ => (f (Complex.mk x t)).im) s‖₊
        ≤ ∫⁻ s in Set.Icc a b, ‖(fderiv ℝ f (Complex.mk x s)) Complex.I‖₊ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hbound] with s hs; exact hs.2
    have hre_fin : eVariationOn (fun s : ℝ => (f (Complex.mk x s)).re) (Set.Icc a b) ≠ ⊤ :=
      ne_top_of_le_ne_top hpartfin ((hxre a b).trans hbnd_re)
    have him_fin : eVariationOn (fun s : ℝ => (f (Complex.mk x s)).im) (Set.Icc a b) ≠ ⊤ :=
      ne_top_of_le_ne_top hpartfin ((hxim a b).trans hbnd_im)
    have hsub : eVariationOn (fun s : ℝ => f (Complex.mk x s)) (Set.Icc a b)
        ≤ eVariationOn (fun s : ℝ => (f (Complex.mk x s)).re) (Set.Icc a b)
          + eVariationOn (fun s : ℝ => (f (Complex.mk x s)).im) (Set.Icc a b) := by
      rw [eVariationOn]
      apply iSup_le
      rintro ⟨n, u, humono, husmem⟩
      simp only
      calc ∑ i ∈ Finset.range n,
              edist (f (Complex.mk x (u (i+1)))) (f (Complex.mk x (u i)))
          ≤ ∑ i ∈ Finset.range n,
              (edist (f (Complex.mk x (u (i+1)))).re (f (Complex.mk x (u i))).re
              + edist (f (Complex.mk x (u (i+1)))).im (f (Complex.mk x (u i))).im) := by
            apply Finset.sum_le_sum
            intro i _
            rw [edist_dist, edist_dist, edist_dist,
              ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
            apply ENNReal.ofReal_le_ofReal
            rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
            calc ‖f (Complex.mk x (u (i+1))) - f (Complex.mk x (u i))‖
                ≤ |(f (Complex.mk x (u (i+1))) - f (Complex.mk x (u i))).re|
                  + |(f (Complex.mk x (u (i+1))) - f (Complex.mk x (u i))).im| :=
                  norm_le_abs_re_add_abs_im _
              _ = |(f (Complex.mk x (u (i+1)))).re - (f (Complex.mk x (u i))).re|
                  + |(f (Complex.mk x (u (i+1)))).im - (f (Complex.mk x (u i))).im| := by
                    rw [Complex.sub_re, Complex.sub_im]
        _ = (∑ i ∈ Finset.range n,
                edist (f (Complex.mk x (u (i+1)))).re (f (Complex.mk x (u i))).re)
            + ∑ i ∈ Finset.range n,
                edist (f (Complex.mk x (u (i+1)))).im (f (Complex.mk x (u i))).im := by
            rw [Finset.sum_add_distrib]
        _ ≤ eVariationOn (fun s : ℝ => (f (Complex.mk x s)).re) (Set.Icc a b)
            + eVariationOn (fun s : ℝ => (f (Complex.mk x s)).im) (Set.Icc a b) :=
            add_le_add (eVariationOn.sum_le humono husmem)
              (eVariationOn.sum_le humono husmem)
    intro htop
    rw [htop, top_le_iff, ENNReal.add_eq_top] at hsub
    rcases hsub with h | h
    · exact hre_fin h
    · exact him_fin h

/-- **Forward ACL (slice absolute continuity).** A geometric `K`-quasiconformal map `f` is
absolutely continuous on almost every horizontal line `x ↦ f⟨x, y⟩` and almost every vertical
line `y ↦ f⟨x, y⟩`.

This is assembled from the bounded-variation residual `ae_slice_boundedVariation` (which gives, per
real component, a.e. slice differentiability via the Mathlib bounded-variation theory and
slice-derivative integrability from `lintegral_nnnorm_deriv_le_eVariationOn`) and the
no-singular-part residual `ae_slice_noSingularPart`, packaged by the absolute-continuity engine
`ae_slice_AC_of_maf` applied to the real and imaginary components and recombined by
`absolutelyContinuousOnInterval_of_re_im`.

It is consumed by the proven weak-gradient bridge `hasWeakGradient_of_aeSliceAC`
(`QC/ReverseLengthArea.lean`) to identify the pointwise partials of `f` as its weak derivatives. -/
theorem IsQCGeometric.ae_slice_absolutelyContinuous {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ᵐ y : ℝ, ∀ a b : ℝ,
        AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b) ∧
    (∀ᵐ x : ℝ, ∀ a b : ℝ,
        AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b) := by
  classical
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  obtain ⟨hBVx, hBVy⟩ := hf.ae_slice_boundedVariation
  obtain ⟨hNSx, hNSy⟩ := hf.ae_slice_noSingularPart
  -- The horizontal embedding `x ↦ ⟨x, y⟩` is continuous in `x`.
  have hembed_x : ∀ y : ℝ, Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro y
    have he : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [he]; exact Complex.continuous_ofReal.add continuous_const
  -- The vertical embedding `y ↦ ⟨x, y⟩` is continuous in `y`.
  have hembed_y : ∀ x : ℝ, Continuous (fun y : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro x
    have he : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [he]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  -- Generic per-component AC engine for the HORIZONTAL slices: given a real-linear
  -- projection `P` whose component-slice has its variation dominated by the integral of its
  -- derivative a.e., conclude almost every horizontal `P`-slice is absolutely continuous.
  have hcompAC_x : ∀ (P : ℂ →L[ℝ] ℝ),
      (∀ᵐ y : ℝ, ∀ a b : ℝ,
          eVariationOn (fun x : ℝ => P (f ⟨x, y⟩)) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => P (f ⟨s, y⟩)) x‖₊) →
      ∀ᵐ y : ℝ, ∀ a c : ℝ,
        AbsolutelyContinuousOnInterval (fun x : ℝ => P (f ⟨x, y⟩)) a c := by
    intro P hNS
    -- The component slice `slice y x := P (f ⟨x, y⟩)`.
    set slice : ℝ → ℝ → ℝ := fun y x => P (f ⟨x, y⟩) with hslice
    -- (1) Each slice is continuous.
    have hsl_cont : ∀ y : ℝ, Continuous (slice y) := by
      intro y; exact P.continuous.comp (hcont.comp (hembed_x y))
    -- (2) For a.e. `y`, the ℂ-slice has finite variation on every interval, hence so does the
    -- real `P`-slice (1-Lipschitz projection), giving `LocallyBoundedVariationOn` on `univ`.
    have hsl_LBV : ∀ᵐ y : ℝ, LocallyBoundedVariationOn (slice y) Set.univ := by
      filter_upwards [hBVx] with y hy
      intro a b _ _
      -- `eVariationOn (slice y) (univ ∩ Icc a b) ≠ ⊤`.
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by
        rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]
      have hbvℂ : BoundedVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc a b) := hy a b
      have := (P.lipschitz).comp_boundedVariationOn (g := fun x : ℝ => f ⟨x, y⟩)
        (s := Set.Icc a b) hbvℂ
      exact this
    -- (3) a.e. `y`, a.e. `x`, the slice has a derivative (BV ⟹ a.e. differentiable).
    have hderiv : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, HasDerivAt (slice y) (deriv (slice y) x) x := by
      filter_upwards [hsl_LBV] with y hy
      filter_upwards [hy.ae_differentiableAt] with x hx
      exact hx.hasDerivAt
    -- (4) a.e. `y`, the slice-derivative norm is interval-integrable on every `[u, v]`.
    have hint : ∀ᵐ y : ℝ, ∀ u v : ℝ,
        IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume u v := by
      filter_upwards [hderiv, hsl_LBV] with y hyderiv hyLBV u v
      -- It suffices to bound `∫⁻ ‖deriv‖₊` on `[u, v]` by the (finite) variation.
      -- Reduce to the `u ≤ v` case.
      have hcore : ∀ p q : ℝ, p ≤ q →
          IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume p q := by
        intro p q hpq
        have hbvfin : eVariationOn (slice y) (Set.Icc p q) ≠ ⊤ := by
          have := hyLBV p q (Set.mem_univ p) (Set.mem_univ q)
          rwa [BoundedVariationOn, Set.univ_inter] at this
        have hlint_le : ∫⁻ x in Set.Icc p q, ‖deriv (slice y) x‖₊
            ≤ eVariationOn (slice y) (Set.Icc p q) :=
          lintegral_nnnorm_deriv_le_eVariationOn hpq hyderiv
        have hfin : ∫⁻ x in Set.Icc p q, (‖deriv (slice y) x‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top hbvfin hlint_le
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
        refine ⟨((measurable_deriv (slice y)).norm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ x in Set.Ioc p q, ‖‖deriv (slice y) x‖‖ₑ
            ≤ ∫⁻ x in Set.Icc p q, (‖deriv (slice y) x‖₊ : ℝ≥0∞) := by
          refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans_eq ?_
          apply lintegral_congr
          intro x; rw [enorm_norm, enorm_eq_nnnorm]
        exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
      rcases le_total u v with huv | hvu
      · exact hcore u v huv
      · exact (hcore v u hvu).symm
    -- (5) The per-slice MAF is exactly the supplied hypothesis (`deriv` form matches by defeq).
    have hmaf : ∀ᵐ y : ℝ, ∀ a c : ℝ,
        eVariationOn (slice y) (Set.Icc a c)
          ≤ ∫⁻ x in Set.Icc a c, ‖deriv (slice y) x‖₊ := hNS
    -- Package by the general AC engine.
    exact ae_slice_AC_of_maf hsl_cont hderiv hint hmaf
  -- Generic per-component AC engine for the VERTICAL slices (mirror).
  have hcompAC_y : ∀ (P : ℂ →L[ℝ] ℝ),
      (∀ᵐ x : ℝ, ∀ a b : ℝ,
          eVariationOn (fun y : ℝ => P (f ⟨x, y⟩)) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => P (f ⟨x, s⟩)) y‖₊) →
      ∀ᵐ x : ℝ, ∀ a c : ℝ,
        AbsolutelyContinuousOnInterval (fun y : ℝ => P (f ⟨x, y⟩)) a c := by
    intro P hNS
    set slice : ℝ → ℝ → ℝ := fun x y => P (f ⟨x, y⟩) with hslice
    have hsl_cont : ∀ x : ℝ, Continuous (slice x) := by
      intro x; exact P.continuous.comp (hcont.comp (hembed_y x))
    have hsl_LBV : ∀ᵐ x : ℝ, LocallyBoundedVariationOn (slice x) Set.univ := by
      filter_upwards [hBVy] with x hx
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by
        rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]
      have hbvℂ : BoundedVariationOn (fun y : ℝ => f ⟨x, y⟩) (Set.Icc a b) := hx a b
      exact (P.lipschitz).comp_boundedVariationOn (g := fun y : ℝ => f ⟨x, y⟩)
        (s := Set.Icc a b) hbvℂ
    have hderiv : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, HasDerivAt (slice x) (deriv (slice x) y) y := by
      filter_upwards [hsl_LBV] with x hx
      filter_upwards [hx.ae_differentiableAt] with y hy
      exact hy.hasDerivAt
    have hint : ∀ᵐ x : ℝ, ∀ u v : ℝ,
        IntervalIntegrable (fun y => ‖deriv (slice x) y‖) volume u v := by
      filter_upwards [hderiv, hsl_LBV] with x hxderiv hxLBV u v
      have hcore : ∀ p q : ℝ, p ≤ q →
          IntervalIntegrable (fun y => ‖deriv (slice x) y‖) volume p q := by
        intro p q hpq
        have hbvfin : eVariationOn (slice x) (Set.Icc p q) ≠ ⊤ := by
          have := hxLBV p q (Set.mem_univ p) (Set.mem_univ q)
          rwa [BoundedVariationOn, Set.univ_inter] at this
        have hlint_le : ∫⁻ y in Set.Icc p q, ‖deriv (slice x) y‖₊
            ≤ eVariationOn (slice x) (Set.Icc p q) :=
          lintegral_nnnorm_deriv_le_eVariationOn hpq hxderiv
        have hfin : ∫⁻ y in Set.Icc p q, (‖deriv (slice x) y‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top hbvfin hlint_le
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
        refine ⟨((measurable_deriv (slice x)).norm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ y in Set.Ioc p q, ‖‖deriv (slice x) y‖‖ₑ
            ≤ ∫⁻ y in Set.Icc p q, (‖deriv (slice x) y‖₊ : ℝ≥0∞) := by
          refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans_eq ?_
          apply lintegral_congr
          intro y; rw [enorm_norm, enorm_eq_nnnorm]
        exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
      rcases le_total u v with huv | hvu
      · exact hcore u v huv
      · exact (hcore v u hvu).symm
    have hmaf : ∀ᵐ x : ℝ, ∀ a c : ℝ,
        eVariationOn (slice x) (Set.Icc a c)
          ≤ ∫⁻ y in Set.Icc a c, ‖deriv (slice x) y‖₊ := hNS
    exact ae_slice_AC_of_maf hsl_cont hderiv hint hmaf
  -- Assemble the horizontal direction from the two components.
  have hHoriz : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b := by
    have hre := hcompAC_x Complex.reCLM (by
      filter_upwards [hNSx] with y hy a b
      exact (hy a b).1)
    have him := hcompAC_x Complex.imCLM (by
      filter_upwards [hNSx] with y hy a b
      exact (hy a b).2)
    filter_upwards [hre, him] with y hyre hyim a b
    exact absolutelyContinuousOnInterval_of_re_im (hyre a b) (hyim a b)
  -- Assemble the vertical direction from the two components.
  have hVert : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b := by
    have hre := hcompAC_y Complex.reCLM (by
      filter_upwards [hNSy] with x hx a b
      exact (hx a b).1)
    have him := hcompAC_y Complex.imCLM (by
      filter_upwards [hNSy] with x hx a b
      exact (hx a b).2)
    filter_upwards [hre, him] with x hxre hxim a b
    exact absolutelyContinuousOnInterval_of_re_im (hxre a b) (hxim a b)
  exact ⟨hHoriz, hVert⟩

/-- **Finite metric upper derivative almost everywhere.** For a geometric `K`-quasiconformal map
`f`, at almost every point `x` the difference quotient is locally bounded:
`∃ C, ∀ᶠ y near x, ‖f y − f x‖ ≤ C·‖y − x‖`.  This is the Stepanov hypothesis; quasiconformal
maps have finite metric derivative almost everywhere (the volume derivative of the pushforward is
finite a.e. and controls the local stretch).

It is consumed by `Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top` to upgrade `f` to
almost-everywhere total differentiability (Rademacher is inapplicable — `f` need not be
Lipschitz). The metric upper derivative is finite at every point of differentiability, and `f` is
differentiable almost everywhere by `IsQCGeometric.ae_differentiableAt'` (the metric/Stepanov
route through the quasiconformal roundness estimate). -/
theorem IsQCGeometric.ae_finite_metric_derivative {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, ∃ C : ℝ, ∀ᶠ y in nhds x, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  filter_upwards [hf.ae_differentiableAt'] with x hx
  -- At a point of differentiability the increment is `O(‖y − x‖)`: the linear part is bounded by
  -- `‖Df‖·‖y − x‖` and the remainder is `o(‖y − x‖)`, so some constant `C` dominates near `x`.
  obtain ⟨C, _, hC⟩ := (hx.hasFDerivAt.isBigO_sub).exists_pos
  exact ⟨C, hC.bound⟩

/-- **Pointwise dilatation bound and nondegeneracy.** For a geometric `K`-quasiconformal map `f`,
at almost every point the differential satisfies the dilatation inequality
`‖Df‖² ≤ K·det Df` and is nondegenerate, `det Df ≠ 0`.  This is the infinitesimal modulus
distortion: at a point of differentiability the linear map `Df` distorts infinitesimal moduli by
at most `K`, which is exactly `‖Df‖² ≤ K·det Df`; nondegeneracy is the area lower bound (Rengel)
ruling out collapse on a positive-measure set.

It supplies the dilatation conjunct of `reverseLengthArea_data` directly, and — combined with
almost-everywhere differentiability — feeds `SensePreserving.ae_det_pos` to give `0 < det Df`. -/
theorem IsQCGeometric.ae_dilatation_bound {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∀ᵐ w : ℂ,
      ‖fderiv ℝ f w‖ ^ 2 ≤ K * (fderiv ℝ f w).det ∧ (fderiv ℝ f w).det ≠ 0 := by
  -- The sharp pointwise dilatation bound and nondegeneracy are supplied by the infinitesimal
  -- modulus blow-up theorem `IsQCGeometric.infinitesimal_dilatation`
  -- (`QC/InfinitesimalModulus.lean`):
  -- at almost every point of differentiability the differential `L = Df w` satisfies
  -- `det L ≠ 0` and `‖L‖² ≤ K·det L`.  Almost-everywhere differentiability comes from
  -- `ae_differentiableAt'`.
  filter_upwards [hf.ae_differentiableAt', hf.infinitesimal_dilatation] with w hdiff hdil
  obtain ⟨hdet, hbound⟩ := hdil hdiff
  exact ⟨hbound, hdet⟩

/-! ## The diff-free slice-derivative witnesses and the three forward length–area residuals

The forward reverse-length-area theorem (Lehto–Virtanen, Väisälä §31) must be proved **without**
any a.e. differentiability of `f` (it *feeds* `ae_differentiableAt_gehringLehto`). So the ACL
gradient witnesses cannot be `fderiv ℝ f · v`; they are the **one-dimensional slice derivatives**,
which exist a.e. from *slice* bounded variation (a 1D fact,
`BoundedVariationOn.ae_differentiableAt`), not from 2D differentiability.

Everything below is therefore stated and assembled in terms of the slice derivatives. The three
genuinely two-dimensional length–area facts are isolated as the residuals `forward_ae_slice_bv`
(slice bounded variation, the length–area *inequality*), `forward_ae_slice_noSingularPart` (the
no-singular-part / Lusin-(N) bound, the length–area *equality*), and `forward_sliceDeriv_memLp`
(the slice-derivative `L²_loc` energy). The complete reduction of `exists_acl_memLp_sliceGradient`
to exactly these three is carried out in full. -/

/-- The **horizontal slice derivative** field: at `w = ⟨x, y⟩`, the classical derivative of the
horizontal slice `t ↦ f ⟨t, y⟩` evaluated at `x`. This is the diff-free `x`-partial witness — a
one-dimensional `deriv`, defined pointwise with no appeal to `fderiv ℝ f`. -/
noncomputable def forwardSliceDerivX (f : ℂ → ℂ) : ℂ → ℂ :=
  fun w => deriv (fun t : ℝ => f ⟨t, w.im⟩) w.re

/-- The **vertical slice derivative** field: at `w = ⟨x, y⟩`, the classical derivative of the
vertical slice `t ↦ f ⟨x, t⟩` evaluated at `y`. This is the diff-free `y`-partial witness. -/
noncomputable def forwardSliceDerivY (f : ℂ → ℂ) : ℂ → ℂ :=
  fun w => deriv (fun t : ℝ => f ⟨w.re, t⟩) w.im

/-- **Measurability of the horizontal slice-derivative field.** For continuous `f`, the field
`forwardSliceDerivX f : ℂ → ℂ` is measurable. The parametrized-derivative measurability
`measurable_deriv_with_param` gives joint measurability of `(y,x) ↦ deriv (t ↦ f⟨t,y⟩) x`; then
precompose with the measurable `w ↦ (w.im, w.re)`. -/
theorem measurable_forwardSliceDerivX {f : ℂ → ℂ} (hf : Continuous f) :
    Measurable (forwardSliceDerivX f) := by
  set F : ℝ → ℝ → ℂ := fun y x => f ⟨x, y⟩ with hF
  have hunc : Continuous (Function.uncurry F) := by
    have he : (Function.uncurry F) = fun p : ℝ × ℝ => f (⟨p.2, p.1⟩ : ℂ) := by
      funext p; rfl
    rw [he]
    refine hf.comp ?_
    have h2 : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [h2]
    exact (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  have hjoint : Measurable (fun p : ℝ × ℝ => deriv (F p.1) p.2) :=
    measurable_deriv_with_param hunc
  have hcomp : forwardSliceDerivX f
      = (fun p : ℝ × ℝ => deriv (F p.1) p.2) ∘ (fun w : ℂ => (w.im, w.re)) := by
    funext w; simp only [forwardSliceDerivX, Function.comp_apply, hF]
  rw [hcomp]
  exact hjoint.comp (Complex.measurable_im.prodMk Complex.measurable_re)

/-- **Measurability of the vertical slice-derivative field.** Mirror of
`measurable_forwardSliceDerivX`. -/
theorem measurable_forwardSliceDerivY {f : ℂ → ℂ} (hf : Continuous f) :
    Measurable (forwardSliceDerivY f) := by
  set F : ℝ → ℝ → ℂ := fun x y => f ⟨x, y⟩ with hF
  have hunc : Continuous (Function.uncurry F) := by
    have he : (Function.uncurry F) = fun p : ℝ × ℝ => f (⟨p.1, p.2⟩ : ℂ) := by
      funext p; rfl
    rw [he]
    refine hf.comp ?_
    have h2 : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [h2]
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hjoint : Measurable (fun p : ℝ × ℝ => deriv (F p.1) p.2) :=
    measurable_deriv_with_param hunc
  have hcomp : forwardSliceDerivY f
      = (fun p : ℝ × ℝ => deriv (F p.1) p.2) ∘ (fun w : ℂ => (w.re, w.im)) := by
    funext w; simp only [forwardSliceDerivY, Function.comp_apply, hF]
  rw [hcomp]
  exact hjoint.comp (Complex.measurable_re.prodMk Complex.measurable_im)

/-! ### The single diff-free length–area energy residual

The bounded-variation residual (`forward_ae_slice_bv`) and the slice-derivative `L²_loc` energy
residual (`forward_sliceDeriv_memLp`) are both consequences of one classical, **differentiability-
free** length–area inequality: for every axis box `R = (a,b)×(s,t)`, the slice variation
`ℓ_f(y) = eVariationOn (x ↦ f⟨x,y⟩) [a,b]` and the slice-derivative energy
`∫_{x∈[a,b]} ‖∂ₓf⟨x,y⟩‖²` integrate over `y ∈ [s,t]` to finite quantities. This is the
forward image-family length–area energy bound: combine the source segment-family modulus lower
bound (`segmentFamily_modulus_ge`/`lengthArea_modulus_lower_bound`), the geometric modulus upper
bound `M(f(R)) ≤ K·(t−s)/(b−a)` (`axisRect_imageModulus_le`), the finiteness of the image area
`area(f(R)) < ∞` (`f` is a homeomorphism, `f''R` compact), and a Cauchy–Schwarz / Fubini estimate,
via the reciprocal-slice-length admissible density on the image plane. It needs **no** 2D
differentiability of `f` (the witnesses are the *one-dimensional* slice derivatives), **no**
Grötzsch symmetrization, and **no** reciprocity — it is the *easy* (mod-upper ⟹ energy-upper)
length–area direction.

Both finiteness facts are bundled here as a single residual because they share the same proof (the
image-family length–area transfer) and the same load-bearing hypothesis (`IsQCGeometric f K`); each
of `forward_ae_slice_bv` and `forward_sliceDeriv_memLp` is then fully derived from it below by
real connective steps (a.e.-finiteness from the `eVariation²` box bound; Fubini/`MemLp` from the
derivative-energy box bound). -/

/-- **Forward length–area energy bound (diff-free, the easy direction; isolated residual).** For a
geometric `K`-quasiconformal map `f` and every axis box `(a,b)×(s,t)`, both the squared slice
variation and the slice-derivative energy integrate to a finite quantity over the box. The two
finiteness facts are stated per axis (horizontal slices indexed by height `y ∈ [s,t]`, vertical
slices indexed by abscissa `x ∈ [a,b]`).

This is the genuinely two-dimensional length–area *inequality* (Väisälä §31.1), the single brick
from which the bounded-variation residual `forward_ae_slice_bv` and the `L²_loc` energy residual
`forward_sliceDeriv_memLp` are both **fully derived below** (a.e.-finite variation from the
`eVariation²` box bound via `ae_eVariationOn_ne_top_of_box`; `MemLp` from the derivative-energy box
bound via `setLIntegral_axisRect_eq_iterated_*` + `measurable_forwardSliceDeriv*`). It is
**differentiability-free** by construction: the slice variations and slice derivatives are intrinsic
one-dimensional quantities of the continuous map `f`.

## Closeability (honest assessment): the forward image-family length–area lower bound.

The classical proof (Lehto–Virtanen; Väisälä §31.1) transfers the geometric modulus upper bound
`M(f(R)) ≤ K·(t−s)/(b−a)` (`axisRect_imageModulus_le`, proven) to the slice energy by building, on
the **image** plane, the *reciprocal-slice-length* admissible density `ρ(w) = 1/ℓ_f(y)` on the image
of the height-`y` slice (where `ℓ_f(y)` is the image-slice length): every image curve `f∘γ_y` then
has `∫_{f∘γ_y} ρ ds = 1`, so `ρ` is admissible and `M(f(R)) ≥ ∫ρ² dArea`, and a Cauchy–Schwarz /
Fubini coupling on the image plane converts `∫ρ²` into the slice-energy lower bound, giving
`∫_y ℓ_f(y)² dy ≤ K·area(f(R)) < ∞` (the image area is finite since `f''R` is compact). This is the
*easy* (mod-upper ⟹ energy-upper) direction — **no** Grötzsch symmetrization, **no** reciprocity.

It is **kept as a `sorry` residual**: the repository has the source-side length–area lower bound
(`lengthArea_modulus_lower_bound`, `segmentFamily_modulus_ge`) and the image-modulus upper bound
(`axisRect_imageModulus_le`), but **not** the image-plane reciprocal-density coupling, which needs a
co-area / change-of-variables *equality* on the (non-Lipschitz, BV-sliced) image — Mathlib-absent in
this regime. This is the genuine forward length–area energy bottleneck (the Gehring–Lehto brick).
It may **not** be discharged via the proven `ae_slice_boundedVariation`/`memLpLocOn_partials`, which
route through `ae_differentiableAt'`/`qc_image_ball_diam_sq_le_volume`: those feed
`ae_differentiableAt_gehringLehto` *through this very leaf*, so using them is a cycle and is on the
forbidden list. The diff-free image-family lower bound is the unique honest route. -/
theorem IsQCGeometric.forward_lengthArea_energy {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ a b s t : ℝ,
        (∫⁻ y in Set.Icc s t,
            (eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)) ^ 2) ≠ ⊤ ∧
        (∫⁻ y in Set.Icc s t,
            (eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)) ^ 2) ≠ ⊤ ∧
        (∫⁻ y in Set.Icc s t, ∫⁻ x in Set.Icc a b,
            (‖forwardSliceDerivX f ⟨x, y⟩‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤) ∧
    (∀ a b s t : ℝ,
        (∫⁻ x in Set.Icc a b,
            (eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc s t)) ^ 2) ≠ ⊤ ∧
        (∫⁻ x in Set.Icc a b,
            (eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc s t)) ^ 2) ≠ ⊤ ∧
        (∫⁻ x in Set.Icc a b, ∫⁻ y in Set.Icc s t,
            (‖forwardSliceDerivY f ⟨x, y⟩‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤) := by
  sorry

/-- **From a box `eVariation²`-integral bound to a.e.-finite slice variation (general engine).**
If `g : ℝ → ℝ → ℝ` is a jointly continuous slice family whose squared slice variation has a finite
box integral over every rectangle (`∫⁻_{y∈[s,t]} (eVariationOn (g y) [a,b])² ≠ ⊤`), then for almost
every `y` the slice `g y` has finite variation on every compact interval. This is the
measure-theoretic core of the bounded-variation residual: a finite box integral of a measurable
nonnegative integrand forces the integrand to be a.e. finite, and an exhaustion by integer boxes
upgrades this to "a.e. `y`, on every interval". -/
private theorem ae_eVariationOn_ne_top_of_box {g : ℝ → ℝ → ℝ}
    (hjoint : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hbox : ∀ a b s t : ℝ,
        (∫⁻ y in Set.Icc s t, (eVariationOn (g y) (Set.Icc a b)) ^ 2) ≠ ⊤) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ, eVariationOn (g y) (Set.Icc a b) ≠ ⊤ := by
  -- `y ↦ eVariationOn (g y) [a,b]` is measurable for every fixed box.
  have hmeas : ∀ a b : ℝ, Measurable (fun y => eVariationOn (g y) (Set.Icc a b)) :=
    fun a b => RiemannDynamics.MAF.measurable_eVariationOn_slice hjoint a b
  -- For each integer `n`, a.e. `y` in `[-n,n]` has finite variation on `[-n,n]`.
  have hper : ∀ n : ℕ, ∀ᵐ y : ℝ,
      y ∈ Set.Icc (-(n : ℝ)) n → eVariationOn (g y) (Set.Icc (-(n : ℝ)) n) ≠ ⊤ := by
    intro n
    -- The squared variation is a.e.-`y`-finite on `[-n,n]` (finite box integral).
    have hfin : ∫⁻ y in Set.Icc (-(n : ℝ)) n,
        (eVariationOn (g y) (Set.Icc (-(n : ℝ)) n)) ^ 2 ≠ ⊤ :=
      hbox (-(n : ℝ)) n (-(n : ℝ)) n
    have hae := MeasureTheory.ae_lt_top'
      ((hmeas (-(n : ℝ)) n).pow_const 2).aemeasurable hfin
    rw [ae_restrict_iff' measurableSet_Icc] at hae
    filter_upwards [hae] with y hy hymem
    have hlt := hy hymem
    intro htop
    rw [htop] at hlt
    simp at hlt
  -- Combine over all `n`, then use interval monotonicity.
  rw [← ae_all_iff] at hper
  filter_upwards [hper] with y hy a b
  -- Pick `n` with `[a,b] ⊆ [-n,n]` **and** `y ∈ [-n,n]`, then use `eVariationOn.mono`.
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max |a| |b|) |y|)
  have ha : |a| ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hb : |b| ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hyn : |y| ≤ n := le_trans (le_max_right _ _) hn
  rw [abs_le] at ha hb hyn
  have hsub : Set.Icc a b ⊆ Set.Icc (-(n : ℝ)) n := by
    intro z hz; rw [Set.mem_Icc] at hz ⊢; exact ⟨le_trans ha.1 hz.1, le_trans hz.2 hb.2⟩
  have hymem : y ∈ Set.Icc (-(n : ℝ)) n := by rw [Set.mem_Icc]; exact hyn
  exact ne_top_of_le_ne_top (hy n hymem) (eVariationOn.mono (g y) hsub)

/-- **Subadditivity of the complex slice variation.** The total variation of a `ℂ`-valued function
on an interval is at most the sum of the variations of its real and imaginary parts (the projection
inequality `‖z‖ ≤ |z.re| + |z.im|` integrated over partitions). -/
private theorem eVariationOn_complex_le_re_add_im (h : ℝ → ℂ) (a b : ℝ) :
    eVariationOn h (Set.Icc a b)
      ≤ eVariationOn (fun t => (h t).re) (Set.Icc a b)
        + eVariationOn (fun t => (h t).im) (Set.Icc a b) := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, humono, husmem⟩
  simp only
  calc ∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (h (u (i + 1))).re (h (u i)).re + edist (h (u (i + 1))).im (h (u i)).im) := by
        apply Finset.sum_le_sum
        intro i _
        rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        apply ENNReal.ofReal_le_ofReal
        rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
        calc ‖h (u (i + 1)) - h (u i)‖
            ≤ |(h (u (i + 1)) - h (u i)).re| + |(h (u (i + 1)) - h (u i)).im| :=
              norm_le_abs_re_add_abs_im _
          _ = |(h (u (i + 1))).re - (h (u i)).re| + |(h (u (i + 1))).im - (h (u i)).im| := by
              rw [Complex.sub_re, Complex.sub_im]
    _ = (∑ i ∈ Finset.range n, edist (h (u (i + 1))).re (h (u i)).re)
        + ∑ i ∈ Finset.range n, edist (h (u (i + 1))).im (h (u i)).im := by
        rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn (fun t => (h t).re) (Set.Icc a b)
        + eVariationOn (fun t => (h t).im) (Set.Icc a b) :=
        add_le_add (eVariationOn.sum_le humono husmem) (eVariationOn.sum_le humono husmem)

/-- The complex slice variation is finite when both real-component variations are finite. -/
private theorem eVariationOn_ne_top_of_re_im_ne_top {h : ℝ → ℂ} {a b : ℝ}
    (hre : eVariationOn (fun t => (h t).re) (Set.Icc a b) ≠ ⊤)
    (him : eVariationOn (fun t => (h t).im) (Set.Icc a b) ≠ ⊤) :
    eVariationOn h (Set.Icc a b) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (eVariationOn_complex_le_re_add_im h a b)
  exact ENNReal.add_ne_top.mpr ⟨hre, him⟩

/-- **Forward a.e. slice bounded variation (diff-free, length–area inequality).** For a geometric
`K`-quasiconformal map `f`, almost every horizontal slice `x ↦ f⟨x, y⟩` and almost every vertical
slice `y ↦ f⟨x, y⟩` has finite total variation on every compact interval.

This is the bounded-variation consequence of the reverse length–area *inequality*: the modulus
bound `M(f(R)) ≤ K·M(R)` (`axisRect_imageModulus_le`), via the rectangle length–area estimate
`∫ ℓ_f(y)² dy ≤ K·area(f(R))` with `area(f(R)) < ∞`, forces the slice variation `ℓ_f(y)` to be
finite almost everywhere.

Proved here in full from the diff-free length–area residual `forward_lengthArea_energy` (whose
component `eVariation²` box bounds force a.e.-finite component variation by
`ae_eVariationOn_ne_top_of_box`; the complex slice variation is then finite by the subadditivity
`Var(f) ≤ Var(Re f) + Var(Im f)`). It is the **diff-free** analogue of
`IsQCGeometric.ae_slice_boundedVariation`, which routes through `ae_differentiableAt'` (the
forbidden 2D differentiability). -/
theorem IsQCGeometric.forward_ae_slice_bv {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc a b) ≠ ⊤) ∧
    (∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun y : ℝ => f ⟨x, y⟩) (Set.Icc a b) ≠ ⊤) := by
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  obtain ⟨hHoriz, hVert⟩ := hf.forward_lengthArea_energy
  -- Joint continuity of the horizontal real/imaginary slice families.
  have hjoint_hx_re : Continuous (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).re) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).re)
        = Complex.reCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.reCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  have hjoint_hx_im : Continuous (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).im) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).im)
        = Complex.imCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.imCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  -- Joint continuity of the vertical real/imaginary slice families.
  have hjoint_vy_re : Continuous (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).re) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).re)
        = Complex.reCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.reCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hjoint_vy_im : Continuous (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).im) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).im)
        = Complex.imCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.imCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  -- The complex slice variation is finite when both component variations are.
  refine ⟨?_, ?_⟩
  · -- Horizontal: combine the re/im a.e.-finite component variations.
    have hre := ae_eVariationOn_ne_top_of_box hjoint_hx_re (fun a b s t => (hHoriz a b s t).1)
    have him := ae_eVariationOn_ne_top_of_box hjoint_hx_im (fun a b s t => (hHoriz a b s t).2.1)
    filter_upwards [hre, him] with y hyre hyim a b
    exact eVariationOn_ne_top_of_re_im_ne_top (hyre a b) (hyim a b)
  · -- Vertical: slice family `g x y = (f⟨x,y⟩).re`, indexed by abscissa `x`.
    have hre := ae_eVariationOn_ne_top_of_box hjoint_vy_re
      (fun A B S T => (hVert S T A B).1)
    have him := ae_eVariationOn_ne_top_of_box hjoint_vy_im
      (fun A B S T => (hVert S T A B).2.1)
    filter_upwards [hre, him] with x hxre hxim a b
    exact eVariationOn_ne_top_of_re_im_ne_top (hxre a b) (hxim a b)

/-- **Forward no-singular-part of the slices (diff-free, length–area equality; isolated residual).**
For a geometric `K`-quasiconformal map `f`, almost every horizontal slice of each real component
has its total variation dominated by the integral of its (a.e.-existing) *slice* derivative — the
Banach–Zaretsky "no singular part" condition `eVariationOn ≤ ∫⁻ ‖deriv‖₊` — and symmetrically for
vertical slices.

This is the genuinely two-dimensional content (the length–area *equality*, Väisälä §31.2), ruling
out a singular part in the slice and upgrading bounded variation (`forward_ae_slice_bv`) to absolute
continuity. It is FALSE for the area-preserving singular shear `g⟨x,y⟩ = x + i(y + s·x)` (whose
slice `x ↦ y + s·x` is singular but has `deriv = 1` a.e.), so the hypothesis `IsQCGeometric f K` is
load-bearing.

The derivatives here are the **one-dimensional slice** derivatives `deriv (fun s => (f⟨s, y⟩).re) x`
(not `(fderiv ℝ f · 1).re`), matching the diff-free witnesses `forwardSliceDerivX`/
`forwardSliceDerivY`. It supplies the `hmaf` input to `ae_slice_AC_of_maf`.

## Closeability (honest assessment): the irreducible diff-free no-singular-part node.

This is the one genuinely length–area-*equality* fact of the forward direction and it is **kept as
a `sorry` residual** because every available engine for it is forbidden on this critical path:

* The **multiplicity area formula** `multiplicityAreaFormula_noSingularPart` (the repo's only
  proven no-singular-part engine, `QC/InverseQC.lean`) requires the a.e. 2D-differentiability
  hypothesis `hGdiff : ∀ᵐ w, DifferentiableAt ℝ G w` — but this leaf *feeds*
  `ae_differentiableAt_gehringLehto`, so 2D differentiability of `f` is precisely what is **not**
  yet available here (using it is a cycle, and is on the explicit forbidden list).
* The **co-area** engine `eilenberg_coarea_grad_le` (`Coarea/Assembly.lean`) needs `LipschitzWith`,
  which the QC map is not.
* The **Banach–Zaretsky** converse (`monotone_ftc_of_luzinN`, `absolutelyContinuousOnInterval_of_*`)
  would close it from a **1D Lusin-(N)** of the monotone Jordan pieces of each slice; but obtaining
  that 1D piece-(N) from the proven **2D** forward Lusin condition `IsQCGeometric.lusinN`
  (`QCLusinN.lean`) is exactly the *forward fibered Lusin-(N)* of `Φ⟨x,y⟩ = (f⟨x,y⟩).re + i·y`,
  which collapses `f`'s image transversally and is **not** derivable from `f''(null)` being null
  without the area-equality (a Fubini/co-area coupling), i.e. without the very thing being proved.

So this residual is the classical Lehto–Virtanen / Marcus–Mizel area-equality core; it is
**Mathlib/repo-absent in the diff-free regime** and is the honest minimal endpoint. (The
*inequality* half — bounded variation and `L²_loc` energy — is fully discharged diff-free from the
single `forward_lengthArea_energy` brick in `forward_ae_slice_bv`/`forward_sliceDeriv_memLp` above.)
-/
theorem IsQCGeometric.forward_ae_slice_noSingularPart {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).re) x‖₊ ∧
        eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).im) x‖₊) ∧
    (∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).re) y‖₊ ∧
        eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).im) y‖₊) := by
  sorry

/-- **Box Tonelli for an `ℝ≥0∞`-valued integrand (`y`-outer form).** For a measurable
`H : ℂ → ℝ≥0∞`, the integral over the axis rectangle `(a,b)×(s,t)` is the iterated integral with the
height `y` outer and the abscissa `x` inner. -/
private theorem setLIntegral_axisRect_eq_iterated_yx {H : ℂ → ℝ≥0∞} (hH : Measurable H)
    (a b s t : ℝ) :
    ∫⁻ w in axisRect a b s t, H w
      = ∫⁻ y in Set.Icc s t, ∫⁻ x in Set.Icc a b, H ⟨x, y⟩ := by
  classical
  -- `axisRect = equiv ⁻¹' (Icc a b ×ˢ Icc s t)`.
  have hpre : axisRect a b s t
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    simp only [axisRect, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
      Complex.measurableEquivRealProd_apply]
  have hmp : MeasurePreserving Complex.measurableEquivRealProd
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
    Complex.volume_preserving_equiv_real_prod
  -- The product-side integrand `H' p = H ⟨p.1, p.2⟩`, measurable.
  set H' : ℝ × ℝ → ℝ≥0∞ := fun p => H ⟨p.1, p.2⟩ with hH'
  have hH'meas : Measurable H' := by
    have hmk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := by
      have : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
          = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      rw [this]
      exact (Complex.measurable_ofReal.comp measurable_fst).add
        ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const)
    exact hH.comp hmk
  -- Rewrite `H w = H' (equiv w)` on the preimage and transfer via the measure-preserving equiv.
  rw [hpre]
  have hcongr : ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t), H w
      = ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t),
          H' (Complex.measurableEquivRealProd w) := by
    refine setLIntegral_congr_fun
      ((Complex.measurableEquivRealProd.measurable)
        (measurableSet_Icc.prod measurableSet_Icc)) ?_
    intro w _
    simp only [hH', Complex.measurableEquivRealProd_apply]
  rw [hcongr, hmp.setLIntegral_comp_preimage (measurableSet_Icc.prod measurableSet_Icc) hH'meas]
  -- Tonelli over the product set, then `y` outer.
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_symm' H' hH'meas]

/-- **Box Tonelli for an `ℝ≥0∞`-valued integrand (`x`-outer form).** Companion to
`setLIntegral_axisRect_eq_iterated_yx`, with the abscissa `x` outer and the height `y` inner. -/
private theorem setLIntegral_axisRect_eq_iterated_xy {H : ℂ → ℝ≥0∞} (hH : Measurable H)
    (a b s t : ℝ) :
    ∫⁻ w in axisRect a b s t, H w
      = ∫⁻ x in Set.Icc a b, ∫⁻ y in Set.Icc s t, H ⟨x, y⟩ := by
  classical
  have hpre : axisRect a b s t
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    simp only [axisRect, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
      Complex.measurableEquivRealProd_apply]
  have hmp : MeasurePreserving Complex.measurableEquivRealProd
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
    Complex.volume_preserving_equiv_real_prod
  set H' : ℝ × ℝ → ℝ≥0∞ := fun p => H ⟨p.1, p.2⟩ with hH'
  have hH'meas : Measurable H' := by
    have hmk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := by
      have : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
          = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      rw [this]
      exact (Complex.measurable_ofReal.comp measurable_fst).add
        ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const)
    exact hH.comp hmk
  rw [hpre]
  have hcongr : ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t), H w
      = ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t),
          H' (Complex.measurableEquivRealProd w) := by
    refine setLIntegral_congr_fun
      ((Complex.measurableEquivRealProd.measurable)
        (measurableSet_Icc.prod measurableSet_Icc)) ?_
    intro w _
    simp only [hH', Complex.measurableEquivRealProd_apply]
  rw [hcongr, hmp.setLIntegral_comp_preimage (measurableSet_Icc.prod measurableSet_Icc) hH'meas]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod H' hH'meas.aemeasurable]

/-- **Forward `L²_loc` slice-derivative energy (diff-free, the easy length–area direction).** For a
geometric `K`-quasiconformal map `f`, the two **slice-derivative** fields `forwardSliceDerivX f`
and `forwardSliceDerivY f` are locally square-integrable.

Proved here in full from the diff-free length–area residual `forward_lengthArea_energy`: on a
compact `Kc ⊆ [-n,n]²`, the energy `∫_{Kc} ‖forwardSliceDerivX f‖²` is bounded by the box integral
`∫_{[-n,n]²} ‖forwardSliceDerivX f‖²`, which by `setLIntegral_axisRect_eq_iterated_yx` (Tonelli) is
exactly the residual's finite derivative-energy box bound; `MemLp` follows from the slice-derivative
field's measurability (`measurable_forwardSliceDerivX`) and this finite energy.

This is the **diff-free** analogue of `IsQCGeometric.memLpLocOn_partials`: that lemma bounds the 2D
operator norm `‖fderiv ℝ f‖` via quasiconformal roundness (`qc_image_ball_diam_sq_le_volume`, the
forbidden route); here the energy is carried by the *slice* derivatives directly through the
length–area inequality, with no 2D differentiability. -/
theorem IsQCGeometric.forward_sliceDeriv_memLp {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    MemLpLocOn (forwardSliceDerivX f) 2 Set.univ ∧
    MemLpLocOn (forwardSliceDerivY f) 2 Set.univ := by
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  obtain ⟨hHoriz, hVert⟩ := hf.forward_lengthArea_energy
  -- The two slice-derivative fields are measurable.
  have hmX : Measurable (forwardSliceDerivX f) := measurable_forwardSliceDerivX hcont
  have hmY : Measurable (forwardSliceDerivY f) := measurable_forwardSliceDerivY hcont
  -- **Generic engine.** A measurable field `H : ℂ → ℂ` whose squared-norm integral is finite over
  -- every axis box is `L²_loc`.
  have engine : ∀ (H : ℂ → ℂ), Measurable H →
      (∀ a b s t : ℝ, (∫⁻ w in axisRect a b s t, (‖H w‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) ≠ ⊤) →
      MemLpLocOn H 2 Set.univ := by
    intro H hHmeas hHbox Kc _ hKcpt
    -- A box `[-n,n]²` containing `Kc`.
    obtain ⟨n, hn⟩ := hKcpt.isBounded.subset_closedBall_lt 0 0
    have hsub : Kc ⊆ axisRect (-n) n (-n) n := by
      intro w hw
      have hwn : ‖w‖ ≤ n := by
        have := hn.2 hw; rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hre : |w.re| ≤ n := le_trans (Complex.abs_re_le_norm w) hwn
      have him : |w.im| ≤ n := le_trans (Complex.abs_im_le_norm w) hwn
      rw [abs_le] at hre him
      exact ⟨⟨hre.1, hre.2⟩, ⟨him.1, him.2⟩⟩
    -- `MemLp` from measurability + finite squared-`L²` integral over `Kc`.
    refine ⟨hHmeas.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
      show ((2 : ℝ≥0∞)).toReal = 2 by norm_num]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (hHbox (-n) n (-n) n))
    exact lintegral_mono_set hsub
  -- The two box bounds, obtained from the residual's iterated forms via the Tonelli helper.
  -- Pointwise bridge `(‖z‖ₑ)^(2:ℝ) = (‖z‖₊ : ℝ≥0∞)^2`, applied under the integral binders.
  have hsq_pt : ∀ z : ℂ, (‖z‖ₑ : ℝ≥0∞) ^ (2 : ℝ) = (‖z‖₊ : ℝ≥0∞) ^ 2 := by
    intro z; rw [← enorm_eq_nnnorm, ← ENNReal.rpow_natCast, Nat.cast_ofNat]
  refine ⟨engine (forwardSliceDerivX f) hmX (fun a b s t => ?_),
    engine (forwardSliceDerivY f) hmY (fun a b s t => ?_)⟩
  · -- Horizontal: `y`-outer Tonelli matches the residual directly.
    rw [setLIntegral_axisRect_eq_iterated_yx (hmX.enorm.pow_const 2) a b s t]
    simp_rw [hsq_pt]
    exact (hHoriz a b s t).2.2
  · -- Vertical: `x`-outer Tonelli (swap the iterated order) matches the residual.
    rw [setLIntegral_axisRect_eq_iterated_xy (hmY.enorm.pow_const 2) a b s t]
    simp_rw [hsq_pt]
    exact (hVert a b s t).2.2

/-- **Forward reverse length–area: ACL slices with `L²_loc` energy (Grötzsch-free).**

A geometric `K`-quasiconformal map `f` is absolutely continuous on almost every horizontal and
vertical line, with `x`- and `y`-partials (the slice classical derivatives `gx`, `gy`) that are
locally square-integrable.

This is the **forward** reverse-length-area / length–area energy inequality, the *easy*
length–area direction:

* The **slice absolute continuity** (`ACLHorizontal`/`ACLVertical`) is already proven Grötzsch-free
  in `IsQCGeometric.ae_slice_absolutelyContinuous` (no quasiconformal-roundness, no symmetrization).
* The **`L²` slice-derivative bound** is the classical forward energy inequality
  `∫ |∂_x f|² ≤ K · area(f)`: combine the length–area lower bound for the horizontal-segment
  family on an axis rectangle with the geometric upper bound `M(f(R)) ≤ K·M(R)` and a
  Cauchy–Schwarz / Fubini estimate. This direction needs **no** Grötzsch symmetrization and **no**
  reciprocity (those are only required for the *reverse* modulus inversion `mod-lower ⟹ diam-upper`,
  the irreducible Teichmüller node).

This conclusion is *identical* to `IsQCGeometric.exists_acl_weakGradient`, by design: it is the
single Grötzsch-free residual that **replaces** the research sorry `grotzsch_symmetrization_kernel`
on the critical path of `reverseLengthArea_data`. The a.e. differentiability and pointwise
dilatation data are then recovered downstream via the proven Gehring–Lehto theorem
(`ae_differentiableAt_of_W12loc_homeomorph`) rather than via quasiconformal roundness. -/
theorem IsQCGeometric.exists_acl_memLp_sliceGradient {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∃ gx gy : ℂ → ℂ, ACLHorizontal f gx ∧ ACLVertical f gy ∧
      MemLpLocOn gx (2 : ℝ≥0∞) Set.univ ∧ MemLpLocOn gy (2 : ℝ≥0∞) Set.univ := by
  classical
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  -- The three diff-free length–area residuals.
  obtain ⟨hBVx, hBVy⟩ := hf.forward_ae_slice_bv
  obtain ⟨hNSx, hNSy⟩ := hf.forward_ae_slice_noSingularPart
  obtain ⟨hL2x, hL2y⟩ := hf.forward_sliceDeriv_memLp
  -- The horizontal/vertical embeddings are continuous in the moving coordinate.
  have hembed_x : ∀ y : ℝ, Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro y
    have he : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [he]; exact Complex.continuous_ofReal.add continuous_const
  have hembed_y : ∀ x : ℝ, Continuous (fun y : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro x
    have he : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [he]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  -- **Generic per-component AC engine for the HORIZONTAL slices.** Given a 1-Lipschitz real
  -- projection `P` whose component-slice has its variation dominated by the integral of its
  -- (1D) derivative a.e., conclude almost every horizontal `P`-slice is AC. This is the diff-free
  -- mirror of the engine inside `ae_slice_absolutelyContinuous`, fed by the residuals above.
  have hcompAC_x : ∀ (P : ℂ →L[ℝ] ℝ),
      (∀ᵐ y : ℝ, ∀ a b : ℝ,
          eVariationOn (fun x : ℝ => P (f ⟨x, y⟩)) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => P (f ⟨s, y⟩)) x‖₊) →
      ∀ᵐ y : ℝ, ∀ a c : ℝ,
        AbsolutelyContinuousOnInterval (fun x : ℝ => P (f ⟨x, y⟩)) a c := by
    intro P hNS
    set slice : ℝ → ℝ → ℝ := fun y x => P (f ⟨x, y⟩) with hslice
    have hsl_cont : ∀ y : ℝ, Continuous (slice y) := by
      intro y; exact P.continuous.comp (hcont.comp (hembed_x y))
    -- a.e. `y`, the real `P`-slice has finite variation on every interval (1-Lipschitz projection
    -- of the BV complex slice), so it is `LocallyBoundedVariationOn univ`.
    have hsl_LBV : ∀ᵐ y : ℝ, LocallyBoundedVariationOn (slice y) Set.univ := by
      filter_upwards [hBVx] with y hy
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]
      exact (P.lipschitz).comp_boundedVariationOn (g := fun x : ℝ => f ⟨x, y⟩)
        (s := Set.Icc a b) (hy a b)
    have hderiv : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, HasDerivAt (slice y) (deriv (slice y) x) x := by
      filter_upwards [hsl_LBV] with y hy
      filter_upwards [hy.ae_differentiableAt] with x hx
      exact hx.hasDerivAt
    have hint : ∀ᵐ y : ℝ, ∀ u v : ℝ,
        IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume u v := by
      filter_upwards [hderiv, hsl_LBV] with y hyderiv hyLBV u v
      have hcore : ∀ p q : ℝ, p ≤ q →
          IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume p q := by
        intro p q hpq
        have hbvfin : eVariationOn (slice y) (Set.Icc p q) ≠ ⊤ := by
          have := hyLBV p q (Set.mem_univ p) (Set.mem_univ q)
          rwa [BoundedVariationOn, Set.univ_inter] at this
        have hlint_le : ∫⁻ x in Set.Icc p q, ‖deriv (slice y) x‖₊
            ≤ eVariationOn (slice y) (Set.Icc p q) :=
          lintegral_nnnorm_deriv_le_eVariationOn hpq hyderiv
        have hfin : ∫⁻ x in Set.Icc p q, (‖deriv (slice y) x‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top hbvfin hlint_le
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
        refine ⟨((measurable_deriv (slice y)).norm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ x in Set.Ioc p q, ‖‖deriv (slice y) x‖‖ₑ
            ≤ ∫⁻ x in Set.Icc p q, (‖deriv (slice y) x‖₊ : ℝ≥0∞) := by
          refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans_eq ?_
          apply lintegral_congr; intro x; rw [enorm_norm, enorm_eq_nnnorm]
        exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
      rcases le_total u v with huv | hvu
      · exact hcore u v huv
      · exact (hcore v u hvu).symm
    have hmaf : ∀ᵐ y : ℝ, ∀ a c : ℝ,
        eVariationOn (slice y) (Set.Icc a c)
          ≤ ∫⁻ x in Set.Icc a c, ‖deriv (slice y) x‖₊ := hNS
    exact ae_slice_AC_of_maf hsl_cont hderiv hint hmaf
  -- **Generic per-component AC engine for the VERTICAL slices** (mirror).
  have hcompAC_y : ∀ (P : ℂ →L[ℝ] ℝ),
      (∀ᵐ x : ℝ, ∀ a b : ℝ,
          eVariationOn (fun y : ℝ => P (f ⟨x, y⟩)) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => P (f ⟨x, s⟩)) y‖₊) →
      ∀ᵐ x : ℝ, ∀ a c : ℝ,
        AbsolutelyContinuousOnInterval (fun y : ℝ => P (f ⟨x, y⟩)) a c := by
    intro P hNS
    set slice : ℝ → ℝ → ℝ := fun x y => P (f ⟨x, y⟩) with hslice
    have hsl_cont : ∀ x : ℝ, Continuous (slice x) := by
      intro x; exact P.continuous.comp (hcont.comp (hembed_y x))
    have hsl_LBV : ∀ᵐ x : ℝ, LocallyBoundedVariationOn (slice x) Set.univ := by
      filter_upwards [hBVy] with x hx
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]
      exact (P.lipschitz).comp_boundedVariationOn (g := fun y : ℝ => f ⟨x, y⟩)
        (s := Set.Icc a b) (hx a b)
    have hderiv : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, HasDerivAt (slice x) (deriv (slice x) y) y := by
      filter_upwards [hsl_LBV] with x hx
      filter_upwards [hx.ae_differentiableAt] with y hy
      exact hy.hasDerivAt
    have hint : ∀ᵐ x : ℝ, ∀ u v : ℝ,
        IntervalIntegrable (fun y => ‖deriv (slice x) y‖) volume u v := by
      filter_upwards [hderiv, hsl_LBV] with x hxderiv hxLBV u v
      have hcore : ∀ p q : ℝ, p ≤ q →
          IntervalIntegrable (fun y => ‖deriv (slice x) y‖) volume p q := by
        intro p q hpq
        have hbvfin : eVariationOn (slice x) (Set.Icc p q) ≠ ⊤ := by
          have := hxLBV p q (Set.mem_univ p) (Set.mem_univ q)
          rwa [BoundedVariationOn, Set.univ_inter] at this
        have hlint_le : ∫⁻ y in Set.Icc p q, ‖deriv (slice x) y‖₊
            ≤ eVariationOn (slice x) (Set.Icc p q) :=
          lintegral_nnnorm_deriv_le_eVariationOn hpq hxderiv
        have hfin : ∫⁻ y in Set.Icc p q, (‖deriv (slice x) y‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top hbvfin hlint_le
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
        refine ⟨((measurable_deriv (slice x)).norm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ y in Set.Ioc p q, ‖‖deriv (slice x) y‖‖ₑ
            ≤ ∫⁻ y in Set.Icc p q, (‖deriv (slice x) y‖₊ : ℝ≥0∞) := by
          refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans_eq ?_
          apply lintegral_congr; intro y; rw [enorm_norm, enorm_eq_nnnorm]
        exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
      rcases le_total u v with huv | hvu
      · exact hcore u v huv
      · exact (hcore v u hvu).symm
    have hmaf : ∀ᵐ x : ℝ, ∀ a c : ℝ,
        eVariationOn (slice x) (Set.Icc a c)
          ≤ ∫⁻ y in Set.Icc a c, ‖deriv (slice x) y‖₊ := hNS
    exact ae_slice_AC_of_maf hsl_cont hderiv hint hmaf
  -- **Horizontal slice AC** (both real components, recombined).
  have hHorizAC : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b := by
    have hre := hcompAC_x Complex.reCLM (by
      filter_upwards [hNSx] with y hy a b; exact (hy a b).1)
    have him := hcompAC_x Complex.imCLM (by
      filter_upwards [hNSx] with y hy a b; exact (hy a b).2)
    filter_upwards [hre, him] with y hyre hyim a b
    exact absolutelyContinuousOnInterval_of_re_im (hyre a b) (hyim a b)
  -- **Vertical slice AC** (both real components, recombined).
  have hVertAC : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b := by
    have hre := hcompAC_y Complex.reCLM (by
      filter_upwards [hNSy] with x hx a b; exact (hx a b).1)
    have him := hcompAC_y Complex.imCLM (by
      filter_upwards [hNSy] with x hx a b; exact (hx a b).2)
    filter_upwards [hre, him] with x hxre hxim a b
    exact absolutelyContinuousOnInterval_of_re_im (hxre a b) (hxim a b)
  -- **Horizontal slice derivative existence.** For a.e. `y`, the complex slice is BV on every
  -- interval, hence a.e.-`x` differentiable; the derivative is `forwardSliceDerivX f ⟨x,y⟩`.
  have hHorizDeriv : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ,
      HasDerivAt (fun t : ℝ => f ⟨t, y⟩) (forwardSliceDerivX f ⟨x, y⟩) x := by
    filter_upwards [hBVx] with y hy
    -- BV on every `[-n, n]` ⟹ a.e. differentiable.
    have hLBV : LocallyBoundedVariationOn (fun t : ℝ => f ⟨t, y⟩) Set.univ := by
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]; exact hy a b
    filter_upwards [hLBV.ae_differentiableAt] with x hx
    have : forwardSliceDerivX f ⟨x, y⟩ = deriv (fun t : ℝ => f ⟨t, y⟩) x := by
      simp only [forwardSliceDerivX]
    rw [this]; exact hx.hasDerivAt
  -- **Vertical slice derivative existence** (mirror).
  have hVertDeriv : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ,
      HasDerivAt (fun t : ℝ => f ⟨x, t⟩) (forwardSliceDerivY f ⟨x, y⟩) y := by
    filter_upwards [hBVy] with x hx
    have hLBV : LocallyBoundedVariationOn (fun t : ℝ => f ⟨x, t⟩) Set.univ := by
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]; exact hx a b
    filter_upwards [hLBV.ae_differentiableAt] with y hy
    have : forwardSliceDerivY f ⟨x, y⟩ = deriv (fun t : ℝ => f ⟨x, t⟩) y := by
      simp only [forwardSliceDerivY]
    rw [this]; exact hy.hasDerivAt
  -- Assemble the four conjuncts of the conclusion.
  refine ⟨forwardSliceDerivX f, forwardSliceDerivY f, ?_, ?_, hL2x, hL2y⟩
  · -- `ACLHorizontal f (forwardSliceDerivX f)`.
    filter_upwards [hHorizAC, hHorizDeriv] with y hyAC hyDeriv
    exact ⟨hyAC, hyDeriv⟩
  · -- `ACLVertical f (forwardSliceDerivY f)`.
    filter_upwards [hVertAC, hVertDeriv] with x hxAC hxDeriv
    exact ⟨hxAC, hxDeriv⟩

/-- **Gehring–Lehto a.e. differentiability (Grötzsch-free).**

A geometric `K`-quasiconformal map `f` is differentiable almost everywhere, obtained **without**
the quasiconformal-roundness / Grötzsch-symmetrization route. The forward reverse length–area
residual `exists_acl_memLp_sliceGradient` supplies an `L²_loc` ACL gradient `(gx, gy)`, i.e.
`f ∈ W^{1,2}_loc` as a homeomorphism; the proven Gehring–Lehto theorem
`ae_differentiableAt_of_W12loc_homeomorph` then yields total differentiability almost everywhere. -/
theorem IsQCGeometric.ae_differentiableAt_gehringLehto {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x := by
  classical
  have hfcont : Continuous f := hf.2.1.isHomeomorph.continuous
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  obtain ⟨gx, gy, haclx, hacly, hgx2, hgy2⟩ := hf.exists_acl_memLp_sliceGradient
  -- `L²_loc ⟹ L¹_loc` on compacts supplies the local integrability the weak-gradient bridge needs.
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict Kc) := hh Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hfLI : LocallyIntegrable f := hfcont.locallyIntegrable
  have hgxLI : LocallyIntegrable gx := hLIofL2 hgx2
  have hgyLI : LocallyIntegrable gy := hLIofL2 hgy2
  -- `f ∈ W^{1,2}_loc`: the ACL slice gradient is the weak gradient.
  have hwg : HasWeakGradient gx gy f Set.univ :=
    hasWeakGradient_of_acl hfLI hgxLI hgyLI haclx hacly
  -- The proven Gehring–Lehto theorem: a `W^{1,2}_loc` homeomorphism is a.e. differentiable.
  exact RiemannDynamics.GehringLehto.ae_differentiableAt_of_W12loc_homeomorph
    hhomeo hwg hgx2 hgy2

end RiemannDynamics

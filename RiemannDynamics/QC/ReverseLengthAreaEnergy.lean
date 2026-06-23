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
import RiemannDynamics.Analysis.Sobolev.AbsolutelyContinuousLines
import RiemannDynamics.Analysis.Sobolev.WeakDeriv

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
  sorry

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
  classical
  -- `1 ≤ K`, hence `0 < K`, and the dilatation constant `c = (K−1)/(K+1) ∈ [0, 1)`.
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  set c : ℝ := (K - 1) / (K + 1) with hc_def
  have hKp1_pos : (0 : ℝ) < K + 1 := by linarith
  have hc0 : (0 : ℝ) ≤ c := by rw [hc_def]; exact div_nonneg (by linarith) hKp1_pos.le
  have hc1 : c < 1 := by
    rw [hc_def, div_lt_one hKp1_pos]; linarith
  -- The dilatation algebra collapses the constant: `(1 + c)/(1 − c) = K`.
  have hconst : (1 + c) / (1 - c) = K := by
    rw [hc_def]
    have h1c : (1 : ℝ) + (K - 1) / (K + 1) = (2 * K) / (K + 1) := by
      field_simp; ring
    have h2c : (1 : ℝ) - (K - 1) / (K + 1) = 2 / (K + 1) := by
      field_simp; ring
    rw [h1c, h2c, div_div_div_cancel_right₀]
    · field_simp
    · positivity
  -- `f` is differentiable almost everywhere (the metric/Stepanov route).
  have hdiff := hf.ae_differentiableAt'
  -- ===================================================================
  -- THE SINGLE GMT RESIDUAL (the length–area *equality* / Beltrami node).
  --
  -- At almost every differentiability point the differential is nondegenerate with the
  -- sharp pointwise Beltrami bound `‖∂̄f x‖ ≤ ((K−1)/(K+1))·‖∂f x‖`.  This is the genuine
  -- two-dimensional content — the *lower*-parity infinitesimal modulus distortion (the
  -- separating/conjugate direction `det Df x ≥ (1/K)·‖Df x‖²`, equivalently the Beltrami
  -- bound), the exact mirror of the proven operator-norm *upper* bound
  -- `‖Df x‖² ≤ (C·π)·ρ(x)` of `memLpLocOn_partials`.  The repository's tools produce only
  -- upper-parity estimates (`qc_image_ball_diam_sq_le_volume`, Rengel `d²·M ≤ area`); none
  -- delivers the cross-coupling that pins the *ratio* `‖Df‖²/det Df`.  Closing this is the
  -- length–area-equality wall (`reverseLengthArea_data`, `volume ≪ ν` inverse Lusin-N).
  -- ===================================================================
  have hbeltrami : ∀ᵐ x : ℂ, DifferentiableAt ℝ f x →
      0 < (fderiv ℝ f x).det ∧ ‖dzbar f x‖ ≤ c * ‖dz f x‖ := by
    sorry
  -- Mechanical assembly: the residual + the Wirtinger dilatation algebra give both conjuncts.
  filter_upwards [hdiff, hbeltrami] with x hxdiff hx
  obtain ⟨hdetpos, hbel⟩ := hx hxdiff
  -- Sharp dilatation: `‖Df x‖² ≤ ((1+c)/(1−c))·det Df x = K·det Df x`.
  have hsharp : ‖fderiv ℝ f x‖ ^ 2 ≤ ((1 + c) / (1 - c)) * (fderiv ℝ f x).det :=
    fderiv_normSq_le_K_mul_det f x hc0 hc1 hdetpos hbel
  rw [hconst] at hsharp
  exact ⟨hsharp, ne_of_gt hdetpos⟩

end RiemannDynamics

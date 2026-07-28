/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Baernstein.CircularPolyaSzego.Subharmonicity
import RiemannDynamics.Analysis.Potential.Subharmonic

/-!
# Star-function inputs for zero-extensions of harmonic functions

This file supplies, for the zero-extension `Set.indicator V u` of a function `u` harmonic on
`V ∩ A` (`V` open, `A = {rI < ‖z − p‖ < rO}` an annulus), the analytic inputs of the re-hypothesized
small-radius sub-mean-value inequality `starPlane_subMeanValue_small`:

* `RiemannDynamics.harmonicOnNhd_comp_arcPoint` — precomposition of a harmonic function with the
  log-polar chart `w ↦ p + exp (w + φ·I)` is harmonic on the preimage of the harmonicity domain;
* `RiemannDynamics.arcIntegral_continuousOn` — the fixed-arc integral of a function continuous on
  the annulus is continuous on the log-polar band `{log rI < Re w < log rO}`;
* `RiemannDynamics.arcIntegral_le_circleAverage_indicator` — the fixed-arc integral of the
  zero-extension satisfies the sub-mean-value inequality on the band: each fibre
  `w ↦ (indicator V u) (p + exp (w + φ·I))` is the zero-extension of a harmonic function along the
  chart, hence subharmonic, and the inequality integrates over the arc-parameter set;
* `RiemannDynamics.arcIntegral_indicator_subharmonicOn` — the two previous points packaged as the
  `SubharmonicOn` predicate for the fixed-arc integral of the zero-extension;
* `RiemannDynamics.starPlane_subharmonicOn_indicator_of_attaining` — Baernstein subharmonicity of
  the star surface of the zero-extension, given a structured extremal attaining set for its star
  value at each point of the strip (the remaining hypothesis of the Sjögren surgery; for `u`
  harmonic on the full annulus it is `exists_attaining_structured`).
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-- **Harmonicity along the log-polar chart.** For `u` harmonic on an open set `V ⊆ ℂ`, the fibre
`w ↦ u (p + exp (w + φ·I))` is harmonic on the preimage of `V` under the chart
`w ↦ p + exp (w + φ·I)`: locally `u` is the real part of a holomorphic `F`, so the fibre is locally
the real part of the holomorphic `F ∘ (w ↦ p + exp (w + φ·I))`. -/
theorem harmonicOnNhd_comp_arcPoint {u : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V)
    (hu : InnerProductSpace.HarmonicOnNhd u V) (p : ℂ) (φ : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun w => u (p + Complex.exp (w + φ * Complex.I)))
      ((fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) ⁻¹' V) := by
  intro w₀ hw₀
  have hganal : ∀ w : ℂ, AnalyticAt ℂ (fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) w :=
    fun w => analyticAt_const.add (analyticAt_cexp.comp (analyticAt_id.add analyticAt_const))
  -- A ball around the image point inside `V`, and a holomorphic primitive `F` with `Re F = u`.
  obtain ⟨R, hR, hRsub⟩ :=
    Metric.isOpen_iff.1 hV (p + Complex.exp (w₀ + φ * Complex.I)) hw₀
  obtain ⟨F, hFanal, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (hu.mono hRsub)
  have hcomp := AnalyticAt.comp (g := F)
    (f := fun w : ℂ => p + Complex.exp (w + φ * Complex.I))
    (hFanal _ (Metric.mem_ball_self hR)) (hganal w₀)
  have hFg : InnerProductSpace.HarmonicAt
      (fun w => (F (p + Complex.exp (w + φ * Complex.I))).re) w₀ :=
    AnalyticAt.harmonicAt_re hcomp
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hFg
  have hnhds : (fun w : ℂ => p + Complex.exp (w + φ * Complex.I))
      ⁻¹' Metric.ball (p + Complex.exp (w₀ + φ * Complex.I)) R ∈ 𝓝 w₀ :=
    (hganal w₀).continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
  filter_upwards [hnhds] with w hw using hFeq hw

/-- The annulus `{rI < ‖z − p‖ < rO}` is open. -/
theorem isOpen_annulus (p : ℂ) (rI rO : ℝ) :
    IsOpen {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
  have h1 : IsOpen {z : ℂ | rI < ‖z - p‖} := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {z : ℂ | ‖z - p‖ < rO} := isOpen_lt (by fun_prop) continuous_const
  simpa [Set.setOf_and] using h1.inter h2

/-- The log-polar band `{log rI < Re w < log rO}` is open. -/
theorem isOpen_logPolarBand (rI rO : ℝ) :
    IsOpen {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := by
  have h1 : IsOpen {w : ℂ | Real.log rI < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {w : ℂ | w.re < Real.log rO} :=
    isOpen_lt Complex.continuous_re continuous_const
  simpa [Set.setOf_and] using h1.inter h2

/-- Points of a closed ball have real part in the window `[Re w₀ − ρ, Re w₀ + ρ]`. -/
theorem re_mem_window_of_mem_closedBall {w₀ w : ℂ} {ρ : ℝ}
    (hw : w ∈ Metric.closedBall w₀ ρ) : w₀.re - ρ ≤ w.re ∧ w.re ≤ w₀.re + ρ := by
  have h1 : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at h1
  have h3 := Metric.mem_closedBall.mp hw
  rw [dist_eq_norm] at h3
  have h2 : |w.re - w₀.re| ≤ ρ := h1.trans h3
  rw [abs_le] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- A closed ball inside the log-polar band spans the log-radius window
`[Re w₀ − ρ, Re w₀ + ρ] ⊆ (log rI, log rO)`. -/
theorem log_window_of_closedBall_subset {rI rO : ℝ} {w₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall w₀ ρ ⊆ {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO}) :
    Real.log rI < w₀.re - ρ ∧ w₀.re + ρ < Real.log rO := by
  have hmem₁ : w₀ - (ρ : ℂ) ∈ Metric.closedBall w₀ ρ := by
    have h : dist (w₀ - (ρ : ℂ)) w₀ = ρ := by
      rw [dist_eq_norm]
      have h2 : w₀ - (ρ : ℂ) - w₀ = -(ρ : ℂ) := by ring
      rw [h2, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact Metric.mem_closedBall.mpr (le_of_eq h)
  have hmem₂ : w₀ + (ρ : ℂ) ∈ Metric.closedBall w₀ ρ := by
    have h : dist (w₀ + (ρ : ℂ)) w₀ = ρ := by
      rw [dist_eq_norm]
      have h2 : w₀ + (ρ : ℂ) - w₀ = (ρ : ℂ) := by ring
      rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact Metric.mem_closedBall.mpr (le_of_eq h)
  constructor
  · have h := (hball hmem₁).1
    rwa [Complex.sub_re, Complex.ofReal_re] at h
  · have h := (hball hmem₂).2
    rwa [Complex.add_re, Complex.ofReal_re] at h

/-- **Uniform bound on the arc samples over a compact log-radius window.** For `u` continuous on
the annulus and a window `[a, b] ⊆ (log rI, log rO)`, the samples `u (p + exp (w + φ·I))` with
`Re w ∈ [a, b]` are uniformly bounded in norm: they live on the compact shell
`{exp a ≤ ‖z − p‖ ≤ exp b}` inside the annulus. -/
theorem exists_norm_bound_arcPoint {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hucont : ContinuousOn u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    {a b : ℝ} (ha : Real.log rI < a) (hb : b < Real.log rO) :
    ∃ M : ℝ, ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ∀ φ : ℝ,
      ‖u (p + Complex.exp (w + φ * Complex.I))‖ ≤ M := by
  set K : Set ℂ := {z : ℂ | Real.exp a ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ Real.exp b} with hKdef
  have hKsub : K ⊆ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
    rw [hKdef]
    rintro z ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
        _ < Real.exp a := Real.exp_lt_exp.mpr ha
        _ ≤ ‖z - p‖ := h1
    · calc ‖z - p‖ ≤ Real.exp b := h2
        _ < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hb
        _ = rO := Real.exp_log (hrI.trans hrO)
  have hKclosed : IsClosed K := by
    rw [hKdef]
    have h1 : IsClosed {z : ℂ | Real.exp a ≤ ‖z - p‖} :=
      isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {z : ℂ | ‖z - p‖ ≤ Real.exp b} :=
      isClosed_le (by fun_prop) continuous_const
    simpa [Set.setOf_and] using h1.inter h2
  have hKcompact : IsCompact K := by
    refine (isCompact_closedBall p (Real.exp b)).of_isClosed_subset hKclosed ?_
    rw [hKdef]
    rintro z ⟨-, h2⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact h2
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn (hucont.mono hKsub)
  refine ⟨M, fun w hwa hwb φ => hM _ ?_⟩
  rw [hKdef]
  exact ⟨by rw [norm_arcPoint_sub]; exact Real.exp_le_exp.mpr hwa,
    by rw [norm_arcPoint_sub]; exact Real.exp_le_exp.mpr hwb⟩

/-- **Continuity of the fixed-arc integral.** For `u` continuous on the annulus and measurable, and
a bounded arc-parameter set `E`, the log-polar arc integral `arcIntegral p u E` is continuous on
the open band `{log rI < Re w < log rO}`: the fibres are continuous in `w` and uniformly dominated
on compact log-radius shells, so dominated convergence applies. -/
theorem arcIntegral_continuousOn {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {E : Set ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hucont : ContinuousOn u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hum : Measurable u) (hEbdd : Bornology.IsBounded E) :
    ContinuousOn (arcIntegral p u E)
      {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := by
  have hEfin : volume E ≠ ⊤ := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hEbdd
    exact ne_top_of_le_ne_top (isCompact_closedBall (0 : ℝ) R).measure_lt_top.ne
      (measure_mono hR)
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict E) := isFiniteMeasure_restrict.2 hEfin
  intro w₀ hw₀
  obtain ⟨ρ, hρpos, hρsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.1 ((isOpen_logPolarBand rI rO).mem_nhds hw₀)
  obtain ⟨hlo, hhi⟩ := log_window_of_closedBall_subset hρpos hρsub
  obtain ⟨M, hM⟩ := exists_norm_bound_arcPoint hrI hrO hucont hlo hhi
  have hCA : ContinuousAt
      (fun w : ℂ => ∫ φ in E, u (p + Complex.exp (w + φ * Complex.I))) w₀ := by
    apply MeasureTheory.continuousAt_of_dominated (bound := fun _ : ℝ => M)
    · refine Filter.Eventually.of_forall fun w => Measurable.aestronglyMeasurable ?_
      apply hum.comp
      fun_prop
    · filter_upwards [Metric.closedBall_mem_nhds w₀ hρpos] with w hw
      refine Filter.Eventually.of_forall fun φ => ?_
      obtain ⟨h1, h2⟩ := re_mem_window_of_mem_closedBall hw
      exact hM w h1 h2 φ
    · exact integrable_const M
    · refine Filter.Eventually.of_forall fun φ => ?_
      have hmem := arcPoint_mem_annulus (p := p) hrI hrO φ hw₀
      exact ContinuousAt.comp (g := u)
        (f := fun w : ℂ => p + Complex.exp (w + φ * Complex.I))
        (hucont.continuousAt ((isOpen_annulus p rI rO).mem_nhds hmem))
        ((by fun_prop :
          Continuous fun w : ℂ => p + Complex.exp (w + φ * Complex.I)).continuousAt)
  exact hCA.continuousWithinAt

/-- **Subharmonicity of the zero-extension along the log-polar chart.** For `V` open and `u`
harmonic on `V ∩ A` (`A` the annulus), each fibre `w ↦ (Set.indicator V u) (p + exp (w + φ·I))` is
subharmonic on the log-polar band: it is the extension by zero, across the chart preimage of `V`,
of the chart-composed harmonic function `w ↦ u (p + exp (w + φ·I))`. -/
theorem subharmonicOn_indicator_comp_arcPoint {p : ℂ} {u : ℂ → ℝ} {V : Set ℂ} {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO) (hV : IsOpen V)
    (hu : InnerProductSpace.HarmonicOnNhd u
      (V ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}))
    (hu0 : ∀ z, 0 ≤ Set.indicator V u z)
    (hcont : ContinuousOn (Set.indicator V u) {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (φ : ℝ) :
    SubharmonicOn (fun w => Set.indicator V u (p + Complex.exp (w + φ * Complex.I)))
      {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := by
  have harcC : Continuous fun w : ℂ => p + Complex.exp (w + φ * Complex.I) := by fun_prop
  have hV' : IsOpen ((fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) ⁻¹' V) :=
    hV.preimage harcC
  have hharm : InnerProductSpace.HarmonicOnNhd
      (fun w => u (p + Complex.exp (w + φ * Complex.I)))
      (((fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) ⁻¹' V)
        ∩ {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO}) := by
    refine (harmonicOnNhd_comp_arcPoint (hV.inter (isOpen_annulus p rI rO)) hu p φ).mono ?_
    rintro w ⟨hwV, hwS⟩
    exact ⟨hwV, arcPoint_mem_annulus hrI hrO φ hwS⟩
  have hind : (fun w => Set.indicator V u (p + Complex.exp (w + φ * Complex.I)))
      = Set.indicator ((fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) ⁻¹' V)
        (fun w => u (p + Complex.exp (w + φ * Complex.I))) := by
    funext w
    by_cases hw : (p + Complex.exp (w + φ * Complex.I)) ∈ V
    · have hw' : w ∈ (fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) ⁻¹' V := hw
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw']
    · have hw' : w ∉ (fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) ⁻¹' V := hw
      rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw']
  rw [hind]
  refine subharmonicOn_indicator_of_harmonicOnNhd hV' (isOpen_logPolarBand rI rO) hharm ?_ ?_
  · rintro w ⟨hwV, -⟩
    have hwV' : (p + Complex.exp (w + φ * Complex.I)) ∈ V := hwV
    have h0 := hu0 (p + Complex.exp (w + φ * Complex.I))
    rwa [Set.indicator_of_mem hwV'] at h0
  · rw [← hind]
    exact ContinuousOn.comp (g := Set.indicator V u)
      (f := fun w : ℂ => p + Complex.exp (w + φ * Complex.I)) hcont harcC.continuousOn
      fun w hw => arcPoint_mem_annulus hrI hrO φ hw

/-- **Sub-mean-value inequality for the fixed-arc integral of a zero-extension.** For `V` open,
`u` harmonic on `V ∩ A`, and the zero-extension `Set.indicator V u` nonnegative, measurable and
continuous on the annulus `A`, the arc integral `arcIntegral p (Set.indicator V u) E` satisfies
the sub-mean-value inequality at every centre whose closed disk lies in the log-polar band: each
fibre is subharmonic (`subharmonicOn_indicator_comp_arcPoint`), and the fibrewise inequality
integrates over `E` by the Fubini interchange of the arc parameter and the circle parameter. -/
theorem arcIntegral_le_circleAverage_indicator {p : ℂ} {u : ℂ → ℝ} {V : Set ℂ} {rI rO : ℝ}
    {E : Set ℝ} {w₀ : ℂ} {ρ : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO) (hV : IsOpen V)
    (hu : InnerProductSpace.HarmonicOnNhd u
      (V ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}))
    (hu0 : ∀ z, 0 ≤ Set.indicator V u z) (hum : Measurable (Set.indicator V u))
    (hcont : ContinuousOn (Set.indicator V u) {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hE : MeasurableSet E) (hEbdd : Bornology.IsBounded E) (hρ : 0 < ρ)
    (hball : Metric.closedBall w₀ ρ
      ⊆ {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO}) :
    arcIntegral p (Set.indicator V u) E w₀
      ≤ Real.circleAverage (arcIntegral p (Set.indicator V u) E) w₀ ρ := by
  have h2π : (0 : ℝ) ≤ 2 * π := by linarith [Real.pi_pos]
  have hEfin : volume E ≠ ⊤ := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hEbdd
    exact ne_top_of_le_ne_top (isCompact_closedBall (0 : ℝ) R).measure_lt_top.ne
      (measure_mono hR)
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict E) := isFiniteMeasure_restrict.2 hEfin
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  obtain ⟨hlo, hhi⟩ := log_window_of_closedBall_subset hρ hball
  obtain ⟨M, hM⟩ := exists_norm_bound_arcPoint hrI hrO hcont hlo hhi
  have hw₀S : w₀ ∈ {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} :=
    hball (Metric.mem_closedBall_self hρ.le)
  -- Fibrewise sub-mean-value inequality from subharmonicity of each fibre.
  have hfib : ∀ φ : ℝ,
      Set.indicator V u (p + Complex.exp (w₀ + φ * Complex.I))
        ≤ Real.circleAverage
            (fun w => Set.indicator V u (p + Complex.exp (w + φ * Complex.I))) w₀ ρ :=
    fun φ => (subharmonicOn_indicator_comp_arcPoint hrI hrO hV hu hu0 hcont φ).2
      w₀ hw₀S ρ hρ hball
  -- Joint measurability and uniform bound of the circle samples.
  have hHmeas : StronglyMeasurable (fun q : ℝ × ℝ =>
      Set.indicator V u (p + Complex.exp (circleMap w₀ ρ q.2 + q.1 * Complex.I))) := by
    refine Measurable.stronglyMeasurable (hum.comp ?_)
    have hc : Continuous fun q : ℝ × ℝ =>
        p + Complex.exp (circleMap w₀ ρ q.2 + q.1 * Complex.I) :=
      continuous_const.add (((continuous_circleMap w₀ ρ).comp continuous_snd).add
        ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).cexp
    exact hc.measurable
  have hHbd : ∀ q : ℝ × ℝ,
      ‖Set.indicator V u (p + Complex.exp (circleMap w₀ ρ q.2 + q.1 * Complex.I))‖ ≤ M := by
    intro q
    obtain ⟨h1, h2⟩ := re_mem_window_of_mem_closedBall
      (circleMap_mem_closedBall w₀ hρ.le q.2)
    exact hM _ h1 h2 q.1
  -- The circle average of each fibre as a set integral over `Ioc 0 (2π)`.
  have havg_eq : ∀ φ : ℝ, Real.circleAverage
      (fun w => Set.indicator V u (p + Complex.exp (w + φ * Complex.I))) w₀ ρ
      = (2 * π)⁻¹ • ∫ t in Set.Ioc (0 : ℝ) (2 * π),
          Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)) := by
    intro φ
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le h2π]
  -- Integrability of the two integrands over `E`.
  have hint1 : IntegrableOn
      (fun φ : ℝ => Set.indicator V u (p + Complex.exp (w₀ + φ * Complex.I))) E := by
    refine Integrable.of_bound (Measurable.aestronglyMeasurable ?_) M ?_
    · apply hum.comp
      fun_prop
    · exact Filter.Eventually.of_forall fun φ =>
        hM w₀ (by linarith) (by linarith) φ
  have hint2 : IntegrableOn (fun φ : ℝ => Real.circleAverage
      (fun w => Set.indicator V u (p + Complex.exp (w + φ * Complex.I))) w₀ ρ) E := by
    have hfun : (fun φ : ℝ => Real.circleAverage
        (fun w => Set.indicator V u (p + Complex.exp (w + φ * Complex.I))) w₀ ρ)
        = fun φ : ℝ => (2 * π)⁻¹ • ∫ t in Set.Ioc (0 : ℝ) (2 * π),
            Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)) :=
      funext fun φ => havg_eq φ
    rw [hfun]
    refine Integrable.of_bound
      ((hHmeas.integral_prod_right.const_smul ((2 * π)⁻¹ : ℝ)).aestronglyMeasurable)
      ((2 * π)⁻¹ * (M * (2 * π))) ?_
    refine Filter.Eventually.of_forall fun φ => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hle := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := M)
      (s := Set.Ioc (0 : ℝ) (2 * π))
      (f := fun t => Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun t _ => hHbd (φ, t))
    refine hle.trans (le_of_eq ?_)
    have hIoc : (volume : Measure ℝ).real (Set.Ioc (0 : ℝ) (2 * π)) = 2 * π := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hIoc]
  -- The fibrewise inequality integrates over `E`.
  have hmono := setIntegral_mono_on hint1 hint2 hE fun φ _ => hfib φ
  -- Fubini: interchange the arc parameter and the circle parameter.
  have hFub : Integrable (Function.uncurry fun (φ t : ℝ) =>
      Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)))
      (((volume : Measure ℝ).restrict E).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) :=
    Integrable.of_bound hHmeas.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun q => hHbd q)
  have hswap : (∫ φ in E, ∫ t in Set.Ioc (0 : ℝ) (2 * π),
        Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)))
      = ∫ t in Set.Ioc (0 : ℝ) (2 * π), ∫ φ in E,
          Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)) :=
    MeasureTheory.integral_integral_swap hFub
  calc arcIntegral p (Set.indicator V u) E w₀
      ≤ ∫ φ in E, Real.circleAverage
          (fun w => Set.indicator V u (p + Complex.exp (w + φ * Complex.I))) w₀ ρ := hmono
    _ = ∫ φ in E, (2 * π)⁻¹ • ∫ t in Set.Ioc (0 : ℝ) (2 * π),
          Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)) :=
        setIntegral_congr_fun hE fun φ _ => havg_eq φ
    _ = (2 * π)⁻¹ • ∫ φ in E, ∫ t in Set.Ioc (0 : ℝ) (2 * π),
          Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)) :=
        integral_smul _ _
    _ = (2 * π)⁻¹ • ∫ t in Set.Ioc (0 : ℝ) (2 * π), ∫ φ in E,
          Set.indicator V u (p + Complex.exp (circleMap w₀ ρ t + φ * Complex.I)) := by
        rw [hswap]
    _ = Real.circleAverage (arcIntegral p (Set.indicator V u) E) w₀ ρ := by
        rw [Real.circleAverage_def, intervalIntegral.integral_of_le h2π]
        rfl

/-- **Subharmonicity of the fixed-arc integral of a zero-extension** on the log-polar band:
packages `arcIntegral_continuousOn` and `arcIntegral_le_circleAverage_indicator` into the
`SubharmonicOn` predicate. This is the `hsub` input of `starPlane_subMeanValue_small` for the
zero-extension `Set.indicator V u`. -/
theorem arcIntegral_indicator_subharmonicOn {p : ℂ} {u : ℂ → ℝ} {V : Set ℂ} {rI rO : ℝ}
    {E : Set ℝ}
    (hrI : 0 < rI) (hrO : rI < rO) (hV : IsOpen V)
    (hu : InnerProductSpace.HarmonicOnNhd u
      (V ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}))
    (hu0 : ∀ z, 0 ≤ Set.indicator V u z) (hum : Measurable (Set.indicator V u))
    (hcont : ContinuousOn (Set.indicator V u) {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hE : MeasurableSet E) (hEbdd : Bornology.IsBounded E) :
    SubharmonicOn (arcIntegral p (Set.indicator V u) E)
      {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := by
  refine ⟨arcIntegral_continuousOn hrI hrO hcont hum hEbdd, ?_⟩
  intro c _ ρ hρ hball
  exact arcIntegral_le_circleAverage_indicator hrI hrO hV hu hu0 hum hcont hE hEbdd hρ hball

/-- **Baernstein subharmonicity for the star surface of a zero-extension, from attaining sets.**
For `V` open, `u` harmonic on `V ∩ A`, and the zero-extension `Set.indicator V u` nonnegative,
measurable and continuous on the annulus `A`, the log-polar star surface
`starPlane p (Set.indicator V u)` is subharmonic on the open strip, provided a structured extremal
attaining set for the star value exists at every radius/aperture pair (`hattain`, the remaining
input of the Sjögren surgery; for `u` harmonic on the full annulus it is supplied by
`exists_attaining_structured`). The other two analytic inputs of `starPlane_subMeanValue_small`
are discharged by `arcIntegral_indicator_subharmonicOn` and `starPlane_continuousOn`. -/
theorem starPlane_subharmonicOn_indicator_of_attaining {p : ℂ} {u : ℂ → ℝ} {V : Set ℂ}
    {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO) (hV : IsOpen V)
    (hu : InnerProductSpace.HarmonicOnNhd u
      (V ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}))
    (hu0 : ∀ z, 0 ≤ Set.indicator V u z) (hum : Measurable (Set.indicator V u))
    (hcont : ContinuousOn (Set.indicator V u) {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hattain : ∀ r ∈ Set.Ioo rI rO, ∀ θ ∈ Set.Ioo 0 π, ∃ (τ δ : ℝ) (F : Set ℝ),
      0 < δ ∧ MeasurableSet F ∧ F ⊆ Set.Icc (τ + δ) (τ + 2 * π - δ) ∧
      volume F = ENNReal.ofReal (2 * θ) ∧
      (∃ x₀, IsLeast F x₀ ∧ Set.Icc x₀ (x₀ + δ) ⊆ F) ∧
      (∫⁻ ψ in F, ENNReal.ofReal ((angularProfile p
          (fun z => ENNReal.ofReal (Set.indicator V u z)) r ψ).toReal))
        = starFunction p (Set.indicator V u) r θ) :
    SubharmonicOn (starPlane p (Set.indicator V u)) (logPolarStrip rI rO) := by
  have hopen : IsOpen (logPolarStrip rI rO) := by
    have heq : logPolarStrip rI rO
        = Complex.re ⁻¹' Set.Ioo (Real.log rI) (Real.log rO)
          ∩ Complex.im ⁻¹' Set.Ioo (0 : ℝ) Real.pi := rfl
    rw [heq]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  refine subharmonicOn_of_locally hopen (starPlane_continuousOn hrI hrO hcont hu0 hum)
    fun c hc => starPlane_subMeanValue_small hrI hrO hcont hu0 hum ?_ ?_ hc
  · have hrmem : Real.exp c.re ∈ Set.Ioo rI rO := by
      constructor
      · calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
          _ < Real.exp c.re := Real.exp_lt_exp.mpr hc.1.1
      · calc Real.exp c.re < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hc.1.2
          _ = rO := Real.exp_log (hrI.trans hrO)
    exact hattain _ hrmem _ hc.2
  · exact fun E hEmeas hEbdd =>
      arcIntegral_indicator_subharmonicOn hrI hrO hV hu hu0 hum hcont hEmeas hEbdd

/-- **Level sets of the circle trace of a zero-extension at positive levels.** For `u` harmonic on
`U ∩ A` (`U` open, `A` the annulus) with `Set.indicator U u` continuous on `A`, and a circle radius
`r ∈ (rI, rO)`, every positive level `d > 0` of the circle profile
`ψ ↦ (Set.indicator U u) (p + r e^{i(ψ − π)})` has finite level set on each compact window, unless
the profile is identically `d`. At a level-`d` point the trace is positive, so the sample point
lies in `U` and the profile agrees near it with the real-analytic `ψ ↦ u (p + r e^{i(ψ − π)})`;
an accumulation of level points therefore propagates, by the principle of isolated zeros and a
clopen argument, to the constant value `d` on all of `ℝ`. -/
private theorem indicator_arc_level_finite_or_const {p : ℂ} {u : ℂ → ℝ} {U : Set ℂ}
    {rI rO r : ℝ} (hrI : 0 < rI) (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u
      (U ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}))
    (hcont : ContinuousOn (Set.indicator U u) {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hr : r ∈ Set.Ioo rI rO) {d : ℝ} (hd : 0 < d) :
    (∀ ψ : ℝ, Set.indicator U u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) = d)
      ∨ ∀ lo hi : ℝ, {ψ ∈ Icc lo hi |
          Set.indicator U u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) = d}.Finite
    := by
  classical
  have hr0 : 0 < r := hrI.trans hr.1
  set G : ℝ → ℝ :=
    fun ψ => Set.indicator U u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) with hGdef
  have hmA : ∀ ψ : ℝ, (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I))
      ∈ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
    intro ψ
    have hn : ‖(p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) - p‖ = r := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have him : ((((ψ - π : ℝ)) : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [him, Real.exp_zero, mul_one, abs_of_pos hr0]
    exact ⟨by rw [hn]; exact hr.1, by rw [hn]; exact hr.2⟩
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro ψ
    have hmc : Continuous
        (fun ψ : ℝ => p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) := by fun_prop
    exact ContinuousAt.comp (x := ψ) (g := Set.indicator U u)
      (hcont.continuousAt ((isOpen_annulus p rI rO).mem_nhds (hmA ψ))) hmc.continuousAt
  -- Real-analyticity of the profile at every point where its value is nonzero.
  have hGanal : ∀ x : ℝ, G x ≠ 0 → AnalyticAt ℝ G x := by
    intro x hx
    have hzU : (p + (r : ℂ) * Complex.exp (((x - π : ℝ)) * Complex.I)) ∈ U := by
      by_contra hzU
      exact hx (Set.indicator_of_notMem hzU u)
    have h0 : AnalyticAt ℝ (fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I) x := by
      have heqf : (fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I)
          = fun ψ : ℝ => (Complex.ofRealCLM ψ - ((π : ℝ) : ℂ)) * Complex.I := by
        funext φ
        rw [Complex.ofRealCLM_apply, Complex.ofReal_sub]
      rw [heqf]
      exact ((Complex.ofRealCLM.analyticAt x).sub analyticAt_const).mul analyticAt_const
    have hexpR : AnalyticAt ℝ Complex.exp ((((x - π : ℝ)) : ℂ) * Complex.I) :=
      @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
        IsScalarTower.right _ _ analyticAt_cexp
    have h1 : AnalyticAt ℝ (fun ψ : ℝ => Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) x :=
      AnalyticAt.comp (g := Complex.exp)
        (f := fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I) hexpR h0
    have h2 : AnalyticAt ℝ
        (fun ψ : ℝ => p + (r : ℂ) * Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) x :=
      analyticAt_const.add (analyticAt_const.mul h1)
    have h3 : AnalyticAt ℝ u (p + (r : ℂ) * Complex.exp (((x - π : ℝ)) * Complex.I)) :=
      HarmonicAt.analyticAt (hu _ ⟨hzU, hmA x⟩)
    have h4 := AnalyticAt.comp (g := u)
      (f := fun ψ : ℝ => p + (r : ℂ) * Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) h3 h2
    refine h4.congr ?_
    have hUopen : IsOpen ((fun ψ : ℝ =>
        p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) ⁻¹' U) :=
      hU.preimage (by fun_prop)
    filter_upwards [hUopen.mem_nhds hzU] with ψ hψ
    exact (Set.indicator_of_mem
      (show (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) ∈ U from hψ) u).symm
  by_cases hfin : ∀ lo hi : ℝ, {ψ ∈ Icc lo hi | G ψ = d}.Finite
  · exact Or.inr hfin
  · left
    push Not at hfin
    obtain ⟨lo, hi, hinf⟩ := hfin
    obtain ⟨x, -, hacc⟩ :=
      hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun ψ hψ => hψ.1)
    have hdlevel : IsClosed {t : ℝ | G t = d} := isClosed_eq hGcont continuous_const
    -- The propagation set: points near which the profile is identically `d`.
    set W : Set ℝ := {y : ℝ | ∀ᶠ z in 𝓝 y, G z = d} with hWdef
    have hWopen : IsOpen W := isOpen_setOf_eventually_nhds
    have hWval : ∀ y ∈ W, G y = d := fun y hy => hy.self_of_nhds
    have hWx : x ∈ W := by
      have hfreq : ∃ᶠ z in 𝓝[≠] x, G z = d := by
        rw [frequently_nhdsWithin_iff]
        exact (accPt_iff_frequently.mp hacc).mono (fun y hy => ⟨hy.2.2, hy.1⟩)
      have hGx : G x = d :=
        hdlevel.closure_subset
          (mem_closure_iff_frequently.mpr (hfreq.filter_mono nhdsWithin_le_nhds))
      have hanal : AnalyticAt ℝ G x := hGanal x (by rw [hGx]; exact ne_of_gt hd)
      exact (hanal.frequently_eq_iff_eventually_eq analyticAt_const).mp hfreq
    have hWclosed : IsClosed W := by
      refine isClosed_of_closure_subset (fun y hy => ?_)
      by_cases hyW : y ∈ W
      · exact hyW
      · have hGy : G y = d :=
          hdlevel.closure_subset (closure_mono (fun w hw => hWval w hw) hy)
        have hanal : AnalyticAt ℝ G y := hGanal y (by rw [hGy]; exact ne_of_gt hd)
        refine (hanal.frequently_eq_iff_eventually_eq analyticAt_const).mp ?_
        rw [frequently_nhdsWithin_iff]
        exact (mem_closure_iff_frequently.mp hy).mono
          (fun w hw => ⟨hWval w hw, fun h => hyW (h ▸ hw)⟩)
    have hWuniv : W = Set.univ := IsClopen.eq_univ ⟨hWclosed, hWopen⟩ ⟨x, hWx⟩
    intro ψ
    have hψW : ψ ∈ W := by rw [hWuniv]; exact Set.mem_univ ψ
    exact hWval ψ hψW

/-- **Structured extremal attaining set for the δ-truncation of a zero-extended harmonic
function.** For `U` open, `u` harmonic on `U ∩ A` (`A` the annulus) with nonnegative, measurable
zero-extension continuous on `A`, and a truncation level `δt > 0`, the star value of the truncated
zero-extension `Set.indicator V (u − δt)` — where `V = {z ∈ U ∩ A | δt < u z}` is open — at radius
`r ∈ (rI, rO)` and half-aperture `θ ∈ (0, π)` is attained by a set `F` with the structure required
by `starPlane_subMeanValue_small`: `F` sits in a `2π`-window with slack `δ > 0`, has measure
exactly `2θ`, and its least point carries a full interval `[x₀, x₀ + δ] ⊆ F`. The circle profile
of the truncation is `(G − δt)⁺` for the trace `G` of the zero-extension; its positive levels are
levels `> δt` of `G`, whose level sets are finite per window unless `G` is constant on the circle
(`indicator_arc_level_finite_or_const`), and the sub-level zone around a window base `τ` supplies
both the slack and, when the rearrangement level vanishes, the room for a seed interval and a
measure filler on which the truncated profile vanishes identically. -/
theorem exists_attaining_structured_indicator_truncated {p : ℂ} {u : ℂ → ℝ} {U : Set ℂ}
    {rI rO r θ δt : ℝ} (hrI : 0 < rI) (hrO : rI < rO) (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u
      (U ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}))
    (hu0 : ∀ z, 0 ≤ Set.indicator U u z) (hum : Measurable (Set.indicator U u))
    (hcont : ContinuousOn (Set.indicator U u) {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hδt : 0 < δt) (hr : r ∈ Set.Ioo rI rO) (hθ : θ ∈ Set.Ioo 0 π) :
    ∃ (τ δ : ℝ) (F : Set ℝ), 0 < δ ∧ MeasurableSet F ∧
      F ⊆ Set.Icc (τ + δ) (τ + 2 * π - δ) ∧
      volume F = ENNReal.ofReal (2 * θ) ∧
      (∃ x₀, IsLeast F x₀ ∧ Set.Icc x₀ (x₀ + δ) ⊆ F) ∧
      (∫⁻ ψ in F, ENNReal.ofReal ((angularProfile p (fun z => ENNReal.ofReal
          (Set.indicator {z : ℂ | z ∈ U ∧ rI < ‖z - p‖ ∧ ‖z - p‖ < rO ∧ δt < u z}
            (fun z => u z - δt) z)) r ψ).toReal))
        = starFunction p (Set.indicator {z : ℂ | z ∈ U ∧ rI < ‖z - p‖ ∧ ‖z - p‖ < rO ∧ δt < u z}
            (fun z => u z - δt)) r θ := by
  classical
  have _ := hrO
  have _ := hu0
  obtain ⟨hθ0, hθπ⟩ := hθ
  have hπpos : (0 : ℝ) < 2 * π := by positivity
  have hr0 : 0 < r := hrI.trans hr.1
  set A : Set ℂ := {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} with hAdef
  have hAopen : IsOpen A := by rw [hAdef]; exact isOpen_annulus p rI rO
  set V : Set ℂ := {z : ℂ | z ∈ U ∧ rI < ‖z - p‖ ∧ ‖z - p‖ < rO ∧ δt < u z} with hVdef
  set ind : ℂ → ℝ := Set.indicator V (fun z => u z - δt) with hinddef
  have hind0 : ∀ z, 0 ≤ ind z := by
    intro z
    rw [hinddef]
    by_cases hz : z ∈ V
    · rw [Set.indicator_of_mem hz]
      obtain ⟨-, -, -, h4⟩ := hz
      linarith
    · rw [Set.indicator_of_notMem hz]
  have hVU : V ⊆ U := fun z hz => hz.1
  have hVopen : IsOpen V := by
    have h2 : IsOpen ((U ∩ A) ∩ u ⁻¹' Set.Ioi δt) :=
      hu.continuousOn.isOpen_inter_preimage (hU.inter hAopen) isOpen_Ioi
    convert h2 using 1
    rw [hVdef, hAdef]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi]
    tauto
  have hindm : Measurable ind := by
    have heq : ind = Set.indicator V (fun z => Set.indicator U u z - δt) := by
      rw [hinddef]
      exact Set.indicator_congr fun z hz => by rw [Set.indicator_of_mem (hVU hz)]
    rw [heq]
    exact (hum.sub measurable_const).indicator hVopen.measurableSet
  have hindmax : ∀ z ∈ A, ind z = max (Set.indicator U u z - δt) 0 := by
    intro z hzA
    rw [hinddef]
    by_cases hzU : z ∈ U
    · by_cases hzu : δt < u z
      · rw [Set.indicator_of_mem (show z ∈ V from ⟨hzU, hzA.1, hzA.2, hzu⟩),
          Set.indicator_of_mem hzU, max_eq_left (by linarith)]
      · rw [Set.indicator_of_notMem (fun hzV : z ∈ V => hzu hzV.2.2.2),
          Set.indicator_of_mem hzU, max_eq_right (by linarith [not_lt.mp hzu])]
    · rw [Set.indicator_of_notMem (fun hzV : z ∈ V => hzU hzV.1),
        Set.indicator_of_notMem hzU, max_eq_right (by linarith)]
  have hindcont : ContinuousOn ind A := by
    have h1 : ContinuousOn (fun z => max (Set.indicator U u z - δt) 0) A :=
      fun x hx => ((hcont x hx).sub continuousWithinAt_const).max continuousWithinAt_const
    exact h1.congr hindmax
  -- The circle profiles: `G` for the zero-extension, `Gδ = (G − δt)⁺` for its truncation.
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal ((angularProfile p (fun z => ENNReal.ofReal (ind z)) r ψ).toReal)
    with hgdef
  set G : ℝ → ℝ :=
    fun ψ => Set.indicator U u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) with hGdef
  set Gδ : ℝ → ℝ :=
    fun ψ => ind (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) with hGδdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (ind z))
        (ENNReal.measurable_ofReal.comp hindm) r))
  have hgG : ∀ ψ : ℝ, g ψ = ENNReal.ofReal (Gδ ψ) := by
    intro ψ
    simp only [hgdef, hGδdef, angularProfile]
    rw [ENNReal.toReal_ofReal (hind0 _)]
  have hGδ0 : ∀ ψ : ℝ, 0 ≤ Gδ ψ := fun ψ => hind0 _
  have hmA : ∀ ψ : ℝ, (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) ∈ A := by
    intro ψ
    have hn : ‖(p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) - p‖ = r := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have him : ((((ψ - π : ℝ)) : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [him, Real.exp_zero, mul_one, abs_of_pos hr0]
    rw [hAdef]
    exact ⟨by rw [hn]; exact hr.1, by rw [hn]; exact hr.2⟩
  have hGδeq : ∀ ψ : ℝ, Gδ ψ = max (G ψ - δt) 0 := by
    intro ψ
    simp only [hGδdef, hGdef]
    exact hindmax _ (hmA ψ)
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro ψ
    have hmc : Continuous
        (fun ψ : ℝ => p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) := by fun_prop
    exact ContinuousAt.comp (x := ψ) (g := Set.indicator U u)
      (hcont.continuousAt (hAopen.mem_nhds (hmA ψ))) hmc.continuousAt
  have hGδcont : Continuous Gδ := by
    have hfe : Gδ = fun ψ => max (G ψ - δt) 0 := funext hGδeq
    rw [hfe]
    exact (hGcont.sub continuous_const).max continuous_const
  -- Periodicity of both profiles through any integer number of turns.
  have harg : ∀ (n : ℤ) (ψ : ℝ), Complex.exp (((ψ + 2 * π * n - π : ℝ)) * Complex.I)
      = Complex.exp (((ψ - π : ℝ)) * Complex.I) := by
    intro n ψ
    have hsplit : (((ψ + 2 * π * n - π : ℝ)) : ℂ) * Complex.I
        = (((ψ - π : ℝ)) : ℂ) * Complex.I + (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hGperZ : ∀ (n : ℤ) (ψ : ℝ), G (ψ + 2 * π * n) = G ψ := by
    intro n ψ; simp only [hGdef, harg]
  have hGper : ∀ ψ : ℝ, G (ψ + 2 * π) = G ψ := by
    intro ψ; simpa using hGperZ 1 ψ
  have hGδperZ : ∀ (n : ℤ) (ψ : ℝ), Gδ (ψ + 2 * π * n) = Gδ ψ := by
    intro n ψ; simp only [hGδdef, harg]
  have hgperZ : ∀ (n : ℤ) (ψ : ℝ), g (ψ + 2 * π * n) = g ψ := by
    intro n ψ; rw [hgG, hgG, hGδperZ]
  -- Uniform bound on the truncated profile, by compactness and periodic reduction.
  have hred : ∀ ψ : ℝ, ∃ s ∈ Icc (0 : ℝ) (2 * π), Gδ ψ = Gδ s := by
    intro ψ
    set n : ℤ := ⌊ψ / (2 * π)⌋ with hn
    have h1 : (n : ℝ) * (2 * π) ≤ ψ := by
      have := Int.floor_le (ψ / (2 * π))
      rwa [le_div_iff₀ hπpos] at this
    have h2 : ψ < ((n : ℝ) + 1) * (2 * π) := by
      have := Int.lt_floor_add_one (ψ / (2 * π))
      rwa [div_lt_iff₀ hπpos] at this
    refine ⟨ψ - 2 * π * n, ⟨by linarith, by linarith⟩, ?_⟩
    have := hGδperZ n (ψ - 2 * π * n)
    rwa [sub_add_cancel] at this
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hGδcont.continuousOn
  have hMle : ∀ ψ : ℝ, Gδ ψ ≤ max M0 0 := by
    intro ψ
    obtain ⟨s, hs, hGs⟩ := hred ψ
    rw [hGs]
    calc Gδ s ≤ |Gδ s| := le_abs_self _
      _ ≤ M0 := hM0 s hs
      _ ≤ max M0 0 := le_max_left _ _
  have hgleM : ∀ ψ : ℝ, g ψ ≤ ENNReal.ofReal (max M0 0) := by
    intro ψ
    rw [hgG]
    exact ENNReal.ofReal_le_ofReal (hMle ψ)
  -- The rearrangement level `c` at measure `2θ`, its real form `c'`, and the trace level `lv`.
  set c : ℝ≥0∞ := decreasingRearrange (2 * π) g (2 * θ) with hcdef
  have hP1 : distribFun (2 * π) g c ≤ ENNReal.ofReal (2 * θ) :=
    distribFun_decreasingRearrange_le (2 * θ)
  have hlt : ∀ t : ℝ≥0∞, t < c → ENNReal.ofReal (2 * θ) < distribFun (2 * π) g t :=
    fun t ht => (lt_decreasingRearrange_iff (2 * θ) t).mp ht
  have hcne : c ≠ ⊤ := by
    intro hctop
    have h1 : ENNReal.ofReal (max M0 0) < c := by rw [hctop]; exact ENNReal.ofReal_lt_top
    have h2 := hlt _ h1
    have hempty : distribFun (2 * π) g (ENNReal.ofReal (max M0 0)) = 0 := by
      have hset : {y ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal (max M0 0) < g y} = ∅ := by
        ext y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun _ => not_lt.mpr (hgleM y)
      rw [distribFun, hset, measure_empty]
    rw [hempty] at h2
    exact absurd h2 (not_lt.mpr (zero_le _))
  set c' : ℝ := c.toReal with hc'def
  have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
  have hcoe : c = ENNReal.ofReal c' := (ENNReal.ofReal_toReal hcne).symm
  set lv : ℝ := δt + c' with hlvdef
  have hlv0 : 0 < lv := by rw [hlvdef]; linarith
  have hsuper_iff : ∀ ψ : ℝ, c < g ψ ↔ lv < G ψ := by
    intro ψ
    rw [hgG ψ, hcoe, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc'0, hGδeq ψ, lt_max_iff]
    constructor
    · rintro (h | h)
      · rw [hlvdef]; linarith
      · linarith
    · intro h
      rw [hlvdef] at h
      exact Or.inl (by linarith)
  have heq_iff : c ≠ 0 → ∀ ψ : ℝ, (g ψ = c ↔ G ψ = lv) := by
    intro hc0 ψ
    have hc'pos : 0 < c' := ENNReal.toReal_pos hc0 hcne
    rw [hgG ψ, hcoe, ENNReal.ofReal_eq_ofReal_iff (hGδ0 ψ) hc'0, hGδeq ψ]
    constructor
    · intro h
      rcases le_or_gt (G ψ - δt) 0 with hle | hgt
      · rw [max_eq_right hle] at h; linarith
      · rw [max_eq_left hgt.le] at h; rw [hlvdef]; linarith
    · intro h
      rw [h, hlvdef, max_eq_left (by linarith)]
      ring
  rcases Classical.em (∀ ψ₁ ψ₂ : ℝ, Gδ ψ₁ = Gδ ψ₂) with hconst | hconst
  · -- Constant circle profile: any measure-`2θ` set attains; take the centered arc.
    have hgc : ∀ ψ : ℝ, g ψ = ENNReal.ofReal (Gδ 0) := by
      intro ψ; rw [hgG ψ, hconst ψ 0]
    have hval : ∀ E : Set ℝ, volume E = ENNReal.ofReal (2 * θ) →
        (∫⁻ ψ in E, g ψ) = ENNReal.ofReal (Gδ 0) * ENNReal.ofReal (2 * θ) := by
      intro E hE
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hgc), setLIntegral_const, hE]
    have hFsub' : Icc (π - θ) (π + θ) ⊆ Icc (0 : ℝ) (2 * π) := by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hFvol' : volume (Icc (π - θ) (π + θ)) = ENNReal.ofReal (2 * θ) := by
      rw [Real.volume_Icc]; congr 1; ring
    have hFmem : Icc (π - θ) (π + θ) ∈ {E : Set ℝ | MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) (2 * π)
        ∧ volume E = ENNReal.ofReal (2 * θ)} := ⟨measurableSet_Icc, hFsub', hFvol'⟩
    have hstar : starFunction p ind r θ = ENNReal.ofReal (Gδ 0) * ENNReal.ofReal (2 * θ) := by
      rw [show starFunction p ind r θ = starProfile (2 * π) g θ from rfl,
        starProfile_eq_iSup_setLIntegral (by positivity) hgmeas hθ0.le (by linarith)]
      apply le_antisymm
      · exact iSup₂_le fun E hE => le_of_eq (hval E hE.2.2)
      · exact le_iSup₂_of_le _ hFmem (le_of_eq (hval _ hFvol').symm)
    refine ⟨0, min (π - θ) θ, Icc (π - θ) (π + θ), lt_min (by linarith) hθ0,
      measurableSet_Icc, ?_, hFvol', ⟨π - θ, ⟨⟨le_rfl, by linarith⟩, fun y hy => hy.1⟩, ?_⟩, ?_⟩
    · intro x hx
      constructor
      · have := min_le_left (π - θ) θ; linarith [hx.1]
      · have := min_le_left (π - θ) θ; linarith [hx.2]
    · intro x hx
      have := min_le_right (π - θ) θ
      exact ⟨hx.1, by linarith [hx.2]⟩
    · rw [hval _ hFvol', hstar]
  · -- Non-constant truncated profile: level structure of `G` at the positive level `lv`.
    have hlevfin : ∀ lo hi : ℝ, {ψ ∈ Icc lo hi | G ψ = lv}.Finite := by
      rcases indicator_arc_level_finite_or_const (d := lv) hrI hU hu hcont hr hlv0 with
        hcst | hfin
      · refine absurd (fun ψ₁ ψ₂ => ?_) hconst
        have h1 : G ψ₁ = lv := hcst ψ₁
        have h2 : G ψ₂ = lv := hcst ψ₂
        rw [hGδeq ψ₁, hGδeq ψ₂, h1, h2]
      · exact hfin
    -- Lower distribution bound at the level `c` (right-continuity of the distribution function).
    have hP2 : ENNReal.ofReal (2 * θ) ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} := by
      rcases eq_or_ne c 0 with hc0 | hc0
      · have hset : {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} = Icc (0 : ℝ) (2 * π) := by
          ext x; simp only [mem_setOf_eq, hc0, zero_le, and_true]
        rw [hset, Real.volume_Icc, sub_zero]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · obtain ⟨v, hvmono, hvmem, hvtend⟩ :=
          exists_seq_strictMono_tendsto' (pos_iff_ne_zero.mpr hc0)
        set s : ℕ → Set ℝ := fun n => {x ∈ Icc (0 : ℝ) (2 * π) | v n < g x} with hs
        have hsmeas : ∀ n, MeasurableSet (s n) :=
          fun n => measurableSet_Icc.inter (measurableSet_lt measurable_const hgmeas)
        have hsanti : Antitone s :=
          fun i j hij x hx => ⟨hx.1, lt_of_le_of_lt (hvmono.monotone hij) hx.2⟩
        have hsfin : ∃ n, volume (s n) ≠ ⊤ := by
          refine ⟨0, ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))⟩
          rw [Real.volume_Icc]; exact ofReal_ne_top
        have hInter : ⋂ n, s n = {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} := by
          ext x
          simp only [mem_iInter, hs, mem_setOf_eq]
          constructor
          · intro h; exact ⟨(h 0).1, le_of_tendsto' hvtend (fun n => (h n).2.le)⟩
          · rintro ⟨hxI, hxc⟩ n; exact ⟨hxI, lt_of_lt_of_le (hvmem n).2 hxc⟩
        have htend : Tendsto (fun n => volume (s n)) atTop (𝓝 (volume (⋂ n, s n))) :=
          tendsto_measure_iInter_atTop (fun n => (hsmeas n).nullMeasurableSet) hsanti hsfin
        rw [hInter] at htend
        exact ge_of_tendsto' htend (fun n => (hlt (v n) (hvmem n).2).le)
    -- Null atoms at nonzero levels, and the exact super-level measure `2θ` there.
    have hatomnull : c ≠ 0 → volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} = 0 := by
      intro hc0
      have hset : {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}
          = {x ∈ Icc (0 : ℝ) (2 * π) | G x = lv} := by
        ext x
        simp only [mem_setOf_eq]
        exact and_congr_right (fun _ => heq_iff hc0 x)
      rw [hset]
      exact ((hlevfin 0 (2 * π)).countable).measure_zero _
    have hsupvol : c ≠ 0 →
        volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} = ENNReal.ofReal (2 * θ) := by
      intro hc0
      refine le_antisymm hP1 (le_trans hP2 ?_)
      have hsplit : {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x}
          ⊆ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := by
        rintro x ⟨hxI, hxc⟩
        rcases eq_or_lt_of_le hxc with h | h
        · exact Or.inr ⟨hxI, h.symm⟩
        · exact Or.inl ⟨hxI, h⟩
      calc volume {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x}
          ≤ volume ({x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}) := measure_mono hsplit
        _ ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              + volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := measure_union_le _ _
        _ = volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} := by rw [hatomnull hc0, add_zero]
    -- The window base `τ`: a point strictly below the trace level `lv`.
    obtain ⟨τ, hτlt⟩ : ∃ τ : ℝ, G τ < lv := by
      by_contra hcon
      push Not at hcon
      have hsubs : Icc (0 : ℝ) (2 * π) ⊆ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
          ∪ {x ∈ Icc (0 : ℝ) (2 * π) | G x = lv} := by
        intro x hx
        rcases eq_or_lt_of_le (hcon x) with h | h
        · exact Or.inr ⟨hx, h.symm⟩
        · exact Or.inl ⟨hx, (hsuper_iff x).mpr h⟩
      have hlevnull : volume {x ∈ Icc (0 : ℝ) (2 * π) | G x = lv} = 0 :=
        ((hlevfin 0 (2 * π)).countable).measure_zero _
      have hchain : ENNReal.ofReal (2 * π) ≤ ENNReal.ofReal (2 * θ) := by
        calc ENNReal.ofReal (2 * π) = volume (Icc (0 : ℝ) (2 * π)) := by
              rw [Real.volume_Icc, sub_zero]
          _ ≤ volume ({x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              ∪ {x ∈ Icc (0 : ℝ) (2 * π) | G x = lv}) := measure_mono hsubs
          _ ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              + volume {x ∈ Icc (0 : ℝ) (2 * π) | G x = lv} := measure_union_le _ _
          _ ≤ ENNReal.ofReal (2 * θ) := by rw [hlevnull, add_zero]; exact hP1
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
      linarith
    -- A sub-level zone around `τ`, capped against the aperture defect `π − θ`.
    obtain ⟨εz, hεz0, hzoneraw⟩ : ∃ εz > 0, ∀ x ∈ Icc (τ - εz) (τ + εz), G x < lv := by
      have hev : ∀ᶠ x in 𝓝 τ, G x < lv :=
        Filter.Tendsto.eventually_lt_const hτlt hGcont.continuousAt
      obtain ⟨ε, hε0, hball⟩ := Metric.eventually_nhds_iff.mp hev
      refine ⟨ε / 2, by positivity, fun x hx => hball ?_⟩
      have h1 : |x - τ| ≤ ε / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [Real.dist_eq]
      linarith
    set ε₁ : ℝ := min εz ((π - θ) / 2) with hε₁def
    have hε₁0 : 0 < ε₁ := lt_min hεz0 (by linarith)
    have hε₁θ : ε₁ ≤ (π - θ) / 2 := min_le_right _ _
    have hzone : ∀ x ∈ Icc (τ - ε₁) (τ + ε₁), G x < lv := by
      intro x hx
      have hεle : ε₁ ≤ εz := min_le_left _ _
      exact hzoneraw x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hzoneR : ∀ x ∈ Icc (τ + 2 * π - ε₁) (τ + 2 * π + ε₁), G x < lv := by
      intro x hx
      have h2 : G x = G (x - 2 * π) := by
        rw [← hGper (x - 2 * π), sub_add_cancel]
      rw [h2]
      exact hzone (x - 2 * π) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hGτ2π : G (τ + 2 * π) < lv := by rw [hGper τ]; exact hτlt
    -- The finite zero set of `G − lv` on the window `[τ, τ + 2π]`, clear of the zones.
    have hZfin : Set.Finite {ψ ∈ Icc τ (τ + 2 * π) | G ψ = lv} := hlevfin τ (τ + 2 * π)
    set Zs : Finset ℝ := hZfin.toFinset with hZsdef
    have hZmem : ∀ z : ℝ, z ∈ Zs ↔ z ∈ Icc τ (τ + 2 * π) ∧ G z = lv := by
      intro z
      rw [hZsdef, Set.Finite.mem_toFinset]
      exact Iff.rfl
    have hZlr : ∀ z ∈ Zs, τ + ε₁ < z ∧ z < τ + 2 * π - ε₁ := by
      intro z hz
      obtain ⟨⟨hz1, hz2⟩, hzlv⟩ := (hZmem z).mp hz
      constructor
      · by_contra hc
        push Not at hc
        exact absurd hzlv (ne_of_lt (hzone z ⟨by linarith, hc⟩))
      · by_contra hc
        push Not at hc
        exact absurd hzlv (ne_of_lt (hzoneR z ⟨hc, by linarith⟩))
    -- Sign constancy on zero-free open intervals, by the intermediate value theorem.
    have hsign : ∀ z₁ z₂ : ℝ, (∀ y ∈ Ioo z₁ z₂, G y ≠ lv) →
        ∀ y₁ ∈ Ioo z₁ z₂, lv < G y₁ → ∀ y ∈ Ioo z₁ z₂, lv < G y := by
      intro z₁ z₂ hnz y₁ hy₁ hy₁gt y hy
      rcases lt_trichotomy (G y) lv with hlt2 | heq2 | hgt2
      · exfalso
        rcases lt_trichotomy y y₁ with hyy | rfl | hyy
        · obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo hyy.le hGcont.continuousOn
            (show lv ∈ Ioo (G y) (G y₁) from ⟨hlt2, hy₁gt⟩)
          exact hnz z ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hy₁.2⟩ hzval
        · exact absurd hy₁gt (not_lt.mpr hlt2.le)
        · obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo' hyy.le hGcont.continuousOn
            (show lv ∈ Ioo (G y) (G y₁) from ⟨hlt2, hy₁gt⟩)
          exact hnz z ⟨lt_trans hy₁.1 hz.1, lt_trans hz.2 hy.2⟩ hzval
      · exact absurd heq2 (hnz y hy)
      · exact hgt2
    -- Every super-level point has zeros of `G − lv` on both sides within the window.
    have hlevbelow : ∀ ψ : ℝ, ψ ∈ Ioo τ (τ + 2 * π) → lv < G ψ → ∃ z ∈ Zs, z < ψ := by
      intro ψ hψ hψgt
      obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo hψ.1.le hGcont.continuousOn
        (show lv ∈ Ioo (G τ) (G ψ) from ⟨hτlt, hψgt⟩)
      exact ⟨z, (hZmem z).mpr ⟨⟨hz.1.le, by linarith [hz.2, hψ.2]⟩, hzval⟩, hz.2⟩
    have hlevabove : ∀ ψ : ℝ, ψ ∈ Ioo τ (τ + 2 * π) → lv < G ψ → ∃ z ∈ Zs, ψ < z := by
      intro ψ hψ hψgt
      obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo' hψ.2.le hGcont.continuousOn
        (show lv ∈ Ioo (G (τ + 2 * π)) (G ψ) from ⟨hGτ2π, hψgt⟩)
      exact ⟨z, (hZmem z).mpr ⟨⟨by linarith [hz.1, hψ.1], hz.2.le⟩, hzval⟩, hz.1⟩
    -- The qualifying zero pairs and the closed-arc core `F₀`.
    set Q : Finset (ℝ × ℝ) :=
      (Zs ×ˢ Zs).filter (fun q => q.1 < q.2 ∧ ∀ y ∈ Ioo q.1 q.2, lv < G y) with hQdef
    set F₀ : Set ℝ := ⋃ q ∈ Q, Icc q.1 q.2 with hF₀def
    have hQprop : ∀ q ∈ Q, q.1 ∈ Zs ∧ q.2 ∈ Zs ∧ q.1 < q.2 ∧ ∀ y ∈ Ioo q.1 q.2, lv < G y := by
      intro q hq
      rw [hQdef, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
    have hF₀meas : MeasurableSet F₀ :=
      hF₀def ▸ Q.measurableSet_biUnion (fun q _ => measurableSet_Icc)
    have hF₀mem : ∀ y : ℝ, y ∈ F₀ ↔ ∃ q ∈ Q, y ∈ Icc q.1 q.2 := by
      intro y
      rw [hF₀def]
      simp only [Set.mem_iUnion, exists_prop]
    -- The core super-level set and the two-sided sandwich for `F₀`.
    set S : Set ℝ := {ψ : ℝ | lv < G ψ} with hSdef
    have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hGcont.measurable
    have hFcore : S ∩ Ioo τ (τ + 2 * π) ⊆ F₀ := by
      rintro ψ ⟨hψgt, hψI⟩
      rw [hSdef, mem_setOf_eq] at hψgt
      obtain ⟨zb, hzbZ, hzblt⟩ := hlevbelow ψ hψI hψgt
      obtain ⟨za, hzaZ, hzagt⟩ := hlevabove ψ hψI hψgt
      have hbne : (Zs.filter (fun z => z < ψ)).Nonempty :=
        ⟨zb, Finset.mem_filter.mpr ⟨hzbZ, hzblt⟩⟩
      have hane : (Zs.filter (fun z => ψ < z)).Nonempty :=
        ⟨za, Finset.mem_filter.mpr ⟨hzaZ, hzagt⟩⟩
      set zl : ℝ := (Zs.filter (fun z => z < ψ)).max' hbne with hzldef
      set zr : ℝ := (Zs.filter (fun z => ψ < z)).min' hane with hzrdef
      have hzlmem := Finset.mem_filter.mp ((Zs.filter (fun z => z < ψ)).max'_mem hbne)
      have hzrmem := Finset.mem_filter.mp ((Zs.filter (fun z => ψ < z)).min'_mem hane)
      have hnolevel : ∀ y ∈ Ioo zl zr, G y ≠ lv := by
        intro y hy hyval
        have hyZs : y ∈ Zs := by
          refine (hZmem y).mpr ⟨⟨?_, ?_⟩, hyval⟩
          · exact le_trans ((hZmem zl).mp hzlmem.1).1.1 hy.1.le
          · exact le_trans hy.2.le ((hZmem zr).mp hzrmem.1).1.2
        rcases lt_trichotomy y ψ with h | h | h
        · exact absurd (Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hyZs, h⟩))
            (not_le.mpr hy.1)
        · exact absurd (h ▸ hyval).symm (ne_of_lt hψgt)
        · exact absurd (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hyZs, h⟩))
            (not_le.mpr hy.2)
      have hqQ : (zl, zr) ∈ Q := by
        rw [hQdef, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hzlmem.1, hzrmem.1⟩, lt_trans hzlmem.2 hzrmem.2,
          hsign zl zr hnolevel ψ ⟨hzlmem.2, hzrmem.2⟩ hψgt⟩
      exact (hF₀mem ψ).mpr ⟨(zl, zr), hqQ, ⟨hzlmem.2.le, hzrmem.2.le⟩⟩
    have hFsub : F₀ ⊆ (S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ) := by
      intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hF₀mem y).mp hy
      obtain ⟨hq1, hq2, hqlt, hqpos⟩ := hQprop q hqQ
      rcases eq_or_lt_of_le hyq.1 with h1 | h1
      · exact Or.inr (Finset.mem_coe.mpr (h1 ▸ hq1))
      · rcases eq_or_lt_of_le hyq.2 with h2 | h2
        · exact Or.inr (Finset.mem_coe.mpr (h2 ▸ hq2))
        · refine Or.inl ⟨hqpos y ⟨h1, h2⟩, ?_, ?_⟩
          · exact lt_of_le_of_lt ((hZmem q.1).mp hq1).1.1 h1
          · exact lt_of_lt_of_le h2 ((hZmem q.2).mp hq2).1.2
    -- The core lies inside the zone-trimmed window.
    have hF₀win : F₀ ⊆ Icc (τ + ε₁) (τ + 2 * π - ε₁) := by
      intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hF₀mem y).mp hy
      obtain ⟨hq1, hq2, -, -⟩ := hQprop q hqQ
      exact ⟨le_trans (hZlr q.1 hq1).1.le hyq.1, le_trans hyq.2 (hZlr q.2 hq2).2.le⟩
    -- Periodic transfer of measure and integral from the `τ`-window to the standard window.
    have hshiftIoc : ∀ (f : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), f (x + 2 * π * n) = f x) →
        ∀ (n : ℤ) (a b : ℝ),
          (∫⁻ x in Ioc a b, f x) = ∫⁻ x in Ioc (a + 2 * π * n) (b + 2 * π * n), f x := by
      intro f hper n a b
      have hmp : MeasurePreserving (fun x : ℝ => x + 2 * π * (n : ℝ)) volume volume :=
        measurePreserving_add_right volume _
      have hkey2 := hmp.setLIntegral_comp_preimage_emb
        (measurableEmbedding_addRight (2 * π * (n : ℝ))) f
        (Ioc (a + 2 * π * (n : ℝ)) (b + 2 * π * (n : ℝ)))
      have hpre : (fun x : ℝ => x + 2 * π * (n : ℝ)) ⁻¹'
          Ioc (a + 2 * π * (n : ℝ)) (b + 2 * π * (n : ℝ)) = Ioc a b := by
        ext x
        simp only [mem_preimage, mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [hpre] at hkey2
      rw [← hkey2]
      exact lintegral_congr_ae (Filter.Eventually.of_forall (fun x => (hper n x).symm))
    have hperwin : ∀ (f : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), f (x + 2 * π * n) = f x) →
        (∫⁻ x in Ioc τ (τ + 2 * π), f x) = ∫⁻ x in Ioc 0 (2 * π), f x := by
      intro f hper
      set k : ℤ := ⌈τ / (2 * π)⌉ with hkdef
      have ha1 : τ ≤ 2 * π * k := by
        have h1 := Int.le_ceil (τ / (2 * π))
        rw [div_le_iff₀ hπpos] at h1
        linarith
      have ha2 : 2 * π * k ≤ τ + 2 * π := by
        have h1 := Int.ceil_lt_add_one (τ / (2 * π))
        have h2 : (k : ℝ) * (2 * π) < (τ / (2 * π) + 1) * (2 * π) :=
          mul_lt_mul_of_pos_right h1 hπpos
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hπpos), one_mul] at h2
        linarith
      set s₀ : ℝ := τ + 2 * π - 2 * π * k with hs₀def
      have hs₀0 : 0 ≤ s₀ := by rw [hs₀def]; linarith
      have hs₀2π : s₀ ≤ 2 * π := by rw [hs₀def]; linarith
      have hdisj1 : Disjoint (Ioc τ (2 * π * k)) (Ioc (2 * π * k) (τ + 2 * π)) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, h1⟩ ⟨h2, -⟩
        exact absurd h2 (not_lt.mpr h1)
      have hdisj2 : Disjoint (Ioc (0 : ℝ) s₀) (Ioc s₀ (2 * π)) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, h1⟩ ⟨h2, -⟩
        exact absurd h2 (not_lt.mpr h1)
      have hs1 : (∫⁻ x in Ioc τ (2 * π * k), f x) = ∫⁻ x in Ioc s₀ (2 * π), f x := by
        rw [hshiftIoc f hper (1 - k) τ (2 * π * k)]
        have he1 : τ + 2 * π * ((1 - k : ℤ) : ℝ) = s₀ := by push_cast; rw [hs₀def]; ring
        have he2 : 2 * π * k + 2 * π * ((1 - k : ℤ) : ℝ) = 2 * π := by push_cast; ring
        rw [he1, he2]
      have hs2 : (∫⁻ x in Ioc (2 * π * k) (τ + 2 * π), f x) = ∫⁻ x in Ioc 0 s₀, f x := by
        rw [hshiftIoc f hper (0 - k) (2 * π * k) (τ + 2 * π)]
        have he1 : 2 * π * k + 2 * π * ((0 - k : ℤ) : ℝ) = 0 := by push_cast; ring
        have he2 : τ + 2 * π + 2 * π * ((0 - k : ℤ) : ℝ) = s₀ := by
          push_cast; rw [hs₀def]; ring
        rw [he1, he2]
      calc (∫⁻ x in Ioc τ (τ + 2 * π), f x)
          = (∫⁻ x in Ioc τ (2 * π * k), f x) + ∫⁻ x in Ioc (2 * π * k) (τ + 2 * π), f x := by
            rw [← lintegral_union measurableSet_Ioc hdisj1, Ioc_union_Ioc_eq_Ioc ha1 ha2]
        _ = (∫⁻ x in Ioc s₀ (2 * π), f x) + ∫⁻ x in Ioc 0 s₀, f x := by rw [hs1, hs2]
        _ = (∫⁻ x in Ioc (0 : ℝ) s₀, f x) + ∫⁻ x in Ioc s₀ (2 * π), f x := add_comm _ _
        _ = ∫⁻ x in Ioc 0 (2 * π), f x := by
            rw [← lintegral_union measurableSet_Ioc hdisj2, Ioc_union_Ioc_eq_Ioc hs₀0 hs₀2π]
    have hSmemper : ∀ (n : ℤ) (x : ℝ), x + 2 * π * n ∈ S ↔ x ∈ S := by
      intro n x
      simp only [hSdef, mem_setOf_eq, hGperZ]
    have hindper : ∀ (h : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), h (x + 2 * π * n) = h x) →
        ∀ (n : ℤ) (x : ℝ), S.indicator h (x + 2 * π * n) = S.indicator h x := by
      intro h hper n x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem ((hSmemper n x).mpr hx), Set.indicator_of_mem hx, hper]
      · rw [Set.indicator_of_notMem (fun hc => hx ((hSmemper n x).mp hc)),
          Set.indicator_of_notMem hx]
    have hindint : ∀ T : Set ℝ, (∫⁻ x in T, S.indicator g x) = ∫⁻ x in S ∩ T, g x := by
      intro T
      rw [lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas]
    have hindvol : ∀ T : Set ℝ,
        (∫⁻ x in T, S.indicator (fun _ => (1 : ℝ≥0∞)) x) = volume (S ∩ T) := by
      intro T
      rw [lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas, setLIntegral_one]
    have hIoo : (volume : Measure ℝ).restrict (Ioo τ (τ + 2 * π))
        = volume.restrict (Ioc τ (τ + 2 * π)) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
    have hIcc : (volume : Measure ℝ).restrict (Icc (0 : ℝ) (2 * π))
        = volume.restrict (Ioc (0 : ℝ) (2 * π)) := Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
    have hcorevol : volume (S ∩ Ioo τ (τ + 2 * π)) = volume (S ∩ Icc (0 : ℝ) (2 * π)) := by
      rw [← hindvol (Ioo τ (τ + 2 * π)), ← hindvol (Icc (0 : ℝ) (2 * π))]
      calc (∫⁻ x in Ioo τ (τ + 2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x)
          = ∫⁻ x in Ioc τ (τ + 2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x := by rw [hIoo]
        _ = ∫⁻ x in Ioc 0 (2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x :=
            hperwin _ (hindper _ (fun n x => rfl))
        _ = ∫⁻ x in Icc (0 : ℝ) (2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x := by rw [hIcc]
    have hcoreint : (∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ)
        = ∫⁻ ψ in S ∩ Icc (0 : ℝ) (2 * π), g ψ := by
      rw [← hindint (Ioo τ (τ + 2 * π)), ← hindint (Icc (0 : ℝ) (2 * π))]
      calc (∫⁻ x in Ioo τ (τ + 2 * π), S.indicator g x)
          = ∫⁻ x in Ioc τ (τ + 2 * π), S.indicator g x := by rw [hIoo]
        _ = ∫⁻ x in Ioc 0 (2 * π), S.indicator g x := hperwin _ (hindper _ hgperZ)
        _ = ∫⁻ x in Icc (0 : ℝ) (2 * π), S.indicator g x := by rw [hIcc]
    -- Identify the standard-window core with the super-level set of `g`.
    have hident : {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} = S ∩ Icc (0 : ℝ) (2 * π) := by
      ext x
      simp only [mem_setOf_eq, mem_inter_iff, hSdef]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(hsuper_iff x).mp h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, (hsuper_iff x).mpr h1⟩
    have hZsnull : volume (Zs : Set ℝ) = 0 := Zs.countable_toSet.measure_zero _
    -- Volume of the core equals the standard-window super-level measure.
    have hvol_eq : volume F₀ = volume (S ∩ Icc (0 : ℝ) (2 * π)) := by
      apply le_antisymm
      · calc volume F₀
            ≤ volume ((S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ)) := measure_mono hFsub
          _ ≤ volume (S ∩ Ioo τ (τ + 2 * π)) + volume (Zs : Set ℝ) := measure_union_le _ _
          _ = volume (S ∩ Icc (0 : ℝ) (2 * π)) := by rw [hZsnull, add_zero, hcorevol]
      · rw [← hcorevol]
        exact measure_mono hFcore
    -- Layer-cake attainment: the integral over the super-level core is the star value.
    have hEstar : (∫⁻ x in {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}, g x)
        = starFunction p ind r θ := by
      have hkey : ∀ t : ℝ,
          volume {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
          = min (ENNReal.ofReal (2 * θ)) (distribFun (2 * π) g (ENNReal.ofReal t)) := by
        intro t
        rcases le_or_gt c (ENNReal.ofReal t) with hct | hct
        · have hset : {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
              = {x ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal t < g x} := by
            ext x
            simp only [mem_setOf_eq]
            constructor
            · rintro ⟨⟨hxI, -⟩, hlt2⟩; exact ⟨hxI, hlt2⟩
            · rintro ⟨hxI, hlt2⟩; exact ⟨⟨hxI, lt_of_le_of_lt hct hlt2⟩, hlt2⟩
          rw [hset]
          change distribFun (2 * π) g (ENNReal.ofReal t) = _
          rw [min_eq_right (le_trans (distribFun_antitone hct) hP1)]
        · have hcne0 : c ≠ 0 := by
            intro h
            rw [h] at hct
            exact absurd hct (not_lt.mpr (zero_le _))
          have hset : {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
              = {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} := by
            ext x
            simp only [mem_setOf_eq]
            constructor
            · rintro ⟨hx, -⟩; exact hx
            · intro hx; exact ⟨hx, lt_trans hct hx.2⟩
          rw [hset, hsupvol hcne0, min_eq_left (hlt _ hct).le]
      rw [show starFunction p ind r θ = starProfile (2 * π) g θ from rfl,
        starProfile_eq_lintegral_min (by positivity) hθ0.le (by linarith),
        lintegral_eq_lintegral_meas_lt_ennreal hgmeas]
      exact lintegral_congr (fun t => hkey t)
    -- Integral of `g` over the core equals the star value.
    have hFstar : (∫⁻ ψ in F₀, g ψ) = starFunction p ind r θ := by
      have hup : (∫⁻ ψ in F₀, g ψ) ≤ ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ := by
        calc (∫⁻ ψ in F₀, g ψ)
            ≤ ∫⁻ ψ in (S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ), g ψ := lintegral_mono_set hFsub
          _ ≤ (∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ) + ∫⁻ ψ in (Zs : Set ℝ), g ψ :=
              lintegral_union_le _ _ _
          _ = ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ := by
              rw [setLIntegral_measure_zero _ _ hZsnull, add_zero]
      have heq1 : (∫⁻ ψ in F₀, g ψ) = ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ :=
        le_antisymm hup (lintegral_mono_set hFcore)
      rw [heq1, hcoreint, ← hident, hEstar]
    have hvle : volume F₀ ≤ ENNReal.ofReal (2 * θ) := by
      rw [hvol_eq, ← hident]
      exact hP1
    rcases eq_or_lt_of_le hvle with hveq | hvlt
    · -- The core has full measure `2θ`: it is itself the attaining set.
      have hFne : F₀.Nonempty := by
        apply nonempty_of_measure_ne_zero (μ := volume)
        rw [hveq]
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity
      obtain ⟨y₀, hy₀F⟩ := hFne
      obtain ⟨qq, hqqQ, -⟩ := (hF₀mem y₀).mp hy₀F
      have hQne : Q.Nonempty := ⟨qq, hqqQ⟩
      have hZsne : Zs.Nonempty := ⟨qq.1, (hQprop qq hqqQ).1⟩
      have hminτ : τ < Zs.min' hZsne := by
        have := (hZlr _ (Zs.min'_mem hZsne)).1
        linarith
      have hmaxτ : Zs.max' hZsne < τ + 2 * π := by
        have := (hZlr _ (Zs.max'_mem hZsne)).2
        linarith
      have hFwin : F₀ ⊆ Icc (Zs.min' hZsne) (Zs.max' hZsne) := by
        intro y hy
        obtain ⟨q, hqQ, hyq⟩ := (hF₀mem y).mp hy
        obtain ⟨h1, h2, -, -⟩ := hQprop q hqQ
        exact ⟨le_trans (Finset.min'_le _ _ h1) hyq.1, le_trans hyq.2 (Finset.le_max' _ _ h2)⟩
      have hfne : (Q.image Prod.fst).Nonempty := hQne.image _
      obtain ⟨q₀, hq₀Q, hq₀eq⟩ := Finset.mem_image.mp ((Q.image Prod.fst).min'_mem hfne)
      obtain ⟨hq₀1Z, hq₀2Z, hq₀lt, -⟩ := hQprop q₀ hq₀Q
      refine ⟨τ, min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1), F₀,
        lt_min (lt_min (by linarith) (by linarith)) (by linarith), hF₀meas, ?_, hveq,
        ⟨q₀.1, ⟨(hF₀mem q₀.1).mpr ⟨q₀, hq₀Q, ⟨le_rfl, hq₀lt.le⟩⟩, ?_⟩, ?_⟩, hFstar⟩
      · intro y hy
        have h := hFwin hy
        constructor
        · have hδ1 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
              ≤ Zs.min' hZsne - τ := le_trans (min_le_left _ _) (min_le_left _ _)
          linarith [h.1]
        · have hδ2 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
              ≤ τ + 2 * π - Zs.max' hZsne := le_trans (min_le_left _ _) (min_le_right _ _)
          linarith [h.2]
      · intro y hy
        obtain ⟨q, hqQ, hyq⟩ := (hF₀mem y).mp hy
        have hle : (Q.image Prod.fst).min' hfne ≤ q.1 :=
          Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hqQ, rfl⟩)
        rw [← hq₀eq] at hle
        linarith [hyq.1]
      · intro y hy
        refine (hF₀mem y).mpr ⟨q₀, hq₀Q, ⟨hy.1, ?_⟩⟩
        have hδ3 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
            ≤ q₀.2 - q₀.1 := min_le_right _ _
        linarith [hy.2]
    · -- Deficient core: the level `c` vanishes, so the profile vanishes off `S`; a seed interval
      -- in the sub-level zone and a filler off `S ∪ Zs` top the measure up to `2θ`.
      have hc0 : c = 0 := by
        by_contra hcne0
        have heq2 : volume F₀ = ENNReal.ofReal (2 * θ) := by
          rw [hvol_eq, ← hident]
          exact hsupvol hcne0
        exact absurd heq2 (ne_of_lt hvlt)
      have hc'eq : c' = 0 := by rw [hc'def, hc0]; simp
      have hgz : ∀ x : ℝ, x ∉ S → g x = 0 := by
        intro x hxS
        rw [hSdef, mem_setOf_eq] at hxS
        have hGx : G x ≤ lv := not_lt.mp hxS
        rw [hgG, hGδeq,
          max_eq_right (by rw [hlvdef, hc'eq] at hGx; linarith), ENNReal.ofReal_zero]
      have hvFne : volume F₀ ≠ ⊤ := hvlt.ne_top
      set vF : ℝ := (volume F₀).toReal with hvFdef
      have hvF0 : 0 ≤ vF := ENNReal.toReal_nonneg
      have hvFcoe : volume F₀ = ENNReal.ofReal vF := (ENNReal.ofReal_toReal hvFne).symm
      have hvFlt : vF < 2 * θ := by
        rw [hvFdef, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * θ)]
        exact ENNReal.toReal_strict_mono ofReal_ne_top hvlt
      set ℓ : ℝ := min (ε₁ / 4) ((2 * θ - vF) / 2) with hℓdef
      have hℓ0 : 0 < ℓ := lt_min (by positivity) (by linarith)
      have hℓa : ℓ ≤ ε₁ / 4 := min_le_left _ _
      have hℓb : ℓ ≤ (2 * θ - vF) / 2 := min_le_right _ _
      set a : ℝ := τ + ε₁ / 4 with hadef
      set m₀ : ℝ := 2 * θ - vF - ℓ with hm₀def
      have hm₀0 : 0 ≤ m₀ := by rw [hm₀def]; linarith
      set Aset : Set ℝ := Icc (τ + ε₁) (τ + 2 * π - ε₁) \ (S ∪ (Zs : Set ℝ)) with hAsetdef
      have hAmeas : MeasurableSet Aset :=
        measurableSet_Icc.diff (hSmeas.union Zs.measurableSet)
      have hAsub : Aset ⊆ Icc (τ + ε₁) (τ + 2 * π - ε₁) := Set.diff_subset
      have hcap : volume ((S ∪ (Zs : Set ℝ)) ∩ Icc (τ + ε₁) (τ + 2 * π - ε₁))
          ≤ ENNReal.ofReal vF := by
        have hsub2 : (S ∪ (Zs : Set ℝ)) ∩ Icc (τ + ε₁) (τ + 2 * π - ε₁)
            ⊆ (S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ) := by
          rintro x ⟨hxS | hxZ, hxI⟩
          · exact Or.inl ⟨hxS, ⟨by linarith [hxI.1], by linarith [hxI.2]⟩⟩
          · exact Or.inr hxZ
        calc volume ((S ∪ (Zs : Set ℝ)) ∩ Icc (τ + ε₁) (τ + 2 * π - ε₁))
            ≤ volume ((S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ)) := measure_mono hsub2
          _ ≤ volume (S ∩ Ioo τ (τ + 2 * π)) + volume (Zs : Set ℝ) := measure_union_le _ _
          _ = ENNReal.ofReal vF := by rw [hZsnull, add_zero, hcorevol, ← hvol_eq, hvFcoe]
      have hAvol : ENNReal.ofReal m₀ ≤ volume Aset := by
        have hdiffeq : Aset = Icc (τ + ε₁) (τ + 2 * π - ε₁)
            \ ((S ∪ (Zs : Set ℝ)) ∩ Icc (τ + ε₁) (τ + 2 * π - ε₁)) := by
          rw [hAsetdef, Set.diff_inter_self_eq_diff]
        calc ENNReal.ofReal m₀
            ≤ ENNReal.ofReal (2 * π - 2 * ε₁) - ENNReal.ofReal vF := by
              refine ENNReal.le_sub_of_add_le_right ofReal_ne_top ?_
              rw [← ENNReal.ofReal_add hm₀0 hvF0]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [hm₀def]
              linarith [hε₁θ, hℓ0]
          _ ≤ volume (Icc (τ + ε₁) (τ + 2 * π - ε₁))
              - volume ((S ∪ (Zs : Set ℝ)) ∩ Icc (τ + ε₁) (τ + 2 * π - ε₁)) := by
              refine tsub_le_tsub (le_of_eq ?_) hcap
              rw [Real.volume_Icc]
              congr 1
              ring
          _ ≤ volume Aset := by
              rw [hdiffeq]
              exact le_measure_diff
      obtain ⟨B, hBsub, hBmeas, hBvol⟩ := exists_measurableSet_subset_volume
        (by linarith : τ + ε₁ ≤ τ + 2 * π - ε₁) Aset hAmeas hAsub hm₀0 hAvol
      set Fb : Set ℝ := Icc a (a + ℓ) ∪ (F₀ ∪ B) with hFbdef
      have hBIcc : B ⊆ Icc (τ + ε₁) (τ + 2 * π - ε₁) := fun x hx => hAsub (hBsub hx)
      have hdisj1 : Disjoint (Icc a (a + ℓ)) (F₀ ∪ B) := by
        rw [Set.disjoint_left]
        rintro x hx (hxF | hxB)
        · have h1 := (hF₀win hxF).1
          linarith [hℓa, hx.2]
        · have h1 := (hBIcc hxB).1
          linarith [hℓa, hx.2]
      have hdisj2 : Disjoint F₀ B := by
        rw [Set.disjoint_left]
        intro x hxF hxB
        obtain ⟨-, hxNS⟩ := hBsub hxB
        rcases hFsub hxF with ⟨hxS, -⟩ | hxZ
        · exact hxNS (Or.inl hxS)
        · exact hxNS (Or.inr hxZ)
      have hFbmeas : MeasurableSet Fb := measurableSet_Icc.union (hF₀meas.union hBmeas)
      have hFbvol : volume Fb = ENNReal.ofReal (2 * θ) := by
        rw [hFbdef, measure_union' hdisj1 measurableSet_Icc,
          measure_union' hdisj2 hF₀meas, Real.volume_Icc, hvFcoe, hBvol, add_sub_cancel_left,
          ← ENNReal.ofReal_add hvF0 hm₀0, ← ENNReal.ofReal_add hℓ0.le (by linarith)]
        congr 1
        rw [hm₀def]
        ring
      set δf : ℝ := min ℓ (ε₁ / 4) with hδfdef
      have hδf0 : 0 < δf := lt_min hℓ0 (by positivity)
      have hδfℓ : δf ≤ ℓ := min_le_left _ _
      have hδfε : δf ≤ ε₁ / 4 := min_le_right _ _
      refine ⟨τ, δf, Fb, hδf0, hFbmeas, ?_, hFbvol, ⟨a, ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rintro x (hx | (hxF | hxB))
        · exact ⟨by linarith [hx.1, hδfε], by linarith [hx.2, hℓa, hδf0, hε₁θ]⟩
        · have h := hF₀win hxF
          exact ⟨by linarith [h.1, hδfε, hε₁0], by linarith [h.2, hδfε, hε₁0]⟩
        · have h := hBIcc hxB
          exact ⟨by linarith [h.1, hδfε, hε₁0], by linarith [h.2, hδfε, hε₁0]⟩
      · exact Or.inl ⟨le_rfl, by linarith [hℓ0]⟩
      · rintro x (hx | (hxF | hxB))
        · exact hx.1
        · have h := (hF₀win hxF).1
          linarith [hε₁0]
        · have h := (hBIcc hxB).1
          linarith [hε₁0]
      · intro x hx
        exact Or.inl ⟨hx.1, by linarith [hx.2, hδfℓ]⟩
      · -- The seed and the filler carry no mass of the truncated profile.
        have hzero : ∀ x ∈ Icc a (a + ℓ) ∪ B, g x = 0 := by
          rintro x (hx | hxB)
          · refine hgz x (fun hxS => ?_)
            have hlt2 : G x < lv :=
              hzone x ⟨by linarith [hx.1, hε₁0], by linarith [hx.2, hℓa]⟩
            have hgt2 : lv < G x := by
              rw [hSdef, mem_setOf_eq] at hxS
              exact hxS
            exact absurd hgt2 (not_lt.mpr hlt2.le)
          · exact hgz x (fun hxS => (hBsub hxB).2 (Or.inl hxS))
        have hle1 : (∫⁻ ψ in Fb, g ψ) ≤ ∫⁻ ψ in F₀, g ψ := by
          have hFsplit : Fb = F₀ ∪ (Icc a (a + ℓ) ∪ B) := by
            rw [hFbdef, Set.union_left_comm]
          calc (∫⁻ ψ in Fb, g ψ)
              = ∫⁻ ψ in F₀ ∪ (Icc a (a + ℓ) ∪ B), g ψ := by rw [hFsplit]
            _ ≤ (∫⁻ ψ in F₀, g ψ) + ∫⁻ ψ in Icc a (a + ℓ) ∪ B, g ψ := lintegral_union_le _ _ _
            _ = ∫⁻ ψ in F₀, g ψ := by
                rw [setLIntegral_eq_zero (measurableSet_Icc.union hBmeas) hzero, add_zero]
        have hle2 : (∫⁻ ψ in F₀, g ψ) ≤ ∫⁻ ψ in Fb, g ψ :=
          lintegral_mono_set (fun x hx => Or.inr (Or.inl hx))
        rw [le_antisymm hle1 hle2]
        exact hFstar

/-- **Baernstein subharmonicity for the star surface of a zero-extension.** For `U` open and `u`
harmonic on `U ∩ A` (`A` the annulus) with nonnegative, measurable zero-extension continuous on
`A`, the log-polar star surface `starPlane p (Set.indicator U u)` is subharmonic on the open
strip. For each truncation level `δt > 0` the truncated zero-extension
`Set.indicator {z ∈ U ∩ A | δt < u z} (u − δt)` has a subharmonic star surface
(`starPlane_subharmonicOn_indicator_of_attaining`, with attaining sets from
`exists_attaining_structured_indicator_truncated`), and on the strip the two star surfaces differ
by at most `2π · δt`; letting `δt → 0` transfers the sub-mean-value inequality on every admissible
circle. -/
theorem starPlane_subharmonicOn_indicator {p : ℂ} {u : ℂ → ℝ} {U : Set ℂ} {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO) (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u
      (U ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}))
    (hu0 : ∀ z, 0 ≤ Set.indicator U u z) (hum : Measurable (Set.indicator U u))
    (hcont : ContinuousOn (Set.indicator U u) {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}) :
    SubharmonicOn (starPlane p (Set.indicator U u)) (logPolarStrip rI rO) := by
  classical
  have hπpos : (0 : ℝ) < 2 * π := by positivity
  refine ⟨starPlane_continuousOn hrI hrO hcont hu0 hum, ?_⟩
  intro w₀ hw₀ ρ hρ hball
  have hkey : ∀ ε : ℝ, 0 < ε → starPlane p (Set.indicator U u) w₀
      ≤ Real.circleAverage (starPlane p (Set.indicator U u)) w₀ ρ + ε := by
    intro ε hε
    set δt : ℝ := ε / (2 * π) with hδtdef
    have hδt : 0 < δt := by rw [hδtdef]; positivity
    set V : Set ℂ := {z : ℂ | z ∈ U ∧ rI < ‖z - p‖ ∧ ‖z - p‖ < rO ∧ δt < u z} with hVdef
    -- The truncated zero-extension: openness, positivity, measurability, continuity, harmonicity.
    have hVU : V ⊆ U := fun z hz => hz.1
    have hVopen : IsOpen V := by
      have h2 : IsOpen ((U ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}) ∩ u ⁻¹' Set.Ioi δt) :=
        hu.continuousOn.isOpen_inter_preimage (hU.inter (isOpen_annulus p rI rO)) isOpen_Ioi
      convert h2 using 1
      rw [hVdef]
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi]
      tauto
    have hind0 : ∀ z, 0 ≤ Set.indicator V (fun z => u z - δt) z := by
      intro z
      by_cases hz : z ∈ V
      · rw [Set.indicator_of_mem hz]
        obtain ⟨-, -, -, h4⟩ := hz
        linarith
      · rw [Set.indicator_of_notMem hz]
    have hindm : Measurable (Set.indicator V (fun z => u z - δt)) := by
      have heq : Set.indicator V (fun z => u z - δt)
          = Set.indicator V (fun z => Set.indicator U u z - δt) :=
        Set.indicator_congr fun z hz => by rw [Set.indicator_of_mem (hVU hz)]
      rw [heq]
      exact (hum.sub measurable_const).indicator hVopen.measurableSet
    have hindmax : ∀ z ∈ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO},
        Set.indicator V (fun z => u z - δt) z = max (Set.indicator U u z - δt) 0 := by
      intro z hzA
      by_cases hzU : z ∈ U
      · by_cases hzu : δt < u z
        · rw [Set.indicator_of_mem (show z ∈ V from ⟨hzU, hzA.1, hzA.2, hzu⟩),
            Set.indicator_of_mem hzU, max_eq_left (by linarith)]
        · rw [Set.indicator_of_notMem (fun hzV : z ∈ V => hzu hzV.2.2.2),
            Set.indicator_of_mem hzU, max_eq_right (by linarith [not_lt.mp hzu])]
      · rw [Set.indicator_of_notMem (fun hzV : z ∈ V => hzU hzV.1),
          Set.indicator_of_notMem hzU, max_eq_right (by linarith)]
    have hindcont : ContinuousOn (Set.indicator V (fun z => u z - δt))
        {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
      have h1 : ContinuousOn (fun z => max (Set.indicator U u z - δt) 0)
          {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} :=
        fun x hx => ((hcont x hx).sub continuousWithinAt_const).max continuousWithinAt_const
      exact h1.congr hindmax
    have hharm : InnerProductSpace.HarmonicOnNhd (fun z => u z - δt)
        (V ∩ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO}) := fun z hz =>
      (hu z ⟨hz.1.1, hz.2⟩).sub (InnerProductSpace.harmonicAt_const δt)
    -- The truncated star surface is subharmonic, by the structured attaining sets.
    have hattain : ∀ r ∈ Set.Ioo rI rO, ∀ θ ∈ Set.Ioo 0 π, ∃ (τ δ : ℝ) (F : Set ℝ),
        0 < δ ∧ MeasurableSet F ∧ F ⊆ Set.Icc (τ + δ) (τ + 2 * π - δ) ∧
        volume F = ENNReal.ofReal (2 * θ) ∧
        (∃ x₀, IsLeast F x₀ ∧ Set.Icc x₀ (x₀ + δ) ⊆ F) ∧
        (∫⁻ ψ in F, ENNReal.ofReal ((angularProfile p
            (fun z => ENNReal.ofReal (Set.indicator V (fun z => u z - δt) z)) r ψ).toReal))
          = starFunction p (Set.indicator V (fun z => u z - δt)) r θ :=
      fun r hr θ hθ =>
        exists_attaining_structured_indicator_truncated hrI hrO hU hu hu0 hum hcont hδt hr hθ
    have hsubδ : SubharmonicOn (starPlane p (Set.indicator V (fun z => u z - δt)))
        (logPolarStrip rI rO) :=
      starPlane_subharmonicOn_indicator_of_attaining hrI hrO hVopen hharm hind0 hindm
        hindcont hattain
    -- Uniform circle bounds and finiteness of both star values on the strip.
    have hbound : ∀ f : ℂ → ℝ, ContinuousOn f {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} →
        ∀ w ∈ logPolarStrip rI rO, ∃ M : ℝ, ∀ φ : ℝ,
          f (p + ((Real.exp w.re : ℝ) : ℂ) * Complex.exp (φ * Complex.I)) ≤ M := by
      intro f hf w hw
      obtain ⟨M, hM⟩ := exists_norm_bound_arcPoint hrI hrO hf hw.1.1 hw.1.2
      refine ⟨M, fun φ => ?_⟩
      have h1 := hM ((w.re : ℝ) : ℂ) (by simp) (by simp) φ
      have h2 : p + Complex.exp (((w.re : ℝ) : ℂ) + φ * Complex.I)
          = p + ((Real.exp w.re : ℝ) : ℂ) * Complex.exp (φ * Complex.I) := by
        rw [Complex.exp_add, Complex.ofReal_exp]
      rw [h2] at h1
      exact le_trans (Real.le_norm_self _) h1
    have hfinU : ∀ w ∈ logPolarStrip rI rO,
        starFunction p (Set.indicator U u) (Real.exp w.re) w.im ≠ ⊤ := fun w hw =>
      (starFunction_lt_top hw.2.1.le hw.2.2.le (hbound _ hcont w hw)).ne
    have hfinV : ∀ w ∈ logPolarStrip rI rO,
        starFunction p (Set.indicator V (fun z => u z - δt)) (Real.exp w.re) w.im ≠ ⊤ :=
      fun w hw => (starFunction_lt_top hw.2.1.le hw.2.2.le (hbound _ hindcont w hw)).ne
    -- Pointwise comparison of the two zero-extensions on the annulus.
    have hind_le : ∀ z ∈ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO},
        Set.indicator V (fun z => u z - δt) z ≤ Set.indicator U u z := by
      intro z hzA
      rw [hindmax z hzA]
      rcases le_or_gt (Set.indicator U u z - δt) 0 with h | h
      · rw [max_eq_right h]
        exact hu0 z
      · rw [max_eq_left h.le]
        linarith
    have hind_ge : ∀ z ∈ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO},
        Set.indicator U u z ≤ Set.indicator V (fun z => u z - δt) z + δt := by
      intro z hzA
      rw [hindmax z hzA]
      rcases le_or_gt (Set.indicator U u z - δt) 0 with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h.le]
        linarith
    -- The star-value sandwich on the strip: `star_V ≤ star_U ≤ star_V + 2π·δt`.
    have hsand : ∀ w ∈ logPolarStrip rI rO,
        starFunction p (Set.indicator V (fun z => u z - δt)) (Real.exp w.re) w.im
          ≤ starFunction p (Set.indicator U u) (Real.exp w.re) w.im ∧
        starFunction p (Set.indicator U u) (Real.exp w.re) w.im
          ≤ starFunction p (Set.indicator V (fun z => u z - δt)) (Real.exp w.re) w.im
            + ENNReal.ofReal (2 * π * δt) := by
      intro w hw
      set r : ℝ := Real.exp w.re with hrdef
      have hrmem : r ∈ Set.Ioo rI rO := by
        rw [hrdef]
        constructor
        · calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
            _ < Real.exp w.re := Real.exp_lt_exp.mpr hw.1.1
        · calc Real.exp w.re < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hw.1.2
            _ = rO := Real.exp_log (hrI.trans hrO)
      have hr0 : 0 < r := hrI.trans hrmem.1
      have hmA : ∀ ψ : ℝ, (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I))
          ∈ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
        intro ψ
        have hn : ‖(p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) - p‖ = r := by
          rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real,
            Real.norm_eq_abs]
          have him : ((((ψ - π : ℝ)) : ℂ) * Complex.I).re = 0 := by
            simp [Complex.mul_re]
          rw [him, Real.exp_zero, mul_one, abs_of_pos hr0]
        exact ⟨by rw [hn]; exact hrmem.1, by rw [hn]; exact hrmem.2⟩
      set gU : ℝ → ℝ≥0∞ := fun ψ => ENNReal.ofReal
        ((angularProfile p (fun z => ENNReal.ofReal (Set.indicator U u z)) r ψ).toReal)
        with hgUdef
      set gV : ℝ → ℝ≥0∞ := fun ψ => ENNReal.ofReal ((angularProfile p
        (fun z => ENNReal.ofReal (Set.indicator V (fun z => u z - δt) z)) r ψ).toReal)
        with hgVdef
      have hgUeq : ∀ ψ : ℝ, gU ψ = ENNReal.ofReal
          (Set.indicator U u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I))) := by
        intro ψ
        simp only [hgUdef, angularProfile]
        rw [ENNReal.toReal_ofReal (hu0 _)]
      have hgVeq : ∀ ψ : ℝ, gV ψ = ENNReal.ofReal (Set.indicator V (fun z => u z - δt)
          (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I))) := by
        intro ψ
        simp only [hgVdef, angularProfile]
        rw [ENNReal.toReal_ofReal (hind0 _)]
      have hgUm : Measurable gU := by
        rw [hgUdef]
        exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
          (measurable_angularProfile p _ (ENNReal.measurable_ofReal.comp hum) r))
      have hgVm : Measurable gV := by
        rw [hgVdef]
        exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
          (measurable_angularProfile p _ (ENNReal.measurable_ofReal.comp hindm) r))
      have hple : ∀ ψ : ℝ, gV ψ ≤ gU ψ := fun ψ => by
        rw [hgUeq, hgVeq]
        exact ENNReal.ofReal_le_ofReal (hind_le _ (hmA ψ))
      have hpge : ∀ ψ : ℝ, gU ψ ≤ gV ψ + ENNReal.ofReal δt := fun ψ => by
        rw [hgUeq, hgVeq]
        exact le_trans (ENNReal.ofReal_le_ofReal (hind_ge _ (hmA ψ))) ENNReal.ofReal_add_le
      have hθ0 : (0 : ℝ) ≤ w.im := hw.2.1.le
      have hθT : w.im ≤ 2 * π / 2 := by linarith [hw.2.2]
      constructor
      · rw [show starFunction p (Set.indicator V (fun z => u z - δt)) r w.im
            = starProfile (2 * π) gV w.im from rfl,
          show starFunction p (Set.indicator U u) r w.im
            = starProfile (2 * π) gU w.im from rfl,
          starProfile_eq_iSup_setLIntegral hπpos hgVm hθ0 hθT,
          starProfile_eq_iSup_setLIntegral hπpos hgUm hθ0 hθT]
        exact iSup₂_le fun E hE => le_iSup₂_of_le E hE (lintegral_mono fun ψ => hple ψ)
      · rw [show starFunction p (Set.indicator V (fun z => u z - δt)) r w.im
            = starProfile (2 * π) gV w.im from rfl,
          show starFunction p (Set.indicator U u) r w.im
            = starProfile (2 * π) gU w.im from rfl,
          starProfile_eq_iSup_setLIntegral hπpos hgUm hθ0 hθT]
        refine iSup₂_le ?_
        rintro E ⟨hEmeas, hEsub, hEvol⟩
        calc (∫⁻ ψ in E, gU ψ)
            ≤ ∫⁻ ψ in E, (gV ψ + ENNReal.ofReal δt) := lintegral_mono fun ψ => hpge ψ
          _ = (∫⁻ ψ in E, gV ψ) + ENNReal.ofReal δt * volume E := by
              rw [lintegral_add_right _ measurable_const, setLIntegral_const]
          _ = (∫⁻ ψ in E, gV ψ) + ENNReal.ofReal δt * ENNReal.ofReal (2 * w.im) := by
              rw [hEvol]
          _ ≤ starProfile (2 * π) gV w.im + ENNReal.ofReal (2 * π * δt) := by
              refine add_le_add ?_ ?_
              · rw [starProfile_eq_iSup_setLIntegral hπpos hgVm hθ0 hθT]
                exact le_iSup₂_of_le E ⟨hEmeas, hEsub, hEvol⟩ le_rfl
              · rw [← ENNReal.ofReal_mul hδt.le]
                refine ENNReal.ofReal_le_ofReal ?_
                have h3 : δt * (2 * w.im) ≤ δt * (2 * π) :=
                  mul_le_mul_of_nonneg_left (by linarith [hw.2.2]) hδt.le
                linarith
    -- Transfer the sandwich to the real-valued star surfaces.
    have hplane_le : ∀ w ∈ logPolarStrip rI rO,
        starPlane p (Set.indicator V (fun z => u z - δt)) w
          ≤ starPlane p (Set.indicator U u) w := fun w hw =>
      ENNReal.toReal_mono (hfinU w hw) (hsand w hw).1
    have hplane_ge : ∀ w ∈ logPolarStrip rI rO,
        starPlane p (Set.indicator U u) w
          ≤ starPlane p (Set.indicator V (fun z => u z - δt)) w + 2 * π * δt := by
      intro w hw
      have hne : starFunction p (Set.indicator V (fun z => u z - δt)) (Real.exp w.re) w.im
          + ENNReal.ofReal (2 * π * δt) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hfinV w hw, ofReal_ne_top⟩
      have h2 := ENNReal.toReal_mono hne (hsand w hw).2
      rw [ENNReal.toReal_add (hfinV w hw) ofReal_ne_top,
        ENNReal.toReal_ofReal (by positivity)] at h2
      exact h2
    -- Sub-mean-value at `w₀` transfers through the sandwich and circle-average monotonicity.
    have hsphere : Metric.sphere w₀ ρ ⊆ logPolarStrip rI rO :=
      Metric.sphere_subset_closedBall.trans hball
    have hsphere' : Metric.sphere w₀ |ρ| ⊆ logPolarStrip rI rO := by
      rwa [abs_of_pos hρ]
    have hciU : CircleIntegrable (starPlane p (Set.indicator U u)) w₀ ρ :=
      ContinuousOn.circleIntegrable hρ.le
        ((starPlane_continuousOn hrI hrO hcont hu0 hum).mono hsphere)
    have hciV : CircleIntegrable (starPlane p (Set.indicator V (fun z => u z - δt))) w₀ ρ :=
      ContinuousOn.circleIntegrable hρ.le
        ((starPlane_continuousOn hrI hrO hindcont hind0 hindm).mono hsphere)
    have hmono := Real.circleAverage_mono hciV hciU (fun x hx => hplane_le x (hsphere' hx))
    have hsmv := hsubδ.2 w₀ hw₀ ρ hρ hball
    have h2πδt : 2 * π * δt = ε := by
      rw [hδtdef]
      field_simp
    calc starPlane p (Set.indicator U u) w₀
        ≤ starPlane p (Set.indicator V (fun z => u z - δt)) w₀ + 2 * π * δt :=
          hplane_ge w₀ hw₀
      _ ≤ Real.circleAverage (starPlane p (Set.indicator V (fun z => u z - δt))) w₀ ρ
            + 2 * π * δt := by linarith
      _ ≤ Real.circleAverage (starPlane p (Set.indicator U u)) w₀ ρ + 2 * π * δt := by
          linarith
      _ = Real.circleAverage (starPlane p (Set.indicator U u)) w₀ ρ + ε := by rw [h2πδt]
  by_contra hcon
  push Not at hcon
  have h2 := hkey ((starPlane p (Set.indicator U u) w₀
    - Real.circleAverage (starPlane p (Set.indicator U u)) w₀ ρ) / 2) (by linarith)
  linarith

end RiemannDynamics

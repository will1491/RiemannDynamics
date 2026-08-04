/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Baernstein.CircularPolyaSzego.Subharmonicity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Baernstein comparison: subharmonic minus harmonic, apex values, Phragmén–Lindelöf

Three ingredients of Baernstein's comparison argument for the star function.

* `RiemannDynamics.SubharmonicOn.sub_harmonicOnNhd` — subtracting a harmonic function preserves
  subharmonicity: circle averages are additive and harmonic functions satisfy the mean-value
  equality, so the sub-mean-value inequality survives the subtraction.
* `RiemannDynamics.logCircleMean` — the circle integral of `u` on the circle of log-radius `ξ`
  about `p`, parametrised over the angle interval `(−π, π)`; with basic positivity and
  integrability lemmas.
* `RiemannDynamics.starFunction_apex` — at full aperture `θ = π` the Baernstein star function is
  the whole-circle integral: symmetric-decreasing rearrangement preserves the total integral.
  `starFunction_apex_toReal` is the real-valued bridge to `logCircleMean`.
* `RiemannDynamics.subharmonicOn_halfStrip_nonpos` — a Phragmén–Lindelöf maximum principle on the
  half-strip `{re < 0, 0 < im < π}`: a subharmonic function bounded by the wedge bounds `2·im`
  and `2·(π − im)` on the strip and asymptotically nonpositive at the right edge is nonpositive.
  The proof runs the maximum principle against the harmonic barrier `ε·e^{−re}·sin(im)` on large
  bounded rectangles, using Jordan's inequality `2·min(θ, π−θ) ≤ π·sin θ` on the far-left edge.
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-! ### Subtracting a harmonic function preserves subharmonicity -/

/-- **Subharmonic minus harmonic is subharmonic.** If `f` is subharmonic on `U` and `h` is
harmonic on a neighbourhood of each point of `U`, then `f − h` is subharmonic on `U`: circle
averages are additive, and `h` satisfies the mean-value equality on every closed disk in `U`. -/
theorem SubharmonicOn.sub_harmonicOnNhd {f h : ℂ → ℝ} {U : Set ℂ}
    (hf : SubharmonicOn f U) (hh : InnerProductSpace.HarmonicOnNhd h U) :
    SubharmonicOn (fun z => f z - h z) U := by
  obtain ⟨hfc, hfmv⟩ := hf
  refine ⟨hfc.sub hh.continuousOn, ?_⟩
  intro c hc r hr hsub
  have hsphere : Metric.sphere c r ⊆ U :=
    Metric.sphere_subset_closedBall.trans hsub
  have hfci : CircleIntegrable f c r :=
    (hfc.mono hsphere).circleIntegrable hr.le
  have hhci : CircleIntegrable h c r :=
    (hh.continuousOn.mono hsphere).circleIntegrable hr.le
  -- The circle average splits, and the harmonic term has the mean-value equality.
  rw [Real.circleAverage_fun_sub hfci hhci]
  have hhavg : Real.circleAverage h c r = h c := by
    apply HarmonicOnNhd.circleAverage_eq
    rw [abs_of_pos hr]
    exact hh.mono hsub
  have hfavg : f c ≤ Real.circleAverage f c r := hfmv c hc r hr hsub
  rw [hhavg]
  linarith

/-! ### The circle mean in log-polar coordinates -/

/-- **The log-polar circle mean.** The integral of `u` over the circle of radius `e^ξ` about `p`,
parametrised by the angle `θ ∈ (−π, π)`:
`logCircleMean p u ξ = ∫_{(−π,π)} u (p + e^{ξ + iθ}) dθ`. -/
def logCircleMean (p : ℂ) (u : ℂ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Set.Ioo (-π) π, u (p + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- The point `p + e^{ξ + iθ}` lies on the sphere of radius `e^ξ` about `p`. -/
theorem logCircleMean_point_mem_sphere (p : ℂ) (ξ θ : ℝ) :
    p + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Metric.sphere p (Real.exp ξ) := by
  simp only [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
  simp

/-- The circle parametrisation `θ ↦ u (p + e^{ξ + iθ})` of a function continuous on the sphere of
radius `e^ξ` is integrable on `(−π, π)`. -/
theorem integrableOn_logCircleMean_param {p : ℂ} {u : ℂ → ℝ} {ξ : ℝ}
    (hu : ContinuousOn u (Metric.sphere p (Real.exp ξ))) :
    IntegrableOn (fun θ : ℝ => u (p + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Set.Ioo (-π) π) := by
  have hparam : Continuous fun θ : ℝ => p + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hcont : ContinuousOn
      (fun θ : ℝ => u (p + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Set.Icc (-π) π) :=
    hu.comp hparam.continuousOn fun θ _ => logCircleMean_point_mem_sphere p ξ θ
  exact (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self

/-- The log-polar circle mean of a function nonnegative on the sphere is nonnegative. -/
theorem logCircleMean_nonneg {p : ℂ} {u : ℂ → ℝ} {ξ : ℝ}
    (hu : ∀ z ∈ Metric.sphere p (Real.exp ξ), 0 ≤ u z) :
    0 ≤ logCircleMean p u ξ := by
  apply setIntegral_nonneg measurableSet_Ioo
  intro θ _
  exact hu _ (logCircleMean_point_mem_sphere p ξ θ)

/-! ### The star function at full aperture -/

/-- Double truncation collapses: `ofReal ∘ toReal ∘ ofReal = ofReal`. -/
theorem ofReal_toReal_ofReal (a : ℝ) :
    ENNReal.ofReal ((ENNReal.ofReal a).toReal) = ENNReal.ofReal a := by
  rcases le_or_gt 0 a with ha | ha
  · rw [ENNReal.toReal_ofReal ha]
  · simp [ENNReal.ofReal_of_nonpos ha.le]

/-- **The star function at full aperture is the whole-circle integral.** At `θ = π` the centered
arc `[T/2 − θ, T/2 + θ]` is the whole parameter interval `[0, 2π]`, and the symmetric-decreasing
rearrangement preserves the total integral. -/
theorem starFunction_apex (p : ℂ) {u : ℂ → ℝ} (hu : Measurable u) (r : ℝ) :
    starFunction p u r π
      = ∫⁻ φ in Icc (0 : ℝ) (2 * π),
          ENNReal.ofReal (u (p + (r : ℂ) * Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I))) := by
  have hg : Measurable fun φ =>
      ENNReal.ofReal ((angularProfile p (fun z => ENNReal.ofReal (u z)) r φ).toReal) :=
    ((measurable_angularProfile p _ hu.ennreal_ofReal r).ennreal_toReal).ennreal_ofReal
  have hlo : 2 * π / 2 - π = (0 : ℝ) := by ring
  have hhi : 2 * π / 2 + π = 2 * π := by ring
  rw [starFunction, starProfile, hlo, hhi,
    lintegral_decreasingRearrangeSymm_eq (by positivity) hg]
  refine lintegral_congr fun φ => ?_
  simp only [angularProfile]
  exact ofReal_toReal_ofReal _

/-- **The apex value of the star function is the log-polar circle mean.** For `u` measurable and
nonnegative on the circle of radius `r > 0` about `p`, the full-aperture star value coincides —
after the `ℝ≥0∞ → ℝ` bridge — with the circle integral `logCircleMean p u (log r)`. -/
theorem starFunction_apex_toReal {p : ℂ} {u : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hu : Measurable u)
    (hnn : ∀ z ∈ Metric.sphere p r, 0 ≤ u z) :
    (starFunction p u r π).toReal = logCircleMean p u (Real.log r) := by
  -- Points of the parametrised circle lie on the sphere of radius `r`.
  have hmem : ∀ θ : ℝ, p + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.sphere p r := by
    intro θ
    simp [Complex.norm_exp, abs_of_pos hr]
  -- Rewrite the log-polar circle mean over the radius-`r` circle.
  have hexp : ∀ θ : ℝ, p + Complex.exp ((Real.log r : ℂ) + (θ : ℂ) * Complex.I)
      = p + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  -- The `Bochner = lintegral` bridge for the nonnegative integrand.
  have hae : 0 ≤ᵐ[volume.restrict (Ioo (-π) π)]
      fun θ : ℝ => u (p + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun θ _ => hnn _ (hmem θ)
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => u (p + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      (volume.restrict (Ioo (-π) π)) := by
    have hcont : Continuous fun θ : ℝ => p + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      fun_prop
    exact (hu.comp hcont.measurable).aestronglyMeasurable
  have hbridge : logCircleMean p u (Real.log r)
      = (∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (u (p + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))).toReal := by
    simp only [logCircleMean, hexp]
    rw [integral_eq_lintegral_of_nonneg_ae hae hmeas]
  -- Translation change of variables `φ = θ + π` on the lintegral side.
  have hpre : (fun θ : ℝ => θ + π) ⁻¹' Icc (0 : ℝ) (2 * π) = Icc (-π) π := by
    ext θ
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hcov := (measurePreserving_add_right volume π).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight π).measurableEmbedding
    (fun φ : ℝ => ENNReal.ofReal
      (u (p + (r : ℂ) * Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I))))
    (Icc (0 : ℝ) (2 * π))
  rw [hpre] at hcov
  simp only [add_sub_cancel_right] at hcov
  rw [starFunction_apex p hu r, hbridge, ← hcov,
    setLIntegral_congr (Ioo_ae_eq_Icc (μ := volume) (a := -π) (b := π))]

/-! ### Phragmén–Lindelöf on the half-strip -/

/-- Subharmonicity restricts to subsets: every closed disk in the smaller set lies in the larger
one, so the sub-mean-value inequality carries over. -/
theorem SubharmonicOn.mono {f : ℂ → ℝ} {U V : Set ℂ} (hf : SubharmonicOn f U) (hVU : V ⊆ U) :
    SubharmonicOn f V :=
  ⟨hf.1.mono hVU, fun c hc r hr hball => hf.2 c (hVU hc) r hr (hball.trans hVU)⟩

/-- **Jordan's inequality for the wedge bound**: `2·min(θ, π − θ) ≤ π·sin θ` on `[0, π]`. On the
left half this is `2θ/π ≤ sin θ`; on the right half apply the reflection `sin θ = sin (π − θ)`. -/
theorem two_mul_min_le_pi_mul_sin {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    2 * min θ (π - θ) ≤ π * Real.sin θ := by
  have hπ0 : (0 : ℝ) < π := Real.pi_pos
  rcases le_total θ (π / 2) with hh | hh
  · have hs := Real.mul_le_sin h0 hh
    have hs' : 2 * θ ≤ π * Real.sin θ := by
      calc 2 * θ = π * (2 / π * θ) := by field_simp
        _ ≤ π * Real.sin θ := mul_le_mul_of_nonneg_left hs hπ0.le
    linarith [min_le_left θ (π - θ)]
  · have hs := Real.mul_le_sin (x := π - θ) (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at hs
    have hs' : 2 * (π - θ) ≤ π * Real.sin θ := by
      calc 2 * (π - θ) = π * (2 / π * (π - θ)) := by field_simp
        _ ≤ π * Real.sin θ := mul_le_mul_of_nonneg_left hs hπ0.le
    linarith [min_le_right θ (π - θ)]

/-- **The Phragmén–Lindelöf barrier is harmonic**: `w ↦ ε·e^{−Re w}·sin (Im w)` is the imaginary
part of the entire function `w ↦ −ε·e^{−w}`. -/
theorem harmonicOnNhd_barrier (ε : ℝ) :
    InnerProductSpace.HarmonicOnNhd
      (fun w : ℂ => ε * Real.exp (-w.re) * Real.sin w.im) Set.univ := by
  have heq : (fun w : ℂ => ε * Real.exp (-w.re) * Real.sin w.im)
      = fun w : ℂ => (-(ε : ℂ) * Complex.exp (-w)).im := by
    funext w
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_im, Real.sin_neg, neg_zero, zero_mul, add_zero]
    ring
  rw [heq]
  intro x _
  exact (analyticAt_const.mul (analyticAt_id.neg.cexp')).harmonicAt_im

/-- **The rectangle estimate.** On a bounded rectangle inside the half-strip
`{re < 0, 0 < im < π}`, a subharmonic `J` obeying the wedge bounds `J ≤ 2·im`, `J ≤ 2·(π − im)`
on the strip and `J ≤ ε` near the right edge is bounded by `ε + 2η` plus the harmonic barrier
`ε·e^{−re}·sin im`, provided the barrier dominates the wedge bound on the far-left edge
(`π ≤ ε·e^R`). -/
theorem halfStrip_rect_bound {J : ℂ → ℝ} {ε δ' η R : ℝ}
    (hJ : SubharmonicOn J {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π})
    (h0 : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, J w ≤ 2 * w.im)
    (hπ : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, J w ≤ 2 * (π - w.im))
    (hedge : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, -δ' ≤ w.re → J w ≤ ε)
    (hεpos : 0 < ε) (hδ'pos : 0 < δ') (hηpos : 0 < η) (hηπ : η < π - η)
    (hRδ' : -R < -δ') (hRε : π ≤ ε * Real.exp R) :
    ∀ w ∈ Ioo (-R) (-δ') ×ℂ Ioo η (π - η),
      J w ≤ ε + 2 * η + ε * Real.exp (-w.re) * Real.sin w.im := by
  set Q : Set ℂ := Ioo (-R) (-δ') ×ℂ Ioo η (π - η) with hQ
  -- The closed rectangle sits inside the open half-strip.
  have hclQ : closure Q ⊆ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} := by
    intro w hw
    rw [hQ, Complex.closure_reProdIm, closure_Ioo hRδ'.ne, closure_Ioo hηπ.ne,
      Complex.mem_reProdIm, mem_Icc, mem_Icc] at hw
    exact ⟨lt_of_le_of_lt hw.1.2 (by linarith), lt_of_lt_of_le hηpos hw.2.1,
      lt_of_le_of_lt hw.2.2 (by linarith)⟩
  have hQS : Q ⊆ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} := subset_closure.trans hclQ
  -- `J` minus the harmonic barrier is subharmonic on the rectangle.
  have hsub : SubharmonicOn (fun w => J w - ε * Real.exp (-w.re) * Real.sin w.im) Q :=
    (hJ.mono hQS).sub_harmonicOnNhd ((harmonicOnNhd_barrier ε).mono (subset_univ Q))
  have hQopen : IsOpen Q := IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  have hQbdd : Bornology.IsBounded Q :=
    (Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)
  have hcont : ContinuousOn (fun w => J w - ε * Real.exp (-w.re) * Real.sin w.im) (closure Q) :=
    (hJ.1.mono hclQ).sub (by fun_prop : Continuous
      fun w : ℂ => ε * Real.exp (-w.re) * Real.sin w.im).continuousOn
  -- Frontier bound: each of the four edges is controlled.
  have hfr : ∀ z ∈ frontier Q, J z - ε * Real.exp (-z.re) * Real.sin z.im ≤ ε + 2 * η := by
    intro z hz
    have hzS := hclQ (frontier_subset_closure hz)
    obtain ⟨hzre, hzim0, hzimπ⟩ := hzS
    have hsin0 : 0 ≤ Real.sin z.im := Real.sin_nonneg_of_nonneg_of_le_pi hzim0.le hzimπ.le
    have hBnn : 0 ≤ ε * Real.exp (-z.re) * Real.sin z.im :=
      mul_nonneg (mul_nonneg hεpos.le (Real.exp_pos _).le) hsin0
    have hedge4 : z.re = -R ∨ z.re = -δ' ∨ z.im = η ∨ z.im = π - η := by
      have h := hz
      rw [hQ, Complex.frontier_reProdIm, frontier_Ioo hRδ', frontier_Ioo hηπ] at h
      rcases h with h | h <;> rw [Complex.mem_reProdIm] at h
      · rcases h.2 with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
      · rcases h.1 with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    rcases hedge4 with hcase | hcase | hcase | hcase
    · -- Far-left edge: the barrier dominates the wedge bound via Jordan's inequality.
      have hJmin : J z ≤ 2 * min z.im (π - z.im) := by
        rcases le_total z.im (π - z.im) with hm | hm
        · rw [min_eq_left hm]; exact h0 z ⟨hzre, hzim0, hzimπ⟩
        · rw [min_eq_right hm]; exact hπ z ⟨hzre, hzim0, hzimπ⟩
      have hjordan := two_mul_min_le_pi_mul_sin hzim0.le hzimπ.le
      have hdom : π * Real.sin z.im ≤ ε * Real.exp (-z.re) * Real.sin z.im := by
        rw [hcase, neg_neg]
        exact mul_le_mul_of_nonneg_right hRε hsin0
      linarith
    · -- Right edge: the near-edge smallness hypothesis applies.
      have hJz : J z ≤ ε := hedge z ⟨hzre, hzim0, hzimπ⟩ hcase.ge
      linarith
    · -- Bottom edge: the wedge bound `J ≤ 2·im = 2η`.
      have hJz := h0 z ⟨hzre, hzim0, hzimπ⟩
      rw [hcase] at hJz
      linarith
    · -- Top edge: the wedge bound `J ≤ 2·(π − im) = 2η`.
      have hJz := hπ z ⟨hzre, hzim0, hzimπ⟩
      rw [hcase] at hJz
      linarith
  intro w hw
  have := hsub.le_of_frontier_le hQopen hQbdd hcont hfr w hw
  linarith

/-- **Phragmén–Lindelöf on the half-strip.** A subharmonic function on
`{re < 0, 0 < im < π}` that satisfies the wedge bounds `J ≤ 2·im` and `J ≤ 2·(π − im)` and is
asymptotically nonpositive at the right edge is nonpositive throughout. At a fixed interior point
run the maximum principle against the barrier `ε·e^{−re}·sin im` on a large rectangle, then send
the aperture `η`, the edge margin, and `ε` to zero. -/
theorem subharmonicOn_halfStrip_nonpos {J : ℂ → ℝ}
    (hJ : SubharmonicOn J {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π})
    (h0 : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, J w ≤ 2 * w.im)
    (hπ : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, J w ≤ 2 * (π - w.im))
    (hright : ∀ ε > 0, ∃ δ > 0, ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π},
      -δ < w.re → J w ≤ ε) :
    ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, J w ≤ 0 := by
  intro w₀ hw₀
  obtain ⟨hw₀re, hw₀im0, hw₀imπ⟩ := hw₀
  have hπ0 : (0 : ℝ) < π := Real.pi_pos
  -- It suffices to dominate `J w₀` by every positive constant.
  have key : ∀ c : ℝ, 0 < c → J w₀ ≤ c := by
    intro c hc
    have hE : 0 < 1 + Real.exp (-w₀.re) := by positivity
    set ε : ℝ := c / (2 * (1 + Real.exp (-w₀.re))) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    obtain ⟨δ, hδpos, hδ⟩ := hright ε hεpos
    set δ' : ℝ := min (δ / 2) (-w₀.re / 2) with hδ'def
    have hδ'pos : 0 < δ' := lt_min (by linarith) (by linarith)
    have hδ'δ : δ' < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ'w₀ : w₀.re < -δ' := by
      have h1 : δ' ≤ -w₀.re / 2 := min_le_right _ _
      linarith
    set η : ℝ := min (c / 8) (min (w₀.im / 2) ((π - w₀.im) / 2)) with hηdef
    have hηpos : 0 < η := lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hηc : η ≤ c / 8 := min_le_left _ _
    have hηim : η ≤ w₀.im / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hηim' : η ≤ (π - w₀.im) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hηπ : η < π - η := by linarith
    set R : ℝ := max (Real.log (π / ε) + 1) (-w₀.re + 1) with hRdef
    have hRw₀ : -R < w₀.re := by
      have := le_max_right (Real.log (π / ε) + 1) (-w₀.re + 1)
      linarith
    have hRδ' : -R < -δ' := lt_trans hRw₀ hδ'w₀
    -- The barrier dominates the wedge bound on the far-left edge.
    have hRε : π ≤ ε * Real.exp R := by
      have h1 : Real.log (π / ε) + 1 ≤ R := le_max_left _ _
      have h2 : Real.exp (Real.log (π / ε)) ≤ Real.exp R := Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_log (by positivity)] at h2
      calc π = ε * (π / ε) := by field_simp
        _ ≤ ε * Real.exp R := mul_le_mul_of_nonneg_left h2 hεpos.le
    -- The right-edge control at the level `-δ'`.
    have hedge : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, -δ' ≤ w.re → J w ≤ ε :=
      fun w hw hre => hδ w hw (lt_of_lt_of_le (by linarith) hre)
    -- The fixed point lies inside the rectangle.
    have hw₀Q : w₀ ∈ Ioo (-R) (-δ') ×ℂ Ioo η (π - η) := by
      rw [Complex.mem_reProdIm, mem_Ioo, mem_Ioo]
      exact ⟨⟨hRw₀, hδ'w₀⟩, by linarith, by linarith⟩
    have hbound := halfStrip_rect_bound hJ h0 hπ hedge hεpos hδ'pos hηpos hηπ hRδ' hRε w₀ hw₀Q
    -- Collect the barrier value and the parameter bookkeeping.
    have hsin1 : Real.sin w₀.im ≤ 1 := Real.sin_le_one _
    have hsin0 : 0 ≤ Real.sin w₀.im := Real.sin_nonneg_of_nonneg_of_le_pi hw₀im0.le hw₀imπ.le
    have hexp0 : 0 < Real.exp (-w₀.re) := Real.exp_pos _
    have hB : ε * Real.exp (-w₀.re) * Real.sin w₀.im ≤ ε * Real.exp (-w₀.re) := by
      have h := mul_le_mul_of_nonneg_left hsin1 (mul_nonneg hεpos.le hexp0.le)
      simpa using h
    have hεE : ε + ε * Real.exp (-w₀.re) = c / 2 := by
      rw [hεdef]
      field_simp
    linarith
  by_contra hcon
  have hpos : 0 < J w₀ := not_le.mp hcon
  have := key (J w₀ / 2) (by linarith)
  linarith

end RiemannDynamics

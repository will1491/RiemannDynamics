/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.H1ZeroDensity
import RiemannDynamics.QC.Regularity.RingModulus

/-!
# The modulus–energy lower bound over bounded admissible densities

For a harmonic potential `u` on a bounded open set `U` and boundary sets `E`, `F`, the Dirichlet
energy of `u` is a lower bound for the density energy `∫ ρ²` over every **bounded** density `ρ`
admissible for the connecting family `connectingCurveFamily E F U`, hence for the infimum of those
energies.

The single-density estimate `dirichletEnergy u U ≤ ∫ ρ²`, valid for each bounded admissible `ρ`, is
the capstone `dirichletEnergy_le_lintegral_sq_of_bounded_admissible`: its competitor
`w z = min (rhoDistance ρ E U z).toReal 1` on `U` (and `u` off `U`) shares the potential's boundary
values, so the boundary-vanishing Hardy Dirichlet principle bounds `dirichletEnergy u U` by the
competitor energy, which `dirichletEnergy_min_rhoDistance_le` bounds by `∫ ρ²`. Passing from the
per-density estimate to the infimum is `le_iInf₂`; the boundary/Hardy regularity of each competitor
difference `w − u` is carried as the hypothesis `hcomp`.

## Main statements

* `dirichletEnergy_le_curveModulus_connecting_of_bounded` — `dirichletEnergy u U` is at most the
  infimum of `∫ ρ²` over bounded densities admissible for `connectingCurveFamily E F U`.
-/

open MeasureTheory Filter Metric Topology
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

open Classical in
/-- **The modulus–energy lower bound over bounded admissible densities.** For a harmonic potential
`u` on a bounded open set `U`, the Dirichlet energy of `u` is at most `∫ ρ²` for every measurable
density `ρ` admissible for the connecting family `connectingCurveFamily E F U` and bounded by some
`M : ℝ≥0`, hence at most the infimum of those energies. Each single-density estimate is the capstone
`dirichletEnergy_le_lintegral_sq_of_bounded_admissible`, whose four competitor-regularity facts
(continuity, local Lipschitz constants on compacts, finite squared-gradient integral, finite Hardy
integral of the competitor difference `w − u`, where `w z = min (rhoDistance ρ E U z).toReal 1` on
`U`) are supplied for every bounded admissible `ρ` through the hypothesis `hcomp`; `le_iInf₂` then
lifts the per-density bound to the infimum. -/
theorem dirichletEnergy_le_curveModulus_connecting_of_bounded {u : ℂ → ℝ} {E F U : Set ℂ}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcomp : ∀ (ρ : ℂ → ℝ≥0∞) (M : ℝ≥0),
        IsAdmissibleDensity ρ (connectingCurveFamily E F U) →
        (∀ x, ρ x ≤ (M : ℝ≥0∞)) →
        (Continuous (fun z =>
            (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z)) ∧
        (∀ K ⊆ U, IsCompact K → ∃ L : ℝ≥0, LipschitzOnWith L (fun z =>
            (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) K) ∧
        (∫⁻ z in U, (‖fderiv ℝ (fun z =>
            (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) z‖₊ : ℝ≥0∞) ^ 2
            ≠ ⊤) ∧
        (∫⁻ z in U, ENNReal.ofReal
            (((if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) ^ 2
              / (Metric.infDist z Uᶜ) ^ 2) ≠ ⊤)) :
    dirichletEnergy u U
      ≤ ⨅ ρ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ (connectingCurveFamily E F U) ∧
          ∃ M : ℝ≥0, ∀ x, ρ x ≤ (M : ℝ≥0∞)}, ∫⁻ z, (ρ z) ^ 2 := by
  refine le_iInf₂ ?_
  rintro ρ ⟨hadm, M, hbdd⟩
  obtain ⟨hcont, hloc, hW12, hHardy⟩ := hcomp ρ M hadm hbdd
  exact dirichletEnergy_le_lintegral_sq_of_bounded_admissible hUopen hUbdd hu hadm.1 hbdd
    hcont hloc hW12 hHardy

open Classical in
/-- **The modulus–energy lower bound over bounded admissible densities, without the competitor
hypothesis.** For a harmonic potential `u` on a bounded open set `U`, continuous up to the closure,
equal to `0` on the boundary continuum `E` and `1` on `F`, the Dirichlet energy of `u` is at most
`∫ ρ²` for every measurable density `ρ` admissible for `connectingCurveFamily E F U` and bounded by
some `M : ℝ≥0`, hence at most the infimum of those energies. The four competitor-regularity facts
of `dirichletEnergy_le_lintegral_sq_of_bounded_admissible` are discharged for each bounded
admissible `ρ`: the truncated `ρ`-length distance `g z = min (rhoDistance ρ E U z).toReal 1` is
`M`-Lipschitz on compact subsets of `U` (segment additive bound), agrees with `u`'s values across
the frontier (via segment-accessibility `haccess` together with `hE`, `hF`, `hfront`),
and has gradient bounded a.e. by `ρ ≤ M` (bounded eikonal); finiteness of the `ρ`-length distance on
`U` (the reachability condition `hrhoFin`, needed for the far-boundary matching) and the Hardy
finiteness of the competitor difference `w − u` (which is `u`-intrinsic, `hHardyU`) are supplied. -/
theorem dirichletEnergy_le_curveModulus_connecting_bounded {u : ℂ → ℝ} {E F U : Set ℂ}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hucont : ContinuousOn u (closure U))
    (hE : ∀ z ∈ E, u z = 0) (hF : ∀ z ∈ F, u z = 1) (hfront : frontier U ⊆ E ∪ F)
    (haccess : ∀ z₀ ∈ frontier U, ∀ᶠ z in nhdsWithin z₀ U, openSegment ℝ z₀ z ⊆ U)
    (hrhoFin : ∀ (ρ : ℂ → ℝ≥0∞), IsAdmissibleDensity ρ (connectingCurveFamily E F U) →
        (∀ z ∈ U, rhoDistance ρ E U z ≠ ⊤))
    (hDu : dirichletEnergy u U ≠ ⊤)
    (hHardyU : ∀ (ρ : ℂ → ℝ≥0∞), IsAdmissibleDensity ρ (connectingCurveFamily E F U) →
        (∀ M : ℝ≥0, (∀ x, ρ x ≤ (M : ℝ≥0∞)) →
          ∫⁻ z in U, ENNReal.ofReal
            (((if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) ^ 2
              / (Metric.infDist z Uᶜ) ^ 2) ≠ ⊤)) :
    dirichletEnergy u U
      ≤ ⨅ ρ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ (connectingCurveFamily E F U) ∧
          ∃ M : ℝ≥0, ∀ x, ρ x ≤ (M : ℝ≥0∞)}, ∫⁻ z, (ρ z) ^ 2 := by
  classical
  refine le_iInf₂ ?_
  rintro ρ ⟨hadm, M, hbdd⟩
  have hρmeas : Measurable ρ := hadm.1
  -- Abbreviations for the truncated `ρ`-length distance `g` and the competitor difference `w`.
  set f : ℂ → ℝ := fun z => (rhoDistance ρ E U z).toReal with hfdef
  set g : ℂ → ℝ := fun z => min (f z) 1 with hgdef
  set w : ℂ → ℝ := fun z => (if z ∈ U then g z else u z) - u z with hwdef
  -- `g ∈ [0, 1]` (truncation of the nonnegative `f`).
  have hg01 : ∀ z, 0 ≤ g z ∧ g z ≤ 1 := by
    intro z; refine ⟨le_min ENNReal.toReal_nonneg (by norm_num), min_le_right _ _⟩
  -- **Two-sided local `M`-Lipschitz bound for `f` on balls inside `U`.**
  have hf_ball : ∀ z ∈ U, ∃ r > 0, Metric.ball z r ⊆ U ∧
      ∀ w ∈ Metric.ball z r, |f w - f z| ≤ (M : ℝ) * ‖w - z‖ := by
    intro z hz
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hUopen z hz
    refine ⟨r, hr, hrsub, fun w hw => ?_⟩
    by_cases hztop : rhoDistance ρ E U z = ⊤
    · -- infinite region: `f` is locally constant `0`.
      have hwU : w ∈ U := hrsub hw
      have hseg : openSegment ℝ w z ⊆ U :=
        ((convex_ball z r).openSegment_subset hw (Metric.mem_ball_self hr)).trans hrsub
      have hle := rhoDistance_le_add_mul_of_bounded (E := E) hbdd hwU hseg
      rw [hztop] at hle
      have hwtop : rhoDistance ρ E U w = ⊤ := by
        by_contra hwfin
        exact (ENNReal.add_ne_top.mpr
          ⟨hwfin, ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩) (top_le_iff.mp hle)
      rw [hfdef]; simp only [hwtop, hztop, ENNReal.toReal_top, sub_self, abs_zero]
      positivity
    · -- finite region: two-sided segment bound.
      have hwU : w ∈ U := hrsub hw
      have hseg1 : openSegment ℝ z w ⊆ U :=
        ((convex_ball z r).openSegment_subset (Metric.mem_ball_self hr) hw).trans hrsub
      have hseg2 : openSegment ℝ w z ⊆ U :=
        ((convex_ball z r).openSegment_subset hw (Metric.mem_ball_self hr)).trans hrsub
      have hle1 := rhoDistance_le_add_mul_of_bounded (E := E) hbdd hz hseg1
      have hle2 := rhoDistance_le_add_mul_of_bounded (E := E) hbdd hwU hseg2
      have hmt1 : (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
      have hmt2 : (M : ℝ≥0∞) * (‖z - w‖₊ : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
      have hwtop : rhoDistance ρ E U w ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hztop, hmt1⟩) hle1
      have hr1 : f w ≤ f z + (M : ℝ) * ‖w - z‖ := by
        have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hztop, hmt1⟩) hle1
        rw [ENNReal.toReal_add hztop hmt1, ENNReal.toReal_mul] at this
        simpa [hfdef, ENNReal.coe_toReal] using this
      have hr2 : f z ≤ f w + (M : ℝ) * ‖z - w‖ := by
        have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hwtop, hmt2⟩) hle2
        rw [ENNReal.toReal_add hwtop hmt2, ENNReal.toReal_mul] at this
        simpa [hfdef, ENNReal.coe_toReal] using this
      rw [abs_sub_le_iff]
      refine ⟨by linarith, ?_⟩
      rw [show ‖z - w‖ = ‖w - z‖ from norm_sub_rev z w] at hr2; linarith
  -- `f` is locally Lipschitz on `U`, hence so is `g = min f 1`.
  have hf_loc : LocallyLipschitzOn U f := by
    intro z hz
    obtain ⟨r, hr, hrsub, hlip⟩ := hf_ball z hz
    refine ⟨M, Metric.ball z r, ?_, ?_⟩
    · exact nhdsWithin_le_nhds (Metric.ball_mem_nhds z hr)
    · rw [lipschitzOnWith_iff_dist_le_mul]
      intro a ha b hb
      rw [Real.dist_eq]
      -- `|f a - f b| ≤ |f a - f z| + |f z - f b| ≤ M(dist a z + dist z b)` is too weak; use direct
      have hab : |f a - f b| ≤ (M : ℝ) * ‖a - b‖ := by
        have hseg : openSegment ℝ b a ⊆ U :=
          ((convex_ball z r).openSegment_subset hb ha).trans hrsub
        have hseg' : openSegment ℝ a b ⊆ U :=
          ((convex_ball z r).openSegment_subset ha hb).trans hrsub
        have hle1 := rhoDistance_le_add_mul_of_bounded (E := E) hbdd (hrsub hb) hseg
        have hle2 := rhoDistance_le_add_mul_of_bounded (E := E) hbdd (hrsub ha) hseg'
        -- `hle1 : ρDist a ≤ ρDist b + M‖a-b‖`, `hle2 : ρDist b ≤ ρDist a + M‖b-a‖`.
        by_cases hbtop : rhoDistance ρ E U b = ⊤
        · -- then `a` is also infinite (finite ⇒ infinite via segment), so both `f` are `0`.
          have hatop : rhoDistance ρ E U a = ⊤ := by
            rw [hbtop] at hle2
            by_contra haf
            exact (ENNReal.add_ne_top.mpr ⟨haf,
              ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩) (top_le_iff.mp hle2)
          rw [hfdef]; simp only [hatop, hbtop, ENNReal.toReal_top, sub_self, abs_zero]; positivity
        · have hmt1 : (M : ℝ≥0∞) * (‖a - b‖₊ : ℝ≥0∞) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
          have hmt2 : (M : ℝ≥0∞) * (‖b - a‖₊ : ℝ≥0∞) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
          have hatop : rhoDistance ρ E U a ≠ ⊤ :=
            ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hbtop, hmt1⟩) hle1
          have hu1 : f a ≤ f b + (M : ℝ) * ‖a - b‖ := by
            have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hbtop, hmt1⟩) hle1
            rw [ENNReal.toReal_add hbtop hmt1, ENNReal.toReal_mul] at this
            simpa [hfdef, ENNReal.coe_toReal] using this
          have hu2 : f b ≤ f a + (M : ℝ) * ‖b - a‖ := by
            have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hatop, hmt2⟩) hle2
            rw [ENNReal.toReal_add hatop hmt2, ENNReal.toReal_mul] at this
            simpa [hfdef, ENNReal.coe_toReal] using this
          rw [abs_sub_le_iff]
          refine ⟨by linarith, ?_⟩
          rw [show ‖b - a‖ = ‖a - b‖ from norm_sub_rev b a] at hu2; linarith
      calc |f a - f b| ≤ (M : ℝ) * ‖a - b‖ := hab
        _ = (M : ℝ) * dist a b := by rw [dist_eq_norm]
  have hg_loc : LocallyLipschitzOn U g := by
    intro z hz
    obtain ⟨K, t, ht, hlip⟩ := hf_loc hz
    exact ⟨K, t, ht, by
      simpa [hgdef] using! (LipschitzWith.id.min_const (1 : ℝ)).comp_lipschitzOnWith hlip⟩
  -- `u` is `C¹` on `U`, hence locally Lipschitz on `U`.
  have hu_contDiff : ∀ z ∈ U, ContDiffAt ℝ 1 u z := fun z hz => (hu z hz).1.of_le (by norm_num)
  have hu_loc : LocallyLipschitzOn U u := by
    intro z hz
    obtain ⟨K, t, ht, hlip⟩ := (hu_contDiff z hz).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hlip⟩
  -- The competitor difference agrees with `g - u` on `U`.
  have hw_eq : ∀ z ∈ U, w z = g z - u z := fun z hz => by simp only [hwdef, if_pos hz]
  -- **FACT (2): local Lipschitz constants on compact subsets of `U`.**
  have hfact2 : ∀ K ⊆ U, IsCompact K → ∃ L : ℝ≥0, LipschitzOnWith L w K := by
    intro K hKU hKcpt
    have hgu_loc : LocallyLipschitzOn U (fun z => g z - u z) := hg_loc.sub hu_loc
    obtain ⟨L, hL⟩ := (hgu_loc.mono hKU).exists_lipschitzOnWith_of_compact hKcpt
    refine ⟨L, ?_⟩
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    rw [dist_eq_norm, hw_eq a (hKU ha), hw_eq b (hKU hb), ← dist_eq_norm]
    exact (lipschitzOnWith_iff_dist_le_mul.mp hL) a ha b hb
  -- **FACT (1): global continuity of the competitor difference `w`.**
  -- The a.e. gradient bound `‖∇g‖ ≤ ρ`, from the bounded eikonal and the truncation contraction.
  have hfact3grad : ∀ᵐ z ∂(volume.restrict U), (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ≤ ρ z := by
    have heik := rhoDistance_upperGradient_of_bounded (E := E) hUopen hρmeas hbdd
    filter_upwards [heik, ae_restrict_mem hUopen.measurableSet] with z hz hzU
    -- pointwise: `‖∇g‖ ≤ ‖∇f‖` via the `min`-with-constant contraction (as in the M0 competitor).
    have hcont : ContinuousAt f z := by
      obtain ⟨r, hr, _, hball⟩ := hf_ball z hzU
      rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨min r (ε / (M + 1)), by positivity, fun v hvd => ?_⟩
      have hvr : v ∈ Metric.ball z r :=
        Metric.mem_ball.mpr (lt_of_lt_of_le hvd (min_le_left _ _))
      have hvd2 : dist v z < ε / (M + 1) := lt_of_lt_of_le hvd (min_le_right _ _)
      rw [Real.dist_eq]
      calc |f v - f z| ≤ (M : ℝ) * ‖v - z‖ := hball v hvr
        _ = (M : ℝ) * dist v z := by rw [dist_eq_norm]
        _ ≤ (M : ℝ) * (ε / (M + 1)) := by
            exact mul_le_mul_of_nonneg_left hvd2.le M.coe_nonneg
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, M.coe_nonneg]
    have hkey : ‖fderiv ℝ g z‖ ≤ ‖fderiv ℝ f z‖ := by
      rcases lt_trichotomy (f z) 1 with hlt | heq | hgt
      · have hev : g =ᶠ[nhds z] f := by
          filter_upwards [hcont (Iio_mem_nhds hlt)] with v hv using min_eq_left hv.le
        rw [hgdef]; rw [show (fun z => min (f z) 1) = g from rfl, hev.fderiv_eq]
      · have hmax : IsMaxOn g Set.univ z := by
          intro v _; simp only [hgdef]
          calc min (f v) 1 ≤ 1 := min_le_right _ _
            _ = min (f z) 1 := by rw [heq, min_self]
        rw [(hmax.isLocalMax Filter.univ_mem).fderiv_eq_zero, norm_zero]; exact norm_nonneg _
      · have hev : g =ᶠ[nhds z] (fun _ => (1 : ℝ)) := by
          filter_upwards [hcont (Ioi_mem_nhds hgt)] with v hv using min_eq_right hv.le
        rw [show (fun z => min (f z) 1) = g from rfl] at *
        rw [hev.fderiv_eq, fderiv_const_apply, norm_zero]; exact norm_nonneg _
    calc (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ≤ (‖fderiv ℝ f z‖₊ : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hkey
      _ ≤ ρ z := hz
  -- `u` is differentiable at each point of `U`.
  have hu_diff : ∀ z ∈ U, DifferentiableAt ℝ u z := fun z hz => (hu_contDiff z hz).differentiableAt
    (by norm_num)
  -- The competitor gradient splits: `‖∇w‖ ≤ ‖∇g‖ + ‖∇u‖` on `U`.
  have hw_grad_le : ∀ z ∈ U, ‖fderiv ℝ w z‖ ≤ ‖fderiv ℝ g z‖ + ‖fderiv ℝ u z‖ := by
    intro z hz
    have hwev : w =ᶠ[nhds z] (fun z => g z - u z) := by
      filter_upwards [hUopen.mem_nhds hz] with v hv using hw_eq v hv
    rw [hwev.fderiv_eq]
    by_cases hgd : DifferentiableAt ℝ g z
    · rw [fderiv_fun_sub hgd (hu_diff z hz)]
      exact norm_sub_le _ _
    · have hgud : ¬ DifferentiableAt ℝ (fun z => g z - u z) z := by
        intro hgu
        have hga : DifferentiableAt ℝ (fun z => (g z - u z) + u z) z := hgu.add (hu_diff z hz)
        exact hgd (by simpa only [sub_add_cancel] using hga)
      rw [fderiv_zero_of_not_differentiableAt hgud, norm_zero]
      positivity
  -- **FACT (3): the competitor squared-gradient integral is finite.**
  have hsq : ∀ a b : ℝ≥0∞, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    intro a b
    rcases eq_or_ne a ⊤ with rfl | ha
    · simp
    rcases eq_or_ne b ⊤ with rfl | hb
    · simp
    lift a to ℝ≥0 using ha
    lift b to ℝ≥0 using hb
    have key : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
      rw [add_sq, two_mul (a ^ 2), two_mul (b ^ 2)]
      calc a ^ 2 + 2 * a * b + b ^ 2 ≤ a ^ 2 + (a ^ 2 + b ^ 2) + b ^ 2 := by
            gcongr; exact two_mul_le_add_sq a b
        _ = a ^ 2 + a ^ 2 + (b ^ 2 + b ^ 2) := by ring
    calc ((a : ℝ≥0∞) + b) ^ 2 = ((a + b : ℝ≥0) : ℝ≥0∞) ^ 2 := by push_cast; ring
      _ ≤ (((2 * a ^ 2 + 2 * b ^ 2 : ℝ≥0)) : ℝ≥0∞) := by exact_mod_cast key
      _ = 2 * (a : ℝ≥0∞) ^ 2 + 2 * (b : ℝ≥0∞) ^ 2 := by push_cast; ring
  have hvolU : volume U ≠ ⊤ := hUbdd.measure_lt_top.ne
  have hfact3 : ∫⁻ z in U, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := by
    have hbound : ∫⁻ z in U, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((M : ℝ≥0∞) ^ 2 * volume U) + 2 * dirichletEnergy u U := by
      calc ∫⁻ z in U, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2
          ≤ ∫⁻ z in U, (2 * (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2) := by
            refine setLIntegral_mono_ae' hUopen.measurableSet (Filter.Eventually.of_forall ?_)
            intro z hz
            have h1 : (‖fderiv ℝ w z‖₊ : ℝ≥0∞)
                ≤ (‖fderiv ℝ g z‖₊ : ℝ≥0∞) + (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
              rw [← ENNReal.coe_add]
              exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hw_grad_le z hz)
            calc (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2
                ≤ ((‖fderiv ℝ g z‖₊ : ℝ≥0∞) + (‖fderiv ℝ u z‖₊ : ℝ≥0∞)) ^ 2 := by gcongr
              _ ≤ 2 * (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 := hsq _ _
        _ = 2 * (∫⁻ z in U, (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2)
              + 2 * ∫⁻ z in U, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 := by
            rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
              lintegral_const_mul _ (by fun_prop)]
        _ ≤ 2 * ((M : ℝ≥0∞) ^ 2 * volume U) + 2 * dirichletEnergy u U := by
            rw [dirichletEnergy]
            gcongr
            calc ∫⁻ z in U, (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2
                ≤ ∫⁻ _ in U, (M : ℝ≥0∞) ^ 2 := by
                  refine lintegral_mono_ae ?_
                  filter_upwards [hfact3grad] with z hz
                  calc (‖fderiv ℝ g z‖₊ : ℝ≥0∞) ^ 2 ≤ (ρ z) ^ 2 := by gcongr
                    _ ≤ (M : ℝ≥0∞) ^ 2 := by gcongr; exact hbdd z
              _ = (M : ℝ≥0∞) ^ 2 * volume U := by rw [setLIntegral_const]
    refine ne_of_lt (lt_of_le_of_lt hbound ?_)
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by simp)
      (ENNReal.mul_lt_top (by simp) hvolU.lt_top),
      ENNReal.mul_lt_top (by simp) hDu.lt_top⟩
  -- **Segment bound to a boundary point of `E`.** For `z₀ ∈ E` with the open segment to `z` in `U`,
  -- the segment is a connecting curve from `E` to `z`, so `rhoDistance z ≤ M‖z − z₀‖`.
  have hseg_bound : ∀ (z₀ z : ℂ), z₀ ∈ E → openSegment ℝ z₀ z ⊆ U →
      rhoDistance ρ E U z ≤ (M : ℝ≥0∞) * (‖z - z₀‖₊ : ℝ≥0∞) := by
    intro z₀ z hz₀ hsegU
    set σ : ℝ → ℂ := fun t => (1 - t) • z₀ + t • z with hσ
    have hσcont : Continuous σ := by
      have : σ = fun θ : ℝ => ((1 - θ : ℝ) : ℂ) * z₀ + (θ : ℂ) * z := by
        funext θ; rw [hσ]; simp only; rw [Complex.real_smul, Complex.real_smul]
      rw [this]; fun_prop
    have hσlip : LipschitzWith ‖z - z₀‖₊ σ := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [hσ]; simp only
      rw [dist_eq_norm, Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul,
        show ((1 - x : ℝ) : ℂ) * z₀ + (x : ℂ) * z - (((1 - y : ℝ) : ℂ) * z₀ + (y : ℂ) * z)
          = ((x - y : ℝ) : ℂ) * (z - z₀) by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, coe_nnnorm, Real.dist_eq, mul_comm]
    have hσac : AbsolutelyContinuousOnInterval σ 0 1 :=
      (hσlip.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
    have hσ0 : σ 0 = z₀ := by rw [hσ]; simp
    have hσ1 : σ 1 = z := by rw [hσ]; simp
    have hσU : ∀ t ∈ Set.Ioo (0 : ℝ) 1, σ t ∈ U := by
      intro t ht
      have heq : openSegment ℝ z₀ z = (fun θ : ℝ => (1 - θ) • z₀ + θ • z) '' Set.Ioo 0 1 :=
        openSegment_eq_image ℝ z₀ z
      exact hsegU (by rw [heq]; exact ⟨t, ht, rfl⟩)
    have hmem : σ ∈ connectingCurveFamily E {z} U :=
      ⟨hσcont, hσac, by rw [hσ0]; exact hz₀, by rw [Set.mem_singleton_iff, hσ1], hσU⟩
    calc rhoDistance ρ E U z ≤ arcLengthLineIntegral ρ σ := rhoDistance_le_arcLength ρ E U z hmem
      _ ≤ (M : ℝ≥0∞) * (‖z - z₀‖₊ : ℝ≥0∞) := arcLengthLineIntegral_segment_le hbdd z₀ z
  -- **FACT (1): the competitor difference `w` is continuous.**
  have hfact1 : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro z₀
    -- `w` is continuous within `Uᶜ` (constant `0` there, or `𝓝[Uᶜ] z₀ = ⊥` when `z₀ ∈ U`).
    have hWUc : ContinuousWithinAt w Uᶜ z₀ := by
      by_cases hz₀U : z₀ ∈ U
      · have hbot : nhdsWithin z₀ Uᶜ = ⊥ :=
          notMem_closure_iff_nhdsWithin_eq_bot.mp (by rwa [hUopen.isClosed_compl.closure_eq,
            Set.notMem_compl_iff])
        rw [ContinuousWithinAt, hbot]; exact tendsto_bot
      · have hval : ∀ v ∈ Uᶜ, w v = 0 := fun v hv => by simp only [hwdef, if_neg hv, sub_self]
        exact (continuousWithinAt_const (b := (0 : ℝ))).congr hval (hval z₀ hz₀U)
    -- `w` is continuous within `U`.
    have hWU : ContinuousWithinAt w U z₀ := by
      by_cases hz₀U : z₀ ∈ U
      · -- interior: `w =ᶠ g − u` near `z₀`, both continuous.
        have hgcont : ContinuousAt g z₀ := hg_loc.continuousOn.continuousAt (hUopen.mem_nhds hz₀U)
        have hucontat : ContinuousAt u z₀ := hu_loc.continuousOn.continuousAt (hUopen.mem_nhds hz₀U)
        have hwev : w =ᶠ[nhds z₀] (fun z => g z - u z) := by
          filter_upwards [hUopen.mem_nhds hz₀U] with v hv using hw_eq v hv
        exact ((hgcont.sub hucontat).congr hwev.symm).continuousWithinAt
      · by_cases hz₀cl : z₀ ∈ closure U
        · -- `z₀ ∈ frontier U`: boundary matching.
          have hz₀fr : z₀ ∈ frontier U := by
            rw [frontier_eq_closure_inter_closure]
            exact ⟨hz₀cl, subset_closure (by simpa using hz₀U)⟩
          have hw0 : w z₀ = 0 := by simp only [hwdef, if_neg hz₀U, sub_self]
          have hutend : Tendsto u (nhdsWithin z₀ U) (nhds (u z₀)) :=
            (hucont.continuousWithinAt hz₀cl).tendsto.mono_left (nhdsWithin_mono z₀ subset_closure)
          -- distance to `z₀` tends to `0` along `𝓝[U] z₀`.
          have hdist0 : Tendsto (fun z => (M : ℝ) * ‖z - z₀‖) (nhdsWithin z₀ U) (nhds 0) := by
            have hc : Continuous (fun z : ℂ => (M : ℝ) * ‖z - z₀‖) := by fun_prop
            have := (hc.tendsto z₀).mono_left (nhdsWithin_le_nhds (s := U))
            simpa using this
          -- `g z → u z₀` along `𝓝[U] z₀`, by the `E`/`F` boundary values.
          have hgtend : Tendsto g (nhdsWithin z₀ U) (nhds (u z₀)) := by
            rcases hfront hz₀fr with hzE | hzF
            · -- on `E`: `u z₀ = 0`; `0 ≤ f z ≤ M‖z − z₀‖ → 0`, so `g = min f 1 → 0`.
              rw [hE z₀ hzE]
              have hfsq : ∀ᶠ z in nhdsWithin z₀ U, 0 ≤ f z ∧ f z ≤ (M : ℝ) * ‖z - z₀‖ := by
                filter_upwards [haccess z₀ hz₀fr] with z hzseg
                refine ⟨ENNReal.toReal_nonneg, ?_⟩
                have hle := hseg_bound z₀ z hzE hzseg
                have hfin : (M : ℝ≥0∞) * (‖z - z₀‖₊ : ℝ≥0∞) ≠ ⊤ :=
                  ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
                have h := ENNReal.toReal_mono hfin hle
                rw [ENNReal.toReal_mul] at h
                simpa only [hfdef, ENNReal.coe_toReal, coe_nnnorm] using h
              have hftend : Tendsto f (nhdsWithin z₀ U) (nhds 0) :=
                squeeze_zero' (hfsq.mono fun z h => h.1) (hfsq.mono fun z h => h.2) hdist0
              have := hftend.min (tendsto_const_nhds (x := (1 : ℝ)))
              simpa only [hgdef, min_eq_left (zero_le_one)] using this
            · -- on `F`: `u z₀ = 1`; `1 − M‖z − z₀‖ ≤ f z`, so `g = min f 1 → 1`.
              rw [hF z₀ hzF]
              have hfge : ∀ᶠ z in nhdsWithin z₀ U, 1 - (M : ℝ) * ‖z - z₀‖ ≤ f z := by
                filter_upwards [haccess z₀ hz₀fr, self_mem_nhdsWithin] with z hzseg hzU
                have hsegU : openSegment ℝ z z₀ ⊆ U := by
                  rwa [openSegment_symm] at hzseg
                have hle : rhoDistance ρ E U z₀
                    ≤ rhoDistance ρ E U z + (M : ℝ≥0∞) * (‖z₀ - z‖₊ : ℝ≥0∞) :=
                  rhoDistance_le_add_mul_of_bounded (E := E) hbdd hzU hsegU
                have h1 : (1 : ℝ≥0∞) ≤ rhoDistance ρ E U z₀ :=
                  one_le_rhoDistance_of_mem_of_admissible hadm hzF
                have hztop : rhoDistance ρ E U z ≠ ⊤ := hrhoFin ρ hadm z hzU
                have hfin : (M : ℝ≥0∞) * (‖z₀ - z‖₊ : ℝ≥0∞) ≠ ⊤ :=
                  ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
                have hle' : (1 : ℝ) ≤ f z + (M : ℝ) * ‖z₀ - z‖ := by
                  have h2 := le_trans h1 hle
                  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hztop, hfin⟩) h2
                  rw [ENNReal.toReal_add hztop hfin, ENNReal.toReal_mul, ENNReal.toReal_one] at h3
                  simpa only [hfdef, ENNReal.coe_toReal, coe_nnnorm] using h3
                rw [show ‖z₀ - z‖ = ‖z - z₀‖ from norm_sub_rev z₀ z] at hle'; linarith
              have hone : Tendsto (fun z => 1 - (M : ℝ) * ‖z - z₀‖) (nhdsWithin z₀ U)
                  (nhds 1) := by
                have := (tendsto_const_nhds (x := (1 : ℝ))).sub hdist0
                simpa using this
              -- squeeze `g = min f 1` between `min (1 − M‖·‖) 1 → 1` and the constant `1`.
              have hlow : Tendsto (fun z => min (1 - (M : ℝ) * ‖z - z₀‖) 1) (nhdsWithin z₀ U)
                  (nhds (min 1 1)) := hone.min tendsto_const_nhds
              rw [min_self] at hlow
              refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
                (hfge.mono fun z h => ?_) (Filter.Eventually.of_forall fun z => ?_)
              · exact min_le_min h (le_refl 1)
              · simp only [hgdef]; exact min_le_right (f z) 1
          have hwtend : Tendsto w (nhdsWithin z₀ U) (nhds (w z₀)) := by
            rw [hw0]
            have h := hgtend.sub hutend
            rw [sub_self] at h
            refine h.congr' ?_
            filter_upwards [self_mem_nhdsWithin] with z hz using (hw_eq z hz).symm
          exact hwtend
        · -- `z₀ ∉ closure U`: `𝓝[U] z₀ = ⊥`, trivially continuous within `U`.
          rw [ContinuousWithinAt, notMem_closure_iff_nhdsWithin_eq_bot.mp hz₀cl]
          exact tendsto_bot
    have hcomb := hWU.union hWUc
    rw [Set.union_compl_self, continuousWithinAt_univ] at hcomb
    exact hcomb
  -- Discharge the per-density estimate via the bounded capstone.
  exact dirichletEnergy_le_lintegral_sq_of_bounded_admissible hUopen hUbdd hu hρmeas hbdd
    hfact1 hfact2 hfact3 (hHardyU ρ hadm M hbdd)

end RiemannDynamics

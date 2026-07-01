/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.RingModulus
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The separating-family modulus of a ring and conjugate-modulus reciprocity

The conformal modulus of a ring domain comes in two conjugate forms. The **connecting** modulus
(`ringModulus`, `QC/Regularity/RingModulus.lean`) is the `curveModulus` of the curves joining the
two boundary components; the **separating** modulus is the `curveModulus` of the loops that wind
once around the hole, separating the two boundary components. For a round annulus the two are
reciprocal:

`ringModulus z₀ r R = 2π / log (R / r)`,  `separatingModulus z₀ r R = log (R / r) / (2π)`,

so their product is `1`. This **reciprocity** is the structural keystone of planar extremal-length
theory: it converts a lower bound on a connecting modulus into an upper bound on the conjugate
separating modulus, and it is the mechanism by which circular symmetrization (which is compatible
with the angular sweep of the separating family) controls the connecting modulus of a general ring.

A separating loop is described through a **continuous logarithmic lift**: a loop `γ` in `U`
separates the centre `z₀` with winding `+1` when `γ t - z₀ = exp (L t)` for an absolutely continuous
`L : ℝ → ℂ` whose total increment is `L 1 - L 0 = 2π i`. The imaginary part of `L` is the continuous
angle, and the `2π i` increment is exactly one counterclockwise turn (the same idiom as
`SensePreserving`). The increment forces `γ 1 = γ 0`, so such loops are automatically closed.

## Main definitions

* `separatingCurveFamily z₀ U` — absolutely continuous loops in `U` winding once around `z₀`;
* `separatingModulus z₀ r R` — the `curveModulus` of the separating family of the round annulus.

## Main statements

* `separatingModulus_roundAnnulus` — `separatingModulus z₀ r R = log (R / r) / (2π)`;
* `roundAnnulus_reciprocity` — `ringModulus z₀ r R * separatingModulus z₀ r R = 1`.

## References

* O. Lehto and K. I. Virtanen, *Quasiconformal mappings in the plane*, Ch. II §1 (the module of a
  ring domain and the conjugate quadrilateral).
* L. V. Ahlfors, *Lectures on quasiconformal mappings*, Ch. I §D (extremal length and its
  conjugate).
-/

open MeasureTheory
open scoped ENNReal NNReal Topology Real

namespace RiemannDynamics

/-- The **separating curve family** of a ring with hole at `z₀` inside the open set `U`: the
absolutely continuous loops in `U` that wind once counterclockwise around `z₀`. The winding is
encoded by a continuous logarithmic lift `L`: an absolutely continuous `L : ℝ → ℂ` with
`γ t - z₀ = exp (L t)` on `[0, 1]` and total increment `L 1 - L 0 = 2π i`. The increment forces
`γ 1 = γ 0` (since `exp` has period `2π i`), so the curve is a closed loop; the imaginary part of
`L` is the continuous angle, whose net change `2π` is exactly one turn around `z₀`. This is the
conjugate of `connectingCurveFamily`: where a connecting curve sweeps the radial range between the
boundary components, a separating loop sweeps the full `2π` of angle around the hole. -/
def separatingCurveFamily (z₀ : ℂ) (U : Set ℂ) : Set (ℝ → ℂ) :=
  {γ | Continuous γ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U) ∧
    ∃ L : ℝ → ℂ, AbsolutelyContinuousOnInterval L 0 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t - z₀ = Complex.exp (L t)) ∧
      L 1 - L 0 = 2 * (Real.pi : ℂ) * Complex.I}

/-- The **separating modulus of a round annulus** `{r < |z - z₀| < R}`: the `curveModulus` of the
family of absolutely continuous loops inside the annulus that wind once around the centre `z₀`. It
is the conjugate of `ringModulus`; for a genuine round annulus it equals `log (R / r) / (2π)`. -/
noncomputable def separatingModulus (z₀ : ℂ) (r R : ℝ) : ℝ≥0∞ :=
  curveModulus (separatingCurveFamily z₀ (RoundAnnulus z₀ r R))

/-- **The separating modulus of a round annulus.** For radii `0 < r < R` the conformal modulus of
the family of loops winding once around the centre inside the round annulus `{r < |z - z₀| < R}`
equals `log (R / r) / (2π)`. The extremal density is the radial `ρ(z) = 1 / (2π · |z - z₀|)`: it is
admissible (a loop winding once sweeps total angle `2π`, so via its logarithmic lift `L` the
arc-length integral is `(1 / 2π) ∫ |L'| ≥ (1 / 2π) |L 1 - L 0| = 1`) and has energy
`∫∫ ρ² = log (R / r) / (2π)`, while the length–area (Cauchy–Schwarz over angular circles) inequality
shows no admissible density has smaller energy. -/
theorem separatingModulus_roundAnnulus {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    separatingModulus z₀ r R = ENNReal.ofReal (Real.log (R / r) / (2 * Real.pi)) := by
  set Lg := Real.log (R / r) with hLg
  have hRr1 : 1 < R / r := (one_lt_div hr).mpr hrR
  have hLgpos : 0 < Lg := Real.log_pos hRr1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- ===================================================================
  -- Helper 1: a Lipschitz map composed with an AC function is AC.
  -- ===================================================================
  have lipComp_ac : ∀ {Y : Type} [PseudoMetricSpace Y] {F : ℝ → ℂ} {l : ℂ → Y} {K : NNReal},
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro Y _ F l K hl a b hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- ===================================================================
  -- Helper 2: the round annulus is open.
  -- ===================================================================
  have isOpen_ann : ∀ (w : ℂ) (a b : ℝ), IsOpen (RoundAnnulus w a b) := by
    intro w a b
    have h1 : IsOpen {z : ℂ | a < dist z w} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have h2 : IsOpen {z : ℂ | dist z w < b} :=
      isOpen_lt (continuous_id.dist continuous_const) continuous_const
    exact h1.inter h2
  -- ===================================================================
  -- Step 0: reduce to the centre `0`.
  -- ===================================================================
  have hreduce : separatingModulus z₀ r R = separatingModulus 0 r R := by
    unfold separatingModulus
    set φ : ℂ → ℂ := fun z => z + z₀ with hφ
    have hhom : IsHomeomorph φ := by
      have : IsHomeomorph (Homeomorph.addRight z₀) := Homeomorph.isHomeomorph _
      simpa [hφ, Homeomorph.addRight] using this
    have hdiff : DifferentiableOn ℂ φ Set.univ :=
      (differentiable_id.add_const z₀).differentiableOn
    have key := curveModulus_conformal_invariant hhom hdiff
      (separatingCurveFamily 0 (RoundAnnulus 0 r R))
    rw [← key]
    congr 1
    have hLipφ : LipschitzWith 1 φ :=
      LipschitzWith.of_dist_le_mul (fun x y => by simp [hφ, dist_eq_norm])
    have hLipχ : LipschitzWith 1 (fun z : ℂ => z - z₀) :=
      LipschitzWith.of_dist_le_mul (fun x y => by simp [dist_eq_norm])
    have hdistφ : ∀ (z : ℂ), dist (φ z) z₀ = dist z 0 := by
      intro z; simp [hφ, dist_eq_norm]
    have hdistχ : ∀ (z : ℂ), dist (z - z₀) 0 = dist z z₀ := by
      intro z; simp [dist_eq_norm]
    ext γ
    constructor
    · rintro ⟨hcont, hac, hsub, L, hacL, hexp, hinc⟩
      refine ⟨fun s => γ s - z₀, ⟨hcont.sub continuous_const, lipComp_ac hLipχ hac, ?_,
        L, hacL, ?_, hinc⟩, ?_⟩
      · intro t ht
        simp only [RoundAnnulus, Set.mem_setOf_eq, hdistχ]
        simpa [RoundAnnulus] using hsub t ht
      · intro t ht
        rw [sub_zero, ← hexp t ht]
      · funext s; simp [hφ]
    · rintro ⟨γ₀, ⟨hcont, hac, hsub, L, hacL, hexp, hinc⟩, rfl⟩
      refine ⟨?_, ?_, ?_, L, hacL, ?_, hinc⟩
      · have : Continuous (fun s => φ (γ₀ s)) := hLipφ.continuous.comp hcont
        simpa [hφ, Function.comp] using this
      · have : AbsolutelyContinuousOnInterval (fun s => φ (γ₀ s)) 0 1 := lipComp_ac hLipφ hac
        simpa [hφ, Function.comp] using this
      · intro t ht
        simp only [Function.comp_apply, hφ, RoundAnnulus, Set.mem_setOf_eq]
        rw [show γ₀ t + z₀ = φ (γ₀ t) from rfl, hdistφ]
        simpa [RoundAnnulus] using hsub t ht
      · intro t ht
        simp only [Function.comp_apply, hφ]
        have hh := hexp t ht
        rw [sub_zero] at hh
        rw [show γ₀ t + z₀ - z₀ = γ₀ t from by ring, hh]
  rw [hreduce]
  -- ===================================================================
  -- The extremal angular density (centred at 0).
  -- ===================================================================
  set rho0 : ℂ → ℝ≥0∞ := fun z =>
    Set.indicator (RoundAnnulus 0 r R)
      (fun z => ENNReal.ofReal (1 / (2 * Real.pi * ‖z‖))) z with hrho0
  have measurable_rho0 : Measurable rho0 := by
    apply Measurable.indicator _ (isOpen_ann 0 r R).measurableSet
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.div (measurable_const.mul measurable_norm))
  -- ===================================================================
  -- Energy: ∫⁻ rho0² = ofReal (log(R/r)/(2π)).
  -- ===================================================================
  have rho0_energy : ∫⁻ z, (rho0 z) ^ 2 = ENNReal.ofReal (Lg / (2 * Real.pi)) := by
    rw [← Complex.lintegral_comp_polarCoord_symm (fun z => (rho0 z) ^ 2)]
    have hval : Set.EqOn
        (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • (rho0 (Complex.polarCoord.symm p)) ^ 2)
        (fun p : ℝ × ℝ =>
          Set.indicator (Set.Ioo r R)
            (fun s => ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * s))) p.1)
        Complex.polarCoord.target := by
      intro p hp
      simp only [Complex.polarCoord_target, Set.mem_prod, Set.mem_Ioi] at hp
      have hp1 : 0 < p.1 := hp.1
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
      simp only [hrho0, smul_eq_mul]
      by_cases hmem : Complex.polarCoord.symm p ∈ RoundAnnulus 0 r R
      · have hmemIoo : p.1 ∈ Set.Ioo r R := by
          simp only [RoundAnnulus, Set.mem_setOf_eq, dist_zero_right, hnorm] at hmem
          exact ⟨hmem.1, hmem.2⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemIoo, hnorm]
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (le_of_lt hp1)]
        congr 1
        rw [div_pow, one_pow, mul_pow]
        field_simp
        ring
      · have hmemIoo : p.1 ∉ Set.Ioo r R := by
          simp only [RoundAnnulus, Set.mem_setOf_eq, dist_zero_right, hnorm] at hmem
          simpa only [Set.mem_Ioo] using hmem
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmemIoo]
        simp
    refine Eq.trans (setLIntegral_congr_fun (μ := volume)
      Complex.polarCoord.open_target.measurableSet hval) ?_
    change ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
        Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * s))) p.1
          = ENNReal.ofReal (Lg / (2 * π))
    rw [Measure.volume_eq_prod]
    rw [setLIntegral_prod]
    · have hinner : ∀ x : ℝ,
          ∫⁻ _y in Set.Ioo (-π) π,
            Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * s))) x
            = Set.indicator (Set.Ioo r R)
                (fun s => ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * s))) x
              * ENNReal.ofReal (2 * π) := by
        intro x
        rw [setLIntegral_const, Real.volume_Ioo]
        congr 2
        ring
      simp only [hinner]
      rw [lintegral_mul_const]
      · rw [setLIntegral_indicator measurableSet_Ioo]
        have hsetEq : Set.Ioo r R ∩ Set.Ioi (0 : ℝ) = Set.Ioo r R := by
          rw [Set.inter_eq_left]
          intro x hx; exact lt_trans hr hx.1
        rw [hsetEq]
        have hradial : ∫⁻ x in Set.Ioo r R, ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * x))
            = ENNReal.ofReal (Lg / (4 * Real.pi ^ 2)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR.le]
            have hsimp : ∀ x : ℝ, 1 / (4 * Real.pi ^ 2 * x) = (1 / (4 * Real.pi ^ 2)) * x⁻¹ := by
              intro x; rw [one_div, mul_inv, one_div]
            simp_rw [hsimp]
            rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr (by linarith)]
            rw [hLg, Real.log_div (ne_of_gt (lt_trans hr hrR)) hr.ne']
            congr 1
            ring
          · rw [← IntegrableOn]
            have hcontOn : ContinuousOn (fun x : ℝ => 1 / (4 * Real.pi ^ 2 * x)) (Set.Icc r R) := by
              apply ContinuousOn.div continuousOn_const
              · exact (continuous_const.mul continuous_id).continuousOn
              · intro x hx
                rw [Set.mem_Icc] at hx
                have : 0 < x := lt_of_lt_of_le hr hx.1
                positivity
            exact (hcontOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
          · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
            have : 0 < x := lt_trans hr hx.1
            positivity
        rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hLg]
        field_simp
        ring
      · apply Measurable.indicator _ measurableSet_Ioo
        apply ENNReal.measurable_ofReal.comp
        exact (measurable_const.div ((measurable_const.mul measurable_id)))
    · apply Measurable.aemeasurable
      have hh : Measurable (fun s : ℝ => ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * s))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_const.mul measurable_id))
      exact (hh.indicator measurableSet_Ioo).comp measurable_fst
  -- ===================================================================
  -- Admissibility of rho0.
  -- ===================================================================
  have rho0_admissible : ∀ {γ : ℝ → ℂ},
      AbsolutelyContinuousOnInterval γ 0 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ RoundAnnulus 0 r R) →
      (∃ L : ℝ → ℂ, AbsolutelyContinuousOnInterval L 0 1 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t - 0 = Complex.exp (L t)) ∧
        L 1 - L 0 = 2 * (Real.pi : ℂ) * Complex.I) →
      1 ≤ arcLengthLineIntegral rho0 γ := by
    rintro γ hac hsub ⟨L, hacL, hexp, hinc⟩
    -- L.im is AC, and the FTC chord bound gives ∫⁻ ‖deriv L‖ ≥ 2π.
    have hLimAC : AbsolutelyContinuousOnInterval (fun t => (L t).im) 0 1 := by
      rw [absolutelyContinuousOnInterval_iff] at hacL ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hacL ε hε
      refine ⟨δ, hδ, fun E hE hlen => ?_⟩
      refine lt_of_le_of_lt ?_ (hδ' E hE hlen)
      apply Finset.sum_le_sum
      intro i _
      rw [Real.dist_eq, ← Complex.sub_im]
      exact le_trans (Complex.abs_im_le_norm _) (le_of_eq (Complex.dist_eq _ _).symm)
    have hFTC : ∫ t in (0 : ℝ)..1, deriv (fun s => (L s).im) t = (L 1).im - (L 0).im :=
      hLimAC.integral_deriv_eq_sub
    have him : (L 1).im - (L 0).im = 2 * Real.pi := by
      have h2 : (L 1 - L 0).im = (2 * (Real.pi : ℂ) * Complex.I).im := by rw [hinc]
      rw [Complex.sub_im] at h2
      have hrhs : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by
        simp [Complex.mul_im, Complex.mul_re]
      rw [hrhs] at h2; exact h2
    have hLdiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ L t :=
      hacL.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    have hderiv_im : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        deriv (fun s => (L s).im) t = (deriv L t).im := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hLdiff] with t htd htmem
      have htu : t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
      have hd := htd htu
      have h2 : HasDerivAt (fun s => (L s).im) (deriv L t).im t := by
        have hh := (Complex.imCLM.hasFDerivAt.comp t hd.hasDerivAt.hasFDerivAt).hasDerivAt
        simpa using hh
      exact h2.deriv
    have hintIm : IntervalIntegrable (deriv (fun s => (L s).im)) volume 0 1 :=
      hLimAC.intervalIntegrable_deriv
    have hIccIoo : (volume.restrict (Set.Icc (0 : ℝ) 1))
        = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm
    have hchord : ENNReal.ofReal (2 * Real.pi)
        ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv L t‖₊ : ℝ≥0∞) := by
      calc ENNReal.ofReal (2 * Real.pi)
          = ENNReal.ofReal ((L 1).im - (L 0).im) := by rw [him]
        _ = ENNReal.ofReal (∫ t in (0 : ℝ)..1, deriv (fun s => (L s).im) t) := by rw [hFTC]
        _ ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, |deriv (fun s => (L s).im) t|) := by
            apply ENNReal.ofReal_le_ofReal
            rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
            apply setIntegral_mono_on
            · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hintIm
            · exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hintIm).abs
            · exact measurableSet_Ioo
            · intro x _; exact le_abs_self _
        _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv (fun s => (L s).im) t| := by
            rw [ofReal_integral_eq_lintegral_ofReal
              ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hintIm).abs
              (ae_restrict_of_forall_mem measurableSet_Ioo (fun x _ => abs_nonneg _))]
        _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |(deriv L t).im| := by
            apply lintegral_congr_ae
            filter_upwards [hderiv_im] with t ht; rw [ht]
        _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv L t‖₊ : ℝ≥0∞) := by
            apply lintegral_mono
            intro t
            simp only
            rw [show (‖deriv L t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv L t‖ from by
              rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]]
            exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)
    -- pointwise: rho0(γ t)*‖deriv γ t‖₊ = ofReal(1/2π)*‖deriv L t‖₊ a.e.
    have hline : arcLengthLineIntegral rho0 γ
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      unfold arcLengthLineIntegral
      rw [hIccIoo]
    rw [hline]
    have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ENNReal.ofReal (1 / (2 * Real.pi)) * (‖deriv L t‖₊ : ℝ≥0∞)
          ≤ rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hLdiff] with t htd htmem
      have htu : t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
      have hd := htd htu
      have hann : γ t ∈ RoundAnnulus 0 r R := hsub t (Set.Ioo_subset_Icc_self htmem)
      -- γ =ᶠ exp∘L near t, so deriv γ t = exp(L t)*deriv L t = γ t * deriv L t.
      have hexpD : HasDerivAt (fun s => Complex.exp (L s)) (Complex.exp (L t) * deriv L t) t :=
        hd.hasDerivAt.cexp
      have hev : γ =ᶠ[nhds t] (fun s => Complex.exp (L s)) := by
        have hopen : Set.Ioo (0 : ℝ) 1 ∈ nhds t := isOpen_Ioo.mem_nhds htmem
        filter_upwards [hopen] with s hs
        have hes := hexp s (Set.Ioo_subset_Icc_self hs)
        rw [sub_zero] at hes; exact hes
      have hγD : HasDerivAt γ (Complex.exp (L t) * deriv L t) t :=
        hexpD.congr_of_eventuallyEq hev
      have hγeq : γ t = Complex.exp (L t) := by
        have := hexp t (Set.Ioo_subset_Icc_self htmem); rw [sub_zero] at this; exact this
      have hderivγ : deriv γ t = γ t * deriv L t := by
        rw [hγD.deriv, hγeq]
      have hgpos : 0 < ‖γ t‖ := by
        rw [hγeq, Complex.norm_exp]; positivity
      have hrhoeq : rho0 (γ t) = ENNReal.ofReal (1 / (2 * Real.pi * ‖γ t‖)) := by
        simp only [hrho0, Set.indicator_of_mem hann]
      rw [hrhoeq, hderivγ]
      rw [show (‖γ t * deriv L t‖₊ : ℝ≥0∞) = ENNReal.ofReal (‖γ t‖ * ‖deriv L t‖) from by
        rw [show ENNReal.ofReal (‖γ t‖ * ‖deriv L t‖) = ENNReal.ofReal ‖γ t * deriv L t‖ from by
          rw [norm_mul], ofReal_norm_eq_enorm, enorm_eq_nnnorm]]
      rw [show (‖deriv L t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv L t‖ from by
        rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply le_of_eq
      congr 1
      field_simp
    calc (1 : ℝ≥0∞)
        = ENNReal.ofReal (1 / (2 * Real.pi)) * ENNReal.ofReal (2 * Real.pi) := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ (by positivity),
            ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (1 / (2 * Real.pi))
            * ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv L t‖₊ : ℝ≥0∞) := by
          gcongr
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            ENNReal.ofReal (1 / (2 * Real.pi)) * (‖deriv L t‖₊ : ℝ≥0∞) := by
          rw [lintegral_const_mul]
          exact measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp (measurable_deriv L))
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) :=
          lintegral_mono_ae hpoint
  -- ===================================================================
  -- Upper bound.
  -- ===================================================================
  have hupper : separatingModulus 0 r R ≤ ENNReal.ofReal (Lg / (2 * Real.pi)) := by
    unfold separatingModulus curveModulus
    refine le_trans (iInf₂_le rho0 ?_) ?_
    · refine ⟨measurable_rho0, ?_⟩
      rintro γ ⟨_, hac, hsub, L, hacL, hexp, hinc⟩
      exact rho0_admissible hac hsub ⟨L, hacL, hexp, hinc⟩
    · exact le_of_eq rho0_energy
  -- ===================================================================
  -- The angular circle (centred at 0): c_s t = polarCoord.symm (s, (2t-1)π).
  -- ===================================================================
  -- For admissible ρ, the per-circle Cauchy–Schwarz bound.
  have angular_energy_lower : ∀ {ρ : ℂ → ℝ≥0∞}, IsAdmissibleDensity ρ
      (separatingCurveFamily 0 (RoundAnnulus 0 r R)) →
      ∀ {s : ℝ}, s ∈ Set.Ioo r R →
        ENNReal.ofReal (1 / (2 * Real.pi * s ^ 2))
          ≤ ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (ρ (Complex.polarCoord.symm (s, θ))) ^ 2 := by
    intro ρ hρ s hs
    have hspos : 0 < s := lt_trans hr hs.1
    set c : ℝ → ℂ := fun t => Complex.polarCoord.symm (s, (2 * t - 1) * Real.pi) with hc
    have hceq : ∀ t, c t = (s : ℂ) * Complex.exp ((((2 * t - 1) * Real.pi : ℝ)) * Complex.I) := by
      intro t
      simp only [hc]
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
      push_cast [Complex.ofReal_cos, Complex.ofReal_sin]; ring
    have hnormc : ∀ t, ‖c t‖ = s := by
      intro t; rw [hceq, norm_mul, Complex.norm_exp]
      simp [Complex.norm_real, abs_of_pos hspos]
    set Lift : ℝ → ℂ :=
      fun t => (Real.log s : ℂ) + ((2 * t - 1) * Real.pi : ℝ) * Complex.I with hLift
    have hD : ∀ t : ℝ, HasDerivAt c
        ((s : ℂ) * (Complex.exp ((((2 * t - 1) * Real.pi : ℝ)) * Complex.I)
          * ((2 * Real.pi : ℝ) * Complex.I))) t := by
      intro t
      have hf : c = fun t : ℝ =>
          (s : ℂ) * Complex.exp ((((2 * t - 1) * Real.pi : ℝ)) * Complex.I) := by
        funext u; exact hceq u
      rw [hf]
      apply HasDerivAt.const_mul
      have h1 : HasDerivAt (fun t : ℝ => (((2 * t - 1) * Real.pi : ℝ)) * Complex.I)
          ((2 * Real.pi : ℝ) * Complex.I) t := by
        have hr2 : HasDerivAt (fun t : ℝ => ((((2 * t - 1) * Real.pi : ℝ)) : ℂ))
            (((2 * Real.pi : ℝ)) : ℂ) t := by
          have hbase : HasDerivAt (fun t : ℝ => ((2 * t - 1) * Real.pi : ℝ)) (2 * Real.pi) t := by
            have := ((hasDerivAt_id t).const_mul (2 : ℝ)).sub_const 1
            simpa using (this.mul_const Real.pi)
          exact hbase.ofReal_comp
        simpa using hr2.mul_const Complex.I
      exact h1.cexp
    have hderivnorm : ∀ t, ‖deriv c t‖ = 2 * Real.pi * s := by
      intro t
      rw [(hD t).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos, norm_mul,
        Complex.norm_exp, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have hre0 : (((2 * t - 1) * Real.pi : ℝ) * Complex.I).re = 0 := by simp
      rw [hre0, Real.exp_zero]
      ring
    have hlipc : LipschitzOnWith (⟨2 * Real.pi * s, by positivity⟩ : ℝ≥0) c (Set.uIcc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]
      have hbound : ∀ z ∈ Set.uIcc (0 : ℝ) 1, ‖deriv c z‖ ≤ 2 * Real.pi * s :=
        fun z _ => le_of_eq (hderivnorm z)
      have hmv := (convex_uIcc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => (hD z).differentiableAt) hbound hy hx
      exact hmv
    have hacc : AbsolutelyContinuousOnInterval c 0 1 := hlipc.absolutelyContinuousOnInterval
    have hcontc : Continuous c := by
      have : Continuous (fun t : ℝ => (s : ℂ)
          * Complex.exp ((((2 * t - 1) * Real.pi : ℝ)) * Complex.I)) := by
        apply continuous_const.mul
        apply Complex.continuous_exp.comp
        exact (Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const
      exact this.congr (fun t => (hceq t).symm)
    have hlipL : LipschitzWith (⟨2 * Real.pi, by positivity⟩ : ℝ≥0) Lift := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm, hLift, NNReal.coe_mk]
      rw [show ((Real.log s : ℂ) + ((2 * x - 1) * Real.pi : ℝ) * Complex.I)
            - ((Real.log s : ℂ) + ((2 * y - 1) * Real.pi : ℝ) * Complex.I)
          = (((2 * x - 1) * Real.pi - (2 * y - 1) * Real.pi : ℝ) : ℂ) * Complex.I from by
        push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [show (2 * x - 1) * Real.pi - (2 * y - 1) * Real.pi = (2 * Real.pi) * (x - y) from by ring]
      rw [abs_mul, abs_of_pos (by positivity)]
    have haccL : AbsolutelyContinuousOnInterval Lift 0 1 :=
      (hlipL.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
    -- c is in the separating family.
    have hcmem : c ∈ separatingCurveFamily 0 (RoundAnnulus 0 r R) := by
      refine ⟨hcontc, hacc, ?_, Lift, haccL, ?_, ?_⟩
      · intro t ht
        simp only [RoundAnnulus, Set.mem_setOf_eq, dist_zero_right, hnormc]
        exact ⟨hs.1, hs.2⟩
      · intro t ht
        rw [sub_zero, hceq, hLift, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hspos]
      · rw [hLift]; push_cast; ring
    have hadm : 1 ≤ arcLengthLineIntegral ρ c := hρ.2 c hcmem
    -- arc-length of c = ofReal(2πs) * ∫_{Ioo 0 1} ρ(c t).
    have harc : arcLengthLineIntegral ρ c
        = ENNReal.ofReal (2 * Real.pi * s) * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ρ (c t) := by
      unfold arcLengthLineIntegral
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro t
      rw [show (‖deriv c t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv c t‖ from by
        rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm], hderivnorm, mul_comm]
    rw [harc] at hadm
    -- Cauchy–Schwarz on [0,1]: ∫_{Ioo} ρ(c·)² ≥ 1/(4π²s²).
    have hmeasf : Measurable (fun t => ρ (c t)) := hρ.1.comp hcontc.measurable
    have hcs : ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * s ^ 2))
        ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ρ (c t)) ^ 2 := by
      set μ := volume.restrict (Set.Ioo (0 : ℝ) 1) with hμ
      set g : ℝ → ℝ≥0∞ := fun _ => 1 with hg
      have hmeasg : AEMeasurable g μ := aemeasurable_const
      have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
        (Real.HolderConjugate.two_two) hmeasf.aemeasurable hmeasg
      have hfg : ∫⁻ t, ((fun t => ρ (c t)) * g) t ∂μ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ρ (c t) := by
        rw [hμ]; apply lintegral_congr; intro t; simp [hg]
      have hgsq : ∫⁻ t, (g t) ^ (2 : ℝ) ∂μ = 1 := by
        rw [hμ, hg]; simp [Real.volume_Ioo]
      have hfsq : ∫⁻ t, ((fun t => ρ (c t)) t) ^ (2 : ℝ) ∂μ
          = ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ρ (c t)) ^ 2 := by
        rw [hμ]; apply lintegral_congr; intro t; rw [ENNReal.rpow_two, sq]
      rw [hfg, hfsq, hgsq] at hholder
      rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hholder
      rw [ENNReal.one_rpow, mul_one] at hholder
      have hlow : ENNReal.ofReal (1 / (2 * Real.pi * s))
          ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ρ (c t) := by
        have hinv : ENNReal.ofReal (1 / (2 * Real.pi * s))
            = (ENNReal.ofReal (2 * Real.pi * s))⁻¹ := by
          rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div]
        rw [hinv]
        rw [ENNReal.inv_le_iff_le_mul
          (fun _ => by intro h; rw [ENNReal.ofReal_eq_zero] at h; nlinarith)
          (fun h => absurd h ENNReal.ofReal_ne_top)]
        exact hadm
      have hkey : ENNReal.ofReal (1 / (2 * Real.pi * s))
          ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, (ρ (c t)) ^ 2) ^ (2 : ℝ)⁻¹ := le_trans hlow hholder
      have hsq := ENNReal.rpow_le_rpow hkey (show (0 : ℝ) ≤ 2 by norm_num)
      rw [← ENNReal.rpow_mul, show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one] at hsq
      refine le_trans (le_of_eq ?_) hsq
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [div_pow, one_pow, mul_pow, mul_pow]
      norm_num
    -- angular slice substitution θ = (2t-1)π relates the two integrals.
    have hslice : ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (ρ (Complex.polarCoord.symm (s, θ))) ^ 2
        = ENNReal.ofReal (2 * Real.pi)
          * ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ρ (c t)) ^ 2 := by
      have himg : (fun t : ℝ => (2 * t - 1) * Real.pi) '' Set.Ioo (0 : ℝ) 1
          = Set.Ioo (-Real.pi) Real.pi := by
        ext θ
        simp only [Set.mem_image, Set.mem_Ioo]
        constructor
        · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
          constructor <;> nlinarith
        · intro ⟨h1, h2⟩
          refine ⟨(θ + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
          · apply div_pos (by linarith) (by positivity)
          · rw [div_lt_one (by positivity)]; linarith
          · field_simp; ring
      rw [← himg]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
        (f := fun t => (2 * t - 1) * Real.pi) (f' := fun _ => 2 * Real.pi) ?_ ?_]
      · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro t
        rw [abs_of_pos (by positivity), hc]
      · intro x _
        have : HasDerivAt (fun t : ℝ => (2 * t - 1) * Real.pi) (2 * Real.pi) x := by
          have := ((hasDerivAt_id x).const_mul (2 : ℝ)).sub_const 1
          simpa using (this.mul_const Real.pi)
        exact this.hasDerivWithinAt
      · intro a _ b _ hab
        simp only at hab
        have h2 := mul_right_cancel₀ hpi.ne' hab
        linarith
    rw [hslice]
    calc ENNReal.ofReal (1 / (2 * Real.pi * s ^ 2))
        = ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (1 / (4 * Real.pi ^ 2 * s ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
          ring
      _ ≤ ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ρ (c t)) ^ 2 := by
          gcongr
  -- ===================================================================
  -- ∫_r^R 1/(2πs) ds = log(R/r)/(2π).
  -- ===================================================================
  have lintegral_inv_angular : ∫⁻ s in Set.Ioo r R, ENNReal.ofReal (1 / (2 * Real.pi * s))
      = ENNReal.ofReal (Lg / (2 * Real.pi)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR.le]
      have hsimp : ∀ x : ℝ, 1 / (2 * Real.pi * x) = (1 / (2 * Real.pi)) * x⁻¹ := by
        intro x; rw [one_div, mul_inv, one_div]
      simp_rw [hsimp]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr (by linarith)]
      rw [hLg]
      congr 1
      rw [one_div, inv_mul_eq_div]
    · rw [← IntegrableOn]
      have hcontOn : ContinuousOn (fun x : ℝ => 1 / (2 * Real.pi * x)) (Set.Icc r R) := by
        apply ContinuousOn.div continuousOn_const
        · exact (continuous_const.mul continuous_id).continuousOn
        · intro x hx
          rw [Set.mem_Icc] at hx
          have : 0 < x := lt_of_lt_of_le hr hx.1
          positivity
      exact (hcontOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
      have : 0 < x := lt_trans hr hx.1
      positivity
  -- ===================================================================
  -- Lower bound.
  -- ===================================================================
  have hlower : ENNReal.ofReal (Lg / (2 * Real.pi)) ≤ separatingModulus 0 r R := by
    unfold separatingModulus curveModulus
    refine le_iInf₂ ?_
    rintro ρ ⟨hρmeas, hρadm⟩
    have hρ : IsAdmissibleDensity ρ (separatingCurveFamily 0 (RoundAnnulus 0 r R)) :=
      ⟨hρmeas, hρadm⟩
    rw [← Complex.lintegral_comp_polarCoord_symm (fun z => (ρ z) ^ 2)]
    -- polar integral with s = p.1 (fst, outer), θ = p.2 (snd, inner).
    have hrwInt : ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • (ρ (Complex.polarCoord.symm p)) ^ 2
        = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
            (ρ (Complex.polarCoord.symm p)) ^ 2 * ENNReal.ofReal p.1 := by
      rw [polarCoord_target]
      refine setLIntegral_congr_fun (μ := volume)
        (by rw [← polarCoord_target]; exact Complex.polarCoord.open_target.measurableSet) ?_
      intro p _
      simp only [smul_eq_mul, mul_comm]
    rw [hrwInt]
    have hmeasInt : Measurable
        (fun p : ℝ × ℝ => (ρ (Complex.polarCoord.symm p)) ^ 2 * ENNReal.ofReal p.1) := by
      apply Measurable.mul
      · refine ((hρmeas.comp ?_).pow_const 2)
        have : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
          simp only [Complex.polarCoord_symm_apply]; fun_prop
        exact this.measurable
      · exact ENNReal.measurable_ofReal.comp measurable_fst
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hmeasInt.aemeasurable]
    calc ENNReal.ofReal (Lg / (2 * Real.pi))
        = ∫⁻ s in Set.Ioo r R, ENNReal.ofReal (1 / (2 * Real.pi * s)) := lintegral_inv_angular.symm
      _ ≤ ∫⁻ s in Set.Ioo r R,
            ∫⁻ θ in Set.Ioo (-π) π,
              (ρ (Complex.polarCoord.symm (s, θ))) ^ 2 * ENNReal.ofReal s := by
          apply lintegral_mono_ae
          refine ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => ?_)
          have hspos : 0 < s := lt_trans hr hs.1
          rw [lintegral_mul_const _ (by
            refine ((hρmeas.comp ?_).pow_const 2)
            have : Continuous (fun θ : ℝ => Complex.polarCoord.symm (s, θ)) := by
              simp only [Complex.polarCoord_symm_apply]; fun_prop
            exact this.measurable)]
          calc ENNReal.ofReal (1 / (2 * Real.pi * s))
              = ENNReal.ofReal (1 / (2 * Real.pi * s ^ 2)) * ENNReal.ofReal s := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                field_simp
            _ ≤ (∫⁻ θ in Set.Ioo (-π) π, (ρ (Complex.polarCoord.symm (s, θ))) ^ 2)
                  * ENNReal.ofReal s := by
                gcongr
                exact angular_energy_lower hρ hs
      _ ≤ ∫⁻ s in Set.Ioi (0 : ℝ),
            ∫⁻ θ in Set.Ioo (-π) π,
              (ρ (Complex.polarCoord.symm (s, θ))) ^ 2 * ENNReal.ofReal s := by
          apply lintegral_mono_set
          intro s hs; exact lt_trans hr hs.1
  rw [hLg] at hupper hlower
  exact le_antisymm hupper hlower

/-- **Conjugate-modulus reciprocity for the round annulus.** The connecting modulus and the
separating modulus of a round annulus are reciprocal: their product is `1`. Immediate from the two
explicit values `ringModulus = 2π / log (R / r)` and `separatingModulus = log (R / r) / (2π)`. This
is the round-annulus case of the general reciprocity `M_connecting · M_separating = 1` for ring
domains. -/
theorem roundAnnulus_reciprocity {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ringModulus z₀ r R * separatingModulus z₀ r R = 1 := by
  rw [ringModulus_roundAnnulus hr hrR, separatingModulus_roundAnnulus hr hrR]
  have hRr1 : 1 < R / r := (one_lt_div hr).mpr hrR
  have hLpos : 0 < Real.log (R / r) := Real.log_pos hRr1
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [← ENNReal.ofReal_mul (by positivity)]
  have hL0 : Real.log (R / r) ≠ 0 := ne_of_gt hLpos
  have hpi0 : (2 * Real.pi) ≠ 0 := by positivity
  rw [show 2 * Real.pi / Real.log (R / r) * (Real.log (R / r) / (2 * Real.pi)) = 1 by
    field_simp]
  exact ENNReal.ofReal_one

end RiemannDynamics

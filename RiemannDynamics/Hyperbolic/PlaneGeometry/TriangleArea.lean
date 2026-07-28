/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.PlaneGeometry.Geodesics
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Hyperbolic areas: wedges, half-strips, and geodesic triangles

The hyperbolic area on the upper half plane is `dx dy / y²`. Areas of regions above a graph
reduce by Fubini to `∫ dx / Y(x)`; over a circular arc the integrand is `1 / √(r² - x²)`,
whose primitive is the arcsine, so the area of a wedge between two verticals over an arc is
an arcsine difference. The Gauss–Bonnet formula for a geodesic triangle follows: the area is
the angle deficit `π - α - β - γ`.

* `volume_smul_gl`, `volume_smul_sl2` — invariance of the hyperbolic area under `GL(2, ℝ)`
  (including orientation-reversing elements) and `SL(2, ℝ)`.
* `volume_region_above` — the master Fubini identity for regions above a graph.
* `volume_halfStrip` — the area `(b - a)/c` of a vertical half-strip.
* `volume_unitWedge` — the wedge over the unit circle between the verticals at `cos θ₂` and
  `cos θ₁` has area `θ₂ - θ₁`; `volume_idealTriangle` — the triply ideal triangle has
  area `π`.
* `volume_wedge` — the wedge over a circle of center `x₀` and radius `r`.
* `volume_hyperbolicTriangle` — the Gauss–Bonnet angle-deficit formula
  `π - α - β - γ` for geodesic triangles.
-/

open MeasureTheory Set Real UpperHalfPlane
open scoped NNReal ENNReal MatrixGroups UpperHalfPlane Pointwise

namespace RiemannDynamics

/-! ## Invariance of the hyperbolic area -/

/-- The hyperbolic area is invariant under the `GL(2, ℝ)` Möbius action, including the
orientation-reversing elements. -/
theorem volume_smul_gl (g : GL (Fin 2) ℝ) (S : Set ℍ) : volume (g • S) = volume S :=
  measure_smul volume g S

/-- The hyperbolic area is invariant under `SL(2, ℝ)`: the `GL(2, ℝ)` invariance transported
through `Matrix.SpecialLinearGroup.mapGL`. -/
theorem volume_smul_sl2 (γ : SL(2, ℝ)) (S : Set ℍ) : volume (γ • S) = volume S := by
  haveI : SMulInvariantMeasure SL(2, ℝ) ℍ (volume : Measure ℍ) :=
    ⟨fun c s hs => SMulInvariantMeasure.measure_preimage_smul
      (μ := (volume : Measure ℍ)) (Matrix.SpecialLinearGroup.mapGL ℝ c) hs⟩
  exact measure_smul volume γ S

/-! ## The density bridge -/

/-- The hyperbolic area density `(1/‖y‖₊)²` as `ENNReal.ofReal (1 / y²)` on `{0 < y}`. -/
theorem hyperbolicDensity_eq {y : ℝ} (hy : 0 < y) :
    (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 / y ^ 2) := by
  rw [Real.nnnorm_of_nonneg hy.le, ENNReal.ofReal]
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (by positivity)]
  push_cast
  rw [div_pow, one_pow]

/-! ## The master Fubini identity -/

set_option maxHeartbeats 400000 in
-- The proof chains `volume_eq_lintegral`, a measurable-embedding change of variables to
-- `ℝ × ℝ`, and `lintegral_prod` over indicator functions; the combined elaboration exceeds
-- the default heartbeat budget.
/-- Hyperbolic area of the region above the graph of `g` over the base `s`, as an iterated
Lebesgue integral of the density `1/y²`. -/
theorem volume_region_above {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    volume {z : ℍ | z.re ∈ s ∧ g z.re ≤ z.im}
      = ∫⁻ x in s, ∫⁻ y in {y : ℝ | 0 < y ∧ g x ≤ y}, ENNReal.ofReal (1 / y ^ 2) := by
  classical
  set S : Set ℍ := {z : ℍ | z.re ∈ s ∧ g z.re ≤ z.im} with hSdef
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.2 ∧ p.1 ∈ s ∧ g p.1 ≤ p.2} with hTdef
  have hTm : MeasurableSet T := by
    have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
      measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet {p : ℝ × ℝ | p.1 ∈ s} := measurable_fst hs
    have h3 : MeasurableSet {p : ℝ × ℝ | g p.1 ≤ p.2} :=
      measurableSet_le (hg.comp measurable_fst) measurable_snd
    exact h1.inter (h2.inter h3)
  have himg : Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' S) = T := by
    rw [Set.image_image]
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.im_pos, hz.1, hz.2⟩
    · rintro ⟨hp2, hp1, hple⟩
      exact ⟨⟨⟨p.1, p.2⟩, hp2⟩, ⟨hp1, hple⟩, rfl⟩
  have hInd : Measurable (T.indicator fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) :=
    (ENNReal.measurable_ofReal.comp
      (measurable_const.div (measurable_snd.pow_const 2))).indicator hTm
  calc volume S
      = ∫⁻ w in UpperHalfPlane.coe '' S, (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
        UpperHalfPlane.volume_eq_lintegral S
    _ = ∫⁻ p in Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' S),
          (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
        Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_emb
          Complex.measurableEquivRealProd.measurableEmbedding
          (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) (UpperHalfPlane.coe '' S)
    _ = ∫⁻ p in T, (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by rw [himg]
    _ = ∫⁻ p in T, ENNReal.ofReal (1 / p.2 ^ 2) :=
        setLIntegral_congr_fun hTm fun p hp => hyperbolicDensity_eq hp.1
    _ = ∫⁻ p, T.indicator (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) p :=
        (lintegral_indicator hTm _).symm
    _ = ∫⁻ x, ∫⁻ y, T.indicator (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) (x, y) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod _ hInd.aemeasurable
    _ = ∫⁻ x, s.indicator
          (fun x => ∫⁻ y in {y : ℝ | 0 < y ∧ g x ≤ y}, ENNReal.ofReal (1 / y ^ 2)) x := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem hx]
          have hAx : MeasurableSet {y : ℝ | 0 < y ∧ g x ≤ y} :=
            (measurableSet_lt measurable_const measurable_id).inter
              (measurableSet_le measurable_const measurable_id)
          rw [← lintegral_indicator hAx]
          refine lintegral_congr fun y => ?_
          by_cases hy : y ∈ {y : ℝ | 0 < y ∧ g x ≤ y}
          · rw [Set.indicator_of_mem hy,
              Set.indicator_of_mem (show (x, y) ∈ T from ⟨hy.1, hx, hy.2⟩)]
          · rw [Set.indicator_apply, if_neg (show (x, y) ∉ T from fun hc => hy ⟨hc.1, hc.2.2⟩),
              Set.indicator_apply, if_neg hy]
        · rw [Set.indicator_apply, if_neg hx]
          have hz : ∀ y : ℝ,
              T.indicator (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) (x, y) = 0 := by
            intro y
            rw [Set.indicator_apply, if_neg (show (x, y) ∉ T from fun hc => hx hc.2.1)]
          rw [lintegral_congr hz, lintegral_zero]
    _ = ∫⁻ x in s, ∫⁻ y in {y : ℝ | 0 < y ∧ g x ≤ y}, ENNReal.ofReal (1 / y ^ 2) :=
        lintegral_indicator hs _

/-! ## The inner integral -/

/-- The inner integral of the density: `∫ y in [t, ∞), dy/y² = 1/t`. -/
theorem lintegral_inv_sq_above {t : ℝ} (ht : 0 < t) :
    ∫⁻ y in {y : ℝ | 0 < y ∧ t ≤ y}, ENNReal.ofReal (1 / y ^ 2) = ENNReal.ofReal (1 / t) := by
  have hset : {y : ℝ | 0 < y ∧ t ≤ y} = Ici t := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ici, and_iff_right_iff_imp]
    exact fun h => ht.trans_le h
  have hEq : EqOn (fun y : ℝ => y ^ (-2 : ℝ)) (fun y : ℝ => 1 / y ^ 2) (Ioi t) := by
    intro y hy
    have hy' : (0 : ℝ) < y := ht.trans hy
    simp only
    rw [Real.rpow_neg hy'.le, Real.rpow_two, one_div]
  have hint : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi t) := by
    have h0 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ht
    exact h0.congr_fun hEq measurableSet_Ioi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi t)] fun y : ℝ => 1 / y ^ 2 :=
    Filter.Eventually.of_forall fun y => by positivity
  have hval : ∫ y in Ioi t, 1 / y ^ 2 = 1 / t := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hEq]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ht]
    norm_num [Real.rpow_neg_one]
  rw [hset, ← setLIntegral_congr (Ioi_ae_eq_Ici (a := t)),
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-! ## The vertical half-strip -/

/-- The hyperbolic area of a vertical half-strip is `(b - a)/c`. -/
theorem volume_halfStrip {a b c : ℝ} (hc : 0 < c) :
    volume {z : ℍ | z.re ∈ Icc a b ∧ c ≤ z.im} = ENNReal.ofReal ((b - a) / c) := by
  calc volume {z : ℍ | z.re ∈ Icc a b ∧ c ≤ z.im}
      = ∫⁻ x in Icc a b, ∫⁻ y in {y : ℝ | 0 < y ∧ c ≤ y}, ENNReal.ofReal (1 / y ^ 2) :=
        volume_region_above measurableSet_Icc measurable_const
    _ = ∫⁻ _ in Icc a b, ENNReal.ofReal (1 / c) :=
        setLIntegral_congr_fun measurableSet_Icc fun x _ => lintegral_inv_sq_above hc
    _ = ENNReal.ofReal (1 / c) * volume (Icc a b) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((b - a) / c) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [one_div, inv_mul_eq_div]

/-! ## The arcsine primitive -/

/-- The Lebesgue integral of `1/√(1 - x²)` over `Ioo u v` inside `[-1, 1]` is an arcsine
difference; the endpoint values `u = -1`, `v = 1` are allowed, integrability holding because
the integrand is the derivative of the continuous monotone arcsine. -/
theorem lintegral_one_div_sqrt_one_sub_sq {u v : ℝ} (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    ∫⁻ x in Ioo u v, ENNReal.ofReal (1 / √(1 - x ^ 2))
      = ENNReal.ofReal (arcsin v - arcsin u) := by
  have hsub : Ioo u v ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo hu hv
  have hderiv : ∀ x ∈ Ioo u v, HasDerivAt arcsin (1 / √(1 - x ^ 2)) x := fun x hx =>
    Real.hasDerivAt_arcsin (hsub hx).1.ne' (hsub hx).2.ne
  have hint : IntervalIntegrable (fun x : ℝ => 1 / √(1 - x ^ 2)) volume u v := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg
      Real.continuous_arcsin.continuousOn (fun x hx => ?_) (fun x hx => by positivity)
    rw [min_eq_left huv, max_eq_right huv] at hx
    exact hderiv x hx
  have hFTC : ∫ x in u..v, 1 / √(1 - x ^ 2) = arcsin v - arcsin u :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huv
      Real.continuous_arcsin.continuousOn
      (fun x hx => (hderiv x hx).hasDerivWithinAt) hint
  have hIoo : ∫ x in Ioo u v, 1 / √(1 - x ^ 2) = arcsin v - arcsin u := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le huv]
    exact hFTC
  have hInt : IntegrableOn (fun x : ℝ => 1 / √(1 - x ^ 2)) (Ioo u v) :=
    (hint.1).mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo u v)] fun x : ℝ => 1 / √(1 - x ^ 2) :=
    Filter.Eventually.of_forall fun x => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn, hIoo]

/-! ## Wedges over the unit circle -/

/-- The wedge bounded by the verticals `re z = cos θ₂`, `re z = cos θ₁` and the unit circle,
for `0 ≤ θ₁ ≤ θ₂ ≤ π`, has area `θ₂ - θ₁`: the vertex at `∞` is ideal, the circle vertices
`e^{iθ₂}`, `e^{iθ₁}` have interior angles `π - θ₂` and `θ₁`, and
`θ₂ - θ₁ = π - 0 - (π - θ₂) - θ₁` is the angle deficit. The endpoint values `θ₁ = 0` and
`θ₂ = π` (ideal circle vertices) are allowed. -/
theorem volume_unitWedge {θ₁ θ₂ : ℝ} (h₁ : 0 ≤ θ₁) (h₁₂ : θ₁ ≤ θ₂) (h₂ : θ₂ ≤ π) :
    volume {z : ℍ | z.re ∈ Icc (cos θ₂) (cos θ₁) ∧ √(1 - z.re ^ 2) ≤ z.im}
      = ENNReal.ofReal (θ₂ - θ₁) := by
  have hg : Measurable fun x : ℝ => √(1 - x ^ 2) :=
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).measurable
  have hcc : cos θ₂ ≤ cos θ₁ := Real.cos_le_cos_of_nonneg_of_le_pi h₁ h₂ h₁₂
  have harcsin : arcsin (cos θ₁) - arcsin (cos θ₂) = θ₂ - θ₁ := by
    rw [← Real.sin_pi_div_two_sub θ₁, ← Real.sin_pi_div_two_sub θ₂,
      Real.arcsin_sin (by linarith) (by linarith),
      Real.arcsin_sin (by linarith) (by linarith)]
    ring
  calc volume {z : ℍ | z.re ∈ Icc (cos θ₂) (cos θ₁) ∧ √(1 - z.re ^ 2) ≤ z.im}
      = ∫⁻ x in Icc (cos θ₂) (cos θ₁),
          ∫⁻ y in {y : ℝ | 0 < y ∧ √(1 - x ^ 2) ≤ y}, ENNReal.ofReal (1 / y ^ 2) :=
        volume_region_above measurableSet_Icc hg
    _ = ∫⁻ x in Ioo (cos θ₂) (cos θ₁),
          ∫⁻ y in {y : ℝ | 0 < y ∧ √(1 - x ^ 2) ≤ y}, ENNReal.ofReal (1 / y ^ 2) := by
        rw [← setLIntegral_congr (Ioo_ae_eq_Icc (μ := volume) (a := cos θ₂) (b := cos θ₁))]
    _ = ∫⁻ x in Ioo (cos θ₂) (cos θ₁), ENNReal.ofReal (1 / √(1 - x ^ 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        have hx1 : -1 < x := lt_of_le_of_lt (Real.neg_one_le_cos θ₂) hx.1
        have hx2 : x < 1 := lt_of_lt_of_le hx.2 (Real.cos_le_one θ₁)
        have hpos : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
        exact lintegral_inv_sq_above hpos
    _ = ENNReal.ofReal (arcsin (cos θ₁) - arcsin (cos θ₂)) :=
        lintegral_one_div_sqrt_one_sub_sq (Real.neg_one_le_cos θ₂) hcc (Real.cos_le_one θ₁)
    _ = ENNReal.ofReal (θ₂ - θ₁) := by rw [harcsin]

/-- The triply ideal triangle with vertices `-1`, `1`, `∞` has area `π`. -/
theorem volume_idealTriangle :
    volume {z : ℍ | z.re ∈ Icc (-1 : ℝ) 1 ∧ √(1 - z.re ^ 2) ≤ z.im} = ENNReal.ofReal π := by
  have h := volume_unitWedge (θ₁ := 0) (θ₂ := π) le_rfl Real.pi_pos.le le_rfl
  rw [Real.cos_zero, Real.cos_pi, sub_zero] at h
  exact h

/-- The triply ideal triangle, written with the Euclidean norm: `{|re z| ≤ 1, |z| ≥ 1}`. -/
theorem idealTriangle_eq_norm_form :
    {z : ℍ | z.re ∈ Icc (-1 : ℝ) 1 ∧ √(1 - z.re ^ 2) ≤ z.im}
      = {z : ℍ | z.re ∈ Icc (-1 : ℝ) 1 ∧ 1 ≤ ‖(z : ℂ)‖} := by
  ext z
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro hre
  have him : 0 < z.im := z.im_pos
  have hnorm : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have h1x : 0 ≤ 1 - z.re ^ 2 := by
    obtain ⟨hl, hr⟩ := hre
    nlinarith
  constructor
  · intro h
    have h2 : 1 - z.re ^ 2 ≤ z.im ^ 2 := by
      have := Real.sq_sqrt h1x
      nlinarith [Real.sqrt_nonneg (1 - z.re ^ 2)]
    have h3 : 1 ≤ ‖(z : ℂ)‖ ^ 2 := by rw [hnorm]; nlinarith
    nlinarith [norm_nonneg (z : ℂ)]
  · intro h
    have h3 : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
      rw [← hnorm]
      nlinarith [norm_nonneg (z : ℂ)]
    calc √(1 - z.re ^ 2) ≤ √(z.im ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = z.im := Real.sqrt_sq him.le

/-- **The triply ideal triangle has area `π`**, in the norm form of the region: the points
of the upper half plane with real part in `[-1, 1]` lying outside the unit circle. -/
theorem volume_idealTriangle_norm :
    volume {z : ℍ | z.re ∈ Icc (-1 : ℝ) 1 ∧ 1 ≤ ‖(z : ℂ)‖} = ENNReal.ofReal π := by
  rw [← idealTriangle_eq_norm_form]
  exact volume_idealTriangle

/-! ## Normalizing a wedge to the unit circle -/

/-- The affine map `z ↦ (z - x₀)/r` with `r > 0`, packaged as the element
`!![1/√r, -x₀/√r; 0, √r]` of `SL(2, ℝ)`. -/
noncomputable def scaleShiftSL2 (x₀ r : ℝ) (hr : 0 < r) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1 / √r, -x₀ / √r; 0, √r], by
    have hsr : (0 : ℝ) < √r := Real.sqrt_pos.mpr hr
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, one_div, inv_mul_cancel₀ hsr.ne']⟩

/-- The `SL(2, ℝ)`-action of `scaleShiftSL2` on the upper half plane is the affine map
`z ↦ (z - x₀)/r`. -/
theorem coe_scaleShiftSL2_smul (x₀ : ℝ) {r : ℝ} (hr : 0 < r) (z : UpperHalfPlane) :
    ((scaleShiftSL2 x₀ r hr • z : UpperHalfPlane) : ℂ)
      = ((z : ℂ) - (x₀ : ℂ)) / (r : ℂ) := by
  have hsr : (0 : ℝ) < √r := Real.sqrt_pos.mpr hr
  have hsq : ((√r : ℝ) : ℂ) * ((√r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le]
  have h00 : (scaleShiftSL2 x₀ r hr) 0 0 = 1 / √r := by simp [scaleShiftSL2]
  have h01 : (scaleShiftSL2 x₀ r hr) 0 1 = -x₀ / √r := by simp [scaleShiftSL2]
  have h10 : (scaleShiftSL2 x₀ r hr) 1 0 = 0 := by simp [scaleShiftSL2]
  have h11 : (scaleShiftSL2 x₀ r hr) 1 1 = √r := by simp [scaleShiftSL2]
  have hsrC : ((√r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsr.ne'
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply, h00, h01, h10, h11]
  rw [Complex.ofReal_zero, zero_mul, zero_add, div_eq_div_iff hsrC hrC]
  push_cast
  field_simp
  linear_combination ((x₀ : ℂ) - (z : ℂ)) * hsq

/-- Real part of the normalized point. -/
theorem scaleShiftSL2_smul_re (x₀ : ℝ) {r : ℝ} (hr : 0 < r) (z : UpperHalfPlane) :
    (scaleShiftSL2 x₀ r hr • z).re = (z.re - x₀) / r := by
  rw [← UpperHalfPlane.coe_re, coe_scaleShiftSL2_smul x₀ hr z, Complex.div_ofReal_re,
    Complex.sub_re, Complex.ofReal_re, UpperHalfPlane.coe_re]

/-- Imaginary part of the normalized point. -/
theorem scaleShiftSL2_smul_im (x₀ : ℝ) {r : ℝ} (hr : 0 < r) (z : UpperHalfPlane) :
    (scaleShiftSL2 x₀ r hr • z).im = z.im / r := by
  rw [← UpperHalfPlane.coe_im, coe_scaleShiftSL2_smul x₀ hr z, Complex.div_ofReal_im,
    Complex.sub_im, Complex.ofReal_im, UpperHalfPlane.coe_im, sub_zero]

/-! ## The general wedge -/

/-- The wedge over the circle of center `x₀` and radius `r` between the verticals at `x₁`
and `x₂` has area `arcsin ((x₂ - x₀)/r) - arcsin ((x₁ - x₀)/r)`. -/
theorem volume_wedge {x₀ r x₁ x₂ : ℝ} (hr : 0 < r) (h₁ : x₀ - r ≤ x₁) (h₁₂ : x₁ ≤ x₂)
    (h₂ : x₂ ≤ x₀ + r) :
    volume {z : ℍ | z.re ∈ Icc x₁ x₂ ∧ √(r ^ 2 - (z.re - x₀) ^ 2) ≤ z.im}
      = ENNReal.ofReal (arcsin ((x₂ - x₀) / r) - arcsin ((x₁ - x₀) / r)) := by
  have hdivle : ∀ p q : ℝ, p / r ≤ q / r ↔ p ≤ q := by
    intro p q
    constructor
    · intro h
      have h2 := mul_le_mul_of_nonneg_right h hr.le
      rwa [div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr.ne'] at h2
    · intro h
      have h2 := mul_le_mul_of_nonneg_right h (inv_pos.mpr hr).le
      rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at h2
  have hu₁l : -1 ≤ (x₁ - x₀) / r := by rw [le_div_iff₀ hr]; linarith
  have hu₂r : (x₂ - x₀) / r ≤ 1 := by rw [div_le_one hr]; linarith
  have hu₁₂ : (x₁ - x₀) / r ≤ (x₂ - x₀) / r := (hdivle _ _).mpr (by linarith)
  have hu₁r : (x₁ - x₀) / r ≤ 1 := hu₁₂.trans hu₂r
  have hu₂l : -1 ≤ (x₂ - x₀) / r := hu₁l.trans hu₁₂
  -- the unit wedge with the transported parameters
  have hθ : arccos ((x₂ - x₀) / r) ≤ arccos ((x₁ - x₀) / r) := Real.arccos_le_arccos hu₁₂
  have hU : volume {z : ℍ | z.re ∈ Icc ((x₁ - x₀) / r) ((x₂ - x₀) / r) ∧
      √(1 - z.re ^ 2) ≤ z.im}
      = ENNReal.ofReal (arcsin ((x₂ - x₀) / r) - arcsin ((x₁ - x₀) / r)) := by
    have h := volume_unitWedge (θ₁ := arccos ((x₂ - x₀) / r))
      (θ₂ := arccos ((x₁ - x₀) / r)) (Real.arccos_nonneg _) hθ (Real.arccos_le_pi _)
    rw [Real.cos_arccos hu₁l hu₁r, Real.cos_arccos hu₂l hu₂r] at h
    rw [h]
    congr 1
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
    ring
  -- transport by the affine normalization
  set g := scaleShiftSL2 x₀ r hr with hgdef
  have hres : ∀ z : UpperHalfPlane, (g • z).re = (z.re - x₀) / r :=
    fun z => scaleShiftSL2_smul_re x₀ hr z
  have hims : ∀ z : UpperHalfPlane, (g • z).im = z.im / r :=
    fun z => scaleShiftSL2_smul_im x₀ hr z
  have hsqrt : ∀ z : UpperHalfPlane, 0 ≤ r ^ 2 - (z.re - x₀) ^ 2 →
      √(1 - ((z.re - x₀) / r) ^ 2) = √(r ^ 2 - (z.re - x₀) ^ 2) / r := by
    intro z hnn
    have hid : 1 - ((z.re - x₀) / r) ^ 2 = (r ^ 2 - (z.re - x₀) ^ 2) / r ^ 2 := by
      field_simp
    rw [hid, Real.sqrt_div hnn, Real.sqrt_sq hr.le]
  have key : ∀ z : UpperHalfPlane,
      z ∈ {z : ℍ | z.re ∈ Icc x₁ x₂ ∧ √(r ^ 2 - (z.re - x₀) ^ 2) ≤ z.im} ↔
      g • z ∈ {z : ℍ | z.re ∈ Icc ((x₁ - x₀) / r) ((x₂ - x₀) / r) ∧
        √(1 - z.re ^ 2) ≤ z.im} := by
    intro z
    simp only [Set.mem_setOf_eq, Set.mem_Icc, hres z, hims z]
    constructor
    · rintro ⟨⟨hz1, hz2⟩, hz3⟩
      have hnn : 0 ≤ r ^ 2 - (z.re - x₀) ^ 2 := by
        have h4 := sq_le_sq' (by linarith : -r ≤ z.re - x₀) (by linarith : z.re - x₀ ≤ r)
        linarith
      refine ⟨⟨(hdivle _ _).mpr (by linarith), (hdivle _ _).mpr (by linarith)⟩, ?_⟩
      rw [hsqrt z hnn]
      exact (hdivle _ _).mpr hz3
    · rintro ⟨⟨hz1, hz2⟩, hz3⟩
      have hx1 : x₁ ≤ z.re := by have := (hdivle _ _).mp hz1; linarith
      have hx2 : z.re ≤ x₂ := by have := (hdivle _ _).mp hz2; linarith
      have hnn : 0 ≤ r ^ 2 - (z.re - x₀) ^ 2 := by
        have h4 := sq_le_sq' (by linarith : -r ≤ z.re - x₀) (by linarith : z.re - x₀ ≤ r)
        linarith
      rw [hsqrt z hnn] at hz3
      exact ⟨⟨hx1, hx2⟩, (hdivle _ _).mp hz3⟩
  have himg : g • {z : ℍ | z.re ∈ Icc x₁ x₂ ∧ √(r ^ 2 - (z.re - x₀) ^ 2) ≤ z.im}
      = {z : ℍ | z.re ∈ Icc ((x₁ - x₀) / r) ((x₂ - x₀) / r) ∧ √(1 - z.re ^ 2) ≤ z.im} := by
    ext w
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hw
      exact (key z).mp hz
    · intro hw
      exact Set.mem_smul_set.mpr ⟨g⁻¹ • w,
        (key _).mpr (by rw [smul_inv_smul]; exact hw), smul_inv_smul g w⟩
  calc volume {z : ℍ | z.re ∈ Icc x₁ x₂ ∧ √(r ^ 2 - (z.re - x₀) ^ 2) ≤ z.im}
      = volume (g • {z : ℍ | z.re ∈ Icc x₁ x₂ ∧ √(r ^ 2 - (z.re - x₀) ^ 2) ≤ z.im}) :=
        (volume_smul_sl2 g _).symm
    _ = volume {z : ℍ | z.re ∈ Icc ((x₁ - x₀) / r) ((x₂ - x₀) / r) ∧
          √(1 - z.re ^ 2) ≤ z.im} := by rw [himg]
    _ = ENNReal.ofReal (arcsin ((x₂ - x₀) / r) - arcsin ((x₁ - x₀) / r)) := hU

/-! ## Null carriers: vertical lines -/

/-- Vertical lines in `ℂ` are volume-null. -/
theorem volume_complex_re_line_eq_zero (r : ℝ) : volume {w : ℂ | w.re = r} = 0 := by
  have h : {w : ℂ | w.re = r} =
      Complex.measurableEquivRealProd ⁻¹' ({r} ×ˢ (Set.univ : Set ℝ)) := by
    ext w
    simp [Complex.measurableEquivRealProd_apply, Set.mem_prod]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton r).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- A subset of the upper half plane whose complex image is Lebesgue-null is null for the
hyperbolic measure: the latter is a density against the pullback of the Lebesgue measure. -/
theorem volume_eq_zero_of_image_coe_null {s : Set UpperHalfPlane}
    (h : volume (UpperHalfPlane.coe '' s) = 0) : volume s = 0 := by
  rw [UpperHalfPlane.volume_def]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [UpperHalfPlane.measurableEmbedding_coe.comap_apply]
  exact h

/-- Vertical lines in the upper half plane are volume-null. -/
theorem volume_vertLine (x : ℝ) : volume {τ : UpperHalfPlane | τ.re = x} = 0 := by
  apply volume_eq_zero_of_image_coe_null
  refine measure_mono_null ?_ (volume_complex_re_line_eq_zero x)
  rintro w ⟨τ, hτ, rfl⟩
  simpa using hτ

/-! ## The equality case of the height-log contraction -/

/-- The `cosh` of the hyperbolic distance in Euclidean coordinates. -/
theorem cosh_dist_expand (z w : UpperHalfPlane) :
    Real.cosh (dist z w)
      = 1 + ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) / (2 * z.im * w.im) := by
  rw [UpperHalfPlane.cosh_dist, dist_eq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The `cosh` of a log-height difference. -/
theorem cosh_log_div {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.cosh (Real.log u - Real.log v) = 1 + (u - v) ^ 2 / (2 * u * v) := by
  rw [Real.cosh_eq, neg_sub, Real.exp_sub, Real.exp_sub, Real.exp_log hu, Real.exp_log hv]
  field_simp
  ring

/-- The log of the height contracts under the hyperbolic distance. -/
theorem abs_log_im_le_dist (z w : UpperHalfPlane) :
    |Real.log z.im - Real.log w.im| ≤ dist z w := by
  have h1 : Real.cosh (Real.log z.im - Real.log w.im) ≤ Real.cosh (dist z w) := by
    rw [cosh_dist_expand, cosh_log_div z.im_pos w.im_pos]
    have hD : (0 : ℝ) < 2 * z.im * w.im := by positivity
    have hfrac : (z.im - w.im) ^ 2 / (2 * z.im * w.im)
        ≤ ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) / (2 * z.im * w.im) := by
      rw [div_le_div_iff₀ hD hD]
      nlinarith [mul_nonneg (sq_nonneg (z.re - w.re)) hD.le]
    linarith
  have h2 := Real.cosh_le_cosh.mp h1
  rwa [abs_of_nonneg dist_nonneg] at h2

/-- A geodesic segment between two points on a common vertical line stays on that line. -/
theorem geodSeg_subset_vertical {a b : UpperHalfPlane} (hre : a.re = b.re) :
    geodSeg a b ⊆ {τ : UpperHalfPlane | τ.re = a.re} := by
  intro z hz
  rw [mem_geodSeg] at hz
  have hle1 : |Real.log a.im - Real.log z.im| ≤ dist a z := abs_log_im_le_dist a z
  have hle2 : |Real.log z.im - Real.log b.im| ≤ dist z b := abs_log_im_le_dist z b
  have hab : dist a b = |Real.log a.im - Real.log b.im| := by
    rw [UpperHalfPlane.dist_of_re_eq hre, Real.dist_eq]
  have htri : |Real.log a.im - Real.log b.im|
      ≤ |Real.log a.im - Real.log z.im| + |Real.log z.im - Real.log b.im| :=
    abs_sub_le _ _ _
  have hEq : dist a z = |Real.log a.im - Real.log z.im| := by linarith
  have hcosh2 : Real.cosh (dist a z) = Real.cosh (Real.log a.im - Real.log z.im) := by
    rw [hEq, Real.cosh_abs]
  rw [cosh_dist_expand, cosh_log_div a.im_pos z.im_pos] at hcosh2
  have hD : (0 : ℝ) < 2 * a.im * z.im := by positivity
  have hfrac : ((a.re - z.re) ^ 2 + (a.im - z.im) ^ 2) / (2 * a.im * z.im)
      = (a.im - z.im) ^ 2 / (2 * a.im * z.im) := by linarith
  have hnum : (a.re - z.re) ^ 2 + (a.im - z.im) ^ 2 = (a.im - z.im) ^ 2 := by
    field_simp [hD.ne'] at hfrac
    linarith
  have hsq : (a.re - z.re) ^ 2 = 0 := by linarith
  have hzero : a.re - z.re = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  change z.re = a.re
  linarith

/-! ## Normalizing a real-centered circle to the imaginary axis -/

/-- Real-linear Möbius denominators with nonzero slope do not vanish on the upper half
plane. -/
theorem linear_denom_ne_zero (p q : ℝ) (hp : p ≠ 0) (z : UpperHalfPlane) :
    ((p : ℝ) : ℂ) * (z : ℂ) + ((q : ℝ) : ℂ) ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_im, UpperHalfPlane.coe_im, zero_mul, add_zero] at him
  rcases mul_eq_zero.mp him with h | h
  · exact hp h
  · exact z.im_pos.ne' h

/-- The Möbius map `z ↦ (z - (c + r))/(z - (c - r))` sending the real-centered circle
`|z - c| = r` to the imaginary axis, packaged in `SL(2, ℝ)`. -/
noncomputable def circleToImagSL2 (c r : ℝ) (hr : 0 < r) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1 / √(2 * r), -(c + r) / √(2 * r); 1 / √(2 * r), -(c - r) / √(2 * r)], by
    have hs : (0 : ℝ) < √(2 * r) := Real.sqrt_pos.mpr (by linarith)
    have hss : √(2 * r) * √(2 * r) = 2 * r := Real.mul_self_sqrt (by linarith)
    rw [Matrix.det_fin_two_of]
    field_simp
    linarith⟩

/-- The `SL(2, ℝ)`-action of `circleToImagSL2` on the upper half plane. -/
theorem coe_circleToImagSL2_smul (c r : ℝ) (hr : 0 < r) (z : UpperHalfPlane) :
    ((circleToImagSL2 c r hr • z : UpperHalfPlane) : ℂ)
      = ((z : ℂ) - (c : ℂ) - (r : ℂ)) / ((z : ℂ) - (c : ℂ) + (r : ℂ)) := by
  have hs : (0 : ℝ) < √(2 * r) := Real.sqrt_pos.mpr (by linarith)
  have h00 : (circleToImagSL2 c r hr) 0 0 = 1 / √(2 * r) := by
    simp [circleToImagSL2]
  have h01 : (circleToImagSL2 c r hr) 0 1 = -(c + r) / √(2 * r) := by
    simp [circleToImagSL2]
  have h10 : (circleToImagSL2 c r hr) 1 0 = 1 / √(2 * r) := by
    simp [circleToImagSL2]
  have h11 : (circleToImagSL2 c r hr) 1 1 = -(c - r) / √(2 * r) := by
    simp [circleToImagSL2]
  have hd1 : ((1 / √(2 * r) : ℝ) : ℂ) * (z : ℂ) + ((-(c - r) / √(2 * r) : ℝ) : ℂ) ≠ 0 :=
    linear_denom_ne_zero _ _ (one_div_ne_zero hs.ne') z
  have hd2 : ((z : ℂ) - (c : ℂ) + (r : ℂ)) ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.zero_im,
      UpperHalfPlane.coe_im, sub_zero, add_zero] at him
    exact z.im_pos.ne' him
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply, h00, h01, h10, h11]
  rw [div_eq_div_iff hd1 hd2]
  push_cast
  ring

/-- Points of the circle `|z - c| = r` are sent to the imaginary axis. -/
theorem circleToImagSL2_smul_re {c r : ℝ} (hr : 0 < r) {z : UpperHalfPlane}
    (hz : Complex.normSq ((z : ℂ) - (c : ℂ)) = r ^ 2) :
    (circleToImagSL2 c r hr • z).re = 0 := by
  have hz' : ((z : ℂ).re - c) ^ 2 + (z : ℂ).im ^ 2 = r ^ 2 := by
    rw [← hz, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hnum : ((z : ℂ) - (c : ℂ) - (r : ℂ)).re * ((z : ℂ) - (c : ℂ) + (r : ℂ)).re
      + ((z : ℂ) - (c : ℂ) - (r : ℂ)).im * ((z : ℂ) - (c : ℂ) + (r : ℂ)).im = 0 := by
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    linear_combination hz'
  rw [← UpperHalfPlane.coe_re, coe_circleToImagSL2_smul c r hr z, Complex.div_re,
    ← add_div, hnum, zero_div]

/-- Two points of distinct real parts are moved onto the imaginary axis by an explicit
`SL(2, ℝ)` element: the one normalizing the carrier circle of their geodesic. -/
theorem exists_smul_re_eq_zero {a b : UpperHalfPlane} (hre : a.re ≠ b.re) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, (g • a).re = 0 ∧ (g • b).re = 0 := by
  have hr : 0 < geodRadius a b := geodRadius_pos a b
  have expand : ∀ w : UpperHalfPlane,
      Complex.normSq ((w : ℂ) - ((geodCenter a b : ℝ) : ℂ))
        = (w.re - geodCenter a b) ^ 2 + w.im ^ 2 := by
    intro w
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have ha' : Complex.normSq ((a : ℂ) - ((geodCenter a b : ℝ) : ℂ)) = geodRadius a b ^ 2 := by
    rw [geodRadius, Complex.sq_norm]
  have hcc : geodCenter a b * (2 * (a.re - b.re))
      = Complex.normSq (a : ℂ) - Complex.normSq (b : ℂ) := by
    rw [geodCenter]
    field_simp [sub_ne_zero.mpr hre]
  have expand0 : ∀ w : UpperHalfPlane,
      Complex.normSq (w : ℂ) = w.re ^ 2 + w.im ^ 2 := by
    intro w
    rw [Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hb' : Complex.normSq ((b : ℂ) - ((geodCenter a b : ℝ) : ℂ)) = geodRadius a b ^ 2 := by
    rw [expand b]
    rw [expand a] at ha'
    rw [expand0 a, expand0 b] at hcc
    linear_combination ha' + hcc
  exact ⟨circleToImagSL2 (geodCenter a b) (geodRadius a b) hr,
    circleToImagSL2_smul_re hr ha', circleToImagSL2_smul_re hr hb'⟩

/-! ## Geodesic segments are null -/

/-- Geodesic segments are hyperbolic-area null: they are carried by a vertical line or by a
circle centered on the real axis. -/
theorem volume_geodSeg_eq_zero (a b : UpperHalfPlane) : volume (geodSeg a b) = 0 := by
  by_cases hre : a.re = b.re
  · exact measure_mono_null (geodSeg_subset_vertical hre) (volume_vertLine a.re)
  · obtain ⟨g, hga, hgb⟩ := exists_smul_re_eq_zero hre
    have himg : g • geodSeg a b = geodSeg (g • a) (g • b) := by
      rw [← Set.image_smul]
      exact smul_geodSeg g a b
    have h0 : volume (geodSeg (g • a) (g • b)) = 0 :=
      measure_mono_null (geodSeg_subset_vertical (hga.trans hgb.symm))
        (volume_vertLine (g • a).re)
    calc volume (geodSeg a b) = volume (g • geodSeg a b) := (volume_smul_sl2 g _).symm
      _ = 0 := by rw [himg]; exact h0

/-! ## Compactness -/

/-- Geodesic triangles are compact: the continuous image of the compact parameter square
under the joint geodesic interpolation. -/
theorem isCompact_hyperbolicTriangle (v₁ v₂ v₃ : UpperHalfPlane) :
    IsCompact (hyperbolicTriangle v₁ v₂ v₃) := by
  have himg : hyperbolicTriangle v₁ v₂ v₃
      = (fun p : ℝ × ℝ => geodInterp v₁ (geodInterp v₂ v₃ p.1) p.2)
        '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hzw⟩ := mem_geodCone.mp hz
      rw [geodSeg_eq_image_geodInterp] at hw
      obtain ⟨s, hs, rfl⟩ := hw
      rw [geodSeg_eq_image_geodInterp] at hzw
      obtain ⟨t, ht, rfl⟩ := hzw
      exact ⟨(s, t), Set.mk_mem_prod hs ht, rfl⟩
    · rintro ⟨⟨s, t⟩, hp, rfl⟩
      exact mem_geodCone.mpr ⟨geodInterp v₂ v₃ s, geodInterp_mem_geodSeg v₂ v₃ hp.1,
        geodInterp_mem_geodSeg v₁ _ hp.2⟩
  rw [himg]
  exact (isCompact_Icc.prod isCompact_Icc).image
    (continuous_geodInterp.comp (continuous_const.prodMk
      ((continuous_geodInterp.comp (continuous_const.prodMk
        (continuous_const.prodMk continuous_fst))).prodMk continuous_snd)))

/-! ## Real and complex utilities -/

/-- Squared Euclidean distance of two coerced points in coordinates. -/
theorem dist_coe_sq (τ a : UpperHalfPlane) :
    dist (τ : ℂ) (a : ℂ) ^ 2 = (τ.re - a.re) ^ 2 + (τ.im - a.im) ^ 2 := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- Square-root comparison: `√A ≤ y ↔ A ≤ y²` for nonnegative data. -/
theorem sqrt_le_iff {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y) : √A ≤ y ↔ A ≤ y ^ 2 := by
  constructor
  · intro h
    calc A = √A ^ 2 := (Real.sq_sqrt hA).symm
      _ ≤ y ^ 2 := by nlinarith [Real.sqrt_nonneg A]
  · intro h
    calc √A ≤ √(y ^ 2) := Real.sqrt_le_sqrt h
      _ = y := Real.sqrt_sq hy

/-- The argument of a point of the upper semicircle of radius `r`. -/
theorem arg_circle_pos {a b r : ℝ} (hb : 0 < b) (hr : 0 < r) (h : a ^ 2 + b ^ 2 = r ^ 2) :
    Complex.arg ((a : ℂ) + (b : ℂ) * Complex.I) = π / 2 - Real.arcsin (a / r) := by
  have ha2 : a ^ 2 ≤ r ^ 2 := by nlinarith
  have ha1 : -1 ≤ a / r := by rw [le_div_iff₀ hr]; nlinarith
  have ha1' : a / r ≤ 1 := by rw [div_le_one hr]; nlinarith
  set θ := π / 2 - Real.arcsin (a / r) with hθdef
  have hθmem : θ ∈ Set.Ioc (-π) π := by
    have h1 := Real.arcsin_le_pi_div_two (a / r)
    have h2 := Real.neg_pi_div_two_le_arcsin (a / r)
    constructor
    · rw [hθdef]; linarith [Real.pi_pos]
    · rw [hθdef]; linarith
  have hcos : Real.cos θ = a / r := by
    rw [hθdef, Real.cos_pi_div_two_sub, Real.sin_arcsin ha1 ha1']
  have hsin : Real.sin θ = b / r := by
    rw [hθdef, Real.sin_pi_div_two_sub, Real.cos_arcsin]
    have hbr : 1 - (a / r) ^ 2 = (b / r) ^ 2 := by
      field_simp
      linarith
    rw [hbr, Real.sqrt_sq (by positivity)]
  have hpt : (a : ℂ) + (b : ℂ) * Complex.I
      = (r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) := by
    rw [hcos, hsin]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.add_re, Complex.mul_re]
      field_simp
      ring
  rw [hpt, Complex.arg_real_mul _ hr, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_cos_add_sin_mul_I hθmem]

/-- The absolute argument of an off-axis point of the circle of radius `r` about `0`. -/
theorem abs_arg_circle {a b r : ℝ} (hb : b ≠ 0) (hr : 0 < r) (h : a ^ 2 + b ^ 2 = r ^ 2) :
    |Complex.arg ((a : ℂ) + (b : ℂ) * Complex.I)| = π / 2 - Real.arcsin (a / r) := by
  have hnn : 0 ≤ π / 2 - Real.arcsin (a / r) := by
    linarith [Real.arcsin_le_pi_div_two (a / r)]
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hkey := arg_circle_pos (a := a) (b := -b) (r := r)
      (by linarith) hr (by nlinarith)
    rw [Complex.ofReal_neg] at hkey
    have hconj : (a : ℂ) + (b : ℂ) * Complex.I
        = (starRingEnd ℂ) ((a : ℂ) + -(b : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    have hne_pi : Complex.arg ((a : ℂ) + -(b : ℂ) * Complex.I) ≠ π := by
      intro hpi
      rw [hkey] at hpi
      have harc : Real.arcsin (a / r) = -(π / 2) := by linarith
      have hsin := congrArg Real.sin harc
      rw [Real.sin_arcsin (by rw [le_div_iff₀ hr]; nlinarith)
        (by rw [div_le_one hr]; nlinarith)] at hsin
      rw [Real.sin_neg, Real.sin_pi_div_two] at hsin
      have haR : a = -r := by
        have := congrArg (· * r) hsin
        field_simp at this
        linarith
      nlinarith
    rw [hconj, Complex.arg_conj, if_neg hne_pi, abs_neg, hkey, abs_of_nonneg hnn]
  · rw [arg_circle_pos hbpos hr h, abs_of_nonneg hnn]

/-! ## The carrier circle through an axis point and an off-axis point -/

/-- Center-radius relations for the geodesic circle through an axis point `A` and a point
`P` off the vertical axis: the squared radius from the axis point, the on-circle relation
for `P`, and the resulting linear formula for the center. -/
theorem axis_apex_rel {A P : UpperHalfPlane} (hA : A.re = 0) (hne : A.re ≠ P.re) :
    geodRadius A P ^ 2 = geodCenter A P ^ 2 + A.im ^ 2 ∧
      (P.re - geodCenter A P) ^ 2 + P.im ^ 2 = geodRadius A P ^ 2 ∧
      2 * geodCenter A P * P.re = P.re ^ 2 + P.im ^ 2 - A.im ^ 2 := by
  have h1 : geodRadius A P ^ 2 = geodCenter A P ^ 2 + A.im ^ 2 := by
    rw [geodRadius, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.ofReal_re,
      Complex.ofReal_im, hA, sub_zero]
    ring
  have h2 : (P.re - geodCenter A P) ^ 2 + P.im ^ 2 = geodRadius A P ^ 2 := by
    have hn := norm_sub_geodCenter hne
    have hsq := congrArg (· ^ 2) hn
    simp only at hsq
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hsq
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero] at hsq
    rw [← hsq]
    ring
  refine ⟨h1, h2, ?_⟩
  nlinarith [h1, h2]

/-- The geodesic center is the unique real point equidistant from the two endpoints. -/
theorem geodCenter_unique {a b : UpperHalfPlane} (hre : a.re ≠ b.re) {x : ℝ}
    (hx : ‖(a : ℂ) - (x : ℂ)‖ = ‖(b : ℂ) - (x : ℂ)‖) : x = geodCenter a b := by
  have hsq := congrArg (· ^ 2) hx
  simp only at hsq
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at hsq
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hsq
  rw [geodCenter, Complex.normSq_apply, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have hden : 2 * (a.re - b.re) ≠ 0 := by
    intro h0
    apply hre
    have h1 : a.re - b.re = 0 := by linarith
    linarith
  rw [eq_div_iff hden]
  nlinarith [hsq]

/-- The Euclidean abscissa strictly decreases along the arc-length coordinate. -/
theorem circ_x_lt {c r : ℝ} (hr : 0 < r) {u v : ℝ} (huv : u < v) :
    c + r * Real.cos (circAngle v) < c + r * Real.cos (circAngle u) := by
  have hmono : circAngle u < circAngle v := by
    unfold circAngle
    have := Real.arctan_strictMono (Real.exp_lt_exp.mpr huv)
    linarith
  have hu := circAngle_mem u
  have hv := circAngle_mem v
  have hcos : Real.cos (circAngle v) < Real.cos (circAngle u) :=
    Real.strictAntiOn_cos ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hv.2.le⟩ hmono
  nlinarith

/-- A point of the carrier circle with abscissa between the endpoint abscissas lies on the
geodesic segment. -/
theorem mem_geodSeg_of_on_circle {a b ζ : UpperHalfPlane} (hre : a.re ≠ b.re)
    (hζ : ‖(ζ : ℂ) - (geodCenter a b : ℂ)‖ = geodRadius a b)
    (h1 : min a.re b.re ≤ ζ.re) (h2 : ζ.re ≤ max a.re b.re) : ζ ∈ geodSeg a b := by
  set c := geodCenter a b with hc
  set r := geodRadius a b with hrdef
  have hr : 0 < r := geodRadius_pos a b
  have ha : circPoint c r (circCoord c a) hr = a := circPoint_circCoord hr rfl
  have hb : circPoint c r (circCoord c b) hr = b :=
    circPoint_circCoord hr (norm_sub_geodCenter hre)
  have hz : circPoint c r (circCoord c ζ) hr = ζ := circPoint_circCoord hr hζ
  set ua := circCoord c a with hua
  set ub := circCoord c b with hub
  set uz := circCoord c ζ with huz
  have hare : a.re = c + r * Real.cos (circAngle ua) := by
    conv_lhs => rw [← ha]
    rw [circPoint_re]
  have hbre : b.re = c + r * Real.cos (circAngle ub) := by
    conv_lhs => rw [← hb]
    rw [circPoint_re]
  have hzre : ζ.re = c + r * Real.cos (circAngle uz) := by
    conv_lhs => rw [← hz]
    rw [circPoint_re]
  have key : ∀ s t : ℝ, c + r * Real.cos (circAngle s) ≤ c + r * Real.cos (circAngle t)
      → t ≤ s := by
    intro s t hst
    by_contra hlt
    exact absurd hst (not_le.mpr (circ_x_lt hr (not_le.mp hlt)))
  have key_le : ∀ {u v : ℝ}, u ≤ v
      → c + r * Real.cos (circAngle v) ≤ c + r * Real.cos (circAngle u) := by
    intro u v huv
    have hcos := Real.strictAntiOn_cos.antitoneOn
      ⟨(circAngle_mem u).1.le, (circAngle_mem u).2.le⟩
      ⟨(circAngle_mem v).1.le, (circAngle_mem v).2.le⟩ (circAngle_mono huv)
    nlinarith
  have hdist : dist a ζ + dist ζ b = dist a b := by
    rw [← ha, ← hb, ← hz, dist_circPoint, dist_circPoint, dist_circPoint]
    rcases le_total ua ub with hab | hab
    · have hxba : b.re ≤ a.re := by
        rw [hare, hbre]
        exact key_le hab
      rw [min_eq_right hxba] at h1
      rw [max_eq_left hxba] at h2
      have hu1 : ua ≤ uz := key uz ua (by rw [← hzre, ← hare]; exact h2)
      have hu2 : uz ≤ ub := key ub uz (by rw [← hbre, ← hzre]; exact h1)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      ring
    · have hxab : a.re ≤ b.re := by
        rw [hare, hbre]
        exact key_le hab
      rw [min_eq_left hxab] at h1
      rw [max_eq_right hxab] at h2
      have hu1 : ub ≤ uz := key uz ub (by rw [← hzre, ← hbre]; exact h2)
      have hu2 : uz ≤ ua := key ua uz (by rw [← hare, ← hzre]; exact h1)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      ring
  exact hdist

/-! ## Half-spaces as distance comparisons -/

/-- The point at height `2r` over the center `c`. -/
noncomputable def topPt (c r : ℝ) (hr : 0 < r) : UpperHalfPlane :=
  UpperHalfPlane.mk ⟨c, 2 * r⟩ (by change (0 : ℝ) < 2 * r; linarith)

/-- The point at height `r/2` over the center `c`. -/
noncomputable def botPt (c r : ℝ) (hr : 0 < r) : UpperHalfPlane :=
  UpperHalfPlane.mk ⟨c, r / 2⟩ (by change (0 : ℝ) < r / 2; linarith)

/-- The top comparison point lies on the vertical through the center `c`. -/
theorem topPt_re (c r : ℝ) (hr : 0 < r) : (topPt c r hr).re = c := rfl

/-- The top comparison point sits at height `2r`, above the circle of radius `r`. -/
theorem topPt_im (c r : ℝ) (hr : 0 < r) : (topPt c r hr).im = 2 * r := rfl

/-- The bottom comparison point lies on the vertical through the center `c`. -/
theorem botPt_re (c r : ℝ) (hr : 0 < r) : (botPt c r hr).re = c := rfl

/-- The bottom comparison point sits at height `r / 2`, inside the circle of radius `r`. -/
theorem botPt_im (c r : ℝ) (hr : 0 < r) : (botPt c r hr).im = r / 2 := rfl

/-- The point at height `1` over the abscissa `x`. -/
noncomputable def ptAt (x : ℝ) : UpperHalfPlane :=
  UpperHalfPlane.mk ⟨x, 1⟩ (by change (0 : ℝ) < 1; norm_num)

/-- The point `ptAt x` lies on the vertical through the abscissa `x`. -/
theorem ptAt_re (x : ℝ) : (ptAt x).re = x := rfl

/-- The point `ptAt x` sits at height `1`. -/
theorem ptAt_im (x : ℝ) : (ptAt x).im = 1 := rfl

/-- The exterior of the circle `|z - c| = r` is the half-space of points closer to the top
comparison point than to the bottom one. -/
theorem ext_circle_iff {c r : ℝ} (hr : 0 < r) (τ : UpperHalfPlane) :
    dist τ (topPt c r hr) ≤ dist τ (botPt c r hr)
      ↔ r ^ 2 ≤ (τ.re - c) ^ 2 + τ.im ^ 2 := by
  rw [dist_le_dist_iff_quadratic, dist_coe_sq, dist_coe_sq,
    topPt_re, topPt_im, botPt_re, botPt_im]
  constructor
  · intro h
    nlinarith [h, hr]
  · intro h
    nlinarith [h, hr]

/-- The closed disc `|z - c| ≤ r` is the half-space of points closer to the bottom
comparison point than to the top one. -/
theorem int_circle_iff {c r : ℝ} (hr : 0 < r) (τ : UpperHalfPlane) :
    dist τ (botPt c r hr) ≤ dist τ (topPt c r hr)
      ↔ (τ.re - c) ^ 2 + τ.im ^ 2 ≤ r ^ 2 := by
  rw [dist_le_dist_iff_quadratic, dist_coe_sq, dist_coe_sq,
    topPt_re, topPt_im, botPt_re, botPt_im]
  constructor
  · intro h
    nlinarith [h, hr]
  · intro h
    nlinarith [h, hr]

/-- The left half-plane `re ≤ m` as a distance comparison. -/
theorem strip_le_iff (m : ℝ) (τ : UpperHalfPlane) :
    dist τ (ptAt (m - 1)) ≤ dist τ (ptAt (m + 1)) ↔ τ.re ≤ m := by
  have h := setOf_dist_le_eq_of_im_eq (a := ptAt (m - 1)) (b := ptAt (m + 1))
    rfl (by rw [ptAt_re, ptAt_re]; linarith)
  have h2 := Set.ext_iff.mp h τ
  simp only [Set.mem_setOf_eq, ptAt_re] at h2
  rw [h2, show (m - 1 + (m + 1)) / 2 = m by ring]

/-- The right half-plane `m ≤ re` as a distance comparison. -/
theorem strip_ge_iff (m : ℝ) (τ : UpperHalfPlane) :
    dist τ (ptAt (m + 1)) ≤ dist τ (ptAt (m - 1)) ↔ m ≤ τ.re := by
  have h := setOf_dist_le_eq_of_im_eq' (a := ptAt (m + 1)) (b := ptAt (m - 1))
    rfl (by rw [ptAt_re, ptAt_re]; linarith)
  have h2 := Set.ext_iff.mp h τ
  simp only [Set.mem_setOf_eq, ptAt_re] at h2
  rw [h2, show (m + 1 + (m - 1)) / 2 = m by ring]

/-- A geodesic cone lies in every distance-comparison half-space containing its apex and
the two ends of its base segment. -/
theorem geodCone_subset_dist_le {P U L p q : UpperHalfPlane}
    (hP : dist P p ≤ dist P q) (hU : dist U p ≤ dist U q) (hL : dist L p ≤ dist L q) :
    geodCone P (geodSeg U L) ⊆ {τ : UpperHalfPlane | dist τ p ≤ dist τ q} := by
  intro z hz
  obtain ⟨w, hw, hzw⟩ := mem_geodCone.mp hz
  have hwH : dist w p ≤ dist w q := geodSeg_subset_setOf_dist_le hU hL hw
  exact geodSeg_subset_setOf_dist_le hP hwH hzw

/-! ## Frame values in the normalized configuration -/

/-- The argument of a quotient equals the argument of the numerator times the conjugated
denominator. -/
theorem arg_div_mul_conj {z w : ℂ} (hw : w ≠ 0) :
    Complex.arg (z / w) = Complex.arg (z * (starRingEnd ℂ) w) := by
  have hns : (0 : ℝ) < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hkey : z / w = (((Complex.normSq w)⁻¹ : ℝ) : ℂ) * (z * (starRingEnd ℂ) w) := by
    rw [div_eq_mul_inv, Complex.inv_def]
    push_cast
    ring
  rw [hkey, Complex.arg_real_mul _ (inv_pos.mpr hns)]

/-- The frame value between two axis points is real. -/
theorem discChart_axis {z w : UpperHalfPlane} (hz : z.re = 0) (hw : w.re = 0) :
    discChart z w = (((w.im - z.im) / (w.im + z.im) : ℝ) : ℂ) := by
  have hnum : (w : ℂ) - (z : ℂ) = Complex.I * ((w.im - z.im : ℝ) : ℂ) := by
    rw [coe_of_re_zero hz, coe_of_re_zero hw]
    push_cast
    ring
  have hden : (w : ℂ) - (starRingEnd ℂ) (z : ℂ)
      = Complex.I * ((w.im + z.im : ℝ) : ℂ) := by
    rw [coe_of_re_zero hw, conj_coe, hz]
    push_cast
    ring
  rw [discChart_eq, hnum, hden, mul_div_mul_left _ _ Complex.I_ne_zero,
    ← Complex.ofReal_div]

/-- The conjugated-denominator product for the frame at an axis point toward `P`. -/
theorem base_prod {A P : UpperHalfPlane} (hA : A.re = 0) (hne : A.re ≠ P.re) :
    ((P : ℂ) - (A : ℂ)) * (starRingEnd ℂ) ((P : ℂ) - (starRingEnd ℂ) (A : ℂ))
      = ((2 * P.re : ℝ) : ℂ)
        * (((geodCenter A P : ℝ) : ℂ) + ((-A.im : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨-, -, hrel⟩ := axis_apex_rel hA hne
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, hA, mul_zero, zero_mul, mul_one, sub_zero, add_zero,
      zero_add, sub_neg_eq_add]
    nlinarith [hrel]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, hA, mul_zero, zero_mul, mul_one, sub_zero, add_zero,
      zero_add, sub_neg_eq_add]
    ring

/-- The argument of the frame at an axis point toward `P`, `P` to the right. -/
theorem arg_discChart_base {A P : UpperHalfPlane} (hA : A.re = 0) (hP : 0 < P.re) :
    Complex.arg (discChart A P)
      = Complex.arg (((geodCenter A P : ℝ) : ℂ) + ((-A.im : ℝ) : ℂ) * Complex.I) := by
  have hne : A.re ≠ P.re := by rw [hA]; exact ne_of_lt hP
  rw [discChart_eq, arg_div_mul_conj (sub_conj_ne_zero A P), base_prod hA hne,
    Complex.arg_real_mul _ (by linarith)]

/-- The argument of the negated frame at an axis point toward `P`. -/
theorem arg_neg_discChart_base {A P : UpperHalfPlane} (hA : A.re = 0) (hP : 0 < P.re) :
    Complex.arg (-discChart A P)
      = Complex.arg (((-geodCenter A P : ℝ) : ℂ) + ((A.im : ℝ) : ℂ) * Complex.I) := by
  have hne : A.re ≠ P.re := by rw [hA]; exact ne_of_lt hP
  have h1 : -discChart A P
      = ((A : ℂ) - (P : ℂ)) / ((P : ℂ) - (starRingEnd ℂ) (A : ℂ)) := by
    rw [discChart_eq, ← neg_div, neg_sub]
  have h2 : ((A : ℂ) - (P : ℂ)) * (starRingEnd ℂ) ((P : ℂ) - (starRingEnd ℂ) (A : ℂ))
      = ((2 * P.re : ℝ) : ℂ)
        * (((-geodCenter A P : ℝ) : ℂ) + ((A.im : ℝ) : ℂ) * Complex.I) := by
    have hb := base_prod hA hne
    push_cast at hb ⊢
    linear_combination -hb
  rw [h1, arg_div_mul_conj (sub_conj_ne_zero A P), h2,
    Complex.arg_real_mul _ (by linarith)]

/-- The frame at `P` toward an axis point, as a positive multiple of the tangent vector
`(P.re - c) + P.im · I` of the carrier circle. -/
theorem discChart_apex {A P : UpperHalfPlane} (hA : A.re = 0) (hP : 0 < P.re) :
    ∃ k : ℝ, 0 < k ∧ discChart P A
      = ((k : ℝ) : ℂ)
        * (((P.re - geodCenter A P : ℝ) : ℂ) + ((P.im : ℝ) : ℂ) * Complex.I) := by
  have hne : A.re ≠ P.re := by rw [hA]; exact ne_of_lt hP
  obtain ⟨-, -, hrel⟩ := axis_apex_rel hA hne
  set D : ℂ := (A : ℂ) - (starRingEnd ℂ) (P : ℂ) with hD
  have hDne : D ≠ 0 := sub_conj_ne_zero P A
  have hns : (0 : ℝ) < Complex.normSq D := Complex.normSq_pos.mpr hDne
  have hprod : ((A : ℂ) - (P : ℂ)) * (starRingEnd ℂ) D
      = ((2 * P.re : ℝ) : ℂ)
        * (((P.re - geodCenter A P : ℝ) : ℂ) + ((P.im : ℝ) : ℂ) * Complex.I) := by
    rw [hD]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im, hA, mul_zero, zero_mul, mul_one, sub_zero, zero_sub,
        add_zero, zero_add, sub_neg_eq_add]
      nlinarith [hrel]
    · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im, hA, mul_zero, zero_mul, mul_one, sub_zero, zero_sub,
        add_zero, zero_add, sub_neg_eq_add]
      ring
  refine ⟨2 * P.re / Complex.normSq D, div_pos (by linarith) hns, ?_⟩
  have hmc : D * (starRingEnd ℂ) D = ((Complex.normSq D : ℝ) : ℂ) := Complex.mul_conj D
  have hnsC : ((Complex.normSq D : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hns.ne'
  rw [discChart_eq, ← hD, div_eq_iff hDne]
  push_cast at hprod hmc ⊢
  field_simp
  linear_combination D * hprod - ((A : ℂ) - (P : ℂ)) * hmc

/-! ## The three angles of the normalized triangle -/

/-- The angle at an axis vertex toward a lower axis point and a point to the right. -/
theorem sectorAngle_axis_down {A B P : UpperHalfPlane} (hA : A.re = 0) (hB : B.re = 0)
    (hP : 0 < P.re) (him : B.im < A.im) :
    sectorAngle A B P = π / 2 + Real.arcsin (geodCenter A P / geodRadius A P) := by
  have hne : A.re ≠ P.re := by rw [hA]; exact ne_of_lt hP
  obtain ⟨h1, -, -⟩ := axis_apex_rel hA hne
  have hr : 0 < geodRadius A P := geodRadius_pos A P
  have hs : (B.im - A.im) / (B.im + A.im) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by linarith [A.im_pos, B.im_pos])
  unfold sectorAngle
  rw [discChart_axis hA hB]
  have hquot : discChart A P / (((B.im - A.im) / (B.im + A.im) : ℝ) : ℂ)
      = (((-((B.im - A.im) / (B.im + A.im)))⁻¹ : ℝ) : ℂ) * (-discChart A P) := by
    have hsne : ((B.im - A.im) / (B.im + A.im) : ℝ) ≠ 0 := ne_of_lt hs
    push_cast
    field_simp
  rw [hquot, Complex.arg_real_mul _ (inv_pos.mpr (neg_pos.mpr hs)),
    arg_neg_discChart_base hA hP,
    abs_arg_circle A.im_pos.ne' hr (by nlinarith [h1]), neg_div, Real.arcsin_neg]
  ring

/-- The angle at an axis vertex toward a higher axis point and a point to the right. -/
theorem sectorAngle_axis_up {A B P : UpperHalfPlane} (hA : A.re = 0) (hB : B.re = 0)
    (hP : 0 < P.re) (him : A.im < B.im) :
    sectorAngle A B P = π / 2 - Real.arcsin (geodCenter A P / geodRadius A P) := by
  have hne : A.re ≠ P.re := by rw [hA]; exact ne_of_lt hP
  obtain ⟨h1, -, -⟩ := axis_apex_rel hA hne
  have hr : 0 < geodRadius A P := geodRadius_pos A P
  have hs : 0 < (B.im - A.im) / (B.im + A.im) :=
    div_pos (by linarith) (by linarith [A.im_pos, B.im_pos])
  unfold sectorAngle
  rw [discChart_axis hA hB]
  have hquot : discChart A P / (((B.im - A.im) / (B.im + A.im) : ℝ) : ℂ)
      = (((((B.im - A.im) / (B.im + A.im)))⁻¹ : ℝ) : ℂ) * discChart A P := by
    have hsne : ((B.im - A.im) / (B.im + A.im) : ℝ) ≠ 0 := ne_of_gt hs
    push_cast
    field_simp
  have hbne : (-A.im : ℝ) ≠ 0 := neg_ne_zero.mpr A.im_pos.ne'
  rw [hquot, Complex.arg_real_mul _ (inv_pos.mpr hs), arg_discChart_base hA hP,
    abs_arg_circle hbne hr (by nlinarith [h1])]

/-- The angle at the apex between the two axis vertices, as an arcsine difference. -/
theorem sectorAngle_apex {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) (him : L.im < U.im) :
    sectorAngle P U L
      = Real.arcsin ((P.re - geodCenter U P) / geodRadius U P)
        - Real.arcsin ((P.re - geodCenter L P) / geodRadius L P) := by
  have hneU : U.re ≠ P.re := by rw [hU]; exact ne_of_lt hP
  have hneL : L.re ≠ P.re := by rw [hL]; exact ne_of_lt hP
  obtain ⟨-, hU2, hUrel⟩ := axis_apex_rel hU hneU
  obtain ⟨-, hL2, hLrel⟩ := axis_apex_rel hL hneL
  have hrU : 0 < geodRadius U P := geodRadius_pos U P
  have hrL : 0 < geodRadius L P := geodRadius_pos L P
  obtain ⟨kU, hkU, hdU⟩ := discChart_apex hU hP
  obtain ⟨kL, hkL, hdL⟩ := discChart_apex hL hP
  set ζU : ℂ := ((P.re - geodCenter U P : ℝ) : ℂ) + ((P.im : ℝ) : ℂ) * Complex.I with hζU
  set ζL : ℂ := ((P.re - geodCenter L P : ℝ) : ℂ) + ((P.im : ℝ) : ℂ) * Complex.I with hζL
  have hζUim : ζU.im = P.im := by
    rw [hζU]
    simp
  have hζLim : ζL.im = P.im := by
    rw [hζL]
    simp
  have hζUne : ζU ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [hζUim, Complex.zero_im] at this
    exact P.im_pos.ne' this
  have hζLne : ζL ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [hζLim, Complex.zero_im] at this
    exact P.im_pos.ne' this
  have hcc : geodCenter U P < geodCenter L P := by
    nlinarith [hUrel, hLrel, him, U.im_pos, L.im_pos]
  unfold sectorAngle
  have hquot : discChart P L / discChart P U = ((kL / kU : ℝ) : ℂ) * (ζL / ζU) := by
    rw [hdL, hdU, mul_div_mul_comm, ← Complex.ofReal_div]
  rw [hquot, Complex.arg_real_mul _ (div_pos hkL hkU)]
  have hβim : 0 ≤ (ζL / ζU).im := by
    rw [Complex.div_im, hζLim, hζUim]
    have hre : ζU.re = P.re - geodCenter U P := by rw [hζU]; simp
    have hre' : ζL.re = P.re - geodCenter L P := by rw [hζL]; simp
    rw [hre, hre']
    have hns : (0 : ℝ) < Complex.normSq ζU := Complex.normSq_pos.mpr hζUne
    rw [div_sub_div_same, div_nonneg_iff]
    left
    constructor
    · nlinarith [P.im_pos]
    · exact hns.le
  have hprod : ζU * (ζL / ζU) = ζL := mul_div_cancel₀ ζL hζUne
  have habs := abs_arg_mul hζUne (div_ne_zero hζLne hζUne)
    (by rw [hζUim]; exact P.im_pos.le) hβim
    (by rw [hprod, hζLim]; exact P.im_pos.le)
    (by
      rintro ⟨hπ, -⟩
      have := Complex.arg_eq_pi_iff.mp hπ
      rw [hζUim] at this
      exact P.im_pos.ne' this.2)
  rw [hprod] at habs
  have hUabs : |Complex.arg ζU|
      = π / 2 - Real.arcsin ((P.re - geodCenter U P) / geodRadius U P) := by
    rw [hζU]
    exact abs_arg_circle P.im_pos.ne' hrU (by nlinarith [hU2])
  have hLabs : |Complex.arg ζL|
      = π / 2 - Real.arcsin ((P.re - geodCenter L P) / geodRadius L P) := by
    rw [hζL]
    exact abs_arg_circle P.im_pos.ne' hrL (by nlinarith [hL2])
  rw [hUabs, hLabs] at habs
  linarith

/-! ## The normalized triangle as a region -/

/-- The cone over the vertical base is contained in the region cut out by the strip and the
two carrier circles. -/
theorem cone_subset_region {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) (him : L.im < U.im) :
    geodCone P (geodSeg U L)
      ⊆ {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
          ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
          ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2} := by
  have hneU : U.re ≠ P.re := by rw [hU]; exact ne_of_lt hP
  have hneL : L.re ≠ P.re := by rw [hL]; exact ne_of_lt hP
  obtain ⟨hU1, hU2, hUrel⟩ := axis_apex_rel hU hneU
  obtain ⟨hL1, hL2, hLrel⟩ := axis_apex_rel hL hneL
  have hru : 0 < geodRadius U P := geodRadius_pos U P
  have hrl : 0 < geodRadius L P := geodRadius_pos L P
  intro z hz
  have hs1 : 0 ≤ z.re := by
    have hmem := geodCone_subset_dist_le
      ((strip_ge_iff 0 P).mpr hP.le)
      ((strip_ge_iff 0 U).mpr (le_of_eq hU.symm))
      ((strip_ge_iff 0 L).mpr (le_of_eq hL.symm)) hz
    exact (strip_ge_iff 0 z).mp hmem
  have hs2 : z.re ≤ P.re := by
    have hmem := geodCone_subset_dist_le
      ((strip_le_iff P.re P).mpr le_rfl)
      ((strip_le_iff P.re U).mpr (by rw [hU]; exact hP.le))
      ((strip_le_iff P.re L).mpr (by rw [hL]; exact hP.le)) hz
    exact (strip_le_iff P.re z).mp hmem
  have hc1 : geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2 := by
    have hmem := geodCone_subset_dist_le
      ((ext_circle_iff hrl P).mpr (le_of_eq hL2.symm))
      ((ext_circle_iff hrl U).mpr
        (by rw [hU]; nlinarith [hL1, him, L.im_pos, U.im_pos]))
      ((ext_circle_iff hrl L).mpr (by rw [hL]; nlinarith [hL1])) hz
    exact (ext_circle_iff hrl z).mp hmem
  have hc2 : (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2 := by
    have hmem := geodCone_subset_dist_le
      ((int_circle_iff hru P).mpr (le_of_eq hU2))
      ((int_circle_iff hru U).mpr (by rw [hU]; nlinarith [hU1]))
      ((int_circle_iff hru L).mpr
        (by rw [hL]; nlinarith [hU1, him, L.im_pos, U.im_pos])) hz
    exact (int_circle_iff hru z).mp hmem
  exact ⟨Set.mem_Icc.mpr ⟨hs1, hs2⟩, hc1, hc2⟩

set_option maxHeartbeats 400000 in
-- The single-declaration proof interleaves quadratic `nlinarith` bounds with the explicit
-- circle-coordinate construction of the exit point; the combined elaboration exceeds the
-- default heartbeat budget.
/-- The region cut out by the strip and the two carrier circles is contained in the cone:
the geodesic through the apex and an interior point exits through the vertical base. -/
theorem region_subset_cone {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) (him : L.im < U.im) :
    {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
        ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
        ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2}
      ⊆ geodCone P (geodSeg U L) := by
  have hneU : U.re ≠ P.re := by rw [hU]; exact ne_of_lt hP
  have hneL : L.re ≠ P.re := by rw [hL]; exact ne_of_lt hP
  obtain ⟨hU1, hU2, hUrel⟩ := axis_apex_rel hU hneU
  obtain ⟨hL1, hL2, hLrel⟩ := axis_apex_rel hL hneL
  rintro z ⟨hicc, hzl, hzu⟩
  obtain ⟨hz0, hzP⟩ := Set.mem_Icc.mp hicc
  rcases eq_or_lt_of_le hz0 with hz0eq | hz0lt
  · -- the point lies on the axis, hence on the base segment
    rw [← hz0eq] at hzl hzu
    have hL_le : L.im ≤ z.im := by nlinarith [hzl, hL1, L.im_pos, z.im_pos]
    have hU_ge : z.im ≤ U.im := by nlinarith [hzu, hU1, U.im_pos, z.im_pos]
    have hzseg : z ∈ geodSeg U L := by
      rw [geodSeg_vertical_eq (by rw [hU, hL])]
      exact ⟨by rw [← hz0eq, hU], by rw [min_eq_right him.le]; exact hL_le,
        by rw [max_eq_left him.le]; exact hU_ge⟩
    exact mem_geodCone.mpr ⟨z, hzseg, right_mem_geodSeg P z⟩
  · rcases eq_or_lt_of_le hzP with hzPeq | hzPlt
    · -- the point is the apex
      rw [hzPeq] at hzl hzu
      have hyeq : z.im = P.im := by nlinarith [hzl, hzu, hL2, hU2, z.im_pos, P.im_pos]
      have hzP' : z = P := ext_re_im hzPeq hyeq
      exact mem_geodCone.mpr ⟨U, left_mem_geodSeg U L,
        by rw [hzP']; exact left_mem_geodSeg P U⟩
    · -- interior abscissa: exit point on the axis
      have hrePz : P.re ≠ z.re := (ne_of_lt hzPlt).symm
      set c := geodCenter P z with hc
      set r := geodRadius P z with hrr
      have hr0 : 0 < r := geodRadius_pos P z
      have hPc : ‖(P : ℂ) - ((c : ℝ) : ℂ)‖ = r := rfl
      have hzc : ‖(z : ℂ) - ((c : ℝ) : ℂ)‖ = r := norm_sub_geodCenter hrePz
      have hcdef : c * (2 * (P.re - z.re))
          = (P.re ^ 2 + P.im ^ 2) - (z.re ^ 2 + z.im ^ 2) := by
        rw [hc, geodCenter, Complex.normSq_apply, Complex.normSq_apply]
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        rw [div_mul_cancel₀]
        · ring
        · intro h0
          exact hrePz (by linarith [sub_eq_zero.mp (by linarith : P.re - z.re = 0)])
      have hr2 : r ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 := by
        have hsq := congrArg (· ^ 2) hzc
        simp only at hsq
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hsq
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.ofReal_re,
          Complex.ofReal_im, sub_zero] at hsq
        rw [← hsq]
        ring
      have hgap : 0 < P.re - z.re := by linarith
      have hα : 0 ≤ z.re ^ 2 + z.im ^ 2 - 2 * geodCenter L P * z.re - L.im ^ 2 := by
        nlinarith [hzl, hL1]
      have hβ : 0 ≤ U.im ^ 2 - (z.re ^ 2 + z.im ^ 2 - 2 * geodCenter U P * z.re) := by
        nlinarith [hzu, hU1]
      have hrc2 : (r ^ 2 - c ^ 2) * (2 * (P.re - z.re))
          = (z.re ^ 2 + z.im ^ 2) * (2 * (P.re - z.re))
            - 2 * z.re * ((P.re ^ 2 + P.im ^ 2) - (z.re ^ 2 + z.im ^ 2)) := by
        linear_combination (2 * (P.re - z.re)) * hr2 - 2 * z.re * hcdef
      have hLz : 2 * geodCenter L P * P.re * z.re
          = (P.re ^ 2 + P.im ^ 2 - L.im ^ 2) * z.re := by
        linear_combination z.re * hLrel
      have hUz : 2 * geodCenter U P * P.re * z.re
          = (P.re ^ 2 + P.im ^ 2 - U.im ^ 2) * z.re := by
        linear_combination z.re * hUrel
      have hDl : 0 ≤ (r ^ 2 - c ^ 2 - L.im ^ 2) * (2 * (P.re - z.re)) := by
        have h1 := mul_nonneg hα hgap.le
        have h2 := mul_nonneg hα hz0lt.le
        linarith [hrc2, h1, h2, hLz]
      have hDu : 0 ≤ (U.im ^ 2 - (r ^ 2 - c ^ 2)) * (2 * (P.re - z.re)) := by
        have h1 := mul_nonneg hβ hgap.le
        have h2 := mul_nonneg hβ hz0lt.le
        linarith [hrc2, h1, h2, hUz]
      have hbound_l : L.im ^ 2 ≤ r ^ 2 - c ^ 2 := by nlinarith [hDl, hgap]
      have hbound_u : r ^ 2 - c ^ 2 ≤ U.im ^ 2 := by nlinarith [hDu, hgap]
      have hpos : 0 < r ^ 2 - c ^ 2 := lt_of_lt_of_le (pow_pos L.im_pos 2) hbound_l
      have hh0pos : 0 < Real.sqrt (r ^ 2 - c ^ 2) := Real.sqrt_pos.mpr hpos
      set w₀ : UpperHalfPlane :=
        UpperHalfPlane.mk ⟨0, Real.sqrt (r ^ 2 - c ^ 2)⟩ hh0pos with hw₀
      have hw₀re : w₀.re = 0 := rfl
      have hw₀im : w₀.im = Real.sqrt (r ^ 2 - c ^ 2) := rfl
      have hw₀c : ‖(w₀ : ℂ) - ((c : ℝ) : ℂ)‖ = r := by
        have hns : Complex.normSq ((w₀ : ℂ) - ((c : ℝ) : ℂ)) = r ^ 2 := by
          rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
          rw [show ((w₀ : ℂ)).re = 0 from rfl,
            show ((w₀ : ℂ)).im = Real.sqrt (r ^ 2 - c ^ 2) from rfl,
            Real.mul_self_sqrt hpos.le]
          ring
        calc ‖(w₀ : ℂ) - ((c : ℝ) : ℂ)‖
            = Real.sqrt (Complex.normSq ((w₀ : ℂ) - ((c : ℝ) : ℂ))) := by
              rw [← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)]
          _ = r := by rw [hns, Real.sqrt_sq hr0.le]
      have hL_le : L.im ≤ w₀.im := by
        rw [hw₀im]
        calc L.im = Real.sqrt (L.im ^ 2) := (Real.sqrt_sq L.im_pos.le).symm
          _ ≤ Real.sqrt (r ^ 2 - c ^ 2) := Real.sqrt_le_sqrt hbound_l
      have hU_ge : w₀.im ≤ U.im := by
        rw [hw₀im]
        calc Real.sqrt (r ^ 2 - c ^ 2) ≤ Real.sqrt (U.im ^ 2) :=
              Real.sqrt_le_sqrt hbound_u
          _ = U.im := Real.sqrt_sq U.im_pos.le
      have hw₀seg : w₀ ∈ geodSeg U L := by
        rw [geodSeg_vertical_eq (by rw [hU, hL])]
        exact ⟨by rw [hw₀re, hU], by rw [min_eq_right him.le]; exact hL_le,
          by rw [max_eq_left him.le]; exact hU_ge⟩
      have hrePw : P.re ≠ w₀.re := by rw [hw₀re]; exact ne_of_gt hP
      have hcuniq : c = geodCenter P w₀ :=
        geodCenter_unique hrePw (by rw [hPc, hw₀c])
      have hrEq : geodRadius P w₀ = r := by
        rw [geodRadius, ← hcuniq]
        exact hPc
      have hzseg : z ∈ geodSeg P w₀ := by
        apply mem_geodSeg_of_on_circle hrePw
        · rw [← hcuniq, hrEq]
          exact hzc
        · rw [hw₀re, min_eq_right hP.le]
          exact hz0lt.le
        · rw [hw₀re, max_eq_left hP.le]
          exact hzPlt.le
      exact mem_geodCone.mpr ⟨w₀, hw₀seg, hzseg⟩

/-- A circle with a positive-height point over `c` extends to the left of `c`. -/
theorem clr_aux {c r y : ℝ} (h1 : r ^ 2 = c ^ 2 + y ^ 2) (hy : 0 < y) (hr : 0 < r) :
    c - r < 0 := by
  nlinarith [sq_nonneg (c - r), sq_nonneg (c + r)]

/-- A circle with a positive-height point at abscissa `x` extends to the right of `x`. -/
theorem crr_aux {c r x y : ℝ} (h2 : (x - c) ^ 2 + y ^ 2 = r ^ 2) (hy : 0 < y)
    (hr : 0 < r) : x < c + r := by
  nlinarith [sq_nonneg (x - c - r), sq_nonneg (x - c + r)]

/-- Interval abscissas stay within the circle range. -/
theorem range_aux {c r x xm : ℝ} (hcl : c - r < 0) (hcr : xm < c + r) (h0 : 0 ≤ x)
    (h1 : x ≤ xm) : 0 ≤ r ^ 2 - (x - c) ^ 2 := by
  nlinarith

/-- The center of the lower circle lies to the right of the center of the upper one. -/
theorem cc_aux {cl cu x₁ yl yu S : ℝ} (hLrel : 2 * cl * x₁ = S - yl ^ 2)
    (hUrel : 2 * cu * x₁ = S - yu ^ 2) (him : yl < yu) (hyl : 0 < yl) (hx : 0 < x₁) :
    cu ≤ cl := by
  nlinarith

/-- Over the strip the lower arc stays below the upper arc. -/
theorem arc_mono_aux {cl rl cu ru x₁ yl yu S x : ℝ} (hL1 : rl ^ 2 = cl ^ 2 + yl ^ 2)
    (hU1 : ru ^ 2 = cu ^ 2 + yu ^ 2) (hLrel : 2 * cl * x₁ = S - yl ^ 2)
    (hUrel : 2 * cu * x₁ = S - yu ^ 2) (hcc : cu ≤ cl) (h1 : x ≤ x₁) :
    rl ^ 2 - (x - cl) ^ 2 ≤ ru ^ 2 - (x - cu) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hcc)]

set_option maxHeartbeats 400000 in
-- The membership sandwich repeatedly rewrites square roots against quadratic constraints;
-- the combined elaboration exceeds the default heartbeat budget.
/-- The region agrees with the difference of the two wedges up to the null upper arc. -/
theorem region_vol_sandwich {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) :
    volume {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
        ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
        ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2}
      = volume ({z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
          ∧ √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im}
        \ {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
          ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im}) := by
  have hneU : U.re ≠ P.re := by rw [hU]; exact ne_of_lt hP
  have hneL : L.re ≠ P.re := by rw [hL]; exact ne_of_lt hP
  obtain ⟨hU1, hU2, -⟩ := axis_apex_rel hU hneU
  obtain ⟨hL1, hL2, -⟩ := axis_apex_rel hL hneL
  have hru : 0 < geodRadius U P := geodRadius_pos U P
  have hrl : 0 < geodRadius L P := geodRadius_pos L P
  have hrangeL : ∀ z : UpperHalfPlane, z.re ∈ Set.Icc 0 P.re
      → 0 ≤ geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2 := fun z hz =>
    range_aux (clr_aux hL1 L.im_pos hrl) (crr_aux hL2 P.im_pos hrl)
      (Set.mem_Icc.mp hz).1 (Set.mem_Icc.mp hz).2
  have hrangeU : ∀ z : UpperHalfPlane, z.re ∈ Set.Icc 0 P.re
      → 0 ≤ geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2 := fun z hz =>
    range_aux (clr_aux hU1 U.im_pos hru) (crr_aux hU2 P.im_pos hru)
      (Set.mem_Icc.mp hz).1 (Set.mem_Icc.mp hz).2
  have hdiff_sub : ∀ z : UpperHalfPlane,
      (z.re ∈ Set.Icc 0 P.re ∧ √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im)
        → ¬ (z.re ∈ Set.Icc 0 P.re
            ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im)
        → z.re ∈ Set.Icc 0 P.re
            ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
            ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2 := by
    rintro z ⟨hicc, hl⟩ hnu
    refine ⟨hicc, ?_, ?_⟩
    · have h2 := (sqrt_le_iff (hrangeL z hicc) z.im_pos.le).mp hl
      linarith
    · have hnotle : ¬ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im :=
        fun hc => hnu ⟨hicc, hc⟩
      have h2 : ¬ geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2 ≤ z.im ^ 2 := fun hc =>
        hnotle ((sqrt_le_iff (hrangeU z hicc) z.im_pos.le).mpr hc)
      linarith [not_le.mp h2]
  apply le_antisymm
  · -- region ⊆ difference ∪ null arc
    have hR_sub : {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
        ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
        ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2}
        ⊆ ({z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
            ∧ √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im}
          \ {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
            ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im})
          ∪ geodSeg U P := by
      rintro z ⟨hicc, hl, hu⟩
      have hzWl : √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im :=
        (sqrt_le_iff (hrangeL z hicc) z.im_pos.le).mpr (by linarith)
      by_cases hzWu : √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im
      · right
        have hle2 : z.im ^ 2 ≤ geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2 := by
          linarith
        have him2 : z.im ^ 2 = geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2 :=
          le_antisymm hle2 ((sqrt_le_iff (hrangeU z hicc) z.im_pos.le).mp hzWu)
        have hnorm : ‖(z : ℂ) - ((geodCenter U P : ℝ) : ℂ)‖ = geodRadius U P := by
          have hns : Complex.normSq ((z : ℂ) - ((geodCenter U P : ℝ) : ℂ))
              = geodRadius U P ^ 2 := by
            rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
            simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero,
              UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
            linear_combination him2
          calc ‖(z : ℂ) - ((geodCenter U P : ℝ) : ℂ)‖
              = √(Complex.normSq ((z : ℂ) - ((geodCenter U P : ℝ) : ℂ))) := by
                rw [← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)]
            _ = geodRadius U P := by rw [hns, Real.sqrt_sq hru.le]
        obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hicc
        exact mem_geodSeg_of_on_circle hneU hnorm
          (by rw [hU, min_eq_left hP.le]; exact h0)
          (by rw [hU, max_eq_right hP.le]; exact h1)
      · exact Or.inl ⟨⟨hicc, hzWl⟩, fun hc => hzWu hc.2⟩
    calc volume {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
          ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
          ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2}
        ≤ volume (({z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
            ∧ √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im}
          \ {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
            ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im})
          ∪ geodSeg U P) := measure_mono hR_sub
      _ ≤ _ + volume (geodSeg U P) := measure_union_le _ _
      _ = _ := by rw [volume_geodSeg_eq_zero, add_zero]
  · exact measure_mono fun z hz => hdiff_sub z hz.1 hz.2

/-- The hyperbolic area of the wedge difference, as an arcsine expression. -/
theorem wedge_diff_vol {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) (him : L.im < U.im) :
    volume ({z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
        ∧ √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im}
      \ {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
        ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im})
      = ENNReal.ofReal
          ((Real.arcsin ((P.re - geodCenter L P) / geodRadius L P)
              + Real.arcsin (geodCenter L P / geodRadius L P))
            - (Real.arcsin ((P.re - geodCenter U P) / geodRadius U P)
              + Real.arcsin (geodCenter U P / geodRadius U P))) := by
  have hneU : U.re ≠ P.re := by rw [hU]; exact ne_of_lt hP
  have hneL : L.re ≠ P.re := by rw [hL]; exact ne_of_lt hP
  obtain ⟨hU1, hU2, hUrel⟩ := axis_apex_rel hU hneU
  obtain ⟨hL1, hL2, hLrel⟩ := axis_apex_rel hL hneL
  have hru : 0 < geodRadius U P := geodRadius_pos U P
  have hrl : 0 < geodRadius L P := geodRadius_pos L P
  have hclL : geodCenter L P - geodRadius L P < 0 := clr_aux hL1 L.im_pos hrl
  have hclR : P.re < geodCenter L P + geodRadius L P := crr_aux hL2 P.im_pos hrl
  have hcuL : geodCenter U P - geodRadius U P < 0 := clr_aux hU1 U.im_pos hru
  have hcuR : P.re < geodCenter U P + geodRadius U P := crr_aux hU2 P.im_pos hru
  have hvl := volume_wedge (x₀ := geodCenter L P) (r := geodRadius L P) (x₁ := 0)
    (x₂ := P.re) hrl (by linarith) hP.le (by linarith)
  have hvu := volume_wedge (x₀ := geodCenter U P) (r := geodRadius U P) (x₁ := 0)
    (x₂ := P.re) hru (by linarith) hP.le (by linarith)
  have hcc : geodCenter U P ≤ geodCenter L P :=
    cc_aux hLrel hUrel him L.im_pos hP
  have hsub : {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
      ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im}
      ⊆ {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
      ∧ √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im} := by
    rintro z ⟨hicc, hle⟩
    exact ⟨hicc, le_trans (Real.sqrt_le_sqrt
      (arc_mono_aux hL1 hU1 hLrel hUrel hcc (Set.mem_Icc.mp hicc).2)) hle⟩
  have hWuClosed : IsClosed {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
      ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im} := by
    have hcont : Continuous fun z : UpperHalfPlane
        => √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) :=
      Real.continuous_sqrt.comp
        (continuous_const.sub ((UpperHalfPlane.continuous_re.sub continuous_const).pow 2))
    exact (isClosed_Icc.preimage UpperHalfPlane.continuous_re).inter
      (isClosed_le hcont UpperHalfPlane.continuous_im)
  have hWu_fin : volume {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
      ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im} ≠ ⊤ := by
    rw [hvu]
    exact ENNReal.ofReal_ne_top
  have hwu_nonneg : 0 ≤ Real.arcsin ((P.re - geodCenter U P) / geodRadius U P)
      - Real.arcsin ((0 - geodCenter U P) / geodRadius U P) := by
    have := Real.arcsin_le_arcsin (x := (0 - geodCenter U P) / geodRadius U P)
      (y := (P.re - geodCenter U P) / geodRadius U P)
      (by rw [div_le_div_iff_of_pos_right hru]; linarith)
    linarith
  rw [measure_diff hsub hWuClosed.measurableSet.nullMeasurableSet hWu_fin, hvl, hvu,
    ← ENNReal.ofReal_sub _ hwu_nonneg,
    show (0 - geodCenter L P) / geodRadius L P = -(geodCenter L P / geodRadius L P) by ring,
    show (0 - geodCenter U P) / geodRadius U P = -(geodCenter U P / geodRadius U P) by ring,
    Real.arcsin_neg, Real.arcsin_neg]
  ring_nf

/-- The hyperbolic area of the normalized region: the difference of the two wedge areas. -/
theorem volume_region {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) (him : L.im < U.im) :
    volume {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
        ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
        ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2}
      = ENNReal.ofReal
          ((Real.arcsin ((P.re - geodCenter L P) / geodRadius L P)
              + Real.arcsin (geodCenter L P / geodRadius L P))
            - (Real.arcsin ((P.re - geodCenter U P) / geodRadius U P)
              + Real.arcsin (geodCenter U P / geodRadius U P))) :=
  (region_vol_sandwich hU hL hP).trans (wedge_diff_vol hU hL hP him)

/-- Gauss-Bonnet for the normalized triangle: apex to the right, vertical base. -/
theorem volume_cone {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) (him : L.im < U.im) :
    volume (geodCone P (geodSeg U L))
      = ENNReal.ofReal
          (π - sectorAngle P U L - sectorAngle U L P - sectorAngle L U P) := by
  have hEq : geodCone P (geodSeg U L)
      = {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
          ∧ geodRadius L P ^ 2 ≤ (z.re - geodCenter L P) ^ 2 + z.im ^ 2
          ∧ (z.re - geodCenter U P) ^ 2 + z.im ^ 2 ≤ geodRadius U P ^ 2} :=
    Set.Subset.antisymm (cone_subset_region hU hL hP him)
      (region_subset_cone hU hL hP him)
  rw [hEq, volume_region hU hL hP him]
  congr 1
  rw [sectorAngle_apex hU hL hP him, sectorAngle_axis_down hU hL hP him,
    sectorAngle_axis_up hL hU hP him]
  ring

/-! ## Transport of the triangle under the isometries -/

/-- Geodesic cones transport along the `SL(2, ℝ)`-action. -/
theorem smul_geodCone (g : SL(2, ℝ)) (z : UpperHalfPlane) (s : Set UpperHalfPlane) :
    (g • ·) '' geodCone z s = geodCone (g • z) ((g • ·) '' s) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_geodCone.mp hx
    refine mem_geodCone.mpr ⟨g • y, ⟨y, hy, rfl⟩, ?_⟩
    rw [← smul_geodSeg]
    exact ⟨x, hxy, rfl⟩
  · intro hw
    obtain ⟨y', hy', hwy⟩ := mem_geodCone.mp hw
    obtain ⟨y, hy, rfl⟩ := hy'
    rw [← smul_geodSeg] at hwy
    obtain ⟨x, hx, rfl⟩ := hwy
    exact ⟨x, mem_geodCone.mpr ⟨y, hy, hx⟩, rfl⟩

/-- Geodesic triangles transport along the `SL(2, ℝ)`-action. -/
theorem smul_triangle (g : SL(2, ℝ)) (v₁ v₂ v₃ : UpperHalfPlane) :
    (g • ·) '' hyperbolicTriangle v₁ v₂ v₃
      = hyperbolicTriangle (g • v₁) (g • v₂) (g • v₃) := by
  unfold hyperbolicTriangle
  rw [smul_geodCone, smul_geodSeg]

/-- The reflection `J` negates the real part. -/
theorem J_smul_re (τ : UpperHalfPlane) : (UpperHalfPlane.J • τ).re = -τ.re := by
  have h := congrArg Complex.re (UpperHalfPlane.coe_J_smul τ)
  simpa using h

/-- The reflection `J` preserves the height. -/
theorem J_smul_im (τ : UpperHalfPlane) : (UpperHalfPlane.J • τ).im = τ.im := by
  have h := congrArg Complex.im (UpperHalfPlane.coe_J_smul τ)
  simpa using h

/-- The reflection `J` is an involution of the upper half plane. -/
theorem J_J (τ : UpperHalfPlane) : UpperHalfPlane.J • UpperHalfPlane.J • τ = τ := by
  rw [← mul_smul, show UpperHalfPlane.J * UpperHalfPlane.J = 1 by
    rw [← sq]; exact UpperHalfPlane.J_sq, one_smul]

/-- The reflection `J` is an isometry of the hyperbolic metric. -/
theorem dist_J (z w : UpperHalfPlane) :
    dist (UpperHalfPlane.J • z) (UpperHalfPlane.J • w) = dist z w := by
  have hcosh : Real.cosh (dist (UpperHalfPlane.J • z) (UpperHalfPlane.J • w))
      = Real.cosh (dist z w) := by
    rw [cosh_dist_expand, cosh_dist_expand, J_smul_re, J_smul_re,
      J_smul_im, J_smul_im]
    ring_nf
  have h1 := Real.cosh_le_cosh.mp hcosh.le
  have h2 := Real.cosh_le_cosh.mp hcosh.ge
  rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h1 h2
  exact le_antisymm h1 h2

/-- Distances across a single reflection move the reflection to the other argument. -/
theorem dist_J_swap (p q : UpperHalfPlane) :
    dist p (UpperHalfPlane.J • q) = dist (UpperHalfPlane.J • p) q := by
  rw [← dist_J p (UpperHalfPlane.J • q), J_J]

/-- Geodesic segments transport along the reflection `J`. -/
theorem J_geodSeg (a b : UpperHalfPlane) :
    (UpperHalfPlane.J • ·) '' geodSeg a b
      = geodSeg (UpperHalfPlane.J • a) (UpperHalfPlane.J • b) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dist _ _ + dist _ _ = dist _ _
    rw [dist_J, dist_J, dist_J]
    exact hx
  · intro hw
    refine ⟨UpperHalfPlane.J • w, ?_, J_J w⟩
    change dist a (UpperHalfPlane.J • w) + dist (UpperHalfPlane.J • w) b = dist a b
    rw [dist_J_swap a w, dist_comm (UpperHalfPlane.J • w) b, dist_J_swap b w,
      ← dist_J a b, dist_comm (UpperHalfPlane.J • b) w]
    exact hw

/-- Geodesic cones transport along the reflection `J`. -/
theorem J_geodCone (z : UpperHalfPlane) (s : Set UpperHalfPlane) :
    (UpperHalfPlane.J • ·) '' geodCone z s
      = geodCone (UpperHalfPlane.J • z) ((UpperHalfPlane.J • ·) '' s) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_geodCone.mp hx
    refine mem_geodCone.mpr ⟨UpperHalfPlane.J • y, ⟨y, hy, rfl⟩, ?_⟩
    rw [← J_geodSeg]
    exact ⟨x, hxy, rfl⟩
  · intro hw
    obtain ⟨y', hy', hwy⟩ := mem_geodCone.mp hw
    obtain ⟨y, hy, rfl⟩ := hy'
    rw [← J_geodSeg] at hwy
    obtain ⟨x, hx, rfl⟩ := hwy
    exact ⟨x, mem_geodCone.mpr ⟨y, hy, hx⟩, rfl⟩

/-- Geodesic triangles transport along the reflection `J`. -/
theorem J_triangle (v₁ v₂ v₃ : UpperHalfPlane) :
    (UpperHalfPlane.J • ·) '' hyperbolicTriangle v₁ v₂ v₃
      = hyperbolicTriangle (UpperHalfPlane.J • v₁) (UpperHalfPlane.J • v₂)
        (UpperHalfPlane.J • v₃) := by
  unfold hyperbolicTriangle
  rw [J_geodCone, J_geodSeg]

/-- Conjugation does not change the absolute argument. -/
theorem abs_arg_conj (ξ : ℂ) : |Complex.arg ((starRingEnd ℂ) ξ)| = |Complex.arg ξ| := by
  rw [Complex.arg_conj]
  split_ifs with h
  · rw [h]
  · rw [abs_neg]

/-- The frame conjugates under the reflection `J`. -/
theorem discChart_J (z w : UpperHalfPlane) :
    discChart (UpperHalfPlane.J • z) (UpperHalfPlane.J • w)
      = (starRingEnd ℂ) (discChart z w) := by
  rw [discChart_eq, discChart_eq, map_div₀, UpperHalfPlane.coe_J_smul,
    UpperHalfPlane.coe_J_smul, map_sub, map_sub, Complex.conj_conj]
  rw [show -(starRingEnd ℂ) (w : ℂ) - -(starRingEnd ℂ) (z : ℂ)
      = -((starRingEnd ℂ) (w : ℂ) - (starRingEnd ℂ) (z : ℂ)) by ring,
    show -(starRingEnd ℂ) (w : ℂ) - (starRingEnd ℂ) (-(starRingEnd ℂ) (z : ℂ))
      = -((starRingEnd ℂ) (w : ℂ) - (z : ℂ)) by rw [map_neg, Complex.conj_conj]; ring,
    neg_div_neg_eq]

/-- Angles are invariant under the reflection `J`. -/
theorem sectorAngle_J (z w₁ w₂ : UpperHalfPlane) :
    sectorAngle (UpperHalfPlane.J • z) (UpperHalfPlane.J • w₁) (UpperHalfPlane.J • w₂)
      = sectorAngle z w₁ w₂ := by
  unfold sectorAngle
  rw [discChart_J, discChart_J, ← map_div₀]
  exact abs_arg_conj _

/-! ## The collinear case -/

/-- The angle at an axis point between two axis points: `π` from the middle point, `0` from
an extreme point. -/
theorem sectorAngle_collinear {z w w' : UpperHalfPlane} (hz : z.re = 0)
    (hw : w.re = 0) (hw' : w'.re = 0) (hne : w ≠ z) (hne' : w' ≠ z) :
    sectorAngle z w w'
      = if (w.im - z.im) * (w'.im - z.im) < 0 then π else 0 := by
  have hwim : w.im ≠ z.im := fun h => hne (ext_re_im (hw.trans hz.symm) h)
  have hwim' : w'.im ≠ z.im := fun h => hne' (ext_re_im (hw'.trans hz.symm) h)
  have hd : 0 < w.im + z.im := by linarith [w.im_pos, z.im_pos]
  have hd' : 0 < w'.im + z.im := by linarith [w'.im_pos, z.im_pos]
  unfold sectorAngle
  rw [discChart_axis hz hw, discChart_axis hz hw', ← Complex.ofReal_div]
  split_ifs with hprod
  · have hneg : (w'.im - z.im) / (w'.im + z.im) / ((w.im - z.im) / (w.im + z.im)) < 0 := by
      rcases lt_or_gt_of_ne (sub_ne_zero.mpr hwim) with hlt | hgt
      · have h2 : 0 < w'.im - z.im := by nlinarith
        apply div_neg_of_pos_of_neg (div_pos h2 hd') (div_neg_of_neg_of_pos hlt hd)
      · have h2 : w'.im - z.im < 0 := by nlinarith
        apply div_neg_of_neg_of_pos (div_neg_of_neg_of_pos h2 hd') (div_pos hgt hd)
    rw [Complex.arg_ofReal_of_neg hneg]
    exact abs_of_pos Real.pi_pos
  · have hnn : 0 ≤ (w'.im - z.im) / (w'.im + z.im) / ((w.im - z.im) / (w.im + z.im)) := by
      have hprod' : 0 < (w.im - z.im) * (w'.im - z.im) :=
        lt_of_le_of_ne (not_lt.mp hprod) (Ne.symm (mul_ne_zero (sub_ne_zero.mpr hwim)
          (sub_ne_zero.mpr hwim')))
      rcases lt_or_gt_of_ne (sub_ne_zero.mpr hwim) with hlt | hgt
      · have h2 : w'.im - z.im < 0 := by nlinarith
        exact le_of_lt (div_pos_of_neg_of_neg (div_neg_of_neg_of_pos h2 hd')
          (div_neg_of_neg_of_pos hlt hd))
      · have h2 : 0 < w'.im - z.im := by nlinarith
        exact le_of_lt (div_pos (div_pos h2 hd') (div_pos hgt hd))
    rw [Complex.arg_ofReal_of_nonneg hnn, abs_zero]

/-- A degenerate triangle with all vertices on the axis is null, and its angles sum to
`π`. -/
theorem volume_collinear {v₁ v₂ v₃ : UpperHalfPlane} (h1 : v₁.re = 0)
    (h2 : v₂.re = 0) (h3 : v₃.re = 0) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    volume (hyperbolicTriangle v₁ v₂ v₃) = ENNReal.ofReal
      (π - sectorAngle v₁ v₂ v₃ - sectorAngle v₂ v₁ v₃ - sectorAngle v₃ v₁ v₂) := by
  have hsubset : hyperbolicTriangle v₁ v₂ v₃ ⊆ {τ : UpperHalfPlane | τ.re = 0} := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_geodCone.mp hx
    have hwre : w.re = v₂.re := (mem_geodSeg_vertical (h2.trans h3.symm) hw).1
    have hre1w : v₁.re = w.re := by rw [h1, hwre, h2]
    have hxre : x.re = v₁.re := (mem_geodSeg_vertical hre1w hxw).1
    change x.re = 0
    rw [hxre, h1]
  have hvol0 : volume (hyperbolicTriangle v₁ v₂ v₃) = 0 :=
    measure_mono_null hsubset (volume_vertLine 0)
  have hA1 := sectorAngle_collinear h1 h2 h3 (Ne.symm h₁₂) (Ne.symm h₁₃)
  have hA2 := sectorAngle_collinear h2 h1 h3 h₁₂ (Ne.symm h₂₃)
  have hA3 := sectorAngle_collinear h3 h1 h2 h₁₃ h₂₃
  have hne12 : v₁.im ≠ v₂.im := fun h => h₁₂ (ext_re_im (h1.trans h2.symm) h)
  have hne13 : v₁.im ≠ v₃.im := fun h => h₁₃ (ext_re_im (h1.trans h3.symm) h)
  have hne23 : v₂.im ≠ v₃.im := fun h => h₂₃ (ext_re_im (h2.trans h3.symm) h)
  have hsum : sectorAngle v₁ v₂ v₃ + sectorAngle v₂ v₁ v₃ + sectorAngle v₃ v₁ v₂ = π := by
    rw [hA1, hA2, hA3]
    rcases lt_or_gt_of_ne hne12 with h12 | h12 <;>
      rcases lt_or_gt_of_ne hne13 with h13 | h13 <;>
        rcases lt_or_gt_of_ne hne23 with h23 | h23 <;>
          first
            | linarith
            | (rw [if_pos (by nlinarith), if_neg (not_lt.mpr (by nlinarith)),
                if_neg (not_lt.mpr (by nlinarith))]; ring)
            | (rw [if_neg (not_lt.mpr (by nlinarith)), if_pos (by nlinarith),
                if_neg (not_lt.mpr (by nlinarith))]; ring)
            | (rw [if_neg (not_lt.mpr (by nlinarith)), if_neg (not_lt.mpr (by nlinarith)),
                if_pos (by nlinarith)]; ring)
  rw [hvol0, show π - sectorAngle v₁ v₂ v₃ - sectorAngle v₂ v₁ v₃ - sectorAngle v₃ v₁ v₂
    = 0 from by linarith, ENNReal.ofReal_zero]

/-! ## The Gauss–Bonnet angle deficit -/

/-- Gauss-Bonnet with the base verticalized and the apex to the right. -/
theorem volume_triangle_pos {w₁ w₂ w₃ : UpperHalfPlane} (h2 : w₂.re = 0)
    (h3 : w₃.re = 0) (hpos : 0 < w₁.re) (h23 : w₂ ≠ w₃) :
    volume (hyperbolicTriangle w₁ w₂ w₃) = ENNReal.ofReal
      (π - sectorAngle w₁ w₂ w₃ - sectorAngle w₂ w₁ w₃ - sectorAngle w₃ w₁ w₂) := by
  have hne23 : w₂.im ≠ w₃.im := fun h => h23 (ext_re_im (h2.trans h3.symm) h)
  rcases lt_or_gt_of_ne hne23 with him | him
  · -- upper base vertex is w₃
    calc volume (hyperbolicTriangle w₁ w₂ w₃)
        = volume (geodCone w₁ (geodSeg w₃ w₂)) := by
          rw [hyperbolicTriangle, geodSeg_comm]
      _ = ENNReal.ofReal
          (π - sectorAngle w₁ w₃ w₂ - sectorAngle w₃ w₂ w₁ - sectorAngle w₂ w₃ w₁) :=
          volume_cone h3 h2 hpos him
      _ = ENNReal.ofReal
          (π - sectorAngle w₁ w₂ w₃ - sectorAngle w₂ w₁ w₃ - sectorAngle w₃ w₁ w₂) := by
          rw [sectorAngle_comm w₁ w₃ w₂, sectorAngle_comm w₃ w₂ w₁,
            sectorAngle_comm w₂ w₃ w₁]
          congr 1
          ring
  · -- upper base vertex is w₂
    calc volume (hyperbolicTriangle w₁ w₂ w₃)
        = volume (geodCone w₁ (geodSeg w₂ w₃)) := rfl
      _ = ENNReal.ofReal
          (π - sectorAngle w₁ w₂ w₃ - sectorAngle w₂ w₃ w₁ - sectorAngle w₃ w₂ w₁) :=
          volume_cone h2 h3 hpos him
      _ = ENNReal.ofReal
          (π - sectorAngle w₁ w₂ w₃ - sectorAngle w₂ w₁ w₃ - sectorAngle w₃ w₁ w₂) := by
          rw [sectorAngle_comm w₂ w₃ w₁, sectorAngle_comm w₃ w₂ w₁]

/-- **Gauss–Bonnet for geodesic triangles**: the hyperbolic area of the geodesic triangle on
three pairwise distinct vertices is the angle deficit `π - α - β - γ`. -/
theorem volume_hyperbolicTriangle (v₁ v₂ v₃ : UpperHalfPlane) (h₁₂ : v₁ ≠ v₂)
    (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    volume (hyperbolicTriangle v₁ v₂ v₃) = ENNReal.ofReal
      (π - sectorAngle v₁ v₂ v₃ - sectorAngle v₂ v₁ v₃ - sectorAngle v₃ v₁ v₂) := by
  suffices H : ∀ w₁ w₂ w₃ : UpperHalfPlane, w₂.re = 0 → w₃.re = 0 → w₁ ≠ w₂ → w₁ ≠ w₃
      → w₂ ≠ w₃ → volume (hyperbolicTriangle w₁ w₂ w₃) = ENNReal.ofReal
        (π - sectorAngle w₁ w₂ w₃ - sectorAngle w₂ w₁ w₃ - sectorAngle w₃ w₁ w₂) by
    obtain ⟨g, hg2, hg3⟩ := exists_verticalize v₂ v₃
    have hvol : volume (hyperbolicTriangle v₁ v₂ v₃)
        = volume (hyperbolicTriangle (g • v₁) (g • v₂) (g • v₃)) := by
      calc volume (hyperbolicTriangle v₁ v₂ v₃)
          = volume (g • hyperbolicTriangle v₁ v₂ v₃) := (volume_smul_sl2 g _).symm
        _ = volume (hyperbolicTriangle (g • v₁) (g • v₂) (g • v₃)) := by
            rw [← Set.image_smul, smul_triangle]
    rw [hvol, ← sectorAngle_smul g v₁ v₂ v₃, ← sectorAngle_smul g v₂ v₁ v₃,
      ← sectorAngle_smul g v₃ v₁ v₂]
    exact H (g • v₁) (g • v₂) (g • v₃) hg2 hg3
      (fun h => h₁₂ (smul_left_cancel g h)) (fun h => h₁₃ (smul_left_cancel g h))
      (fun h => h₂₃ (smul_left_cancel g h))
  intro w₁ w₂ w₃ h2 h3 h12 h13 h23
  rcases lt_trichotomy w₁.re 0 with hneg | hzero | hpos
  · -- reflect across the axis
    have hvol : volume (hyperbolicTriangle w₁ w₂ w₃)
        = volume (hyperbolicTriangle (UpperHalfPlane.J • w₁) (UpperHalfPlane.J • w₂)
            (UpperHalfPlane.J • w₃)) := by
      calc volume (hyperbolicTriangle w₁ w₂ w₃)
          = volume (UpperHalfPlane.J • hyperbolicTriangle w₁ w₂ w₃) :=
            (volume_smul_gl UpperHalfPlane.J _).symm
        _ = _ := by rw [← Set.image_smul, J_triangle]
    rw [hvol, ← sectorAngle_J w₁ w₂ w₃, ← sectorAngle_J w₂ w₁ w₃,
      ← sectorAngle_J w₃ w₁ w₂]
    exact volume_triangle_pos
      (by rw [J_smul_re, h2, neg_zero]) (by rw [J_smul_re, h3, neg_zero])
      (by rw [J_smul_re]; linarith)
      (fun h => h23 (by rw [← J_J w₂, h, J_J]))
  · exact volume_collinear hzero h2 h3 h12 h13 h23
  · exact volume_triangle_pos h2 h3 hpos h23

/-- The angle deficit of the normalized cone triangle is nonnegative: the wedge over the
upper circle is contained in the wedge over the lower circle. -/
theorem cone_deficit_nonneg {U L P : UpperHalfPlane} (hU : U.re = 0) (hL : L.re = 0)
    (hP : 0 < P.re) (him : L.im < U.im) :
    0 ≤ π - sectorAngle P U L - sectorAngle U L P - sectorAngle L U P := by
  have hneU : U.re ≠ P.re := by rw [hU]; exact ne_of_lt hP
  have hneL : L.re ≠ P.re := by rw [hL]; exact ne_of_lt hP
  obtain ⟨hU1, hU2, hUrel⟩ := axis_apex_rel hU hneU
  obtain ⟨hL1, hL2, hLrel⟩ := axis_apex_rel hL hneL
  have hru : 0 < geodRadius U P := geodRadius_pos U P
  have hrl : 0 < geodRadius L P := geodRadius_pos L P
  have hclL : geodCenter L P - geodRadius L P < 0 := clr_aux hL1 L.im_pos hrl
  have hclR : P.re < geodCenter L P + geodRadius L P := crr_aux hL2 P.im_pos hrl
  have hcuL : geodCenter U P - geodRadius U P < 0 := clr_aux hU1 U.im_pos hru
  have hcuR : P.re < geodCenter U P + geodRadius U P := crr_aux hU2 P.im_pos hru
  have hvl := volume_wedge (x₀ := geodCenter L P) (r := geodRadius L P) (x₁ := 0)
    (x₂ := P.re) hrl (by linarith) hP.le (by linarith)
  have hvu := volume_wedge (x₀ := geodCenter U P) (r := geodRadius U P) (x₁ := 0)
    (x₂ := P.re) hru (by linarith) hP.le (by linarith)
  have hcc : geodCenter U P ≤ geodCenter L P := cc_aux hLrel hUrel him L.im_pos hP
  have hsub : {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
      ∧ √(geodRadius U P ^ 2 - (z.re - geodCenter U P) ^ 2) ≤ z.im}
      ⊆ {z : UpperHalfPlane | z.re ∈ Set.Icc 0 P.re
      ∧ √(geodRadius L P ^ 2 - (z.re - geodCenter L P) ^ 2) ≤ z.im} := by
    rintro z ⟨hicc, hle⟩
    exact ⟨hicc, le_trans (Real.sqrt_le_sqrt
      (arc_mono_aux hL1 hU1 hLrel hUrel hcc (Set.mem_Icc.mp hicc).2)) hle⟩
  have hle := measure_mono (μ := (volume : Measure UpperHalfPlane)) hsub
  rw [hvl, hvu] at hle
  have hL0 : 0 ≤ arcsin ((P.re - geodCenter L P) / geodRadius L P)
      - arcsin ((0 - geodCenter L P) / geodRadius L P) := by
    have := Real.arcsin_le_arcsin (x := (0 - geodCenter L P) / geodRadius L P)
      (y := (P.re - geodCenter L P) / geodRadius L P)
      (by rw [div_le_div_iff_of_pos_right hrl]; linarith)
    linarith
  have hkey : arcsin ((P.re - geodCenter U P) / geodRadius U P)
      - arcsin ((0 - geodCenter U P) / geodRadius U P)
      ≤ arcsin ((P.re - geodCenter L P) / geodRadius L P)
      - arcsin ((0 - geodCenter L P) / geodRadius L P) :=
    (ENNReal.ofReal_le_ofReal_iff hL0).mp hle
  rw [show (0 - geodCenter L P) / geodRadius L P
      = -(geodCenter L P / geodRadius L P) by ring,
    show (0 - geodCenter U P) / geodRadius U P
      = -(geodCenter U P / geodRadius U P) by ring,
    Real.arcsin_neg, Real.arcsin_neg] at hkey
  rw [sectorAngle_apex hU hL hP him, sectorAngle_axis_down hU hL hP him,
    sectorAngle_axis_up hL hU hP him]
  linarith

/-- The angle deficit is nonnegative for a triangle with vertical base and apex to the
right. -/
theorem deficit_nonneg_pos {w₁ w₂ w₃ : UpperHalfPlane} (h2 : w₂.re = 0)
    (h3 : w₃.re = 0) (hpos : 0 < w₁.re) (h23 : w₂ ≠ w₃) :
    0 ≤ π - sectorAngle w₁ w₂ w₃ - sectorAngle w₂ w₁ w₃ - sectorAngle w₃ w₁ w₂ := by
  have hne23 : w₂.im ≠ w₃.im := fun h => h23 (ext_re_im (h2.trans h3.symm) h)
  rcases lt_or_gt_of_ne hne23 with him | him
  · have h := cone_deficit_nonneg h3 h2 hpos him
    rw [sectorAngle_comm w₁ w₃ w₂, sectorAngle_comm w₃ w₂ w₁,
      sectorAngle_comm w₂ w₃ w₁] at h
    linarith
  · have h := cone_deficit_nonneg h2 h3 hpos him
    rwa [sectorAngle_comm w₂ w₃ w₁, sectorAngle_comm w₃ w₂ w₁] at h

/-- The angles of a degenerate triangle carried by the imaginary axis sum to `π`. -/
theorem deficit_collinear {v₁ v₂ v₃ : UpperHalfPlane} (h1 : v₁.re = 0)
    (h2 : v₂.re = 0) (h3 : v₃.re = 0) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    sectorAngle v₁ v₂ v₃ + sectorAngle v₂ v₁ v₃ + sectorAngle v₃ v₁ v₂ = π := by
  have hA1 := sectorAngle_collinear h1 h2 h3 (Ne.symm h₁₂) (Ne.symm h₁₃)
  have hA2 := sectorAngle_collinear h2 h1 h3 h₁₂ (Ne.symm h₂₃)
  have hA3 := sectorAngle_collinear h3 h1 h2 h₁₃ h₂₃
  have hne12 : v₁.im ≠ v₂.im := fun h => h₁₂ (ext_re_im (h1.trans h2.symm) h)
  have hne13 : v₁.im ≠ v₃.im := fun h => h₁₃ (ext_re_im (h1.trans h3.symm) h)
  have hne23 : v₂.im ≠ v₃.im := fun h => h₂₃ (ext_re_im (h2.trans h3.symm) h)
  rw [hA1, hA2, hA3]
  rcases lt_or_gt_of_ne hne12 with h12 | h12 <;>
    rcases lt_or_gt_of_ne hne13 with h13 | h13 <;>
      rcases lt_or_gt_of_ne hne23 with h23 | h23 <;>
        first
          | linarith
          | (rw [if_pos (by nlinarith), if_neg (not_lt.mpr (by nlinarith)),
              if_neg (not_lt.mpr (by nlinarith))]; ring)
          | (rw [if_neg (not_lt.mpr (by nlinarith)), if_pos (by nlinarith),
              if_neg (not_lt.mpr (by nlinarith))]; ring)
          | (rw [if_neg (not_lt.mpr (by nlinarith)), if_neg (not_lt.mpr (by nlinarith)),
              if_pos (by nlinarith)]; ring)

/-- **Nonnegative angle deficit**: the three angles of a geodesic triangle on pairwise
distinct vertices sum to at most `π`. -/
theorem deficit_nonneg (v₁ v₂ v₃ : UpperHalfPlane) (h₁₂ : v₁ ≠ v₂)
    (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    0 ≤ π - sectorAngle v₁ v₂ v₃ - sectorAngle v₂ v₁ v₃ - sectorAngle v₃ v₁ v₂ := by
  suffices H : ∀ w₁ w₂ w₃ : UpperHalfPlane, w₂.re = 0 → w₃.re = 0 → w₁ ≠ w₂ → w₁ ≠ w₃
      → w₂ ≠ w₃ →
      0 ≤ π - sectorAngle w₁ w₂ w₃ - sectorAngle w₂ w₁ w₃ - sectorAngle w₃ w₁ w₂ by
    obtain ⟨g, hg2, hg3⟩ := exists_verticalize v₂ v₃
    rw [← sectorAngle_smul g v₁ v₂ v₃, ← sectorAngle_smul g v₂ v₁ v₃,
      ← sectorAngle_smul g v₃ v₁ v₂]
    exact H (g • v₁) (g • v₂) (g • v₃) hg2 hg3
      (fun h => h₁₂ (smul_left_cancel g h)) (fun h => h₁₃ (smul_left_cancel g h))
      (fun h => h₂₃ (smul_left_cancel g h))
  intro w₁ w₂ w₃ h2 h3 h12 h13 h23
  rcases lt_trichotomy w₁.re 0 with hneg | hzero | hpos
  · rw [← sectorAngle_J w₁ w₂ w₃, ← sectorAngle_J w₂ w₁ w₃, ← sectorAngle_J w₃ w₁ w₂]
    have hJ12 : UpperHalfPlane.J • w₁ ≠ UpperHalfPlane.J • w₂ := fun h =>
      h12 (by rw [← J_J w₁, h, J_J])
    have hJ13 : UpperHalfPlane.J • w₁ ≠ UpperHalfPlane.J • w₃ := fun h =>
      h13 (by rw [← J_J w₁, h, J_J])
    have hJ23 : UpperHalfPlane.J • w₂ ≠ UpperHalfPlane.J • w₃ := fun h =>
      h23 (by rw [← J_J w₂, h, J_J])
    exact deficit_nonneg_pos (by rw [J_smul_re, h2, neg_zero])
      (by rw [J_smul_re, h3, neg_zero]) (by rw [J_smul_re]; linarith) hJ23
  · have hsum := deficit_collinear hzero h2 h3 h12 h13 h23
    linarith
  · exact deficit_nonneg_pos h2 h3 hpos h23

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

end RiemannDynamics

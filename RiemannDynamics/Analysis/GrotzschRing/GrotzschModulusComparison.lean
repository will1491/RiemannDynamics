/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.GrotzschKeystone
import RiemannDynamics.QC.Regularity.ModulusEnergyLower

/-!
# The Grötzsch modulus comparison over bounded admissible densities

The Grötzsch keystone `grotzschModulus_le_dirichletEnergy_ringPotential''` bounds the Grötzsch
modulus by the Dirichlet energy of an admissible ring potential `u` on a competing ring `U`. The
modulus–energy lower bound `dirichletEnergy_le_lintegral_sq_of_bounded_admissible` bounds that
energy by `∫ ρ²` for a **bounded** density `ρ` admissible for the connecting family
`connectingCurveFamily E grotzschOuter U`. Composing the two yields the modulus comparison in the
form the Grötzsch inequality consumes, restricted to bounded admissible densities.

The full comparison `grotzschModulus s ≤ curveModulus (connectingCurveFamily E grotzschOuter U)`
requires the per-density bound for *every* admissible `ρ`, including unbounded ones of finite
energy. Truncating an unbounded admissible density destroys admissibility, and the eikonal
upper-gradient inequality for the resulting lower semicontinuous `ρ`-length distance is not
available in this framework, so only the bounded-density comparison is landed here.

## Main statements

* `grotzschModulus_le_lintegral_sq_of_bounded_admissible_ring` — for every measurable density `ρ`
  admissible for `connectingCurveFamily E grotzschOuter U` and bounded by some `M : ℝ≥0`, the
  Grötzsch modulus is at most `∫ ρ²`, provided the four competitor-regularity facts of the
  modulus–energy lower bound hold for `ρ`.
* `grotzschModulus_le_boundedCurveModulus_ring` — the same bound phrased as the Grötzsch modulus
  being at most the infimum of `∫ ρ²` over bounded admissible densities.
-/

open Set Real MeasureTheory Complex
open scoped ENNReal NNReal

namespace RiemannDynamics

open Classical in
/-- **The Grötzsch modulus is at most the energy of a bounded admissible ring density.** For
`0 < s < 1`, a competing ring `U ⊆ ball 0 1` whose full outer collar `{r₀ < |z| < 1}` lies in `U`,
carrying an admissible ring potential `u` (harmonic, continuous up to `closure U`, `1` on the unit
circle, vanishing on the low-modulus frontier, valued in `[0, 1]`, with the flux and slice data of
the keystone) around a connected low-modulus frontier continuum `E` containing the puncture `0` and
the slit tip `s`, the Grötzsch modulus is at most `∫ ρ²` for every measurable density `ρ` admissible
for the connecting family `connectingCurveFamily E grotzschOuter U` and bounded by `M : ℝ≥0`.

The proof chains the Grötzsch keystone `grotzschModulus_le_dirichletEnergy_ringPotential''`
(`grotzschModulus s ≤ dirichletEnergy u U`) with the modulus–energy lower bound
`dirichletEnergy_le_lintegral_sq_of_bounded_admissible` (`dirichletEnergy u U ≤ ∫ ρ²`), whose four
competitor-regularity facts for the truncated `ρ`-length distance are carried as the hypotheses
`hcompcont`, `hcomploc`, `hcompW12`, `hHardy`. -/
theorem grotzschModulus_le_lintegral_sq_of_bounded_admissible_ring {s r₀ : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hsr₀ : s < r₀) (hr₀1 : r₀ < 1) {u : ℂ → ℝ} {U E : Set ℂ}
    (hUopen : IsOpen U)
    (hUball : U ⊆ Metric.ball (0 : ℂ) 1)
    (hcollarSub : RoundAnnulus 0 r₀ 1 ⊆ U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U))
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hEconn : IsConnected E) (h0E : (0 : ℂ) ∈ E) (hsE : (s : ℂ) ∈ E)
    (hEfront : E ⊆ frontier U)
    {ρ : ℂ → ℝ≥0∞} {M : ℝ≥0}
    (hadm : IsAdmissibleDensity ρ (connectingCurveFamily E grotzschOuter U))
    (hρbdd : ∀ x, ρ x ≤ (M : ℝ≥0∞))
    (hcompcont : Continuous (fun z =>
        (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z))
    (hcomploc : ∀ K ⊆ U, IsCompact K → ∃ L : ℝ≥0, LipschitzOnWith L (fun z =>
        (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) K)
    (hcompW12 : ∫⁻ z in U, (‖fderiv ℝ (fun z =>
        (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤)
    (hHardy : ∫⁻ z in U, ENNReal.ofReal
        (((if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) ^ 2
          / (Metric.infDist z Uᶜ) ^ 2) ≠ ⊤) :
    grotzschModulus s ≤ ∫⁻ z, (ρ z) ^ 2 := by
  have hUbdd : Bornology.IsBounded U :=
    (Metric.isBounded_ball).subset hUball
  calc grotzschModulus s
      ≤ dirichletEnergy u U :=
        grotzschModulus_le_dirichletEnergy_ringPotential'' hs0 hs1 hsr₀ hr₀1 hUopen hUball
          hcollarSub hu hucont hone hE0 hrangeU hpos hnc hcontR hEInt hcont hEconn h0E hsE hEfront
    _ ≤ ∫⁻ z, (ρ z) ^ 2 :=
        dirichletEnergy_le_lintegral_sq_of_bounded_admissible hUopen hUbdd hu hadm.1 hρbdd
          hcompcont hcomploc hcompW12 hHardy

open Classical in
/-- **The Grötzsch modulus is at most the infimum of `∫ ρ²` over bounded admissible ring
densities.** Under the ring-potential hypotheses of the Grötzsch keystone together with the
boundary-matching data of the modulus–energy lower bound (`hE`, `hfront`, segment accessibility
`haccess`, reachability `hrhoFin`, energy finiteness `hDu`, and the `u`-intrinsic Hardy finiteness
`hHardyU`), the Grötzsch modulus is at most the infimum of `∫ ρ²` over all densities `ρ` admissible
for `connectingCurveFamily E grotzschOuter U` and bounded by some `M : ℝ≥0`.

Chains the Grötzsch keystone `grotzschModulus_le_dirichletEnergy_ringPotential''` with the
competitor-free bounded modulus–energy lower bound
`dirichletEnergy_le_curveModulus_connecting_bounded`, which discharges the competitor continuity,
local Lipschitz, and finite squared-gradient facts internally from the carried boundary data. -/
theorem grotzschModulus_le_boundedCurveModulus_ring {s r₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsr₀ : s < r₀) (hr₀1 : r₀ < 1) {u : ℂ → ℝ} {U E : Set ℂ}
    (hUopen : IsOpen U)
    (hUball : U ⊆ Metric.ball (0 : ℂ) 1)
    (hcollarSub : RoundAnnulus 0 r₀ 1 ⊆ U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U))
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hEconn : IsConnected E) (h0E : (0 : ℂ) ∈ E) (hsE : (s : ℂ) ∈ E)
    (hEfront : E ⊆ frontier U)
    (hEval : ∀ z ∈ E, u z = 0) (hfront : frontier U ⊆ E ∪ grotzschOuter)
    (haccess : ∀ z₀ ∈ frontier U, ∀ᶠ z in nhdsWithin z₀ U, openSegment ℝ z₀ z ⊆ U)
    (hrhoFin : ∀ (ρ : ℂ → ℝ≥0∞),
        IsAdmissibleDensity ρ (connectingCurveFamily E grotzschOuter U) →
        (∀ z ∈ U, rhoDistance ρ E U z ≠ ⊤))
    (hDu : dirichletEnergy u U ≠ ⊤)
    (hHardyU : ∀ (ρ : ℂ → ℝ≥0∞),
        IsAdmissibleDensity ρ (connectingCurveFamily E grotzschOuter U) →
        (∀ M : ℝ≥0, (∀ x, ρ x ≤ (M : ℝ≥0∞)) →
          ∫⁻ z in U, ENNReal.ofReal
            (((if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) ^ 2
              / (Metric.infDist z Uᶜ) ^ 2) ≠ ⊤)) :
    grotzschModulus s
      ≤ ⨅ ρ ∈ {ρ : ℂ → ℝ≥0∞ |
          IsAdmissibleDensity ρ (connectingCurveFamily E grotzschOuter U) ∧
          ∃ M : ℝ≥0, ∀ x, ρ x ≤ (M : ℝ≥0∞)}, ∫⁻ z, (ρ z) ^ 2 := by
  have hUbdd : Bornology.IsBounded U :=
    (Metric.isBounded_ball).subset hUball
  calc grotzschModulus s
      ≤ dirichletEnergy u U :=
        grotzschModulus_le_dirichletEnergy_ringPotential'' hs0 hs1 hsr₀ hr₀1 hUopen hUball
          hcollarSub hu hucont hone hE0 hrangeU hpos hnc hcontR hEInt hcont hEconn h0E hsE hEfront
    _ ≤ _ :=
        dirichletEnergy_le_curveModulus_connecting_bounded hUopen hUbdd hu hucont hEval hone
          hfront haccess hrhoFin hDu hHardyU

open Classical in
/-- **Elementary positivity lower bound for the Grötzsch modulus.** For `0 < s < 1` the Grötzsch
modulus `grotzschModulus s` is at least `ENNReal.ofReal s`. Foliating the region under the unit
circle over the base segment `[0, s]` by the vertical segments `γ_x(t) = x + i·t·√(1 − x²)` — each
an admissible connecting curve of `connectingCurveFamily (grotzschInner s) grotzschOuter
(grotzschRing s)` running from the slit `[0, s]` to the unit circle inside the ring — gives, for
every admissible density `ρ`, the fibrewise bound `∫_{y ∈ (0, √(1−x²))} ρ(x+iy) dy ≥ 1` (after the
per-`x` change of variables `y = t√(1−x²)`); one-dimensional Cauchy–Schwarz then yields
`∫_{y ∈ (0, √(1−x²))} ρ(x+iy)² dy ≥ 1/√(1−x²) ≥ 1`, and integrating over `x ∈ (0, s)` and comparing
with the full plane integral gives `∫ ρ² ≥ s`. Taking the infimum over admissible `ρ` gives the
claim. -/
theorem ofReal_le_grotzschModulus {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ENNReal.ofReal s ≤ grotzschModulus s := by
  unfold grotzschModulus curveModulus
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hρadm⟩
  -- Abbreviations for the vertical-segment foliation.
  set c : ℝ → ℝ := fun x => Real.sqrt (1 - x ^ 2) with hc
  have hcpos : ∀ x ∈ Set.Ioo (0 : ℝ) s, 0 < c x := by
    intro x hx
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2, hs1]
    exact Real.sqrt_pos.mpr (by linarith)
  have hcle1 : ∀ x, c x ≤ 1 := by
    intro x
    have h : (1 : ℝ) - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    calc c x = Real.sqrt (1 - x ^ 2) := rfl
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
      _ = 1 := Real.sqrt_one
  -- The vertical segment through `x`.
  set seg : ℝ → ℝ → ℂ := fun x t => (x : ℂ) + (t * c x : ℝ) * Complex.I with hseg
  -- Per-fibre lower bound: `1 ≤ ∫_{y ∈ (0, c x)} ρ(x + i y) dy` for `x ∈ (0, s)`.
  have fibre_lower : ∀ x ∈ Set.Ioo (0 : ℝ) s,
      1 ≤ ∫⁻ y in Set.Ioo (0 : ℝ) (c x), ρ ((x : ℂ) + (y : ℝ) * Complex.I) := by
    intro x hx
    have hcx : 0 < c x := hcpos x hx
    set γ : ℝ → ℂ := seg x with hγ
    have hγeq : ∀ t, γ t = (x : ℂ) + (t * c x : ℝ) * Complex.I := fun t => rfl
    -- derivative of γ is `i·c x`, constant.
    have hderiv : ∀ t, HasDerivAt γ ((c x : ℝ) * Complex.I) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (t * c x : ℝ)) (c x) t := by
        simpa using (hasDerivAt_id t).mul_const (c x)
      have h2 : HasDerivAt (fun t : ℝ => ((t * c x : ℝ) : ℂ)) ((c x : ℝ) : ℂ) t :=
        h1.ofReal_comp
      have h3 : HasDerivAt (fun t : ℝ => ((t * c x : ℝ) : ℂ) * Complex.I)
          (((c x : ℝ) : ℂ) * Complex.I) t := h2.mul_const Complex.I
      have h4 := h3.const_add (x : ℂ)
      exact h4
    have hderiveq : ∀ t, deriv γ t = (c x : ℝ) * Complex.I := fun t => (hderiv t).deriv
    have hnormderiv : ∀ t, ‖deriv γ t‖ = c x := by
      intro t; rw [hderiveq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hcx]
    -- γ is Lipschitz hence continuous and AC.
    have hlipγ : LipschitzWith (NNReal.mk (c x) hcx.le) γ := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [dist_eq_norm, dist_eq_norm, hγeq, hγeq]
      rw [show ((x : ℂ) + (u * c x : ℝ) * Complex.I) - ((x : ℂ) + (v * c x : ℝ) * Complex.I)
          = (((u - v) * c x : ℝ)) * Complex.I from by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hcx, NNReal.coe_mk, Real.norm_eq_abs, mul_comm]
    have hcontγ : Continuous γ := hlipγ.continuous
    have hacγ : AbsolutelyContinuousOnInterval γ 0 1 :=
      (hlipγ.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
    -- membership in the connecting family.
    have hmemf : γ ∈ connectingCurveFamily (grotzschInner s) grotzschOuter (grotzschRing s) := by
      refine ⟨hcontγ, hacγ, ?_, ?_, ?_⟩
      · -- `γ 0 = x ∈ segment[0, s]`.
        have h0 : γ 0 = (x : ℂ) := by rw [hγeq]; push_cast; ring
        rw [h0, grotzschInner]
        refine ⟨1 - x / s, x / s, ?_, ?_, by ring, ?_⟩
        · rw [sub_nonneg, div_le_one hs0]; exact hx.2.le
        · exact le_of_lt (div_pos hx.1 hs0)
        · rw [Complex.real_smul, Complex.real_smul, mul_zero, zero_add,
            ← Complex.ofReal_mul, div_mul_cancel₀ _ hs0.ne']
      · -- `γ 1 = x + i·c x` on the unit circle.
        have h1 : γ 1 = (x : ℂ) + (c x : ℝ) * Complex.I := by rw [hγeq]; push_cast; ring
        rw [h1, grotzschOuter, Metric.mem_sphere, dist_zero_right, Complex.norm_add_mul_I, hc]
        rw [Real.sq_sqrt (by nlinarith [hx.1, hx.2, hs1] : (0:ℝ) ≤ 1 - x ^ 2)]
        rw [show x ^ 2 + (1 - x ^ 2) = 1 from by ring, Real.sqrt_one]
      · -- interior in the Grötzsch ring.
        intro t ht
        have himpos : 0 < t * c x := mul_pos ht.1 hcx
        have hpt : γ t = (x : ℂ) + ((t * c x : ℝ) : ℝ) * Complex.I := by rw [hγeq]
        rw [grotzschRing]
        refine ⟨?_, ?_⟩
        · -- in the open unit ball.
          rw [Metric.mem_ball, dist_zero_right, hpt, Complex.norm_add_mul_I]
          rw [show ((t * c x : ℝ)) ^ 2 = t ^ 2 * (c x) ^ 2 from by ring]
          rw [hc, Real.sq_sqrt (by nlinarith [hx.1, hx.2, hs1] : (0:ℝ) ≤ 1 - x ^ 2)]
          have ht1 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
          rw [show x ^ 2 + t ^ 2 * (1 - x ^ 2) = 1 - (1 - t ^ 2) * (1 - x ^ 2) from by ring]
          have hprod : 0 < (1 - t ^ 2) * (1 - x ^ 2) := by
            apply mul_pos (by linarith)
            nlinarith [hx.1, hx.2, hs1]
          have : Real.sqrt (1 - (1 - t ^ 2) * (1 - x ^ 2)) < Real.sqrt 1 := by
            apply Real.sqrt_lt_sqrt (by nlinarith [hprod]) (by linarith)
          rwa [Real.sqrt_one] at this
        · -- off the slit: imaginary part positive, so not on segment [0,s] ⊆ real axis.
          intro hmem
          obtain ⟨a, b, _, _, _, ha⟩ := hmem
          have him : (γ t).im = 0 := by
            rw [← ha]
            simp only [Complex.real_smul, mul_zero, zero_add, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          rw [hpt] at him
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, zero_add, mul_one, zero_mul, add_zero] at him
          exact absurd him himpos.ne'
    have hadm : 1 ≤ arcLengthLineIntegral ρ γ := hρadm γ hmemf
    -- Rewrite the arc-length integral as `∫_{(0,c x)} ρ(x+iy) dy` via the 1D change of variables.
    have hcontseg : Continuous (fun y : ℝ => (x : ℂ) + (y : ℝ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have himg : (fun t : ℝ => t * c x) '' Set.Ioo 0 1 = Set.Ioo 0 (c x) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioo]
      constructor
      · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
        exact ⟨mul_pos ht0 hcx, by nlinarith [ht1, hcx]⟩
      · rintro ⟨hy0, hyc⟩
        refine ⟨y / c x, ⟨by positivity, ?_⟩, by rw [div_mul_cancel₀ _ hcx.ne']⟩
        rw [div_lt_one hcx]; exact hyc
    have hcov : ∫⁻ y in Set.Ioo (0 : ℝ) (c x), ρ ((x : ℂ) + (y : ℝ) * Complex.I)
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (c x)
            * ρ ((x : ℂ) + ((t * c x : ℝ) : ℝ) * Complex.I) := by
      rw [← himg]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
        (f := fun t => t * c x) (f' := fun _ => c x) ?_ ?_]
      · apply lintegral_congr
        intro t; rw [abs_of_pos hcx]
      · intro t _
        have : HasDerivAt (fun t : ℝ => t * c x) (c x) t := by
          simpa using (hasDerivAt_id t).mul_const (c x)
        exact this.hasDerivWithinAt
      · intro a _ b _ hab
        simp only at hab
        exact mul_right_cancel₀ hcx.ne' hab
    have harc : arcLengthLineIntegral ρ γ
        = ∫⁻ y in Set.Ioo (0 : ℝ) (c x), ρ ((x : ℂ) + (y : ℝ) * Complex.I) := by
      rw [hcov]
      unfold arcLengthLineIntegral
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
      apply lintegral_congr
      intro t
      rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm], hnormderiv, mul_comm]
    rw [← harc]; exact hadm
  -- Per-fibre Cauchy–Schwarz: `1 ≤ ∫_{(0,c x)} ρ(x+iy)²`.
  have fibre_sq_lower : ∀ x ∈ Set.Ioo (0 : ℝ) s,
      1 ≤ ∫⁻ y in Set.Ioo (0 : ℝ) (c x), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
    intro x hx
    have hcx : 0 < c x := hcpos x hx
    set μ := volume.restrict (Set.Ioo (0 : ℝ) (c x)) with hμ
    set f : ℝ → ℝ≥0∞ := fun y => ρ ((x : ℂ) + (y : ℝ) * Complex.I) with hf
    set g : ℝ → ℝ≥0∞ := fun _ => 1 with hg
    have hcontseg : Continuous (fun y : ℝ => (x : ℂ) + (y : ℝ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hmeasf : AEMeasurable f μ := (hρmeas.comp hcontseg.measurable).aemeasurable
    have hmeasg : AEMeasurable g μ := aemeasurable_const
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (Real.HolderConjugate.two_two) hmeasf hmeasg
    have hone : 1 ≤ ∫⁻ y, (f * g) y ∂μ := by
      have : ∫⁻ y, (f * g) y ∂μ = ∫⁻ y in Set.Ioo (0 : ℝ) (c x),
          ρ ((x : ℂ) + (y : ℝ) * Complex.I) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hf, hg]
      rw [this]; exact fibre_lower x hx
    have hgsq : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ENNReal.ofReal (c x) := by
      have : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ∫⁻ _y in Set.Ioo (0 : ℝ) (c x), (1 : ℝ≥0∞) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hg]
      rw [this, setLIntegral_const, Real.volume_Ioo, sub_zero]
      simp [ENNReal.ofReal]
    have hfsq : ∫⁻ y, f y ^ (2 : ℝ) ∂μ
        = ∫⁻ y in Set.Ioo (0 : ℝ) (c x), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
      rw [hμ]; apply lintegral_congr; intro y
      rw [hf, ENNReal.rpow_two, sq]
    rw [hfsq, hgsq] at hholder
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hholder
    -- `1 ≤ (∫ f²)^{1/2} · (c x)^{1/2}` ⇒ `1 ≤ (∫ f²) · c x` ⇒ `∫ f² ≥ 1/c x ≥ 1`.
    set A : ℝ≥0∞ := ∫⁻ y in Set.Ioo (0 : ℝ) (c x),
      (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 with hA
    have hle : (1 : ℝ≥0∞) ≤ A ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal (c x)) ^ (2 : ℝ)⁻¹ :=
      le_trans hone hholder
    have hAcx : (1 : ℝ≥0∞) ≤ A * ENNReal.ofReal (c x) := by
      have h := ENNReal.rpow_le_rpow hle (show (0 : ℝ) ≤ 2 by norm_num)
      rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at h
      rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one] at h
    -- since `c x ≤ 1`, `A · c x ≤ A`, so `1 ≤ A`.
    calc (1 : ℝ≥0∞) ≤ A * ENNReal.ofReal (c x) := hAcx
      _ ≤ A * 1 := by
          gcongr
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
          exact ENNReal.ofReal_le_ofReal (hcle1 x)
      _ = A := mul_one A
  -- Integrate the fibre bound over `x ∈ (0, s)` and compare with the full plane energy.
  -- First: `s ≤ ∫_{x ∈ (0,s)} ∫_{y ∈ (0, c x)} ρ(x+iy)² dy dx`.
  have hstep1 : ENNReal.ofReal s ≤ ∫⁻ x in Set.Ioo (0 : ℝ) s,
      ∫⁻ y in Set.Ioo (0 : ℝ) (c x), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
    calc ENNReal.ofReal s = ∫⁻ _x in Set.Ioo (0 : ℝ) s, (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, one_mul]
      _ ≤ ∫⁻ x in Set.Ioo (0 : ℝ) s,
            ∫⁻ y in Set.Ioo (0 : ℝ) (c x), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
          apply lintegral_mono_ae
          refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => fibre_sq_lower x hx)
  -- Second: the iterated integral is ≤ the full plane energy `∫ ρ²`.
  have hstep2 : (∫⁻ x in Set.Ioo (0 : ℝ) s,
      ∫⁻ y in Set.Ioo (0 : ℝ) (c x), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2)
      ≤ ∫⁻ z, (ρ z) ^ 2 := by
    -- extend `y` to all of ℝ and `x` to all of ℝ, then identify with the plane integral.
    have hcontseg2 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℝ) * Complex.I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hmeas2 : Measurable
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2) :=
      (hρmeas.comp hcontseg2.measurable).pow_const 2
    have hmono1 : (∫⁻ x in Set.Ioo (0 : ℝ) s,
        ∫⁻ y in Set.Ioo (0 : ℝ) (c x), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2)
        ≤ ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
      refine lintegral_mono' Measure.restrict_le_self (fun x => ?_)
      exact setLIntegral_le_lintegral _ _
    have hprod : (∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2 := by
      have hae : AEMeasurable (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
          ((volume : Measure ℝ).prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hmeas2.aemeasurable
      rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
      exact (lintegral_prod _ hae).symm
    have hplane : (∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ z, (ρ z) ^ 2 := by
      rw [← Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
        Complex.measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)]
      apply lintegral_congr
      intro z
      simp only [Complex.measurableEquivRealProd_apply]
      congr 2
      exact Complex.re_add_im z
    rw [hprod, hplane] at hmono1
    exact hmono1
  exact le_trans hstep1 hstep2

open Classical in
/-- **Positivity lower bound for the connecting modulus of a small connected hole.** For `0 < s`
with `s² < 1/2`, and a compact connected set `E ⊆ closedBall 0 s` containing the puncture `0` and
the point `s`, the conformal modulus `curveModulus (connectingCurveFamily E grotzschOuter
(ball 0 1 \ E))` of the family of curves joining `E` to the unit circle inside `ball 0 1 \ E` is at
least `ENNReal.ofReal s`. The projection `Complex.re '' E` is connected and contains `0` and `s`, so
it covers the base segment `[0, s]`, giving for each `x ∈ (0, s)` a nonempty compact vertical slice
`S_x = {y | x + i y ∈ E}`. Using the top slice point `y⁺ = sSup S_x` (or the bottom point
`y⁻ = sInf S_x` when `y⁺ < 0`), the vertical segment from that slice point to the unit circle at
`x + i·√(1 − x²)` (respectively `x − i·√(1 − x²)`) is an admissible connecting curve of length at
most `√(1 − x²) ≤ 1`; one-dimensional Cauchy–Schwarz gives the fibrewise bound
`∫_{y ∈ (−√(1−x²), √(1−x²))} ρ(x + i y)² dy ≥ 1`, and integrating over `x ∈ (0, s)` and comparing
with the full plane integral gives `∫ ρ² ≥ s`. Taking the infimum over admissible `ρ` gives the
claim. The gate `s² < 1/2` guarantees `s < √(1 − x²)`, so the slice point lies strictly below the
circle and the segment is non-degenerate. -/
theorem ofReal_le_curveModulus_of_connected_hole {s : ℝ} (hs0 : 0 < s) (hs2 : s ^ 2 < 1 / 2)
    {E : Set ℂ} (hEcpt : IsCompact E) (hEconn : IsConnected E) (h0E : (0 : ℂ) ∈ E)
    (hsE : (s : ℂ) ∈ E) (hEball : E ⊆ Metric.closedBall (0 : ℂ) s) :
    ENNReal.ofReal s
      ≤ curveModulus (connectingCurveFamily E grotzschOuter (Metric.ball (0 : ℂ) 1 \ E)) := by
  -- Basic numeric facts from the gate `s² < 1/2`.
  have hs1 : s < 1 := by nlinarith [hs2, hs0]
  have hEclosed : IsClosed E := hEcpt.isClosed
  unfold curveModulus
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hρadm⟩
  -- `c x = √(1 - x²)`, the height of the unit circle over `x`.
  set c : ℝ → ℝ := fun x => Real.sqrt (1 - x ^ 2) with hc
  have hcpos : ∀ x ∈ Set.Ioo (0 : ℝ) s, 0 < c x := by
    intro x hx
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2, hs1]
    exact Real.sqrt_pos.mpr (by linarith)
  have hcle1 : ∀ x, c x ≤ 1 := by
    intro x
    have h : (1 : ℝ) - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    calc c x = Real.sqrt (1 - x ^ 2) := rfl
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
      _ = 1 := Real.sqrt_one
  -- `s < c x` for `x ∈ (0, s)`: since `x² < s² < 1/2 < 1 - s² ≤ 1 - x²`.
  have hslt : ∀ x ∈ Set.Ioo (0 : ℝ) s, s < c x := by
    intro x hx
    have hx2 : x ^ 2 < s ^ 2 := by nlinarith [hx.1, hx.2]
    have hs_sq : s ^ 2 < 1 - x ^ 2 := by nlinarith [hs2, hx2]
    have : Real.sqrt (s ^ 2) < c x := Real.sqrt_lt_sqrt (sq_nonneg s) hs_sq
    rwa [Real.sqrt_sq hs0.le] at this
  -- The vertical slice `S_x = {y | x + i y ∈ E}` and its embedding into ℂ.
  set emb : ℝ → ℝ → ℂ := fun x y => (x : ℂ) + (y : ℝ) * Complex.I with hemb
  have hembcont : ∀ x, Continuous (emb x) :=
    fun x => continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  set S : ℝ → Set ℝ := fun x => (emb x) ⁻¹' E with hS
  -- Each slice is compact: closed preimage of `E`, contained in the compact `[-s, s]`.
  have hSsub : ∀ x, S x ⊆ Set.Icc (-s) s := by
    intro x y hy
    have hmem : emb x y ∈ E := hy
    have hball : emb x y ∈ Metric.closedBall (0 : ℂ) s := hEball hmem
    rw [Metric.mem_closedBall, dist_zero_right, hemb, Complex.norm_add_mul_I] at hball
    have hxy : x ^ 2 + y ^ 2 ≤ s ^ 2 := by
      have h1 : Real.sqrt (x ^ 2 + y ^ 2) ^ 2 ≤ s ^ 2 := by
        apply sq_le_sq'
        · linarith [Real.sqrt_nonneg (x ^ 2 + y ^ 2), hball]
        · exact hball
      rwa [Real.sq_sqrt (by positivity : (0:ℝ) ≤ x ^ 2 + y ^ 2)] at h1
    have hy2 : y ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg x]
    rw [Set.mem_Icc]
    constructor
    · nlinarith [hy2, hs0]
    · nlinarith [hy2, hs0]
  have hScompact : ∀ x, IsCompact (S x) := by
    intro x
    apply IsCompact.of_isClosed_subset isCompact_Icc (hEclosed.preimage (hembcont x)) (hSsub x)
  -- The projection `Complex.re '' E` covers `[0, s]`, so each slice `S x` (x ∈ (0,s)) is nonempty.
  have hproj : Set.Icc (0 : ℝ) s ⊆ Complex.re '' E := by
    have hconn : IsConnected (Complex.re '' E) := hEconn.image _ Complex.continuous_re.continuousOn
    refine hconn.Icc_subset ?_ ?_
    · exact ⟨0, h0E, by simp⟩
    · exact ⟨(s : ℂ), hsE, by simp⟩
  have hSne : ∀ x ∈ Set.Ioo (0 : ℝ) s, (S x).Nonempty := by
    intro x hx
    obtain ⟨w, hwE, hwre⟩ := hproj ⟨hx.1.le, hx.2.le⟩
    refine ⟨w.im, ?_⟩
    have : emb x w.im = w := by
      rw [hemb, ← hwre]; exact (Complex.re_add_im w)
    rw [hS]; simp only [Set.mem_preimage, this]; exact hwE
  -- Top/bottom slice points, in `S x` and controlled by `[-s, s]`.
  set yTop : ℝ → ℝ := fun x => sSup (S x) with hyTop
  set yBot : ℝ → ℝ := fun x => sInf (S x) with hyBot
  have hyTopMem : ∀ x ∈ Set.Ioo (0 : ℝ) s, yTop x ∈ S x :=
    fun x hx => (hScompact x).sSup_mem (hSne x hx)
  have hyBotMem : ∀ x ∈ Set.Ioo (0 : ℝ) s, yBot x ∈ S x :=
    fun x hx => (hScompact x).sInf_mem (hSne x hx)
  have hyTople : ∀ x ∈ Set.Ioo (0 : ℝ) s, yTop x ≤ s := fun x hx =>
    ((Set.mem_Icc.mp (hSsub x (hyTopMem x hx))).2)
  have hyBotge : ∀ x ∈ Set.Ioo (0 : ℝ) s, -s ≤ yBot x := fun x hx =>
    ((Set.mem_Icc.mp (hSsub x (hyBotMem x hx))).1)
  -- `y ∉ S x` when `y > yTop x` or `y < yBot x`.
  have hSbddA : ∀ x ∈ Set.Ioo (0 : ℝ) s, BddAbove (S x) := fun x hx => (hScompact x).bddAbove
  have hSbddB : ∀ x ∈ Set.Ioo (0 : ℝ) s, BddBelow (S x) := fun x hx => (hScompact x).bddBelow
  have hnotTop : ∀ x ∈ Set.Ioo (0 : ℝ) s, ∀ y, yTop x < y → y ∉ S x := by
    intro x hx y hy hmem
    exact absurd (le_csSup (hSbddA x hx) hmem) (not_le.mpr hy)
  have hnotBot : ∀ x ∈ Set.Ioo (0 : ℝ) s, ∀ y, y < yBot x → y ∉ S x := by
    intro x hx y hy hmem
    exact absurd (csInf_le (hSbddB x hx) hmem) (not_le.mpr hy)
  -- Reusable vertical-segment helper: from an E-endpoint at height `p` to a circle-endpoint at
  -- height `q`, of length `|q - p| ≤ 1`, whose open interior lies in the ring, forces
  -- `∫_{(min p q, max p q)} ρ² ≥ 1`.
  have seg_bound : ∀ (x p q : ℝ), p ≠ q → |q - p| ≤ 1 →
      emb x p ∈ E → emb x q ∈ grotzschOuter →
      (∀ y ∈ Set.Ioo (min p q) (max p q), emb x y ∈ Metric.ball (0 : ℂ) 1 \ E) →
      1 ≤ ∫⁻ y in Set.Ioo (min p q) (max p q), (ρ (emb x y)) ^ 2 := by
    intro x p q hpq hlen hpE hqO hint
    set L : ℝ → ℝ := fun t => p + t * (q - p) with hL
    set γ : ℝ → ℂ := fun t => emb x (L t) with hγ
    have hqp : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    -- Derivative of `γ` is the constant `(q - p) i`; its norm is `|q - p|`.
    have hderiv : ∀ t, HasDerivAt γ (((q - p : ℝ) : ℂ) * Complex.I) t := by
      intro t
      have h1 : HasDerivAt L (q - p) t := by
        rw [hL]
        have := ((hasDerivAt_id t).mul_const (q - p)).const_add p
        simpa using this
      have h2 : HasDerivAt (fun t => ((L t : ℝ) : ℂ)) (((q - p : ℝ) : ℂ)) t := h1.ofReal_comp
      have h3 : HasDerivAt (fun t => ((L t : ℝ) : ℂ) * Complex.I)
          (((q - p : ℝ) : ℂ) * Complex.I) t := h2.mul_const Complex.I
      have h4 := h3.const_add (x : ℂ)
      simpa [hγ, hemb, hL] using h4
    have hderiveq : ∀ t, deriv γ t = ((q - p : ℝ) : ℂ) * Complex.I := fun t => (hderiv t).deriv
    have hnormderiv : ∀ t, ‖deriv γ t‖ = |q - p| := by
      intro t; rw [hderiveq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
    -- `γ` is Lipschitz, hence continuous and AC on `[0, 1]`.
    have hlipγ : LipschitzWith (NNReal.mk |q - p| (abs_nonneg _)) γ := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [dist_eq_norm, dist_eq_norm, hγ, hemb, hL]
      rw [show ((x : ℂ) + ((p + u * (q - p) : ℝ) : ℂ) * Complex.I)
          - ((x : ℂ) + ((p + v * (q - p) : ℝ) : ℂ) * Complex.I)
          = (((u - v) * (q - p) : ℝ)) * Complex.I from by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        NNReal.coe_mk, Real.norm_eq_abs, mul_comm]
    have hcontγ : Continuous γ := hlipγ.continuous
    have hacγ : AbsolutelyContinuousOnInterval γ 0 1 :=
      (hlipγ.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
    -- `L t` lies strictly between `p` and `q` for `t ∈ (0, 1)`.
    have hLmem : ∀ t ∈ Set.Ioo (0 : ℝ) 1, L t ∈ Set.Ioo (min p q) (max p q) := by
      intro t ht
      rcases lt_or_gt_of_ne hpq with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le, hL]
        constructor
        · nlinarith [ht.1, ht.2, sub_pos.mpr hlt]
        · nlinarith [ht.1, ht.2, sub_pos.mpr hlt]
      · rw [min_eq_right hgt.le, max_eq_left hgt.le, hL]
        constructor
        · nlinarith [ht.1, ht.2, sub_neg.mpr hgt]
        · nlinarith [ht.1, ht.2, sub_neg.mpr hgt]
    -- `γ` is a curve of the connecting family, so its arc-length integral is at least `1`.
    have hmemf : γ ∈ connectingCurveFamily E grotzschOuter (Metric.ball (0 : ℂ) 1 \ E) := by
      refine ⟨hcontγ, hacγ, ?_, ?_, ?_⟩
      · show γ 0 ∈ E
        have : γ 0 = emb x p := by rw [hγ, hL]; simp
        rw [this]; exact hpE
      · show γ 1 ∈ grotzschOuter
        have : γ 1 = emb x q := by rw [hγ, hL]; simp
        rw [this]; exact hqO
      · intro t ht
        have : γ t = emb x (L t) := rfl
        rw [this]; exact hint (L t) (hLmem t ht)
    have hadm : 1 ≤ arcLengthLineIntegral ρ γ := hρadm γ hmemf
    -- Change of variables `y = L t` rewrites the arc-length integral over `(min, max)`.
    have hLimg : L '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (min p q) (max p q) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioo]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact hLmem t ht
      · intro hy
        refine ⟨(y - p) / (q - p), ⟨?_, ?_⟩, ?_⟩
        rotate_right
        · rw [hL]; field_simp; ring
        · rcases lt_or_gt_of_ne hpq with hlt | hgt
          · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hy
            exact div_pos (by linarith [hy.1]) (by linarith [sub_pos.mpr hlt])
          · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hy
            exact div_pos_of_neg_of_neg (by linarith [hy.2]) (by linarith [sub_neg.mpr hgt])
        · rcases lt_or_gt_of_ne hpq with hlt | hgt
          · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hy
            rw [div_lt_one (by linarith [sub_pos.mpr hlt])]; linarith [hy.2]
          · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hy
            rw [div_lt_one_of_neg (by linarith [sub_neg.mpr hgt])]; linarith [hy.1]
    have hcov : ∫⁻ y in Set.Ioo (min p q) (max p q), ρ (emb x y)
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (|q - p|) * ρ (emb x (L t)) := by
      rw [← hLimg]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
        (f := L) (f' := fun _ => q - p) ?_ ?_]
      · intro t _
        have : HasDerivAt L (q - p) t := by
          rw [hL]
          have := ((hasDerivAt_id t).mul_const (q - p)).const_add p
          simpa using this
        exact this.hasDerivWithinAt
      · intro a _ b _ hab
        simp only [hL] at hab
        have : a * (q - p) = b * (q - p) := by linarith [hab]
        exact mul_right_cancel₀ hqp this
    have harc : arcLengthLineIntegral ρ γ
        = ∫⁻ y in Set.Ioo (min p q) (max p q), ρ (emb x y) := by
      rw [hcov]
      unfold arcLengthLineIntegral
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
      apply lintegral_congr
      intro t
      rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm], hnormderiv, mul_comm]
    have hlow : 1 ≤ ∫⁻ y in Set.Ioo (min p q) (max p q), ρ (emb x y) := by
      rw [← harc]; exact hadm
    -- Cauchy–Schwarz on the interval of length `max - min = |q - p| ≤ 1`.
    set I := Set.Ioo (min p q) (max p q) with hI
    have hlenIcc : max p q - min p q = |q - p| := by
      rcases lt_or_gt_of_ne hpq with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le, abs_of_pos (sub_pos.mpr hlt)]
      · rw [min_eq_right hgt.le, max_eq_left hgt.le, abs_of_neg (sub_neg.mpr hgt)]; ring
    have hmm : min p q ≤ max p q := min_le_max
    set μ := volume.restrict I with hμ
    set f : ℝ → ℝ≥0∞ := fun y => ρ (emb x y) with hf
    set g : ℝ → ℝ≥0∞ := fun _ => 1 with hg
    have hmeasf : AEMeasurable f μ := (hρmeas.comp (hembcont x).measurable).aemeasurable
    have hmeasg : AEMeasurable g μ := aemeasurable_const
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (Real.HolderConjugate.two_two) hmeasf hmeasg
    have hone : 1 ≤ ∫⁻ y, (f * g) y ∂μ := by
      have hfg : ∫⁻ y, (f * g) y ∂μ = ∫⁻ y in I, ρ (emb x y) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hf, hg]
      rw [hfg]; exact hlow
    have hgsq : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ENNReal.ofReal (|q - p|) := by
      have : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ∫⁻ _y in I, (1 : ℝ≥0∞) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hg]
      rw [this, setLIntegral_const, Real.volume_Ioo, hlenIcc]
      simp [ENNReal.ofReal]
    have hfsq : ∫⁻ y, f y ^ (2 : ℝ) ∂μ = ∫⁻ y in I, (ρ (emb x y)) ^ 2 := by
      rw [hμ]; apply lintegral_congr; intro y; rw [hf, ENNReal.rpow_two, sq]
    rw [hfsq, hgsq] at hholder
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hholder
    set A : ℝ≥0∞ := ∫⁻ y in I, (ρ (emb x y)) ^ 2 with hA
    have hle : (1 : ℝ≥0∞) ≤ A ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal (|q - p|)) ^ (2 : ℝ)⁻¹ :=
      le_trans hone hholder
    have hAcx : (1 : ℝ≥0∞) ≤ A * ENNReal.ofReal (|q - p|) := by
      have h := ENNReal.rpow_le_rpow hle (show (0 : ℝ) ≤ 2 by norm_num)
      rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at h
      rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one] at h
    calc (1 : ℝ≥0∞) ≤ A * ENNReal.ofReal (|q - p|) := hAcx
      _ ≤ A * 1 := by
          gcongr
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
          exact ENNReal.ofReal_le_ofReal hlen
      _ = A := mul_one A
  -- The unit-circle points `x ± i·c x` over `x`.
  have hcirc : ∀ x ∈ Set.Ioo (0 : ℝ) s, ∀ σ : ℝ, |σ| = c x → emb x σ ∈ grotzschOuter := by
    intro x hx σ hσ
    have hx2 : (0:ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2, hs1]
    rw [hemb, grotzschOuter, Metric.mem_sphere, dist_zero_right, Complex.norm_add_mul_I]
    rw [show σ ^ 2 = |σ| ^ 2 from (sq_abs σ).symm, hσ, hc, Real.sq_sqrt hx2]
    rw [show x ^ 2 + (1 - x ^ 2) = 1 from by ring, Real.sqrt_one]
  -- Per-fibre Cauchy–Schwarz: `1 ≤ ∫_{(-c x, c x)} ρ(x + i y)²`.
  have fibre_sq_lower : ∀ x ∈ Set.Ioo (0 : ℝ) s,
      1 ≤ ∫⁻ y in Set.Ioo (-(c x)) (c x), (ρ (emb x y)) ^ 2 := by
    intro x hx
    have hcx : 0 < c x := hcpos x hx
    have hsc : s < c x := hslt x hx
    rcases le_or_gt 0 (yTop x) with hnn | hneg
    · -- Up-segment from the top slice point.
      have hlt : yTop x < c x := lt_of_le_of_lt (hyTople x hx) hsc
      have hpq : yTop x ≠ c x := ne_of_lt hlt
      have hlen : |c x - yTop x| ≤ 1 := by
        rw [abs_of_pos (by linarith [hlt] : (0:ℝ) < c x - yTop x)]
        linarith [hnn, hcle1 x]
      have hint : ∀ y ∈ Set.Ioo (min (yTop x) (c x)) (max (yTop x) (c x)),
          emb x y ∈ Metric.ball (0 : ℂ) 1 \ E := by
        intro y hy
        rw [min_eq_left hlt.le, max_eq_right hlt.le] at hy
        refine ⟨?_, hnotTop x hx y hy.1⟩
        rw [hemb, Metric.mem_ball, dist_zero_right, Complex.norm_add_mul_I]
        have : y ^ 2 < (c x) ^ 2 := by nlinarith [hy.1, hy.2, hnn]
        have hx2 : (0:ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2, hs1]
        rw [hc, Real.sq_sqrt hx2] at this
        calc Real.sqrt (x ^ 2 + y ^ 2) < Real.sqrt 1 := by
              apply Real.sqrt_lt_sqrt (by positivity); nlinarith [this]
          _ = 1 := Real.sqrt_one
      have hseg := seg_bound x (yTop x) (c x) hpq hlen (hyTopMem x hx)
        (hcirc x hx (c x) (by rw [abs_of_pos hcx])) hint
      rw [min_eq_left hlt.le, max_eq_right hlt.le] at hseg
      refine le_trans hseg (lintegral_mono_set ?_)
      intro y hy; exact ⟨by linarith [hy.1, hnn, hcx], hy.2⟩
    · -- Down-segment from the bottom slice point (whole slice below the axis).
      have hbotle : yBot x ≤ yTop x :=
        csInf_le_csSup (hSne x hx) (hSbddB x hx) (hSbddA x hx)
      have hbotneg : yBot x < 0 := lt_of_le_of_lt hbotle hneg
      have hbotgt : -(c x) < yBot x := lt_of_lt_of_le (by linarith [hsc]) (hyBotge x hx)
      have hpq : yBot x ≠ -(c x) := ne_of_gt hbotgt
      have hlen : |(-(c x)) - yBot x| ≤ 1 := by
        rw [abs_of_neg (by linarith [hbotgt] : (-(c x)) - yBot x < 0)]
        linarith [hbotneg, hcle1 x]
      have hint : ∀ y ∈ Set.Ioo (min (yBot x) (-(c x))) (max (yBot x) (-(c x))),
          emb x y ∈ Metric.ball (0 : ℂ) 1 \ E := by
        intro y hy
        rw [min_eq_right hbotgt.le, max_eq_left hbotgt.le] at hy
        refine ⟨?_, hnotBot x hx y hy.2⟩
        rw [hemb, Metric.mem_ball, dist_zero_right, Complex.norm_add_mul_I]
        have : y ^ 2 < (c x) ^ 2 := by nlinarith [hy.1, hy.2, hbotneg]
        have hx2 : (0:ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2, hs1]
        rw [hc, Real.sq_sqrt hx2] at this
        calc Real.sqrt (x ^ 2 + y ^ 2) < Real.sqrt 1 := by
              apply Real.sqrt_lt_sqrt (by positivity); nlinarith [this]
          _ = 1 := Real.sqrt_one
      have hseg := seg_bound x (yBot x) (-(c x)) hpq hlen (hyBotMem x hx)
        (hcirc x hx (-(c x)) (by rw [abs_neg, abs_of_pos hcx])) hint
      rw [min_eq_right hbotgt.le, max_eq_left hbotgt.le] at hseg
      refine le_trans hseg (lintegral_mono_set ?_)
      intro y hy; exact ⟨hy.1, by linarith [hy.2, hbotneg, hcx]⟩
  -- Integrate the fibre bound over `x ∈ (0, s)` and compare with the full plane energy.
  have hstep1 : ENNReal.ofReal s ≤ ∫⁻ x in Set.Ioo (0 : ℝ) s,
      ∫⁻ y in Set.Ioo (-(c x)) (c x), (ρ (emb x y)) ^ 2 := by
    calc ENNReal.ofReal s = ∫⁻ _x in Set.Ioo (0 : ℝ) s, (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, one_mul]
      _ ≤ ∫⁻ x in Set.Ioo (0 : ℝ) s,
            ∫⁻ y in Set.Ioo (-(c x)) (c x), (ρ (emb x y)) ^ 2 := by
          apply lintegral_mono_ae
          refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => fibre_sq_lower x hx)
  have hstep2 : (∫⁻ x in Set.Ioo (0 : ℝ) s,
      ∫⁻ y in Set.Ioo (-(c x)) (c x), (ρ (emb x y)) ^ 2)
      ≤ ∫⁻ z, (ρ z) ^ 2 := by
    have hcontseg2 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℝ) * Complex.I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hmeas2 : Measurable
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2) :=
      (hρmeas.comp hcontseg2.measurable).pow_const 2
    have hmono1 : (∫⁻ x in Set.Ioo (0 : ℝ) s,
        ∫⁻ y in Set.Ioo (-(c x)) (c x), (ρ (emb x y)) ^ 2)
        ≤ ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
      refine lintegral_mono' Measure.restrict_le_self (fun x => ?_)
      calc (∫⁻ y in Set.Ioo (-(c x)) (c x), (ρ (emb x y)) ^ 2)
          = ∫⁻ y in Set.Ioo (-(c x)) (c x), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
            apply lintegral_congr; intro y; rw [hemb]
        _ ≤ ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := setLIntegral_le_lintegral _ _
    have hprod : (∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2 := by
      have hae : AEMeasurable (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
          ((volume : Measure ℝ).prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hmeas2.aemeasurable
      rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
      exact (lintegral_prod _ hae).symm
    have hplane : (∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ z, (ρ z) ^ 2 := by
      rw [← Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
        Complex.measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)]
      apply lintegral_congr
      intro z
      simp only [Complex.measurableEquivRealProd_apply]
      congr 2
      exact Complex.re_add_im z
    rw [hprod, hplane] at hmono1
    exact hmono1
  exact le_trans hstep1 hstep2

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Rearrangement1D
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Circular (Schwarz) rearrangement on `ℂ` and planar energy preservation

This file lifts the one-dimensional decreasing rearrangement `decreasingRearrange`
(built in `RiemannDynamics.Analysis.Rearrangement1D`) to the **circular rearrangement**
`circRearrange p σ` of an extended-real density `σ : ℂ → ℝ≥0∞` about a centre `p : ℂ`.

On each circle `{‖z − p‖ = r}` one rearranges the angular profile `θ ↦ σ(p + r e^{iθ})` by
its one-dimensional symmetric decreasing rearrangement (in the angle, over an interval of
length `2π`). Because rearrangement preserves the layer-cake `p`-energy of the angular profile
on every circle, and the planar Lebesgue measure factors as `r dr dθ` in polar coordinates,
the circular rearrangement **preserves the planar energy** `∫⁻ z, (σ z)^2`. This is the
symmetrization brick toward the Grötzsch/Teichmüller modulus inversion.

## Main definitions

* `RiemannDynamics.angularProfile p σ r` — the angular profile `φ ↦ σ(p + r e^{i(φ − π)})` on the
  parameter interval `[0, 2π]` (the underlying geometric angle `φ − π` ranges over `[−π, π]`,
  matching the polar-coordinate angle range).
* `RiemannDynamics.circRearrange p σ` — the circular rearrangement of `σ` about `p`:
  `z ↦ (angularProfile p σ ‖z − p‖)♯[2π] (arg(z − p) + π)`.

## Main results

* `RiemannDynamics.measurable_circRearrange` — `circRearrange p σ` is measurable.
* `RiemannDynamics.lintegral_circRearrange_sq` — **planar energy preservation**:
  `∫⁻ z, (circRearrange p σ z)^2 = ∫⁻ z, (σ z)^2`.
* `RiemannDynamics.lintegral_circRearrange_rpow` — the general `p`-energy version for `0 < p`.
* `RiemannDynamics.circRearrange_radial` — **radial invariance**: if `σ` is radial (depends on
  `z` only through `‖z − p‖`), then `circRearrange p σ z = σ z` off the negative real axis from
  `p` (a co-null set), in particular a.e.
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-- The **angular profile** of `σ` on the circle of radius `r` about `p`, parametrised by the
angle `φ ∈ [0, 2π]`: `angularProfile p σ r φ = σ(p + r · e^{i(φ − π)})`. The shift by `π`
aligns the parameter interval `[0, 2π]` with the polar-coordinate angle range `(−π, π)`. -/
def angularProfile (p : ℂ) (σ : ℂ → ℝ≥0∞) (r : ℝ) : ℝ → ℝ≥0∞ :=
  fun φ => σ (p + (r : ℂ) * Complex.exp (((φ - π : ℝ)) * Complex.I))

/-- The **circular (Schwarz) rearrangement** of `σ` about `p`: on each circle `{‖z − p‖ = r}` the
angular profile `angularProfile p σ r` is replaced by its symmetric decreasing rearrangement on
`[0, 2π]`, evaluated at the parameter `arg(z − p) + π` corresponding to `z`. -/
def circRearrange (p : ℂ) (σ : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  fun z => decreasingRearrangeSymm (2 * π) (angularProfile p σ ‖z - p‖) (Complex.arg (z - p) + π)

/-- For fixed radius `r`, the angular profile is measurable in the angle. -/
theorem measurable_angularProfile (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) (r : ℝ) :
    Measurable (angularProfile p σ r) := by
  unfold angularProfile
  refine hσ.comp (Measurable.add measurable_const ?_)
  exact (Complex.measurable_ofReal.comp (measurable_id.sub measurable_const)).mul_const _
    |>.cexp |>.const_mul _

/-- The inverse polar-coordinate map `ℝ × ℝ → ℂ`, `(r, θ) ↦ r(cos θ + sin θ·i)`, is
measurable. -/
theorem measurable_polarCoord_symm : Measurable (Complex.polarCoord.symm) := by
  have heq : (Complex.polarCoord.symm : ℝ × ℝ → ℂ)
      = fun q => (q.1 : ℂ) * (Real.cos q.2 + Real.sin q.2 * Complex.I) := by
    funext q; rw [Complex.polarCoord_symm_apply]
  rw [heq]; fun_prop

/-- The angular profile is **jointly** measurable in `(r, φ)`. -/
theorem measurable_angularProfile_uncurry (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) :
    Measurable (fun q : ℝ × ℝ => angularProfile p σ q.1 q.2) := by
  unfold angularProfile
  refine hσ.comp (Measurable.add measurable_const (Measurable.mul ?_ ?_))
  · exact Complex.measurable_ofReal.comp measurable_fst
  · exact (Complex.measurable_ofReal.comp (measurable_snd.sub measurable_const)).mul_const _ |>.cexp

/-- The **section distribution function** `r ↦ distribFun (2π) (angularProfile p σ r) c` is
measurable, as the measure of a section of the jointly measurable super-level set. -/
theorem measurable_distribFun_section (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) (c : ℝ≥0∞) :
    Measurable (fun r : ℝ => distribFun (2 * π) (angularProfile p σ r) c) := by
  unfold distribFun
  have hjoint := measurable_angularProfile_uncurry p σ hσ
  have hSmeas : MeasurableSet
      {q : ℝ × ℝ | q.2 ∈ Icc (0 : ℝ) (2 * π) ∧ c < angularProfile p σ q.1 q.2} :=
    (measurable_snd measurableSet_Icc).inter (measurableSet_lt measurable_const hjoint)
  exact measurable_measure_prodMk_left hSmeas

/-- **Measurability of the circular rearrangement.** Established through the fundamental relation
`c < f♯ x ↔ ofReal x < distribFun T f c`: the super-level set `{z | c < circRearrange p σ z}`
equals `{z | ofReal (arg(z − p) + π) < distribFun (2π) (angularProfile p σ ‖z − p‖) c}`, an
inequality between two measurable functions of `z` (the second via the measurable section
distribution function). -/
theorem measurable_circRearrange (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) :
    Measurable (circRearrange p σ) := by
  apply measurable_of_Ioi
  intro c
  have hpre : circRearrange p σ ⁻¹' Ioi c = {z : ℂ | c < circRearrange p σ z} := rfl
  rw [hpre]
  -- fold identity: `f^sym (θ + π) = f♯[2π] (2 |θ|)` (since the centre is `π`)
  have hfold : ∀ (g : ℝ → ℝ≥0∞) (θ : ℝ),
      decreasingRearrangeSymm (2 * π) g (θ + π) = decreasingRearrange (2 * π) g (2 * |θ|) := by
    intro g θ
    unfold decreasingRearrangeSymm
    congr 2
    rw [show (2 * π) / 2 = π by ring, add_sub_cancel_right]
  have hchar : {z : ℂ | c < circRearrange p σ z}
      = {z : ℂ | ENNReal.ofReal (2 * |Complex.arg (z - p)|)
          < distribFun (2 * π) (angularProfile p σ ‖z - p‖) c} := by
    ext z
    simp only [mem_setOf_eq, circRearrange, hfold]
    exact lt_decreasingRearrange_iff (T := 2 * π) (f := angularProfile p σ ‖z - p‖)
      (2 * |Complex.arg (z - p)|) c
  rw [hchar]
  have hmeasD : Measurable (fun z : ℂ => distribFun (2 * π) (angularProfile p σ ‖z - p‖) c) :=
    (measurable_distribFun_section p σ hσ c).comp
      ((continuous_norm.comp (continuous_id.sub continuous_const)).measurable)
  have hmeasX : Measurable (fun z : ℂ => ENNReal.ofReal (2 * |Complex.arg (z - p)|)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        (_root_.continuous_abs.measurable.comp
          (Complex.measurable_arg.comp (measurable_id.sub measurable_const))))
  exact measurableSet_lt hmeasX hmeasD

/-- **Angular translation of a line integral.** Substituting `θ ↦ θ + π` carries the polar angle
interval `(−π, π)` onto the rearrangement parameter interval `(0, 2π)`. -/
theorem lintegral_translate_angle (G : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Ioo (-π) π, G (θ + π)) = ∫⁻ φ in Ioo 0 (2 * π), G φ := by
  have hmp : MeasurePreserving (fun θ : ℝ => θ + π) (volume.restrict (Ioo (-π) π))
      (volume.restrict (Ioo 0 (2 * π))) := by
    have h := (measurePreserving_add_right volume π).restrict_preimage
      (s := Ioo 0 (2 * π)) measurableSet_Ioo
    convert h using 2
    ext θ; simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [← hmp.lintegral_comp_emb (measurableEmbedding_addRight π)]

/-- **Per-radius angular energy preservation (the circle brick), general exponent.** On each
circle the `e`-energy of the rearranged angular profile equals that of the original, over the
polar angle interval `(−π, π)`. This is `lintegral_rpow_decreasingRearrange_eq` (with `T = 2π`)
transported to `(−π, π)` via the angular translation. -/
theorem inner_energy_rpow_eq (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) (r : ℝ) {e : ℝ}
    (he : 0 < e) :
    (∫⁻ θ in Ioo (-π) π, (decreasingRearrangeSymm (2 * π) (angularProfile p σ r) (θ + π)) ^ e)
      = ∫⁻ θ in Ioo (-π) π, (angularProfile p σ r (θ + π)) ^ e := by
  rw [lintegral_translate_angle
        (fun φ => (decreasingRearrangeSymm (2 * π) (angularProfile p σ r) φ) ^ e),
      lintegral_translate_angle (fun φ => (angularProfile p σ r φ) ^ e),
      setLIntegral_congr Ioo_ae_eq_Icc, setLIntegral_congr Ioo_ae_eq_Icc]
  exact lintegral_rpow_decreasingRearrangeSymm_eq (T := 2 * π) (f := angularProfile p σ r)
    (by positivity) (measurable_angularProfile p σ hσ r) he

/-- **Per-radius angular energy preservation (the circle brick), `L²` case.** On each circle the
squared energy of the rearranged angular profile equals that of the original, over the polar
angle interval `(−π, π)`. -/
theorem inner_energy_eq (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) (r : ℝ) :
    (∫⁻ θ in Ioo (-π) π, (decreasingRearrangeSymm (2 * π) (angularProfile p σ r) (θ + π)) ^ 2)
      = ∫⁻ θ in Ioo (-π) π, (angularProfile p σ r (θ + π)) ^ 2 := by
  have hpow : ∀ a : ℝ≥0∞, a ^ (2 : ℕ) = a ^ (2 : ℝ) := fun a => by
    rw [← ENNReal.rpow_natCast a 2]; norm_num
  simp_rw [hpow]
  exact inner_energy_rpow_eq p σ hσ r (by norm_num)

/-- **Planar energy preservation (the main brick).** The circular rearrangement preserves the
planar `L²` energy:
`∫⁻ z, (circRearrange p σ z)^2 = ∫⁻ z, (σ z)^2`.

Proof: in polar coordinates `z = p + r e^{iθ}` the planar measure factors as `r dr dθ`; on each
circle the `θ`-integral of the squared rearranged profile equals that of `σ` by `inner_energy_eq`,
so the integrands agree for every `r`, hence the integrals. -/
theorem lintegral_circRearrange_sq (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) :
    (∫⁻ z, (circRearrange p σ z) ^ 2) = ∫⁻ z, (σ z) ^ 2 := by
  -- generic polar reduction centred at `p`
  have hpolar : ∀ (H : ℂ → ℝ≥0∞),
      (∫⁻ z, H z) = ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal q.1 • H (p + Complex.polarCoord.symm q) := by
    intro H
    rw [← lintegral_add_left_eq_self (μ := (volume : Measure ℂ)) H p,
        ← Complex.lintegral_comp_polarCoord_symm (fun w => H (p + w)),
        polarCoord_target]
  rw [hpolar (fun z => (circRearrange p σ z) ^ 2), hpolar (fun z => (σ z) ^ 2)]
  -- Fubini both sides over `Ioi 0 ×ˢ Ioo (-π) π`
  have haem : ∀ (H : ℂ → ℝ≥0∞), Measurable H →
      AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 • H (p + Complex.polarCoord.symm q))
        ((volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)) := by
    intro H hH
    refine Measurable.aemeasurable ?_
    refine Measurable.smul (ENNReal.measurable_ofReal.comp measurable_fst) ?_
    exact hH.comp (Measurable.add measurable_const measurable_polarCoord_symm)
  rw [Measure.volume_eq_prod,
      setLIntegral_prod _ (haem _ ((measurable_circRearrange p σ hσ).pow_const 2)),
      setLIntegral_prod _ (haem _ (hσ.pow_const 2))]
  -- per-radius equality of the inner `θ`-integrals
  refine lintegral_congr (fun r => ?_)
  -- pull the `r`-factor out and reduce to `inner_energy_eq`
  by_cases hr : 0 < r
  · -- on the polar target the integrands simplify pointwise in `θ`
    have hcirc : ∀ θ ∈ Ioo (-π) π,
        ENNReal.ofReal r • (circRearrange p σ (p + Complex.polarCoord.symm (r, θ))) ^ 2
          = ENNReal.ofReal r •
              (decreasingRearrangeSymm (2 * π) (angularProfile p σ r) (θ + π)) ^ 2 := by
      intro θ hθ
      have hnorm : ‖(p + Complex.polarCoord.symm (r, θ)) - p‖ = r := by
        rw [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hr]
      have harg : Complex.arg ((p + Complex.polarCoord.symm (r, θ)) - p) = θ := by
        rw [add_sub_cancel_left, Complex.polarCoord_symm_apply, Complex.ofReal_cos,
          Complex.ofReal_sin]
        exact Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [circRearrange, hnorm, harg]
    have hsig : ∀ θ ∈ Ioo (-π) π,
        ENNReal.ofReal r • (σ (p + Complex.polarCoord.symm (r, θ))) ^ 2
          = ENNReal.ofReal r • (angularProfile p σ r (θ + π)) ^ 2 := by
      intro θ _
      have hpt : p + Complex.polarCoord.symm (r, θ)
          = p + (r : ℂ) * Complex.exp (θ * Complex.I) := by
        rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring
      have hprof : angularProfile p σ r (θ + π)
          = σ (p + (r : ℂ) * Complex.exp (θ * Complex.I)) := by
        unfold angularProfile; norm_num
      rw [hpt, hprof]
    rw [setLIntegral_congr_fun measurableSet_Ioo hcirc,
        setLIntegral_congr_fun measurableSet_Ioo hsig]
    simp only [smul_eq_mul]
    rw [lintegral_const_mul' _ _ (by finiteness), lintegral_const_mul' _ _ (by finiteness),
        inner_energy_eq p σ hσ r]
  · -- `r ≤ 0`: the `ofReal r` factor is `0`, both inner integrals vanish
    have hr0 : ENNReal.ofReal r = 0 := by
      rw [ENNReal.ofReal_eq_zero]; exact not_lt.mp hr
    simp only [smul_eq_mul, hr0, zero_mul, lintegral_zero]

/-- **Planar `p`-energy preservation.** For `0 < p`, the circular rearrangement preserves the
`p`-energy `∫⁻ z, (σ z)^p`. Same polar / per-circle argument as the `p = 2` case. -/
theorem lintegral_circRearrange_rpow (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) {e : ℝ}
    (he : 0 < e) :
    (∫⁻ z, (circRearrange p σ z) ^ e) = ∫⁻ z, (σ z) ^ e := by
  have hpolar : ∀ (H : ℂ → ℝ≥0∞),
      (∫⁻ z, H z) = ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal q.1 • H (p + Complex.polarCoord.symm q) := by
    intro H
    rw [← lintegral_add_left_eq_self (μ := (volume : Measure ℂ)) H p,
        ← Complex.lintegral_comp_polarCoord_symm (fun w => H (p + w)),
        polarCoord_target]
  rw [hpolar (fun z => (circRearrange p σ z) ^ e), hpolar (fun z => (σ z) ^ e)]
  have haem : ∀ (H : ℂ → ℝ≥0∞), Measurable H →
      AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 • H (p + Complex.polarCoord.symm q))
        ((volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)) := by
    intro H hH
    refine Measurable.aemeasurable ?_
    refine Measurable.smul (ENNReal.measurable_ofReal.comp measurable_fst) ?_
    exact hH.comp (Measurable.add measurable_const measurable_polarCoord_symm)
  rw [Measure.volume_eq_prod,
      setLIntegral_prod _ (haem _ ((measurable_circRearrange p σ hσ).pow_const e)),
      setLIntegral_prod _ (haem _ (hσ.pow_const e))]
  refine lintegral_congr (fun r => ?_)
  by_cases hr : 0 < r
  · have hcirc : ∀ θ ∈ Ioo (-π) π,
        ENNReal.ofReal r • (circRearrange p σ (p + Complex.polarCoord.symm (r, θ))) ^ e
          = ENNReal.ofReal r •
              (decreasingRearrangeSymm (2 * π) (angularProfile p σ r) (θ + π)) ^ e := by
      intro θ hθ
      have hnorm : ‖(p + Complex.polarCoord.symm (r, θ)) - p‖ = r := by
        rw [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hr]
      have harg : Complex.arg ((p + Complex.polarCoord.symm (r, θ)) - p) = θ := by
        rw [add_sub_cancel_left, Complex.polarCoord_symm_apply, Complex.ofReal_cos,
          Complex.ofReal_sin]
        exact Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [circRearrange, hnorm, harg]
    have hsig : ∀ θ ∈ Ioo (-π) π,
        ENNReal.ofReal r • (σ (p + Complex.polarCoord.symm (r, θ))) ^ e
          = ENNReal.ofReal r • (angularProfile p σ r (θ + π)) ^ e := by
      intro θ _
      have hpt : p + Complex.polarCoord.symm (r, θ)
          = p + (r : ℂ) * Complex.exp (θ * Complex.I) := by
        rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring
      have hprof : angularProfile p σ r (θ + π)
          = σ (p + (r : ℂ) * Complex.exp (θ * Complex.I)) := by
        unfold angularProfile; norm_num
      rw [hpt, hprof]
    rw [setLIntegral_congr_fun measurableSet_Ioo hcirc,
        setLIntegral_congr_fun measurableSet_Ioo hsig]
    simp only [smul_eq_mul]
    rw [lintegral_const_mul' _ _ (by finiteness), lintegral_const_mul' _ _ (by finiteness),
        inner_energy_rpow_eq p σ hσ r he]
  · have hr0 : ENNReal.ofReal r = 0 := by rw [ENNReal.ofReal_eq_zero]; exact not_lt.mp hr
    simp only [smul_eq_mul, hr0, zero_mul, lintegral_zero]

/-- **Radial invariance.** If `σ` is radial — its value `σ z` depends on `z` only through
`‖z − p‖`, witnessed by `g : ℝ → ℝ≥0∞` with `σ z = g ‖z − p‖` — then the circular rearrangement
leaves `σ` unchanged off the negative real axis emanating from `p` (the locus `arg(z − p) = π`,
a co-null set); in particular `circRearrange p σ z = σ z` for every `z` with `arg(z − p) ≠ π`. -/
theorem circRearrange_radial (p : ℂ) (σ : ℂ → ℝ≥0∞) {g : ℝ → ℝ≥0∞}
    (hg : ∀ z, σ z = g ‖z - p‖) {z : ℂ} (hz : Complex.arg (z - p) ≠ π) :
    circRearrange p σ z = σ z := by
  -- the angular profile is constant in the angle (equal to `g ‖z − p‖ = σ z`)
  have hconst : angularProfile p σ ‖z - p‖ = fun _ => σ z := by
    funext φ
    rw [angularProfile, hg, hg]
    congr 1
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_norm]
  -- `|arg(z − p)| < π`, so the fold argument `2 |arg(z − p)|` lies in `[0, 2π)`
  have habs : |Complex.arg (z - p)| < π := by
    rw [abs_lt]
    exact ⟨Complex.neg_pi_lt_arg (z - p), lt_of_le_of_ne (Complex.arg_le_pi (z - p)) hz⟩
  rw [circRearrange, hconst]
  unfold decreasingRearrangeSymm
  rw [decreasingRearrange_const (σ z) (by positivity) ?_]
  rw [show (2 * π) / 2 = π by ring, add_sub_cancel_right]
  calc 2 * |Complex.arg (z - p)| < 2 * π := by linarith [habs]

end RiemannDynamics

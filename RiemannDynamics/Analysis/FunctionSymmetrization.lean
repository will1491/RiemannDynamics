/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.CircularRearrangement

/-!
# Circular symmetrization of a real function and super-level equimeasurability

This file defines the **circular (Schwarz) symmetrization** `circSymm p u` of a real-valued
function `u : ℂ → ℝ` about a centre `p : ℂ`, and proves that it is **equimeasurable** with `u`:
the planar Lebesgue measure of every super-level set is preserved.

On each circle `{‖z − p‖ = r}` the angular profile `θ ↦ u(p + r e^{iθ})` is replaced by its
one-dimensional symmetric decreasing rearrangement in the angle. To reuse the extended-real
rearrangement machinery `decreasingRearrange` (which acts on `ℝ≥0∞`-valued functions), the real
values are transported to `ℝ≥0∞` through the strictly monotone bijection `c ↦ ofReal (exp c)` of
`ℝ` onto `Ioo 0 ∞`, the density `circRearrange` is applied, and the result is decoded by
`t ↦ log t.toReal`. Because the exponential encoding is a strictly monotone measurable order
embedding whose values stay strictly between `0` and `∞`, and the density `circRearrange`
preserves super-level measures on `ℂ` (which in turn follows from angular equimeasurability of the
decreasing rearrangement together with the polar factorisation `r dr dθ`), the decoded function
`circSymm p u` has the same planar distribution as `u`.

## Main definitions

* `RiemannDynamics.circSymm p u` — the circular symmetrization of `u : ℂ → ℝ` about `p`, defined by
  `z ↦ log (circRearrange p (ofReal ∘ exp ∘ u) z).toReal`.

## Main results

* `RiemannDynamics.measurable_circSymm` — `circSymm p u` is measurable when `u` is.
* `RiemannDynamics.volume_symmetrized_superlevel_eq` — **super-level equimeasurability**:
  `volume ((circSymm p u) ⁻¹' Ioi c) = volume (u ⁻¹' Ioi c)` for every threshold `c`.
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal symmDiff

noncomputable section

namespace RiemannDynamics

/-! ### Boundary values of the one-dimensional decreasing rearrangement

The decoding step requires the density `circRearrange` to take values strictly inside `Ioo 0 ∞`;
we first record when the one-dimensional rearrangement is positive and finite. -/

variable {T : ℝ} {f : ℝ → ℝ≥0∞}

/-- The distribution function at level `0` of a strictly positive `f` is the full length
`ofReal T`, since the super-level set above `0` is all of `Icc 0 T`. -/
theorem distribFun_zero_of_pos (hf : ∀ φ, 0 < f φ) : distribFun T f 0 = ENNReal.ofReal T := by
  unfold distribFun
  have hset : {x ∈ Icc (0 : ℝ) T | (0 : ℝ≥0∞) < f x} = Icc 0 T := by
    ext x; simp only [mem_setOf_eq, mem_Icc]; exact ⟨fun h => h.1, fun h => ⟨h, hf x⟩⟩
  rw [hset, Real.volume_Icc, sub_zero]

/-- **Positivity of the rearrangement.** For strictly positive `f` and a parameter `x ∈ [0, T)`,
the decreasing rearrangement is strictly positive: by the fundamental relation this reduces to
`ofReal x < distribFun T f 0 = ofReal T`, i.e. `x < T`. -/
theorem decreasingRearrange_pos (hf : ∀ φ, 0 < f φ) {x : ℝ} (hx0 : 0 ≤ x) (hxT : x < T) :
    0 < decreasingRearrange T f x := by
  rw [lt_decreasingRearrange_iff, distribFun_zero_of_pos hf]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0).mpr hxT

/-- The distribution function evaluated along the integer levels tends to `0`: the super-level
sets `{φ | n < f φ}` decrease to `{φ | f φ = ∞} = ∅` (as `f` is finite), so their measures
vanish in the limit. -/
theorem distribFun_nat_tendsto_zero (hf : Measurable f) (hlt : ∀ φ, f φ < ⊤) :
    Tendsto (fun n : ℕ => distribFun T f n) atTop (𝓝 0) := by
  set A : ℕ → Set ℝ := fun n => {φ ∈ Icc (0 : ℝ) T | (n : ℝ≥0∞) < f φ} with hA
  have hmeas : ∀ n, NullMeasurableSet (A n) volume := fun n =>
    (measurableSet_Icc.inter (measurableSet_lt measurable_const hf)).nullMeasurableSet
  have hanti : Antitone A := fun m n hmn φ hφ =>
    ⟨hφ.1, lt_of_le_of_lt (by exact_mod_cast Nat.cast_le.mpr hmn) hφ.2⟩
  have hfin : ∃ i, volume (A i) ≠ ∞ :=
    ⟨0, ne_top_of_le_ne_top ENNReal.ofReal_ne_top (distribFun_le_ofReal_T (T := T) (f := f) _)⟩
  have hInter : ⋂ n, A n = ∅ := by
    ext φ
    simp only [hA, mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
    by_cases hφI : φ ∈ Icc (0 : ℝ) T
    · obtain ⟨n, hn⟩ := exists_nat_gt (f φ).toReal
      refine ⟨n, fun hc => ?_⟩
      have hfn : f φ < (n : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal (hlt φ).ne, ← ENNReal.ofReal_natCast]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr hn
      exact absurd hfn (not_lt.mpr hc.2.le)
    · exact ⟨0, fun hc => hφI hc.1⟩
  have htend := tendsto_measure_iInter_atTop hmeas hanti hfin
  rw [hInter, measure_empty] at htend
  convert htend using 1

/-- **Finiteness of the rearrangement.** For finite measurable `f` and a positive parameter `x`,
the decreasing rearrangement is finite: some integer level `n` has `distribFun T f n ≤ ofReal x`
(since the distribution function tends to `0`), and `n` then bounds the defining infimum. -/
theorem decreasingRearrange_lt_top (hf : Measurable f) (hlt : ∀ φ, f φ < ⊤) {x : ℝ}
    (hx : 0 < x) : decreasingRearrange T f x < ⊤ := by
  have htend := distribFun_nat_tendsto_zero hf hlt (T := T)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal x := ENNReal.ofReal_pos.mpr hx
  have hev : ∀ᶠ n : ℕ in atTop, distribFun T f (n : ℝ≥0∞) < ENNReal.ofReal x :=
    htend.eventually (eventually_lt_nhds hpos)
  obtain ⟨n, hn⟩ := hev.exists
  calc decreasingRearrange T f x ≤ (n : ℝ≥0∞) := sInf_le (by simp only [mem_setOf_eq]; exact hn.le)
    _ < ⊤ := ENNReal.natCast_lt_top n

/-! ### Boundary values of the circular rearrangement -/

/-- The circular rearrangement of a finite density is finite off the positive real axis from `p`
(the exceptional set `{arg(z − p) = 0}`, where the symmetric peak is anchored): there the folded
parameter `2·|arg(z − p)|` is strictly positive, and the angular profile is finite. -/
theorem circRearrange_lt_top (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) (hlt : ∀ w, σ w < ⊤)
    (z : ℂ) (hz : Complex.arg (z - p) ≠ 0) : circRearrange p σ z < ⊤ := by
  unfold circRearrange decreasingRearrangeSymm
  refine decreasingRearrange_lt_top (measurable_angularProfile p σ hσ _) (fun φ => hlt _) ?_
  rw [show (2 * π) / 2 = π by ring, add_sub_cancel_right]
  have : 0 < |Complex.arg (z - p)| := abs_pos.mpr hz
  positivity

/-- The circular rearrangement of a strictly positive density is strictly positive off the
negative real axis from `p`: there the parameter `arg(z − p) + π` lies in `[0, 2π)` and the
angular profile is strictly positive. -/
theorem circRearrange_pos (p : ℂ) (σ : ℂ → ℝ≥0∞) (hpos : ∀ w, 0 < σ w)
    {z : ℂ} (hz : Complex.arg (z - p) ≠ π) : 0 < circRearrange p σ z := by
  unfold circRearrange decreasingRearrangeSymm
  refine decreasingRearrange_pos (fun φ => hpos _) ?_ ?_
  · positivity
  · rw [show (2 * π) / 2 = π by ring, add_sub_cancel_right]
    have hlt : Complex.arg (z - p) < π := lt_of_le_of_ne (Complex.arg_le_pi (z - p)) hz
    have hgt : -π < Complex.arg (z - p) := Complex.neg_pi_lt_arg (z - p)
    have habs : |Complex.arg (z - p)| < π := abs_lt.mpr ⟨hgt, hlt⟩
    linarith

/-! ### Density super-level equimeasurability of the circular rearrangement -/

/-- The super-level indicator integral of a measurable `f` over `Icc 0 (2π)` recovers the
distribution function `distribFun (2π) f t`. -/
theorem lintegral_superlevel_indicator_eq (f : ℝ → ℝ≥0∞) (t : ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ φ in Icc (0 : ℝ) (2 * π), Set.indicator {φ | t < f φ} (fun _ => (1 : ℝ≥0∞)) φ)
      = distribFun (2 * π) f t := by
  have hms : MeasurableSet {φ : ℝ | t < f φ} := measurableSet_lt measurable_const hf
  rw [lintegral_indicator hms, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, one_mul, Measure.restrict_apply hms, inter_comm]
  rfl

/-- **Per-radius angular super-level equimeasurability (the circle brick).** On each circle the
angular measure of the super-level set of the rearranged profile equals that of the original,
over the polar angle interval `(−π, π)`. This is `distribFun_decreasingRearrange` (with `T = 2π`)
transported to `(−π, π)` via the angular translation. -/
theorem inner_superlevel_eq (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ) (r : ℝ) (t : ℝ≥0∞) :
    (∫⁻ θ in Ioo (-π) π, Set.indicator
        {θ | t < decreasingRearrangeSymm (2 * π) (angularProfile p σ r) (θ + π)}
        (fun _ => (1 : ℝ≥0∞)) θ)
      = ∫⁻ θ in Ioo (-π) π, Set.indicator
        {θ | t < angularProfile p σ r (θ + π)} (fun _ => (1 : ℝ≥0∞)) θ := by
  have hrw : ∀ (g : ℝ → ℝ≥0∞),
      (fun θ => Set.indicator {θ | t < g (θ + π)} (fun _ => (1 : ℝ≥0∞)) θ)
        = (fun θ => (fun φ => Set.indicator {φ | t < g φ} (fun _ => (1 : ℝ≥0∞)) φ) (θ + π)) := by
    intro g; funext θ; simp only [Set.indicator, mem_setOf_eq]
  rw [hrw (decreasingRearrangeSymm (2 * π) (angularProfile p σ r)), hrw (angularProfile p σ r),
      lintegral_translate_angle
        (fun φ => Set.indicator {φ | t < decreasingRearrangeSymm (2 * π) (angularProfile p σ r) φ}
          (fun _ => (1 : ℝ≥0∞)) φ),
      lintegral_translate_angle
        (fun φ => Set.indicator {φ | t < angularProfile p σ r φ} (fun _ => (1 : ℝ≥0∞)) φ),
      setLIntegral_congr Ioo_ae_eq_Icc, setLIntegral_congr Ioo_ae_eq_Icc,
      lintegral_superlevel_indicator_eq _ t measurable_decreasingRearrangeSymm,
      lintegral_superlevel_indicator_eq _ t (measurable_angularProfile p σ hσ r),
      distribFun_decreasingRearrangeSymm (by positivity) t]

/-- **Planar super-level equimeasurability of the circular rearrangement.** For every threshold
`t`, the circular rearrangement preserves the planar measure of the super-level set:
`volume {z | t < circRearrange p σ z} = volume {z | t < σ z}`.

Proof: writing each super-level measure as the planar integral of its indicator and passing to
polar coordinates `z = p + r e^{iθ}` (so the measure factors as `r dr dθ`), the inner `θ`-integral
equals the angular super-level measure, which `inner_superlevel_eq` identifies for the rearranged
and original profiles on every circle; the integrands agree for each `r`, hence the integrals. -/
theorem volume_superlevel_circRearrange_eq (p : ℂ) (σ : ℂ → ℝ≥0∞) (hσ : Measurable σ)
    (t : ℝ≥0∞) :
    volume {z | t < circRearrange p σ z} = volume {z | t < σ z} := by
  have hvol : ∀ (f : ℂ → ℝ≥0∞), Measurable f →
      volume {z | t < f z} = ∫⁻ z, Set.indicator {z | t < f z} (fun _ => (1 : ℝ≥0∞)) z := by
    intro f hf
    have hms : MeasurableSet {z : ℂ | t < f z} := measurableSet_lt measurable_const hf
    rw [lintegral_indicator hms, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, one_mul]
  rw [hvol _ (measurable_circRearrange p σ hσ), hvol _ hσ]
  have hpolar : ∀ (H : ℂ → ℝ≥0∞),
      (∫⁻ z, H z) = ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal q.1 • H (p + Complex.polarCoord.symm q) := by
    intro H
    rw [← lintegral_add_left_eq_self (μ := (volume : Measure ℂ)) H p,
        ← Complex.lintegral_comp_polarCoord_symm (fun w => H (p + w)), polarCoord_target]
  rw [hpolar (fun z => Set.indicator {z | t < circRearrange p σ z} (fun _ => (1 : ℝ≥0∞)) z),
      hpolar (fun z => Set.indicator {z | t < σ z} (fun _ => (1 : ℝ≥0∞)) z)]
  have haem : ∀ (H : ℂ → ℝ≥0∞), Measurable H →
      AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 • H (p + Complex.polarCoord.symm q))
        ((volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)) := by
    intro H hH
    refine Measurable.aemeasurable (Measurable.smul (ENNReal.measurable_ofReal.comp measurable_fst)
      (hH.comp (Measurable.add measurable_const measurable_polarCoord_symm)))
  have hmC : Measurable (fun z : ℂ =>
      Set.indicator {z | t < circRearrange p σ z} (fun _ => (1 : ℝ≥0∞)) z) :=
    Measurable.indicator measurable_const
      (measurableSet_lt measurable_const (measurable_circRearrange p σ hσ))
  have hmS : Measurable (fun z : ℂ => Set.indicator {z | t < σ z} (fun _ => (1 : ℝ≥0∞)) z) :=
    Measurable.indicator measurable_const (measurableSet_lt measurable_const hσ)
  rw [Measure.volume_eq_prod, setLIntegral_prod _ (haem _ hmC), setLIntegral_prod _ (haem _ hmS)]
  refine lintegral_congr (fun r => ?_)
  by_cases hr : 0 < r
  · have hcirc : ∀ θ ∈ Ioo (-π) π,
        ENNReal.ofReal r • Set.indicator {z | t < circRearrange p σ z} (fun _ => (1 : ℝ≥0∞))
            (p + Complex.polarCoord.symm (r, θ))
          = ENNReal.ofReal r • Set.indicator
              {θ | t < decreasingRearrangeSymm (2 * π) (angularProfile p σ r) (θ + π)}
              (fun _ => (1 : ℝ≥0∞)) θ := by
      intro θ hθ
      have hnorm : ‖(p + Complex.polarCoord.symm (r, θ)) - p‖ = r := by
        rw [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hr]
      have harg : Complex.arg ((p + Complex.polarCoord.symm (r, θ)) - p) = θ := by
        rw [add_sub_cancel_left, Complex.polarCoord_symm_apply, Complex.ofReal_cos,
          Complex.ofReal_sin]
        exact Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      congr 1
      simp only [Set.indicator, mem_setOf_eq, circRearrange, hnorm, harg]
    have hsig : ∀ θ ∈ Ioo (-π) π,
        ENNReal.ofReal r • Set.indicator {z | t < σ z} (fun _ => (1 : ℝ≥0∞))
            (p + Complex.polarCoord.symm (r, θ))
          = ENNReal.ofReal r • Set.indicator {θ | t < angularProfile p σ r (θ + π)}
              (fun _ => (1 : ℝ≥0∞)) θ := by
      intro θ _
      have hpt : p + Complex.polarCoord.symm (r, θ)
          = p + (r : ℂ) * Complex.exp (θ * Complex.I) := by
        rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring
      have hprof : angularProfile p σ r (θ + π)
          = σ (p + (r : ℂ) * Complex.exp (θ * Complex.I)) := by
        unfold angularProfile; norm_num
      congr 1
      simp only [Set.indicator, mem_setOf_eq, hpt, hprof]
    rw [setLIntegral_congr_fun measurableSet_Ioo hcirc,
        setLIntegral_congr_fun measurableSet_Ioo hsig]
    simp only [smul_eq_mul]
    rw [lintegral_const_mul' _ _ (by finiteness), lintegral_const_mul' _ _ (by finiteness),
        inner_superlevel_eq p σ hσ r t]
  · have hr0 : ENNReal.ofReal r = 0 := by rw [ENNReal.ofReal_eq_zero]; exact not_lt.mp hr
    simp only [smul_eq_mul, hr0, zero_mul, lintegral_zero]

/-! ### The exponential order embedding `ℝ → ℝ≥0∞` -/

/-- The strictly monotone measurable encoding of `ℝ` into `Ioo 0 ∞ ⊆ ℝ≥0∞`, `c ↦ ofReal (exp c)`,
used to transport real values through the extended-real rearrangement machinery. -/
def realEnc (c : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp c)

/-- The encoding is strictly positive. -/
theorem realEnc_pos (c : ℝ) : 0 < realEnc c := ENNReal.ofReal_pos.mpr (Real.exp_pos c)

/-- The encoding is finite. -/
theorem realEnc_lt_top (c : ℝ) : realEnc c < ⊤ := ENNReal.ofReal_lt_top

/-- The encoding is measurable. -/
theorem measurable_realEnc : Measurable realEnc :=
  ENNReal.measurable_ofReal.comp Real.measurable_exp

/-- The encoding is a strict order embedding: `realEnc c < realEnc d ↔ c < d`. -/
theorem realEnc_lt_realEnc {c d : ℝ} : realEnc c < realEnc d ↔ c < d := by
  unfold realEnc
  rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos d), Real.exp_lt_exp]

/-- **Decoding adjunction.** For a value `t` strictly inside `Ioo 0 ∞`, the decoded threshold
`log t.toReal` exceeds `c` exactly when `t` exceeds the encoded threshold `realEnc c`. -/
theorem lt_log_toReal_iff {c : ℝ} {t : ℝ≥0∞} (ht0 : 0 < t) (htt : t < ⊤) :
    c < Real.log t.toReal ↔ realEnc c < t := by
  unfold realEnc
  rw [Real.lt_log_iff_exp_lt (ENNReal.toReal_pos ht0.ne' htt.ne),
    ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos c).le htt.ne]

/-! ### The circular symmetrization of a real function -/

/-- The **circular (Schwarz) symmetrization** of a real function `u : ℂ → ℝ` about `p`: encode the
values by `realEnc = ofReal ∘ exp`, apply the density circular rearrangement, and decode by
`log ∘ toReal`. On each circle this replaces the angular profile of `u` by its symmetric decreasing
rearrangement (in the angle). -/
def circSymm (p : ℂ) (u : ℂ → ℝ) : ℂ → ℝ :=
  fun z => Real.log (circRearrange p (fun w => realEnc (u w)) z).toReal

/-- **Measurability of the circular symmetrization.** -/
theorem measurable_circSymm (p : ℂ) (u : ℂ → ℝ) (hu : Measurable u) :
    Measurable (circSymm p u) :=
  Real.measurable_log.comp
    (ENNReal.measurable_toReal.comp (measurable_circRearrange p _ (measurable_realEnc.comp hu)))

/-- **Super-level equimeasurability of the circular symmetrization.** The symmetrization preserves
the planar measure of every super-level set:
`volume ((circSymm p u) ⁻¹' Ioi c) = volume (u ⁻¹' Ioi c)`.

Off the real axis through `p` (a planar null set), the decoding adjunction turns the real
super-level set `{c < circSymm p u z}` into the encoded super-level set
`{realEnc c < circRearrange p (realEnc ∘ u) z}`; the two sets differ only within that null line, so
their measures agree. The density equimeasurability `volume_superlevel_circRearrange_eq` transfers
the encoded super-level measure to `{realEnc c < realEnc (u z)}`, which the order embedding
`realEnc_lt_realEnc` identifies with `{c < u z}`. -/
theorem volume_symmetrized_superlevel_eq (p : ℂ) (u : ℂ → ℝ) (hu : Measurable u) (c : ℝ) :
    volume ((circSymm p u) ⁻¹' Set.Ioi c) = volume (u ⁻¹' Set.Ioi c) := by
  set σ : ℂ → ℝ≥0∞ := fun w => realEnc (u w) with hσdef
  have hσm : Measurable σ := measurable_realEnc.comp hu
  have hσpos : ∀ w, 0 < σ w := fun w => realEnc_pos (u w)
  have hσlt : ∀ w, σ w < ⊤ := fun w => realEnc_lt_top (u w)
  have hpre1 : (circSymm p u) ⁻¹' Set.Ioi c = {z | c < circSymm p u z} := rfl
  have hpre2 : u ⁻¹' Set.Ioi c = {z | c < u z} := rfl
  rw [hpre1, hpre2]
  -- the exceptional ray `{arg(z − p) = π}` is planar null (it lies on the line `(z − p).im = 0`)
  have hlinenull : volume {z : ℂ | (z - p).im = 0} = 0 := by
    have hpres := Complex.volume_preserving_equiv_real_prod
    have hset : {z : ℂ | (z - p).im = 0}
        = Complex.measurableEquivRealProd ⁻¹' {q : ℝ × ℝ | q.2 = p.im} := by
      ext z
      simp only [mem_setOf_eq, mem_preimage, Complex.measurableEquivRealProd_apply, Complex.sub_im]
      exact ⟨fun h => by linarith, fun h => by linarith⟩
    have hms : MeasurableSet {q : ℝ × ℝ | q.2 = p.im} :=
      measurableSet_eq_fun measurable_snd measurable_const
    rw [hset, hpres.measure_preimage hms.nullMeasurableSet]
    have hprod : {q : ℝ × ℝ | q.2 = p.im} = univ ×ˢ {p.im} := by
      ext q; simp only [mem_setOf_eq, mem_prod, mem_univ, true_and, mem_singleton_iff]
    rw [hprod, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  -- the two super-level sets differ only within the null real axis through `p`
  have hsub : {z | c < circSymm p u z} ∆ {z | realEnc c < circRearrange p σ z}
      ⊆ {z : ℂ | (z - p).im = 0} := by
    intro z hz
    by_contra hznot
    simp only [mem_setOf_eq] at hznot
    have hz0 : Complex.arg (z - p) ≠ 0 := fun h => hznot (Complex.arg_eq_zero_iff.mp h).2
    have hzπ : Complex.arg (z - p) ≠ π := fun h => hznot (Complex.arg_eq_pi_iff.mp h).2
    have hlt : circRearrange p σ z < ⊤ := circRearrange_lt_top p σ hσm hσlt z hz0
    have hpos : 0 < circRearrange p σ z := circRearrange_pos p σ hσpos hzπ
    have hiff : c < circSymm p u z ↔ realEnc c < circRearrange p σ z := by
      unfold circSymm; rw [lt_log_toReal_iff hpos hlt]
    rcases hz with hz | hz
    · exact hz.2 (by simp only [mem_setOf_eq]; exact hiff.mp (by simpa using hz.1))
    · exact hz.2 (by simp only [mem_setOf_eq]; exact hiff.mpr (by simpa using hz.1))
  have haeeq : {z | c < circSymm p u z} =ᵐ[volume] {z | realEnc c < circRearrange p σ z} :=
    measure_symmDiff_eq_zero_iff.mp (measure_mono_null hsub hlinenull)
  rw [measure_congr haeeq, volume_superlevel_circRearrange_eq p σ hσm (realEnc c)]
  congr 1
  ext z
  simp only [mem_setOf_eq, hσdef]
  exact realEnc_lt_realEnc

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.FunctionSymmetrization
import RiemannDynamics.Analysis.PolarizationDir

/-!
# Polarization rigidity toward the circular symmetrization

This file develops the machinery for the **Brock–Solynin rigidity** step, which identifies the limit
of iterated polarizations with a circular symmetrization. Two ingredients are assembled here:

* the **polar descent** correspondence, turning a planar almost-everywhere equality into an
  a.e.-in-angle equality on almost every circle (and its converse), so that a planar fixed-point
  hypothesis reduces to a per-circle statement;
* the per-circle reduction of the directional polarization `polarizeDir θ` to the one-dimensional
  angular two-point reflection `angReflect θ`, together with the **super-level bridge** reducing a
  function equality to a family of super-level-set equalities.

## Main definitions

* `RiemannDynamics.angReflect θ g` — the angular two-point reflection of a circle profile `g` across
  the axis at angle `θ`, taking `max` on the side `sin (φ − θ) ≥ 0` and `min` on the other.

## Main statements

* `RiemannDynamics.ae_slice_of_ae_planar` / `ae_planar_of_ae_slice` — the polar descent and lift;
* `RiemannDynamics.polarizeDir_apply_circle` — `polarizeDir θ` acts per-circle as `angReflect θ`;
* `RiemannDynamics.ae_circle_fixed_of_polarizeDir_fixed` — the per-circle reduction of a planar
  polarization fixed point;
* `RiemannDynamics.ae_eq_of_superlevel_ae_eq` — the super-level bridge;
* `RiemannDynamics.circSymm_congr_of_superlevel_eq` — per-radius angular equidistribution ⟹ equal
  circular symmetrizations.
-/

open MeasureTheory Set Complex Filter Topology
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-! ### The rearrangement depends only on the distribution function -/

/-- The decreasing rearrangement depends on `f` only through its distribution function: equal
distribution functions yield an equal rearrangement. -/
theorem decreasingRearrange_congr {T : ℝ} {f g : ℝ → ℝ≥0∞}
    (h : distribFun T f = distribFun T g) :
    decreasingRearrange T f = decreasingRearrange T g := by
  funext x
  simp only [decreasingRearrange, h]

/-- The symmetric decreasing rearrangement depends on `f` only through its distribution function. -/
theorem decreasingRearrangeSymm_congr {T : ℝ} {f g : ℝ → ℝ≥0∞}
    (h : distribFun T f = distribFun T g) :
    decreasingRearrangeSymm T f = decreasingRearrangeSymm T g := by
  funext x
  simp only [decreasingRearrangeSymm]
  rw [decreasingRearrange_congr h]

/-! ### Polar descent of almost-everywhere equalities -/

/-- **Polar descent.** A planar a.e. equality of two measurable functions descends, off the centre,
to an a.e.-in-angle equality on almost every circle. -/
theorem ae_slice_of_ae_planar {F G : ℂ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (h : F =ᵐ[volume] G) :
    ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      (fun (φ : ℝ) => F ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)))
        =ᵐ[volume.restrict (Ioo (-π) π)]
      (fun (φ : ℝ) => G ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) := by
  -- The polar identity turning `(r,φ)` back into `r e^{iφ}`.
  have hpsymm : ∀ (r φ : ℝ),
      Complex.polarCoord.symm (r, φ) = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
    intro r φ
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring
  -- The disagreement set and its indicator.
  set S : Set ℂ := {z | F z ≠ G z} with hSdef
  have hSm : MeasurableSet S := (measurableSet_eq_fun hF hG).compl
  set N : ℂ → ℝ≥0∞ := fun z => Set.indicator S (fun _ => (1 : ℝ≥0∞)) z with hNdef
  have hNm : Measurable N := Measurable.indicator measurable_const hSm
  -- The planar integral of the indicator is `0`.
  have hSnull : volume S = 0 := by rw [hSdef]; exact h
  have hintzero : (∫⁻ z, N z) = 0 := by
    rw [hNdef, lintegral_indicator hSm, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, hSnull, mul_zero]
  -- Rewrite as an iterated polar integral over `Ioi 0 ×ˢ Ioo (-π) π`.
  have hpolar : (∫⁻ z, N z)
      = ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
          ENNReal.ofReal q.1 • N (Complex.polarCoord.symm q) := by
    rw [← Complex.lintegral_comp_polarCoord_symm N]; rfl
  have haem : AEMeasurable
      (fun q : ℝ × ℝ => ENNReal.ofReal q.1 • N (Complex.polarCoord.symm q))
        ((volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)) :=
    Measurable.aemeasurable (Measurable.smul (ENNReal.measurable_ofReal.comp measurable_fst)
      (hNm.comp measurable_polarCoord_symm))
  rw [hpolar, Measure.volume_eq_prod, setLIntegral_prod _ haem] at hintzero
  -- Outer super-level: a.e. `r ∈ Ioi 0` the inner integral vanishes.
  have hinnermeas : Measurable (fun r : ℝ =>
      ∫⁻ φ in Ioo (-π) π,
        ENNReal.ofReal r • N (Complex.polarCoord.symm (r, φ))) := by
    apply Measurable.lintegral_prod_right
    exact Measurable.smul (ENNReal.measurable_ofReal.comp measurable_fst)
      (hNm.comp (measurable_polarCoord_symm.comp measurable_id))
  rw [setLIntegral_eq_zero_iff measurableSet_Ioi hinnermeas] at hintzero
  rw [← ae_restrict_iff' measurableSet_Ioi] at hintzero
  -- Descend to each circle.
  filter_upwards [hintzero, ae_restrict_mem measurableSet_Ioi] with r hr_inner hr_mem
  have hr : (0 : ℝ) < r := hr_mem
  -- Pull out the (nonzero, finite) radial weight.
  have hrne : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hinner0 : (∫⁻ φ in Ioo (-π) π, N (Complex.polarCoord.symm (r, φ))) = 0 := by
    have heq : (∫⁻ φ in Ioo (-π) π, ENNReal.ofReal r • N (Complex.polarCoord.symm (r, φ)))
        = ENNReal.ofReal r * ∫⁻ φ in Ioo (-π) π, N (Complex.polarCoord.symm (r, φ)) := by
      rw [← lintegral_const_mul' _ _ (by finiteness : ENNReal.ofReal r ≠ ∞)]
      exact lintegral_congr fun φ => smul_eq_mul _ _
    rw [heq] at hr_inner
    exact (mul_eq_zero.mp hr_inner).resolve_left hrne
  -- Inner super-level: a.e. `φ ∈ Ioo (-π) π` the indicator vanishes.
  have hNmeas_r : Measurable (fun φ : ℝ => N (Complex.polarCoord.symm (r, φ))) :=
    hNm.comp (measurable_polarCoord_symm.comp (measurable_const.prodMk measurable_id))
  rw [setLIntegral_eq_zero_iff measurableSet_Ioo hNmeas_r] at hinner0
  rw [← ae_restrict_iff' measurableSet_Ioo] at hinner0
  filter_upwards [hinner0] with φ hφ
  -- `N (r,φ) = 0` means `r e^{iφ} ∉ {F ≠ G}`, i.e. `F = G` there.
  rw [hNdef] at hφ
  simp only at hφ
  rw [Set.indicator_apply_eq_zero] at hφ
  have hnotmem : Complex.polarCoord.symm (r, φ) ∉ S := by
    intro hz; exact absurd (hφ hz) one_ne_zero
  rw [hSdef, Set.mem_setOf_eq, not_not] at hnotmem
  rw [hpsymm] at hnotmem
  exact hnotmem

/-- **Polar lift.** A per-circle a.e.-in-angle equality (on almost every circle) lifts back to a
planar a.e. equality. -/
theorem ae_planar_of_ae_slice {F G : ℂ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (h : ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      (fun (φ : ℝ) => F ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)))
        =ᵐ[volume.restrict (Ioo (-π) π)]
      (fun (φ : ℝ) => G ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)))) :
    F =ᵐ[volume] G := by
  -- The polar identity turning `(r,φ)` back into `r e^{iφ}`.
  have hpsymm : ∀ (r φ : ℝ),
      Complex.polarCoord.symm (r, φ) = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
    intro r φ
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring
  -- The disagreement set and its indicator.
  set S : Set ℂ := {z | F z ≠ G z} with hSdef
  have hSm : MeasurableSet S := (measurableSet_eq_fun hF hG).compl
  set N : ℂ → ℝ≥0∞ := fun z => Set.indicator S (fun _ => (1 : ℝ≥0∞)) z with hNdef
  have hNm : Measurable N := Measurable.indicator measurable_const hSm
  have hNmeas_r : ∀ r : ℝ, Measurable (fun φ : ℝ => N (Complex.polarCoord.symm (r, φ))) :=
    fun r => hNm.comp (measurable_polarCoord_symm.comp (measurable_const.prodMk measurable_id))
  -- On almost every circle the weighted inner integral vanishes.
  have hinner : ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      (∫⁻ φ in Ioo (-π) π, ENNReal.ofReal r • N (Complex.polarCoord.symm (r, φ)))
        = 0 := by
    filter_upwards [h] with r hr_eq
    -- The slice equality says the indicator vanishes a.e. on the angle interval.
    have hN0 : (∫⁻ φ in Ioo (-π) π, N (Complex.polarCoord.symm (r, φ))) = 0 := by
      rw [setLIntegral_eq_zero_iff measurableSet_Ioo (hNmeas_r r),
        ← ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hr_eq] with φ hφ
      rw [hpsymm, hNdef]
      simp only [Set.indicator_apply_eq_zero]
      intro hmem
      rw [hSdef, Set.mem_setOf_eq] at hmem
      exact absurd hφ hmem
    calc (∫⁻ φ in Ioo (-π) π, ENNReal.ofReal r • N (Complex.polarCoord.symm (r, φ)))
        = ENNReal.ofReal r * ∫⁻ φ in Ioo (-π) π, N (Complex.polarCoord.symm (r, φ)) := by
          rw [← lintegral_const_mul' _ _ (by finiteness : ENNReal.ofReal r ≠ ∞)]
          exact lintegral_congr fun φ => smul_eq_mul _ _
      _ = 0 := by rw [hN0, mul_zero]
  -- Hence the outer (radial) integral vanishes, so does the planar integral.
  have haem : AEMeasurable
      (fun q : ℝ × ℝ => ENNReal.ofReal q.1 • N (Complex.polarCoord.symm q))
        ((volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)) :=
    Measurable.aemeasurable (Measurable.smul (ENNReal.measurable_ofReal.comp measurable_fst)
      (hNm.comp measurable_polarCoord_symm))
  have houter : (∫⁻ r in Ioi (0 : ℝ), ∫⁻ φ in Ioo (-π) π,
      ENNReal.ofReal r • N (Complex.polarCoord.symm (r, φ))) = 0 := by
    rw [lintegral_congr_ae (by filter_upwards [hinner] with r hr using hr), lintegral_zero]
  have hpolar : (∫⁻ z, N z)
      = ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
          ENNReal.ofReal q.1 • N (Complex.polarCoord.symm q) := by
    rw [← Complex.lintegral_comp_polarCoord_symm N]; rfl
  have hintzero : (∫⁻ z, N z) = 0 := by
    rw [hpolar, Measure.volume_eq_prod, setLIntegral_prod _ haem, houter]
  -- Turn the vanishing indicator integral into a null disagreement set.
  have hSnull : volume S = 0 := by
    rw [hNdef, lintegral_indicator hSm, lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul] at hintzero
    exact hintzero
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  exact hSnull

/-! ### The angular two-point reflection -/

/-- The **angular two-point reflection** of a circle profile `g : ℝ → ℝ` across the axis at angle
`θ`: on the side `sin (φ − θ) ≥ 0` it takes the `max` of `g φ` and its mirror `g (2θ − φ)`, and the
`min` on the other side. This is the action of `polarizeDir θ` restricted to a circle. -/
def angReflect (θ : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun φ => if 0 ≤ Real.sin (φ - θ) then max (g φ) (g (2 * θ - φ)) else min (g φ) (g (2 * θ - φ))

/-- **Per-circle action of the directional polarization (pointwise).** On the circle of radius
`r > 0`, `polarizeDir θ v` acts on the angular profile `φ ↦ v (r e^{iφ})` as the angular two-point
reflection across the axis at angle `θ`. -/
theorem polarizeDir_apply_circle (θ : ℝ) (v : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    polarizeDir θ v (r * Complex.exp (φ * Complex.I))
      = angReflect θ (fun ψ => v (r * Complex.exp (ψ * Complex.I))) φ := by
  set z : ℂ := (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) with hz
  -- The rotated point `w = exp(-θI) * z` in polar form.
  have hw : Complex.exp (-((θ : ℝ) * Complex.I)) * z
      = (r : ℂ) * Complex.exp (((φ - θ : ℝ)) * Complex.I) := by
    rw [hz, ← mul_assoc, mul_comm (Complex.exp (-((θ : ℝ) * Complex.I))) (r : ℂ), mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  -- Its imaginary part.
  have hwim : (Complex.exp (-((θ : ℝ) * Complex.I)) * z).im = r * Real.sin (φ - θ) := by
    rw [hw, Complex.mul_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- The sign condition matches the angular one.
  have hsign : (0 ≤ (Complex.exp (-((θ : ℝ) * Complex.I)) * z).im)
      = (0 ≤ Real.sin (φ - θ)) := by
    rw [hwim]
    exact propext (mul_nonneg_iff_of_pos_left hr)
  -- The value at `w`.
  have hval : v (Complex.exp ((θ : ℝ) * Complex.I) * (Complex.exp (-((θ : ℝ) * Complex.I)) * z))
      = v ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) := by
    congr 1
    rw [hw, ← mul_assoc, mul_comm (Complex.exp ((θ : ℝ) * Complex.I)) (r : ℂ), mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  -- The value at `conj w`.
  have hconj : (starRingEnd ℂ) (Complex.exp (-((θ : ℝ) * Complex.I)) * z)
      = (r : ℂ) * Complex.exp (((-(φ - θ) : ℝ)) * Complex.I) := by
    rw [hw, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hvalconj :
      v (Complex.exp ((θ : ℝ) * Complex.I)
          * (starRingEnd ℂ) (Complex.exp (-((θ : ℝ) * Complex.I)) * z))
        = v ((r : ℂ) * Complex.exp (((2 * θ - φ : ℝ)) * Complex.I)) := by
    congr 1
    rw [hconj, ← mul_assoc, mul_comm (Complex.exp ((θ : ℝ) * Complex.I)) (r : ℂ), mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [polarizeDir, polarize, angReflect, hsign, hval, hvalconj]

/-- **Per-circle reduction (B1).** If `polarizeDir θ v =ᵐ v`, then for almost every radius `r` the
angular profile of `v` is a.e. fixed by the angular two-point reflection across angle `θ`. -/
theorem ae_circle_fixed_of_polarizeDir_fixed (θ : ℝ) (v : ℂ → ℝ) (hv : Measurable v)
    (hfix : polarizeDir θ v =ᵐ[volume] v) :
    ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      angReflect θ (fun (φ : ℝ) => v ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)))
        =ᵐ[volume.restrict (Ioo (-π) π)]
      (fun (φ : ℝ) => v ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) := by
  -- `polarizeDir θ v` is measurable.
  have hpv : Measurable (polarizeDir θ v) := by
    rw [polarizeDir_eq]
    set w := fun w => v (rotLIE θ w) with hw
    have hwmeas : Measurable w := by
      have hR : Measurable (fun w : ℂ => rotLIE θ w) := by
        simp only [rotLIE_apply]; exact measurable_const.mul measurable_id
      exact hv.comp hR
    have hpolw : Measurable (polarize w) := by
      unfold polarize
      have hconj : Measurable (starRingEnd ℂ) := conj_emb.measurable
      exact Measurable.ite (measurableSet_le measurable_const Complex.measurable_im)
        (hwmeas.max (hwmeas.comp hconj)) (hwmeas.min (hwmeas.comp hconj))
    exact hpolw.comp ((rotLIE θ).symm.continuous.measurable)
  -- Descend the planar fixed-point equality to each circle.
  have hslice := ae_slice_of_ae_planar hpv hv hfix
  filter_upwards [hslice, ae_restrict_mem measurableSet_Ioi] with r hr_eq hr_mem
  have hr : (0 : ℝ) < r := hr_mem
  -- On the circle of radius `r`, `polarizeDir θ v` acts as the angular reflection.
  have hfun : (fun (φ : ℝ) => polarizeDir θ v ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)))
      = angReflect θ (fun (ψ : ℝ) => v ((r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))) := by
    funext φ
    exact polarizeDir_apply_circle θ v hr φ
  rw [hfun] at hr_eq
  exact hr_eq

/-! ### The one-dimensional circle rigidity -/

/-- **Fixed-point order form (B2a).** If a profile `g` is a.e. fixed by the angular two-point
reflection across `θ`, then a.e. on the peak side `sin (φ − θ) ≥ 0` its mirror value is `≤` its
value. (The converse needs `g` to be `2π`-periodic, which is not assumed; only this direction is
consumed by the rigidity argument.) -/
theorem angReflect_fixed_order (θ : ℝ) (g : ℝ → ℝ) (hg : Measurable g)
    (hfix : angReflect θ g =ᵐ[volume.restrict (Ioo (-π) π)] g) :
    ∀ᵐ φ ∂(volume.restrict (Ioo (-π) π)),
      0 ≤ Real.sin (φ - θ) → g (2 * θ - φ) ≤ g φ := by
  filter_upwards [hfix] with φ hφ
  intro hsin
  simp only [angReflect] at hφ
  rw [if_pos hsin] at hφ
  exact max_eq_left_iff.mp hφ

/-- **Super-level bridge.** Two measurable `ℝ≥0∞`-valued functions on a measurable set `s` whose
super-level sets agree a.e. for every threshold in a countable dense set of levels are a.e. equal on
`s`. Reduces a function equality to a family of super-level-set equalities. -/
theorem ae_eq_of_superlevel_ae_eq {s : Set ℝ} (hs : MeasurableSet s)
    {f h : ℝ → ℝ≥0∞} (hf : Measurable f) (hh : Measurable h)
    {L : Set ℝ≥0∞} (hLcount : L.Countable) (hLdense : Dense L)
    (hlev : ∀ t ∈ L, {x ∈ s | t < f x} =ᵐ[volume] {x ∈ s | t < h x}) :
    f =ᵐ[volume.restrict s] h := by
  -- Turn each level equality into a pointwise iff, valid a.e.
  have hlev' : ∀ t ∈ L, ∀ᵐ x ∂volume, (x ∈ s ∧ t < f x) ↔ (x ∈ s ∧ t < h x) := by
    intro t ht
    filter_upwards [hlev t ht] with x hx
    simpa only [Set.mem_setOf_eq, eq_iff_iff] using hx
  -- Collect over the countable set of levels.
  have hall : ∀ᵐ x ∂volume, ∀ t ∈ L, (x ∈ s ∧ t < f x) ↔ (x ∈ s ∧ t < h x) :=
    (MeasureTheory.ae_ball_iff hLcount).mpr hlev'
  rw [Filter.EventuallyEq, ae_restrict_iff' hs]
  filter_upwards [hall] with x hx
  intro hxs
  -- On `x ∈ s`, the collected iffs reduce to `∀ t ∈ L, t < f x ↔ t < h x`.
  have hiff : ∀ t ∈ L, (t < f x ↔ t < h x) := by
    intro t ht
    have := hx t ht
    simpa only [hxs, true_and] using this
  -- Conclude `f x = h x` by contradiction using density of `L`.
  by_contra hne
  -- WLOG `f x < h x`; the other case is symmetric.
  have hcore : ∀ a b : ℝ≥0∞, a < b → (∀ t ∈ L, (t < a ↔ t < b)) → False := by
    intro a b hab hiffab
    have hne : (Set.Ioo a b).Nonempty := Set.nonempty_Ioo.mpr hab
    obtain ⟨t, htL, htab⟩ := hLdense.exists_mem_open isOpen_Ioo hne
    have h1 : t < b := htab.2
    have h2 : ¬ t < a := not_lt.mpr (le_of_lt htab.1)
    exact h2 ((hiffab t htL).mpr h1)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hcore (f x) (h x) hlt hiff
  · exact hcore (h x) (f x) hgt (fun t ht => (hiff t ht).symm)

/-! ### The top-level rigidity theorems -/

/-- **Circular symmetrization from per-radius equidistribution.** If `v` and `u` have, on every
circle, the same angular distribution function of their exponential encodings, then their circular
symmetrizations about `0` coincide. -/
theorem circSymm_congr_of_superlevel_eq (v u : ℂ → ℝ)
    (hdist : ∀ r : ℝ, distribFun (2 * π) (angularProfile 0 (fun w => realEnc (v w)) r)
      = distribFun (2 * π) (angularProfile 0 (fun w => realEnc (u w)) r)) :
    circSymm 0 v = circSymm 0 u := by
  funext z
  simp only [circSymm]
  congr 1
  congr 1
  show circRearrange 0 (fun w => realEnc (v w)) z = circRearrange 0 (fun w => realEnc (u w)) z
  simp only [circRearrange, sub_zero]
  exact congrFun (decreasingRearrangeSymm_congr (hdist ‖z‖)) (Complex.arg z + π)

end RiemannDynamics

end

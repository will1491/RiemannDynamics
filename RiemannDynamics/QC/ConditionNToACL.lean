/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.LengthArea
import RiemannDynamics.QC.BanachZaretsky
import RiemannDynamics.QC.BanachIndicatrix
import RiemannDynamics.QC.PlanarCoarea

/-!
# Weak gradient ⟹ ACL (the Sobolev `W^{1,1}_loc ⇒ ACL` direction, all PROVEN)

A continuous map `g : ℂ → ℂ` whose `L¹_loc` pointwise partials `gx`/`gy` are its **weak
(distributional)** directional derivatives (`HasWeakDirDeriv 1 gx g univ`,
`HasWeakDirDeriv I gy g univ` — i.e. `g ∈ W^{1,1}_loc`) is **absolutely continuous on almost every
horizontal line** (and, symmetrically, on almost every vertical line), with the pointwise partial
as the classical line derivative, satisfying the per-slice fundamental theorem of calculus.
Everything in this file is **fully proven** (axiom-clean); the single genuine analytic input is the
weak-gradient hypothesis, threaded in from the caller.

## ⚠ Correctness fix (2026-06-20): the weak-gradient hypothesis is genuinely necessary

A previous version of this development tried to derive a.e.-slice absolute continuity from purely
*pointwise* a.e. data — condition (N⁺) (`E ↦ volume (g '' E)` absolutely continuous) plus
injectivity plus `L¹_loc` *pointwise* partials, packaged through the swept-area set function
`Φ_{c,d}(I) := volume (g '' (I ×ℂ Icc c d))` and a co-area / Banach-indicatrix residual. **That
route is FALSE.** Condition (N⁺) and the area set function constrain only the **Jacobian / swept
area**, never the off-diagonal *tangential* partial, whose distributional part can be singular while
its pointwise a.e. value is harmless. The decisive counterexample is the **area-preserving singular
shear** `g ⟨x, y⟩ = x + i·(y + s x)`, with `s` a continuous strictly-increasing singular function
(e.g. Minkowski `?`): it is injective, continuous, a.e.-differentiable with `Dg = id` a.e., hence
**measure-preserving** (so it satisfies (N⁺), the pointwise dilatation bound, and has `L²_loc`
*pointwise* partials), yet **every** horizontal slice's imaginary part `y + s ·` is singular (not
AC). The honest extra ingredient is exactly that `gx`/`gy` be the *weak* derivatives —
`g ∈ W^{1,1}_loc` — which the shear fails (`∂ₓ(g.im) = ds`, a singular measure, not the
a.e.-pointwise `0`). For the quasiconformal inverse the weak gradient is genuine via `MemW12loc`
(`IsQCAnalytic.inverse_memW12loc`).

The former false residual (`ae_slice_monotoneDecompN_x` in `QC/PlanarCoarea`, and the
`ae_slice_*_of_area` / `slice_*_of_area` / `weakDirDeriv_*_of_conditionNPlus` machinery here) has
been **removed**; the sound replacement is `ae_slice_ac_of_weakDirDeriv_x` (`QC/PlanarCoarea`),
which consumes the weak-derivative hypothesis directly.

## The proof (Sobolev ⇒ ACL, Nikodym; Evans–Gariepy §4.9.2)

Once `gx` is the weak `x`-derivative, the converse Sobolev embedding gives an AC-on-lines
representative `g' =ᵐ g` (`exists_aclHorizontal_of_hasWeakDirDeriv_one`); a continuity transfer
(`g` continuous, `g'`'s slice AC hence continuous, agreeing a.e. ⟹ everywhere) upgrades the AC to
`g`'s own slice. The per-slice FTC `g ⟨b, y⟩ - g ⟨a, y⟩ = ∫ₐᵇ gx ⟨t, y⟩` then follows from the FTC
for absolutely continuous functions (`complex_ac_ftc_slice`) and the Fubini slice derivative
(`ae_slice_hasDerivAt_x`).

## Main results (all PROVEN, axiom-clean)

* `slice_isAbsolutelyContinuous_x_of_conditionNPlus` /
  `slice_isAbsolutelyContinuous_y_of_conditionNPlus` — for `g` continuous with the weak
  directional derivative `gx`/`gy`, a.e. slice is absolutely continuous (reduction to
  `ae_slice_ac_of_weakDirDeriv_x` in `QC/PlanarCoarea`);
* `slice_fundamentalTheorem_x` / `slice_fundamentalTheorem_y` — the per-slice fundamental theorem
  of calculus `g ⟨b, y⟩ - g ⟨a, y⟩ = ∫ₐᵇ gx ⟨t, y⟩`, from the absolute-continuity result via
  Fubini and the componentwise FTC for AC functions (`complex_ac_ftc_slice`);
* `aclHorizontal_of_conditionNPlus` / `aclVertical_of_conditionNPlus` — the target theorems,
  reducing the FTC core to `ACLHorizontal`/`ACLVertical`. (Names retained for the keystone caller in
  `QC/LengthAreaInverse`; the genuine hypothesis is now the weak gradient, not condition (N⁺).)
-/

open MeasureTheory Complex Set Filter
open scoped ENNReal Topology ContDiff

namespace RiemannDynamics

/-! ## Slice integrability via Fubini (proven) -/

/-- Local integrability of `G : ℂ → ℂ` transfers to its real-product realization. -/
private theorem locallyIntegrable_realProd_of_locallyIntegrable {G : ℂ → ℂ}
    (hG : LocallyIntegrable G) :
    LocallyIntegrable (fun p : ℝ × ℝ => G ⟨p.1, p.2⟩) volume := by
  rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
  set e := Complex.measurableEquivRealProd
  have hmpsymm : MeasurePreserving e.symm (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    (Complex.volume_preserving_equiv_real_prod).symm e
  have hcont : Continuous (e.symm : ℝ × ℝ → ℂ) := by
    have : (e.symm : ℝ × ℝ → ℂ) = (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) := by
      ext p; simp [e, Complex.measurableEquivRealProd, Complex.equivRealProdCLM]
    rw [this]; exact Complex.equivRealProdCLM.symm.continuous
  have himg : IsCompact (e.symm '' K) := hK.image hcont
  have hGon : IntegrableOn G (e.symm '' K) volume := hG.integrableOn_isCompact himg
  have hmeas : MeasurableEmbedding e.symm := e.symm.measurableEmbedding
  have key : IntegrableOn (G ∘ e.symm) (e.symm ⁻¹' (e.symm '' K)) volume :=
    (hmpsymm.integrableOn_comp_preimage hmeas).mpr hGon
  rw [e.symm.injective.preimage_image] at key; exact key

/-- **a.e.-slice interval integrability** from joint local integrability (Fubini). For a locally
integrable `G : ℝ × ℝ → ℂ`, for almost every `y`, the slice `x ↦ G (x, y)` is interval
integrable on every interval. -/
private theorem ae_slice_intervalIntegrable {G : ℝ × ℝ → ℂ} (hG : LocallyIntegrable G volume) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ, IntervalIntegrable (fun x => G (x, y)) volume a b := by
  have hslice' : ∀ n : ℕ, ∀ᵐ y : ℝ, y ∈ Icc (-(n : ℝ)) n →
      IntegrableOn (fun x => G (x, y)) (Icc (-(n : ℝ)) n) volume := by
    intro n
    have hbox : Integrable G ((volume.restrict (Icc (-(n : ℝ)) n)).prod
        (volume.restrict (Icc (-(n : ℝ)) n))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hG.integrableOn_isCompact (isCompact_Icc.prod isCompact_Icc)
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
  have hyn : y ∈ Icc (-(n : ℝ)) n := ⟨hyb.1, hyb.2⟩
  have hint := hy n hyn
  have hsub : uIcc a b ⊆ Icc (-(n : ℝ)) n := by
    intro t ht; rw [Set.mem_uIcc] at ht; rw [Set.mem_Icc]
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [intervalIntegrable_iff]
  exact hint.mono_set (le_trans Set.uIoc_subset_uIcc hsub)

/-! ## Reduction of the slice FTC to ACL (proven)

From the slice FTC `g ⟨b, y⟩ - g ⟨a, y⟩ = ∫ₐᵇ gx ⟨t, y⟩` (with `t ↦ gx ⟨t, y⟩` interval
integrable on a.e. slice) the two pieces of `ACLHorizontal` follow:

* **Absolute continuity.** The slice equals `g ⟨0, y⟩ + ∫₀ˣ gx ⟨t, y⟩`, the constant plus the
  primitive of an integrable function; primitives of integrable functions are AC
  (`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`), componentwise in
  `re`/`im`.
* **Line-derivative.** By the Lebesgue differentiation theorem
  (`LocallyIntegrable.ae_hasDerivAt_integral`) the primitive's derivative is `gx ⟨x, y⟩`
  a.e., so the slice has classical derivative `gx ⟨x, y⟩` a.e. -/

/-- The componentwise recombination: a `ℂ`-valued function whose `re` and `im` slices are AC is
AC. -/
private theorem absolutelyContinuousOnInterval_of_re_im {F : ℝ → ℂ} {a b : ℝ}
    (hre : AbsolutelyContinuousOnInterval (fun x => (F x).re) a b)
    (him : AbsolutelyContinuousOnInterval (fun x => (F x).im) a b) :
    AbsolutelyContinuousOnInterval F a b := by
  rw [absolutelyContinuousOnInterval_iff] at hre him ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hre (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := him (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hE hlen => ?_⟩
  have hl1 : ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ₁ :=
    lt_of_lt_of_le hlen (min_le_left _ _)
  have hl2 : ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ₂ :=
    lt_of_lt_of_le hlen (min_le_right _ _)
  have k1 := h₁ E hE hl1
  have k2 := h₂ E hE hl2
  have hbound : ∀ i, dist (F (E.2 i).1) (F (E.2 i).2)
      ≤ dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
        + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) := by
    intro i
    rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
    calc ‖F (E.2 i).1 - F (E.2 i).2‖
        ≤ |(F (E.2 i).1 - F (E.2 i).2).re| + |(F (E.2 i).1 - F (E.2 i).2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |(F (E.2 i).1).re - (F (E.2 i).2).re| + |(F (E.2 i).1).im - (F (E.2 i).2).im| := by
          rw [Complex.sub_re, Complex.sub_im]
  calc ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, (dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
          + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im)) :=
        Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).re) ((F (E.2 i).2).re))
        + ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) := by
        rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add k1 k2
    _ = ε := by ring

/-- An `ℝ`-valued primitive `x ↦ ∫₀ˣ φ` of an interval-integrable `φ : ℝ → ℝ` is absolutely
continuous on every interval. We enlarge to an interval `uIcc (-n) n` that contains both `0`
and `uIcc a b`, apply Mathlib's AC-of-primitive there (the base point `0` lies in it), and
restrict. -/
private theorem absolutelyContinuousOnInterval_realPrimitive {φ : ℝ → ℝ}
    (hφ : ∀ a b : ℝ, IntervalIntegrable φ volume a b) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, φ t) a b := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max (|a|) (|b|))
  have h3 := le_max_left (|a|) (|b|)
  have h4 := le_max_right (|a|) (|b|)
  have ha : |a| ≤ n := by linarith
  have hb : |b| ≤ n := by linarith
  rw [abs_le] at ha hb
  have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnn : -(n : ℝ) ≤ (n : ℝ) := by linarith
  have h0 : (0 : ℝ) ∈ uIcc (-(n : ℝ)) n := by
    rw [Set.uIcc_of_le hnn]; exact ⟨by linarith, hN⟩
  have hbig : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, φ t)
      (-(n : ℝ)) n :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (hφ _ _) h0
  refine hbig.mono ?_
  rw [Set.uIcc_of_le hnn]
  intro t ht
  rw [Set.mem_uIcc] at ht
  rw [Set.mem_Icc]
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The `re`-component of an interval-integrable `ℂ`-valued function is interval integrable. -/
private theorem IntervalIntegrable.re_comp {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun t => (φ t).re) volume a b := by
  rw [intervalIntegrable_iff] at hφ ⊢
  exact hφ.re

/-- The `im`-component of an interval-integrable `ℂ`-valued function is interval integrable. -/
private theorem IntervalIntegrable.im_comp {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun t => (φ t).im) volume a b := by
  rw [intervalIntegrable_iff] at hφ ⊢
  exact hφ.im

/-- `re` commutes with the interval integral of a `ℂ`-valued function. -/
private theorem re_intervalIntegral {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    (∫ t in a..b, φ t).re = ∫ t in a..b, (φ t).re := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hφ
  simpa [Complex.reCLM_apply] using this.symm

/-- `im` commutes with the interval integral of a `ℂ`-valued function. -/
private theorem im_intervalIntegral {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    (∫ t in a..b, φ t).im = ∫ t in a..b, (φ t).im := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hφ
  simpa [Complex.imCLM_apply] using this.symm

/-- A `ℂ`-valued primitive `x ↦ ∫₀ˣ φ` of an interval-integrable `φ : ℝ → ℂ` is absolutely
continuous on every interval (componentwise in `re`/`im`). -/
private theorem absolutelyContinuousOnInterval_complexPrimitive {φ : ℝ → ℂ}
    (hφ : ∀ a b : ℝ, IntervalIntegrable φ volume a b) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, φ t) a b := by
  refine absolutelyContinuousOnInterval_of_re_im ?_ ?_
  · have hre : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, (φ t).re) a b :=
      absolutelyContinuousOnInterval_realPrimitive
        (fun a b => IntervalIntegrable.re_comp (hφ a b)) a b
    convert hre using 2 with x
    exact re_intervalIntegral (hφ 0 x)
  · have him : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, (φ t).im) a b :=
      absolutelyContinuousOnInterval_realPrimitive
        (fun a b => IntervalIntegrable.im_comp (hφ a b)) a b
    convert him using 2 with x
    exact im_intervalIntegral (hφ 0 x)

/-- An `ℝ → ℝ` function that is interval integrable on every interval is locally integrable. -/
private theorem locallyIntegrable_realPart {ψ : ℝ → ℝ}
    (hψ : ∀ a b : ℝ, IntervalIntegrable ψ volume a b) : LocallyIntegrable ψ volume := by
  rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
  obtain ⟨a, ha⟩ := hK.bddBelow; obtain ⟨b, hb⟩ := hK.bddAbove
  have hsub : K ⊆ Icc a b := fun x hx => ⟨ha hx, hb hx⟩
  rcases le_or_gt a b with hle | hlt
  · have := hψ a b
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle] at this
    exact this.mono_set hsub
  · rw [Icc_eq_empty (not_le.2 hlt), subset_empty_iff] at hsub
    rw [hsub]; exact integrableOn_empty

/-- **Derivative of the `ℂ`-valued primitive (Lebesgue differentiation).** If `φ : ℝ → ℂ` is
interval integrable on every interval, then for almost every `x` the primitive `∫₀ˣ φ` has
derivative `φ x` at `x`. (Componentwise Lebesgue differentiation, recombined.) -/
private theorem ae_hasDerivAt_complexPrimitive {φ : ℝ → ℂ}
    (hφ : ∀ a b : ℝ, IntervalIntegrable φ volume a b) :
    ∀ᵐ x : ℝ, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, φ t) (φ x) x := by
  have hLI_re : LocallyIntegrable (fun t => (φ t).re) volume :=
    locallyIntegrable_realPart (fun a b => IntervalIntegrable.re_comp (hφ a b))
  have hLI_im : LocallyIntegrable (fun t => (φ t).im) volume :=
    locallyIntegrable_realPart (fun a b => IntervalIntegrable.im_comp (hφ a b))
  have hderiv_re := _root_.LocallyIntegrable.ae_hasDerivAt_integral hLI_re
  have hderiv_im := _root_.LocallyIntegrable.ae_hasDerivAt_integral hLI_im
  filter_upwards [hderiv_re, hderiv_im] with x hxre hxim
  have hre' : HasDerivAt (fun x => (∫ t in (0 : ℝ)..x, φ t).re) (φ x).re x := by
    have := hxre 0
    refine this.congr_of_eventuallyEq ?_
    filter_upwards with u
    exact re_intervalIntegral (hφ 0 u)
  have him' : HasDerivAt (fun x => (∫ t in (0 : ℝ)..x, φ t).im) (φ x).im x := by
    have := hxim 0
    refine this.congr_of_eventuallyEq ?_
    filter_upwards with u
    exact im_intervalIntegral (hφ 0 u)
  -- Recombine `re`/`im` into the `ℂ`-derivative.
  have hcombine : HasDerivAt
      (fun x => (((∫ t in (0 : ℝ)..x, φ t).re : ℂ))
        + ((∫ t in (0 : ℝ)..x, φ t).im : ℂ) * Complex.I)
      (((φ x).re : ℂ) + ((φ x).im : ℂ) * Complex.I) x :=
    hre'.ofReal_comp.add ((him'.ofReal_comp).mul_const Complex.I)
  have heqfun : (fun x => (((∫ t in (0 : ℝ)..x, φ t).re : ℂ))
      + ((∫ t in (0 : ℝ)..x, φ t).im : ℂ) * Complex.I)
      = (fun x => ∫ t in (0 : ℝ)..x, φ t) := by
    funext x; exact Complex.re_add_im _
  rw [heqfun] at hcombine
  rwa [Complex.re_add_im] at hcombine

/-! ## The slice FTC from slice absolute continuity (all PROVEN)

`slice_fundamentalTheorem_x` recovers, on almost every horizontal slice, the fundamental theorem of
calculus with the pointwise partial `gx` as density. It is reduced, by a *fully proven* (Fubini +
componentwise FTC-for-AC-functions) argument, to the slice absolute continuity
(`slice_isAbsolutelyContinuous_x_of_conditionNPlus`). Once a slice is absolutely continuous, the
fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) recovers it from its a.e. derivative, and
Fubini identifies that a.e. derivative with the pointwise partial `gx` and supplies its interval
integrability. The slice absolute continuity is itself the converse Sobolev embedding
`W^{1,1}_loc ⇒ ACL` (`ae_slice_ac_of_weakDirDeriv_x`, `QC/PlanarCoarea`), consuming the
weak-gradient hypothesis. -/

/-! ### Fully-proven reductions: FTC-for-AC slices and the Fubini slice derivative -/

/-- **Complex fundamental theorem of calculus for an absolutely continuous slice.** If
`h : ℝ → ℂ` is absolutely continuous on `uIcc a b`, has pointwise derivative `h' t` for almost
every `t`, and `h'` is interval integrable on `a..b`, then `h b - h a = ∫ₐᵇ h'`.

Componentwise: the real and imaginary parts of `h` are real absolutely continuous (Lipschitz
composition), so Mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` applies to
each, and the a.e. derivatives `deriv (re ∘ h)`, `deriv (im ∘ h)` agree a.e. with `(h' ·).re`,
`(h' ·).im`; recombine through `Complex.re_add_im`. (This is the complex analogue of the real
Mathlib FTC; it is `private`-local because the project copy in `LengthArea` is `private`.) -/
private theorem complex_ac_ftc_slice {h h' : ℝ → ℂ} {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval h a b)
    (hderiv : ∀ᵐ t : ℝ, HasDerivAt h (h' t) t)
    (hint : IntervalIntegrable h' volume a b) :
    h b - h a = ∫ t in a..b, h' t := by
  -- Lipschitz composition: the real/imaginary parts of an AC slice are AC.
  have hLipComp : ∀ {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → AbsolutelyContinuousOnInterval (fun t => l (h t)) a b := by
    intro Y _ l K hl
    rw [absolutelyContinuousOnInterval_iff] at hac ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hac (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (h (E.2 i).1)) (l (h (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (h (E.2 i).1) (h (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (h (E.2 i).1) (h (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hre_ac : AbsolutelyContinuousOnInterval (fun t => (h t).re) a b :=
    hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz
  have him_ac : AbsolutelyContinuousOnInterval (fun t => (h t).im) a b :=
    hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz
  -- a.e. derivatives of the real/imaginary parts.
  have hre_deriv_eq : ∀ᵐ t : ℝ, deriv (fun s => (h s).re) t = (h' t).re := by
    filter_upwards [hderiv] with t ht
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using this.deriv
  have him_deriv_eq : ∀ᵐ t : ℝ, deriv (fun s => (h s).im) t = (h' t).im := by
    filter_upwards [hderiv] with t ht
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using this.deriv
  -- Real FTC on each part.
  have hre_ftc : ∫ t in a..b, deriv (fun s => (h s).re) t = (h b).re - (h a).re :=
    hre_ac.integral_deriv_eq_sub
  have him_ftc : ∫ t in a..b, deriv (fun s => (h s).im) t = (h b).im - (h a).im :=
    him_ac.integral_deriv_eq_sub
  -- Replace the `deriv (… .re)` integrand by `(h' ·).re` under the integral sign.
  have hre_congr : (∫ t in a..b, deriv (fun s => (h s).re) t) = ∫ t in a..b, (h' t).re :=
    intervalIntegral.integral_congr_ae (by filter_upwards [hre_deriv_eq] with t ht _ using ht)
  have him_congr : (∫ t in a..b, deriv (fun s => (h s).im) t) = ∫ t in a..b, (h' t).im :=
    intervalIntegral.integral_congr_ae (by filter_upwards [him_deriv_eq] with t ht _ using ht)
  have hre_int : ∫ t in a..b, (h' t).re = (h b).re - (h a).re := by rw [← hre_congr, hre_ftc]
  have him_int : ∫ t in a..b, (h' t).im = (h b).im - (h a).im := by rw [← him_congr, him_ftc]
  -- Conclude componentwise.
  apply Complex.ext
  · rw [Complex.sub_re, re_intervalIntegral hint, hre_int]
  · rw [Complex.sub_im, im_intervalIntegral hint, him_int]

/-- **The horizontal-slice derivative, a.e., from a.e. differentiability (Fubini).** From
`g` differentiable for almost every plane point and `gx w = (Dg w) 1` for almost every plane
point, for almost every `y` the horizontal slice `t ↦ g ⟨t, y⟩` has derivative `gx ⟨x, y⟩` for
almost every `x`. The slice derivative is `(fderiv ℝ g ⟨x, y⟩) 1` by the chain rule for the
affine slice map `t ↦ ⟨t, y⟩` (derivative `1`), identified with `gx ⟨x, y⟩` via `hgx`; the
plane-to-slice transfer is the volume-preserving `ℂ ≃ ℝ × ℝ` plus `Measure.ae_ae_of_ae_prod`. -/
private theorem ae_slice_hasDerivAt_x {g : ℂ → ℂ}
    (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    {gx : ℂ → ℂ} (hgx : ∀ᵐ w, gx w = (fderiv ℝ g w) 1) :
    ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, HasDerivAt (fun t : ℝ => g ⟨t, y⟩) (gx ⟨x, y⟩) x := by
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  -- Combine the two plane-a.e. facts, then transfer to a.e. slices.
  have hcombined : ∀ᵐ w : ℂ, DifferentiableAt ℝ g w ∧ gx w = (fderiv ℝ g w) 1 := hgdiff.and hgx
  -- Pull back to `ℝ × ℝ`, swap coordinates, take iterated a.e.
  have hprod : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ g ⟨p.2, p.1⟩ ∧
      gx ⟨p.2, p.1⟩ = (fderiv ℝ g ⟨p.2, p.1⟩) 1 := by
    have hpb : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ g ⟨p.1, p.2⟩ ∧
        gx ⟨p.1, p.2⟩ = (fderiv ℝ g ⟨p.1, p.2⟩) 1 := by
      have := hmpsymm.quasiMeasurePreserving.ae hcombined
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hpb
    simpa [Prod.swap] using this
  have hline : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ g ⟨x, y⟩ ∧
      gx ⟨x, y⟩ = (fderiv ℝ g ⟨x, y⟩) 1 := MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hline] with y hy
  filter_upwards [hy] with x hx
  obtain ⟨hx_diff, hx_eq⟩ := hx
  -- Chain rule: the affine slice map `t ↦ ⟨t, y⟩` has derivative `1`.
  have haff : HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
    have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
      funext t; apply Complex.ext <;> simp
    rw [he]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
  have hfd : HasFDerivAt g (fderiv ℝ g ⟨x, y⟩) ⟨x, y⟩ := hx_diff.hasFDerivAt
  have := hfd.comp_hasDerivAt x haff
  rw [hx_eq]; simpa using this

/-- **The vertical-slice derivative, a.e., from a.e. differentiability (Fubini).** Symmetric to
`ae_slice_hasDerivAt_x`: for almost every `x` the vertical slice `t ↦ g ⟨x, t⟩` has derivative
`gy ⟨x, t⟩` for almost every `t`, where `gy w = (Dg w) I` and the slice derivative is computed
along the affine map `t ↦ ⟨x, t⟩` (derivative `I`). -/
private theorem ae_slice_hasDerivAt_y {g : ℂ → ℂ}
    (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    {gy : ℂ → ℂ} (hgy : ∀ᵐ w, gy w = (fderiv ℝ g w) Complex.I) :
    ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, HasDerivAt (fun t : ℝ => g ⟨x, t⟩) (gy ⟨x, y⟩) y := by
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hcombined : ∀ᵐ w : ℂ, DifferentiableAt ℝ g w ∧ gy w = (fderiv ℝ g w) Complex.I :=
    hgdiff.and hgy
  -- Pull back to `ℝ × ℝ` directly (no swap: the outer a.e. is over the first coordinate `x`).
  have hprod : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ g ⟨p.1, p.2⟩ ∧
      gy ⟨p.1, p.2⟩ = (fderiv ℝ g ⟨p.1, p.2⟩) Complex.I := by
    have := hmpsymm.quasiMeasurePreserving.ae hcombined
    filter_upwards [this] with p hp
    simpa [Complex.measurableEquivRealProd_symm_apply] using hp
  have hline : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, DifferentiableAt ℝ g ⟨x, y⟩ ∧
      gy ⟨x, y⟩ = (fderiv ℝ g ⟨x, y⟩) Complex.I := MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hline] with x hx
  filter_upwards [hx] with y hy
  obtain ⟨hy_diff, hy_eq⟩ := hy
  -- Chain rule: the affine slice map `t ↦ ⟨x, t⟩` has derivative `I`.
  have haff : HasDerivAt (fun t : ℝ => (⟨x, t⟩ : ℂ)) Complex.I y := by
    have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
      funext t; apply Complex.ext <;> simp
    rw [he]
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ)
  have hfd : HasFDerivAt g (fderiv ℝ g ⟨x, y⟩) ⟨x, y⟩ := hy_diff.hasFDerivAt
  have := hfd.comp_hasDerivAt y haff
  rw [hy_eq]; simpa using this

/-! ### Slice absolute continuity, fully reduced to the distributional residual

The two lemmas below recover the per-slice absolute continuity of `g` itself from the
distributional residual, by the representative + continuity-transfer argument described above.
Both reductions are **fully proven**; they consume no per-line condition-(N). -/

/-- **Absolute continuity of horizontal slices from the weak `x`-derivative** (`W^{1,1}_loc ⇒
ACL`). For a continuous map `g` with `L¹_loc` `x`-partial witness `gx` that is its **weak
(distributional)** `x`-derivative (`hweak : HasWeakDirDeriv 1 gx g univ`), for almost every `y` the
horizontal slice `t ↦ g ⟨t, y⟩` is absolutely continuous on every interval.

This is the converse Sobolev embedding; it is reduced to `ae_slice_ac_of_weakDirDeriv_x`
(`QC/PlanarCoarea`), proven from the weak-gradient hypothesis via the AC representative
`exists_aclHorizontal_of_hasWeakDirDeriv_one` and a continuity transfer. The weak-gradient
hypothesis is the genuine analytic input and is genuinely necessary (see the module docstring: the
area-preserving singular shear has all the pointwise a.e. data yet singular slices). -/
theorem slice_isAbsolutelyContinuous_x_of_conditionNPlus {g : ℂ → ℂ}
    (hgcont : Continuous g)
    {gx : ℂ → ℂ} (hgxLI : LocallyIntegrable gx)
    (hweak : HasWeakDirDeriv 1 gx g Set.univ) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x : ℝ => g ⟨x, y⟩) a b :=
  ae_slice_ac_of_weakDirDeriv_x hgcont hgxLI hweak

/-- **Absolute continuity of vertical slices from the weak `y`-derivative** (`W^{1,1}_loc ⇒ ACL`,
vertical). Identical to `slice_isAbsolutelyContinuous_x_of_conditionNPlus` with the two coordinates
swapped (the `y`-partial witness `gy` is the weak `I`-directional derivative,
`hweak : HasWeakDirDeriv I gy g univ`).

Proven from the weak-gradient hypothesis via the AC representative
`exists_aclVertical_of_hasWeakDirDeriv_I` and a continuity transfer (vertical analogue of
`ae_slice_ac_of_weakDirDeriv_x`). -/
theorem slice_isAbsolutelyContinuous_y_of_conditionNPlus {g : ℂ → ℂ}
    (hgcont : Continuous g)
    {gy : ℂ → ℂ} (hgyLI : LocallyIntegrable gy)
    (hweak : HasWeakDirDeriv Complex.I gy g Set.univ) :
    ∀ᵐ x : ℝ, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun y : ℝ => g ⟨x, y⟩) a b := by
  have hgLI : LocallyIntegrable g := hgcont.locallyIntegrable
  -- An AC-on-vertical-lines representative `g'`, equal to `g` a.e.
  obtain ⟨g', hg'ae, hg'acl⟩ :=
    exists_aclVertical_of_hasWeakDirDeriv_I hgLI hgyLI hweak
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hae2 : (fun p : ℝ × ℝ => g' ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
      (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) := by
    rw [← Measure.volume_eq_prod]
    have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hg'ae
    filter_upwards [this] with p hp
    simpa [Complex.measurableEquivRealProd_symm_apply] using hp
  -- For vertical slices the outer a.e. is over the first coordinate `x` (no swap).
  have hslice_eq : ∀ᵐ x : ℝ,
      (fun y : ℝ => g' ⟨x, y⟩) =ᵐ[volume] (fun y : ℝ => g ⟨x, y⟩) :=
    Measure.ae_ae_eq_of_ae_eq_uncurry hae2
  have hsliceCont : ∀ x : ℝ, Continuous (fun y : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro x
    have he : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [he]
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hg'ac : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => g' ⟨x, y⟩) a b := by
    filter_upwards [hg'acl] with x hx; exact hx.1
  filter_upwards [hg'ac, hslice_eq] with x hac' hx_eq
  set s  : ℝ → ℂ := fun y => g ⟨x, y⟩ with hs
  set s' : ℝ → ℂ := fun y => g' ⟨x, y⟩ with hs'
  have hcont_s : Continuous s := hgcont.comp (hsliceCont x)
  have hcont_s' : Continuous s' := by
    rw [continuous_iff_continuousAt]
    intro y
    have hco := (hac' (y - 1) (y + 1)).continuousOn
    rw [Set.uIcc_of_le (by linarith)] at hco
    exact (hco y ⟨by linarith, by linarith⟩).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  have heq : s' = s := (hcont_s'.ae_eq_iff_eq (μ := volume) hcont_s).mp hx_eq
  intro a b; rw [← heq]; exact hac' a b

/-! ### The slice FTC, fully reduced to the absolute-continuity residual -/

/-- **Fundamental theorem of calculus on horizontal slices** (from the weak gradient). For a
continuous a.e.-differentiable map whose `L¹_loc` `x`-partial witness `gx` is its **weak**
`x`-derivative (`hweak : HasWeakDirDeriv 1 gx g univ`), for almost every imaginary part `y` the
horizontal slice `t ↦ g ⟨t, y⟩` recovers itself from `gx` by the fundamental theorem of calculus:
`g ⟨b, y⟩ - g ⟨a, y⟩ = ∫ₐᵇ gx ⟨t, y⟩` for all `a, b`.

Proven by a *fully proven* reduction to the slice absolute continuity
`slice_isAbsolutelyContinuous_x_of_conditionNPlus`: once a slice is absolutely continuous, the FTC
for absolutely continuous functions recovers it from its a.e. derivative, which Fubini identifies
with `gx ⟨·, y⟩` and supplies as interval integrable.

The genuine analytic content is the weak-gradient hypothesis (`g ∈ W^{1,1}_loc`), which is
genuinely necessary: the area-preserving singular shear `g ⟨x, y⟩ = x + i·(y + s x)` satisfies all
the pointwise a.e. data (injective, continuous, a.e.-diff, condition (N⁺), pointwise dilatation
bound) yet has singular slices, so its slice FTC fails — see the module docstring. -/
theorem slice_fundamentalTheorem_x {g : ℂ → ℂ}
    (hgcont : Continuous g) (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    {gx : ℂ → ℂ} (hgx : ∀ᵐ w, gx w = (fderiv ℝ g w) 1)
    (hgxLI : LocallyIntegrable gx)
    (hweak : HasWeakDirDeriv 1 gx g Set.univ) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ, g ⟨b, y⟩ - g ⟨a, y⟩ = ∫ t in a..b, gx ⟨t, y⟩ := by
  -- The genuine residual: a.e. slice is absolutely continuous.
  have hAC :=
    slice_isAbsolutelyContinuous_x_of_conditionNPlus hgcont hgxLI hweak
  -- a.e. slice has derivative `gx ⟨x, y⟩` (Fubini).
  have hderiv := ae_slice_hasDerivAt_x hgdiff hgx
  -- a.e. slice integrability of `gx` (Fubini).
  have hII : ∀ᵐ y : ℝ, ∀ a b : ℝ, IntervalIntegrable (fun t => gx ⟨t, y⟩) volume a b := by
    have := ae_slice_intervalIntegrable
      (locallyIntegrable_realProd_of_locallyIntegrable hgxLI)
    filter_upwards [this] with y hy a b
    convert hy a b using 2
  filter_upwards [hAC, hderiv, hII] with y hACy hderivy hIIy a b
  exact complex_ac_ftc_slice (hACy a b) hderivy (hIIy a b)

/-- **Fundamental theorem of calculus on vertical slices** (the symmetric core, from the weak
gradient). For a continuous a.e.-differentiable map whose `L¹_loc` `y`-partial witness `gy` is its
**weak** `I`-derivative (`hweak : HasWeakDirDeriv I gy g univ`), for almost every real part `x` the
vertical slice `t ↦ g ⟨x, t⟩` recovers itself from `gy` by the fundamental theorem of calculus:
`g ⟨x, b⟩ - g ⟨x, a⟩ = ∫ₐᵇ gy ⟨x, t⟩` for all `a, b`.

Fully reduced (Fubini + componentwise FTC-for-AC-functions) to the residual
`slice_isAbsolutelyContinuous_y_of_conditionNPlus`; soundness is identical to
`slice_fundamentalTheorem_x` with the roles of the two coordinates swapped. -/
theorem slice_fundamentalTheorem_y {g : ℂ → ℂ}
    (hgcont : Continuous g) (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    {gy : ℂ → ℂ} (hgy : ∀ᵐ w, gy w = (fderiv ℝ g w) Complex.I)
    (hgyLI : LocallyIntegrable gy)
    (hweak : HasWeakDirDeriv Complex.I gy g Set.univ) :
    ∀ᵐ x : ℝ, ∀ a b : ℝ, g ⟨x, b⟩ - g ⟨x, a⟩ = ∫ t in a..b, gy ⟨x, t⟩ := by
  -- The genuine residual: a.e. (vertical) slice is absolutely continuous.
  have hAC :=
    slice_isAbsolutelyContinuous_y_of_conditionNPlus hgcont hgyLI hweak
  -- a.e. slice has derivative `gy ⟨x, t⟩` (Fubini).
  have hderiv := ae_slice_hasDerivAt_y hgdiff hgy
  -- a.e. (vertical) slice integrability of `gy` (Fubini; coordinate-swapped).
  have hII : ∀ᵐ x : ℝ, ∀ a b : ℝ, IntervalIntegrable (fun t => gy ⟨x, t⟩) volume a b := by
    -- The vertical slice of `gy` is the horizontal slice of `(p₁,p₂) ↦ gy ⟨p₂, p₁⟩`.
    have hswap : LocallyIntegrable (fun p : ℝ × ℝ => gy ⟨p.2, p.1⟩) volume := by
      have hLI := locallyIntegrable_realProd_of_locallyIntegrable hgyLI
      have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
          (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) :=
        Measure.measurePreserving_swap
      rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
      have himg : IsCompact (Prod.swap '' K) := hK.image continuous_swap
      have hGon : IntegrableOn (fun p : ℝ × ℝ => gy ⟨p.1, p.2⟩) (Prod.swap '' K) volume :=
        hLI.integrableOn_isCompact himg
      have hmeas : MeasurableEmbedding (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
        (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding
      have key : IntegrableOn ((fun p : ℝ × ℝ => gy ⟨p.1, p.2⟩) ∘ Prod.swap)
          (Prod.swap ⁻¹' (Prod.swap '' K)) volume :=
        (hmp.integrableOn_comp_preimage hmeas).mpr hGon
      have hpre : Prod.swap ⁻¹' (Prod.swap '' K) = K :=
        Function.Injective.preimage_image Prod.swap_injective K
      rw [hpre] at key
      convert key using 1
    have := ae_slice_intervalIntegrable hswap
    filter_upwards [this] with x hx a b
    convert hx a b using 2
  filter_upwards [hAC, hderiv, hII] with x hACx hderivx hIIx a b
  exact complex_ac_ftc_slice (hACx a b) hderivx (hIIx a b)

/-! ## The target theorems -/

/-- **Weak gradient ⟹ ACL on horizontal lines** (`W^{1,1}_loc ⇒ ACL`, horizontal half). A
continuous a.e.-differentiable map `g : ℂ → ℂ` with `L¹_loc` `x`-partial witness `gx ⟨w⟩ = (Dg w) 1`
that is its **weak** `x`-derivative (`hweak : HasWeakDirDeriv 1 gx g univ`) is absolutely continuous
on almost every horizontal line, with `gx` the classical line derivative.

The genuine analytic content is `slice_fundamentalTheorem_x` (the slice FTC); the present theorem
performs the fully-proven reduction from that FTC identity to `ACLHorizontal`: the slice is
`const + ∫₀ˣ gx`, AC by the primitive lemma `absolutelyContinuousOnInterval_complexPrimitive`, and
with line-derivative `gx ⟨x, y⟩` a.e. by Lebesgue differentiation
(`LocallyIntegrable.ae_hasDerivAt_integral`).

The weak-gradient hypothesis is genuinely necessary (the area-preserving singular shear has all the
pointwise a.e. data — condition (N⁺), pointwise dilatation, `L²_loc` partials — yet is not ACL; see
the module docstring). It is supplied by the caller, where `g` is a quasiconformal inverse and the
weak gradient is genuine via `IsQCAnalytic.inverse_memW12loc`. The theorem name is retained for that
caller (`QC/LengthAreaInverse`). -/
theorem aclHorizontal_of_conditionNPlus {g : ℂ → ℂ}
    (hgcont : Continuous g) (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    {gx : ℂ → ℂ} (hgx : ∀ᵐ w, gx w = (fderiv ℝ g w) 1)
    (hgxLI : LocallyIntegrable gx)
    (hweak : HasWeakDirDeriv 1 gx g Set.univ) : ACLHorizontal g gx := by
  -- The slice FTC core.
  have hFTC := slice_fundamentalTheorem_x hgcont hgdiff hgx hgxLI hweak
  -- a.e.-slice interval integrability of `gx`.
  have hslice_II : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      IntervalIntegrable (fun t => gx ⟨t, y⟩) volume a b := by
    have := ae_slice_intervalIntegrable
      (locallyIntegrable_realProd_of_locallyIntegrable hgxLI)
    filter_upwards [this] with y hy a b
    -- rewrite `gx ⟨t, y⟩` as `gx (t, y)` through the realization.
    convert hy a b using 2
  unfold ACLHorizontal
  filter_upwards [hFTC, hslice_II] with y hFTCy hIIy
  -- Express the slice as `g ⟨0, y⟩ + ∫₀ˣ gx ⟨t, y⟩`.
  have hslice_eq : ∀ x : ℝ, g ⟨x, y⟩ = g ⟨0, y⟩ + ∫ t in (0 : ℝ)..x, gx ⟨t, y⟩ := by
    intro x
    have h := hFTCy 0 x
    linear_combination h
  refine ⟨?_, ?_⟩
  · -- Absolute continuity: `const + primitive`.
    intro a b
    have hprim : AbsolutelyContinuousOnInterval
        (fun x => ∫ t in (0 : ℝ)..x, gx ⟨t, y⟩) a b :=
      absolutelyContinuousOnInterval_complexPrimitive hIIy a b
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => g ⟨0, y⟩) a b := by
      rw [absolutelyContinuousOnInterval_iff]
      intro ε hε
      exact ⟨1, one_pos, fun E _ _ => by simpa using (by positivity : (0 : ℝ) < ε)⟩
    have heq : (fun x : ℝ => g ⟨x, y⟩)
        = (fun x : ℝ => g ⟨0, y⟩) + (fun x => ∫ t in (0 : ℝ)..x, gx ⟨t, y⟩) := by
      funext x; simp [hslice_eq x]
    rw [heq]; exact hconst.add hprim
  · -- Line derivative: Lebesgue differentiation of the primitive.
    have hcprim := ae_hasDerivAt_complexPrimitive (φ := fun t => gx ⟨t, y⟩) hIIy
    filter_upwards [hcprim] with x hx
    -- The slice = const + primitive, so it has the same derivative.
    have hcsum : HasDerivAt (fun t : ℝ => g ⟨0, y⟩ + ∫ s in (0 : ℝ)..t, gx ⟨s, y⟩)
        (gx ⟨x, y⟩) x := by
      have h := ((hasDerivAt_const x (g ⟨0, y⟩)).add hx)
      rw [zero_add] at h
      exact h
    refine hcsum.congr_of_eventuallyEq ?_
    filter_upwards with t
    exact hslice_eq t

/-- **Weak gradient ⟹ ACL on vertical lines** (`W^{1,1}_loc ⇒ ACL`, vertical half). The symmetric
statement: a continuous a.e.-differentiable map with `L¹_loc` `y`-partial witness
`gy ⟨w⟩ = (Dg w) I` that is its **weak** `I`-derivative (`hweak : HasWeakDirDeriv I gy g univ`) is
absolutely continuous on almost every vertical line, with `gy` the classical line derivative.
Identical reduction to `aclHorizontal_of_conditionNPlus`, off the vertical core
`slice_fundamentalTheorem_y`. -/
theorem aclVertical_of_conditionNPlus {g : ℂ → ℂ}
    (hgcont : Continuous g) (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    {gy : ℂ → ℂ} (hgy : ∀ᵐ w, gy w = (fderiv ℝ g w) Complex.I)
    (hgyLI : LocallyIntegrable gy)
    (hweak : HasWeakDirDeriv Complex.I gy g Set.univ) : ACLVertical g gy := by
  have hFTC := slice_fundamentalTheorem_y hgcont hgdiff hgy hgyLI hweak
  -- a.e.-slice interval integrability of `gy` (vertical slices: `t ↦ gy ⟨x, t⟩`).
  have hslice_II : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      IntervalIntegrable (fun t => gy ⟨x, t⟩) volume a b := by
    -- Swap coordinates: the vertical slice of `gy` is the horizontal slice of `(x,y) ↦ gy⟨y,x⟩`.
    have hswap : LocallyIntegrable (fun p : ℝ × ℝ => gy ⟨p.2, p.1⟩) volume := by
      have hLI := locallyIntegrable_realProd_of_locallyIntegrable hgyLI
      have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
          (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) :=
        Measure.measurePreserving_swap
      rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
      have himg : IsCompact (Prod.swap '' K) := hK.image continuous_swap
      have hGon : IntegrableOn (fun p : ℝ × ℝ => gy ⟨p.1, p.2⟩) (Prod.swap '' K) volume :=
        hLI.integrableOn_isCompact himg
      have hmeas : MeasurableEmbedding (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
        (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding
      have key : IntegrableOn ((fun p : ℝ × ℝ => gy ⟨p.1, p.2⟩) ∘ Prod.swap)
          (Prod.swap ⁻¹' (Prod.swap '' K)) volume :=
        (hmp.integrableOn_comp_preimage hmeas).mpr hGon
      have hpre : Prod.swap ⁻¹' (Prod.swap '' K) = K :=
        Function.Injective.preimage_image Prod.swap_injective K
      rw [hpre] at key
      convert key using 1
    have := ae_slice_intervalIntegrable hswap
    filter_upwards [this] with x hx a b
    convert hx a b using 2
  unfold ACLVertical
  filter_upwards [hFTC, hslice_II] with x hFTCx hIIx
  have hslice_eq : ∀ y : ℝ, g ⟨x, y⟩ = g ⟨x, 0⟩ + ∫ t in (0 : ℝ)..y, gy ⟨x, t⟩ := by
    intro y
    have h := hFTCx 0 y
    linear_combination h
  refine ⟨?_, ?_⟩
  · intro a b
    have hprim : AbsolutelyContinuousOnInterval
        (fun y => ∫ t in (0 : ℝ)..y, gy ⟨x, t⟩) a b :=
      absolutelyContinuousOnInterval_complexPrimitive hIIx a b
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => g ⟨x, 0⟩) a b := by
      rw [absolutelyContinuousOnInterval_iff]
      intro ε hε
      exact ⟨1, one_pos, fun E _ _ => by simpa using (by positivity : (0 : ℝ) < ε)⟩
    have heq : (fun y : ℝ => g ⟨x, y⟩)
        = (fun _ : ℝ => g ⟨x, 0⟩) + (fun y => ∫ t in (0 : ℝ)..y, gy ⟨x, t⟩) := by
      funext y; simp [hslice_eq y]
    rw [heq]; exact hconst.add hprim
  · -- Line derivative: Lebesgue differentiation of the primitive.
    have hcprim := ae_hasDerivAt_complexPrimitive (φ := fun t => gy ⟨x, t⟩) hIIx
    filter_upwards [hcprim] with y hy
    have hcsum : HasDerivAt (fun t : ℝ => g ⟨x, 0⟩ + ∫ s in (0 : ℝ)..t, gy ⟨x, s⟩)
        (gy ⟨x, y⟩) y := by
      have h := ((hasDerivAt_const y (g ⟨x, 0⟩)).add hy)
      rw [zero_add] at h
      exact h
    refine hcsum.congr_of_eventuallyEq ?_
    filter_upwards with t
    exact hslice_eq t

end RiemannDynamics

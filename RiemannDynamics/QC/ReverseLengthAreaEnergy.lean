/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.SensePreserving
import RiemannDynamics.QC.ReverseLengthArea
import RiemannDynamics.QC.InverseQC
import RiemannDynamics.QC.GeometricDifferentiable.Reciprocity
import RiemannDynamics.QC.InfinitesimalModulus
import RiemannDynamics.Analysis.Sobolev.AbsolutelyContinuousLines
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import RiemannDynamics.Analysis.Sobolev.DifferenceQuotient
import RiemannDynamics.Analysis.Sobolev.GehringLehto

/-!
# Forward reverse length–area: the Grötzsch-free slice residuals

This file decomposes the single bundled residual `IsQCGeometric.reverseLengthArea_data`
(`QC/GeometricToAnalytic.lean`) — the heart of the hard direction
`isQCAnalytic_of_isQCGeometric` — into named, individually-attackable forward GMT residuals
stated in terms of the **one-dimensional slice derivatives** (`forwardSliceDerivX/Y`), so the
whole development is **Grötzsch-free** (no quasiconformal-roundness, no symmetrization): it
proves the ACL `L²_loc` slice gradient *before* any a.e. differentiability of `f`, then recovers
a.e. differentiability downstream via the proved Gehring–Lehto theorem.

The classical Lehto–Virtanen / Väisälä reverse length–area theorem says a geometric
`K`-quasiconformal map `f` is absolutely continuous on almost every line with locally
square-integrable line partials. The genuinely two-dimensional length–area content is isolated
into the residuals below; the rest of the reduction (to `exists_acl_memLp_sliceGradient` and then
`ae_differentiableAt_gehringLehto`) is carried out in full from the repository's already-proven
infrastructure (`axisRect_imageModulus_le`, `rengel_area_lower_bound`).

## The residuals and their downstream consumers

* `IsQCGeometric.forward_lengthArea_energy` — the diff-free length–area energy brick (finite box
  integrals of the squared slice variation and the squared slice derivative). Feeds both
  `forward_ae_slice_bv` and `forward_sliceDeriv_memLp`.
* `IsQCGeometric.forward_ae_slice_bv` (**proved** from the brick) — almost every slice has finite
  variation on every interval (the length–area *inequality*).
* `IsQCGeometric.forward_ae_slice_noSingularPart` — the no-singular-part / Lusin-(N) bound (the
  length–area *equality*), upgrading bounded variation to absolute continuity.
* `IsQCGeometric.forward_sliceDeriv_memLp` (**proved** from the brick) — the slice derivatives are
  locally square-integrable.

These assemble into `IsQCGeometric.exists_acl_memLp_sliceGradient` (ACL slices with `L²_loc`
energy), from which `IsQCGeometric.ae_differentiableAt_gehringLehto` follows by the proved
Gehring–Lehto theorem `ae_differentiableAt_of_W12loc_homeomorph`.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace RiemannDynamics

/-! ## The diff-free slice-derivative witnesses and the three forward length–area residuals

The forward reverse-length-area theorem (Lehto–Virtanen, Väisälä §31) must be proved **without**
any a.e. differentiability of `f` (it *feeds* `ae_differentiableAt_gehringLehto`). So the ACL
gradient witnesses cannot be `fderiv ℝ f · v`; they are the **one-dimensional slice derivatives**,
which exist a.e. from *slice* bounded variation (a 1D fact,
`BoundedVariationOn.ae_differentiableAt`), not from 2D differentiability.

Everything below is therefore stated and assembled in terms of the slice derivatives. The three
genuinely two-dimensional length–area facts are isolated as the residuals `forward_ae_slice_bv`
(slice bounded variation, the length–area *inequality*), `forward_ae_slice_noSingularPart` (the
no-singular-part / Lusin-(N) bound, the length–area *equality*), and `forward_sliceDeriv_memLp`
(the slice-derivative `L²_loc` energy). The complete reduction of `exists_acl_memLp_sliceGradient`
to exactly these three is carried out in full. -/

/-- The **horizontal slice derivative** field: at `w = ⟨x, y⟩`, the classical derivative of the
horizontal slice `t ↦ f ⟨t, y⟩` evaluated at `x`. This is the diff-free `x`-partial witness — a
one-dimensional `deriv`, defined pointwise with no appeal to `fderiv ℝ f`. -/
noncomputable def forwardSliceDerivX (f : ℂ → ℂ) : ℂ → ℂ :=
  fun w => deriv (fun t : ℝ => f ⟨t, w.im⟩) w.re

/-- The **vertical slice derivative** field: at `w = ⟨x, y⟩`, the classical derivative of the
vertical slice `t ↦ f ⟨x, t⟩` evaluated at `y`. This is the diff-free `y`-partial witness. -/
noncomputable def forwardSliceDerivY (f : ℂ → ℂ) : ℂ → ℂ :=
  fun w => deriv (fun t : ℝ => f ⟨w.re, t⟩) w.im

/-- **Measurability of the horizontal slice-derivative field.** For continuous `f`, the field
`forwardSliceDerivX f : ℂ → ℂ` is measurable. The parametrized-derivative measurability
`measurable_deriv_with_param` gives joint measurability of `(y,x) ↦ deriv (t ↦ f⟨t,y⟩) x`; then
precompose with the measurable `w ↦ (w.im, w.re)`. -/
theorem measurable_forwardSliceDerivX {f : ℂ → ℂ} (hf : Continuous f) :
    Measurable (forwardSliceDerivX f) := by
  set F : ℝ → ℝ → ℂ := fun y x => f ⟨x, y⟩ with hF
  have hunc : Continuous (Function.uncurry F) := by
    have he : (Function.uncurry F) = fun p : ℝ × ℝ => f (⟨p.2, p.1⟩ : ℂ) := by
      funext p; rfl
    rw [he]
    refine hf.comp ?_
    have h2 : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [h2]
    exact (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  have hjoint : Measurable (fun p : ℝ × ℝ => deriv (F p.1) p.2) :=
    measurable_deriv_with_param hunc
  have hcomp : forwardSliceDerivX f
      = (fun p : ℝ × ℝ => deriv (F p.1) p.2) ∘ (fun w : ℂ => (w.im, w.re)) := by
    funext w; simp only [forwardSliceDerivX, Function.comp_apply, hF]
  rw [hcomp]
  exact hjoint.comp (Complex.measurable_im.prodMk Complex.measurable_re)

/-- **Measurability of the vertical slice-derivative field.** Mirror of
`measurable_forwardSliceDerivX`. -/
theorem measurable_forwardSliceDerivY {f : ℂ → ℂ} (hf : Continuous f) :
    Measurable (forwardSliceDerivY f) := by
  set F : ℝ → ℝ → ℂ := fun x y => f ⟨x, y⟩ with hF
  have hunc : Continuous (Function.uncurry F) := by
    have he : (Function.uncurry F) = fun p : ℝ × ℝ => f (⟨p.1, p.2⟩ : ℂ) := by
      funext p; rfl
    rw [he]
    refine hf.comp ?_
    have h2 : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [h2]
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hjoint : Measurable (fun p : ℝ × ℝ => deriv (F p.1) p.2) :=
    measurable_deriv_with_param hunc
  have hcomp : forwardSliceDerivY f
      = (fun p : ℝ × ℝ => deriv (F p.1) p.2) ∘ (fun w : ℂ => (w.re, w.im)) := by
    funext w; simp only [forwardSliceDerivY, Function.comp_apply, hF]
  rw [hcomp]
  exact hjoint.comp (Complex.measurable_re.prodMk Complex.measurable_im)

/-! ### The single diff-free length–area energy residual

The bounded-variation residual (`forward_ae_slice_bv`) and the slice-derivative `L²_loc` energy
residual (`forward_sliceDeriv_memLp`) are both consequences of one classical, **differentiability-
free** length–area inequality: for every axis box `R = (a,b)×(s,t)`, the slice variation
`ℓ_f(y) = eVariationOn (x ↦ f⟨x,y⟩) [a,b]` and the slice-derivative energy
`∫_{x∈[a,b]} ‖∂ₓf⟨x,y⟩‖²` integrate over `y ∈ [s,t]` to finite quantities. This is the
forward image-family length–area energy bound: combine the source segment-family modulus lower
bound (`segmentFamily_modulus_ge`/`lengthArea_modulus_lower_bound`), the geometric modulus upper
bound `M(f(R)) ≤ K·(t−s)/(b−a)` (`axisRect_imageModulus_le`), the finiteness of the image area
`area(f(R)) < ∞` (`f` is a homeomorphism, `f''R` compact), and a Cauchy–Schwarz / Fubini estimate,
via the reciprocal-slice-length admissible density on the image plane. It needs **no** 2D
differentiability of `f` (the witnesses are the *one-dimensional* slice derivatives), **no**
Grötzsch symmetrization, and **no** reciprocity — it is the *easy* (mod-upper ⟹ energy-upper)
length–area direction.

Both finiteness facts are bundled here as a single residual because they share the same proof (the
image-family length–area transfer) and the same load-bearing hypothesis (`IsQCGeometric f K`); each
of `forward_ae_slice_bv` and `forward_sliceDeriv_memLp` is then fully derived from it below by
real connective steps (a.e.-finiteness from the `eVariation²` box bound; Fubini/`MemLp` from the
derivative-energy box bound). -/

/-- **Forward length–area energy bound (diff-free, the easy direction; isolated residual).** For a
geometric `K`-quasiconformal map `f` and every axis box `(a,b)×(s,t)`, both the squared slice
variation and the slice-derivative energy integrate to a finite quantity over the box. The two
finiteness facts are stated per axis (horizontal slices indexed by height `y ∈ [s,t]`, vertical
slices indexed by abscissa `x ∈ [a,b]`).

This is the genuinely two-dimensional length–area *inequality* (Väisälä §31.1), the single brick
from which the bounded-variation residual `forward_ae_slice_bv` and the `L²_loc` energy residual
`forward_sliceDeriv_memLp` are both **fully derived below** (a.e.-finite variation from the
`eVariation²` box bound via `ae_eVariationOn_ne_top_of_box`; `MemLp` from the derivative-energy box
bound via `setLIntegral_axisRect_eq_iterated_*` + `measurable_forwardSliceDeriv*`). It is
**differentiability-free** by construction: the slice variations and slice derivatives are intrinsic
one-dimensional quantities of the continuous map `f`.

## Closeability (honest assessment): the forward image-family length–area lower bound.

The classical proof (Lehto–Virtanen; Väisälä §31.1) transfers the geometric modulus upper bound
`M(f(R)) ≤ K·(t−s)/(b−a)` (`axisRect_imageModulus_le`, proven) to the slice energy by building, on
the **image** plane, the *reciprocal-slice-length* admissible density `ρ(w) = 1/ℓ_f(y)` on the image
of the height-`y` slice (where `ℓ_f(y)` is the image-slice length): every image curve `f∘γ_y` then
has `∫_{f∘γ_y} ρ ds = 1`, so `ρ` is admissible and `M(f(R)) ≥ ∫ρ² dArea`, and a Cauchy–Schwarz /
Fubini coupling on the image plane converts `∫ρ²` into the slice-energy lower bound, giving
`∫_y ℓ_f(y)² dy ≤ K·area(f(R)) < ∞` (the image area is finite since `f''R` is compact). This is the
*easy* (mod-upper ⟹ energy-upper) direction — **no** Grötzsch symmetrization, **no** reciprocity.

It is **kept as a `sorry` residual**: the repository has the source-side length–area lower bound
(`lengthArea_modulus_lower_bound`, `segmentFamily_modulus_ge`) and the image-modulus upper bound
(`axisRect_imageModulus_le`), but **not** the image-plane reciprocal-density coupling, which needs a
co-area / change-of-variables *equality* on the (non-Lipschitz, BV-sliced) image — Mathlib-absent in
this regime. This is the genuine forward length–area energy bottleneck (the Gehring–Lehto brick).
It may **not** be discharged via the proven `ae_slice_boundedVariation`/`memLpLocOn_partials`, which
route through `ae_differentiableAt'`/`qc_image_ball_diam_sq_le_volume`: those feed
`ae_differentiableAt_gehringLehto` *through this very leaf*, so using them is a cycle and is on the
forbidden list. The diff-free image-family lower bound is the unique honest route. -/
theorem IsQCGeometric.forward_lengthArea_energy {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ a b s t : ℝ,
        (∫⁻ y in Set.Icc s t,
            (eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)) ^ 2) ≠ ⊤ ∧
        (∫⁻ y in Set.Icc s t,
            (eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)) ^ 2) ≠ ⊤ ∧
        (∫⁻ y in Set.Icc s t, ∫⁻ x in Set.Icc a b,
            (‖forwardSliceDerivX f ⟨x, y⟩‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤) ∧
    (∀ a b s t : ℝ,
        (∫⁻ x in Set.Icc a b,
            (eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc s t)) ^ 2) ≠ ⊤ ∧
        (∫⁻ x in Set.Icc a b,
            (eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc s t)) ^ 2) ≠ ⊤ ∧
        (∫⁻ x in Set.Icc a b, ∫⁻ y in Set.Icc s t,
            (‖forwardSliceDerivY f ⟨x, y⟩‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤) := by
  sorry

/-- **From a box `eVariation²`-integral bound to a.e.-finite slice variation (general engine).**
If `g : ℝ → ℝ → ℝ` is a jointly continuous slice family whose squared slice variation has a finite
box integral over every rectangle (`∫⁻_{y∈[s,t]} (eVariationOn (g y) [a,b])² ≠ ⊤`), then for almost
every `y` the slice `g y` has finite variation on every compact interval. This is the
measure-theoretic core of the bounded-variation residual: a finite box integral of a measurable
nonnegative integrand forces the integrand to be a.e. finite, and an exhaustion by integer boxes
upgrades this to "a.e. `y`, on every interval". -/
private theorem ae_eVariationOn_ne_top_of_box {g : ℝ → ℝ → ℝ}
    (hjoint : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hbox : ∀ a b s t : ℝ,
        (∫⁻ y in Set.Icc s t, (eVariationOn (g y) (Set.Icc a b)) ^ 2) ≠ ⊤) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ, eVariationOn (g y) (Set.Icc a b) ≠ ⊤ := by
  -- `y ↦ eVariationOn (g y) [a,b]` is measurable for every fixed box.
  have hmeas : ∀ a b : ℝ, Measurable (fun y => eVariationOn (g y) (Set.Icc a b)) :=
    fun a b => RiemannDynamics.MAF.measurable_eVariationOn_slice hjoint a b
  -- For each integer `n`, a.e. `y` in `[-n,n]` has finite variation on `[-n,n]`.
  have hper : ∀ n : ℕ, ∀ᵐ y : ℝ,
      y ∈ Set.Icc (-(n : ℝ)) n → eVariationOn (g y) (Set.Icc (-(n : ℝ)) n) ≠ ⊤ := by
    intro n
    -- The squared variation is a.e.-`y`-finite on `[-n,n]` (finite box integral).
    have hfin : ∫⁻ y in Set.Icc (-(n : ℝ)) n,
        (eVariationOn (g y) (Set.Icc (-(n : ℝ)) n)) ^ 2 ≠ ⊤ :=
      hbox (-(n : ℝ)) n (-(n : ℝ)) n
    have hae := MeasureTheory.ae_lt_top'
      ((hmeas (-(n : ℝ)) n).pow_const 2).aemeasurable hfin
    rw [ae_restrict_iff' measurableSet_Icc] at hae
    filter_upwards [hae] with y hy hymem
    have hlt := hy hymem
    intro htop
    rw [htop] at hlt
    simp at hlt
  -- Combine over all `n`, then use interval monotonicity.
  rw [← ae_all_iff] at hper
  filter_upwards [hper] with y hy a b
  -- Pick `n` with `[a,b] ⊆ [-n,n]` **and** `y ∈ [-n,n]`, then use `eVariationOn.mono`.
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max |a| |b|) |y|)
  have ha : |a| ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hb : |b| ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hyn : |y| ≤ n := le_trans (le_max_right _ _) hn
  rw [abs_le] at ha hb hyn
  have hsub : Set.Icc a b ⊆ Set.Icc (-(n : ℝ)) n := by
    intro z hz; rw [Set.mem_Icc] at hz ⊢; exact ⟨le_trans ha.1 hz.1, le_trans hz.2 hb.2⟩
  have hymem : y ∈ Set.Icc (-(n : ℝ)) n := by rw [Set.mem_Icc]; exact hyn
  exact ne_top_of_le_ne_top (hy n hymem) (eVariationOn.mono (g y) hsub)

/-- **Subadditivity of the complex slice variation.** The total variation of a `ℂ`-valued function
on an interval is at most the sum of the variations of its real and imaginary parts (the projection
inequality `‖z‖ ≤ |z.re| + |z.im|` integrated over partitions). -/
private theorem eVariationOn_complex_le_re_add_im (h : ℝ → ℂ) (a b : ℝ) :
    eVariationOn h (Set.Icc a b)
      ≤ eVariationOn (fun t => (h t).re) (Set.Icc a b)
        + eVariationOn (fun t => (h t).im) (Set.Icc a b) := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, humono, husmem⟩
  simp only
  calc ∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (h (u (i + 1))).re (h (u i)).re + edist (h (u (i + 1))).im (h (u i)).im) := by
        apply Finset.sum_le_sum
        intro i _
        rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        apply ENNReal.ofReal_le_ofReal
        rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
        calc ‖h (u (i + 1)) - h (u i)‖
            ≤ |(h (u (i + 1)) - h (u i)).re| + |(h (u (i + 1)) - h (u i)).im| :=
              norm_le_abs_re_add_abs_im _
          _ = |(h (u (i + 1))).re - (h (u i)).re| + |(h (u (i + 1))).im - (h (u i)).im| := by
              rw [Complex.sub_re, Complex.sub_im]
    _ = (∑ i ∈ Finset.range n, edist (h (u (i + 1))).re (h (u i)).re)
        + ∑ i ∈ Finset.range n, edist (h (u (i + 1))).im (h (u i)).im := by
        rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn (fun t => (h t).re) (Set.Icc a b)
        + eVariationOn (fun t => (h t).im) (Set.Icc a b) :=
        add_le_add (eVariationOn.sum_le humono husmem) (eVariationOn.sum_le humono husmem)

/-- The complex slice variation is finite when both real-component variations are finite. -/
private theorem eVariationOn_ne_top_of_re_im_ne_top {h : ℝ → ℂ} {a b : ℝ}
    (hre : eVariationOn (fun t => (h t).re) (Set.Icc a b) ≠ ⊤)
    (him : eVariationOn (fun t => (h t).im) (Set.Icc a b) ≠ ⊤) :
    eVariationOn h (Set.Icc a b) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (eVariationOn_complex_le_re_add_im h a b)
  exact ENNReal.add_ne_top.mpr ⟨hre, him⟩

/-- **Forward a.e. slice bounded variation (diff-free, length–area inequality).** For a geometric
`K`-quasiconformal map `f`, almost every horizontal slice `x ↦ f⟨x, y⟩` and almost every vertical
slice `y ↦ f⟨x, y⟩` has finite total variation on every compact interval.

This is the bounded-variation consequence of the reverse length–area *inequality*: the modulus
bound `M(f(R)) ≤ K·M(R)` (`axisRect_imageModulus_le`), via the rectangle length–area estimate
`∫ ℓ_f(y)² dy ≤ K·area(f(R))` with `area(f(R)) < ∞`, forces the slice variation `ℓ_f(y)` to be
finite almost everywhere.

Proved here in full from the diff-free length–area residual `forward_lengthArea_energy` (whose
component `eVariation²` box bounds force a.e.-finite component variation by
`ae_eVariationOn_ne_top_of_box`; the complex slice variation is then finite by the subadditivity
`Var(f) ≤ Var(Re f) + Var(Im f)`). It is the **diff-free** analogue of
`IsQCGeometric.ae_slice_boundedVariation`, which routes through `ae_differentiableAt'` (the
forbidden 2D differentiability). -/
theorem IsQCGeometric.forward_ae_slice_bv {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc a b) ≠ ⊤) ∧
    (∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun y : ℝ => f ⟨x, y⟩) (Set.Icc a b) ≠ ⊤) := by
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  obtain ⟨hHoriz, hVert⟩ := hf.forward_lengthArea_energy
  -- Joint continuity of the horizontal real/imaginary slice families.
  have hjoint_hx_re : Continuous (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).re) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).re)
        = Complex.reCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.reCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  have hjoint_hx_im : Continuous (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).im) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.2, p.1⟩).im)
        = Complex.imCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.imCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  -- Joint continuity of the vertical real/imaginary slice families.
  have hjoint_vy_re : Continuous (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).re) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).re)
        = Complex.reCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.reCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hjoint_vy_im : Continuous (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).im) := by
    have : (fun p : ℝ × ℝ => (f ⟨p.1, p.2⟩).im)
        = Complex.imCLM ∘ f ∘ (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := rfl
    rw [this]
    refine Complex.imCLM.continuous.comp (hcont.comp ?_)
    have he : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  -- The complex slice variation is finite when both component variations are.
  refine ⟨?_, ?_⟩
  · -- Horizontal: combine the re/im a.e.-finite component variations.
    have hre := ae_eVariationOn_ne_top_of_box hjoint_hx_re (fun a b s t => (hHoriz a b s t).1)
    have him := ae_eVariationOn_ne_top_of_box hjoint_hx_im (fun a b s t => (hHoriz a b s t).2.1)
    filter_upwards [hre, him] with y hyre hyim a b
    exact eVariationOn_ne_top_of_re_im_ne_top (hyre a b) (hyim a b)
  · -- Vertical: slice family `g x y = (f⟨x,y⟩).re`, indexed by abscissa `x`.
    have hre := ae_eVariationOn_ne_top_of_box hjoint_vy_re
      (fun A B S T => (hVert S T A B).1)
    have him := ae_eVariationOn_ne_top_of_box hjoint_vy_im
      (fun A B S T => (hVert S T A B).2.1)
    filter_upwards [hre, him] with x hxre hxim a b
    exact eVariationOn_ne_top_of_re_im_ne_top (hxre a b) (hxim a b)

/-- **Forward no-singular-part of the slices (diff-free, length–area equality; isolated residual).**
For a geometric `K`-quasiconformal map `f`, almost every horizontal slice of each real component
has its total variation dominated by the integral of its (a.e.-existing) *slice* derivative — the
Banach–Zaretsky "no singular part" condition `eVariationOn ≤ ∫⁻ ‖deriv‖₊` — and symmetrically for
vertical slices.

This is the genuinely two-dimensional content (the length–area *equality*, Väisälä §31.2), ruling
out a singular part in the slice and upgrading bounded variation (`forward_ae_slice_bv`) to absolute
continuity. It is FALSE for the area-preserving singular shear `g⟨x,y⟩ = x + i(y + s·x)` (whose
slice `x ↦ y + s·x` is singular but has `deriv = 1` a.e.), so the hypothesis `IsQCGeometric f K` is
load-bearing.

The derivatives here are the **one-dimensional slice** derivatives `deriv (fun s => (f⟨s, y⟩).re) x`
(not `(fderiv ℝ f · 1).re`), matching the diff-free witnesses `forwardSliceDerivX`/
`forwardSliceDerivY`. It supplies the `hmaf` input to `ae_slice_AC_of_maf`.

## Closeability (honest assessment): the irreducible diff-free no-singular-part node.

This is the one genuinely length–area-*equality* fact of the forward direction and it is **kept as
a `sorry` residual** because every available engine for it is forbidden on this critical path:

* The **multiplicity area formula** `multiplicityAreaFormula_noSingularPart` (the repo's only
  proven no-singular-part engine, `QC/InverseQC.lean`) requires the a.e. 2D-differentiability
  hypothesis `hGdiff : ∀ᵐ w, DifferentiableAt ℝ G w` — but this leaf *feeds*
  `ae_differentiableAt_gehringLehto`, so 2D differentiability of `f` is precisely what is **not**
  yet available here (using it is a cycle, and is on the explicit forbidden list).
* The **co-area** engine `eilenberg_coarea_grad_le` (`Coarea/Assembly.lean`) needs `LipschitzWith`,
  which the QC map is not.
* The **Banach–Zaretsky** converse (`monotone_ftc_of_luzinN`, `absolutelyContinuousOnInterval_of_*`)
  would close it from a **1D Lusin-(N)** of the monotone Jordan pieces of each slice; but obtaining
  that 1D piece-(N) from the proven **2D** forward Lusin condition `IsQCGeometric.lusinN`
  (`QCLusinN.lean`) is exactly the *forward fibered Lusin-(N)* of `Φ⟨x,y⟩ = (f⟨x,y⟩).re + i·y`,
  which collapses `f`'s image transversally and is **not** derivable from `f''(null)` being null
  without the area-equality (a Fubini/co-area coupling), i.e. without the very thing being proved.

So this residual is the classical Lehto–Virtanen / Marcus–Mizel area-equality core; it is
**Mathlib/repo-absent in the diff-free regime** and is the honest minimal endpoint. (The
*inequality* half — bounded variation and `L²_loc` energy — is fully discharged diff-free from the
single `forward_lengthArea_energy` brick in `forward_ae_slice_bv`/`forward_sliceDeriv_memLp` above.)
-/
theorem IsQCGeometric.forward_ae_slice_noSingularPart {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    (∀ᵐ y : ℝ, ∀ a b : ℝ,
        eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).re) x‖₊ ∧
        eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).im) x‖₊) ∧
    (∀ᵐ x : ℝ, ∀ a b : ℝ,
        eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).re) y‖₊ ∧
        eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).im) y‖₊) := by
  sorry

/-- **Box Tonelli for an `ℝ≥0∞`-valued integrand (`y`-outer form).** For a measurable
`H : ℂ → ℝ≥0∞`, the integral over the axis rectangle `(a,b)×(s,t)` is the iterated integral with the
height `y` outer and the abscissa `x` inner. -/
private theorem setLIntegral_axisRect_eq_iterated_yx {H : ℂ → ℝ≥0∞} (hH : Measurable H)
    (a b s t : ℝ) :
    ∫⁻ w in axisRect a b s t, H w
      = ∫⁻ y in Set.Icc s t, ∫⁻ x in Set.Icc a b, H ⟨x, y⟩ := by
  classical
  -- `axisRect = equiv ⁻¹' (Icc a b ×ˢ Icc s t)`.
  have hpre : axisRect a b s t
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    simp only [axisRect, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
      Complex.measurableEquivRealProd_apply]
  have hmp : MeasurePreserving Complex.measurableEquivRealProd
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
    Complex.volume_preserving_equiv_real_prod
  -- The product-side integrand `H' p = H ⟨p.1, p.2⟩`, measurable.
  set H' : ℝ × ℝ → ℝ≥0∞ := fun p => H ⟨p.1, p.2⟩ with hH'
  have hH'meas : Measurable H' := by
    have hmk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := by
      have : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
          = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      rw [this]
      exact (Complex.measurable_ofReal.comp measurable_fst).add
        ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const)
    exact hH.comp hmk
  -- Rewrite `H w = H' (equiv w)` on the preimage and transfer via the measure-preserving equiv.
  rw [hpre]
  have hcongr : ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t), H w
      = ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t),
          H' (Complex.measurableEquivRealProd w) := by
    refine setLIntegral_congr_fun
      ((Complex.measurableEquivRealProd.measurable)
        (measurableSet_Icc.prod measurableSet_Icc)) ?_
    intro w _
    simp only [hH', Complex.measurableEquivRealProd_apply]
  rw [hcongr, hmp.setLIntegral_comp_preimage (measurableSet_Icc.prod measurableSet_Icc) hH'meas]
  -- Tonelli over the product set, then `y` outer.
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_symm' H' hH'meas]

/-- **Box Tonelli for an `ℝ≥0∞`-valued integrand (`x`-outer form).** Companion to
`setLIntegral_axisRect_eq_iterated_yx`, with the abscissa `x` outer and the height `y` inner. -/
private theorem setLIntegral_axisRect_eq_iterated_xy {H : ℂ → ℝ≥0∞} (hH : Measurable H)
    (a b s t : ℝ) :
    ∫⁻ w in axisRect a b s t, H w
      = ∫⁻ x in Set.Icc a b, ∫⁻ y in Set.Icc s t, H ⟨x, y⟩ := by
  classical
  have hpre : axisRect a b s t
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    simp only [axisRect, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
      Complex.measurableEquivRealProd_apply]
  have hmp : MeasurePreserving Complex.measurableEquivRealProd
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
    Complex.volume_preserving_equiv_real_prod
  set H' : ℝ × ℝ → ℝ≥0∞ := fun p => H ⟨p.1, p.2⟩ with hH'
  have hH'meas : Measurable H' := by
    have hmk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := by
      have : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
          = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      rw [this]
      exact (Complex.measurable_ofReal.comp measurable_fst).add
        ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const)
    exact hH.comp hmk
  rw [hpre]
  have hcongr : ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t), H w
      = ∫⁻ w in Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t),
          H' (Complex.measurableEquivRealProd w) := by
    refine setLIntegral_congr_fun
      ((Complex.measurableEquivRealProd.measurable)
        (measurableSet_Icc.prod measurableSet_Icc)) ?_
    intro w _
    simp only [hH', Complex.measurableEquivRealProd_apply]
  rw [hcongr, hmp.setLIntegral_comp_preimage (measurableSet_Icc.prod measurableSet_Icc) hH'meas]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod H' hH'meas.aemeasurable]

/-- **Forward `L²_loc` slice-derivative energy (diff-free, the easy length–area direction).** For a
geometric `K`-quasiconformal map `f`, the two **slice-derivative** fields `forwardSliceDerivX f`
and `forwardSliceDerivY f` are locally square-integrable.

Proved here in full from the diff-free length–area residual `forward_lengthArea_energy`: on a
compact `Kc ⊆ [-n,n]²`, the energy `∫_{Kc} ‖forwardSliceDerivX f‖²` is bounded by the box integral
`∫_{[-n,n]²} ‖forwardSliceDerivX f‖²`, which by `setLIntegral_axisRect_eq_iterated_yx` (Tonelli) is
exactly the residual's finite derivative-energy box bound; `MemLp` follows from the slice-derivative
field's measurability (`measurable_forwardSliceDerivX`) and this finite energy.

This is the **diff-free** analogue of `IsQCGeometric.memLpLocOn_partials`: that lemma bounds the 2D
operator norm `‖fderiv ℝ f‖` via quasiconformal roundness (`qc_image_ball_diam_sq_le_volume`, the
forbidden route); here the energy is carried by the *slice* derivatives directly through the
length–area inequality, with no 2D differentiability. -/
theorem IsQCGeometric.forward_sliceDeriv_memLp {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    MemLpLocOn (forwardSliceDerivX f) 2 Set.univ ∧
    MemLpLocOn (forwardSliceDerivY f) 2 Set.univ := by
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  obtain ⟨hHoriz, hVert⟩ := hf.forward_lengthArea_energy
  -- The two slice-derivative fields are measurable.
  have hmX : Measurable (forwardSliceDerivX f) := measurable_forwardSliceDerivX hcont
  have hmY : Measurable (forwardSliceDerivY f) := measurable_forwardSliceDerivY hcont
  -- **Generic engine.** A measurable field `H : ℂ → ℂ` whose squared-norm integral is finite over
  -- every axis box is `L²_loc`.
  have engine : ∀ (H : ℂ → ℂ), Measurable H →
      (∀ a b s t : ℝ, (∫⁻ w in axisRect a b s t, (‖H w‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) ≠ ⊤) →
      MemLpLocOn H 2 Set.univ := by
    intro H hHmeas hHbox Kc _ hKcpt
    -- A box `[-n,n]²` containing `Kc`.
    obtain ⟨n, hn⟩ := hKcpt.isBounded.subset_closedBall_lt 0 0
    have hsub : Kc ⊆ axisRect (-n) n (-n) n := by
      intro w hw
      have hwn : ‖w‖ ≤ n := by
        have := hn.2 hw; rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hre : |w.re| ≤ n := le_trans (Complex.abs_re_le_norm w) hwn
      have him : |w.im| ≤ n := le_trans (Complex.abs_im_le_norm w) hwn
      rw [abs_le] at hre him
      exact ⟨⟨hre.1, hre.2⟩, ⟨him.1, him.2⟩⟩
    -- `MemLp` from measurability + finite squared-`L²` integral over `Kc`.
    refine ⟨hHmeas.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
      show ((2 : ℝ≥0∞)).toReal = 2 by norm_num]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (hHbox (-n) n (-n) n))
    exact lintegral_mono_set hsub
  -- The two box bounds, obtained from the residual's iterated forms via the Tonelli helper.
  -- Pointwise bridge `(‖z‖ₑ)^(2:ℝ) = (‖z‖₊ : ℝ≥0∞)^2`, applied under the integral binders.
  have hsq_pt : ∀ z : ℂ, (‖z‖ₑ : ℝ≥0∞) ^ (2 : ℝ) = (‖z‖₊ : ℝ≥0∞) ^ 2 := by
    intro z; rw [← enorm_eq_nnnorm, ← ENNReal.rpow_natCast, Nat.cast_ofNat]
  refine ⟨engine (forwardSliceDerivX f) hmX (fun a b s t => ?_),
    engine (forwardSliceDerivY f) hmY (fun a b s t => ?_)⟩
  · -- Horizontal: `y`-outer Tonelli matches the residual directly.
    rw [setLIntegral_axisRect_eq_iterated_yx (hmX.enorm.pow_const 2) a b s t]
    simp_rw [hsq_pt]
    exact (hHoriz a b s t).2.2
  · -- Vertical: `x`-outer Tonelli (swap the iterated order) matches the residual.
    rw [setLIntegral_axisRect_eq_iterated_xy (hmY.enorm.pow_const 2) a b s t]
    simp_rw [hsq_pt]
    exact (hVert a b s t).2.2

/-- **Forward reverse length–area: ACL slices with `L²_loc` energy (Grötzsch-free).**

A geometric `K`-quasiconformal map `f` is absolutely continuous on almost every horizontal and
vertical line, with `x`- and `y`-partials (the slice classical derivatives `gx`, `gy`) that are
locally square-integrable.

This is the **forward** reverse-length-area / length–area energy inequality, the *easy*
length–area direction:

* The **slice absolute continuity** (`ACLHorizontal`/`ACLVertical`) is already proven Grötzsch-free
  in `IsQCGeometric.ae_slice_absolutelyContinuous` (no quasiconformal-roundness, no symmetrization).
* The **`L²` slice-derivative bound** is the classical forward energy inequality
  `∫ |∂_x f|² ≤ K · area(f)`: combine the length–area lower bound for the horizontal-segment
  family on an axis rectangle with the geometric upper bound `M(f(R)) ≤ K·M(R)` and a
  Cauchy–Schwarz / Fubini estimate. This direction needs **no** Grötzsch symmetrization and **no**
  reciprocity (those are only required for the *reverse* modulus inversion `mod-lower ⟹ diam-upper`,
  the irreducible Teichmüller node).

This conclusion is *identical* to `IsQCGeometric.exists_acl_weakGradient`, by design: it is the
single Grötzsch-free residual that **replaces** the research sorry `grotzsch_symmetrization_kernel`
on the critical path of `reverseLengthArea_data`. The a.e. differentiability and pointwise
dilatation data are then recovered downstream via the proven Gehring–Lehto theorem
(`ae_differentiableAt_of_W12loc_homeomorph`) rather than via quasiconformal roundness. -/
theorem IsQCGeometric.exists_acl_memLp_sliceGradient {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∃ gx gy : ℂ → ℂ, ACLHorizontal f gx ∧ ACLVertical f gy ∧
      MemLpLocOn gx (2 : ℝ≥0∞) Set.univ ∧ MemLpLocOn gy (2 : ℝ≥0∞) Set.univ := by
  classical
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  -- The three diff-free length–area residuals.
  obtain ⟨hBVx, hBVy⟩ := hf.forward_ae_slice_bv
  obtain ⟨hNSx, hNSy⟩ := hf.forward_ae_slice_noSingularPart
  obtain ⟨hL2x, hL2y⟩ := hf.forward_sliceDeriv_memLp
  -- The horizontal/vertical embeddings are continuous in the moving coordinate.
  have hembed_x : ∀ y : ℝ, Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro y
    have he : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [he]; exact Complex.continuous_ofReal.add continuous_const
  have hembed_y : ∀ x : ℝ, Continuous (fun y : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro x
    have he : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [he]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  -- **Generic per-component AC engine for the HORIZONTAL slices.** Given a 1-Lipschitz real
  -- projection `P` whose component-slice has its variation dominated by the integral of its
  -- (1D) derivative a.e., conclude almost every horizontal `P`-slice is AC. This is the diff-free
  -- mirror of the engine inside `ae_slice_absolutelyContinuous`, fed by the residuals above.
  have hcompAC_x : ∀ (P : ℂ →L[ℝ] ℝ),
      (∀ᵐ y : ℝ, ∀ a b : ℝ,
          eVariationOn (fun x : ℝ => P (f ⟨x, y⟩)) (Set.Icc a b)
            ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => P (f ⟨s, y⟩)) x‖₊) →
      ∀ᵐ y : ℝ, ∀ a c : ℝ,
        AbsolutelyContinuousOnInterval (fun x : ℝ => P (f ⟨x, y⟩)) a c := by
    intro P hNS
    set slice : ℝ → ℝ → ℝ := fun y x => P (f ⟨x, y⟩) with hslice
    have hsl_cont : ∀ y : ℝ, Continuous (slice y) := by
      intro y; exact P.continuous.comp (hcont.comp (hembed_x y))
    -- a.e. `y`, the real `P`-slice has finite variation on every interval (1-Lipschitz projection
    -- of the BV complex slice), so it is `LocallyBoundedVariationOn univ`.
    have hsl_LBV : ∀ᵐ y : ℝ, LocallyBoundedVariationOn (slice y) Set.univ := by
      filter_upwards [hBVx] with y hy
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]
      exact (P.lipschitz).comp_boundedVariationOn (g := fun x : ℝ => f ⟨x, y⟩)
        (s := Set.Icc a b) (hy a b)
    have hderiv : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, HasDerivAt (slice y) (deriv (slice y) x) x := by
      filter_upwards [hsl_LBV] with y hy
      filter_upwards [hy.ae_differentiableAt] with x hx
      exact hx.hasDerivAt
    have hint : ∀ᵐ y : ℝ, ∀ u v : ℝ,
        IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume u v := by
      filter_upwards [hderiv, hsl_LBV] with y hyderiv hyLBV u v
      have hcore : ∀ p q : ℝ, p ≤ q →
          IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume p q := by
        intro p q hpq
        have hbvfin : eVariationOn (slice y) (Set.Icc p q) ≠ ⊤ := by
          have := hyLBV p q (Set.mem_univ p) (Set.mem_univ q)
          rwa [BoundedVariationOn, Set.univ_inter] at this
        have hlint_le : ∫⁻ x in Set.Icc p q, ‖deriv (slice y) x‖₊
            ≤ eVariationOn (slice y) (Set.Icc p q) :=
          lintegral_nnnorm_deriv_le_eVariationOn hpq hyderiv
        have hfin : ∫⁻ x in Set.Icc p q, (‖deriv (slice y) x‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top hbvfin hlint_le
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
        refine ⟨((measurable_deriv (slice y)).norm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ x in Set.Ioc p q, ‖‖deriv (slice y) x‖‖ₑ
            ≤ ∫⁻ x in Set.Icc p q, (‖deriv (slice y) x‖₊ : ℝ≥0∞) := by
          refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans_eq ?_
          apply lintegral_congr; intro x; rw [enorm_norm, enorm_eq_nnnorm]
        exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
      rcases le_total u v with huv | hvu
      · exact hcore u v huv
      · exact (hcore v u hvu).symm
    have hmaf : ∀ᵐ y : ℝ, ∀ a c : ℝ,
        eVariationOn (slice y) (Set.Icc a c)
          ≤ ∫⁻ x in Set.Icc a c, ‖deriv (slice y) x‖₊ := hNS
    exact ae_slice_AC_of_maf hsl_cont hderiv hint hmaf
  -- **Generic per-component AC engine for the VERTICAL slices** (mirror).
  have hcompAC_y : ∀ (P : ℂ →L[ℝ] ℝ),
      (∀ᵐ x : ℝ, ∀ a b : ℝ,
          eVariationOn (fun y : ℝ => P (f ⟨x, y⟩)) (Set.Icc a b)
            ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => P (f ⟨x, s⟩)) y‖₊) →
      ∀ᵐ x : ℝ, ∀ a c : ℝ,
        AbsolutelyContinuousOnInterval (fun y : ℝ => P (f ⟨x, y⟩)) a c := by
    intro P hNS
    set slice : ℝ → ℝ → ℝ := fun x y => P (f ⟨x, y⟩) with hslice
    have hsl_cont : ∀ x : ℝ, Continuous (slice x) := by
      intro x; exact P.continuous.comp (hcont.comp (hembed_y x))
    have hsl_LBV : ∀ᵐ x : ℝ, LocallyBoundedVariationOn (slice x) Set.univ := by
      filter_upwards [hBVy] with x hx
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]
      exact (P.lipschitz).comp_boundedVariationOn (g := fun y : ℝ => f ⟨x, y⟩)
        (s := Set.Icc a b) (hx a b)
    have hderiv : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, HasDerivAt (slice x) (deriv (slice x) y) y := by
      filter_upwards [hsl_LBV] with x hx
      filter_upwards [hx.ae_differentiableAt] with y hy
      exact hy.hasDerivAt
    have hint : ∀ᵐ x : ℝ, ∀ u v : ℝ,
        IntervalIntegrable (fun y => ‖deriv (slice x) y‖) volume u v := by
      filter_upwards [hderiv, hsl_LBV] with x hxderiv hxLBV u v
      have hcore : ∀ p q : ℝ, p ≤ q →
          IntervalIntegrable (fun y => ‖deriv (slice x) y‖) volume p q := by
        intro p q hpq
        have hbvfin : eVariationOn (slice x) (Set.Icc p q) ≠ ⊤ := by
          have := hxLBV p q (Set.mem_univ p) (Set.mem_univ q)
          rwa [BoundedVariationOn, Set.univ_inter] at this
        have hlint_le : ∫⁻ y in Set.Icc p q, ‖deriv (slice x) y‖₊
            ≤ eVariationOn (slice x) (Set.Icc p q) :=
          lintegral_nnnorm_deriv_le_eVariationOn hpq hxderiv
        have hfin : ∫⁻ y in Set.Icc p q, (‖deriv (slice x) y‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top hbvfin hlint_le
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
        refine ⟨((measurable_deriv (slice x)).norm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ y in Set.Ioc p q, ‖‖deriv (slice x) y‖‖ₑ
            ≤ ∫⁻ y in Set.Icc p q, (‖deriv (slice x) y‖₊ : ℝ≥0∞) := by
          refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans_eq ?_
          apply lintegral_congr; intro y; rw [enorm_norm, enorm_eq_nnnorm]
        exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
      rcases le_total u v with huv | hvu
      · exact hcore u v huv
      · exact (hcore v u hvu).symm
    have hmaf : ∀ᵐ x : ℝ, ∀ a c : ℝ,
        eVariationOn (slice x) (Set.Icc a c)
          ≤ ∫⁻ y in Set.Icc a c, ‖deriv (slice x) y‖₊ := hNS
    exact ae_slice_AC_of_maf hsl_cont hderiv hint hmaf
  -- **Horizontal slice AC** (both real components, recombined).
  have hHorizAC : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b := by
    have hre := hcompAC_x Complex.reCLM (by
      filter_upwards [hNSx] with y hy a b; exact (hy a b).1)
    have him := hcompAC_x Complex.imCLM (by
      filter_upwards [hNSx] with y hy a b; exact (hy a b).2)
    filter_upwards [hre, him] with y hyre hyim a b
    exact absolutelyContinuousOnInterval_of_re_im (hyre a b) (hyim a b)
  -- **Vertical slice AC** (both real components, recombined).
  have hVertAC : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b := by
    have hre := hcompAC_y Complex.reCLM (by
      filter_upwards [hNSy] with x hx a b; exact (hx a b).1)
    have him := hcompAC_y Complex.imCLM (by
      filter_upwards [hNSy] with x hx a b; exact (hx a b).2)
    filter_upwards [hre, him] with x hxre hxim a b
    exact absolutelyContinuousOnInterval_of_re_im (hxre a b) (hxim a b)
  -- **Horizontal slice derivative existence.** For a.e. `y`, the complex slice is BV on every
  -- interval, hence a.e.-`x` differentiable; the derivative is `forwardSliceDerivX f ⟨x,y⟩`.
  have hHorizDeriv : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ,
      HasDerivAt (fun t : ℝ => f ⟨t, y⟩) (forwardSliceDerivX f ⟨x, y⟩) x := by
    filter_upwards [hBVx] with y hy
    -- BV on every `[-n, n]` ⟹ a.e. differentiable.
    have hLBV : LocallyBoundedVariationOn (fun t : ℝ => f ⟨t, y⟩) Set.univ := by
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]; exact hy a b
    filter_upwards [hLBV.ae_differentiableAt] with x hx
    have : forwardSliceDerivX f ⟨x, y⟩ = deriv (fun t : ℝ => f ⟨t, y⟩) x := by
      simp only [forwardSliceDerivX]
    rw [this]; exact hx.hasDerivAt
  -- **Vertical slice derivative existence** (mirror).
  have hVertDeriv : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ,
      HasDerivAt (fun t : ℝ => f ⟨x, t⟩) (forwardSliceDerivY f ⟨x, y⟩) y := by
    filter_upwards [hBVy] with x hx
    have hLBV : LocallyBoundedVariationOn (fun t : ℝ => f ⟨x, t⟩) Set.univ := by
      intro a b _ _
      have hUI : (Set.univ : Set ℝ) ∩ Set.Icc a b = Set.Icc a b := by rw [Set.univ_inter]
      rw [BoundedVariationOn, hUI]; exact hx a b
    filter_upwards [hLBV.ae_differentiableAt] with y hy
    have : forwardSliceDerivY f ⟨x, y⟩ = deriv (fun t : ℝ => f ⟨x, t⟩) y := by
      simp only [forwardSliceDerivY]
    rw [this]; exact hy.hasDerivAt
  -- Assemble the four conjuncts of the conclusion.
  refine ⟨forwardSliceDerivX f, forwardSliceDerivY f, ?_, ?_, hL2x, hL2y⟩
  · -- `ACLHorizontal f (forwardSliceDerivX f)`.
    filter_upwards [hHorizAC, hHorizDeriv] with y hyAC hyDeriv
    exact ⟨hyAC, hyDeriv⟩
  · -- `ACLVertical f (forwardSliceDerivY f)`.
    filter_upwards [hVertAC, hVertDeriv] with x hxAC hxDeriv
    exact ⟨hxAC, hxDeriv⟩

/-- **Gehring–Lehto a.e. differentiability (Grötzsch-free).**

A geometric `K`-quasiconformal map `f` is differentiable almost everywhere, obtained **without**
the quasiconformal-roundness / Grötzsch-symmetrization route. The forward reverse length–area
residual `exists_acl_memLp_sliceGradient` supplies an `L²_loc` ACL gradient `(gx, gy)`, i.e.
`f ∈ W^{1,2}_loc` as a homeomorphism; the proven Gehring–Lehto theorem
`ae_differentiableAt_of_W12loc_homeomorph` then yields total differentiability almost everywhere. -/
theorem IsQCGeometric.ae_differentiableAt_gehringLehto {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x := by
  classical
  have hfcont : Continuous f := hf.2.1.isHomeomorph.continuous
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  obtain ⟨gx, gy, haclx, hacly, hgx2, hgy2⟩ := hf.exists_acl_memLp_sliceGradient
  -- `L²_loc ⟹ L¹_loc` on compacts supplies the local integrability the weak-gradient bridge needs.
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict Kc) := hh Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hfLI : LocallyIntegrable f := hfcont.locallyIntegrable
  have hgxLI : LocallyIntegrable gx := hLIofL2 hgx2
  have hgyLI : LocallyIntegrable gy := hLIofL2 hgy2
  -- `f ∈ W^{1,2}_loc`: the ACL slice gradient is the weak gradient.
  have hwg : HasWeakGradient gx gy f Set.univ :=
    hasWeakGradient_of_acl hfLI hgxLI hgyLI haclx hacly
  -- The proven Gehring–Lehto theorem: a `W^{1,2}_loc` homeomorphism is a.e. differentiable.
  exact RiemannDynamics.GehringLehto.ae_differentiableAt_of_W12loc_homeomorph
    hhomeo hwg hgx2 hgy2

end RiemannDynamics

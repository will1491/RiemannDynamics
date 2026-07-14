/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.GeometricToACL
import RiemannDynamics.QC.LengthArea.LengthAreaInverse

/-!
# Lusin condition N for the geometric quasiconformal inverse

For a geometrically `K`-quasiconformal homeomorphism `f`, the inverse homeomorphism
`g = f⁻¹` maps Lebesgue-null sets to Lebesgue-null sets (Lusin condition N), and the
image of a null set meets almost every vertical line in a null set.

The load-bearing input is the almost-everywhere structure of the *forward* map `f`:
differentiability almost everywhere with almost-everywhere positive Jacobian
determinant. From these two facts the inverse-function theorem forces `g` to inherit a
genuine differential wherever `f` is nondegenerate, so the image area has no singular
part. The regularity pack (`hae_diff`, `hae_det`) is carried as hypotheses, discharged
downstream by `geometric_ae_differentiableAt` and `geometric_ae_det_pos`.

## Main statements

* `geometric_ae_det_pos` — almost-everywhere positive Jacobian of the forward map;
* `geometric_inverse_conditionN` — the inverse maps null sets to null sets;
* `geometric_sliced_noSingular` — the image of a null set meets almost every vertical
  line in a null set.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology Real

namespace RiemannDynamics

/-- **Almost-everywhere positive Jacobian of a geometrically quasiconformal map.** A
geometrically `K`-quasiconformal homeomorphism `f` has almost-everywhere positive
Jacobian determinant. The homeomorphism is `SensePreserving`, so at an almost-every
point the image circles wind `+1`; together with almost-everywhere differentiability
and nonvanishing Jacobian this forces the determinant to be positive
(`SensePreserving.ae_det_pos`). -/
theorem geometric_ae_det_pos {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ z : ℂ, 0 < (fderiv ℝ f z).det :=
  (IsQCGeometric.reverseLengthArea_data hf).2.1

/-- **Lusin condition N for the geometric quasiconformal inverse.** For a homeomorphism
`f : ℂ → ℂ` that is differentiable almost everywhere (`hae_diff`) with almost-everywhere
positive Jacobian determinant (`hae_det`), the inverse homeomorphism
`g = ⇑(hhomeo.homeomorph f).symm` maps Lebesgue-null sets to Lebesgue-null sets: for
every null `S`, `volume (g '' S) = 0`.

Pointwise a.e. quasiconformality of `g` alone does *not* imply Lusin condition N (the
Minkowski-`?` obstruction), so the proof uses the global inverse-function-theorem
structure of `f`. Split `S = (S ∩ D) ∪ (S ∩ Dᶜ)` along the differentiability set
`D = {w | DifferentiableAt ℝ g w}`:
* on `S ∩ D` the map `g` is differentiable, so the differentiable-map null-image
  theorem gives a null image;
* on `S ∩ Dᶜ ⊆ Dᶜ`, `g '' Dᶜ ⊆ E` where
  `E = {z | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < det (Df z)}` is null (by `hae_diff`,
  `hae_det`): wherever `f` is differentiable at `g w` with positive Jacobian, the easy
  half of the inverse function theorem makes `g` differentiable at `w`, contradicting
  `w ∉ D`.
This uses only the forward map's almost-everywhere nondegeneracy and the
inverse-relation; it never assumes Lusin-N for `g`. -/
theorem geometric_inverse_conditionN {f : ℂ → ℂ} {K : ℝ} (_hf : IsQCGeometric f K)
    (hhomeo : IsHomeomorph f)
    (hae_diff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z)
    (hae_det : ∀ᵐ z : ℂ, 0 < (fderiv ℝ f z).det) :
    ∀ S : Set ℂ, volume S = 0 → volume ((⇑(hhomeo.homeomorph f).symm) '' S) = 0 := by
  classical
  -- The inverse homeomorphism `g = f⁻¹` and the mutual-inverse relations.
  set g : ℂ → ℂ := ⇑(hhomeo.homeomorph f).symm with hg
  have hfwd : ∀ z, (hhomeo.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hhomeo z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hhomeo.homeomorph f).symm w)]
    exact (hhomeo.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg, ← hfwd z]
    exact (hhomeo.homeomorph f).symm_apply_apply z
  have hgcont : Continuous g := (hhomeo.homeomorph f).continuous_symm
  -- The differentiability set `D` of `g` (measurable).
  set D : Set ℂ := {w : ℂ | DifferentiableAt ℝ g w} with hD
  have hDmeas : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  -- The degeneracy set of the forward map `f`, which is null.
  set E : Set ℂ := {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det} with hE
  have hEnull : volume E = 0 := by
    have hdiffnull : volume {z : ℂ | ¬ DifferentiableAt ℝ f z} = 0 :=
      MeasureTheory.ae_iff.mp hae_diff
    have hdetnull : volume {z : ℂ | ¬ 0 < (fderiv ℝ f z).det} = 0 := by
      rw [← ae_iff]; exact hae_det
    have hsub : E ⊆ {z : ℂ | ¬ DifferentiableAt ℝ f z} ∪ {z : ℂ | ¬ 0 < (fderiv ℝ f z).det} := by
      intro z hz; exact hz
    exact measure_mono_null hsub (measure_union_null hdiffnull hdetnull)
  -- KEY: `g '' Dᶜ ⊆ E`, hence `volume (g '' Dᶜ) = 0`.
  have hsingular : g '' Dᶜ ⊆ E := by
    rintro _ ⟨w, hwD, rfl⟩
    by_contra hgwE
    -- `g w ∉ E` means `f` is differentiable at `g w` with positive Jacobian.
    rw [hE, Set.mem_setOf_eq, not_or, not_not, not_not] at hgwE
    obtain ⟨hdiff, hdetpos⟩ := hgwE
    -- Build the linear equivalence from the nonvanishing determinant of `Df (g w)`.
    set f' : ℂ →L[ℝ] ℂ := fderiv ℝ f (g w) with hf'
    have hdetne : f'.det ≠ 0 := ne_of_gt hdetpos
    set e : ℂ ≃L[ℝ] ℂ := f'.toContinuousLinearEquivOfDetNeZero hdetne with he
    have hecoe : (e : ℂ →L[ℝ] ℂ) = f' :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero f' hdetne
    have hfderiv : HasFDerivAt f (e : ℂ →L[ℝ] ℂ) (g w) := by
      rw [hecoe]; exact hdiff.hasFDerivAt
    have hloc : ∀ᶠ y in nhds w, f (g y) = y := Filter.Eventually.of_forall hfg
    -- The easy half of the inverse function theorem: `g` is differentiable at `w`.
    have hgfderiv : HasFDerivAt g (e.symm : ℂ →L[ℝ] ℂ) w :=
      HasFDerivAt.of_local_left_inverse hgcont.continuousAt hfderiv hloc
    -- But `w ∉ D` says `g` is *not* differentiable at `w`.
    exact hwD hgfderiv.differentiableAt
  have hsingular_null : volume (g '' Dᶜ) = 0 := measure_mono_null hsingular hEnull
  -- Now the main split, for an arbitrary null `S`.
  intro S hS
  have hSsplit : g '' S = g '' (S ∩ D) ∪ g '' (S ∩ Dᶜ) := by
    rw [← Set.image_union, ← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
  rw [hSsplit]
  refine measure_union_null ?_ ?_
  · -- Differentiable part: `g` is differentiable on `S ∩ D` (null), so its image is null.
    have hSDnull : volume (S ∩ D) = 0 := measure_mono_null Set.inter_subset_left hS
    have hgdiffOn : DifferentiableOn ℝ g (S ∩ D) := fun w hw => hw.2.differentiableWithinAt
    exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      hgdiffOn hSDnull
  · -- Singular part: `g '' (S ∩ Dᶜ) ⊆ g '' Dᶜ`, which is null.
    exact measure_mono_null (Set.image_mono Set.inter_subset_right) hsingular_null

/-- **Vertical-slice null image for the geometric quasiconformal map.** For a
homeomorphism `f : ℂ → ℂ` that is differentiable almost everywhere (`hae_diff`) with
almost-everywhere positive Jacobian determinant (`hae_det`), and a measurable null set
`E`, the image `f '' E` meets almost every vertical line in a Lebesgue-null set:
`∀ᵐ x : ℝ, volume {y : ℝ | (Complex.mk x y) ∈ f '' E} = 0`. The image `f '' E` is
Lebesgue-null (Lusin condition N for `f`, from its almost-everywhere nondegeneracy), and
a null planar set has null vertical slices at almost every abscissa (Fubini / Tonelli). -/
theorem geometric_sliced_noSingular {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (hhomeo : IsHomeomorph f)
    (hae_diff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z)
    (hae_det : ∀ᵐ z : ℂ, 0 < (fderiv ℝ f z).det)
    {E : Set ℂ} (hEmeas : MeasurableSet E) (hEnull : volume E = 0) :
    ∀ᵐ x : ℝ, volume {y : ℝ | (Complex.mk x y : ℂ) ∈ f '' E} = 0 := by
  -- The a.e.-nondegeneracy and measurability hypotheses are subsumed: the super-critical weak
  -- gradient below is extracted from `hf` alone, and Lusin (N) needs only nullity of `E`.
  have _ := hae_diff
  have _ := hae_det
  have _ := hEmeas
  -- **Forward Lusin (N).** The map `f` has a super-critical (`L^p_loc`, `p > 2`) weak gradient,
  -- so it maps the null set `E` to a null set (planar Marcus–Mizel / Morrey).
  obtain ⟨p, gx, gy, hp2, hgrad, hgxp, hgyp⟩ :=
    IsQCGeometric.exists_weakGradient_memLpLocOn_gt_two hf
  have hcont : Continuous f := hhomeo.continuous
  have hT : volume (f '' E) = 0 :=
    lusinN_image_null_of_weakGradient hp2 hcont hgrad hgxp hgyp hEnull
  -- **Fubini slicing.** A null planar set meets almost every vertical line in a null set.
  set T : Set ℂ := f '' E with hTdef
  -- Transport `T` to a null set `T'` in `ℝ × ℝ` (coordinates `(x, y) = (re, im)`).
  have hmp : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  set T' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' T with hT'def
  have hT'null : volume T' = 0 := hmp.quasiMeasurePreserving.preimage_null hT
  -- For the product measure, `volume T' = 0` ⟹ a.e. first-fiber (the `x = re`) is null.
  have hprodnull : ∀ᵐ q : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), q ∉ T' := by
    rw [ae_iff]; simpa [Measure.volume_eq_prod] using hT'null
  have hae : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, (x, y) ∉ T' := Measure.ae_ae_of_ae_prod hprodnull
  refine hae.mono (fun x hx => ?_)
  have hmem : ∀ y : ℝ, ((x, y) ∈ T') ↔ ((Complex.mk x y) ∈ T) := by
    intro y
    simp only [hT'def, Set.mem_preimage, Complex.measurableEquivRealProd_symm_apply]
  rw [ae_iff] at hx
  have hset : {y : ℝ | (Complex.mk x y : ℂ) ∈ T} = {y : ℝ | (x, y) ∈ T'} := by
    ext y; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hmem y]
  rw [hset]; simpa using hx

end RiemannDynamics

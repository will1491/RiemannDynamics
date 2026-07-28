/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.Foundations.Equivariance
import RiemannDynamics.Surface.Orientation

/-!
# Teichmüller representatives over an abstract Fuchsian base

A point of the Bers model of Teichmüller space over `Γ₀ ≤ SL(2, ℝ)` is represented by a
Beltrami coefficient that is symmetric across the real axis and `Γ₀`-invariant (`TeichRep`).
Each representative `x` has a unique normalized quasiconformal solution `x.w` fixing `0` and
`1`; it commutes with conjugation, restricts to an increasing homeomorphism `x.boundary` of
the real line, and conjugates `Γ₀` to the Fuchsian group `x.group = fuchsianImage Γ₀ x.w`,
which inherits proper discontinuity, freeness and cocompactness from `Γ₀`. Membership in
`x.group` is detected by the boundary values of `x.w` alone.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A **Teichmüller representative** over the base `Γ₀ ≤ SL(2, ℝ)`: a Beltrami coefficient
symmetric across the real axis and invariant under `Γ₀`. -/
structure TeichRep (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) where
  /-- The underlying Beltrami coefficient. -/
  b : BeltramiCoeff
  /-- The coefficient commutes a.e. with complex conjugation. -/
  symm : IsSymmetricBeltrami b
  /-- The coefficient satisfies the `Γ₀`-invariance law. -/
  inv : IsInvariantBeltrami' Γ₀ b

/-- The base point: the zero Beltrami coefficient is symmetric and invariant. -/
noncomputable def TeichRep.zero (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    TeichRep Γ₀ where
  b := BeltramiCoeff.zero
  symm := Filter.Eventually.of_forall fun z => by simp [BeltramiCoeff.zero]
  inv := fun γ _ => Filter.Eventually.of_forall fun z => by simp [BeltramiCoeff.zero]

instance (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Nonempty (TeichRep Γ₀) := ⟨TeichRep.zero Γ₀⟩

/-! ## Symmetric extension of upper-half-plane data -/

/-- The reflection-symmetric extension of a Beltrami datum given on the upper half plane:
`μ̂(z) = μ(z)` for `im z > 0` and `μ̂(z) = conj (μ(z̄))` otherwise. -/
noncomputable def symmExtension (μ : ℂ → ℂ) : ℂ → ℂ := fun z =>
  if 0 < z.im then μ z else starRingEnd ℂ (μ (starRingEnd ℂ z))

/-- Measurability of the symmetric extension. -/
theorem symmExtension_measurable {μ : ℂ → ℂ} (hmeas : Measurable μ) :
    Measurable (symmExtension μ) := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  exact Measurable.ite hU hmeas
    (Complex.continuous_conj.measurable.comp (hmeas.comp Complex.continuous_conj.measurable))

/-- The essential supremum bound of the symmetric extension, from the bound of the datum on
the upper half plane. -/
theorem symmExtension_bound {μ : ℂ → ℂ}
    (hbound : eLpNormEssSup μ (volume.restrict {z : ℂ | 0 < z.im}) < 1) :
    eLpNormEssSup (symmExtension μ) volume < 1 := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have h1 : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ‖μ z‖ₑ ≤ eLpNormEssSup μ (volume.restrict {z : ℂ | 0 < z.im}) :=
    enorm_ae_le_eLpNormEssSup μ _
  have h1' : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
      ‖μ z‖ₑ ≤ eLpNormEssSup μ (volume.restrict {z : ℂ | 0 < z.im}) :=
    (ae_restrict_iff' hU).mp h1
  have hmp : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) volume volume := by
    have h := Complex.conjLIE.measurePreserving
    have heq : (fun z : ℂ => starRingEnd ℂ z) = ⇑Complex.conjLIE := by
      funext z
      rw [Complex.conjLIE_apply]
    rw [heq]
    exact h
  have h2 := hmp.quasiMeasurePreserving.ae h1'
  have haxis : ∀ᵐ z : ℂ, z.im ≠ 0 := by
    rw [ae_iff]
    have hset : {a : ℂ | ¬a.im ≠ 0} = {z : ℂ | z.im = 0} := by
      ext a
      simp
    rw [hset]
    exact volume_imZero
  have hae : ∀ᵐ z : ℂ, ‖symmExtension μ z‖ₑ
      ≤ eLpNormEssSup μ (volume.restrict {z : ℂ | 0 < z.im}) := by
    filter_upwards [h1', h2, haxis] with z hz1 hz2 hzax
    by_cases hzim : 0 < z.im
    · have hval : symmExtension μ z = μ z := by
        simp only [symmExtension]
        rw [if_pos hzim]
      rw [hval]
      exact hz1 hzim
    · have hmem : starRingEnd ℂ z ∈ {w : ℂ | 0 < w.im} := by
        have hlt : z.im < 0 := lt_of_le_of_ne (not_lt.mp hzim) hzax
        simp only [Set.mem_setOf_eq, Complex.conj_im]
        linarith
      have hval : symmExtension μ z = starRingEnd ℂ (μ (starRingEnd ℂ z)) := by
        simp only [symmExtension]
        rw [if_neg hzim]
      rw [hval]
      have henorm : ‖starRingEnd ℂ (μ (starRingEnd ℂ z))‖ₑ = ‖μ (starRingEnd ℂ z)‖ₑ := by
        simp [enorm_eq_nnnorm]
      rw [henorm]
      exact hz2 hmem
  exact lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound hae) hbound

/-- The symmetric extension commutes with conjugation off the real axis, hence a.e. -/
theorem symmExtension_symmetric {μ : ℂ → ℂ} :
    ∀ᵐ z : ℂ, symmExtension μ (starRingEnd ℂ z) = starRingEnd ℂ (symmExtension μ z) := by
  have haxis : ∀ᵐ z : ℂ, z.im ≠ 0 := by
    rw [ae_iff]
    have hset : {a : ℂ | ¬a.im ≠ 0} = {z : ℂ | z.im = 0} := by
      ext a
      simp
    rw [hset]
    exact volume_imZero
  filter_upwards [haxis] with z hz
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have h1 : 0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im]
      linarith
    have hL : symmExtension μ (starRingEnd ℂ z) = μ (starRingEnd ℂ z) := by
      simp only [symmExtension]
      rw [if_pos h1]
    have hR : symmExtension μ z = starRingEnd ℂ (μ (starRingEnd ℂ z)) := by
      simp only [symmExtension]
      rw [if_neg (not_lt.mpr hneg.le)]
    rw [hL, hR, Complex.conj_conj]
  · have h1 : ¬0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im, not_lt]
      linarith
    have hL : symmExtension μ (starRingEnd ℂ z)
        = starRingEnd ℂ (μ (starRingEnd ℂ (starRingEnd ℂ z))) := by
      simp only [symmExtension]
      rw [if_neg h1]
    have hR : symmExtension μ z = μ z := by
      simp only [symmExtension]
      rw [if_pos hpos]
    rw [hL, hR, Complex.conj_conj]

/-- Invariance of the symmetric extension from invariance of the datum on the upper half
plane: real Möbius maps preserve both half planes and commute with conjugation. -/
theorem symmExtension_invariant {μ : ℂ → ℂ}
    (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hinv : ∀ γ ∈ Γ₀, ∀ᵐ z : ℂ ∂(volume.restrict {z : ℂ | 0 < z.im}),
      μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) :
    ∀ γ ∈ Γ₀, ∀ᵐ z : ℂ, symmExtension μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = symmExtension μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  intro γ hγ
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hDconj : ∀ w : ℂ,
      moebiusDenom γ (starRingEnd ℂ w) = starRingEnd ℂ (moebiusDenom γ w) := by
    intro w
    simp [moebiusDenom, map_add, map_mul, Complex.conj_ofReal]
  have hMconj : ∀ w : ℂ,
      moebiusMap γ (starRingEnd ℂ w) = starRingEnd ℂ (moebiusMap γ w) := by
    intro w
    simp [moebiusMap, moebiusDenom, map_div₀, map_add, map_mul, Complex.conj_ofReal]
  have h1' : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
      μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 :=
    (ae_restrict_iff' hU).mp (hinv γ hγ)
  have hmp : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) volume volume := by
    have h := Complex.conjLIE.measurePreserving
    have heq : (fun z : ℂ => starRingEnd ℂ z) = ⇑Complex.conjLIE := by
      funext z
      rw [Complex.conjLIE_apply]
    rw [heq]
    exact h
  have h2' := hmp.quasiMeasurePreserving.ae h1'
  have haxis : ∀ᵐ z : ℂ, z.im ≠ 0 := by
    rw [ae_iff]
    have hset : {a : ℂ | ¬a.im ≠ 0} = {z : ℂ | z.im = 0} := by
      ext a
      simp
    rw [hset]
    exact volume_imZero
  filter_upwards [h1', h2', haxis] with z hz1 hz2 hzax
  rcases lt_or_gt_of_ne hzax with hneg | hpos
  · have hgzneg : (moebiusMap γ z).im < 0 := moebiusMap_im_neg γ hneg
    have hgznlt : ¬0 < (moebiusMap γ z).im := not_lt.mpr hgzneg.le
    have hznlt : ¬0 < z.im := not_lt.mpr hneg.le
    have hczU : starRingEnd ℂ z ∈ {w : ℂ | 0 < w.im} := by
      simp only [Set.mem_setOf_eq, Complex.conj_im]
      linarith
    have hL : symmExtension μ (moebiusMap γ z)
        = starRingEnd ℂ (μ (starRingEnd ℂ (moebiusMap γ z))) := by
      simp only [symmExtension]
      rw [if_neg hgznlt]
    have hR : symmExtension μ z = starRingEnd ℂ (μ (starRingEnd ℂ z)) := by
      simp only [symmExtension]
      rw [if_neg hznlt]
    rw [hL, hR]
    have hkey := hz2 hczU
    rw [hMconj z, hDconj z] at hkey
    rw [Complex.conj_conj] at hkey
    have hconj := congrArg (starRingEnd ℂ) hkey
    simp only [map_mul, map_pow, Complex.conj_conj] at hconj
    exact hconj
  · have hgz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hpos
    have hL : symmExtension μ (moebiusMap γ z) = μ (moebiusMap γ z) := by
      simp only [symmExtension]
      rw [if_pos hgz]
    have hR : symmExtension μ z = μ z := by
      simp only [symmExtension]
      rw [if_pos hpos]
    rw [hL, hR]
    exact hz1 hpos

/-- Constructor of a Teichmüller representative from a Beltrami datum on the upper half
plane, by reflection-symmetric extension. -/
noncomputable def TeichRep.ofUpper (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (μ : ℂ → ℂ) (hmeas : Measurable μ)
    (hbound : eLpNormEssSup μ (volume.restrict {z : ℂ | 0 < z.im}) < 1)
    (hinv : ∀ γ ∈ Γ₀, ∀ᵐ z : ℂ ∂(volume.restrict {z : ℂ | 0 < z.im}),
      μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) : TeichRep Γ₀ where
  b := ⟨symmExtension μ, symmExtension_measurable hmeas, symmExtension_bound hbound⟩
  symm := symmExtension_symmetric
  inv := symmExtension_invariant Γ₀ hinv

/-! ## The normalized solution -/

/-- The normalized quasiconformal solution of the Beltrami coefficient of `x`: the unique
quasiconformal `w` with `∂̄w = μ ∂w`, `w 0 = 0` and `w 1 = 1`. -/
noncomputable def TeichRep.w (x : TeichRep Γ₀) : ℂ → ℂ :=
  (mrmt_unique_normalized x.b).choose

/-- The normalized solution is quasiconformal with coefficient `x.b`. -/
theorem TeichRep.w_isQCAnalytic (x : TeichRep Γ₀) : IsQCAnalytic x.w x.b := by
  exact (mrmt_unique_normalized x.b).choose_spec.1.1

/-- The normalized solution fixes `0`. -/
theorem TeichRep.w_zero (x : TeichRep Γ₀) : x.w 0 = 0 := by
  exact (mrmt_unique_normalized x.b).choose_spec.1.2.1

/-- The normalized solution fixes `1`. -/
theorem TeichRep.w_one (x : TeichRep Γ₀) : x.w 1 = 1 := by
  exact (mrmt_unique_normalized x.b).choose_spec.1.2.2

/-- Uniqueness of the normalized solution: any quasiconformal map with coefficient `x.b`
fixing `0` and `1` equals `x.w` as a function. -/
theorem TeichRep.w_unique (x : TeichRep Γ₀) {g : ℂ → ℂ} (hg : IsQCAnalytic g x.b)
    (g0 : g 0 = 0) (g1 : g 1 = 1) : g = x.w := by
  exact (mrmt_unique_normalized x.b).choose_spec.2 g ⟨hg, g0, g1⟩

/-- The normalized solution is injective. -/
theorem TeichRep.w_injective (x : TeichRep Γ₀) : Function.Injective x.w :=
  x.w_isQCAnalytic.injective

/-- The normalized solution of a symmetric coefficient commutes with conjugation at every
point: `conj ∘ w ∘ conj` solves the same normalized problem. -/
theorem TeichRep.w_conj (x : TeichRep Γ₀) :
    ∀ z : ℂ, x.w (starRingEnd ℂ z) = starRingEnd ℂ (x.w z) := by
  have hG : IsQCAnalytic (fun z => starRingEnd ℂ (x.w (starRingEnd ℂ z))) x.b.reflect :=
    isQCAnalytic_conj_conj x.w_isQCAnalytic
  have hrefl : x.b.reflect.μ =ᵐ[volume] x.b.μ :=
    (isSymmetricBeltrami_iff_reflect x.b).mp x.symm
  have hG' : IsQCAnalytic (fun z => starRingEnd ℂ (x.w (starRingEnd ℂ z))) x.b :=
    hG.congr_coeff hrefl
  have h0 : (fun z : ℂ => starRingEnd ℂ (x.w (starRingEnd ℂ z))) 0 = 0 := by
    simp only [map_zero, TeichRep.w_zero]
  have h1 : (fun z : ℂ => starRingEnd ℂ (x.w (starRingEnd ℂ z))) 1 = 1 := by
    simp only [map_one, TeichRep.w_one]
  have heq := x.w_unique hG' h0 h1
  intro z
  have hz := congrFun heq (starRingEnd ℂ z)
  simp only [Complex.conj_conj] at hz
  exact hz.symm

/-! ## Boundary values -/

/-- The normalized solution maps real points to real points. -/
theorem TeichRep.w_real (x : TeichRep Γ₀) (t : ℝ) : (x.w t).im = 0 := by
  have h := x.w_conj (t : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- The boundary map of a Teichmüller representative: the restriction of the normalized
solution to the real line. -/
noncomputable def TeichRep.boundary (x : TeichRep Γ₀) : ℝ → ℝ := fun t => (x.w t).re

/-- The boundary map fixes `0`. -/
theorem TeichRep.boundary_zero (x : TeichRep Γ₀) : x.boundary 0 = 0 := by
  simp only [TeichRep.boundary, Complex.ofReal_zero, TeichRep.w_zero, Complex.zero_re]

/-- The boundary map fixes `1`. -/
theorem TeichRep.boundary_one (x : TeichRep Γ₀) : x.boundary 1 = 1 := by
  simp only [TeichRep.boundary, Complex.ofReal_one, TeichRep.w_one, Complex.one_re]

/-- On the real line the normalized solution is the coercion of its boundary map. -/
theorem TeichRep.w_ofReal (x : TeichRep Γ₀) (t : ℝ) : x.w t = (x.boundary t : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp only [TeichRep.boundary, Complex.ofReal_re]
  · rw [x.w_real t, Complex.ofReal_im]

/-- The boundary map is strictly increasing. -/
theorem TeichRep.boundary_strictMono (x : TeichRep Γ₀) : StrictMono x.boundary := by
  have hcont : Continuous x.boundary := by
    have h : Continuous fun t : ℝ => (x.w (t : ℂ)).re :=
      Complex.continuous_re.comp
        ((x.w_isQCAnalytic.1.1.continuous).comp Complex.continuous_ofReal)
    exact h
  have hinj : Function.Injective x.boundary := by
    intro s t hst
    have hs := x.w_ofReal s
    have ht := x.w_ofReal t
    have hw : x.w s = x.w t := by
      rw [hs, ht, hst]
    have hc := x.w_isQCAnalytic.injective hw
    exact_mod_cast hc
  rcases hcont.strictMono_of_inj hinj with h | h
  · exact h
  · exfalso
    have h01 := h (by norm_num : (0 : ℝ) < 1)
    rw [x.boundary_zero, x.boundary_one] at h01
    exact absurd h01 (by norm_num)

/-- The boundary map is onto the real line. -/
theorem TeichRep.boundary_surjective (x : TeichRep Γ₀) :
    Function.Surjective x.boundary := by
  intro s
  obtain ⟨z, hz⟩ := x.w_isQCAnalytic.1.1.bijective.surjective ((s : ℝ) : ℂ)
  have hconj : x.w (starRingEnd ℂ z) = x.w z := by
    rw [x.w_conj z, hz, Complex.conj_ofReal]
  have hzr : starRingEnd ℂ z = z := x.w_isQCAnalytic.injective hconj
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hzr
  refine ⟨z.re, ?_⟩
  have hzeq : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
  simp only [TeichRep.boundary]
  rw [hzeq, hz, Complex.ofReal_re]

/-- The normalized solution preserves the upper half plane or carries it onto the lower half
plane. -/
theorem TeichRep.w_halfPlane_dichotomy (x : TeichRep Γ₀) :
    ((∀ z : ℂ, 0 < z.im → 0 < (x.w z).im) ∧
        x.w '' {z : ℂ | 0 < z.im} = {z : ℂ | 0 < z.im}) ∨
      ((∀ z : ℂ, 0 < z.im → (x.w z).im < 0) ∧
        x.w '' {z : ℂ | 0 < z.im} = {z : ℂ | z.im < 0}) := by
  have hcont : Continuous x.w := x.w_isQCAnalytic.1.1.continuous
  have hinj : Function.Injective x.w := x.w_isQCAnalytic.injective
  have hsurj : Function.Surjective x.w := x.w_isQCAnalytic.1.1.bijective.surjective
  have hreal_iff : ∀ z : ℂ, (x.w z).im = 0 ↔ z.im = 0 := by
    intro z
    constructor
    · intro h0
      obtain ⟨t, ht⟩ := x.boundary_surjective (x.w z).re
      have htz : x.w (t : ℂ) = x.w z := by
        rw [x.w_ofReal t, ht]
        exact Complex.ext (by simp) (by simp [h0])
      have hz := hinj htz
      rw [← hz]
      simp
    · intro h0
      have hz : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [h0])
      rw [← hz]
      exact x.w_real z.re
  have himsub : x.w '' {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0} := by
    rintro u ⟨z, hzU, rfl⟩
    have hzne : z.im ≠ 0 := ne_of_gt hzU
    have hne : (x.w z).im ≠ 0 := fun h => hzne ((hreal_iff z).mp h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hpre : IsPreconnected (x.w '' {z : ℂ | 0 < z.im}) :=
    ((convex_halfSpace_im_gt 0).isPreconnected).image _ hcont.continuousOn
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hLopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hdisj : Disjoint {z : ℂ | 0 < z.im} {z : ℂ | z.im < 0} := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : 0 < z.im := hz1
    have h2 : z.im < 0 := hz2
    linarith
  rcases hpre.subset_or_subset hUopen hLopen hdisj himsub with hUU | hUL
  · left
    have hpt : ∀ z : ℂ, 0 < z.im → 0 < (x.w z).im := fun z hz => hUU ⟨z, hz, rfl⟩
    refine ⟨hpt, Set.Subset.antisymm hUU ?_⟩
    intro u hu
    obtain ⟨z, rfl⟩ := hsurj u
    have hu' : 0 < (x.w z).im := hu
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · exfalso
      have h1 : 0 < (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        linarith
      have h2 : 0 < (x.w (starRingEnd ℂ z)).im := hpt _ h1
      rw [x.w_conj z, Complex.conj_im] at h2
      linarith
    · exfalso
      have h0 : (x.w z).im = 0 := (hreal_iff z).mpr hzero
      linarith
    · exact ⟨z, hpos, rfl⟩
  · right
    have hpt : ∀ z : ℂ, 0 < z.im → (x.w z).im < 0 := fun z hz => hUL ⟨z, hz, rfl⟩
    refine ⟨hpt, Set.Subset.antisymm hUL ?_⟩
    intro u hu
    obtain ⟨z, rfl⟩ := hsurj u
    have hu' : (x.w z).im < 0 := hu
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · exfalso
      have h1 : 0 < (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        linarith
      have h2 : (x.w (starRingEnd ℂ z)).im < 0 := hpt _ h1
      rw [x.w_conj z, Complex.conj_im] at h2
      linarith
    · exfalso
      have h0 : (x.w z).im = 0 := (hreal_iff z).mpr hzero
      linarith
    · exact ⟨z, hpos, rfl⟩

/-- The normalized solution preserves the upper half plane: the strictly increasing
boundary map together with the almost-everywhere positive Jacobian selects the preserving
branch of the half-plane dichotomy. -/
theorem TeichRep.w_mapsTo_upper (x : TeichRep Γ₀) :
    ∀ z : ℂ, 0 < z.im → 0 < (x.w z).im := by
  rcases x.w_halfPlane_dichotomy with ⟨hpos, -⟩ | ⟨hneg, -⟩
  · exact hpos
  · exfalso
    have hOP : OrientationPreservingHomeo x.w := x.w_isQCAnalytic.1
    have hhom : IsHomeomorph x.w := hOP.1
    have hcont : Continuous x.w := hhom.continuous
    have hinj : Function.Injective x.w := hhom.injective
    -- the lower half plane goes up
    have hneg' : ∀ z : ℂ, z.im < 0 → 0 < (x.w z).im := by
      intro z hz
      have h1 : 0 < (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        linarith
      have h2 : (x.w (starRingEnd ℂ z)).im < 0 := hneg _ h1
      rw [x.w_conj z, Complex.conj_im] at h2
      linarith
    -- winding-number extensionality helper
    have hwn_ext : ∀ (A B : C(unitInterval, ℂ)) (q : ℂ), (∀ t, A t = B t) →
        windingNumber A q = windingNumber B q := by
      intro A B q hAB
      rw [ContinuousMap.ext hAB]
    -- the packaged homeomorphism and its plane chart
    set W : ℂ ≃ₜ ℂ := hhom.homeomorph x.w
    set E : OpenPartialHomeomorph ℂ ℂ := W.toOpenPartialHomeomorph
    have hEsrc : E.source = Set.univ := Homeomorph.toOpenPartialHomeomorph_source W
    -- the self-charted plane has an oriented atlas
    have hatlas : HasOrientedAtlas ℂ := by
      intro e1 he1 e2 he2 z hz
      rw [chartedSpaceSelf_atlas] at he1 he2
      subst he1
      subst he2
      have hEq : Set.EqOn
          ((OpenPartialHomeomorph.refl ℂ).symm.trans (OpenPartialHomeomorph.refl ℂ)) id
          Set.univ := fun w _ => rfl
      have hsrc : ((OpenPartialHomeomorph.refl ℂ).symm.trans
          (OpenPartialHomeomorph.refl ℂ)).source = Set.univ := by
        simp
      exact isOrientationPreservingAt_id hEq isOpen_univ (Set.mem_univ z)
        (fun w _ => by rw [hsrc]; trivial)
    -- source of the chart representatives
    have hhsrc : ∀ p : ℂ, (homeoChartRep W p).source = Set.univ := by
      intro p
      unfold homeoChartRep
      rw [chartAt_self_eq]
      simp [Homeomorph.toOpenPartialHomeomorph_source]
    -- a point of differentiability with positive Jacobian
    obtain ⟨z₀, hdet⟩ := hOP.2.exists
    have hdiff : DifferentiableAt ℝ x.w z₀ := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
      simp [ContinuousLinearMap.det] at hdet
    -- a positive radius whose image circle admits a `+2πi` logarithm lift
    have hev := (windingOne_iff_det_pos hcont hdiff (ne_of_gt hdet)).mpr hdet
    have hev' : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ((∃ L : ℝ → ℂ, Continuous L ∧
          (∀ θ : ℝ, Complex.exp (L θ)
            = x.w (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - x.w z₀) ∧
          L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I) ∧ 0 < r) :=
      hev.and (eventually_mem_nhdsWithin.mono fun r hr => hr)
    obtain ⟨r₀, ⟨L₀, hL₀c, hL₀e, hL₀incr⟩, hr₀pos⟩ := hev'.exists
    -- the image circle of radius `r₀` about `z₀` as a loop
    have hγ₀cont : Continuous fun t : unitInterval => x.w (circleLoop z₀ r₀ t) :=
      hcont.comp (circleLoop z₀ r₀).continuous
    set γ₀ : C(unitInterval, ℂ) :=
      ⟨fun t => x.w (circleLoop z₀ r₀ t), hγ₀cont⟩
    have hcircν : ∀ t : unitInterval, circleLoop z₀ r₀ t
        = z₀ + (r₀ : ℝ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := fun t => rfl
    have hγ₀cl : γ₀ 0 = γ₀ 1 := by
      change x.w (circleLoop z₀ r₀ 0) = x.w (circleLoop z₀ r₀ 1)
      rw [hcircν 0, hcircν 1]
      norm_num [Complex.exp_two_pi_mul_I]
    have hγ₀ne : ∀ t : unitInterval, γ₀ t ≠ x.w z₀ := by
      intro t heq
      have h1 : circleLoop z₀ r₀ t = z₀ := hinj heq
      rw [hcircν t] at h1
      have h2 : (r₀ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact (ne_of_gt hr₀pos) (Complex.ofReal_eq_zero.mp h3)
      · exact Complex.exp_ne_zero _ h3
    -- the `[0, 2π]` lift reparametrized over the unit interval
    have hMcont : Continuous fun t : unitInterval => L₀ (2 * Real.pi * (t : ℝ)) :=
      hL₀c.comp (continuous_const.mul continuous_subtype_val)
    set M : C(unitInterval, ℂ) :=
      ⟨fun t => L₀ (2 * Real.pi * (t : ℝ)), hMcont⟩
    have hM : IsLogLiftOf M (shiftedCurve γ₀ (x.w z₀)) := by
      intro t
      have hs : shiftedCurve γ₀ (x.w z₀) t = γ₀ t - x.w z₀ := by
        simp [shiftedCurve]
      change Complex.exp (L₀ (2 * Real.pi * (t : ℝ))) = shiftedCurve γ₀ (x.w z₀) t
      rw [hs, hL₀e (2 * Real.pi * (t : ℝ))]
      have harg : ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I
          = 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ) := by
        push_cast
        ring
      have hpt : z₀ + (r₀ : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
          = circleLoop z₀ r₀ t := by
        rw [hcircν t, harg]
      rw [hpt]
      rfl
    -- the winding number of the image circle about the image centre is one
    have hspec₀ := windingNumber_spec hγ₀cl hγ₀ne hM
    have hM1 : M 1 = L₀ (2 * Real.pi) := by
      change L₀ (2 * Real.pi * (((1 : unitInterval) : ℝ))) = L₀ (2 * Real.pi)
      norm_num
    have hM0 : M 0 = L₀ 0 := by
      change L₀ (2 * Real.pi * (((0 : unitInterval) : ℝ))) = L₀ 0
      norm_num
    rw [hM1, hM0, hL₀incr] at hspec₀
    have hwn₀ : windingNumber γ₀ (x.w z₀) = 1 := by
      have h2ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : ((windingNumber γ₀ (x.w z₀) : ℤ) : ℂ) = 1 := by
        field_simp at hspec₀
        exact_mod_cast hspec₀.symm
      exact_mod_cast h3
    -- orientation preservation at `z₀`, hence at the chart representative
    have hsub₀ : Metric.closedBall z₀ r₀ ⊆ E.source := by
      rw [hEsrc]
      exact Set.subset_univ _
    have hOPz₀ : IsOrientationPreservingAt E z₀ := by
      refine ⟨r₀, hr₀pos, hsub₀, ?_⟩
      unfold windingDegreeAt
      exact Eq.trans (hwn_ext _ γ₀ (x.w z₀) fun t => rfl) hwn₀
    have hchart : IsOrientationPreservingAt (homeoChartRep W z₀) (chartAt ℂ z₀ z₀) := by
      have hEq : Set.EqOn (⇑E) (⇑(homeoChartRep W z₀)) Set.univ := fun w _ => rfl
      exact (isOrientationPreservingAt_congr hEq isOpen_univ (Set.mem_univ z₀)
        (fun w _ => by rw [hEsrc]; trivial)
        (fun w _ => by rw [hhsrc z₀]; trivial)).mp hOPz₀
    -- global propagation to the origin
    have hglob := isOrientationPreserving_of_isOrientationPreservingAt_point hatlas W z₀ hchart
    have h0 : IsOrientationPreservingAt E 0 := by
      have hEq : Set.EqOn (⇑(homeoChartRep W 0)) (⇑E) Set.univ := fun w _ => rfl
      exact (isOrientationPreservingAt_congr hEq isOpen_univ (Set.mem_univ 0)
        (fun w _ => by rw [hhsrc 0]; trivial)
        (fun w _ => by rw [hEsrc]; trivial)).mp (hglob 0)
    -- the unit circle about the origin
    have hγcont : Continuous fun t : unitInterval => x.w (circleLoop 0 1 t) :=
      hcont.comp (circleLoop 0 1).continuous
    set γ : C(unitInterval, ℂ) := ⟨fun t => x.w (circleLoop 0 1 t), hγcont⟩
    have hcirc : ∀ t : unitInterval, circleLoop 0 1 t
        = Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      intro t
      have h : circleLoop 0 1 t
          = 0 + ((1 : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [h]
      norm_num
    have him : ∀ t : unitInterval,
        (circleLoop 0 1 t).im = Real.sin (2 * Real.pi * (t : ℝ)) := by
      intro t
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)
          = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hcirc t, harg, Complex.exp_ofReal_mul_I_im]
    have hc0 : circleLoop 0 1 0 = 1 := by
      rw [hcirc 0]
      norm_num
    have hc1 : circleLoop 0 1 1 = 1 := by
      rw [hcirc 1]
      have h1 : (((1 : unitInterval) : ℝ) : ℂ) = 1 := by norm_num
      rw [h1, mul_one, Complex.exp_two_pi_mul_I]
    have hγcl : γ 0 = γ 1 := by
      change x.w (circleLoop 0 1 0) = x.w (circleLoop 0 1 1)
      rw [hc0, hc1]
    have hγne : ∀ t : unitInterval, γ t ≠ 0 := by
      intro t heq
      have h0' : x.w (circleLoop 0 1 t) = x.w 0 := by
        change x.w (circleLoop 0 1 t) = _ at heq
        rw [heq, x.w_zero]
      have h1 := hinj h0'
      rw [hcirc t] at h1
      exact Complex.exp_ne_zero _ h1
    -- the winding number of the image unit circle about the origin is one
    have hsub1 : Metric.closedBall (0 : ℂ) 1 ⊆ E.source := by
      rw [hEsrc]
      exact Set.subset_univ _
    have hdeg1 := ((isOrientationPreservingAt_iff_forall E 0).mp h0).2 1 one_pos hsub1
    have hwn1 : windingNumber γ (x.w 0) = 1 := by
      rw [← hdeg1]
      unfold windingDegreeAt
      exact (hwn_ext _ γ (x.w 0) fun t => rfl).symm
    rw [x.w_zero] at hwn1
    -- logarithm lift of the image unit circle
    have hδ : ∀ t : unitInterval, shiftedCurve γ 0 t ≠ 0 := by
      intro t
      have hs : shiftedCurve γ 0 t = γ t - 0 := by
        simp [shiftedCurve]
      rw [hs, sub_zero]
      exact hγne t
    obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ 0) hδ
    have hLt : ∀ t : unitInterval, Complex.exp (L t) = γ t := by
      intro t
      rw [hL t]
      simp [shiftedCurve]
    have him_eq : ∀ t : unitInterval,
        (γ t).im = Real.exp ((L t).re) * Real.sin ((L t).im) := by
      intro t
      rw [← hLt t, Complex.exp_im]
    -- the lift starts on `2πiℤ` since the curve starts at `1`
    have hγ0 : γ 0 = 1 := by
      change x.w (circleLoop 0 1 0) = 1
      rw [hc0]
      exact x.w_one
    have hexpL0 : Complex.exp (L 0) = 1 := (hLt 0).trans hγ0
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexpL0
    have hL0im : (L 0).im = 2 * Real.pi * (k : ℝ) := by
      rw [hk]
      simp [Complex.mul_im, Complex.mul_re]
      ring
    -- the lift increment is `+2πi`
    have hspecγ := windingNumber_spec hγcl hγne hL
    rw [hwn1] at hspecγ
    have hL1im : (L 1).im = 2 * Real.pi * (k : ℝ) + 2 * Real.pi := by
      have h := congrArg Complex.im hspecγ
      simp [Complex.sub_im, Complex.mul_im, Complex.mul_re] at h
      linarith [hL0im, h]
    -- the imaginary part of the lift as a real function
    set φ : ℝ → ℝ := fun s => (L (Set.projIcc (0 : ℝ) 1 zero_le_one s)).im with hφdef
    have hφcont : Continuous φ :=
      Complex.continuous_im.comp (L.continuous.comp continuous_projIcc)
    have hφIcc : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) 1), φ s = (L ⟨s, hs⟩).im := by
      intro s hs
      simp only [hφdef]
      rw [Set.projIcc_of_mem]
    have hφ0 : φ 0 = 2 * Real.pi * (k : ℝ) := by
      rw [hφIcc 0 ⟨le_rfl, zero_le_one⟩]
      exact hL0im
    have hφ1 : φ 1 = 2 * Real.pi * (k : ℝ) + 2 * Real.pi := by
      rw [hφIcc 1 ⟨zero_le_one, le_rfl⟩]
      exact hL1im
    have hπ := Real.pi_pos
    -- first intermediate value: the argument passes through `2πk + π`
    have hmid1 : 2 * Real.pi * (k : ℝ) + Real.pi ∈ Set.Icc (φ 0) (φ 1) := by
      rw [hφ0, hφ1]
      constructor <;> linarith
    obtain ⟨s, hsmem, hφs⟩ :=
      intermediate_value_Icc zero_le_one hφcont.continuousOn hmid1
    have hs0 : 0 < s := by
      rcases lt_or_eq_of_le hsmem.1 with h | h
      · exact h
      · exfalso
        rw [← h] at hφs
        rw [hφ0] at hφs
        linarith
    have hs1 : s < 1 := by
      rcases lt_or_eq_of_le hsmem.2 with h | h
      · exact h
      · exfalso
        rw [h] at hφs
        rw [hφ1] at hφs
        linarith
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := hsmem
    -- at that parameter the image point is real
    have hLsim : (L ⟨s, hsIcc⟩).im = 2 * Real.pi * (k : ℝ) + Real.pi :=
      (hφIcc s hsIcc).symm.trans hφs
    have hsin0 : Real.sin (2 * Real.pi * (k : ℝ) + Real.pi) = 0 := by
      rw [add_comm, mul_comm (2 * Real.pi) (k : ℝ)]
      rw [show (k : ℝ) * (2 * Real.pi) = (k : ℤ) * (2 * Real.pi) by norm_num]
      rw [Real.sin_add_int_mul_two_pi, Real.sin_pi]
    have hγsim : (γ ⟨s, hsIcc⟩).im = 0 := by
      rw [him_eq ⟨s, hsIcc⟩, hLsim, hsin0, mul_zero]
    -- the circle parameter is forced to `1/2`
    have hs_half : s = 1 / 2 := by
      rcases lt_trichotomy (Real.sin (2 * Real.pi * s)) 0 with hlt | heq0 | hgt
      · exfalso
        have h1 : (circleLoop 0 1 ⟨s, hsIcc⟩).im < 0 := by
          rw [him ⟨s, hsIcc⟩]
          exact hlt
        have h2 := hneg' _ h1
        have h3 : 0 < (γ ⟨s, hsIcc⟩).im := h2
        linarith [hγsim]
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp heq0
        have hn' : (n : ℝ) * Real.pi = 2 * s * Real.pi := by
          rw [hn]
          ring
        have hn2 : (n : ℝ) = 2 * s := mul_right_cancel₀ (ne_of_gt hπ) hn'
        have hb1 : (0 : ℝ) < (n : ℝ) := by
          rw [hn2]
          linarith
        have hb2 : (n : ℝ) < 2 := by
          rw [hn2]
          linarith
        have hi1 : (0 : ℤ) < n := by exact_mod_cast hb1
        have hi2 : n < 2 := by exact_mod_cast hb2
        have hn1 : n = 1 := by omega
        rw [hn1] at hn2
        norm_num at hn2
        linarith
      · exfalso
        have h1 : 0 < (circleLoop 0 1 ⟨s, hsIcc⟩).im := by
          rw [him ⟨s, hsIcc⟩]
          exact hgt
        have h2 := hneg _ h1
        have h3 : (γ ⟨s, hsIcc⟩).im < 0 := h2
        linarith [hγsim]
    -- second intermediate value: the argument passes through `2πk + π/2` before `1/2`
    have hφhalf : φ (1 / 2) = 2 * Real.pi * (k : ℝ) + Real.pi := by
      rw [← hs_half]
      exact hφs
    have hmid2 : 2 * Real.pi * (k : ℝ) + Real.pi / 2 ∈ Set.Icc (φ 0) (φ (1 / 2)) := by
      rw [hφ0, hφhalf]
      constructor <;> linarith
    obtain ⟨s', hs'mem, hφs'⟩ :=
      intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hφcont.continuousOn hmid2
    have hs'0 : 0 < s' := by
      rcases lt_or_eq_of_le hs'mem.1 with h | h
      · exact h
      · exfalso
        rw [← h] at hφs'
        rw [hφ0] at hφs'
        linarith
    have hs'half : s' < 1 / 2 := by
      rcases lt_or_eq_of_le hs'mem.2 with h | h
      · exact h
      · exfalso
        rw [h] at hφs'
        rw [hφhalf] at hφs'
        linarith
    have hs'Icc : s' ∈ Set.Icc (0 : ℝ) 1 := ⟨hs'mem.1, by linarith⟩
    have hLs'im : (L ⟨s', hs'Icc⟩).im = 2 * Real.pi * (k : ℝ) + Real.pi / 2 := by
      have h := hφIcc s' hs'Icc
      rw [← h]
      exact hφs'
    have hsin1 : Real.sin (2 * Real.pi * (k : ℝ) + Real.pi / 2) = 1 := by
      rw [add_comm, mul_comm (2 * Real.pi) (k : ℝ)]
      rw [show (k : ℝ) * (2 * Real.pi) = (k : ℤ) * (2 * Real.pi) by norm_num]
      rw [Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
    -- the contradiction: the image of an upper point has positive imaginary part
    have h1 : 0 < (circleLoop 0 1 ⟨s', hs'Icc⟩).im := by
      rw [him ⟨s', hs'Icc⟩]
      exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    have h2 := hneg _ h1
    have h3 : (γ ⟨s', hs'Icc⟩).im < 0 := h2
    have h4 : (γ ⟨s', hs'Icc⟩).im = Real.exp ((L ⟨s', hs'Icc⟩).re) := by
      rw [him_eq ⟨s', hs'Icc⟩, hLs'im, hsin1, mul_one]
    have h5 := Real.exp_pos ((L ⟨s', hs'Icc⟩).re)
    rw [h4] at h3
    linarith

/-! ## The conjugated Fuchsian group -/

/-- The Fuchsian group of a Teichmüller representative: the image of `Γ₀` under conjugation
by the normalized solution `x.w`. -/
noncomputable def TeichRep.group (x : TeichRep Γ₀) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  fuchsianImage Γ₀ x.w x.w_injective

/-- Every `γ ∈ Γ₀` has a Möbius conjugator in `x.group`: the equivariance theorem applied to
the invariance clause of the representative. -/
theorem TeichRep.mem_group_of (x : TeichRep Γ₀)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) :
    ∃ W ∈ x.group, ∀ᵐ z : ℂ, x.w (moebiusMap γ z) = moebiusMap W (x.w z) := by
  obtain ⟨W, hW⟩ := exists_sl2_equivariant x.w_isQCAnalytic x.w_zero x.w_one x.w_conj γ
    (x.inv γ hγ)
  have haePole : ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact volume_moebiusDenom_zero γ
  have hae : ∀ᵐ z : ℂ, x.w (moebiusMap γ z) = moebiusMap W (x.w z) := by
    filter_upwards [haePole] with z hz
    exact hW z hz
  exact ⟨W, mem_fuchsianImage_of_equivariant x.w_injective hγ hae, hae⟩

/-- The conjugated group is Fuchsian. -/
theorem TeichRep.isFuchsian_group (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (x : TeichRep Γ₀) : IsFuchsianGroup x.group := by
  have _ := hfree
  exact fuchsianImage_isFuchsianGroup hΓ₀ x.w_isQCAnalytic x.w_zero x.w_one x.w_conj x.inv

/-- Freeness of the conjugated group: elements with a fixed point act as the identity. -/
theorem TeichRep.group_free
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (x : TeichRep Γ₀) :
    ∀ W : x.group, (∃ τ : UpperHalfPlane, W • τ = τ) →
      ∀ τ' : UpperHalfPlane, W • τ' = τ' := by
  exact fuchsianImage_free hfree x.w_isQCAnalytic x.w_zero x.w_one x.w_conj x.inv

/-- Cocompactness of the conjugated group. -/
theorem TeichRep.group_cocompact
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (x : TeichRep Γ₀) :
    CompactSpace (Quotient (MulAction.orbitRel x.group UpperHalfPlane)) := by
  exact fuchsianImage_cocompact hcc x.w_isQCAnalytic x.w_zero x.w_one x.w_conj x.inv

/-- Membership in the conjugated group is detected on the real line: `W ∈ x.group` iff the
conjugation identity holds at every non-pole real point for some `γ ∈ Γ₀`. -/
theorem TeichRep.mem_group_iff_boundary (x : TeichRep Γ₀)
    (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    W ∈ x.group ↔ ∃ γ ∈ Γ₀, ∀ t : ℝ, moebiusDenom γ (t : ℂ) ≠ 0 →
      x.w (moebiusMap γ (t : ℂ)) = moebiusMap W (x.w (t : ℂ)) := by
  have hfc : Continuous x.w := x.w_isQCAnalytic.1.1.continuous
  have him0 : ∀ z : ℂ, 0 < z.im → (x.w z).im ≠ 0 := by
    rcases x.w_halfPlane_dichotomy with ⟨hpos, _⟩ | ⟨hneg, _⟩
    · exact fun z hz => ne_of_gt (hpos z hz)
    · exact fun z hz => ne_of_lt (hneg z hz)
  constructor
  · intro hW
    have hmem : W ∈ fuchsianImageCarrier Γ₀ x.w := hW
    obtain ⟨γ, hγ, hae⟩ := hmem
    refine ⟨γ, hγ, ?_⟩
    intro t ht
    -- the a.e. conjugation identity upgrades to everywhere on the open upper half plane
    have hupg : ∀ z : ℂ, 0 < z.im → x.w (moebiusMap γ z) = moebiusMap W (x.w z) := by
      intro z hz
      have hUopen : IsOpen {w : ℂ | 0 < w.im} :=
        isOpen_lt continuous_const Complex.continuous_im
      have h1 : ContinuousOn (fun w => x.w (moebiusMap γ w)) {w : ℂ | 0 < w.im} := by
        intro w hw
        have hd := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hw)
        exact (hfc.continuousAt.comp
          (hasDerivAt_moebiusMap γ hd).continuousAt).continuousWithinAt
      have h2 : ContinuousOn (fun w => moebiusMap W (x.w w)) {w : ℂ | 0 < w.im} := by
        intro w hw
        have hd := moebiusDenom_ne_zero_of_im_ne_zero W (him0 w hw)
        exact ((hasDerivAt_moebiusMap W hd).continuousAt.comp
          hfc.continuousAt).continuousWithinAt
      have heq : Set.EqOn (fun w => x.w (moebiusMap γ w)) (fun w => moebiusMap W (x.w w))
          {w : ℂ | 0 < w.im} := by
        refine Measure.eqOn_of_ae_eq (ae_restrict_of_ae hae) h1 h2 ?_
        rw [hUopen.interior_eq]
        exact subset_closure
      exact heq hz
    -- the real point lies in the closure of the upper half plane
    have hTcl : (t : ℂ) ∈ closure {z : ℂ | 0 < z.im} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(t : ℂ) + Complex.I * ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, one_mul, zero_add, mul_zero]
        linarith
      · rw [dist_eq_norm]
        have hsub : (t : ℂ) - ((t : ℂ) + Complex.I * ((ε / 2 : ℝ) : ℂ))
            = -(Complex.I * ((ε / 2 : ℝ) : ℂ)) := by ring
        rw [hsub, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
    have hNB : (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hTcl
    haveI := hNB
    have hLc : ContinuousAt (fun z : ℂ => x.w (moebiusMap γ z)) (t : ℂ) :=
      hfc.continuousAt.comp (hasDerivAt_moebiusMap γ ht).continuousAt
    have hL : Filter.Tendsto (fun z : ℂ => x.w (moebiusMap γ z))
        (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds (x.w (moebiusMap γ (t : ℂ)))) :=
      hLc.continuousWithinAt
    have hEq : (fun z : ℂ => x.w (moebiusMap γ z))
        =ᶠ[nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}] fun z : ℂ => moebiusMap W (x.w z) :=
      eventually_nhdsWithin_of_forall fun z hz => hupg z hz
    have hR : Filter.Tendsto (fun z : ℂ => moebiusMap W (x.w z))
        (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds (x.w (moebiusMap γ (t : ℂ)))) :=
      Filter.Tendsto.congr' hEq hL
    -- the image of the real point avoids the pole of `W`
    have hWden : moebiusDenom W (x.w (t : ℂ)) ≠ 0 := by
      intro h0
      have hdenC : Continuous (moebiusDenom W) := by
        unfold moebiusDenom
        fun_prop
      have hden0 : Filter.Tendsto (fun z : ℂ => moebiusDenom W (x.w z))
          (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds 0) := by
        have hc : Continuous fun z : ℂ => moebiusDenom W (x.w z) := hdenC.comp hfc
        have ht0 : Filter.Tendsto (fun z : ℂ => moebiusDenom W (x.w z))
            (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
            (nhds (moebiusDenom W (x.w (t : ℂ)))) :=
          (hc.tendsto (t : ℂ)).mono_left nhdsWithin_le_nhds
        rwa [h0] at ht0
      have hnumC : Continuous fun z : ℂ => (W 0 0 : ℂ) * x.w z + (W 0 1 : ℂ) :=
        (continuous_const.mul hfc).add continuous_const
      have hnum : Filter.Tendsto (fun z : ℂ => (W 0 0 : ℂ) * x.w z + (W 0 1 : ℂ))
          (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
          (nhds ((W 0 0 : ℂ) * x.w (t : ℂ) + (W 0 1 : ℂ))) :=
        (hnumC.tendsto (t : ℂ)).mono_left nhdsWithin_le_nhds
      have hEq2 : (fun z : ℂ => moebiusMap W (x.w z) * moebiusDenom W (x.w z))
          =ᶠ[nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}]
            fun z : ℂ => (W 0 0 : ℂ) * x.w z + (W 0 1 : ℂ) :=
        eventually_nhdsWithin_of_forall fun z hz => by
          have hdz : moebiusDenom W (x.w z) ≠ 0 :=
            moebiusDenom_ne_zero_of_im_ne_zero W (him0 z hz)
          simp only [moebiusMap]
          exact div_mul_cancel₀ _ hdz
      have hnum' : Filter.Tendsto (fun z : ℂ => (W 0 0 : ℂ) * x.w z + (W 0 1 : ℂ))
          (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
          (nhds (x.w (moebiusMap γ (t : ℂ)) * 0)) :=
        Filter.Tendsto.congr' hEq2 (hR.mul hden0)
      have hlim := tendsto_nhds_unique hnum hnum'
      rw [mul_zero] at hlim
      have hdet : W 0 0 * W 1 1 - W 0 1 * W 1 0 = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe W
        rwa [Matrix.det_fin_two] at h
      have hdetC : (W 0 0 : ℂ) * (W 1 1 : ℂ) - (W 0 1 : ℂ) * (W 1 0 : ℂ) = 1 := by
        exact_mod_cast hdet
      have h0' : (W 1 0 : ℂ) * x.w (t : ℂ) + (W 1 1 : ℂ) = 0 := h0
      have hcontra : (1 : ℂ) = 0 := by
        linear_combination (W 0 0 : ℂ) * h0' - (W 1 0 : ℂ) * hlim - hdetC
      exact one_ne_zero hcontra
    -- pass to the limit from the upper half plane
    have hRc : ContinuousAt (fun z : ℂ => moebiusMap W (x.w z)) (t : ℂ) :=
      (hasDerivAt_moebiusMap W hWden).continuousAt.comp hfc.continuousAt
    have hR2 : Filter.Tendsto (fun z : ℂ => moebiusMap W (x.w z))
        (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds (moebiusMap W (x.w (t : ℂ)))) :=
      hRc.continuousWithinAt
    exact tendsto_nhds_unique hR hR2
  · rintro ⟨γ, hγ, hbd⟩
    obtain ⟨W', hW'⟩ := exists_sl2_equivariant x.w_isQCAnalytic x.w_zero x.w_one x.w_conj γ
      (x.inv γ hγ)
    have haePole : ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      exact volume_moebiusDenom_zero γ
    have haeW' : ∀ᵐ z : ℂ, x.w (moebiusMap γ z) = moebiusMap W' (x.w z) := by
      filter_upwards [haePole] with z hz
      exact hW' z hz
    have hW'mem : W' ∈ x.group :=
      mem_fuchsianImage_of_equivariant x.w_injective hγ haeW'
    -- the pole set of a real Möbius map is a subsingleton
    have hpoleSub : ∀ V : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        Set.Subsingleton {u : ℂ | moebiusDenom V u = 0} := by
      intro V w₁ hw₁ w₂ hw₂
      have h₁' : (V 1 0 : ℂ) * w₁ + (V 1 1 : ℂ) = 0 := hw₁
      have h₂' : (V 1 0 : ℂ) * w₂ + (V 1 1 : ℂ) = 0 := hw₂
      by_cases hc : V 1 0 = 0
      · exfalso
        have hdet : V 0 0 * V 1 1 - V 0 1 * V 1 0 = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe V
          rwa [Matrix.det_fin_two] at h
        have hcC : ((V 1 0 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
        rw [hcC, zero_mul, zero_add] at h₁'
        have hd : V 1 1 = 0 := by exact_mod_cast h₁'
        rw [hc, hd] at hdet
        simp at hdet
      · have hcC : ((V 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
        have hmul : (V 1 0 : ℂ) * w₁ = (V 1 0 : ℂ) * w₂ := by
          linear_combination h₁' - h₂'
        exact mul_left_cancel₀ hcC hmul
    have hwinj : Function.Injective fun s : ℝ => x.w (s : ℂ) := by
      intro s₁ s₂ hs
      exact Complex.ofReal_injective (x.w_injective hs)
    -- at most three real points are excluded; pick three good ones
    have hB1 : ({s : ℝ | moebiusDenom γ (s : ℂ) = 0}).Finite :=
      Set.Subsingleton.finite ((hpoleSub γ).preimage Complex.ofReal_injective)
    have hB2 : ({s : ℝ | moebiusDenom W (x.w (s : ℂ)) = 0}).Finite :=
      Set.Subsingleton.finite ((hpoleSub W).preimage hwinj)
    have hB3 : ({s : ℝ | moebiusDenom W' (x.w (s : ℂ)) = 0}).Finite :=
      Set.Subsingleton.finite ((hpoleSub W').preimage hwinj)
    have hBfin : ({s : ℝ | moebiusDenom γ (s : ℂ) = 0}
        ∪ {s : ℝ | moebiusDenom W (x.w (s : ℂ)) = 0}
        ∪ {s : ℝ | moebiusDenom W' (x.w (s : ℂ)) = 0}).Finite :=
      (hB1.union hB2).union hB3
    have hsplit : ∀ s : ℝ, s ∈ ({s : ℝ | moebiusDenom γ (s : ℂ) = 0}
        ∪ {s : ℝ | moebiusDenom W (x.w (s : ℂ)) = 0}
        ∪ {s : ℝ | moebiusDenom W' (x.w (s : ℂ)) = 0})ᶜ →
        moebiusDenom γ (s : ℂ) ≠ 0 ∧ moebiusDenom W (x.w (s : ℂ)) ≠ 0
          ∧ moebiusDenom W' (x.w (s : ℂ)) ≠ 0 := by
      intro s hs
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hs
      exact ⟨hs.1.1, hs.1.2, hs.2⟩
    have hBc := hBfin.infinite_compl
    obtain ⟨t₁, ht₁⟩ := hBc.nonempty
    obtain ⟨t₂, ht₂⟩ := (hBc.diff (Set.finite_singleton t₁)).nonempty
    obtain ⟨t₃, ht₃⟩ := (hBc.diff ((Set.finite_singleton t₂).insert t₁)).nonempty
    obtain ⟨hd1, hdW1, hdW'1⟩ := hsplit t₁ ht₁
    obtain ⟨hd2, hdW2, hdW'2⟩ := hsplit t₂ ht₂.1
    obtain ⟨hd3, hdW3, hdW'3⟩ := hsplit t₃ ht₃.1
    have ht21 : t₂ ≠ t₁ := fun hEq => ht₂.2 hEq
    have ht31 : t₃ ≠ t₁ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inl hEq))
    have ht32 : t₃ ≠ t₂ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inr hEq))
    have hz12 : x.w (t₁ : ℂ) ≠ x.w (t₂ : ℂ) := fun hEq =>
      ht21 (Complex.ofReal_injective (x.w_injective hEq)).symm
    have hz13 : x.w (t₁ : ℂ) ≠ x.w (t₃ : ℂ) := fun hEq =>
      ht31 (Complex.ofReal_injective (x.w_injective hEq)).symm
    have hz23 : x.w (t₂ : ℂ) ≠ x.w (t₃ : ℂ) := fun hEq =>
      ht32 (Complex.ofReal_injective (x.w_injective hEq)).symm
    have hVden : ∀ z ∈ ({x.w (t₁ : ℂ), x.w (t₂ : ℂ), x.w (t₃ : ℂ)} : Set ℂ),
        moebiusDenom W z ≠ 0 := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hdW1
      · exact hdW2
      · exact hdW3
    have hW'den : ∀ z ∈ ({x.w (t₁ : ℂ), x.w (t₂ : ℂ), x.w (t₃ : ℂ)} : Set ℂ),
        moebiusDenom W' z ≠ 0 := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hdW'1
      · exact hdW'2
      · exact hdW'3
    have hagree : ∀ z ∈ ({x.w (t₁ : ℂ), x.w (t₂ : ℂ), x.w (t₃ : ℂ)} : Set ℂ),
        moebiusMap W z = moebiusMap W' z := by
      have hkey : ∀ s : ℝ, moebiusDenom γ (s : ℂ) ≠ 0 →
          moebiusMap W (x.w (s : ℂ)) = moebiusMap W' (x.w (s : ℂ)) := by
        intro s hd
        rw [← hbd s hd]
        exact hW' (s : ℂ) hd
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hkey t₁ hd1
      · exact hkey t₂ hd2
      · exact hkey t₃ hd3
    rcases moebius_ext_three hz12 hz13 hz23 hVden hW'den hagree with heq | hneg
    · have hWW' : W = W' := Subtype.ext heq
      rw [hWW']
      exact hW'mem
    · exact neg_mem_fuchsianImage x.w_injective hW'mem hneg

/-- Representatives with the same boundary map have the same conjugated group. -/
theorem TeichRep.group_eq_of_boundary_eq {x y : TeichRep Γ₀}
    (h : x.boundary = y.boundary) : x.group = y.group := by
  have hwr : ∀ t : ℝ, x.w (t : ℂ) = y.w (t : ℂ) := by
    intro t
    rw [x.w_ofReal t, y.w_ofReal t, h]
  have htrans : ∀ u v : TeichRep Γ₀, (∀ t : ℝ, u.w (t : ℂ) = v.w (t : ℂ)) →
      ∀ W γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∀ t : ℝ, moebiusDenom γ (t : ℂ) ≠ 0 →
          u.w (moebiusMap γ (t : ℂ)) = moebiusMap W (u.w (t : ℂ))) →
        ∀ t : ℝ, moebiusDenom γ (t : ℂ) ≠ 0 →
          v.w (moebiusMap γ (t : ℂ)) = moebiusMap W (v.w (t : ℂ)) := by
    intro u v huv W γ hbd t ht
    have him : (moebiusMap γ (t : ℂ)).im = 0 :=
      moebiusMap_im_eq_zero γ (by simp) ht
    have hreal : (((moebiusMap γ (t : ℂ)).re : ℝ) : ℂ) = moebiusMap γ (t : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    have h1 : v.w (moebiusMap γ (t : ℂ)) = u.w (moebiusMap γ (t : ℂ)) := by
      rw [← hreal, huv (moebiusMap γ (t : ℂ)).re]
    rw [h1, hbd t ht, huv t]
  ext W
  rw [TeichRep.mem_group_iff_boundary x W, TeichRep.mem_group_iff_boundary y W]
  constructor
  · rintro ⟨γ, hγ, hbd⟩
    exact ⟨γ, hγ, htrans x y hwr W γ hbd⟩
  · rintro ⟨γ, hγ, hbd⟩
    exact ⟨γ, hγ, htrans y x (fun t => (hwr t).symm) W γ hbd⟩

end RiemannDynamics

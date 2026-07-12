import RiemannDynamics.Teichmuller.Equivariance

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
  sorry

/-- The conjugated group is Fuchsian. -/
theorem TeichRep.isFuchsian_group (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (x : TeichRep Γ₀) : IsFuchsianGroup x.group := by
  sorry

/-- Freeness of the conjugated group: elements with a fixed point act as the identity. -/
theorem TeichRep.group_free
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (x : TeichRep Γ₀) :
    ∀ W : x.group, (∃ τ : UpperHalfPlane, W • τ = τ) →
      ∀ τ' : UpperHalfPlane, W • τ' = τ' := by
  sorry

/-- Cocompactness of the conjugated group. -/
theorem TeichRep.group_cocompact
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (x : TeichRep Γ₀) :
    CompactSpace (Quotient (MulAction.orbitRel x.group UpperHalfPlane)) := by
  sorry

/-- Membership in the conjugated group is detected on the real line: `W ∈ x.group` iff the
conjugation identity holds at every non-pole real point for some `γ ∈ Γ₀`. -/
theorem TeichRep.mem_group_iff_boundary (x : TeichRep Γ₀)
    (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    W ∈ x.group ↔ ∃ γ ∈ Γ₀, ∀ t : ℝ, moebiusDenom γ (t : ℂ) ≠ 0 →
      x.w (moebiusMap γ (t : ℂ)) = moebiusMap W (x.w (t : ℂ)) := by
  sorry

/-- Representatives with the same boundary map have the same conjugated group. -/
theorem TeichRep.group_eq_of_boundary_eq {x y : TeichRep Γ₀}
    (h : x.boundary = y.boundary) : x.group = y.group := by
  sorry

end RiemannDynamics

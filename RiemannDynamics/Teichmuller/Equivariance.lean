import RiemannDynamics.Teichmuller.Beltrami
import RiemannDynamics.Uniformization.Fuchsian
import RiemannDynamics.QC.Calculus.Removability
import RiemannDynamics.QC.Calculus.Weyl
import RiemannDynamics.QC.GeometricToAnalytic.NondegeneracyAssembly

/-!
# Equivariance of normalized quasiconformal maps

For a normalized symmetric quasiconformal map `w` whose Beltrami coefficient is invariant
under `γ ∈ SL(2, ℝ)`, the composition `w ∘ γ` is again quasiconformal with the same
coefficient, so by uniqueness `w ∘ γ = W ∘ w` for an explicit real Möbius map `W`
(`exists_sl2_equivariant`). The two Bruhat cases are treated separately: affine `γ`
(lower-left entry zero) and the general case through the inversion transport
`inversionTransport`, which realizes conjugation of a quasiconformal plane map by `z ↦ -1/z`
as a genuine plane homeomorphism. The image group `fuchsianImage Γ₀ w` collects the Möbius
conjugators; proper discontinuity, freeness and cocompactness transport to it along the
induced homeomorphism of the upper half plane.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## Boundary behaviour of symmetric normalized solutions -/

/-- A conjugation-symmetric plane map sends real points to real points. -/
theorem realLine_im_eq_zero {f : ℂ → ℂ}
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) (t : ℝ) : (f t).im = 0 := by
  have h := hsym (t : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- The real trace of a normalized symmetric quasiconformal map is strictly increasing. -/
theorem realLine_strictMono {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) :
    StrictMono (fun t : ℝ => (f t).re) := by
  have hfc : Continuous f := hf.1.1.continuous
  have hcont : Continuous fun t : ℝ => (f t).re :=
    Complex.continuous_re.comp (hfc.comp Complex.continuous_ofReal)
  have hinj : Function.Injective fun t : ℝ => (f t).re := by
    intro s t hst
    have hs := realLine_im_eq_zero hsym s
    have ht := realLine_im_eq_zero hsym t
    have hfeq : f s = f t := Complex.ext hst (hs.trans ht.symm)
    have h2 := hf.injective hfeq
    exact_mod_cast h2
  rcases hcont.strictMono_of_inj hinj with h | h
  · exact h
  · exfalso
    have h01 := h (show (0 : ℝ) < 1 from zero_lt_one)
    have h01' : (f ((1 : ℝ) : ℂ)).re < (f ((0 : ℝ) : ℂ)).re := h01
    rw [Complex.ofReal_one, Complex.ofReal_zero, h0, h1] at h01'
    norm_num at h01'

/-- A symmetric quasiconformal plane map carries the real line onto the real line. -/
theorem image_realLine_eq {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) :
    f '' {z : ℂ | z.im = 0} = {z : ℂ | z.im = 0} := by
  apply Set.Subset.antisymm
  · rintro w ⟨z, hz, rfl⟩
    have hz' : z.im = 0 := hz
    have h := hsym z
    rw [Complex.conj_eq_iff_im.mpr hz'] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  · intro w hw
    have hw' : w.im = 0 := hw
    obtain ⟨z, rfl⟩ := hf.1.1.bijective.surjective w
    have h2 : f (starRingEnd ℂ z) = f z := by
      rw [hsym z]
      exact Complex.conj_eq_iff_im.mpr hw'
    exact ⟨z, Complex.conj_eq_iff_im.mp (hf.injective h2), rfl⟩

/-- A symmetric quasiconformal plane map either preserves the open upper half plane or maps
it onto the open lower half plane; in each case the image of the upper half plane is the
stated half plane. -/
theorem halfPlane_dichotomy {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) :
    ((∀ z : ℂ, 0 < z.im → 0 < (f z).im) ∧
        f '' {z : ℂ | 0 < z.im} = {z : ℂ | 0 < z.im}) ∨
      ((∀ z : ℂ, 0 < z.im → (f z).im < 0) ∧
        f '' {z : ℂ | 0 < z.im} = {z : ℂ | z.im < 0}) := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hLopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hdisj : Disjoint {z : ℂ | 0 < z.im} {z : ℂ | z.im < 0} := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : 0 < z.im := hz1
    have h2 : z.im < 0 := hz2
    linarith
  have himconn : IsPreconnected (f '' {z : ℂ | 0 < z.im}) :=
    ((convex_halfSpace_im_gt 0).isPreconnected).image f hf.1.1.continuous.continuousOn
  have hsub : f '' {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0} := by
    rintro w ⟨z, hz, rfl⟩
    have hz' : 0 < z.im := hz
    rcases lt_trichotomy (0 : ℝ) ((f z).im) with h | h | h
    · exact Or.inl h
    · exfalso
      have h2 : f (starRingEnd ℂ z) = f z := by
        rw [hsym z]
        exact Complex.conj_eq_iff_im.mpr h.symm
      have h3 := Complex.conj_eq_iff_im.mp (hf.injective h2)
      linarith
    · exact Or.inr h
  rcases himconn.subset_or_subset hUopen hLopen hdisj hsub with hU | hL
  · left
    have hfwd : ∀ z : ℂ, 0 < z.im → 0 < (f z).im := fun z hz => hU ⟨z, hz, rfl⟩
    refine ⟨hfwd, Set.Subset.antisymm hU fun w hw => ?_⟩
    have hw' : 0 < w.im := hw
    obtain ⟨z, rfl⟩ := hf.1.1.bijective.surjective w
    rcases lt_trichotomy (0 : ℝ) z.im with h | h | h
    · exact ⟨z, h, rfl⟩
    · exfalso
      have hzc : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr h.symm
      have h2 := hsym z
      rw [hzc] at h2
      have h3 := Complex.conj_eq_iff_im.mp h2.symm
      linarith
    · exfalso
      have hcj : 0 < (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        linarith
      have h4 := hfwd _ hcj
      rw [hsym z, Complex.conj_im] at h4
      linarith
  · right
    have hfwd : ∀ z : ℂ, 0 < z.im → (f z).im < 0 := fun z hz => hL ⟨z, hz, rfl⟩
    refine ⟨hfwd, Set.Subset.antisymm hL fun w hw => ?_⟩
    have hw' : w.im < 0 := hw
    obtain ⟨z, rfl⟩ := hf.1.1.bijective.surjective w
    rcases lt_trichotomy (0 : ℝ) z.im with h | h | h
    · exact ⟨z, h, rfl⟩
    · exfalso
      have hzc : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr h.symm
      have h2 := hsym z
      rw [hzc] at h2
      have h3 := Complex.conj_eq_iff_im.mp h2.symm
      linarith
    · exfalso
      have hcj : 0 < (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        linarith
      have h4 := hfwd _ hcj
      rw [hsym z, Complex.conj_im] at h4
      linarith

/-! ## Affine case -/

/-- Equivariance in the affine Bruhat case: if the lower-left entry of `γ` vanishes and the
coefficient of the normalized symmetric solution `f` is `γ`-invariant, then `f ∘ γ = W ∘ f`
everywhere for an explicit `W ∈ SL(2, ℝ)`. -/
theorem exists_sl2_equivariant_of_lowerLeft_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc0 : γ 1 0 = 0)
    (hinv : ∀ᵐ z : ℂ, b.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = b.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) :
    ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rw [hc0, mul_zero, sub_zero] at hdet
  have ha : γ 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have hd : γ 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  have hcne : ((γ 0 0 : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ha)
  have hmoeb : ∀ z : ℂ, moebiusMap γ z
      = affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) z := by
    intro z
    rw [affineMap_apply, moebiusMap_of_lowerLeft_zero γ hc0 z]
  have harg0 : affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) 0
      = ((γ 0 0 * γ 0 1 : ℝ) : ℂ) := by
    rw [affineMap_apply]
    push_cast
    ring
  have harg1 : affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) 1
      = ((γ 0 0 ^ 2 + γ 0 0 * γ 0 1 : ℝ) : ℂ) := by
    rw [affineMap_apply]
    push_cast
    ring
  have hμinv : ∀ᵐ z : ℂ, b.μ (moebiusMap γ z) = b.μ z := by
    have hd2 : ((γ 1 1 : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hd)
    filter_upwards [hinv] with z hz
    have hdenz : moebiusDenom γ z = (γ 1 1 : ℂ) := by
      simp [moebiusDenom, hc0]
    rw [hdenz, Complex.conj_ofReal] at hz
    exact mul_right_cancel₀ hd2 hz
  have hcoef : (b.pullbackAffine hcne ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))).μ =ᵐ[volume] b.μ := by
    have hcconj : starRingEnd ℂ ((γ 0 0 : ℂ) ^ 2) / (γ 0 0 : ℂ) ^ 2 = 1 := by
      rw [map_pow, Complex.conj_ofReal]
      exact div_self hcne
    filter_upwards [hμinv] with z hz
    change b.μ ((γ 0 0 : ℂ) ^ 2 * z + (γ 0 0 : ℂ) * (γ 0 1 : ℂ))
        * (starRingEnd ℂ ((γ 0 0 : ℂ) ^ 2) / (γ 0 0 : ℂ) ^ 2) = b.μ z
    rw [hcconj, mul_one, ← moebiusMap_of_lowerLeft_zero γ hc0 z]
    exact hz
  have hF : IsQCAnalytic (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) b :=
    (isQCAnalytic_comp_affine hf hcne ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))).congr_coeff hcoef
  have hmono := realLine_strictMono hf h0 h1 hsym
  obtain ⟨X₀, hX₀⟩ : ∃ X : ℂ, f ((γ 0 0 * γ 0 1 : ℝ) : ℂ) = X := ⟨_, rfl⟩
  obtain ⟨X₁, hX₁⟩ : ∃ X : ℂ, f ((γ 0 0 ^ 2 + γ 0 0 * γ 0 1 : ℝ) : ℂ) = X := ⟨_, rfl⟩
  have him₀ : X₀.im = 0 := by
    rw [← hX₀]
    exact realLine_im_eq_zero hsym (γ 0 0 * γ 0 1)
  have him₁ : X₁.im = 0 := by
    rw [← hX₁]
    exact realLine_im_eq_zero hsym (γ 0 0 ^ 2 + γ 0 0 * γ 0 1)
  have hre_lt : X₀.re < X₁.re := by
    rw [← hX₀, ← hX₁]
    have hlt : γ 0 0 * γ 0 1 < γ 0 0 ^ 2 + γ 0 0 * γ 0 1 := by
      have := pow_two_pos_of_ne_zero ha
      linarith
    exact hmono hlt
  have hne : X₁ - X₀ ≠ 0 := by
    rw [← hX₀, ← hX₁]
    refine sub_ne_zero.mpr fun hcontra => ?_
    have h2 := hf.injective hcontra
    rw [Complex.ofReal_inj] at h2
    have := pow_two_pos_of_ne_zero ha
    linarith
  have hb0 : (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) 0 = X₀ := by
    rw [Function.comp_apply, harg0, hX₀]
  have hb1 : (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) 1 = X₁ := by
    rw [Function.comp_apply, harg1, hX₁]
  have hq0 : (fun z => (X₁ - X₀)⁻¹ * (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2)
      ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) z + -((X₁ - X₀)⁻¹ * X₀)) 0 = 0 := by
    change (X₁ - X₀)⁻¹ * (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) 0
        + -((X₁ - X₀)⁻¹ * X₀) = 0
    rw [hb0]
    ring
  have hq1 : (fun z => (X₁ - X₀)⁻¹ * (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2)
      ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) z + -((X₁ - X₀)⁻¹ * X₀)) 1 = 1 := by
    change (X₁ - X₀)⁻¹ * (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) 1
        + -((X₁ - X₀)⁻¹ * X₀) = 1
    rw [hb1, show (X₁ - X₀)⁻¹ * X₁ + -((X₁ - X₀)⁻¹ * X₀) = (X₁ - X₀)⁻¹ * (X₁ - X₀) from by
      ring]
    exact inv_mul_cancel₀ hne
  have hqf : (fun z => (X₁ - X₀)⁻¹ * (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2)
      ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) z + -((X₁ - X₀)⁻¹ * X₀)) = f :=
    (mrmt_unique_normalized b).unique
      ⟨hF.affine_postcomp (inv_ne_zero hne) (-((X₁ - X₀)⁻¹ * X₀)), hq0, hq1⟩ ⟨hf, h0, h1⟩
  have hFz : ∀ z : ℂ,
      f (affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) z)
        = (X₁ - X₀) * f z + X₀ := by
    intro z
    have h := congrFun hqf z
    change (X₁ - X₀)⁻¹ * f (affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) z)
        + -((X₁ - X₀)⁻¹ * X₀) = f z at h
    have h2 : (X₁ - X₀) * ((X₁ - X₀)⁻¹ * f (affineMap ((γ 0 0 : ℂ) ^ 2)
        ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) z) + -((X₁ - X₀)⁻¹ * X₀)) + X₀
        = f (affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) z) := by
      linear_combination (f (affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ)) z) - X₀)
        * mul_inv_cancel₀ hne
    rw [← h2, h]
  have hαC : X₁ - X₀ = ((X₁.re - X₀.re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.ofReal_re]
    · rw [Complex.sub_im, him₁, him₀, Complex.ofReal_im, sub_zero]
  have hβC : X₀ = ((X₀.re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [him₀, Complex.ofReal_im]
  refine ⟨affineSL2 (X₁.re - X₀.re) X₀.re (sub_pos.mpr hre_lt), fun z => ?_⟩
  rw [moebiusMap_affineSL2 (sub_pos.mpr hre_lt) X₀.re (f z), hmoeb z, hFz z, ← hαC, ← hβC]

/-! ## Inversion transport -/

/-- Conjugation of a quasiconformal plane map `h` by the inversion `z ↦ -1/z`, renormalized
so that `0 ↦ 0`: the map `z ↦ (h(-1/z) - h(0))⁻¹` extended by `0 ↦ 0`. It is again a plane
homeomorphism, quasiconformal with the pulled-back coefficient. -/
noncomputable def inversionTransport (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (h (-1 / z) - h 0)⁻¹

/-- The inversion transport of a quasiconformal map is quasiconformal, with a coefficient of
no larger essential supremum satisfying the pullback law
`μ_G(z) z̄² = μ_h(-1/z) z²` almost everywhere. -/
theorem exists_isQCAnalytic_inversionTransport {h : ℂ → ℂ} {bh : BeltramiCoeff}
    (hh : IsQCAnalytic h bh) :
    ∃ bG : BeltramiCoeff, bG.normInf ≤ bh.normInf ∧
      IsQCAnalytic (inversionTransport h) bG ∧
      ∀ᵐ z : ℂ, bG.μ z * (starRingEnd ℂ z) ^ 2 = bh.μ (-1 / z) * z ^ 2 := by
  sorry

/-! ## General case via the Bruhat factorization -/

/-- Bruhat factorization in `SL(2, ℝ)`: a matrix with nonvanishing lower-left entry is a
product `A₁ · S · A₂` with `A₁, A₂` upper triangular and `S` the inversion, explicitly
`!![a, b; c, d] = !![1, a c⁻¹; 0, 1] · !![0, -1; 1, 0] · !![c, d; 0, c⁻¹]`. -/
theorem bruhat_factorization (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : γ 1 0 ≠ 0) :
    ∃ A₁ A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      A₁ 1 0 = 0 ∧ A₂ 1 0 = 0 ∧ γ = A₁ * inversionSL2 * A₂ := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hdetA₁ : (!![1, γ 0 0 * (γ 1 0)⁻¹; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    ring
  have hdetA₂ : (!![γ 1 0, γ 1 1; 0, (γ 1 0)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hc]
    ring
  refine ⟨⟨_, hdetA₁⟩, ⟨_, hdetA₂⟩, ?_, ?_, ?_⟩
  · simp
  · simp
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [inversionSL2, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
    · simp [inversionSL2, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      linear_combination -hdet
    · simp [inversionSL2, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [inversionSL2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Equivariance in the generic Bruhat case: if the lower-left entry of `γ` does not vanish
and the coefficient of the normalized symmetric solution `f` is `γ`-invariant, then
`f ∘ γ = W ∘ f` off the pole of `γ` for an explicit `W ∈ SL(2, ℝ)`. -/
theorem exists_sl2_equivariant_of_lowerLeft_ne_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : γ 1 0 ≠ 0)
    (hinv : ∀ᵐ z : ℂ, b.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = b.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) :
    ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, moebiusDenom γ z ≠ 0 → f (moebiusMap γ z) = moebiusMap W (f z) := by
  sorry

/-- **Equivariance of normalized solutions.** If the Beltrami coefficient of the normalized
symmetric quasiconformal map `f` is invariant under `γ ∈ SL(2, ℝ)`, then there is
`W ∈ SL(2, ℝ)` with `f (γ z) = W (f z)` at every non-pole point `z`. -/
theorem exists_sl2_equivariant {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hinv : ∀ᵐ z : ℂ, b.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = b.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) :
    ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, moebiusDenom γ z ≠ 0 → f (moebiusMap γ z) = moebiusMap W (f z) := by
  sorry

/-! ## The image group -/

/-- The carrier of the image group: matrices `W` that conjugate `f` against some `γ ∈ Γ₀`
almost everywhere, `f ∘ γ = W ∘ f` a.e. -/
def fuchsianImageCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (f : ℂ → ℂ) : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  {W | ∃ γ ∈ Γ₀, ∀ᵐ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z)}

/-- The identity matrix conjugates `f` against `γ = 1`. -/
theorem one_mem_fuchsianImageCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (f : ℂ → ℂ) : 1 ∈ fuchsianImageCarrier Γ₀ f := by
  sorry

/-- The image carrier of an injective map is closed under products: the two a.e. identities
compose along the Möbius cocycle, pulling null sets back through the smooth Möbius factors
and through point preimages of `f`. -/
theorem mul_mem_fuchsianImageCarrier {f : ℂ → ℂ} (hf : Function.Injective f)
    {W₁ W₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h₁ : W₁ ∈ fuchsianImageCarrier Γ₀ f)
    (h₂ : W₂ ∈ fuchsianImageCarrier Γ₀ f) : W₁ * W₂ ∈ fuchsianImageCarrier Γ₀ f := by
  sorry

/-- The image carrier of an injective map is closed under inverses. -/
theorem inv_mem_fuchsianImageCarrier {f : ℂ → ℂ} (hf : Function.Injective f)
    {W : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : W ∈ fuchsianImageCarrier Γ₀ f) :
    W⁻¹ ∈ fuchsianImageCarrier Γ₀ f := by
  sorry

/-- The **image group** of `Γ₀` under an injective plane map `f`: the subgroup of matrices
`W ∈ SL(2, ℝ)` with `f ∘ γ = W ∘ f` a.e. for some `γ ∈ Γ₀`. -/
def fuchsianImage (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (f : ℂ → ℂ)
    (hf : Function.Injective f) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) where
  carrier := fuchsianImageCarrier Γ₀ f
  one_mem' := one_mem_fuchsianImageCarrier Γ₀ f
  mul_mem' := fun h₁ h₂ => mul_mem_fuchsianImageCarrier hf h₁ h₂
  inv_mem' := fun h => inv_mem_fuchsianImageCarrier hf h

/-- Membership in the image group from an a.e. conjugation identity. -/
theorem mem_fuchsianImage_of_equivariant {f : ℂ → ℂ} (hf : Function.Injective f)
    {γ W : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀)
    (h : ∀ᵐ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z)) :
    W ∈ fuchsianImage Γ₀ f hf := by
  sorry

/-- The image group is closed under negation of the matrix: `moebiusMap (-W) = moebiusMap W`,
so the same `γ` witnesses membership. -/
theorem neg_mem_fuchsianImage {f : ℂ → ℂ} (hf : Function.Injective f)
    {W W' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hW : W ∈ fuchsianImage Γ₀ f hf)
    (h : (W' : Matrix (Fin 2) (Fin 2) ℝ) = -(W : Matrix (Fin 2) (Fin 2) ℝ)) :
    W' ∈ fuchsianImage Γ₀ f hf := by
  sorry

/-! ## Transport along the induced homeomorphism of the upper half plane -/

/-- The conjugating homeomorphism of the upper half plane induced by a symmetric
quasiconformal plane map: `f` restricted to the upper half plane when `f` preserves it, and
`conj ∘ f` otherwise; it intertwines every a.e. Möbius conjugation identity of `f` with the
corresponding actions on the upper half plane. -/
theorem exists_conjugating_upperHomeo {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) :
    ∃ e : UpperHalfPlane ≃ₜ UpperHalfPlane,
      ∀ γ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∀ᵐ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z)) →
        ∀ τ : UpperHalfPlane, e (γ • τ) = W • e τ := by
  sorry

/-- Proper discontinuity transports along an equivariant homeomorphism: given a relation
matching every element of `G'` to a partner in `G` intertwined by `e`, and a finite kernel of
the `G'`-action, proper discontinuity of the `G`-action yields that of the `G'`-action. -/
theorem properlyDiscontinuousSMul_of_equivariant_homeo {G G' T T' : Type*} [Group G]
    [Group G'] [TopologicalSpace T] [TopologicalSpace T'] [MulAction G T] [MulAction G' T']
    (e : T ≃ₜ T') (R : G → G' → Prop) (hR : ∀ g' : G', ∃ g : G, R g g')
    (hint : ∀ g g', R g g' → ∀ t : T, e (g • t) = g' • e t)
    (hker : {g' : G' | ∀ t' : T', g' • t' = t'}.Finite)
    (hG : ProperlyDiscontinuousSMul G T) : ProperlyDiscontinuousSMul G' T' := by
  sorry

/-- The image group of a Fuchsian group under a normalized symmetric quasiconformal map with
invariant coefficient is again Fuchsian. -/
theorem fuchsianImage_isFuchsianGroup (hΓ₀ : IsFuchsianGroup Γ₀) {f : ℂ → ℂ}
    {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hinv : IsInvariantBeltrami' Γ₀ b) :
    IsFuchsianGroup (fuchsianImage Γ₀ f hf.injective) := by
  sorry

/-- Freeness transports to the image group: an element of the image group with a fixed point
in the upper half plane acts as the identity. -/
theorem fuchsianImage_free
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hinv : IsInvariantBeltrami' Γ₀ b) :
    ∀ W : fuchsianImage Γ₀ f hf.injective,
      (∃ τ : UpperHalfPlane, W • τ = τ) → ∀ τ' : UpperHalfPlane, W • τ' = τ' := by
  sorry

/-- Cocompactness transports to the image group: the conjugating homeomorphism of the upper
half plane descends to a homeomorphism of the orbit spaces. -/
theorem fuchsianImage_cocompact
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hinv : IsInvariantBeltrami' Γ₀ b) :
    CompactSpace
      (Quotient (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)) := by
  sorry

end RiemannDynamics

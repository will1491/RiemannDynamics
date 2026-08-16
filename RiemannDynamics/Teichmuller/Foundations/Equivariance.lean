/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.Foundations.Beltrami
import RiemannDynamics.Uniformization.Fuchsian
import RiemannDynamics.QC.Calculus.Removability
import RiemannDynamics.QC.Calculus.Weyl
import RiemannDynamics.QC.GeometricToAnalytic.NondegeneracyAssembly
import RiemannDynamics.Analysis.Sobolev.ConformalCoV.Removable
import RiemannDynamics.QC.InverseQC.LusinN

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

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

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

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: the probe's homeomorphism block, the Wirtinger chain-rule
-- block, the conformal weak chain rule and the image-area energy bound all elaborate
-- inside one declaration.
/-- The inversion transport of a quasiconformal map is quasiconformal, with a coefficient of
no larger essential supremum satisfying the pullback law
`μ_G(z) z̄² = μ_h(-1/z) z²` almost everywhere. -/
theorem exists_isQCAnalytic_inversionTransport {h : ℂ → ℂ} {bh : BeltramiCoeff}
    (hh : IsQCAnalytic h bh) :
    ∃ bG : BeltramiCoeff, bG.normInf ≤ bh.normInf ∧
      IsQCAnalytic (inversionTransport h) bG ∧
      ∀ᵐ z : ℂ, bG.μ z * (starRingEnd ℂ z) ^ 2 = bh.μ (-1 / z) * z ^ 2 := by
  classical
  -- ==== basic data of `h` ====
  have hhomeo : IsHomeomorph h := hh.1.1
  have hinj : Function.Injective h := hhomeo.injective
  have hcont : Continuous h := hhomeo.continuous
  have hdeth : ∀ᵐ ζ : ℂ, 0 < (fderiv ℝ h ζ).det := hh.1.2
  have hdiffh : ∀ᵐ ζ : ℂ, DifferentiableAt ℝ h ζ := hh.ae_differentiableAt
  -- ==== pointwise basics of the transported map ====
  have hG0 : inversionTransport h 0 = 0 := by simp [inversionTransport]
  have hGapp : ∀ z : ℂ, z ≠ 0 → inversionTransport h z = (h (-z⁻¹) - h 0)⁻¹ := by
    intro z hz
    simp only [inversionTransport, if_neg hz, neg_div, one_div]
  have hden : ∀ z : ℂ, z ≠ 0 → h (-z⁻¹) - h 0 ≠ 0 := by
    intro z hz
    have h1 : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
    exact sub_ne_zero.mpr fun hEq => h1 (hinj hEq)
  have hGne : ∀ z : ℂ, z ≠ 0 → inversionTransport h z ≠ 0 := by
    intro z hz
    rw [hGapp z hz]
    exact inv_ne_zero (hden z hz)
  -- ==== `inversionTransport h` is a homeomorphism of the plane ====
  have hGhomeo : IsHomeomorph (inversionTransport h) := by
    set W : ℂ ≃ₜ ℂ := hhomeo.homeomorph h
    have hWap : ∀ z, W z = h z := fun z => IsHomeomorph.homeomorph_apply h hhomeo z
    have hWs : ∀ u, h (W.symm u) = u := fun u => by
      rw [← hWap (W.symm u)]; exact W.apply_symm_apply u
    have hsW : ∀ z, W.symm (h z) = z := fun z => by
      rw [← hWap z]; exact W.symm_apply_apply z
    -- the inverse map
    set Ginv : ℂ → ℂ := fun v => if v = 0 then 0 else -(W.symm (v⁻¹ + h 0))⁻¹ with hGinv
    have hleft : ∀ z, Ginv (inversionTransport h z) = z := by
      intro z
      by_cases hz : z = 0
      · subst hz; rw [hG0]; simp [hGinv]
      · have hFne := hGne z hz
        rw [hGinv]
        simp only [if_neg hFne]
        rw [hGapp z hz, inv_inv, sub_add_cancel, hsW]
        rw [inv_neg, inv_inv, neg_neg]
    have hright : ∀ v, inversionTransport h (Ginv v) = v := by
      intro v
      by_cases hv : v = 0
      · subst hv; simp [hGinv, hG0]
      · have hvinv : v⁻¹ ≠ 0 := inv_ne_zero hv
        set u : ℂ := W.symm (v⁻¹ + h 0) with hu
        have hwu : h u = v⁻¹ + h 0 := hWs _
        have hu0 : u ≠ 0 := by
          intro hEq
          rw [hEq] at hwu
          exact hvinv (by linear_combination -hwu)
        have hGv : Ginv v = -u⁻¹ := by rw [hGinv]; simp only [if_neg hv]; rw [← hu]
        have hGvne : Ginv v ≠ 0 := by
          rw [hGv]; exact neg_ne_zero.mpr (inv_ne_zero hu0)
        rw [hGapp _ hGvne, hGv]
        rw [inv_neg, inv_inv, neg_neg, hwu]
        rw [add_sub_cancel_right, inv_inv]
    -- continuity of the transported map off the puncture
    have hcont_ne : ∀ z : ℂ, z ≠ 0 → ContinuousAt (inversionTransport h) z := by
      intro z hz
      have hev : (fun z' : ℂ => (h (-z'⁻¹) - h 0)⁻¹) =ᶠ[𝓝 z] inversionTransport h := by
        have hnb : ∀ᶠ z' in 𝓝 z, z' ≠ 0 := isOpen_compl_singleton.eventually_mem hz
        filter_upwards [hnb] with z' hz'
        rw [hGapp z' hz']
      have hbase : ContinuousAt (fun z' : ℂ => (h (-z'⁻¹) - h 0)⁻¹) z := by
        have h1 : ContinuousAt (fun z' : ℂ => -z'⁻¹) z := (continuousAt_inv₀ hz).neg
        have h2 : ContinuousAt (fun z' : ℂ => h (-z'⁻¹) - h 0) z :=
          ((hcont.continuousAt).comp h1).sub continuousAt_const
        exact h2.inv₀ (hden z hz)
      exact hbase.congr hev
    -- continuity at the puncture, via properness
    have hw_cobounded : Tendsto h (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
      rw [Metric.cobounded_eq_cocompact]
      have := W.toCocompactMap.cocompact_tendsto'
      exact this.congr hWap
    have hsub_cobounded :
        Tendsto (fun x : ℂ => x - h 0) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
      rw [Metric.cobounded_eq_cocompact]
      exact (Homeomorph.subRight (h 0)).toCocompactMap.cocompact_tendsto'
    have hcont_zero : ContinuousAt (inversionTransport h) 0 := by
      have hpunct : Tendsto (inversionTransport h) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
        have h1 : Tendsto (fun z : ℂ => -z⁻¹) (𝓝[≠] (0 : ℂ)) (Bornology.cobounded ℂ) := by
          have := (tendsto_mul_left_cobounded (a := (-1 : ℂ)) (by norm_num)).comp
            tendsto_inv₀_nhdsNE_zero
          refine this.congr fun z => ?_
          simp [Function.comp]
        have h2 : Tendsto (fun z : ℂ => h (-z⁻¹) - h 0) (𝓝[≠] (0 : ℂ))
            (Bornology.cobounded ℂ) := hsub_cobounded.comp (hw_cobounded.comp h1)
        have h3 : Tendsto (fun z : ℂ => (h (-z⁻¹) - h 0)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
          tendsto_inv₀_cobounded.comp h2
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [hGapp z hz]
      have hpure : Tendsto (inversionTransport h) (pure (0 : ℂ)) (𝓝 0) := by
        have := tendsto_pure_nhds (inversionTransport h) 0
        rwa [hG0] at this
      have key : Tendsto (inversionTransport h) (𝓝[≠] (0 : ℂ) ⊔ pure 0) (𝓝 0) :=
        tendsto_sup.mpr ⟨hpunct, hpure⟩
      rw [nhdsNE_sup_pure] at key
      unfold ContinuousAt
      rwa [hG0]
    -- continuity of the inverse off the puncture
    have hGcont_ne : ∀ v : ℂ, v ≠ 0 → ContinuousAt Ginv v := by
      intro v hv
      have hvinv : v⁻¹ ≠ 0 := inv_ne_zero hv
      have hune : W.symm (v⁻¹ + h 0) ≠ 0 := by
        intro hEq
        have hwu : h (W.symm (v⁻¹ + h 0)) = v⁻¹ + h 0 := hWs _
        rw [hEq] at hwu
        exact hvinv (by linear_combination -hwu)
      have hev : (fun v' : ℂ => -(W.symm (v'⁻¹ + h 0))⁻¹) =ᶠ[𝓝 v] Ginv := by
        have hnb : ∀ᶠ v' in 𝓝 v, v' ≠ 0 := isOpen_compl_singleton.eventually_mem hv
        filter_upwards [hnb] with v' hv'
        rw [hGinv]; simp only [if_neg hv']
      have hbase : ContinuousAt (fun v' : ℂ => -(W.symm (v'⁻¹ + h 0))⁻¹) v := by
        have h1 : ContinuousAt (fun v' : ℂ => v'⁻¹ + h 0) v :=
          (continuousAt_inv₀ hv).add continuousAt_const
        have h2 : ContinuousAt (fun v' : ℂ => W.symm (v'⁻¹ + h 0)) v :=
          (W.continuous_symm.continuousAt).comp h1
        exact (h2.inv₀ hune).neg
      exact hbase.congr hev
    -- continuity of the inverse at the puncture
    have hWsymm_cobounded :
        Tendsto (⇑W.symm) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
      rw [Metric.cobounded_eq_cocompact]
      exact W.symm.toCocompactMap.cocompact_tendsto'
    have hGcont_zero : ContinuousAt Ginv 0 := by
      have hGinv0 : Ginv 0 = 0 := by simp [hGinv]
      have hpunct : Tendsto Ginv (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
        have h1 : Tendsto (fun v : ℂ => v⁻¹ + h 0) (𝓝[≠] (0 : ℂ))
            (Bornology.cobounded ℂ) := by
          have hadd : Tendsto (fun x : ℂ => x + h 0) (Bornology.cobounded ℂ)
              (Bornology.cobounded ℂ) := by
            rw [Metric.cobounded_eq_cocompact]
            exact (Homeomorph.addRight (h 0)).toCocompactMap.cocompact_tendsto'
          exact hadd.comp tendsto_inv₀_nhdsNE_zero
        have h2 : Tendsto (fun v : ℂ => W.symm (v⁻¹ + h 0)) (𝓝[≠] (0 : ℂ))
            (Bornology.cobounded ℂ) := hWsymm_cobounded.comp h1
        have h3 : Tendsto (fun v : ℂ => -(W.symm (v⁻¹ + h 0))⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
          have := (tendsto_inv₀_cobounded.comp h2).neg
          simpa using this
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with v hv
        rw [hGinv]; simp only [if_neg (show v ≠ 0 by simpa using hv)]
      have hpure : Tendsto Ginv (pure (0 : ℂ)) (𝓝 0) := by
        have := tendsto_pure_nhds Ginv 0
        rwa [hGinv0] at this
      have key : Tendsto Ginv (𝓝[≠] (0 : ℂ) ⊔ pure 0) (𝓝 0) :=
        tendsto_sup.mpr ⟨hpunct, hpure⟩
      rw [nhdsNE_sup_pure] at key
      unfold ContinuousAt
      rwa [hGinv0]
    have hFcont : Continuous (inversionTransport h) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz : z = 0
      · subst hz; exact hcont_zero
      · exact hcont_ne z hz
    have hGicont : Continuous Ginv := by
      rw [continuous_iff_continuousAt]
      intro v
      by_cases hv : v = 0
      · subst hv; exact hGcont_zero
      · exact hGcont_ne v hv
    exact Homeomorph.isHomeomorph
      { toFun := inversionTransport h
        invFun := Ginv
        left_inv := hleft
        right_inv := hright
        continuous_toFun := hFcont
        continuous_invFun := hGicont }
  -- ==== canonical weak partial derivatives of `h` ====
  obtain ⟨hhL2, gx0, gy0, ⟨hwx0, hwy0⟩, hgx0L2, hgy0L2⟩ := hh.2.1
  have hgx0L2' : MemLpLocOn gx0 2 Set.univ := hgx0L2
  have hgy0L2' : MemLpLocOn gy0 2 Set.univ := hgy0L2
  have hL2toLoc : ∀ {g0 : ℂ → ℂ}, MemLpLocOn g0 2 Set.univ →
      LocallyIntegrableOn g0 Set.univ := by
    intro g0 hg0
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hg0 k (Set.subset_univ _) hk).mono_exponent (by norm_num))
  have hfloc : LocallyIntegrable h := hcont.locallyIntegrable
  have haex : ∀ᵐ ζ : ℂ, (fderiv ℝ h ζ) 1 = gx0 ζ :=
    fderiv_ae_eq_weakDirDeriv hwx0 (hL2toLoc hgx0L2') hdiffh (Or.inl rfl) hfloc
  have haey : ∀ᵐ ζ : ℂ, (fderiv ℝ h ζ) Complex.I = gy0 ζ :=
    fderiv_ae_eq_weakDirDeriv hwy0 (hL2toLoc hgy0L2') hdiffh (Or.inr rfl) hfloc
  set px : ℂ → ℂ := fun ζ => (fderiv ℝ h ζ) 1 with hpx
  set py : ℂ → ℂ := fun ζ => (fderiv ℝ h ζ) Complex.I with hpy
  have hwx : HasWeakDirDeriv 1 px h Set.univ := by
    intro φ hφ hφc hφs
    rw [hwx0 φ hφ hφc hφs]
    refine neg_inj.mpr (integral_congr_ae ?_)
    filter_upwards [haex] with ζ hζ
    simp only [hpx]
    rw [hζ]
  have hwy : HasWeakDirDeriv Complex.I py h Set.univ := by
    intro φ hφ hφc hφs
    rw [hwy0 φ hφ hφc hφs]
    refine neg_inj.mpr (integral_congr_ae ?_)
    filter_upwards [haey] with ζ hζ
    simp only [hpy]
    rw [hζ]
  have hpxL2 : MemLpLocOn px 2 Set.univ := by
    intro K hKu hKc
    refine (hgx0L2' K hKu hKc).ae_eq ?_
    refine ae_restrict_of_ae ?_
    filter_upwards [haex] with ζ hζ
    simp only [hpx]
    exact hζ.symm
  have hpyL2 : MemLpLocOn py 2 Set.univ := by
    intro K hKu hKc
    refine (hgy0L2' K hKu hKc).ae_eq ?_
    refine ae_restrict_of_ae ?_
    filter_upwards [haey] with ζ hζ
    simp only [hpy]
    exact hζ.symm
  have hpxmeas : Measurable px := by
    rw [hpx]
    exact measurable_fderiv_apply_const ℝ h 1
  have hpymeas : Measurable py := by
    rw [hpy]
    exact measurable_fderiv_apply_const ℝ h Complex.I
  -- ==== transport of null sets and a.e. facts through the inversion ====
  have himgnull : ∀ N : Set ℂ, volume N = 0 →
      volume ((fun z : ℂ => -z⁻¹) '' (N ∩ {(0 : ℂ)}ᶜ)) = 0 := by
    intro N hN
    have hsub : (fun z : ℂ => -z⁻¹) '' (N ∩ {(0 : ℂ)}ᶜ)
        ⊆ (fun z : ℂ => -z⁻¹) '' (toMeasurable volume N ∩ {(0 : ℂ)}ᶜ) :=
      Set.image_mono (Set.inter_subset_inter_left _ (subset_toMeasurable _ _))
    refine measure_mono_null hsub ?_
    have hSmeas : MeasurableSet (toMeasurable volume N ∩ {(0 : ℂ)}ᶜ) :=
      (measurableSet_toMeasurable _ _).inter isOpen_compl_singleton.measurableSet
    have hSnull : volume (toMeasurable volume N ∩ {(0 : ℂ)}ᶜ) = 0 := by
      refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le)
      rw [measure_toMeasurable]
      exact hN.le
    have hfd : ∀ z ∈ toMeasurable volume N ∩ {(0 : ℂ)}ᶜ,
        HasFDerivWithinAt (fun z' : ℂ => -z'⁻¹) (fderiv ℝ (fun z' : ℂ => -z'⁻¹) z)
          (toMeasurable volume N ∩ {(0 : ℂ)}ᶜ) z := by
      intro z hz
      have hz' : z ≠ 0 := by simpa using hz.2
      have hder : HasDerivAt (fun z' : ℂ => -z'⁻¹) ((z ^ 2)⁻¹) z := by
        simpa using! (hasDerivAt_inv hz').neg
      exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
    have hinjOn : Set.InjOn (fun z' : ℂ => -z'⁻¹)
        (toMeasurable volume N ∩ {(0 : ℂ)}ᶜ) :=
      fun x _ y _ hxy => inv_injective (neg_injective hxy)
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
      (fun _ => (1 : ℝ≥0∞))
    rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
    exact hcov
  have haeInv : ∀ P : ℂ → Prop, (∀ᵐ ζ : ℂ, P ζ) → ∀ᵐ z : ℂ, z ≠ 0 → P (-z⁻¹) := by
    intro P hP
    rw [ae_iff] at hP ⊢
    refine measure_mono_null ?_ (himgnull _ hP)
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    rw [Classical.not_imp] at hz
    refine ⟨-z⁻¹, ⟨hz.2, ?_⟩, ?_⟩
    · simpa using neg_ne_zero.mpr (inv_ne_zero hz.1)
    · change -(-z⁻¹)⁻¹ = z
      rw [inv_neg, inv_inv, neg_neg]
  have hμbound : ∀ᵐ ζ : ℂ, ‖bh.μ ζ‖ ≤ bh.normInf := by
    have htop : eLpNormEssSup bh.μ volume ≠ ⊤ := (lt_of_lt_of_le bh.bound le_top).ne
    filter_upwards [ae_le_eLpNormEssSup (f := bh.μ) (μ := volume)] with ζ hζ
    have hle : ENNReal.ofReal ‖bh.μ ζ‖ ≤ eLpNormEssSup bh.μ volume := by
      rw [ofReal_norm]
      exact hζ
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hle
  have hne0 : ∀ᵐ z : ℂ, z ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  -- ==== the transported Beltrami coefficient ====
  set μG : ℂ → ℂ :=
    fun z => if z = 0 then 0 else bh.μ (-z⁻¹) * z ^ 2 / (starRingEnd ℂ z) ^ 2 with hμG
  have hinvmeas : Measurable fun u : ℂ => u⁻¹ := by
    refine measurable_of_continuousOn_compl_singleton 0 ?_
    intro u hu
    exact (continuousAt_inv₀ (by simpa using hu)).continuousWithinAt
  have hφmeas : Measurable fun z : ℂ => -z⁻¹ := hinvmeas.neg
  have hμGmeas : Measurable μG := by
    rw [hμG]
    refine Measurable.ite measurableSet_eq measurable_const ?_
    exact ((bh.measurable.comp hφmeas).mul ((continuous_pow 2).measurable)).mul
      (hinvmeas.comp ((Complex.continuous_conj.pow 2).measurable))
  -- ==== the chain-rule derivative candidates ====
  set GF : ℂ → ℂ → ℂ := fun v z =>
    -(((h (-z⁻¹) - h 0) ^ 2)⁻¹) *
      (((v * (z ^ 2)⁻¹).re : ℂ) * px (-z⁻¹) + ((v * (z ^ 2)⁻¹).im : ℂ) * py (-z⁻¹)) with hGF
  -- ==== master pointwise block ====
  have hgood : ∀ᵐ z : ℂ, z ≠ 0 → (0 < (fderiv ℝ h (-z⁻¹)).det ∧
      dzbar h (-z⁻¹) = bh.μ (-z⁻¹) * dz h (-z⁻¹) ∧ ‖bh.μ (-z⁻¹)‖ ≤ bh.normInf) :=
    haeInv _ (hdeth.and (hh.2.2.and hμbound))
  have hkey : ∀ᵐ z : ℂ,
      0 < (fderiv ℝ (inversionTransport h) z).det ∧
      dzbar (inversionTransport h) z = μG z * dz (inversionTransport h) z ∧
      ∀ v : ℂ, ‖v‖ = 1 →
        ‖GF v z‖ ^ 2 ≤ bh.K * (fderiv ℝ (inversionTransport h) z).det := by
    filter_upwards [hgood, hne0] with z hgz hz0
    obtain ⟨hdet0, hbeltζ, hbndζ⟩ := hgz hz0
    have hzinv0 : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz0)
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
    have hwdiff : DifferentiableAt ℝ h (-z⁻¹) := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hdet0
      simp [ContinuousLinearMap.det] at hdet0
    have hm₁der : HasDerivAt (fun z' : ℂ => -z'⁻¹) ((z ^ 2)⁻¹) z := by
      simpa using! (hasDerivAt_inv hz0).neg
    have hm₁C : DifferentiableAt ℂ (fun z' : ℂ => -z'⁻¹) z := hm₁der.differentiableAt
    have hm₁R : DifferentiableAt ℝ (fun z' : ℂ => -z'⁻¹) z :=
      (hm₁der.complexToReal_fderiv).differentiableAt
    set gc : ℂ → ℂ := fun z' => h (-z'⁻¹) with hgc
    have hgcz : gc z = h (-z⁻¹) := by rw [hgc]
    have hgdiff : DifferentiableAt ℝ gc z := by
      rw [hgc]
      exact hwdiff.comp z hm₁R
    have hgz_ne : gc z ≠ h 0 := by
      rw [hgcz]
      exact fun hEq => hzinv0 (hinj hEq)
    have hm₂der : HasDerivAt (fun u : ℂ => (u - h 0)⁻¹)
        (-(((gc z - h 0) ^ 2)⁻¹)) (gc z) := by
      have hsub : HasDerivAt (fun u : ℂ => u - h 0) 1 (gc z) := by
        simpa using (hasDerivAt_id (gc z)).sub_const (h 0)
      simpa using! (hasDerivAt_inv (sub_ne_zero.mpr hgz_ne)).comp (gc z) hsub
    have hm₂C : DifferentiableAt ℂ (fun u : ℂ => (u - h 0)⁻¹) (gc z) :=
      hm₂der.differentiableAt
    have hm₂R : DifferentiableAt ℝ (fun u : ℂ => (u - h 0)⁻¹) (gc z) :=
      (hm₂der.complexToReal_fderiv).differentiableAt
    have hev : inversionTransport h =ᶠ[𝓝 z] fun z' => (gc z' - h 0)⁻¹ := by
      have hnb : ∀ᶠ z' in 𝓝 z, z' ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
      filter_upwards [hnb] with z' hz'
      rw [hGapp z' hz', hgc]
    have hfeq : fderiv ℝ (inversionTransport h) z
        = fderiv ℝ (fun z' => ((gc z' - h 0)⁻¹ : ℂ)) z := hev.fderiv_eq
    have hm₁dzbar : dzbar (fun z' : ℂ => -z'⁻¹) z = 0 :=
      dzbar_eq_zero_of_differentiableAt hm₁C
    have hm₁dz : dz (fun z' : ℂ => -z'⁻¹) z = (z ^ 2)⁻¹ := by
      rw [dz_eq_deriv_of_differentiableAt hm₁C]
      exact hm₁der.deriv
    have hgdz : dz gc z = dz h (-z⁻¹) * (z ^ 2)⁻¹ := by
      rw [hgc, dz_comp hm₁R hwdiff, hm₁dzbar, hm₁dz]
      simp
    have hgdzbar : dzbar gc z = dzbar h (-z⁻¹) * (starRingEnd ℂ) ((z ^ 2)⁻¹) := by
      rw [hgc, dzbar_comp hm₁R hwdiff, hm₁dzbar, hm₁dz]
      simp
    have hm₂dzbar : dzbar (fun u : ℂ => (u - h 0)⁻¹) (gc z) = 0 :=
      dzbar_eq_zero_of_differentiableAt hm₂C
    have hm₂dz : dz (fun u : ℂ => (u - h 0)⁻¹) (gc z) = -(((gc z - h 0) ^ 2)⁻¹) := by
      rw [dz_eq_deriv_of_differentiableAt hm₂C]
      exact hm₂der.deriv
    have hdzG : dz (inversionTransport h) z
        = -(((gc z - h 0) ^ 2)⁻¹) * (dz h (-z⁻¹) * (z ^ 2)⁻¹) := by
      have hF : dz (fun z' => ((gc z' - h 0)⁻¹ : ℂ)) z
          = -(((gc z - h 0) ^ 2)⁻¹) * (dz h (-z⁻¹) * (z ^ 2)⁻¹) := by
        rw [dz_comp hgdiff hm₂R, hm₂dzbar, hm₂dz, hgdz]
        simp
      unfold dz
      rw [hfeq]
      exact hF
    have hdzbarG : dzbar (inversionTransport h) z
        = -(((gc z - h 0) ^ 2)⁻¹) * (dzbar h (-z⁻¹) * (starRingEnd ℂ) ((z ^ 2)⁻¹)) := by
      have hF : dzbar (fun z' => ((gc z' - h 0)⁻¹ : ℂ)) z
          = -(((gc z - h 0) ^ 2)⁻¹) * (dzbar h (-z⁻¹) * (starRingEnd ℂ) ((z ^ 2)⁻¹)) := by
        rw [dzbar_comp hgdiff hm₂R, hm₂dzbar, hm₂dz, hgdzbar]
        simp
      unfold dzbar
      rw [hfeq]
      exact hF
    have hdet_h : 0 < ‖dz h (-z⁻¹)‖ ^ 2 - ‖dzbar h (-z⁻¹)‖ ^ 2 := by
      rw [← det_fderiv_eq_wirtinger]
      exact hdet0
    have hc₂ : (0 : ℝ) < ‖-(((gc z - h 0) ^ 2)⁻¹)‖ := by
      rw [norm_pos_iff]
      exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hgz_ne)))
    have hc₁ : (0 : ℝ) < ‖(z ^ 2)⁻¹‖ := by
      rw [norm_pos_iff]
      exact inv_ne_zero hz2
    have hnormconj : ‖(starRingEnd ℂ) ((z ^ 2)⁻¹)‖ = ‖(z ^ 2)⁻¹‖ := by simp
    have hdetval : (fderiv ℝ (inversionTransport h) z).det
        = (‖-(((gc z - h 0) ^ 2)⁻¹)‖ * ‖(z ^ 2)⁻¹‖) ^ 2 *
          (‖dz h (-z⁻¹)‖ ^ 2 - ‖dzbar h (-z⁻¹)‖ ^ 2) := by
      rw [det_fderiv_eq_wirtinger, hdzG, hdzbarG, norm_mul, norm_mul, norm_mul, norm_mul,
        hnormconj]
      ring
    have hrepr : ∀ a : ℂ, (a.re : ℂ) * px (-z⁻¹) + (a.im : ℂ) * py (-z⁻¹)
        = dz h (-z⁻¹) * a + dzbar h (-z⁻¹) * (starRingEnd ℂ) a := by
      intro a
      have hca : (starRingEnd ℂ) a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
        simp [Complex.ext_iff]
      have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
      simp only [hpx, hpy, dz, dzbar]
      linear_combination (-(1 / 2 : ℂ) * ((fderiv ℝ h (-z⁻¹)) 1
            - Complex.I * (fderiv ℝ h (-z⁻¹)) Complex.I)) * ha
        + (-(1 / 2 : ℂ) * ((fderiv ℝ h (-z⁻¹)) 1
            + Complex.I * (fderiv ℝ h (-z⁻¹)) Complex.I)) * hca
        + ((a.im : ℂ) * (fderiv ℝ h (-z⁻¹)) Complex.I) * Complex.I_mul_I
    refine ⟨?_, ?_, ?_⟩
    · rw [hdetval]
      exact mul_pos (pow_pos (mul_pos hc₂ hc₁) 2) hdet_h
    · have hcz : (starRingEnd ℂ) z ≠ 0 := by simpa using hz0
      have hczp : (starRingEnd ℂ) z ^ 2 ≠ 0 := pow_ne_zero 2 hcz
      have hgcne : (gc z - h 0) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hgz_ne)
      rw [hdzbarG, hdzG, hbeltζ]
      simp only [hμG, if_neg hz0]
      rw [map_inv₀, map_pow]
      field_simp
    · intro v hv
      have hval : GF v z = -(((gc z - h 0) ^ 2)⁻¹) *
          (dz h (-z⁻¹) * (v * (z ^ 2)⁻¹)
            + dzbar h (-z⁻¹) * (starRingEnd ℂ) (v * (z ^ 2)⁻¹)) := by
        simp only [hGF]
        rw [hrepr (v * (z ^ 2)⁻¹), hgcz]
      rw [hval]
      have hnorma : ‖v * (z ^ 2)⁻¹‖ = ‖(z ^ 2)⁻¹‖ := by
        rw [norm_mul, hv, one_mul]
      have hnormca : ‖(starRingEnd ℂ) (v * (z ^ 2)⁻¹)‖ = ‖(z ^ 2)⁻¹‖ := by
        rw [← hnorma]
        simp
      set D : ℝ := ‖dz h (-z⁻¹)‖ with hDdef
      set E : ℝ := ‖dzbar h (-z⁻¹)‖ with hEdef
      have hED : E ≤ bh.normInf * D := by
        rw [hEdef, hDdef, hbeltζ, norm_mul]
        exact mul_le_mul_of_nonneg_right hbndζ (norm_nonneg _)
      have hD0 : 0 ≤ D := by rw [hDdef]; exact norm_nonneg _
      have hE0 : 0 ≤ E := by rw [hEdef]; exact norm_nonneg _
      have hcore : (D + E) ^ 2 ≤ bh.K * (D ^ 2 - E ^ 2) := by
        have hKdef : bh.K = (1 + bh.normInf) / (1 - bh.normInf) := rfl
        have hk1 : bh.normInf < 1 := bh.normInf_lt_one
        rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hED) (add_nonneg hD0 hE0)]
      calc ‖-(((gc z - h 0) ^ 2)⁻¹) *
            (dz h (-z⁻¹) * (v * (z ^ 2)⁻¹)
              + dzbar h (-z⁻¹) * (starRingEnd ℂ) (v * (z ^ 2)⁻¹))‖ ^ 2
          ≤ (‖-(((gc z - h 0) ^ 2)⁻¹)‖ * (‖(z ^ 2)⁻¹‖ * (D + E))) ^ 2 := by
            refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            calc ‖dz h (-z⁻¹) * (v * (z ^ 2)⁻¹)
                  + dzbar h (-z⁻¹) * (starRingEnd ℂ) (v * (z ^ 2)⁻¹)‖
                ≤ ‖dz h (-z⁻¹) * (v * (z ^ 2)⁻¹)‖
                  + ‖dzbar h (-z⁻¹) * (starRingEnd ℂ) (v * (z ^ 2)⁻¹)‖ :=
                  norm_add_le _ _
              _ = D * ‖(z ^ 2)⁻¹‖ + E * ‖(z ^ 2)⁻¹‖ := by
                  rw [norm_mul (dz h (-z⁻¹)), norm_mul (dzbar h (-z⁻¹)), hnorma, hnormca,
                    hDdef, hEdef]
              _ = ‖(z ^ 2)⁻¹‖ * (D + E) := by ring
        _ = (‖-(((gc z - h 0) ^ 2)⁻¹)‖ * ‖(z ^ 2)⁻¹‖) ^ 2 * (D + E) ^ 2 := by ring
        _ ≤ (‖-(((gc z - h 0) ^ 2)⁻¹)‖ * ‖(z ^ 2)⁻¹‖) ^ 2 * (bh.K * (D ^ 2 - E ^ 2)) :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
        _ = bh.K * ((‖-(((gc z - h 0) ^ 2)⁻¹)‖ * ‖(z ^ 2)⁻¹‖) ^ 2
              * (D ^ 2 - E ^ 2)) := by ring
        _ = bh.K * (fderiv ℝ (inversionTransport h) z).det := by rw [hdetval]
  -- ==== consumers of the master block ====
  have hdetG : ∀ᵐ z : ℂ, 0 < (fderiv ℝ (inversionTransport h) z).det :=
    hkey.mono fun z hz => hz.1
  have hGbelt : ∀ᵐ z : ℂ,
      dzbar (inversionTransport h) z = μG z * dz (inversionTransport h) z :=
    hkey.mono fun z hz => hz.2.1
  -- ==== the conformal weak chain rule off the puncture (W1) ====
  have himg : (fun z : ℂ => -z⁻¹) '' {(0 : ℂ)}ᶜ = {(0 : ℂ)}ᶜ := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using neg_ne_zero.mpr (inv_ne_zero (show z ≠ 0 by simpa using hz))
    · intro hv
      have hv' : v ≠ 0 := by simpa using hv
      refine ⟨-v⁻¹, by simpa using neg_ne_zero.mpr (inv_ne_zero hv'), ?_⟩
      change -(-v⁻¹)⁻¹ = v
      rw [inv_neg, inv_inv, neg_neg]
  have hcc : ∀ v : ℂ,
      HasWeakDirDeriv v (GF v) (inversionTransport h) {(0 : ℂ)}ᶜ ∧
        MemLpLocOn (GF v) 2 {(0 : ℂ)}ᶜ := by
    intro v
    have hφat : ∀ z ∈ ({(0 : ℂ)}ᶜ : Set ℂ),
        HasDerivAt (fun z' : ℂ => -z'⁻¹) ((z ^ 2)⁻¹) z := by
      intro z hz
      simpa using! (hasDerivAt_inv (show z ≠ 0 by simpa using hz)).neg
    have hφ0 : ∀ z ∈ ({(0 : ℂ)}ᶜ : Set ℂ), (z ^ 2)⁻¹ ≠ 0 := by
      intro z hz
      exact inv_ne_zero (pow_ne_zero 2 (show z ≠ 0 by simpa using hz))
    have hφinj : Set.InjOn (fun z' : ℂ => -z'⁻¹) {(0 : ℂ)}ᶜ :=
      fun x _ y _ hxy => inv_injective (neg_injective hxy)
    have hψat : ∀ u ∈ ({h 0}ᶜ : Set ℂ),
        HasDerivAt (fun u' : ℂ => (u' - h 0)⁻¹) (-(((u - h 0) ^ 2)⁻¹)) u := by
      intro u hu
      have hu' : u - h 0 ≠ 0 := sub_ne_zero.mpr (by simpa using hu)
      have hsub : HasDerivAt (fun u' : ℂ => u' - h 0) 1 u := by
        simpa using (hasDerivAt_id u).sub_const (h 0)
      simpa using! (hasDerivAt_inv hu').comp u hsub
    have hmaps : Set.MapsTo h ((fun z' : ℂ => -z'⁻¹) '' {(0 : ℂ)}ᶜ) {h 0}ᶜ := by
      rw [himg]
      intro ζ hζ
      exact fun hEq => (show ζ ≠ 0 by simpa using hζ) (hinj hEq)
    have hwcOn : ContinuousOn h ((fun z' : ℂ => -z'⁻¹) '' {(0 : ℂ)}ᶜ) :=
      hcont.continuousOn
    have hwg : HasWeakGradient px py h ((fun z' : ℂ => -z'⁻¹) '' {(0 : ℂ)}ᶜ) :=
      ⟨hwx.mono (Set.subset_univ _), hwy.mono (Set.subset_univ _)⟩
    have hgxOn : MemLpLocOn px 2 ((fun z' : ℂ => -z'⁻¹) '' {(0 : ℂ)}ᶜ) :=
      hpxL2.mono (Set.subset_univ _)
    have hgyOn : MemLpLocOn py 2 ((fun z' : ℂ => -z'⁻¹) '' {(0 : ℂ)}ᶜ) :=
      hpyL2.mono (Set.subset_univ _)
    have hfeqOn : Set.EqOn (inversionTransport h)
        (fun z => (fun u : ℂ => (u - h 0)⁻¹) (h ((fun z' : ℂ => -z'⁻¹) z)))
        {(0 : ℂ)}ᶜ := by
      intro z hz
      have hz' : z ≠ 0 := by simpa using hz
      rw [hGapp z hz']
    exact hasWeakDirDeriv_comp_conformal isOpen_compl_singleton isOpen_compl_singleton
      hφat hφ0 hφinj hψat hmaps hwcOn hwg hgxOn hgyOn hfeqOn v
  -- ==== image-area finiteness of the Jacobian integral ====
  have hdetmeas : Measurable fun z : ℂ =>
      ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det) :=
    ENNReal.measurable_ofReal.comp
      (ContinuousLinearMap.continuous_det.measurable.comp
        (measurable_fderiv ℝ (inversionTransport h)))
  have hdetint : ∀ K : Set ℂ, IsCompact K →
      ∫⁻ z in K, ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det) < ⊤ := by
    intro K hKc
    have hSGmeas : MeasurableSet {z : ℂ | 0 < (fderiv ℝ (inversionTransport h) z).det} :=
      (ContinuousLinearMap.continuous_det.measurable.comp
        (measurable_fderiv ℝ (inversionTransport h))) measurableSet_Ioi
    have hSGc : volume {z : ℂ | 0 < (fderiv ℝ (inversionTransport h) z).det}ᶜ = 0 := by
      have hae := hdetG
      rw [ae_iff] at hae
      simpa [Set.compl_ofPred] using hae
    set SK := K ∩ {z : ℂ | 0 < (fderiv ℝ (inversionTransport h) z).det} with hSK
    have hKae : K =ᵐ[volume] SK := by
      rw [ae_eq_set]
      constructor
      · rw [hSK, Set.sdiff_self_inter]
        exact measure_mono_null (fun z hz => hz.2) hSGc
      · rw [hSK, Set.sdiff_eq_empty.mpr Set.inter_subset_left]
        exact measure_empty
    have hSKmeas : MeasurableSet SK := hKc.measurableSet.inter hSGmeas
    have hfd : ∀ z ∈ SK, HasFDerivWithinAt (inversionTransport h)
        (fderiv ℝ (inversionTransport h) z) SK z := by
      intro z hz
      have hdiffz : DifferentiableAt ℝ (inversionTransport h) z := by
        by_contra hnd
        have hpos : 0 < (fderiv ℝ (inversionTransport h) z).det := hz.2
        rw [fderiv_zero_of_not_differentiableAt hnd] at hpos
        simp [ContinuousLinearMap.det] at hpos
      exact hdiffz.hasFDerivAt.hasFDerivWithinAt
    have hinjG : Set.InjOn (inversionTransport h) SK := hGhomeo.injective.injOn
    have hcov := lintegral_abs_det_fderiv_eq_addHaar_image volume hSKmeas hfd hinjG
    calc ∫⁻ z in K, ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det)
        = ∫⁻ z in SK, ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det) := by
          rw [Measure.restrict_congr_set hKae]
      _ = ∫⁻ z in SK, ENNReal.ofReal |(fderiv ℝ (inversionTransport h) z).det| := by
          refine setLIntegral_congr_fun hSKmeas fun z hz => ?_
          rw [abs_of_pos hz.2]
      _ = volume (inversionTransport h '' SK) := hcov
      _ ≤ volume (inversionTransport h '' K) := by
          refine measure_mono (Set.image_mono ?_)
          rw [hSK]
          exact Set.inter_subset_left
      _ < ⊤ := (hKc.image hGhomeo.continuous).measure_lt_top
  -- ==== the energy bound: derivative candidates are locally square integrable ====
  have henergy : ∀ F : ℂ → ℂ, Measurable F →
      (∀ᵐ z : ℂ, ‖F z‖ ^ 2 ≤ bh.K * (fderiv ℝ (inversionTransport h) z).det) →
      MemLpLocOn F 2 Set.univ := by
    intro F hFmeas hFbd K _ hKc
    refine ⟨hFmeas.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    have hexp : ∀ x : ℝ≥0∞, x ^ (2 : ℝ≥0∞).toReal = x ^ (2 : ℕ) := by
      intro x
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    simp only [hexp]
    have hae2 : ∀ᵐ z ∂volume.restrict K, ‖F z‖ₑ ^ (2 : ℕ)
        ≤ ENNReal.ofReal bh.K
          * ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det) := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hFbd] with z hz
      calc ‖F z‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (‖F z‖ ^ 2) := by
            rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        _ ≤ ENNReal.ofReal (bh.K * (fderiv ℝ (inversionTransport h) z).det) :=
            ENNReal.ofReal_le_ofReal hz
        _ = ENNReal.ofReal bh.K
            * ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det) :=
            ENNReal.ofReal_mul (by linarith [bh.one_le_K])
    calc ∫⁻ z, ‖F z‖ₑ ^ (2 : ℕ) ∂volume.restrict K
        ≤ ∫⁻ z, ENNReal.ofReal bh.K
            * ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det)
            ∂volume.restrict K := lintegral_mono_ae hae2
      _ = ENNReal.ofReal bh.K
          * ∫⁻ z in K, ENNReal.ofReal ((fderiv ℝ (inversionTransport h) z).det) :=
          lintegral_const_mul _ hdetmeas
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hdetint K hKc)
  have hGFmeas : ∀ v : ℂ, Measurable (GF v) := by
    intro v
    simp only [hGF]
    refine Measurable.mul ?_ ?_
    · refine Measurable.neg ?_
      exact hinvmeas.comp
        (((hcont.measurable.comp hφmeas).sub measurable_const).pow_const 2)
    · refine Measurable.add ?_ ?_
      · exact (Complex.measurable_ofReal.comp (Complex.measurable_re.comp
          ((hinvmeas.comp ((continuous_pow 2).measurable)).const_mul v))).mul
          (hpxmeas.comp hφmeas)
      · exact (Complex.measurable_ofReal.comp (Complex.measurable_im.comp
          ((hinvmeas.comp ((continuous_pow 2).measurable)).const_mul v))).mul
          (hpymeas.comp hφmeas)
  have hGxL2 : MemLpLocOn (GF 1) 2 Set.univ := by
    refine henergy _ (hGFmeas 1) ?_
    exact hkey.mono fun z hz => hz.2.2 1 norm_one
  have hGyL2 : MemLpLocOn (GF Complex.I) 2 Set.univ := by
    refine henergy _ (hGFmeas Complex.I) ?_
    exact hkey.mono fun z hz => hz.2.2 Complex.I Complex.norm_I
  -- ==== W2: remove the puncture ====
  have hWxU : HasWeakDirDeriv 1 (GF 1) (inversionTransport h) Set.univ := by
    refine HasWeakDirDeriv.removable_singleton (p := 0) ?_ isOpen_univ
      hGhomeo.continuous.continuousOn hGxL2
    rw [← Set.compl_eq_univ_sdiff]
    exact (hcc 1).1
  have hWyU : HasWeakDirDeriv Complex.I (GF Complex.I) (inversionTransport h)
      Set.univ := by
    refine HasWeakDirDeriv.removable_singleton (p := 0) ?_ isOpen_univ
      hGhomeo.continuous.continuousOn hGyL2
    rw [← Set.compl_eq_univ_sdiff]
    exact (hcc Complex.I).1
  -- ==== local square integrability of the map itself, and membership in W^{1,2} ====
  have hGL2 : MemLpLocOn (inversionTransport h) 2 Set.univ := by
    intro K _ hKc
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hGhomeo.continuous.continuousOn
    exact MemLp.of_bound hGhomeo.continuous.aestronglyMeasurable C
      (ae_restrict_of_forall_mem hKc.measurableSet fun z hz => hC z hz)
  have hGW12 : MemW12loc (inversionTransport h) :=
    ⟨hGL2, GF 1, GF Complex.I, ⟨hWxU, hWyU⟩, hGxL2, hGyL2⟩
  -- ==== coefficient bound ====
  have hμGbound : ∀ᵐ z : ℂ, ‖μG z‖ₑ ≤ eLpNormEssSup bh.μ volume := by
    filter_upwards [haeInv _ (ae_le_eLpNormEssSup (f := bh.μ) (μ := volume)), hne0]
      with z hz hz0
    have hb := hz hz0
    have hnorm : ‖μG z‖ = ‖bh.μ (-z⁻¹)‖ := by
      simp only [hμG, if_neg hz0]
      rw [norm_div, norm_mul, norm_pow, norm_pow]
      rw [show ‖(starRingEnd ℂ) z‖ = ‖z‖ from by simp]
      rw [mul_div_assoc, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0)), mul_one]
    rw [← ofReal_norm, hnorm, ofReal_norm]
    exact hb
  have hbGtop : eLpNormEssSup bh.μ volume ≠ ⊤ := (lt_of_lt_of_le bh.bound le_top).ne
  have hμGess : eLpNormEssSup μG volume ≤ eLpNormEssSup bh.μ volume :=
    essSup_le_of_ae_le _ hμGbound
  have hμGlt : eLpNormEssSup μG volume < 1 := lt_of_le_of_lt hμGess bh.bound
  -- ==== assembly ====
  refine ⟨⟨μG, hμGmeas, hμGlt⟩, ?_, ⟨⟨hGhomeo, hdetG⟩, hGW12, hGbelt⟩, ?_⟩
  · exact ENNReal.toReal_mono hbGtop hμGess
  · filter_upwards [hne0] with z hz0
    simp only [hμG, if_neg hz0]
    rw [neg_div, one_div]
    exact div_mul_cancel₀ _
      (pow_ne_zero 2 (show (starRingEnd ℂ) z ≠ 0 by simpa using hz0))

/-! ## General case via the Bruhat factorization -/

set_option backward.isDefEq.respectTransparency false in
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

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: the Bruhat assembly elaborates the affine pullback bookkeeping,
-- the inversion-transport consumer, the uniqueness renormalization and the sign analysis
-- inside one declaration.
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
  classical
  obtain ⟨A₁, A₂, hA₁c, hA₂c, hγfac⟩ := bruhat_factorization γ hc
  -- ==== entry data of the Bruhat factors ====
  have hdet₁ : A₁ 0 0 * A₁ 1 1 - A₁ 0 1 * A₁ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe A₁
    rwa [Matrix.det_fin_two] at h
  rw [hA₁c, mul_zero, sub_zero] at hdet₁
  have ha₁ : A₁ 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet₁
    exact zero_ne_one hdet₁
  have he₁ : A₁ 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet₁
    exact zero_ne_one hdet₁
  have hdet₂ : A₂ 0 0 * A₂ 1 1 - A₂ 0 1 * A₂ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe A₂
    rwa [Matrix.det_fin_two] at h
  rw [hA₂c, mul_zero, sub_zero] at hdet₂
  have ha₂ : A₂ 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet₂
    exact zero_ne_one hdet₂
  have he₂ : A₂ 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet₂
    exact zero_ne_one hdet₂
  set c₁ : ℂ := ((A₁ 0 0 ^ 2 : ℝ) : ℂ) with hc₁def
  set d₁ : ℂ := ((A₁ 0 0 * A₁ 0 1 : ℝ) : ℂ) with hd₁def
  set c₂ : ℂ := ((A₂ 0 0 ^ 2 : ℝ) : ℂ) with hc₂def
  set d₂ : ℂ := ((A₂ 0 0 * A₂ 0 1 : ℝ) : ℂ) with hd₂def
  have hc₁ne : c₁ ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 ha₁)
  have hc₂ne : c₂ ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 ha₂)
  have hc₁conj : starRingEnd ℂ c₁ = c₁ := by rw [hc₁def]; exact Complex.conj_ofReal _
  have hc₂conj : starRingEnd ℂ c₂ = c₂ := by rw [hc₂def]; exact Complex.conj_ofReal _
  have hd₁conj : starRingEnd ℂ d₁ = d₁ := by rw [hd₁def]; exact Complex.conj_ofReal _
  have hd₂conj : starRingEnd ℂ d₂ = d₂ := by rw [hd₂def]; exact Complex.conj_ofReal _
  have hmA₁ : ∀ v : ℂ, moebiusMap A₁ v = c₁ * v + d₁ := by
    intro v
    rw [moebiusMap_of_lowerLeft_zero A₁ hA₁c v, hc₁def, hd₁def]
    push_cast
    ring
  have hmA₂ : ∀ v : ℂ, moebiusMap A₂ v = c₂ * v + d₂ := by
    intro v
    rw [moebiusMap_of_lowerLeft_zero A₂ hA₂c v, hc₂def, hd₂def]
    push_cast
    ring
  -- ==== denominators along the factorization ====
  have he₁C : (A₁ 1 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he₁
  have he₂C : (A₂ 1 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he₂
  have hdenA₂ : ∀ z : ℂ, moebiusDenom A₂ z = (A₂ 1 1 : ℂ) := by
    intro z
    simp [moebiusDenom, hA₂c]
  have hdenA₂ne : ∀ z : ℂ, moebiusDenom A₂ z ≠ 0 := fun z => by
    rw [hdenA₂ z]; exact he₂C
  have hAS10 : (A₁ * inversionSL2) 1 0 = A₁ 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [inversionSL2, hA₁c]
  have hAS11 : (A₁ * inversionSL2) 1 1 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [inversionSL2, hA₁c]
  have hdenAS : ∀ u : ℂ, moebiusDenom (A₁ * inversionSL2) u = (A₁ 1 1 : ℂ) * u := by
    intro u
    simp [moebiusDenom, hAS10, hAS11]
  have hdγ : ∀ z : ℂ, moebiusDenom γ z = (A₁ 1 1 : ℂ) * (c₂ * z + d₂) * (A₂ 1 1 : ℂ) := by
    intro z
    rw [hγfac, ← moebiusDenom_mul (A₁ * inversionSL2) A₂ z (hdenA₂ne z), hmA₂ z, hdenAS,
      hdenA₂]
  have hpole : ∀ z : ℂ, moebiusDenom γ z ≠ 0 ↔ c₂ * z + d₂ ≠ 0 := by
    intro z
    rw [hdγ z]
    constructor
    · intro hne h0'
      rw [h0', mul_zero, zero_mul] at hne
      exact hne rfl
    · intro hu
      exact mul_ne_zero (mul_ne_zero he₁C hu) he₂C
  have hmγ : ∀ z : ℂ, c₂ * z + d₂ ≠ 0 →
      moebiusMap γ z = c₁ * (-1 / (c₂ * z + d₂)) + d₁ := by
    intro z hu
    have hdenS : moebiusDenom inversionSL2 (c₂ * z + d₂) = c₂ * z + d₂ := by
      simp [moebiusDenom, inversionSL2]
    have hdenSne : moebiusDenom inversionSL2 (c₂ * z + d₂) ≠ 0 := by
      rw [hdenS]; exact hu
    rw [hγfac, ← moebiusMap_mul (A₁ * inversionSL2) A₂ z (hdenA₂ne z), hmA₂ z,
      ← moebiusMap_mul A₁ inversionSL2 _ hdenSne, moebiusMap_inversionSL2, hmA₁]
  -- ==== the transported map through the inversion ====
  set g : ℂ → ℂ := f ∘ affineMap c₁ d₁ with hgdef
  have hgqc : IsQCAnalytic g (b.pullbackAffine hc₁ne d₁) :=
    isQCAnalytic_comp_affine hf hc₁ne d₁
  obtain ⟨bG, hbGle, hGqc', hGpull⟩ := exists_isQCAnalytic_inversionTransport hgqc
  set Φ : ℂ → ℂ := inversionTransport g ∘ affineMap c₂ d₂ with hΦdef
  have hΦqc0 : IsQCAnalytic Φ (bG.pullbackAffine hc₂ne d₂) :=
    isQCAnalytic_comp_affine hGqc' hc₂ne d₂
  -- ==== affine maps are quasi-measure-preserving ====
  have haffQMP : ∀ (c x₀ : ℂ), c ≠ 0 →
      Measure.QuasiMeasurePreserving (fun z : ℂ => c * z + x₀) volume volume := by
    intro c x₀ hcne
    have hns : (0 : ℝ) < Complex.normSq c := Complex.normSq_pos.mpr hcne
    have hMapp : ⇑((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ)
        = fun w : ℂ => c * w := rfl
    have hFD : HasFDerivAt (fun w : ℂ => c * w)
        ((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) 0 := by
      have h := ((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ).hasFDerivAt (x := 0)
      rwa [hMapp] at h
    have hdet2 : (fderiv ℝ (fun w : ℂ => c * w) 0).det = Complex.normSq c := by
      have hdiff : DifferentiableAt ℂ (fun w : ℂ => c * w) 0 := by fun_prop
      rw [det_fderiv_eq_wirtinger, dzbar_eq_zero_of_differentiableAt hdiff,
        dz_eq_deriv_of_differentiableAt hdiff]
      have hd : deriv (fun w : ℂ => c * w) 0 = c := by
        simp
      rw [hd]
      simp [Complex.normSq_eq_norm_sq]
    have hdetL : LinearMap.det
        ((((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
        = Complex.normSq c := by
      rw [hFD.fderiv] at hdet2
      exact hdet2
    have hmapmul : Measure.map (fun w : ℂ => c * w) volume
        = ENNReal.ofReal ((Complex.normSq c)⁻¹) • volume := by
      have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
        (f := ((((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) : ℂ →L[ℝ] ℂ) :
          ℂ →ₗ[ℝ] ℂ)) (by rw [hdetL]; exact ne_of_gt hns)
      rw [hdetL, abs_of_pos (inv_pos.mpr hns)] at h
      exact h
    have hmap : Measure.map (fun z : ℂ => c * z + x₀) volume
        = ENNReal.ofReal ((Complex.normSq c)⁻¹) • volume := by
      have hcm : Measurable fun w : ℂ => c * w := measurable_id.const_mul c
      have hcomp : (fun z : ℂ => c * z + x₀) = (fun y : ℂ => y + x₀) ∘ fun w : ℂ => c * w :=
        rfl
      rw [hcomp, ← Measure.map_map (measurable_add_const x₀) hcm, hmapmul, Measure.map_smul,
        (measurePreserving_add_right volume x₀).map_eq]
    exact ⟨(measurable_id'.const_mul c).add_const x₀, by
      rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  -- ==== a.e. avoidance of the affine zero ====
  have hu0 : ∀ᵐ z : ℂ, c₂ * z + d₂ ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (measure_singleton (-d₂ / c₂))
    rw [Set.mem_ofPred_eq, not_not] at hz
    have hzval : z = -d₂ / c₂ := by
      rw [eq_div_iff hc₂ne]
      linear_combination hz
    simpa [Set.mem_singleton_iff] using hzval
  -- ==== coefficient bookkeeping: the pulled-back coefficient agrees a.e. with b ====
  have hcoef : (bG.pullbackAffine hc₂ne d₂).μ =ᵐ[volume] b.μ := by
    have htrans := (haffQMP c₂ d₂ hc₂ne).ae hGpull
    filter_upwards [htrans, hinv, hu0] with z hz1 hz2 hz3
    have hcu : starRingEnd ℂ (c₂ * z + d₂) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz3
    have hcu2 : (starRingEnd ℂ (c₂ * z + d₂)) ^ 2 ≠ 0 := pow_ne_zero 2 hcu
    have hpb₁ : (b.pullbackAffine hc₁ne d₁).μ (-1 / (c₂ * z + d₂))
        = b.μ (moebiusMap γ z) := by
      change b.μ (c₁ * (-1 / (c₂ * z + d₂)) + d₁) * (starRingEnd ℂ c₁ / c₁) = _
      rw [hc₁conj, div_self hc₁ne, mul_one, ← hmγ z hz3]
    have hkey1 : b.μ (moebiusMap γ z) * (c₂ * z + d₂) ^ 2
        = b.μ z * (starRingEnd ℂ (c₂ * z + d₂)) ^ 2 := by
      have h := hz2
      rw [hdγ z, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal] at h
      have hρ : ((A₁ 1 1 : ℂ) * (A₂ 1 1 : ℂ)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (mul_ne_zero he₁C he₂C)
      apply mul_right_cancel₀ hρ
      linear_combination h
    change bG.μ (c₂ * z + d₂) * (starRingEnd ℂ c₂ / c₂) = b.μ z
    rw [hc₂conj, div_self hc₂ne, mul_one]
    apply mul_right_cancel₀ hcu2
    calc bG.μ (c₂ * z + d₂) * (starRingEnd ℂ (c₂ * z + d₂)) ^ 2
        = (b.pullbackAffine hc₁ne d₁).μ (-1 / (c₂ * z + d₂)) * (c₂ * z + d₂) ^ 2 := hz1
      _ = b.μ (moebiusMap γ z) * (c₂ * z + d₂) ^ 2 := by rw [hpb₁]
      _ = b.μ z * (starRingEnd ℂ (c₂ * z + d₂)) ^ 2 := hkey1
  have hΦqcb : IsQCAnalytic Φ b := hΦqc0.congr_coeff hcoef
  have hΦinj : Function.Injective Φ := hΦqcb.injective
  -- ==== uniqueness renormalization: the normalized transported map is f ====
  set Y₀ : ℂ := Φ 0 with hY₀def
  set Y₁ : ℂ := Φ 1 with hY₁def
  have hne : Y₁ - Y₀ ≠ 0 := by
    refine sub_ne_zero.mpr fun hEq => ?_
    rw [hY₁def, hY₀def] at hEq
    exact one_ne_zero (hΦinj hEq)
  have hq0 : (fun z => (Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀)) 0 = 0 := by
    change (Y₁ - Y₀)⁻¹ * Y₀ + -((Y₁ - Y₀)⁻¹ * Y₀) = 0
    ring
  have hq1 : (fun z => (Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀)) 1 = 1 := by
    change (Y₁ - Y₀)⁻¹ * Y₁ + -((Y₁ - Y₀)⁻¹ * Y₀) = 1
    rw [show (Y₁ - Y₀)⁻¹ * Y₁ + -((Y₁ - Y₀)⁻¹ * Y₀) = (Y₁ - Y₀)⁻¹ * (Y₁ - Y₀) from by ring]
    exact inv_mul_cancel₀ hne
  have hqf : (fun z => (Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀)) = f :=
    (mrmt_unique_normalized b).unique
      ⟨hΦqcb.affine_postcomp (inv_ne_zero hne) (-((Y₁ - Y₀)⁻¹ * Y₀)), hq0, hq1⟩ ⟨hf, h0, h1⟩
  have hΦz : ∀ z : ℂ, Φ z = (Y₁ - Y₀) * f z + Y₀ := by
    intro z
    have h := congrFun hqf z
    change (Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀) = f z at h
    have h2 : (Y₁ - Y₀) * ((Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀)) + Y₀ = Φ z := by
      linear_combination (Φ z - Y₀) * mul_inv_cancel₀ hne
    rw [← h2, h]
  -- ==== pointwise value of Φ off the pole ====
  have hgd₁ : g 0 = f d₁ := by
    change f (affineMap c₁ d₁ 0) = f d₁
    rw [affineMap_apply, mul_zero, zero_add]
  have hΦval : ∀ z : ℂ, c₂ * z + d₂ ≠ 0 → Φ z = (f (moebiusMap γ z) - f d₁)⁻¹ := by
    intro z hu
    change inversionTransport g (affineMap c₂ d₂ z) = _
    rw [affineMap_apply]
    simp only [inversionTransport, if_neg hu]
    have harg : g (-1 / (c₂ * z + d₂)) = f (moebiusMap γ z) := by
      change f (affineMap c₁ d₁ (-1 / (c₂ * z + d₂))) = f (moebiusMap γ z)
      rw [affineMap_apply, ← hmγ z hu]
    rw [harg, hgd₁]
  -- ==== symmetry of the transported map; realness of the normalization data ====
  have hgsym : ∀ v : ℂ, g (starRingEnd ℂ v) = starRingEnd ℂ (g v) := by
    intro v
    change f (affineMap c₁ d₁ (starRingEnd ℂ v)) = starRingEnd ℂ (f (affineMap c₁ d₁ v))
    rw [affineMap_apply, affineMap_apply, ← hsym]
    congr 1
    rw [map_add, map_mul, hc₁conj, hd₁conj]
  have hΦsym : ∀ v : ℂ, Φ (starRingEnd ℂ v) = starRingEnd ℂ (Φ v) := by
    intro v
    have hgg0 : starRingEnd ℂ (g 0) = g 0 := by
      have h := hgsym 0
      rw [map_zero] at h
      exact h.symm
    change inversionTransport g (affineMap c₂ d₂ (starRingEnd ℂ v))
        = starRingEnd ℂ (inversionTransport g (affineMap c₂ d₂ v))
    rw [affineMap_apply, affineMap_apply]
    have hconjarg : c₂ * starRingEnd ℂ v + d₂ = starRingEnd ℂ (c₂ * v + d₂) := by
      rw [map_add, map_mul, hc₂conj, hd₂conj]
    rw [hconjarg]
    by_cases hv : c₂ * v + d₂ = 0
    · rw [hv, map_zero]
      simp [inversionTransport]
    · have hv' : starRingEnd ℂ (c₂ * v + d₂) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hv
      simp only [inversionTransport, if_neg hv, if_neg hv']
      rw [map_inv₀]
      congr 1
      rw [map_sub, hgg0, ← hgsym]
      congr 2
      rw [map_div₀, map_neg, map_one]
  have him₀ : Y₀.im = 0 := by
    have h := hΦsym 0
    rw [map_zero] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  have him₁ : Y₁.im = 0 := by
    have h := hΦsym 1
    rw [map_one] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  have hαC : Y₁ - Y₀ = ((Y₁.re - Y₀.re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.ofReal_re]
    · rw [Complex.sub_im, him₁, him₀, Complex.ofReal_im, sub_zero]
  have hβC : Y₀ = ((Y₀.re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [him₀, Complex.ofReal_im]
  -- ==== sign of the leading coefficient via the value at I ====
  set u₂ : ℂ := c₂ * Complex.I + d₂ with hu₂def
  have hu₂im : u₂.im = A₂ 0 0 ^ 2 := by
    rw [hu₂def, hc₂def, hd₂def]
    simp only [Fin.isValue, Complex.ofReal_pow, Complex.ofReal_mul, Complex.add_im, Complex.mul_im,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hu₂pos : 0 < u₂.im := by
    rw [hu₂im]
    exact pow_two_pos_of_ne_zero ha₂
  have hu₂ne : u₂ ≠ 0 := by
    intro hEq
    rw [hEq, Complex.zero_im] at hu₂pos
    exact lt_irrefl 0 hu₂pos
  have hζpos : 0 < (-1 / u₂).im := by
    rw [neg_div, one_div, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hu₂pos (Complex.normSq_pos.mpr hu₂ne)
  have hd₁im : ∀ ζ : ℂ, (c₁ * ζ + d₁).im = A₁ 0 0 ^ 2 * ζ.im := by
    intro ζ
    rw [hc₁def, hd₁def]
    simp only [Fin.isValue, Complex.ofReal_pow, Complex.ofReal_mul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hfd₁im : (f d₁).im = 0 := by
    rw [hd₁def]
    exact realLine_im_eq_zero hsym (A₁ 0 0 * A₁ 0 1)
  have hfIarg : 0 < (c₁ * (-1 / u₂) + d₁).im := by
    rw [hd₁im]
    exact mul_pos (pow_two_pos_of_ne_zero ha₁) hζpos
  have hΦI : Φ Complex.I = (f (c₁ * (-1 / u₂) + d₁) - f d₁)⁻¹ := by
    change inversionTransport g (affineMap c₂ d₂ Complex.I) = _
    rw [affineMap_apply, ← hu₂def]
    simp only [inversionTransport, if_neg hu₂ne]
    have harg : g (-1 / u₂) = f (c₁ * (-1 / u₂) + d₁) := by
      change f (affineMap c₁ d₁ (-1 / u₂)) = _
      rw [affineMap_apply]
    rw [harg, hgd₁]
  have hΦI_eq : (Φ Complex.I).im = (Y₁.re - Y₀.re) * (f Complex.I).im := by
    rw [hΦz Complex.I, hαC, hβC, Complex.add_im, Complex.ofReal_im, add_zero,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hαneg : Y₁.re - Y₀.re < 0 := by
    rcases halfPlane_dichotomy hf hsym with ⟨hup, _⟩ | ⟨hdn, _⟩
    · have hfIpos : 0 < (f Complex.I).im := hup Complex.I (by rw [Complex.I_im]; norm_num)
      have hwpos : 0 < (f (c₁ * (-1 / u₂) + d₁) - f d₁).im := by
        rw [Complex.sub_im, hfd₁im, sub_zero]
        exact hup _ hfIarg
      have hwne : f (c₁ * (-1 / u₂) + d₁) - f d₁ ≠ 0 := by
        intro hEq
        rw [hEq, Complex.zero_im] at hwpos
        exact lt_irrefl 0 hwpos
      have hΦIneg : (Φ Complex.I).im < 0 := by
        rw [hΦI, Complex.inv_im]
        exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hwpos) (Complex.normSq_pos.mpr hwne)
      rw [hΦI_eq] at hΦIneg
      by_contra hcon
      have hcon' : 0 ≤ Y₁.re - Y₀.re := not_lt.mp hcon
      nlinarith
    · have hfIneg : (f Complex.I).im < 0 := hdn Complex.I (by rw [Complex.I_im]; norm_num)
      have hwneg : (f (c₁ * (-1 / u₂) + d₁) - f d₁).im < 0 := by
        rw [Complex.sub_im, hfd₁im, sub_zero]
        exact hdn _ hfIarg
      have hwne : f (c₁ * (-1 / u₂) + d₁) - f d₁ ≠ 0 := by
        intro hEq
        rw [hEq, Complex.zero_im] at hwneg
        exact lt_irrefl 0 hwneg
      have hΦIpos : 0 < (Φ Complex.I).im := by
        rw [hΦI, Complex.inv_im]
        exact div_pos (neg_pos.mpr hwneg) (Complex.normSq_pos.mpr hwne)
      rw [hΦI_eq] at hΦIpos
      by_contra hcon
      have hcon' : 0 ≤ Y₁.re - Y₀.re := not_lt.mp hcon
      nlinarith
  -- ==== the explicit real Möbius conjugator ====
  set αr : ℝ := Y₁.re - Y₀.re with hαrdef
  set βr : ℝ := Y₀.re with hβrdef
  set cr : ℝ := (f d₁).re with hcrdef
  have hc₀C : f d₁ = (cr : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [hfd₁im, Complex.ofReal_im]
  set s : ℝ := Real.sqrt (-αr) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsne
  have hs2 : s * s = -αr := Real.mul_self_sqrt (by linarith)
  have hdetW : (!![cr * αr / s, (cr * βr + 1) / s; αr / s, βr / s] :
      Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination -hs2
  refine ⟨⟨!![cr * αr / s, (cr * βr + 1) / s; αr / s, βr / s], hdetW⟩, ?_⟩
  intro z hz
  have hu : c₂ * z + d₂ ≠ 0 := (hpole z).mp hz
  have hΦvz := hΦval z hu
  have hfne : f (moebiusMap γ z) - f d₁ ≠ 0 := by
    rw [hmγ z hu]
    intro hEq
    have h2 := hf.injective (sub_eq_zero.mp hEq)
    have h3 : c₁ * (-1 / (c₂ * z + d₂)) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hc₁ne h4
    · rw [div_eq_zero_iff] at h4
      rcases h4 with h5 | h5
      · exact (by norm_num : (-1 : ℂ) ≠ 0) h5
      · exact hu h5
  have hΦne : Φ z ≠ 0 := by
    rw [hΦvz]
    exact inv_ne_zero hfne
  have hWmoeb : moebiusMap
      (⟨!![cr * αr / s, (cr * βr + 1) / s; αr / s, βr / s], hdetW⟩ :
        Matrix.SpecialLinearGroup (Fin 2) ℝ) (f z)
      = (((cr * αr / s : ℝ) : ℂ) * f z + (((cr * βr + 1) / s : ℝ) : ℂ))
        / (((αr / s : ℝ) : ℂ) * f z + ((βr / s : ℝ) : ℂ)) := by
    simp [moebiusMap, moebiusDenom]
  rw [hWmoeb]
  have hdenval : ((αr / s : ℝ) : ℂ) * f z + ((βr / s : ℝ) : ℂ) = Φ z / ((s : ℝ) : ℂ) := by
    rw [hΦz z, hαC, hβC]
    push_cast
    field_simp
  have hdenne : ((αr / s : ℝ) : ℂ) * f z + ((βr / s : ℝ) : ℂ) ≠ 0 := by
    rw [hdenval]
    exact div_ne_zero hΦne hsC
  rw [eq_div_iff hdenne, hdenval]
  have hfmz : f (moebiusMap γ z) = (cr : ℂ) + (Φ z)⁻¹ := by
    rw [hΦvz, inv_inv, hc₀C]
    ring
  have hcancel : ((cr : ℂ) + (Φ z)⁻¹) * (Φ z / ((s : ℝ) : ℂ))
      = ((cr : ℂ) * Φ z + 1) / ((s : ℝ) : ℂ) := by
    field_simp
  rw [hfmz, hcancel, hΦz z, hαC, hβC]
  push_cast
  field_simp
  ring

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
  by_cases hc : γ 1 0 = 0
  · obtain ⟨W, hW⟩ := exists_sl2_equivariant_of_lowerLeft_zero hf h0 h1 hsym γ hc hinv
    exact ⟨W, fun z _ => hW z⟩
  · exact exists_sl2_equivariant_of_lowerLeft_ne_zero hf h0 h1 hsym γ hc hinv

/-! ## The image group -/

/-- The carrier of the image group: matrices `W` that conjugate `f` against some `γ ∈ Γ₀`
almost everywhere, `f ∘ γ = W ∘ f` a.e. -/
def fuchsianImageCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (f : ℂ → ℂ) : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  {W | ∃ γ ∈ Γ₀, ∀ᵐ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z)}

/-- The identity matrix conjugates `f` against `γ = 1`. -/
theorem one_mem_fuchsianImageCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (f : ℂ → ℂ) : 1 ∈ fuchsianImageCarrier Γ₀ f := by
  refine ⟨1, one_mem Γ₀, ?_⟩
  filter_upwards with z
  rw [moebiusMap_one, moebiusMap_one]

/-- The image carrier of an injective map is closed under products: the two a.e. identities
compose along the Möbius cocycle, pulling null sets back through the smooth Möbius factors
and through point preimages of `f`. -/
theorem mul_mem_fuchsianImageCarrier {f : ℂ → ℂ} (hf : Function.Injective f)
    {W₁ W₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h₁ : W₁ ∈ fuchsianImageCarrier Γ₀ f)
    (h₂ : W₂ ∈ fuchsianImageCarrier Γ₀ f) : W₁ * W₂ ∈ fuchsianImageCarrier Γ₀ f := by
  obtain ⟨γ₁, hγ₁, hae₁⟩ := h₁
  obtain ⟨γ₂, hγ₂, hae₂⟩ := h₂
  -- a.e. facts transport through a plane Möbius map off its pole
  have haeMoeb : ∀ (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : ℂ → Prop),
      (∀ᵐ w : ℂ, P w) → ∀ᵐ z : ℂ, moebiusDenom δ z ≠ 0 → P (moebiusMap δ z) := by
    intro δ P hP
    have hopen : IsOpen {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom δ⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hP ⊢
    have himg : volume (moebiusMap δ⁻¹ ''
        (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le)
        rw [measure_toMeasurable]
        exact hP.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap δ⁻¹) (fderiv ℝ (moebiusMap δ⁻¹) w)
            (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap δ⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap δ⁻¹)
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) := by
        intro x hx y hy hxy
        have hx1 : moebiusMap δ (moebiusMap δ⁻¹ x) = x := by
          rw [moebiusMap_mul δ δ⁻¹ x hx.2, mul_inv_cancel, moebiusMap_one]
        have hy1 : moebiusMap δ (moebiusMap δ⁻¹ y) = y := by
          rw [moebiusMap_mul δ δ⁻¹ y hy.2, mul_inv_cancel, moebiusMap_one]
        rw [← hx1, ← hy1, hxy]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom δ⁻¹ (moebiusMap δ z) * moebiusDenom δ z = 1 := by
      rw [moebiusDenom_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom δ⁻¹ (moebiusMap δ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap δ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusMap_one]
  -- a.e. avoidance of the pole of `γ₂`
  have haePole : ∀ᵐ z : ℂ, moebiusDenom γ₂ z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact volume_moebiusDenom_zero γ₂
  -- a.e. avoidance of the pole of `W₂` after `f`
  have hfPole : ∀ᵐ z : ℂ, moebiusDenom W₂ (f z) ≠ 0 := by
    have hPsub : Set.Subsingleton {w : ℂ | moebiusDenom W₂ w = 0} := by
      intro w₁ hw₁ w₂ hw₂
      have h₁' : (W₂ 1 0 : ℂ) * w₁ + (W₂ 1 1 : ℂ) = 0 := hw₁
      have h₂' : (W₂ 1 0 : ℂ) * w₂ + (W₂ 1 1 : ℂ) = 0 := hw₂
      by_cases hc : W₂ 1 0 = 0
      · exfalso
        have hdet : W₂ 0 0 * W₂ 1 1 - W₂ 0 1 * W₂ 1 0 = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe W₂
          rwa [Matrix.det_fin_two] at h
        have hcC : ((W₂ 1 0 : ℝ) : ℂ) = 0 := by
          rw [hc, Complex.ofReal_zero]
        rw [hcC, zero_mul, zero_add] at h₁'
        have hd : W₂ 1 1 = 0 := by exact_mod_cast h₁'
        rw [hc, hd] at hdet
        simp at hdet
      · have hcC : ((W₂ 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
        have hmul : (W₂ 1 0 : ℂ) * w₁ = (W₂ 1 0 : ℂ) * w₂ := by
          linear_combination h₁' - h₂'
        exact mul_left_cancel₀ hcC hmul
    have hpre : Set.Subsingleton (f ⁻¹' {w : ℂ | moebiusDenom W₂ w = 0}) := by
      intro x hx y hy
      exact hf (hPsub hx hy)
    rw [ae_iff]
    refine measure_mono_null ?_ (hpre.measure_zero volume)
    intro z hz
    simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hz
    exact hz
  refine ⟨γ₁ * γ₂, mul_mem hγ₁ hγ₂, ?_⟩
  have hpull := haeMoeb γ₂ (fun w => f (moebiusMap γ₁ w) = moebiusMap W₁ (f w)) hae₁
  filter_upwards [haePole, hae₂, hpull, hfPole] with z hd2 h2 h1 hdW2
  rw [← moebiusMap_mul γ₁ γ₂ z hd2, h1 hd2, h2, moebiusMap_mul W₁ W₂ (f z) hdW2]

/-- The image carrier of an injective map is closed under inverses. -/
theorem inv_mem_fuchsianImageCarrier {f : ℂ → ℂ} (hf : Function.Injective f)
    {W : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : W ∈ fuchsianImageCarrier Γ₀ f) :
    W⁻¹ ∈ fuchsianImageCarrier Γ₀ f := by
  obtain ⟨γ, hγ, hae⟩ := h
  -- a.e. facts transport through a plane Möbius map off its pole
  have haeMoeb : ∀ (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : ℂ → Prop),
      (∀ᵐ w : ℂ, P w) → ∀ᵐ z : ℂ, moebiusDenom δ z ≠ 0 → P (moebiusMap δ z) := by
    intro δ P hP
    have hopen : IsOpen {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom δ⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hP ⊢
    have himg : volume (moebiusMap δ⁻¹ ''
        (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le)
        rw [measure_toMeasurable]
        exact hP.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap δ⁻¹) (fderiv ℝ (moebiusMap δ⁻¹) w)
            (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap δ⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap δ⁻¹)
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) := by
        intro x hx y hy hxy
        have hx1 : moebiusMap δ (moebiusMap δ⁻¹ x) = x := by
          rw [moebiusMap_mul δ δ⁻¹ x hx.2, mul_inv_cancel, moebiusMap_one]
        have hy1 : moebiusMap δ (moebiusMap δ⁻¹ y) = y := by
          rw [moebiusMap_mul δ δ⁻¹ y hy.2, mul_inv_cancel, moebiusMap_one]
        rw [← hx1, ← hy1, hxy]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom δ⁻¹ (moebiusMap δ z) * moebiusDenom δ z = 1 := by
      rw [moebiusDenom_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom δ⁻¹ (moebiusMap δ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap δ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusMap_one]
  -- a.e. avoidance of the pole of `W` after `f`
  have hfPole : ∀ᵐ z : ℂ, moebiusDenom W (f z) ≠ 0 := by
    have hPsub : Set.Subsingleton {w : ℂ | moebiusDenom W w = 0} := by
      intro w₁ hw₁ w₂ hw₂
      have h₁' : (W 1 0 : ℂ) * w₁ + (W 1 1 : ℂ) = 0 := hw₁
      have h₂' : (W 1 0 : ℂ) * w₂ + (W 1 1 : ℂ) = 0 := hw₂
      by_cases hc : W 1 0 = 0
      · exfalso
        have hdet : W 0 0 * W 1 1 - W 0 1 * W 1 0 = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe W
          rwa [Matrix.det_fin_two] at h
        have hcC : ((W 1 0 : ℝ) : ℂ) = 0 := by
          rw [hc, Complex.ofReal_zero]
        rw [hcC, zero_mul, zero_add] at h₁'
        have hd : W 1 1 = 0 := by exact_mod_cast h₁'
        rw [hc, hd] at hdet
        simp at hdet
      · have hcC : ((W 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
        have hmul : (W 1 0 : ℂ) * w₁ = (W 1 0 : ℂ) * w₂ := by
          linear_combination h₁' - h₂'
        exact mul_left_cancel₀ hcC hmul
    have hpre : Set.Subsingleton (f ⁻¹' {w : ℂ | moebiusDenom W w = 0}) := by
      intro x hx y hy
      exact hf (hPsub hx hy)
    rw [ae_iff]
    refine measure_mono_null ?_ (hpre.measure_zero volume)
    intro z hz
    simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hz
    exact hz
  refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
  have haePole : ∀ᵐ z : ℂ, moebiusDenom γ⁻¹ z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact volume_moebiusDenom_zero γ⁻¹
  have hpull := haeMoeb γ⁻¹ (fun w => f (moebiusMap γ w) = moebiusMap W (f w)) hae
  have hWpull := haeMoeb γ⁻¹ (fun w => moebiusDenom W (f w) ≠ 0) hfPole
  filter_upwards [haePole, hpull, hWpull] with z hd hp hW2
  have hback : moebiusMap γ (moebiusMap γ⁻¹ z) = z := by
    rw [moebiusMap_mul γ γ⁻¹ z hd, mul_inv_cancel, moebiusMap_one]
  have hfz := hp hd
  rw [hback] at hfz
  rw [hfz, moebiusMap_mul W⁻¹ W (f (moebiusMap γ⁻¹ z)) (hW2 hd), inv_mul_cancel,
    moebiusMap_one]

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
  exact ⟨γ, hγ, h⟩

/-- The image group is closed under negation of the matrix: `moebiusMap (-W) = moebiusMap W`,
so the same `γ` witnesses membership. -/
theorem neg_mem_fuchsianImage {f : ℂ → ℂ} (hf : Function.Injective f)
    {W W' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hW : W ∈ fuchsianImage Γ₀ f hf)
    (h : (W' : Matrix (Fin 2) (Fin 2) ℝ) = -(W : Matrix (Fin 2) (Fin 2) ℝ)) :
    W' ∈ fuchsianImage Γ₀ f hf := by
  have hWmem : W ∈ fuchsianImageCarrier Γ₀ f := hW
  obtain ⟨γ, hγ, hae⟩ := hWmem
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hae] with z hz
  rw [moebiusMap_neg_matrix h (f z)]
  exact hz

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
  have hfc : Continuous f := hf.1.1.continuous
  have hdich := halfPlane_dichotomy hf hsym
  have him0 : ∀ z : ℂ, 0 < z.im → (f z).im ≠ 0 := by
    rcases hdich with ⟨hpos, _⟩ | ⟨hneg, _⟩
    · exact fun z hz => ne_of_gt (hpos z hz)
    · exact fun z hz => ne_of_lt (hneg z hz)
  -- the a.e. Möbius conjugation identity upgrades to everywhere on the upper half plane
  have hupg : ∀ γ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ᵐ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z)) →
      ∀ z : ℂ, 0 < z.im → f (moebiusMap γ z) = moebiusMap W (f z) := by
    intro γ W hae z hz
    have hUopen : IsOpen {w : ℂ | 0 < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    have h1 : ContinuousOn (fun w => f (moebiusMap γ w)) {w : ℂ | 0 < w.im} := by
      intro w hw
      have hd := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hw)
      exact (hfc.continuousAt.comp
        (hasDerivAt_moebiusMap γ hd).continuousAt).continuousWithinAt
    have h2 : ContinuousOn (fun w => moebiusMap W (f w)) {w : ℂ | 0 < w.im} := by
      intro w hw
      have hd := moebiusDenom_ne_zero_of_im_ne_zero W (him0 w hw)
      exact ((hasDerivAt_moebiusMap W hd).continuousAt.comp
        hfc.continuousAt).continuousWithinAt
    have heq : Set.EqOn (fun w => f (moebiusMap γ w)) (fun w => moebiusMap W (f w))
        {w : ℂ | 0 < w.im} := by
      refine Measure.eqOn_of_ae_eq (ae_restrict_of_ae hae) h1 h2 ?_
      rw [hUopen.interior_eq]
      exact subset_closure
    exact heq hz
  rcases hdich with ⟨hpos, himg⟩ | ⟨hneg, himg⟩
  · -- `f` preserves the upper half plane
    have hinvmem : ∀ τ : UpperHalfPlane,
        0 < ((IsHomeomorph.homeomorph f hf.1.1).symm ↑τ).im := by
      intro τ
      have hτ : (↑τ : ℂ) ∈ f '' {z : ℂ | 0 < z.im} := by
        rw [himg]
        exact τ.2
      obtain ⟨z, hz, hfz⟩ := hτ
      have hFz : (IsHomeomorph.homeomorph f hf.1.1).symm ↑τ = z := by
        rw [← hfz]
        exact (IsHomeomorph.homeomorph f hf.1.1).symm_apply_apply z
      rw [hFz]
      exact hz
    refine ⟨{ toFun := fun τ => ⟨f ↑τ, hpos ↑τ τ.2⟩
              invFun := fun τ => ⟨(IsHomeomorph.homeomorph f hf.1.1).symm ↑τ, hinvmem τ⟩
              left_inv := fun τ => by
                apply UpperHalfPlane.ext
                exact (IsHomeomorph.homeomorph f hf.1.1).symm_apply_apply ↑τ
              right_inv := fun τ => by
                apply UpperHalfPlane.ext
                exact (IsHomeomorph.homeomorph f hf.1.1).apply_symm_apply ↑τ
              continuous_toFun := by
                have hind := UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing
                exact hind.continuous_iff.mpr (hfc.comp UpperHalfPlane.continuous_coe)
              continuous_invFun := by
                have hind := UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing
                exact hind.continuous_iff.mpr
                  ((IsHomeomorph.homeomorph f hf.1.1).symm.continuous.comp
                    UpperHalfPlane.continuous_coe) }, ?_⟩
    intro γ W hae τ
    have hup := hupg γ W hae ↑τ τ.2
    apply UpperHalfPlane.ext
    rw [coe_smul_eq_moebiusMap W]
    change f ↑(γ • τ) = moebiusMap W (f ↑τ)
    rw [coe_smul_eq_moebiusMap γ]
    exact hup
  · -- `f` maps the upper half plane onto the lower half plane; conjugate back
    have hmemU : ∀ τ : UpperHalfPlane, 0 < (starRingEnd ℂ (f ↑τ)).im := by
      intro τ
      rw [Complex.conj_im]
      have := hneg ↑τ τ.2
      linarith
    have hinvmem : ∀ τ : UpperHalfPlane,
        0 < ((IsHomeomorph.homeomorph f hf.1.1).symm (starRingEnd ℂ ↑τ)).im := by
      intro τ
      have hτ : starRingEnd ℂ (↑τ : ℂ) ∈ f '' {z : ℂ | 0 < z.im} := by
        rw [himg]
        have h2 := τ.2
        change (starRingEnd ℂ (↑τ : ℂ)).im < 0
        rw [Complex.conj_im]
        linarith
      obtain ⟨z, hz, hfz⟩ := hτ
      have hFz : (IsHomeomorph.homeomorph f hf.1.1).symm (starRingEnd ℂ ↑τ) = z := by
        rw [← hfz]
        exact (IsHomeomorph.homeomorph f hf.1.1).symm_apply_apply z
      rw [hFz]
      exact hz
    refine ⟨{ toFun := fun τ => ⟨starRingEnd ℂ (f ↑τ), hmemU τ⟩
              invFun := fun τ =>
                ⟨(IsHomeomorph.homeomorph f hf.1.1).symm (starRingEnd ℂ ↑τ), hinvmem τ⟩
              left_inv := fun τ => by
                apply UpperHalfPlane.ext
                change (IsHomeomorph.homeomorph f hf.1.1).symm
                    (starRingEnd ℂ (starRingEnd ℂ (f ↑τ))) = ↑τ
                rw [Complex.conj_conj]
                exact (IsHomeomorph.homeomorph f hf.1.1).symm_apply_apply ↑τ
              right_inv := fun τ => by
                apply UpperHalfPlane.ext
                change starRingEnd ℂ
                    (f ((IsHomeomorph.homeomorph f hf.1.1).symm (starRingEnd ℂ ↑τ))) = ↑τ
                have happ : f ((IsHomeomorph.homeomorph f hf.1.1).symm (starRingEnd ℂ ↑τ))
                    = starRingEnd ℂ ↑τ :=
                  (IsHomeomorph.homeomorph f hf.1.1).apply_symm_apply (starRingEnd ℂ ↑τ)
                rw [happ, Complex.conj_conj]
              continuous_toFun := by
                have hind := UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing
                exact hind.continuous_iff.mpr
                  (Complex.continuous_conj.comp (hfc.comp UpperHalfPlane.continuous_coe))
              continuous_invFun := by
                have hind := UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing
                exact hind.continuous_iff.mpr
                  ((IsHomeomorph.homeomorph f hf.1.1).symm.continuous.comp
                    (Complex.continuous_conj.comp UpperHalfPlane.continuous_coe)) }, ?_⟩
    intro γ W hae τ
    have hup := hupg γ W hae ↑τ τ.2
    have hWconj : ∀ u : ℂ,
        moebiusMap W (starRingEnd ℂ u) = starRingEnd ℂ (moebiusMap W u) := by
      intro u
      simp [moebiusMap, moebiusDenom, map_div₀, map_add, map_mul, Complex.conj_ofReal]
    apply UpperHalfPlane.ext
    rw [coe_smul_eq_moebiusMap W]
    change starRingEnd ℂ (f ↑(γ • τ)) = moebiusMap W (starRingEnd ℂ (f ↑τ))
    rw [coe_smul_eq_moebiusMap γ, hup, hWconj]

/-- Proper discontinuity transports along an equivariant homeomorphism: given a relation
matching every element of `G'` to a partner in `G` intertwined by `e`, and a finite kernel of
the `G'`-action, proper discontinuity of the `G`-action yields that of the `G'`-action. -/
theorem properlyDiscontinuousSMul_of_equivariant_homeo {G G' T T' : Type*} [Group G]
    [Group G'] [TopologicalSpace T] [TopologicalSpace T'] [MulAction G T] [MulAction G' T']
    (e : T ≃ₜ T') (R : G → G' → Prop) (hR : ∀ g' : G', ∃ g : G, R g g')
    (hint : ∀ g g', R g g' → ∀ t : T, e (g • t) = g' • e t)
    (hker : {g' : G' | ∀ t' : T', g' • t' = t'}.Finite)
    (hG : ProperlyDiscontinuousSMul G T) : ProperlyDiscontinuousSMul G' T' := by
  constructor
  intro K' L' hK' hL'
  have hK : IsCompact (e.symm '' K') := hK'.image e.symm.continuous
  have hL : IsCompact (e.symm '' L') := hL'.image e.symm.continuous
  have hfin := hG.finite_disjoint_inter_image hK hL
  have hfib : ∀ g : G, {g' : G' | R g g'}.Finite := by
    intro g
    rcases Set.eq_empty_or_nonempty {g' : G' | R g g'} with hemp | ⟨g₀', hg₀'⟩
    · rw [hemp]
      exact Set.finite_empty
    · refine Set.Finite.subset (hker.image (fun k => g₀' * k)) ?_
      intro g'' hg''
      refine ⟨g₀'⁻¹ * g'', ?_, ?_⟩
      · intro t'
        have h1 : g'' • e (e.symm t') = g₀' • e (e.symm t') := by
          rw [← hint g g'' hg'' (e.symm t'), ← hint g g₀' hg₀' (e.symm t')]
        rw [e.apply_symm_apply] at h1
        rw [mul_smul, h1, inv_smul_smul]
      · exact mul_inv_cancel_left g₀' g''
  refine Set.Finite.subset (hfin.biUnion fun g _ => hfib g) ?_
  intro g' hg'
  obtain ⟨g, hRg⟩ := hR g'
  obtain ⟨x', hx'⟩ := hg'
  obtain ⟨himgx, hLx⟩ := hx'
  obtain ⟨k', hk', hgk⟩ := himgx
  have hgk' : g' • k' = x' := hgk
  have hkey : e (g • e.symm k') = g' • k' := by
    rw [hint g g' hRg (e.symm k'), e.apply_symm_apply]
  refine Set.mem_biUnion ?_ hRg
  refine ⟨g • e.symm k', ⟨⟨e.symm k', Set.mem_image_of_mem _ hk', rfl⟩, ?_⟩⟩
  refine ⟨x', hLx, ?_⟩
  rw [← hgk', ← hkey, e.symm_apply_apply]

/-- The image group of a Fuchsian group under a normalized symmetric quasiconformal map with
invariant coefficient is again Fuchsian. -/
theorem fuchsianImage_isFuchsianGroup (hΓ₀ : IsFuchsianGroup Γ₀) {f : ℂ → ℂ}
    {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hinv : IsInvariantBeltrami' Γ₀ b) :
    IsFuchsianGroup (fuchsianImage Γ₀ f hf.injective) := by
  have _ := h0
  have _ := h1
  have _ := hinv
  obtain ⟨e, he⟩ := exists_conjugating_upperHomeo hf hsym
  have hker : {W' : ↥(fuchsianImage Γ₀ f hf.injective) |
      ∀ τ' : UpperHalfPlane, W' • τ' = τ'}.Finite := by
    have hsub : {W' : ↥(fuchsianImage Γ₀ f hf.injective) |
        ∀ τ' : UpperHalfPlane, W' • τ' = τ'}
        ⊆ (fun W' : ↥(fuchsianImage Γ₀ f hf.injective) =>
            ((W' : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹'
          {1, -1} := by
      intro W' hW'
      exact (smul_id_iff_pm_one (W' : Matrix.SpecialLinearGroup (Fin 2) ℝ)).mp hW'
    refine Set.Finite.subset (Set.Finite.preimage (fun x _ y _ hxy => ?_) ?_) hsub
    · exact Subtype.ext (Subtype.ext hxy)
    · exact (Set.finite_singleton _).insert _
  refine properlyDiscontinuousSMul_of_equivariant_homeo (G := ↥Γ₀)
    (G' := ↥(fuchsianImage Γ₀ f hf.injective)) e
    (fun g W' => ∀ τ : UpperHalfPlane,
      e ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ)
        = (W' : Matrix.SpecialLinearGroup (Fin 2) ℝ) • e τ)
    (fun W' => ?_) (fun g W' hint₀ τ => hint₀ τ) hker hΓ₀
  have hWmem : (W' : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ fuchsianImageCarrier Γ₀ f :=
    W'.2
  obtain ⟨γ, hγ, hae⟩ := hWmem
  exact ⟨⟨γ, hγ⟩, he γ ↑W' hae⟩

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
  have _ := h0
  have _ := h1
  have _ := hinv
  obtain ⟨e, he⟩ := exists_conjugating_upperHomeo hf hsym
  rintro W ⟨τ₀, hτ₀⟩ τ'
  have hWmem : (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ fuchsianImageCarrier Γ₀ f :=
    W.2
  obtain ⟨γ, hγ, hae⟩ := hWmem
  have hint := he γ ↑W hae
  have hτ₀' : (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ₀ = τ₀ := hτ₀
  have hfix : γ • e.symm τ₀ = e.symm τ₀ := by
    apply e.injective
    rw [hint (e.symm τ₀), e.apply_symm_apply, hτ₀']
  have hall := hfree ⟨γ, hγ⟩ ⟨e.symm τ₀, hfix⟩
  have hallSL : ∀ τ'' : UpperHalfPlane, γ • τ'' = τ'' := hall
  have hW : (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ' = τ' := by
    rw [← e.apply_symm_apply τ', ← hint (e.symm τ'), hallSL (e.symm τ')]
  exact hW

/-- Cocompactness transports to the image group: the conjugating homeomorphism of the upper
half plane descends to a homeomorphism of the orbit spaces. -/
theorem fuchsianImage_cocompact
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hinv : IsInvariantBeltrami' Γ₀ b) :
    CompactSpace
      (Quotient (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)) := by
  obtain ⟨e, he⟩ := exists_conjugating_upperHomeo hf hsym
  have hpart : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ₀ →
      ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        W ∈ fuchsianImage Γ₀ f hf.injective ∧
          ∀ τ : UpperHalfPlane, e (γ • τ) = W • e τ := by
    intro γ hγ
    obtain ⟨W, hW⟩ := exists_sl2_equivariant hf h0 h1 hsym γ (hinv γ hγ)
    have haePole : ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      exact volume_moebiusDenom_zero γ
    have hae : ∀ᵐ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z) := by
      filter_upwards [haePole] with z hz
      exact hW z hz
    exact ⟨W, mem_fuchsianImage_of_equivariant hf.injective hγ hae, he γ W hae⟩
  have hresp : ∀ a b : UpperHalfPlane,
      (MulAction.orbitRel Γ₀ UpperHalfPlane) a b →
        Quotient.mk (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)
            (e a)
          = Quotient.mk
              (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)
              (e b) := by
    intro a b hab
    have hab' : a ∈ MulAction.orbit ↥Γ₀ b := MulAction.orbitRel_apply.mp hab
    obtain ⟨g, hg⟩ := hab'
    have hg' : (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • b = a := hg
    obtain ⟨W, hWmem, hWint⟩ := hpart ↑g g.2
    have horb : (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) • e b = e a := by
      rw [← hWint b, ← hg']
    exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨⟨W, hWmem⟩, horb⟩)
  have hcont : Continuous (Quotient.lift
      (fun τ : UpperHalfPlane =>
        Quotient.mk (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)
          (e τ)) hresp) :=
    Continuous.quotient_lift (continuous_quot_mk.comp e.continuous) hresp
  have hsurj : Function.Surjective (Quotient.lift
      (fun τ : UpperHalfPlane =>
        Quotient.mk (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)
          (e τ)) hresp) := by
    intro x
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep x
    refine ⟨Quotient.mk (MulAction.orbitRel Γ₀ UpperHalfPlane) (e.symm σ), ?_⟩
    have hq : Quotient.lift
        (fun τ : UpperHalfPlane =>
          Quotient.mk (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)
            (e τ)) hresp (Quotient.mk (MulAction.orbitRel Γ₀ UpperHalfPlane) (e.symm σ))
        = Quotient.mk (MulAction.orbitRel (fuchsianImage Γ₀ f hf.injective) UpperHalfPlane)
            (e (e.symm σ)) := rfl
    rw [hq, e.apply_symm_apply]
    exact hσ
  have := hcc
  exact ⟨by rw [← hsurj.range_eq]; exact isCompact_range hcont⟩

end RiemannDynamics

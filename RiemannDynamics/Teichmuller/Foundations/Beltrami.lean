/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Equivalence
import RiemannDynamics.QC.MRMT.Uniqueness
import RiemannDynamics.QC.InverseQC.SliceAC
import RiemannDynamics.QC.GeometricToAnalytic.InfinitesimalModulus
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Plane Möbius maps and Beltrami-coefficient symmetries

The plane reading `moebiusMap γ z = (a z + b) / (c z + d)` of a matrix
`γ = !![a, b; c, d] ∈ SL(2, ℝ)` (junk value `0` at the unique pole), its cocycle laws, the
bridge to the `SL(2, ℝ)`-action on the upper half plane, and the symmetry layer for Beltrami
coefficients: invariance under a subgroup (`IsInvariantBeltrami'`), reflection symmetry across
the real axis (`IsSymmetricBeltrami`, `BeltramiCoeff.reflect`), affine pullbacks
(`BeltramiCoeff.pullbackAffine`), Wirtinger chain rules for affine and holomorphic
precomposition and for conjugation by `conj`, and the composition and uniqueness laws of
quasiconformal maps with prescribed coefficient.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-! ## Plane Möbius maps -/

/-- The denominator `c·z + d` of the plane Möbius map of `γ ∈ SL(2, ℝ)`, with `c = γ 1 0`,
`d = γ 1 1` read as real numbers and coerced to `ℂ`. -/
noncomputable def moebiusDenom (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)

/-- The plane Möbius map `z ↦ (a z + b) / (c z + d)` of `γ ∈ SL(2, ℝ)`, totalized with the
junk value `0` at the pole of the denominator. -/
noncomputable def moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / moebiusDenom γ z

/-- The affine map `z ↦ α z + β` with `α > 0`, packaged as the element
`!![√α, β/√α; 0, 1/√α]` of `SL(2, ℝ)`. -/
noncomputable def affineSL2 (α β : ℝ) (hα : 0 < α) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![Real.sqrt α, β / Real.sqrt α; 0, 1 / Real.sqrt α], by
    have h : Real.sqrt α ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hα)
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

/-- The inversion `z ↦ -1/z`, packaged as the element `!![0, -1; 1, 0]` of `SL(2, ℝ)`. -/
noncomputable def inversionSL2 : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; norm_num⟩

/-- The Möbius denominator of the identity matrix is constantly `1`. -/
theorem moebiusDenom_one (z : ℂ) : moebiusDenom 1 z = 1 := by
  simp [moebiusDenom, Matrix.SpecialLinearGroup.coe_one]

/-- The plane Möbius map of the identity matrix is the identity. -/
theorem moebiusMap_one (z : ℂ) : moebiusMap 1 z = z := by
  simp [moebiusMap, moebiusDenom, Matrix.SpecialLinearGroup.coe_one]

/-- Denominator cocycle: away from the pole of `γ₂`, the denominators multiply along the
matrix product. -/
theorem moebiusDenom_mul (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ)
    (hz : moebiusDenom γ₂ z ≠ 0) :
    moebiusDenom γ₁ (moebiusMap γ₂ z) * moebiusDenom γ₂ z = moebiusDenom (γ₁ * γ₂) z := by
  have h10 : (γ₁ * γ₂) 1 0 = γ₁ 1 0 * γ₂ 0 0 + γ₁ 1 1 * γ₂ 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (γ₁ * γ₂) 1 1 = γ₁ 1 0 * γ₂ 0 1 + γ₁ 1 1 * γ₂ 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [moebiusDenom] at hz
  simp only [moebiusDenom, moebiusMap, h10, h11]
  push_cast
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ hz]
  ring

/-- Cocycle law for plane Möbius maps: away from the pole of `γ₂`, composition realizes the
matrix product. -/
theorem moebiusMap_mul (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ)
    (hz : moebiusDenom γ₂ z ≠ 0) :
    moebiusMap γ₁ (moebiusMap γ₂ z) = moebiusMap (γ₁ * γ₂) z := by
  have h00 : (γ₁ * γ₂) 0 0 = γ₁ 0 0 * γ₂ 0 0 + γ₁ 0 1 * γ₂ 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (γ₁ * γ₂) 0 1 = γ₁ 0 0 * γ₂ 0 1 + γ₁ 0 1 * γ₂ 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hM : moebiusMap γ₂ z * moebiusDenom γ₂ z = (γ₂ 0 0 : ℂ) * z + (γ₂ 0 1 : ℂ) := by
    simp only [moebiusMap]
    exact div_mul_cancel₀ _ hz
  have hnum : ((γ₁ 0 0 : ℂ) * moebiusMap γ₂ z + (γ₁ 0 1 : ℂ)) * moebiusDenom γ₂ z
      = ((γ₁ * γ₂) 0 0 : ℂ) * z + ((γ₁ * γ₂) 0 1 : ℂ) := by
    rw [add_mul, mul_assoc, hM, h00, h01]
    simp only [moebiusDenom]
    push_cast
    ring
  have hden := moebiusDenom_mul γ₁ γ₂ z hz
  calc moebiusMap γ₁ (moebiusMap γ₂ z)
      = (((γ₁ 0 0 : ℂ) * moebiusMap γ₂ z + (γ₁ 0 1 : ℂ)) * moebiusDenom γ₂ z)
        / (moebiusDenom γ₁ (moebiusMap γ₂ z) * moebiusDenom γ₂ z) := by
        rw [mul_div_mul_right _ _ hz]
        rfl
    _ = (((γ₁ * γ₂) 0 0 : ℂ) * z + ((γ₁ * γ₂) 0 1 : ℂ)) / moebiusDenom (γ₁ * γ₂) z := by
        rw [hnum, hden]
    _ = moebiusMap (γ₁ * γ₂) z := rfl

/-- Off its pole, `moebiusMap γ` is complex-differentiable with derivative
`(c z + d)⁻²`, since `det γ = 1`. -/
theorem hasDerivAt_moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : moebiusDenom γ z ≠ 0) :
    HasDerivAt (moebiusMap γ) (((moebiusDenom γ z) ^ 2)⁻¹) z := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hdetC : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    exact_mod_cast hdet
  have hnum : HasDerivAt (fun w : ℂ => (γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) (γ 0 0 : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℝ) : ℂ)).add_const ((γ 0 1 : ℝ) : ℂ)
  have hden : HasDerivAt (fun w : ℂ => (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) (γ 1 0 : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℝ) : ℂ)).add_const ((γ 1 1 : ℝ) : ℂ)
  have hz' : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := hz
  have h := hnum.div hden hz'
  have hval : ((γ 0 0 : ℂ) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))
        - ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) * (γ 1 0 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ 2
      = ((moebiusDenom γ z) ^ 2)⁻¹ := by
    have hnum1 : (γ 0 0 : ℂ) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))
        - ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) * (γ 1 0 : ℂ) = 1 := by
      linear_combination hdetC
    rw [hnum1, one_div]
    rfl
  rw [hval] at h
  exact h

/-- The pole set of a plane Möbius map is Lebesgue-null: it is empty or a single point. -/
theorem volume_moebiusDenom_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    volume {z : ℂ | moebiusDenom γ z = 0} = 0 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  by_cases hc : γ 1 0 = 0
  · have hd : γ 1 1 ≠ 0 := by
      intro h0
      rw [hc, h0] at hdet
      simp at hdet
    have hempty : {z : ℂ | moebiusDenom γ z = 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, moebiusDenom, hc]
      push_cast
      simp [hd]
    rw [hempty]
    exact measure_empty
  · have hcC : (γ 1 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have hsingle : {z : ℂ | moebiusDenom γ z = 0} = {(-(γ 1 1 : ℂ)) / (γ 1 0 : ℂ)} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, moebiusDenom]
      constructor
      · intro h0
        rw [eq_div_iff hcC]
        linear_combination h0
      · intro h0
        rw [h0]
        field_simp
        ring
    rw [hsingle]
    exact measure_singleton _

/-- Bridge between the `SL(2, ℝ)`-action on the upper half plane and the plane Möbius map:
the coercion of `γ • τ` is `moebiusMap γ` applied to the coercion of `τ`. -/
theorem coe_smul_eq_moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (τ : UpperHalfPlane) : ((γ • τ : UpperHalfPlane) : ℂ) = moebiusMap γ (τ : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [moebiusMap, moebiusDenom]

/-- A real matrix sends real non-pole points to real points. -/
theorem moebiusMap_im_eq_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : z.im = 0) (hd : moebiusDenom γ z ≠ 0) : (moebiusMap γ z).im = 0 := by
  have _hne := hd
  have hconj : ∀ w : ℂ, moebiusMap γ (starRingEnd ℂ w) = starRingEnd ℂ (moebiusMap γ w) := by
    intro w
    simp [moebiusMap, moebiusDenom, map_div₀, map_add, map_mul, Complex.conj_ofReal]
  have hzfix : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr hz
  have h := hconj z
  rw [hzfix] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- The Möbius denominator of a real matrix does not vanish off the real axis. -/
theorem moebiusDenom_ne_zero_of_im_ne_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : z.im ≠ 0) : moebiusDenom γ z ≠ 0 := by
  intro h0
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp only [moebiusDenom, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
  have hc : γ 1 0 = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hz
  simp only [moebiusDenom, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re, hc] at hre
  rw [hc] at hdet
  simp only [zero_add] at hre
  rw [hre] at hdet
  simp at hdet

/-- A plane Möbius map of `SL(2, ℝ)` preserves the open upper half plane. -/
theorem moebiusMap_im_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : 0 < (moebiusMap γ z).im := by
  have h := coe_smul_eq_moebiusMap γ ⟨z, hz⟩
  rw [← h]
  exact (γ • (⟨z, hz⟩ : UpperHalfPlane)).2

/-- A plane Möbius map of `SL(2, ℝ)` preserves the open lower half plane. -/
theorem moebiusMap_im_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : z.im < 0) : (moebiusMap γ z).im < 0 := by
  have hconj : ∀ w : ℂ, moebiusMap γ (starRingEnd ℂ w) = starRingEnd ℂ (moebiusMap γ w) := by
    intro w
    simp [moebiusMap, moebiusDenom, map_div₀, map_add, map_mul, Complex.conj_ofReal]
  have hw : 0 < (starRingEnd ℂ z).im := by
    rw [Complex.conj_im]
    linarith
  have h1 : moebiusMap γ z = starRingEnd ℂ (moebiusMap γ (starRingEnd ℂ z)) := by
    rw [← hconj (starRingEnd ℂ z), Complex.conj_conj]
  rw [h1, Complex.conj_im]
  have := moebiusMap_im_pos γ hw
  linarith

/-- When the lower-left entry vanishes, the plane Möbius map is the affine map
`z ↦ a² z + a b` with positive real leading coefficient `a² = (γ 0 0)²`. -/
theorem moebiusMap_of_lowerLeft_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : γ 1 0 = 0) (z : ℂ) :
    moebiusMap γ z = (γ 0 0 : ℂ) ^ 2 * z + (γ 0 0 : ℂ) * (γ 0 1 : ℂ) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rw [hc, mul_zero, sub_zero] at hdet
  have hdetC : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) = 1 := by exact_mod_cast hdet
  have hdC : (γ 1 1 : ℂ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdetC
    exact zero_ne_one hdetC
  simp only [moebiusMap, moebiusDenom, hc]
  push_cast
  rw [zero_mul, zero_add, div_eq_iff hdC]
  linear_combination (-((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ))) * hdetC

/-- The plane Möbius map of `inversionSL2` is `z ↦ -1/z` (with matching junk value at `0`). -/
theorem moebiusMap_inversionSL2 (z : ℂ) : moebiusMap inversionSL2 z = -1 / z := by
  simp [moebiusMap, moebiusDenom, inversionSL2]

/-- The plane Möbius map of `affineSL2 α β hα` is the affine map `z ↦ α z + β`. -/
theorem moebiusMap_affineSL2 {α : ℝ} (hα : 0 < α) (β : ℝ) (z : ℂ) :
    moebiusMap (affineSL2 α β hα) z = (α : ℂ) * z + (β : ℂ) := by
  have hs : Real.sqrt α ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hα)
  have hsC : (Real.sqrt α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsq : (Real.sqrt α : ℂ) * (Real.sqrt α : ℂ) = (α : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hα.le]
  have h00 : (affineSL2 α β hα) 0 0 = Real.sqrt α := by simp [affineSL2]
  have h01 : (affineSL2 α β hα) 0 1 = β / Real.sqrt α := by simp [affineSL2]
  have h10 : (affineSL2 α β hα) 1 0 = 0 := by simp [affineSL2]
  have h11 : (affineSL2 α β hα) 1 1 = 1 / Real.sqrt α := by simp [affineSL2]
  simp only [moebiusMap, moebiusDenom, h00, h01, h10, h11]
  push_cast
  rw [zero_mul, zero_add]
  field_simp
  linear_combination z * hsq

/-- Negating the matrix does not change the plane Möbius map: numerator and denominator both
change sign. -/
theorem moebiusMap_neg_matrix {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : (γ' : Matrix (Fin 2) (Fin 2) ℝ) = -(γ : Matrix (Fin 2) (Fin 2) ℝ)) (z : ℂ) :
    moebiusMap γ' z = moebiusMap γ z := by
  have h00 : γ' 0 0 = -(γ 0 0) := by rw [h, Matrix.neg_apply]
  have h01 : γ' 0 1 = -(γ 0 1) := by rw [h, Matrix.neg_apply]
  have h10 : γ' 1 0 = -(γ 1 0) := by rw [h, Matrix.neg_apply]
  have h11 : γ' 1 1 = -(γ 1 1) := by rw [h, Matrix.neg_apply]
  simp only [moebiusMap, moebiusDenom, h00, h01, h10, h11]
  push_cast
  rw [show -(γ 0 0 : ℂ) * z + -(γ 0 1 : ℂ) = -((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) by ring,
    show -(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ) = -((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) by ring,
    neg_div_neg_eq]

/-- An element of `SL(2, ℝ)` acts as the identity on the upper half plane exactly when it is
`±1`: a Möbius map with more than two fixed points is the identity. -/
theorem smul_id_iff_pm_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (∀ τ : UpperHalfPlane, A • τ = τ) ↔
      (A : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  constructor
  · intro hA
    have key : ∀ z : ℂ, 0 < z.im → moebiusMap A z = z := by
      intro z hz
      have h := congrArg UpperHalfPlane.coe (hA ⟨z, hz⟩)
      rwa [coe_smul_eq_moebiusMap] at h
    have quad : ∀ z : ℂ, 0 < z.im →
        (A 1 0 : ℂ) * z ^ 2 + ((A 1 1 : ℂ) - (A 0 0 : ℂ)) * z - (A 0 1 : ℂ) = 0 := by
      intro z hz
      have hden : moebiusDenom A z ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero A (ne_of_gt hz)
      have h := key z hz
      have h2 : ((A 0 0 : ℂ) * z + (A 0 1 : ℂ)) / moebiusDenom A z = z := h
      rw [div_eq_iff hden] at h2
      have h3 : (A 0 0 : ℂ) * z + (A 0 1 : ℂ) = z * ((A 1 0 : ℂ) * z + (A 1 1 : ℂ)) := h2
      linear_combination -h3
    have e1 := quad Complex.I (by simp)
    have e2 := quad (2 * Complex.I) (by simp)
    have e3 := quad (3 * Complex.I) (by simp)
    have e1' : -(A 1 0 : ℂ) + ((A 1 1 : ℂ) - (A 0 0 : ℂ)) * Complex.I - (A 0 1 : ℂ) = 0 := by
      linear_combination e1 - (A 1 0 : ℂ) * Complex.I_sq
    have e2' : -4 * (A 1 0 : ℂ) + 2 * ((A 1 1 : ℂ) - (A 0 0 : ℂ)) * Complex.I
        - (A 0 1 : ℂ) = 0 := by
      linear_combination e2 - 4 * (A 1 0 : ℂ) * Complex.I_sq
    have e3' : -9 * (A 1 0 : ℂ) + 3 * ((A 1 1 : ℂ) - (A 0 0 : ℂ)) * Complex.I
        - (A 0 1 : ℂ) = 0 := by
      linear_combination e3 - 9 * (A 1 0 : ℂ) * Complex.I_sq
    have hcC : (A 1 0 : ℂ) = 0 := by
      linear_combination (-1 / 2 : ℂ) * e1' + e2' - (1 / 2 : ℂ) * e3'
    have heI : ((A 1 1 : ℂ) - (A 0 0 : ℂ)) * Complex.I = 0 := by
      linear_combination e2' - e1' + 3 * hcC
    have heC : (A 1 1 : ℂ) - (A 0 0 : ℂ) = 0 :=
      (mul_eq_zero.mp heI).resolve_right Complex.I_ne_zero
    have hqC : (A 0 1 : ℂ) = 0 := by
      linear_combination -e1' - hcC + heI
    have hc0 : A 1 0 = 0 := by exact_mod_cast hcC
    have hq0 : A 0 1 = 0 := by exact_mod_cast hqC
    have he0 : A 1 1 = A 0 0 := by
      have : (A 1 1 : ℂ) = (A 0 0 : ℂ) := by linear_combination heC
      exact_mod_cast this
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe A
      rwa [Matrix.det_fin_two] at h
    rw [hq0, hc0, he0] at hdet
    simp only [mul_zero, sub_zero] at hdet
    have hfac : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      have ha : A 0 0 = 1 := by linarith [sub_eq_zero.mp h1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ha, hq0, hc0, he0]
    · right
      have ha : A 0 0 = -1 := by linarith [add_eq_zero_iff_eq_neg.mp h1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ha, hq0, hc0, he0]
  · rintro (h | h) τ
    · have hcoe : (A : Matrix (Fin 2) (Fin 2) ℝ)
          = ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [h, Matrix.SpecialLinearGroup.coe_one]
      have hA1 : A = (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) := Subtype.coe_injective hcoe
      rw [hA1, one_smul]
    · apply UpperHalfPlane.ext
      rw [coe_smul_eq_moebiusMap]
      have hneg : moebiusMap A (τ : ℂ) = moebiusMap 1 (τ : ℂ) := by
        refine moebiusMap_neg_matrix ?_ (τ : ℂ)
        rw [h, Matrix.SpecialLinearGroup.coe_one]
      rw [hneg, moebiusMap_one]

/-- A Möbius map of `SL(2, ℝ)` is determined by its values at three distinct non-pole points,
up to the global sign of the matrix. -/
theorem moebius_ext_three {V W : Matrix.SpecialLinearGroup (Fin 2) ℝ} {z₁ z₂ z₃ : ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hV : ∀ z ∈ ({z₁, z₂, z₃} : Set ℂ), moebiusDenom V z ≠ 0)
    (hW : ∀ z ∈ ({z₁, z₂, z₃} : Set ℂ), moebiusDenom W z ≠ 0)
    (h : ∀ z ∈ ({z₁, z₂, z₃} : Set ℂ), moebiusMap V z = moebiusMap W z) :
    (V : Matrix (Fin 2) (Fin 2) ℝ) = (W : Matrix (Fin 2) (Fin 2) ℝ) ∨
      (V : Matrix (Fin 2) (Fin 2) ℝ) = -(W : Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  have hback : ∀ z ∈ ({z₁, z₂, z₃} : Set ℂ), moebiusMap W⁻¹ (moebiusMap W z) = z := by
    intro z hz
    rw [moebiusMap_mul W⁻¹ W z (hW z hz), inv_mul_cancel, moebiusMap_one]
  have key : ∀ z ∈ ({z₁, z₂, z₃} : Set ℂ),
      ((V * W⁻¹) 1 0 : ℂ) * (moebiusMap W z) ^ 2
        + (((V * W⁻¹) 1 1 : ℂ) - ((V * W⁻¹) 0 0 : ℂ)) * moebiusMap W z
        - ((V * W⁻¹) 0 1 : ℂ) = 0 := by
    intro z hz
    have hWz := hW z hz
    have hVz := hV z hz
    have heq := h z hz
    have hcoc := moebiusDenom_mul W⁻¹ W z hWz
    rw [inv_mul_cancel, moebiusDenom_one] at hcoc
    have hWinvDen : moebiusDenom W⁻¹ (moebiusMap W z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcoc
      exact one_ne_zero hcoc.symm
    have hfix : moebiusMap (V * W⁻¹) (moebiusMap W z) = moebiusMap W z := by
      rw [← moebiusMap_mul V W⁻¹ (moebiusMap W z) hWinvDen, hback z hz, heq]
    have hUden : moebiusDenom (V * W⁻¹) (moebiusMap W z) ≠ 0 := by
      rw [← moebiusDenom_mul V W⁻¹ (moebiusMap W z) hWinvDen, hback z hz]
      exact mul_ne_zero hVz hWinvDen
    have h2 : (((V * W⁻¹) 0 0 : ℂ) * moebiusMap W z + ((V * W⁻¹) 0 1 : ℂ))
        / moebiusDenom (V * W⁻¹) (moebiusMap W z) = moebiusMap W z := hfix
    rw [div_eq_iff hUden] at h2
    have h3 : ((V * W⁻¹) 0 0 : ℂ) * moebiusMap W z + ((V * W⁻¹) 0 1 : ℂ)
        = moebiusMap W z * (((V * W⁻¹) 1 0 : ℂ) * moebiusMap W z + ((V * W⁻¹) 1 1 : ℂ)) := h2
    linear_combination -h3
  have hm1 : z₁ ∈ ({z₁, z₂, z₃} : Set ℂ) := by simp
  have hm2 : z₂ ∈ ({z₁, z₂, z₃} : Set ℂ) := by simp
  have hm3 : z₃ ∈ ({z₁, z₂, z₃} : Set ℂ) := by simp
  have hw12 : moebiusMap W z₁ ≠ moebiusMap W z₂ := by
    intro hcontra
    exact h12 (by rw [← hback z₁ hm1, hcontra, hback z₂ hm2])
  have hw13 : moebiusMap W z₁ ≠ moebiusMap W z₃ := by
    intro hcontra
    exact h13 (by rw [← hback z₁ hm1, hcontra, hback z₃ hm3])
  have hw23 : moebiusMap W z₂ ≠ moebiusMap W z₃ := by
    intro hcontra
    exact h23 (by rw [← hback z₂ hm2, hcontra, hback z₃ hm3])
  have e1 := key z₁ hm1
  have e2 := key z₂ hm2
  have e3 := key z₃ hm3
  have f12 : ((V * W⁻¹) 1 0 : ℂ) * (moebiusMap W z₁ + moebiusMap W z₂)
      + (((V * W⁻¹) 1 1 : ℂ) - ((V * W⁻¹) 0 0 : ℂ)) = 0 := by
    have hd := sub_ne_zero.mpr hw12
    have hz : (moebiusMap W z₁ - moebiusMap W z₂) * (((V * W⁻¹) 1 0 : ℂ)
        * (moebiusMap W z₁ + moebiusMap W z₂)
        + (((V * W⁻¹) 1 1 : ℂ) - ((V * W⁻¹) 0 0 : ℂ))) = 0 := by
      linear_combination e1 - e2
    exact (mul_eq_zero.mp hz).resolve_left hd
  have f13 : ((V * W⁻¹) 1 0 : ℂ) * (moebiusMap W z₁ + moebiusMap W z₃)
      + (((V * W⁻¹) 1 1 : ℂ) - ((V * W⁻¹) 0 0 : ℂ)) = 0 := by
    have hd := sub_ne_zero.mpr hw13
    have hz : (moebiusMap W z₁ - moebiusMap W z₃) * (((V * W⁻¹) 1 0 : ℂ)
        * (moebiusMap W z₁ + moebiusMap W z₃)
        + (((V * W⁻¹) 1 1 : ℂ) - ((V * W⁻¹) 0 0 : ℂ))) = 0 := by
      linear_combination e1 - e3
    exact (mul_eq_zero.mp hz).resolve_left hd
  have hcC : ((V * W⁻¹) 1 0 : ℂ) = 0 := by
    have hd := sub_ne_zero.mpr hw23
    have hz : ((V * W⁻¹) 1 0 : ℂ) * (moebiusMap W z₂ - moebiusMap W z₃) = 0 := by
      linear_combination f12 - f13
    exact (mul_eq_zero.mp hz).resolve_right hd
  have heC : ((V * W⁻¹) 1 1 : ℂ) - ((V * W⁻¹) 0 0 : ℂ) = 0 := by
    linear_combination f12 - (moebiusMap W z₁ + moebiusMap W z₂) * hcC
  have hqC : ((V * W⁻¹) 0 1 : ℂ) = 0 := by
    linear_combination -e1 + (moebiusMap W z₁) ^ 2 * hcC + moebiusMap W z₁ * heC
  have hc0 : (V * W⁻¹) 1 0 = 0 := by exact_mod_cast hcC
  have hq0 : (V * W⁻¹) 0 1 = 0 := by exact_mod_cast hqC
  have he0 : (V * W⁻¹) 1 1 = (V * W⁻¹) 0 0 := by
    have : ((V * W⁻¹) 1 1 : ℂ) = ((V * W⁻¹) 0 0 : ℂ) := by linear_combination heC
    exact_mod_cast this
  have hdet : (V * W⁻¹) 0 0 * (V * W⁻¹) 1 1 - (V * W⁻¹) 0 1 * (V * W⁻¹) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (V * W⁻¹)
    rwa [Matrix.det_fin_two] at h
  rw [hq0, hc0, he0] at hdet
  simp only [mul_zero, sub_zero] at hdet
  have hfac : ((V * W⁻¹) 0 0 - 1) * ((V * W⁻¹) 0 0 + 1) = 0 := by linear_combination hdet
  have hVU : V = (V * W⁻¹) * W := by rw [inv_mul_cancel_right]
  have hcoeV : (V : Matrix (Fin 2) (Fin 2) ℝ)
      = ((V * W⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * (W : Matrix (Fin 2) (Fin 2) ℝ) := by
    conv_lhs => rw [hVU]
    rw [Matrix.SpecialLinearGroup.coe_mul]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left
    have ha : (V * W⁻¹) 0 0 = 1 := by linarith [sub_eq_zero.mp h1]
    have hUone : ((V * W⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hq0, hc0, he0]
    rw [hcoeV, hUone, one_mul]
  · right
    have ha : (V * W⁻¹) 0 0 = -1 := by linarith [add_eq_zero_iff_eq_neg.mp h1]
    have hUneg : ((V * W⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hq0, hc0, he0]
    rw [hcoeV, hUneg, neg_one_mul]

/-! ## Monotonicity, named dilatation wrapper, coefficient trivia -/

/-- Geometric quasiconformality is monotone in the dilatation constant. -/
theorem IsQCGeometric.mono {f : ℂ → ℂ} {K K' : ℝ} (hf : IsQCGeometric f K) (hK : K ≤ K') :
    IsQCGeometric f K' := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨h1.trans hK, h2, fun Q => ?_⟩
  exact (h3 Q).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK) _)

/-- A quasiconformal map with Beltrami coefficient `b` is geometrically `b.K`-quasiconformal,
where `K = (1 + ‖μ‖∞) / (1 − ‖μ‖∞)` is the maximal dilatation. -/
theorem IsQCAnalytic.isQCGeometric_K {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) : IsQCGeometric f b.K := by
  have hm0 := b.normInf_nonneg
  have hm1 := b.normInf_lt_one
  have hK1 : 1 ≤ b.K := b.one_le_K
  have hden : (0 : ℝ) < 1 - b.normInf := by linarith
  have hKeq : b.K * (1 - b.normInf) = 1 + b.normInf := by
    rw [show b.K = (1 + b.normInf) / (1 - b.normInf) from rfl,
      div_mul_cancel₀ _ (ne_of_gt hden)]
  have hKpos : (0 : ℝ) < b.K + 1 := by linarith
  have hbnd : b.normInf ≤ (b.K - 1) / (b.K + 1) := by
    rw [le_div_iff₀ hKpos]
    nlinarith [hKeq]
  exact isQCGeometric_of_isQCAnalytic hK1 hbnd hf

/-- The Beltrami equation only sees the coefficient almost everywhere: coefficients that agree
a.e. have the same quasiconformal solutions. -/
theorem IsQCAnalytic.congr_coeff {f : ℂ → ℂ} {b b' : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (h : b.μ =ᵐ[volume] b'.μ) : IsQCAnalytic f b' := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨h1, h2, ?_⟩
  filter_upwards [h3, h] with z hz hμ
  rw [hz, hμ]

/-- A quasiconformal plane map is injective. -/
theorem IsQCAnalytic.injective {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) :
    Function.Injective f :=
  hf.1.1.bijective.injective

/-! ## Wirtinger chain rules -/

/-- Pointwise Wirtinger `∂` chain rule for precomposition with a map holomorphic at `z`. -/
theorem dz_comp_of_holomorphicAt {f g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z)
    (hf : DifferentiableAt ℝ f (g z)) :
    dz (f ∘ g) z = dz f (g z) * deriv g z := by
  have h := dz_comp (differentiableAt_complex_iff_differentiableAt_real.mp hg).1 hf
  rw [dz_eq_deriv_of_differentiableAt hg, dzbar_eq_zero_of_differentiableAt hg] at h
  simpa [Function.comp_def] using h

/-- Pointwise Wirtinger `∂̄` chain rule for precomposition with a map holomorphic at `z`. -/
theorem dzbar_comp_of_holomorphicAt {f g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z)
    (hf : DifferentiableAt ℝ f (g z)) :
    dzbar (f ∘ g) z = dzbar f (g z) * starRingEnd ℂ (deriv g z) := by
  have h := dzbar_comp (differentiableAt_complex_iff_differentiableAt_real.mp hg).1 hf
  rw [dz_eq_deriv_of_differentiableAt hg, dzbar_eq_zero_of_differentiableAt hg] at h
  simpa [Function.comp_def] using h

/-- Wirtinger `∂` chain rule for precomposition with the affine map `z ↦ c z + x₀`. Where `f`
is not real-differentiable at the image point both sides are the junk value `0`. -/
theorem dz_comp_affine (f : ℂ → ℂ) {c : ℂ} (hc : c ≠ 0) (x₀ z : ℂ) :
    dz (f ∘ affineMap c x₀) z = dz f (affineMap c x₀ z) * c := by
  have hAd : DifferentiableAt ℂ (affineMap c x₀) z := (affineMap_differentiable c x₀) z
  have hAderiv : deriv (affineMap c x₀) z = c := by
    have h0 : HasDerivAt (fun w : ℂ => c * w + x₀) c z := by
      simpa using ((hasDerivAt_id z).const_mul c).add_const x₀
    exact h0.deriv
  by_cases hf : DifferentiableAt ℝ f (affineMap c x₀ z)
  · rw [dz_comp_of_holomorphicAt hAd hf, hAderiv]
  · have hnd : ¬ DifferentiableAt ℝ (f ∘ affineMap c x₀) z := by
      intro hcomp
      apply hf
      have hinv : DifferentiableAt ℝ (fun w : ℂ => (w - x₀) / c) (affineMap c x₀ z) := by
        fun_prop
      have harg : (fun w : ℂ => (w - x₀) / c) (affineMap c x₀ z) = z := by
        change (affineMap c x₀ z - x₀) / c = z
        rw [affineMap_apply, add_sub_cancel_right, mul_div_cancel_left₀ _ hc]
      have houter : DifferentiableAt ℝ (f ∘ affineMap c x₀)
          ((fun w : ℂ => (w - x₀) / c) (affineMap c x₀ z)) := by
        rw [harg]
        exact hcomp
      have hcompinv := DifferentiableAt.comp (affineMap c x₀ z) houter hinv
      have hid : (f ∘ affineMap c x₀) ∘ (fun w : ℂ => (w - x₀) / c) = f := by
        funext w
        simp only [Function.comp_apply, affineMap_apply]
        rw [mul_div_cancel₀ _ hc, sub_add_cancel]
      rwa [hid] at hcompinv
    simp only [dz, fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hnd, zero_apply, mul_zero,
      sub_zero, zero_mul]

/-- Wirtinger `∂̄` chain rule for precomposition with the affine map `z ↦ c z + x₀`. -/
theorem dzbar_comp_affine (f : ℂ → ℂ) {c : ℂ} (hc : c ≠ 0) (x₀ z : ℂ) :
    dzbar (f ∘ affineMap c x₀) z = dzbar f (affineMap c x₀ z) * starRingEnd ℂ c := by
  have hAd : DifferentiableAt ℂ (affineMap c x₀) z := (affineMap_differentiable c x₀) z
  have hAderiv : deriv (affineMap c x₀) z = c := by
    have h0 : HasDerivAt (fun w : ℂ => c * w + x₀) c z := by
      simpa using ((hasDerivAt_id z).const_mul c).add_const x₀
    exact h0.deriv
  by_cases hf : DifferentiableAt ℝ f (affineMap c x₀ z)
  · rw [dzbar_comp_of_holomorphicAt hAd hf, hAderiv]
  · have hnd : ¬ DifferentiableAt ℝ (f ∘ affineMap c x₀) z := by
      intro hcomp
      apply hf
      have hinv : DifferentiableAt ℝ (fun w : ℂ => (w - x₀) / c) (affineMap c x₀ z) := by
        fun_prop
      have harg : (fun w : ℂ => (w - x₀) / c) (affineMap c x₀ z) = z := by
        change (affineMap c x₀ z - x₀) / c = z
        rw [affineMap_apply, add_sub_cancel_right, mul_div_cancel_left₀ _ hc]
      have houter : DifferentiableAt ℝ (f ∘ affineMap c x₀)
          ((fun w : ℂ => (w - x₀) / c) (affineMap c x₀ z)) := by
        rw [harg]
        exact hcomp
      have hcompinv := DifferentiableAt.comp (affineMap c x₀ z) houter hinv
      have hid : (f ∘ affineMap c x₀) ∘ (fun w : ℂ => (w - x₀) / c) = f := by
        funext w
        simp only [Function.comp_apply, affineMap_apply]
        rw [mul_div_cancel₀ _ hc, sub_add_cancel]
      rwa [hid] at hcompinv
    simp only [dzbar, fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hnd, zero_apply, mul_zero,
      add_zero, zero_mul]

/-- Wirtinger `∂` rule for conjugation by `conj`: for `G z = conj (f (conj z))` one has
`∂G(z) = conj (∂f(z̄))`, unconditionally (junk values transport through the conjugation). -/
theorem dz_conj_conj (f : ℂ → ℂ) (z : ℂ) :
    dz (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) z
      = starRingEnd ℂ (dz f (starRingEnd ℂ z)) := by
  have h1 : dz (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) z
      = starRingEnd ℂ (dzbar (fun w => f (starRingEnd ℂ w)) z) :=
    dz_conj (fun w => f (starRingEnd ℂ w)) z
  have h2 : dzbar (fun w => f (starRingEnd ℂ w)) z = dz f (starRingEnd ℂ z) := by
    have hE : (fun w : ℂ => f (starRingEnd ℂ w)) = f ∘ ⇑Complex.conjCLE := by
      funext w
      simp
    rw [hE]
    simp only [dzbar, dz, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one,
      Complex.conj_I, map_neg]
    ring
  rw [h1, h2]

/-- Wirtinger `∂̄` rule for conjugation by `conj`: for `G z = conj (f (conj z))` one has
`∂̄G(z) = conj (∂̄f(z̄))`, unconditionally. -/
theorem dzbar_conj_conj (f : ℂ → ℂ) (z : ℂ) :
    dzbar (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) z
      = starRingEnd ℂ (dzbar f (starRingEnd ℂ z)) := by
  have h1 : dzbar (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) z
      = starRingEnd ℂ (dz (fun w => f (starRingEnd ℂ w)) z) :=
    dzbar_conj (fun w => f (starRingEnd ℂ w)) z
  have h2 : dz (fun w => f (starRingEnd ℂ w)) z = dzbar f (starRingEnd ℂ z) := by
    have hE : (fun w : ℂ => f (starRingEnd ℂ w)) = f ∘ ⇑Complex.conjCLE := by
      funext w
      simp
    rw [hE]
    simp only [dz, dzbar, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one,
      Complex.conj_I, map_neg]
    ring
  rw [h1, h2]

/-! ## Affine post- and precomposition of quasiconformal maps -/

/-- Post-composition with a nonzero affine map `w ↦ a w + β` preserves quasiconformality with
the SAME Beltrami coefficient: both Wirtinger derivatives scale by `a`. -/
theorem IsQCAnalytic.affine_postcomp {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {a : ℂ} (ha : a ≠ 0) (β : ℂ) :
    IsQCAnalytic (fun z => a * f z + β) b := by
  obtain ⟨⟨hFhomeo, hFdet⟩, hFW12, hFbelt⟩ := hf
  have hFcont : Continuous f := hFhomeo.continuous
  have hFdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z := by
    filter_upwards [hFdet] with z hz
    by_contra hnd
    rw [det_fderiv_eq_wirtinger] at hz
    simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hnd] at hz
  have hkey : ∀ᵐ z : ℂ, fderiv ℝ (fun w => a * f w + β) z = a • fderiv ℝ f z := by
    filter_upwards [hFdiff] with z hz
    have hfun : (fun w => a * f w + β) = fun w => (a • f) w + β := by
      funext w
      simp [smul_eq_mul]
    rw [hfun, fderiv_add_const, fderiv_const_smul hz a]
  have hdzs : ∀ᵐ z : ℂ, dz (fun w => a * f w + β) z = a * dz f z
      ∧ dzbar (fun w => a * f w + β) z = a * dzbar f z := by
    filter_upwards [hkey] with z hk
    constructor
    · simp only [dz, hk, smul_apply, smul_eq_mul]
      ring
    · simp only [dzbar, hk, smul_apply, smul_eq_mul]
      ring
  have hAhomeo : IsHomeomorph (fun z => a * f z + β) := by
    have h1 := ((Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight β)).isHomeomorph
    have h2 : ⇑((Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight β))
        = fun w : ℂ => a * w + β := by
      funext w
      simp [Homeomorph.trans_apply]
    rw [h2] at h1
    have h3 := h1.comp hFhomeo
    simpa [Function.comp_def] using h3
  have hAdet : ∀ᵐ z : ℂ, 0 < (fderiv ℝ (fun w => a * f w + β) z).det := by
    filter_upwards [hdzs, hFdet] with z hdw hd
    rw [det_fderiv_eq_wirtinger, hdw.1, hdw.2, norm_mul, norm_mul, mul_pow, mul_pow, ← mul_sub]
    rw [det_fderiv_eq_wirtinger] at hd
    exact mul_pos (pow_pos (norm_pos_iff.mpr ha) 2) hd
  have hAcont : Continuous fun z => a * f z + β :=
    (continuous_const.mul hFcont).add continuous_const
  have hLIofL2 : ∀ {w : ℂ → ℂ}, MemLpLocOn w 2 Set.univ → LocallyIntegrableOn w Set.univ := by
    intro w hw
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro Kc hKc
    have : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hw Kc (Set.subset_univ _) hKc).mono_exponent (by norm_num))
  obtain ⟨hFloc, gx, gy, hFgrad, hgx, hgy⟩ := hFW12
  have hconst : ∀ v : ℂ, HasWeakDirDeriv v (fun _ : ℂ => (0 : ℂ)) (fun _ : ℂ => β)
      Set.univ := by
    intro v
    have h := HasWeakDirDeriv.of_contDiffOn (v := v) isOpen_univ (contDiffOn_const (c := β))
    have hzero : (fun z : ℂ => (fderiv ℝ (fun _ : ℂ => β) z) v) = fun _ => (0 : ℂ) := by
      funext z
      rw [(hasFDerivAt_const β z).fderiv]
      simp
    rwa [hzero] at h
  have hLIaf : LocallyIntegrableOn (fun z => a * f z) Set.univ :=
    (continuous_const.mul hFcont).locallyIntegrable.locallyIntegrableOn _
  have hLIc : LocallyIntegrableOn (fun _ : ℂ => β) Set.univ :=
    continuous_const.locallyIntegrable.locallyIntegrableOn _
  have hLI0 : LocallyIntegrableOn (fun _ : ℂ => (0 : ℂ)) Set.univ :=
    continuous_const.locallyIntegrable.locallyIntegrableOn _
  have hgax : MemLpLocOn (fun z => a * gx z) 2 Set.univ :=
    fun Kc hs hKc => (hgx Kc hs hKc).const_mul a
  have hgay : MemLpLocOn (fun z => a * gy z) 2 Set.univ :=
    fun Kc hs hKc => (hgy Kc hs hKc).const_mul a
  have hgoalx : HasWeakDirDeriv 1 (fun z => a * gx z) (fun z => a * f z + β) Set.univ := by
    have h1 : HasWeakDirDeriv 1 (fun z => a * gx z) (fun z => a * f z) Set.univ := by
      simpa [smul_eq_mul] using HasWeakDirDeriv.const_smul a hFgrad.1
    have hsum := HasWeakDirDeriv.add h1 (hconst 1) hLIaf hLIc (hLIofL2 hgax) hLI0
    simpa using hsum
  have hgoaly : HasWeakDirDeriv Complex.I (fun z => a * gy z) (fun z => a * f z + β)
      Set.univ := by
    have h1 : HasWeakDirDeriv Complex.I (fun z => a * gy z) (fun z => a * f z) Set.univ := by
      simpa [smul_eq_mul] using HasWeakDirDeriv.const_smul a hFgrad.2
    have hsum := HasWeakDirDeriv.add h1 (hconst Complex.I) hLIaf hLIc (hLIofL2 hgay) hLI0
    simpa using hsum
  have hAloc : MemLpLocOn (fun z => a * f z + β) 2 Set.univ := by
    intro Kc _ hKc
    have : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hAcont.continuousOn
    refine MemLp.of_bound hAcont.aestronglyMeasurable.restrict C ?_
    filter_upwards [ae_restrict_mem hKc.measurableSet] with z hz
    exact hC z hz
  have hAbelt : ∀ᵐ z : ℂ, dzbar (fun w => a * f w + β) z
      = b.μ z * dz (fun w => a * f w + β) z := by
    filter_upwards [hdzs, hFbelt] with z hdw hb
    rw [hdw.1, hdw.2, hb]
    ring
  exact ⟨⟨hAhomeo, hAdet⟩, ⟨hAloc, fun z => a * gx z, fun z => a * gy z, ⟨hgoalx, hgoaly⟩,
    hgax, hgay⟩, hAbelt⟩

/-- The essential supremum bound of the affine pullback coefficient
`z ↦ μ(c z + x₀) · (c̄ / c)`: the unimodular factor and the volume-scaling change of variable
preserve the essential supremum. -/
theorem BeltramiCoeff.pullbackAffine_bound (b : BeltramiCoeff) {c : ℂ} (hc : c ≠ 0)
    (x₀ : ℂ) :
    eLpNormEssSup (fun z => b.μ (c * z + x₀) * (starRingEnd ℂ c / c)) volume < 1 := by
  have hns : (0 : ℝ) < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hMapp : ⇑((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) = fun w : ℂ => c * w := rfl
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
      (f := ((((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))
      (by rw [hdetL]; exact ne_of_gt hns)
    rw [hdetL, abs_of_pos (inv_pos.mpr hns)] at h
    exact h
  have hmap : Measure.map (fun z : ℂ => c * z + x₀) volume
      = ENNReal.ofReal ((Complex.normSq c)⁻¹) • volume := by
    have hcm : Measurable fun w : ℂ => c * w := measurable_id.const_mul c
    have hcomp : (fun z : ℂ => c * z + x₀) = (fun y : ℂ => y + x₀) ∘ fun w : ℂ => c * w := rfl
    rw [hcomp, ← Measure.map_map (measurable_add_const x₀) hcm, hmapmul, Measure.map_smul,
      (measurePreserving_add_right volume x₀).map_eq]
  have hu1 : ‖starRingEnd ℂ c / c‖ₑ = 1 := by
    rw [← ofReal_norm, norm_div, RCLike.norm_conj,
      div_self (norm_ne_zero_iff.mpr hc), ENNReal.ofReal_one]
  have key : eLpNormEssSup (fun z : ℂ => b.μ (c * z + x₀) * (starRingEnd ℂ c / c)) volume
      = eLpNormEssSup b.μ volume := by
    rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    have hfun : (fun z : ℂ => ‖b.μ (c * z + x₀) * (starRingEnd ℂ c / c)‖ₑ)
        = (fun w : ℂ => ‖b.μ w‖ₑ) ∘ fun z : ℂ => c * z + x₀ := by
      funext z
      simp only [Function.comp_apply, enorm_mul, hu1, mul_one]
    rw [hfun, ← essSup_map_measure (b.measurable.enorm.aemeasurable)
        (((measurable_id'.const_mul c).add_const x₀).aemeasurable), hmap,
      essSup_ennreal_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hns)))]
  rw [key]
  exact b.bound

/-- The pullback of a Beltrami coefficient under the affine map `z ↦ c z + x₀`: the
coefficient of `f ∘ (c · + x₀)` when `μ` is the coefficient of `f`. -/
noncomputable def BeltramiCoeff.pullbackAffine (b : BeltramiCoeff) {c : ℂ} (hc : c ≠ 0)
    (x₀ : ℂ) : BeltramiCoeff where
  μ := fun z => b.μ (c * z + x₀) * (starRingEnd ℂ c / c)
  measurable := (b.measurable.comp ((measurable_id.const_mul c).add_const x₀)).mul_const _
  bound := b.pullbackAffine_bound hc x₀

/-- The affine pullback does not change the essential supremum norm. -/
theorem BeltramiCoeff.normInf_pullbackAffine (b : BeltramiCoeff) {c : ℂ} (hc : c ≠ 0)
    (x₀ : ℂ) : (b.pullbackAffine hc x₀).normInf = b.normInf := by
  have hns : (0 : ℝ) < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hMapp : ⇑((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) = fun w : ℂ => c * w := rfl
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
      (f := ((((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))
      (by rw [hdetL]; exact ne_of_gt hns)
    rw [hdetL, abs_of_pos (inv_pos.mpr hns)] at h
    exact h
  have hmap : Measure.map (fun z : ℂ => c * z + x₀) volume
      = ENNReal.ofReal ((Complex.normSq c)⁻¹) • volume := by
    have hcm : Measurable fun w : ℂ => c * w := measurable_id.const_mul c
    have hcomp : (fun z : ℂ => c * z + x₀) = (fun y : ℂ => y + x₀) ∘ fun w : ℂ => c * w := rfl
    rw [hcomp, ← Measure.map_map (measurable_add_const x₀) hcm, hmapmul, Measure.map_smul,
      (measurePreserving_add_right volume x₀).map_eq]
  have hu1 : ‖starRingEnd ℂ c / c‖ₑ = 1 := by
    rw [← ofReal_norm, norm_div, RCLike.norm_conj,
      div_self (norm_ne_zero_iff.mpr hc), ENNReal.ofReal_one]
  have key : eLpNormEssSup (fun z : ℂ => b.μ (c * z + x₀) * (starRingEnd ℂ c / c)) volume
      = eLpNormEssSup b.μ volume := by
    rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    have hfun : (fun z : ℂ => ‖b.μ (c * z + x₀) * (starRingEnd ℂ c / c)‖ₑ)
        = (fun w : ℂ => ‖b.μ w‖ₑ) ∘ fun z : ℂ => c * z + x₀ := by
      funext z
      simp only [Function.comp_apply, enorm_mul, hu1, mul_one]
    rw [hfun, ← essSup_map_measure (b.measurable.enorm.aemeasurable)
        (((measurable_id'.const_mul c).add_const x₀).aemeasurable), hmap,
      essSup_ennreal_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hns)))]
  have hμ : (b.pullbackAffine hc x₀).μ
      = fun z => b.μ (c * z + x₀) * (starRingEnd ℂ c / c) := rfl
  simp only [BeltramiCoeff.normInf, hμ]
  rw [key]

/-- Precomposition with the affine map `z ↦ c z + x₀` transforms the Beltrami coefficient by
the affine pullback `μ(c z + x₀) · (c̄ / c)`. -/
theorem isQCAnalytic_comp_affine {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    {c : ℂ} (hc : c ≠ 0) (x₀ : ℂ) :
    IsQCAnalytic (f ∘ affineMap c x₀) (b.pullbackAffine hc x₀) := by
  -- the geometric round trip supplies the homeomorphism, orientation and Sobolev data
  have hm0 := b.normInf_nonneg
  have hm1 := b.normInf_lt_one
  have hK1 : 1 ≤ b.K := b.one_le_K
  have hbnd : b.normInf ≤ (b.K - 1) / (b.K + 1) := by
    have hden : (0 : ℝ) < 1 - b.normInf := by linarith
    have hKval : b.K = (1 + b.normInf) / (1 - b.normInf) := rfl
    have hKeq : b.K * (1 - b.normInf) = 1 + b.normInf := by
      rw [hKval, div_mul_cancel₀ _ (ne_of_gt hden)]
    have hKpos : (0 : ℝ) < b.K + 1 := by linarith
    rw [le_div_iff₀ hKpos]
    nlinarith [hKeq]
  have hgeo : IsQCGeometric f b.K := isQCGeometric_of_isQCAnalytic hK1 hbnd hf
  have hgeoA : IsQCGeometric (f ∘ affineMap c x₀) b.K := isQCGeometric_comp_affine hgeo hc x₀
  obtain ⟨b', _hb'norm, hb'⟩ := isQCAnalytic_of_isQCGeometric hK1 hgeoA
  refine ⟨hb'.1, hb'.2.1, ?_⟩
  -- the affine map is quasi-measure-preserving: its pushforward is a scaled volume
  have hns : (0 : ℝ) < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hMapp : ⇑((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) = fun w : ℂ => c * w := rfl
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
      (f := ((((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))
      (by rw [hdetL]; exact ne_of_gt hns)
    rw [hdetL, abs_of_pos (inv_pos.mpr hns)] at h
    exact h
  have hmap : Measure.map (fun z : ℂ => c * z + x₀) volume
      = ENNReal.ofReal ((Complex.normSq c)⁻¹) • volume := by
    have hcm : Measurable fun w : ℂ => c * w := measurable_id.const_mul c
    have hcomp : (fun z : ℂ => c * z + x₀) = (fun y : ℂ => y + x₀) ∘ fun w : ℂ => c * w := rfl
    rw [hcomp, ← Measure.map_map (measurable_add_const x₀) hcm, hmapmul, Measure.map_smul,
      (measurePreserving_add_right volume x₀).map_eq]
  have hqmp : Measure.QuasiMeasurePreserving (fun z : ℂ => c * z + x₀) volume volume :=
    ⟨(measurable_id'.const_mul c).add_const x₀, by
      rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  have hbelt : ∀ᵐ z : ℂ, dzbar f (c * z + x₀) = b.μ (c * z + x₀) * dz f (c * z + x₀) :=
    hqmp.ae hf.2.2
  filter_upwards [hbelt] with z hz
  rw [dzbar_comp_affine f hc x₀ z, dz_comp_affine f hc x₀ z]
  have hμ : (b.pullbackAffine hc x₀).μ z = b.μ (c * z + x₀) * (starRingEnd ℂ c / c) := rfl
  rw [hμ, affineMap_apply, hz]
  field_simp

/-! ## Reflection symmetry across the real axis -/

/-- A Beltrami coefficient is **symmetric** when it commutes a.e. with complex conjugation:
`μ(z̄) = conj (μ(z))`. Symmetric coefficients are the ones whose normalized solutions fix the
real line. -/
def IsSymmetricBeltrami (b : BeltramiCoeff) : Prop :=
  ∀ᵐ z : ℂ, b.μ (starRingEnd ℂ z) = starRingEnd ℂ (b.μ z)

/-- The essential supremum bound of the reflected coefficient `z ↦ conj (μ (conj z))`:
conjugation is a pointwise isometry and a volume-preserving change of variable. -/
theorem BeltramiCoeff.reflect_bound (b : BeltramiCoeff) :
    eLpNormEssSup (fun z => starRingEnd ℂ (b.μ (starRingEnd ℂ z))) volume < 1 := by
  have hmp : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) volume volume := by
    have h := Complex.conjLIE.measurePreserving
    have heq : (fun z : ℂ => starRingEnd ℂ z) = ⇑Complex.conjLIE := by
      funext z
      rw [Complex.conjLIE_apply]
    rw [heq]
    exact h
  have h1 : eLpNormEssSup (fun z => starRingEnd ℂ (b.μ (starRingEnd ℂ z))) volume
      = eLpNormEssSup (fun z => b.μ (starRingEnd ℂ z)) volume := by
    simp only [eLpNormEssSup]
    congr 1
    funext z
    simp
  have hmeas : AEStronglyMeasurable b.μ
      (Measure.map (fun z : ℂ => starRingEnd ℂ z) volume) := by
    rw [hmp.map_eq]
    exact b.measurable.aestronglyMeasurable
  have h2 := eLpNormEssSup_map_measure hmeas hmp.measurable.aemeasurable
  rw [hmp.map_eq] at h2
  rw [h1, show (fun z => b.μ (starRingEnd ℂ z)) = b.μ ∘ (fun z : ℂ => starRingEnd ℂ z)
    from rfl, ← h2]
  exact b.bound

/-- The reflected Beltrami coefficient `z ↦ conj (μ (conj z))`: the coefficient of
`conj ∘ f ∘ conj` when `μ` is the coefficient of `f`. -/
noncomputable def BeltramiCoeff.reflect (b : BeltramiCoeff) : BeltramiCoeff where
  μ := fun z => starRingEnd ℂ (b.μ (starRingEnd ℂ z))
  measurable :=
    Complex.continuous_conj.measurable.comp
      (b.measurable.comp Complex.continuous_conj.measurable)
  bound := b.reflect_bound

/-- Reflection does not change the essential supremum norm. -/
theorem BeltramiCoeff.normInf_reflect (b : BeltramiCoeff) :
    b.reflect.normInf = b.normInf := by
  have hmp : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) volume volume := by
    have h := Complex.conjLIE.measurePreserving
    have heq : (fun z : ℂ => starRingEnd ℂ z) = ⇑Complex.conjLIE := by
      funext z
      rw [Complex.conjLIE_apply]
    rw [heq]
    exact h
  have h1 : eLpNormEssSup (fun z => starRingEnd ℂ (b.μ (starRingEnd ℂ z))) volume
      = eLpNormEssSup (fun z => b.μ (starRingEnd ℂ z)) volume := by
    simp only [eLpNormEssSup]
    congr 1
    funext z
    simp
  have hmeas : AEStronglyMeasurable b.μ
      (Measure.map (fun z : ℂ => starRingEnd ℂ z) volume) := by
    rw [hmp.map_eq]
    exact b.measurable.aestronglyMeasurable
  have h2 := eLpNormEssSup_map_measure hmeas hmp.measurable.aemeasurable
  rw [hmp.map_eq] at h2
  simp only [BeltramiCoeff.normInf]
  congr 1
  have hμ : b.reflect.μ = fun z => starRingEnd ℂ (b.μ (starRingEnd ℂ z)) := rfl
  rw [hμ, h1, show (fun z => b.μ (starRingEnd ℂ z)) = b.μ ∘ (fun z : ℂ => starRingEnd ℂ z)
    from rfl, ← h2]

/-- Symmetry of a Beltrami coefficient is a.e. equality with its reflection. -/
theorem isSymmetricBeltrami_iff_reflect (b : BeltramiCoeff) :
    IsSymmetricBeltrami b ↔ b.reflect.μ =ᵐ[volume] b.μ := by
  constructor
  · intro hsym
    filter_upwards [hsym] with z hz
    change starRingEnd ℂ (b.μ (starRingEnd ℂ z)) = b.μ z
    rw [hz, Complex.conj_conj]
  · intro hrefl
    unfold IsSymmetricBeltrami
    filter_upwards [hrefl] with z hz
    have hz' : starRingEnd ℂ (b.μ (starRingEnd ℂ z)) = b.μ z := hz
    rw [← hz', Complex.conj_conj]

/-- Conjugating a quasiconformal map by complex conjugation reflects its Beltrami
coefficient: if `∂̄f = μ ∂f` then `G = conj ∘ f ∘ conj` satisfies `∂̄G = μ̃ ∂G` with
`μ̃(z) = conj (μ(z̄))`. -/
theorem isQCAnalytic_conj_conj {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) :
    IsQCAnalytic (fun z => starRingEnd ℂ (f (starRingEnd ℂ z))) b.reflect := by
  -- conjugation as a measure-preserving measurable embedding
  have hmp : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) volume volume := by
    have h := Complex.conjLIE.measurePreserving
    have he : ⇑Complex.conjLIE = fun z : ℂ => starRingEnd ℂ z := by
      funext z
      simp [Complex.conjLIE_apply]
    rwa [he] at h
  have hemb : MeasurableEmbedding (fun z : ℂ => starRingEnd ℂ z) := by
    have h := Complex.conjLIE.toHomeomorph.measurableEmbedding
    have he : ⇑Complex.conjLIE.toHomeomorph = fun z : ℂ => starRingEnd ℂ z := by
      funext z
      simp [LinearIsometryEquiv.coe_toHomeomorph, Complex.conjLIE_apply]
    rwa [he] at h
  obtain ⟨⟨hFhomeo, hFdet⟩, hFW12, hFbelt⟩ := hf
  have hFcont : Continuous f := hFhomeo.continuous
  -- homeomorphism
  have hconjHomeo : IsHomeomorph (fun z : ℂ => starRingEnd ℂ z) := by
    have h := Complex.conjCLE.toHomeomorph.isHomeomorph
    have he : ⇑Complex.conjCLE.toHomeomorph = fun z : ℂ => starRingEnd ℂ z := by
      funext z
      simp [ContinuousLinearEquiv.coe_toHomeomorph]
    rwa [he] at h
  have hGhomeo : IsHomeomorph (fun z : ℂ => starRingEnd ℂ (f (starRingEnd ℂ z))) := by
    have h := (hconjHomeo.comp hFhomeo).comp hconjHomeo
    simpa [Function.comp_def] using h
  -- orientation: the Jacobian is invariant under the double conjugation
  have hGdet : ∀ᵐ z : ℂ,
      0 < (fderiv ℝ (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) z).det := by
    have hae : ∀ᵐ z : ℂ, 0 < (fderiv ℝ f (starRingEnd ℂ z)).det :=
      hmp.quasiMeasurePreserving.ae hFdet
    filter_upwards [hae] with z hz
    rw [det_fderiv_eq_wirtinger, dz_conj_conj f z, dzbar_conj_conj f z,
      RCLike.norm_conj, RCLike.norm_conj]
    rw [det_fderiv_eq_wirtinger] at hz
    exact hz
  -- the Beltrami equation for the reflected coefficient
  have hGbelt : ∀ᵐ z : ℂ, dzbar (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) z
      = b.reflect.μ z * dz (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) z := by
    have hae : ∀ᵐ z : ℂ, dzbar f (starRingEnd ℂ z)
        = b.μ (starRingEnd ℂ z) * dz f (starRingEnd ℂ z) :=
      hmp.quasiMeasurePreserving.ae hFbelt
    filter_upwards [hae] with z hz
    rw [dzbar_conj_conj f z, dz_conj_conj f z, hz, map_mul]
    rfl
  -- Sobolev membership
  obtain ⟨hFloc, gx, gy, hFgrad, hgx, hgy⟩ := hFW12
  have hGcont : Continuous (fun z : ℂ => starRingEnd ℂ (f (starRingEnd ℂ z))) :=
    Complex.continuous_conj.comp (hFcont.comp Complex.continuous_conj)
  have hGloc : MemLpLocOn (fun z : ℂ => starRingEnd ℂ (f (starRingEnd ℂ z))) 2 Set.univ := by
    intro Kc _ hKc
    have : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hGcont.continuousOn
    refine MemLp.of_bound hGcont.aestronglyMeasurable.restrict C ?_
    filter_upwards [ae_restrict_mem hKc.measurableSet] with z hz
    exact hC z hz
  -- local square-integrability transfers through the double conjugation
  have hLpConj : ∀ g : ℂ → ℂ, MemLpLocOn g 2 Set.univ →
      MemLpLocOn (fun z => starRingEnd ℂ (g (starRingEnd ℂ z))) 2 Set.univ := by
    intro g hg Kc _ hKc
    have hKim : IsCompact ((fun z : ℂ => starRingEnd ℂ z) '' Kc) :=
      hKc.image Complex.continuous_conj
    have hpre : (fun z : ℂ => starRingEnd ℂ z) ⁻¹' ((fun z : ℂ => starRingEnd ℂ z) '' Kc)
        = Kc := by
      ext w
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨k, hk, hkw⟩
        have hkw' : k = w := by
          have h := congrArg (starRingEnd ℂ) hkw
          simpa using h
        rwa [← hkw']
      · intro hw
        exact ⟨w, hw, rfl⟩
    have hmem : MemLp g 2 (volume.restrict ((fun z : ℂ => starRingEnd ℂ z) '' Kc)) :=
      hg _ (Set.subset_univ _) hKim
    have hres : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) (volume.restrict Kc)
        (volume.restrict ((fun z : ℂ => starRingEnd ℂ z) '' Kc)) := by
      have h := hmp.restrict_preimage hKim.measurableSet
      rwa [hpre] at h
    constructor
    · exact Complex.continuous_conj.comp_aestronglyMeasurable
        (hmem.1.comp_quasiMeasurePreserving hres.quasiMeasurePreserving)
    · have h1 : eLpNorm (fun z => starRingEnd ℂ (g (starRingEnd ℂ z))) 2 (volume.restrict Kc)
          = eLpNorm (g ∘ fun z : ℂ => starRingEnd ℂ z) 2 (volume.restrict Kc) :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun z => by simp)
      rw [h1, eLpNorm_comp_measurePreserving hmem.1 hres]
      exact hmem.2
  -- weak partial derivative in the direction `1`
  have hwx : HasWeakDirDeriv 1 (fun z => starRingEnd ℂ (gx (starRingEnd ℂ z)))
      (fun z => starRingEnd ℂ (f (starRingEnd ℂ z))) Set.univ := by
    intro φ hφ hφc _
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℝ, ψ = fun w : ℂ => φ (starRingEnd ℂ w) := ⟨_, rfl⟩
    have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
      rw [hψdef]
      have h := hφ.comp (ContinuousLinearMap.contDiff (Complex.conjCLE : ℂ →L[ℝ] ℂ))
      have he : φ ∘ ⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) = fun w : ℂ => φ (starRingEnd ℂ w) := by
        funext w
        simp
      rwa [he] at h
    have hψc : HasCompactSupport ψ := by
      rw [hψdef]
      have h := hφc.comp_homeomorph Complex.conjCLE.toHomeomorph
      have he : φ ∘ ⇑Complex.conjCLE.toHomeomorph = fun w : ℂ => φ (starRingEnd ℂ w) := by
        funext w
        simp [ContinuousLinearEquiv.coe_toHomeomorph]
      rwa [he] at h
    have hφψ : φ = ψ ∘ ⇑Complex.conjCLE := by
      funext w
      simp [hψdef]
    have hfd1 : ∀ w : ℂ, (fderiv ℝ φ w) 1 = (fderiv ℝ ψ (starRingEnd ℂ w)) 1 := by
      intro w
      conv_lhs => rw [hφψ]
      rw [ContinuousLinearEquiv.comp_right_fderiv]
      simp
    have hIBP := hFgrad.1 ψ hψs hψc (Set.subset_univ _)
    change ∫ z : ℂ, (fderiv ℝ φ z) 1 • starRingEnd ℂ (f (starRingEnd ℂ z))
        = - ∫ z : ℂ, φ z • starRingEnd ℂ (gx (starRingEnd ℂ z))
    calc ∫ z : ℂ, (fderiv ℝ φ z) 1 • starRingEnd ℂ (f (starRingEnd ℂ z))
        = ∫ z : ℂ, starRingEnd ℂ
            ((fun w : ℂ => (fderiv ℝ ψ w) 1 • f w) (starRingEnd ℂ z)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          dsimp only
          rw [hfd1 z, Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
      _ = starRingEnd ℂ
            (∫ z : ℂ, (fun w : ℂ => (fderiv ℝ ψ w) 1 • f w) (starRingEnd ℂ z)) :=
          integral_conj
      _ = starRingEnd ℂ (∫ w : ℂ, (fderiv ℝ ψ w) 1 • f w) :=
          congrArg (starRingEnd ℂ)
            (hmp.integral_comp hemb fun w : ℂ => (fderiv ℝ ψ w) 1 • f w)
      _ = starRingEnd ℂ (- ∫ w : ℂ, ψ w • gx w) := by rw [hIBP]
      _ = - ∫ w : ℂ, starRingEnd ℂ (ψ w • gx w) := by
          rw [map_neg]
          exact congrArg Neg.neg integral_conj.symm
      _ = - ∫ w : ℂ, (fun u : ℂ => ψ u • starRingEnd ℂ (gx u)) w := by
          refine congrArg Neg.neg
            (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
          dsimp only
          rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
      _ = - ∫ z : ℂ, (fun u : ℂ => ψ u • starRingEnd ℂ (gx u)) (starRingEnd ℂ z) :=
          congrArg Neg.neg
            (hmp.integral_comp hemb fun u : ℂ => ψ u • starRingEnd ℂ (gx u)).symm
      _ = - ∫ z : ℂ, φ z • starRingEnd ℂ (gx (starRingEnd ℂ z)) := by
          refine congrArg Neg.neg
            (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
          dsimp only
          rw [hψdef]
          simp
  -- weak partial derivative in the direction `I` (the sign flips through `conj I = -I`)
  have hwy : HasWeakDirDeriv Complex.I (fun z => -starRingEnd ℂ (gy (starRingEnd ℂ z)))
      (fun z => starRingEnd ℂ (f (starRingEnd ℂ z))) Set.univ := by
    intro φ hφ hφc _
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℝ, ψ = fun w : ℂ => φ (starRingEnd ℂ w) := ⟨_, rfl⟩
    have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
      rw [hψdef]
      have h := hφ.comp (ContinuousLinearMap.contDiff (Complex.conjCLE : ℂ →L[ℝ] ℂ))
      have he : φ ∘ ⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) = fun w : ℂ => φ (starRingEnd ℂ w) := by
        funext w
        simp
      rwa [he] at h
    have hψc : HasCompactSupport ψ := by
      rw [hψdef]
      have h := hφc.comp_homeomorph Complex.conjCLE.toHomeomorph
      have he : φ ∘ ⇑Complex.conjCLE.toHomeomorph = fun w : ℂ => φ (starRingEnd ℂ w) := by
        funext w
        simp [ContinuousLinearEquiv.coe_toHomeomorph]
      rwa [he] at h
    have hφψ : φ = ψ ∘ ⇑Complex.conjCLE := by
      funext w
      simp [hψdef]
    have hfdI : ∀ w : ℂ, (fderiv ℝ φ w) Complex.I
        = -((fderiv ℝ ψ (starRingEnd ℂ w)) Complex.I) := by
      intro w
      conv_lhs => rw [hφψ]
      rw [ContinuousLinearEquiv.comp_right_fderiv]
      simp [Complex.conj_I]
    have hIBP := hFgrad.2 ψ hψs hψc (Set.subset_univ _)
    change ∫ z : ℂ, (fderiv ℝ φ z) Complex.I • starRingEnd ℂ (f (starRingEnd ℂ z))
        = - ∫ z : ℂ, φ z • -starRingEnd ℂ (gy (starRingEnd ℂ z))
    calc ∫ z : ℂ, (fderiv ℝ φ z) Complex.I • starRingEnd ℂ (f (starRingEnd ℂ z))
        = ∫ z : ℂ, -(starRingEnd ℂ
            ((fun w : ℂ => (fderiv ℝ ψ w) Complex.I • f w) (starRingEnd ℂ z))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          dsimp only
          rw [hfdI z, Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal,
            Complex.ofReal_neg]
          ring
      _ = - ∫ z : ℂ, starRingEnd ℂ
            ((fun w : ℂ => (fderiv ℝ ψ w) Complex.I • f w) (starRingEnd ℂ z)) :=
          integral_neg _
      _ = - starRingEnd ℂ
            (∫ z : ℂ, (fun w : ℂ => (fderiv ℝ ψ w) Complex.I • f w) (starRingEnd ℂ z)) :=
          congrArg Neg.neg integral_conj
      _ = - starRingEnd ℂ (∫ w : ℂ, (fderiv ℝ ψ w) Complex.I • f w) :=
          congrArg (fun t => -(starRingEnd ℂ t))
            (hmp.integral_comp hemb fun w : ℂ => (fderiv ℝ ψ w) Complex.I • f w)
      _ = - starRingEnd ℂ (- ∫ w : ℂ, ψ w • gy w) := by rw [hIBP]
      _ = ∫ w : ℂ, starRingEnd ℂ (ψ w • gy w) := by
          rw [map_neg, neg_neg]
          exact integral_conj.symm
      _ = ∫ w : ℂ, (fun u : ℂ => ψ u • starRingEnd ℂ (gy u)) w := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          dsimp only
          rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
      _ = ∫ z : ℂ, (fun u : ℂ => ψ u • starRingEnd ℂ (gy u)) (starRingEnd ℂ z) :=
          (hmp.integral_comp hemb fun u : ℂ => ψ u • starRingEnd ℂ (gy u)).symm
      _ = - ∫ z : ℂ, φ z • -starRingEnd ℂ (gy (starRingEnd ℂ z)) := by
          rw [← integral_neg]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          dsimp only
          rw [hψdef]
          simp only [Complex.real_smul, Complex.conj_conj]
          ring
  exact ⟨⟨hGhomeo, hGdet⟩, ⟨hGloc, fun z => starRingEnd ℂ (gx (starRingEnd ℂ z)),
    fun z => -starRingEnd ℂ (gy (starRingEnd ℂ z)), ⟨hwx, hwy⟩, hLpConj gx hgx,
    fun Kc hs hKc => ((hLpConj gy hgy) Kc hs hKc).neg⟩, hGbelt⟩

/-! ## Invariance under a subgroup of `SL(2, ℝ)` -/

/-- A Beltrami coefficient is **invariant** under `Γ₀ ≤ SL(2, ℝ)` when for every `γ ∈ Γ₀` the
pullback law `μ(γ z) · conj(γ'(z))/γ'(z) = μ(z)` holds a.e., written in the multiplied-out
form `μ(γ z) (c z + d)² = μ(z) conj(c z + d)²` that needs no division. -/
def IsInvariantBeltrami' (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (b : BeltramiCoeff) : Prop :=
  ∀ γ ∈ Γ₀, ∀ᵐ z : ℂ,
    b.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = b.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2

/-! ## Coefficient uniqueness, the zero coefficient, and composition -/

/-- Two Beltrami coefficients of the same quasiconformal map agree almost everywhere: the
Jacobian identity `det Df = ‖∂f‖² − ‖∂̄f‖²` forces `∂f ≠ 0` a.e., and there
`μ = ∂̄f / ∂f` is determined. -/
theorem beltrami_coeff_unique_ae {f : ℂ → ℂ} {b b' : BeltramiCoeff}
    (h : IsQCAnalytic f b) (h' : IsQCAnalytic f b') : b.μ =ᵐ[volume] b'.μ := by
  filter_upwards [h.1.2, h.2.2, h'.2.2] with z hdet hb hb'
  rw [det_fderiv_eq_wirtinger] at hdet
  have hdz : dz f z ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp only [norm_zero] at hdet
    nlinarith [norm_nonneg (dzbar f z), sq_nonneg ‖dzbar f z‖]
  exact mul_right_cancel₀ hdz (hb.symm.trans hb')

/-- The zero Beltrami coefficient. -/
noncomputable def BeltramiCoeff.zero : BeltramiCoeff where
  μ := 0
  measurable := measurable_const
  bound := by rw [eLpNormEssSup_zero]; exact zero_lt_one

/-- The identity is quasiconformal with the zero Beltrami coefficient. -/
theorem isQCAnalytic_id : IsQCAnalytic id BeltramiCoeff.zero := by
  have hcont2 : ∀ g : ℂ → ℂ, Continuous g → MemLpLocOn g 2 Set.univ := by
    intro g hg K _ hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    have hbound : ∀ᵐ x ∂(volume.restrict K), ‖g x‖ ≤ C := by
      rw [ae_restrict_iff' hK.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hg.aestronglyMeasurable C hbound).mono_exponent le_top
  refine ⟨⟨IsHomeomorph.id, ?_⟩, ⟨hcont2 id continuous_id, ?_⟩, ?_⟩
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [fderiv_id]
    have h1 : (ContinuousLinearMap.id ℝ ℂ).det = 1 := by simp [ContinuousLinearMap.det]
    rw [h1]
    exact one_pos
  · refine ⟨fun _ => 1, fun _ => Complex.I, ⟨?_, ?_⟩, ?_, ?_⟩
    · have h := HasWeakDirDeriv.of_contDiffOn (v := (1 : ℂ)) isOpen_univ
        (contDiffOn_id : ContDiffOn ℝ 1 (id : ℂ → ℂ) Set.univ)
      have heq : (fun z : ℂ => (fderiv ℝ (id : ℂ → ℂ) z) 1) = fun _ : ℂ => (1 : ℂ) := by
        funext z
        rw [fderiv_id]
        rfl
      rwa [heq] at h
    · have h := HasWeakDirDeriv.of_contDiffOn (v := Complex.I) isOpen_univ
        (contDiffOn_id : ContDiffOn ℝ 1 (id : ℂ → ℂ) Set.univ)
      have heq : (fun z : ℂ => (fderiv ℝ (id : ℂ → ℂ) z) Complex.I)
          = fun _ : ℂ => Complex.I := by
        funext z
        rw [fderiv_id]
        rfl
      rwa [heq] at h
    · exact hcont2 (fun _ => 1) continuous_const
    · exact hcont2 (fun _ => Complex.I) continuous_const
  · refine Filter.Eventually.of_forall fun z => ?_
    have h0 : dzbar id z = 0 :=
      dzbar_eq_zero_of_differentiableAt (differentiable_id.differentiableAt)
    rw [h0]
    simp [BeltramiCoeff.zero]

/-- Composition of quasiconformal maps is quasiconformal, with a coefficient controlled by
the product of the maximal dilatations. -/
theorem exists_isQCAnalytic_comp {f g : ℂ → ℂ} {bf bg : BeltramiCoeff}
    (hf : IsQCAnalytic f bf) (hg : IsQCAnalytic g bg) :
    ∃ b : BeltramiCoeff, b.normInf ≤ (bf.K * bg.K - 1) / (bf.K * bg.K + 1) ∧
      IsQCAnalytic (f ∘ g) b := by
  have hfK := IsQCAnalytic.isQCGeometric_K hf
  have hgK := IsQCAnalytic.isQCGeometric_K hg
  have hcomp : IsQCGeometric (f ∘ g) (bf.K * bg.K) := hfK.comp hgK
  have hK1 : 1 ≤ bf.K * bg.K :=
    le_trans bf.one_le_K (le_mul_of_one_le_right (by linarith [bf.one_le_K]) bg.one_le_K)
  exact isQCAnalytic_of_isQCGeometric hK1 hcomp

end RiemannDynamics

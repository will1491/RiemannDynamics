/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.Foundations.Metric
import RiemannDynamics.Teichmuller.ModuliAction.UpperQC.Factorization
import RiemannDynamics.Surface.MappingClassGroup
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# The moduli group and its isometric action on Teichmüller space

The group of plane homeomorphisms compatible with the base group, the pullback
of Teichmüller representatives, the induced action on Teichmüller space, its
isometry, and the moduli space quotient.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The moduli group -/

/-- The carrier of the moduli group: quasiconformal, conjugation-symmetric plane
homeomorphisms compatible with `Γ₀` on both sides. -/
def modGroupCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Set (ℂ ≃ₜ ℂ) :=
  {F | (∃ K : ℝ, IsQCGeometric (⇑F) K)
    ∧ (∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    ∧ (∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ᵐ z : ℂ, F (moebiusMap γ z) = moebiusMap γ' (F z))
    ∧ (∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ᵐ z : ℂ, F (moebiusMap γ z) = moebiusMap γ' (F z))}

/-- The identity homeomorphism belongs to the moduli carrier. -/
theorem one_mem_modGroupCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    (1 : ℂ ≃ₜ ℂ) ∈ modGroupCarrier Γ₀ := by
  refine ⟨⟨BeltramiCoeff.zero.K, isQCAnalytic_id.isQCGeometric_K⟩, fun z => rfl, ?_, ?_⟩
  · exact fun γ hγ => ⟨γ, hγ, Filter.Eventually.of_forall fun z => rfl⟩
  · exact fun γ' hγ' => ⟨γ', hγ', Filter.Eventually.of_forall fun z => rfl⟩

/-- The moduli carrier is closed under composition: dilatations multiply, and the two-sided
compatibility clauses chain, pulling null sets back through Möbius maps and quasiconformal
inverses. -/
theorem mul_mem_modGroupCarrier {F G : ℂ ≃ₜ ℂ} (hF : F ∈ modGroupCarrier Γ₀)
    (hG : G ∈ modGroupCarrier Γ₀) : F * G ∈ modGroupCarrier Γ₀ := by
  obtain ⟨⟨KF, hKF⟩, hsymF, hF5, hF6⟩ := hF
  obtain ⟨⟨KG, hKG⟩, hsymG, hG5, hG6⟩ := hG
  -- preimages of null sets under `G` are null, through the quasiconformal inverse
  have hGpre : ∀ N : Set ℂ, volume N = 0 → volume (⇑G ⁻¹' N) = 0 := by
    intro N hN
    have h := hKG.inverse_lusinN N hN
    have hset : ⇑(IsHomeomorph.homeomorph (⇑G) hKG.2.1.isHomeomorph).symm '' N
        = ⇑G ⁻¹' N := by
      ext w
      constructor
      · rintro ⟨n, hn, rfl⟩
        have happ := (IsHomeomorph.homeomorph (⇑G) hKG.2.1.isHomeomorph).apply_symm_apply n
        rw [IsHomeomorph.homeomorph_apply] at happ
        rw [Set.mem_preimage, happ]
        exact hn
      · intro hw
        refine ⟨G w, hw, ?_⟩
        have happ := (IsHomeomorph.homeomorph (⇑G) hKG.2.1.isHomeomorph).symm_apply_apply w
        rwa [IsHomeomorph.homeomorph_apply] at happ
    rwa [hset] at h
  refine ⟨⟨KF * KG, hKF.comp hKG⟩, ?_, ?_, ?_⟩
  · intro z
    calc (F * G) (starRingEnd ℂ z) = F (G (starRingEnd ℂ z)) := rfl
      _ = F (starRingEnd ℂ (G z)) := by rw [hsymG z]
      _ = starRingEnd ℂ (F (G z)) := hsymF (G z)
      _ = starRingEnd ℂ ((F * G) z) := rfl
  · intro γ hγ
    obtain ⟨γ', hγ'm, hae1⟩ := hG5 γ hγ
    obtain ⟨γ'', hγ''m, hae2⟩ := hF5 γ' hγ'm
    refine ⟨γ'', hγ''m, ?_⟩
    have hae2' : ∀ᵐ z : ℂ, F (moebiusMap γ' (G z)) = moebiusMap γ'' (F (G z)) := by
      rw [ae_iff] at hae2 ⊢
      exact hGpre _ hae2
    filter_upwards [hae1, hae2'] with z h1 h2
    calc (F * G) (moebiusMap γ z) = F (G (moebiusMap γ z)) := rfl
      _ = F (moebiusMap γ' (G z)) := by rw [h1]
      _ = moebiusMap γ'' (F (G z)) := h2
      _ = moebiusMap γ'' ((F * G) z) := rfl
  · intro γ'' hγ''
    obtain ⟨γ', hγ'm, hae2⟩ := hF6 γ'' hγ''
    obtain ⟨γ, hγm, hae1⟩ := hG6 γ' hγ'm
    refine ⟨γ, hγm, ?_⟩
    have hae2' : ∀ᵐ z : ℂ, F (moebiusMap γ' (G z)) = moebiusMap γ'' (F (G z)) := by
      rw [ae_iff] at hae2 ⊢
      exact hGpre _ hae2
    filter_upwards [hae1, hae2'] with z h1 h2
    calc (F * G) (moebiusMap γ z) = F (G (moebiusMap γ z)) := rfl
      _ = F (moebiusMap γ' (G z)) := by rw [h1]
      _ = moebiusMap γ'' (F (G z)) := h2
      _ = moebiusMap γ'' ((F * G) z) := rfl

/-- The moduli carrier is closed under inversion: the two-sided compatibility clauses swap. -/
theorem inv_mem_modGroupCarrier {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroupCarrier Γ₀) :
    F⁻¹ ∈ modGroupCarrier Γ₀ := by
  obtain ⟨⟨K, hK⟩, hsymF, hF5, hF6⟩ := hF
  -- images of null sets under `F` are null: the forward Lusin condition (N)
  have hFimg : ∀ N : Set ℂ, volume N = 0 → ∀ᵐ w : ℂ, w ∉ ⇑F '' N := by
    intro N hN
    rw [ae_iff]
    refine measure_mono_null (fun w hw => ?_) (hK.lusinN N hN)
    simpa using hw
  refine ⟨⟨K, ?_⟩, ?_, ?_, ?_⟩
  · have hfun : ⇑(F⁻¹) = ⇑(IsHomeomorph.homeomorph (⇑F) hK.2.1.isHomeomorph).symm := by
      funext w
      have h1 := (IsHomeomorph.homeomorph (⇑F) hK.2.1.isHomeomorph).apply_symm_apply w
      rw [IsHomeomorph.homeomorph_apply] at h1
      simp only [Homeomorph.inv_apply]
      apply F.injective
      rw [F.apply_symm_apply, h1]
    rw [hfun]
    exact isQCGeometric_inv_of_isQCGeometric hK
  · intro z
    simp only [Homeomorph.inv_apply]
    apply F.injective
    rw [F.apply_symm_apply, hsymF (F.symm z), F.apply_symm_apply]
  · intro γ hγ
    obtain ⟨δ, hδm, hae⟩ := hF6 γ hγ
    refine ⟨δ, hδm, ?_⟩
    have haeW := hFimg {z : ℂ | ¬ F (moebiusMap δ z) = moebiusMap γ (F z)}
      (by rw [ae_iff] at hae; exact hae)
    filter_upwards [haeW] with w hw
    have hzid : F (moebiusMap δ (F.symm w)) = moebiusMap γ (F (F.symm w)) := by
      by_contra hcon
      exact hw ⟨F.symm w, hcon, F.apply_symm_apply w⟩
    rw [F.apply_symm_apply] at hzid
    simp only [Homeomorph.inv_apply]
    rw [← hzid, F.symm_apply_apply]
  · intro γ' hγ'
    obtain ⟨δ, hδm, hae⟩ := hF5 γ' hγ'
    refine ⟨δ, hδm, ?_⟩
    have haeW := hFimg {z : ℂ | ¬ F (moebiusMap γ' z) = moebiusMap δ (F z)}
      (by rw [ae_iff] at hae; exact hae)
    filter_upwards [haeW] with w hw
    have hzid : F (moebiusMap γ' (F.symm w)) = moebiusMap δ (F (F.symm w)) := by
      by_contra hcon
      exact hw ⟨F.symm w, hcon, F.apply_symm_apply w⟩
    rw [F.apply_symm_apply] at hzid
    simp only [Homeomorph.inv_apply]
    rw [← hzid, F.symm_apply_apply]

/-- The **moduli group** over the base `Γ₀`: symmetric quasiconformal plane homeomorphisms
compatible with `Γ₀` on both sides, a subgroup of the group of plane self-homeomorphisms. -/
def modGroup (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Subgroup (ℂ ≃ₜ ℂ) where
  carrier := modGroupCarrier Γ₀
  one_mem' := one_mem_modGroupCarrier Γ₀
  mul_mem' := fun hF hG => mul_mem_modGroupCarrier hF hG
  inv_mem' := fun hF => inv_mem_modGroupCarrier hF

/-- Membership in the moduli group unfolds to membership in its carrier. -/
theorem mem_modGroup_iff {F : ℂ ≃ₜ ℂ} : F ∈ modGroup Γ₀ ↔ F ∈ modGroupCarrier Γ₀ :=
  Iff.rfl

/-- A compatibility identity of a moduli-group element holds at every non-pole point, by
continuity of both sides on the open co-null set. -/
theorem modGroup_equivariant_offPole {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀)
    {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hae : ∀ᵐ z : ℂ, F (moebiusMap γ z) = moebiusMap γ' (F z)) :
    ∀ z : ℂ, moebiusDenom γ z ≠ 0 → F (moebiusMap γ z) = moebiusMap γ' (F z) := by
  obtain ⟨⟨K, hK⟩, -, -, -⟩ := hF
  have hFc : Continuous (⇑F) := hK.2.1.isHomeomorph.continuous
  have hdet' : (γ' 0 0 : ℂ) * (γ' 1 1 : ℂ) - (γ' 0 1 : ℂ) * (γ' 1 0 : ℂ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ'
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  -- the pole of `γ'` is avoided by `F` almost everywhere: its `F`-preimage is a subsingleton
  have hpole' : ∀ᵐ z : ℂ, moebiusDenom γ' (F z) ≠ 0 := by
    have hPsub : Set.Subsingleton {w : ℂ | moebiusDenom γ' w = 0} := by
      intro w₁ hw₁ w₂ hw₂
      have h₁' : (γ' 1 0 : ℂ) * w₁ + (γ' 1 1 : ℂ) = 0 := hw₁
      have h₂' : (γ' 1 0 : ℂ) * w₂ + (γ' 1 1 : ℂ) = 0 := hw₂
      by_cases hc : γ' 1 0 = 0
      · exfalso
        have hcC : ((γ' 1 0 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
        rw [hcC, zero_mul, zero_add] at h₁'
        have hd : ((γ' 1 1 : ℝ) : ℂ) = 0 := h₁'
        rw [hcC, hd] at hdet'
        simp at hdet'
      · have hcC : ((γ' 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
        have hmul : (γ' 1 0 : ℂ) * w₁ = (γ' 1 0 : ℂ) * w₂ := by linear_combination h₁' - h₂'
        exact mul_left_cancel₀ hcC hmul
    have hpre : Set.Subsingleton (⇑F ⁻¹' {w : ℂ | moebiusDenom γ' w = 0}) := by
      intro x hx y hy
      exact F.injective (hPsub hx hy)
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (hpre.measure_zero volume)
    simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hz
    exact hz
  -- the denominator-cleared identity holds a.e., and both sides are continuous off the pole
  have haeC : ∀ᵐ z : ℂ, moebiusDenom γ' (F z) * F (moebiusMap γ z)
      = (γ' 0 0 : ℂ) * F z + (γ' 0 1 : ℂ) := by
    filter_upwards [hae, hpole'] with z h1 h2
    rw [h1]
    simp only [moebiusMap]
    rw [mul_comm, div_mul_cancel₀ _ h2]
  have hU : IsOpen {z : ℂ | moebiusDenom γ z ≠ 0} := by
    have hc : Continuous (moebiusDenom γ) := by
      unfold moebiusDenom
      fun_prop
    exact isOpen_compl_singleton.preimage hc
  have hdenc : Continuous fun w : ℂ => moebiusDenom γ' (F w) := by
    unfold moebiusDenom
    fun_prop
  have h1 : ContinuousOn (fun w : ℂ => moebiusDenom γ' (F w) * F (moebiusMap γ w))
      {w : ℂ | moebiusDenom γ w ≠ 0} := by
    intro w hw
    have hmw : ContinuousAt (moebiusMap γ) w := (hasDerivAt_moebiusMap γ hw).continuousAt
    exact (hdenc.continuousAt.mul (hFc.continuousAt.comp hmw)).continuousWithinAt
  have h2 : Continuous fun w : ℂ => (γ' 0 0 : ℂ) * F w + (γ' 0 1 : ℂ) := by fun_prop
  have heq : Set.EqOn (fun w : ℂ => moebiusDenom γ' (F w) * F (moebiusMap γ w))
      (fun w : ℂ => (γ' 0 0 : ℂ) * F w + (γ' 0 1 : ℂ)) {w : ℂ | moebiusDenom γ w ≠ 0} := by
    refine Measure.eqOn_of_ae_eq (ae_restrict_of_ae haeC) h1 h2.continuousOn ?_
    rw [hU.interior_eq]
    exact subset_closure
  intro z hz
  have hclz : moebiusDenom γ' (F z) * F (moebiusMap γ z)
      = (γ' 0 0 : ℂ) * F z + (γ' 0 1 : ℂ) := heq hz
  by_cases hd : moebiusDenom γ' (F z) = 0
  · exfalso
    rw [hd, zero_mul] at hclz
    have hdd : (γ' 1 0 : ℂ) * F z + (γ' 1 1 : ℂ) = 0 := hd
    have h01 : (0 : ℂ) = 1 := by
      linear_combination -((γ' 0 0 : ℂ) * hdd) + (γ' 1 0 : ℂ) * hclz.symm + hdet'
    exact zero_ne_one h01
  · have hval : moebiusMap γ' (F z)
        = ((γ' 0 0 : ℂ) * F z + (γ' 0 1 : ℂ)) / moebiusDenom γ' (F z) := rfl
    rw [hval, eq_div_iff hd, ← hclz]
    ring

/-- A moduli-group element maps real points to real points. -/
theorem modGroup_real_im {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀) (t : ℝ) :
    (F (t : ℂ)).im = 0 := by
  exact realLine_im_eq_zero hF.2.1 t

/-- The real trace of a moduli-group element is strictly monotone in one of the two
directions: it is a continuous injection of the real line into itself. -/
theorem modGroup_real_strictMono {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀) :
    StrictMono (fun t : ℝ => (F (t : ℂ)).re)
      ∨ StrictAnti (fun t : ℝ => (F (t : ℂ)).re) := by
  have hcont : Continuous fun t : ℝ => (F (t : ℂ)).re :=
    Complex.continuous_re.comp (F.continuous.comp Complex.continuous_ofReal)
  have hinj : Function.Injective fun t : ℝ => (F (t : ℂ)).re := by
    intro s t hst
    have him : (F (s : ℂ)).im = (F (t : ℂ)).im := by
      rw [modGroup_real_im hF s, modGroup_real_im hF t]
    have hre : (F (s : ℂ)).re = (F (t : ℂ)).re := hst
    have hFeq : F (s : ℂ) = F (t : ℂ) := Complex.ext hre him
    exact_mod_cast F.injective hFeq
  exact hcont.strictMono_of_inj hinj

/-- The real trace of a moduli-group element is onto the real line. -/
theorem modGroup_real_surjective {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀) :
    Function.Surjective fun t : ℝ => (F (t : ℂ)).re := by
  obtain ⟨⟨K, hK⟩, hsymF, -, -⟩ := hF
  obtain ⟨b, -, hFb⟩ := isQCAnalytic_of_isQCGeometric hK.1 hK
  intro s
  obtain ⟨z, hz⟩ := hFb.1.1.bijective.surjective ((s : ℝ) : ℂ)
  have hconj : F (starRingEnd ℂ z) = F z := by
    rw [hsymF z, hz, Complex.conj_ofReal]
  have hzr : starRingEnd ℂ z = z := hFb.injective hconj
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hzr
  refine ⟨z.re, ?_⟩
  have hzeq : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
  dsimp only
  rw [hzeq, hz, Complex.ofReal_re]

/-! ## Pulling back representatives -/

/-- A quasiconformal map that is Möbius-conjugated by `γ` has a `γ`-invariant coefficient:
differentiating `h ∘ γ = W ∘ h` a.e. yields the multiplicative invariance law. -/
theorem isInvariantBeltrami'_single_of_moebius_conj {h : ℂ → ℂ} {bh : BeltramiCoeff}
    (hh : IsQCAnalytic h bh) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hconj : ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, h (moebiusMap γ z) = moebiusMap W (h z)) :
    ∀ᵐ z : ℂ, bh.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = bh.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  obtain ⟨W, hae⟩ := hconj
  have hcont : Continuous h := hh.1.1.continuous
  have hinj : Function.Injective h := hh.1.1.bijective.injective
  have hdet' : (W 0 0 : ℂ) * (W 1 1 : ℂ) - (W 0 1 : ℂ) * (W 1 0 : ℂ) = 1 := by
    have hW := Matrix.SpecialLinearGroup.det_coe W
    rw [Matrix.det_fin_two] at hW
    exact_mod_cast hW
  -- Step 1: upgrade the a.e. identity to every non-pole point, in denominator-cleared form.
  have hpole' : ∀ᵐ z : ℂ, moebiusDenom W (h z) ≠ 0 := by
    have hPsub : Set.Subsingleton {w : ℂ | moebiusDenom W w = 0} := by
      intro w₁ hw₁ w₂ hw₂
      have h₁' : (W 1 0 : ℂ) * w₁ + (W 1 1 : ℂ) = 0 := hw₁
      have h₂' : (W 1 0 : ℂ) * w₂ + (W 1 1 : ℂ) = 0 := hw₂
      by_cases hc : W 1 0 = 0
      · exfalso
        have hcC : ((W 1 0 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
        rw [hcC, zero_mul, zero_add] at h₁'
        have hd : ((W 1 1 : ℝ) : ℂ) = 0 := h₁'
        rw [hcC, hd] at hdet'
        simp at hdet'
      · have hcC : ((W 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
        have hmul : (W 1 0 : ℂ) * w₁ = (W 1 0 : ℂ) * w₂ := by linear_combination h₁' - h₂'
        exact mul_left_cancel₀ hcC hmul
    have hpre : Set.Subsingleton (h ⁻¹' {w : ℂ | moebiusDenom W w = 0}) := by
      intro x hx y hy
      exact hinj (hPsub hx hy)
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (hpre.measure_zero volume)
    simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hz
    exact hz
  have haeC : ∀ᵐ z : ℂ, moebiusDenom W (h z) * h (moebiusMap γ z)
      = (W 0 0 : ℂ) * h z + (W 0 1 : ℂ) := by
    filter_upwards [hae, hpole'] with z h1 h2
    rw [h1]
    simp only [moebiusMap]
    rw [mul_comm, div_mul_cancel₀ _ h2]
  have hU : IsOpen {z : ℂ | moebiusDenom γ z ≠ 0} := by
    have hc : Continuous (moebiusDenom γ) := by
      unfold moebiusDenom
      fun_prop
    exact isOpen_compl_singleton.preimage hc
  have hdenc : Continuous fun w : ℂ => moebiusDenom W (h w) := by
    unfold moebiusDenom
    fun_prop
  have h1c : ContinuousOn (fun w : ℂ => moebiusDenom W (h w) * h (moebiusMap γ w))
      {w : ℂ | moebiusDenom γ w ≠ 0} := by
    intro w hw
    have hmw : ContinuousAt (moebiusMap γ) w := (hasDerivAt_moebiusMap γ hw).continuousAt
    exact (hdenc.continuousAt.mul (hcont.continuousAt.comp hmw)).continuousWithinAt
  have h2c : Continuous fun w : ℂ => (W 0 0 : ℂ) * h w + (W 0 1 : ℂ) := by fun_prop
  have heqC : Set.EqOn (fun w : ℂ => moebiusDenom W (h w) * h (moebiusMap γ w))
      (fun w : ℂ => (W 0 0 : ℂ) * h w + (W 0 1 : ℂ)) {w : ℂ | moebiusDenom γ w ≠ 0} := by
    refine Measure.eqOn_of_ae_eq (ae_restrict_of_ae haeC) h1c h2c.continuousOn ?_
    rw [hU.interior_eq]
    exact subset_closure
  -- off the pole of `γ`, `h z` avoids the pole of `W` and the identity holds on the nose
  have hoff : ∀ z : ℂ, moebiusDenom γ z ≠ 0 →
      moebiusDenom W (h z) ≠ 0 ∧ h (moebiusMap γ z) = moebiusMap W (h z) := by
    intro z hz
    have hclz : moebiusDenom W (h z) * h (moebiusMap γ z)
        = (W 0 0 : ℂ) * h z + (W 0 1 : ℂ) := heqC hz
    by_cases hd : moebiusDenom W (h z) = 0
    · exfalso
      rw [hd, zero_mul] at hclz
      have hdd : (W 1 0 : ℂ) * h z + (W 1 1 : ℂ) = 0 := hd
      have h01 : (0 : ℂ) = 1 := by
        linear_combination -((W 0 0 : ℂ) * hdd) + (W 1 0 : ℂ) * hclz.symm + hdet'
      exact zero_ne_one h01
    · refine ⟨hd, ?_⟩
      have hval : moebiusMap W (h z)
          = ((W 0 0 : ℂ) * h z + (W 0 1 : ℂ)) / moebiusDenom W (h z) := rfl
      rw [hval, eq_div_iff hd, ← hclz]
      ring
  -- Step 2: transport the a.e. Jacobian and Beltrami data through the Möbius map.
  have haeMoeb : ∀ P : ℂ → Prop,
      (∀ᵐ w : ℂ, P w) → ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 → P (moebiusMap γ z) := by
    intro P hP
    have hopen : IsOpen {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom γ⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hP ⊢
    have himg : volume (moebiusMap γ⁻¹ ''
        (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le)
        rw [measure_toMeasurable]
        exact hP.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap γ⁻¹) (fderiv ℝ (moebiusMap γ⁻¹) w)
            (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap γ⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap γ⁻¹)
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) := by
        intro x hx y hy hxy
        have hx1 : moebiusMap γ (moebiusMap γ⁻¹ x) = x := by
          rw [moebiusMap_mul γ γ⁻¹ x hx.2, mul_inv_cancel, moebiusMap_one]
        have hy1 : moebiusMap γ (moebiusMap γ⁻¹ y) = y := by
          rw [moebiusMap_mul γ γ⁻¹ y hy.2, mul_inv_cancel, moebiusMap_one]
        rw [← hx1, ← hy1, hxy]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom γ⁻¹ (moebiusMap γ z) * moebiusDenom γ z = 1 := by
      rw [moebiusDenom_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom γ⁻¹ (moebiusMap γ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap γ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusMap_one]
  have hpole : ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact volume_moebiusDenom_zero γ
  have hgood : ∀ᵐ w : ℂ, 0 < (fderiv ℝ h w).det ∧ dzbar h w = bh.μ w * dz h w :=
    hh.1.2.and hh.2.2
  have hgoodT := haeMoeb (fun w => 0 < (fderiv ℝ h w).det ∧ dzbar h w = bh.μ w * dz h w) hgood
  -- Step 3: differentiate the identity at a.e. point and divide out.
  filter_upwards [hpole, hgood, hgoodT] with z hz hgz hgTz
  obtain ⟨hdet_z, hbel_z⟩ := hgz
  obtain ⟨hdet_p, hbel_p⟩ := hgTz hz
  have hWd : moebiusDenom W (h z) ≠ 0 := (hoff z hz).1
  have hDz : DifferentiableAt ℝ h z := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet_z
    simp [ContinuousLinearMap.det] at hdet_z
  have hDp : DifferentiableAt ℝ h (moebiusMap γ z) := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet_p
    simp [ContinuousLinearMap.det] at hdet_p
  have hγd := hasDerivAt_moebiusMap γ hz
  have hWdd := hasDerivAt_moebiusMap W hWd
  have hev : (fun w => h (moebiusMap γ w)) =ᶠ[nhds z] fun w => moebiusMap W (h w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hoff w hw).2
  have hfd : fderiv ℝ (fun w => h (moebiusMap γ w)) z
      = fderiv ℝ (fun w => moebiusMap W (h w)) z := hev.fderiv_eq
  have hdzEq : dz (fun w => h (moebiusMap γ w)) z = dz (fun w => moebiusMap W (h w)) z := by
    unfold dz
    rw [hfd]
  have hdzbEq : dzbar (fun w => h (moebiusMap γ w)) z
      = dzbar (fun w => moebiusMap W (h w)) z := by
    unfold dzbar
    rw [hfd]
  -- chain rules on both sides
  have hLdz : dz (fun w => h (moebiusMap γ w)) z
      = dz h (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹ := by
    have hcr := dz_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hLdzb : dzbar (fun w => h (moebiusMap γ w)) z
      = dzbar h (moebiusMap γ z) * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹) := by
    have hcr := dzbar_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hWreal : DifferentiableAt ℝ (moebiusMap W) (h z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hWdd.differentiableAt).1
  have hdzW : dz (moebiusMap W) (h z) = ((moebiusDenom W (h z)) ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hWdd.differentiableAt, hWdd.deriv]
  have hdzbW : dzbar (moebiusMap W) (h z) = 0 :=
    dzbar_eq_zero_of_differentiableAt hWdd.differentiableAt
  have hRdz : dz (fun w => moebiusMap W (h w)) z
      = ((moebiusDenom W (h z)) ^ 2)⁻¹ * dz h z := by
    have hcr := dz_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hRdzb : dzbar (fun w => moebiusMap W (h w)) z
      = ((moebiusDenom W (h z)) ^ 2)⁻¹ * dzbar h z := by
    have hcr := dzbar_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  -- the two Wirtinger equations
  have hEq1 : dz h (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹
      = ((moebiusDenom W (h z)) ^ 2)⁻¹ * dz h z := by
    rw [← hLdz, ← hRdz]
    exact hdzEq
  have hEq2 : dzbar h (moebiusMap γ z) * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹)
      = ((moebiusDenom W (h z)) ^ 2)⁻¹ * dzbar h z := by
    rw [← hLdzb, ← hRdzb]
    exact hdzbEq
  rw [hbel_p, hbel_z, map_inv₀, map_pow] at hEq2
  -- nonvanishing of the holomorphic Wirtinger derivatives from the Jacobian identity
  have hdzne : dz h z ≠ 0 := by
    intro h0
    rw [det_fderiv_eq_wirtinger, h0] at hdet_z
    simp only [norm_zero] at hdet_z
    nlinarith [norm_nonneg (dzbar h z), sq_nonneg ‖dzbar h z‖]
  have hdzpne : dz h (moebiusMap γ z) ≠ 0 := by
    intro h0
    rw [det_fderiv_eq_wirtinger, h0] at hdet_p
    simp only [norm_zero] at hdet_p
    nlinarith [norm_nonneg (dzbar h (moebiusMap γ z)), sq_nonneg ‖dzbar h (moebiusMap γ z)‖]
  have hD2 : (moebiusDenom γ z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hE2 : (moebiusDenom W (h z)) ^ 2 ≠ 0 := pow_ne_zero 2 hWd
  have hcD : starRingEnd ℂ (moebiusDenom γ z) ≠ 0 := by simpa using hz
  have hcD2 : (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 ≠ 0 := pow_ne_zero 2 hcD
  field_simp [hD2, hE2, hcD2] at hEq1 hEq2
  have hgoal2 : bh.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2 * dz h z
      = bh.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 * dz h z := by
    linear_combination hEq2 - bh.μ (moebiusMap γ z) * hEq1
  exact mul_right_cancel₀ hdzne hgoal2

/-- The coefficient of `x.w ∘ F` for a moduli-group element `F` is again a Teichmüller
representative: symmetric by the symmetry clauses, invariant by the compatibility clauses and
the equivariance of `x.w`. -/
theorem exists_pull_rep (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) :
    ∃ y : TeichRep Γ₀, IsQCAnalytic (x.w ∘ ⇑F) y.b := by
  obtain ⟨⟨K, hK⟩, hsymF, hF5, hF6⟩ := hF
  obtain ⟨bF, -, hFqc⟩ := isQCAnalytic_of_isQCGeometric hK.1 hK
  obtain ⟨bc, -, hbc⟩ := exists_isQCAnalytic_comp x.w_isQCAnalytic hFqc
  -- symmetry: `conj ∘ (w ∘ F) ∘ conj = w ∘ F`, so the coefficient equals its reflection a.e.
  have hsymm : IsSymmetricBeltrami bc := by
    have hcc := isQCAnalytic_conj_conj hbc
    have hfeq : (fun z => starRingEnd ℂ ((x.w ∘ ⇑F) (starRingEnd ℂ z))) = x.w ∘ ⇑F := by
      funext z
      simp only [Function.comp_apply]
      rw [hsymF z, x.w_conj (F z), Complex.conj_conj]
    rw [hfeq] at hcc
    exact (isSymmetricBeltrami_iff_reflect bc).mpr (beltrami_coeff_unique_ae hcc hbc)
  -- invariance: chain the compatibility clause with the equivariance of `x.w`
  have hinv : IsInvariantBeltrami' Γ₀ bc := by
    intro γ hγ
    obtain ⟨γ', hγ'm, haeF⟩ := hF5 γ hγ
    obtain ⟨W, hW⟩ := exists_sl2_equivariant x.w_isQCAnalytic x.w_zero x.w_one x.w_conj γ'
      (x.inv γ' hγ'm)
    refine isInvariantBeltrami'_single_of_moebius_conj hbc γ ⟨W, ?_⟩
    have hdet' : (γ' 0 0 : ℂ) * (γ' 1 1 : ℂ) - (γ' 0 1 : ℂ) * (γ' 1 0 : ℂ) = 1 := by
      have hd := Matrix.SpecialLinearGroup.det_coe γ'
      rw [Matrix.det_fin_two] at hd
      exact_mod_cast hd
    have hpole' : ∀ᵐ z : ℂ, moebiusDenom γ' (F z) ≠ 0 := by
      have hPsub : Set.Subsingleton {w : ℂ | moebiusDenom γ' w = 0} := by
        intro w₁ hw₁ w₂ hw₂
        have h₁' : (γ' 1 0 : ℂ) * w₁ + (γ' 1 1 : ℂ) = 0 := hw₁
        have h₂' : (γ' 1 0 : ℂ) * w₂ + (γ' 1 1 : ℂ) = 0 := hw₂
        by_cases hc : γ' 1 0 = 0
        · exfalso
          have hcC : ((γ' 1 0 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
          rw [hcC, zero_mul, zero_add] at h₁'
          have hd : ((γ' 1 1 : ℝ) : ℂ) = 0 := h₁'
          rw [hcC, hd] at hdet'
          simp at hdet'
        · have hcC : ((γ' 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
          have hmul : (γ' 1 0 : ℂ) * w₁ = (γ' 1 0 : ℂ) * w₂ := by
            linear_combination h₁' - h₂'
          exact mul_left_cancel₀ hcC hmul
      have hpre : Set.Subsingleton (⇑F ⁻¹' {w : ℂ | moebiusDenom γ' w = 0}) := by
        intro a ha b hb
        exact F.injective (hPsub ha hb)
      rw [ae_iff]
      refine measure_mono_null (fun z hz => ?_) (hpre.measure_zero volume)
      simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hz
      exact hz
    filter_upwards [haeF, hpole'] with z h1 h2
    simp only [Function.comp_apply]
    rw [h1]
    exact hW (F z) h2
  exact ⟨⟨bc, hsymm, hinv⟩, hbc⟩

/-- The pullback of a representative along a moduli-group element: a representative whose
coefficient is the coefficient of `x.w ∘ F`. -/
noncomputable def TeichRep.pull (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ)
    (hF : F ∈ modGroup Γ₀) : TeichRep Γ₀ :=
  (exists_pull_rep x F hF).choose

/-- The pulled representative carries a coefficient of `x.w ∘ F`. -/
theorem TeichRep.pull_isQCAnalytic (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ)
    (hF : F ∈ modGroup Γ₀) : IsQCAnalytic (x.w ∘ ⇑F) (x.pull F hF).b :=
  (exists_pull_rep x F hF).choose_spec

/-- The normalized solution of the pulled representative renormalizes `x.w ∘ F` by the real
affine map matching its values at `0` and `1`: the renormalized composite is quasiconformal
with the pulled coefficient, and it fixes `0` and `1`. The denominator is a nonzero real
number, as `x.w ∘ F` is injective and carries the real line into itself. -/
theorem TeichRep.pull_w' (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) :
    (x.pull F hF).w
      = fun z => (x.w (F z) - x.w (F 0)) / (x.w (F 1) - x.w (F 0)) := by
  have hden : x.w (F 1) - x.w (F 0) ≠ 0 :=
    sub_ne_zero.mpr fun hcon => one_ne_zero (F.injective (x.w_injective hcon))
  have haff : IsQCAnalytic (fun z => (x.w (F 1) - x.w (F 0))⁻¹ * (x.w ∘ ⇑F) z
      + -((x.w (F 1) - x.w (F 0))⁻¹ * x.w (F 0))) (x.pull F hF).b :=
    (x.pull_isQCAnalytic F hF).affine_postcomp (inv_ne_zero hden)
      (-((x.w (F 1) - x.w (F 0))⁻¹ * x.w (F 0)))
  have hfun : (fun z => (x.w (F 1) - x.w (F 0))⁻¹ * (x.w ∘ ⇑F) z
        + -((x.w (F 1) - x.w (F 0))⁻¹ * x.w (F 0)))
      = fun z => (x.w (F z) - x.w (F 0)) / (x.w (F 1) - x.w (F 0)) := by
    funext z
    simp only [Function.comp_apply, div_eq_mul_inv]
    ring
  rw [hfun] at haff
  have h0 : (fun z => (x.w (F z) - x.w (F 0)) / (x.w (F 1) - x.w (F 0))) 0 = 0 := by
    simp only [sub_self, zero_div]
  have h1 : (fun z => (x.w (F z) - x.w (F 0)) / (x.w (F 1) - x.w (F 0))) 1 = 1 :=
    div_self hden
  exact ((x.pull F hF).w_unique haff h0 h1).symm

/-! ## The action on Teichmüller space -/

/-- Pulling back respects inseparability: inseparable representatives have equal boundary
values, hence so do their pullbacks. -/
theorem pull_mk_congr (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) :
    ∀ x y : TeichRep Γ₀, Inseparable x y →
      (SeparationQuotient.mk (x.pull F hF) : Teich Γ₀)
        = SeparationQuotient.mk (y.pull F hF) := by
  intro x y hxy
  have hb : ∀ t : ℝ, x.w t = y.w t := inseparable_iff_boundary_eq.mp hxy
  have hreal : ∀ s : ℝ, x.w (F (s : ℂ)) = y.w (F (s : ℂ)) := by
    intro s
    have him : (F (s : ℂ)).im = 0 := modGroup_real_im hF s
    have heq : (((F (s : ℂ)).re : ℝ) : ℂ) = F (s : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    rw [← heq]
    exact hb ((F (s : ℂ)).re)
  have h0 : x.w (F 0) = y.w (F 0) := by
    have h := hreal 0
    rwa [Complex.ofReal_zero] at h
  have h1 : x.w (F 1) = y.w (F 1) := by
    have h := hreal 1
    rwa [Complex.ofReal_one] at h
  rw [Teich.mk_eq_mk_iff_boundary]
  intro t
  rw [x.pull_w' F hF, y.pull_w' F hF]
  simp only [hreal t, h0, h1]

/-- The left action of the moduli group on Teichmüller space: `F` acts by pulling back
representatives along `F⁻¹`. -/
noncomputable def Teich.modSMul (F : modGroup Γ₀) (ξ : Teich Γ₀) : Teich Γ₀ :=
  SeparationQuotient.lift
    (fun x : TeichRep Γ₀ =>
      (SeparationQuotient.mk (x.pull (↑(F⁻¹)) (F⁻¹).2) : Teich Γ₀))
    (pull_mk_congr (↑(F⁻¹)) (F⁻¹).2) ξ

set_option backward.isDefEq.respectTransparency false in
/-- The identity of the moduli group acts trivially: the renormalization of `x.w` at its
values `x.w 0 = 0` and `x.w 1 = 1` is `x.w` itself. -/
theorem Teich.modSMul_one (ξ : Teich Γ₀) : Teich.modSMul 1 ξ = ξ := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk ξ
  unfold Teich.modSMul
  rw [SeparationQuotient.lift_mk]
  refine Teich.mk_eq_mk_iff_boundary.mpr fun t => ?_
  rw [TeichRep.pull_w']
  have h1 : ∀ z : ℂ, (↑((1 : modGroup Γ₀)⁻¹) : ℂ ≃ₜ ℂ) z = z := by
    intro z
    rw [inv_one]
    rfl
  simp only [h1, x.w_zero, x.w_one, sub_zero, div_one]

set_option backward.isDefEq.respectTransparency false in
/-- Pull-by-inverse is a left action: `(F G)⁻¹ = G⁻¹ F⁻¹` composes contravariantly with the
contravariant pullback. -/
theorem Teich.modSMul_mul (F G : modGroup Γ₀) (ξ : Teich Γ₀) :
    Teich.modSMul (F * G) ξ = Teich.modSMul F (Teich.modSMul G ξ) := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk ξ
  unfold Teich.modSMul
  rw [SeparationQuotient.lift_mk, SeparationQuotient.lift_mk, SeparationQuotient.lift_mk]
  refine Teich.mk_eq_mk_iff_boundary.mpr fun t => ?_
  rw [TeichRep.pull_w', TeichRep.pull_w', TeichRep.pull_w']
  have h1 : ∀ z : ℂ, (↑((F * G)⁻¹) : ℂ ≃ₜ ℂ) z
      = (↑(G⁻¹) : ℂ ≃ₜ ℂ) ((↑(F⁻¹) : ℂ ≃ₜ ℂ) z) := by
    intro z
    rw [mul_inv_rev]
    rfl
  simp only [h1]
  have hxinj := x.w_injective
  have hqp : x.w ((↑(G⁻¹) : ℂ ≃ₜ ℂ) 1) - x.w ((↑(G⁻¹) : ℂ ≃ₜ ℂ) 0) ≠ 0 := by
    refine sub_ne_zero.mpr fun hcon => ?_
    exact one_ne_zero ((↑(G⁻¹) : ℂ ≃ₜ ℂ).injective (hxinj hcon))
  have hcb : x.w ((↑(G⁻¹) : ℂ ≃ₜ ℂ) ((↑(F⁻¹) : ℂ ≃ₜ ℂ) 1))
      - x.w ((↑(G⁻¹) : ℂ ≃ₜ ℂ) ((↑(F⁻¹) : ℂ ≃ₜ ℂ) 0)) ≠ 0 := by
    refine sub_ne_zero.mpr fun hcon => ?_
    exact one_ne_zero
      ((↑(F⁻¹) : ℂ ≃ₜ ℂ).injective ((↑(G⁻¹) : ℂ ≃ₜ ℂ).injective (hxinj hcon)))
  rw [div_sub_div_same, div_sub_div_same, sub_sub_sub_cancel_right,
    sub_sub_sub_cancel_right, div_div_div_cancel_right₀]
  exact hqp

/-- The moduli group acts on Teichmüller space. -/
noncomputable instance : MulAction (modGroup Γ₀) (Teich Γ₀) where
  smul := Teich.modSMul
  one_smul := Teich.modSMul_one
  mul_smul := Teich.modSMul_mul

/-- The action computed on classes of representatives. -/
theorem Teich.smul_mk (F : modGroup Γ₀) (x : TeichRep Γ₀) :
    F • Teich.mk x = Teich.mk (x.pull (↑(F⁻¹)) (F⁻¹).2) := by
  rfl

/-! ## Isometry of the action -/

/-- Pulling back both representatives along a moduli-group element does not change the
dilatation set: candidates are conjugated by the real affine renormalizations of the two
pullbacks and reindexed along the real line by the boundary values of `F`; real affine
conjugation preserves the dilatation. -/
theorem dilatationSet_pull (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) (x y : TeichRep Γ₀) :
    dilatationSet (x.pull F hF) (y.pull F hF) = dilatationSet x y := by
  have hdenx : x.w (F 1) - x.w (F 0) ≠ 0 :=
    sub_ne_zero.mpr fun hcon => one_ne_zero (F.injective (x.w_injective hcon))
  have hdeny : y.w (F 1) - y.w (F 0) ≠ 0 :=
    sub_ne_zero.mpr fun hcon => one_ne_zero (F.injective (y.w_injective hcon))
  have hpwx := TeichRep.pull_w' x F hF
  have hpwy := TeichRep.pull_w' y F hF
  have hFr : ∀ t : ℝ, (((F (t : ℂ)).re : ℝ) : ℂ) = F (t : ℂ) := fun t =>
    Complex.ext (by simp) (by simp [modGroup_real_im hF t])
  have haff : ∀ u c d : ℂ, d⁻¹ * u + -(d⁻¹ * c) = (u - c) / d := by
    intro u c d
    rw [div_eq_mul_inv]
    ring
  have hinvaff : ∀ u c d : ℂ, d ≠ 0 → d * ((u - c) / d) + c = u := by
    intro u c d hd
    field_simp
    ring
  ext K
  simp only [dilatationSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨G, hG, hGb⟩
    refine ⟨affineMap (x.w (F 1) - x.w (F 0)) (x.w (F 0)) ∘ (G ∘ affineMap
        (y.w (F 1) - y.w (F 0))⁻¹ (-((y.w (F 1) - y.w (F 0))⁻¹ * y.w (F 0)))),
      isQCGeometric_affine_comp (isQCGeometric_comp_affine hG (inv_ne_zero hdeny) _) hdenx,
      fun t => ?_⟩
    obtain ⟨s, hs0⟩ := modGroup_real_surjective hF t
    have hs : (F (s : ℂ)).re = t := hs0
    have hFs : F (s : ℂ) = (t : ℂ) := by rw [← hFr s, hs]
    rw [← hFs]
    simp only [Function.comp_apply, affineMap_apply]
    rw [haff (y.w (F (s : ℂ))) (y.w (F 0)) (y.w (F 1) - y.w (F 0))]
    have hpy : (y.pull F hF).w (s : ℂ)
        = (y.w (F (s : ℂ)) - y.w (F 0)) / (y.w (F 1) - y.w (F 0)) := congrFun hpwy (s : ℂ)
    have hpx : (x.pull F hF).w (s : ℂ)
        = (x.w (F (s : ℂ)) - x.w (F 0)) / (x.w (F 1) - x.w (F 0)) := congrFun hpwx (s : ℂ)
    rw [← hpy, hGb s, hpx]
    exact hinvaff (x.w (F (s : ℂ))) (x.w (F 0)) (x.w (F 1) - x.w (F 0)) hdenx
  · rintro ⟨G, hG, hGb⟩
    refine ⟨affineMap (x.w (F 1) - x.w (F 0))⁻¹ (-((x.w (F 1) - x.w (F 0))⁻¹ * x.w (F 0)))
        ∘ (G ∘ affineMap (y.w (F 1) - y.w (F 0)) (y.w (F 0))),
      isQCGeometric_affine_comp (isQCGeometric_comp_affine hG hdeny _) (inv_ne_zero hdenx),
      fun t => ?_⟩
    have hpy : (y.pull F hF).w (t : ℂ)
        = (y.w (F (t : ℂ)) - y.w (F 0)) / (y.w (F 1) - y.w (F 0)) := congrFun hpwy (t : ℂ)
    have hpx : (x.pull F hF).w (t : ℂ)
        = (x.w (F (t : ℂ)) - x.w (F 0)) / (x.w (F 1) - x.w (F 0)) := congrFun hpwx (t : ℂ)
    rw [hpy, hpx]
    simp only [Function.comp_apply, affineMap_apply]
    rw [hinvaff (y.w (F (t : ℂ))) (y.w (F 0)) (y.w (F 1) - y.w (F 0)) hdeny]
    have hGF : G (y.w (F (t : ℂ))) = x.w (F (t : ℂ)) := by
      rw [← hFr t]
      exact hGb ((F (t : ℂ)).re)
    rw [hGF]
    exact haff (x.w (F (t : ℂ))) (x.w (F 0)) (x.w (F 1) - x.w (F 0))

/-- Each moduli-group element acts isometrically on Teichmüller space. -/
theorem Teich.isometry_smul_mod (F : modGroup Γ₀) :
    Isometry (fun ξ : Teich Γ₀ => F • ξ) := by
  refine Isometry.of_dist_eq fun ξ η => ?_
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk ξ
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk η
  have h1 : dist (Teich.mk (x.pull (↑(F⁻¹)) (F⁻¹).2)) (Teich.mk (y.pull (↑(F⁻¹)) (F⁻¹).2))
      = teichPseudoDist (x.pull (↑(F⁻¹)) (F⁻¹).2) (y.pull (↑(F⁻¹)) (F⁻¹).2) :=
    Teich.dist_mk _ _
  have h2 : dist (Teich.mk x) (Teich.mk y) = teichPseudoDist x y := Teich.dist_mk x y
  change dist (Teich.mk (x.pull (↑(F⁻¹)) (F⁻¹).2)) (Teich.mk (y.pull (↑(F⁻¹)) (F⁻¹).2))
      = dist (Teich.mk x) (Teich.mk y)
  rw [h1, h2]
  unfold teichPseudoDist
  rw [dilatationSet_pull (↑(F⁻¹)) (F⁻¹).2 x y]

/-- The moduli-group action on Teichmüller space is isometric. -/
instance : IsIsometricSMul (modGroup Γ₀) (Teich Γ₀) :=
  ⟨Teich.isometry_smul_mod⟩

/-- **Moduli space** over the base `Γ₀`: the orbit space of Teichmüller space under the
moduli group. -/
def Moduli (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quotient (MulAction.orbitRel (modGroup Γ₀) (Teich Γ₀))

end RiemannDynamics

import RiemannDynamics.Teichmuller.Metric
import RiemannDynamics.Teichmuller.UpperQC
import RiemannDynamics.Surface.MappingClassGroup
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# The moduli group and its isometric action on Teichmüller space

The moduli group `modGroup Γ₀` consists of the symmetric quasiconformal self-homeomorphisms
of the plane compatible with `Γ₀` on both sides (`F ∘ γ = γ' ∘ F` a.e. with `γ, γ'` running
through `Γ₀`). It acts on `Teich Γ₀` by pulling back representatives along the inverse,
`F • [x] = [x.pull F⁻¹]`, where the pulled representative is characterized by the
renormalization `(x.pull F).w = ((x.w ∘ F) − x.w (F 0)) / (x.w (F 1) − x.w (F 0))`, which
fixes `0` and `1`. The action is isometric: candidate maps for a pair of pulled
representatives are the candidates for the original pair conjugated by real affine maps and
reindexed along the real line. The orbit space is the moduli space `Moduli Γ₀`.
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
    simp only [Set.mem_setOf_eq, ne_eq, not_not] at hz
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
    simp only [Set.mem_setOf_eq, ne_eq, not_not] at hz
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
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le _)
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
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
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
      simp only [Set.mem_setOf_eq, ne_eq, not_not] at hz
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
  simp only [dilatationSet, Set.mem_setOf_eq]
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

/-! ## Upper-half-plane moduli re-markings

The plane moduli group is a strict sub-groupoid of the classical Teichmüller modular
action: the boundary map of a plane element fixes `∞`, while the boundary realization of a
general mapping class need not. The classical modular action acts on coefficients through
quasiconformal self-maps of the upper half plane compatible with `Γ₀`, with no plane
extension; the plane elements embed by restriction. -/

/-- An **upper-half-plane moduli re-marking** over `Γ₀`: a quasiconformal self-map of the
upper half plane with coefficient bound below `1`, compatible with `Γ₀` on both sides on
the upper half plane. -/
structure ModGroupUpper (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) where
  /-- The re-marking map on the upper half plane. -/
  g : ℂ → ℂ
  /-- A two-sided inverse of the re-marking on the upper half plane. -/
  ginv : ℂ → ℂ
  /-- The Beltrami bound of the re-marking. -/
  κ : ℝ
  /-- The Beltrami bound is below `1`. -/
  hκ : κ < 1
  /-- The re-marking is an upper-half-plane quasiconformal map. -/
  qc : IsQCUpper g ginv κ
  /-- Forward `Γ₀`-compatibility on the upper half plane. -/
  compat : ∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
    g (moebiusMap γ z) = moebiusMap γ' (g z)
  /-- Backward `Γ₀`-compatibility on the upper half plane. -/
  compat' : ∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
    g (moebiusMap γ z) = moebiusMap γ' (g z)

/-- A plane moduli-group element mapping the upper half plane into itself restricts to an
upper-half-plane re-marking: symmetry carries the half-plane preservation to the inverse,
and the almost-everywhere compatibility upgrades to every point of the upper half plane by
continuity. -/
theorem exists_modGroupUpper_of_modGroup {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀)
    (hup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im) :
    ∃ P : ModGroupUpper Γ₀, P.g = ⇑F := by
  sorry

/-- The **Wirtinger quotient** of a map: the ratio of the conjugate-linear and the
complex-linear parts of its real derivative. -/
noncomputable def wirtingerQuotient (f : ℂ → ℂ) (z : ℂ) : ℂ := dzbar f z / dz f z

/-- The Wirtinger quotient of a re-marked solution is measurable. -/
theorem measurable_wirtingerQuotient_remark (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    Measurable (wirtingerQuotient (x.w ∘ P.g)) := by
  have h1 : Measurable fun z : ℂ => (fderiv ℝ (x.w ∘ P.g) z) 1 :=
    (measurable_fderiv ℝ (x.w ∘ P.g)).apply_continuousLinearMap 1
  have hI : Measurable fun z : ℂ => (fderiv ℝ (x.w ∘ P.g) z) Complex.I :=
    (measurable_fderiv ℝ (x.w ∘ P.g)).apply_continuousLinearMap Complex.I
  have hdz : Measurable (dz (x.w ∘ P.g)) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ (x.w ∘ P.g) z) 1 - Complex.I * (fderiv ℝ (x.w ∘ P.g) z) Complex.I)
    exact (h1.sub (hI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdzbar : Measurable (dzbar (x.w ∘ P.g)) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ (x.w ∘ P.g) z) 1 + Complex.I * (fderiv ℝ (x.w ∘ P.g) z) Complex.I)
    exact (h1.add (hI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  change Measurable fun z : ℂ => dzbar (x.w ∘ P.g) z / dz (x.w ∘ P.g) z
  exact hdzbar.div hdz

/-- The Wirtinger quotient of a re-marked solution is essentially bounded below `1` on the
upper half plane: dilatations multiply under composition. -/
theorem wirtingerQuotient_remark_bound (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    eLpNormEssSup (wirtingerQuotient (x.w ∘ P.g))
      (volume.restrict {z : ℂ | 0 < z.im}) < 1 := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  -- Wirtinger measurability of the re-marking map
  have hg1 : Measurable fun z : ℂ => (fderiv ℝ P.g z) 1 :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap 1
  have hgI : Measurable fun z : ℂ => (fderiv ℝ P.g z) Complex.I :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap Complex.I
  have hdzg : Measurable (dz P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 - Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.sub (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdzbarg : Measurable (dzbar P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 + Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.add (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdetmeas : Measurable fun z : ℂ => (fderiv ℝ P.g z).det := by
    have hfun : (fun z : ℂ => (fderiv ℝ P.g z).det)
        = fun z : ℂ => ‖dz P.g z‖ ^ 2 - ‖dzbar P.g z‖ ^ 2 :=
      funext fun z => det_fderiv_eq_wirtinger P.g z
    rw [hfun]
    exact (hdzg.norm.pow_const 2).sub (hdzbarg.norm.pow_const 2)
  -- preimages of null sets under `P.g` are null on the differentiability set: the image of
  -- a positive-Jacobian piece has measure `∫ |det|` by the area formula, and it sits in a
  -- null set, forcing the piece to be null
  have hpull : ∀ N : Set ℂ, volume N = 0 →
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det) → P.g z ∉ N := by
    intro N hN
    have hgae : AEMeasurable P.g (volume.restrict {z : ℂ | 0 < z.im}) :=
      P.qc.cont.aemeasurable hU
    have hgeq : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), P.g z = hgae.mk P.g z :=
      hgae.ae_eq_mk
    have hbadnull : (volume.restrict {z : ℂ | 0 < z.im})
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} = 0 := ae_iff.mp hgeq
    obtain ⟨T, hTsub, hTmeas, hTnull⟩ : ∃ T : Set ℂ,
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} ⊆ T ∧ MeasurableSet T
          ∧ (volume.restrict {z : ℂ | 0 < z.im}) T = 0 :=
      ⟨toMeasurable (volume.restrict {z : ℂ | 0 < z.im}) {z : ℂ | ¬ P.g z = hgae.mk P.g z},
        subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hbadnull⟩
    obtain ⟨N', hNsub, hN'meas, hN'null⟩ : ∃ N' : Set ℂ,
        N ⊆ N' ∧ MeasurableSet N' ∧ volume N' = 0 :=
      ⟨toMeasurable volume N, subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hN⟩
    set S : Set ℂ := ({z : ℂ | 0 < z.im} ∩ {z : ℂ | DifferentiableAt ℝ P.g z}
      ∩ {z : ℂ | 0 < (fderiv ℝ P.g z).det} ∩ (hgae.mk P.g ⁻¹' N')) \ T with hSdef
    have hSmeas : MeasurableSet S :=
      (((hU.inter (measurableSet_of_differentiableAt ℝ P.g)).inter
        (measurableSet_lt measurable_const hdetmeas)).inter
          (hgae.measurable_mk hN'meas)).diff hTmeas
    have hSfacts : ∀ z ∈ S, 0 < z.im ∧ DifferentiableAt ℝ P.g z
        ∧ 0 < (fderiv ℝ P.g z).det ∧ P.g z ∈ N' ∧ z ∉ T := by
      intro z hz
      rw [hSdef] at hz
      obtain ⟨⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩, hz5⟩ := hz
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hz5 (hTsub hne)
      exact ⟨hz1, hz2, hz3, by rw [hgz]; exact hz4, hz5⟩
    have hfd : ∀ z ∈ S, HasFDerivWithinAt P.g (fderiv ℝ P.g z) S z := fun z hz =>
      ((hSfacts z hz).2.1.hasFDerivAt).hasFDerivWithinAt
    have hinjS : Set.InjOn P.g S := by
      intro p hp q hq hpq
      have h1 := P.qc.left_inv p (hSfacts p hp).1
      have h2 := P.qc.left_inv q (hSfacts q hq).1
      rw [← h1, ← h2, hpq]
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjS
      (fun _ => (1 : ℝ≥0∞))
    rw [setLIntegral_one] at hcov
    simp only [mul_one] at hcov
    have himgnull : volume (P.g '' S) = 0 := by
      refine le_antisymm (le_trans (measure_mono ?_) hN'null.le) (zero_le _)
      rintro w ⟨z, hz, rfl⟩
      exact (hSfacts z hz).2.2.2.1
    have hint0 : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
      rw [← hcov]
      exact himgnull
    have hSnull : volume S = 0 := by
      have hmeasint : Measurable fun z : ℂ => ENNReal.ofReal |(fderiv ℝ P.g z).det| :=
        (continuous_abs.measurable.comp hdetmeas).ennreal_ofReal
      have h2 := (lintegral_eq_zero_iff hmeasint).mp hint0
      have h2' : ∀ᵐ z ∂(volume.restrict S),
          ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
        filter_upwards [h2] with z hz2
        simpa using hz2
      have h3 : ∀ᵐ z : ℂ, z ∈ S → ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 :=
        (ae_restrict_iff' hSmeas).mp h2'
      rw [ae_iff] at h3
      refine le_antisymm (le_trans (measure_mono ?_) h3.le) (zero_le _)
      intro z hz
      simp only [Set.mem_setOf_eq, Classical.not_imp]
      refine ⟨hz, ?_⟩
      intro h0
      rw [ENNReal.ofReal_eq_zero] at h0
      have hpos := abs_pos.mpr (ne_of_gt (hSfacts z hz).2.2.1)
      linarith
    rw [ae_iff, Measure.restrict_apply' hU]
    have hTH : volume (T ∩ {z : ℂ | 0 < z.im}) = 0 := by
      rw [Measure.restrict_apply hTmeas] at hTnull
      exact hTnull
    refine measure_mono_null ?_ (measure_union_null hTH hSnull)
    intro z hz
    obtain ⟨hzbad, hzU⟩ := hz
    simp only [Set.mem_setOf_eq, Classical.not_imp, not_not] at hzbad
    obtain ⟨⟨hdiff, hdet⟩, hgN⟩ := hzbad
    by_cases hzT : z ∈ T
    · exact Or.inl ⟨hzT, hzU⟩
    · refine Or.inr ?_
      rw [hSdef]
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hzT (hTsub hne)
      exact ⟨⟨⟨⟨hzU, hdiff⟩, hdet⟩, by rw [Set.mem_preimage, ← hgz]; exact hNsub hgN⟩, hzT⟩
  -- dilatation constants
  have ha0 : 0 ≤ max P.κ 0 := le_max_right _ _
  have ha1 : max P.κ 0 < 1 := max_lt P.hκ zero_lt_one
  have hbw0 : 0 ≤ x.b.normInf := x.b.normInf_nonneg
  have hbw1 : x.b.normInf < 1 := x.b.normInf_lt_one
  have h1pab : 0 < 1 + max P.κ 0 * x.b.normInf := by nlinarith [mul_nonneg ha0 hbw0]
  have hκ'0 : 0 ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) :=
    div_nonneg (by linarith) h1pab.le
  have hκ'1 : (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) < 1 := by
    rw [div_lt_one h1pab]
    nlinarith [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hbw1)]
  -- the sharp composition estimate on squared norms, with the shared cross term
  have hsharp : ∀ a b s t q R : ℝ, 0 ≤ a → a < 1 → 0 ≤ b → b < 1 → 0 ≤ s → 0 ≤ t →
      0 ≤ q → t ≤ a * s → q ≤ b → |R| ≤ q * s * t →
      (t ^ 2 + q ^ 2 * s ^ 2 + 2 * R) * (1 + a * b) ^ 2
        ≤ (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * R) := by
    intro a b s t q R ha0' ha1' hb0' hb1' hs ht hq htas hqb hRb
    have hqst : R ≤ q * s * t := (abs_le.mp hRb).2
    have hlin : (t + q * s) * (1 + a * b) ≤ (a + b) * (s + q * t) := by
      have h1 : 0 ≤ (1 - a ^ 2) * ((b - q) * s) :=
        mul_nonneg (by nlinarith) (mul_nonneg (by linarith) hs)
      have h2 : 0 ≤ (1 + a * b - q * (a + b)) * (a * s - t) := by
        refine mul_nonneg ?_ (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right hqb (show (0:ℝ) ≤ a + b by linarith),
          mul_nonneg hb0' (sub_nonneg.mpr hb1'.le)]
      nlinarith [h1, h2]
    have hXnn : 0 ≤ (t + q * s) * (1 + a * b) :=
      mul_nonneg (add_nonneg ht (mul_nonneg hq hs))
        (by nlinarith [mul_nonneg ha0' hb0'])
    have hYnn : 0 ≤ (a + b) * (s + q * t) := le_trans hXnn hlin
    have hsq : ((t + q * s) * (1 + a * b)) ^ 2 ≤ ((a + b) * (s + q * t)) ^ 2 := by
      nlinarith [hlin, hXnn, hYnn]
    have hfac : 0 ≤ (q * s * t - R) * ((1 + a * b) ^ 2 - (a + b) ^ 2) := by
      refine mul_nonneg (by linarith) ?_
      nlinarith [mul_pos (mul_pos (mul_pos (show (0:ℝ) < 1 + a by linarith)
        (show (0:ℝ) < 1 + b by linarith)) (show (0:ℝ) < 1 - a by linarith))
        (show (0:ℝ) < 1 - b by linarith)]
    nlinarith [hsq, hfac]
  -- the almost-everywhere good set of the plane solution
  have hbw_ae : ∀ᵐ w : ℂ, ‖x.b.μ w‖ ≤ x.b.normInf := by
    filter_upwards [enorm_ae_le_eLpNormEssSup x.b.μ volume] with w hw
    have h2 := ENNReal.toReal_mono (ne_top_of_lt x.b.bound) hw
    simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
  have hwgood : ∀ᵐ w : ℂ, DifferentiableAt ℝ x.w w ∧ 0 < (fderiv ℝ x.w w).det
      ∧ dzbar x.w w = x.b.μ w * dz x.w w ∧ ‖x.b.μ w‖ ≤ x.b.normInf := by
    filter_upwards [x.w_isQCAnalytic.1.2, x.w_isQCAnalytic.2.2, hbw_ae] with w h1 h2 h3
    refine ⟨?_, h1, h2, h3⟩
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at h1
    simp [ContinuousLinearMap.det] at h1
  have hNnull : volume {w : ℂ | ¬ (DifferentiableAt ℝ x.w w ∧ 0 < (fderiv ℝ x.w w).det
      ∧ dzbar x.w w = x.b.μ w * dz x.w w ∧ ‖x.b.μ w‖ ≤ x.b.normInf)} = 0 :=
    ae_iff.mp hwgood
  refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound ?_)
    (ENNReal.ofReal_lt_one.mpr hκ'1)
  filter_upwards [P.qc.jac, P.qc.belt, hpull _ hNnull] with z hjac hbelt htr
  have hgdiff : DifferentiableAt ℝ P.g z := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hjac
    simp [ContinuousLinearMap.det] at hjac
  have hw4 := htr ⟨hgdiff, hjac⟩
  simp only [not_not] at hw4
  obtain ⟨hwdiff, hwdet, hwbelt, hwmu⟩ := hw4
  -- chain rule with the Beltrami substitution
  have hcompeq : x.w ∘ P.g = fun w : ℂ => x.w (P.g w) := rfl
  have hdzF := dz_comp hgdiff hwdiff
  have hdzbarF := dzbar_comp hgdiff hwdiff
  have hdzF' : dz (x.w ∘ P.g) z
      = dz x.w (P.g z) * (dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)) := by
    rw [hcompeq, hdzF, hwbelt]
    ring
  have hdzbarF' : dzbar (x.w ∘ P.g) z
      = dz x.w (P.g z) * (dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)) := by
    rw [hcompeq, hdzbarF, hwbelt]
    ring
  -- nonvanishing from the positive Jacobians
  have hpne : dz x.w (P.g z) ≠ 0 := by
    intro h0
    rw [det_fderiv_eq_wirtinger, h0] at hwdet
    simp only [norm_zero] at hwdet
    nlinarith [norm_nonneg (dzbar x.w (P.g z)), sq_nonneg ‖dzbar x.w (P.g z)‖]
  have hgs : ‖dzbar P.g z‖ < ‖dz P.g z‖ := by
    rw [det_fderiv_eq_wirtinger] at hjac
    nlinarith [norm_nonneg (dz P.g z), norm_nonneg (dzbar P.g z)]
  have htle : ‖dzbar P.g z‖ ≤ max P.κ 0 * ‖dz P.g z‖ :=
    le_trans hbelt (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- the shared cross term and the two squared-norm expansions
  have hnumSq : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ ^ 2
      = ‖dzbar P.g z‖ ^ 2 + ‖x.b.μ (P.g z)‖ ^ 2 * ‖dz P.g z‖ ^ 2
        + 2 * (dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re := by
    simp only [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_conj]
    have hcross : dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z))
        = dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z)) := by
      rw [map_mul, Complex.conj_conj]
      ring
    rw [hcross]
  have hdenSq : ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ ^ 2
      = ‖dz P.g z‖ ^ 2 + ‖x.b.μ (P.g z)‖ ^ 2 * ‖dzbar P.g z‖ ^ 2
        + 2 * (dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re := by
    simp only [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_conj]
    have hcross : dz P.g z * starRingEnd ℂ (x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z))
        = dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z)) := by
      rw [map_mul, Complex.conj_conj]
      ring
    rw [hcross]
  have hRb : |(dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re|
      ≤ ‖x.b.μ (P.g z)‖ * ‖dz P.g z‖ * ‖dzbar P.g z‖ := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    exact le_of_eq (by ring)
  have hkey2 := hsharp (max P.κ 0) x.b.normInf ‖dz P.g z‖ ‖dzbar P.g z‖ ‖x.b.μ (P.g z)‖
    ((dz P.g z * dzbar P.g z * starRingEnd ℂ (x.b.μ (P.g z))).re)
    ha0 ha1 hbw0 hbw1 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) htle hwmu hRb
  have hkey3 : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ ^ 2
      * (1 + max P.κ 0 * x.b.normInf) ^ 2
      ≤ (max P.κ 0 + x.b.normInf) ^ 2
        * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ ^ 2 := by
    rw [hnumSq, hdenSq]
    exact hkey2
  have hnormle : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
      * (1 + max P.κ 0 * x.b.normInf)
      ≤ (max P.κ 0 + x.b.normInf)
        * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ := by
    nlinarith [hkey3,
      mul_nonneg (norm_nonneg (dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)))
        h1pab.le,
      mul_nonneg (show (0:ℝ) ≤ max P.κ 0 + x.b.normInf by linarith)
        (norm_nonneg (dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)))]
  -- positivity of the denominator
  have hdenpos : 0 < ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ := by
    have h4 := norm_add_le (dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z))
      (-(x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)))
    simp only [add_neg_cancel_right, norm_neg] at h4
    have h5 : ‖x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖
        ≤ x.b.normInf * ‖dzbar P.g z‖ := by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_right hwmu (norm_nonneg _)
    have h6 : x.b.normInf * ‖dzbar P.g z‖ < ‖dz P.g z‖ :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hbw1.le) hgs
    linarith
  have hFdzpos : 0 < ‖dz (x.w ∘ P.g) z‖ := by
    rw [hdzF', norm_mul]
    exact mul_pos (norm_pos_iff.mpr hpne) hdenpos
  have hnumle : ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
      ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
        * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1pab]
    exact hnormle
  have hquot : ‖wirtingerQuotient (x.w ∘ P.g) z‖
      ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) := by
    have hq : wirtingerQuotient (x.w ∘ P.g) z
        = dzbar (x.w ∘ P.g) z / dz (x.w ∘ P.g) z := rfl
    rw [hq, norm_div, div_le_iff₀ hFdzpos]
    calc ‖dzbar (x.w ∘ P.g) z‖
        = ‖dz x.w (P.g z)‖
          * ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ := by
          rw [hdzbarF', norm_mul]
      _ ≤ ‖dz x.w (P.g z)‖ * ((max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
          * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) :=
        mul_le_mul_of_nonneg_left hnumle (norm_nonneg _)
      _ = (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
          * (‖dz x.w (P.g z)‖
            * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) := by ring
      _ = (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
          * ‖dz (x.w ∘ P.g) z‖ := by rw [hdzF', norm_mul]
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal hquot

/-- The Wirtinger quotient of a re-marked solution satisfies the `Γ₀`-invariance law on the
upper half plane: chain the compatibility of the re-marking with the equivariance of the
normalized solution through the almost-everywhere chain rule. -/
theorem wirtingerQuotient_remark_invariant (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    ∀ γ ∈ Γ₀, ∀ᵐ z : ℂ ∂(volume.restrict {z : ℂ | 0 < z.im}),
      wirtingerQuotient (x.w ∘ P.g) (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = wirtingerQuotient (x.w ∘ P.g) z
          * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  intro γ hγ
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hUopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  -- Wirtinger measurability of the re-marking map
  have hg1 : Measurable fun z : ℂ => (fderiv ℝ P.g z) 1 :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap 1
  have hgI : Measurable fun z : ℂ => (fderiv ℝ P.g z) Complex.I :=
    (measurable_fderiv ℝ P.g).apply_continuousLinearMap Complex.I
  have hdzg : Measurable (dz P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 - Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.sub (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdzbarg : Measurable (dzbar P.g) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ P.g z) 1 + Complex.I * (fderiv ℝ P.g z) Complex.I)
    exact (hg1.add (hgI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdetmeas : Measurable fun z : ℂ => (fderiv ℝ P.g z).det := by
    have hfun : (fun z : ℂ => (fderiv ℝ P.g z).det)
        = fun z : ℂ => ‖dz P.g z‖ ^ 2 - ‖dzbar P.g z‖ ^ 2 :=
      funext fun z => det_fderiv_eq_wirtinger P.g z
    rw [hfun]
    exact (hdzg.norm.pow_const 2).sub (hdzbarg.norm.pow_const 2)
  -- preimages of null sets under `P.g` are null on the differentiability set
  have hpull : ∀ N : Set ℂ, volume N = 0 →
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det) → P.g z ∉ N := by
    intro N hN
    have hgae : AEMeasurable P.g (volume.restrict {z : ℂ | 0 < z.im}) :=
      P.qc.cont.aemeasurable hU
    have hgeq : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), P.g z = hgae.mk P.g z :=
      hgae.ae_eq_mk
    have hbadnull : (volume.restrict {z : ℂ | 0 < z.im})
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} = 0 := ae_iff.mp hgeq
    obtain ⟨T, hTsub, hTmeas, hTnull⟩ : ∃ T : Set ℂ,
        {z : ℂ | ¬ P.g z = hgae.mk P.g z} ⊆ T ∧ MeasurableSet T
          ∧ (volume.restrict {z : ℂ | 0 < z.im}) T = 0 :=
      ⟨toMeasurable (volume.restrict {z : ℂ | 0 < z.im}) {z : ℂ | ¬ P.g z = hgae.mk P.g z},
        subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hbadnull⟩
    obtain ⟨N', hNsub, hN'meas, hN'null⟩ : ∃ N' : Set ℂ,
        N ⊆ N' ∧ MeasurableSet N' ∧ volume N' = 0 :=
      ⟨toMeasurable volume N, subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
        by rw [measure_toMeasurable]; exact hN⟩
    set S : Set ℂ := ({z : ℂ | 0 < z.im} ∩ {z : ℂ | DifferentiableAt ℝ P.g z}
      ∩ {z : ℂ | 0 < (fderiv ℝ P.g z).det} ∩ (hgae.mk P.g ⁻¹' N')) \ T with hSdef
    have hSmeas : MeasurableSet S :=
      (((hU.inter (measurableSet_of_differentiableAt ℝ P.g)).inter
        (measurableSet_lt measurable_const hdetmeas)).inter
          (hgae.measurable_mk hN'meas)).diff hTmeas
    have hSfacts : ∀ z ∈ S, 0 < z.im ∧ DifferentiableAt ℝ P.g z
        ∧ 0 < (fderiv ℝ P.g z).det ∧ P.g z ∈ N' ∧ z ∉ T := by
      intro z hz
      rw [hSdef] at hz
      obtain ⟨⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩, hz5⟩ := hz
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hz5 (hTsub hne)
      exact ⟨hz1, hz2, hz3, by rw [hgz]; exact hz4, hz5⟩
    have hfd : ∀ z ∈ S, HasFDerivWithinAt P.g (fderiv ℝ P.g z) S z := fun z hz =>
      ((hSfacts z hz).2.1.hasFDerivAt).hasFDerivWithinAt
    have hinjS : Set.InjOn P.g S := by
      intro p hp q hq hpq
      have h1 := P.qc.left_inv p (hSfacts p hp).1
      have h2 := P.qc.left_inv q (hSfacts q hq).1
      rw [← h1, ← h2, hpq]
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjS
      (fun _ => (1 : ℝ≥0∞))
    rw [setLIntegral_one] at hcov
    simp only [mul_one] at hcov
    have himgnull : volume (P.g '' S) = 0 := by
      refine le_antisymm (le_trans (measure_mono ?_) hN'null.le) (zero_le _)
      rintro w ⟨z, hz, rfl⟩
      exact (hSfacts z hz).2.2.2.1
    have hint0 : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
      rw [← hcov]
      exact himgnull
    have hSnull : volume S = 0 := by
      have hmeasint : Measurable fun z : ℂ => ENNReal.ofReal |(fderiv ℝ P.g z).det| :=
        (continuous_abs.measurable.comp hdetmeas).ennreal_ofReal
      have h2 := (lintegral_eq_zero_iff hmeasint).mp hint0
      have h2' : ∀ᵐ z ∂(volume.restrict S),
          ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 := by
        filter_upwards [h2] with z hz2
        simpa using hz2
      have h3 : ∀ᵐ z : ℂ, z ∈ S → ENNReal.ofReal |(fderiv ℝ P.g z).det| = 0 :=
        (ae_restrict_iff' hSmeas).mp h2'
      rw [ae_iff] at h3
      refine le_antisymm (le_trans (measure_mono ?_) h3.le) (zero_le _)
      intro z hz
      simp only [Set.mem_setOf_eq, Classical.not_imp]
      refine ⟨hz, ?_⟩
      intro h0
      rw [ENNReal.ofReal_eq_zero] at h0
      have hpos := abs_pos.mpr (ne_of_gt (hSfacts z hz).2.2.1)
      linarith
    rw [ae_iff, Measure.restrict_apply' hU]
    have hTH : volume (T ∩ {z : ℂ | 0 < z.im}) = 0 := by
      rw [Measure.restrict_apply hTmeas] at hTnull
      exact hTnull
    refine measure_mono_null ?_ (measure_union_null hTH hSnull)
    intro z hz
    obtain ⟨hzbad, hzU⟩ := hz
    simp only [Set.mem_setOf_eq, Classical.not_imp, not_not] at hzbad
    obtain ⟨⟨hdiff, hdet⟩, hgN⟩ := hzbad
    by_cases hzT : z ∈ T
    · exact Or.inl ⟨hzT, hzU⟩
    · refine Or.inr ?_
      rw [hSdef]
      have hgz : P.g z = hgae.mk P.g z := by
        by_contra hne
        exact hzT (hTsub hne)
      exact ⟨⟨⟨⟨hzU, hdiff⟩, hdet⟩, by rw [Set.mem_preimage, ← hgz]; exact hNsub hgN⟩, hzT⟩
  -- the exact conjugation identity on the upper half plane
  obtain ⟨γ', hγ'm, hcompat⟩ := P.compat γ hγ
  obtain ⟨W, hW⟩ := exists_sl2_equivariant x.w_isQCAnalytic x.w_zero x.w_one x.w_conj γ'
    (x.inv γ' hγ'm)
  have him0 : ∀ w : ℂ, 0 < w.im → (x.w w).im ≠ 0 := by
    rcases x.w_halfPlane_dichotomy with ⟨hpos, -⟩ | ⟨hneg, -⟩
    · exact fun w hw => ne_of_gt (hpos w hw)
    · exact fun w hw => ne_of_lt (hneg w hw)
  have hFconj : ∀ w : ℂ, 0 < w.im
      → (x.w ∘ P.g) (moebiusMap γ w) = moebiusMap W ((x.w ∘ P.g) w) := by
    intro w hw
    have hgw : 0 < (P.g w).im := P.qc.mapsTo w hw
    have h1 : P.g (moebiusMap γ w) = moebiusMap γ' (P.g w) := hcompat w hw
    change x.w (P.g (moebiusMap γ w)) = moebiusMap W (x.w (P.g w))
    rw [h1]
    exact hW (P.g w) (moebiusDenom_ne_zero_of_im_ne_zero γ' (ne_of_gt hgw))
  -- the composite is differentiable almost everywhere on the upper half plane
  have hwdiffae : ∀ᵐ w : ℂ, DifferentiableAt ℝ x.w w := by
    filter_upwards [x.w_isQCAnalytic.1.2] with w h1
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at h1
    simp [ContinuousLinearMap.det] at h1
  have hNnull : volume {w : ℂ | ¬ DifferentiableAt ℝ x.w w} = 0 := ae_iff.mp hwdiffae
  have hGood : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      DifferentiableAt ℝ (x.w ∘ P.g) z := by
    filter_upwards [P.qc.jac, hpull _ hNnull] with z hjac htr
    have hgdiff : DifferentiableAt ℝ P.g z := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hjac
      simp [ContinuousLinearMap.det] at hjac
    have hw4 := htr ⟨hgdiff, hjac⟩
    simp only [not_not] at hw4
    exact hw4.comp z hgdiff
  have hGoodG : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} → DifferentiableAt ℝ (x.w ∘ P.g) z :=
    (ae_restrict_iff' hU).mp hGood
  -- transport of an a.e. plane statement along the Möbius map `γ`
  have haeMoeb : ∀ Q : ℂ → Prop,
      (∀ᵐ w : ℂ, Q w) → ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 → Q (moebiusMap γ z) := by
    intro Q hQ
    have hopen : IsOpen {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom γ⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hQ ⊢
    have himg : volume (moebiusMap γ⁻¹ ''
        (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le _)
        rw [measure_toMeasurable]
        exact hQ.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap γ⁻¹) (fderiv ℝ (moebiusMap γ⁻¹) w)
            (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap γ⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap γ⁻¹)
          (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) := by
        intro a ha b hb hab
        have ha1 : moebiusMap γ (moebiusMap γ⁻¹ a) = a := by
          rw [moebiusMap_mul γ γ⁻¹ a ha.2, mul_inv_cancel, moebiusMap_one]
        have hb1 : moebiusMap γ (moebiusMap γ⁻¹ b) = b := by
          rw [moebiusMap_mul γ γ⁻¹ b hb.2, mul_inv_cancel, moebiusMap_one]
        rw [← ha1, ← hb1, hab]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom γ⁻¹ (moebiusMap γ z) * moebiusDenom γ z = 1 := by
      rw [moebiusDenom_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom γ⁻¹ (moebiusMap γ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap γ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusMap_one]
  have hGoodT := haeMoeb (fun w : ℂ => w ∈ {z : ℂ | 0 < z.im}
    → DifferentiableAt ℝ (x.w ∘ P.g) w) hGoodG
  -- differentiate the exact conjugation identity at a.e. point of the upper half plane
  filter_upwards [ae_restrict_of_ae hGoodT, ae_restrict_mem hU, ae_restrict_of_ae hGoodG]
    with z htrans hzU hgood
  have hz : 0 < z.im := hzU
  have hdenγ : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz)
  have hγim : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
  have hDz : DifferentiableAt ℝ (x.w ∘ P.g) z := hgood hzU
  have hDp : DifferentiableAt ℝ (x.w ∘ P.g) (moebiusMap γ z) := htrans hdenγ hγim
  have hev : (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w))
      =ᶠ[nhds z] fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w) := by
    filter_upwards [hUopen.mem_nhds hz] with w hw
    exact hFconj w hw
  have hfde : fderiv ℝ (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = fderiv ℝ (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z := hev.fderiv_eq
  have hdzEq : dz (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dz (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z := by
    unfold dz
    rw [hfde]
  have hdzbEq : dzbar (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dzbar (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z := by
    unfold dzbar
    rw [hfde]
  have hγd := hasDerivAt_moebiusMap γ hdenγ
  have hFzim : ((x.w ∘ P.g) z).im ≠ 0 := him0 (P.g z) (P.qc.mapsTo z hz)
  have hWd : moebiusDenom W ((x.w ∘ P.g) z) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero W hFzim
  have hWdd := hasDerivAt_moebiusMap W hWd
  have hLdz : dz (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dz (x.w ∘ P.g) (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹ := by
    have hcr := dz_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hLdzb : dzbar (fun w : ℂ => (x.w ∘ P.g) (moebiusMap γ w)) z
      = dzbar (x.w ∘ P.g) (moebiusMap γ z)
        * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹) := by
    have hcr := dzbar_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hWreal : DifferentiableAt ℝ (moebiusMap W) ((x.w ∘ P.g) z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hWdd.differentiableAt).1
  have hdzW : dz (moebiusMap W) ((x.w ∘ P.g) z)
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hWdd.differentiableAt, hWdd.deriv]
  have hdzbW : dzbar (moebiusMap W) ((x.w ∘ P.g) z) = 0 :=
    dzbar_eq_zero_of_differentiableAt hWdd.differentiableAt
  have hRdz : dz (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dz (x.w ∘ P.g) z := by
    have hcr := dz_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hRdzb : dzbar (fun w : ℂ => moebiusMap W ((x.w ∘ P.g) w)) z
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dzbar (x.w ∘ P.g) z := by
    have hcr := dzbar_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hEq1 : dz (x.w ∘ P.g) (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dz (x.w ∘ P.g) z := by
    rw [← hLdz, ← hRdz]
    exact hdzEq
  have hEq2 : dzbar (x.w ∘ P.g) (moebiusMap γ z)
      * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹)
      = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dzbar (x.w ∘ P.g) z := by
    rw [← hLdzb, ← hRdzb]
    exact hdzbEq
  -- divide out the two Wirtinger identities
  have hq1 : wirtingerQuotient (x.w ∘ P.g) (moebiusMap γ z)
      = dzbar (x.w ∘ P.g) (moebiusMap γ z) / dz (x.w ∘ P.g) (moebiusMap γ z) := rfl
  have hq2 : wirtingerQuotient (x.w ∘ P.g) z
      = dzbar (x.w ∘ P.g) z / dz (x.w ∘ P.g) z := rfl
  rw [hq1, hq2]
  have hD2 : (moebiusDenom γ z) ^ 2 ≠ 0 := pow_ne_zero 2 hdenγ
  have hE2 : (moebiusDenom W ((x.w ∘ P.g) z)) ^ 2 ≠ 0 := pow_ne_zero 2 hWd
  have hcD : starRingEnd ℂ (moebiusDenom γ z) ≠ 0 := by simpa using hdenγ
  have hcD2 : (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 ≠ 0 := pow_ne_zero 2 hcD
  rw [map_inv₀, map_pow] at hEq2
  by_cases hdzz : dz (x.w ∘ P.g) z = 0
  · have hA0 : dz (x.w ∘ P.g) (moebiusMap γ z) = 0 := by
      have h5 := hEq1
      rw [hdzz, mul_zero] at h5
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact h6
      · exact absurd h6 (inv_ne_zero hD2)
    rw [hA0, hdzz, div_zero, div_zero, zero_mul, zero_mul]
  · have hAne : dz (x.w ∘ P.g) (moebiusMap γ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hEq1
      rcases mul_eq_zero.mp hEq1.symm with h6 | h6
      · exact inv_ne_zero hE2 h6
      · exact hdzz h6
    have hAval : dz (x.w ∘ P.g) (moebiusMap γ z)
        = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dz (x.w ∘ P.g) z
          * (moebiusDenom γ z) ^ 2 := by
      have h7 := congrArg (fun t : ℂ => t * (moebiusDenom γ z) ^ 2) hEq1
      simpa [inv_mul_cancel_right₀ hD2] using h7
    have hBval : dzbar (x.w ∘ P.g) (moebiusMap γ z)
        = ((moebiusDenom W ((x.w ∘ P.g) z)) ^ 2)⁻¹ * dzbar (x.w ∘ P.g) z
          * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
      have h8 := congrArg (fun t : ℂ => t * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) hEq2
      simpa [inv_mul_cancel_right₀ hcD2] using h8
    rw [hAval, hBval]
    field_simp

/-- Composition closure on the upper half plane: the re-marked solution `x.w ∘ P.g` is an
upper-half-plane quasiconformal map. Its inverse is the inverse re-marking after the
global inverse of the solution, and its coefficient bound is `(a + b) / (1 + a * b)` for
the re-marking bound `a = max P.κ 0` and the solution bound `b = ‖x.b.μ‖_∞`. -/
theorem TeichRep.isQCUpper_remark (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    IsQCUpper (x.w ∘ P.g) (P.ginv ∘ Function.invFun x.w)
      ((max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)) := by
  sorry

/-- The **re-marked representative**: the representative whose coefficient is the
symmetric extension of the Beltrami datum of `x.w ∘ P.g` on the upper half plane. -/
noncomputable def TeichRep.smulUpper (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    TeichRep Γ₀ :=
  TeichRep.ofUpper Γ₀ (wirtingerQuotient (x.w ∘ P.g))
    (measurable_wirtingerQuotient_remark x P)
    (wirtingerQuotient_remark_bound x P)
    (wirtingerQuotient_remark_invariant x P)

/-- Factorization of the re-marked solution: on the upper half plane, the normalized
solution of the re-marked representative is a real Möbius map applied to `x.w ∘ P.g`, as
the two maps solve the same Beltrami equation there. -/
theorem TeichRep.smulUpper_w (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → (x.smulUpper P).w z = moebiusMap R (x.w (P.g z)) := by
  sorry

/-- Re-marking respects inseparability of representatives. -/
theorem smulUpper_mk_congr (P : ModGroupUpper Γ₀) :
    ∀ x y : TeichRep Γ₀, Inseparable x y →
      (Teich.mk (x.smulUpper P) : Teich Γ₀) = Teich.mk (y.smulUpper P) := by
  sorry

/-- Upper-half-plane re-markings act on Teichmüller space through coefficients. -/
noncomputable instance : SMul (ModGroupUpper Γ₀) (Teich Γ₀) :=
  ⟨fun P ξ => SeparationQuotient.lift
    (fun x : TeichRep Γ₀ => (Teich.mk (x.smulUpper P) : Teich Γ₀))
    (smulUpper_mk_congr P) ξ⟩

/-- The re-marking action computed on classes of representatives. -/
theorem Teich.smulUpper_mk (P : ModGroupUpper Γ₀) (x : TeichRep Γ₀) :
    P • Teich.mk x = Teich.mk (x.smulUpper P) := by
  rfl

end RiemannDynamics

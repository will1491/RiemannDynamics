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
  obtain ⟨⟨K, hK⟩, hsym, hcompat, hcompat'⟩ := mem_modGroup_iff.mp hF
  have hK1 : 1 ≤ K := hK.1
  have hκ : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < K + 1)]
    linarith
  have hqc : IsQCUpper (⇑F) (⇑F.symm) ((K - 1) / (K + 1)) :=
    isQCUpper_of_isQCGeometric hK hsym hup
      (fun z => F.symm_apply_apply z) (fun z => F.apply_symm_apply z)
  have hcompatU : ∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      F (moebiusMap γ z) = moebiusMap γ' (F z) := by
    intro γ hγ
    obtain ⟨γ', hγ', hae⟩ := hcompat γ hγ
    exact ⟨γ', hγ', fun z hz => modGroup_equivariant_offPole hF hae z
      (moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz))⟩
  have hcompatU' : ∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      F (moebiusMap γ z) = moebiusMap γ' (F z) := by
    intro γ' hγ'
    obtain ⟨γ, hγ, hae⟩ := hcompat' γ' hγ'
    exact ⟨γ, hγ, fun z hz => modGroup_equivariant_offPole hF hae z
      (moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz))⟩
  exact ⟨⟨⇑F, ⇑F.symm, (K - 1) / (K + 1), hκ, hqc, hcompatU, hcompatU'⟩, rfl⟩

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

set_option maxHeartbeats 400000 in
-- The Sobolev field runs a two-scale mollification limit through the change-of-variables
-- estimate; the single-declaration elaboration exceeds the default heartbeat budget.
/-- Composition closure on the upper half plane: the re-marked solution `x.w ∘ P.g` is an
upper-half-plane quasiconformal map. Its inverse is the inverse re-marking after the
global inverse of the solution, and its coefficient bound is `(a + b) / (1 + a * b)` for
the re-marking bound `a = max P.κ 0` and the solution bound `b = ‖x.b.μ‖_∞`. -/
theorem TeichRep.isQCUpper_remark (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    IsQCUpper (x.w ∘ P.g) (P.ginv ∘ Function.invFun x.w)
      ((max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)) := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hxc : Continuous x.w := x.w_isQCAnalytic.1.1.continuous
  have hxinj : Function.Injective x.w := x.w_injective
  have hxsurj : Function.Surjective x.w := x.w_isQCAnalytic.1.1.bijective.surjective
  -- the image of the upper half plane is the upper half plane
  have hximg : x.w '' {z : ℂ | 0 < z.im} = {z : ℂ | 0 < z.im} := by
    rcases x.w_halfPlane_dichotomy with ⟨-, himg⟩ | ⟨hneg, -⟩
    · exact himg
    · exfalso
      have h1 : 0 < (Complex.I).im := by simp
      have h2 := x.w_mapsTo_upper Complex.I h1
      have h3 := hneg Complex.I h1
      linarith
  -- the global inverse of the normalized solution preserves the upper half plane
  have hinvmem : ∀ z : ℂ, 0 < z.im → 0 < (Function.invFun x.w z).im := by
    intro z hz
    have hzimg : z ∈ x.w '' {z : ℂ | 0 < z.im} := by
      rw [hximg]
      exact hz
    obtain ⟨u, hu, huz⟩ := hzimg
    have hval : Function.invFun x.w z = u := by
      rw [← huz]
      exact Function.leftInverse_invFun hxinj u
    rw [hval]
    exact hu
  -- identification of the set-inverse with the homeomorphism inverse
  have hhomeo : IsHomeomorph x.w := x.w_isQCAnalytic.1.1
  have hinvW : Function.invFun x.w = ⇑(IsHomeomorph.homeomorph x.w hhomeo).symm := by
    funext z
    apply hxinj
    rw [Function.invFun_eq (hxsurj z)]
    have h1 := (IsHomeomorph.homeomorph x.w hhomeo).apply_symm_apply z
    rw [IsHomeomorph.homeomorph_apply] at h1
    rw [h1]
  -- ===== Wirtinger measurability of the re-marking map =====
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
  -- ===== preimages of null sets under `P.g` are null on the positive-Jacobian set =====
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
  -- ===== dilatation constants =====
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
  -- ===== the sharp composition estimate on squared norms =====
  have hsharp : ∀ a b s t q R : ℝ, 0 ≤ a → a < 1 → 0 ≤ b → b < 1 → 0 ≤ s → 0 ≤ t →
      0 ≤ q → t ≤ a * s → q ≤ b → |R| ≤ q * s * t →
      (t ^ 2 + q ^ 2 * s ^ 2 + 2 * R) * (1 + a * b) ^ 2
        ≤ (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * R) := by
    intro a b s t q R ha0' ha1' hb0' hb1' hs ht hq htas hqb hRb
    have hqst : R ≤ q * s * t := (abs_le.mp hRb).2
    have hab0 : 0 ≤ a * b := mul_nonneg ha0' hb0'
    have hlin : (t + q * s) * (1 + a * b) ≤ (a + b) * (s + q * t) := by
      have ha2 : 0 ≤ 1 - a ^ 2 := by
        have hid : 1 - a ^ 2 = (1 - a) * (1 + a) := by ring
        rw [hid]
        exact mul_nonneg (by linarith) (by linarith)
      have h1 : 0 ≤ (1 - a ^ 2) * ((b - q) * s) :=
        mul_nonneg ha2 (mul_nonneg (by linarith) hs)
      have h2 : 0 ≤ (1 + a * b - q * (a + b)) * (a * s - t) := by
        refine mul_nonneg ?_ (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right hqb (show (0:ℝ) ≤ a + b by linarith),
          mul_nonneg hb0' (sub_nonneg.mpr hb1'.le)]
      linarith [h1, h2]
    have hXnn : 0 ≤ (t + q * s) * (1 + a * b) :=
      mul_nonneg (add_nonneg ht (mul_nonneg hq hs)) (by linarith)
    have hsq : ((t + q * s) * (1 + a * b)) ^ 2 ≤ ((a + b) * (s + q * t)) ^ 2 :=
      pow_le_pow_left₀ hXnn hlin 2
    have hfac : 0 ≤ (q * s * t - R) * ((1 + a * b) ^ 2 - (a + b) ^ 2) := by
      refine mul_nonneg (by linarith) ?_
      have hyy : 0 ≤ ((1 + a) * (1 + b)) * ((1 - a) * (1 - b)) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith))
          (mul_nonneg (by linarith) (by linarith))
      have hid2 : (1 + a * b) ^ 2 - (a + b) ^ 2
          = ((1 + a) * (1 + b)) * ((1 - a) * (1 - b)) := by ring
      rw [hid2]
      exact hyy
    have h3 : (t ^ 2 + q ^ 2 * s ^ 2 + 2 * (q * s * t)) * (1 + a * b) ^ 2
        ≤ (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * (q * s * t)) := by
      calc (t ^ 2 + q ^ 2 * s ^ 2 + 2 * (q * s * t)) * (1 + a * b) ^ 2
          = ((t + q * s) * (1 + a * b)) ^ 2 := by ring
        _ ≤ ((a + b) * (s + q * t)) ^ 2 := hsq
        _ = (a + b) ^ 2 * (s ^ 2 + q ^ 2 * t ^ 2 + 2 * (q * s * t)) := by ring
    have h4 : 0 ≤ q * s * t * (1 + a * b) ^ 2 - R * (1 + a * b) ^ 2
        - q * s * t * (a + b) ^ 2 + R * (a + b) ^ 2 := by
      have hid3 : q * s * t * (1 + a * b) ^ 2 - R * (1 + a * b) ^ 2
          - q * s * t * (a + b) ^ 2 + R * (a + b) ^ 2
          = (q * s * t - R) * ((1 + a * b) ^ 2 - (a + b) ^ 2) := by ring
      rw [hid3]
      exact hfac
    linarith [h3, h4]
  -- ===== the almost-everywhere good set of the plane solution =====
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
  -- ===== the almost-everywhere Beltrami band of the composite =====
  have hband : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ‖dzbar (x.w ∘ P.g) z‖
          ≤ (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf)
            * ‖dz (x.w ∘ P.g) z‖
        ∧ 0 < ‖dz (x.w ∘ P.g) z‖ := by
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
      have hsq2 : (‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
          * (1 + max P.κ 0 * x.b.normInf)) ^ 2
          ≤ ((max P.κ 0 + x.b.normInf)
            * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) ^ 2 := by
        calc (‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖
            * (1 + max P.κ 0 * x.b.normInf)) ^ 2
            = ‖dzbar P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dz P.g z)‖ ^ 2
              * (1 + max P.κ 0 * x.b.normInf) ^ 2 := by ring
          _ ≤ (max P.κ 0 + x.b.normInf) ^ 2
              * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖ ^ 2 := hkey3
          _ = ((max P.κ 0 + x.b.normInf)
              * ‖dz P.g z + x.b.μ (P.g z) * starRingEnd ℂ (dzbar P.g z)‖) ^ 2 := by ring
      exact (pow_le_pow_iff_left₀
        (mul_nonneg (norm_nonneg _) h1pab.le)
        (mul_nonneg (by linarith) (norm_nonneg _)) (by norm_num)).mp hsq2
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
    refine ⟨?_, hFdzpos⟩
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mapsTo
    intro z hz
    exact x.w_mapsTo_upper _ (P.qc.mapsTo z hz)
  · -- mapsTo'
    intro z hz
    exact P.qc.mapsTo' _ (hinvmem z hz)
  · -- left_inv
    intro z hz
    have h1 : Function.invFun x.w (x.w (P.g z)) = P.g z :=
      Function.leftInverse_invFun hxinj (P.g z)
    calc (P.ginv ∘ Function.invFun x.w) ((x.w ∘ P.g) z)
        = P.ginv (Function.invFun x.w (x.w (P.g z))) := rfl
      _ = P.ginv (P.g z) := by rw [h1]
      _ = z := P.qc.left_inv z hz
  · -- right_inv
    intro z hz
    have hu : 0 < (Function.invFun x.w z).im := hinvmem z hz
    have h1 : P.g (P.ginv (Function.invFun x.w z)) = Function.invFun x.w z :=
      P.qc.right_inv _ hu
    calc (x.w ∘ P.g) ((P.ginv ∘ Function.invFun x.w) z)
        = x.w (P.g (P.ginv (Function.invFun x.w z))) := rfl
      _ = x.w (Function.invFun x.w z) := by rw [h1]
      _ = z := Function.invFun_eq (hxsurj z)
  · -- cont
    exact hxc.comp_continuousOn P.qc.cont
  · -- cont'
    refine P.qc.cont'.comp ?_ ?_
    · rw [hinvW]
      exact (IsHomeomorph.homeomorph x.w hhomeo).symm.continuous.continuousOn
    · intro z hz
      exact hinvmem z hz
  · -- sobolev
    have hle1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by norm_num
    have hne0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by norm_num
    haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
    haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
    haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
    have hxLI : LocallyIntegrable x.w volume := hxc.locallyIntegrable
    have hxdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ x.w w :=
      IsQCAnalytic.ae_differentiableAt x.w_isQCAnalytic
    -- ===== the pointwise linear-map representation in Wirtinger form =====
    have hrepr : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ),
        L w = (1 / 2 : ℂ) * ((L 1) - Complex.I * (L Complex.I)) * w
          + (1 / 2 : ℂ) * ((L 1) + Complex.I * (L Complex.I)) * (starRingEnd ℂ w) := by
      intro L w
      have hLw : L w = (↑w.re : ℂ) * L 1 + (↑w.im : ℂ) * L Complex.I := by
        conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
          rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
        rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      have hcw : starRingEnd ℂ w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im w]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
      rw [hLw, hcw]
      set a : ℂ := (↑w.re : ℂ) with ha
      set b : ℂ := (↑w.im : ℂ) with hb
      rw [hw]
      linear_combination (b * L Complex.I) * Complex.I_mul_I
    -- ===== a.e. good facts of `P.g` on the upper half plane =====
    have hggood : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det
          ∧ ‖dzbar P.g z‖ ≤ max P.κ 0 * ‖dz P.g z‖ := by
      filter_upwards [P.qc.jac, P.qc.belt] with z hjac hbelt
      have hgdiff : DifferentiableAt ℝ P.g z := by
        by_contra hnd
        rw [fderiv_zero_of_not_differentiableAt hnd] at hjac
        simp [ContinuousLinearMap.det] at hjac
      exact ⟨hgdiff, hjac,
        le_trans hbelt (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
    -- ===== pointwise distortion: `‖(Dg)v‖² ≤ C₀ · det(Dg)` for unit `v` =====
    have hdistort : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ∀ v : ℂ, ‖v‖ = 1 →
        ‖(fderiv ℝ P.g z) v‖ ^ 2
          ≤ (1 + max P.κ 0) / (1 - max P.κ 0) * (fderiv ℝ P.g z).det := by
      filter_upwards [hggood] with z hz v hv
      obtain ⟨hgdiff, hjac, hbelt⟩ := hz
      have happ : (fderiv ℝ P.g z) v = dz P.g z * v + dzbar P.g z * starRingEnd ℂ v := by
        have h1 := hrepr (fderiv ℝ P.g z) v
        rw [h1]
        simp only [dz, dzbar]
      have hnorm : ‖(fderiv ℝ P.g z) v‖ ≤ ‖dz P.g z‖ + ‖dzbar P.g z‖ := by
        rw [happ]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj, hv, mul_one, mul_one]
      rw [det_fderiv_eq_wirtinger]
      set a := max P.κ 0 with hadef
      set s := ‖dz P.g z‖ with hsdef
      set t := ‖dzbar P.g z‖ with htdef
      have hs0 : 0 ≤ s := norm_nonneg _
      have ht0 : 0 ≤ t := norm_nonneg _
      have hden : 0 < 1 - a := by linarith
      have hB : ‖(fderiv ℝ P.g z) v‖ ^ 2 ≤ (s + t) ^ 2 := by
        have := norm_nonneg ((fderiv ℝ P.g z) v)
        nlinarith [hnorm]
      refine le_trans hB ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hden]
      nlinarith [mul_nonneg (sub_nonneg.mpr hbelt) (add_nonneg hs0 ht0)]
    -- ===== the almost-everywhere chain rule for the composite =====
    have hchain : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        DifferentiableAt ℝ P.g z ∧ DifferentiableAt ℝ x.w (P.g z) ∧
          fderiv ℝ (x.w ∘ P.g) z = (fderiv ℝ x.w (P.g z)).comp (fderiv ℝ P.g z) := by
      have hN : volume {w : ℂ | ¬ DifferentiableAt ℝ x.w w} = 0 := ae_iff.mp hxdiff
      filter_upwards [hggood, hpull _ hN] with z hz htr
      obtain ⟨hgdiff, hjac, -⟩ := hz
      have hxd : DifferentiableAt ℝ x.w (P.g z) := by
        have h2 := htr ⟨hgdiff, hjac⟩
        simpa using h2
      exact ⟨hgdiff, hxd, fderiv_comp z hxd hgdiff⟩
    -- ===== the forward area estimate on subsets of the upper half plane =====
    have hArea : ∀ S : Set ℂ, MeasurableSet S → S ⊆ {z : ℂ | 0 < z.im} →
        ∀ B : Set ℂ, P.g '' S ⊆ B → ∀ h : ℂ → ℝ≥0∞,
        ∫⁻ z in S, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          ≤ ∫⁻ u in B, h u := by
      intro S hSmeas hSsub B hB h
      set Sg := S ∩ ({z : ℂ | DifferentiableAt ℝ P.g z}
        ∩ {z : ℂ | 0 < (fderiv ℝ P.g z).det}) with hSgdef
      have hSgmeas : MeasurableSet Sg :=
        hSmeas.inter ((measurableSet_of_differentiableAt ℝ P.g).inter
          (measurableSet_lt measurable_const hdetmeas))
      have hSgsub : Sg ⊆ S := Set.inter_subset_left
      have hnull : volume (S \ Sg) = 0 := by
        have h1 : (volume.restrict {z : ℂ | 0 < z.im})
            {z : ℂ | ¬ (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det)} = 0 :=
          ae_iff.mp (hggood.mono fun z hz => ⟨hz.1, hz.2.1⟩)
        rw [Measure.restrict_apply' hU] at h1
        refine measure_mono_null ?_ h1
        intro z hz
        obtain ⟨hzS, hzn⟩ := hz
        refine ⟨?_, hSsub hzS⟩
        intro hgood
        exact hzn ⟨hzS, hgood.1, hgood.2⟩
      have hSeq : Sg =ᵐ[volume] S := by
        refine ae_eq_set.mpr ⟨?_, hnull⟩
        rw [Set.diff_eq_empty.mpr hSgsub]
        exact measure_empty
      have hstep1 : ∫⁻ z in S, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          = ∫⁻ z in Sg, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z) := by
        rw [Measure.restrict_congr_set hSeq]
      have hfd : ∀ z ∈ Sg, HasFDerivWithinAt P.g (fderiv ℝ P.g z) Sg z := fun z hz =>
        (hz.2.1.hasFDerivAt).hasFDerivWithinAt
      have hinj : Set.InjOn P.g Sg := by
        intro p hp q hq hpq
        have h1 := P.qc.left_inv p (hSsub (hSgsub hp))
        have h2 := P.qc.left_inv q (hSsub (hSgsub hq))
        rw [← h1, ← h2, hpq]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSgmeas hfd hinj h
      have hstep2 : ∫⁻ z in Sg, ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          = ∫⁻ u in P.g '' Sg, h u := by
        rw [hcov]
        refine lintegral_congr_ae ?_
        refine (ae_restrict_iff' hSgmeas).mpr (Filter.Eventually.of_forall fun z hz => ?_)
        change ENNReal.ofReal ((fderiv ℝ P.g z).det) * h (P.g z)
          = ENNReal.ofReal |(fderiv ℝ P.g z).det| * h (P.g z)
        rw [abs_of_pos hz.2.2]
      have hstep3 : ∫⁻ u in P.g '' Sg, h u ≤ ∫⁻ u in B, h u := by
        refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
        exact subset_trans (Set.image_mono hSgsub) hB
      rw [hstep1, hstep2]
      exact hstep3
    -- ===== `L²` on compacts of the composite directional derivative =====
    have hgradL2 : ∀ v : ℂ, ‖v‖ = 1 →
        MemLpLocOn (fun z => (fderiv ℝ (x.w ∘ P.g) z) v) 2 {z : ℂ | 0 < z.im} := by
      intro v hv Kc hKcU hKcc
      haveI : IsFiniteMeasure (volume.restrict Kc) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKcc.measure_lt_top⟩
      refine ⟨((measurable_fderiv ℝ (x.w ∘ P.g)).apply_continuousLinearMap
        v).aestronglyMeasurable, ?_⟩
      obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, P.g '' Kc ⊆ Metric.ball 0 R1 := by
        obtain ⟨R1, hR1⟩ := (hKcc.image_of_continuousOn
          (P.qc.cont.mono hKcU)).isBounded.subset_ball (0 : ℂ)
        exact ⟨R1, hR1⟩
      have hptwise : ∀ᵐ z ∂(volume.restrict Kc),
          ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2
            ≤ ENNReal.ofReal ((fderiv ℝ P.g z).det)
              * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * ‖fderiv ℝ x.w (P.g z)‖ₑ ^ 2) := by
        have hres : volume.restrict Kc ≤ volume.restrict {z : ℂ | 0 < z.im} := by
          exact Measure.restrict_mono hKcU le_rfl
        have hC0 : (0:ℝ) ≤ (1 + max P.κ 0) / (1 - max P.κ 0) :=
          div_nonneg (by linarith) (by linarith)
        filter_upwards [(ae_mono hres) hchain, (ae_mono hres) hdistort,
          (ae_mono hres) hggood] with z hz hd hgg
        obtain ⟨hgdiff, hxd, hcomp⟩ := hz
        have hdet0 : (0:ℝ) ≤ (fderiv ℝ P.g z).det := hgg.2.1.le
        have h1 : ‖(fderiv ℝ (x.w ∘ P.g) z) v‖
            ≤ ‖fderiv ℝ x.w (P.g z)‖ * ‖(fderiv ℝ P.g z) v‖ := by
          rw [hcomp, ContinuousLinearMap.comp_apply]
          exact (fderiv ℝ x.w (P.g z)).le_opNorm _
        have h2 := hd v hv
        have h3 : ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ ^ 2
            ≤ (fderiv ℝ P.g z).det
              * ((1 + max P.κ 0) / (1 - max P.κ 0) * ‖fderiv ℝ x.w (P.g z)‖ ^ 2) := by
          have h4 : ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ ^ 2
              ≤ ‖fderiv ℝ x.w (P.g z)‖ ^ 2 * ‖(fderiv ℝ P.g z) v‖ ^ 2 := by
            have h5 := mul_self_le_mul_self (norm_nonneg _) h1
            have h6 : 0 ≤ ‖fderiv ℝ x.w (P.g z)‖ * ‖(fderiv ℝ P.g z) v‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            nlinarith
          have h7 : (0:ℝ) ≤ ‖fderiv ℝ x.w (P.g z)‖ ^ 2 := sq_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left h2 h7]
        calc ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2
            = ENNReal.ofReal (‖(fderiv ℝ (x.w ∘ P.g) z) v‖ ^ 2) := by
              rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          _ ≤ ENNReal.ofReal ((fderiv ℝ P.g z).det
                * ((1 + max P.κ 0) / (1 - max P.κ 0) * ‖fderiv ℝ x.w (P.g z)‖ ^ 2)) :=
              ENNReal.ofReal_le_ofReal h3
          _ = ENNReal.ofReal ((fderiv ℝ P.g z).det)
                * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * ‖fderiv ℝ x.w (P.g z)‖ₑ ^ 2) := by
              rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
                ENNReal.ofReal_mul hdet0, ENNReal.ofReal_mul hC0]
      have hmain : ∫⁻ z in Kc, ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2
          ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
            * ∫⁻ u in Metric.ball 0 R1, ‖fderiv ℝ x.w u‖ₑ ^ 2 := by
        refine le_trans (lintegral_mono_ae hptwise) ?_
        have h8 := hArea Kc hKcc.measurableSet hKcU (Metric.ball 0 R1) hR1
          (fun u => ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
            * ‖fderiv ℝ x.w u‖ₑ ^ 2)
        refine le_trans h8 ?_
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
      have hfin : ∫⁻ z in Kc, ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ 2 < ⊤ := by
        refine lt_of_le_of_lt hmain ?_
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_top_iff_ne_top.mpr (IsQCAnalytic.lintegralSq_fderiv_ball_ne_top
            x.w_isQCAnalytic R1))
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      have hconv : ∀ z : ℂ, ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ ((2:ℝ≥0∞).toReal)
          = ‖(fderiv ℝ (x.w ∘ P.g) z) v‖ₑ ^ (2:ℕ) := by
        intro z
        rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
        norm_num
      simpa only [hconv] using hfin
    -- ===== the weak-derivative identity for the composite =====
    have hKEY : ∀ (v : ℂ) (gv0 : ℂ → ℂ), (v = 1 ∨ v = Complex.I) →
        HasWeakDirDeriv v gv0 P.g {z : ℂ | 0 < z.im} →
        MemLpLocOn gv0 2 {z : ℂ | 0 < z.im} →
        HasWeakDirDeriv v (fun z => (fderiv ℝ (x.w ∘ P.g) z) v) (x.w ∘ P.g)
          {z : ℂ | 0 < z.im} := by
      intro v gv0 hv1I hwd hgvL2
      have hv1 : ‖v‖ = 1 := by
        rcases hv1I with rfl | rfl
        · simp
        · simp
      intro φ hφs hφc hφsupp
      have hKc : IsCompact (tsupport φ) := hφc
      have hKU : tsupport φ ⊆ {z : ℂ | 0 < z.im} := hφsupp
      obtain ⟨d, hd0, hdU⟩ := hKc.exists_cthickening_subset_open hUopen hKU
      set r : ℝ := d / 3 with hrdef
      have hr0 : 0 < r := by rw [hrdef]; positivity
      have hmono : ∀ {s t : ℝ}, s ≤ t →
          Metric.cthickening s (tsupport φ) ⊆ Metric.cthickening t (tsupport φ) :=
        fun hst => Metric.cthickening_mono hst _
      have hK1U : Metric.cthickening r (tsupport φ) ⊆ {z : ℂ | 0 < z.im} :=
        (hmono (by rw [hrdef]; linarith)).trans hdU
      have hK3meas : MeasurableSet (Metric.cthickening d (tsupport φ)) :=
        Metric.isClosed_cthickening.measurableSet
      have hK3c : IsCompact (Metric.cthickening d (tsupport φ)) := hKc.cthickening
      haveI hK3fin : IsFiniteMeasure (volume.restrict (Metric.cthickening d (tsupport φ))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hK3c.measure_lt_top⟩
      -- ===== the smooth cutoff, by mollifying an indicator =====
      set β : ContDiffBump (0:ℂ) :=
        { rIn := r / 2, rOut := r,
          rIn_pos := by positivity,
          rIn_lt_rOut := by linarith } with hβdef
      set ind : ℂ → ℝ :=
        (Metric.cthickening (2*r) (tsupport φ)).indicator (fun _ => (1:ℝ)) with hinddef
      have hindmeas : Measurable ind :=
        measurable_const.indicator Metric.isClosed_cthickening.measurableSet
      have hindLI : LocallyIntegrable ind volume := by
        refine Integrable.locallyIntegrable ?_
        rw [hinddef, integrable_indicator_iff Metric.isClosed_cthickening.measurableSet]
        refine integrableOn_const ?_ ?_
        · exact hKc.cthickening.measure_lt_top.ne
        · simp
      set χ : ℂ → ℝ :=
        MeasureTheory.convolution (β.normed volume) ind
          (ContinuousLinearMap.lsmul ℝ ℝ) volume with hχdef
      have hβsupp : Function.support (β.normed volume) ⊆ Metric.ball 0 r := by
        rw [β.support_normed_eq]
      have hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
        HasCompactSupport.contDiff_convolution_left _ β.hasCompactSupport_normed
          β.contDiff_normed hindLI
      have hcthstep : ∀ {δ : ℝ}, 0 ≤ δ → ∀ z w : ℂ, z ∈ Metric.cthickening δ (tsupport φ) →
          dist w z ≤ r → w ∈ Metric.cthickening (δ + r) (tsupport φ) := by
        intro δ hδ0 z w hz hd'
        rw [Metric.mem_cthickening_iff] at hz ⊢
        refine le_trans (Metric.infEDist_le_infEDist_add_edist (y := z)) ?_
        rw [edist_dist]
        calc Metric.infEDist z (tsupport φ) + ENNReal.ofReal (dist w z)
            ≤ ENNReal.ofReal δ + ENNReal.ofReal r :=
              add_le_add hz (ENNReal.ofReal_le_ofReal hd')
          _ = ENNReal.ofReal (δ + r) := (ENNReal.ofReal_add hδ0 hr0.le).symm
      -- ===== values of the cutoff =====
      have hχ1 : ∀ z ∈ Metric.cthickening r (tsupport φ), χ z = 1 := by
        intro z hz
        have h := dist_convolution_le (μ := volume) (z₀ := (1:ℝ)) (x₀ := z) (R := r)
          (le_refl (0:ℝ)) hβsupp β.nonneg_normed β.integral_normed
          hindmeas.aestronglyMeasurable
          (fun w hw => by
            have hw2 : w ∈ Metric.cthickening (r + r) (tsupport φ) :=
              hcthstep hr0.le z w hz (Metric.mem_ball.mp hw).le
            have hw2' : w ∈ Metric.cthickening (2*r) (tsupport φ) := by
              rw [show (2:ℝ)*r = r + r by ring]
              exact hw2
            rw [hinddef]
            rw [Set.indicator_of_mem hw2']
            simp)
        have h2 : dist (χ z) 1 = 0 := le_antisymm h dist_nonneg
        exact dist_eq_zero.mp h2
      have hχ0 : ∀ z : ℂ, z ∉ Metric.cthickening d (tsupport φ) → χ z = 0 := by
        intro z hz
        have h := dist_convolution_le (μ := volume) (z₀ := (0:ℝ)) (x₀ := z) (R := r)
          (le_refl (0:ℝ)) hβsupp β.nonneg_normed β.integral_normed
          hindmeas.aestronglyMeasurable
          (fun w hw => by
            have hwn : w ∉ Metric.cthickening (2*r) (tsupport φ) := by
              intro hwc
              have hz2 : z ∈ Metric.cthickening (2*r + r) (tsupport φ) := by
                refine hcthstep (by linarith) w z hwc ?_
                rw [dist_comm]
                exact (Metric.mem_ball.mp hw).le
              have h3 : (2*r + r : ℝ) = d := by rw [hrdef]; ring
              rw [h3] at hz2
              exact hz hz2
            rw [hinddef]
            rw [Set.indicator_of_notMem hwn]
            simp)
        have h2 : dist (χ z) 0 = 0 := le_antisymm h dist_nonneg
        simpa using dist_eq_zero.mp h2
      have hχ01 : ∀ z : ℂ, 0 ≤ χ z ∧ χ z ≤ 1 := by
        intro z
        have h := dist_convolution_le (μ := volume) (z₀ := ((1:ℝ)/2)) (x₀ := z) (R := r)
          (ε := (1:ℝ)/2) (by norm_num) hβsupp β.nonneg_normed β.integral_normed
          hindmeas.aestronglyMeasurable
          (fun w _ => by
            rw [hinddef]
            by_cases hw2 : w ∈ Metric.cthickening (2*r) (tsupport φ)
            · rw [Set.indicator_of_mem hw2]
              rw [Real.dist_eq]
              norm_num
            · rw [Set.indicator_of_notMem hw2]
              rw [Real.dist_eq]
              norm_num)
        rw [Real.dist_eq] at h
        have h2 := abs_le.mp h
        constructor <;> linarith [h2.1, h2.2]
      have htsχ : tsupport χ ⊆ Metric.cthickening d (tsupport φ) := by
        refine closure_minimal ?_ Metric.isClosed_cthickening
        intro z hz
        by_contra hzn
        exact hz (hχ0 z hzn)
      have hdχ0 : ∀ z ∈ Metric.thickening r (tsupport φ), fderiv ℝ χ z = 0 := by
        intro z hz
        have hev : χ =ᶠ[nhds z] fun _ => (1:ℝ) :=
          Filter.eventually_of_mem (Metric.isOpen_thickening.mem_nhds hz)
            (fun w hw => hχ1 w (Metric.thickening_subset_cthickening _ _ hw))
        rw [Filter.EventuallyEq.fderiv_eq hev]
        simp
      have hdχK3 : ∀ z : ℂ, z ∉ Metric.cthickening d (tsupport φ) → fderiv ℝ χ z = 0 := by
        intro z hz
        have hev : χ =ᶠ[nhds z] fun _ => (0:ℝ) :=
          Filter.eventually_of_mem
            (Metric.isClosed_cthickening.isOpen_compl.mem_nhds hz)
            (fun w hw => hχ0 w hw)
        rw [Filter.EventuallyEq.fderiv_eq hev]
        simp
      -- ===== the localized inner map and its weak derivative datum =====
      set gt : ℂ → ℂ := fun w => if 0 < w.im then P.g w else 0 with hgtdef
      have hgtU : ∀ w : ℂ, 0 < w.im → gt w = P.g w := fun w hw => if_pos hw
      have hgtcont : ContinuousOn gt {z : ℂ | 0 < z.im} :=
        P.qc.cont.congr fun w hw => if_pos hw
      set G : ℂ → ℂ := fun w => χ w • gt w with hGdef
      have hGeq : ∀ w ∈ Metric.cthickening r (tsupport φ), G w = P.g w := by
        intro w hw
        rw [hGdef]
        simp only
        rw [hχ1 w hw, hgtU w (hK1U hw)]
        exact one_smul ℝ _
      have hGzero : ∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → G w = 0 := by
        intro w hw
        rw [hGdef]
        simp only
        rw [hχ0 w hw]
        exact zero_smul ℝ _
      have hGcont : Continuous G := by
        rw [continuous_iff_continuousAt]
        intro w
        by_cases hw : 0 < w.im
        · exact (hχsmooth.continuous.continuousOn.smul hgtcont).continuousAt
            (hUopen.mem_nhds hw)
        · have hwn : w ∉ Metric.cthickening d (tsupport φ) := fun hc => hw (hdU hc)
          have hev : G =ᶠ[nhds w] fun _ => (0:ℂ) :=
            Filter.eventually_of_mem
              (Metric.isClosed_cthickening.isOpen_compl.mem_nhds hwn)
              (fun u hu => hGzero u hu)
          exact ContinuousAt.congr (continuousAt_const (y := (0:ℂ))) hev.symm
      have hGsupp : HasCompactSupport G :=
        HasCompactSupport.intro hKc.cthickening hGzero
      have hGLI : LocallyIntegrable G volume := hGcont.locallyIntegrable
      have hGunif : UniformContinuous G :=
        hGsupp.uniformContinuous_of_continuous hGcont
      -- ===== the localized weak-derivative datum =====
      set Gv : ℂ → ℂ := fun w => χ w • gv0 w + ((fderiv ℝ χ w) v) • gt w with hGvdef
      have hGvzero : ∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → Gv w = 0 := by
        intro w hw
        rw [hGvdef]
        simp only
        rw [hχ0 w hw, hdχK3 w hw]
        simp
      have hGvind : Gv = (Metric.cthickening d (tsupport φ)).indicator Gv := by
        funext w
        by_cases hw : w ∈ Metric.cthickening d (tsupport φ)
        · rw [Set.indicator_of_mem hw]
        · rw [Set.indicator_of_notMem hw, hGvzero w hw]
      have hgv0K3 : MemLp gv0 2 (volume.restrict (Metric.cthickening d (tsupport φ))) :=
        hgvL2 _ hdU hK3c
      have hgtK3 : AEStronglyMeasurable gt
          (volume.restrict (Metric.cthickening d (tsupport φ))) :=
        ((hgtcont.mono hdU).aemeasurable hK3meas).aestronglyMeasurable
      have hχcont : Continuous χ := hχsmooth.continuous
      have hdχvcont : Continuous fun w => (fderiv ℝ χ w) v := by
        have h1 : Continuous fun w => fderiv ℝ χ w :=
          hχsmooth.continuous_fderiv hne0
        exact h1.clm_apply continuous_const
      have hpc1 : MemLp (fun w => χ w • gv0 w) 2
          (volume.restrict (Metric.cthickening d (tsupport φ))) := by
        refine MemLp.of_le hgv0K3 (hχcont.aestronglyMeasurable.smul
          hgv0K3.aestronglyMeasurable) ?_
        refine Filter.Eventually.of_forall fun w => ?_
        rw [norm_smul]
        have h2 : ‖χ w‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [(hχ01 w).1], (hχ01 w).2⟩
        exact mul_le_of_le_one_left (norm_nonneg _) h2
      obtain ⟨M1, hM1⟩ := hK3c.exists_bound_of_continuousOn (hgtcont.mono hdU)
      obtain ⟨M2, hM2⟩ := hK3c.exists_bound_of_continuousOn hdχvcont.continuousOn
      have hpc2 : MemLp (fun w => ((fderiv ℝ χ w) v) • gt w) 2
          (volume.restrict (Metric.cthickening d (tsupport φ))) := by
        refine MemLp.of_bound (hdχvcont.aestronglyMeasurable.smul hgtK3)
          (max M2 0 * max M1 0) ?_
        refine (ae_restrict_iff' hK3meas).mpr (Filter.Eventually.of_forall fun w hw => ?_)
        rw [norm_smul]
        refine mul_le_mul (le_trans (hM2 w hw) (le_max_left _ _))
          (le_trans (hM1 w hw) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
      have hGvK3L2 : MemLp Gv 2
          (volume.restrict (Metric.cthickening d (tsupport φ))) := by
        have h3 := hpc1.add hpc2
        exact h3
      have hGvsm : AEStronglyMeasurable Gv volume := by
        rw [hGvind]
        exact (aestronglyMeasurable_indicator_iff hK3meas).mpr hGvK3L2.aestronglyMeasurable
      have hGvL2 : MemLp Gv 2 volume := by
        refine ⟨hGvsm, ?_⟩
        have h4 : eLpNorm Gv 2 volume
            = eLpNorm Gv 2 (volume.restrict (Metric.cthickening d (tsupport φ))) := by
          conv_lhs => rw [hGvind]
          exact eLpNorm_indicator_eq_eLpNorm_restrict hK3meas
        rw [h4]
        exact hGvK3L2.2
      have hGvInt : Integrable Gv volume := by
        rw [hGvind, integrable_indicator_iff hK3meas]
        exact (hGvK3L2.mono_exponent one_le_two).integrable le_rfl
      have hGvLI : LocallyIntegrable Gv volume := hGvInt.locallyIntegrable
      have hχd : Differentiable ℝ χ := hχsmooth.differentiable hne0
      -- ===== integrability of the cutoff pairings =====
      have hIntgt : ∀ c : ℂ → ℝ, Continuous c →
          (∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → c w = 0) →
          Integrable (fun w => c w • gt w) volume := by
        intro c hc hczero
        have hind : (fun w => c w • gt w)
            = (Metric.cthickening d (tsupport φ)).indicator (fun w => c w • gt w) := by
          funext w
          by_cases hw : w ∈ Metric.cthickening d (tsupport φ)
          · rw [Set.indicator_of_mem hw]
          · rw [Set.indicator_of_notMem hw, hczero w hw]
            exact zero_smul ℝ _
        rw [hind, integrable_indicator_iff hK3meas]
        obtain ⟨Mc, hMc⟩ := hK3c.exists_bound_of_continuousOn hc.continuousOn
        have hmb : MemLp (fun w => c w • gt w) 1
            (volume.restrict (Metric.cthickening d (tsupport φ))) := by
          refine MemLp.of_bound (hc.aestronglyMeasurable.smul hgtK3)
            (max Mc 0 * max M1 0) ?_
          refine (ae_restrict_iff' hK3meas).mpr (Filter.Eventually.of_forall fun w hw => ?_)
          rw [norm_smul]
          refine mul_le_mul (le_trans (hMc w hw) (le_max_left _ _))
            (le_trans (hM1 w hw) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
        exact hmb.integrable le_rfl
      have hIntgv : ∀ c : ℂ → ℝ, Continuous c →
          (∀ w : ℂ, w ∉ Metric.cthickening d (tsupport φ) → c w = 0) →
          Integrable (fun w => c w • gv0 w) volume := by
        intro c hc hczero
        have hind : (fun w => c w • gv0 w)
            = (Metric.cthickening d (tsupport φ)).indicator (fun w => c w • gv0 w) := by
          funext w
          by_cases hw : w ∈ Metric.cthickening d (tsupport φ)
          · rw [Set.indicator_of_mem hw]
          · rw [Set.indicator_of_notMem hw, hczero w hw]
            exact zero_smul ℝ _
        rw [hind, integrable_indicator_iff hK3meas]
        obtain ⟨Mc, hMc⟩ := hK3c.exists_bound_of_continuousOn hc.continuousOn
        have hmb : MemLp (fun w => c w • gv0 w) 2
            (volume.restrict (Metric.cthickening d (tsupport φ))) := by
          refine MemLp.of_le (hgv0K3.const_smul (max Mc 0))
            (hc.aestronglyMeasurable.smul hgv0K3.aestronglyMeasurable) ?_
          refine (ae_restrict_iff' hK3meas).mpr (Filter.Eventually.of_forall fun w hw => ?_)
          rw [norm_smul, Pi.smul_apply, norm_smul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have h10 : ‖max Mc 0‖ = max Mc 0 := Real.norm_of_nonneg (le_max_right _ _)
          rw [h10]
          exact le_trans (hMc w hw) (le_max_left _ _)
        exact (hmb.mono_exponent one_le_two).integrable le_rfl
      -- ===== the weak directional derivative of the localization on the plane =====
      have hGweak : HasWeakDirDeriv v Gv G Set.univ := by
        intro ψ hψs hψc hψsub
        have hψd : Differentiable ℝ ψ := hψs.differentiable hne0
        have hψχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ψ w * χ w) := hψs.mul hχsmooth
        have hψχc : HasCompactSupport (fun w => ψ w * χ w) := hψc.mul_right
        have hψχts : tsupport (fun w => ψ w * χ w)
            ⊆ Metric.cthickening d (tsupport φ) := by
          refine subset_trans (closure_mono ?_) htsχ
          intro w hw
          rw [Function.mem_support] at hw ⊢
          intro h0
          exact hw (by rw [h0, mul_zero])
        have hψχU : tsupport (fun w => ψ w * χ w) ⊆ {z : ℂ | 0 < z.im} :=
          hψχts.trans hdU
        have hIBP := hwd (fun w => ψ w * χ w) hψχs hψχc hψχU
        have hprod : ∀ z : ℂ, (fderiv ℝ (fun w => ψ w * χ w) z) v
            = ψ z * ((fderiv ℝ χ z) v) + χ z * ((fderiv ℝ ψ z) v) := by
          intro z
          have h13 : HasFDerivAt (fun w => ψ w * χ w)
              (ψ z • fderiv ℝ χ z + χ z • fderiv ℝ ψ z) z :=
            (hψd z).hasFDerivAt.mul (hχd z).hasFDerivAt
          rw [h13.fderiv]
          simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        have hdψχ0 : ∀ z : ℂ, z ∉ Metric.cthickening d (tsupport φ) →
            (fderiv ℝ (fun w => ψ w * χ w) z) v = 0 := by
          intro z hz
          have h5 : z ∉ tsupport (fun w => ψ w * χ w) := fun hc => hz (hψχts hc)
          have h6 : fderiv ℝ (fun w => ψ w * χ w) z = 0 := by
            by_contra h8
            exact h5 (support_fderiv_subset ℝ (Function.mem_support.mpr h8))
          rw [h6]
          rfl
        have hLrw : ∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • P.g z
            = ∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          change ((fderiv ℝ (fun w => ψ w * χ w) z) v) • P.g z
            = ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z
          by_cases hz : 0 < z.im
          · rw [hgtU z hz]
          · have hz3 : z ∉ Metric.cthickening d (tsupport φ) := fun hc => hz (hdU hc)
            rw [hdψχ0 z hz3]
            simp
        have hsplit : ∀ z : ℂ, ((fderiv ℝ ψ z) v) • G z
            = ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z
              - (ψ z * ((fderiv ℝ χ z) v)) • gt z := by
          intro z
          rw [hGdef]
          simp only
          rw [hprod z]
          simp only [Complex.real_smul]
          push_cast
          ring
        have hdψχcont : Continuous fun z => (fderiv ℝ (fun w => ψ w * χ w) z) v :=
          (hψχs.continuous_fderiv hne0).clm_apply continuous_const
        have hI1 : Integrable
            (fun z => ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z) volume :=
          hIntgt _ hdψχcont hdψχ0
        have hI2 : Integrable (fun z => (ψ z * ((fderiv ℝ χ z) v)) • gt z) volume :=
          hIntgt _ (hψs.continuous.mul hdχvcont)
            (fun w hw => by rw [hdχK3 w hw]; simp)
        have hI3 : Integrable (fun z => (ψ z * χ z) • gv0 z) volume :=
          hIntgv _ (hψs.continuous.mul hχcont)
            (fun w hw => by rw [hχ0 w hw]; simp)
        calc ∫ z, ((fderiv ℝ ψ z) v) • G z
            = ∫ z, (((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z
                - (ψ z * ((fderiv ℝ χ z) v)) • gt z) :=
              integral_congr_ae (Filter.Eventually.of_forall fun z => hsplit z)
          _ = (∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • gt z)
                - ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z := integral_sub hI1 hI2
          _ = (∫ z, ((fderiv ℝ (fun w => ψ w * χ w) z) v) • P.g z)
                - ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z := by rw [hLrw]
          _ = (- ∫ z, ((fun w => ψ w * χ w) z) • gv0 z)
                - ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z := by rw [hIBP]
          _ = - ((∫ z, (ψ z * χ z) • gv0 z)
                + ∫ z, (ψ z * ((fderiv ℝ χ z) v)) • gt z) := by ring
          _ = - ∫ z, ((ψ z * χ z) • gv0 z + (ψ z * ((fderiv ℝ χ z) v)) • gt z) := by
              rw [integral_add hI3 hI2]
          _ = - ∫ z, ψ z • Gv z := by
              refine congrArg Neg.neg
                (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
              rw [hGvdef]
              simp only [Complex.real_smul]
              push_cast
              ring
      -- ===== almost-everywhere differentiability of the localization =====
      have haxis : ∀ᵐ z : ℂ, z.im ≠ 0 := by
        rw [ae_iff]
        have hset : {a : ℂ | ¬a.im ≠ 0} = {z : ℂ | z.im = 0} := by
          ext a
          simp
        rw [hset]
        exact volume_imZero
      have hgae2 : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
          (DifferentiableAt ℝ P.g z ∧ 0 < (fderiv ℝ P.g z).det) :=
        (ae_restrict_iff' hU).mp (hggood.mono fun z hz => ⟨hz.1, hz.2.1⟩)
      have hGdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ G z := by
        filter_upwards [haxis, hgae2] with z hz1 hz2
        rcases lt_or_gt_of_ne hz1 with hneg | hpos
        · have hzn : z ∉ Metric.cthickening d (tsupport φ) := by
            intro hc
            have h11 : (0:ℝ) < z.im := hdU hc
            linarith
          have hev : G =ᶠ[nhds z] fun _ => (0:ℂ) :=
            Filter.eventually_of_mem
              (Metric.isClosed_cthickening.isOpen_compl.mem_nhds hzn)
              (fun u hu => hGzero u hu)
          exact (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq hev
        · obtain ⟨hgd, hdet⟩ := hz2 hpos
          have hev : G =ᶠ[nhds z] fun w => χ w • P.g w :=
            Filter.eventually_of_mem (hUopen.mem_nhds hpos)
              (fun w hw => by
                rw [hGdef]
                simp only
                rw [hgtU w hw])
          exact ((hχd z).smul hgd).congr_of_eventuallyEq hev
      have hGveq : ∀ᵐ z : ℂ, (fderiv ℝ G z) v = Gv z :=
        fderiv_ae_eq_weakDirDeriv hGweak (locallyIntegrableOn_univ.mpr hGvLI)
          hGdiff hv1I hGLI
      have hGveqPg : ∀ᵐ z : ℂ, z ∈ Metric.thickening r (tsupport φ) →
          Gv z = (fderiv ℝ P.g z) v := by
        filter_upwards [hGveq] with z hz hmem
        have hev : G =ᶠ[nhds z] P.g :=
          Filter.eventually_of_mem (Metric.isOpen_thickening.mem_nhds hmem)
            (fun w hw => hGeq w (Metric.thickening_subset_cthickening _ _ hw))
        rw [← hz, Filter.EventuallyEq.fderiv_eq hev]
      -- ===== the mollifier sequence =====
      set Θ : ℕ → ContDiffBump (0:ℂ) := fun n =>
        { rIn := 1/(n+2), rOut := 2/(n+2),
          rIn_pos := by positivity,
          rIn_lt_rOut := by
            have h1 : (0:ℝ) < 1/((n:ℝ)+2) := by positivity
            have h2 : (2:ℝ)/((n:ℝ)+2) = 1/((n:ℝ)+2) + 1/((n:ℝ)+2) := by ring
            linarith } with hΘdef
      have hΘrout : Filter.Tendsto (fun n : ℕ => (Θ n).rOut) Filter.atTop (nhds 0) := by
        have h1 := (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp
          (Filter.tendsto_add_atTop_nat 2)
        have h2 : ((fun n : ℕ => (2:ℝ)/(n:ℝ)) ∘ fun n : ℕ => n + 2)
            = fun n : ℕ => (Θ n).rOut := by
          funext n
          simp only [Function.comp, hΘdef]
          push_cast
          ring
        rwa [h2] at h1
      have hΘsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, (Θ n).rOut < ε :=
        fun ε hε => hΘrout.eventually_lt_const hε
      have hΘsupp : ∀ n, Function.support ((Θ n).normed volume)
          ⊆ Metric.ball 0 ((Θ n).rOut) := by
        intro n
        rw [(Θ n).support_normed_eq]
      -- ===== the two mollifications =====
      set A : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((Θ n).normed volume) x.w
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hAdef
      have hAsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A n) := fun n =>
        HasCompactSupport.contDiff_convolution_left _ (Θ n).hasCompactSupport_normed
          (Θ n).contDiff_normed hxLI
      set gm : ℕ → ℂ → ℂ := fun m => MeasureTheory.convolution ((Θ m).normed volume) G
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgmdef
      have hgmsm : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gm m) := fun m =>
        HasCompactSupport.contDiff_convolution_left _ (Θ m).hasCompactSupport_normed
          (Θ m).contDiff_normed hGLI
      set CV : ℕ → ℂ → ℂ := fun m => MeasureTheory.convolution ((Θ m).normed volume) Gv
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCVdef
      have hgmderiv : ∀ (m : ℕ) (z : ℂ), (fderiv ℝ (gm m) z) v = CV m z := fun m z =>
        fderiv_convolution_normed_apply_eq hGweak hGLI hGvLI (Θ m).contDiff_normed
          (Θ m).hasCompactSupport_normed z
      have hCVcont : ∀ m : ℕ, Continuous (CV m) := fun m =>
        HasCompactSupport.continuous_convolution_left _
          (Θ m).hasCompactSupport_normed ((Θ m).contDiff_normed (n := 0)).continuous
          hGvLI
      have hCVconv : Filter.Tendsto (fun m => eLpNorm (CV m - Gv) 2 volume)
          Filter.atTop (nhds 0) :=
        eLpNorm_convolution_normed_sub_tendsto_zero hGvL2 Θ hΘrout
      -- ===== uniform convergence of the inner mollification =====
      have hgmconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in Filter.atTop, ∀ w : ℂ,
          dist (gm m w) (G w) ≤ ε := by
        intro ε hε
        obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hGunif ε hε
        filter_upwards [hΘsmall δ hδ0] with m hm w
        refine dist_convolution_le hε.le (hΘsupp m) (Θ m).nonneg_normed
          (Θ m).integral_normed hGcont.aestronglyMeasurable ?_
        intro u hu
        exact (hδ (lt_of_lt_of_le (Metric.mem_ball.mp hu) hm.le)).le
      -- ===== the image compact, its ball, and uniform outer convergence =====
      set Kg : Set ℂ := P.g '' tsupport φ with hKgdef
      have hKgc : IsCompact Kg := hKc.image_of_continuousOn (P.qc.cont.mono hKU)
      obtain ⟨R0, hR0⟩ := hKgc.isBounded.subset_ball (0:ℂ)
      set Kg1 : Set ℂ := Metric.cthickening 1 Kg with hKg1def
      have hKg1c : IsCompact Kg1 := hKgc.cthickening
      have hKgsub : Kg ⊆ Kg1 := Metric.self_subset_cthickening _
      have hnearKg1 : ∀ u ∈ Kg, ∀ w : ℂ, dist w u ≤ 1 → w ∈ Kg1 := by
        intro u hu w hw
        rw [hKg1def, Metric.mem_cthickening_iff]
        refine le_trans (Metric.infEDist_le_infEDist_add_edist (y := u)) ?_
        rw [Metric.infEDist_zero_of_mem hu, zero_add, edist_dist]
        exact ENNReal.ofReal_le_ofReal hw
      have hAconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ u ∈ Kg,
          dist (A n u) (x.w u) ≤ ε := by
        intro ε hε
        have huc := hKg1c.uniformContinuousOn_of_continuous hxc.continuousOn
        obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
        filter_upwards [hΘsmall (min δ 1) (lt_min hδ0 one_pos)] with n hn u hu
        refine dist_convolution_le hε.le (hΘsupp n) (Θ n).nonneg_normed
          (Θ n).integral_normed hxc.aestronglyMeasurable ?_
        intro w hw
        have hd1 : dist w u < min δ 1 := lt_of_lt_of_le (Metric.mem_ball.mp hw) hn.le
        have hwKg1 : w ∈ Kg1 :=
          hnearKg1 u hu w (le_trans hd1.le (min_le_right _ _))
        exact (hδ w hwKg1 u (hKgsub hu) (lt_of_lt_of_le hd1 (min_le_left _ _))).le
      -- ===== the mollified-differential energy decay on the image ball =====
      have henergy := mollified_fderiv_ball_energy_tendsto_zero x.w_isQCAnalytic R0 Θ hΘrout
      -- ===== support and bound bookkeeping for the test function =====
      have hKmeas : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
      have hKvol : volume (tsupport φ) < ⊤ := hKc.measure_lt_top
      have hφzero : ∀ z : ℂ, z ∉ tsupport φ → φ z = 0 :=
        fun z hz => image_eq_zero_of_notMem_tsupport hz
      have hdφcont : Continuous fun z : ℂ => (fderiv ℝ φ z) v :=
        (hφs.continuous_fderiv hne0).clm_apply continuous_const
      have hdφzero : ∀ z : ℂ, z ∉ tsupport φ → (fderiv ℝ φ z) v = 0 := by
        intro z hz
        have h6 : fderiv ℝ φ z = 0 := by
          by_contra h8
          exact hz (support_fderiv_subset ℝ (Function.mem_support.mpr h8))
        rw [h6]
        rfl
      obtain ⟨Mφ0, hMφ0⟩ := hKc.exists_bound_of_continuousOn hφs.continuous.continuousOn
      have hMφ : ∀ z : ℂ, ‖φ z‖ ≤ max Mφ0 0 := by
        intro z
        by_cases hz : z ∈ tsupport φ
        · exact le_trans (hMφ0 z hz) (le_max_left _ _)
        · rw [hφzero z hz, norm_zero]
          exact le_max_right _ _
      obtain ⟨Md0, hMd0⟩ := hKc.exists_bound_of_continuousOn hdφcont.continuousOn
      have hMdφ : ∀ z : ℂ, ‖(fderiv ℝ φ z) v‖ ≤ max Md0 0 := by
        intro z
        by_cases hz : z ∈ tsupport φ
        · exact le_trans (hMd0 z hz) (le_max_left _ _)
        · rw [hdφzero z hz, norm_zero]
          exact le_max_right _ _
      -- ===== integrability engines =====
      have hIntCont : ∀ (c : ℂ → ℝ) (H : ℂ → ℂ), Continuous c →
          (∀ z : ℂ, z ∉ tsupport φ → c z = 0) → Continuous H →
          Integrable (fun z => c z • H z) volume := by
        intro c H hc hc0 hH
        refine (hc.smul hH).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.intro hKc fun z hz => ?_
        rw [hc0 z hz]
        exact zero_smul ℝ _
      have hIntCLM : ∀ (T : ℂ → (ℂ →L[ℝ] ℂ)), Continuous T → ∀ (MT : ℝ),
          (∀ z ∈ tsupport φ, ‖T z‖ ≤ MT) → ∀ (Y : ℂ → ℂ), AEStronglyMeasurable Y volume →
          Integrable Y volume → Integrable (fun z => φ z • ((T z) (Y z))) volume := by
        intro T hT MT hMT Y hYm hYi
        have hsm : AEStronglyMeasurable (fun z => φ z • ((T z) (Y z))) volume := by
          refine (hφs.continuous.aestronglyMeasurable).smul ?_
          have h1 : Continuous fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2 :=
            isBoundedBilinearMap_apply.continuous
          exact h1.comp_aestronglyMeasurable ((hT.aestronglyMeasurable).prodMk hYm)
        refine Integrable.mono' (hYi.norm.const_mul (max Mφ0 0 * max MT 0)) hsm ?_
        refine Filter.Eventually.of_forall fun z => ?_
        rw [norm_smul]
        by_cases hz : z ∈ tsupport φ
        · have h2 : ‖(T z) (Y z)‖ ≤ max MT 0 * ‖Y z‖ :=
            le_trans ((T z).le_opNorm _) (mul_le_mul_of_nonneg_right
              (le_trans (hMT z hz) (le_max_left _ _)) (norm_nonneg _))
          calc ‖φ z‖ * ‖(T z) (Y z)‖
              ≤ (max Mφ0 0) * (max MT 0 * ‖Y z‖) :=
                mul_le_mul (hMφ z) h2 (norm_nonneg _) (le_max_right _ _)
            _ = max Mφ0 0 * max MT 0 * ‖Y z‖ := by ring
        · rw [hφzero z hz, norm_zero, zero_mul]
          positivity
      -- ===== lintegral support restriction =====
      have hlsupp : ∀ X : ℂ → ℂ, (∀ z : ℂ, z ∉ tsupport φ → X z = 0) →
          ∫⁻ z, ‖X z‖ₑ = ∫⁻ z in tsupport φ, ‖X z‖ₑ := by
        intro X hX0
        rw [← lintegral_indicator hKmeas]
        congr 1
        funext z
        by_cases hz : z ∈ tsupport φ
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, hX0 z hz]
          simp
      -- ===== the `ε`-threshold engine in `ℝ≥0∞` =====
      have hthreshold : ∀ (D : ℝ≥0∞), D ≠ ⊤ → ∀ ε : ℝ≥0∞, 0 < ε →
          ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal ε' * D ≤ ε := by
        intro D hD ε hε
        by_cases hεtop : ε = ⊤
        · exact ⟨1, one_pos, by rw [hεtop]; exact le_top⟩
        · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
          have hDr : 0 ≤ D.toReal := ENNReal.toReal_nonneg
          refine ⟨ε.toReal / (D.toReal + 1), by positivity, ?_⟩
          have hDle : D ≤ ENNReal.ofReal D.toReal := le_of_eq (ENNReal.ofReal_toReal hD).symm
          calc ENNReal.ofReal (ε.toReal / (D.toReal + 1)) * D
              ≤ ENNReal.ofReal (ε.toReal / (D.toReal + 1))
                * ENNReal.ofReal D.toReal := mul_le_mul_right hDle _
            _ = ENNReal.ofReal (ε.toReal / (D.toReal + 1) * D.toReal) := by
                rw [ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal ε.toReal := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                nlinarith
            _ = ε := ENNReal.ofReal_toReal hεtop
      -- ===== the sup-convergence L¹ engine =====
      have hsupL1 : ∀ (c : ℂ → ℝ) (Mc : ℝ), (∀ z : ℂ, ‖c z‖ ≤ Mc) →
          (∀ z : ℂ, z ∉ tsupport φ → c z = 0) →
          ∀ (H : ℕ → ℂ → ℂ) (Hl : ℂ → ℂ),
          (∀ ε : ℝ, 0 < ε → ∀ᶠ m in Filter.atTop, ∀ z ∈ tsupport φ, ‖H m z - Hl z‖ ≤ ε) →
          Filter.Tendsto (fun m => ∫⁻ z, ‖c z • H m z - c z • Hl z‖ₑ)
            Filter.atTop (nhds 0) := by
        intro c Mc hMc hc0 H Hl hconv
        rw [ENNReal.tendsto_atTop_zero]
        intro ε hε
        obtain ⟨ε', hε'0, hε'⟩ := hthreshold
          (ENNReal.ofReal (Mc + 1) * volume (tsupport φ))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKvol.ne) ε hε
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconv ε' hε'0)
        refine ⟨N, fun m hm => ?_⟩
        have hbd : ∫⁻ z, ‖c z • H m z - c z • Hl z‖ₑ
            ≤ ENNReal.ofReal ((Mc + 1) * ε') * volume (tsupport φ) := by
          have heq0 : ∀ z : ℂ, c z • H m z - c z • Hl z = c z • (H m z - Hl z) :=
            fun z => (smul_sub _ _ _).symm
          have hsupp0 : ∀ z : ℂ, z ∉ tsupport φ → c z • H m z - c z • Hl z = 0 := by
            intro z hz
            rw [heq0 z, hc0 z hz]
            exact zero_smul ℝ _
          rw [hlsupp _ hsupp0]
          have hptb : ∀ z ∈ tsupport φ, ‖c z • H m z - c z • Hl z‖ₑ
              ≤ ENNReal.ofReal ((Mc + 1) * ε') := by
            intro z hz
            rw [heq0 z, ← ofReal_norm_eq_enorm]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_smul]
            have hMc0 : 0 ≤ Mc := le_trans (norm_nonneg _) (hMc 0)
            refine mul_le_mul (le_trans (hMc z) (by linarith)) (hN m hm z hz)
              (norm_nonneg _) (by linarith)
          calc ∫⁻ z in tsupport φ, ‖c z • H m z - c z • Hl z‖ₑ
              ≤ ∫⁻ _ in tsupport φ, ENNReal.ofReal ((Mc + 1) * ε') := by
                refine lintegral_mono_ae ?_
                exact (ae_restrict_iff' hKmeas).mpr (Filter.Eventually.of_forall hptb)
            _ = ENNReal.ofReal ((Mc + 1) * ε') * volume (tsupport φ) := by
                rw [setLIntegral_const]
        refine le_trans hbd ?_
        have heq1 : ENNReal.ofReal ((Mc + 1) * ε')
            = ENNReal.ofReal ε' * ENNReal.ofReal (Mc + 1) := by
          rw [← ENNReal.ofReal_mul (by
            have hMc0 : 0 ≤ Mc := le_trans (norm_nonneg _) (hMc 0)
            linarith)]
          ring_nf
        rw [heq1, mul_assoc]
        exact hε'
      -- ===== an `L²`-to-`L¹` restriction bound on the support =====
      have hL2K : ∀ Y : ℂ → ℂ, AEStronglyMeasurable Y volume →
          ∫⁻ z in tsupport φ, ‖Y z‖ₑ
            ≤ eLpNorm Y 2 volume * (volume (tsupport φ)) ^ ((1:ℝ)/2) := by
        intro Y hY
        have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq
          (volume.restrict (tsupport φ)) (by constructor <;> norm_num :
            (2:ℝ).HolderConjugate 2)
          (f := fun z => ‖Y z‖ₑ) (g := fun _ => 1)
          (hY.enorm.restrict) aemeasurable_const
        simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow] at hcs
        refine le_trans hcs ?_
        have h2 : (∫⁻ z in tsupport φ, ‖Y z‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)
            ≤ eLpNorm Y 2 volume := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
          simp only [ENNReal.toReal_ofNat]
          rw [one_div]
          exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by norm_num)
        have h3 : (∫⁻ (_ : ℂ) in tsupport φ, (1:ℝ≥0∞)) ^ ((1:ℝ)/2)
            = (volume (tsupport φ)) ^ ((1:ℝ)/2) := by
          rw [setLIntegral_one]
        rw [h3]
        exact mul_le_mul_left h2 _
      -- ===== the per-`n` mollified identity =====
      have hGKg : ∀ z ∈ tsupport φ, G z ∈ Kg := by
        intro z hz
        rw [hGeq z (Metric.self_subset_cthickening _ hz)]
        exact ⟨z, hz, rfl⟩
      have hGvfin : ∫⁻ z in tsupport φ, ‖Gv z‖ₑ < ⊤ :=
        lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hGvInt.2
      set QD : ℕ → ℂ → ℝ≥0∞ :=
        fun n u => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ with hQDdef
      set CB : ℝ≥0∞ := (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
        * volume (tsupport φ)) ^ ((1:ℝ)/2) with hCBdef
      have hEn : ∀ n : ℕ, ∫ z, ((fderiv ℝ φ z) v) • (A n (G z))
          = - ∫ z, φ z • ((fderiv ℝ (A n) (G z)) (Gv z)) := by
        intro n
        have hDncont : Continuous fun u : ℂ => fderiv ℝ (A n) u :=
          (hAsm n).continuous_fderiv hne0
        obtain ⟨MD0, hMD0⟩ := hKg1c.exists_bound_of_continuousOn hDncont.continuousOn
        -- (I) per-`m` smooth integration by parts
        have hIBPm : ∀ m : ℕ, ∫ z, ((fderiv ℝ φ z) v) • (A n (gm m z))
            = - ∫ z, φ z • ((fderiv ℝ (A n) (gm m z))
                ((CV m) z)) := by
          intro m
          have hcomp : ContDiffOn ℝ 1 (A n ∘ gm m) Set.univ :=
            (((hAsm n).comp (hgmsm m)).of_le hle1).contDiffOn
          have hIBP0 := HasWeakDirDeriv.of_contDiffOn (v := v) isOpen_univ hcomp φ hφs hφc
            (Set.subset_univ _)
          calc ∫ z, ((fderiv ℝ φ z) v) • (A n (gm m z))
              = ∫ z, ((fderiv ℝ φ z) v) • ((A n ∘ gm m) z) := rfl
            _ = - ∫ z, φ z • ((fderiv ℝ (A n ∘ gm m) z) v) := hIBP0
            _ = - ∫ z, φ z • ((fderiv ℝ (A n) (gm m z))
                  ((CV m) z)) := by
                refine congrArg Neg.neg (integral_congr_ae
                  (Filter.Eventually.of_forall fun z => ?_))
                have hd1 : DifferentiableAt ℝ (A n) (gm m z) :=
                  ((hAsm n).differentiable hne0).differentiableAt
                have hd2 : DifferentiableAt ℝ (gm m) z :=
                  ((hgmsm m).differentiable hne0).differentiableAt
                simp only
                rw [fderiv_comp z hd1 hd2, ContinuousLinearMap.comp_apply, hgmderiv m z]
        -- (II) the left `m`-limit
        have hLconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in Filter.atTop, ∀ z ∈ tsupport φ,
            ‖A n (gm m z) - A n (G z)‖ ≤ ε := by
          intro ε hε
          have hucA := hKg1c.uniformContinuousOn_of_continuous
            (hAsm n).continuous.continuousOn
          obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp hucA ε hε
          filter_upwards [hgmconv (min (δ/2) 1) (lt_min (by linarith) one_pos)] with m hm z hz
          have h1 := hm z
          have hGz : G z ∈ Kg1 := hKgsub (hGKg z hz)
          have hgmz : gm m z ∈ Kg1 :=
            hnearKg1 (G z) (hGKg z hz) (gm m z) (le_trans h1 (min_le_right _ _))
          have h2 : dist (gm m z) (G z) < δ :=
            lt_of_le_of_lt (le_trans h1 (min_le_left _ _)) (by linarith)
          rw [← dist_eq_norm]
          exact (hδ (gm m z) hgmz (G z) hGz h2).le
        have hLlim : Filter.Tendsto (fun m => ∫ z, ((fderiv ℝ φ z) v) • (A n (gm m z)))
            Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) v) • (A n (G z)))) := by
          refine tendsto_integral_of_L1 _ (hIntCont _ _ hdφcont hdφzero
            ((hAsm n).continuous.comp hGcont)) ?_ ?_
          · exact Filter.Eventually.of_forall fun m =>
              hIntCont _ _ hdφcont hdφzero ((hAsm n).continuous.comp (hgmsm m).continuous)
          · exact hsupL1 _ _ hMdφ hdφzero _ _ hLconv
        -- (III) the right `m`-limit
        have hRlim : Filter.Tendsto (fun m => ∫ z, φ z • ((fderiv ℝ (A n) (gm m z))
              ((CV m) z)))
            Filter.atTop (nhds (∫ z, φ z • ((fderiv ℝ (A n) (G z)) (Gv z)))) := by
          have hTcont : Continuous fun z => fderiv ℝ (A n) (G z) := hDncont.comp hGcont
          have hTbd : ∀ z ∈ tsupport φ, ‖fderiv ℝ (A n) (G z)‖ ≤ MD0 :=
            fun z hz => hMD0 _ (hKgsub (hGKg z hz))
          refine tendsto_integral_of_L1 _
            (hIntCLM _ hTcont MD0 hTbd Gv hGvsm hGvInt) ?_ ?_
          · filter_upwards with m
            exact hIntCont _ _ hφs.continuous hφzero
              ((hDncont.comp (hgmsm m).continuous).clm_apply (hCVcont m))
          · -- the `L¹` difference limit
            rw [ENNReal.tendsto_atTop_zero]
            intro ε hε
            set CMD : ℝ≥0∞ := ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) with hCMDdef
            have hCMDtop : CMD ≠ ⊤ := ENNReal.ofReal_ne_top
            set Cvol : ℝ≥0∞ := (volume (tsupport φ)) ^ ((1:ℝ)/2) with hCvoldef
            have hCvoltop : Cvol ≠ ⊤ := by
              rw [hCvoldef]
              exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKvol.ne).ne
            obtain ⟨ε1, hε10, hε1⟩ := hthreshold (CMD * Cvol)
              (ENNReal.mul_ne_top hCMDtop hCvoltop) (ε/2) (ENNReal.half_pos hε.ne')
            obtain ⟨ε2, hε20, hε2⟩ := hthreshold
              (ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ, ‖Gv z‖ₑ)
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGvfin.ne) (ε/2)
              (ENNReal.half_pos hε.ne')
            -- eventual smallness of the convolution error in `L²`
            obtain ⟨N1, hN1⟩ := (ENNReal.tendsto_atTop_zero.mp hCVconv)
              (ENNReal.ofReal ε1) (ENNReal.ofReal_pos.mpr hε10)
            -- eventual uniform closeness of the differentials along the tube
            have hDuc := hKg1c.uniformContinuousOn_of_continuous hDncont.continuousOn
            obtain ⟨δ2, hδ20, hδ2⟩ := Metric.uniformContinuousOn_iff.mp hDuc ε2 hε20
            obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
              (hgmconv (min (δ2/2) 1) (lt_min (by linarith) one_pos))
            refine ⟨max N1 N2, fun m hm => ?_⟩
            have hmN1 : N1 ≤ m := le_trans (le_max_left _ _) hm
            have hmN2 : N2 ≤ m := le_trans (le_max_right _ _) hm
            -- names for the two pieces
            set Ym : ℂ → ℂ := fun z => CV m z - Gv z with hYmdef
            have hYmsm : AEStronglyMeasurable Ym volume :=
              (hCVcont m).aestronglyMeasurable.sub hGvsm
            -- pointwise split
            have hptw : ∀ z : ℂ, ‖φ z • ((fderiv ℝ (A n) (gm m z))
                  ((CV m) z))
                - φ z • ((fderiv ℝ (A n) (G z)) (Gv z))‖ₑ
                ≤ ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                  + ‖φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ := by
              intro z
              have halg : φ z • ((fderiv ℝ (A n) (gm m z)) ((CV m) z))
                  - φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  = φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))
                    + φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z)) := by
                rw [hYmdef]
                simp only [map_sub, ContinuousLinearMap.sub_apply, Complex.real_smul]
                ring
              rw [halg]
              exact enorm_add_le _ _
            have hsm1 : AEStronglyMeasurable
                (fun z => φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))) volume := by
              refine (hφs.continuous.aestronglyMeasurable).smul ?_
              exact (isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
                (((hDncont.comp (hgmsm m).continuous).aestronglyMeasurable).prodMk hYmsm)
            have hbound1 : ∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ ≤ ε/2 := by
              have hz1 : ∀ z : ℂ, z ∉ tsupport φ →
                  φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z)) = 0 := by
                intro z hz
                rw [hφzero z hz]
                exact zero_smul ℝ _
              rw [hlsupp _ hz1]
              have hpt1 : ∀ z ∈ tsupport φ,
                  ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                    ≤ ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ₑ := by
                intro z hz
                have hgmz : gm m z ∈ Kg1 :=
                  hnearKg1 (G z) (hGKg z hz) (gm m z)
                    (le_trans (hN2 m hmN2 z) (min_le_right _ _))
                have hb1 : ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖
                    ≤ (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ := by
                  rw [norm_smul]
                  have hb2 : ‖(fderiv ℝ (A n) (gm m z)) (Ym z)‖
                      ≤ (max MD0 0 + 1) * ‖Ym z‖ := by
                    refine le_trans ((fderiv ℝ (A n) (gm m z)).le_opNorm _) ?_
                    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                    have := hMD0 _ hgmz
                    have h13 : MD0 ≤ max MD0 0 := le_max_left _ _
                    linarith
                  calc ‖φ z‖ * ‖(fderiv ℝ (A n) (gm m z)) (Ym z)‖
                      ≤ (max Mφ0 0) * ((max MD0 0 + 1) * ‖Ym z‖) := by
                        refine mul_le_mul (hMφ z) hb2 (norm_nonneg _) (le_max_right _ _)
                    _ = (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ := by ring
                calc ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                    = ENNReal.ofReal ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ :=
                      (ofReal_norm_eq_enorm _).symm
                  _ ≤ ENNReal.ofReal ((max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖) :=
                      ENNReal.ofReal_le_ofReal hb1
                  _ = ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ₑ := by
                      rw [ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm]
              calc ∫⁻ z in tsupport φ, ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                  ≤ ∫⁻ z in tsupport φ,
                      ENNReal.ofReal (max Mφ0 0 * (max MD0 0 + 1)) * ‖Ym z‖ₑ :=
                    lintegral_mono_ae ((ae_restrict_iff' hKmeas).mpr
                      (Filter.Eventually.of_forall hpt1))
                _ = CMD * ∫⁻ z in tsupport φ, ‖Ym z‖ₑ := by
                    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCMDdef]
                _ ≤ CMD * (eLpNorm Ym 2 volume * Cvol) := by
                    refine mul_le_mul_right ?_ _
                    rw [hCvoldef]
                    exact hL2K Ym hYmsm
                _ = (CMD * Cvol) * eLpNorm Ym 2 volume := by ring
                _ ≤ (CMD * Cvol) * ENNReal.ofReal ε1 :=
                    mul_le_mul_right (hN1 m hmN1) _
                _ = ENNReal.ofReal ε1 * (CMD * Cvol) := by ring
                _ ≤ ε/2 := hε1
            have hbound2 : ∫⁻ z, ‖φ z • (((fderiv ℝ (A n) (gm m z))
                  - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ ≤ ε/2 := by
              have hz2 : ∀ z : ℂ, z ∉ tsupport φ →
                  φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z)) = 0 := by
                intro z hz
                rw [hφzero z hz]
                exact zero_smul ℝ _
              rw [hlsupp _ hz2]
              have hpt2 : ∀ z ∈ tsupport φ,
                  ‖φ z • (((fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ
                    ≤ ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2 * ‖Gv z‖ₑ := by
                intro z hz
                have hgmz : gm m z ∈ Kg1 :=
                  hnearKg1 (G z) (hGKg z hz) (gm m z)
                    (le_trans (hN2 m hmN2 z) (min_le_right _ _))
                have hdd : dist (gm m z) (G z) < δ2 :=
                  lt_of_le_of_lt (le_trans (hN2 m hmN2 z) (min_le_left _ _)) (by linarith)
                have hopb : ‖(fderiv ℝ (A n) (gm m z)) - (fderiv ℝ (A n) (G z))‖ ≤ ε2 := by
                  rw [← dist_eq_norm]
                  exact (hδ2 (gm m z) hgmz (G z) (hKgsub (hGKg z hz)) hdd).le
                have hb1 : ‖φ z • (((fderiv ℝ (A n) (gm m z))
                      - (fderiv ℝ (A n) (G z))) (Gv z))‖
                    ≤ (max Mφ0 0) * (ε2 * ‖Gv z‖) := by
                  rw [norm_smul]
                  refine mul_le_mul (hMφ z) ?_ (norm_nonneg _) (le_max_right _ _)
                  refine le_trans (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))).le_opNorm _) ?_
                  exact mul_le_mul_of_nonneg_right hopb (norm_nonneg _)
                calc ‖φ z • (((fderiv ℝ (A n) (gm m z))
                      - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ
                    = ENNReal.ofReal ‖φ z • (((fderiv ℝ (A n) (gm m z))
                        - (fderiv ℝ (A n) (G z))) (Gv z))‖ := (ofReal_norm_eq_enorm _).symm
                  _ ≤ ENNReal.ofReal ((max Mφ0 0) * (ε2 * ‖Gv z‖)) :=
                      ENNReal.ofReal_le_ofReal hb1
                  _ = ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2 * ‖Gv z‖ₑ := by
                      rw [ENNReal.ofReal_mul (le_max_right _ _),
                        ENNReal.ofReal_mul hε20.le, ofReal_norm_eq_enorm, mul_assoc]
              calc ∫⁻ z in tsupport φ, ‖φ z • (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ
                  ≤ ∫⁻ z in tsupport φ,
                      ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2 * ‖Gv z‖ₑ :=
                    lintegral_mono_ae ((ae_restrict_iff' hKmeas).mpr
                      (Filter.Eventually.of_forall hpt2))
                _ = ENNReal.ofReal (max Mφ0 0) * ENNReal.ofReal ε2
                      * ∫⁻ z in tsupport φ, ‖Gv z‖ₑ := by
                    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
                      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
                _ = ENNReal.ofReal ε2
                      * (ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ, ‖Gv z‖ₑ) := by
                    ring
                _ ≤ ε/2 := hε2
            calc ∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (gm m z))
                  ((CV m) z))
                - φ z • ((fderiv ℝ (A n) (G z)) (Gv z))‖ₑ
                ≤ ∫⁻ z, (‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ
                  + ‖φ z • (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ) := lintegral_mono hptw
              _ = (∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (gm m z)) (Ym z))‖ₑ)
                  + ∫⁻ z, ‖φ z • (((fderiv ℝ (A n) (gm m z))
                    - (fderiv ℝ (A n) (G z))) (Gv z))‖ₑ :=
                  lintegral_add_left' hsm1.enorm _
              _ ≤ ε/2 + ε/2 := add_le_add hbound1 hbound2
              _ = ε := ENNReal.add_halves ε
        -- combine the three `m`-facts
        exact tendsto_nhds_unique hLlim
          ((hRlim.neg).congr fun m => (hIBPm m).symm)
      -- ===== the Cauchy–Schwarz/area estimate =====
      have hJfacts : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
          ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ 0
            ∧ ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ)
              ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * ENNReal.ofReal ((fderiv ℝ P.g z).det) := by
        have hres : volume.restrict (tsupport φ) ≤ volume.restrict {z : ℂ | 0 < z.im} :=
          Measure.restrict_mono hKU le_rfl
        filter_upwards [(ae_mono hres) hggood, (ae_mono hres) hdistort] with z hz hd
        constructor
        · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          exact hz.2.1
        · have h2 := hd v hv1
          calc ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ)
              = ENNReal.ofReal (‖(fderiv ℝ P.g z) v‖ ^ 2) := by
                rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
            _ ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0) * (fderiv ℝ P.g z).det) :=
                ENNReal.ofReal_le_ofReal h2
            _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * ENNReal.ofReal ((fderiv ℝ P.g z).det) := by
                rw [ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]
      have hCSJ : ∀ Q : ℂ → ℝ≥0∞, Measurable Q →
          ∫⁻ z in tsupport φ, Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
            ≤ ((∫⁻ u in Metric.ball 0 R0, Q u ^ (2:ℕ)) ^ ((1:ℝ)/2))
              * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * volume (tsupport φ)) ^ ((1:ℝ)/2) := by
        intro Q hQ
        have hgaeK : AEMeasurable P.g (volume.restrict (tsupport φ)) :=
          (P.qc.cont.mono hKU).aemeasurable hKmeas
        have hf1m : AEMeasurable (fun z => Q (P.g z)
            * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
            (volume.restrict (tsupport φ)) :=
          (hQ.comp_aemeasurable hgaeK).mul
            ((hdetmeas.ennreal_ofReal.aemeasurable.mono_measure
              (Measure.restrict_le_self)).pow_const _)
        have hf2m : AEMeasurable (fun z => ‖(fderiv ℝ P.g z) v‖ₑ
            * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2)))
            (volume.restrict (tsupport φ)) := by
          refine AEMeasurable.mul ?_ ?_
          · exact (((measurable_fderiv ℝ P.g).apply_continuousLinearMap v).enorm).aemeasurable
          · exact (hdetmeas.ennreal_ofReal.aemeasurable.mono_measure
              (Measure.restrict_le_self)).pow_const _
        have hsplit : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
            Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
              = (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
                * (‖(fderiv ℝ P.g z) v‖ₑ
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) := by
          filter_upwards [hJfacts] with z hz
          have hJ0 : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ 0 := hz.1
          have hJt : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ ⊤ := ENNReal.ofReal_ne_top
          have hone : (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)
              * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2)) = 1 := by
            rw [← ENNReal.rpow_add _ _ hJ0 hJt]
            norm_num
          calc Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
              = Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
                * ((ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) := by
                rw [hone, mul_one]
            _ = (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
                * (‖(fderiv ℝ P.g z) v‖ₑ
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) := by
                ring
        have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (tsupport φ))
          (by constructor <;> norm_num : (2:ℝ).HolderConjugate 2) hf1m hf2m
        have hstepA : ∫⁻ z in tsupport φ, Q (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ
            = ∫⁻ z in tsupport φ,
                ((fun z => Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2))
                * fun z => ‖(fderiv ℝ P.g z) v‖ₑ
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) z :=
          lintegral_congr_ae (hsplit.mono fun z hz => by simpa using hz)
        rw [hstepA]
        refine le_trans hcs ?_
        -- first factor: the area estimate
        have hfac1 : (∫⁻ z in tsupport φ,
            (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)) ^ (2:ℝ))
              ^ ((1:ℝ)/2)
            ≤ ((∫⁻ u in Metric.ball 0 R0, Q u ^ (2:ℕ)) ^ ((1:ℝ)/2)) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          have heq2 : ∀ z : ℂ,
              (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)) ^ (2:ℝ)
              = ENNReal.ofReal ((fderiv ℝ P.g z).det) * (Q (P.g z)) ^ (2:ℕ) := by
            intro z
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
              ← ENNReal.rpow_mul (ENNReal.ofReal ((fderiv ℝ P.g z).det)),
              ← ENNReal.rpow_natCast (Q (P.g z)) 2]
            norm_num
            rw [mul_comm]
          calc ∫⁻ z in tsupport φ,
              (Q (P.g z) * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ ((1:ℝ)/2)) ^ (2:ℝ)
              = ∫⁻ z in tsupport φ,
                ENNReal.ofReal ((fderiv ℝ P.g z).det) * (Q (P.g z)) ^ (2:ℕ) :=
                lintegral_congr fun z => heq2 z
            _ ≤ ∫⁻ u in Metric.ball 0 R0, Q u ^ (2:ℕ) :=
                hArea (tsupport φ) hKmeas hKU (Metric.ball 0 R0)
                  (by rw [← hKgdef]; exact hR0) (fun u => Q u ^ (2:ℕ))
        -- second factor: the distortion bound
        have hfac2 : (∫⁻ z in tsupport φ,
            (‖(fderiv ℝ P.g z) v‖ₑ
              * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ))
              ^ ((1:ℝ)/2)
            ≤ (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
              * volume (tsupport φ)) ^ ((1:ℝ)/2) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          have hptb : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
              (‖(fderiv ℝ P.g z) v‖ₑ
                * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ)
              ≤ ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0)) := by
            filter_upwards [hJfacts] with z hz
            have hJ0 : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ 0 := hz.1
            have hJt : ENNReal.ofReal ((fderiv ℝ P.g z).det) ≠ ⊤ := ENNReal.ofReal_ne_top
            have hexp : (‖(fderiv ℝ P.g z) v‖ₑ
                * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ)
                = ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ)
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹ := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
                ← ENNReal.rpow_mul (ENNReal.ofReal ((fderiv ℝ P.g z).det)),
                ← ENNReal.rpow_natCast (‖(fderiv ℝ P.g z) v‖ₑ) 2]
              norm_num
              rw [ENNReal.rpow_neg_one]
            rw [hexp]
            calc ‖(fderiv ℝ P.g z) v‖ₑ ^ (2:ℕ) * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹
                ≤ (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                    * ENNReal.ofReal ((fderiv ℝ P.g z).det))
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹ :=
                  mul_le_mul_left hz.2 _
              _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * (ENNReal.ofReal ((fderiv ℝ P.g z).det)
                    * (ENNReal.ofReal ((fderiv ℝ P.g z).det))⁻¹) := by ring
              _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0)) := by
                  rw [ENNReal.mul_inv_cancel hz.1 ENNReal.ofReal_ne_top, mul_one]
          calc ∫⁻ z in tsupport φ,
              (‖(fderiv ℝ P.g z) v‖ₑ
                * (ENNReal.ofReal ((fderiv ℝ P.g z).det)) ^ (-((1:ℝ)/2))) ^ (2:ℝ)
              ≤ ∫⁻ _ in tsupport φ,
                ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0)) :=
                lintegral_mono_ae hptb
            _ = ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * volume (tsupport φ) := setLIntegral_const _ _
        exact mul_le_mul' hfac1 hfac2
      -- ===== restriction form of the gradient identification =====
      have hGvK : ∀ᵐ z ∂(volume.restrict (tsupport φ)), Gv z = (fderiv ℝ P.g z) v := by
        filter_upwards [ae_restrict_of_ae hGveqPg, ae_restrict_mem hKmeas] with z h1 h2
        exact h1 (Metric.self_subset_thickening hr0 _ h2)
      -- ===== the left `n`-limit =====
      have hLconvN : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ z ∈ tsupport φ,
          ‖A n (G z) - x.w (G z)‖ ≤ ε := by
        intro ε hε
        filter_upwards [hAconv ε hε] with n hn z hz
        rw [← dist_eq_norm]
        exact hn (G z) (hGKg z hz)
      have hLlimN : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φ z) v) • (A n (G z)))
          Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) v) • (x.w (G z)))) := by
        refine tendsto_integral_of_L1 _
          (hIntCont _ _ hdφcont hdφzero (hxc.comp hGcont)) ?_ ?_
        · exact Filter.Eventually.of_forall fun n =>
            hIntCont _ _ hdφcont hdφzero ((hAsm n).continuous.comp hGcont)
        · exact hsupL1 _ _ hMdφ hdφzero _ _ hLconvN
      -- ===== the right `n`-limit through the Cauchy–Schwarz/area estimate =====
      have hQxm : Measurable fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ :=
        (measurable_fderiv ℝ x.w).enorm
      have hxball : ∫⁻ u in Metric.ball 0 R0, (fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ)
          ≠ ⊤ := by
        have h1 := IsQCAnalytic.lintegralSq_fderiv_ball_ne_top x.w_isQCAnalytic R0
        simpa [enorm_eq_nnnorm] using h1
      have hIntlim : Integrable (fun z => φ z • ((fderiv ℝ x.w (G z)) (Gv z))) volume := by
        constructor
        · refine (hφs.continuous.aestronglyMeasurable).smul ?_
          exact (isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
            ((((measurable_fderiv ℝ x.w).comp
              hGcont.measurable).aestronglyMeasurable).prodMk hGvsm)
        · rw [hasFiniteIntegral_iff_enorm]
          have hz0 : ∀ z : ℂ, z ∉ tsupport φ →
              φ z • ((fderiv ℝ x.w (G z)) (Gv z)) = 0 := by
            intro z hz
            rw [hφzero z hz]
            exact zero_smul ℝ _
          rw [hlsupp _ hz0]
          have hptb : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
              ‖φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
                ≤ ENNReal.ofReal (max Mφ0 0)
                  * ((fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z)
                    * ‖(fderiv ℝ P.g z) v‖ₑ) := by
            filter_upwards [hGvK, ae_restrict_mem hKmeas] with z h1 h2
            have hGz : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ h2)
            rw [hGz, h1]
            calc ‖φ z • ((fderiv ℝ x.w (P.g z)) ((fderiv ℝ P.g z) v))‖ₑ
                = ENNReal.ofReal ‖φ z • ((fderiv ℝ x.w (P.g z)) ((fderiv ℝ P.g z) v))‖ :=
                  (ofReal_norm_eq_enorm _).symm
              _ ≤ ENNReal.ofReal ((max Mφ0 0)
                    * (‖fderiv ℝ x.w (P.g z)‖ * ‖(fderiv ℝ P.g z) v‖)) := by
                  refine ENNReal.ofReal_le_ofReal ?_
                  rw [norm_smul]
                  refine mul_le_mul (hMφ z)
                    ((fderiv ℝ x.w (P.g z)).le_opNorm _) (norm_nonneg _)
                    (le_max_right _ _)
              _ = ENNReal.ofReal (max Mφ0 0)
                    * ((fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z)
                      * ‖(fderiv ℝ P.g z) v‖ₑ) := by
                  rw [ENNReal.ofReal_mul (le_max_right _ _),
                    ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm,
                    ofReal_norm_eq_enorm]
          calc ∫⁻ z in tsupport φ, ‖φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
              ≤ ∫⁻ z in tsupport φ, ENNReal.ofReal (max Mφ0 0)
                  * ((fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z)
                    * ‖(fderiv ℝ P.g z) v‖ₑ) := lintegral_mono_ae hptb
            _ = ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ,
                  (fun u : ℂ => ‖fderiv ℝ x.w u‖ₑ) (P.g z) * ‖(fderiv ℝ P.g z) v‖ₑ :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ < ⊤ := by
                refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
                refine lt_of_le_of_lt (hCSJ _ hQxm) ?_
                refine ENNReal.mul_lt_top ?_ ?_
                · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
                    hxball
                · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
                    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKvol.ne)
      have hRlimN : Filter.Tendsto
          (fun n => ∫ z, φ z • ((fderiv ℝ (A n) (G z)) (Gv z)))
          Filter.atTop (nhds (∫ z, φ z • ((fderiv ℝ x.w (G z)) (Gv z)))) := by
        refine tendsto_integral_of_L1 _ hIntlim ?_ ?_
        · refine Filter.Eventually.of_forall fun n => ?_
          have hDncont : Continuous fun u : ℂ => fderiv ℝ (A n) u :=
            (hAsm n).continuous_fderiv hne0
          obtain ⟨MD0, hMD0⟩ := hKg1c.exists_bound_of_continuousOn hDncont.continuousOn
          exact hIntCLM _ (hDncont.comp hGcont) MD0
            (fun z hz => hMD0 _ (hKgsub (hGKg z hz))) Gv hGvsm hGvInt
        · -- the `L¹` difference limit via the energy decay
          have hboundall : ∀ n : ℕ,
              ∫⁻ z, ‖φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                - φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
              ≤ ENNReal.ofReal (max Mφ0 0)
                * (((∫⁻ u in Metric.ball 0 R0,
                    (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                      ^ ((1:ℝ)/2))
                  * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                    * volume (tsupport φ)) ^ ((1:ℝ)/2)) := by
            intro n
            have hz0 : ∀ z : ℂ, z ∉ tsupport φ →
                φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z)) = 0 := by
              intro z hz
              rw [hφzero z hz]
              simp
            rw [hlsupp _ hz0]
            have hptb : ∀ᵐ z ∂(volume.restrict (tsupport φ)),
                ‖φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
                ≤ ENNReal.ofReal (max Mφ0 0)
                  * ((fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                    * ‖(fderiv ℝ P.g z) v‖ₑ) := by
              filter_upwards [hGvK, ae_restrict_mem hKmeas] with z h1 h2
              have hGz : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ h2)
              have halg2 : φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z))
                  = φ z • (((fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)))
                      ((fderiv ℝ P.g z) v)) := by
                rw [hGz, h1, ContinuousLinearMap.sub_apply]
                simp only [Complex.real_smul]
                ring
              rw [halg2]
              calc ‖φ z • (((fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)))
                    ((fderiv ℝ P.g z) v))‖ₑ
                  = ENNReal.ofReal ‖φ z • (((fderiv ℝ (A n) (P.g z)
                      - fderiv ℝ x.w (P.g z))) ((fderiv ℝ P.g z) v))‖ :=
                    (ofReal_norm_eq_enorm _).symm
                _ ≤ ENNReal.ofReal ((max Mφ0 0)
                      * (‖fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)‖
                        * ‖(fderiv ℝ P.g z) v‖)) := by
                    refine ENNReal.ofReal_le_ofReal ?_
                    rw [norm_smul]
                    refine mul_le_mul (hMφ z)
                      ((fderiv ℝ (A n) (P.g z) - fderiv ℝ x.w (P.g z)).le_opNorm _)
                      (norm_nonneg _) (le_max_right _ _)
                _ = ENNReal.ofReal (max Mφ0 0)
                      * ((fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                        * ‖(fderiv ℝ P.g z) v‖ₑ) := by
                    rw [ENNReal.ofReal_mul (le_max_right _ _),
                      ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm,
                      ofReal_norm_eq_enorm]
            have hQnm : Measurable fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ := by
              have hDncont : Continuous fun u : ℂ => fderiv ℝ (A n) u :=
                (hAsm n).continuous_fderiv hne0
              exact (hDncont.measurable.sub (measurable_fderiv ℝ x.w)).enorm
            calc ∫⁻ z in tsupport φ, ‖φ z • ((fderiv ℝ (A n) (G z)) (Gv z))
                  - φ z • ((fderiv ℝ x.w (G z)) (Gv z))‖ₑ
                ≤ ∫⁻ z in tsupport φ, ENNReal.ofReal (max Mφ0 0)
                    * ((fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                      * ‖(fderiv ℝ P.g z) v‖ₑ) := lintegral_mono_ae hptb
              _ = ENNReal.ofReal (max Mφ0 0) * ∫⁻ z in tsupport φ,
                    (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) (P.g z)
                      * ‖(fderiv ℝ P.g z) v‖ₑ :=
                  lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
              _ ≤ ENNReal.ofReal (max Mφ0 0)
                  * (((∫⁻ u in Metric.ball 0 R0,
                      (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                        ^ ((1:ℝ)/2))
                    * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                      * volume (tsupport φ)) ^ ((1:ℝ)/2)) :=
                  mul_le_mul_right (hCSJ _ hQnm) _
          have hEnergyN : Filter.Tendsto (fun n => ∫⁻ u in Metric.ball 0 R0,
              (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
              Filter.atTop (nhds 0) := by
            have h1 := henergy
            refine h1.congr fun n => ?_
            refine lintegral_congr fun u => ?_
            simp [enorm_eq_nnnorm, hAdef]
          have hbtend : Filter.Tendsto (fun n => ENNReal.ofReal (max Mφ0 0)
              * (((∫⁻ u in Metric.ball 0 R0,
                  (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                    ^ ((1:ℝ)/2))
                * (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                  * volume (tsupport φ)) ^ ((1:ℝ)/2)))
              Filter.atTop (nhds 0) := by
            have h2 : Filter.Tendsto (fun n => (∫⁻ u in Metric.ball 0 R0,
                (fun u : ℂ => ‖fderiv ℝ (A n) u - fderiv ℝ x.w u‖ₑ) u ^ (2:ℕ))
                  ^ ((1:ℝ)/2)) Filter.atTop (nhds 0) := by
              have h3 := (ENNReal.continuous_rpow_const (y := (1:ℝ)/2)).continuousAt
                (x := 0)
              have h4 := h3.tendsto.comp hEnergyN
              simpa [ENNReal.zero_rpow_of_pos] using h4
            have h5 := ENNReal.Tendsto.mul_const h2
              (b := (ENNReal.ofReal ((1 + max P.κ 0) / (1 - max P.κ 0))
                * volume (tsupport φ)) ^ ((1:ℝ)/2))
              (Or.inr ((ENNReal.rpow_lt_top_of_nonneg (by norm_num)
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKvol.ne)).ne))
            have h6 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (max Mφ0 0)) h5
              (Or.inr ENNReal.ofReal_ne_top)
            simpa using h6
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbtend
            (fun n => zero_le _) (fun n => hboundall n)
      -- ===== final assembly =====
      have hgoal1 : ∫ z, ((fderiv ℝ φ z) v) • ((x.w ∘ P.g) z)
          = ∫ z, ((fderiv ℝ φ z) v) • (x.w (G z)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        change ((fderiv ℝ φ z) v) • ((x.w ∘ P.g) z) = ((fderiv ℝ φ z) v) • (x.w (G z))
        by_cases hz : z ∈ tsupport φ
        · have h1 : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ hz)
          rw [h1]
          rfl
        · rw [hdφzero z hz]
          simp
      have hkeyeq := tendsto_nhds_unique hLlimN ((hRlimN.neg).congr fun n => (hEn n).symm)
      have hgoal2 : ∫ z, φ z • ((fderiv ℝ x.w (G z)) (Gv z))
          = ∫ z, φ z • ((fderiv ℝ (x.w ∘ P.g) z) v) := by
        have hch : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
            (DifferentiableAt ℝ P.g z ∧ DifferentiableAt ℝ x.w (P.g z) ∧
              fderiv ℝ (x.w ∘ P.g) z = (fderiv ℝ x.w (P.g z)).comp (fderiv ℝ P.g z)) :=
          (ae_restrict_iff' hU).mp hchain
        refine integral_congr_ae ?_
        filter_upwards [hGveqPg, hch] with z h1 h2
        by_cases hz : z ∈ tsupport φ
        · have hGz : G z = P.g z := hGeq z (Metric.self_subset_cthickening _ hz)
          have hGvz : Gv z = (fderiv ℝ P.g z) v :=
            h1 (Metric.self_subset_thickening hr0 _ hz)
          have hcz := h2 (hKU hz)
          rw [hGz, hGvz, hcz.2.2, ContinuousLinearMap.comp_apply]
        · rw [hφzero z hz]
          simp
      calc ∫ z, ((fderiv ℝ φ z) v) • ((x.w ∘ P.g) z)
          = ∫ z, ((fderiv ℝ φ z) v) • (x.w (G z)) := hgoal1
        _ = - ∫ z, φ z • ((fderiv ℝ x.w (G z)) (Gv z)) := hkeyeq
        _ = - ∫ z, φ z • ((fderiv ℝ (x.w ∘ P.g) z) v) := congrArg Neg.neg hgoal2
    -- ===== assemble the local Sobolev membership =====
    obtain ⟨hgLp0, gx0, gy0, ⟨hgx0, hgy0⟩, hmx0, hmy0⟩ := P.qc.sobolev
    refine ⟨?_, fun z => (fderiv ℝ (x.w ∘ P.g) z) 1,
      fun z => (fderiv ℝ (x.w ∘ P.g) z) Complex.I,
      ⟨hKEY 1 gx0 (Or.inl rfl) hgx0 hmx0,
        hKEY Complex.I gy0 (Or.inr rfl) hgy0 hmy0⟩,
      hgradL2 1 (by simp), hgradL2 Complex.I (by simp)⟩
    intro Kc hKcU hKcc
    haveI : IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKcc.measure_lt_top⟩
    have hFcont : ContinuousOn (x.w ∘ P.g) {z : ℂ | 0 < z.im} :=
      hxc.comp_continuousOn P.qc.cont
    obtain ⟨MF, hMF⟩ := hKcc.exists_bound_of_continuousOn (hFcont.mono hKcU)
    refine MemLp.of_bound (((hFcont.mono hKcU).aemeasurable
      hKcc.measurableSet).aestronglyMeasurable) MF ?_
    exact (ae_restrict_iff' hKcc.measurableSet).mpr (Filter.Eventually.of_forall hMF)
  · -- jac
    filter_upwards [hband] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hB0 : 0 ≤ ‖dzbar (x.w ∘ P.g) z‖ := norm_nonneg _
    rw [det_fderiv_eq_wirtinger]
    set c := (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) with hc
    set A := ‖dz (x.w ∘ P.g) z‖ with hA
    set B := ‖dzbar (x.w ∘ P.g) z‖ with hB
    have hcc : c * c < 1 := by
      have h3 : c * c ≤ c := mul_le_of_le_one_left hκ'0 hκ'1.le
      linarith
    have h1 : B * B ≤ (c * A) * (c * A) := mul_self_le_mul_self hB0 hz1
    have h2 : 0 < (1 - c * c) * (A * A) := mul_pos (by linarith) (mul_pos hz2 hz2)
    nlinarith [h1, h2]
  · -- belt
    filter_upwards [hband] with z hz
    exact hz.1

/-- The **re-marked representative**: the representative whose coefficient is the
symmetric extension of the Beltrami datum of `x.w ∘ P.g` on the upper half plane. -/
noncomputable def TeichRep.smulUpper (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    TeichRep Γ₀ :=
  TeichRep.ofUpper Γ₀ (wirtingerQuotient (x.w ∘ P.g))
    (measurable_wirtingerQuotient_remark x P)
    (wirtingerQuotient_remark_bound x P)
    (wirtingerQuotient_remark_invariant x P)

/-- Plane Möbius maps of real matrices commute with complex conjugation. -/
theorem moebiusMap_conj (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    moebiusMap γ (starRingEnd ℂ z) = starRingEnd ℂ (moebiusMap γ z) := by
  simp [moebiusMap, moebiusDenom, map_div₀, map_add, map_mul, Complex.conj_ofReal]

/-- A real Möbius map sends real points to real points. -/
theorem moebiusMap_ofReal (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    ∃ r : ℝ, moebiusMap γ (t : ℂ) = (r : ℂ) := by
  have h := moebiusMap_conj γ (t : ℂ)
  rw [Complex.conj_ofReal] at h
  have him : (moebiusMap γ (t : ℂ)).im = 0 := Complex.conj_eq_iff_im.mp h.symm
  exact ⟨(moebiusMap γ (t : ℂ)).re, (Complex.ext (by simp) (by simp [him])).symm⟩

/-- The pole set of a plane Möbius map is a subsingleton. -/
theorem moebiusDenom_zero_subsingleton (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Set.Subsingleton {w : ℂ | moebiusDenom γ w = 0} := by
  intro w₁ hw₁ w₂ hw₂
  have h₁' : (γ 1 0 : ℂ) * w₁ + (γ 1 1 : ℂ) = 0 := hw₁
  have h₂' : (γ 1 0 : ℂ) * w₂ + (γ 1 1 : ℂ) = 0 := hw₂
  by_cases hc : γ 1 0 = 0
  · exfalso
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe γ
      rwa [Matrix.det_fin_two] at h
    have hcC : ((γ 1 0 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
    rw [hcC, zero_mul, zero_add] at h₁'
    have hd : γ 1 1 = 0 := by exact_mod_cast h₁'
    rw [hc, hd] at hdet
    simp at hdet
  · have hcC : ((γ 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have hmul : (γ 1 0 : ℂ) * w₁ = (γ 1 0 : ℂ) * w₂ := by linear_combination h₁' - h₂'
    exact mul_left_cancel₀ hcC hmul

/-- The normalized solution reflects upper-half-plane membership. -/
theorem w_im_pos_rev (x : TeichRep Γ₀) {z : ℂ} (h : 0 < (x.w z).im) : 0 < z.im := by
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · exfalso
    have h1 : 0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im]
      linarith
    have h2 := x.w_mapsTo_upper _ h1
    rw [x.w_conj, Complex.conj_im] at h2
    linarith
  · exfalso
    have hz : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hzero])
    have h4 := x.w_real z.re
    rw [hz] at h4
    linarith
  · exact hpos

/-- Boundary limit: a continuous plane map that factors through Möbius maps and a
real-fixing continuous map on the upper half plane extends the Möbius identity to a real
boundary point off the poles. -/
theorem moebius_boundary {Λ φ : ℂ → ℂ} (hΛc : Continuous Λ) (hφc : Continuous φ)
    (hφr : ∀ r : ℝ, φ (r : ℂ) = (r : ℂ)) (Rx Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hint : ∀ ζ : ℂ, 0 < ζ.im → Λ ζ = moebiusMap Rx (φ (moebiusMap Ry⁻¹ ζ)))
    {t : ℝ} (hd1 : moebiusDenom Ry⁻¹ (t : ℂ) ≠ 0)
    (hd2 : moebiusDenom Rx (moebiusMap Ry⁻¹ (t : ℂ)) ≠ 0) :
    Λ (t : ℂ) = moebiusMap Rx (moebiusMap Ry⁻¹ (t : ℂ)) := by
  obtain ⟨r, hr⟩ := moebiusMap_ofReal Ry⁻¹ t
  set z : ℕ → ℂ := fun n => (t : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hzdef
  have him' : ∀ s : ℝ, ((t : ℂ) + (s : ℂ) * Complex.I).im = s := by
    intro s
    simp [Complex.add_im, Complex.mul_im]
  have hzim : ∀ n : ℕ, 0 < (z n).im := by
    intro n
    have h1 : (z n).im = 1 / ((n : ℝ) + 1) := by
      rw [hzdef]
      exact him' (1 / ((n : ℝ) + 1))
    rw [h1]
    positivity
  have htend : Filter.Tendsto z Filter.atTop (nhds (t : ℂ)) := by
    rw [hzdef]
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (nhds ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    have h3 := (h2.mul_const Complex.I).const_add (t : ℂ)
    simpa using h3
  have hL : Filter.Tendsto (fun n => Λ (z n)) Filter.atTop (nhds (Λ (t : ℂ))) :=
    (hΛc.tendsto _).comp htend
  have hc1 : ContinuousAt (moebiusMap Ry⁻¹) (t : ℂ) :=
    (hasDerivAt_moebiusMap Ry⁻¹ hd1).continuousAt
  have hc2 : ContinuousAt φ (moebiusMap Ry⁻¹ (t : ℂ)) := hφc.continuousAt
  have hφpt : φ (moebiusMap Ry⁻¹ (t : ℂ)) = moebiusMap Ry⁻¹ (t : ℂ) := by
    rw [hr, hφr r]
  have hc3 : ContinuousAt (moebiusMap Rx) (φ (moebiusMap Ry⁻¹ (t : ℂ))) := by
    rw [hφpt]
    exact (hasDerivAt_moebiusMap Rx hd2).continuousAt
  have hR : Filter.Tendsto (fun n => moebiusMap Rx (φ (moebiusMap Ry⁻¹ (z n))))
      Filter.atTop (nhds (moebiusMap Rx (φ (moebiusMap Ry⁻¹ (t : ℂ))))) := by
    have s1 : Filter.Tendsto (fun n => moebiusMap Ry⁻¹ (z n)) Filter.atTop
        (nhds (moebiusMap Ry⁻¹ (t : ℂ))) := hc1.tendsto.comp htend
    have s2 : Filter.Tendsto (fun n => φ (moebiusMap Ry⁻¹ (z n))) Filter.atTop
        (nhds (φ (moebiusMap Ry⁻¹ (t : ℂ)))) := hc2.tendsto.comp s1
    exact hc3.tendsto.comp s2
  have hEqn : (fun n => Λ (z n)) = fun n => moebiusMap Rx (φ (moebiusMap Ry⁻¹ (z n))) :=
    funext fun n => hint (z n) (hzim n)
  rw [hEqn] at hL
  have hfin := tendsto_nhds_unique hL hR
  rw [hfin, hφpt]

/-- A plane homeomorphism agreeing with a real Möbius map on a cofinite set of the real
line forces the Möbius map to be affine: otherwise the Möbius values stay bounded along
large reals while the homeomorphism escapes every compact set. -/
theorem sl2_lower_left_eq_zero (Λ : ℂ ≃ₜ ℂ)
    (S : Matrix.SpecialLinearGroup (Fin 2) ℝ) {B : Set ℝ} (hB : B.Finite)
    (hEq : ∀ t : ℝ, t ∉ B → Λ (t : ℂ) = moebiusMap S (t : ℂ)) : S 1 0 = 0 := by
  by_contra hc
  have hcpos : 0 < |S 1 0| := abs_pos.mpr hc
  obtain ⟨M, hM⟩ := hB.bddAbove
  have hnorm : ∀ t : ℝ, ‖moebiusMap S (t : ℂ)‖
      = |S 0 0 * t + S 0 1| / |S 1 0 * t + S 1 1| := by
    intro t
    have hcast : moebiusMap S (t : ℂ)
        = ((S 0 0 * t + S 0 1 : ℝ) : ℂ) / ((S 1 0 * t + S 1 1 : ℝ) : ℂ) := by
      simp only [moebiusMap, moebiusDenom]
      push_cast
      ring
    rw [hcast, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  set C := 2 * (|S 0 0| + |S 0 1|) / |S 1 0| with hCdef
  set T := (2 * |S 1 1| + 2) / |S 1 0| with hTdef
  have hbound : ∀ t : ℝ, max T 1 ≤ t → ‖moebiusMap S (t : ℂ)‖ ≤ C := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hTt : 2 * |S 1 1| + 2 ≤ |S 1 0| * t := by
      rw [hTdef, div_le_iff₀ hcpos] at htT
      linarith [htT, mul_comm t |S 1 0|]
    have hup : |S 0 0 * t + S 0 1| ≤ (|S 0 0| + |S 0 1|) * t := by
      have h1 : |S 0 0 * t + S 0 1| ≤ |S 0 0 * t| + |S 0 1| := abs_add_le _ _
      have h2 : |S 0 0 * t| = |S 0 0| * t := by rw [abs_mul, abs_of_pos htpos]
      have h3 : |S 0 1| ≤ |S 0 1| * t := le_mul_of_one_le_right (abs_nonneg _) ht1
      nlinarith [h1, h2, h3]
    have hlow : |S 1 0| * t / 2 ≤ |S 1 0 * t + S 1 1| := by
      have h1 : |S 1 0 * t| ≤ |S 1 0 * t + S 1 1| + |S 1 1| := by
        have h := abs_add_le (S 1 0 * t + S 1 1) (-(S 1 1))
        simp only [add_neg_cancel_right, abs_neg] at h
        exact h
      have h2 : |S 1 0 * t| = |S 1 0| * t := by rw [abs_mul, abs_of_pos htpos]
      linarith [h1, h2, hTt]
    have hlowpos : 0 < |S 1 0 * t + S 1 1| := by
      have h4 : 0 < |S 1 0| * t / 2 := by positivity
      linarith
    rw [hnorm t, div_le_iff₀ hlowpos]
    have hCnn : 0 ≤ C := by
      rw [hCdef]
      positivity
    have hmid : (|S 0 0| + |S 0 1|) * t = C * (|S 1 0| * t / 2) := by
      rw [hCdef]
      field_simp
    calc |S 0 0 * t + S 0 1| ≤ (|S 0 0| + |S 0 1|) * t := hup
      _ = C * (|S 1 0| * t / 2) := hmid
      _ ≤ C * |S 1 0 * t + S 1 1| := mul_le_mul_of_nonneg_left hlow hCnn
  have hKc : IsCompact (⇑Λ.symm '' Metric.closedBall (0 : ℂ) C) :=
    (isCompact_closedBall _ _).image Λ.symm.continuous
  obtain ⟨M', hM'⟩ := hKc.isBounded.subset_closedBall 0
  set t0 := max (max T 1) (max M M') + 1 with ht0def
  have ht0T : max T 1 ≤ t0 := by
    rw [ht0def]
    linarith [le_max_left (max T 1) (max M M')]
  have ht0M : M < t0 := by
    rw [ht0def]
    linarith [le_max_left M M', le_max_right (max T 1) (max M M')]
  have ht0M' : M' < t0 := by
    rw [ht0def]
    linarith [le_max_right M M', le_max_right (max T 1) (max M M')]
  have hgood : t0 ∉ B := fun hmem => absurd (hM hmem) (not_le.mpr ht0M)
  have hmem : Λ ((t0 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) C := by
    rw [mem_closedBall_zero_iff, hEq t0 hgood]
    exact hbound t0 ht0T
  have himg : ((t0 : ℝ) : ℂ) ∈ ⇑Λ.symm '' Metric.closedBall (0 : ℂ) C :=
    ⟨Λ ((t0 : ℝ) : ℂ), hmem, Λ.symm_apply_apply _⟩
  have hnrm : ‖((t0 : ℝ) : ℂ)‖ ≤ M' := by
    have h := hM' himg
    rwa [mem_closedBall_zero_iff] at h
  rw [Complex.norm_real, Real.norm_eq_abs] at hnrm
  have hle : t0 ≤ M' := le_trans (le_abs_self t0) hnrm
  linarith

/-- A continuous plane map that fixes `0` and `1` and agrees on the real line off a
subsingleton with an affine real Möbius map fixes the whole real line. -/
theorem homeo_fix_real {Λ : ℂ → ℂ} (hΛc : Continuous Λ)
    (S : Matrix.SpecialLinearGroup (Fin 2) ℝ) {B : Set ℝ} (hB : B.Subsingleton)
    (hc : S 1 0 = 0) (hEq : ∀ t : ℝ, t ∉ B → Λ (t : ℂ) = moebiusMap S (t : ℂ))
    (h0 : Λ 0 = 0) (h1 : Λ 1 = 1) : ∀ t : ℝ, Λ (t : ℂ) = (t : ℂ) := by
  have hdet : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe S
    rwa [Matrix.det_fin_two] at h
  have hd : S 1 1 ≠ 0 := by
    intro h0'
    rw [hc, h0'] at hdet
    simp at hdet
  have hdC : ((S 1 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hval : ∀ s : ℝ, moebiusMap S (s : ℂ)
      = ((S 0 0 : ℂ) * (s : ℂ) + (S 0 1 : ℂ)) / (S 1 1 : ℂ) := by
    intro s
    simp only [moebiusMap, moebiusDenom, hc, Complex.ofReal_zero, zero_mul, zero_add]
  have hdense : Dense Bᶜ := by
    rcases hB.eq_empty_or_singleton with hB0 | ⟨p, hp⟩
    · rw [hB0, Set.compl_empty]
      exact dense_univ
    · rw [hp]
      exact dense_compl_singleton p
  have hf1 : Continuous fun s : ℝ => Λ (s : ℂ) := hΛc.comp Complex.continuous_ofReal
  have hf2 : Continuous fun s : ℝ => moebiusMap S (s : ℂ) := by
    have heq : (fun s : ℝ => moebiusMap S (s : ℂ))
        = fun s : ℝ => ((S 0 0 : ℂ) * (s : ℂ) + (S 0 1 : ℂ)) / (S 1 1 : ℂ) :=
      funext hval
    rw [heq]
    exact ((continuous_const.mul Complex.continuous_ofReal).add continuous_const).div_const _
  have hext : (fun s : ℝ => Λ (s : ℂ)) = fun s : ℝ => moebiusMap S (s : ℂ) :=
    Continuous.ext_on hdense hf1 hf2 fun s hs => hEq s hs
  have hall : ∀ s : ℝ, Λ (s : ℂ) = ((S 0 0 : ℂ) * (s : ℂ) + (S 0 1 : ℂ)) / (S 1 1 : ℂ) :=
    fun s => (congrFun hext s).trans (hval s)
  have hb0 : ((S 0 1 : ℝ) : ℂ) = 0 := by
    have h := hall 0
    rw [Complex.ofReal_zero, h0, mul_zero, zero_add] at h
    rcases div_eq_zero_iff.mp h.symm with h' | h'
    · exact h'
    · exact absurd h' hdC
  have ha : ((S 0 0 : ℝ) : ℂ) = ((S 1 1 : ℝ) : ℂ) := by
    have h := hall 1
    rw [Complex.ofReal_one, h1, mul_one, hb0, add_zero] at h
    have h2 := (eq_div_iff hdC).mp h
    rw [one_mul] at h2
    exact h2.symm
  intro t
  rw [hall t, hb0, add_zero, ha, mul_comm ((S 1 1 : ℝ) : ℂ) ((t : ℝ) : ℂ), mul_div_assoc,
    div_self hdC, mul_one]

/-- The Möbius endgame: a plane self-homeomorphism fixing `0` and `1` whose restriction to
the upper half plane is a Möbius conjugate of a continuous real-fixing map fixes the real
line pointwise. -/
theorem upper_factor_fix_real (Λ : ℂ ≃ₜ ℂ) {φ : ℂ → ℂ} (hφc : Continuous φ)
    (hφr : ∀ r : ℝ, φ (r : ℂ) = (r : ℂ)) (Rx Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hint : ∀ ζ : ℂ, 0 < ζ.im → Λ ζ = moebiusMap Rx (φ (moebiusMap Ry⁻¹ ζ)))
    (h0 : Λ 0 = 0) (h1 : Λ 1 = 1) : ∀ t : ℝ, Λ (t : ℂ) = (t : ℂ) := by
  classical
  set B1 : Set ℝ := {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) = 0} with hB1def
  set B2 : Set ℝ := {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0
    ∧ moebiusDenom Rx (moebiusMap Ry⁻¹ (s : ℂ)) = 0} with hB2def
  have hB1sub : B1.Subsingleton := by
    intro t₁ h₁ t₂ h₂
    have h₁' : moebiusDenom Ry⁻¹ ((t₁ : ℝ) : ℂ) = 0 := h₁
    have h₂' : moebiusDenom Ry⁻¹ ((t₂ : ℝ) : ℂ) = 0 := h₂
    have h := moebiusDenom_zero_subsingleton Ry⁻¹ h₁' h₂'
    exact_mod_cast h
  have hback : ∀ s : ℝ, moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 →
      moebiusMap Ry (moebiusMap Ry⁻¹ (s : ℂ)) = (s : ℂ) := by
    intro s hs
    rw [moebiusMap_mul Ry Ry⁻¹ _ hs, mul_inv_cancel, moebiusMap_one]
  have hB2sub : B2.Subsingleton := by
    intro t₁ h₁ t₂ h₂
    obtain ⟨h₁a, h₁b⟩ := h₁
    obtain ⟨h₂a, h₂b⟩ := h₂
    have h₁b' : moebiusDenom Rx (moebiusMap Ry⁻¹ ((t₁ : ℝ) : ℂ)) = 0 := h₁b
    have h₂b' : moebiusDenom Rx (moebiusMap Ry⁻¹ ((t₂ : ℝ) : ℂ)) = 0 := h₂b
    have hw := moebiusDenom_zero_subsingleton Rx h₁b' h₂b'
    have h := hback t₁ h₁a
    rw [hw, hback t₂ h₂a] at h
    exact_mod_cast h.symm
  have hEqGood : ∀ s : ℝ, s ∉ B1 ∪ B2 → Λ (s : ℂ) = moebiusMap (Rx * Ry⁻¹) (s : ℂ) := by
    intro s hs
    have hd1 : moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 := fun h => hs (Set.mem_union_left _ h)
    have hd2 : moebiusDenom Rx (moebiusMap Ry⁻¹ (s : ℂ)) ≠ 0 := fun h =>
      hs (Set.mem_union_right _ ⟨hd1, h⟩)
    rw [moebius_boundary Λ.continuous hφc hφr Rx Ry hint hd1 hd2,
      moebiusMap_mul Rx Ry⁻¹ _ hd1]
  have hc0 : (Rx * Ry⁻¹) 1 0 = 0 :=
    sl2_lower_left_eq_zero Λ (Rx * Ry⁻¹) (hB1sub.finite.union hB2sub.finite) hEqGood
  have hdet : (Rx * Ry⁻¹) 0 0 * (Rx * Ry⁻¹) 1 1
      - (Rx * Ry⁻¹) 0 1 * (Rx * Ry⁻¹) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (Rx * Ry⁻¹)
    rwa [Matrix.det_fin_two] at h
  have hd11 : (Rx * Ry⁻¹) 1 1 ≠ 0 := by
    intro h'
    rw [hc0, h'] at hdet
    simp at hdet
  have hEq1 : ∀ s : ℝ, s ∉ B1 → Λ (s : ℂ) = moebiusMap (Rx * Ry⁻¹) (s : ℂ) := by
    intro s hs
    have hd1 : moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 := hs
    have hSden : moebiusDenom (Rx * Ry⁻¹) (s : ℂ) ≠ 0 := by
      simp only [moebiusDenom, hc0, Complex.ofReal_zero, zero_mul, zero_add]
      exact Complex.ofReal_ne_zero.mpr hd11
    have hprod : moebiusDenom Rx (moebiusMap Ry⁻¹ (s : ℂ))
        * moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 := by
      rw [moebiusDenom_mul Rx Ry⁻¹ _ hd1]
      exact hSden
    have hd2 := left_ne_zero_of_mul hprod
    rw [moebius_boundary Λ.continuous hφc hφr Rx Ry hint hd1 hd2,
      moebiusMap_mul Rx Ry⁻¹ _ hd1]
  exact homeo_fix_real Λ.continuous (Rx * Ry⁻¹) hB1sub hc0 hEq1 h0 h1

/-- Factorization of the re-marked solution: on the upper half plane, the normalized
solution of the re-marked representative is a real Möbius map applied to `x.w ∘ P.g`, as
the two maps solve the same Beltrami equation there. -/
theorem TeichRep.smulUpper_w (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → (x.smulUpper P).w z = moebiusMap R (x.w (P.g z)) := by
  have hv := x.isQCUpper_remark P
  have hκ : (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) < 1 := by
    have ha0 : (0 : ℝ) ≤ max P.κ 0 := le_max_right _ _
    have ha1 : max P.κ 0 < 1 := max_lt P.hκ one_pos
    have hb0 : (0 : ℝ) ≤ x.b.normInf := x.b.normInf_nonneg
    have hb1 : x.b.normInf < 1 := x.b.normInf_lt_one
    have hab : (0 : ℝ) < 1 + max P.κ 0 * x.b.normInf := by nlinarith [mul_nonneg ha0 hb0]
    rw [div_lt_one hab]
    nlinarith [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1)]
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar (x.w ∘ P.g) z = (x.smulUpper P).b.μ z * dz (x.w ∘ P.g) z := by
    filter_upwards [hv.belt, ae_restrict_mem hU] with z hbelt hzU
    have hμ : (x.smulUpper P).b.μ z = wirtingerQuotient (x.w ∘ P.g) z := by
      change symmExtension (wirtingerQuotient (x.w ∘ P.g)) z = wirtingerQuotient (x.w ∘ P.g) z
      simp only [symmExtension]
      rw [if_pos hzU]
    rw [hμ]
    simp only [wirtingerQuotient]
    by_cases hdz : dz (x.w ∘ P.g) z = 0
    · rw [hdz, mul_zero]
      rw [hdz, norm_zero, mul_zero] at hbelt
      exact norm_le_zero_iff.mp hbelt
    · rw [div_mul_cancel₀ _ hdz]
  obtain ⟨R, hR⟩ := exists_sl2_factorization_of_eq_coeff (x.smulUpper P) hκ hv hcoeff
  exact ⟨R, fun z hz => hR z hz⟩

/-- The boundary maps of two re-marked representatives agree when the original boundary
maps agree: the transition homeomorphism is a Möbius conjugate of a real-fixing map on the
upper half plane, hence fixes the real line. -/
theorem smulUpper_boundary_eq (P : ModGroupUpper Γ₀) (x y : TeichRep Γ₀)
    (hb : ∀ t : ℝ, x.w t = y.w t) :
    ∀ t : ℝ, (x.smulUpper P).w t = (y.smulUpper P).w t := by
  obtain ⟨Rx, hRx⟩ := TeichRep.smulUpper_w x P
  obtain ⟨Ry, hRy⟩ := TeichRep.smulUpper_w y P
  have hu11 : IsHomeomorph (x.smulUpper P).w := (x.smulUpper P).w_isQCAnalytic.1.1
  have hv11 : IsHomeomorph (y.smulUpper P).w := (y.smulUpper P).w_isQCAnalytic.1.1
  have hy11 : IsHomeomorph y.w := y.w_isQCAnalytic.1.1
  set Wu : ℂ ≃ₜ ℂ := hu11.homeomorph (x.smulUpper P).w with hWudef
  set Wv : ℂ ≃ₜ ℂ := hv11.homeomorph (y.smulUpper P).w with hWvdef
  set Wy : ℂ ≃ₜ ℂ := hy11.homeomorph y.w with hWydef
  have hWu_app : ∀ w : ℂ, Wu w = (x.smulUpper P).w w := by
    intro w
    rw [hWudef]
    exact IsHomeomorph.homeomorph_apply _ hu11 w
  have hWv_app : ∀ w : ℂ, Wv w = (y.smulUpper P).w w := by
    intro w
    rw [hWvdef]
    exact IsHomeomorph.homeomorph_apply _ hv11 w
  have hWy_app : ∀ w : ℂ, Wy w = y.w w := by
    intro w
    rw [hWydef]
    exact IsHomeomorph.homeomorph_apply _ hy11 w
  set Λ : ℂ ≃ₜ ℂ := Wv.symm.trans Wu with hΛdef
  have hΛ_app : ∀ w : ℂ, Λ ((y.smulUpper P).w w) = (x.smulUpper P).w w := by
    intro w
    have h1 : Wv.symm ((y.smulUpper P).w w) = w := by
      rw [← hWv_app w]
      exact Wv.symm_apply_apply w
    rw [hΛdef]
    simp only [Homeomorph.trans_apply]
    rw [h1]
    exact hWu_app w
  have hΛ0 : Λ 0 = 0 := by
    have h := hΛ_app 0
    rwa [(y.smulUpper P).w_zero, (x.smulUpper P).w_zero] at h
  have hΛ1 : Λ 1 = 1 := by
    have h := hΛ_app 1
    rwa [(y.smulUpper P).w_one, (x.smulUpper P).w_one] at h
  have hφc : Continuous fun s : ℂ => x.w (Wy.symm s) :=
    (x.w_isQCAnalytic.1.1.continuous).comp Wy.symm.continuous
  have hφr : ∀ r : ℝ, (fun s : ℂ => x.w (Wy.symm s)) (r : ℂ) = (r : ℂ) := by
    intro r
    change x.w (Wy.symm (r : ℂ)) = (r : ℂ)
    have hys : y.w (Wy.symm (r : ℂ)) = (r : ℂ) := by
      rw [← hWy_app]
      exact Wy.apply_symm_apply _
    have hconj : starRingEnd ℂ (Wy.symm (r : ℂ)) = Wy.symm (r : ℂ) := by
      apply y.w_injective
      rw [y.w_conj, hys, Complex.conj_ofReal]
    have him : (Wy.symm (r : ℂ)).im = 0 := Complex.conj_eq_iff_im.mp hconj
    have hre : (((Wy.symm (r : ℂ)).re : ℝ) : ℂ) = Wy.symm (r : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    rw [← hre, hb ((Wy.symm (r : ℂ)).re), hre]
    exact hys
  have hint : ∀ ζ : ℂ, 0 < ζ.im →
      Λ ζ = moebiusMap Rx ((fun s : ℂ => x.w (Wy.symm s)) (moebiusMap Ry⁻¹ ζ)) := by
    intro ζ hζ
    have hvz : (y.smulUpper P).w (Wv.symm ζ) = ζ := by
      rw [← hWv_app (Wv.symm ζ)]
      exact Wv.apply_symm_apply ζ
    have hzpos : 0 < (Wv.symm ζ).im := by
      apply w_im_pos_rev (y.smulUpper P)
      rw [hvz]
      exact hζ
    have hgz : 0 < (P.g (Wv.symm ζ)).im := P.qc.mapsTo _ hzpos
    have hwpos : 0 < (y.w (P.g (Wv.symm ζ))).im := y.w_mapsTo_upper _ hgz
    have hζval : ζ = moebiusMap Ry (y.w (P.g (Wv.symm ζ))) := by
      conv_lhs => rw [← hvz]
      exact hRy _ hzpos
    have hden : moebiusDenom Ry (y.w (P.g (Wv.symm ζ))) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero Ry (ne_of_gt hwpos)
    have hinvζ : moebiusMap Ry⁻¹ ζ = y.w (P.g (Wv.symm ζ)) := by
      conv_lhs => rw [hζval]
      rw [moebiusMap_mul Ry⁻¹ Ry _ hden, inv_mul_cancel, moebiusMap_one]
    have hWyinv : Wy.symm (y.w (P.g (Wv.symm ζ))) = P.g (Wv.symm ζ) := by
      rw [← hWy_app (P.g (Wv.symm ζ))]
      exact Wy.symm_apply_apply _
    have hLHS : Λ ζ = (x.smulUpper P).w (Wv.symm ζ) := by
      rw [hΛdef]
      simp only [Homeomorph.trans_apply]
      exact hWu_app _
    rw [hLHS, hRx _ hzpos]
    change moebiusMap Rx (x.w (P.g (Wv.symm ζ)))
      = moebiusMap Rx (x.w (Wy.symm (moebiusMap Ry⁻¹ ζ)))
    rw [hinvζ, hWyinv]
  have hfix := upper_factor_fix_real Λ hφc hφr Rx Ry hint hΛ0 hΛ1
  intro t
  have h1 : (x.smulUpper P).w (t : ℂ) = Λ ((y.smulUpper P).w (t : ℂ)) := (hΛ_app _).symm
  rw [h1, (y.smulUpper P).w_ofReal t]
  exact hfix ((y.smulUpper P).boundary t)

/-- Re-marking respects inseparability of representatives. -/
theorem smulUpper_mk_congr (P : ModGroupUpper Γ₀) :
    ∀ x y : TeichRep Γ₀, Inseparable x y →
      (Teich.mk (x.smulUpper P) : Teich Γ₀) = Teich.mk (y.smulUpper P) := by
  intro x y hxy
  exact Teich.mk_eq_mk_iff_boundary.mpr
    (smulUpper_boundary_eq P x y (inseparable_iff_boundary_eq.mp hxy))

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

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Bergman

/-!
# The Poincaré theta series of the quartic kernel

For a point `z` of the lower half plane, the Poincaré series of the kernel
`ζ ↦ (ζ − z)⁻⁴` over a cocompact free Fuchsian group converges to an integrable
holomorphic weight-4 automorphic form, and unfolding turns the pairing of an invariant
coefficient with the kernel over the upper half plane into its Hamilton pairing with the
theta series over the Dirichlet domain. Consequently a coefficient annihilating every
integrable quadratic differential annihilates the quartic kernel at every point of the
lower half plane — the kernel step of the variational lemma.

* `exists_theta_qd` — the theta series as a quadratic differential, with the unfolding
  identity.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **The theta series of the quartic kernel**: for `z` in the lower half plane there is
an integrable quadratic differential `Θ` whose Hamilton pairing with any bounded
invariant coefficient computes the pairing of the coefficient with the kernel
`(ζ − z)⁻⁴` over the whole upper half plane. -/
theorem exists_theta_qd (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {z : ℂ} (hz : z.im < 0) :
    ∃ Θ : QuadraticDifferential Γ, Θ.l1Norm ≠ ⊤ ∧
      ∀ (κ : ℂ → ℂ) (M : ℝ), Measurable κ → (∀ w : ℂ, ‖κ w‖ ≤ M) →
        (∀ W ∈ Γ, ∀ᵐ w ∂(volume.restrict {w : ℂ | 0 < w.im}),
          κ (moebiusMap W w) * (moebiusDenom W w) ^ 2
            = κ w * (starRingEnd ℂ (moebiusDenom W w)) ^ 2) →
        (∫ ζ in {ζ : ℂ | 0 < ζ.im}, κ ζ / (ζ - z) ^ 4) = qdPairing κ Θ := by
  classical
  have hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  have : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  -- ## Ambient sets
  set U : Set ℂ := {ζ : ℂ | 0 < ζ.im} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  set Dh : Set UpperHalfPlane := dirichletDomain Γ UpperHalfPlane.I with hDh
  have hDhc : IsCompact Dh := isCompact_dirichletDomain hdense
  set Ih : Set UpperHalfPlane := interior Dh with hIh
  have hIhopen : IsOpen Ih := isOpen_interior
  set Dpl : Set ℂ := UpperHalfPlane.coe '' Dh with hDpl
  have hDplc : IsCompact Dpl := hDhc.image UpperHalfPlane.continuous_coe
  have hDplmeas : MeasurableSet Dpl := hDplc.measurableSet
  have hDplsub : Dpl ⊆ U := by
    rintro w ⟨τ, -, rfl⟩
    simpa using! τ.im_pos
  set Opl : Set ℂ := UpperHalfPlane.coe '' Ih with hOpl
  have hOplopen : IsOpen Opl :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hIhopen
  have hOplsubD : Opl ⊆ Dpl := Set.image_mono interior_subset
  have hOplsub : Opl ⊆ U := hOplsubD.trans hDplsub
  set Fpl : Set ℂ := Dpl \ Opl with hFpl
  have hFplmeas : MeasurableSet Fpl := hDplmeas.diff hOplopen.measurableSet
  have hFplsub : Fpl ⊆ U := fun w hw => hDplsub hw.1
  -- ## The frontier of the Dirichlet tile is plane-null
  have hDhclosed : IsClosed Dh := isClosed_dirichletDomain Γ UpperHalfPlane.I
  have hFplnull : volume Fpl = 0 := by
    have hfr := frontier_dirichletDomain_subset hΓ hdense
    rw [← hDh] at hfr
    have hbis : ∀ γ : ↥Γ, γ ∈ activeSides Γ UpperHalfPlane.I R →
        ∃ S : Set ℂ, volume S = 0 ∧ ∀ τ : UpperHalfPlane,
          dist τ UpperHalfPlane.I = dist τ (γ • UpperHalfPlane.I) → (τ : ℂ) ∈ S :=
      fun γ hγ => exists_null_carrier_bisector UpperHalfPlane.I (γ • UpperHalfPlane.I)
        (Ne.symm hγ.2)
    choose! S hS0 hSmem using hbis
    have hsub : Fpl ⊆ ⋃ γ ∈ activeSides Γ UpperHalfPlane.I R, S γ := by
      rintro w hw
      obtain ⟨τ, hτD, rfl⟩ := hw.1
      have hτni : τ ∉ Ih := fun hin =>
        hw.2 (Set.mem_image_of_mem UpperHalfPlane.coe hin)
      have hτfr : τ ∈ frontier Dh := by
        rw [hDhclosed.frontier_eq]
        exact ⟨hτD, fun hin => hτni (hIh.symm ▸ hin)⟩
      obtain ⟨γ, hγact, hγmem⟩ := Set.mem_iUnion₂.mp (hfr hτfr)
      exact Set.mem_biUnion hγact (hSmem γ hγact τ hγmem)
    refine measure_mono_null hsub ?_
    rw [measure_biUnion_null_iff (finite_activeSides hΓ UpperHalfPlane.I R).countable]
    exact fun γ hγ => hS0 γ hγ
  -- ## The kernel and the terms of the theta series
  set k₀ : ℂ → ℂ := fun ζ => ((ζ - z) ^ 4)⁻¹ with hk₀def
  set trm : Matrix.SpecialLinearGroup (Fin 2) ℝ → ℂ → ℂ :=
    fun γ ζ => ((moebiusDenom γ ζ) ^ 4)⁻¹ * ((moebiusMap γ ζ - z) ^ 4)⁻¹ with htrmdef
  have hne : ∀ ζ : ℂ, 0 < ζ.im → ζ - z ≠ 0 := by
    intro ζ hζ h
    have h2 : (ζ - z).im = 0 := by rw [h]; simp
    rw [Complex.sub_im] at h2
    linarith
  have hdne : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ζ : ℂ), 0 < ζ.im →
      moebiusDenom γ ζ ≠ 0 := fun γ ζ hζ => moebiusDenom_ne_zero_of_im_ne_zero γ hζ.ne'
  have hk₀meas : Measurable k₀ := ((measurable_id.sub_const z).pow_const 4).inv
  have hmoebmeas : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, Measurable (moebiusMap γ) := by
    intro γ
    unfold moebiusMap moebiusDenom
    fun_prop
  have hdenommeas : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      Measurable (moebiusDenom γ) := by
    intro γ
    unfold moebiusDenom
    fun_prop
  have htrmmeas : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, Measurable (trm γ) :=
    fun γ => (((hdenommeas γ).pow_const 4).inv).mul
      ((((hmoebmeas γ).sub_const z).pow_const 4).inv)
  have htrmholo : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      DifferentiableOn ℂ (trm γ) U := by
    intro γ ζ hζ
    have hζ' : (0 : ℝ) < ζ.im := hζ
    have hd1 : DifferentiableAt ℂ (fun w => moebiusDenom γ w) ζ := by
      unfold moebiusDenom
      fun_prop
    have hd2 : DifferentiableAt ℂ (moebiusMap γ) ζ :=
      (hasDerivAt_moebiusMap_of_im_pos γ hζ').differentiableAt
    exact (((hd1.pow 4).inv (pow_ne_zero 4 (hdne γ ζ hζ'))).mul
      (((hd2.sub_const z).pow 4).inv
        (pow_ne_zero 4 (hne _ (moebiusMap_im_pos γ hζ'))))).differentiableWithinAt
  -- ## Change of variables, lintegral and Bochner forms
  have hCOV : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℂ),
      MeasurableSet S → S ⊆ U → ∀ g : ℂ → ℝ≥0∞,
      ∫⁻ w in moebiusMap γ '' S, g w
        = ∫⁻ ζ in S, ENNReal.ofReal ((‖moebiusDenom γ ζ‖ ^ 4)⁻¹) * g (moebiusMap γ ζ) := by
    intro γ S hSmeas hSsub g
    have hfd : ∀ ζ ∈ S, HasFDerivWithinAt (moebiusMap γ) (fderiv ℝ (moebiusMap γ) ζ) S ζ := by
      intro ζ hζS
      have hd : moebiusDenom γ ζ ≠ 0 := hdne γ ζ (hSsub hζS)
      exact (((hasDerivAt_moebiusMap γ hd).complexToReal_fderiv).differentiableAt.hasFDerivAt
        ).hasFDerivWithinAt
    have hinj : Set.InjOn (moebiusMap γ) S := by
      intro x hx y hy hxy
      have hdx : moebiusDenom γ x ≠ 0 := hdne γ x (hSsub hx)
      have hdy : moebiusDenom γ y ≠ 0 := hdne γ y (hSsub hy)
      have h1 : moebiusMap γ⁻¹ (moebiusMap γ x) = x := by
        rw [moebiusMap_mul γ⁻¹ γ x hdx, inv_mul_cancel, moebiusMap_one]
      have h2 : moebiusMap γ⁻¹ (moebiusMap γ y) = y := by
        rw [moebiusMap_mul γ⁻¹ γ y hdy, inv_mul_cancel, moebiusMap_one]
      rw [← h1, ← h2, hxy]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinj g]
    refine setLIntegral_congr_fun hSmeas (fun ζ hζS => ?_)
    rw [det_fderiv_moebiusMap_of_im_pos γ (hSsub hζS), abs_of_nonneg (by positivity)]
  have hCOVB : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℂ),
      MeasurableSet S → S ⊆ U → ∀ g : ℂ → ℂ,
      ∫ w in moebiusMap γ '' S, g w
        = ∫ ζ in S, ((‖moebiusDenom γ ζ‖ ^ 4)⁻¹) • g (moebiusMap γ ζ) := by
    intro γ S hSmeas hSsub g
    have hfd : ∀ ζ ∈ S, HasFDerivWithinAt (moebiusMap γ) (fderiv ℝ (moebiusMap γ) ζ) S ζ := by
      intro ζ hζS
      have hd : moebiusDenom γ ζ ≠ 0 := hdne γ ζ (hSsub hζS)
      exact (((hasDerivAt_moebiusMap γ hd).complexToReal_fderiv).differentiableAt.hasFDerivAt
        ).hasFDerivWithinAt
    have hinj : Set.InjOn (moebiusMap γ) S := by
      intro x hx y hy hxy
      have hdx : moebiusDenom γ x ≠ 0 := hdne γ x (hSsub hx)
      have hdy : moebiusDenom γ y ≠ 0 := hdne γ y (hSsub hy)
      have h1 : moebiusMap γ⁻¹ (moebiusMap γ x) = x := by
        rw [moebiusMap_mul γ⁻¹ γ x hdx, inv_mul_cancel, moebiusMap_one]
      have h2 : moebiusMap γ⁻¹ (moebiusMap γ y) = y := by
        rw [moebiusMap_mul γ⁻¹ γ y hdy, inv_mul_cancel, moebiusMap_one]
      rw [← h1, ← h2, hxy]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume hSmeas hfd hinj g]
    refine setIntegral_congr_fun hSmeas (fun ζ hζS => ?_)
    rw [det_fderiv_moebiusMap_of_im_pos γ (hSsub hζS), abs_of_nonneg (by positivity)]
  have hnullimg : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℂ),
      MeasurableSet S → S ⊆ U → volume S = 0 → volume (moebiusMap γ '' S) = 0 := by
    intro γ S hm hs h0
    have h1 := hCOV γ S hm hs (fun _ => (1 : ℝ≥0∞))
    simp only [mul_one] at h1
    rw [setLIntegral_one] at h1
    rw [h1, Measure.restrict_eq_zero.mpr h0]
    simp
  -- ## Integrability of the kernel over the upper half plane
  have hKKne : (∫⁻ ζ in U, ‖k₀ ζ‖ₑ) ≠ ⊤ := by
    set d : ℝ := -z.im with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have hdist : ∀ ζ : ℂ, 0 < ζ.im → d ≤ ‖ζ - z‖ := by
      intro ζ hζ
      have h1 : d ≤ (ζ - z).im := by rw [Complex.sub_im, hd]; linarith
      exact h1.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
    have hjap : Integrable (fun w : ℂ => (1 + ‖w‖) ^ (-(4 : ℝ))) := by
      refine integrable_one_add_norm ?_
      rw [Complex.finrank_real_complex]
      norm_num
    have htrans : Integrable (fun ζ : ℂ => (1 + ‖ζ - z‖) ^ (-(4 : ℝ))) :=
      hjap.comp_sub_right z
    have hfin1 : (∫⁻ ζ : ℂ, ‖(1 + ‖ζ - z‖) ^ (-(4 : ℝ))‖ₑ) ≠ ⊤ := by
      have h2 := htrans.2
      rw [hasFiniteIntegral_iff_enorm] at h2
      exact h2.ne
    set C : ℝ≥0∞ := ENNReal.ofReal ((1 + d⁻¹) ^ 4) with hC
    have hbound : ∀ ζ ∈ U, ‖k₀ ζ‖ₑ ≤ C * ‖(1 + ‖ζ - z‖) ^ (-(4 : ℝ))‖ₑ := by
      intro ζ hζ
      have hζ' : (0 : ℝ) < ζ.im := hζ
      have ht0 : 0 < ‖ζ - z‖ := lt_of_lt_of_le hd0 (hdist ζ hζ')
      have hrp : (1 + ‖ζ - z‖) ^ (-(4 : ℝ)) = ((1 + ‖ζ - z‖) ^ (4 : ℕ))⁻¹ := by
        rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
          Real.rpow_natCast]
      have h4 : (1 + ‖ζ - z‖) ^ (4 : ℕ) ≤ (1 + d⁻¹) ^ 4 * ‖ζ - z‖ ^ 4 := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ 4
        have h5 : 1 ≤ ‖ζ - z‖ * d⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hd0, one_mul]
          exact hdist ζ hζ'
        calc 1 + ‖ζ - z‖ ≤ ‖ζ - z‖ * d⁻¹ + ‖ζ - z‖ := by linarith
          _ = (1 + d⁻¹) * ‖ζ - z‖ := by ring
      have h6 : (‖ζ - z‖ ^ 4)⁻¹ ≤ (1 + d⁻¹) ^ 4 * ((1 + ‖ζ - z‖) ^ (4 : ℕ))⁻¹ := by
        have h5 : ((1 + d⁻¹) ^ 4 * ‖ζ - z‖ ^ 4)⁻¹ ≤ ((1 + ‖ζ - z‖) ^ (4 : ℕ))⁻¹ := by
          exact inv_anti₀ (by positivity) h4
        have h7 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ (1 + d⁻¹) ^ 4)
        rwa [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h7
      have hnk : ‖k₀ ζ‖ = (‖ζ - z‖ ^ 4)⁻¹ := by
        simp only [hk₀def]
        rw [norm_inv, norm_pow]
      rw [← ofReal_norm, hnk, Real.enorm_eq_ofReal (by positivity), hC,
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hrp]
      exact h6
    have hchain : (∫⁻ ζ in U, ‖k₀ ζ‖ₑ)
        ≤ C * ∫⁻ ζ : ℂ, ‖(1 + ‖ζ - z‖) ^ (-(4 : ℝ))‖ₑ := by
      calc (∫⁻ ζ in U, ‖k₀ ζ‖ₑ)
          ≤ ∫⁻ ζ in U, C * ‖(1 + ‖ζ - z‖) ^ (-(4 : ℝ))‖ₑ :=
            setLIntegral_mono' hUmeas hbound
        _ = C * ∫⁻ ζ in U, ‖(1 + ‖ζ - z‖) ^ (-(4 : ℝ))‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ C * ∫⁻ ζ : ℂ, ‖(1 + ‖ζ - z‖) ^ (-(4 : ℝ))‖ₑ :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin1) hchain
  -- ## The trivially acting elements and the covering multiplicity
  set T : Set ↥Γ := {σ : ↥Γ | ∀ τ : UpperHalfPlane, σ • τ = τ} with hT
  have hTfin : T.Finite := by
    have hfin : {σ : ↥Γ | ((fun x => σ • x) '' {UpperHalfPlane.I} ∩
        {UpperHalfPlane.I}).Nonempty}.Finite :=
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
        isCompact_singleton
    refine hfin.subset fun σ hσ => ?_
    exact ⟨UpperHalfPlane.I, ⟨UpperHalfPlane.I, rfl, hσ UpperHalfPlane.I⟩, rfl⟩
  have h1T : (1 : ↥Γ) ∈ T := fun τ => one_smul _ τ
  set m : ℕ := hTfin.toFinset.card with hm
  have hm0 : m ≠ 0 := by
    rw [hm, ← Nat.pos_iff_ne_zero, Finset.card_pos, hTfin.toFinset_nonempty]
    exact ⟨1, h1T⟩
  have himg : ∀ (γ : ↥Γ) (s : Set UpperHalfPlane),
      moebiusMap (↑γ) '' (UpperHalfPlane.coe '' s)
        = UpperHalfPlane.coe '' ((γ • ·) '' s) := by
    intro γ s
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun τ _ => ?_
    rw [Subgroup.smul_def]
    exact (coe_smul_eq_moebiusMap (↑γ) τ).symm
  have htrans_open : ∀ γ : ↥Γ,
      IsOpen (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl) := by
    intro γ
    rw [hOpl, himg]
    refine UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ?_
    have h1 : ((γ • ·) '' Ih) = (γ⁻¹ • ·) ⁻¹' Ih := by
      ext τ
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        simpa [inv_smul_smul] using hσ
      · intro hτ
        exact ⟨γ⁻¹ • τ, hτ, smul_inv_smul γ τ⟩
    rw [h1]
    exact (isometry_smul UpperHalfPlane (γ⁻¹ : ↥Γ)).continuous.isOpen_preimage _ hIhopen
  have htrans_subU : ∀ γ : ↥Γ,
      moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl ⊆ U := by
    rintro γ w ⟨ζ, hζ, rfl⟩
    exact moebiusMap_im_pos _ (hOplsub hζ)
  have hcoset : ∀ γ δ : ↥Γ, (((γ • ·) '' Ih) ∩ ((δ • ·) '' Ih)).Nonempty →
      γ⁻¹ * δ ∈ T := by
    intro γ δ hnon
    obtain ⟨x, ⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ := hnon
    have hab : a = (γ⁻¹ * δ) • b := by
      have h1 : γ • a = δ • b := hax.trans hbx.symm
      calc a = γ⁻¹ • (γ • a) := (inv_smul_smul γ a).symm
        _ = γ⁻¹ • (δ • b) := by rw [h1]
        _ = (γ⁻¹ * δ) • b := (mul_smul γ⁻¹ δ b).symm
    have hfix : (γ⁻¹ * δ) • UpperHalfPlane.I = UpperHalfPlane.I := by
      by_contra hmove
      have hdisj := disjoint_smul_interior_dirichletDomain hΓ hdense hmove
      rw [← hDh, ← hIh, Set.disjoint_left] at hdisj
      exact hdisj ha ⟨b, hb, hab.symm⟩
    exact fun τ' => hfree (γ⁻¹ * δ) ⟨UpperHalfPlane.I, hfix⟩ τ'
  have hshift : ∀ (γ σ : ↥Γ), σ ∈ T → ((γ * σ) • ·) '' Ih = (γ • ·) '' Ih := by
    intro γ σ hσ
    refine Set.image_congr fun τ _ => ?_
    rw [mul_smul, hσ τ]
  have hfib : ∀ (M' : Type) [AddCommMonoid M'] [TopologicalSpace M'] [T2Space M'],
      ∀ (c : ℂ → M') (ζ : ℂ) (γ₀ : ↥Γ),
      ζ ∈ moebiusMap (↑γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl →
      (∑' γ : ↥Γ, (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        '' Opl).indicator c ζ) = m • c ζ := by
    intro M' _ _ _ c ζ γ₀ hγ₀
    have hmem_iff : ∀ γ : ↥Γ,
        ζ ∈ moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl ↔
        γ ∈ Finset.image (fun σ => γ₀ * σ) hTfin.toFinset := by
      intro γ
      constructor
      · intro hγ
        rw [Finset.mem_image]
        refine ⟨γ₀⁻¹ * γ, ?_, by rw [mul_inv_cancel_left]⟩
        rw [Set.Finite.mem_toFinset]
        refine hcoset γ₀ γ ?_
        rw [hOpl, himg] at hγ hγ₀
        obtain ⟨a, ha, hac⟩ := hγ₀
        obtain ⟨b, hb, hbc⟩ := hγ
        have hba : b = a := UpperHalfPlane.ext (hbc.trans hac.symm)
        exact ⟨a, ha, hba ▸ hb⟩
      · intro hγ
        rw [Finset.mem_image] at hγ
        obtain ⟨σ, hσ, rfl⟩ := hγ
        rw [Set.Finite.mem_toFinset] at hσ
        rw [hOpl, himg, hshift γ₀ σ hσ, ← himg, ← hOpl]
        exact hγ₀
    rw [tsum_eq_sum (s := Finset.image (fun σ => γ₀ * σ) hTfin.toFinset)
      (fun γ hγ => Set.indicator_of_notMem (fun hmem => hγ ((hmem_iff γ).mp hmem)) c)]
    rw [Finset.sum_congr rfl fun γ hγ => Set.indicator_of_mem ((hmem_iff γ).mpr hγ) c]
    rw [Finset.sum_const, Finset.card_image_of_injective _ (mul_right_injective γ₀), hm]
  -- ## The null bad set and the exact covering
  set Bad : Set ℂ := ⋃ γ : ↥Γ, moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    '' Fpl with hBad
  have hBadnull : volume Bad = 0 :=
    measure_iUnion_null fun γ => hnullimg _ Fpl hFplmeas hFplsub hFplnull
  have hcov : ∀ ζ : ℂ, 0 < ζ.im → ζ ∉ Bad →
      ∃ γ₀ : ↥Γ, ζ ∈ moebiusMap (↑γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl := by
    intro ζ hζ hB
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ UpperHalfPlane.I ⟨ζ, hζ⟩
    rw [← hDh] at hγ
    by_cases hint : γ • (⟨ζ, hζ⟩ : UpperHalfPlane) ∈ Ih
    · refine ⟨γ⁻¹, ?_⟩
      rw [hOpl, himg]
      have h5 : γ⁻¹ • (γ • (⟨ζ, hζ⟩ : UpperHalfPlane)) = ⟨ζ, hζ⟩ := inv_smul_smul γ _
      have h1 : γ⁻¹ • (γ • (⟨ζ, hζ⟩ : UpperHalfPlane)) ∈ (γ⁻¹ • ·) '' Ih :=
        Set.mem_image_of_mem _ hint
      rw [h5] at h1
      exact ⟨⟨ζ, hζ⟩, h1, rfl⟩
    · exfalso
      apply hB
      rw [hBad]
      refine Set.mem_iUnion.mpr ⟨γ⁻¹, ?_⟩
      have hmem : ((γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ Fpl := by
        rw [hFpl, hDpl]
        refine ⟨Set.mem_image_of_mem UpperHalfPlane.coe hγ, ?_⟩
        rintro ⟨τ', hτ', hcoe⟩
        exact hint ((UpperHalfPlane.ext hcoe : τ' = _) ▸ hτ')
      refine ⟨_, hmem, ?_⟩
      have h2 : moebiusMap (↑(γ⁻¹ : ↥Γ)) ((γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
          = ((γ⁻¹ • (γ • (⟨ζ, hζ⟩ : UpperHalfPlane)) : UpperHalfPlane) : ℂ) := by
        rw [Subgroup.smul_def γ⁻¹]
        exact (coe_smul_eq_moebiusMap _ _).symm
      rw [h2, inv_smul_smul]
  -- ## The tiling mass identities
  have haeset : ∀ γ : ↥Γ,
      (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl : Set ℂ)
        =ᵐ[volume] moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl := by
    intro γ
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (fun w hw => ?_)
        (hnullimg (↑γ) Fpl hFplmeas hFplsub hFplnull)
      obtain ⟨hw1, hw2⟩ := hw
      obtain ⟨x, hx, rfl⟩ := hw1
      exact ⟨x, ⟨hx, fun hxO => hw2 ⟨x, hxO, rfl⟩⟩, rfl⟩
    · have hempty : moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl
          \ moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl = ∅ := by
        rw [Set.sdiff_eq_empty]
        exact Set.image_mono hOplsubD
      rw [hempty, measure_empty]
  have hpt : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ζ : ℂ), 0 < ζ.im →
      ENNReal.ofReal ((‖moebiusDenom γ ζ‖ ^ 4)⁻¹) * ‖k₀ (moebiusMap γ ζ)‖ₑ
        = ‖trm γ ζ‖ₑ := by
    intro γ ζ hζ
    simp only [htrmdef, hk₀def]
    rw [enorm_mul, ← ofReal_norm ((moebiusDenom γ ζ ^ 4)⁻¹), norm_inv, norm_pow]
  have htileA : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∫⁻ w in moebiusMap γ '' Dpl, ‖k₀ w‖ₑ) = ∫⁻ ζ in Dpl, ‖trm γ ζ‖ₑ := by
    intro γ
    rw [hCOV γ Dpl hDplmeas hDplsub]
    exact setLIntegral_congr_fun hDplmeas fun ζ hζ => hpt γ ζ (hDplsub hζ)
  have htile : ∀ γ : ↥Γ, (∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ)
      = ∫⁻ w in moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl, ‖k₀ w‖ₑ := by
    intro γ
    rw [← htileA, setLIntegral_congr (haeset γ)]
  have hStot : (∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ)
      ≤ (m : ℝ≥0∞) * ∫⁻ ζ in U, ‖k₀ ζ‖ₑ := by
    have h1 : ∀ γ : ↥Γ, (∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ)
        = ∫⁻ ζ in U, (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          '' Opl).indicator (fun w => ‖k₀ w‖ₑ) ζ := by
      intro γ
      rw [htile γ, setLIntegral_indicator (htrans_open γ).measurableSet,
        Set.inter_eq_self_of_subset_left (htrans_subU γ)]
    rw [tsum_congr h1, ← lintegral_tsum fun γ =>
      ((hk₀meas.enorm).indicator (htrans_open γ).measurableSet).aemeasurable]
    calc (∫⁻ ζ in U, ∑' γ : ↥Γ, (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          '' Opl).indicator (fun w => ‖k₀ w‖ₑ) ζ)
        ≤ ∫⁻ ζ in U, (m : ℝ≥0∞) * ‖k₀ ζ‖ₑ := by
          refine lintegral_mono fun ζ => ?_
          by_cases hc : ∃ γ₀ : ↥Γ,
            ζ ∈ moebiusMap (↑γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl
          · obtain ⟨γ₀, h₀⟩ := hc
            rw [hfib ℝ≥0∞ (fun w => ‖k₀ w‖ₑ) ζ γ₀ h₀, nsmul_eq_mul]
          · push Not at hc
            rw [tsum_congr fun γ => Set.indicator_of_notMem (hc γ) _, tsum_zero]
            exact zero_le
      _ = (m : ℝ≥0∞) * ∫⁻ ζ in U, ‖k₀ ζ‖ₑ :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top m)
  have hStot_ne : (∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hKKne) hStot
  -- ## Mass bound over arbitrary compacts, sup bounds, summability
  have hbiUnion : ∀ (F : Finset ↥Γ) (A : ↥Γ → Set ℂ) (f : ℂ → ℝ≥0∞),
      (∫⁻ ζ in ⋃ δ ∈ F, A δ, f ζ) ≤ ∑ δ ∈ F, ∫⁻ ζ in A δ, f ζ := by
    intro F A f
    induction F using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
        exact le_trans (lintegral_union_le _ _ _) (add_le_add le_rfl ih)
  have hmoebcont : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ContinuousOn (moebiusMap γ) U := fun γ ζ hζ =>
    ((hasDerivAt_moebiusMap_of_im_pos γ hζ).differentiableAt).continuousAt.continuousWithinAt
  have hKmass : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      (∑' γ : ↥Γ, ∫⁻ ζ in K, ‖trm (↑γ) ζ‖ₑ) ≠ ⊤ := by
    intro K hKc hKU
    have hK' : IsCompact (UpperHalfPlane.coe ⁻¹' K) := by
      refine UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage' hKc ?_
      intro w hw
      exact ⟨⟨w, hKU hw⟩, rfl⟩
    have hfin : {δ : ↥Γ | ((fun x => δ • x) '' Dh ∩ UpperHalfPlane.coe ⁻¹' K).Nonempty}.Finite :=
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image hDhc hK'
    have hcover : K ⊆ ⋃ δ ∈ hfin.toFinset,
        moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl := by
      intro w hw
      obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ UpperHalfPlane.I ⟨w, hKU hw⟩
      rw [← hDh] at hγ
      have h5 : γ⁻¹ • (γ • (⟨w, hKU hw⟩ : UpperHalfPlane)) = ⟨w, hKU hw⟩ :=
        inv_smul_smul γ _
      have hmemF : γ⁻¹ ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        have h6 : γ⁻¹ • (γ • (⟨w, hKU hw⟩ : UpperHalfPlane)) ∈ (fun x => γ⁻¹ • x) '' Dh :=
          Set.mem_image_of_mem _ hγ
        rw [h5] at h6
        have h7 : (⟨w, hKU hw⟩ : UpperHalfPlane) ∈ UpperHalfPlane.coe ⁻¹' K := by
          rw [Set.mem_preimage]
          exact hw
        exact ⟨⟨w, hKU hw⟩, h6, h7⟩
      refine Set.mem_biUnion hmemF ?_
      rw [hDpl, himg]
      have h8 : γ⁻¹ • (γ • (⟨w, hKU hw⟩ : UpperHalfPlane)) ∈ (γ⁻¹ • ·) '' Dh :=
        Set.mem_image_of_mem _ hγ
      rw [h5] at h8
      exact ⟨⟨w, hKU hw⟩, h8, rfl⟩
    have hinner : ∀ δ : ↥Γ,
        (∑' γ : ↥Γ, ∫⁻ ζ in moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          '' Dpl, ‖trm (↑γ) ζ‖ₑ) ≤ (m : ℝ≥0∞) * ∫⁻ ζ in U, ‖k₀ ζ‖ₑ := by
      intro δ
      have hDc' : IsCompact (moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl) :=
        hDplc.image_of_continuousOn ((hmoebcont _).mono hDplsub)
      have hDmeas' : MeasurableSet
          (moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl) :=
        hDc'.measurableSet
      have hsubU' : moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl ⊆ U := by
        rintro w ⟨x, hx, rfl⟩
        exact moebiusMap_im_pos _ (hDplsub hx)
      have hstep : ∀ γ : ↥Γ,
          (∫⁻ ζ in moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl,
            ‖trm (↑γ) ζ‖ₑ)
          = ∫⁻ w in moebiusMap ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
              * (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) '' Dpl, ‖k₀ w‖ₑ := by
        intro γ
        have hcompimg : moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            '' (moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl)
            = moebiusMap ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
              * (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) '' Dpl := by
          rw [Set.image_image]
          exact Set.image_congr fun w hw => moebiusMap_mul _ _ w (hdne _ w (hDplsub hw))
        calc (∫⁻ ζ in moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl,
              ‖trm (↑γ) ζ‖ₑ)
            = ∫⁻ ζ in moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl,
              ENNReal.ofReal ((‖moebiusDenom (↑γ) ζ‖ ^ 4)⁻¹)
                * ‖k₀ (moebiusMap (↑γ) ζ)‖ₑ :=
              setLIntegral_congr_fun hDmeas' fun ζ hζ => (hpt (↑γ) ζ (hsubU' hζ)).symm
          _ = ∫⁻ w in moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
                '' (moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl),
              ‖k₀ w‖ₑ := (hCOV (↑γ) _ hDmeas' hsubU' (fun w => ‖k₀ w‖ₑ)).symm
          _ = _ := by rw [hcompimg]
      rw [tsum_congr hstep]
      have hreidx : (∑' γ : ↥Γ, ∫⁻ w in
            moebiusMap ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
              * (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) '' Dpl, ‖k₀ w‖ₑ)
          = ∑' γ' : ↥Γ, ∫⁻ w in
            moebiusMap (↑γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl, ‖k₀ w‖ₑ := by
        have h := (Equiv.mulRight δ).tsum_eq (fun γ' : ↥Γ =>
          ∫⁻ w in moebiusMap (↑γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl, ‖k₀ w‖ₑ)
        simpa only [Equiv.coe_mulRight, Subgroup.coe_mul] using h
      rw [hreidx, tsum_congr fun γ : ↥Γ => htileA (↑γ)]
      exact hStot
    have hle1 : ∀ γ : ↥Γ, (∫⁻ ζ in K, ‖trm (↑γ) ζ‖ₑ)
        ≤ ∑ δ ∈ hfin.toFinset, ∫⁻ ζ in
          moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl, ‖trm (↑γ) ζ‖ₑ :=
      fun γ => (lintegral_mono_set hcover).trans (hbiUnion _ _ _)
    have hchain : (∑' γ : ↥Γ, ∫⁻ ζ in K, ‖trm (↑γ) ζ‖ₑ)
        ≤ hfin.toFinset.card • ((m : ℝ≥0∞) * ∫⁻ ζ in U, ‖k₀ ζ‖ₑ) := by
      calc (∑' γ : ↥Γ, ∫⁻ ζ in K, ‖trm (↑γ) ζ‖ₑ)
          ≤ ∑' γ : ↥Γ, ∑ δ ∈ hfin.toFinset, ∫⁻ ζ in
            moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl, ‖trm (↑γ) ζ‖ₑ :=
            ENNReal.tsum_le_tsum hle1
        _ = ∑ δ ∈ hfin.toFinset, ∑' γ : ↥Γ, ∫⁻ ζ in
            moebiusMap (↑δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl, ‖trm (↑γ) ζ‖ₑ :=
            Summable.tsum_finsetSum fun δ _ => ENNReal.summable
        _ ≤ ∑ _δ ∈ hfin.toFinset, (m : ℝ≥0∞) * ∫⁻ ζ in U, ‖k₀ ζ‖ₑ :=
            Finset.sum_le_sum fun δ _ => hinner δ
        _ = hfin.toFinset.card • ((m : ℝ≥0∞) * ∫⁻ ζ in U, ‖k₀ ζ‖ₑ) := by
            rw [Finset.sum_const]
    refine ne_top_of_le_ne_top ?_ hchain
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hKKne)
  have hMtest : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ u : ↥Γ → ℝ, Summable u ∧ ∀ γ : ↥Γ, ∀ ζ ∈ K, ‖trm (↑γ) ζ‖ ≤ u γ := by
    intro K hKc hKU
    obtain ⟨δ', hδ'0, hδ'sub⟩ := hKc.exists_thickening_subset_open hUopen hKU
    set ρ : ℝ := δ' / 2 with hρ
    have hρ0 : 0 < ρ := by rw [hρ]; linarith
    set K' : Set ℂ := Metric.cthickening ρ K with hK'
    have hK'c : IsCompact K' := hKc.cthickening
    have hK'U : K' ⊆ U :=
      (Metric.cthickening_subset_thickening' hδ'0 (by rw [hρ]; linarith) K).trans hδ'sub
    set c : ℝ≥0∞ := ENNReal.ofReal (Real.pi * ρ ^ 2) with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hfinK' := hKmass K' hK'c hK'U
    refine ⟨fun γ => ((∫⁻ ζ in K', ‖trm (↑γ) ζ‖ₑ) / c).toReal, ?_, ?_⟩
    · refine ENNReal.summable_toReal ?_
      have hEq : (∑' γ : ↥Γ, (∫⁻ ζ in K', ‖trm (↑γ) ζ‖ₑ) / c)
          = (∑' γ : ↥Γ, ∫⁻ ζ in K', ‖trm (↑γ) ζ‖ₑ) / c := by
        simp only [div_eq_mul_inv]
        exact ENNReal.tsum_mul_right
      rw [hEq]
      exact (ENNReal.div_lt_top hfinK' hc0).ne
    · intro γ ζ hζ
      have hball : Metric.closedBall ζ ρ ⊆ K' := Metric.closedBall_subset_cthickening hζ ρ
      have hballU : Metric.closedBall ζ ρ ⊆ U := hball.trans hK'U
      have hf : DifferentiableOn ℂ (trm (↑γ)) (Metric.ball ζ ρ) :=
        (htrmholo (↑γ)).mono (Metric.ball_subset_closedBall.trans hballU)
      have hcont : ContinuousOn (trm (↑γ)) (Metric.closedBall ζ ρ) :=
        ((htrmholo (↑γ)).continuousOn).mono hballU
      have h1 : ‖trm (↑γ) ζ‖ₑ * c ≤ ∫⁻ w in Metric.closedBall ζ ρ, ‖trm (↑γ) w‖ₑ :=
        enorm_mul_le_lintegral_closedBall hρ0 hf hcont
      have h2 : ‖trm (↑γ) ζ‖ₑ ≤ (∫⁻ ζ in K', ‖trm (↑γ) ζ‖ₑ) / c :=
        (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop)).mpr
          (h1.trans (lintegral_mono_set hball))
      have h3 := ENNReal.toReal_mono
        ((ENNReal.div_lt_top (ENNReal.ne_top_of_tsum_ne_top hfinK' γ) hc0).ne) h2
      rwa [toReal_enorm] at h3
  have hsummable' : ∀ ζ : ℂ, 0 < ζ.im → Summable fun γ : ↥Γ => ‖trm (↑γ) ζ‖ := by
    intro ζ hζ
    obtain ⟨u, hu, hub⟩ := hMtest {ζ} isCompact_singleton (by simpa using! hζ)
    exact hu.of_nonneg_of_le (fun γ => norm_nonneg _)
      (fun γ => hub γ ζ (Set.mem_singleton ζ))
  have hsummable : ∀ ζ : ℂ, 0 < ζ.im → Summable fun γ : ↥Γ => trm (↑γ) ζ :=
    fun ζ hζ => (hsummable' ζ hζ).of_norm
  -- ## The theta series carrier
  set Θfun : ℂ → ℂ := fun ζ => if 0 < ζ.im then ∑' γ : ↥Γ, trm (↑γ) ζ else 0 with hΘdef
  have hTLU : TendstoLocallyUniformlyOn
      (fun (F : Finset ↥Γ) ζ => ∑ γ ∈ F, trm (↑γ) ζ) Θfun Filter.atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen]
    intro K hKU hKc
    obtain ⟨u, hu, hub⟩ := hMtest K hKc hKU
    have h1 := tendstoUniformlyOn_tsum hu (fun γ ζ hζ => hub γ ζ hζ) (s := K)
    refine h1.congr_right fun ζ hζ => ?_
    have h9 : (0 : ℝ) < ζ.im := hKU hζ
    simp only [hΘdef]
    rw [if_pos h9]
  have hΘmeas : Measurable Θfun := by
    have hpart : ∀ F : Finset ↥Γ, Measurable
        (fun ζ => if 0 < ζ.im then ∑ γ ∈ F, trm (↑γ) ζ else 0) := by
      intro F
      refine Measurable.ite ?_ ?_ measurable_const
      · exact measurableSet_lt measurable_const Complex.measurable_im
      · exact Finset.measurable_sum F fun γ _ => htrmmeas (↑γ)
    refine measurable_of_tendsto_metrizable' Filter.atTop hpart ?_
    rw [tendsto_pi_nhds]
    intro ζ
    by_cases hζ : 0 < ζ.im
    · simp only [hΘdef, if_pos hζ]
      exact (hsummable ζ hζ).hasSum
    · simp only [hΘdef, if_neg hζ]
      exact tendsto_const_nhds
  have hΘholo : DifferentiableOn ℂ Θfun U :=
    hTLU.differentiableOn
      (Filter.Eventually.of_forall fun F => DifferentiableOn.fun_sum
        fun γ _ => htrmholo (↑γ)) hUopen
  have hΘauto : ∀ γ ∈ Γ, ∀ ζ : ℂ, 0 < ζ.im →
      Θfun (moebiusMap γ ζ) = moebiusDenom γ ζ ^ 4 * Θfun ζ := by
    intro γ₀ hγ₀ ζ hζ
    have him := moebiusMap_im_pos γ₀ hζ
    simp only [hΘdef]
    rw [if_pos him, if_pos hζ]
    have hterm : ∀ γ : ↥Γ, trm (↑γ) (moebiusMap γ₀ ζ)
        = moebiusDenom γ₀ ζ ^ 4 * trm ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * γ₀) ζ := by
      intro γ
      have hd0 : moebiusDenom γ₀ ζ ≠ 0 := hdne γ₀ ζ hζ
      have h1 : moebiusDenom (↑γ) (moebiusMap γ₀ ζ)
          = moebiusDenom ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * γ₀) ζ
            * (moebiusDenom γ₀ ζ)⁻¹ :=
        (eq_mul_inv_iff_mul_eq₀ hd0).mpr (moebiusDenom_mul (↑γ) γ₀ ζ hd0)
      simp only [htrmdef]
      rw [moebiusMap_mul (↑γ) γ₀ ζ hd0, h1, mul_pow, mul_inv, inv_pow, inv_inv]
      ring
    rw [tsum_congr hterm, tsum_mul_left]
    congr 1
    have h := (Equiv.mulRight (⟨γ₀, hγ₀⟩ : ↥Γ)).tsum_eq (fun γ' : ↥Γ => trm (↑γ') ζ)
    simpa only [Equiv.coe_mulRight, Subgroup.coe_mul] using h
  set Θqd : QuadraticDifferential Γ := ⟨Θfun, hΘmeas, hΘholo, hΘauto⟩ with hΘqd
  have hΘl1 : Θqd.l1Norm ≤ ∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ := by
    have hdef : Θqd.l1Norm = ∫⁻ ζ in Dpl, ‖Θfun ζ‖ₑ := rfl
    rw [hdef, ← lintegral_tsum fun γ : ↥Γ => ((htrmmeas (↑γ)).enorm).aemeasurable]
    refine setLIntegral_mono' hDplmeas fun ζ hζ => ?_
    have hζU : (0 : ℝ) < ζ.im := hDplsub hζ
    simp only [hΘdef]
    rw [if_pos hζU]
    have hsum := hsummable' ζ hζU
    calc ‖∑' γ : ↥Γ, trm (↑γ) ζ‖ₑ
        = ENNReal.ofReal ‖∑' γ : ↥Γ, trm (↑γ) ζ‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑' γ : ↥Γ, ‖trm (↑γ) ζ‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hsum)
      _ = ∑' γ : ↥Γ, ENNReal.ofReal ‖trm (↑γ) ζ‖ :=
          ENNReal.ofReal_tsum_of_nonneg (fun γ => norm_nonneg _) hsum
      _ = ∑' γ : ↥Γ, ‖trm (↑γ) ζ‖ₑ := tsum_congr fun γ => ofReal_norm _
  have hΘl1ne : Θqd.l1Norm ≠ ⊤ := ne_top_of_le_ne_top hStot_ne hΘl1
  -- ## The theta differential, normalized by the multiplicity
  refine ⟨((m : ℂ))⁻¹ • Θqd, ?_, ?_⟩
  · rw [l1Norm_smul]
    exact ENNReal.mul_ne_top enorm_ne_top hΘl1ne
  intro κ M hκm hκb hκlaw
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (κ 0)) (hκb 0)
  have hκe : ∀ w : ℂ, ‖κ w‖ₑ ≤ ENNReal.ofReal M := by
    intro w
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hκb w)
  have hdom : ∀ (f : ℂ → ℂ) (S : Set ℂ), (∫⁻ ζ in S, ‖κ ζ * f ζ‖ₑ)
      ≤ ENNReal.ofReal M * ∫⁻ ζ in S, ‖f ζ‖ₑ := by
    intro f S
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ζ => ?_
    rw [enorm_mul]
    exact mul_le_mul' (hκe ζ) le_rfl
  have hdomsum : (∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖κ ζ * trm (↑γ) ζ‖ₑ) ≠ ⊤ := by
    have hle : (∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖κ ζ * trm (↑γ) ζ‖ₑ)
        ≤ ENNReal.ofReal M * ∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ := by
      calc (∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖κ ζ * trm (↑γ) ζ‖ₑ)
          ≤ ∑' γ : ↥Γ, ENNReal.ofReal M * ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ :=
            ENNReal.tsum_le_tsum fun γ => hdom (trm (↑γ)) Dpl
        _ = ENNReal.ofReal M * ∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ :=
            ENNReal.tsum_mul_left
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hStot_ne) hle
  -- Step B : the pairing as a series of tile integrals
  have hstepB : qdPairing κ Θqd = ∑' γ : ↥Γ, ∫ ζ in Dpl, κ ζ * trm (↑γ) ζ := by
    have h0 : qdPairing κ Θqd = ∫ ζ in Dpl, κ ζ * Θfun ζ := rfl
    rw [h0]
    have h1 : (∫ ζ in Dpl, κ ζ * Θfun ζ)
        = ∫ ζ in Dpl, ∑' γ : ↥Γ, κ ζ * trm (↑γ) ζ := by
      refine setIntegral_congr_fun hDplmeas fun ζ hζ => ?_
      have h9 : (0 : ℝ) < ζ.im := hDplsub hζ
      simp only [hΘdef]
      rw [if_pos h9]
      exact tsum_mul_left.symm
    rw [h1]
    exact integral_tsum (fun γ => (hκm.mul (htrmmeas (↑γ))).aestronglyMeasurable) hdomsum
  -- Step C : unfolding each tile integral
  have hstepC : ∀ γ : ↥Γ, (∫ ζ in Dpl, κ ζ * trm (↑γ) ζ)
      = ∫ w in moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl,
        κ w * k₀ w := by
    intro γ
    rw [show (∫ w in moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl,
        κ w * k₀ w)
      = ∫ w in moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Dpl,
        κ w * k₀ w from setIntegral_congr_set (haeset γ).symm]
    rw [hCOVB (↑γ) Dpl hDplmeas hDplsub (fun w => κ w * k₀ w)]
    have hlaw := ae_restrict_of_ae_restrict_of_subset hDplsub (hκlaw (↑γ) γ.2)
    refine setIntegral_congr_ae hDplmeas ?_
    have hlaw2 := (ae_restrict_iff' hDplmeas).mp hlaw
    filter_upwards [hlaw2] with ζ hlζ0 hζmem
    have hlζ := hlζ0 hζmem
    have hζU : (0 : ℝ) < ζ.im := hDplsub hζmem
    have hd : moebiusDenom (↑γ) ζ ≠ 0 := hdne _ ζ hζU
    have hcd : starRingEnd ℂ (moebiusDenom (↑γ) ζ) ≠ 0 := by simpa using hd
    have hκm2 : κ (moebiusMap (↑γ) ζ)
        = κ ζ * (starRingEnd ℂ (moebiusDenom (↑γ) ζ)) ^ 2
          * ((moebiusDenom (↑γ) ζ) ^ 2)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 hd)).mpr hlζ
    have hD4 : ((‖moebiusDenom (↑γ) ζ‖ : ℝ) : ℂ) ^ 4
        = moebiusDenom (↑γ) ζ ^ 2 * (starRingEnd ℂ (moebiusDenom (↑γ) ζ)) ^ 2 := by
      have hns : ((‖moebiusDenom (↑γ) ζ‖ : ℝ) : ℂ) ^ 2
          = moebiusDenom (↑γ) ζ * starRingEnd ℂ (moebiusDenom (↑γ) ζ) := by
        rw [Complex.mul_conj]
        norm_cast
        exact (Complex.normSq_eq_norm_sq _).symm
      calc ((‖moebiusDenom (↑γ) ζ‖ : ℝ) : ℂ) ^ 4
          = (((‖moebiusDenom (↑γ) ζ‖ : ℝ) : ℂ) ^ 2) ^ 2 := by ring
        _ = (moebiusDenom (↑γ) ζ * starRingEnd ℂ (moebiusDenom (↑γ) ζ)) ^ 2 := by rw [hns]
        _ = _ := by ring
    rw [Complex.real_smul, hκm2]
    simp only [htrmdef, hk₀def]
    push_cast
    rw [hD4]
    field_simp
  -- Step D : summing the unfolded tiles by the exact multiplicity
  have hstepD : (∑' γ : ↥Γ, ∫ w in
        moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl, κ w * k₀ w)
      = (m : ℂ) * ∫ ζ in U, κ ζ * k₀ ζ := by
    have h1 : ∀ γ : ↥Γ, (∫ w in
          moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl, κ w * k₀ w)
        = ∫ ζ in U, (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            '' Opl).indicator (fun w => κ w * k₀ w) ζ := by
      intro γ
      rw [setIntegral_indicator (htrans_open γ).measurableSet,
        Set.inter_eq_self_of_subset_right (htrans_subU γ)]
    have hmeas1 : ∀ γ : ↥Γ, AEStronglyMeasurable
        ((moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          '' Opl).indicator (fun w => κ w * k₀ w)) (volume.restrict U) :=
      fun γ => ((hκm.mul hk₀meas).indicator
        (htrans_open γ).measurableSet).aestronglyMeasurable
    have hdom2 : (∑' γ : ↥Γ, ∫⁻ ζ in U,
        ‖(moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          '' Opl).indicator (fun w => κ w * k₀ w) ζ‖ₑ) ≠ ⊤ := by
      have hb : ∀ γ : ↥Γ, (∫⁻ ζ in U,
          ‖(moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            '' Opl).indicator (fun w => κ w * k₀ w) ζ‖ₑ)
          = ∫⁻ ζ in moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl,
            ‖κ ζ * k₀ ζ‖ₑ := by
        intro γ
        calc (∫⁻ ζ in U, ‖(moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
              '' Opl).indicator (fun w => κ w * k₀ w) ζ‖ₑ)
            = ∫⁻ ζ in U, (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
              '' Opl).indicator (fun w => ‖κ w * k₀ w‖ₑ) ζ :=
              lintegral_congr fun ζ => enorm_indicator_eq_indicator_enorm _ _
          _ = ∫⁻ ζ in (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl) ∩ U,
              ‖κ ζ * k₀ ζ‖ₑ :=
              setLIntegral_indicator (htrans_open γ).measurableSet _
          _ = ∫⁻ ζ in moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl,
              ‖κ ζ * k₀ ζ‖ₑ := by
              rw [Set.inter_eq_self_of_subset_left (htrans_subU γ)]
      rw [tsum_congr hb]
      have hle : (∑' γ : ↥Γ, ∫⁻ ζ in
            moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl, ‖κ ζ * k₀ ζ‖ₑ)
          ≤ ENNReal.ofReal M * ∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ := by
        calc (∑' γ : ↥Γ, ∫⁻ ζ in
              moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl, ‖κ ζ * k₀ ζ‖ₑ)
            ≤ ∑' γ : ↥Γ, ENNReal.ofReal M * ∫⁻ ζ in
              moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl, ‖k₀ ζ‖ₑ :=
              ENNReal.tsum_le_tsum fun γ => hdom k₀ _
          _ = ∑' γ : ↥Γ, ENNReal.ofReal M * ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ := by
              refine tsum_congr fun γ : ↥Γ => ?_
              rw [htile γ]
          _ = ENNReal.ofReal M * ∑' γ : ↥Γ, ∫⁻ ζ in Dpl, ‖trm (↑γ) ζ‖ₑ :=
              ENNReal.tsum_mul_left
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hStot_ne) hle
    rw [tsum_congr h1, ← integral_tsum hmeas1 hdom2]
    have h2 : ∀ᵐ ζ ∂(volume.restrict U),
        (∑' γ : ↥Γ, (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          '' Opl).indicator (fun w => κ w * k₀ w) ζ)
          = (m : ℂ) * (κ ζ * k₀ ζ) := by
      have hae1 : ∀ᵐ ζ ∂(volume.restrict U), ζ ∉ Bad := by
        refine Filter.Eventually.filter_mono (ae_mono Measure.restrict_le_self) ?_
        rw [ae_iff]
        simpa [Classical.not_not] using hBadnull
      filter_upwards [hae1, ae_restrict_mem hUmeas] with ζ hζB hζU
      obtain ⟨γ₀, h₀⟩ := hcov ζ hζU hζB
      rw [hfib ℂ (fun w => κ w * k₀ w) ζ γ₀ h₀, nsmul_eq_mul]
    rw [integral_congr_ae h2]
    exact integral_const_mul _ _
  -- final assembly
  have hfinal : qdPairing κ (((m : ℂ))⁻¹ • Θqd) = ∫ ζ in U, κ ζ * k₀ ζ := by
    calc qdPairing κ (((m : ℂ))⁻¹ • Θqd)
        = ((m : ℂ))⁻¹ * qdPairing κ Θqd := qdPairing_smul κ _ Θqd
      _ = ((m : ℂ))⁻¹ * ∑' γ : ↥Γ, ∫ ζ in Dpl, κ ζ * trm (↑γ) ζ := by rw [hstepB]
      _ = ((m : ℂ))⁻¹ * ∑' γ : ↥Γ, ∫ w in
            moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl, κ w * k₀ w := by
          rw [tsum_congr hstepC]
      _ = ((m : ℂ))⁻¹ * ((m : ℂ) * ∫ ζ in U, κ ζ * k₀ ζ) := by rw [hstepD]
      _ = ∫ ζ in U, κ ζ * k₀ ζ := by
          rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm0), one_mul]
  rw [hfinal]
  refine setIntegral_congr_fun hUmeas fun ζ _ => ?_
  simp only [hk₀def]
  rw [div_eq_mul_inv]

end RiemannDynamics

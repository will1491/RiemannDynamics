/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.WeylRigidity
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.AffineFamily
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Nehari
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Theta
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Reproducing

/-!
# Invariant spreading from the Dirichlet domain

A bounded measurable datum on the canonical Dirichlet domain spreads along the tiling to
a bounded measurable coefficient supported in the upper half plane and obeying the
Beltrami invariance law: the tiles are disjointified, the datum is transported with the
unimodular denominator-cocycle phase, and the trivially-acting coset keeps the phase
well defined.

* `exists_invariant_extension_of_dirichlet` — invariant spreading from the Dirichlet
  domain.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **Invariant spreading**: a bounded measurable datum on the canonical Dirichlet
domain extends to a bounded measurable coefficient supported in the upper half plane,
obeying the invariance law and agreeing with the datum almost everywhere on the
domain. -/
theorem exists_invariant_extension_of_dirichlet (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {ν₀ : ℂ → ℂ} (hmeas : Measurable ν₀) {m : ℝ} (hm : ∀ z, ‖ν₀ z‖ ≤ m) :
    ∃ ν : ℂ → ℂ, Measurable ν ∧ (∀ z, ‖ν z‖ ≤ m) ∧
      (∀ z : ℂ, z.im ≤ 0 → ν z = 0) ∧
      (∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        ν (moebiusMap W z) * (moebiusDenom W z) ^ 2
          = ν z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2) ∧
      (∀ᵐ z ∂(volume.restrict
        (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)), ν z = ν₀ z) := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  haveI : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
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
    simpa using τ.im_pos
  set Opl : Set ℂ := UpperHalfPlane.coe '' Ih with hOpl
  have hOplopen : IsOpen Opl :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hIhopen
  have hOplsubD : Opl ⊆ Dpl := Set.image_mono interior_subset
  have hOplsub : Opl ⊆ U := hOplsubD.trans hDplsub
  set Fpl : Set ℂ := Dpl \ Opl with hFpl
  have hFplmeas : MeasurableSet Fpl := hDplmeas.diff hOplopen.measurableSet
  have hFplsub : Fpl ⊆ U := fun w hw => hDplsub hw.1
  have hFplc : IsCompact Fpl := hDplc.diff hOplopen
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
  -- ## Möbius helpers
  have hdne : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ζ : ℂ), 0 < ζ.im →
      moebiusDenom γ ζ ≠ 0 := fun γ ζ hζ => moebiusDenom_ne_zero_of_im_ne_zero γ hζ.ne'
  have hmoebmeas : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, Measurable (moebiusMap γ) := by
    intro γ
    unfold moebiusMap moebiusDenom
    fun_prop
  have hdenommeas : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      Measurable (moebiusDenom γ) := by
    intro γ
    unfold moebiusDenom
    fun_prop
  have hmoebcont : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ContinuousOn (moebiusMap γ) U := fun γ ζ hζ =>
    ((hasDerivAt_moebiusMap_of_im_pos γ hζ).differentiableAt).continuousAt.continuousWithinAt
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
  have hnullimg : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℂ),
      MeasurableSet S → S ⊆ U → volume S = 0 → volume (moebiusMap γ '' S) = 0 := by
    intro γ S hm' hs h0
    have h1 := hCOV γ S hm' hs (fun _ => (1 : ℝ≥0∞))
    simp only [mul_one] at h1
    rw [setLIntegral_one] at h1
    rw [h1, Measure.restrict_eq_zero.mpr h0]
    simp
  -- ## Trivially acting elements, tiles, coset dichotomy
  set T : Set ↥Γ := {σ : ↥Γ | ∀ τ : UpperHalfPlane, σ • τ = τ} with hT
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
  -- ## Trivially acting elements fix the upper plane pointwise, constant real denominator
  have hfixT : ∀ σ : ↥Γ, σ ∈ T → ∀ w : ℂ, 0 < w.im →
      moebiusMap (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) w = w := by
    intro σ hσ w hw
    have h1 : σ • (⟨w, hw⟩ : UpperHalfPlane) = ⟨w, hw⟩ := hσ ⟨w, hw⟩
    rw [Subgroup.smul_def] at h1
    have h2 := coe_smul_eq_moebiusMap
      (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (⟨w, hw⟩ : UpperHalfPlane)
    rw [h1] at h2
    exact h2.symm
  have hrigid : ∀ σ : ↥Γ, σ ∈ T → ∃ s : ℝ, ((s : ℂ) ≠ 0 ∧ ∀ w : ℂ,
      moebiusDenom (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) w = (s : ℂ)) := by
    intro σ hσ
    have hIim : (0 : ℝ) < (Complex.I).im := by simp
    have h2Iim : (0 : ℝ) < ((2 : ℂ) * Complex.I).im := by
      simp
    have hdI : moebiusDenom (↑σ) Complex.I ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero _ (by simp)
    have hd2I : moebiusDenom (↑σ) ((2 : ℂ) * Complex.I) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero _ (by norm_num)
    have e1 := hfixT σ hσ Complex.I hIim
    have e2 := hfixT σ hσ ((2 : ℂ) * Complex.I) h2Iim
    unfold moebiusMap at e1 e2
    rw [div_eq_iff hdI] at e1
    rw [div_eq_iff hd2I] at e2
    unfold moebiusDenom at e1 e2
    have e1r := congrArg Complex.re e1
    have e1i := congrArg Complex.im e1
    have e2r := congrArg Complex.re e2
    have e2i := congrArg Complex.im e2
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, mul_one, zero_mul, one_mul, zero_add, add_zero, sub_zero,
      zero_sub] at e1r e1i e2r e2i
    have hdet : (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0
          * (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1
        - (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1
          * (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      rwa [Matrix.det_fin_two] at h
    have hc0 : (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 = 0 := by linarith
    have hb0 : (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 = 0 := by linarith
    have had : (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0
        * (↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 = 1 := by
      rw [hb0, hc0] at hdet
      simpa using hdet
    refine ⟨(↑σ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1, ?_, ?_⟩
    · rw [Complex.ofReal_ne_zero]
      intro h0
      rw [h0, mul_zero] at had
      exact one_ne_zero had.symm
    · intro w
      unfold moebiusDenom
      rw [hc0]
      simp
  -- ## The null bad set and the covering
  set Bad : Set ℂ := ⋃ γ : ↥Γ, moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    '' Fpl with hBad
  have hBadnull : volume Bad = 0 :=
    measure_iUnion_null fun γ => hnullimg _ Fpl hFplmeas hFplsub hFplnull
  have hBadmeas : MeasurableSet Bad := by
    rw [hBad]
    exact MeasurableSet.iUnion fun γ =>
      (hFplc.image_of_continuousOn ((hmoebcont _).mono hFplsub)).measurableSet
  have hBadsubU : Bad ⊆ U := by
    intro w hw
    rw [hBad] at hw
    obtain ⟨γ, x, hx, rfl⟩ := Set.mem_iUnion.mp hw
    exact moebiusMap_im_pos _ (hFplsub hx)
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
  -- ## Enumeration of the group with the identity first
  obtain ⟨f, hfsurj⟩ := exists_surjective_nat ↥Γ
  set e : ℕ → ↥Γ := fun n => if n = 0 then 1 else f (n - 1) with hedef
  have he0 : e 0 = 1 := by simp [hedef]
  have hesurj : ∀ γ : ↥Γ, ∃ n : ℕ, e n = γ := by
    intro γ
    obtain ⟨n, hn⟩ := hfsurj γ
    exact ⟨n + 1, by simp [hedef, hn]⟩
  -- ## Disjointified tiles
  set B : ℕ → Set ℂ := disjointed (fun n =>
    moebiusMap (↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl) with hBdef
  have hBsub : ∀ n : ℕ,
      B n ⊆ moebiusMap (↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl := by
    rw [hBdef]
    exact fun n => disjointed_subset _ n
  have hBmeas : ∀ n : ℕ, MeasurableSet (B n) := by
    rw [hBdef]
    exact fun n => MeasurableSet.disjointed
      (fun k => (htrans_open (e k)).measurableSet) n
  have hBdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j) := by
    rw [hBdef]
    exact fun i j h => disjoint_disjointed _ h
  have hBcover : ∀ z : ℂ, 0 < z.im → z ∉ Bad → ∃ n : ℕ, z ∈ B n := by
    intro z hz hzB
    obtain ⟨γ₀, hγ₀⟩ := hcov z hz hzB
    obtain ⟨n₀, hn₀⟩ := hesurj γ₀
    have hzT : z ∈ ⋃ k : ℕ,
        moebiusMap (↑(e k) : Matrix.SpecialLinearGroup (Fin 2) ℝ) '' Opl :=
      Set.mem_iUnion.mpr ⟨n₀, by rw [hn₀]; exact hγ₀⟩
    rw [← iUnion_disjointed, ← hBdef] at hzT
    exact Set.mem_iUnion.mp hzT
  have hB0 : B 0 = Opl := by
    rw [hBdef]
    simp only [disjointed_zero]
    rw [he0, OneMemClass.coe_one]
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [moebiusMap_one]
      exact hv
    · intro hw
      exact ⟨w, hw, moebiusMap_one w⟩
  -- ## The piecewise value and the spread coefficient
  set P : ℕ → ℂ → ℂ := fun n w =>
    ν₀ (moebiusMap ((↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ w)
      * (starRingEnd ℂ (moebiusDenom (↑(e n))
          (moebiusMap ((↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ w))) ^ 2
      * ((moebiusDenom (↑(e n))
          (moebiusMap ((↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ w)) ^ 2)⁻¹
    with hPdef
  have hPmeas : ∀ n : ℕ, Measurable (P n) := by
    intro n
    rw [hPdef]
    have h1 : Measurable (moebiusMap ((↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹) :=
      hmoebmeas _
    have h2 : Measurable fun w : ℂ => moebiusDenom (↑(e n))
        (moebiusMap ((↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ w) :=
      (hdenommeas _).comp h1
    exact ((hmeas.comp h1).mul
      ((Complex.continuous_conj.measurable.comp h2).pow_const 2)).mul
      ((h2.pow_const 2).inv)
  set ν : ℂ → ℂ := fun z => ∑' n : ℕ, (B n).indicator (P n) z with hνdef
  have hsumm : ∀ z : ℂ, Summable fun n : ℕ => (B n).indicator (P n) z := by
    intro z
    by_cases hex : ∃ n, z ∈ B n
    · obtain ⟨n, hn⟩ := hex
      exact (hasSum_single (f := fun k : ℕ => (B k).indicator (P k) z) n
        fun k hk => Set.indicator_of_notMem
          (fun hzk => Set.disjoint_left.mp (hBdisj hk) hzk hn) _).summable
    · push Not at hex
      exact summable_zero.congr fun n => (Set.indicator_of_notMem (hex n) _).symm
  have heval : ∀ (z : ℂ) (n : ℕ), z ∈ B n → ν z = P n z := by
    intro z n hn
    simp only [hνdef]
    rw [tsum_eq_single n fun k hk => Set.indicator_of_notMem
      (fun hzk => Set.disjoint_left.mp (hBdisj hk) hzk hn) _]
    exact Set.indicator_of_mem hn _
  have hevalz : ∀ z : ℂ, (∀ n, z ∉ B n) → ν z = 0 := by
    intro z hz
    simp only [hνdef]
    rw [tsum_congr fun n => Set.indicator_of_notMem (hz n) (P n)]
    exact tsum_zero
  have hνmeas : Measurable ν := by
    have hpart : ∀ F : Finset ℕ, Measurable fun z => ∑ n ∈ F, (B n).indicator (P n) z :=
      fun F => Finset.measurable_sum F fun n _ => (hPmeas n).indicator (hBmeas n)
    rw [hνdef]
    refine measurable_of_tendsto_metrizable' Filter.atTop hpart ?_
    rw [tendsto_pi_nhds]
    intro z
    exact (hsumm z).hasSum
  -- ## The pointwise bound
  have hm0 : 0 ≤ m := le_trans (norm_nonneg _) (hm 0)
  have hbound : ∀ z : ℂ, ‖ν z‖ ≤ m := by
    intro z
    by_cases hex : ∃ n, z ∈ B n
    · obtain ⟨n, hn⟩ := hex
      obtain ⟨x, hxO, hxz⟩ := hBsub n hn
      have hxup : (0 : ℝ) < x.im := hOplsub hxO
      have hdx : moebiusDenom (↑(e n)) x ≠ 0 := hdne _ x hxup
      have hinv : moebiusMap ((↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ z = x := by
        rw [← hxz, moebiusMap_mul _ _ x hdx, inv_mul_cancel, moebiusMap_one]
      rw [heval z n hn]
      simp only [hPdef]
      rw [hinv, norm_mul, norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_conj,
        mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hdx)), mul_one]
      exact hm x
    · push Not at hex
      rw [hevalz z hex, norm_zero]
      exact hm0
  -- ## Support in the closed upper half plane
  have hsupp : ∀ z : ℂ, z.im ≤ 0 → ν z = 0 := by
    intro z hz
    refine hevalz z fun n hn => ?_
    exact (not_lt.mpr hz) (htrans_subU (e n) (hBsub n hn))
  -- ## The invariance law
  have hlaw : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict U),
      ν (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = ν z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
    intro W hW
    have hNnull : volume (Bad ∪ moebiusMap W⁻¹ '' Bad) = 0 :=
      measure_union_null hBadnull (hnullimg W⁻¹ Bad hBadmeas hBadsubU hBadnull)
    rw [ae_restrict_iff' hUmeas, ae_iff]
    refine measure_mono_null (fun z hz => ?_) hNnull
    rw [Set.mem_setOf_eq] at hz
    push Not at hz
    by_contra hzN
    have hzU : (0 : ℝ) < z.im := hz.1
    have hz1 : z ∉ Bad := fun h => hzN (Or.inl h)
    have hz2 : moebiusMap W z ∉ Bad := by
      intro h
      refine hzN (Or.inr ⟨moebiusMap W z, h, ?_⟩)
      rw [moebiusMap_mul W⁻¹ W z (hdne W z hzU), inv_mul_cancel, moebiusMap_one]
    apply hz.2
    obtain ⟨n, hzBn⟩ := hBcover z hzU hz1
    obtain ⟨k, hWzBk⟩ := hBcover (moebiusMap W z) (moebiusMap_im_pos W hzU) hz2
    obtain ⟨x, hxO, hxz⟩ := hBsub n hzBn
    have hxup : (0 : ℝ) < x.im := hOplsub hxO
    have hdnx : moebiusDenom (↑(e n)) x ≠ 0 := hdne _ x hxup
    have hinvzx : moebiusMap ((↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ z = x := by
      rw [← hxz, moebiusMap_mul _ _ x hdnx, inv_mul_cancel, moebiusMap_one]
    obtain ⟨y, hyO, hyz⟩ := hBsub k hWzBk
    have hyup : (0 : ℝ) < y.im := hOplsub hyO
    have hdky : moebiusDenom (↑(e k)) y ≠ 0 := hdne _ y hyup
    have hinvwy :
        moebiusMap ((↑(e k) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ (moebiusMap W z)
          = y := by
      rw [← hyz, moebiusMap_mul _ _ y hdky, inv_mul_cancel, moebiusMap_one]
    rw [hOpl] at hxO hyO
    obtain ⟨τx, hτx, hτxc⟩ := hxO
    obtain ⟨τy, hτy, hτyc⟩ := hyO
    have hpt : (e k) • τy = ((⟨W, hW⟩ : ↥Γ) * e n) • τx := by
      apply UpperHalfPlane.ext
      have h1 : (((e k) • τy : UpperHalfPlane) : ℂ) = moebiusMap W z := by
        rw [Subgroup.smul_def, coe_smul_eq_moebiusMap, hτyc, hyz]
      have h2 : ((((⟨W, hW⟩ : ↥Γ) * e n) • τx : UpperHalfPlane) : ℂ)
          = moebiusMap W z := by
        rw [Subgroup.smul_def, coe_smul_eq_moebiusMap, hτxc, Subgroup.coe_mul]
        change moebiusMap (W * (↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ)) x
          = moebiusMap W z
        rw [← moebiusMap_mul W _ x hdnx, hxz]
      rw [h1, h2]
    have hσT : (e k)⁻¹ * ((⟨W, hW⟩ : ↥Γ) * e n) ∈ T :=
      hcoset (e k) ((⟨W, hW⟩ : ↥Γ) * e n)
        ⟨(e k) • τy, ⟨τy, hτy, rfl⟩, ⟨τx, hτx, hpt.symm⟩⟩
    obtain ⟨s, hs0, hsden⟩ := hrigid _ hσT
    have hσfix :
        moebiusMap (↑((e k)⁻¹ * ((⟨W, hW⟩ : ↥Γ) * e n)) :
          Matrix.SpecialLinearGroup (Fin 2) ℝ) x = x := hfixT _ hσT x hxup
    have hσd : moebiusDenom (↑((e k)⁻¹ * ((⟨W, hW⟩ : ↥Γ) * e n))) x ≠ 0 := by
      rw [hsden]
      exact hs0
    have hcoeσ : (↑(e k) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          * (↑((e k)⁻¹ * ((⟨W, hW⟩ : ↥Γ) * e n)) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        = W * (↑(e n) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left, Subgroup.coe_mul]
    have hrel : moebiusDenom W z * moebiusDenom (↑(e n)) x
        = moebiusDenom (↑(e k)) x * (s : ℂ) := by
      have h1 := moebiusDenom_mul W (↑(e n)) x hdnx
      rw [hxz] at h1
      have h2 := moebiusDenom_mul (↑(e k))
        (↑((e k)⁻¹ * ((⟨W, hW⟩ : ↥Γ) * e n))) x hσd
      rw [hσfix, hsden, hcoeσ] at h2
      rw [h1, ← h2]
    have hyx : y = x := by
      have hq : moebiusMap (↑(e k)) y = moebiusMap (↑(e k)) x := by
        rw [hyz, ← hxz, moebiusMap_mul W (↑(e n)) x hdnx, ← hcoeσ,
          ← moebiusMap_mul (↑(e k)) _ x hσd, hσfix]
      have h3 := congrArg
        (moebiusMap ((↑(e k) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹) hq
      rwa [moebiusMap_mul _ _ y hdky, inv_mul_cancel, moebiusMap_one,
        moebiusMap_mul _ _ x (hdne _ x hxup), inv_mul_cancel, moebiusMap_one] at h3
    rw [hyx] at hinvwy
    have hdkx : moebiusDenom (↑(e k)) x ≠ 0 := hdne _ x hxup
    rw [heval (moebiusMap W z) k hWzBk, heval z n hzBn]
    simp only [hPdef]
    rw [hinvwy, hinvzx]
    have hconjrel := congrArg (starRingEnd ℂ) hrel
    simp only [map_mul, Complex.conj_ofReal] at hconjrel
    have hsq : (moebiusDenom W z) ^ 2 * (moebiusDenom (↑(e n)) x) ^ 2
        = (moebiusDenom (↑(e k)) x) ^ 2 * ((s : ℂ)) ^ 2 := by
      rw [← mul_pow, hrel, mul_pow]
    have hsq' : (starRingEnd ℂ (moebiusDenom W z)) ^ 2
          * (starRingEnd ℂ (moebiusDenom (↑(e n)) x)) ^ 2
        = (starRingEnd ℂ (moebiusDenom (↑(e k)) x)) ^ 2 * ((s : ℂ)) ^ 2 := by
      rw [← mul_pow, hconjrel, mul_pow]
    field_simp
    linear_combination ν₀ x * (starRingEnd ℂ (moebiusDenom (↑(e k)) x)) ^ 2 * hsq
      - ν₀ x * (moebiusDenom (↑(e k)) x) ^ 2 * hsq'
  -- ## Agreement on the Dirichlet domain
  have hagreeO : ∀ z ∈ Opl, ν z = ν₀ z := by
    intro z hzO
    have hz0 : z ∈ B 0 := by
      rw [hB0]
      exact hzO
    rw [heval z 0 hz0]
    simp only [hPdef]
    rw [he0, OneMemClass.coe_one, inv_one, moebiusMap_one, moebiusDenom_one]
    simp
  have hagree : ∀ᵐ z ∂(volume.restrict Dpl), ν z = ν₀ z := by
    rw [ae_restrict_iff' hDplmeas, ae_iff]
    refine measure_mono_null (fun z hz => ?_) hFplnull
    rw [Set.mem_setOf_eq] at hz
    push Not at hz
    rw [hFpl]
    exact ⟨hz.1, fun hO => hz.2 (hagreeO z hO)⟩
  exact ⟨ν, hνmeas, hbound, hsupp, hlaw, hagree⟩

end RiemannDynamics

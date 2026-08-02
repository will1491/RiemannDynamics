/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.ZeroExtension
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Nehari
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Theta
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Reproducing

/-!
# The fundamental variational lemma

A bounded invariant direction supported in the upper half plane and annihilating every
integrable quadratic differential deforms, to first order, only trivially: for every
tolerance there are exactly trivial coefficients within relative tolerance of the ray —
the coefficient is invariant, its normalized solution is the identity on the closed
lower half plane and commutes with the group. The correction is produced by a Newton
iteration on the Bers-type map (the Schwarzian of the zero-extension solution on the
lower half plane), whose derivative at the origin pairs the direction with the quartic
kernel, annihilated by the theta series, and whose bounded right inverse is the
reproducing formula; the Nehari bound keeps the iterates in the weighted ball. An
essentially bounded datum on the Dirichlet domain first spreads to an invariant
coefficient of the same bound.

* `exists_invariant_extension_of_dirichlet` — invariant spreading from the Dirichlet
  domain.
* `exists_trivial_deformation` — the fundamental variational lemma.
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

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: the Newton iteration on the Bers-type map is assembled
-- in one declaration, from the dslope Cauchy bounds through the equivariant
-- transports to the geometric convergence of the iterates.
/-- **The fundamental variational lemma**: a bounded invariant upper-supported direction
annihilating every integrable quadratic differential admits, for every tolerance and all
small positive times, an exactly trivial coefficient within relative tolerance of the
ray: the coefficient is invariant and upper-supported, and its normalized solution is
the identity on the closed lower half plane and commutes with the group. -/
theorem exists_trivial_deformation (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {η : ℂ → ℂ} (hmeas : Measurable η) {M : ℝ} (hM : ∀ z, ‖η z‖ ≤ M)
    (hsupp : ∀ z : ℂ, z.im ≤ 0 → η z = 0)
    (hinv : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      η (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = η z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2)
    (hperp : ∀ q : QuadraticDifferential Γ, q.l1Norm ≠ ⊤ → qdPairing η q = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∃ (σ w : ℂ → ℂ) (b : BeltramiCoeff), Measurable σ ∧
        (∀ z : ℂ, z.im ≤ 0 → σ z = 0) ∧
        (∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
          σ (moebiusMap W z) * (moebiusDenom W z) ^ 2
            = σ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2) ∧
        (∀ z, ‖σ z - t * η z‖ ≤ ε * t) ∧
        (∀ z, b.μ z = σ z) ∧ IsQCAnalytic w b ∧
        (∀ z : ℂ, z.im ≤ 0 → w z = z) ∧
        (∀ γ ∈ Γ, ∀ z : ℂ, moebiusDenom γ z ≠ 0 →
          w (moebiusMap γ z) = moebiusMap γ (w z)) := by
  classical
  -- ==================================================================
  -- ## Part 0: the degenerate branch `M ≤ 0` (then `η ≡ 0`).
  -- ==================================================================
  by_cases hM0 : M ≤ 0
  · refine ⟨1, one_pos, fun t ht _ => ?_⟩
    have hη0 : ∀ z, η z = 0 := fun z =>
      norm_le_zero_iff.mp ((hM z).trans hM0)
    refine ⟨fun _ => 0, id, BeltramiCoeff.zero, measurable_const,
      fun _ _ => rfl, ?_, ?_, fun _ => rfl, isQCAnalytic_id, fun _ _ => rfl,
      fun _ _ _ _ => rfl⟩
    · intro W _
      filter_upwards with z
      simp
    · intro z
      rw [hη0 z, mul_zero, sub_zero, norm_zero]
      positivity
  push Not at hM0
  -- ==================================================================
  -- ## Part 1: context-free analytic helpers (dslope Cauchy–Taylor bounds).
  -- ==================================================================
  -- The difference quotient of a map holomorphic on a ball is holomorphic there.
  have hdsl : ∀ (g : ℂ → ℂ) (R : ℝ), 0 < R → DifferentiableOn ℂ g (Metric.ball 0 R) →
      DifferentiableOn ℂ (dslope g 0) (Metric.ball 0 R) := by
    intro g R hR hg b hb
    rcases eq_or_ne b 0 with rfl | hb0
    · have han : AnalyticAt ℂ g 0 := hg.analyticAt (Metric.ball_mem_nhds 0 hR)
      obtain ⟨p, hp⟩ := han
      exact (AnalyticAt.differentiableAt
        ⟨_, hp.has_fpower_series_dslope_fslope⟩).differentiableWithinAt
    · have hd : DifferentiableAt ℂ g b :=
        hg.differentiableAt (Metric.isOpen_ball.mem_nhds hb)
      exact ((differentiableAt_dslope_of_ne hb0).mpr hd).differentiableWithinAt
  -- Maximum-modulus bound for the difference quotient on the three-quarter ball.
  have hdslB : ∀ (g : ℂ → ℂ) (R A : ℝ), 0 < R → DifferentiableOn ℂ g (Metric.ball 0 R) →
      (∀ u ∈ Metric.ball (0 : ℂ) R, ‖g u‖ ≤ A) →
      ∀ w : ℂ, ‖w‖ ≤ 3 * R / 4 → ‖dslope g 0 w‖ ≤ 8 * A / (3 * R) := by
    intro g R A hR hg hA w hw
    have hρ : (0 : ℝ) < 3 * R / 4 := by linarith only [hR]
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Metric.mem_ball_self hR))
    have hsub : Metric.closedBall (0 : ℂ) (3 * R / 4) ⊆ Metric.ball 0 R := by
      intro u hu
      rw [Metric.mem_closedBall, dist_zero_right] at hu
      rw [Metric.mem_ball, dist_zero_right]
      linarith only [hu, hR]
    have hdiff := hdsl g R hR hg
    have hdc : DiffContOnCl ℂ (dslope g 0) (Metric.ball 0 (3 * R / 4)) := by
      refine ⟨hdiff.mono fun u hu => hsub (Metric.ball_subset_closedBall hu), ?_⟩
      rw [closure_ball (0 : ℂ) (ne_of_gt hρ)]
      exact (hdiff.mono hsub).continuousOn
    have hfr : ∀ u ∈ frontier (Metric.ball (0 : ℂ) (3 * R / 4)),
        ‖dslope g 0 u‖ ≤ 8 * A / (3 * R) := by
      rw [frontier_ball (0 : ℂ) (ne_of_gt hρ)]
      intro u hu
      rw [mem_sphere_zero_iff_norm] at hu
      have hu0 : u ≠ 0 := by
        intro h
        rw [h, norm_zero] at hu
        linarith only [hu, hρ]
      have huball : u ∈ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right, hu]
        linarith only [hR]
      rw [dslope_of_ne g hu0, slope_def_field, sub_zero, norm_div, hu]
      have hnum : ‖g u - g 0‖ ≤ 2 * A :=
        (norm_sub_le _ _).trans
          (by linarith only [hA u huball, hA 0 (Metric.mem_ball_self hR)])
      rw [div_le_div_iff₀ (by linarith only [hR]) (by linarith only [hR])]
      nlinarith only [hnum, hR, hA0]
    have hcl : w ∈ closure (Metric.ball (0 : ℂ) (3 * R / 4)) := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hρ), Metric.mem_closedBall, dist_zero_right]
      exact hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc hfr hcl
  -- Cauchy bound on the derivative at the origin.
  have hDer : ∀ (g : ℂ → ℂ) (R A : ℝ), 0 < R → DifferentiableOn ℂ g (Metric.ball 0 R) →
      (∀ u ∈ Metric.ball (0 : ℂ) R, ‖g u‖ ≤ A) → ‖deriv g 0‖ ≤ 3 * A / R := by
    intro g R A hR hg hA
    have h := hdslB g R A hR hg hA 0 (by rw [norm_zero]; linarith only [hR])
    rw [dslope_same] at h
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Metric.mem_ball_self hR))
    refine h.trans ?_
    rw [div_le_div_iff₀ (by linarith only [hR]) hR]
    nlinarith only [hA0, hR]
  -- Lipschitz bound from `0` to `1`.
  have hLip : ∀ (g : ℂ → ℂ) (R A : ℝ), 2 ≤ R → DifferentiableOn ℂ g (Metric.ball 0 R) →
      (∀ u ∈ Metric.ball (0 : ℂ) R, ‖g u‖ ≤ A) → ‖g 1 - g 0‖ ≤ 3 * A / R := by
    intro g R A hR hg hA
    have hR0 : (0 : ℝ) < R := by linarith only [hR]
    have h := hdslB g R A hR0 hg hA 1 (by rw [norm_one]; linarith only [hR])
    rw [dslope_of_ne g one_ne_zero, slope_def_field, sub_zero, div_one] at h
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Metric.mem_ball_self hR0))
    refine h.trans ?_
    rw [div_le_div_iff₀ (by linarith only [hR0]) hR0]
    nlinarith only [hA0, hR0]
  -- Quadratic Taylor remainder bound at `1`.
  have hQuad : ∀ (g : ℂ → ℂ) (R A : ℝ), 2 ≤ R → DifferentiableOn ℂ g (Metric.ball 0 R) →
      (∀ u ∈ Metric.ball (0 : ℂ) R, ‖g u‖ ≤ A) →
      ‖g 1 - g 0 - deriv g 0‖ ≤ 10 * A / R ^ 2 := by
    intro g R A hR hg hA
    have hR0 : (0 : ℝ) < R := by linarith only [hR]
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Metric.mem_ball_self hR0))
    have hρ : (0 : ℝ) < 3 * R / 4 := by linarith only [hR0]
    -- the once-divided map, on the three-quarter ball
    have hd1 : DifferentiableOn ℂ (dslope g 0) (Metric.ball 0 (3 * R / 4)) :=
      (hdsl g R hR0 hg).mono (Metric.ball_subset_ball (by linarith only [hR0]))
    have hb1 : ∀ u ∈ Metric.ball (0 : ℂ) (3 * R / 4), ‖dslope g 0 u‖ ≤ 8 * A / (3 * R) := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      exact hdslB g R A hR0 hg hA u hu.le
    -- the twice-divided map
    have h2 := hdslB (dslope g 0) (3 * R / 4) (8 * A / (3 * R)) hρ hd1 hb1 1
      (by rw [norm_one]; linarith only [hR])
    rw [dslope_of_ne _ one_ne_zero, slope_def_field, sub_zero, div_one,
      dslope_of_ne g one_ne_zero, slope_def_field, sub_zero, div_one, dslope_same] at h2
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by linarith only [hR0]) (by positivity)]
    have hL : 8 * (8 * A / (3 * R)) * R ^ 2 = 64 * A * R / 3 := by
      field_simp
      ring
    rw [hL, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith only [hA0, hR0, hR]
  -- ==================================================================
  -- ## Part 2: global objects (the Bers map, the pairing constants).
  -- ==================================================================
  -- Pointwise-equal coefficients have the same quasiconformal solutions.
  have hQCtr : ∀ (b b' : BeltramiCoeff) (f : ℂ → ℂ), (∀ ζ, b.μ ζ = b'.μ ζ) →
      IsQCAnalytic f b → IsQCAnalytic f b' := fun b b' f hbb hf =>
    hf.congr_coeff (Filter.Eventually.of_forall hbb)
  -- The Bers-type map: `Λ ρ` is the Schwarzian of THE normalized solution of `ρ`.
  obtain ⟨Λ, hΛ⟩ : ∃ L : (ℂ → ℂ) → ℂ → ℂ,
      ∀ (ρ : ℂ → ℂ) (b : BeltramiCoeff) (f : ℂ → ℂ), (∀ ζ, b.μ ζ = ρ ζ) →
        IsQCAnalytic f b → f 0 = 0 → f 1 = 1 → L ρ = schwarzian f := by
    refine ⟨fun ρ =>
      if h : ∃ p : (ℂ → ℂ) × BeltramiCoeff, (∀ ζ, p.2.μ ζ = ρ ζ) ∧
        IsQCAnalytic p.1 p.2 ∧ p.1 0 = 0 ∧ p.1 1 = 1
      then schwarzian h.choose.1 else 0, ?_⟩
    intro ρ b f hbμ hf h0 h1
    have hex : ∃ p : (ℂ → ℂ) × BeltramiCoeff, (∀ ζ, p.2.μ ζ = ρ ζ) ∧
        IsQCAnalytic p.1 p.2 ∧ p.1 0 = 0 ∧ p.1 1 = 1 := ⟨(f, b), hbμ, hf, h0, h1⟩
    simp only [dif_pos hex]
    obtain ⟨hμ', hqc', h0', h1'⟩ := hex.choose_spec
    have hfb' : IsQCAnalytic f hex.choose.2 :=
      hQCtr b hex.choose.2 f (fun ζ => (hbμ ζ).trans (hμ' ζ).symm) hf
    have hu := (mrmt_unique_normalized hex.choose.2).unique ⟨hqc', h0', h1'⟩ ⟨hfb', h0, h1⟩
    rw [hu]
  -- The two universal constants.
  obtain ⟨c', hc'0, hfam⟩ := exists_affine_solution_family
  obtain ⟨cR, hcR0, hrep⟩ := exists_reproducing_constant
  -- The solution package of a small upper-supported coefficient.
  have hupmeas : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hlowopen : IsOpen {z : ℂ | z.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hsol : ∀ ρ : ℂ → ℂ, Measurable ρ → (∀ ζ, ‖ρ ζ‖ ≤ 1 / 2) →
      (∀ ζ : ℂ, ζ.im ≤ 0 → ρ ζ = 0) →
      ∃ (f : ℂ → ℂ) (b : BeltramiCoeff), (∀ ζ, b.μ ζ = ρ ζ) ∧ IsQCAnalytic f b ∧
        f 0 = 0 ∧ f 1 = 1 ∧ Λ ρ = schwarzian f ∧
        DifferentiableOn ℂ f {z : ℂ | z.im < 0} ∧
        (∀ z : ℂ, z.im < 0 → (2 * z.im) ^ 2 * ‖Λ ρ z‖ ≤ 6) := by
    intro ρ hρm hρb hρs
    have hbound : eLpNormEssSup ρ volume < 1 := by
      refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (C := 1 / 2)
        (Filter.Eventually.of_forall hρb)) ?_
      exact ENNReal.ofReal_lt_one.mpr (by norm_num)
    obtain ⟨f, ⟨hfqc, hf0, hf1⟩, -⟩ := mrmt_unique_normalized ⟨ρ, hρm, hbound⟩
    have hbμ : ∀ ζ, (⟨ρ, hρm, hbound⟩ : BeltramiCoeff).μ ζ = ρ ζ := fun _ => rfl
    have hΛρ : Λ ρ = schwarzian f := hΛ ρ _ f hbμ hfqc hf0 hf1
    have hconf : DifferentiableOn ℂ f {z : ℂ | z.im < 0} := by
      refine differentiableOn_of_beltrami_ae_zero hfqc hlowopen ?_
      filter_upwards [ae_restrict_mem hlowopen.measurableSet] with ζ hζ
      exact hρs ζ (le_of_lt hζ)
    refine ⟨f, _, hbμ, hfqc, hf0, hf1, hΛρ, hconf, fun z hz => ?_⟩
    rw [hΛρ]
    exact schwarzian_le_of_injOn_lower hconf (hfqc.injective.injOn) hz
  -- The Schwarzian of a conformal injection is analytic.
  have hID2 : ∀ F : ℂ → ℂ, iteratedDeriv 2 F = deriv (deriv F) := fun F => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hID3 : ∀ F : ℂ → ℂ, iteratedDeriv 3 F = deriv (iteratedDeriv 2 F) := fun F => by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  have hschwan : ∀ (f : ℂ → ℂ) (z : ℂ), AnalyticAt ℂ f z → deriv f z ≠ 0 →
      AnalyticAt ℂ (schwarzian f) z := by
    intro f z hf hf'
    have h2an : AnalyticAt ℂ (iteratedDeriv 2 f) z := by rw [hID2]; exact hf.deriv.deriv
    have h3an : AnalyticAt ℂ (iteratedDeriv 3 f) z := by rw [hID3]; exact h2an.deriv
    have hdan : AnalyticAt ℂ (deriv f) z := hf.deriv
    have hcomb : AnalyticAt ℂ (fun w => iteratedDeriv 3 f w / deriv f w
        - 3 / 2 * (iteratedDeriv 2 f w / deriv f w) ^ 2) z :=
      (h3an.fun_div hdan hf').fun_sub
        (analyticAt_const.fun_mul ((h2an.fun_div hdan hf').fun_pow 2))
    exact hcomb
  -- The Schwarzian of any map is Borel measurable.
  have hschwmeas : ∀ f : ℂ → ℂ, Measurable (schwarzian f) := by
    intro f
    have h1 : Measurable (deriv f) := measurable_deriv f
    have h2 : Measurable (iteratedDeriv 2 f) := by rw [hID2]; exact measurable_deriv _
    have h3 : Measurable (iteratedDeriv 3 f) := by rw [hID3]; exact measurable_deriv _
    exact (h3.div h1).sub (measurable_const.mul ((h2.div h1).pow_const 2))
  -- ==================================================================
  -- ## Part 3: null real line and globalization of the invariance law.
  -- ==================================================================
  have hline : volume {z : ℂ | z.im = 0} = 0 := by
    have hmp := Complex.volume_preserving_equiv_real_prod
    have hset : {z : ℂ | z.im = 0}
        = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ ({0} : Set ℝ)) := by
      ext z
      simp [Complex.measurableEquivRealProd_apply, Set.mem_prod]
    rw [hset, hmp.measure_preimage
      ((MeasurableSet.univ.prod (measurableSet_singleton (0 : ℝ))).nullMeasurableSet)]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  have hglob : ∀ ρ : ℂ → ℂ, (∀ ζ : ℂ, ζ.im ≤ 0 → ρ ζ = 0) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        ρ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
          = ρ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) →
      ∀ᵐ z : ℂ, ρ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = ρ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
    intro ρ hρs γ hae
    have h1 := (ae_restrict_iff' hupmeas).mp hae
    have h2 : ∀ᵐ z : ℂ, z.im ≠ 0 := by
      rw [ae_iff]
      refine measure_mono_null (fun z hz => ?_) hline
      simpa using hz
    filter_upwards [h1, h2] with z hz1 hz2
    rcases lt_or_gt_of_ne hz2 with hneg | hpos
    · rw [hρs z hneg.le, hρs _ (moebiusMap_im_neg γ hneg).le, zero_mul, zero_mul]
    · exact hz1 hpos
  -- ==================================================================
  -- ## Part 4: the analytic family of Bers maps along affine paths.
  -- ==================================================================
  have hfamA : ∀ (κ ν : ℂ → ℂ) (m Mv : ℝ), Measurable κ → Measurable ν →
      (∀ ζ, ‖κ ζ‖ ≤ m) → (∀ ζ, ‖ν ζ‖ ≤ Mv) →
      (∀ ζ : ℂ, ζ.im ≤ 0 → κ ζ = 0) → (∀ ζ : ℂ, ζ.im ≤ 0 → ν ζ = 0) →
      m < 1 → 0 < Mv → ∀ z : ℂ, z.im < 0 →
      (∀ u : ℂ, ‖u‖ < (1 - m) / Mv →
        (2 * z.im) ^ 2 * ‖Λ (fun ζ => κ ζ + u * ν ζ) z‖ ≤ 6) ∧
      DifferentiableOn ℂ (fun u => Λ (fun ζ => κ ζ + u * ν ζ) z)
        (Metric.ball 0 ((1 - m) / Mv)) ∧
      ((∀ ζ, κ ζ = 0) → HasDerivAt (fun u => Λ (fun ζ => κ ζ + u * ν ζ) z)
        (c' * ∫ ζ in {ζ : ℂ | 0 < ζ.im}, ν ζ / (ζ - z) ^ 4) 0) := by
    intro κ ν m Mv hκm hνm hκb hνb hκs hνs hm1 hMv z hz
    obtain ⟨W, hW1, _hW2, hW3, hW4⟩ := hfam κ ν m Mv hκm hνm hκb hνb hκs hνs hm1 hMv
    have hid : ∀ u : ℂ, ‖u‖ < (1 - m) / Mv →
        Λ (fun ζ => κ ζ + u * ν ζ) = schwarzian (W u) := by
      intro u hu
      obtain ⟨b, hb, hqc, h0, h1⟩ := hW1 u hu
      exact hΛ _ b (W u) hb hqc h0 h1
    have hopen : IsOpen {u : ℂ | ‖u‖ < (1 - m) / Mv} :=
      isOpen_lt continuous_norm continuous_const
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨b, hb, hqc, h0, h1⟩ := hW1 u hu
      have hconf : DifferentiableOn ℂ (W u) {w : ℂ | w.im < 0} := by
        refine differentiableOn_of_beltrami_ae_zero hqc hlowopen ?_
        filter_upwards [ae_restrict_mem hlowopen.measurableSet] with ζ hζ
        rw [hb ζ, hκs ζ (le_of_lt hζ), hνs ζ (le_of_lt hζ), mul_zero, add_zero]
      rw [hid u hu]
      exact schwarzian_le_of_injOn_lower hconf (hqc.injective.injOn) hz
    · intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      have hu' : u ∈ {u : ℂ | ‖u‖ < (1 - m) / Mv} := hu
      have hev : (fun v => schwarzian (W v) z) =ᶠ[nhds u]
          (fun v => Λ (fun ζ => κ ζ + v * ν ζ) z) := by
        filter_upwards [hopen.mem_nhds hu'] with v hv
        rw [hid v hv]
      exact (((hW3 z hz u hu').congr hev).differentiableAt).differentiableWithinAt
    · intro hκ0
      have h0mem : (0 : ℂ) ∈ {u : ℂ | ‖u‖ < (1 - m) / Mv} := by
        simp only [Set.mem_setOf_eq, norm_zero]
        exact div_pos (by linarith only [hm1]) hMv
      have hev : (fun v => Λ (fun ζ => κ ζ + v * ν ζ) z) =ᶠ[nhds (0 : ℂ)]
          (fun v => schwarzian (W v) z) := by
        filter_upwards [hopen.mem_nhds h0mem] with v hv
        rw [hid v hv]
      exact (hW4 hκ0 z hz).congr_of_eventuallyEq hev
  -- The quartic kernel annihilates the direction `η`.
  have hK0 : ∀ z : ℂ, z.im < 0 → (∫ ζ in {ζ : ℂ | 0 < ζ.im}, η ζ / (ζ - z) ^ 4) = 0 := by
    intro z hz
    obtain ⟨Θ, hΘl1, hΘid⟩ := exists_theta_qd hΓ hfree hcc hz
    rw [hΘid η M hmeas hM hinv]
    exact hperp Θ hΘl1
  -- ==================================================================
  -- ## Part 5: the reproducing operator `Sop`.
  -- ==================================================================
  obtain ⟨Sop, hSop⟩ : ∃ S : (ℂ → ℂ) → ℂ → ℂ, ∀ φ ζ, S φ ζ =
      if 0 < ζ.im then cR * (ζ - starRingEnd ℂ ζ) ^ 2 * φ (starRingEnd ℂ ζ) else 0 :=
    ⟨fun φ ζ => if 0 < ζ.im then cR * (ζ - starRingEnd ℂ ζ) ^ 2 * φ (starRingEnd ℂ ζ)
      else 0, fun _ _ => rfl⟩
  have hSmeas : ∀ φ : ℂ → ℂ, Measurable φ → Measurable (Sop φ) := by
    intro φ hφ
    have hfun : Sop φ = fun ζ => if 0 < ζ.im then
        cR * (ζ - starRingEnd ℂ ζ) ^ 2 * φ (starRingEnd ℂ ζ) else 0 := funext (hSop φ)
    rw [hfun]
    refine Measurable.ite hupmeas ?_ measurable_const
    exact (measurable_const.mul
      (((measurable_id.sub Complex.continuous_conj.measurable).pow_const 2))).mul
      (hφ.comp Complex.continuous_conj.measurable)
  have hSsupp : ∀ (φ : ℂ → ℂ) (ζ : ℂ), ζ.im ≤ 0 → Sop φ ζ = 0 := by
    intro φ ζ hζ
    rw [hSop, if_neg (not_lt.mpr hζ)]
  have hSbound : ∀ (φ : ℂ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ z : ℂ, z.im < 0 → (2 * z.im) ^ 2 * ‖φ z‖ ≤ B) →
      ∀ ζ, ‖Sop φ ζ‖ ≤ ‖cR‖ * B := by
    intro φ B hB0 hφ ζ
    rw [hSop]
    split_ifs with hζ
    · have hcim : (starRingEnd ℂ ζ).im < 0 := by rw [Complex.conj_im]; linarith only [hζ]
      have hb := hφ _ hcim
      rw [Complex.conj_im] at hb
      have hsub : ζ - starRingEnd ℂ ζ = ((2 * ζ.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
        ring
      rw [norm_mul, norm_mul, norm_pow, hsub, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs]
      have h1 : |2 * ζ.im| ^ 2 = (2 * -ζ.im) ^ 2 := by rw [sq_abs]; ring
      rw [h1, mul_assoc]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg cR)
    · rw [norm_zero]
      positivity
  -- The reproducing identity for `Sop`.
  have hSrep : ∀ (φ : ℂ → ℂ) (B : ℝ), DifferentiableOn ℂ φ {z : ℂ | z.im < 0} →
      (∀ z : ℂ, z.im < 0 → (2 * z.im) ^ 2 * ‖φ z‖ ≤ B) → ∀ z : ℂ, z.im < 0 →
      (∫ ζ in {ζ : ℂ | 0 < ζ.im}, Sop φ ζ / (ζ - z) ^ 4) = φ z := by
    intro φ B hφd hφb z hz
    rw [← hrep φ B hφd hφb z hz]
    refine setIntegral_congr_fun hupmeas fun ζ hζ => ?_
    have hζ' : 0 < ζ.im := hζ
    rw [hSop, if_pos hζ']
  -- ==================================================================
  -- ## Part 6: the Möbius transition of solutions of invariant coefficients.
  -- ==================================================================
  have htrans : ∀ (b : BeltramiCoeff) (f : ℂ → ℂ), IsQCAnalytic f b → f 0 = 0 → f 1 = 1 →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ᵐ z : ℂ, b.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = b.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) →
      ∃ p q r s : ℂ, p * s - q * r ≠ 0 ∧ ∀ z : ℂ, z.im < 0 →
        r * f z + s ≠ 0 ∧ f (moebiusMap γ z) = (p * f z + q) / (r * f z + s) := by
    intro b f hf h0 h1 γ hinvγ
    -- affine maps are quasi-measure-preserving (for coefficient transport)
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
          simpa using ((hasDerivAt_id (0 : ℂ)).const_mul c).deriv
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
        have hcomp : (fun z : ℂ => c * z + x₀)
            = (fun y : ℂ => y + x₀) ∘ fun w : ℂ => c * w := rfl
        rw [hcomp, ← Measure.map_map (measurable_add_const x₀) hcm, hmapmul,
          Measure.map_smul, (measurePreserving_add_right volume x₀).map_eq]
      exact ⟨(measurable_id'.const_mul c).add_const x₀, by
        rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
    by_cases hc : γ 1 0 = 0
    · -- ==== the affine case ====
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe γ
        rwa [Matrix.det_fin_two] at h
      rw [hc, mul_zero, sub_zero] at hdet
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
        rw [affineMap_apply, moebiusMap_of_lowerLeft_zero γ hc z]
      have hμinv : ∀ᵐ z : ℂ, b.μ (moebiusMap γ z) = b.μ z := by
        have hd2 : ((γ 1 1 : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hd)
        filter_upwards [hinvγ] with z hz
        have hdenz : moebiusDenom γ z = (γ 1 1 : ℂ) := by
          simp [moebiusDenom, hc]
        rw [hdenz, Complex.conj_ofReal] at hz
        exact mul_right_cancel₀ hd2 hz
      have hcoef : (b.pullbackAffine hcne ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))).μ =ᵐ[volume] b.μ := by
        have hcconj : starRingEnd ℂ ((γ 0 0 : ℂ) ^ 2) / (γ 0 0 : ℂ) ^ 2 = 1 := by
          rw [map_pow, Complex.conj_ofReal]
          exact div_self hcne
        filter_upwards [hμinv] with z hz
        change b.μ ((γ 0 0 : ℂ) ^ 2 * z + (γ 0 0 : ℂ) * (γ 0 1 : ℂ))
            * (starRingEnd ℂ ((γ 0 0 : ℂ) ^ 2) / (γ 0 0 : ℂ) ^ 2) = b.μ z
        rw [hcconj, mul_one, ← moebiusMap_of_lowerLeft_zero γ hc z]
        exact hz
      have hF : IsQCAnalytic
          (f ∘ affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))) b :=
        (isQCAnalytic_comp_affine hf hcne ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))).congr_coeff hcoef
      set F : ℂ → ℂ := f ∘ affineMap ((γ 0 0 : ℂ) ^ 2) ((γ 0 0 : ℂ) * (γ 0 1 : ℂ))
        with hFdef
      set Y₀ : ℂ := F 0 with hY₀
      set Y₁ : ℂ := F 1 with hY₁
      have hne : Y₁ - Y₀ ≠ 0 := by
        refine sub_ne_zero.mpr fun hEq => ?_
        exact one_ne_zero (hF.injective hEq)
      have hq0 : (fun z => (Y₁ - Y₀)⁻¹ * F z + -((Y₁ - Y₀)⁻¹ * Y₀)) 0 = 0 := by
        change (Y₁ - Y₀)⁻¹ * F 0 + -((Y₁ - Y₀)⁻¹ * Y₀) = 0
        rw [← hY₀]
        ring
      have hq1 : (fun z => (Y₁ - Y₀)⁻¹ * F z + -((Y₁ - Y₀)⁻¹ * Y₀)) 1 = 1 := by
        change (Y₁ - Y₀)⁻¹ * F 1 + -((Y₁ - Y₀)⁻¹ * Y₀) = 1
        rw [← hY₁, show (Y₁ - Y₀)⁻¹ * Y₁ + -((Y₁ - Y₀)⁻¹ * Y₀)
          = (Y₁ - Y₀)⁻¹ * (Y₁ - Y₀) from by ring]
        exact inv_mul_cancel₀ hne
      have hqf : (fun z => (Y₁ - Y₀)⁻¹ * F z + -((Y₁ - Y₀)⁻¹ * Y₀)) = f :=
        (mrmt_unique_normalized b).unique
          ⟨hF.affine_postcomp (inv_ne_zero hne) (-((Y₁ - Y₀)⁻¹ * Y₀)), hq0, hq1⟩
          ⟨hf, h0, h1⟩
      have hFz : ∀ z : ℂ, F z = (Y₁ - Y₀) * f z + Y₀ := by
        intro z
        have h := congrFun hqf z
        change (Y₁ - Y₀)⁻¹ * F z + -((Y₁ - Y₀)⁻¹ * Y₀) = f z at h
        have h2 : (Y₁ - Y₀) * ((Y₁ - Y₀)⁻¹ * F z + -((Y₁ - Y₀)⁻¹ * Y₀)) + Y₀ = F z := by
          linear_combination (F z - Y₀) * mul_inv_cancel₀ hne
        rw [← h2, h]
      refine ⟨Y₁ - Y₀, Y₀, 0, 1, ?_, fun z _ => ?_⟩
      · rw [mul_one, mul_zero, sub_zero]
        exact hne
      constructor
      · rw [zero_mul, zero_add]
        exact one_ne_zero
      · rw [hmoeb z, zero_mul, zero_add, div_one]
        exact hFz z
    · -- ==== the generic case, through the Bruhat factorization ====
      obtain ⟨A₁, A₂, hA₁c, hA₂c, hγfac⟩ := bruhat_factorization γ hc
      have hdet₁ : A₁ 0 0 * A₁ 1 1 - A₁ 0 1 * A₁ 1 0 = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe A₁
        rwa [Matrix.det_fin_two] at h
      rw [hA₁c, mul_zero, sub_zero] at hdet₁
      have ha₁ : A₁ 0 0 ≠ 0 := by
        intro h
        rw [h, zero_mul] at hdet₁
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
      have he₁ : A₁ 1 1 ≠ 0 := by
        intro h
        rw [h, mul_zero] at hdet₁
        exact zero_ne_one hdet₁
      set c₁ : ℂ := ((A₁ 0 0 ^ 2 : ℝ) : ℂ) with hc₁def
      set d₁ : ℂ := ((A₁ 0 0 * A₁ 0 1 : ℝ) : ℂ) with hd₁def
      set c₂ : ℂ := ((A₂ 0 0 ^ 2 : ℝ) : ℂ) with hc₂def
      set d₂ : ℂ := ((A₂ 0 0 * A₂ 0 1 : ℝ) : ℂ) with hd₂def
      have hc₁ne : c₁ ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 ha₁)
      have hc₂ne : c₂ ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 ha₂)
      have hc₁conj : starRingEnd ℂ c₁ = c₁ := by rw [hc₁def]; exact Complex.conj_ofReal _
      have hc₂conj : starRingEnd ℂ c₂ = c₂ := by rw [hc₂def]; exact Complex.conj_ofReal _
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
      have hdγ : ∀ z : ℂ, moebiusDenom γ z
          = (A₁ 1 1 : ℂ) * (c₂ * z + d₂) * (A₂ 1 1 : ℂ) := by
        intro z
        rw [hγfac, ← moebiusDenom_mul (A₁ * inversionSL2) A₂ z (hdenA₂ne z), hmA₂ z,
          hdenAS, hdenA₂]
      have hmγ : ∀ z : ℂ, c₂ * z + d₂ ≠ 0 →
          moebiusMap γ z = c₁ * (-1 / (c₂ * z + d₂)) + d₁ := by
        intro z hu
        have hdenS : moebiusDenom inversionSL2 (c₂ * z + d₂) = c₂ * z + d₂ := by
          simp [moebiusDenom, inversionSL2]
        have hdenSne : moebiusDenom inversionSL2 (c₂ * z + d₂) ≠ 0 := by
          rw [hdenS]; exact hu
        rw [hγfac, ← moebiusMap_mul (A₁ * inversionSL2) A₂ z (hdenA₂ne z), hmA₂ z,
          ← moebiusMap_mul A₁ inversionSL2 _ hdenSne, moebiusMap_inversionSL2, hmA₁]
      -- the transported map through the inversion
      set g : ℂ → ℂ := f ∘ affineMap c₁ d₁ with hgdef
      have hgqc : IsQCAnalytic g (b.pullbackAffine hc₁ne d₁) :=
        isQCAnalytic_comp_affine hf hc₁ne d₁
      obtain ⟨bG, _hbGle, hGqc', hGpull⟩ := exists_isQCAnalytic_inversionTransport hgqc
      set Φ : ℂ → ℂ := inversionTransport g ∘ affineMap c₂ d₂ with hΦdef
      have hΦqc0 : IsQCAnalytic Φ (bG.pullbackAffine hc₂ne d₂) :=
        isQCAnalytic_comp_affine hGqc' hc₂ne d₂
      have hu0 : ∀ᵐ z : ℂ, c₂ * z + d₂ ≠ 0 := by
        rw [ae_iff]
        refine measure_mono_null (fun z hz => ?_) (measure_singleton (-d₂ / c₂))
        rw [Set.mem_setOf_eq, not_not] at hz
        have hzval : z = -d₂ / c₂ := by
          rw [eq_div_iff hc₂ne]
          linear_combination hz
        simpa [Set.mem_singleton_iff] using hzval
      have hcoef : (bG.pullbackAffine hc₂ne d₂).μ =ᵐ[volume] b.μ := by
        have htransfer := (haffQMP c₂ d₂ hc₂ne).ae hGpull
        filter_upwards [htransfer, hinvγ, hu0] with z hz1 hz2 hz3
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
        rw [show (Y₁ - Y₀)⁻¹ * Y₁ + -((Y₁ - Y₀)⁻¹ * Y₀)
          = (Y₁ - Y₀)⁻¹ * (Y₁ - Y₀) from by ring]
        exact inv_mul_cancel₀ hne
      have hqf : (fun z => (Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀)) = f :=
        (mrmt_unique_normalized b).unique
          ⟨hΦqcb.affine_postcomp (inv_ne_zero hne) (-((Y₁ - Y₀)⁻¹ * Y₀)), hq0, hq1⟩
          ⟨hf, h0, h1⟩
      have hΦz : ∀ z : ℂ, Φ z = (Y₁ - Y₀) * f z + Y₀ := by
        intro z
        have h := congrFun hqf z
        change (Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀) = f z at h
        have h2 : (Y₁ - Y₀) * ((Y₁ - Y₀)⁻¹ * Φ z + -((Y₁ - Y₀)⁻¹ * Y₀)) + Y₀ = Φ z := by
          linear_combination (Φ z - Y₀) * mul_inv_cancel₀ hne
        rw [← h2, h]
      -- unwind the value of `Φ` on the lower half plane
      refine ⟨f d₁ * (Y₁ - Y₀), f d₁ * Y₀ + 1, Y₁ - Y₀, Y₀, ?_, fun z hz => ?_⟩
      · intro hdet0
        apply hne
        linear_combination -hdet0
      have hu : c₂ * z + d₂ ≠ 0 := by
        intro h0'
        have him := congrArg Complex.im h0'
        rw [Complex.add_im, Complex.mul_im] at him
        rw [hc₂def, hd₂def] at him
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.zero_im] at him
        rcases mul_eq_zero.mp him with h | h
        · exact pow_ne_zero 2 ha₂ h
        · exact absurd h (ne_of_lt hz)
      have hΦval : Φ z = (f (moebiusMap γ z) - f d₁)⁻¹ := by
        change inversionTransport g (affineMap c₂ d₂ z) = _
        rw [affineMap_apply]
        rw [show inversionTransport g (c₂ * z + d₂)
          = (g (-1 / (c₂ * z + d₂)) - g 0)⁻¹ from by
            simp only [inversionTransport, if_neg hu]]
        have hg1 : g (-1 / (c₂ * z + d₂)) = f (moebiusMap γ z) := by
          change f (affineMap c₁ d₁ (-1 / (c₂ * z + d₂))) = _
          rw [affineMap_apply, ← hmγ z hu]
        have hg0 : g 0 = f d₁ := by
          change f (affineMap c₁ d₁ 0) = _
          rw [affineMap_apply, mul_zero, zero_add]
        rw [hg1, hg0]
      have hlow : (moebiusMap γ z).im < 0 := moebiusMap_im_neg γ hz
      have hne2 : f (moebiusMap γ z) - f d₁ ≠ 0 := by
        refine sub_ne_zero.mpr fun hEq => ?_
        have heq2 := hf.injective hEq
        rw [heq2, hd₁def, Complex.ofReal_im] at hlow
        exact lt_irrefl 0 hlow
      have hΦz' := hΦz z
      rw [hΦval] at hΦz'
      have hden : (Y₁ - Y₀) * f z + Y₀ ≠ 0 := by
        rw [← hΦz']
        exact inv_ne_zero hne2
      refine ⟨hden, ?_⟩
      rw [eq_div_iff hden]
      have hkey : (f (moebiusMap γ z) - f d₁) * ((Y₁ - Y₀) * f z + Y₀) = 1 := by
        rw [← hΦz']
        exact mul_inv_cancel₀ hne2
      linear_combination hkey
  -- ==================================================================
  -- ## Part 7: weight-4 automorphy of the Bers map of an invariant coefficient.
  -- ==================================================================
  have hauto : ∀ ρ : ℂ → ℂ, Measurable ρ → (∀ ζ, ‖ρ ζ‖ ≤ 1 / 2) →
      (∀ ζ : ℂ, ζ.im ≤ 0 → ρ ζ = 0) →
      (∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        ρ (moebiusMap W z) * (moebiusDenom W z) ^ 2
          = ρ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2) →
      ∀ γ ∈ Γ, ∀ w : ℂ, w.im < 0 →
        Λ ρ (moebiusMap γ w) = Λ ρ w * (moebiusDenom γ w) ^ 4 := by
    intro ρ hρm hρb hρs hρinv γ hγ w hw
    obtain ⟨f, b, hbμ, hf, h0, h1, hΛρ, hconf, -⟩ := hsol ρ hρm hρb hρs
    have hbinv : ∀ᵐ z : ℂ, b.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = b.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
      filter_upwards [hglob ρ hρs γ (hρinv γ hγ)] with z hz
      rw [hbμ, hbμ]
      exact hz
    obtain ⟨p, q, r, s, hdet, hpt⟩ := htrans b f hf h0 h1 γ hbinv
    have hdenne : moebiusDenom γ w ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_lt hw)
    have hγw : (moebiusMap γ w).im < 0 := moebiusMap_im_neg γ hw
    have hfan : ∀ v : ℂ, v.im < 0 → AnalyticAt ℂ f v := fun v hv =>
      hconf.analyticAt (hlowopen.mem_nhds hv)
    have hfder : ∀ v : ℂ, v.im < 0 → deriv f v ≠ 0 := fun v hv =>
      deriv_ne_zero_of_injOn hlowopen hconf (hf.injective.injOn) hv
    have hMM : moebiusMap γ
        = fun v => ((γ 0 0 : ℂ) * v + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * v + (γ 1 1 : ℂ)) := rfl
    have hMan : AnalyticAt ℂ (moebiusMap γ) w := by
      rw [hMM]
      exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).fun_div
        ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hdenne
    have hMder : deriv (moebiusMap γ) w = ((moebiusDenom γ w) ^ 2)⁻¹ :=
      (hasDerivAt_moebiusMap γ hdenne).deriv
    have hMder0 : deriv (moebiusMap γ) w ≠ 0 := by
      rw [hMder]
      exact inv_ne_zero (pow_ne_zero 2 hdenne)
    have hne1 : r * f w + s ≠ 0 := (hpt w hw).1
    have hMoban : AnalyticAt ℂ (fun x => (p * x + q) / (r * x + s)) (f w) :=
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const).fun_div
        ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hne1
    have hMobder : HasDerivAt (fun x => (p * x + q) / (r * x + s))
        ((p * s - q * r) / (r * f w + s) ^ 2) (f w) := by
      have hnum : HasDerivAt (fun x => p * x + q) p (f w) := by
        simpa using ((hasDerivAt_id (f w)).const_mul p).add_const q
      have hden : HasDerivAt (fun x => r * x + s) r (f w) := by
        simpa using ((hasDerivAt_id (f w)).const_mul r).add_const s
      have h := hnum.div hden hne1
      have heq : (p * (r * f w + s) - (p * f w + q) * r) / (r * f w + s) ^ 2
          = (p * s - q * r) / (r * f w + s) ^ 2 := by ring
      rwa [heq] at h
    have hMobder0 : deriv (fun x => (p * x + q) / (r * x + s)) (f w) ≠ 0 := by
      rw [hMobder.deriv]
      exact div_ne_zero hdet (pow_ne_zero 2 hne1)
    have hev : (f ∘ moebiusMap γ) =ᶠ[nhds w]
        ((fun x => (p * x + q) / (r * x + s)) ∘ f) := by
      filter_upwards [hlowopen.mem_nhds hw] with v hv
      simp only [Function.comp_apply]
      exact (hpt v hv).2
    have hstep1 : schwarzian (f ∘ moebiusMap γ) w
        = schwarzian f (moebiusMap γ w) * (deriv (moebiusMap γ) w) ^ 2
          + schwarzian (moebiusMap γ) w :=
      schwarzian_comp hMan hMder0 (hfan _ hγw) (hfder _ hγw)
    have hstep2 : schwarzian ((fun x => (p * x + q) / (r * x + s)) ∘ f) w
        = schwarzian (fun x => (p * x + q) / (r * x + s)) (f w) * (deriv f w) ^ 2
          + schwarzian f w :=
      schwarzian_comp (hfan w hw) (hfder w hw) hMoban hMobder0
    have hchain : schwarzian f (moebiusMap γ w) * (((moebiusDenom γ w) ^ 2)⁻¹) ^ 2
        = schwarzian f w := by
      calc schwarzian f (moebiusMap γ w) * (((moebiusDenom γ w) ^ 2)⁻¹) ^ 2
          = schwarzian f (moebiusMap γ w) * (deriv (moebiusMap γ) w) ^ 2
            + schwarzian (moebiusMap γ) w := by
            rw [hMder, schwarzian_moebiusMap γ hdenne, add_zero]
        _ = schwarzian (f ∘ moebiusMap γ) w := hstep1.symm
        _ = schwarzian ((fun x => (p * x + q) / (r * x + s)) ∘ f) w :=
            schwarzian_congr_nhds hev
        _ = schwarzian (fun x => (p * x + q) / (r * x + s)) (f w) * (deriv f w) ^ 2
            + schwarzian f w := hstep2
        _ = schwarzian f w := by
            rw [schwarzian_ratio_eq_zero hdet hne1, zero_mul, zero_add]
    have hne4 : (moebiusDenom γ w) ^ 2 ≠ 0 := pow_ne_zero 2 hdenne
    have hinv2 : (((moebiusDenom γ w) ^ 2)⁻¹) ^ 2 * ((moebiusDenom γ w) ^ 2) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hne4, one_pow]
    rw [hΛρ]
    calc schwarzian f (moebiusMap γ w)
        = schwarzian f (moebiusMap γ w)
          * ((((moebiusDenom γ w) ^ 2)⁻¹) ^ 2 * ((moebiusDenom γ w) ^ 2) ^ 2) := by
          rw [hinv2, mul_one]
      _ = (schwarzian f (moebiusMap γ w) * (((moebiusDenom γ w) ^ 2)⁻¹) ^ 2)
          * ((moebiusDenom γ w) ^ 2) ^ 2 := by ring
      _ = schwarzian f w * ((moebiusDenom γ w) ^ 2) ^ 2 := by rw [hchain]
      _ = schwarzian f w * (moebiusDenom γ w) ^ 4 := by ring
  -- ==================================================================
  -- ## Part 8: the reproducing operator maps automorphic maps to invariant
  -- coefficients.
  -- ==================================================================
  have hSinv : ∀ φ : ℂ → ℂ,
      (∀ γ, γ ∈ Γ → ∀ v : ℂ, v.im < 0 →
        φ (moebiusMap γ v) = φ v * (moebiusDenom γ v) ^ 4) →
      ∀ γ, γ ∈ Γ → ∀ z : ℂ, 0 < z.im →
        Sop φ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
          = Sop φ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
    intro φ hφa γ hγ z hz
    have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz)
    have hdcj : starRingEnd ℂ (moebiusDenom γ z) ≠ 0 := (map_ne_zero _).mpr hd
    have hup : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hcz : (starRingEnd ℂ z).im < 0 := by
      rw [Complex.conj_im]
      linarith only [hz]
    have hconjM : ∀ v : ℂ,
        moebiusMap γ (starRingEnd ℂ v) = starRingEnd ℂ (moebiusMap γ v) := by
      intro v
      simp [moebiusMap, moebiusDenom, map_div₀, map_add, map_mul, Complex.conj_ofReal]
    have hconjD : ∀ v : ℂ,
        moebiusDenom γ (starRingEnd ℂ v) = starRingEnd ℂ (moebiusDenom γ v) := by
      intro v
      simp [moebiusDenom, map_add, map_mul, Complex.conj_ofReal]
    have hdc : moebiusDenom γ (starRingEnd ℂ z) ≠ 0 := by
      rw [hconjD]
      exact hdcj
    have hdiff : moebiusMap γ z - moebiusMap γ (starRingEnd ℂ z)
        = (z - starRingEnd ℂ z)
          / (moebiusDenom γ z * moebiusDenom γ (starRingEnd ℂ z)) := by
      have hdetC : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
        have h1 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe γ
          rwa [Matrix.det_fin_two] at h
        exact_mod_cast h1
      rw [eq_div_iff (mul_ne_zero hd hdc)]
      have h1 : moebiusMap γ z * moebiusDenom γ z = (γ 0 0 : ℂ) * z + (γ 0 1 : ℂ) := by
        simp only [moebiusMap]
        exact div_mul_cancel₀ _ hd
      have h2 : moebiusMap γ (starRingEnd ℂ z) * moebiusDenom γ (starRingEnd ℂ z)
          = (γ 0 0 : ℂ) * starRingEnd ℂ z + (γ 0 1 : ℂ) := by
        simp only [moebiusMap]
        exact div_mul_cancel₀ _ hdc
      calc (moebiusMap γ z - moebiusMap γ (starRingEnd ℂ z))
            * (moebiusDenom γ z * moebiusDenom γ (starRingEnd ℂ z))
          = (moebiusMap γ z * moebiusDenom γ z) * moebiusDenom γ (starRingEnd ℂ z)
            - (moebiusMap γ (starRingEnd ℂ z) * moebiusDenom γ (starRingEnd ℂ z))
              * moebiusDenom γ z := by ring
        _ = ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ))
              * ((γ 1 0 : ℂ) * starRingEnd ℂ z + (γ 1 1 : ℂ))
            - ((γ 0 0 : ℂ) * starRingEnd ℂ z + (γ 0 1 : ℂ))
              * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
            rw [h1, h2]
            simp only [moebiusDenom]
        _ = z - starRingEnd ℂ z := by
            linear_combination (z - starRingEnd ℂ z) * hdetC
    have hφz := hφa γ hγ (starRingEnd ℂ z) hcz
    rw [hSop φ (moebiusMap γ z), hSop φ z, if_pos hup, if_pos hz, ← hconjM z, hφz,
      hdiff, hconjD z]
    field_simp
  -- ==================================================================
  -- ## Part 9: the Newton iteration and the conclusion.
  -- ==================================================================
  have hy2 : ∀ z : ℂ, z.im < 0 → 0 < (2 * z.im) ^ 2 := by
    intro z hz
    nlinarith only [mul_pos_of_neg_of_neg hz hz]
  -- The Bers map vanishes on the zero coefficient.
  have hΛzero : ∀ ρ : ℂ → ℂ, (∀ ζ, ρ ζ = 0) → ∀ v : ℂ, Λ ρ v = 0 := by
    intro ρ hρ0 v
    have hbz : ∀ ζ, BeltramiCoeff.zero.μ ζ = ρ ζ := fun ζ => (hρ0 ζ).symm
    have hΛid : Λ ρ = schwarzian id := hΛ ρ BeltramiCoeff.zero id hbz isQCAnalytic_id rfl rfl
    have hd1 : deriv (id : ℂ → ℂ) = fun _ => (1 : ℂ) := funext fun x => deriv_id x
    have h2 : iteratedDeriv 2 (id : ℂ → ℂ) = fun _ => 0 := by
      rw [hID2, hd1]
      exact funext fun x => deriv_const x 1
    have h3 : iteratedDeriv 3 (id : ℂ → ℂ) = fun _ => 0 := by
      rw [hID3, h2]
      exact funext fun x => deriv_const x 0
    rw [hΛid]
    simp [schwarzian, h2, h3, hd1]
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ‖cR‖ := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = ‖c'‖ := ⟨_, rfl⟩
  have hP0 : 0 < P := by
    rw [hPdef]
    exact norm_pos_iff.mpr hcR0
  have hQ0 : 0 < Q := by
    rw [hQdef]
    exact norm_pos_iff.mpr hc'0
  have hSboundP : ∀ (φ : ℂ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ z : ℂ, z.im < 0 → (2 * z.im) ^ 2 * ‖φ z‖ ≤ B) →
      ∀ ζ, ‖Sop φ ζ‖ ≤ P * B := by
    rw [hPdef]
    exact hSbound
  -- The time threshold.
  refine ⟨min (1 / (16 * M)) (min (1 / (32 * M * (1 + 8 * P / Q)))
    (min (Q / (2 * M * (500 * P + 4720 * P ^ 2 / Q))) (ε * Q / (120 * P * M ^ 2)))),
    ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 / (16 * M) := by positivity
    have h2 : (0 : ℝ) < 1 / (32 * M * (1 + 8 * P / Q)) := by positivity
    have h3 : (0 : ℝ) < Q / (2 * M * (500 * P + 4720 * P ^ 2 / Q)) := by positivity
    have h4 : (0 : ℝ) < ε * Q / (120 * P * M ^ 2) := by positivity
    exact lt_min h1 (lt_min h2 (lt_min h3 h4))
  intro t ht htlt
  -- ==== numeric consequences of the smallness of `t` ====
  obtain ⟨D, hDdef⟩ : ∃ D' : ℝ, D' = 60 * (t * M) ^ 2 / Q := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β' : ℝ, β' = 2 * D := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have hβ0 : 0 < β := by rw [hβdef]; linarith only [hD0]
  have htM0 : 0 < t * M := mul_pos ht hM0
  have htM : t * M < 1 / 16 := by
    have h1 : t < 1 / (16 * M) := lt_of_lt_of_le htlt (min_le_left _ _)
    have h2 : t * (16 * M) < 1 := (lt_div_iff₀ (by positivity)).mp h1
    linarith only [h2]
  have hβQ : β * Q = 120 * (t * M) ^ 2 := by
    rw [hβdef, hDdef]
    field_simp
    ring
  have hN1 : t * M + P * β ≤ 1 / 16 := by
    have h1 : t < 1 / (32 * M * (1 + 8 * P / Q)) :=
      lt_of_lt_of_le htlt ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : t * (32 * M * (1 + 8 * P / Q)) < 1 :=
      (lt_div_iff₀ (by positivity)).mp h1
    have h2' : 32 * (t * M) * Q + 256 * (t * M) * P < Q := by
      have h := mul_lt_mul_of_pos_right h2 hQ0
      have hexp : t * (32 * M * (1 + 8 * P / Q)) * Q
          = 32 * (t * M) * Q + 256 * (t * M) * P := by
        field_simp
        ring
      linarith only [h, hexp]
    have hbr : P * (t * M) ^ 2 ≤ P * (t * M) * (1 / 16) := by
      nlinarith only [mul_nonneg (mul_nonneg hP0.le htM0.le)
        (by linarith only [htM] : (0 : ℝ) ≤ 1 / 16 - t * M)]
    rw [← mul_le_mul_iff_left₀ hQ0]
    have hexp2 : (t * M + P * β) * Q = t * M * Q + 120 * (P * (t * M) ^ 2) := by
      calc (t * M + P * β) * Q = t * M * Q + P * (β * Q) := by ring
        _ = t * M * Q + P * (120 * (t * M) ^ 2) := by rw [hβQ]
        _ = t * M * Q + 120 * (P * (t * M) ^ 2) := by ring
    rw [hexp2]
    nlinarith only [hbr, h2', hQ0, mul_nonneg htM0.le hP0.le]
  have hβS2 : P * β ≤ 1 / 16 := by linarith only [hN1, htM0]
  have hN2 : 90 * P ^ 2 * β + 500 * P * (t * M + P * β) ≤ Q / 2 := by
    have h1 : t < Q / (2 * M * (500 * P + 4720 * P ^ 2 / Q)) :=
      lt_of_lt_of_le htlt ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have h2 : t * (2 * M * (500 * P + 4720 * P ^ 2 / Q)) < Q :=
      (lt_div_iff₀ (by positivity)).mp h1
    have h2' : 1000 * (t * M) * P * Q + 9440 * (t * M) * P ^ 2 < Q ^ 2 := by
      have h := mul_lt_mul_of_pos_right h2 hQ0
      have hexp : t * (2 * M * (500 * P + 4720 * P ^ 2 / Q)) * Q
          = 1000 * (t * M) * P * Q + 9440 * (t * M) * P ^ 2 := by
        field_simp
        ring
      linarith only [h, hexp]
    have hbr : P ^ 2 * (t * M) ^ 2 ≤ P ^ 2 * (t * M) * (1 / 16) := by
      nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg P) htM0.le)
        (by linarith only [htM] : (0 : ℝ) ≤ 1 / 16 - t * M)]
    rw [← mul_le_mul_iff_left₀ hQ0]
    have hexp2 : (90 * P ^ 2 * β + 500 * P * (t * M + P * β)) * Q
        = 70800 * (P ^ 2 * (t * M) ^ 2) + 500 * (t * M) * P * Q := by
      calc (90 * P ^ 2 * β + 500 * P * (t * M + P * β)) * Q
          = 590 * P ^ 2 * (β * Q) + 500 * (t * M) * P * Q := by ring
        _ = 590 * P ^ 2 * (120 * (t * M) ^ 2) + 500 * (t * M) * P * Q := by rw [hβQ]
        _ = 70800 * (P ^ 2 * (t * M) ^ 2) + 500 * (t * M) * P * Q := by ring
    rw [hexp2]
    nlinarith only [hbr, h2', mul_nonneg (sq_nonneg P) htM0.le]
  have hN3 : P * β ≤ ε * t := by
    have h1 : t < ε * Q / (120 * P * M ^ 2) :=
      lt_of_lt_of_le htlt ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have h2 : t * (120 * P * M ^ 2) < ε * Q :=
      (lt_div_iff₀ (by positivity)).mp h1
    rw [hβdef, hDdef]
    rw [show P * (2 * (60 * (t * M) ^ 2 / Q)) = 120 * P * (t * M) ^ 2 / Q by ring]
    rw [div_le_iff₀ hQ0]
    nlinarith only [h2, ht]
  -- ==== the initial defect bound ====
  have hinit : ∀ z : ℂ, z.im < 0 →
      (2 * z.im) ^ 2 * ‖Λ (fun ζ => (t : ℂ) * η ζ) z‖ ≤ 60 * (t * M) ^ 2 := by
    intro z hz
    have hy2z := hy2 z hz
    have hνb : ∀ ζ, ‖(t : ℂ) * η ζ‖ ≤ t * M := by
      intro ζ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (hM ζ) ht.le
    have hνs : ∀ ζ : ℂ, ζ.im ≤ 0 → (t : ℂ) * η ζ = 0 := fun ζ hζ => by
      rw [hsupp ζ hζ, mul_zero]
    obtain ⟨hN, hD', hDer'⟩ := hfamA (fun _ => (0 : ℂ)) (fun ζ => (t : ℂ) * η ζ) 0 (t * M)
      measurable_const (measurable_const.mul hmeas)
      (fun ζ => by rw [norm_zero]) hνb (fun _ _ => rfl) hνs one_pos htM0 z hz
    have hR2 : 2 ≤ (1 - 0) / (t * M) := by
      rw [le_div_iff₀ htM0]
      linarith only [htM]
    have hgb : ∀ u ∈ Metric.ball (0 : ℂ) ((1 - 0) / (t * M)),
        ‖Λ (fun ζ => (0 : ℂ) + u * ((t : ℂ) * η ζ)) z‖ ≤ 6 / (2 * z.im) ^ 2 := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      have h := hN u hu
      rw [le_div_iff₀ hy2z, mul_comm]
      exact h
    have hq := hQuad (fun u => Λ (fun ζ => (0 : ℂ) + u * ((t : ℂ) * η ζ)) z)
      ((1 - 0) / (t * M)) (6 / (2 * z.im) ^ 2) hR2 hD' hgb
    -- the value at `0` vanishes
    have hg0 : Λ (fun ζ => (0 : ℂ) + (0 : ℂ) * ((t : ℂ) * η ζ)) z = 0 :=
      hΛzero _ (fun ζ => by ring) z
    -- the derivative at `0` vanishes
    have hint : (∫ ζ in {ζ : ℂ | 0 < ζ.im}, (t : ℂ) * η ζ / (ζ - z) ^ 4) = 0 := by
      have h1 : (∫ ζ in {ζ : ℂ | 0 < ζ.im}, (t : ℂ) * η ζ / (ζ - z) ^ 4)
          = ∫ ζ in {ζ : ℂ | 0 < ζ.im}, (t : ℂ) * (η ζ / (ζ - z) ^ 4) := by
        congr 1
        funext ζ
        rw [mul_div_assoc]
      have h2 : (∫ ζ in {ζ : ℂ | 0 < ζ.im}, (t : ℂ) * (η ζ / (ζ - z) ^ 4))
          = (t : ℂ) * ∫ ζ in {ζ : ℂ | 0 < ζ.im}, η ζ / (ζ - z) ^ 4 :=
        integral_const_mul (t : ℂ) fun ζ => η ζ / (ζ - z) ^ 4
      rw [h1, h2, hK0 z hz, mul_zero]
    have hder0 : deriv (fun u => Λ (fun ζ => (0 : ℂ) + u * ((t : ℂ) * η ζ)) z) 0 = 0 := by
      have h := hDer' (fun _ => rfl)
      rw [hint, mul_zero] at h
      exact h.deriv
    -- restate the quadratic bound in reduced form
    have hq' : ‖Λ (fun ζ => (0 : ℂ) + (1 : ℂ) * ((t : ℂ) * η ζ)) z
        - Λ (fun ζ => (0 : ℂ) + (0 : ℂ) * ((t : ℂ) * η ζ)) z
        - deriv (fun u => Λ (fun ζ => (0 : ℂ) + u * ((t : ℂ) * η ζ)) z) 0‖
        ≤ 10 * (6 / (2 * z.im) ^ 2) / ((1 - 0) / (t * M)) ^ 2 := hq
    rw [hg0, hder0, sub_zero, sub_zero] at hq'
    -- identify the value at `1`
    have hc1 : (fun ζ => (0 : ℂ) + (1 : ℂ) * ((t : ℂ) * η ζ)) = fun ζ => (t : ℂ) * η ζ :=
      funext fun ζ => by ring
    rw [hc1] at hq'
    have hzim : z.im ≠ 0 := ne_of_lt hz
    calc (2 * z.im) ^ 2 * ‖Λ (fun ζ => (t : ℂ) * η ζ) z‖
        ≤ (2 * z.im) ^ 2 * (10 * (6 / (2 * z.im) ^ 2) / ((1 - 0) / (t * M)) ^ 2) :=
          mul_le_mul_of_nonneg_left hq' hy2z.le
      _ = 60 * (t * M) ^ 2 := by
          field_simp
          ring
  -- ==== the master contraction inequality ====
  have hkey : ∀ (ψ δ : ℂ → ℂ) (bψ bδ : ℝ), Measurable ψ → Measurable δ →
      DifferentiableOn ℂ ψ {v : ℂ | v.im < 0} →
      DifferentiableOn ℂ δ {v : ℂ | v.im < 0} →
      0 ≤ bψ → 0 < bδ →
      (∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖ψ v‖ ≤ bψ) →
      (∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖δ v‖ ≤ bδ) →
      bψ ≤ β → bδ ≤ β →
      ∀ z : ℂ, z.im < 0 →
      (2 * z.im) ^ 2 * ‖Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 1 * Sop δ ζ) z
        - Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 0 * Sop δ ζ) z - c' * δ z‖
        ≤ Q / 2 * bδ := by
    intro ψ δ bψ bδ hψm hδm hψd hδd hbψ0 hbδ0 hψb hδb hψβ hδβ z hz
    have hy2z := hy2 z hz
    obtain ⟨A, hAdef⟩ : ∃ A' : ℝ, A' = 6 / (2 * z.im) ^ 2 := ⟨_, rfl⟩
    have hA0 : 0 < A := by rw [hAdef]; positivity
    -- data of the base coefficient
    have hbase_meas : Measurable fun ζ => (t : ℂ) * η ζ + Sop ψ ζ :=
      (measurable_const.mul hmeas).add (hSmeas ψ hψm)
    have htηb : ∀ ζ, ‖(t : ℂ) * η ζ‖ ≤ t * M := by
      intro ζ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (hM ζ) ht.le
    have hbase_bd : ∀ ζ, ‖(t : ℂ) * η ζ + Sop ψ ζ‖ ≤ t * M + P * β := by
      intro ζ
      refine (norm_add_le _ _).trans ?_
      have h2 : ‖Sop ψ ζ‖ ≤ P * bψ := hSboundP ψ bψ hbψ0 hψb ζ
      have h3 : P * bψ ≤ P * β := mul_le_mul_of_nonneg_left hψβ hP0.le
      exact add_le_add (htηb ζ) (h2.trans h3)
    have hbase_bd8 : ∀ ζ, ‖(t : ℂ) * η ζ + Sop ψ ζ‖ ≤ 1 / 8 := fun ζ =>
      (hbase_bd ζ).trans (by linarith only [hN1])
    have hbase_supp : ∀ ζ : ℂ, ζ.im ≤ 0 → (t : ℂ) * η ζ + Sop ψ ζ = 0 := by
      intro ζ hζ
      rw [hsupp ζ hζ, hSsupp ψ ζ hζ, mul_zero, add_zero]
    have hδS_meas := hSmeas δ hδm
    have hδS_bd : ∀ ζ, ‖Sop δ ζ‖ ≤ P * bδ := hSboundP δ bδ hbδ0.le hδb
    have hPbδ : 0 < P * bδ := mul_pos hP0 hbδ0
    have hPbδ16 : P * bδ ≤ 1 / 16 :=
      (mul_le_mul_of_nonneg_left hδβ hP0.le).trans hβS2
    -- the two parameter slices, on the common radius `R₁`
    obtain ⟨R₁, hR₁def⟩ : ∃ R : ℝ, R = (1 - 1 / 8) / (P * bδ) := ⟨_, rfl⟩
    have hR₁2 : 2 ≤ R₁ := by
      rw [hR₁def, le_div_iff₀ hPbδ]
      linarith only [hPbδ16]
    obtain ⟨hg₁N, hg₁D, -⟩ := hfamA (fun ζ => (t : ℂ) * η ζ + Sop ψ ζ) (Sop δ)
      (1 / 8) (P * bδ) hbase_meas hδS_meas hbase_bd8 hδS_bd hbase_supp (hSsupp δ)
      (by norm_num) hPbδ z hz
    obtain ⟨hg₀N, hg₀D, hg₀der⟩ := hfamA (fun _ => (0 : ℂ)) (Sop δ) (1 / 8) (P * bδ)
      measurable_const hδS_meas (fun ζ => by rw [norm_zero]; norm_num) hδS_bd
      (fun _ _ => rfl) (hSsupp δ) (by norm_num) hPbδ z hz
    rw [← hR₁def] at hg₁N hg₁D hg₀N hg₀D
    -- the difference of the two slices is small, uniformly on the ball
    have hdiffb : ∀ u ∈ Metric.ball (0 : ℂ) R₁,
        ‖Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z
          - Λ (fun ζ => (0 : ℂ) + u * Sop δ ζ) z‖
          ≤ 3 * A / ((1 - 7 / 8) / (t * M + P * β)) := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      -- the `s`-slice through the two values
      have hκu_meas : Measurable fun ζ => u * Sop δ ζ := measurable_const.mul hδS_meas
      have hκu_bd : ∀ ζ, ‖u * Sop δ ζ‖ ≤ 7 / 8 := by
        intro ζ
        rw [norm_mul]
        have h1 : ‖u‖ * ‖Sop δ ζ‖ ≤ R₁ * (P * bδ) :=
          mul_le_mul hu.le (hδS_bd ζ) (norm_nonneg _) (by positivity)
        have h2 : R₁ * (P * bδ) = 1 - 1 / 8 := by
          rw [hR₁def]
          field_simp
        linarith only [h1, h2]
      have hκu_supp : ∀ ζ : ℂ, ζ.im ≤ 0 → u * Sop δ ζ = 0 := fun ζ hζ => by
        rw [hSsupp δ ζ hζ, mul_zero]
      have hm₁0 : 0 < t * M + P * β := by positivity
      obtain ⟨hGN, hGD, -⟩ := hfamA (fun ζ => u * Sop δ ζ)
        (fun ζ => (t : ℂ) * η ζ + Sop ψ ζ) (7 / 8) (t * M + P * β)
        hκu_meas hbase_meas hκu_bd hbase_bd hκu_supp hbase_supp (by norm_num) hm₁0 z hz
      have hRs2 : 2 ≤ (1 - 7 / 8) / (t * M + P * β) := by
        rw [le_div_iff₀ hm₁0]
        linarith only [hN1]
      have hGb : ∀ s ∈ Metric.ball (0 : ℂ) ((1 - 7 / 8) / (t * M + P * β)),
          ‖Λ (fun ζ => u * Sop δ ζ + s * ((t : ℂ) * η ζ + Sop ψ ζ)) z‖ ≤ A := by
        intro s hs
        rw [Metric.mem_ball, dist_zero_right] at hs
        have h := hGN s hs
        rw [hAdef, le_div_iff₀ hy2z, mul_comm]
        exact h
      have hL := hLip (fun s => Λ (fun ζ => u * Sop δ ζ
        + s * ((t : ℂ) * η ζ + Sop ψ ζ)) z) ((1 - 7 / 8) / (t * M + P * β)) A hRs2 hGD hGb
      -- restate in reduced form and identify the endpoint values
      have hL' : ‖Λ (fun ζ => u * Sop δ ζ + (1 : ℂ) * ((t : ℂ) * η ζ + Sop ψ ζ)) z
          - Λ (fun ζ => u * Sop δ ζ + (0 : ℂ) * ((t : ℂ) * η ζ + Sop ψ ζ)) z‖
          ≤ 3 * A / ((1 - 7 / 8) / (t * M + P * β)) := hL
      have he1 : (fun ζ => u * Sop δ ζ + (1 : ℂ) * ((t : ℂ) * η ζ + Sop ψ ζ))
          = fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ := funext fun ζ => by ring
      have he0 : (fun ζ => u * Sop δ ζ + (0 : ℂ) * ((t : ℂ) * η ζ + Sop ψ ζ))
          = fun ζ => (0 : ℂ) + u * Sop δ ζ := funext fun ζ => by ring
      rw [he1, he0] at hL'
      exact hL'
    -- the derivative comparison at the origin
    have hg₁at : DifferentiableAt ℂ
        (fun u => Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z) 0 :=
      (hg₁D.differentiableAt (Metric.isOpen_ball.mem_nhds
        (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; linarith only [hR₁2])))
    have hg₀at : DifferentiableAt ℂ
        (fun u => Λ (fun ζ => (0 : ℂ) + u * Sop δ ζ) z) 0 :=
      (hg₀D.differentiableAt (Metric.isOpen_ball.mem_nhds
        (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; linarith only [hR₁2])))
    have hdsub : DifferentiableOn ℂ
        (fun u => Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z
          - Λ (fun ζ => (0 : ℂ) + u * Sop δ ζ) z) (Metric.ball 0 R₁) :=
      hg₁D.sub hg₀D
    have hE2 : ‖deriv (fun u => Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z
        - Λ (fun ζ => (0 : ℂ) + u * Sop δ ζ) z) 0‖
        ≤ 3 * (3 * A / ((1 - 7 / 8) / (t * M + P * β))) / R₁ :=
      hDer _ R₁ _ (by linarith only [hR₁2]) hdsub hdiffb
    have hderiv_split : deriv (fun u =>
        Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z
          - Λ (fun ζ => (0 : ℂ) + u * Sop δ ζ) z) 0
        = deriv (fun u => Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z) 0
          - deriv (fun u => Λ (fun ζ => (0 : ℂ) + u * Sop δ ζ) z) 0 :=
      deriv_fun_sub hg₁at hg₀at
    -- the derivative of the centered slice is the reproducing value
    have hδrep : (∫ ζ in {ζ : ℂ | 0 < ζ.im}, Sop δ ζ / (ζ - z) ^ 4) = δ z :=
      hSrep δ bδ hδd hδb z hz
    have hg₀val : deriv (fun u => Λ (fun ζ => (0 : ℂ) + u * Sop δ ζ) z) 0 = c' * δ z := by
      have h := hg₀der (fun _ => rfl)
      rw [hδrep] at h
      exact h.deriv
    -- the quadratic remainder of the outer slice
    have hg₁b : ∀ u ∈ Metric.ball (0 : ℂ) R₁,
        ‖Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z‖ ≤ A := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      have h := hg₁N u hu
      rw [hAdef, le_div_iff₀ hy2z, mul_comm]
      exact h
    have hqd := hQuad (fun u => Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z)
      R₁ A hR₁2 hg₁D hg₁b
    -- assemble the three pieces
    have htotal : ‖Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 1 * Sop δ ζ) z
        - Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 0 * Sop δ ζ) z - c' * δ z‖
        ≤ 10 * A / R₁ ^ 2
          + 3 * (3 * A / ((1 - 7 / 8) / (t * M + P * β))) / R₁ := by
      have h0eq : (fun ζ : ℂ => ((t : ℂ) * η ζ + Sop ψ ζ) + 0 * Sop δ ζ)
          = fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + (0 : ℂ) * Sop δ ζ := rfl
      have hsplit : Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 1 * Sop δ ζ) z
          - Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 0 * Sop δ ζ) z - c' * δ z
          = (Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 1 * Sop δ ζ) z
              - Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 0 * Sop δ ζ) z
              - deriv (fun u =>
                  Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z) 0)
            + (deriv (fun u =>
                  Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z) 0
                - c' * δ z) := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add hqd ?_)
      rw [← hg₀val, ← hderiv_split]
      exact hE2
    -- numeric closing
    have hcalc : (2 * z.im) ^ 2 * (10 * A / R₁ ^ 2
        + 3 * (3 * A / ((1 - 7 / 8) / (t * M + P * β))) / R₁) ≤ Q / 2 * bδ := by
      have hy2ne : (2 * z.im) ^ 2 ≠ 0 := ne_of_gt hy2z
      have hzim : z.im ≠ 0 := ne_of_lt hz
      have hm₁0 : 0 < t * M + P * β := by positivity
      have hm₁ne : t * M + P * β ≠ 0 := ne_of_gt hm₁0
      have hPbδne : P * bδ ≠ 0 := ne_of_gt hPbδ
      have he1 : (2 * z.im) ^ 2 * (10 * A / R₁ ^ 2) = 3840 / 49 * (P * bδ) ^ 2 := by
        rw [hAdef, hR₁def]
        field_simp
        ring
      have he2 : (2 * z.im) ^ 2 * (3 * (3 * A / ((1 - 7 / 8) / (t * M + P * β))) / R₁)
          = 3456 / 7 * ((t * M + P * β) * (P * bδ)) := by
        rw [hAdef, hR₁def]
        field_simp
        ring
      have hb1 : 3840 / 49 * (P * bδ) ^ 2 ≤ 90 * P ^ 2 * β * bδ := by
        nlinarith only [mul_le_mul_of_nonneg_left hδβ
          (by positivity : (0 : ℝ) ≤ P ^ 2 * bδ),
          (by positivity : (0 : ℝ) ≤ P ^ 2 * β * bδ)]
      have hb2 : 3456 / 7 * ((t * M + P * β) * (P * bδ))
          ≤ 500 * P * (t * M + P * β) * bδ := by
        nlinarith only [mul_nonneg (mul_nonneg hm₁0.le hP0.le) hbδ0.le]
      calc (2 * z.im) ^ 2 * (10 * A / R₁ ^ 2
          + 3 * (3 * A / ((1 - 7 / 8) / (t * M + P * β))) / R₁)
          = (2 * z.im) ^ 2 * (10 * A / R₁ ^ 2)
            + (2 * z.im) ^ 2
              * (3 * (3 * A / ((1 - 7 / 8) / (t * M + P * β))) / R₁) := by ring
        _ ≤ 90 * P ^ 2 * β * bδ + 500 * P * (t * M + P * β) * bδ := by
            rw [he1, he2]
            exact add_le_add hb1 hb2
        _ = (90 * P ^ 2 * β + 500 * P * (t * M + P * β)) * bδ := by ring
        _ ≤ Q / 2 * bδ := mul_le_mul_of_nonneg_right hN2 hbδ0.le
    calc (2 * z.im) ^ 2 * ‖Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 1 * Sop δ ζ) z
        - Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 0 * Sop δ ζ) z - c' * δ z‖
        ≤ (2 * z.im) ^ 2 * (10 * A / R₁ ^ 2
          + 3 * (3 * A / ((1 - 7 / 8) / (t * M + P * β))) / R₁) :=
          mul_le_mul_of_nonneg_left htotal hy2z.le
      _ ≤ Q / 2 * bδ := hcalc
  -- ==== splitting of the reproducing operator along differences ====
  have hSsplit : ∀ (φ₁ φ₂ : ℂ → ℂ) (ζ : ℂ),
      Sop φ₁ ζ = Sop φ₂ ζ + Sop (fun w => φ₁ w - φ₂ w) ζ := by
    intro φ₁ φ₂ ζ
    rw [hSop, hSop, hSop]
    split_ifs
    · ring
    · rw [add_zero]
  -- ==== the coefficient and Bers-map package of an admissible direction ====
  have htηb : ∀ ζ, ‖(t : ℂ) * η ζ‖ ≤ t * M := by
    intro ζ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hM ζ) ht.le
  have hpkg : ∀ ψ : ℂ → ℂ, Measurable ψ →
      (∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖ψ v‖ ≤ β) →
      (∀ γ, γ ∈ Γ → ∀ v : ℂ, v.im < 0 →
        ψ (moebiusMap γ v) = ψ v * (moebiusDenom γ v) ^ 4) →
      Measurable (Λ (fun ζ => (t : ℂ) * η ζ + Sop ψ ζ))
        ∧ DifferentiableOn ℂ (Λ (fun ζ => (t : ℂ) * η ζ + Sop ψ ζ)) {v : ℂ | v.im < 0}
        ∧ (∀ γ, γ ∈ Γ → ∀ v : ℂ, v.im < 0 →
            Λ (fun ζ => (t : ℂ) * η ζ + Sop ψ ζ) (moebiusMap γ v)
              = Λ (fun ζ => (t : ℂ) * η ζ + Sop ψ ζ) v * (moebiusDenom γ v) ^ 4) := by
    intro ψ hψm hψb hψa
    have hcm : Measurable fun ζ => (t : ℂ) * η ζ + Sop ψ ζ :=
      (measurable_const.mul hmeas).add (hSmeas ψ hψm)
    have hcb : ∀ ζ, ‖(t : ℂ) * η ζ + Sop ψ ζ‖ ≤ 1 / 2 := by
      intro ζ
      refine (norm_add_le _ _).trans ?_
      have h2 : ‖Sop ψ ζ‖ ≤ P * β := hSboundP ψ β hβ0.le hψb ζ
      have h3 := htηb ζ
      linarith only [h2, h3, hN1]
    have hcs : ∀ ζ : ℂ, ζ.im ≤ 0 → (t : ℂ) * η ζ + Sop ψ ζ = 0 := by
      intro ζ hζ
      rw [hsupp ζ hζ, hSsupp ψ ζ hζ, mul_zero, add_zero]
    have hcinv : ∀ W, W ∈ Γ → ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        ((t : ℂ) * η (moebiusMap W z) + Sop ψ (moebiusMap W z)) * (moebiusDenom W z) ^ 2
          = ((t : ℂ) * η z + Sop ψ z) * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
      intro W hW
      filter_upwards [hinv W hW, ae_restrict_mem hupmeas] with z h1 h2
      have h3 := hSinv ψ hψa W hW z h2
      calc ((t : ℂ) * η (moebiusMap W z) + Sop ψ (moebiusMap W z))
            * (moebiusDenom W z) ^ 2
          = (t : ℂ) * (η (moebiusMap W z) * (moebiusDenom W z) ^ 2)
            + Sop ψ (moebiusMap W z) * (moebiusDenom W z) ^ 2 := by ring
        _ = (t : ℂ) * (η z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2)
            + Sop ψ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by rw [h1, h3]
        _ = ((t : ℂ) * η z + Sop ψ z) * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
            ring
    obtain ⟨f, b, hbμ, hf, h0, h1, hΛeq, hconf, -⟩ := hsol _ hcm hcb hcs
    refine ⟨?_, ?_, hauto _ hcm hcb hcs hcinv⟩
    · rw [hΛeq]
      exact hschwmeas f
    · rw [hΛeq]
      intro v hv
      exact ((hschwan f v (hconf.analyticAt (hlowopen.mem_nhds hv))
        (deriv_ne_zero_of_injOn hlowopen hconf hf.injective.injOn hv)
        ).differentiableAt).differentiableWithinAt
  -- ==== the Newton sequence ====
  obtain ⟨φit, hφ0, hφS⟩ : ∃ φ : ℕ → ℂ → ℂ, (∀ ζ, φ 0 ζ = 0) ∧ ∀ (k : ℕ) (ζ : ℂ),
      φ (k + 1) ζ = φ k ζ - c'⁻¹ * Λ (fun ξ => (t : ℂ) * η ξ + Sop (φ k) ξ) ζ :=
    ⟨fun n => Nat.rec (fun _ => (0 : ℂ))
      (fun _ ψv => fun ζ => ψv ζ - c'⁻¹ * Λ (fun ξ => (t : ℂ) * η ξ + Sop ψv ξ) ζ) n,
      fun _ => rfl, fun _ _ => rfl⟩
  have hS00 : ∀ ξ : ℂ, Sop (φit 0) ξ = 0 := by
    intro ξ
    rw [hSop]
    split_ifs with h
    · rw [hφ0, mul_zero]
    · rfl
  have hcoef0 : (fun ξ => (t : ℂ) * η ξ + Sop (φit 0) ξ) = fun ζ => (t : ℂ) * η ζ :=
    funext fun ξ => by rw [hS00, add_zero]
  -- ==== the master induction ====
  have hIND : ∀ k : ℕ, (Measurable (φit k)
      ∧ DifferentiableOn ℂ (φit k) {v : ℂ | v.im < 0}
      ∧ (∀ γ, γ ∈ Γ → ∀ v : ℂ, v.im < 0 →
          φit k (moebiusMap γ v) = φit k v * (moebiusDenom γ v) ^ 4)
      ∧ (∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖φit k v‖ ≤ β * (1 - (1 / 2) ^ k)))
      ∧ (∀ v : ℂ, v.im < 0 →
          (2 * v.im) ^ 2 * ‖φit (k + 1) v - φit k v‖ ≤ D * (1 / 2) ^ k) := by
    intro k
    induction k with
    | zero =>
      have hfun0 : φit 0 = fun _ => (0 : ℂ) := funext hφ0
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hfun0]
        exact measurable_const
      · rw [hfun0]
        exact differentiableOn_const 0
      · intro γ hγ v hv
        rw [hφ0, hφ0, zero_mul]
      · intro v hv
        rw [hφ0, norm_zero, mul_zero, pow_zero, sub_self, mul_zero]
      · intro v hv
        have hΔ0 : φit 1 v - φit 0 v = -(c'⁻¹ * Λ (fun ζ => (t : ℂ) * η ζ) v) := by
          rw [hφS 0 v, hcoef0]
          ring
        rw [hΔ0, norm_neg, norm_mul, norm_inv, pow_zero, mul_one]
        have h1 := hinit v hv
        have h2 : (2 * v.im) ^ 2 * (‖c'‖⁻¹ * ‖Λ (fun ζ => (t : ℂ) * η ζ) v‖)
            = ‖c'‖⁻¹ * ((2 * v.im) ^ 2 * ‖Λ (fun ζ => (t : ℂ) * η ζ) v‖) := by ring
        rw [h2, hDdef]
        rw [show (60 : ℝ) * (t * M) ^ 2 / Q = ‖c'‖⁻¹ * (60 * (t * M) ^ 2) from by
          rw [hQdef]; field_simp]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    | succ k ih =>
      obtain ⟨⟨hm_k, hd_k, ha_k, hb_k⟩, hdb_k⟩ := ih
      have hbcap_k : ∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖φit k v‖ ≤ β := by
        intro v hv
        refine (hb_k v hv).trans ?_
        have hp1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
        nlinarith only [hβ0, hp1]
      obtain ⟨hLm, hLd, hLa⟩ := hpkg (φit k) hm_k hbcap_k ha_k
      have hfun : φit (k + 1) = fun ζ => φit k ζ
          - c'⁻¹ * Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) ζ := funext (hφS k)
      -- the four properties at step `k+1`
      have hm_k1 : Measurable (φit (k + 1)) := by
        rw [hfun]
        exact hm_k.sub (measurable_const.mul hLm)
      have hd_k1 : DifferentiableOn ℂ (φit (k + 1)) {v : ℂ | v.im < 0} := by
        rw [hfun]
        exact hd_k.sub (hLd.const_mul c'⁻¹)
      have ha_k1 : ∀ γ, γ ∈ Γ → ∀ v : ℂ, v.im < 0 →
          φit (k + 1) (moebiusMap γ v) = φit (k + 1) v * (moebiusDenom γ v) ^ 4 := by
        intro γ hγ v hv
        calc φit (k + 1) (moebiusMap γ v)
            = φit k (moebiusMap γ v) - c'⁻¹
              * Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) (moebiusMap γ v) := hφS k _
          _ = φit k v * (moebiusDenom γ v) ^ 4 - c'⁻¹
              * (Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v
                * (moebiusDenom γ v) ^ 4) := by
              rw [ha_k γ hγ v hv, hLa γ hγ v hv]
          _ = (φit k v - c'⁻¹ * Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v)
              * (moebiusDenom γ v) ^ 4 := by ring
          _ = φit (k + 1) v * (moebiusDenom γ v) ^ 4 := by rw [← hφS k v]
      have hb_k1 : ∀ v : ℂ, v.im < 0 →
          (2 * v.im) ^ 2 * ‖φit (k + 1) v‖ ≤ β * (1 - (1 / 2) ^ (k + 1)) := by
        intro v hv
        have htri : ‖φit (k + 1) v‖ ≤ ‖φit k v‖ + ‖φit (k + 1) v - φit k v‖ := by
          have h := norm_add_le (φit k v) (φit (k + 1) v - φit k v)
          rwa [add_sub_cancel] at h
        have h1 := hb_k v hv
        have h2 := hdb_k v hv
        have h3 : (2 * v.im) ^ 2 * ‖φit (k + 1) v‖
            ≤ (2 * v.im) ^ 2 * ‖φit k v‖
              + (2 * v.im) ^ 2 * ‖φit (k + 1) v - φit k v‖ := by
          have := mul_le_mul_of_nonneg_left htri (hy2 v hv).le
          linarith only [this]
        have hgeom : β * (1 - (1 / 2 : ℝ) ^ k) + D * (1 / 2) ^ k
            = β * (1 - (1 / 2) ^ (k + 1)) := by
          rw [hβdef, pow_succ]
          ring
        linarith only [h1, h2, h3, hgeom]
      refine ⟨⟨hm_k1, hd_k1, ha_k1, hb_k1⟩, ?_⟩
      -- the geometric decay of the increments
      intro v hv
      have hδm : Measurable fun w => φit (k + 1) w - φit k w := hm_k1.sub hm_k
      have hδd : DifferentiableOn ℂ (fun w => φit (k + 1) w - φit k w)
          {v : ℂ | v.im < 0} := hd_k1.sub hd_k
      have hbψ0 : (0 : ℝ) ≤ β * (1 - (1 / 2) ^ k) := by
        have hp1 : (1 / 2 : ℝ) ^ k ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith only [hβ0, hp1]
      have hbδ0 : (0 : ℝ) < D * (1 / 2) ^ k := by positivity
      have hψβ : β * (1 - (1 / 2 : ℝ) ^ k) ≤ β := by
        have hp1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
        nlinarith only [hβ0, hp1]
      have hδβ : D * (1 / 2 : ℝ) ^ k ≤ β := by
        have hp1 : (1 / 2 : ℝ) ^ k ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        rw [hβdef]
        nlinarith only [hD0, hp1]
      have hkey' := hkey (φit k) (fun w => φit (k + 1) w - φit k w)
        (β * (1 - (1 / 2) ^ k)) (D * (1 / 2) ^ k) hm_k hδm hd_k hδd hbψ0 hbδ0
        hb_k hdb_k hψβ hδβ v hv
      -- identify the two coefficients
      have hid1 : (fun ζ => ((t : ℂ) * η ζ + Sop (φit k) ζ)
            + 1 * Sop (fun w => φit (k + 1) w - φit k w) ζ)
          = fun ξ => (t : ℂ) * η ξ + Sop (φit (k + 1)) ξ := by
        funext ζ
        rw [hSsplit (φit (k + 1)) (φit k) ζ]
        ring
      have hid0 : (fun ζ => ((t : ℂ) * η ζ + Sop (φit k) ζ)
            + 0 * Sop (fun w => φit (k + 1) w - φit k w) ζ)
          = fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ := by
        funext ζ
        ring
      rw [hid1, hid0] at hkey'
      -- the increment identity
      have hΔ : φit (k + 2) v - φit (k + 1) v
          = -(c'⁻¹ * (Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit (k + 1)) ξ) v
            - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v
            - c' * (φit (k + 1) v - φit k v))) := by
        have e1 := hφS (k + 1) v
        have e2 := hφS k v
        have hinv1 : c'⁻¹ * c' = 1 := inv_mul_cancel₀ hc'0
        rw [e1]
        linear_combination (-1 : ℂ) * e2 - (φit (k + 1) v - φit k v) * hinv1
      rw [hΔ, norm_neg, norm_mul, norm_inv]
      have h2 : (2 * v.im) ^ 2 * (‖c'‖⁻¹
          * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit (k + 1)) ξ) v
            - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v
            - c' * (φit (k + 1) v - φit k v)‖)
          = ‖c'‖⁻¹ * ((2 * v.im) ^ 2
            * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit (k + 1)) ξ) v
              - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v
              - c' * (φit (k + 1) v - φit k v)‖) := by ring
      rw [h2]
      have h3 : ‖c'‖⁻¹ * ((2 * v.im) ^ 2
          * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit (k + 1)) ξ) v
            - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v
            - c' * (φit (k + 1) v - φit k v)‖)
          ≤ ‖c'‖⁻¹ * (Q / 2 * (D * (1 / 2) ^ k)) :=
        mul_le_mul_of_nonneg_left hkey' (by positivity)
      refine h3.trans (le_of_eq ?_)
      rw [hQdef, pow_succ]
      field_simp
  -- ==================================================================
  -- ## Part 10: passage to the limit.
  -- ==================================================================
  -- the Lipschitz continuity of the Bers map along the correction
  have hΛLip : ∀ (ψ δ : ℂ → ℂ) (bδ : ℝ), Measurable ψ → Measurable δ →
      (∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖ψ v‖ ≤ β) → 0 < bδ →
      (∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖δ v‖ ≤ bδ) → bδ ≤ β →
      ∀ z : ℂ, z.im < 0 →
      (2 * z.im) ^ 2 * ‖Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 1 * Sop δ ζ) z
        - Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + 0 * Sop δ ζ) z‖ ≤ 24 * P * bδ := by
    intro ψ δ bδ hψm hδm hψb hbδ0 hδb hδβ z hz
    have hy2z := hy2 z hz
    have hbase_meas : Measurable fun ζ => (t : ℂ) * η ζ + Sop ψ ζ :=
      (measurable_const.mul hmeas).add (hSmeas ψ hψm)
    have hbase_bd8 : ∀ ζ, ‖(t : ℂ) * η ζ + Sop ψ ζ‖ ≤ 1 / 8 := by
      intro ζ
      refine (norm_add_le _ _).trans ?_
      have h2 : ‖Sop ψ ζ‖ ≤ P * β := hSboundP ψ β hβ0.le hψb ζ
      linarith only [h2, htηb ζ, hN1]
    have hbase_supp : ∀ ζ : ℂ, ζ.im ≤ 0 → (t : ℂ) * η ζ + Sop ψ ζ = 0 := fun ζ hζ => by
      rw [hsupp ζ hζ, hSsupp ψ ζ hζ, mul_zero, add_zero]
    have hδS_bd : ∀ ζ, ‖Sop δ ζ‖ ≤ P * bδ := hSboundP δ bδ hbδ0.le hδb
    have hPbδ : 0 < P * bδ := mul_pos hP0 hbδ0
    have hPbδ16 : P * bδ ≤ 1 / 16 := (mul_le_mul_of_nonneg_left hδβ hP0.le).trans hβS2
    obtain ⟨hg₁N, hg₁D, -⟩ := hfamA (fun ζ => (t : ℂ) * η ζ + Sop ψ ζ) (Sop δ)
      (1 / 8) (P * bδ) hbase_meas (hSmeas δ hδm) hbase_bd8 hδS_bd hbase_supp (hSsupp δ)
      (by norm_num) hPbδ z hz
    have hR₁2 : 2 ≤ (1 - 1 / 8) / (P * bδ) := by
      rw [le_div_iff₀ hPbδ]
      linarith only [hPbδ16]
    have hg₁b : ∀ u ∈ Metric.ball (0 : ℂ) ((1 - 1 / 8) / (P * bδ)),
        ‖Λ (fun ζ => ((t : ℂ) * η ζ + Sop ψ ζ) + u * Sop δ ζ) z‖
          ≤ 6 / (2 * z.im) ^ 2 := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      have h := hg₁N u hu
      rw [le_div_iff₀ hy2z, mul_comm]
      exact h
    have hL := hLip _ _ _ hR₁2 hg₁D hg₁b
    have hle := mul_le_mul_of_nonneg_left hL hy2z.le
    refine hle.trans ?_
    have hy2ne : (2 * z.im) ^ 2 ≠ 0 := ne_of_gt hy2z
    have hzim : z.im ≠ 0 := ne_of_lt hz
    have hPbδne : P * bδ ≠ 0 := ne_of_gt hPbδ
    have heq : (2 * z.im) ^ 2 * (3 * (6 / (2 * z.im) ^ 2) / ((1 - 1 / 8) / (P * bδ)))
        = 144 / 7 * (P * bδ) := by
      field_simp
      ring
    rw [heq]
    linarith only [hPbδ]
  -- pointwise limits of the iteration
  have hexlim : ∀ ζ : ℂ, ∃ L : ℂ,
      Filter.Tendsto (fun k => if ζ.im < 0 then φit k ζ else 0) Filter.atTop (nhds L) := by
    intro ζ
    by_cases hζ : ζ.im < 0
    · simp only [if_pos hζ]
      have hy2ζ := hy2 ζ hζ
      have hCau : CauchySeq fun k => φit k ζ := by
        refine cauchySeq_of_le_geometric (1 / 2) (D / (2 * ζ.im) ^ 2) (by norm_num) ?_
        intro n
        rw [dist_eq_norm, norm_sub_rev, div_mul_eq_mul_div, le_div_iff₀ hy2ζ]
        have h := (hIND n).2 ζ hζ
        linarith only [h]
      exact cauchySeq_tendsto_of_complete hCau
    · exact ⟨0, by simp only [if_neg hζ]; exact tendsto_const_nhds⟩
  choose glim hglim using hexlim
  have hgmeas : Measurable glim := by
    refine measurable_of_tendsto_metrizable
      (f := fun k ζ => if ζ.im < 0 then φit k ζ else 0)
      (fun k => Measurable.ite hlowopen.measurableSet (hIND k).1.1 measurable_const)
      (tendsto_pi_nhds.mpr hglim)
  have hglow : ∀ ζ : ℂ, ζ.im < 0 →
      Filter.Tendsto (fun k => φit k ζ) Filter.atTop (nhds (glim ζ)) := by
    intro ζ hζ
    have h := hglim ζ
    simp only [if_pos hζ] at h
    exact h
  -- the geometric tail bound
  have htail : ∀ (k : ℕ) (v : ℂ), v.im < 0 →
      (2 * v.im) ^ 2 * ‖glim v - φit k v‖ ≤ 2 * D * (1 / 2) ^ k := by
    intro k v hv
    have hstep : ∀ j : ℕ, (2 * v.im) ^ 2 * ‖φit (k + j) v - φit k v‖
        ≤ 2 * D * (1 / 2) ^ k * (1 - (1 / 2) ^ j) := by
      intro j
      induction j with
      | zero => simp [sub_self]
      | succ j ihj =>
        have h1 := (hIND (k + j)).2 v hv
        have htri : ‖φit (k + (j + 1)) v - φit k v‖
            ≤ ‖φit (k + j + 1) v - φit (k + j) v‖ + ‖φit (k + j) v - φit k v‖ := by
          have h := norm_add_le (φit (k + j + 1) v - φit (k + j) v)
            (φit (k + j) v - φit k v)
          rwa [sub_add_sub_cancel] at h
        have h3 : (2 * v.im) ^ 2 * ‖φit (k + (j + 1)) v - φit k v‖
            ≤ (2 * v.im) ^ 2 * ‖φit (k + j + 1) v - φit (k + j) v‖
              + (2 * v.im) ^ 2 * ‖φit (k + j) v - φit k v‖ := by
          have h := mul_le_mul_of_nonneg_left htri (hy2 v hv).le
          linarith only [h, h1, ihj]
        have hgeo : D * (1 / 2 : ℝ) ^ (k + j) + 2 * D * (1 / 2) ^ k * (1 - (1 / 2) ^ j)
            = 2 * D * (1 / 2) ^ k * (1 - (1 / 2) ^ (j + 1)) := by
          rw [pow_add, pow_succ]
          ring
        linarith only [h1, h3, hgeo, ihj]
    have hlim2 : Filter.Tendsto (fun j => (2 * v.im) ^ 2 * ‖φit (k + j) v - φit k v‖)
        Filter.atTop (nhds ((2 * v.im) ^ 2 * ‖glim v - φit k v‖)) := by
      have h1 : Filter.Tendsto (fun j : ℕ => k + j) Filter.atTop Filter.atTop := by
        have h := Filter.tendsto_add_atTop_nat k
        have he : (fun j : ℕ => k + j) = fun j : ℕ => j + k :=
          funext fun j => Nat.add_comm k j
        rwa [he]
      have h2 : Filter.Tendsto (fun j => φit (k + j) v) Filter.atTop (nhds (glim v)) :=
        (hglow v hv).comp h1
      exact ((h2.sub_const (φit k v)).norm).const_mul _
    refine le_of_tendsto hlim2 (Filter.Eventually.of_forall fun j => (hstep j).trans ?_)
    nlinarith only [(by positivity : (0 : ℝ) ≤ 2 * D * (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ j)]
  -- holomorphy of the limit
  have hgdiff : DifferentiableOn ℂ glim {v : ℂ | v.im < 0} := by
    refine TendstoLocallyUniformlyOn.differentiableOn (F := fun k => φit k)
      (φ := Filter.atTop) ?_
      (Filter.Eventually.of_forall fun k => (hIND k).1.2.1) hlowopen
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hlowopen]
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact tendstoUniformlyOn_empty
    have hcont : ContinuousOn (fun v : ℂ => (2 * v.im) ^ 2) K :=
      ((continuous_const.mul Complex.continuous_im).pow 2).continuousOn
    obtain ⟨v₀, hv₀K, hv₀min⟩ := hK.exists_isMinOn hKne hcont
    have hc0 : 0 < (2 * v₀.im) ^ 2 := hy2 v₀ (hKsub hv₀K)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε' hε'
    have htend : Filter.Tendsto (fun k : ℕ => 2 * D * (1 / 2 : ℝ) ^ k)
        Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      simpa using h.const_mul (2 * D)
    have hev := htend.eventually_lt_const
      (by positivity : (0 : ℝ) < ε' * (2 * v₀.im) ^ 2)
    filter_upwards [hev] with k hk v hvK
    rw [dist_eq_norm]
    have hvlow : v.im < 0 := hKsub hvK
    have h1 := htail k v hvlow
    have h2 : (2 * v₀.im) ^ 2 ≤ (2 * v.im) ^ 2 := hv₀min hvK
    have hy2v := hy2 v hvlow
    nlinarith only [h1, hk, hy2v, hε', norm_nonneg (glim v - φit k v),
      mul_le_mul_of_nonneg_left h2 hε'.le]
  -- bound and automorphy of the limit
  have hgbound : ∀ v : ℂ, v.im < 0 → (2 * v.im) ^ 2 * ‖glim v‖ ≤ β := by
    intro v hv
    refine le_of_tendsto (((hglow v hv).norm).const_mul ((2 * v.im) ^ 2))
      (Filter.Eventually.of_forall fun k => ?_)
    refine ((hIND k).1.2.2.2 v hv).trans ?_
    have hp1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    nlinarith only [hβ0, hp1]
  have hgauto : ∀ γ, γ ∈ Γ → ∀ v : ℂ, v.im < 0 →
      glim (moebiusMap γ v) = glim v * (moebiusDenom γ v) ^ 4 := by
    intro γ hγ v hv
    have hγv : (moebiusMap γ v).im < 0 := moebiusMap_im_neg γ hv
    have h1 := hglow _ hγv
    have h2 := (hglow v hv).mul_const ((moebiusDenom γ v) ^ 4)
    have hev : (fun k => φit k (moebiusMap γ v))
        = fun k => φit k v * (moebiusDenom γ v) ^ 4 :=
      funext fun k => (hIND k).1.2.2.1 γ hγ v hv
    rw [hev] at h1
    exact tendsto_nhds_unique h1 h2
  -- the limiting defect vanishes
  have hgdefect : ∀ v : ℂ, v.im < 0 →
      Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v = 0 := by
    intro v hv
    have hy2v := hy2 v hv
    have hinv2 : c' * c'⁻¹ = 1 := mul_inv_cancel₀ hc'0
    have hbnd : ∀ k : ℕ, (2 * v.im) ^ 2 * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v‖
        ≤ (48 * P * D + Q * D) * (1 / 2) ^ k := by
      intro k
      obtain ⟨⟨hm_k, hd_k, ha_k, hb_k⟩, hdb_k⟩ := hIND k
      have hbcap_k : ∀ u : ℂ, u.im < 0 → (2 * u.im) ^ 2 * ‖φit k u‖ ≤ β := by
        intro u hu
        refine (hb_k u hu).trans ?_
        have hp1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
        nlinarith only [hβ0, hp1]
      have hbδ0 : (0 : ℝ) < 2 * D * (1 / 2) ^ k := by positivity
      have hδβ : 2 * D * (1 / 2 : ℝ) ^ k ≤ β := by
        have hp1 : (1 / 2 : ℝ) ^ k ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        rw [hβdef]
        nlinarith only [hD0, hp1]
      have hLc := hΛLip (φit k) (fun w => glim w - φit k w) (2 * D * (1 / 2) ^ k)
        hm_k (hgmeas.sub hm_k) hbcap_k hbδ0 (fun u hu => htail k u hu) hδβ v hv
      have hidg : (fun ζ => ((t : ℂ) * η ζ + Sop (φit k) ζ)
            + 1 * Sop (fun w => glim w - φit k w) ζ)
          = fun ξ => (t : ℂ) * η ξ + Sop glim ξ := by
        funext ζ
        rw [hSsplit glim (φit k) ζ]
        ring
      have hidg0 : (fun ζ => ((t : ℂ) * η ζ + Sop (φit k) ζ)
            + 0 * Sop (fun w => glim w - φit k w) ζ)
          = fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ := by
        funext ζ
        ring
      rw [hidg, hidg0] at hLc
      -- the defect of the `k`-th iterate
      have hΛval : Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v
          = c' * (φit k v - φit (k + 1) v) := by
        have e2 := hφS k v
        linear_combination c' * e2
          - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v * hinv2
      have hdef_k : (2 * v.im) ^ 2 * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v‖
          ≤ Q * (D * (1 / 2) ^ k) := by
        rw [hΛval, norm_mul, ← hQdef, norm_sub_rev]
        have h := hdb_k v hv
        calc (2 * v.im) ^ 2 * (Q * ‖φit (k + 1) v - φit k v‖)
            = Q * ((2 * v.im) ^ 2 * ‖φit (k + 1) v - φit k v‖) := by ring
          _ ≤ Q * (D * (1 / 2) ^ k) := mul_le_mul_of_nonneg_left h hQ0.le
      -- triangle
      have htri : ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v‖
          ≤ ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v
              - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v‖
            + ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v‖ := by
        have h := norm_add_le (Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v
          - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v)
          (Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v)
        rwa [sub_add_cancel] at h
      have h4 : (2 * v.im) ^ 2 * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v‖
          ≤ (2 * v.im) ^ 2 * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v
              - Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v‖
            + (2 * v.im) ^ 2 * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop (φit k) ξ) v‖ := by
        have h := mul_le_mul_of_nonneg_left htri hy2v.le
        linarith only [h]
      have h5 : 24 * P * (2 * D * (1 / 2 : ℝ) ^ k) + Q * (D * (1 / 2) ^ k)
          = (48 * P * D + Q * D) * (1 / 2) ^ k := by ring
      linarith only [hLc, hdef_k, h4, h5]
    have htend0 : Filter.Tendsto (fun k : ℕ => (48 * P * D + Q * D) * (1 / 2 : ℝ) ^ k)
        Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      simpa using h.const_mul (48 * P * D + Q * D)
    have hle0 : (2 * v.im) ^ 2 * ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v‖ ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds htend0 hbnd
    have hn0 : ‖Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v‖ ≤ 0 := by
      nlinarith only [hle0, hy2v, norm_nonneg (Λ (fun ξ => (t : ℂ) * η ξ + Sop glim ξ) v)]
    exact norm_le_zero_iff.mp hn0
  -- ==================================================================
  -- ## Part 11: assembly of the conclusion.
  -- ==================================================================
  have hσmeas : Measurable fun ζ => (t : ℂ) * η ζ + Sop glim ζ :=
    (measurable_const.mul hmeas).add (hSmeas glim hgmeas)
  have hσb : ∀ ζ, ‖(t : ℂ) * η ζ + Sop glim ζ‖ ≤ 1 / 2 := by
    intro ζ
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖Sop glim ζ‖ ≤ P * β := hSboundP glim β hβ0.le hgbound ζ
    linarith only [h2, htηb ζ, hN1]
  have hσsupp : ∀ ζ : ℂ, ζ.im ≤ 0 → (t : ℂ) * η ζ + Sop glim ζ = 0 := by
    intro ζ hζ
    rw [hsupp ζ hζ, hSsupp glim ζ hζ, mul_zero, add_zero]
  obtain ⟨w, b, hbμ, hwqc, hw0, hw1, hΛw, hwconf, -⟩ := hsol _ hσmeas hσb hσsupp
  have hσinv : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ((t : ℂ) * η (moebiusMap W z) + Sop glim (moebiusMap W z)) * (moebiusDenom W z) ^ 2
        = ((t : ℂ) * η z + Sop glim z) * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
    intro W hW
    filter_upwards [hinv W hW, ae_restrict_mem hupmeas] with z h1 h2
    have h3 := hSinv glim hgauto W hW z h2
    calc ((t : ℂ) * η (moebiusMap W z) + Sop glim (moebiusMap W z))
          * (moebiusDenom W z) ^ 2
        = (t : ℂ) * (η (moebiusMap W z) * (moebiusDenom W z) ^ 2)
          + Sop glim (moebiusMap W z) * (moebiusDenom W z) ^ 2 := by ring
      _ = (t : ℂ) * (η z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2)
          + Sop glim z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by rw [h1, h3]
      _ = ((t : ℂ) * η z + Sop glim z) * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
          ring
  have hS0 : ∀ z : ℂ, z.im < 0 → schwarzian w z = 0 := by
    intro z hz
    rw [← hΛw]
    exact hgdefect z hz
  have hbz : ∀ z : ℂ, z.im ≤ 0 → b.μ z = 0 := by
    intro z hz
    rw [hbμ]
    exact hσsupp z hz
  have hbinv : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      b.μ (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = b.μ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
    intro W hW
    filter_upwards [hσinv W hW] with z hz
    rw [hbμ, hbμ]
    exact hz
  have hid := eq_id_on_lower_of_schwarzian_eq_zero hwqc hbz hw0 hw1 hS0
  have hcomm := moebiusMap_comm_of_eq_id_lower hwqc hbz hbinv hid
  refine ⟨fun ζ => (t : ℂ) * η ζ + Sop glim ζ, w, b, hσmeas, hσsupp, hσinv, ?_,
    hbμ, hwqc, hid, hcomm⟩
  intro z
  rw [show (t : ℂ) * η z + Sop glim z - (t : ℂ) * η z = Sop glim z from by ring]
  exact (hSboundP glim β hβ0.le hgbound z).trans hN3

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.GaussBonnet
import RiemannDynamics.Teichmuller.ModuliAction.ModAction
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Holomorphic quadratic differentials over a Fuchsian base

A holomorphic quadratic differential for `Γ ≤ SL(2, ℝ)` is a weight-4 automorphic function
on the upper half plane: a plane function `q`, holomorphic on `{0 < im}`, with
`q (γ z) = (c z + d)⁴ q z` for every `γ ∈ Γ`. The tensor `q dz²` is then `Γ`-invariant:
the flat length density `|q|^{1/2} |dz|` and the Euclidean area density `|q| dx dy` both
descend to the quotient surface. The file provides the carrier, its module operations, the
invariance of the area density, the `L¹` mass over the canonical Dirichlet domain, the
Teichmüller Beltrami coefficient `k conj q / |q|` of a differential, and the bridge to
Mathlib's weight-4 slash-invariant forms.
-/

open MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups ModularForm Manifold

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A **holomorphic quadratic differential** for the Fuchsian group `Γ`, as a weight-4
automorphic function on the upper half plane: `q (γ z) = (c z + d)⁴ q z`. The function is
carried by the whole plane (values off the closed upper half plane are junk), with global
measurability and holomorphy on the open upper half plane. -/
structure QuadraticDifferential (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) where
  /-- The underlying plane function. -/
  toFun : ℂ → ℂ
  /-- Global measurability of the plane carrier. -/
  measurable : Measurable toFun
  /-- Holomorphy on the open upper half plane. -/
  holo : DifferentiableOn ℂ toFun {z : ℂ | 0 < z.im}
  /-- The weight-4 automorphy law. -/
  automorphy : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
    toFun (moebiusMap γ z) = moebiusDenom γ z ^ 4 * toFun z

instance : CoeFun (QuadraticDifferential Γ) (fun _ => ℂ → ℂ) := ⟨QuadraticDifferential.toFun⟩

/-- Equality of quadratic differentials on the upper half plane. Off the upper half plane
the carriers are unconstrained, so this is the meaningful equality relation. -/
def QuadraticDifferential.EqOnUpper (q q' : QuadraticDifferential Γ) : Prop :=
  ∀ z : ℂ, 0 < z.im → q z = q' z

instance : Zero (QuadraticDifferential Γ) where
  zero := { toFun := fun _ => 0
            measurable := measurable_const
            holo := differentiableOn_const 0
            automorphy := fun _ _ _ _ => (mul_zero _).symm }

@[simp] theorem QuadraticDifferential.zero_apply (z : ℂ) :
    (0 : QuadraticDifferential Γ) z = 0 := rfl

instance : Add (QuadraticDifferential Γ) where
  add q q' := { toFun := fun z => q z + q' z
                measurable := q.measurable.add q'.measurable
                holo := q.holo.add q'.holo
                automorphy := fun γ hγ z hz => by
                  simp only [q.automorphy γ hγ z hz, q'.automorphy γ hγ z hz]; ring }

@[simp] theorem QuadraticDifferential.add_apply (q q' : QuadraticDifferential Γ) (z : ℂ) :
    (q + q') z = q z + q' z := rfl

instance : SMul ℂ (QuadraticDifferential Γ) where
  smul c q := { toFun := fun z => c * q z
                measurable := measurable_const.mul q.measurable
                holo := q.holo.const_mul c
                automorphy := fun γ hγ z hz => by
                  simp only [q.automorphy γ hγ z hz]; ring }

@[simp] theorem QuadraticDifferential.smul_apply (c : ℂ) (q : QuadraticDifferential Γ)
    (z : ℂ) : (c • q) z = c * q z := rfl

/-- A quadratic differential is continuous on the open upper half plane. -/
theorem QuadraticDifferential.continuousOn_upper (q : QuadraticDifferential Γ) :
    ContinuousOn q {z : ℂ | 0 < z.im} :=
  q.holo.continuousOn

/-! ## Möbius calculus off the real axis -/

/-- On the upper half plane the plane Möbius map of `γ ∈ SL(2, ℝ)` is complex differentiable
with derivative `(c z + d)⁻²`. -/
theorem hasDerivAt_moebiusMap_of_im_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : HasDerivAt (moebiusMap γ) (((moebiusDenom γ z) ^ 2)⁻¹) z :=
  hasDerivAt_moebiusMap γ (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')

/-- The `deriv` form of `hasDerivAt_moebiusMap_of_im_pos`. -/
theorem deriv_moebiusMap_of_im_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : deriv (moebiusMap γ) z = ((moebiusDenom γ z) ^ 2)⁻¹ :=
  (hasDerivAt_moebiusMap_of_im_pos γ hz).deriv

/-- The weight-4 laws for `γ₁` and `γ₂` compose to the law for `γ₁ * γ₂`, via the cocycle
identity of `moebiusDenom`. -/
theorem weight4_automorphy_mul (q : ℂ → ℂ) (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h₁ : ∀ z : ℂ, 0 < z.im → q (moebiusMap γ₁ z) = (moebiusDenom γ₁ z) ^ 4 * q z)
    (h₂ : ∀ z : ℂ, 0 < z.im → q (moebiusMap γ₂ z) = (moebiusDenom γ₂ z) ^ 4 * q z)
    {z : ℂ} (hz : 0 < z.im) :
    q (moebiusMap (γ₁ * γ₂) z) = (moebiusDenom (γ₁ * γ₂) z) ^ 4 * q z := by
  have hd₂ : moebiusDenom γ₂ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ₂ hz.ne'
  have him : 0 < (moebiusMap γ₂ z).im := moebiusMap_im_pos γ₂ hz
  rw [← moebiusMap_mul γ₁ γ₂ z hd₂, h₁ _ him, h₂ z hz, ← moebiusDenom_mul γ₁ γ₂ z hd₂]
  ring

/-- The Jacobian of the plane Möbius map off the real axis: the determinant of the real
Fréchet derivative is `‖moebiusDenom γ z‖⁻⁴`. -/
theorem det_fderiv_moebiusMap_of_im_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : (fderiv ℝ (moebiusMap γ) z).det = (‖moebiusDenom γ z‖ ^ 4)⁻¹ := by
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have hder := hasDerivAt_moebiusMap γ hd
  have hdiff : DifferentiableAt ℂ (moebiusMap γ) z := hder.differentiableAt
  have hnd : ‖moebiusDenom γ z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  rw [det_fderiv_eq_wirtinger, dzbar_eq_zero_of_differentiableAt hdiff,
    dz_eq_deriv_of_differentiableAt hdiff, hder.deriv]
  rw [norm_zero, norm_inv, norm_pow]
  field_simp
  ring

set_option maxHeartbeats 400000 in
-- The change-of-variables step elaborates the full Jacobian formula on `ℂ` together with
-- ENNReal/enorm rewriting; the default heartbeat budget is exceeded in this single proof.
/-- **Invariance of the area density**: for a weight-4 automorphic `q` and a measurable
`S` inside the upper half plane, the Euclidean mass `∫⁻ |q|` over `moebiusMap γ '' S`
equals the one over `S` — the Jacobian `‖denom‖⁻⁴` cancels the automorphy factor. -/
theorem lintegral_enorm_moebiusMap_image (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {q : ℂ → ℂ} (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γ z) = (moebiusDenom γ z) ^ 4 * q z)
    {S : Set ℂ} (hSmeas : MeasurableSet S) (hS : S ⊆ {z : ℂ | 0 < z.im}) :
    ∫⁻ w in moebiusMap γ '' S, ‖q w‖ₑ = ∫⁻ z in S, ‖q z‖ₑ := by
  have hfd : ∀ z ∈ S, HasFDerivWithinAt (moebiusMap γ) (fderiv ℝ (moebiusMap γ) z) S z := by
    intro z hzS
    have hd : moebiusDenom γ z ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero γ (hS hzS).ne'
    exact (((hasDerivAt_moebiusMap γ hd).complexToReal_fderiv).differentiableAt.hasFDerivAt
      ).hasFDerivWithinAt
  have hinj : Set.InjOn (moebiusMap γ) S := by
    intro x hx y hy hxy
    have hdx : moebiusDenom γ x ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (hS hx).ne'
    have hdy : moebiusDenom γ y ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (hS hy).ne'
    have h1 : moebiusMap γ⁻¹ (moebiusMap γ x) = x := by
      rw [moebiusMap_mul γ⁻¹ γ x hdx, inv_mul_cancel, moebiusMap_one]
    have h2 : moebiusMap γ⁻¹ (moebiusMap γ y) = y := by
      rw [moebiusMap_mul γ⁻¹ γ y hdy, inv_mul_cancel, moebiusMap_one]
    rw [← h1, ← h2, hxy]
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinj
    (fun w => ‖q w‖ₑ)
  rw [hcov]
  refine setLIntegral_congr_fun hSmeas (fun z hzS => ?_)
  have hzim : 0 < z.im := hS hzS
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hzim.ne'
  have hnd : ‖moebiusDenom γ z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  rw [det_fderiv_moebiusMap_of_im_pos γ hzim, abs_of_nonneg (by positivity), hq z hzim,
    ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [norm_mul, norm_pow]
  field_simp

/-- Bundled invariance: the `|q| dA` mass of a quadratic differential is `Γ`-invariant on
subsets of the upper half plane. -/
theorem QuadraticDifferential.lintegral_enorm_image (q : QuadraticDifferential Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    {S : Set ℂ} (hSmeas : MeasurableSet S) (hS : S ⊆ {z : ℂ | 0 < z.im}) :
    ∫⁻ w in moebiusMap γ '' S, ‖q w‖ₑ = ∫⁻ z in S, ‖q z‖ₑ :=
  lintegral_enorm_moebiusMap_image γ (fun z hz => q.automorphy γ hγ z hz) hSmeas hS

/-! ## The zero set and the `L¹` mass -/

/-- **Identity theorem, null form**: a function holomorphic on the open upper half plane
which is not identically zero there vanishes only on a Lebesgue-null set — its zeros are
isolated in the connected open set `{0 < im}`, hence countable. -/
theorem ae_ne_zero_of_differentiableOn {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), q z ≠ 0 := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have han : AnalyticOnNhd ℂ q {z : ℂ | 0 < z.im} := hq.analyticOnNhd hUopen
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected hUconn with h | h
  · obtain ⟨z, hz, hqz⟩ := hq0
    exact absurd (h hz) hqz
  · exact ae_restrict_le_codiscreteWithin hUopen.measurableSet h

/-- A quadratic differential that is somewhere nonzero on the upper half plane is almost
everywhere nonzero there. -/
theorem QuadraticDifferential.ae_ne_zero (q : QuadraticDifferential Γ)
    (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), q z ≠ 0 :=
  ae_ne_zero_of_differentiableOn q.holo hq0

/-- The **`L¹` mass** of a quadratic differential: the Euclidean integral of `|q|` over the
canonical Dirichlet domain at `i`, viewed inside the plane. This is the flat area of the
quotient surface in the `|q|^{1/2} |dz|` metric. -/
noncomputable def QuadraticDifferential.l1Norm (q : QuadraticDifferential Γ) : ℝ≥0∞ :=
  ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, ‖q z‖ₑ

/-- For a cocompact free Fuchsian base the `L¹` mass is finite: the Dirichlet domain is
compact and `|q|` is continuous on it. -/
theorem QuadraticDifferential.l1Norm_ne_top (q : QuadraticDifferential Γ)
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    q.l1Norm ≠ ⊤ := by
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  have hdef : q.l1Norm
      = ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, ‖q z‖ₑ := rfl
  rw [hdef]
  set K : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hKdef
  have hKc : IsCompact K :=
    (isCompact_dirichletDomain hdense).image UpperHalfPlane.continuous_coe
  have hsub : K ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hcont : ContinuousOn q K := q.continuousOn_upper.mono hsub
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  have hbound : (∫⁻ z in K, ‖q z‖ₑ) ≤ ENNReal.ofReal C * volume K := by
    rw [← setLIntegral_const K (ENNReal.ofReal C)]
    refine setLIntegral_mono' hKc.measurableSet fun z hz => ?_
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC z hz)
  have hfin : ENNReal.ofReal C * volume K < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top
  exact (lt_of_le_of_lt hbound hfin).ne

/-! ## The Teichmüller Beltrami coefficient -/

/-- The **Teichmüller Beltrami coefficient** of modulus `k` attached to a plane function
`q`: the coefficient `k conj q / |q|`, extended by `0` across the zeros of `q`. -/
noncomputable def teichmullerCoeffFun (q : ℂ → ℂ) (k : ℝ) : ℂ → ℂ := fun z =>
  (k : ℂ) * starRingEnd ℂ (q z) * ((‖q z‖⁻¹ : ℝ) : ℂ)

/-- Measurability of the Teichmüller coefficient. -/
theorem teichmullerCoeffFun_measurable {q : ℂ → ℂ} (hq : Measurable q) (k : ℝ) :
    Measurable (teichmullerCoeffFun q k) :=
  (measurable_const.mul (Complex.continuous_conj.measurable.comp hq)).mul
    (Complex.measurable_ofReal.comp hq.norm.inv)

/-- The Teichmüller coefficient has modulus at most `k` everywhere. -/
theorem norm_teichmullerCoeffFun_le {q : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (z : ℂ) :
    ‖teichmullerCoeffFun q k z‖ ≤ k := by
  unfold teichmullerCoeffFun
  rcases eq_or_ne (q z) 0 with h | h
  · simp [h, hk0]
  · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk0,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), mul_assoc,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), mul_one]

/-- The essential supremum bound of the Teichmüller coefficient on the upper half plane. -/
theorem eLpNormEssSup_teichmullerCoeffFun_lt_one {q : ℂ → ℂ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    eLpNormEssSup (teichmullerCoeffFun q k)
      (volume.restrict {z : ℂ | 0 < z.im}) < 1 := by
  refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound
    (Filter.Eventually.of_forall fun z => norm_teichmullerCoeffFun_le hk0 z)) ?_
  exact ENNReal.ofReal_lt_one.mpr hk1

/-- Algebraic core: the denominator cocycle of the Teichmüller coefficient. -/
theorem teichmullerCoeff_key (k : ℝ) (d a : ℂ) (hd : d ≠ 0) :
    (k : ℂ) * starRingEnd ℂ (d ^ 4 * a) * ((‖d ^ 4 * a‖⁻¹ : ℝ) : ℂ) * d ^ 2
      = (k : ℂ) * starRingEnd ℂ a * ((‖a‖⁻¹ : ℝ) : ℂ) * starRingEnd ℂ d ^ 2 := by
  rcases eq_or_ne a 0 with h0 | h0
  · simp [h0]
  · have hqn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have hcd : starRingEnd ℂ d ≠ 0 := by simpa using hd
    have hAn : ((‖a‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqn
    have hns : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * starRingEnd ℂ d := by
      rw [Complex.mul_conj]
      norm_cast
      exact (Complex.normSq_eq_norm_sq _).symm
    have hD4 : ((‖d‖ : ℝ) : ℂ) ^ 4 = d ^ 2 * starRingEnd ℂ d ^ 2 := by
      calc ((‖d‖ : ℝ) : ℂ) ^ 4 = (((‖d‖ : ℝ) : ℂ) ^ 2) ^ 2 := by ring
        _ = (d * starRingEnd ℂ d) ^ 2 := by rw [hns]
        _ = d ^ 2 * starRingEnd ℂ d ^ 2 := by ring
    rw [norm_mul, norm_pow, map_mul, map_pow, mul_inv]
    push_cast
    rw [hD4]
    field_simp

/-- **Invariance law of the Teichmüller coefficient**: for a weight-4 automorphic `q` the
coefficient `k conj q / |q|` satisfies the Beltrami invariance
`μ (γ z) (c z + d)² = μ z conj (c z + d)²` on the upper half plane. -/
theorem teichmullerCoeffFun_invariant (q : QuadraticDifferential Γ) (k : ℝ) :
    ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      teichmullerCoeffFun q k (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = teichmullerCoeffFun q k z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  intro γ hγ z hz
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have haut := q.automorphy γ hγ z hz
  unfold teichmullerCoeffFun
  rw [haut]
  exact teichmullerCoeff_key k (moebiusDenom γ z) (q.toFun z) hd

/-- The almost-everywhere form of `teichmullerCoeffFun_invariant`, as consumed by the
symmetric-extension constructor of Teichmüller representatives. -/
theorem teichmullerCoeffFun_invariant_ae (q : QuadraticDifferential Γ) (k : ℝ) :
    ∀ γ ∈ Γ, ∀ᵐ z : ℂ ∂(volume.restrict {z : ℂ | 0 < z.im}),
      teichmullerCoeffFun q k (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = teichmullerCoeffFun q k z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  intro γ hγ
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  exact (ae_restrict_iff' hU).mpr (Filter.Eventually.of_forall fun z hz =>
    teichmullerCoeffFun_invariant q k γ hγ z hz)

/-- The Teichmüller representative of modulus `k` in the direction of the quadratic
differential `q`: the point of the Bers model with Beltrami coefficient `k conj q / |q|`. -/
noncomputable def teichmullerCoeff (q : QuadraticDifferential Γ) (k : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k < 1) : TeichRep Γ :=
  TeichRep.ofUpper Γ (teichmullerCoeffFun q k)
    (teichmullerCoeffFun_measurable q.measurable k)
    (eLpNormEssSup_teichmullerCoeffFun_lt_one hk0 hk1)
    (teichmullerCoeffFun_invariant_ae q k)

/-- A symmetric extension of a pointwise `k`-bounded datum has `L∞` norm at most `k`. -/
theorem normInf_le_of_symmExtension {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k)
    (hpt : ∀ z : ℂ, ‖μ z‖ ≤ k) {b : BeltramiCoeff} (hb : b.μ = symmExtension μ) :
    b.normInf ≤ k := by
  have hpt' : ∀ z : ℂ, ‖b.μ z‖ ≤ k := by
    intro z
    rw [hb]
    unfold symmExtension
    split_ifs with h
    · exact hpt z
    · rw [Complex.norm_conj]
      exact hpt _
  have hess : eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k :=
    eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hpt')
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
  rwa [ENNReal.toReal_ofReal hk0] at h

/-- Distance to the base point from any representative with `‖μ‖∞ ≤ k`: the inverse of the
normalized solution is a candidate of dilatation `K = (1 + ‖μ‖∞)/(1 − ‖μ‖∞) ≤ (1+k)/(1−k)`. -/
theorem teichPseudoDist_zero_le_of_normInf_le (y : TeichRep Γ) {k : ℝ} (hk1 : k < 1)
    (hnk : y.b.normInf ≤ k) :
    teichPseudoDist (TeichRep.zero Γ) y ≤ 1 / 2 * Real.log ((1 + k) / (1 - k)) := by
  have hzw : (TeichRep.zero Γ).w = id :=
    ((TeichRep.zero Γ).w_unique isQCAnalytic_id rfl rfl).symm
  have hyg : IsQCGeometric y.w y.b.K := y.w_isQCAnalytic.isQCGeometric_K
  have hinv := isQCGeometric_inv_of_isQCGeometric hyg
  have hb : ∀ t : ℝ,
      (hyg.2.1.isHomeomorph.homeomorph y.w).symm (y.w t) = (TeichRep.zero Γ).w t := by
    intro t
    have hcoe : y.w (t : ℂ) = (hyg.2.1.isHomeomorph.homeomorph y.w) (t : ℂ) :=
      (IsHomeomorph.homeomorph_apply _ hyg.2.1.isHomeomorph (t : ℂ)).symm
    rw [hzw, hcoe, Homeomorph.symm_apply_apply]
    rfl
  have h1 := teichPseudoDist_le_of_candidate hinv hb
  have hn0 := y.b.normInf_nonneg
  have hn1 := y.b.normInf_lt_one
  have hKle : y.b.K ≤ (1 + k) / (1 - k) := by
    rw [BeltramiCoeff.K, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hKpos : (0 : ℝ) < y.b.K := lt_of_lt_of_le one_pos y.b.one_le_K
  have hlog := Real.log_le_log hKpos hKle
  linarith

/-- **Distance bound along the Teichmüller ray**: the point of modulus `k` in the direction
of `q` is at Teichmüller pseudodistance at most `½ log ((1 + k) / (1 − k))` from the base
point. -/
theorem teichPseudoDist_teichmullerCoeff_le (q : QuadraticDifferential Γ) {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    teichPseudoDist (TeichRep.zero Γ) (teichmullerCoeff q k hk0 hk1)
      ≤ 1 / 2 * Real.log ((1 + k) / (1 - k)) :=
  teichPseudoDist_zero_le_of_normInf_le (teichmullerCoeff q k hk0 hk1) hk1
    (normInf_le_of_symmExtension hk0
      (fun z => norm_teichmullerCoeffFun_le hk0 z) rfl)

/-! ## Bridge to Mathlib's slash-invariant forms -/

/-- The `GL(2, ℝ)` denominator of `mapGL ℝ γ` agrees with the plane `moebiusDenom`. -/
theorem denom_mapGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z = moebiusDenom γ z := by
  simp [UpperHalfPlane.denom, moebiusDenom, Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- The plane weight-4 law is slash-invariance of weight `4` for the image of `γ` under
`mapGL ℝ : SL(2, ℝ) →* GL(2, ℝ)`. -/
theorem weight4_slashInvariance (q : ℂ → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γ z) = (moebiusDenom γ z) ^ 4 * q z) :
    (fun τ : ℍ => q (τ : ℂ)) ∣[(4 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      = fun τ : ℍ => q (τ : ℂ) := by
  funext τ
  rw [ModularForm.slash_apply]
  have hσ : ∀ x : ℂ, σ (Matrix.SpecialLinearGroup.mapGL ℝ γ) x = x := by
    intro x
    simp [σ, Matrix.SpecialLinearGroup.det_mapGL]
  have hsmul : ((Matrix.SpecialLinearGroup.mapGL ℝ γ • τ : ℍ) : ℂ)
      = moebiusMap γ (τ : ℂ) := coe_smul_eq_moebiusMap γ τ
  have hd : moebiusDenom γ (τ : ℂ) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero γ τ.im_ne_zero
  rw [hσ, hsmul, hq _ τ.im_pos, denom_mapGL, Matrix.SpecialLinearGroup.det_mapGL]
  simp only [Units.val_one, abs_one, Complex.ofReal_one, one_zpow, mul_one, zpow_neg]
  rw [show ((4 : ℤ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
  field_simp

/-- Plane holomorphy on `{0 < im}` transports to manifold holomorphy on `ℍ`. -/
theorem mdifferentiable_coe_of_differentiableOn {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => q (τ : ℂ)) := by
  refine UpperHalfPlane.mdifferentiable_iff.mpr (hq.congr fun z hz => ?_)
  simp [Function.comp, ofComplex_apply_of_im_pos hz]

/-- A quadratic differential for `Γ` yields a Mathlib slash-invariant form of weight `4`
for the image of `Γ` in `GL(2, ℝ)`. -/
noncomputable def QuadraticDifferential.toSlashInvariantForm (q : QuadraticDifferential Γ) :
    SlashInvariantForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 4 where
  toFun := fun τ : ℍ => q (τ : ℂ)
  slash_action_eq' := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hγ'
    exact weight4_slashInvariance q.toFun γ (fun z hz => q.automorphy γ hγ z hz)

end RiemannDynamics

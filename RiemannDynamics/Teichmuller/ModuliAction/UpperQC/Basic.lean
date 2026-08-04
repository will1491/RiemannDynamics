/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.Interpolate.Assembly
import RiemannDynamics.Uniformization.Fuchsian
import RiemannDynamics.Uniformization.HolomorphicEquiv
import RiemannDynamics.QC.MRMT.Uniqueness
import RiemannDynamics.QC.Calculus.WeylLocal
import RiemannDynamics.QC.Calculus.AnalyticClosedness
import RiemannDynamics.QC.InverseQC.LusinN
import RiemannDynamics.QC.Regularity.Quasisymmetry
import RiemannDynamics.Hyperbolic.DiskModel.DiskMetric

/-!
# Upper-half-plane quasiconformal pairs and the pairing limits

The two-sided upper-half-plane quasiconformal predicate at a Beltrami bound,
its extraction from geometric pairs, Marden stability in generator form, the
change-of-variables bound, mollification, and the pairing limit machinery for
smooth approximations.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- `h` is an **upper-half-plane quasiconformal map** with coefficient bound `κ`: a
homeomorphism of the open upper half plane onto itself, recorded with a two-sided inverse
`hinv`, lying in `W^{1,2}_loc` of the open upper half plane, with almost-everywhere
positive Jacobian and Beltrami bound `‖∂̄h‖ ≤ κ ‖∂h‖` almost everywhere on the upper half
plane. -/
structure IsQCUpper (h hinv : ℂ → ℂ) (κ : ℝ) : Prop where
  mapsTo : ∀ z : ℂ, 0 < z.im → 0 < (h z).im
  mapsTo' : ∀ z : ℂ, 0 < z.im → 0 < (hinv z).im
  left_inv : ∀ z : ℂ, 0 < z.im → hinv (h z) = z
  right_inv : ∀ z : ℂ, 0 < z.im → h (hinv z) = z
  cont : ContinuousOn h {z : ℂ | 0 < z.im}
  cont' : ContinuousOn hinv {z : ℂ | 0 < z.im}
  sobolev : MemWklocP h 1 2 {z : ℂ | 0 < z.im}
  jac : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), 0 < (fderiv ℝ h z).det
  belt : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖dzbar h z‖ ≤ κ * ‖dz h z‖

/-- A conjugation-symmetric quasiconformal plane homeomorphism mapping the upper half
plane into itself restricts to an upper-half-plane quasiconformal map with the
corresponding coefficient bound: symmetry carries the half-plane preservation to the
inverse. -/
theorem isQCUpper_of_isQCGeometric {F G : ℂ → ℂ} {K : ℝ} (hF : IsQCGeometric F K)
    (hsym : ∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    (hup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im)
    (hGF : ∀ z : ℂ, G (F z) = z) (hFG : ∀ z : ℂ, F (G z) = z) :
    IsQCUpper F G ((K - 1) / (K + 1)) := by
  have hhomeo : IsHomeomorph F := hF.2.1.isHomeomorph
  obtain ⟨b, hbnd, hQCA⟩ := isQCAnalytic_of_isQCGeometric hF.1 hF
  -- `G` is globally continuous: it is the inverse of the open bijection `F`, so
  -- `G ⁻¹' U = F '' U` is open for every open `U`.
  have hGcont : Continuous G := by
    rw [continuous_def]
    intro U hU
    have hpre : G ⁻¹' U = F '' U := by
      ext z
      constructor
      · intro hz
        exact ⟨G z, hz, hFG z⟩
      · rintro ⟨w, hw, rfl⟩
        simpa [hGF w] using hw
    rw [hpre]
    exact hhomeo.isOpenMap U hU
  -- `G` preserves the upper half plane: conjugation symmetry of `F` forbids `G z`
  -- from lying on the real axis or in the lower half plane.
  have hmapsTo' : ∀ z : ℂ, 0 < z.im → 0 < (G z).im := by
    intro z hz
    by_contra hle
    rw [not_lt] at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- `(G z).im = 0`: then `G z` is fixed by conjugation, hence so is `z = F (G z)`.
      have hconj : starRingEnd ℂ (G z) = G z := Complex.conj_eq_iff_im.mpr heq
      have hzfix : starRingEnd ℂ z = z := by
        calc starRingEnd ℂ z = starRingEnd ℂ (F (G z)) := by rw [hFG z]
          _ = F (starRingEnd ℂ (G z)) := (hsym (G z)).symm
          _ = F (G z) := by rw [hconj]
          _ = z := hFG z
      exact absurd (Complex.conj_eq_iff_im.mp hzfix) (ne_of_gt hz)
    · -- `(G z).im < 0`: then `conj (G z)` lies in the upper half plane, but `F` sends it
      -- to `conj z`, whose imaginary part is negative.
      have him : 0 < (starRingEnd ℂ (G z)).im := by
        rw [Complex.conj_im]; linarith
      have h1 := hup _ him
      rw [hsym (G z), hFG z, Complex.conj_im] at h1
      linarith
  refine ⟨hup, hmapsTo', fun z _ => hGF z, fun z _ => hFG z,
    hhomeo.continuous.continuousOn, hGcont.continuousOn,
    MemWklocP.mono hQCA.2.1 (Set.subset_univ _),
    ae_restrict_of_ae hQCA.1.2, ?_⟩
  -- The Beltrami bound: `‖μ‖ ≤ ‖μ‖∞ ≤ (K − 1)/(K + 1)` almost everywhere, and the
  -- Beltrami equation converts this into the dilatation inequality.
  have hbw_ae : ∀ᵐ w : ℂ, ‖b.μ w‖ ≤ b.normInf := by
    filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with w hw
    have h2 := ENNReal.toReal_mono (ne_top_of_lt b.bound) hw
    simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
  refine ae_restrict_of_ae ?_
  filter_upwards [hQCA.2.2, hbw_ae] with z hbel hbw
  calc ‖dzbar F z‖ = ‖b.μ z‖ * ‖dz F z‖ := by rw [hbel, norm_mul]
    _ ≤ b.normInf * ‖dz F z‖ := mul_le_mul_of_nonneg_right hbw (norm_nonneg _)
    _ ≤ (K - 1) / (K + 1) * ‖dz F z‖ := mul_le_mul_of_nonneg_right hbnd (norm_nonneg _)

/-! ## Marden stability, upper-half-plane generator form -/

/-- **Marden stability, upper-half-plane generator form.** Along generator tuples of
trace-gapped Fuchsian groups converging entrywise to the tuple of a cocompact trace-gapped
limit group, for every `κ > 0`, eventually in `n` there is an upper-half-plane
quasiconformal conjugacy with Beltrami bound `κ` intertwining the limit tuple with the
`n`-th tuple exactly on the upper half plane. -/
theorem exists_equivariant_upper_conjugacy_K_to_one
    {ι : Type} [Finite ι] {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hΓ : ∀ n, IsFuchsianGroup (Γ n))
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    (gens : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ) (hmem : ∀ n i, gens n i ∈ Γ n)
    (ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hlim : ∀ i, Filter.Tendsto (fun n => gens n i) Filter.atTop (nhds (ρ i)))
    (hgapρ : ∀ h ∈ Subgroup.closure (Set.range ρ), actsNontrivially h →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ)|)
    (hccρ : CompactSpace (Quotient (MulAction.orbitRel (Subgroup.closure (Set.range ρ))
      UpperHalfPlane))) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ n in Filter.atTop, ∃ h hinv : ℂ → ℂ,
      IsQCUpper h hinv κ ∧
      ∀ i, ∀ z : ℂ, 0 < z.im → h (moebiusMap (ρ i) z) = moebiusMap (gens n i) (h z) := by
  intro κ hκ
  filter_upwards [exists_developed_interpolation hε Γ hΓ hgap gens hmem ρ hlim hgapρ hccρ κ hκ]
    with n hn
  obtain ⟨h, hinv, him, hinvim, hleft, hright, hcont, hinvcont, hSob, hjac, hbelt, hgen⟩ := hn
  exact ⟨h, hinv, ⟨him, hinvim, hleft, hright, hcont, hinvcont, hSob, hjac, hbelt⟩, hgen⟩

/-! ## The factorization lemma -/

/-- Change-of-variables/Hölder bound for a plane quasiconformal map.
For `q` analytically quasiconformal with coefficient `bq`, a measurable set `S`, a unit
direction `e`, and a measurable `g`, the weighted composition integral is controlled by
the global `L²` mass of `g`, the distortion constant, and the measure of `S`. -/
theorem qc_cov_bound {q : ℂ → ℂ} {bq : BeltramiCoeff} (hq : IsQCAnalytic q bq)
    {S : Set ℂ} (hS : MeasurableSet S) {e : ℂ} (he : ‖e‖ = 1) (g : ℂ → ℂ)
    (hgm : Measurable g) :
    ∫⁻ w in S, ‖g (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ
      ≤ ((∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)) *
        ((ENNReal.ofReal ((1 + bq.normInf) ^ 2 / (1 - bq.normInf ^ 2)) * volume S)
          ^ (1/2 : ℝ)) := by
  classical
  set k : ℝ := bq.normInf with hkdef
  have hk0 : 0 ≤ k := bq.normInf_nonneg
  have hk1 : k < 1 := bq.normInf_lt_one
  have hone : (0 : ℝ) < 1 - k ^ 2 := by nlinarith
  set Kd : ℝ := (1 + k) ^ 2 / (1 - k ^ 2) with hKddef
  have hKd0 : 0 ≤ Kd := by
    rw [hKddef]; positivity
  -- The a.e. package on `S`: differentiability, positive Jacobian, distortion.
  have haeS : ∀ᵐ w ∂(volume.restrict S), DifferentiableAt ℝ q w ∧
      0 < (fderiv ℝ q w).det ∧ ‖(fderiv ℝ q w) e‖ ^ 2 ≤ Kd * (fderiv ℝ q w).det := by
    have hbelt : ∀ᵐ z : ℂ, dzbar q z = bq.μ z * dz q z := hq.2.2
    have hmub : ∀ᵐ z : ℂ, ‖bq.μ z‖ₑ ≤ eLpNormEssSup bq.μ volume :=
      enorm_ae_le_eLpNormEssSup bq.μ volume
    have hdet : ∀ᵐ z : ℂ, 0 < (fderiv ℝ q z).det := hq.1.2
    have hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ q z := hq.ae_differentiableAt
    refine ae_restrict_of_ae ?_
    filter_upwards [hbelt, hmub, hdet, hdiff] with z hb hm hd hdf
    refine ⟨hdf, hd, ?_⟩
    -- Wirtinger representation of the directional derivative.
    have hrepr : (fderiv ℝ q z) e = dz q z * e + dzbar q z * (starRingEnd ℂ) e := by
      set T : ℂ →L[ℝ] ℂ := fderiv ℝ q z with hT
      have hTv : T e = (e.re : ℂ) * T 1 + (e.im : ℂ) * T Complex.I := by
        conv_lhs => rw [show e = e.re • (1 : ℂ) + e.im • Complex.I by
          rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
        rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      have hcv : (starRingEnd ℂ) e = (e.re : ℂ) - (e.im : ℂ) * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im e]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hv : e = (e.re : ℂ) + (e.im : ℂ) * Complex.I := (Complex.re_add_im e).symm
      simp only [dz, dzbar, ← hT]
      rw [hTv, hcv]
      linear_combination (-(1 / 2 : ℂ) * (T 1 - Complex.I * T Complex.I)) * hv +
        ((e.im : ℂ) * T Complex.I) * Complex.I_sq
    -- Real-number norm bound on the Beltrami ratio.
    have hmuk : ‖bq.μ z‖ ≤ k := by
      have h2 : eLpNormEssSup bq.μ volume ≠ ⊤ := ne_top_of_lt bq.bound
      have h4 := ENNReal.toReal_mono h2 hm
      rwa [toReal_enorm] at h4
    have hzb : ‖dzbar q z‖ ≤ k * ‖dz q z‖ := by
      rw [hb, norm_mul]
      exact mul_le_mul_of_nonneg_right hmuk (norm_nonneg _)
    have hdet_wirt : (fderiv ℝ q z).det = ‖dz q z‖ ^ 2 - ‖dzbar q z‖ ^ 2 :=
      det_fderiv_eq_wirtinger q z
    have hdir : ‖(fderiv ℝ q z) e‖ ≤ ‖dz q z‖ + ‖dzbar q z‖ := by
      rw [hrepr]
      calc ‖dz q z * e + dzbar q z * (starRingEnd ℂ) e‖
          ≤ ‖dz q z * e‖ + ‖dzbar q z * (starRingEnd ℂ) e‖ := norm_add_le _ _
        _ = ‖dz q z‖ + ‖dzbar q z‖ := by
            rw [norm_mul, norm_mul, RCLike.norm_conj, he, mul_one, mul_one]
    have hdet_lb : (1 - k ^ 2) * ‖dz q z‖ ^ 2 ≤ (fderiv ℝ q z).det := by
      rw [hdet_wirt]
      nlinarith [hzb, norm_nonneg (dzbar q z), norm_nonneg (dz q z)]
    have hdir2 : ‖(fderiv ℝ q z) e‖ ^ 2 ≤ (1 + k) ^ 2 * ‖dz q z‖ ^ 2 := by
      have h1 : ‖(fderiv ℝ q z) e‖ ≤ (1 + k) * ‖dz q z‖ := by
        calc ‖(fderiv ℝ q z) e‖ ≤ ‖dz q z‖ + ‖dzbar q z‖ := hdir
          _ ≤ (1 + k) * ‖dz q z‖ := by nlinarith
      nlinarith [norm_nonneg ((fderiv ℝ q z) e),
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 + k) (norm_nonneg (dz q z))]
    have h3 : ‖(fderiv ℝ q z) e‖ ^ 2 * (1 - k ^ 2) ≤ (1 + k) ^ 2 * (fderiv ℝ q z).det := by
      nlinarith [hdet_lb, hdir2, sq_nonneg (1 + k)]
    rw [hKddef, div_mul_eq_mul_div, le_div_iff₀ hone]
    linarith
  -- Notation for the Jacobian weight.
  set J : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal ((fderiv ℝ q w).det) with hJdef
  have hJmeas : Measurable J := by
    have hfderivmeas : Measurable (fderiv ℝ q) := measurable_fderiv ℝ q
    exact ENNReal.measurable_ofReal.comp
      (ContinuousLinearMap.continuous_det.measurable.comp hfderivmeas)
  have hqcont : Continuous q := hq.1.1.continuous
  have hgqmeas : Measurable fun w => ‖g (q w)‖ₑ :=
    (hgm.comp hqcont.measurable).enorm
  have hDmeas : Measurable fun w => ‖(fderiv ℝ q w) e‖ₑ :=
    (measurable_fderiv_apply_const ℝ q e).enorm
  -- Split the integrand through the Jacobian weight and apply Cauchy–Schwarz.
  have hsplit : ∫⁻ w in S, ‖g (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ
      = ∫⁻ w in S, (‖g (q w)‖ₑ * J w ^ (1/2 : ℝ)) *
          (‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [haeS] with w hw
    have hJ0 : J w ≠ 0 := by
      rw [hJdef]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hw.2.1
    have hJtop : J w ≠ ⊤ := ENNReal.ofReal_ne_top
    have hcancel : J w ^ (1/2 : ℝ) * J w ^ (-(1/2) : ℝ) = 1 := by
      rw [← ENNReal.rpow_add _ _ hJ0 hJtop]
      norm_num
    calc ‖g (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ
        = ‖g (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ * (J w ^ (1/2 : ℝ) * J w ^ (-(1/2) : ℝ)) := by
          rw [hcancel, mul_one]
      _ = (‖g (q w)‖ₑ * J w ^ (1/2 : ℝ)) *
          (‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ)) := by ring
  rw [hsplit]
  have hf1meas : AEMeasurable (fun w => ‖g (q w)‖ₑ * J w ^ (1/2 : ℝ))
      (volume.restrict S) :=
    (hgqmeas.mul (hJmeas.pow_const _)).aemeasurable
  have hf2meas : AEMeasurable (fun w => ‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ))
      (volume.restrict S) :=
    (hDmeas.mul (hJmeas.pow_const _)).aemeasurable
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S)
    (Real.HolderConjugate.two_two) hf1meas hf2meas
  refine le_trans hholder ?_
  -- Factor 1: the area-formula bound.
  have hfact1 : ∫⁻ w in S, (‖g (q w)‖ₑ * J w ^ (1/2 : ℝ)) ^ (2 : ℝ)
      ≤ ∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) := by
    have hrw : ∫⁻ w in S, (‖g (q w)‖ₑ * J w ^ (1/2 : ℝ)) ^ (2 : ℝ)
        = ∫⁻ w in S, ENNReal.ofReal |(fderiv ℝ q w).det| * ‖g (q w)‖ₑ ^ (2 : ℕ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [haeS] with w hw
      have habs : ENNReal.ofReal |(fderiv ℝ q w).det| = J w := by
        rw [hJdef, abs_of_pos hw.2.1]
      have hJsq : (J w ^ (1/2 : ℝ)) ^ (2 : ℝ) = J w := by
        rw [← ENNReal.rpow_mul]
        norm_num
      have hgsq : ‖g (q w)‖ₑ ^ (2 : ℝ) = ‖g (q w)‖ₑ ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast]
        norm_num
      calc (‖g (q w)‖ₑ * J w ^ (1/2 : ℝ)) ^ (2 : ℝ)
          = ‖g (q w)‖ₑ ^ (2 : ℝ) * (J w ^ (1/2 : ℝ)) ^ (2 : ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ = ‖g (q w)‖ₑ ^ (2 : ℕ) * J w := by rw [hJsq, hgsq]
        _ = ENNReal.ofReal |(fderiv ℝ q w).det| * ‖g (q w)‖ₑ ^ (2 : ℕ) := by
            rw [habs, mul_comm]
    rw [hrw]
    -- Restrict to the differentiability set and change variables.
    set s : Set ℂ := S ∩ {z : ℂ | DifferentiableAt ℝ q z} with hsdef
    have hsmeas : MeasurableSet s := hS.inter (measurableSet_of_differentiableAt ℝ q)
    have hSs : volume (S \ s) = 0 := by
      have hsub : S \ s ⊆ {z : ℂ | ¬ DifferentiableAt ℝ q z} := by
        rintro z ⟨hzS, hzs⟩
        intro hdz
        exact hzs ⟨hzS, hdz⟩
      exact measure_mono_null hsub (ae_iff.mp hq.ae_differentiableAt)
    have hcongr : ∫⁻ w in S, ENNReal.ofReal |(fderiv ℝ q w).det| * ‖g (q w)‖ₑ ^ (2 : ℕ)
        = ∫⁻ w in s, ENNReal.ofReal |(fderiv ℝ q w).det| * ‖g (q w)‖ₑ ^ (2 : ℕ) := by
      have hae : S =ᵐ[volume] s := by
        rw [MeasureTheory.ae_eq_set]
        refine ⟨hSs, ?_⟩
        have hempty : s \ S = ∅ := Set.diff_eq_empty.mpr Set.inter_subset_left
        rw [hempty]
        exact measure_empty
      rw [Measure.restrict_congr_set hae]
    rw [hcongr]
    -- The area formula on the differentiability set.
    have hderivs : ∀ x ∈ s, HasFDerivWithinAt q (fderiv ℝ q x) s x := fun x hx =>
      (hx.2.hasFDerivAt).hasFDerivWithinAt
    have hinj : Set.InjOn q s := hq.injective.injOn
    have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (volume : Measure ℂ) hsmeas hderivs hinj (fun z => ‖g z‖ₑ ^ (2 : ℕ))
    rw [← hcov]
    exact setLIntegral_le_lintegral _ _
  -- Factor 2: the distortion bound.
  have hfact2 : ∫⁻ w in S, (‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal Kd * volume S := by
    have hbd : ∀ᵐ w ∂(volume.restrict S),
        (‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ)) ^ (2 : ℝ) ≤ ENNReal.ofReal Kd := by
      filter_upwards [haeS] with w hw
      have hJ0 : J w ≠ 0 := by
        rw [hJdef]
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact hw.2.1
      have hJtop : J w ≠ ⊤ := ENNReal.ofReal_ne_top
      have hsq : (‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ)) ^ (2 : ℝ)
          = ‖(fderiv ℝ q w) e‖ₑ ^ (2 : ℝ) * (J w)⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), ← ENNReal.rpow_mul,
          show (-(1/2) : ℝ) * 2 = -1 by norm_num, ENNReal.rpow_neg_one]
      rw [hsq]
      have henorm2 : ‖(fderiv ℝ q w) e‖ₑ ^ (2 : ℝ)
          = ENNReal.ofReal (‖(fderiv ℝ q w) e‖ ^ 2) := by
        rw [← ofReal_norm_eq_enorm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
        norm_num [Real.rpow_natCast]
      rw [henorm2]
      have hstep : ENNReal.ofReal (‖(fderiv ℝ q w) e‖ ^ 2)
          ≤ ENNReal.ofReal Kd * J w := by
        rw [hJdef, ← ENNReal.ofReal_mul hKd0]
        exact ENNReal.ofReal_le_ofReal hw.2.2
      calc ENNReal.ofReal (‖(fderiv ℝ q w) e‖ ^ 2) * (J w)⁻¹
          ≤ (ENNReal.ofReal Kd * J w) * (J w)⁻¹ := by gcongr
        _ = ENNReal.ofReal Kd * (J w * (J w)⁻¹) := by ring
        _ = ENNReal.ofReal Kd := by rw [ENNReal.mul_inv_cancel hJ0 hJtop, mul_one]
    calc ∫⁻ w in S, (‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ)) ^ (2 : ℝ)
        ≤ ∫⁻ _ in S, ENNReal.ofReal Kd := lintegral_mono_ae hbd
      _ = ENNReal.ofReal Kd * volume S := by
          rw [setLIntegral_const]
  -- Assemble the two factors.
  have h1 : (∫⁻ w in S, (‖g (q w)‖ₑ * J w ^ (1/2 : ℝ)) ^ (2 : ℝ)) ^ (1/2 : ℝ)
      ≤ (∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ) :=
    ENNReal.rpow_le_rpow hfact1 (by norm_num)
  have h2 : (∫⁻ w in S, (‖(fderiv ℝ q w) e‖ₑ * J w ^ (-(1/2) : ℝ)) ^ (2 : ℝ)) ^ (1/2 : ℝ)
      ≤ (ENNReal.ofReal Kd * volume S) ^ (1/2 : ℝ) :=
    ENNReal.rpow_le_rpow hfact2 (by norm_num)
  exact mul_le_mul' h1 h2

/-- Localized `L²` convergence of mollifications. On a compact set the
mollifications of a locally square-integrable function converge to it in `L²`. -/
theorem mollify_L2_loc {h : ℂ → ℂ} (hm : Measurable h) (h2 : MemLpLocOn h 2 Set.univ)
    {K : Set ℂ} (hK : IsCompact K) (hKm : MeasurableSet K)
    (Φ : ℕ → ContDiffBump (0 : ℂ))
    (hΦ : Filter.Tendsto (fun n => (Φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm
      (fun z => MeasureTheory.convolution ((Φ n).normed volume) h
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z - h z) 2 (volume.restrict K))
      Filter.atTop (nhds 0) := by
  classical
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  -- The compact thickening `C` of `K` and the truncation of `h`.
  set C : Set ℂ := Metric.cthickening 1 K with hCdef
  have hCc : IsCompact C := hK.cthickening
  have hCm : MeasurableSet C := (Metric.isClosed_cthickening).measurableSet
  have hKC : K ⊆ C := Metric.self_subset_cthickening K
  set h1 : ℂ → ℂ := C.indicator h with hh1def
  have hh1L2 : MemLp h1 2 volume := by
    refine ⟨(hm.indicator hCm).aestronglyMeasurable, ?_⟩
    rw [hh1def, eLpNorm_indicator_eq_eLpNorm_restrict hCm]
    exact (h2 C (Set.subset_univ C) hCc).2
  -- Local integrability of `h`, `h1` and the truncation remainder.
  have hloc : MeasureTheory.LocallyIntegrable h volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((h2 k (Set.subset_univ k) hk).mono_exponent (by norm_num))
  have hh1loc : MeasureTheory.LocallyIntegrable h1 volume :=
    hh1L2.locallyIntegrable (by norm_num)
  have hrestloc : MeasureTheory.LocallyIntegrable (h - h1) volume := hloc.sub hh1loc
  -- Convolution splits along `h = h1 + (h - h1)`.
  have hsum : (fun z => h1 z + (h - h1) z) = h := by
    funext z
    simp
  have hsplit : ∀ n : ℕ, ∀ z : ℂ,
      MeasureTheory.convolution ((Φ n).normed volume) h L volume z
        = MeasureTheory.convolution ((Φ n).normed volume) h1 L volume z
          + MeasureTheory.convolution ((Φ n).normed volume) (h - h1) L volume z := by
    intro n z
    have hce1 : ConvolutionExistsAt ((Φ n).normed volume) h1 z L volume :=
      (((Φ n).hasCompactSupport_normed).convolutionExists_left L
        ((Φ n).continuous_normed) hh1loc) z
    have hce2 : ConvolutionExistsAt ((Φ n).normed volume) (h - h1) z L volume :=
      (((Φ n).hasCompactSupport_normed).convolutionExists_left L
        ((Φ n).continuous_normed) hrestloc) z
    have hd := hce1.distrib_add hce2
    calc MeasureTheory.convolution ((Φ n).normed volume) h L volume z
        = MeasureTheory.convolution ((Φ n).normed volume) (h1 + (h - h1)) L volume z := by
          rw [show h1 + (h - h1) = h by funext z; simp]
      _ = _ := hd
  -- The remainder convolution vanishes on `K` once `rOut < 1`.
  have hev : ∀ᶠ n in Filter.atTop, (Φ n).rOut < 1 := hΦ.eventually (gt_mem_nhds one_pos)
  have hvanish : ∀ n : ℕ, (Φ n).rOut < 1 → ∀ z ∈ K,
      MeasureTheory.convolution ((Φ n).normed volume) (h - h1) L volume z = 0 := by
    intro n hn z hz
    by_contra hne
    have hzsup : z ∈ Function.support
        (MeasureTheory.convolution ((Φ n).normed volume) (h - h1) L volume) := hne
    have hsub := MeasureTheory.support_convolution_subset (μ := volume)
      (f := (Φ n).normed volume) (g := h - h1) L
    obtain ⟨a, ha, b, hb, hab⟩ := hsub hzsup
    have haball : a ∈ Metric.ball (0 : ℂ) (Φ n).rOut := by
      rw [← (Φ n).support_normed_eq (μ := volume)]
      exact ha
    have hbC : b ∉ C := by
      intro hbC
      have hb0 : (h - h1) b = 0 := by
        simp only [Pi.sub_apply, hh1def, Set.indicator_of_mem hbC, sub_self]
      exact hb hb0
    apply hbC
    rw [hCdef, Metric.mem_cthickening_iff]
    have hedist : Metric.infEDist b K ≤ edist b z :=
      Metric.infEDist_le_edist_of_mem hz
    have hbz : edist b z ≤ ENNReal.ofReal 1 := by
      have hbz' : b - z = -a := by
        have : z = a + b := hab.symm
        rw [this]; ring
      rw [edist_eq_enorm_sub, hbz', enorm_neg, ← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Metric.mem_ball, dist_zero_right] at haball
      linarith
    exact le_trans hedist hbz
  -- Eventually, the restricted `eLpNorm` is dominated by the global truncated one.
  have hdom : ∀ᶠ n in Filter.atTop,
      eLpNorm (fun z => MeasureTheory.convolution ((Φ n).normed volume) h L volume z - h z)
        2 (volume.restrict K)
      ≤ eLpNorm (fun z =>
          MeasureTheory.convolution ((Φ n).normed volume) h1 L volume z - h1 z) 2 volume := by
    filter_upwards [hev] with n hn
    have heq : ∀ z ∈ K,
        MeasureTheory.convolution ((Φ n).normed volume) h L volume z - h z
          = MeasureTheory.convolution ((Φ n).normed volume) h1 L volume z - h1 z := by
      intro z hz
      rw [hsplit n z, hvanish n hn z hz, add_zero, hh1def,
        Set.indicator_of_mem (hKC hz)]
    have hcongr : eLpNorm
        (fun z => MeasureTheory.convolution ((Φ n).normed volume) h L volume z - h z)
          2 (volume.restrict K)
        = eLpNorm (fun z =>
            MeasureTheory.convolution ((Φ n).normed volume) h1 L volume z - h1 z)
          2 (volume.restrict K) := by
      refine eLpNorm_congr_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' hKm]
      exact Filter.Eventually.of_forall heq
    rw [hcongr]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  -- Conclude by squeezing against the in-tree global convergence.
  have hglobal := eLpNorm_convolution_normed_sub_tendsto_zero hh1L2 Φ hΦ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hglobal
    (Filter.Eventually.of_forall fun n => zero_le _) ?_
  filter_upwards [hdom] with n hn
  exact hn

-- Elaborating the `L¹`-error assembly in one declaration needs the raised budget.
set_option maxHeartbeats 400000 in
-- The abstract pairing-limit argument chains dominated convergence through the pairing;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Abstract pairing limit: if `QE m → qe` in `L¹` of the compact support of
the real test weight `φ`, the frames `U m, V m` are uniformly bounded and converge
pointwise to `u, v`, then the paired integrals converge. -/
theorem pairing_tendsto
    {φ : ℂ → ℝ} {S : Set ℂ} (hScomp : IsCompact S) (hSm : MeasurableSet S)
    (hφcont : Continuous φ) (hφzero : ∀ z, z ∉ S → φ z = 0)
    {Mφ : ℝ} (hMφ : ∀ z, ‖φ z‖ ≤ Mφ)
    {qe : ℂ → ℂ} (hqem : Measurable qe) (hqeS : IntegrableOn qe S volume)
    {u v : ℂ → ℂ} (hu : Continuous u) (hv : Continuous v)
    {U V : ℕ → ℂ → ℂ} (hU : ∀ m, Continuous (U m)) (hV : ∀ m, Continuous (V m))
    {MX MY : ℝ}
    (hMXb : ∀ m z, ‖U m z‖ ≤ MX) (hMYb : ∀ m z, ‖V m z‖ ≤ MY)
    (hub : ∀ z, ‖u z‖ ≤ MX) (hvb : ∀ z, ‖v z‖ ≤ MY)
    (hUpt : ∀ z, Filter.Tendsto (fun m => U m z) Filter.atTop (nhds (u z)))
    (hVpt : ∀ z, Filter.Tendsto (fun m => V m z) Filter.atTop (nhds (v z)))
    {QE : ℕ → ℂ → ℂ} (hQEc : ∀ m, Continuous (QE m))
    (hQEL1 : Filter.Tendsto (fun m => ∫ z in S, ‖QE m z - qe z‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m => ∫ z, φ z • ((QE m z).re • U m z + (QE m z).im • V m z)) Filter.atTop
      (nhds (∫ z, φ z • ((qe z).re • u z + (qe z).im • v z))) := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hMφ0 : 0 ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
  have hMX0 : 0 ≤ MX := le_trans (norm_nonneg _) (hub 0)
  have hMY0 : 0 ≤ MY := le_trans (norm_nonneg _) (hvb 0)
  have habs_re : ∀ w : ℂ, |w.re| ≤ ‖w‖ := fun w => Complex.abs_re_le_norm w
  have habs_im : ∀ w : ℂ, |w.im| ≤ ‖w‖ := fun w => Complex.abs_im_le_norm w
  -- Integrability of the `m`-th and limit integrands.
  have hHm_int : ∀ m, Integrable
      (fun z => φ z • ((QE m z).re • U m z + (QE m z).im • V m z)) volume := by
    intro m
    have hc : Continuous
        (fun z => φ z • ((QE m z).re • U m z + (QE m z).im • V m z)) := by
      refine hφcont.smul ?_
      exact ((Complex.continuous_re.comp (hQEc m)).smul (hU m)).add
        ((Complex.continuous_im.comp (hQEc m)).smul (hV m))
    refine hc.integrable_of_hasCompactSupport ?_
    refine IsCompact.of_isClosed_subset hScomp (isClosed_tsupport _)
      (closure_minimal ?_ ?_)
    · intro z hz
      by_contra hzS
      refine hz ?_
      change φ z • ((QE m z).re • U m z + (QE m z).im • V m z) = 0
      rw [hφzero z hzS]
      exact zero_smul ℝ _
    · exact hScomp.isClosed
  have hqeSnorm : IntegrableOn (fun z => ‖qe z‖) S volume := hqeS.norm
  have hdomInt : Integrable
      (S.indicator (fun z => Mφ * ((MX + MY) * ‖qe z‖))) volume := by
    rw [MeasureTheory.integrable_indicator_iff hSm]
    exact ((hqeSnorm.const_mul (MX + MY)).const_mul Mφ)
  have hcombo_bd : ∀ (w u₁ u₂ : ℂ), ‖w.re • u₁ + w.im • u₂‖ ≤
      |w.re| * ‖u₁‖ + |w.im| * ‖u₂‖ := by
    intro w u₁ u₂
    calc ‖w.re • u₁ + w.im • u₂‖ ≤ ‖w.re • u₁‖ + ‖w.im • u₂‖ := norm_add_le _ _
      _ = |w.re| * ‖u₁‖ + |w.im| * ‖u₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hHinf_int : Integrable
      (fun z => φ z • ((qe z).re • u z + (qe z).im • v z)) volume := by
    refine MeasureTheory.Integrable.mono' hdomInt ?_ ?_
    · refine AEStronglyMeasurable.smul hφcont.aestronglyMeasurable ?_
      refine AEStronglyMeasurable.add ?_ ?_
      · exact ((Complex.measurable_re.comp hqem).aestronglyMeasurable).smul
          (hu.aestronglyMeasurable)
      · exact ((Complex.measurable_im.comp hqem).aestronglyMeasurable).smul
          (hv.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun z => ?_
      by_cases hzS : z ∈ S
      · rw [Set.indicator_of_mem hzS, norm_smul]
        have h1 : ‖(qe z).re • u z + (qe z).im • v z‖ ≤ (MX + MY) * ‖qe z‖ := by
          refine le_trans (hcombo_bd (qe z) _ _) ?_
          have h4 := hub z
          have h5 := hvb z
          have h6 := norm_nonneg (qe z)
          have h7 := habs_re (qe z)
          have h8 := habs_im (qe z)
          have h9 : (0:ℝ) ≤ |(qe z).re| := abs_nonneg _
          have h10 : (0:ℝ) ≤ |(qe z).im| := abs_nonneg _
          nlinarith
        have h2 := hMφ z
        have h3 : (0:ℝ) ≤ ‖φ z‖ := norm_nonneg _
        have h11 : (0:ℝ) ≤ (MX + MY) * ‖qe z‖ := by positivity
        nlinarith [norm_nonneg ((qe z).re • u z + (qe z).im • v z)]
      · have h00 : (0:ℝ) • ((qe z).re • u z + (qe z).im • v z) = 0 := zero_smul ℝ _
        rw [hφzero z hzS, h00, norm_zero]
        exact Set.indicator_nonneg (fun y _ => by positivity) z
  -- The two error pieces.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set A : ℕ → ℝ := fun m => Mφ * (MX + MY) * ∫ z in S, ‖QE m z - qe z‖ with hAdef
  set B : ℕ → ℝ := fun m => ∫ z, ‖φ z‖ * (‖qe z‖ *
    (‖U m z - u z‖ + ‖V m z - v z‖)) with hBdef
  have hB0dom : Integrable
      (S.indicator (fun z => Mφ * (‖qe z‖ * (2 * (MX + MY))))) volume := by
    rw [MeasureTheory.integrable_indicator_iff hSm]
    exact ((hqeSnorm.mul_const (2 * (MX + MY))).const_mul Mφ)
  have hBmeas : ∀ m, AEStronglyMeasurable (fun z => ‖φ z‖ * (‖qe z‖ *
      (‖U m z - u z‖ + ‖V m z - v z‖))) volume := by
    intro m
    refine (hφcont.norm.aestronglyMeasurable).mul ?_
    refine (hqem.norm.aestronglyMeasurable).mul ?_
    exact ((((hU m).sub hu).norm).add (((hV m).sub hv).norm)).aestronglyMeasurable
  have hBbound : ∀ m, ∀ᵐ z : ℂ ∂volume, ‖‖φ z‖ * (‖qe z‖ *
      (‖U m z - u z‖ + ‖V m z - v z‖))‖
      ≤ S.indicator (fun z => Mφ * (‖qe z‖ * (2 * (MX + MY)))) z := by
    intro m
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, Real.norm_eq_abs]
      have hDXd : ‖U m z - u z‖ ≤ 2 * MX := by
        calc ‖U m z - u z‖ ≤ ‖U m z‖ + ‖u z‖ := norm_sub_le _ _
          _ ≤ 2 * MX := by
              have h1 := hMXb m z
              have h2 := hub z
              linarith
      have hDYd : ‖V m z - v z‖ ≤ 2 * MY := by
        calc ‖V m z - v z‖ ≤ ‖V m z‖ + ‖v z‖ := norm_sub_le _ _
          _ ≤ 2 * MY := by
              have h1 := hMYb m z
              have h2 := hvb z
              linarith
      have h6 := norm_nonneg (qe z)
      have h2 := hMφ z
      have h3 : (0:ℝ) ≤ ‖φ z‖ := norm_nonneg _
      have habsval : |‖φ z‖ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖))|
          = ‖φ z‖ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖)) := by
        refine abs_of_nonneg ?_
        positivity
      rw [habsval]
      have h7 : ‖U m z - u z‖ + ‖V m z - v z‖ ≤ 2 * (MX + MY) := by linarith
      have h8 : (0:ℝ) ≤ ‖U m z - u z‖ + ‖V m z - v z‖ := by positivity
      calc ‖φ z‖ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖))
          ≤ Mφ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖)) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ Mφ * (‖qe z‖ * (2 * (MX + MY))) := by
            have h9 := mul_le_mul_of_nonneg_left h7 h6
            nlinarith
    · rw [hφzero z hzS, norm_zero, zero_mul, Real.norm_eq_abs, abs_zero]
      exact Set.indicator_nonneg (fun y _ => by positivity) z
  have hBint : ∀ m, Integrable (fun z => ‖φ z‖ * (‖qe z‖ *
      (‖U m z - u z‖ + ‖V m z - v z‖))) volume :=
    fun m => MeasureTheory.Integrable.mono' hB0dom (hBmeas m) (hBbound m)
  have hAlim : Filter.Tendsto A Filter.atTop (nhds 0) := by
    have := hQEL1.const_mul (Mφ * (MX + MY))
    rwa [mul_zero] at this
  have hBlim : Filter.Tendsto B Filter.atTop (nhds 0) := by
    have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun m z => ‖φ z‖ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖)))
      (f := fun _ => (0 : ℝ))
      (S.indicator (fun z => Mφ * (‖qe z‖ * (2 * (MX + MY)))))
      hBmeas hB0dom hBbound
      (Filter.Eventually.of_forall fun z => by
        have h1 : Filter.Tendsto (fun m => ‖U m z - u z‖) Filter.atTop (nhds 0) := by
          have h2 := (hUpt z).sub (tendsto_const_nhds (x := u z))
          rw [sub_self] at h2
          have h3 := h2.norm
          rwa [norm_zero] at h3
        have h4 : Filter.Tendsto (fun m => ‖V m z - v z‖) Filter.atTop (nhds 0) := by
          have h5 := (hVpt z).sub (tendsto_const_nhds (x := v z))
          rw [sub_self] at h5
          have h6 := h5.norm
          rwa [norm_zero] at h6
        have h7 := (h1.add h4).const_mul ‖qe z‖
        rw [add_zero, mul_zero] at h7
        have h8 := h7.const_mul ‖φ z‖
        rwa [mul_zero] at h8)
    rw [MeasureTheory.integral_zero] at hDCT
    exact hDCT
  -- The difference bound and the squeeze.
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) (by
    have := hAlim.add hBlim
    rwa [add_zero] at this)
  rw [← MeasureTheory.integral_sub (hHm_int m) hHinf_int]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hAint_m : Integrable
      (S.indicator fun z => Mφ * ((MX + MY) * ‖QE m z - qe z‖)) volume := by
    rw [MeasureTheory.integrable_indicator_iff hSm]
    have h1 : IntegrableOn (fun z => QE m z - qe z) S volume :=
      ((((hQEc m).continuousOn).integrableOn_compact hScomp).sub hqeS)
    exact ((h1.norm.const_mul (MX + MY)).const_mul Mφ)
  have hptw : ∀ z,
      ‖φ z • ((QE m z).re • U m z + (QE m z).im • V m z)
        - φ z • ((qe z).re • u z + (qe z).im • v z)‖
      ≤ S.indicator (fun z => Mφ * ((MX + MY) * ‖QE m z - qe z‖)) z
        + ‖φ z‖ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖)) := by
    intro z
    by_cases hzS : z ∈ S
    · have hsm : φ z • ((QE m z).re • U m z + (QE m z).im • V m z)
          - φ z • ((qe z).re • u z + (qe z).im • v z)
          = φ z • ((QE m z).re • U m z + (QE m z).im • V m z
            - ((qe z).re • u z + (qe z).im • v z)) :=
        (smul_sub (φ z) _ _).symm
      rw [Set.indicator_of_mem hzS, hsm, norm_smul]
      have hΔ : (QE m z).re • U m z + (QE m z).im • V m z
          - ((qe z).re • u z + (qe z).im • v z)
          = ((QE m z).re - (qe z).re) • U m z + (qe z).re • (U m z - u z)
            + (((QE m z).im - (qe z).im) • V m z + (qe z).im • (V m z - v z)) := by
        module
      rw [hΔ]
      have hb1 : ‖((QE m z).re - (qe z).re) • U m z + (qe z).re • (U m z - u z)
          + (((QE m z).im - (qe z).im) • V m z + (qe z).im • (V m z - v z))‖
          ≤ |(QE m z).re - (qe z).re| * ‖U m z‖ + |(qe z).re| * ‖U m z - u z‖
            + (|(QE m z).im - (qe z).im| * ‖V m z‖ + |(qe z).im| * ‖V m z - v z‖) := by
        refine le_trans (norm_add_le _ _) ?_
        refine add_le_add ?_ ?_
        · refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        · refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hre : |(QE m z).re - (qe z).re| ≤ ‖QE m z - qe z‖ := by
        rw [← Complex.sub_re]
        exact habs_re _
      have him : |(QE m z).im - (qe z).im| ≤ ‖QE m z - qe z‖ := by
        rw [← Complex.sub_im]
        exact habs_im _
      have h4 := hMXb m z
      have h5 := hMYb m z
      have h6 := norm_nonneg (QE m z - qe z)
      have h7 := habs_re (qe z)
      have h8 := habs_im (qe z)
      have h9 := norm_nonneg (qe z)
      have h10 := norm_nonneg (U m z - u z)
      have h11 := norm_nonneg (V m z - v z)
      have h12 := hMφ z
      have h13 : (0:ℝ) ≤ ‖φ z‖ := norm_nonneg _
      have h14 : (0:ℝ) ≤ |(QE m z).re - (qe z).re| := abs_nonneg _
      have h15 : (0:ℝ) ≤ |(QE m z).im - (qe z).im| := abs_nonneg _
      have h16 : (0:ℝ) ≤ |(qe z).re| := abs_nonneg _
      have h17 : (0:ℝ) ≤ |(qe z).im| := abs_nonneg _
      have hmid : ‖φ z‖ * (|(QE m z).re - (qe z).re| * ‖U m z‖
            + |(qe z).re| * ‖U m z - u z‖
            + (|(QE m z).im - (qe z).im| * ‖V m z‖ + |(qe z).im| * ‖V m z - v z‖))
          ≤ Mφ * ((MX + MY) * ‖QE m z - qe z‖)
            + ‖φ z‖ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖)) := by
        have hA1 : |(QE m z).re - (qe z).re| * ‖U m z‖
            + |(QE m z).im - (qe z).im| * ‖V m z‖
            ≤ (MX + MY) * ‖QE m z - qe z‖ := by
          nlinarith
        have hA2 : |(qe z).re| * ‖U m z - u z‖ + |(qe z).im| * ‖V m z - v z‖
            ≤ ‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖) := by
          nlinarith
        have hA3 : (0:ℝ) ≤ (MX + MY) * ‖QE m z - qe z‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hA1 h13,
          mul_le_mul_of_nonneg_left hA2 h13,
          mul_le_mul_of_nonneg_right h12 hA3]
      calc ‖φ z‖ * ‖((QE m z).re - (qe z).re) • U m z + (qe z).re • (U m z - u z)
            + (((QE m z).im - (qe z).im) • V m z + (qe z).im • (V m z - v z))‖
          ≤ ‖φ z‖ * (|(QE m z).re - (qe z).re| * ‖U m z‖
            + |(qe z).re| * ‖U m z - u z‖
            + (|(QE m z).im - (qe z).im| * ‖V m z‖ + |(qe z).im| * ‖V m z - v z‖)) :=
            mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
        _ ≤ _ := hmid
    · have h00 : (0:ℝ) • ((QE m z).re • U m z + (QE m z).im • V m z) = 0 :=
        zero_smul ℝ _
      have h01 : (0:ℝ) • ((qe z).re • u z + (qe z).im • v z) = 0 := zero_smul ℝ _
      rw [hφzero z hzS, h00, h01, sub_zero, norm_zero, Set.indicator_of_notMem hzS]
      positivity
  calc ∫ z, ‖φ z • ((QE m z).re • U m z + (QE m z).im • V m z)
        - φ z • ((qe z).re • u z + (qe z).im • v z)‖
      ≤ ∫ z, (S.indicator (fun z => Mφ * ((MX + MY) * ‖QE m z - qe z‖)) z
          + ‖φ z‖ * (‖qe z‖ * (‖U m z - u z‖ + ‖V m z - v z‖))) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => norm_nonneg _)
          (hAint_m.add (hBint m)) (Filter.Eventually.of_forall hptw)
    _ = A m + B m := by
        rw [MeasureTheory.integral_add hAint_m (hBint m),
          MeasureTheory.integral_indicator hSm]
        congr 1
        rw [hAdef]
        have h1 : (fun z => Mφ * ((MX + MY) * ‖QE m z - qe z‖))
            = fun z => (Mφ * (MX + MY)) * ‖QE m z - qe z‖ := by
          funext z
          ring
        rw [h1, MeasureTheory.integral_const_mul]

-- The two nested dominated-convergence passes and the `L¹`-error assembly make this a
-- long single elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The smooth-composite weak chain rule elaborates a long mollification chain;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Weak chain rule for the composition of a smooth compactly supported
map with a plane quasiconformal map. The weak directional derivative of `G ∘ q` is the
chain-rule pairing of the classical differential of `G` along `q` with the weak
directional derivative of `q`. -/
theorem comp_smooth_qc
    {q : ℂ → ℂ} {bq : BeltramiCoeff} (hq : IsQCAnalytic q bq)
    {e : ℂ} {qe : ℂ → ℂ} (hqe : HasWeakDirDeriv e qe q Set.univ) (hqem : Measurable qe)
    (hqe2 : MemLpLocOn qe 2 Set.univ)
    {G : ℂ → ℂ} (hGsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (hGcs : HasCompactSupport G) :
    HasWeakDirDeriv e
      (fun z => (qe z).re • (fderiv ℝ G (q z)) 1 + (qe z).im • (fderiv ℝ G (q z)) Complex.I)
      (fun z => G (q z)) Set.univ := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hone_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one]
    exact WithTop.coe_le_coe.mpr le_top
  have htop_add : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  have htop_ne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hqcont : Continuous q := hq.1.1.continuous
  have hqloc : MeasureTheory.LocallyIntegrable q volume := hqcont.locallyIntegrable
  have hqeloc : MeasureTheory.LocallyIntegrable qe volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hqe2 k (Set.subset_univ k) hk).mono_exponent (by norm_num))
  -- The outer map, its partials, and their bounds.
  set DXG : ℂ → ℂ := fun p => (fderiv ℝ G p) 1 with hDXGdef
  set DYG : ℂ → ℂ := fun p => (fderiv ℝ G p) Complex.I with hDYGdef
  have hGcont : Continuous G := hGsm.continuous
  have hDGcont : Continuous (fderiv ℝ G) :=
    (hGsm.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) htop_add).continuous
  have hDXGc : Continuous DXG :=
    (ContinuousLinearMap.apply ℝ ℂ 1).continuous.comp hDGcont
  have hDYGc : Continuous DYG :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous.comp hDGcont
  obtain ⟨MG, hMG⟩ := hGcont.bounded_above_of_compact_support hGcs
  have hDbd : ∀ u : ℂ, ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖(fderiv ℝ G p) u‖ ≤ M := by
    intro u
    have hcont : Continuous fun p => (fderiv ℝ G p) u :=
      (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp hDGcont
    have hcs : HasCompactSupport fun p => (fderiv ℝ G p) u := by
      have h1 : Function.support (fun p => (fderiv ℝ G p) u)
          ⊆ tsupport (fderiv ℝ G) := by
        intro p hp
        have h2 : fderiv ℝ G p ≠ 0 := by
          intro h0
          refine hp ?_
          change (fderiv ℝ G p) u = 0
          rw [h0]
          rfl
        exact subset_tsupport _ h2
      refine IsCompact.of_isClosed_subset (hGcs.fderiv ℝ) (isClosed_tsupport _) ?_
      exact closure_minimal h1 (isClosed_tsupport _)
    obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), hM⟩
  obtain ⟨MX, hMX0, hMX⟩ := hDbd 1
  obtain ⟨MY, hMY0, hMY⟩ := hDbd Complex.I
  -- The bump family and the mollified inner map.
  set Φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := 1 / (n + 2), rOut := 1 / (n + 1),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        have h1 : (0 : ℝ) < n + 1 := by positivity
        exact one_div_lt_one_div_of_lt h1 (by nlinarith) } with hΦdef
  have hΦr : Filter.Tendsto (fun n => (Φ n).rOut) Filter.atTop (nhds 0) := by
    have : (fun n : ℕ => (Φ n).rOut) = fun n : ℕ => 1 / ((n : ℝ) + 1) := rfl
    rw [this]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set ρ : ℕ → ℂ → ℝ := fun n => (Φ n).normed volume with hρdef
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (Φ n).contDiff_normed
  have hρcs : ∀ n, HasCompactSupport (ρ n) := fun n => (Φ n).hasCompactSupport_normed
  set Qm : ℕ → ℂ → ℂ := fun m => MeasureTheory.convolution (ρ m) q L volume with hQmdef
  set QE : ℕ → ℂ → ℂ := fun m => MeasureTheory.convolution (ρ m) qe L volume with hQEdef
  have hQmsm : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Qm m) := fun m =>
    (hρcs m).contDiff_convolution_left L (hρsm m) hqloc
  have hQmpt : ∀ z : ℂ, Filter.Tendsto (fun m => Qm m z) Filter.atTop (nhds (q z)) :=
    fun z => ContDiffBump.convolution_tendsto_right_of_continuous hΦr hqcont z
  have hQEcont : ∀ m, Continuous (QE m) := fun m =>
    (hρcs m).continuous_convolution_left L ((Φ m).continuous_normed) hqeloc
  have hQme : ∀ m z, (fderiv ℝ (Qm m) z) e = QE m z :=
    fun m z => fderiv_convolution_normed_apply_eq hqe hqloc hqeloc (hρsm m) (hρcs m) z
  -- The test-function identity.
  intro φ hφ hφc hφs
  set S : Set ℂ := tsupport φ with hSdef
  have hScomp : IsCompact S := hφc
  have hSm : MeasurableSet S := (isClosed_tsupport φ).measurableSet
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Mφ, hMφ⟩ := hφcont.bounded_above_of_compact_support hφc
  have hMφ0 : 0 ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
  have hφzero : ∀ z, z ∉ S → φ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (subset_tsupport φ hne)
  have hdφcont : Continuous fun z => (fderiv ℝ φ z) e := by
    have h1 : Continuous (fderiv ℝ φ) :=
      (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by
        rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])).continuous
    exact (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp h1
  have hdφsupp : Function.support (fun z => (fderiv ℝ φ z) e) ⊆ S := by
    intro z hz
    have h1 : fderiv ℝ φ z ≠ 0 := by
      intro h0
      refine hz ?_
      change (fderiv ℝ φ z) e = 0
      rw [h0]
      rfl
    have h2 : z ∈ Function.support (fderiv ℝ φ) := h1
    exact (support_fderiv_subset ℝ) h2
  have hdec : ∀ (T : ℂ →L[ℝ] ℂ) (u : ℂ), T u = u.re • T 1 + u.im • T Complex.I := by
    intro T u
    conv_lhs => rw [show u = u.re • (1 : ℂ) + u.im • Complex.I by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
    rw [map_add, map_smul, map_smul]
  -- The classical identity at level `m`.
  have hIm : ∀ m : ℕ,
      ∫ z, ((fderiv ℝ φ z) e) • G (Qm m z)
        = -∫ z, φ z • ((QE m z).re • DXG (Qm m z) + (QE m z).im • DYG (Qm m z)) := by
    intro m
    have hcomp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z => G (Qm m z) :=
      hGsm.comp (hQmsm m)
    have hcomp1 : ContDiffOn ℝ 1 (fun z => G (Qm m z)) Set.univ :=
      (hcomp.of_le hone_top).contDiffOn
    have hW := HasWeakDirDeriv.of_contDiffOn (v := e) isOpen_univ hcomp1
    have hid := hW φ hφ hφc (by intro z _; trivial)
    have hchain : ∀ z, (fderiv ℝ (fun z => G (Qm m z)) z) e
        = (QE m z).re • DXG (Qm m z) + (QE m z).im • DYG (Qm m z) := by
      intro z
      have hdF : DifferentiableAt ℝ G (Qm m z) :=
        (hGsm.differentiable htop_ne).differentiableAt
      have hdQ : DifferentiableAt ℝ (Qm m) z :=
        ((hQmsm m).differentiable htop_ne).differentiableAt
      have hcompeq : (fun z => G (Qm m z)) = G ∘ (Qm m) := rfl
      rw [hcompeq, fderiv_comp z hdF hdQ]
      have h1 : ((fderiv ℝ G (Qm m z)).comp (fderiv ℝ (Qm m) z)) e
          = (fderiv ℝ G (Qm m z)) ((fderiv ℝ (Qm m) z) e) := rfl
      rw [h1, hQme m z, hdec (fderiv ℝ G (Qm m z)) (QE m z)]
    calc ∫ z, ((fderiv ℝ φ z) e) • G (Qm m z)
        = -∫ z, φ z • (fderiv ℝ (fun z => G (Qm m z)) z) e := hid
      _ = -∫ z, φ z • ((QE m z).re • DXG (Qm m z) + (QE m z).im • DYG (Qm m z)) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact congrArg (fun t => φ z • t) (hchain z)
  -- `m → ∞` on the left-hand side.
  have hLHS : Filter.Tendsto (fun m => ∫ z, ((fderiv ℝ φ z) e) • G (Qm m z))
      Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) e) • G (q z))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun z => ‖(fderiv ℝ φ z) e‖ * MG) ?_ ?_ ?_ ?_
    · intro m
      exact (hdφcont.smul (hGcont.comp (hQmsm m).continuous)).aestronglyMeasurable
    · have hbcont : Continuous fun z => ‖(fderiv ℝ φ z) e‖ * MG :=
        (hdφcont.norm).mul continuous_const
      have hbcs : HasCompactSupport fun z => ‖(fderiv ℝ φ z) e‖ * MG := by
        have h1 : Function.support (fun z => ‖(fderiv ℝ φ z) e‖ * MG) ⊆ S := by
          intro z hz
          refine hdφsupp ?_
          intro h0
          have h0' : (fderiv ℝ φ z) e = 0 := h0
          refine hz ?_
          change ‖(fderiv ℝ φ z) e‖ * MG = 0
          rw [h0']
          simp
        refine IsCompact.of_isClosed_subset hScomp (isClosed_tsupport _) ?_
        exact closure_minimal h1 (isClosed_tsupport φ)
      exact hbcont.integrable_of_hasCompactSupport hbcs
    · intro m
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hMG _) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun z => ?_
      exact Filter.Tendsto.const_smul ((hGcont.tendsto _).comp (hQmpt z)) _
  -- `L¹(S)` convergence of the mollified weak derivative.
  have hL2 := mollify_L2_loc hqem hqe2 hScomp hSm Φ hΦr
  have hQEL1 : Filter.Tendsto
      (fun m => ∫ z in S, ‖QE m z - qe z‖) Filter.atTop (nhds 0) := by
    have hle : ∀ m, eLpNorm (fun z => QE m z - qe z) 1 (volume.restrict S)
        ≤ eLpNorm (fun z => QE m z - qe z) 2 (volume.restrict S)
          * (volume S) ^ (1/2 : ℝ) := by
      intro m
      have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
        (by norm_num)
        (((hQEcont m).measurable.sub hqem).aestronglyMeasurable
          (μ := volume.restrict S))
      have h2 : (volume.restrict S) Set.univ = volume S := by
        rw [Measure.restrict_apply_univ]
      rw [h2] at h1
      have h3 : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = 1/2 := by
        norm_num
      rw [h3] at h1
      exact h1
    have hSvol : volume S ≠ ⊤ := hScomp.measure_lt_top.ne
    have hlim2 : Filter.Tendsto
        (fun m => eLpNorm (fun z => QE m z - qe z) 2 (volume.restrict S)
          * (volume S) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hfin : (volume S) ^ (1/2 : ℝ) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSvol
      have := ENNReal.Tendsto.mul_const hL2 (Or.inr hfin)
      rwa [zero_mul] at this
    have hlim1 : Filter.Tendsto
        (fun m => eLpNorm (fun z => QE m z - qe z) 1 (volume.restrict S))
        Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim2
        (Filter.Eventually.of_forall fun m => zero_le _)
        (Filter.Eventually.of_forall hle)
    have hint : ∀ m, ∫ z in S, ‖QE m z - qe z‖
        = (eLpNorm (fun z => QE m z - qe z) 1 (volume.restrict S)).toReal := by
      intro m
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact integral_norm_eq_lintegral_enorm
        (((hQEcont m).measurable.sub hqem).aestronglyMeasurable)
    have htoReal : Filter.Tendsto
        (fun m => (eLpNorm (fun z => QE m z - qe z) 1 (volume.restrict S)).toReal)
        Filter.atTop (nhds 0) := by
      have h0 : (0 : ℝ≥0∞).toReal = 0 := rfl
      rw [← h0]
      exact (ENNReal.tendsto_toReal (by norm_num)).comp hlim1
    -- Right-hand side convergence, via the abstract pairing limit.
    refine htoReal.congr fun m => (hint m).symm
  have hqeS : IntegrableOn qe S volume := hqeloc.integrableOn_isCompact hScomp
  have hRHS : Filter.Tendsto
      (fun m => ∫ z, φ z • ((QE m z).re • DXG (Qm m z) + (QE m z).im • DYG (Qm m z)))
      Filter.atTop
      (nhds (∫ z, φ z • ((qe z).re • DXG (q z) + (qe z).im • DYG (q z)))) := by
    refine pairing_tendsto hScomp hSm hφcont hφzero hMφ hqem hqeS
      (u := fun z => DXG (q z)) (v := fun z => DYG (q z))
      (hDXGc.comp hqcont) (hDYGc.comp hqcont)
      (U := fun m z => DXG (Qm m z)) (V := fun m z => DYG (Qm m z))
      (fun m => hDXGc.comp (hQmsm m).continuous)
      (fun m => hDYGc.comp (hQmsm m).continuous)
      (MX := MX) (MY := MY)
      (fun m z => hMX _) (fun m z => hMY _) (fun z => hMX _) (fun z => hMY _)
      (fun z => (hDXGc.tendsto _).comp (hQmpt z))
      (fun z => (hDYGc.tendsto _).comp (hQmpt z))
      hQEcont hQEL1
  -- Conclude: uniqueness of limits against the classical identities.
  have h1 : (fun m => ∫ z, ((fderiv ℝ φ z) e) • G (Qm m z))
      = fun m => -∫ z, φ z • ((QE m z).re • DXG (Qm m z) + (QE m z).im • DYG (Qm m z)) :=
    funext hIm
  have h2 : Filter.Tendsto (fun m => ∫ z, ((fderiv ℝ φ z) e) • G (Qm m z))
      Filter.atTop
      (nhds (-∫ z, φ z • ((qe z).re • DXG (q z) + (qe z).im • DYG (q z)))) := by
    rw [h1]
    exact hRHS.neg
  exact tendsto_nhds_unique hLHS h2

/-- `lintegral` bound for a paired integrand against the composed
frames, through the change-of-variables estimate. -/
theorem cov_pairing_bound
    {q : ℂ → ℂ} {bq : BeltramiCoeff} (hq : IsQCAnalytic q bq)
    {e : ℂ} (hen : ‖e‖ = 1) {qe : ℂ → ℂ} (hqem : Measurable qe)
    (hae : ∀ᵐ w : ℂ, (fderiv ℝ q w) e = qe w)
    {φ : ℂ → ℝ} {S : Set ℂ} (hSm : MeasurableSet S)
    (hφzero : ∀ z, z ∉ S → φ z = 0) {Mφ : ℝ} (hMφ : ∀ z, ‖φ z‖ ≤ Mφ)
    {dX dY : ℂ → ℂ} (hdXm : Measurable dX) (hdYm : Measurable dY) :
    ∫⁻ z, ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖ₑ
      ≤ ENNReal.ofReal Mφ *
        ((((∫⁻ z, ‖dX z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)) + ((∫⁻ z, ‖dY z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)))
          * ((ENNReal.ofReal ((1 + bq.normInf) ^ 2 / (1 - bq.normInf ^ 2)) * volume S)
            ^ (1/2 : ℝ))) := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hqcont : Continuous q := hq.1.1.continuous
  have habs_re : ∀ w : ℂ, |w.re| ≤ ‖w‖ := fun w => Complex.abs_re_le_norm w
  have habs_im : ∀ w : ℂ, |w.im| ≤ ‖w‖ := fun w => Complex.abs_im_le_norm w
  -- The integrand vanishes off `S`.
  have hind : (fun z => ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖ₑ)
      = S.indicator (fun z => ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖ₑ) := by
    funext z
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS]
    · rw [Set.indicator_of_notMem hzS, hφzero z hzS]
      have h00 : (0:ℝ) • ((qe z).re • dX (q z) + (qe z).im • dY (q z)) = 0 :=
        zero_smul ℝ _
      rw [h00]
      simp
  rw [hind, lintegral_indicator hSm]
  -- Pointwise bound in `ℝ≥0∞`.
  have hpt : ∀ z, ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖ₑ
      ≤ ENNReal.ofReal Mφ * (‖qe z‖ₑ * (‖dX (q z)‖ₑ + ‖dY (q z)‖ₑ)) := by
    intro z
    have hreal : ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖
        ≤ Mφ * (‖qe z‖ * (‖dX (q z)‖ + ‖dY (q z)‖)) := by
      rw [norm_smul]
      have h1 : ‖(qe z).re • dX (q z) + (qe z).im • dY (q z)‖
          ≤ ‖qe z‖ * (‖dX (q z)‖ + ‖dY (q z)‖) := by
        calc ‖(qe z).re • dX (q z) + (qe z).im • dY (q z)‖
            ≤ ‖(qe z).re • dX (q z)‖ + ‖(qe z).im • dY (q z)‖ := norm_add_le _ _
          _ = |(qe z).re| * ‖dX (q z)‖ + |(qe z).im| * ‖dY (q z)‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖qe z‖ * (‖dX (q z)‖ + ‖dY (q z)‖) := by
              have h2 := habs_re (qe z)
              have h3 := habs_im (qe z)
              have h4 := norm_nonneg (dX (q z))
              have h5 := norm_nonneg (dY (q z))
              have h6 := abs_nonneg (qe z).re
              have h7 := abs_nonneg (qe z).im
              nlinarith
      have h8 := hMφ z
      have h9 := norm_nonneg (φ z)
      have h10 : (0:ℝ) ≤ ‖qe z‖ * (‖dX (q z)‖ + ‖dY (q z)‖) := by positivity
      nlinarith [norm_nonneg ((qe z).re • dX (q z) + (qe z).im • dY (q z))]
    calc ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖ₑ
        = ENNReal.ofReal ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖ :=
          (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal (Mφ * (‖qe z‖ * (‖dX (q z)‖ + ‖dY (q z)‖))) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal Mφ * (‖qe z‖ₑ * (‖dX (q z)‖ₑ + ‖dY (q z)‖ₑ)) := by
          have hMφ0 : 0 ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
          rw [ENNReal.ofReal_mul hMφ0, ENNReal.ofReal_mul (norm_nonneg _),
            ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
            ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]
  -- Assemble through the change-of-variables bound.
  have hqe_meas : Measurable fun z => ‖qe z‖ₑ := hqem.enorm
  have hdXq_meas : Measurable fun z => ‖dX (q z)‖ₑ :=
    (hdXm.comp hqcont.measurable).enorm
  have hdYq_meas : Measurable fun z => ‖dY (q z)‖ₑ :=
    (hdYm.comp hqcont.measurable).enorm
  calc ∫⁻ z in S, ‖φ z • ((qe z).re • dX (q z) + (qe z).im • dY (q z))‖ₑ
      ≤ ∫⁻ z in S, ENNReal.ofReal Mφ * (‖qe z‖ₑ * (‖dX (q z)‖ₑ + ‖dY (q z)‖ₑ)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal Mφ *
        ∫⁻ z in S, ‖qe z‖ₑ * (‖dX (q z)‖ₑ + ‖dY (q z)‖ₑ) := by
        rw [lintegral_const_mul _ (hqe_meas.mul (hdXq_meas.add hdYq_meas))]
    _ = ENNReal.ofReal Mφ *
        ∫⁻ z in S, (‖dX (q z)‖ₑ * ‖qe z‖ₑ + ‖dY (q z)‖ₑ * ‖qe z‖ₑ) := by
        congr 1
        refine lintegral_congr fun z => ?_
        ring
    _ ≤ ENNReal.ofReal Mφ *
        ((((∫⁻ z, ‖dX z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ))
            + ((∫⁻ z, ‖dY z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)))
          * ((ENNReal.ofReal ((1 + bq.normInf) ^ 2 / (1 - bq.normInf ^ 2)) * volume S)
            ^ (1/2 : ℝ))) := by
        gcongr
        have hDe_meas : Measurable fun w => ‖(fderiv ℝ q w) e‖ₑ :=
          (measurable_fderiv_apply_const ℝ q e).enorm
        have h1 : ∀ᵐ w ∂(volume.restrict S),
            ‖dX (q w)‖ₑ * ‖qe w‖ₑ + ‖dY (q w)‖ₑ * ‖qe w‖ₑ
            = ‖dX (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ + ‖dY (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ := by
          filter_upwards [ae_restrict_of_ae hae] with w hw
          rw [hw]
        calc ∫⁻ z in S, (‖dX (q z)‖ₑ * ‖qe z‖ₑ + ‖dY (q z)‖ₑ * ‖qe z‖ₑ)
            = ∫⁻ w in S, (‖dX (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ
                + ‖dY (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ) := lintegral_congr_ae h1
          _ = (∫⁻ w in S, ‖dX (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ)
              + ∫⁻ w in S, ‖dY (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ :=
              lintegral_add_left (μ := volume.restrict S) (hdXq_meas.mul hDe_meas)
                (fun w => ‖dY (q w)‖ₑ * ‖(fderiv ℝ q w) e‖ₑ)
          _ ≤ (((∫⁻ z, ‖dX z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ))
                * ((ENNReal.ofReal ((1 + bq.normInf) ^ 2 / (1 - bq.normInf ^ 2))
                  * volume S) ^ (1/2 : ℝ)))
              + (((∫⁻ z, ‖dY z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ))
                * ((ENNReal.ofReal ((1 + bq.normInf) ^ 2 / (1 - bq.normInf ^ 2))
                  * volume S) ^ (1/2 : ℝ))) :=
              add_le_add (qc_cov_bound hq hSm hen dX hdXm)
                (qc_cov_bound hq hSm hen dY hdYm)
          _ = (((∫⁻ z, ‖dX z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ))
                + ((∫⁻ z, ‖dY z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)))
              * ((ENNReal.ofReal ((1 + bq.normInf) ^ 2 / (1 - bq.normInf ^ 2))
                * volume S) ^ (1/2 : ℝ)) := (add_mul _ _ _).symm

-- The `L²`-error assembly and the finiteness bookkeeping need the raised budget.
set_option maxHeartbeats 400000 in
-- The frame-convergence limit interchanges two L2 limits against test pairings;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- If the frames `GX n, GY n` converge in `L²(ℂ)` to `gX, gY` and are
bounded, the paired integrals against the composed frames converge, by the
change-of-variables estimate. -/
theorem pairing_tendsto_L2
    {q : ℂ → ℂ} {bq : BeltramiCoeff} (hq : IsQCAnalytic q bq)
    {e : ℂ} (hen : ‖e‖ = 1) {qe : ℂ → ℂ} (hqem : Measurable qe)
    (hae : ∀ᵐ w : ℂ, (fderiv ℝ q w) e = qe w)
    {φ : ℂ → ℝ} {S : Set ℂ} (hScomp : IsCompact S) (hSm : MeasurableSet S)
    (hφcont : Continuous φ) (hφzero : ∀ z, z ∉ S → φ z = 0)
    {Mφ : ℝ} (hMφ : ∀ z, ‖φ z‖ ≤ Mφ)
    (hqeS : IntegrableOn qe S volume)
    {gX gY : ℂ → ℂ} (hgXm : Measurable gX) (hgYm : Measurable gY)
    (hgX2 : MemLp gX 2 volume) (hgY2 : MemLp gY 2 volume)
    {GX GY : ℕ → ℂ → ℂ} (hGXc : ∀ n, Continuous (GX n)) (hGYc : ∀ n, Continuous (GY n))
    (hGXb : ∀ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖GX n p‖ ≤ M)
    (hGYb : ∀ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖GY n p‖ ≤ M)
    (hX2 : Filter.Tendsto (fun n => eLpNorm (fun z => GX n z - gX z) 2 volume)
      Filter.atTop (nhds 0))
    (hY2 : Filter.Tendsto (fun n => eLpNorm (fun z => GY n z - gY z) 2 volume)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)))
      Filter.atTop
      (nhds (∫ z, φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z)))) := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hqcont : Continuous q := hq.1.1.continuous
  have hMφ0 : 0 ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
  have habs_re : ∀ w : ℂ, |w.re| ≤ ‖w‖ := fun w => Complex.abs_re_le_norm w
  have habs_im : ∀ w : ℂ, |w.im| ≤ ‖w‖ := fun w => Complex.abs_im_le_norm w
  set C : ℝ≥0∞ := (ENNReal.ofReal ((1 + bq.normInf) ^ 2 / (1 - bq.normInf ^ 2))
    * volume S) ^ (1/2 : ℝ) with hCdef
  have hC_ne_top : C ≠ ⊤ := by
    rw [hCdef]
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hScomp.measure_lt_top).ne
  -- The square-integral norms in `eLpNorm` form.
  have hel : ∀ h : ℂ → ℂ, ((∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)) = eLpNorm h 2 volume := by
    intro h
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
    rw [h2]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.rpow_natCast (‖h z‖ₑ) 2]
    norm_num
  -- Integrability of the limit integrand, via the pairing bound.
  have hlim_meas : AEStronglyMeasurable
      (fun z => φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))) volume := by
    refine AEStronglyMeasurable.smul hφcont.aestronglyMeasurable ?_
    refine AEStronglyMeasurable.add ?_ ?_
    · exact ((Complex.measurable_re.comp hqem).aestronglyMeasurable).smul
        ((hgXm.comp hqcont.measurable).aestronglyMeasurable)
    · exact ((Complex.measurable_im.comp hqem).aestronglyMeasurable).smul
        ((hgYm.comp hqcont.measurable).aestronglyMeasurable)
  have hIlim : Integrable
      (fun z => φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))) volume := by
    refine ⟨hlim_meas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (cov_pairing_bound hq hen hqem hae hSm hφzero hMφ
      hgXm hgYm) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    refine ENNReal.mul_lt_top ?_ ?_
    · rw [lt_top_iff_ne_top]
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · rw [hel gX]
        exact hgX2.2.ne
      · rw [hel gY]
        exact hgY2.2.ne
    · rw [lt_top_iff_ne_top]
      exact hC_ne_top
  -- Integrability of the `n`-th integrands, by boundedness of the frames.
  have hIn : ∀ n, Integrable
      (fun z => φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))) volume := by
    intro n
    obtain ⟨MnX, hMnX0, hMnX⟩ := hGXb n
    obtain ⟨MnY, hMnY0, hMnY⟩ := hGYb n
    have hdom : Integrable
        (S.indicator (fun z => Mφ * ((MnX + MnY) * ‖qe z‖))) volume := by
      rw [MeasureTheory.integrable_indicator_iff hSm]
      exact ((hqeS.norm.const_mul (MnX + MnY)).const_mul Mφ)
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · refine AEStronglyMeasurable.smul hφcont.aestronglyMeasurable ?_
      refine AEStronglyMeasurable.add ?_ ?_
      · exact ((Complex.measurable_re.comp hqem).aestronglyMeasurable).smul
          (((hGXc n).comp hqcont).aestronglyMeasurable)
      · exact ((Complex.measurable_im.comp hqem).aestronglyMeasurable).smul
          (((hGYc n).comp hqcont).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun z => ?_
      by_cases hzS : z ∈ S
      · rw [Set.indicator_of_mem hzS, norm_smul]
        have h1 : ‖(qe z).re • GX n (q z) + (qe z).im • GY n (q z)‖
            ≤ (MnX + MnY) * ‖qe z‖ := by
          calc ‖(qe z).re • GX n (q z) + (qe z).im • GY n (q z)‖
              ≤ ‖(qe z).re • GX n (q z)‖ + ‖(qe z).im • GY n (q z)‖ := norm_add_le _ _
            _ = |(qe z).re| * ‖GX n (q z)‖ + |(qe z).im| * ‖GY n (q z)‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            _ ≤ (MnX + MnY) * ‖qe z‖ := by
                have h4 := hMnX (q z)
                have h5 := hMnY (q z)
                have h6 := norm_nonneg (qe z)
                have h7 := habs_re (qe z)
                have h8 := habs_im (qe z)
                have h9 := abs_nonneg (qe z).re
                have h10 := abs_nonneg (qe z).im
                nlinarith
        have h2 := hMφ z
        have h3 : (0:ℝ) ≤ ‖φ z‖ := norm_nonneg _
        have h11 : (0:ℝ) ≤ (MnX + MnY) * ‖qe z‖ := by positivity
        nlinarith [norm_nonneg ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))]
      · have h00 : (0:ℝ) • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)) = 0 :=
          zero_smul ℝ _
        rw [hφzero z hzS, h00, norm_zero]
        exact Set.indicator_nonneg (fun y _ => by positivity) z
  -- The difference bound in `ℝ≥0∞`, and the squeeze.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set bound : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal Mφ *
    ((eLpNorm (fun z => GX n z - gX z) 2 volume
      + eLpNorm (fun z => GY n z - gY z) 2 volume) * C) with hbounddef
  have hchain : ∀ n, ENNReal.ofReal
      ‖(∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)))
        - ∫ z, φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))‖ ≤ bound n := by
    intro n
    by_cases hbtop : bound n = ⊤
    · rw [hbtop]
      exact le_top
    -- Difference of integrals as the integral of the difference.
    have hsub : (∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)))
        - ∫ z, φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))
        = ∫ z, (φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))
          - φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))) :=
      (MeasureTheory.integral_sub (hIn n) hIlim).symm
    -- The pointwise difference is a pairing against the difference frames.
    have hptdiff : ∀ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))
        - φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))
        = φ z • ((qe z).re • (GX n (q z) - gX (q z))
          + (qe z).im • (GY n (q z) - gY (q z))) := by
      intro z
      module
    have hlint : ∫⁻ z, ‖φ z • ((qe z).re • ((fun p => GX n p - gX p) (q z))
        + (qe z).im • ((fun p => GY n p - gY p) (q z)))‖ₑ ≤ bound n := by
      refine le_trans (cov_pairing_bound (dX := fun p => GX n p - gX p)
        (dY := fun p => GY n p - gY p) hq hen hqem hae hSm hφzero hMφ
        ((hGXc n).measurable.sub hgXm) ((hGYc n).measurable.sub hgYm)) ?_
      rw [hbounddef]
      refine mul_le_mul_right ?_ _
      refine mul_le_mul_left ?_ _
      refine add_le_add ?_ ?_
      · rw [hel (fun p => GX n p - gX p)]
      · rw [hel (fun p => GY n p - gY p)]
    have hlint_ne : ∫⁻ z, ‖φ z • ((qe z).re • (GX n (q z) - gX (q z))
        + (qe z).im • (GY n (q z) - gY (q z)))‖ₑ ≠ ⊤ :=
      fun h => hbtop (top_le_iff.mp (h ▸ hlint))
    calc ENNReal.ofReal ‖(∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)))
          - ∫ z, φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))‖
        = ENNReal.ofReal ‖∫ z, (φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))
            - φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z)))‖ := by rw [hsub]
      _ ≤ ∫⁻ z, ‖φ z • ((qe z).re • (GX n (q z) - gX (q z))
            + (qe z).im • (GY n (q z) - gY (q z)))‖ₑ := by
          have h1 := MeasureTheory.norm_integral_le_lintegral_norm
            (μ := (volume : Measure ℂ))
            (fun z => φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))
              - φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z)))
          have h2 : ∫⁻ z, ENNReal.ofReal
              ‖φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))
                - φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))‖
              = ∫⁻ z, ‖φ z • ((qe z).re • (GX n (q z) - gX (q z))
                + (qe z).im • (GY n (q z) - gY (q z)))‖ₑ := by
            refine lintegral_congr fun z => ?_
            rw [hptdiff z, ofReal_norm_eq_enorm]
          rw [h2] at h1
          calc ENNReal.ofReal ‖∫ z,
                (φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z))
                  - φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z)))‖
              ≤ ENNReal.ofReal ((∫⁻ z, ‖φ z • ((qe z).re • (GX n (q z) - gX (q z))
                  + (qe z).im • (GY n (q z) - gY (q z)))‖ₑ).toReal) :=
                ENNReal.ofReal_le_ofReal h1
            _ = _ := ENNReal.ofReal_toReal hlint_ne
      _ ≤ bound n := by
          refine le_trans (le_of_eq ?_) hlint
          rfl
  -- The bound tends to `0`.
  have hboundlim : Filter.Tendsto bound Filter.atTop (nhds 0) := by
    have h1 := hX2.add hY2
    rw [add_zero] at h1
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hC_ne_top)
    rw [zero_mul] at h2
    have hMne : ENNReal.ofReal Mφ ≠ ⊤ := ENNReal.ofReal_ne_top
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hMne)
    rwa [mul_zero] at h3
  -- Convert back to the real line.
  have hzero : Filter.Tendsto (fun n => ENNReal.ofReal
      ‖(∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)))
        - ∫ z, φ z • ((qe z).re • gX (q z) + (qe z).im • gY (q z))‖)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hboundlim
      (Filter.Eventually.of_forall fun n => zero_le _)
      (Filter.Eventually.of_forall hchain)
  have htr := (ENNReal.tendsto_toReal (by norm_num : (0:ℝ≥0∞) ≠ ⊤)).comp hzero
  refine Filter.Tendsto.congr ?_ htr
  intro n
  exact ENNReal.toReal_ofReal (norm_nonneg _)

end RiemannDynamics

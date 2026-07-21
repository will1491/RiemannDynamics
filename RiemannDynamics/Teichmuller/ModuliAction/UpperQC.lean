import RiemannDynamics.Teichmuller.ModuliAction.Interpolate
import RiemannDynamics.Uniformization.Fuchsian
import RiemannDynamics.Uniformization.HolomorphicEquiv
import RiemannDynamics.QC.MRMT.Uniqueness
import RiemannDynamics.QC.Calculus.WeylLocal
import RiemannDynamics.QC.Calculus.AnalyticClosedness
import RiemannDynamics.QC.InverseQC.LusinN
import RiemannDynamics.QC.Regularity.Quasisymmetry
import RiemannDynamics.Hyperbolic.DiskModel.DiskMetric

/-!
# Upper-half-plane quasiconformal conjugacies and Marden stability

Quasiconformal self-maps of the open upper half plane and the generator form of Marden
stability at the level of the upper half plane: the conjugating map is a self-map of `ℍ`,
exact on the generator tuples, with Beltrami bound tending to `0`. A conjugacy of an
exactly matched marked pair of cocompact Fuchsian groups has a rigid boundary map, so it
does not in general extend to a plane homeomorphism; the upper-half-plane formulation
carries the full content of the stability statement.

* `IsQCUpper` — quasiconformal self-maps of the upper half plane with a Beltrami bound.
* `isQCUpper_of_isQCGeometric` — symmetric plane quasiconformal homeomorphisms preserving
  the upper half plane restrict to upper-half-plane quasiconformal maps.
* `exists_equivariant_upper_conjugacy_K_to_one` — **Marden stability**: along generator
  tuples converging to the tuple of a cocompact trace-gapped limit group, for every
  `κ > 0`, eventually there is an upper-half-plane quasiconformal conjugacy with Beltrami
  bound `κ` intertwining the tuples exactly.
* `exists_sl2_factorization_of_eq_coeff` — factorization: two solutions of the same
  Beltrami equation on the upper half plane differ by a real Möbius map.
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

/-- Stage A (X3+X4+X5): change-of-variables/Hölder bound for a plane quasiconformal map.
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

/-- Stage B1 (X6a): localized `L²` convergence of mollifications. On a compact set the
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
/-- Stage B2a′ (abstract pairing limit): if `QE m → qe` in `L¹` of the compact support of
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
/-- Stage B2a (X6): weak chain rule for the composition of a smooth compactly supported
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

/-- Stage B2b (X7-core): `lintegral` bound for a paired integrand against the composed
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
/-- Stage B2c (X7): if the frames `GX n, GY n` converge in `L²(ℂ)` to `gX, gY` and are
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

-- Instantiating the two abstract limit lemmas over the mollified frames is a heavy
-- elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The weak chain rule assembles the three mollification stages in one declaration;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage B2 (X6–X8): weak chain rule for the composition of a compactly supported
continuous `W^{1,2}` function with a plane quasiconformal map, in the directions `1, I`. -/
theorem hasWeakDirDeriv_comp_qc
    {q : ℂ → ℂ} {bq : BeltramiCoeff} (hq : IsQCAnalytic q bq)
    {e : ℂ} (he : e = 1 ∨ e = Complex.I)
    {qe : ℂ → ℂ} (hqe : HasWeakDirDeriv e qe q Set.univ) (hqem : Measurable qe)
    (hqe2 : MemLpLocOn qe 2 Set.univ)
    {F Fx Fy : ℂ → ℂ} (hFc : Continuous F) (hFsupp : HasCompactSupport F)
    (hFwg : HasWeakGradient Fx Fy F Set.univ)
    (hFxm : Measurable Fx) (hFym : Measurable Fy)
    (hFx2 : MemLp Fx 2 volume) (hFy2 : MemLp Fy 2 volume) :
    HasWeakDirDeriv e
      (fun w => (qe w).re • Fx (q w) + (qe w).im • Fy (q w)) (fun w => F (q w))
      Set.univ := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hone_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one]
    exact WithTop.coe_le_coe.mpr le_top
  have htop_add : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
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
  have hFloc : MeasureTheory.LocallyIntegrable F volume := hFc.locallyIntegrable
  have hFxloc : MeasureTheory.LocallyIntegrable Fx volume :=
    hFx2.locallyIntegrable (by norm_num)
  have hFyloc : MeasureTheory.LocallyIntegrable Fy volume :=
    hFy2.locallyIntegrable (by norm_num)
  have henorm : ‖e‖ = 1 := by
    rcases he with rfl | rfl
    · simp
    · simp
  have hae : ∀ᵐ w : ℂ, (fderiv ℝ q w) e = qe w := by
    refine fderiv_ae_eq_weakDirDeriv hqe ?_ hq.ae_differentiableAt he hqloc
    rwa [MeasureTheory.locallyIntegrableOn_univ]
  obtain ⟨MF, hMF⟩ := hFc.bounded_above_of_compact_support hFsupp
  -- The bump family and the mollified outer maps.
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
  set Fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) F L volume with hFndef
  have hFnsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fn n) := fun n =>
    (hρcs n).contDiff_convolution_left L (hρsm n) hFloc
  have hFncs : ∀ n, HasCompactSupport (Fn n) := fun n =>
    (hρcs n).convolution L hFsupp
  have hFnpt : ∀ p : ℂ, Filter.Tendsto (fun n => Fn n p) Filter.atTop (nhds (F p)) :=
    fun p => ContDiffBump.convolution_tendsto_right_of_continuous hΦr hFc p
  -- Uniform bound on the mollified outer maps.
  have hFnbd : ∀ n z, ‖Fn n z‖ ≤ MF := by
    intro n z
    have hce : ConvolutionExistsAt (ρ n) F z L volume :=
      ((hρcs n).convolutionExists_left L ((Φ n).continuous_normed) hFloc) z
    have h1 : ‖Fn n z‖ ≤ ∫ t, ‖(ρ n) t • F (z - t)‖ := by
      rw [hFndef]
      exact norm_integral_le_integral_norm _
    have h2 : ∫ t, ‖(ρ n) t • F (z - t)‖ ≤ ∫ t, (ρ n) t * MF := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
        (((Φ n).integrable_normed).mul_const MF) ?_
      refine Filter.Eventually.of_forall fun t => ?_
      change ‖(ρ n) t • F (z - t)‖ ≤ (ρ n) t * MF
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((Φ n).nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hMF _) ((Φ n).nonneg_normed t)
    have h3 : ∫ t, (ρ n) t * MF = MF := by
      rw [MeasureTheory.integral_mul_const, (Φ n).integral_normed, one_mul]
    calc ‖Fn n z‖ ≤ ∫ t, ‖(ρ n) t • F (z - t)‖ := h1
      _ ≤ ∫ t, (ρ n) t * MF := h2
      _ = MF := h3
  -- The frame sequences: partial derivatives of the mollified outer maps.
  set GX : ℕ → ℂ → ℂ := fun n p => (fderiv ℝ (Fn n) p) 1 with hGXdef
  set GY : ℕ → ℂ → ℂ := fun n p => (fderiv ℝ (Fn n) p) Complex.I with hGYdef
  have hDFncont : ∀ n, Continuous (fderiv ℝ (Fn n)) := fun n =>
    ((hFnsm n).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) htop_add).continuous
  have hGXc : ∀ n, Continuous (GX n) := fun n =>
    (ContinuousLinearMap.apply ℝ ℂ 1).continuous.comp (hDFncont n)
  have hGYc : ∀ n, Continuous (GY n) := fun n =>
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous.comp (hDFncont n)
  have hGbd : ∀ n (u : ℂ), ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖(fderiv ℝ (Fn n) p) u‖ ≤ M := by
    intro n u
    have hcont : Continuous fun p => (fderiv ℝ (Fn n) p) u :=
      (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp (hDFncont n)
    have hcs : HasCompactSupport fun p => (fderiv ℝ (Fn n) p) u := by
      have h1 : Function.support (fun p => (fderiv ℝ (Fn n) p) u)
          ⊆ tsupport (fderiv ℝ (Fn n)) := by
        intro p hp
        have h2 : fderiv ℝ (Fn n) p ≠ 0 := by
          intro h0
          refine hp ?_
          change (fderiv ℝ (Fn n) p) u = 0
          rw [h0]
          rfl
        exact subset_tsupport _ h2
      refine IsCompact.of_isClosed_subset ((hFncs n).fderiv ℝ) (isClosed_tsupport _) ?_
      exact closure_minimal h1 (isClosed_tsupport _)
    obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), hM⟩
  -- The `L²` convergence of the frames, from the derivative-of-mollification identity.
  have hFnx : ∀ n p, GX n p = MeasureTheory.convolution (ρ n) Fx L volume p :=
    fun n p => fderiv_convolution_normed_apply_eq hFwg.1 hFloc hFxloc (hρsm n) (hρcs n) p
  have hFny : ∀ n p, GY n p = MeasureTheory.convolution (ρ n) Fy L volume p :=
    fun n p => fderiv_convolution_normed_apply_eq hFwg.2 hFloc hFyloc (hρsm n) (hρcs n) p
  have hX2 : Filter.Tendsto (fun n => eLpNorm (fun z => GX n z - Fx z) 2 volume)
      Filter.atTop (nhds 0) := by
    have hcong : (fun n => eLpNorm (fun z => GX n z - Fx z) 2 volume)
        = fun n => eLpNorm
          (MeasureTheory.convolution (ρ n) Fx L volume - Fx) 2 volume := by
      funext n
      congr 1
      funext z
      rw [hFnx n z]
      rfl
    rw [hcong]
    exact eLpNorm_convolution_normed_sub_tendsto_zero hFx2 Φ hΦr
  have hY2 : Filter.Tendsto (fun n => eLpNorm (fun z => GY n z - Fy z) 2 volume)
      Filter.atTop (nhds 0) := by
    have hcong : (fun n => eLpNorm (fun z => GY n z - Fy z) 2 volume)
        = fun n => eLpNorm
          (MeasureTheory.convolution (ρ n) Fy L volume - Fy) 2 volume := by
      funext n
      congr 1
      funext z
      rw [hFny n z]
      rfl
    rw [hcong]
    exact eLpNorm_convolution_normed_sub_tendsto_zero hFy2 Φ hΦr
  -- The test-function identity.
  intro φ hφ hφc hφs
  set S : Set ℂ := tsupport φ with hSdef
  have hScomp : IsCompact S := hφc
  have hSm : MeasurableSet S := (isClosed_tsupport φ).measurableSet
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Mφ, hMφ⟩ := hφcont.bounded_above_of_compact_support hφc
  have hφzero : ∀ z, z ∉ S → φ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (subset_tsupport φ hne)
  have hqeS : IntegrableOn qe S volume := hqeloc.integrableOn_isCompact hScomp
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
    exact (support_fderiv_subset ℝ) h1
  -- The level-`n` identities from the smooth chain rule.
  have key1 : ∀ n : ℕ, ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z)
      = -∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)) := by
    intro n
    exact comp_smooth_qc hq hqe hqem hqe2 (hFnsm n) (hFncs n) φ hφ hφc
      (by intro z _; trivial)
  -- The left-hand limit.
  have hLHS : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z))
      Filter.atTop (nhds (∫ z, ((fderiv ℝ φ z) e) • F (q z))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun z => ‖(fderiv ℝ φ z) e‖ * MF) ?_ ?_ ?_ ?_
    · intro n
      exact (hdφcont.smul ((hFnsm n).continuous.comp hqcont)).aestronglyMeasurable
    · have hbcont : Continuous fun z => ‖(fderiv ℝ φ z) e‖ * MF :=
        (hdφcont.norm).mul continuous_const
      have hbcs : HasCompactSupport fun z => ‖(fderiv ℝ φ z) e‖ * MF := by
        have h1 : Function.support (fun z => ‖(fderiv ℝ φ z) e‖ * MF) ⊆ S := by
          intro z hz
          refine hdφsupp ?_
          intro h0
          have h0' : (fderiv ℝ φ z) e = 0 := h0
          refine hz ?_
          change ‖(fderiv ℝ φ z) e‖ * MF = 0
          rw [h0']
          simp
        refine IsCompact.of_isClosed_subset hScomp (isClosed_tsupport _) ?_
        exact closure_minimal h1 (isClosed_tsupport φ)
      exact hbcont.integrable_of_hasCompactSupport hbcs
    · intro n
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hFnbd n _) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun z => ?_
      exact Filter.Tendsto.const_smul (hFnpt (q z)) _
  -- The right-hand limit, from the `L²` pairing lemma.
  have hRHS : Filter.Tendsto
      (fun n => ∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)))
      Filter.atTop
      (nhds (∫ z, φ z • ((qe z).re • Fx (q z) + (qe z).im • Fy (q z)))) :=
    pairing_tendsto_L2 hq henorm hqem hae hScomp hSm hφcont hφzero hMφ hqeS
      hFxm hFym hFx2 hFy2 hGXc hGYc (fun n => hGbd n 1) (fun n => hGbd n Complex.I)
      hX2 hY2
  -- Conclude by uniqueness of limits.
  have h1 : (fun n => ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z))
      = fun n => -∫ z, φ z • ((qe z).re • GX n (q z) + (qe z).im • GY n (q z)) :=
    funext key1
  have h2 : Filter.Tendsto (fun n => ∫ z, ((fderiv ℝ φ z) e) • Fn n (q z))
      Filter.atTop
      (nhds (-∫ z, φ z • ((qe z).re • Fx (q z) + (qe z).im • Fy (q z)))) := by
    rw [h1]
    exact hRHS.neg
  exact tendsto_nhds_unique hLHS h2

-- The cutoff transfer to the plane lemma and the covering assembly are one long
-- elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The classical-derivative bridge runs a Lebesgue-point argument over the open set;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage C ([BRIDGE]): on an open set, the classical directional derivative of an
almost-everywhere differentiable function agrees almost everywhere with any locally
integrable weak directional derivative, by cutoff transfer to the plane statement. -/
theorem fderiv_ae_eq_weakDirDeriv_on
    {v g : ℂ → ℂ} {ed : ℂ} (hed : ed = 1 ∨ ed = Complex.I)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hg : HasWeakDirDeriv ed g v Ω)
    (hgloc : MeasureTheory.LocallyIntegrableOn g Ω volume)
    (hvcont : ContinuousOn v Ω)
    (hdiff : ∀ᵐ z ∂(volume.restrict Ω), DifferentiableAt ℝ v z) :
    ∀ᵐ z ∂(volume.restrict Ω), (fderiv ℝ v z) ed = g z := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hdiff' : ∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ v z :=
    (ae_restrict_iff' hΩ.measurableSet).mp hdiff
  -- The per-ball statement.
  have hball : ∀ z₀ : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall z₀ (2*r) ⊆ Ω →
      ∀ᵐ z : ℂ, z ∈ Metric.ball z₀ r → (fderiv ℝ v z) ed = g z := by
    intro z₀ r hr hsub
    -- The cutoff bump.
    set χb : ContDiffBump z₀ :=
      { rIn := (3/2) * r, rOut := (9/5) * r,
        rIn_pos := by linarith,
        rIn_lt_rOut := by linarith } with hχdef
    set χ : ℂ → ℝ := fun z => χb z with hχfun
    have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := χb.contDiff
    have hχsupp : Function.support χ = Metric.ball z₀ ((9/5) * r) := χb.support_eq
    have hχone : ∀ z ∈ Metric.closedBall z₀ ((3/2) * r), χ z = 1 := fun z hz =>
      χb.one_of_mem_closedBall hz
    have htsχ : tsupport χ ⊆ Metric.closedBall z₀ ((9/5) * r) := by
      rw [tsupport, hχsupp]
      exact Metric.closure_ball_subset_closedBall
    have htsΩ : tsupport χ ⊆ Ω := by
      refine subset_trans htsχ (subset_trans ?_ hsub)
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      linarith
    have hcompl : ∀ z : ℂ, z ∉ tsupport χ → χ z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport hz
    -- The plane cover: `ℂ = Ω ∪ (tsupport χ)ᶜ`.
    have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport χ := by
      intro z
      by_cases hz : z ∈ tsupport χ
      · exact Or.inl (htsΩ hz)
      · exact Or.inr hz
    -- The localized function and its weak derivative.
    set Fc : ℂ → ℂ := fun z => χ z • v z with hFcdef
    set Fg : ℂ → ℂ := fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z with hFgdef
    have hχcont : Continuous χ := hχsm.continuous
    have hdχcont : Continuous fun z => (fderiv ℝ χ z) ed := by
      have h1 : Continuous (fderiv ℝ χ) :=
        (hχsm.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
          (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
      exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
    have hdχsupp : ∀ z : ℂ, z ∉ tsupport χ → (fderiv ℝ χ z) ed = 0 := by
      intro z hz
      have h1 : fderiv ℝ χ z = 0 := by
        by_contra hne
        exact hz ((support_fderiv_subset ℝ)
          (by simpa [Function.mem_support] using hne))
      rw [h1]
      rfl
    have hKχ : IsCompact (tsupport χ) :=
      IsCompact.of_isClosed_subset (isCompact_closedBall z₀ ((9/5) * r))
        (isClosed_tsupport χ) htsχ
    -- Gluing continuity: continuous on `Ω`, vanishing off the support of the cutoff.
    have htop_ne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hcont_of : ∀ H : ℂ → ℂ, (∀ z, z ∈ Ω → ContinuousAt H z) →
        (∀ z, z ∉ tsupport χ → H z = 0) → Continuous H := by
      intro H h1 h2
      rw [continuous_iff_continuousAt]
      intro z
      rcases hcover z with hzΩ | hzout
      · exact h1 z hzΩ
      · have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
        have hev : ∀ᶠ w in nhds z, H w = 0 := by
          filter_upwards [hopen.mem_nhds hzout] with w hw
          exact h2 w hw
        refine ContinuousAt.congr (f := fun _ : ℂ => (0 : ℂ)) continuousAt_const ?_
        filter_upwards [hev] with w hw
        exact hw.symm
    have hFccont : Continuous Fc := by
      refine hcont_of Fc ?_ ?_
      · intro z hzΩ
        exact (hχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
      · intro z hz
        change χ z • v z = 0
        rw [hcompl z hz]
        exact zero_smul ℝ _
    -- Global integrability of the cutoff-weighted weak derivative.
    have hgK : IntegrableOn g (tsupport χ) volume :=
      hgloc.integrableOn_compact_subset htsΩ hKχ
    have hbmul : ∀ (b : ℂ → ℝ) (Mb : ℝ), Continuous b → (∀ z, |b z| ≤ Mb) →
        (∀ z, z ∉ tsupport χ → b z = 0) →
        Integrable (fun z => b z • g z) volume := by
      intro b Mb hbc hbM hb0
      have hmeas : AEStronglyMeasurable (fun z => b z • g z)
          (volume.restrict (tsupport χ)) :=
        (hbc.aestronglyMeasurable).smul hgK.aestronglyMeasurable
      have hint : IntegrableOn (fun z => b z • g z) (tsupport χ) volume := by
        refine MeasureTheory.Integrable.mono' (hgK.norm.const_mul Mb) hmeas ?_
        refine Filter.Eventually.of_forall fun z => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbM z) (norm_nonneg _)
      have hsupp : Function.support (fun z => b z • g z) ⊆ tsupport χ := by
        intro z hz
        by_contra hzout
        rw [Function.mem_support] at hz
        rw [hb0 z hzout] at hz
        exact hz (zero_smul ℝ _)
      exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hint
    -- The weak-derivative identity for the localization `Fc` on the whole plane.
    have hFcweak : HasWeakDirDeriv ed Fg Fc Set.univ := by
      intro φ hφ hφc hφs
      have hφcont : Continuous φ := hφ.continuous
      obtain ⟨Mφ, hMφ⟩ := hφcont.bounded_above_of_compact_support hφc
      have hφχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z * χ z) :=
        hφ.mul hχsm
      have hφχcs : HasCompactSupport (fun z => φ z * χ z) := by
        refine HasCompactSupport.intro hφc ?_
        intro z hz
        change φ z * χ z = 0
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      have hφχsupp : tsupport (fun z => φ z * χ z) ⊆ Ω := by
        refine subset_trans (closure_minimal ?_ (isClosed_tsupport χ)) htsΩ
        intro z hz
        rw [Function.mem_support] at hz
        have hχz : χ z ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
        exact subset_tsupport χ hχz
      have hid := hg (fun z => φ z * χ z) hφχsm hφχcs hφχsupp
      -- The product rule for the localized test function.
      have hfd : ∀ z, (fderiv ℝ (fun w => φ w * χ w) z) ed
          = φ z * ((fderiv ℝ χ z) ed) + χ z * ((fderiv ℝ φ z) ed) := by
        intro z
        have hφd : DifferentiableAt ℝ φ z :=
          (hφ.differentiable htop_ne).differentiableAt
        have hχd : DifferentiableAt ℝ χ z :=
          (hχsm.differentiable htop_ne).differentiableAt
        have h1 : (fun w => φ w * χ w) = φ * χ := rfl
        rw [h1, fderiv_mul hφd hχd]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul]
      -- The three integrable pieces.
      have hdφcont : Continuous fun z => (fderiv ℝ φ z) ed := by
        have h1 : Continuous (fderiv ℝ φ) :=
          (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
            (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
        exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
      have hI1cont : Continuous fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
        refine hcont_of _ ?_ ?_
        · intro z hzΩ
          exact ((hφcont.mul hdχcont).continuousAt).smul
            (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
        · intro z hz
          rw [hdχsupp z hz, mul_zero]
          exact zero_smul ℝ _
      have hI1cs : HasCompactSupport fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
        refine HasCompactSupport.intro hKχ ?_
        intro z hz
        rw [hdχsupp z hz, mul_zero]
        exact zero_smul ℝ _
      have hI1int : Integrable (fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z) volume :=
        hI1cont.integrable_of_hasCompactSupport hI1cs
      have hI2cont : Continuous fun z => ((fderiv ℝ φ z) ed) • Fc z :=
        hdφcont.smul hFccont
      have hI2cs : HasCompactSupport fun z => ((fderiv ℝ φ z) ed) • Fc z := by
        refine HasCompactSupport.intro hφc ?_
        intro z hz
        have h1 : fderiv ℝ φ z = 0 := by
          by_contra hne
          exact hz ((support_fderiv_subset ℝ)
            (by simpa [Function.mem_support] using hne))
        have h2 : (fderiv ℝ φ z) ed = 0 := by
          rw [h1]
          rfl
        rw [h2]
        exact zero_smul ℝ _
      have hI2int : Integrable (fun z => ((fderiv ℝ φ z) ed) • Fc z) volume :=
        hI2cont.integrable_of_hasCompactSupport hI2cs
      have hφχg_int : Integrable (fun z => (φ z * χ z) • g z) volume := by
        refine hbmul (fun z => φ z * χ z) (Mφ * 1) (hφcont.mul hχcont) ?_ ?_
        · intro z
          rw [abs_mul]
          have h1 : |φ z| ≤ Mφ := by
            have := hMφ z
            rwa [Real.norm_eq_abs] at this
          have h2 : |χ z| ≤ 1 := by
            rw [abs_of_nonneg (χb.nonneg)]
            exact χb.le_one
          have h3 : (0:ℝ) ≤ |φ z| := abs_nonneg _
          nlinarith [abs_nonneg (χ z)]
        · intro z hz
          change φ z * χ z = 0
          rw [hcompl z hz, mul_zero]
      have hI1g_int : Integrable
          (fun z => (φ z * χ z) • g z + (φ z * ((fderiv ℝ χ z) ed)) • v z) volume :=
        hφχg_int.add hI1int
      -- Assemble the identity.
      have hsplit : ∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
          = (∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z)
            + ∫ z, ((fderiv ℝ φ z) ed) • Fc z := by
        rw [← MeasureTheory.integral_add hI1int hI2int]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        change ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
          = (φ z * ((fderiv ℝ χ z) ed)) • v z + ((fderiv ℝ φ z) ed) • (χ z • v z)
        rw [hfd z]
        module
      have hgoal : ∫ z, ((fderiv ℝ φ z) ed) • Fc z = -∫ z, φ z • Fg z := by
        have h1 : ∫ z, ((fderiv ℝ φ z) ed) • Fc z
            = (∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z)
              - ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
          rw [hsplit]
          ring
        rw [h1, hid]
        have h2 : ∫ z, φ z • Fg z
            = (∫ z, (φ z * χ z) • g z) + ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
          rw [← MeasureTheory.integral_add hφχg_int hI1int]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          change φ z • (χ z • g z + ((fderiv ℝ χ z) ed) • v z)
            = (φ z * χ z) • g z + (φ z * ((fderiv ℝ χ z) ed)) • v z
          module
        rw [h2]
        ring
      exact hgoal
    -- Global almost-everywhere differentiability and integrability data.
    have hFcdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ Fc z := by
      filter_upwards [hdiff'] with z hz
      rcases hcover z with hzΩ | hzout
      · have hχd : DifferentiableAt ℝ χ z :=
          (hχsm.differentiable htop_ne).differentiableAt
        exact hχd.smul (hz hzΩ)
      · have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
        have hev : Fc =ᶠ[nhds z] fun _ => (0 : ℂ) := by
          filter_upwards [hopen.mem_nhds hzout] with w hw
          change χ w • v w = 0
          rw [hcompl w hw]
          exact zero_smul ℝ _
        exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr
          (differentiableAt_const 0)
    have hFcloc : MeasureTheory.LocallyIntegrable Fc volume := hFccont.locallyIntegrable
    have hFgint : Integrable Fg volume := by
      have h1 : Integrable (fun z => χ z • g z) volume := by
        refine hbmul χ 1 hχcont ?_ ?_
        · intro z
          rw [abs_of_nonneg (χb.nonneg)]
          exact χb.le_one
        · intro z hz
          exact hcompl z hz
      have h2cont : Continuous fun z => ((fderiv ℝ χ z) ed) • v z := by
        refine hcont_of _ ?_ ?_
        · intro z hzΩ
          exact (hdχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
        · intro z hz
          rw [hdχsupp z hz]
          exact zero_smul ℝ _
      have h2cs : HasCompactSupport fun z => ((fderiv ℝ χ z) ed) • v z := by
        refine HasCompactSupport.intro hKχ ?_
        intro z hz
        rw [hdχsupp z hz]
        exact zero_smul ℝ _
      exact h1.add (h2cont.integrable_of_hasCompactSupport h2cs)
    have hFgloc : MeasureTheory.LocallyIntegrableOn Fg Set.univ volume := by
      rw [MeasureTheory.locallyIntegrableOn_univ]
      exact hFgint.locallyIntegrable
    -- The plane statement applies to the localization.
    have haefd : ∀ᵐ z : ℂ, (fderiv ℝ Fc z) ed = Fg z :=
      fderiv_ae_eq_weakDirDeriv hFcweak hFgloc hFcdiff hed hFcloc
    -- Localize back to the small ball.
    filter_upwards [haefd] with z hz hzB
    have hmemIn : Metric.ball z₀ r ⊆ Metric.ball z₀ ((3/2) * r) :=
      Metric.ball_subset_ball (by linarith)
    have hopenIn : IsOpen (Metric.ball z₀ ((3/2) * r)) := Metric.isOpen_ball
    have hnb : Metric.ball z₀ ((3/2) * r) ∈ nhds z := hopenIn.mem_nhds (hmemIn hzB)
    have hFcev : Fc =ᶠ[nhds z] v := by
      filter_upwards [hnb] with w hw
      change χ w • v w = v w
      rw [hχone w (Metric.ball_subset_closedBall hw)]
      exact one_smul ℝ _
    have hχev : χ =ᶠ[nhds z] fun _ => (1 : ℝ) := by
      filter_upwards [hnb] with w hw
      exact hχone w (Metric.ball_subset_closedBall hw)
    have hfd1 : fderiv ℝ Fc z = fderiv ℝ v z := hFcev.fderiv_eq
    have hfd2 : fderiv ℝ χ z = 0 := by
      rw [hχev.fderiv_eq]
      exact fderiv_const_apply 1
    have hχz1 : χ z = 1 := hχone z (Metric.ball_subset_closedBall (hmemIn hzB))
    rw [hfd1] at hz
    rw [hz]
    change χ z • g z + ((fderiv ℝ χ z) ed) • v z = g z
    rw [hχz1, hfd2]
    simp
  -- Countable covering assembly.
  have hchoice : ∀ p : ℂ, p ∈ Ω → ∃ r : ℝ, 0 < r ∧ Metric.closedBall p (2*r) ⊆ Ω := by
    intro p hp
    obtain ⟨ε, hε, hballsub⟩ := Metric.isOpen_iff.mp hΩ p hp
    refine ⟨ε/3, by linarith, ?_⟩
    intro w hw
    refine hballsub ?_
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith
  classical
  set rad : Ω → ℝ := fun p => (hchoice p.1 p.2).choose with hraddef
  have hrad : ∀ p : Ω, 0 < rad p ∧ Metric.closedBall p.1 (2 * rad p) ⊆ Ω := fun p =>
    (hchoice p.1 p.2).choose_spec
  set s : Ω → Set ℂ := fun p => Metric.ball p.1 (rad p) with hsdef
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable s
    (fun p => Metric.isOpen_ball)
  have hcov : Ω ⊆ ⋃ p ∈ T, s p := by
    rw [hTeq]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hrad ⟨z, hz⟩).1⟩
  rw [ae_restrict_iff' hΩ.measurableSet]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ⋃ p ∈ T, {z : ℂ | z ∈ s p ∧ ¬ (fderiv ℝ v z) ed = g z})
    ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, not_forall] at hz
    obtain ⟨hzΩ, hzne⟩ := hz
    obtain ⟨p, hpT, hps⟩ := Set.mem_iUnion₂.mp (hcov hzΩ)
    exact Set.mem_iUnion₂.mpr ⟨p, hpT, ⟨hps, hzne⟩⟩
  · rw [measure_biUnion_null_iff hTc]
    intro p _
    have hp := hball p.1 (rad p) (hrad p).1 (hrad p).2
    rw [MeasureTheory.ae_iff] at hp
    refine measure_mono_null ?_ hp
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    intro hcontra
    exact hz.2 (hcontra hz.1)

-- The localized integration-by-parts assembly is one long elaboration; the raised
-- budget is required.
set_option maxHeartbeats 400000 in
-- The cutoff package discharges support, smoothness, and derivative bounds together;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage D1: the cutoff package. For a smooth compactly supported cutoff `χ` with
support in the open set `Ω`, the localization `χ • v` of a function with weak
directional derivative `g` on `Ω` has the Leibniz combination as a weak directional
derivative on the whole plane, and the two localized pieces are continuous. -/
theorem cutoff_hasWeakDirDeriv
    {v g : ℂ → ℂ} {ed : ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hg : HasWeakDirDeriv ed g v Ω)
    (hgloc : MeasureTheory.LocallyIntegrableOn g Ω volume)
    (hvcont : ContinuousOn v Ω)
    {χ : ℂ → ℝ} (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχcs : HasCompactSupport χ) (htsΩ : tsupport χ ⊆ Ω)
    (hχ1 : ∀ z, |χ z| ≤ 1) :
    HasWeakDirDeriv ed (fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z)
        (fun z => χ z • v z) Set.univ
      ∧ Continuous (fun z => χ z • v z)
      ∧ Continuous (fun z => ((fderiv ℝ χ z) ed) • v z)
      ∧ Integrable (fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z) volume := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have htop_ne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hχcont : Continuous χ := hχsm.continuous
  have hcompl : ∀ z : ℂ, z ∉ tsupport χ → χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport hz
  have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport χ := by
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact Or.inl (htsΩ hz)
    · exact Or.inr hz
  have hdχcont : Continuous fun z => (fderiv ℝ χ z) ed := by
    have h1 : Continuous (fderiv ℝ χ) :=
      (hχsm.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
        (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
    exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
  have hdχsupp : ∀ z : ℂ, z ∉ tsupport χ → (fderiv ℝ χ z) ed = 0 := by
    intro z hz
    have h1 : fderiv ℝ χ z = 0 := by
      by_contra hne
      exact hz ((support_fderiv_subset ℝ)
        (by simpa [Function.mem_support] using hne))
    rw [h1]
    rfl
  have hKχ : IsCompact (tsupport χ) := hχcs
  have hcont_of : ∀ H : ℂ → ℂ, (∀ z, z ∈ Ω → ContinuousAt H z) →
      (∀ z, z ∉ tsupport χ → H z = 0) → Continuous H := by
    intro H h1 h2
    rw [continuous_iff_continuousAt]
    intro z
    rcases hcover z with hzΩ | hzout
    · exact h1 z hzΩ
    · have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
      have hev : ∀ᶠ w in nhds z, H w = 0 := by
        filter_upwards [hopen.mem_nhds hzout] with w hw
        exact h2 w hw
      refine ContinuousAt.congr (f := fun _ : ℂ => (0 : ℂ)) continuousAt_const ?_
      filter_upwards [hev] with w hw
      exact hw.symm
  have hFccont : Continuous (fun z => χ z • v z) := by
    refine hcont_of _ ?_ ?_
    · intro z hzΩ
      exact (hχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
    · intro z hz
      change χ z • v z = 0
      rw [hcompl z hz]
      exact zero_smul ℝ _
  have hdχvcont : Continuous (fun z => ((fderiv ℝ χ z) ed) • v z) := by
    refine hcont_of _ ?_ ?_
    · intro z hzΩ
      exact (hdχcont.continuousAt).smul (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
    · intro z hz
      change ((fderiv ℝ χ z) ed) • v z = 0
      rw [hdχsupp z hz]
      exact zero_smul ℝ _
  have hgK : IntegrableOn g (tsupport χ) volume :=
    hgloc.integrableOn_compact_subset htsΩ hKχ
  have hbmul : ∀ (b : ℂ → ℝ) (Mb : ℝ), Continuous b → (∀ z, |b z| ≤ Mb) →
      (∀ z, z ∉ tsupport χ → b z = 0) →
      Integrable (fun z => b z • g z) volume := by
    intro b Mb hbc hbM hb0
    have hmeas : AEStronglyMeasurable (fun z => b z • g z)
        (volume.restrict (tsupport χ)) :=
      (hbc.aestronglyMeasurable).smul hgK.aestronglyMeasurable
    have hint : IntegrableOn (fun z => b z • g z) (tsupport χ) volume := by
      refine MeasureTheory.Integrable.mono' (hgK.norm.const_mul Mb) hmeas ?_
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbM z) (norm_nonneg _)
    have hsupp : Function.support (fun z => b z • g z) ⊆ tsupport χ := by
      intro z hz
      by_contra hzout
      rw [Function.mem_support] at hz
      rw [hb0 z hzout] at hz
      exact hz (zero_smul ℝ _)
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hint
  have hχg_int : Integrable (fun z => χ z • g z) volume :=
    hbmul χ 1 hχcont hχ1 hcompl
  have hdχv_cs : HasCompactSupport (fun z => ((fderiv ℝ χ z) ed) • v z) := by
    refine HasCompactSupport.intro hKχ ?_
    intro z hz
    change ((fderiv ℝ χ z) ed) • v z = 0
    rw [hdχsupp z hz]
    exact zero_smul ℝ _
  have hFg_int : Integrable (fun z => χ z • g z + ((fderiv ℝ χ z) ed) • v z) volume :=
    hχg_int.add (hdχvcont.integrable_of_hasCompactSupport hdχv_cs)
  refine ⟨?_, hFccont, hdχvcont, hFg_int⟩
  intro φ hφ hφc hφs
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Mφ, hMφ⟩ := hφcont.bounded_above_of_compact_support hφc
  have hφχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z * χ z) := hφ.mul hχsm
  have hφχcs : HasCompactSupport (fun z => φ z * χ z) := by
    refine HasCompactSupport.intro hφc ?_
    intro z hz
    change φ z * χ z = 0
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hφχsupp : tsupport (fun z => φ z * χ z) ⊆ Ω := by
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport χ)) htsΩ
    intro z hz
    rw [Function.mem_support] at hz
    have hχz : χ z ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    exact subset_tsupport χ hχz
  have hid := hg (fun z => φ z * χ z) hφχsm hφχcs hφχsupp
  have hfd : ∀ z, (fderiv ℝ (fun w => φ w * χ w) z) ed
      = φ z * ((fderiv ℝ χ z) ed) + χ z * ((fderiv ℝ φ z) ed) := by
    intro z
    have hφd : DifferentiableAt ℝ φ z := (hφ.differentiable htop_ne).differentiableAt
    have hχd : DifferentiableAt ℝ χ z := (hχsm.differentiable htop_ne).differentiableAt
    have h1 : (fun w => φ w * χ w) = φ * χ := rfl
    rw [h1, fderiv_mul hφd hχd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  have hdφcont : Continuous fun z => (fderiv ℝ φ z) ed := by
    have h1 : Continuous (fderiv ℝ φ) :=
      (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
        (le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]))).continuous
    exact (ContinuousLinearMap.apply ℝ ℝ ed).continuous.comp h1
  have hI1cont : Continuous fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    refine hcont_of _ ?_ ?_
    · intro z hzΩ
      exact ((hφcont.mul hdχcont).continuousAt).smul
        (hvcont.continuousAt (hΩ.mem_nhds hzΩ))
    · intro z hz
      change (φ z * ((fderiv ℝ χ z) ed)) • v z = 0
      rw [hdχsupp z hz, mul_zero]
      exact zero_smul ℝ _
  have hI1cs : HasCompactSupport fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    refine HasCompactSupport.intro hKχ ?_
    intro z hz
    change (φ z * ((fderiv ℝ χ z) ed)) • v z = 0
    rw [hdχsupp z hz, mul_zero]
    exact zero_smul ℝ _
  have hI1int : Integrable (fun z => (φ z * ((fderiv ℝ χ z) ed)) • v z) volume :=
    hI1cont.integrable_of_hasCompactSupport hI1cs
  have hI2cont : Continuous fun z => ((fderiv ℝ φ z) ed) • (χ z • v z) :=
    hdφcont.smul hFccont
  have hI2cs : HasCompactSupport fun z => ((fderiv ℝ φ z) ed) • (χ z • v z) := by
    refine HasCompactSupport.intro hφc ?_
    intro z hz
    have h1 : fderiv ℝ φ z = 0 := by
      by_contra hne
      exact hz ((support_fderiv_subset ℝ)
        (by simpa [Function.mem_support] using hne))
    have h2 : (fderiv ℝ φ z) ed = 0 := by
      rw [h1]
      rfl
    change ((fderiv ℝ φ z) ed) • (χ z • v z) = 0
    rw [h2]
    exact zero_smul ℝ _
  have hI2int : Integrable (fun z => ((fderiv ℝ φ z) ed) • (χ z • v z)) volume :=
    hI2cont.integrable_of_hasCompactSupport hI2cs
  have hφχg_int : Integrable (fun z => (φ z * χ z) • g z) volume := by
    refine hbmul (fun z => φ z * χ z) (Mφ * 1) (hφcont.mul hχcont) ?_ ?_
    · intro z
      rw [abs_mul]
      have h1 : |φ z| ≤ Mφ := by
        have := hMφ z
        rwa [Real.norm_eq_abs] at this
      have h3 : (0:ℝ) ≤ |φ z| := abs_nonneg _
      nlinarith [abs_nonneg (χ z), hχ1 z]
    · intro z hz
      change φ z * χ z = 0
      rw [hcompl z hz, mul_zero]
  have hsplit : ∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
      = (∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z)
        + ∫ z, ((fderiv ℝ φ z) ed) • (χ z • v z) := by
    rw [← MeasureTheory.integral_add hI1int hI2int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z
      = (φ z * ((fderiv ℝ χ z) ed)) • v z + ((fderiv ℝ φ z) ed) • (χ z • v z)
    rw [hfd z]
    module
  have hgoal2 : ∫ z, φ z • (χ z • g z + ((fderiv ℝ χ z) ed) • v z)
      = (∫ z, (φ z * χ z) • g z) + ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    rw [← MeasureTheory.integral_add hφχg_int hI1int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change φ z • (χ z • g z + ((fderiv ℝ χ z) ed) • v z)
      = (φ z * χ z) • g z + (φ z * ((fderiv ℝ χ z) ed)) • v z
    module
  have h1 : ∫ z, ((fderiv ℝ φ z) ed) • (χ z • v z)
      = (∫ z, ((fderiv ℝ (fun w => φ w * χ w) z) ed) • v z)
        - ∫ z, (φ z * ((fderiv ℝ χ z) ed)) • v z := by
    rw [hsplit]
    ring
  rw [h1, hid, hgoal2]
  ring

/-- Stage D2: a smooth compact-set cutoff by mollification of an indicator: it is `1` on
an open neighbourhood of the compact set `K`, supported inside the open set `U`. -/
theorem smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ z, |χ z| ≤ 1) ∧
      ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ ∀ z ∈ V, χ z = 1 := by
  classical
  obtain ⟨δ, hδ0, hδsub⟩ := hK.exists_cthickening_subset_open hU hKU
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  set A : Set ℂ := Metric.cthickening (δ/2) K with hAdef
  have hAm : MeasurableSet A := (Metric.isClosed_cthickening).measurableSet
  have hAc : IsCompact A := hK.cthickening
  set ind : ℂ → ℝ := A.indicator (fun _ => (1:ℝ)) with hinddef
  have hind_int : Integrable ind volume := by
    rw [hinddef, MeasureTheory.integrable_indicator_iff hAm]
    exact integrableOn_const (hAc.measure_lt_top.ne) (by simp)
  have hindloc : MeasureTheory.LocallyIntegrable ind volume := hind_int.locallyIntegrable
  have hind01 : ∀ z, 0 ≤ ind z ∧ ind z ≤ 1 := by
    intro z
    rw [hinddef]
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz]
      norm_num
    · rw [Set.indicator_of_notMem hz]
      norm_num
  set Φδ : ContDiffBump (0 : ℂ) :=
    { rIn := δ/8, rOut := δ/4,
      rIn_pos := by linarith,
      rIn_lt_rOut := by linarith } with hΦδdef
  set ρδ : ℂ → ℝ := Φδ.normed volume with hρδdef
  have hρsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρδ := Φδ.contDiff_normed
  have hρcs : HasCompactSupport ρδ := Φδ.hasCompactSupport_normed
  set χ : ℂ → ℝ := MeasureTheory.convolution ρδ ind L volume with hχdef
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    hρcs.contDiff_convolution_left L hρsm hindloc
  have hind_cs : HasCompactSupport ind := by
    refine HasCompactSupport.intro hAc ?_
    intro z hz
    rw [hinddef, Set.indicator_of_notMem hz]
  have hχcs : HasCompactSupport χ := hρcs.convolution L hind_cs
  have hce : ∀ z, ConvolutionExistsAt ρδ ind z L volume :=
    fun z => (hρcs.convolutionExists_left L (Φδ.continuous_normed) hindloc) z
  -- Support estimate.
  have hsupp : tsupport χ ⊆ U := by
    have h1 : Function.support χ ⊆ Metric.cthickening ((3/4)*δ) K := by
      intro z hz
      have h2 := MeasureTheory.support_convolution_subset (μ := volume)
        (f := ρδ) (g := ind) L hz
      obtain ⟨b, hb, a, ha, hab⟩ := h2
      have hbball : b ∈ Metric.ball (0 : ℂ) (δ/4) := by
        rw [← Φδ.support_normed_eq (μ := volume)]
        exact hb
      have haA : a ∈ A := by
        by_contra haA
        have h0 : ind a = 0 := by rw [hinddef, Set.indicator_of_notMem haA]
        exact ha h0
      rw [Metric.mem_cthickening_iff]
      have h3 : Metric.infEDist z K ≤ Metric.infEDist a K + edist z a :=
        Metric.infEDist_le_infEDist_add_edist
      have h4 : Metric.infEDist a K ≤ ENNReal.ofReal (δ/2) := by
        rw [hAdef, Metric.mem_cthickening_iff] at haA
        exact haA
      have h5 : edist z a ≤ ENNReal.ofReal (δ/4) := by
        have h6 : z - a = b := by rw [← hab]; ring
        rw [edist_eq_enorm_sub, h6, ← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Metric.mem_ball, dist_zero_right] at hbball
        linarith
      calc Metric.infEDist z K ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/4) :=
            le_trans h3 (add_le_add h4 h5)
        _ = ENNReal.ofReal (δ/2 + δ/4) := (ENNReal.ofReal_add (by linarith)
            (by linarith)).symm
        _ ≤ ENNReal.ofReal ((3/4)*δ) := by
            refine ENNReal.ofReal_le_ofReal ?_
            linarith
    refine subset_trans (closure_minimal h1 Metric.isClosed_cthickening) ?_
    refine subset_trans (Metric.cthickening_mono (by linarith) K) hδsub
  -- Value bounds.
  have hval : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := by
    intro z
    constructor
    · rw [hχdef]
      refine integral_nonneg fun t => ?_
      have h1 := (hind01 (z - t)).1
      have h2 : 0 ≤ ρδ t := Φδ.nonneg_normed t
      simpa [hLdef, smul_eq_mul] using mul_nonneg h2 h1
    · rw [hχdef]
      have h2 : ∫ t, ρδ t * ind (z - t) ≤ ∫ t, ρδ t * 1 := by
        refine integral_mono_of_nonneg ?_ ((Φδ.integrable_normed).mul_const 1) ?_
        · refine Filter.Eventually.of_forall fun t => ?_
          exact mul_nonneg (Φδ.nonneg_normed t) (hind01 (z - t)).1
        · refine Filter.Eventually.of_forall fun t => ?_
          exact mul_le_mul_of_nonneg_left (hind01 (z - t)).2 (Φδ.nonneg_normed t)
      have h3 : ∫ t, ρδ t * 1 = 1 := by
        rw [MeasureTheory.integral_mul_const, Φδ.integral_normed, one_mul]
      calc MeasureTheory.convolution ρδ ind L volume z
          = ∫ t, ρδ t * ind (z - t) := by rfl
        _ ≤ ∫ t, ρδ t * 1 := h2
        _ = 1 := h3
  refine ⟨χ, hχsm, hχcs, hsupp, ?_, ?_⟩
  · intro z
    rw [abs_le]
    exact ⟨by linarith [(hval z).1], (hval z).2⟩
  -- The neighbourhood where `χ = 1`.
  refine ⟨Metric.thickening (δ/8) K, Metric.isOpen_thickening,
    Metric.self_subset_thickening (by linarith) K, ?_⟩
  intro z hz
  have hzA : ∀ t ∈ Metric.ball (0 : ℂ) (δ/4), z - t ∈ A := by
    intro t ht
    rw [hAdef, Metric.mem_cthickening_iff]
    have h3 : Metric.infEDist (z - t) K ≤ Metric.infEDist z K + edist (z - t) z :=
      Metric.infEDist_le_infEDist_add_edist
    have h4 : Metric.infEDist z K < ENNReal.ofReal (δ/8) :=
      Metric.mem_thickening_iff_infEDist_lt.mp hz
    have h5 : edist (z - t) z ≤ ENNReal.ofReal (δ/4) := by
      have h6 : (z - t) - z = -t := by ring
      rw [edist_eq_enorm_sub, h6, enorm_neg, ← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Metric.mem_ball, dist_zero_right] at ht
      linarith
    calc Metric.infEDist (z - t) K
        ≤ ENNReal.ofReal (δ/8) + ENNReal.ofReal (δ/4) :=
          le_trans h3 (add_le_add h4.le h5)
      _ = ENNReal.ofReal (δ/8 + δ/4) := (ENNReal.ofReal_add (by linarith)
          (by linarith)).symm
      _ ≤ ENNReal.ofReal (δ/2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          linarith
  have hptwise : ∀ t, ρδ t * ind (z - t) = ρδ t := by
    intro t
    by_cases ht : t ∈ Function.support ρδ
    · have htball : t ∈ Metric.ball (0 : ℂ) (δ/4) := by
        rw [← Φδ.support_normed_eq (μ := volume)]
        exact ht
      have h1 : ind (z - t) = 1 := by
        rw [hinddef, Set.indicator_of_mem (hzA t htball)]
      rw [h1, mul_one]
    · have h0 : ρδ t = 0 := Function.notMem_support.mp ht
      rw [h0, zero_mul]
  calc χ z = ∫ t, ρδ t * ind (z - t) := by rfl
    _ = ∫ t, ρδ t := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        exact hptwise t
    _ = 1 := Φδ.integral_normed

/-- Stage D3: pointwise Wirtinger cancellation. If `w` and `v` solve the same Beltrami
ratio at `z`, with invertible sense-preserving differential of `w`, then the pairing of
the differential of `v` against the inverse differential of `w` has vanishing
`∂̄`-combination. -/
theorem wirtinger_cancel
    {w v : ℂ → ℂ} {z : ℂ} {μz : ℂ}
    (hwdet : 0 < (fderiv ℝ w z).det)
    (hwbelt : dzbar w z = μz * dz w z)
    (hvbelt : dzbar v z = μz * dz v z)
    (A : ℂ →L[ℝ] ℂ) (hA : ∀ u : ℂ, (fderiv ℝ w z) (A u) = u) :
    ((A 1).re • (fderiv ℝ v z) 1 + (A 1).im • (fderiv ℝ v z) Complex.I)
      + Complex.I * ((A Complex.I).re • (fderiv ℝ v z) 1
        + (A Complex.I).im • (fderiv ℝ v z) Complex.I) = 0 := by
  classical
  -- The Wirtinger representation of a real differential.
  have hrepr : ∀ (F : ℂ → ℂ) (ζ u : ℂ),
      (fderiv ℝ F ζ) u = dz F ζ * u + dzbar F ζ * (starRingEnd ℂ) u := by
    intro F ζ u
    set T : ℂ →L[ℝ] ℂ := fderiv ℝ F ζ with hT
    have hTv : T u = (u.re : ℂ) * T 1 + (u.im : ℂ) * T Complex.I := by
      conv_lhs => rw [show u = u.re • (1 : ℂ) + u.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcv : (starRingEnd ℂ) u = (u.re : ℂ) - (u.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im u]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hv : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
    simp only [dz, dzbar, ← hT]
    rw [hTv, hcv]
    linear_combination (-(1 / 2 : ℂ) * (T 1 - Complex.I * T Complex.I)) * hv +
      ((u.im : ℂ) * T Complex.I) * Complex.I_sq
  -- The linear-map decomposition.
  have hdec : ∀ (T : ℂ →L[ℝ] ℂ) (u : ℂ), u.re • T 1 + u.im • T Complex.I = T u := by
    intro T u
    conv_rhs => rw [show u = u.re • (1 : ℂ) + u.im • Complex.I by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
    rw [map_add, map_smul, map_smul]
  rw [hdec (fderiv ℝ v z) (A 1), hdec (fderiv ℝ v z) (A Complex.I)]
  -- `∂w ≠ 0` from the positive Jacobian.
  have hpBne : dz w z ≠ 0 := by
    intro h0
    have hdd := det_fderiv_eq_wirtinger w z
    rw [h0, norm_zero] at hdd
    nlinarith [hwdet, sq_nonneg ‖dzbar w z‖]
  -- The defining equations of the inverse differential.
  have h1 : dz w z * A 1 + dzbar w z * (starRingEnd ℂ) (A 1) = 1 := by
    rw [← hrepr w z (A 1)]
    exact hA 1
  have hI : dz w z * A Complex.I + dzbar w z * (starRingEnd ℂ) (A Complex.I)
      = Complex.I := by
    rw [← hrepr w z (A Complex.I)]
    exact hA Complex.I
  -- Beltrami cancellation.
  have hbr : A 1 + μz * (starRingEnd ℂ) (A 1)
      + Complex.I * (A Complex.I + μz * (starRingEnd ℂ) (A Complex.I)) = 0 := by
    have hkey : dz w z * (A 1 + μz * (starRingEnd ℂ) (A 1)
        + Complex.I * (A Complex.I + μz * (starRingEnd ℂ) (A Complex.I))) = 0 := by
      linear_combination h1 + Complex.I * hI + Complex.I_sq
        - ((starRingEnd ℂ) (A 1)
            + Complex.I * (starRingEnd ℂ) (A Complex.I)) * hwbelt
    exact (mul_eq_zero.mp hkey).resolve_left hpBne
  -- Conclude by the representation of the differential of `v`.
  rw [hrepr v z (A 1), hrepr v z (A Complex.I)]
  linear_combination (dz v z) * hbr +
    ((starRingEnd ℂ) (A 1) + Complex.I * (starRingEnd ℂ) (A Complex.I)) * hvbelt

-- Assembling the composite through the abstract bricks over a per-point ball is a heavy
-- elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The transition-map analysis composes the chain rule with the Weyl lemma input;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage D ([CHAIN]+[WEYL]): the transition map `v ∘ u.w⁻¹` of two solutions of the same
Beltrami equation on the upper half plane is holomorphic there, provided the normalized
plane solution preserves the upper half plane. -/
theorem composite_holomorphic
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (u : TeichRep Γ₀)
    {v vinv : ℂ → ℂ} {κ : ℝ} (hv : IsQCUpper v vinv κ)
    (hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar v z = u.b.μ z * dz v z)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 < (u.w z).im)
    {uinv : ℂ → ℂ} (huinvc : Continuous uinv)
    (_hui1 : ∀ z, uinv (u.w z) = z) (hui2 : ∀ z, u.w (uinv z) = z) :
    DifferentiableOn ℂ (fun w => v (uinv w)) {z : ℂ | 0 < z.im} := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  set Ω : Set ℂ := {z : ℂ | 0 < z.im} with hΩdef
  have hΩ : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_im
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  -- The plane solution and its inverse.
  have hwqc : IsQCAnalytic u.w u.b := u.w_isQCAnalytic
  have hwcont : Continuous u.w := hwqc.1.1.continuous
  obtain ⟨p, wgx, wgy, hp2, hwgrad, hgxp, hgyp⟩ :=
    hwqc.exists_weakGradient_memLpLocOn_gt_two
  have hLusin : ∀ S : Set ℂ, volume S = 0 → volume (u.w '' S) = 0 := fun S hS =>
    lusinN_image_null_of_weakGradient hp2 hwcont hwgrad hgxp hgyp hS
  have hK1 : 1 ≤ u.b.K := u.b.one_le_K
  have hbnd : u.b.normInf ≤ (u.b.K - 1) / (u.b.K + 1) := by
    have hm0 := u.b.normInf_nonneg
    have hm1 := u.b.normInf_lt_one
    have hden : (0 : ℝ) < 1 - u.b.normInf := by linarith
    have hKval : u.b.K = (1 + u.b.normInf) / (1 - u.b.normInf) := rfl
    have hKeq : u.b.K * (1 - u.b.normInf) = 1 + u.b.normInf := by
      rw [hKval, div_mul_cancel₀ _ (ne_of_gt hden)]
    have hKpos : (0 : ℝ) < u.b.K + 1 := by linarith
    rw [le_div_iff₀ hKpos]
    nlinarith [hKeq]
  have hwgeom : IsQCGeometric u.w u.b.K := isQCGeometric_of_isQCAnalytic hK1 hbnd hwqc
  have hinvgeom := isQCGeometric_inv_of_isQCGeometric hwgeom
  have hbridge : ⇑(hwgeom.2.1.isHomeomorph.homeomorph u.w).symm = uinv := by
    funext w
    have hinj : Function.Injective u.w := hwqc.injective
    have hL : u.w ((hwgeom.2.1.isHomeomorph.homeomorph u.w).symm w) = w := by
      rw [← IsHomeomorph.homeomorph_apply u.w hwgeom.2.1.isHomeomorph
            ((hwgeom.2.1.isHomeomorph.homeomorph u.w).symm w)]
      exact (hwgeom.2.1.isHomeomorph.homeomorph u.w).apply_symm_apply w
    exact hinj (hL.trans (hui2 w).symm)
  have huinv_geom : IsQCGeometric uinv u.b.K := hbridge ▸ hinvgeom
  obtain ⟨bq, hbqle, hqinv⟩ := isQCAnalytic_of_isQCGeometric hK1 huinv_geom
  -- The inverse preserves the upper half plane.
  have huinvΩ : ∀ w' : ℂ, w' ∈ Ω → uinv w' ∈ Ω := by
    intro w' hw'
    have hw'pos : 0 < w'.im := hw'
    by_contra hle
    have hle' : (uinv w').im ≤ 0 := not_lt.mp hle
    rcases eq_or_lt_of_le hle' with heq | hlt
    · have hzr : ((((uinv w').re : ℝ)) : ℂ) = uinv w' :=
        Complex.ext (by simp) (by simp [heq.symm])
      have h1 : (u.w (uinv w')).im = 0 := by
        rw [← hzr]
        exact u.w_real (uinv w').re
      rw [hui2 w'] at h1
      rw [h1] at hw'pos
      exact lt_irrefl 0 hw'pos
    · have h1 : 0 < (starRingEnd ℂ (uinv w')).im := by
        rw [Complex.conj_im]
        linarith
      have h2 := hpos _ h1
      rw [u.w_conj (uinv w'), hui2 w', Complex.conj_im] at h2
      linarith
  -- The upper-half-plane weak-gradient data, with measurable representatives.
  obtain ⟨hvL2, gx, gy, hvgrad, hgx2, hgy2⟩ := hv.sobolev
  have hlocOn : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Ω →
      MeasureTheory.LocallyIntegrableOn h Ω volume := by
    intro h hh
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk1 hk2
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk2.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp ((hh k hk1 hk2).mono_exponent (by norm_num))
  have hgxli : MeasureTheory.LocallyIntegrableOn gx Ω volume := hlocOn hgx2
  have hgyli : MeasureTheory.LocallyIntegrableOn gy Ω volume := hlocOn hgy2
  -- Measurable representatives of the witnesses.
  have hrep : ∀ (g : ℂ → ℂ), MeasureTheory.LocallyIntegrableOn g Ω volume →
      ∃ g' : ℂ → ℂ, Measurable g' ∧ volume {z | z ∈ Ω ∧ g z ≠ g' z} = 0 := by
    intro g hgli
    have hAESM := hgli.aestronglyMeasurable
    refine ⟨hAESM.mk g, hAESM.stronglyMeasurable_mk.measurable, ?_⟩
    have h1 : ∀ᵐ z ∂(volume.restrict Ω), g z = hAESM.mk g z := hAESM.ae_eq_mk
    rw [MeasureTheory.ae_iff] at h1
    rw [Measure.restrict_apply' hΩm] at h1
    refine measure_mono_null ?_ h1
    intro z hz
    exact ⟨hz.2, hz.1⟩
  obtain ⟨gx', hgx'm, hgx'eq⟩ := hrep gx hgxli
  obtain ⟨gy', hgy'm, hgy'eq⟩ := hrep gy hgyli
  -- Transfer of the weak-derivative identities to the representatives.
  have htransfer : ∀ (g g' : ℂ → ℂ) (ed : ℂ), HasWeakDirDeriv ed g v Ω →
      volume {z | z ∈ Ω ∧ g z ≠ g' z} = 0 → HasWeakDirDeriv ed g' v Ω := by
    intro g g' ed hg hnull φ hφ hφc hφs
    rw [hg φ hφ hφc hφs]
    congr 1
    refine integral_congr_ae ?_
    have h1 : {z : ℂ | ¬ φ z • g z = φ z • g' z} ⊆ {z | z ∈ Ω ∧ g z ≠ g' z} := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      by_cases hzs : z ∈ tsupport φ
      · refine ⟨hφs hzs, ?_⟩
        intro heq
        exact hz (by rw [heq])
      · exfalso
        have h0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hzs
        have e1 : φ z • g z = 0 := by rw [h0]; exact zero_smul ℝ _
        have e2 : φ z • g' z = 0 := by rw [h0]; exact zero_smul ℝ _
        exact hz (by rw [e1, e2])
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    exact measure_mono_null h1 hnull
  have hvgradx' : HasWeakDirDeriv 1 gx' v Ω := htransfer gx gx' 1 hvgrad.1 hgx'eq
  have hvgrady' : HasWeakDirDeriv Complex.I gy' v Ω := htransfer gy gy' Complex.I
    hvgrad.2 hgy'eq
  have hgx'li : MeasureTheory.LocallyIntegrableOn gx' Ω volume := by
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk1 hk2
    have h1 : IntegrableOn gx k volume := by
      have := hgxli
      rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed] at this
      exact this k hk1 hk2
    refine h1.congr ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    rw [Measure.restrict_apply' hk2.measurableSet]
    refine measure_mono_null ?_ hgx'eq
    intro z hz
    exact ⟨hk1 hz.2, hz.1⟩
  have hgy'li : MeasureTheory.LocallyIntegrableOn gy' Ω volume := by
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk1 hk2
    have h1 : IntegrableOn gy k volume := by
      have := hgyli
      rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed] at this
      exact this k hk1 hk2
    refine h1.congr ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    rw [Measure.restrict_apply' hk2.measurableSet]
    refine measure_mono_null ?_ hgy'eq
    intro z hz
    exact ⟨hk1 hz.2, hz.1⟩
  have hgx'2 : MemLpLocOn gx' 2 Ω := by
    intro k hk1 hk2
    refine ⟨((hgx'm).aestronglyMeasurable), ?_⟩
    have h1 := (hgx2 k hk1 hk2).2
    have h2 : eLpNorm gx' 2 (volume.restrict k) = eLpNorm gx 2 (volume.restrict k) := by
      refine eLpNorm_congr_ae ?_
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      rw [Measure.restrict_apply' hk2.measurableSet]
      refine measure_mono_null ?_ hgx'eq
      intro z hz
      exact ⟨hk1 hz.2, Ne.symm hz.1⟩
    rw [h2]
    exact h1
  have hgy'2 : MemLpLocOn gy' 2 Ω := by
    intro k hk1 hk2
    refine ⟨((hgy'm).aestronglyMeasurable), ?_⟩
    have h1 := (hgy2 k hk1 hk2).2
    have h2 : eLpNorm gy' 2 (volume.restrict k) = eLpNorm gy 2 (volume.restrict k) := by
      refine eLpNorm_congr_ae ?_
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      rw [Measure.restrict_apply' hk2.measurableSet]
      refine measure_mono_null ?_ hgy'eq
      intro z hz
      exact ⟨hk1 hz.2, Ne.symm hz.1⟩
    rw [h2]
    exact h1
  -- Almost-everywhere differentiability of `v` on `Ω`.
  have hvdiff : ∀ᵐ z ∂(volume.restrict Ω), DifferentiableAt ℝ v z := by
    filter_upwards [hv.jac] with z hz
    by_contra h
    have h0 : fderiv ℝ v z = 0 := fderiv_zero_of_not_differentiableAt h
    rw [h0] at hz
    have hdet0 : (0 : ℂ →L[ℝ] ℂ).det = 0 := by
      simp [ContinuousLinearMap.det]
    rw [hdet0] at hz
    exact lt_irrefl 0 hz
  -- The pointwise partials agree with the representatives almost everywhere on `Ω`.
  have hbrx := fderiv_ae_eq_weakDirDeriv_on (Or.inl rfl) hΩ hvgradx' hgx'li
    hv.cont hvdiff
  have hbry := fderiv_ae_eq_weakDirDeriv_on (Or.inr rfl) hΩ hvgrady' hgy'li
    hv.cont hvdiff
  -- Weak-gradient data for the inverse plane map, with measurable representatives.
  obtain ⟨hqL2, qx, qy, hqgrad, hqx2, hqy2⟩ := hqinv.2.1
  have hlocU : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ →
      MeasureTheory.LocallyIntegrable h volume := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hh k (Set.subset_univ k) hk).mono_exponent (by norm_num))
  have hqxli : MeasureTheory.LocallyIntegrable qx volume := hlocU hqx2
  have hqyli : MeasureTheory.LocallyIntegrable qy volume := hlocU hqy2
  have hrepU : ∀ (g : ℂ → ℂ), MeasureTheory.LocallyIntegrable g volume →
      ∃ g' : ℂ → ℂ, Measurable g' ∧ ∀ᵐ z : ℂ, g z = g' z := by
    intro g hgli
    have hAESM := hgli.aestronglyMeasurable
    exact ⟨hAESM.mk g, hAESM.stronglyMeasurable_mk.measurable, hAESM.ae_eq_mk⟩
  obtain ⟨qx', hqx'm, hqx'eq⟩ := hrepU qx hqxli
  obtain ⟨qy', hqy'm, hqy'eq⟩ := hrepU qy hqyli
  have htransferU : ∀ (g g' : ℂ → ℂ) (ed : ℂ), HasWeakDirDeriv ed g uinv Set.univ →
      (∀ᵐ z : ℂ, g z = g' z) → HasWeakDirDeriv ed g' uinv Set.univ := by
    intro g g' ed hg hae φ hφ hφc hφs
    rw [hg φ hφ hφc hφs]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  have hqgradx' : HasWeakDirDeriv 1 qx' uinv Set.univ :=
    htransferU qx qx' 1 hqgrad.1 hqx'eq
  have hqgrady' : HasWeakDirDeriv Complex.I qy' uinv Set.univ :=
    htransferU qy qy' Complex.I hqgrad.2 hqy'eq
  have hqx'li : MeasureTheory.LocallyIntegrable qx' volume := hqxli.congr hqx'eq
  have hqy'li : MeasureTheory.LocallyIntegrable qy' volume := hqyli.congr hqy'eq
  have hqx'2 : MemLpLocOn qx' 2 Set.univ := by
    intro k hk1 hk2
    refine ⟨hqx'm.aestronglyMeasurable, ?_⟩
    have h2 : eLpNorm qx' 2 (volume.restrict k) = eLpNorm qx 2 (volume.restrict k) :=
      eLpNorm_congr_ae (ae_restrict_of_ae (by filter_upwards [hqx'eq] with z hz
        using hz.symm))
    rw [h2]
    exact (hqx2 k hk1 hk2).2
  have hqy'2 : MemLpLocOn qy' 2 Set.univ := by
    intro k hk1 hk2
    refine ⟨hqy'm.aestronglyMeasurable, ?_⟩
    have h2 : eLpNorm qy' 2 (volume.restrict k) = eLpNorm qy 2 (volume.restrict k) :=
      eLpNorm_congr_ae (ae_restrict_of_ae (by filter_upwards [hqy'eq] with z hz
        using hz.symm))
    rw [h2]
    exact (hqy2 k hk1 hk2).2
  have hqae_x : ∀ᵐ w : ℂ, (fderiv ℝ uinv w) 1 = qx' w :=
    fderiv_ae_eq_weakDirDeriv hqgradx'
      (by rwa [MeasureTheory.locallyIntegrableOn_univ])
      hqinv.ae_differentiableAt (Or.inl rfl) huinvc.locallyIntegrable
  have hqae_y : ∀ᵐ w : ℂ, (fderiv ℝ uinv w) Complex.I = qy' w :=
    fderiv_ae_eq_weakDirDeriv hqgrady'
      (by rwa [MeasureTheory.locallyIntegrableOn_univ])
      hqinv.ae_differentiableAt (Or.inr rfl) huinvc.locallyIntegrable
  -- The good-point package on the `z`-side.
  have hgood : ∀ᵐ z ∂(volume.restrict Ω),
      (0 < (fderiv ℝ u.w z).det ∧ dzbar u.w z = u.b.μ z * dz u.w z) ∧
      (dzbar v z = u.b.μ z * dz v z) ∧
      ((fderiv ℝ v z) 1 = gx' z ∧ (fderiv ℝ v z) Complex.I = gy' z) := by
    have h1 : ∀ᵐ z : ℂ, 0 < (fderiv ℝ u.w z).det := hwqc.1.2
    have h2 : ∀ᵐ z : ℂ, dzbar u.w z = u.b.μ z * dz u.w z := hwqc.2.2
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae h2, hcoeff, hbrx, hbry]
      with z hz1 hz2 hz3 hz4 hz5
    exact ⟨⟨hz1, hz2⟩, hz3, hz4, hz5⟩
  -- Transfer of the good-point package to the `w`-side through the solution.
  have hwside : ∀ᵐ w' ∂(volume.restrict Ω),
      (0 < (fderiv ℝ u.w (uinv w')).det ∧
        dzbar u.w (uinv w') = u.b.μ (uinv w') * dz u.w (uinv w')) ∧
      (dzbar v (uinv w') = u.b.μ (uinv w') * dz v (uinv w')) ∧
      ((fderiv ℝ v (uinv w')) 1 = gx' (uinv w') ∧
        (fderiv ℝ v (uinv w')) Complex.I = gy' (uinv w')) := by
    have h1 := hgood
    rw [MeasureTheory.ae_iff, Measure.restrict_apply' hΩm] at h1 ⊢
    refine measure_mono_null ?_ (hLusin _ h1)
    intro w' hw'
    exact ⟨uinv w', ⟨hw'.1, huinvΩ w' hw'.2⟩, hui2 w'⟩
  -- The per-point ball argument.
  intro w₀ hw₀
  obtain ⟨ε0, hε00, hεsub⟩ := Metric.isOpen_iff.mp hΩ w₀ hw₀
  set s3 : ℝ := ε0/2 with hs3def
  have hs30 : 0 < s3 := by rw [hs3def]; linarith
  have hcbsub : Metric.closedBall w₀ s3 ⊆ Ω := by
    refine subset_trans ?_ hεsub
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    rw [hs3def] at hz
    linarith
  set K2 : Set ℂ := uinv '' (Metric.closedBall w₀ s3) with hK2def
  have hK2c : IsCompact K2 := (isCompact_closedBall _ _).image huinvc
  have hK2sub : K2 ⊆ Ω := by
    rintro z ⟨w', hw', rfl⟩
    exact huinvΩ w' (hcbsub hw')
  obtain ⟨χ2, hχ2sm, hχ2cs, hχ2ts, hχ2le, V2, hV2open, hKV2, hV2one⟩ :=
    smooth_cutoff hK2c hΩ hK2sub
  -- The cutoff package in the two directions.
  obtain ⟨hFwx, hFcont, hdxvcont, hFgx_int⟩ :=
    cutoff_hasWeakDirDeriv hΩ hvgradx' hgx'li hv.cont hχ2sm hχ2cs hχ2ts hχ2le
  obtain ⟨hFwy, -, hdyvcont, hFgy_int⟩ :=
    cutoff_hasWeakDirDeriv hΩ hvgrady' hgy'li hv.cont hχ2sm hχ2cs hχ2ts hχ2le
  have hχ2compl : ∀ z : ℂ, z ∉ tsupport χ2 → χ2 z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport hz
  have hdχ2supp : ∀ (ed : ℂ) (z : ℂ), z ∉ tsupport χ2 → (fderiv ℝ χ2 z) ed = 0 := by
    intro ed z hz
    have h1 : fderiv ℝ χ2 z = 0 := by
      by_contra hne
      exact hz ((support_fderiv_subset ℝ)
        (by simpa [Function.mem_support] using hne))
    rw [h1]
    rfl
  have hFcs : HasCompactSupport (fun z => χ2 z • v z) := by
    refine HasCompactSupport.intro hχ2cs ?_
    intro z hz
    change χ2 z • v z = 0
    rw [hχ2compl z hz]
    exact zero_smul ℝ _
  -- Measurability and square-integrability of the localized weak gradient.
  have hsmul_meas : ∀ {g : ℂ → ℂ}, Measurable g →
      Measurable (fun z => χ2 z • g z) := by
    intro g hgm
    have h1 : (fun z => χ2 z • g z) = fun z => ((χ2 z : ℝ) : ℂ) * g z := by
      funext z
      rw [Complex.real_smul]
    rw [h1]
    exact (Complex.measurable_ofReal.comp hχ2sm.continuous.measurable).mul hgm
  have hFxm : Measurable (fun z => χ2 z • gx' z + ((fderiv ℝ χ2 z) 1) • v z) :=
    (hsmul_meas hgx'm).add hdxvcont.measurable
  have hFym : Measurable
      (fun z => χ2 z • gy' z + ((fderiv ℝ χ2 z) Complex.I) • v z) :=
    (hsmul_meas hgy'm).add hdyvcont.measurable
  have hmemLp_part : ∀ {g : ℂ → ℂ}, Measurable g → MemLpLocOn g 2 Ω →
      MemLp (fun z => χ2 z • g z) 2 volume := by
    intro g hgm hg2
    refine ⟨(hsmul_meas hgm).aestronglyMeasurable, ?_⟩
    have h1 : eLpNorm (fun z => χ2 z • g z) 2 volume
        ≤ eLpNorm ((tsupport χ2).indicator g) 2 volume := by
      refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ tsupport χ2
      · rw [Set.indicator_of_mem hz, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχ2le z)
      · have h0 : χ2 z • g z = 0 := by
          rw [hχ2compl z hz]
          exact zero_smul ℝ _
        rw [h0, Set.indicator_of_notMem hz]
    refine lt_of_le_of_lt h1 ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hχ2cs.isClosed.measurableSet)]
    exact (hg2 (tsupport χ2) hχ2ts hχ2cs).2
  have hdχv_cs : ∀ ed : ℂ, HasCompactSupport
      (fun z => ((fderiv ℝ χ2 z) ed) • v z) := by
    intro ed
    refine HasCompactSupport.intro hχ2cs ?_
    intro z hz
    change ((fderiv ℝ χ2 z) ed) • v z = 0
    rw [hdχ2supp ed z hz]
    exact zero_smul ℝ _
  have hFx2 : MemLp (fun z => χ2 z • gx' z + ((fderiv ℝ χ2 z) 1) • v z) 2 volume :=
    (hmemLp_part hgx'm hgx'2).add
      (hdxvcont.memLp_of_hasCompactSupport (hdχv_cs 1))
  have hFy2 : MemLp
      (fun z => χ2 z • gy' z + ((fderiv ℝ χ2 z) Complex.I) • v z) 2 volume :=
    (hmemLp_part hgy'm hgy'2).add
      (hdyvcont.memLp_of_hasCompactSupport (hdχv_cs Complex.I))
  -- The composite weak derivatives on the plane.
  have hcompX := hasWeakDirDeriv_comp_qc hqinv (Or.inl rfl) hqgradx' hqx'm hqx'2
    hFcont hFcs ⟨hFwx, hFwy⟩ hFxm hFym hFx2 hFy2
  have hcompY := hasWeakDirDeriv_comp_qc hqinv (Or.inr rfl) hqgrady' hqy'm hqy'2
    hFcont hFcs ⟨hFwx, hFwy⟩ hFxm hFym hFx2 hFy2
  -- Names for the pairing functions.
  set FxD : ℂ → ℂ := fun z => χ2 z • gx' z + ((fderiv ℝ χ2 z) 1) • v z with hFxDdef
  set FyD : ℂ → ℂ := fun z => χ2 z • gy' z + ((fderiv ℝ χ2 z) Complex.I) • v z
    with hFyDdef
  set GxD : ℂ → ℂ := fun w => (qx' w).re • FxD (uinv w) + (qx' w).im • FyD (uinv w)
    with hGxDdef
  set GyD : ℂ → ℂ := fun w => (qy' w).re • FxD (uinv w) + (qy' w).im • FyD (uinv w)
    with hGyDdef
  set B3 : Set ℂ := Metric.ball w₀ s3 with hB3def
  have hB3sub : B3 ⊆ Ω := fun w' hw' => hcbsub (Metric.ball_subset_closedBall hw')
  have hψeqB : ∀ w' ∈ B3, χ2 (uinv w') • v (uinv w') = v (uinv w') := by
    intro w' hw'
    have h1 : uinv w' ∈ V2 :=
      hKV2 ⟨w', Metric.ball_subset_closedBall hw', rfl⟩
    rw [hV2one _ h1]
    exact one_smul ℝ _
  -- Restriction of the composite weak derivatives to the ball, transferred to `v∘uinv`.
  have hrestr : ∀ (ed : ℂ) (G : ℂ → ℂ),
      HasWeakDirDeriv ed G (fun w => χ2 (uinv w) • v (uinv w)) Set.univ →
      HasWeakDirDeriv ed G (fun w => v (uinv w)) B3 := by
    intro ed G hG φ hφ hφc hφs
    rw [← hG φ hφ hφc (by intro z _; trivial)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · change ((fderiv ℝ φ z) ed) • v (uinv z)
        = ((fderiv ℝ φ z) ed) • (χ2 (uinv z) • v (uinv z))
      rw [hψeqB z (hφs hz)]
    · have h1 : fderiv ℝ φ z = 0 := by
        by_contra hne
        exact hz ((support_fderiv_subset ℝ)
          (by simpa [Function.mem_support] using hne))
      have h2 : (fderiv ℝ φ z) ed = 0 := by
        rw [h1]
        rfl
      change ((fderiv ℝ φ z) ed) • v (uinv z)
        = ((fderiv ℝ φ z) ed) • (χ2 (uinv z) • v (uinv z))
      rw [h2]
      have e1 : (0:ℝ) • v (uinv z) = 0 := zero_smul ℝ _
      have e2 : (0:ℝ) • (χ2 (uinv z) • v (uinv z)) = 0 := zero_smul ℝ _
      rw [e1, e2]
  have hwx : HasWeakDirDeriv 1 GxD (fun w => v (uinv w)) B3 := hrestr 1 GxD hcompX
  have hwy : HasWeakDirDeriv Complex.I GyD (fun w => v (uinv w)) B3 :=
    hrestr Complex.I GyD hcompY
  -- Local integrability of the pairing functions on the ball.
  set Φ3 : ContDiffBump w₀ :=
    { rIn := s3, rOut := 2*s3,
      rIn_pos := hs30,
      rIn_lt_rOut := by linarith } with hΦ3def
  set S3 : Set ℂ := Metric.closedBall w₀ (2*s3) with hS3def
  have hS3m : MeasurableSet S3 := (Metric.isClosed_closedBall).measurableSet
  have hφ3zero : ∀ z, z ∉ S3 → (Φ3 : ℂ → ℝ) z = 0 := by
    intro z hz
    have h1 : z ∉ Function.support (Φ3 : ℂ → ℝ) := by
      rw [Φ3.support_eq]
      intro h2
      exact hz (Metric.ball_subset_closedBall h2)
    exact Function.notMem_support.mp h1
  have hφ3bd : ∀ z, ‖(Φ3 : ℂ → ℝ) z‖ ≤ 1 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (Φ3.nonneg)]
    exact Φ3.le_one
  have hel2 : ∀ h : ℂ → ℂ, ((∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ)) ^ (1/2 : ℝ)) = eLpNorm h 2 volume := by
    intro h
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
    rw [h2]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.rpow_natCast (‖h z‖ₑ) 2]
    norm_num
  have hGmeas : ∀ (qe' : ℂ → ℂ), Measurable qe' → Measurable
      (fun w => (qe' w).re • FxD (uinv w) + (qe' w).im • FyD (uinv w)) := by
    intro qe' hqe'm
    have h1 : (fun w => (qe' w).re • FxD (uinv w) + (qe' w).im • FyD (uinv w))
        = fun w => (((qe' w).re : ℝ) : ℂ) * FxD (uinv w)
          + (((qe' w).im : ℝ) : ℂ) * FyD (uinv w) := by
      funext w
      rw [Complex.real_smul, Complex.real_smul]
    rw [h1]
    exact ((Complex.measurable_ofReal.comp (Complex.measurable_re.comp hqe'm)).mul
        (hFxm.comp huinvc.measurable)).add
      ((Complex.measurable_ofReal.comp (Complex.measurable_im.comp hqe'm)).mul
        (hFym.comp huinvc.measurable))
  have hGint : ∀ (qe' : ℂ → ℂ), Measurable qe' →
      (∀ᵐ w : ℂ, (fderiv ℝ uinv w) 1 = qe' w) ∨
        (∀ᵐ w : ℂ, (fderiv ℝ uinv w) Complex.I = qe' w) →
      MeasureTheory.LocallyIntegrableOn
        (fun w => (qe' w).re • FxD (uinv w) + (qe' w).im • FyD (uinv w)) B3 volume := by
    intro qe' hqe'm hae'
    rw [MeasureTheory.locallyIntegrableOn_iff Metric.isOpen_ball.isLocallyClosed]
    intro k hk1 hk2
    refine IntegrableOn.mono_set ?_
      (subset_trans hk1 Metric.ball_subset_closedBall)
    refine ⟨(hGmeas qe' hqe'm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hone : ∀ w' ∈ Metric.closedBall w₀ s3, (Φ3 : ℂ → ℝ) w' = 1 := fun w' hw' =>
      Φ3.one_of_mem_closedBall hw'
    have hcov : ∫⁻ w' in Metric.closedBall w₀ s3,
        ‖(qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w')‖ₑ
        ≤ ∫⁻ w', ‖(Φ3 : ℂ → ℝ) w' • ((qe' w').re • FxD (uinv w')
          + (qe' w').im • FyD (uinv w'))‖ₑ := by
      have h1 : ∫⁻ w' in Metric.closedBall w₀ s3,
          ‖(qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w')‖ₑ
          = ∫⁻ w' in Metric.closedBall w₀ s3,
            ‖(Φ3 : ℂ → ℝ) w' • ((qe' w').re • FxD (uinv w')
              + (qe' w').im • FyD (uinv w'))‖ₑ := by
        refine setLIntegral_congr_fun (Metric.isClosed_closedBall).measurableSet ?_
        intro w' hw'
        change ‖(qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w')‖ₑ
          = ‖(Φ3 : ℂ → ℝ) w' • ((qe' w').re • FxD (uinv w')
            + (qe' w').im • FyD (uinv w'))‖ₑ
        have e1 : (1:ℝ) • ((qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w'))
            = (qe' w').re • FxD (uinv w') + (qe' w').im • FyD (uinv w') := one_smul ℝ _
        rw [hone w' hw', e1]
      rw [h1]
      exact setLIntegral_le_lintegral _ _
    have hbound : ∀ (hen' : ‖(1:ℂ)‖ = 1 ∨ ‖(Complex.I)‖ = 1), True := fun _ => trivial
    rcases hae' with hae1 | haeI
    · have h2 := cov_pairing_bound hqinv (by norm_num : ‖(1:ℂ)‖ = 1) hqe'm hae1
        hS3m hφ3zero hφ3bd hFxm hFym
      refine lt_of_le_of_lt (le_trans hcov h2) ?_
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine ENNReal.mul_lt_top ?_ ?_
      · rw [lt_top_iff_ne_top]
        refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
        · rw [hel2 FxD]
          exact hFx2.2.ne
        · rw [hel2 FyD]
          exact hFy2.2.ne
      · rw [lt_top_iff_ne_top]
        refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
        exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (isCompact_closedBall _ _).measure_lt_top).ne
    · have h2 := cov_pairing_bound hqinv (by simp : ‖(Complex.I)‖ = 1) hqe'm haeI
        hS3m hφ3zero hφ3bd hFxm hFym
      refine lt_of_le_of_lt (le_trans hcov h2) ?_
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine ENNReal.mul_lt_top ?_ ?_
      · rw [lt_top_iff_ne_top]
        refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
        · rw [hel2 FxD]
          exact hFx2.2.ne
        · rw [hel2 FyD]
          exact hFy2.2.ne
      · rw [lt_top_iff_ne_top]
        refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
        exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (isCompact_closedBall _ _).measure_lt_top).ne
  have hGxli2 : MeasureTheory.LocallyIntegrableOn GxD B3 volume :=
    hGint qx' hqx'm (Or.inl hqae_x)
  have hGyli2 : MeasureTheory.LocallyIntegrableOn GyD B3 volume :=
    hGint qy' hqy'm (Or.inr hqae_y)
  -- The combination vanishes almost everywhere on the ball.
  have hcomb : ∀ᵐ z : ℂ, z ∈ B3 → GxD z + Complex.I * GyD z = 0 := by
    have h1 := hwside
    rw [ae_restrict_iff' hΩm] at h1
    filter_upwards [h1, hqae_x, hqae_y] with w' hP hqx hqy
    intro hw'B
    have hw'Ω : w' ∈ Ω := hB3sub hw'B
    obtain ⟨⟨hdet, hwbelt⟩, hvbelt, hgx'v, hgy'v⟩ := hP hw'Ω
    have hwdiffz : DifferentiableAt ℝ u.w (uinv w') := by
      by_contra h
      rw [fderiv_zero_of_not_differentiableAt h] at hdet
      have hdet0 : (0 : ℂ →L[ℝ] ℂ).det = 0 := by
        simp [ContinuousLinearMap.det]
      rw [hdet0] at hdet
      exact lt_irrefl 0 hdet
    have hdetne : (fderiv ℝ u.w (uinv w')).det ≠ 0 := ne_of_gt hdet
    set eL := (fderiv ℝ u.w (uinv w')).toContinuousLinearEquivOfDetNeZero hdetne
      with heLdef
    have hecoe : (eL : ℂ →L[ℝ] ℂ) = fderiv ℝ u.w (uinv w') :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdetne
    have hfd1 : HasFDerivAt u.w (eL : ℂ →L[ℝ] ℂ) (uinv w') := by
      rw [hecoe]
      exact hwdiffz.hasFDerivAt
    have hloc : ∀ᶠ y in nhds w', u.w (uinv y) = y := Filter.Eventually.of_forall hui2
    have hgfd : HasFDerivAt uinv ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) w' :=
      HasFDerivAt.of_local_left_inverse huinvc.continuousAt hfd1 hloc
    have hqx1 : qx' w' = ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 1 := by
      rw [← hqx, hgfd.fderiv]
    have hqy1 : qy' w' = ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) Complex.I := by
      rw [← hqy, hgfd.fderiv]
    have hzV2 : uinv w' ∈ V2 :=
      hKV2 ⟨w', Metric.ball_subset_closedBall hw'B, rfl⟩
    have hχ2z : χ2 (uinv w') = 1 := hV2one _ hzV2
    have hdχ2z : fderiv ℝ χ2 (uinv w') = 0 := by
      have hev : χ2 =ᶠ[nhds (uinv w')] fun _ => (1:ℝ) := by
        filter_upwards [hV2open.mem_nhds hzV2] with p hp
        exact hV2one p hp
      rw [hev.fderiv_eq]
      exact fderiv_const_apply 1
    have hFxz : FxD (uinv w') = gx' (uinv w') := by
      change χ2 (uinv w') • gx' (uinv w')
        + ((fderiv ℝ χ2 (uinv w')) 1) • v (uinv w') = gx' (uinv w')
      rw [hχ2z, hdχ2z]
      have e1 : (1:ℝ) • gx' (uinv w') = gx' (uinv w') := one_smul ℝ _
      have e2 : ((0 : ℂ →L[ℝ] ℝ) 1) • v (uinv w') = 0 := by
        rw [ContinuousLinearMap.zero_apply]
        exact zero_smul ℝ _
      rw [e1, e2, add_zero]
    have hFyz : FyD (uinv w') = gy' (uinv w') := by
      change χ2 (uinv w') • gy' (uinv w')
        + ((fderiv ℝ χ2 (uinv w')) Complex.I) • v (uinv w') = gy' (uinv w')
      rw [hχ2z, hdχ2z]
      have e1 : (1:ℝ) • gy' (uinv w') = gy' (uinv w') := one_smul ℝ _
      have e2 : ((0 : ℂ →L[ℝ] ℝ) Complex.I) • v (uinv w') = 0 := by
        rw [ContinuousLinearMap.zero_apply]
        exact zero_smul ℝ _
      rw [e1, e2, add_zero]
    have hA : ∀ u' : ℂ, (fderiv ℝ u.w (uinv w'))
        (((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) u') = u' := by
      intro u'
      rw [← hecoe]
      simp
    have hcancel := wirtinger_cancel hdet hwbelt hvbelt
      ((eL.symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) hA
    change ((qx' w').re • FxD (uinv w') + (qx' w').im • FyD (uinv w'))
      + Complex.I * ((qy' w').re • FxD (uinv w') + (qy' w').im • FyD (uinv w')) = 0
    rw [hFxz, hFyz, hqx1, hqy1, hgx'v.symm, hgy'v.symm]
    exact hcancel
  -- Weyl's lemma on the ball, and the conclusion at the point.
  have hψcont : ContinuousOn (fun w => v (uinv w)) B3 := by
    refine ContinuousOn.comp hv.cont huinvc.continuousOn ?_
    intro w' hw'
    exact huinvΩ w' (hB3sub hw')
  have hweyl := weyl_lemma_on Metric.isOpen_ball hψcont ⟨hwx, hwy⟩ hGxli2 hGyli2 hcomb
  have hw₀B : w₀ ∈ B3 := Metric.mem_ball_self hs30
  exact ((hweyl w₀ hw₀B).differentiableAt
    (Metric.isOpen_ball.mem_nhds hw₀B)).differentiableWithinAt

-- The removable-singularity inverse-holomorphy transcription and the manifold
-- plumbing are one long elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The Moebius classification splits into affine and inversion branches with long algebra;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage E ([MÖBIUS]): a holomorphic homeomorphism of the upper half plane is a real
Möbius map, through the Cayley transform and the classification of disc automorphisms. -/
theorem holo_upper_selfmap_moebius
    {ψ θ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | 0 < z.im})
    (hψmaps : ∀ z : ℂ, 0 < z.im → 0 < (ψ z).im)
    (hθmaps : ∀ z : ℂ, 0 < z.im → 0 < (θ z).im)
    (hθψ : ∀ z : ℂ, 0 < z.im → θ (ψ z) = z)
    (hψθ : ∀ z : ℂ, 0 < z.im → ψ (θ z) = z)
    (hθcont : ContinuousOn θ {z : ℂ | 0 < z.im}) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → ψ z = moebiusMap A z := by
  classical
  set Ω : Set ℂ := {z : ℂ | 0 < z.im} with hΩdef
  have hΩ : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_im
  have hAn : AnalyticOnNhd ℂ ψ Ω := hψ.analyticOnNhd hΩ
  have hinj : Set.InjOn ψ Ω := by
    intro a ha b hb hab
    have h1 := hθψ  -- keep the name in scope
    calc a = θ (ψ a) := (hθψ a ha).symm
      _ = θ (ψ b) := by rw [hab]
      _ = b := hθψ b hb
  -- `ψ` is an open map on `Ω`.
  have hopen : ∀ z ∈ Ω, nhds (ψ z) ≤ Filter.map ψ (nhds z) := by
    intro z hz
    rcases (hAn z hz).eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have h1 : ∀ᶠ z' in nhdsWithin z {z}ᶜ, ψ z' = ψ z ∧ z' ∈ Ω :=
        (hconst.and (hΩ.eventually_mem hz)).filter_mono nhdsWithin_le_nhds
      obtain ⟨z', ⟨hfz', hz'Ω⟩, hz'ne⟩ := (h1.and eventually_mem_nhdsWithin).exists
      exact hz'ne (Set.mem_singleton_iff.mpr (hinj hz'Ω hz hfz'))
    · exact hle
  -- Critical points of `ψ` are isolated in `Ω`.
  have hcrit : ∀ z ∈ Ω, ∀ᶠ z' in nhdsWithin z {z}ᶜ, deriv ψ z' ≠ 0 := by
    intro z hz
    rcases (hAn.deriv z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      obtain ⟨r, hr0, hball⟩ :=
        Metric.eventually_nhds_iff_ball.mp (h0.and (hΩ.eventually_mem hz))
      have hconst : ∀ z' ∈ Metric.ball z r, ψ z' = ψ z := by
        intro z' hz'
        refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball z r)
          (hψ.mono fun p hp => (hball p hp).2) ?_ hz' (Metric.mem_ball_self hr0)
        intro p hp
        rw [fderivWithin_of_isOpen Metric.isOpen_ball hp]
        refine ContinuousLinearMap.ext_ring ?_
        rw [fderiv_apply_one_eq_deriv, (hball p hp).1]
        simp
      have hmem : z + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have heq : z + ((r / 2 : ℝ) : ℂ) = z :=
        hinj (hball _ hmem).2 hz (hconst _ hmem)
      have hr2 : ((r / 2 : ℝ) : ℂ) = 0 := by simpa using heq
      have : (r / 2 : ℝ) = 0 := by exact_mod_cast hr2
      linarith
    · exact hne
  -- Inverse differentiability at non-critical values.
  have hθd_nc : ∀ w ∈ Ω, deriv ψ (θ w) ≠ 0 → DifferentiableAt ℂ θ w := by
    intro w hw hder
    have hθwΩ : θ w ∈ Ω := hθmaps w hw
    have hfd : HasDerivAt ψ (deriv ψ (θ w)) (θ w) :=
      ((hAn (θ w) hθwΩ).differentiableAt).hasDerivAt
    have hev : ∀ᶠ y in nhds w, ψ (θ y) = y := by
      filter_upwards [hΩ.mem_nhds hw] with y hy
      exact hψθ y hy
    exact (HasDerivAt.of_local_left_inverse (hθcont.continuousAt (hΩ.mem_nhds hw))
      hfd hder hev).differentiableAt
  -- `ψ` maps `Ω` onto `Ω`.
  have himg : ∀ w ∈ Ω, ∃ z ∈ Ω, ψ z = w := fun w hw =>
    ⟨θ w, hθmaps w hw, hψθ w hw⟩
  have himgOpen : ∀ S : Set ℂ, S ⊆ Ω → IsOpen S → IsOpen (ψ '' S) := by
    intro S hSΩ hSo
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hzS, rfl⟩
    exact Filter.le_def.mp (hopen z (hSΩ hzS)) _
      (Filter.image_mem_map (hSo.mem_nhds hzS))
  -- Inverse differentiability everywhere on `Ω`, via removable singularities.
  have hθd : ∀ w ∈ Ω, DifferentiableAt ℂ θ w := by
    intro w hw
    by_cases hder : deriv ψ (θ w) = 0
    swap
    · exact hθd_nc w hw hder
    have hθwΩ : θ w ∈ Ω := hθmaps w hw
    obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      ((eventually_nhdsWithin_iff.mp (hcrit (θ w) hθwΩ)).and (hΩ.eventually_mem hθwΩ))
    have hballΩ : Metric.ball (θ w) r ⊆ Ω := fun p hp => (hball p hp).2
    have hWo : IsOpen (ψ '' Metric.ball (θ w) r) :=
      himgOpen _ hballΩ Metric.isOpen_ball
    have hwW : w ∈ ψ '' Metric.ball (θ w) r :=
      ⟨θ w, Metric.mem_ball_self hr0, hψθ w hw⟩
    have hWΩ : ψ '' Metric.ball (θ w) r ⊆ Ω := by
      rintro w' ⟨z', hz'b, rfl⟩
      exact hψmaps z' (hballΩ hz'b)
    have hoff : DifferentiableOn ℂ θ (ψ '' Metric.ball (θ w) r \ {w}) := by
      rintro w' ⟨⟨z', hz'b, rfl⟩, hw'ne⟩
      have hθz' : θ (ψ z') = z' := hθψ z' (hballΩ hz'b)
      have hz'ne : z' ∈ ({θ w}ᶜ : Set ℂ) := by
        intro hmem
        refine hw'ne (Set.mem_singleton_iff.mpr ?_)
        rw [Set.mem_singleton_iff.mp hmem]
        exact hψθ w hw
      refine ((hθd_nc (ψ z') (hWΩ ⟨z', hz'b, rfl⟩) ?_).differentiableWithinAt)
      rw [hθz']
      exact (hball z' hz'b).1 hz'ne
    have hθW : DifferentiableOn ℂ θ (ψ '' Metric.ball (θ w) r) :=
      (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (hWo.mem_nhds hwW)).mp ⟨hoff, hθcont.continuousAt (hΩ.mem_nhds hw)⟩
    exact hθW.differentiableAt (hWo.mem_nhds hwW)
  have hθdiff : DifferentiableOn ℂ θ Ω := fun w hw =>
    (hθd w hw).differentiableWithinAt
  -- Cayley transport to the unit disc.
  have hcay_holo : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 →
      DifferentiableAt ℂ cayleyToHalfPlane d := by
    intro d hd
    have hne : (1:ℂ) - d ≠ 0 := by
      intro h0
      have h1 : d = 1 := by
        have := sub_eq_zero.mp h0
        exact this.symm
      rw [h1] at hd
      rw [Metric.mem_ball, dist_zero_right] at hd
      simp at hd
    have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.I * (1 + z)) d :=
      (differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (1:ℂ) - z) d :=
      (differentiableAt_const _).sub differentiableAt_id
    have h3 := h1.div h2 hne
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  have hhtc_holo : ∀ τ : ℂ, τ ∈ Ω → DifferentiableAt ℂ halfPlaneToCayley τ := by
    intro τ hτ
    have hne : τ + Complex.I ≠ 0 := by
      intro h0
      have h1 : (τ + Complex.I).im = 0 := by rw [h0]; rfl
      rw [Complex.add_im, Complex.I_im] at h1
      have hτ' : 0 < τ.im := hτ
      linarith
    have h1 : DifferentiableAt ℂ (fun z : ℂ => z - Complex.I) τ :=
      differentiableAt_id.sub (differentiableAt_const _)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => z + Complex.I) τ :=
      differentiableAt_id.add (differentiableAt_const _)
    have h3 := h1.div h2 hne
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  have hcay_mem : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → cayleyToHalfPlane d ∈ Ω :=
    fun d hd => cayleyToHalfPlane_im_pos hd
  -- The transported disc maps.
  set E : ℂ → ℂ := fun d => halfPlaneToCayley (ψ (cayleyToHalfPlane d)) with hEdef
  set Einv : ℂ → ℂ := fun d => halfPlaneToCayley (θ (cayleyToHalfPlane d)) with hEinvdef
  have hE_mem : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → E d ∈ Metric.ball (0:ℂ) 1 := by
    intro d hd
    exact halfPlaneToCayley_mem_ball (hψmaps _ (hcay_mem d hd))
  have hEinv_mem : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 →
      Einv d ∈ Metric.ball (0:ℂ) 1 := by
    intro d hd
    exact halfPlaneToCayley_mem_ball (hθmaps _ (hcay_mem d hd))
  have hE_left : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → Einv (E d) = d := by
    intro d hd
    have h1 : cayleyToHalfPlane (E d) = ψ (cayleyToHalfPlane d) := by
      rw [hEdef]
      exact cayleyToHalfPlane_halfPlaneToCayley (hψmaps _ (hcay_mem d hd))
    rw [hEinvdef]
    change halfPlaneToCayley (θ (cayleyToHalfPlane (E d))) = d
    rw [h1, hθψ _ (hcay_mem d hd)]
    exact halfPlaneToCayley_cayleyToHalfPlane hd
  have hE_right : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → E (Einv d) = d := by
    intro d hd
    have h1 : cayleyToHalfPlane (Einv d) = θ (cayleyToHalfPlane d) := by
      rw [hEinvdef]
      exact cayleyToHalfPlane_halfPlaneToCayley (hθmaps _ (hcay_mem d hd))
    rw [hEdef]
    change halfPlaneToCayley (ψ (cayleyToHalfPlane (Einv d))) = d
    rw [h1, hψθ _ (hcay_mem d hd)]
    exact halfPlaneToCayley_cayleyToHalfPlane hd
  have hE_holo : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 → DifferentiableAt ℂ E d := by
    intro d hd
    have h1 := hcay_holo d hd
    have h2 : DifferentiableAt ℂ ψ (cayleyToHalfPlane d) :=
      (hAn _ (hcay_mem d hd)).differentiableAt
    have h3 : DifferentiableAt ℂ halfPlaneToCayley (ψ (cayleyToHalfPlane d)) :=
      hhtc_holo _ (hψmaps _ (hcay_mem d hd))
    exact DifferentiableAt.comp d h3 (DifferentiableAt.comp d h2 h1)
  have hEinv_holo : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 →
      DifferentiableAt ℂ Einv d := by
    intro d hd
    have h1 := hcay_holo d hd
    have h2 : DifferentiableAt ℂ θ (cayleyToHalfPlane d) :=
      hθd _ (hcay_mem d hd)
    have h3 : DifferentiableAt ℂ halfPlaneToCayley (θ (cayleyToHalfPlane d)) :=
      hhtc_holo _ (hθmaps _ (hcay_mem d hd))
    exact DifferentiableAt.comp d h3 (DifferentiableAt.comp d h2 h1)
  -- The disc diffeomorphism.
  have hmem_disc : ∀ d : ℂ, d ∈ Metric.ball (0:ℂ) 1 ↔ d ∈ unitDiscOpens := by
    intro d
    rfl
  have hbridge : ∀ (F : ℂ → ↥unitDiscOpens) (z : ℂ),
      AnalyticAt ℂ (fun p => (F p : ℂ)) z →
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤ F z := by
    intro F z hFa
    rw [contMDiffAt_iff]
    constructor
    · exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hFa.continuousAt
    · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        PartialEquiv.refl_symm, Function.comp_id, modelWithCornersSelf_coe,
        Set.range_id, id_eq]
      rw [contDiffWithinAt_univ]
      exact hFa.contDiffAt
  have h0disc : (0:ℂ) ∈ Metric.ball (0:ℂ) 1 := Metric.mem_ball_self one_pos
  set D : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ↥unitDiscOpens ↥unitDiscOpens ⊤ :=
    { toFun := fun d => ⟨E (d : ℂ), hE_mem (d : ℂ) d.2⟩
      invFun := fun d => ⟨Einv (d : ℂ), hEinv_mem (d : ℂ) d.2⟩
      left_inv := fun d => Subtype.ext (hE_left (d : ℂ) d.2)
      right_inv := fun d => Subtype.ext (hE_right (d : ℂ) d.2)
      contMDiff_toFun := by
        intro x
        have hxmem : E (x : ℂ) ∈ Metric.ball (0:ℂ) 1 := hE_mem (x : ℂ) x.2
        have key : ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
            (fun d : ℂ =>
              if h : E d ∈ Metric.ball (0:ℂ) 1 then (⟨E d, h⟩ : ↥unitDiscOpens)
              else ⟨E (x : ℂ), hxmem⟩) (x : ℂ) := by
          refine hbridge _ (x : ℂ) ?_
          have h1 : AnalyticAt ℂ E (x : ℂ) := by
            have hEdiffOn : DifferentiableOn ℂ E (Metric.ball (0:ℂ) 1) :=
              fun p hp => (hE_holo p hp).differentiableWithinAt
            exact hEdiffOn.analyticAt (Metric.isOpen_ball.mem_nhds x.2)
          refine h1.congr ?_
          filter_upwards [Metric.isOpen_ball.mem_nhds x.2] with p hp
          rw [dif_pos (hE_mem p hp)]
        have key2 := key.comp x (contMDiff_subtype_val.contMDiffAt
          (I := modelWithCornersSelf ℂ ℂ) (n := (⊤ : WithTop ℕ∞)))
        refine key2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun d => ?_)
        change (⟨E (d : ℂ), hE_mem (d : ℂ) d.2⟩ : ↥unitDiscOpens)
          = if h : E (d : ℂ) ∈ Metric.ball (0:ℂ) 1 then (⟨E (d : ℂ), h⟩ : ↥unitDiscOpens)
            else ⟨E (x : ℂ), hxmem⟩
        rw [dif_pos (hE_mem (d : ℂ) d.2)]
      contMDiff_invFun := by
        intro x
        have hxmem : Einv (x : ℂ) ∈ Metric.ball (0:ℂ) 1 := hEinv_mem (x : ℂ) x.2
        have key : ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
            (fun d : ℂ =>
              if h : Einv d ∈ Metric.ball (0:ℂ) 1 then (⟨Einv d, h⟩ : ↥unitDiscOpens)
              else ⟨Einv (x : ℂ), hxmem⟩) (x : ℂ) := by
          refine hbridge _ (x : ℂ) ?_
          have h1 : AnalyticAt ℂ Einv (x : ℂ) := by
            have hEdiffOn : DifferentiableOn ℂ Einv (Metric.ball (0:ℂ) 1) :=
              fun p hp => (hEinv_holo p hp).differentiableWithinAt
            exact hEdiffOn.analyticAt (Metric.isOpen_ball.mem_nhds x.2)
          refine h1.congr ?_
          filter_upwards [Metric.isOpen_ball.mem_nhds x.2] with p hp
          rw [dif_pos (hEinv_mem p hp)]
        have key2 := key.comp x (contMDiff_subtype_val.contMDiffAt
          (I := modelWithCornersSelf ℂ ℂ) (n := (⊤ : WithTop ℕ∞)))
        refine key2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun d => ?_)
        change (⟨Einv (d : ℂ), hEinv_mem (d : ℂ) d.2⟩ : ↥unitDiscOpens)
          = if h : Einv (d : ℂ) ∈ Metric.ball (0:ℂ) 1
            then (⟨Einv (d : ℂ), h⟩ : ↥unitDiscOpens)
            else ⟨Einv (x : ℂ), hxmem⟩
        rw [dif_pos (hEinv_mem (d : ℂ) d.2)] } with hDdef
  obtain ⟨A, hA⟩ := exists_sl2_of_diffeomorph_unitDisc D
  refine ⟨A, ?_⟩
  intro z hz
  set d : ↥unitDiscOpens := ⟨halfPlaneToCayley z, halfPlaneToCayley_mem_ball hz⟩
    with hddef
  obtain ⟨τ, τ', h1, h2, h3⟩ := hA d
  have hτ : (τ : ℂ) = z := by
    rw [h1, hddef]
    exact cayleyToHalfPlane_halfPlaneToCayley hz
  have hDd : ((D d : ↥unitDiscOpens) : ℂ) = halfPlaneToCayley (ψ z) := by
    change E (halfPlaneToCayley z) = halfPlaneToCayley (ψ z)
    rw [hEdef]
    change halfPlaneToCayley (ψ (cayleyToHalfPlane (halfPlaneToCayley z)))
      = halfPlaneToCayley (ψ z)
    rw [cayleyToHalfPlane_halfPlaneToCayley hz]
  have hτ' : (τ' : ℂ) = ψ z := by
    rw [h2, hDd]
    exact cayleyToHalfPlane_halfPlaneToCayley (hψmaps z hz)
  have h4 := coe_smul_eq_moebiusMap A τ
  rw [h3] at h4
  rw [hτ, hτ'] at h4
  exact h4

-- The gauge bookkeeping for the half-disc contour is one long elaboration; the raised
-- budget is required.
set_option maxHeartbeats 400000 in
-- The radial contour parameterization carries explicit trigonometric estimates;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage F1 ([HALF] contour): the radial parameterization of the boundary of the upper
half-disc `{‖z‖ ≤ R} ∩ {im ≥ 0}` from an interior point `z₀`, via the Minkowski gauge:
a positive continuous radial function landing on the frontier, uniquely determined by
frontier membership along each ray. -/
theorem halfdisc_radial (z₀ : ℂ) (hz₀ : 0 < z₀.im) (R : ℝ) (hR : ‖z₀‖ + 1 < R) :
    ∃ rad : ℝ → ℝ, Continuous rad ∧ (∀ ϑ : ℝ, 0 < rad ϑ) ∧
      (∀ ϑ : ℝ, ‖z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)‖ ≤ R ∧
        0 ≤ (z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)).im ∧
        (‖z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)‖ = R ∨
          (z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I)).im = 0)) ∧
      (∀ (ϑ t : ℝ), 0 < t →
        ‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ ≤ R →
        0 ≤ (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im →
        ¬(‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ < R ∧
          0 < (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im) →
        rad ϑ = t) := by
  classical
  haveI : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have hRpos : 0 < R := lt_of_le_of_lt (by positivity) hR
  -- The half-disc body, shifted to put `z₀` at the origin.
  set B₀ : Set ℂ := {w : ℂ | ‖z₀ + w‖ ≤ R ∧ 0 ≤ (z₀ + w).im} with hB₀def
  have hpre : B₀ = (fun w => z₀ + w) ⁻¹'
      (Metric.closedBall 0 R ∩ {c : ℂ | 0 ≤ c.im}) := by
    ext w
    simp only [hB₀def, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right]
  have hconv : Convex ℝ B₀ := by
    have him : B₀ = (fun w => -z₀ + w) ''
        (Metric.closedBall 0 R ∩ {c : ℂ | 0 ≤ c.im}) := by
      ext w
      simp only [hB₀def, Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff,
        Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hw
        exact ⟨z₀ + w, ⟨hw.1, hw.2⟩, by ring⟩
      · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
        have h2 : z₀ + (-z₀ + k) = k := by ring
        rw [h2]
        exact ⟨hk1, hk2⟩
    rw [him]
    exact ((convex_closedBall (0:ℂ) R).inter (convex_halfSpace_im_ge 0)).translate (-z₀)
  have hclosed : IsClosed B₀ := by
    rw [hpre]
    refine IsClosed.preimage (by fun_prop) ?_
    exact (Metric.isClosed_closedBall).inter
      (isClosed_le continuous_const Complex.continuous_im)
  have hB₀nhds : B₀ ∈ nhds (0 : ℂ) := by
    have hδ : 0 < min (R - ‖z₀‖) z₀.im := by
      refine lt_min ?_ hz₀
      linarith
    refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ) ?_
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have h1 : ‖w‖ < R - ‖z₀‖ := lt_of_lt_of_le hw (min_le_left _ _)
    have h2 : ‖w‖ < z₀.im := lt_of_lt_of_le hw (min_le_right _ _)
    constructor
    · calc ‖z₀ + w‖ ≤ ‖z₀‖ + ‖w‖ := norm_add_le _ _
        _ ≤ R := by linarith
    · have h3 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      rw [Complex.add_im]
      have h4 : -z₀.im < w.im := by
        have := abs_lt.mp (lt_of_le_of_lt h3 h2)
        linarith [this.1]
      linarith
  have habs : Absorbent ℝ B₀ := absorbent_nhds_zero hB₀nhds
  have hbdd : Bornology.IsVonNBounded ℝ B₀ := by
    refine (NormedSpace.isVonNBounded_iff ℝ).mpr ?_
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall
      (x := (0:ℂ)) (r := R + ‖z₀‖)) ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ = ‖(z₀ + w) - z₀‖ := by ring_nf
      _ ≤ ‖z₀ + w‖ + ‖z₀‖ := norm_sub_le _ _
      _ ≤ R + ‖z₀‖ := by
          have := hw.1
          linarith
  have hgpos : ∀ u : ℂ, u ≠ 0 → 0 < gauge B₀ u := fun u hu =>
    (gauge_pos habs hbdd).mpr hu
  have hgcont : Continuous (gauge B₀) := continuous_gauge hconv hB₀nhds
  -- Membership from the gauge.
  have hmemB : ∀ u : ℂ, gauge B₀ u ≤ 1 → u ∈ B₀ := by
    intro u hu
    have hseq : Filter.Tendsto (fun n : ℕ => (1 - 1/(n+2) : ℝ) • u)
        Filter.atTop (nhds u) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 - 1/(n+2) : ℝ))
          Filter.atTop (nhds 1) := by
        have h2 : Filter.Tendsto (fun n : ℕ => (1/(n+2) : ℝ)) Filter.atTop (nhds 0) := by
          have h3 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h4 : (fun n : ℕ => (1/(n+2) : ℝ))
              = fun n : ℕ => 1/((((n+1 : ℕ) : ℝ)) + 1) := by
            funext n
            push_cast
            ring_nf
          rw [h4]
          exact h3.comp (Filter.tendsto_add_atTop_nat 1)
        have h5 := (tendsto_const_nhds (x := (1:ℝ))).sub h2
        rwa [sub_zero] at h5
      have h6 := h1.smul_const u
      simpa using h6
    refine hclosed.mem_of_tendsto hseq ?_
    refine Filter.Eventually.of_forall fun n => ?_
    have hn1 : (0:ℝ) < 1/(n+2) := by positivity
    have hn2 : (1 - 1/(n+2) : ℝ) < 1 := by linarith
    have hn0 : (0:ℝ) ≤ 1 - 1/(n+2) := by
      have h7 : (1/(n+2) : ℝ) ≤ 1/2 := by
        refine one_div_le_one_div_of_le (by norm_num) ?_
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    have h8 : gauge B₀ ((1 - 1/(n+2) : ℝ) • u) < 1 := by
      have h9 : gauge B₀ ((1 - 1/(n+2) : ℝ) • u) = (1 - 1/(n+2) : ℝ) * gauge B₀ u := by
        have h10 := gauge_smul_of_nonneg (s := B₀) hn0 u
        rw [smul_eq_mul] at h10
        exact h10
      rw [h9]
      calc (1 - 1/(n+2) : ℝ) * gauge B₀ u ≤ (1 - 1/(n+2) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hu hn0
        _ < 1 := by linarith
    have h10 := (gauge_lt_one_iff_mem_interior hconv hB₀nhds).mp h8
    exact interior_subset h10
  -- Strict interior points of the body.
  have hsub : interior B₀ ⊆ {w : ℂ | ‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im} := by
    intro w' hw'
    have hw'B : w' ∈ B₀ := interior_subset hw'
    constructor
    · rcases lt_or_eq_of_le hw'B.1 with h | h
      · exact h
      · exfalso
        have hne : z₀ + w' ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at h
          linarith
        have hcont2 : Filter.Tendsto
            (fun ε : ℝ => w' + (ε : ℂ) * (z₀ + w')) (nhdsWithin 0 (Set.Ioi 0))
            (nhds w') := by
          have hc : Continuous (fun ε : ℝ => w' + (ε : ℂ) * (z₀ + w')) := by
            fun_prop
          have h1 := hc.tendsto 0
          have h2 : w' + (((0:ℝ) : ℂ)) * (z₀ + w') = w' := by simp
          rw [h2] at h1
          exact h1.mono_left nhdsWithin_le_nhds
        have hmem := hcont2.eventually (isOpen_interior.mem_nhds hw')
        obtain ⟨ε, hεmem, hεpos⟩ := (hmem.and self_mem_nhdsWithin).exists
        have hεB : w' + (ε : ℂ) * (z₀ + w') ∈ B₀ := interior_subset hεmem
        have hnorm : ‖z₀ + (w' + (ε : ℂ) * (z₀ + w'))‖ = (1 + ε) * ‖z₀ + w'‖ := by
          have h2 : z₀ + (w' + (ε : ℂ) * (z₀ + w')) = ((1 + ε : ℝ) : ℂ) * (z₀ + w') := by
            push_cast
            ring
          rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [hεpos])]
        have h3 := hεB.1
        rw [hnorm, ← h] at h3
        have h4 : (0:ℝ) < ‖z₀ + w'‖ := norm_pos_iff.mpr hne
        have hε0 : (0:ℝ) < ε := hεpos
        nlinarith
    · rcases lt_or_eq_of_le hw'B.2 with h | h
      · exact h
      · exfalso
        have hcont2 : Filter.Tendsto
            (fun ε : ℝ => w' - (ε : ℂ) * Complex.I) (nhdsWithin 0 (Set.Ioi 0))
            (nhds w') := by
          have hc : Continuous (fun ε : ℝ => w' - (ε : ℂ) * Complex.I) := by
            fun_prop
          have h1 := hc.tendsto 0
          have h2 : w' - (((0:ℝ) : ℂ)) * Complex.I = w' := by simp
          rw [h2] at h1
          exact h1.mono_left nhdsWithin_le_nhds
        have hmem := hcont2.eventually (isOpen_interior.mem_nhds hw')
        obtain ⟨ε, hεmem, hεpos⟩ := (hmem.and self_mem_nhdsWithin).exists
        have hεB : w' - (ε : ℂ) * Complex.I ∈ B₀ := interior_subset hεmem
        have h3 := hεB.2
        have h4 : (z₀ + (w' - (ε : ℂ) * Complex.I)).im = (z₀ + w').im - ε := by
          simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]
          ring
        rw [h4, ← h] at h3
        have hε0 : (0:ℝ) < ε := hεpos
        linarith
  -- The gauge is `1` exactly on the non-strict frontier part.
  have hfr1 : ∀ w : ℂ, w ∈ B₀ → ¬(‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im) →
      gauge B₀ w = 1 := by
    intro w hw hnot
    refine le_antisymm (gauge_le_one_of_mem hw) ?_
    by_contra hlt
    push Not at hlt
    exact hnot (hsub ((gauge_lt_one_iff_mem_interior hconv hB₀nhds).mp hlt))
  -- The radial function.
  refine ⟨fun ϑ => (gauge B₀ (Complex.exp (ϑ * Complex.I)))⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : Continuous fun ϑ : ℝ => Complex.exp (ϑ * Complex.I) := by
      fun_prop
    refine (hgcont.comp h1).inv₀ ?_
    intro ϑ
    exact ne_of_gt (hgpos _ (Complex.exp_ne_zero _))
  · intro ϑ
    exact inv_pos.mpr (hgpos _ (Complex.exp_ne_zero _))
  · intro ϑ
    set g1 : ℝ := gauge B₀ (Complex.exp (ϑ * Complex.I)) with hg1def
    have hg1pos : 0 < g1 := hgpos _ (Complex.exp_ne_zero _)
    have hkey : gauge B₀ ((g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I)) = 1 := by
      have h10 := gauge_smul_of_nonneg (s := B₀)
        (le_of_lt (inv_pos.mpr hg1pos)) (Complex.exp (ϑ * Complex.I))
      rw [smul_eq_mul] at h10
      have h11 : gauge B₀ ((g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I))
          = g1⁻¹ * gauge B₀ (Complex.exp (ϑ * Complex.I)) := h10
      rw [h11, ← hg1def, inv_mul_cancel₀ (ne_of_gt hg1pos)]
    have hsm : ((g1⁻¹ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)
        = (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I) := by
      rw [Complex.real_smul]
    have hmem : (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I) ∈ B₀ :=
      hmemB _ (le_of_eq hkey)
    have hnotint : ¬((g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I) ∈ interior B₀) := by
      intro hint
      have := (gauge_lt_one_iff_mem_interior hconv hB₀nhds).mpr hint
      rw [hkey] at this
      exact lt_irrefl 1 this
    have hnotstrict : ¬(‖z₀ + (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I)‖ < R ∧
        0 < (z₀ + (g1⁻¹ : ℝ) • Complex.exp (ϑ * Complex.I)).im) := by
      intro hstrict
      refine hnotint ?_
      have hopen : IsOpen {w : ℂ | ‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im} := by
        refine IsOpen.inter ?_ ?_
        · exact isOpen_lt ((continuous_const.add continuous_id).norm) continuous_const
        · exact isOpen_lt continuous_const
            (Complex.continuous_im.comp (continuous_const.add continuous_id))
      have hsubB : {w : ℂ | ‖z₀ + w‖ < R ∧ 0 < (z₀ + w).im} ⊆ B₀ := by
        intro w hw
        exact ⟨le_of_lt hw.1, le_of_lt hw.2⟩
      exact interior_maximal hsubB hopen hstrict
    rw [hsm]
    refine ⟨hmem.1, hmem.2, ?_⟩
    by_contra hor
    push Not at hor
    exact hnotstrict ⟨lt_of_le_of_ne hmem.1 hor.1, lt_of_le_of_ne hmem.2 (Ne.symm hor.2)⟩
  · intro ϑ t ht htle htim hnot
    have hmem : (t : ℝ) • Complex.exp (ϑ * Complex.I) ∈ B₀ := by
      rw [← Complex.real_smul] at htle htim ⊢
      exact ⟨htle, htim⟩
    have hnot' : ¬(‖z₀ + (t : ℝ) • Complex.exp (ϑ * Complex.I)‖ < R ∧
        0 < (z₀ + (t : ℝ) • Complex.exp (ϑ * Complex.I)).im) := by
      rw [← Complex.real_smul] at hnot
      exact hnot
    have h1 := hfr1 _ hmem hnot'
    have h10 := gauge_smul_of_nonneg (s := B₀) (le_of_lt ht)
      (Complex.exp (ϑ * Complex.I))
    rw [smul_eq_mul] at h10
    have h11 : gauge B₀ ((t : ℝ) • Complex.exp (ϑ * Complex.I))
        = t * gauge B₀ (Complex.exp (ϑ * Complex.I)) := h10
    rw [h11] at h1
    have h2 : gauge B₀ (Complex.exp (ϑ * Complex.I)) = t⁻¹ := by
      field_simp at h1 ⊢
      linarith [h1]
    change (gauge B₀ (Complex.exp (ϑ * Complex.I)))⁻¹ = t
    rw [h2, inv_inv]

/-- Stage F2: a continuous function on an interval with values in `2πiℤ` takes equal
values at the endpoints. -/
theorem disc_const {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hint : ∀ s ∈ Set.Icc a b, ∃ K : ℤ, f s = (K : ℂ) * (2 * Real.pi * Complex.I)) :
    f a = f b := by
  classical
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  -- The normalized imaginary part is an integer-valued continuous function.
  set J : ℝ → ℝ := fun s => (f s).im / (2 * Real.pi) with hJdef
  have hJc : ContinuousOn J (Set.Icc a b) :=
    (Complex.continuous_im.comp_continuousOn hf).div_const _
  have hJint : ∀ s ∈ Set.Icc a b, ∃ K : ℤ, J s = (K : ℝ) := by
    intro s hs
    obtain ⟨K, hK⟩ := hint s hs
    refine ⟨K, ?_⟩
    change (f s).im / (2 * Real.pi) = (K : ℝ)
    have h1 : (f s).im = K * (2 * Real.pi) := by
      rw [hK]
      simp [Complex.mul_im, Complex.mul_re]
    rw [h1]
    field_simp
  -- Equal endpoint values of `J` by the intermediate value theorem.
  have hJab : J a = J b := by
    by_contra hne
    obtain ⟨Ka, hKa⟩ := hJint a (Set.left_mem_Icc.mpr hab)
    obtain ⟨Kb, hKb⟩ := hJint b (Set.right_mem_Icc.mpr hab)
    have hKab : Ka ≠ Kb := by
      intro h
      exact hne (by rw [hKa, hKb, h])
    -- A value strictly between two distinct integers that is not an integer.
    set m : ℝ := (max Ka Kb : ℤ) - 1/2 with hmdef
    have hmmem : m ∈ Set.uIcc (J a) (J b) := by
      rw [Set.mem_uIcc]
      rcases lt_or_gt_of_ne hKab with h | h
      · left
        constructor
        · rw [hKa, hmdef]
          have hZ : Ka ≤ Kb - 1 := by omega
          have h1 : (Ka : ℝ) ≤ (Kb : ℝ) - 1 := by exact_mod_cast hZ
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Kb := by
            rw [max_eq_right (le_of_lt h)]
          rw [h2]
          linarith
        · rw [hKb, hmdef]
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Kb := by
            rw [max_eq_right (le_of_lt h)]
          rw [h2]
          linarith
      · right
        constructor
        · rw [hKb, hmdef]
          have hZ : Kb ≤ Ka - 1 := by omega
          have h1 : (Kb : ℝ) ≤ (Ka : ℝ) - 1 := by exact_mod_cast hZ
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Ka := by
            rw [max_eq_left (le_of_lt h)]
          rw [h2]
          linarith
        · rw [hKa, hmdef]
          have h2 : ((max Ka Kb : ℤ) : ℝ) = Ka := by
            rw [max_eq_left (le_of_lt h)]
          rw [h2]
          linarith
    have hIVT := intermediate_value_uIcc (f := J) (a := a) (b := b)
      (hJc.mono (Set.uIcc_of_le hab).subset)
    obtain ⟨c, hc, hJceq⟩ := hIVT hmmem
    have hcIcc : c ∈ Set.Icc a b := (Set.uIcc_of_le hab).subset hc
    obtain ⟨Kc, hKc⟩ := hJint c hcIcc
    rw [hKc, hmdef] at hJceq
    have h1 : (2 * Kc : ℤ) = 2 * (max Ka Kb) - 1 := by
      have h2 : (2 * (Kc:ℝ)) = 2 * ((max Ka Kb : ℤ):ℝ) - 1 := by linarith
      exact_mod_cast h2
    omega
  -- Endpoint equality of `f` from that of `J`.
  obtain ⟨Ka, hKa⟩ := hint a (Set.left_mem_Icc.mpr hab)
  obtain ⟨Kb, hKb⟩ := hint b (Set.right_mem_Icc.mpr hab)
  have hJa : J a = (Ka : ℝ) := by
    change (f a).im / (2 * Real.pi) = (Ka : ℝ)
    have h1 : (f a).im = Ka * (2 * Real.pi) := by
      rw [hKa]
      simp [Complex.mul_im, Complex.mul_re]
    rw [h1]
    field_simp
  have hJb : J b = (Kb : ℝ) := by
    change (f b).im / (2 * Real.pi) = (Kb : ℝ)
    have h1 : (f b).im = Kb * (2 * Real.pi) := by
      rw [hKb]
      simp [Complex.mul_im, Complex.mul_re]
    rw [h1]
    field_simp
  have hKab : Ka = Kb := by
    have h1 : (Ka : ℝ) = (Kb : ℝ) := by
      rw [← hJa, ← hJb, hJab]
    exact_mod_cast h1
  rw [hKa, hKb, hKab]

-- The crossing-window geometry is one long elaboration; the raised budget is required.
set_option maxHeartbeats 400000 in
-- The window-selection argument iterates the contour estimate through a bisection;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage F3 ([HALF] window): the half-disc radial contour passes through a prescribed
real frontier point at a unique angle in `(π, 2π)`, and near that angle the contour is
real with strictly increasing real part. -/
theorem halfdisc_window (z₀ : ℂ) (hz₀ : 0 < z₀.im) (R : ℝ)
    (rad : ℝ → ℝ) (_hradpos : ∀ ϑ : ℝ, 0 < rad ϑ)
    (hraduniq : ∀ (ϑ t : ℝ), 0 < t →
      ‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ ≤ R →
      0 ≤ (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im →
      ¬(‖z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)‖ < R ∧
        0 < (z₀ + (t : ℂ) * Complex.exp (ϑ * Complex.I)).im) →
      rad ϑ = t)
    (q : ℂ) (hqim : q.im = 0) (hqnorm : ‖q‖ < R) (hqzne : q - z₀ ≠ 0) :
    ∃ ϑstar ϑminus ϑplus : ℝ,
      (Real.pi < ϑstar ∧ ϑstar < 2*Real.pi) ∧
      (0 < ϑminus ∧ ϑminus < ϑstar ∧ ϑstar < ϑplus ∧ ϑplus < 2*Real.pi) ∧
      rad ϑstar = ‖q - z₀‖ ∧
      z₀ + ((rad ϑstar : ℝ) : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q ∧
      q - z₀ = ((‖q - z₀‖ : ℝ) : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) ∧
      (∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
        (z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).im = 0) ∧
      (∀ ϑ ϑ' : ℝ, ϑminus ≤ ϑ → ϑ < ϑ' → ϑ' ≤ ϑplus →
        (z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).re
          < (z₀ + ((rad ϑ' : ℝ) : ℂ) * Complex.exp ((ϑ' : ℂ) * Complex.I)).re) := by
  classical
  -- The crossing angle.
  set tstar : ℝ := ‖q - z₀‖ with htstardef
  have htstarpos : 0 < tstar := norm_pos_iff.mpr hqzne
  set ϑstar : ℝ := Complex.arg (q - z₀) + 2*Real.pi with hϑstardef
  have hargneg : Complex.arg (q - z₀) < 0 := by
    rw [Complex.arg_neg_iff]
    rw [Complex.sub_im, hqim]
    linarith
  have harggt : -Real.pi < Complex.arg (q - z₀) := Complex.neg_pi_lt_arg _
  have hϑstarmem : Real.pi < ϑstar ∧ ϑstar < 2*Real.pi := by
    constructor
    · rw [hϑstardef]; linarith
    · rw [hϑstardef]; linarith
  have hϑstarexp : Complex.exp ((ϑstar : ℂ) * Complex.I)
      = Complex.exp ((Complex.arg (q - z₀) : ℂ) * Complex.I) := by
    rw [hϑstardef]
    push_cast
    rw [add_mul, Complex.exp_add]
    have h1 : (2:ℂ) * Real.pi * Complex.I = 2 * ↑Real.pi * Complex.I := by ring
    rw [show ((2:ℂ) * ↑Real.pi) * Complex.I = 2 * ↑Real.pi * Complex.I by ring,
      Complex.exp_two_pi_mul_I, mul_one]
  have hpolar : q - z₀ = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := by
    rw [hϑstarexp, htstardef]
    exact (Complex.norm_mul_exp_arg_mul_I (q - z₀)).symm
  -- The radial function passes through the crossing point.
  have hradstar : rad ϑstar = tstar := by
    refine hraduniq ϑstar tstar htstarpos ?_ ?_ ?_
    · have h1 : z₀ + (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q := by
        rw [← hpolar]
        ring
      rw [h1]
      exact le_of_lt hqnorm
    · have h1 : z₀ + (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q := by
        rw [← hpolar]
        ring
      rw [h1, hqim]
    · have h1 : z₀ + (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q := by
        rw [← hpolar]
        ring
      rw [h1, hqim]
      intro hstrict
      exact lt_irrefl 0 hstrict.2
  set tr : ℝ → ℝ := fun ϑ => -z₀.im / Real.sin ϑ with htrdef
  set η : ℝ → ℂ := fun ϑ => z₀ + (tr ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)
    with hηdef
  have hexpstar : Complex.exp ((ϑstar : ℂ) * Complex.I)
      = (q - z₀) / (tstar : ℂ) := by
    rw [hpolar]
    have h1 : (tstar : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt htstarpos
    field_simp
  have hsinstar : Real.sin ϑstar < 0 := by
    have h1 : Real.sin ϑstar = ((q - z₀) / (tstar : ℂ)).im := by
      rw [← hexpstar]
      exact (Complex.exp_ofReal_mul_I_im ϑstar).symm
    have h2 : ((q - z₀) / (tstar : ℂ)).im = (q - z₀).im / tstar := by
      rw [Complex.div_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      have h3 : (tstar:ℝ) ≠ 0 := ne_of_gt htstarpos
      field_simp
      rw [Complex.normSq_ofReal]
      ring
    have h4 : (q - z₀).im = -z₀.im := by
      rw [Complex.sub_im, hqim]
      ring
    rw [h1, h2, h4]
    have h5 : (0:ℝ) < z₀.im / tstar := div_pos hz₀ htstarpos
    have h6 : -z₀.im / tstar = -(z₀.im / tstar) := by ring
    rw [h6]
    linarith
  have htrstar : tr ϑstar = tstar := by
    rw [htrdef]
    have h1 : Real.sin ϑstar = -z₀.im / tstar := by
      have h2 : Real.sin ϑstar = ((q - z₀) / (tstar : ℂ)).im := by
        rw [← hexpstar]
        exact (Complex.exp_ofReal_mul_I_im ϑstar).symm
      have h3 : ((q - z₀) / (tstar : ℂ)).im = (q - z₀).im / tstar := by
        rw [Complex.div_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im]
        field_simp
        rw [Complex.normSq_ofReal]
        ring
      have h4 : (q - z₀).im = -z₀.im := by
        rw [Complex.sub_im, hqim]
        ring
      rw [h2, h3, h4]
    change -z₀.im / Real.sin ϑstar = tstar
    rw [h1]
    have h5 : z₀.im ≠ 0 := ne_of_gt hz₀
    field_simp
  have hηstar : η ϑstar = q := by
    rw [hηdef]
    change z₀ + (tr ϑstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) = q
    rw [htrstar, ← hpolar]
    ring
  -- The window: an interval around the crossing angle where the contour is real.
  have hVsin : IsOpen {ϑ : ℝ | Real.sin ϑ < 0} :=
    isOpen_lt Real.continuous_sin continuous_const
  have htrcont : ContinuousOn tr {ϑ : ℝ | Real.sin ϑ < 0} := by
    refine ContinuousOn.div continuousOn_const Real.continuous_sin.continuousOn ?_
    intro ϑ hϑ
    exact ne_of_lt hϑ
  have hηcont : ContinuousOn η {ϑ : ℝ | Real.sin ϑ < 0} := by
    refine ContinuousOn.add continuousOn_const ?_
    refine ContinuousOn.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp_continuousOn htrcont
    · refine Continuous.continuousOn ?_
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal).mul continuous_const)
  have hWopen1 : IsOpen ({ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)) :=
    htrcont.isOpen_inter_preimage hVsin isOpen_Ioi
  have hWopen : IsOpen ({ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)
      ∩ (fun ϑ => ‖η ϑ‖) ⁻¹' (Set.Iio R)) := by
    have h1 : ContinuousOn (fun ϑ => ‖η ϑ‖)
        ({ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)) :=
      (hηcont.mono Set.inter_subset_left).norm
    exact h1.isOpen_inter_preimage hWopen1 isOpen_Iio
  have hstarW : ϑstar ∈ {ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)
      ∩ (fun ϑ => ‖η ϑ‖) ⁻¹' (Set.Iio R) := by
    refine ⟨⟨hsinstar, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, htrstar]
      exact htstarpos
    · rw [Set.mem_preimage, hηstar]
      exact hqnorm
  obtain ⟨ε₀, hε₀pos, hε₀ball⟩ := Metric.isOpen_iff.mp hWopen ϑstar hstarW
  set ε : ℝ := min ε₀ (min ϑstar (2*Real.pi - ϑstar)) with hεdef
  have hεpos : 0 < ε := by
    refine lt_min hε₀pos (lt_min ?_ ?_)
    · linarith [hϑstarmem.1, Real.pi_pos]
    · linarith [hϑstarmem.2]
  have hεball : Metric.ball ϑstar ε ⊆ {ϑ : ℝ | Real.sin ϑ < 0} ∩ tr ⁻¹' (Set.Ioi 0)
      ∩ (fun ϑ => ‖η ϑ‖) ⁻¹' (Set.Iio R) :=
    subset_trans (Metric.ball_subset_ball (min_le_left _ _)) hε₀ball
  have hεle1 : ε ≤ ϑstar := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle2 : ε ≤ 2*Real.pi - ϑstar := le_trans (min_le_right _ _) (min_le_right _ _)
  set ϑplus : ℝ := ϑstar + ε/2 with hϑplusdef
  set ϑminus : ℝ := ϑstar - ε/2 with hϑminusdef
  have hwin : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
      Real.sin ϑ < 0 ∧ 0 < tr ϑ ∧ ‖η ϑ‖ < R := by
    intro ϑ h1 h2
    have h3 : ϑ ∈ Metric.ball ϑstar ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · rw [hϑminusdef] at h1
        linarith
      · rw [hϑplusdef] at h2
        linarith
    obtain ⟨⟨ha, hb⟩, hc⟩ := hεball h3
    exact ⟨ha, hb, hc⟩
  -- On the window, the contour is the real hit point.
  have hηim : ∀ ϑ : ℝ, Real.sin ϑ < 0 → (η ϑ).im = 0 := by
    intro ϑ hϑ
    change (z₀ + (tr ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).im = 0
    rw [Complex.add_im, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_re]
    have h1 : Real.sin ϑ ≠ 0 := ne_of_lt hϑ
    rw [htrdef]
    field_simp
    ring
  have hradwin : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus → rad ϑ = tr ϑ := by
    intro ϑ h1 h2
    obtain ⟨ha, hb, hc⟩ := hwin ϑ h1 h2
    refine hraduniq ϑ (tr ϑ) hb ?_ ?_ ?_
    · exact le_of_lt hc
    · rw [show z₀ + ((tr ϑ : ℝ) : ℂ) * Complex.exp ((ϑ:ℂ) * Complex.I) = η ϑ from rfl]
      rw [hηim ϑ ha]
    · rw [show z₀ + ((tr ϑ : ℝ) : ℂ) * Complex.exp ((ϑ:ℂ) * Complex.I) = η ϑ from rfl]
      intro hstrict
      rw [hηim ϑ ha] at hstrict
      exact lt_irrefl 0 hstrict.2
  set X : ℝ → ℝ := fun ϑ => z₀.re - z₀.im * (Real.cos ϑ / Real.sin ϑ) with hXdef
  have hηre : ∀ ϑ : ℝ, Real.sin ϑ < 0 → (η ϑ).re = X ϑ := by
    intro ϑ hϑ
    change (z₀ + (tr ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)).re = X ϑ
    rw [Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_re]
    have h1 : Real.sin ϑ ≠ 0 := ne_of_lt hϑ
    rw [htrdef, hXdef]
    field_simp
    ring
  have hηofReal : ∀ ϑ : ℝ, Real.sin ϑ < 0 → η ϑ = ((X ϑ : ℝ) : ℂ) := by
    intro ϑ hϑ
    refine Complex.ext ?_ ?_
    · rw [hηre ϑ hϑ]
      simp
    · rw [hηim ϑ hϑ]
      simp
  have hXmono : StrictMonoOn X (Set.Icc ϑminus ϑplus) := by
    have hD : Convex ℝ (Set.Icc ϑminus ϑplus) := convex_Icc _ _
    have hXd : ∀ ϑ ∈ Set.Icc ϑminus ϑplus,
        HasDerivAt X (z₀.im / (Real.sin ϑ)^2) ϑ := by
      intro ϑ hϑ
      have hsin : Real.sin ϑ < 0 := (hwin ϑ hϑ.1 hϑ.2).1
      have hsinne : Real.sin ϑ ≠ 0 := ne_of_lt hsin
      have h1 : HasDerivAt (fun ϑ => Real.cos ϑ / Real.sin ϑ)
          ((-Real.sin ϑ * Real.sin ϑ - Real.cos ϑ * Real.cos ϑ) / (Real.sin ϑ)^2) ϑ :=
        (Real.hasDerivAt_cos ϑ).div (Real.hasDerivAt_sin ϑ) hsinne
      have h2 : HasDerivAt X
          (-(z₀.im * ((-Real.sin ϑ * Real.sin ϑ - Real.cos ϑ * Real.cos ϑ)
            / (Real.sin ϑ)^2))) ϑ := by
        exact ((h1.const_mul z₀.im).neg).const_add z₀.re
      have h3 : -(z₀.im * ((-Real.sin ϑ * Real.sin ϑ - Real.cos ϑ * Real.cos ϑ)
          / (Real.sin ϑ)^2)) = z₀.im / (Real.sin ϑ)^2 := by
        have h4 : Real.sin ϑ * Real.sin ϑ + Real.cos ϑ * Real.cos ϑ = 1 := by
          have := Real.sin_sq_add_cos_sq ϑ
          nlinarith
        field_simp
        nlinarith [h4]
      rw [h3] at h2
      exact h2
    refine strictMonoOn_of_deriv_pos hD ?_ ?_
    · intro ϑ hϑ
      exact (hXd ϑ hϑ).continuousAt.continuousWithinAt
    · intro ϑ hϑ
      rw [interior_Icc] at hϑ
      have hϑ' : ϑ ∈ Set.Icc ϑminus ϑplus := ⟨le_of_lt hϑ.1, le_of_lt hϑ.2⟩
      rw [(hXd ϑ hϑ').deriv]
      have hsin : Real.sin ϑ < 0 := (hwin ϑ hϑ'.1 hϑ'.2).1
      have h5 : (0:ℝ) < (Real.sin ϑ)^2 := by
        have h6 : Real.sin ϑ ≠ 0 := ne_of_lt hsin
        positivity
      exact div_pos hz₀ h5
  have hstarwin : ϑstar ∈ Set.Icc ϑminus ϑplus := by
    constructor
    · rw [hϑminusdef]
      linarith
    · rw [hϑplusdef]
      linarith
  have hϑminus0' : 0 < ϑminus := by
    rw [hϑminusdef]
    linarith [hϑstarmem.1, Real.pi_pos, hεle1]
  have hϑplus2π' : ϑplus < 2*Real.pi := by
    rw [hϑplusdef]
    linarith [hεle2, hεpos]
  have hpolar' : q - z₀ = ((‖q - z₀‖ : ℝ) : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := by
    rw [← htstardef]
    exact hpolar
  -- Packaging.
  refine ⟨ϑstar, ϑminus, ϑplus, hϑstarmem, ⟨hϑminus0', ?_, ?_, hϑplus2π'⟩,
    hradstar, ?_, hpolar', ?_, ?_⟩
  · rw [hϑminusdef]
    linarith [hεpos]
  · rw [hϑplusdef]
    linarith [hεpos]
  · rw [hradstar, ← hpolar']
    ring
  · intro ϑ h1 h2
    have hsin : Real.sin ϑ < 0 := (hwin ϑ h1 h2).1
    have h3 : z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) = η ϑ := by
      rw [hradwin ϑ h1 h2]
    rw [h3]
    exact hηim ϑ hsin
  · intro ϑ ϑ' h1 h2 h3
    have hsin : Real.sin ϑ < 0 := (hwin ϑ h1 (by linarith)).1
    have hsin' : Real.sin ϑ' < 0 := (hwin ϑ' (by linarith) h3).1
    have h4 : z₀ + ((rad ϑ : ℝ) : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) = η ϑ := by
      rw [hradwin ϑ h1 (by linarith)]
    have h5 : z₀ + ((rad ϑ' : ℝ) : ℂ) * Complex.exp ((ϑ' : ℂ) * Complex.I) = η ϑ' := by
      rw [hradwin ϑ' (by linarith) h3]
    rw [h4, h5, hηre ϑ hsin, hηre ϑ' hsin']
    exact hXmono ⟨h1, by linarith⟩ ⟨by linarith, h3⟩ h2

/-- Stage F4: the principal branch shift across the negative imaginary side: for `w` in
the open upper half plane, `log w = log (-w) + πi`. -/
theorem log_branch_plus {w : ℂ} (hw : w ≠ 0) (him : 0 < w.im) :
    Complex.log w = Complex.log (-w) + Real.pi * Complex.I := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw
  have hd1 : Complex.exp (Complex.log w
      - (Complex.log (-w) + Real.pi * Complex.I)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hw, Complex.exp_log hnw]
    have h1 : Complex.exp (Real.pi * Complex.I) = -1 := by
      have := Complex.exp_pi_mul_I
      exact_mod_cast this
    rw [h1]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hd1
  have harg1 : 0 < Complex.arg w := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr (le_of_lt him)) with h | h
    · exact h
    · exfalso
      have h1 := Complex.norm_mul_exp_arg_mul_I w
      rw [← h] at h1
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h1
      have h2 : w.im = 0 := by
        rw [← h1]
        simp
      linarith
  have harg2 : Complex.arg w < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi w) with h | h
    · exact h
    · exfalso
      have h1 := Complex.arg_eq_pi_iff.mp h
      linarith [h1.2, him]
  have harg3 : Complex.arg (-w) < 0 := by
    rw [Complex.arg_neg_iff, Complex.neg_im]
    linarith
  have harg4 : -Real.pi < Complex.arg (-w) := Complex.neg_pi_lt_arg _
  have him_eq : (Complex.log w - (Complex.log (-w) + Real.pi * Complex.I)).im
      = Complex.arg w - Complex.arg (-w) - Real.pi := by
    simp only [Complex.sub_im, Complex.add_im, Complex.log_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hn_im : Complex.arg w - Complex.arg (-w) - Real.pi = (n : ℝ) * (2 * Real.pi) := by
    have h2 := congrArg Complex.im hn
    rw [him_eq] at h2
    simpa [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] using h2
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · exfalso
      have h7 : (n:ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      nlinarith
    · exact h
    · exfalso
      have h7 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith
  rw [hn0] at hn
  simp at hn
  linear_combination hn

/-- Stage F4′: the mirrored branch shift: for `w` in the open lower half plane,
`log w = log (-w) - πi`. -/
theorem log_branch_minus {w : ℂ} (hw : w ≠ 0) (him : w.im < 0) :
    Complex.log w = Complex.log (-w) - Real.pi * Complex.I := by
  have h1 := log_branch_plus (neg_ne_zero.mpr hw)
    (by rw [Complex.neg_im]; linarith : 0 < (-w).im)
  rw [neg_neg] at h1
  linear_combination -h1

-- The winding computation around the half-disc contour is one long elaboration; the
-- raised budget is required.
set_option maxHeartbeats 400000 in
-- The half-plane preservation proof assembles the contour, window, and winding stages;
-- the single-declaration elaboration exceeds the default heartbeat budget.
/-- Stage F ([HALF]): the normalized solution of a Teichmüller representative preserves
the upper half plane. The lower branch of the half-plane dichotomy is excluded by a
winding-number computation: the image of a small circle winds `+1` (sense preservation),
while the image of the half-disc contour, whose interior pieces land in the closed lower
half plane far from the base point, winds `-1`. -/
theorem teichRep_w_im_pos {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (u : TeichRep Γ₀) : ∀ z : ℂ, 0 < z.im → 0 < (u.w z).im := by
  classical
  rcases u.w_halfPlane_dichotomy with ⟨hpos, _⟩ | ⟨hneg, _⟩
  · exact hpos
  exfalso
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hwqc : IsQCAnalytic u.w u.b := u.w_isQCAnalytic
  have hwcont : Continuous u.w := hwqc.1.1.continuous
  have hwinj : Function.Injective u.w := hwqc.injective
  set h : ℂ ≃ₜ ℂ := hwqc.1.1.homeomorph u.w with hhdef
  have hhap : ∀ z : ℂ, h z = u.w z := fun z =>
    IsHomeomorph.homeomorph_apply u.w hwqc.1.1 z
  set winv : ℂ → ℂ := ⇑h.symm with hwinvdef
  have hwinv2 : ∀ z : ℂ, u.w (winv z) = z := by
    intro z
    rw [hwinvdef, ← hhap (h.symm z)]
    exact h.apply_symm_apply z
  have hwinv1 : ∀ z : ℂ, winv (u.w z) = z := by
    intro z
    refine hwinj ?_
    rw [hwinv2 (u.w z)]
  -- Real values only at real points.
  have hreal : ∀ z : ℂ, (u.w z).im = 0 → z.im = 0 := by
    intro z h0
    obtain ⟨t, ht⟩ := u.boundary_surjective (u.w z).re
    have htz : u.w (t : ℂ) = u.w z := by
      rw [u.w_ofReal t, ht]
      exact Complex.ext (by simp) (by simp [h0])
    have hz := hwinj htz
    rw [← hz]
    simp
  -- The winding point: a sense-preserving centre in the upper half plane.
  have hsp : SensePreserving u.w := SensePreserving.of_orientationPreservingHomeo hwqc.1
  set Ω : Set ℂ := {z : ℂ | 0 < z.im} with hΩdef
  have hΩopen : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_im
  have hΩpos : (0:ℝ≥0∞) < volume Ω := by
    refine hΩopen.measure_pos volume ⟨Complex.I, ?_⟩
    simp [hΩdef]
  obtain ⟨z₀, hz₀Ω, hz₀P⟩ : ∃ z₀ : ℂ, z₀ ∈ Ω ∧
      (∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), ∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ)
          = u.w (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - u.w z₀) ∧
        L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I) := by
    have h1 := hsp.2
    set Nset : Set ℂ := {z₀ : ℂ | ¬ (∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ)
          = u.w (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - u.w z₀) ∧
        L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I)} with hNdef
    have h2 : volume Nset = 0 := MeasureTheory.ae_iff.mp h1
    have h3 : (Ω \ Nset).Nonempty := by
      refine MeasureTheory.nonempty_of_measure_ne_zero (μ := volume) ?_
      intro h0
      have h4 : volume Ω ≤ volume (Ω \ Nset) + volume Nset := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro z hz
        by_cases hzN : z ∈ Nset
        · exact Or.inr hzN
        · exact Or.inl ⟨hz, hzN⟩
      rw [h0, h2, add_zero] at h4
      exact absurd (le_antisymm h4 (zero_le _)) (ne_of_gt hΩpos)
    obtain ⟨z₀, hz₀Ω, hz₀N⟩ := h3
    exact ⟨z₀, hz₀Ω, not_not.mp hz₀N⟩
  have hz₀im : 0 < z₀.im := hz₀Ω
  -- The radius for the reference circle.
  obtain ⟨r, ⟨hLpack, hrlt⟩, hrpos'⟩ :=
    ((hz₀P.and (nhdsWithin_le_nhds (gt_mem_nhds hz₀im))).and
      self_mem_nhdsWithin).exists
  have hrpos : (0:ℝ) < r := hrpos'
  obtain ⟨L₀, hL₀c, hL₀e, hL₀inc⟩ := hLpack
  -- The image point and its preimage on the real axis.
  set p : ℂ := u.w z₀ with hpdef
  have hpim : p.im < 0 := hneg z₀ hz₀im
  set qhat : ℂ := (p.re : ℂ) with hqhatdef
  set qstar : ℂ := winv qhat with hqstardef
  have hqstarW : u.w qstar = qhat := hwinv2 qhat
  have hqstarim : qstar.im = 0 := by
    refine hreal qstar ?_
    rw [hqstarW, hqhatdef]
    simp
  have hqstarne : qstar - z₀ ≠ 0 := by
    intro h0
    have h1 : qstar = z₀ := by
      have := sub_eq_zero.mp h0
      exact this
    rw [h1] at hqstarim
    rw [hqstarim] at hz₀im
    exact lt_irrefl 0 hz₀im
  -- The outer radius: far points have far images.
  obtain ⟨R₀, hR₀⟩ := (((isCompact_closedBall (0:ℂ) (‖p‖ + 1)).image
    h.symm.continuous).isBounded).subset_closedBall 0
  set R : ℝ := max (max (R₀ + 1) (‖z₀‖ + 2)) (‖qstar‖ + 1) with hRdef
  have hRz₀ : ‖z₀‖ + 1 < R := by
    have h1 : ‖z₀‖ + 2 ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hRq : ‖qstar‖ < R := by
    have h1 : ‖qstar‖ + 1 ≤ R := le_max_right _ _
    linarith
  have hfar : ∀ w : ℂ, ‖w‖ = R → ‖p‖ + 1 < ‖u.w w‖ := by
    intro w hw
    by_contra hle
    push Not at hle
    have h1 : u.w w ∈ Metric.closedBall (0:ℂ) (‖p‖ + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hle
    have h2 : w ∈ ⇑h.symm '' Metric.closedBall (0:ℂ) (‖p‖ + 1) := by
      refine ⟨u.w w, h1, ?_⟩
      exact hwinv1 w
    have h3 := hR₀ h2
    rw [Metric.mem_closedBall, dist_zero_right] at h3
    have h4 : R₀ + 1 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hw] at h3
    linarith
  -- The half-disc contour.
  obtain ⟨rad, hradc, hradpos, hradfr, hraduniq⟩ := halfdisc_radial z₀ hz₀im R hRz₀
  set γ1 : ℝ → ℂ := fun ϑ => z₀ + (rad ϑ : ℂ) * Complex.exp (ϑ * Complex.I) with hγ1def
  set Λ : ℝ → ℂ := fun ϑ => u.w (γ1 ϑ) with hΛdef
  -- The interpolating family and its lift.
  set H : ℝ → ℝ → ℂ := fun s ϑ =>
    u.w (z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)) - p
    with hHdef
  have hρpos : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ ϑ : ℝ, 0 < (1-s)*r + s*rad ϑ := by
    intro s hs ϑ
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0]
      simpa using hrpos
    · have h1 : 0 < s * rad ϑ := mul_pos h0 (hradpos ϑ)
      have h2 : 0 ≤ (1-s)*r := mul_nonneg (by linarith [hs.2]) (le_of_lt hrpos)
      linarith
  have hHcont : ContinuousOn (Function.uncurry H)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2*Real.pi)) := by
    refine Continuous.continuousOn ?_
    refine Continuous.sub ?_ continuous_const
    refine hwcont.comp ?_
    refine Continuous.add continuous_const ?_
    refine Continuous.mul ?_ ?_
    · refine Complex.continuous_ofReal.comp ?_
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub continuous_fst).mul continuous_const
      · exact continuous_fst.mul (hradc.comp continuous_snd)
    · refine Complex.continuous_exp.comp ?_
      exact (Complex.continuous_ofReal.comp continuous_snd).mul continuous_const
  have hHne : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), H s ϑ ≠ 0 := by
    intro s hs ϑ _
    rw [hHdef]
    intro h0
    have h1 : u.w (z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I))
        = u.w z₀ := by
      rw [← hpdef]
      exact sub_eq_zero.mp h0
    have h2 := hwinj h1
    have h3 : (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I) = 0 := by
      have h4 : z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)
          - z₀ = 0 := by
        rw [h2]
        ring
      calc (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I)
          = z₀ + (((1-s)*r + s*rad ϑ : ℝ) : ℂ) * Complex.exp (ϑ * Complex.I) - z₀ := by
            ring
        _ = 0 := h4
    rcases mul_eq_zero.mp h3 with h5 | h5
    · have h6 : ((1-s)*r + s*rad ϑ : ℝ) = 0 := by exact_mod_cast h5
      have h7 := hρpos s hs ϑ
      rw [h6] at h7
      exact lt_irrefl 0 h7
    · exact Complex.exp_ne_zero _ h5
  obtain ⟨L, hLc, hLe⟩ := continuous_log_lift_param_of_continuous_ne_zero
    (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ 2*Real.pi) H hHcont hHne
  -- The endpoint increments are constant in the parameter.
  have hmemθ : ∀ ϑ : ℝ, ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi) → True := fun _ _ => trivial
  have h2πmem : (2*Real.pi : ℝ) ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    Set.right_mem_Icc.mpr (by positivity)
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    Set.left_mem_Icc.mpr (by positivity)
  have hexp02π : Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((0:ℝ) : ℂ) * Complex.I) := by
    push_cast
    rw [Complex.exp_two_pi_mul_I]
    simp
  have hradper : rad 0 = rad (2*Real.pi) := by
    obtain ⟨ha1, ha2, ha3⟩ := hradfr (2*Real.pi)
    refine hraduniq 0 (rad (2*Real.pi)) (hradpos _) ?_ ?_ ?_
    · rw [show Complex.exp (((0:ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I) from hexp02π.symm]
      exact ha1
    · rw [show Complex.exp (((0:ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I) from hexp02π.symm]
      exact ha2
    · rw [show Complex.exp (((0:ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I) from hexp02π.symm]
      intro hstrict
      rcases ha3 with h | h
      · exact absurd h (ne_of_lt hstrict.1)
      · exact absurd h (ne_of_gt hstrict.2)
  have hHper : ∀ s ∈ Set.Icc (0:ℝ) 1, H s (2*Real.pi) = H s 0 := by
    intro s _
    change u.w (z₀ + (((1-s)*r + s*rad (2*Real.pi) : ℝ) : ℂ)
        * Complex.exp (((2*Real.pi : ℝ) : ℂ) * Complex.I)) - p
      = u.w (z₀ + (((1-s)*r + s*rad 0 : ℝ) : ℂ)
        * Complex.exp (((0:ℝ) : ℂ) * Complex.I)) - p
    rw [hexp02π, ← hradper]
  have h0mem1 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
  have h1mem1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.right_mem_Icc.mpr (by norm_num)
  -- The endpoint increment is constant along the interpolation.
  set Inc : ℝ → ℂ := fun s => L s (2*Real.pi) - L s 0 with hIncdef
  have hIncint : ∀ s ∈ Set.Icc (0:ℝ) 1, ∃ K : ℤ,
      Inc s = (K : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    have h1 : Complex.exp (L s 0) = Complex.exp (L s (2*Real.pi)) := by
      rw [hLe s hs 0 h0mem, hLe s hs _ h2πmem, hHper s hs]
    exact winding_lift_integer_coeff (L s) h1
  have hInccont : ContinuousOn Inc (Set.Icc (0:ℝ) 1) := by
    refine Continuous.continuousOn ?_
    refine Continuous.sub ?_ ?_
    · exact hLc.comp (continuous_id.prodMk continuous_const)
    · exact hLc.comp (continuous_id.prodMk continuous_const)
  have hIncconst : Inc 0 = Inc 1 :=
    disc_const (by norm_num) hInccont hIncint
  -- The base increment is `2πi`, by uniqueness of lifts against the reference lift.
  have hH0 : ∀ ϑ : ℝ, H 0 ϑ
      = u.w (z₀ + (r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)) - u.w z₀ := by
    intro ϑ
    change u.w (z₀ + (((1-0)*r + 0*rad ϑ : ℝ) : ℂ) * Complex.exp (↑ϑ * Complex.I)) - p
      = u.w (z₀ + (r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)) - u.w z₀
    rw [hpdef]
    norm_num
  have hI0 : Inc 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    have hd_int : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), ∃ K : ℤ,
        (L 0 ϑ - L₀ ϑ) = (K : ℂ) * (2 * Real.pi * Complex.I) := by
      intro ϑ hϑ
      have h1 : Complex.exp (L₀ ϑ) = Complex.exp (L 0 ϑ) := by
        rw [hLe 0 h0mem1 ϑ hϑ, hL₀e ϑ, hH0 ϑ]
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
      refine ⟨-n, ?_⟩
      rw [hn]
      push_cast
      ring
    have hdc : ContinuousOn (fun ϑ => L 0 ϑ - L₀ ϑ) (Set.Icc (0:ℝ) (2*Real.pi)) := by
      refine Continuous.continuousOn ?_
      exact (hLc.comp (continuous_const.prodMk continuous_id)).sub hL₀c
    have hd := disc_const (by positivity) hdc hd_int
    have h2 : Inc 0 = (L 0 (2*Real.pi) - L₀ (2*Real.pi)) - (L 0 0 - L₀ 0)
        + (L₀ (2*Real.pi) - L₀ 0) := by
      rw [hIncdef]
      ring
    rw [h2, ← hd, hL₀inc]
    ring
  -- The crossing angle, from the window lemma.
  obtain ⟨ϑstar, ϑminus, ϑplus, hϑstarmem, hwinb, hradstar0, hγ1stareq, hpolar0,
    hwinim, hwinmono⟩ :=
    halfdisc_window z₀ hz₀im R rad hradpos hraduniq qstar hqstarim hRq hqstarne
  set tstar : ℝ := ‖qstar - z₀‖ with htstardef
  have htstarpos : 0 < tstar := norm_pos_iff.mpr hqstarne
  have hradstar : rad ϑstar = tstar := hradstar0
  have hpolar : qstar - z₀ = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) :=
    hpolar0
  have hγ1star : γ1 ϑstar = qstar := hγ1stareq
  have hΛstar : Λ ϑstar = qhat := by
    change u.w (γ1 ϑstar) = qhat
    rw [hγ1star]
    exact hqstarW
  have hγpos : ∀ ϑ : ℝ, 0 ≤ (γ1 ϑ).im ∧ ‖γ1 ϑ‖ ≤ R ∧
      ((γ1 ϑ).im = 0 ∨ ‖γ1 ϑ‖ = R) := by
    intro ϑ
    obtain ⟨h1, h2, h3⟩ := hradfr ϑ
    refine ⟨h2, h1, ?_⟩
    rcases h3 with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hΛim : ∀ ϑ : ℝ, (Λ ϑ).im ≤ 0 := by
    intro ϑ
    rcases lt_or_eq_of_le (hγpos ϑ).1 with h | h
    · exact le_of_lt (hneg _ h)
    · have h1 : γ1 ϑ = ((γ1 ϑ).re : ℂ) := Complex.ext (by simp) (by simp [h.symm])
      rw [hΛdef]
      change (u.w (γ1 ϑ)).im ≤ 0
      rw [h1]
      rw [u.w_real (γ1 ϑ).re]
  have hΛreal : ∀ ϑ : ℝ, (γ1 ϑ).im = 0 → (Λ ϑ).im = 0 := by
    intro ϑ h
    have h1 : γ1 ϑ = ((γ1 ϑ).re : ℂ) := Complex.ext (by simp) (by simp [h.symm])
    rw [hΛdef]
    change (u.w (γ1 ϑ)).im = 0
    rw [h1]
    exact u.w_real (γ1 ϑ).re
  have hΛfar : ∀ ϑ : ℝ, ‖γ1 ϑ‖ = R → ‖p‖ + 1 < ‖Λ ϑ‖ := fun ϑ h => hfar _ h
  -- Off-ray characterization: the ray only meets the image at the crossing angle.
  have honray : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), ϑ ≠ ϑstar →
      ¬((Λ ϑ - p).re = 0 ∧ 0 ≤ (Λ ϑ - p).im) := by
    intro ϑ hϑ hne hray
    have him : 0 ≤ (Λ ϑ).im - p.im := by
      have := hray.2
      rwa [Complex.sub_im] at this
    have hre : (Λ ϑ).re = p.re := by
      have := hray.1
      rw [Complex.sub_re] at this
      linarith
    rcases (hγpos ϑ).2.2 with hγreal | hγfar
    · -- Real piece: forces the crossing point, contradicting `ϑ ≠ ϑstar`.
      have hΛr : (Λ ϑ).im = 0 := hΛreal ϑ hγreal
      have hΛeq : Λ ϑ = qhat := by
        refine Complex.ext ?_ ?_
        · rw [hre, hqhatdef]
          simp
        · rw [hΛr, hqhatdef]
          simp
      have hγeq : γ1 ϑ = qstar := by
        refine hwinj ?_
        have h1 : u.w (γ1 ϑ) = qhat := hΛeq
        rw [h1, hqstarW]
      have hprod : (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)
          = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := by
        have h2 : z₀ + (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) = qstar := hγeq
        calc (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)
            = z₀ + (rad ϑ : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) - z₀ := by ring
          _ = qstar - z₀ := by rw [h2]
          _ = (tstar : ℂ) * Complex.exp ((ϑstar : ℂ) * Complex.I) := hpolar
      have hradt : rad ϑ = tstar := by
        have h3 := congrArg norm hprod
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
          mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (hradpos ϑ), abs_of_pos htstarpos] at h3
        exact h3
      have hexpeq : Complex.exp ((ϑ : ℂ) * Complex.I)
          = Complex.exp ((ϑstar : ℂ) * Complex.I) := by
        rw [hradt] at hprod
        refine mul_left_cancel₀ ?_ hprod
        exact_mod_cast ne_of_gt htstarpos
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexpeq
      have h5 : ϑ = ϑstar + n * (2*Real.pi) := by
        have h6 := congrArg Complex.im hn
        simpa [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] using h6
      have hn0 : n = 0 := by
        rcases lt_trichotomy n 0 with h | h | h
        · exfalso
          have h7 : (n:ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
          have h8 := hϑ.1
          nlinarith [hϑstarmem.2, hπ]
        · exact h
        · exfalso
          have h7 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
          have h8 := hϑ.2
          nlinarith [hϑstarmem.1, hπ]
      rw [hn0] at h5
      push_cast at h5
      have h9 : ϑ = ϑstar := by linarith [h5]
      exact hne h9
    · -- Far piece: the ray segment lies inside the ball of radius `‖p‖`.
      have hf := hΛfar ϑ hγfar
      have h1 : ‖Λ ϑ‖^2 = (Λ ϑ).re^2 + (Λ ϑ).im^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have h2 : ‖p‖^2 = p.re^2 + p.im^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have h3 := hΛim ϑ
      have h4 : p.im ≤ (Λ ϑ).im := by linarith [him]
      have h5 : (Λ ϑ).im^2 ≤ p.im^2 := by nlinarith
      have hb : (0:ℝ) < ‖p‖ + 1 := by positivity
      have h6 : (‖p‖+1)^2 < ‖Λ ϑ‖^2 := by nlinarith
      have h7 : ‖Λ ϑ‖^2 ≤ ‖p‖^2 := by
        rw [h1, h2, hre]
        linarith
      nlinarith [norm_nonneg p]
  -- The real-hit window around the crossing angle.
  -- Consequences of the window structure for the image curve.
  have hΛwinim : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus → (Λ ϑ).im = 0 := by
    intro ϑ h1 h2
    exact hΛreal ϑ (hwinim ϑ h1 h2)
  have hγre : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
      Λ ϑ = ((u.boundary ((γ1 ϑ).re) : ℝ) : ℂ) := by
    intro ϑ h1 h2
    have h3 : γ1 ϑ = (((γ1 ϑ).re : ℝ) : ℂ) := by
      refine Complex.ext (by simp) ?_
      have h4 : (γ1 ϑ).im = 0 := hwinim ϑ h1 h2
      rw [h4]
      simp
    change u.w (γ1 ϑ) = ((u.boundary ((γ1 ϑ).re) : ℝ) : ℂ)
    conv_lhs => rw [h3]
    rw [u.w_ofReal]
  have hsw1 : ϑminus ≤ ϑstar := le_of_lt hwinb.2.1
  have hsw2 : ϑstar ≤ ϑplus := le_of_lt hwinb.2.2.1
  have hbstar : u.boundary ((γ1 ϑstar).re) = p.re := by
    have h1 : ((u.boundary ((γ1 ϑstar).re) : ℝ) : ℂ) = qhat := by
      rw [← hγre ϑstar hsw1 hsw2, hΛstar]
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re, hqhatdef] at h2
    simpa using h2
  have hxileft : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ < ϑstar → (Λ ϑ).re < p.re := by
    intro ϑ h1 h2
    have h3 := hwinmono ϑ ϑstar h1 h2 hsw2
    have h4 : (γ1 ϑ).re < (γ1 ϑstar).re := h3
    have h5 := u.boundary_strictMono h4
    rw [hγre ϑ h1 (by linarith), Complex.ofReal_re, ← hbstar]
    exact h5
  have hxiright : ∀ ϑ : ℝ, ϑstar < ϑ → ϑ ≤ ϑplus → p.re < (Λ ϑ).re := by
    intro ϑ h1 h2
    have h3 := hwinmono ϑstar ϑ hsw1 h1 h2
    have h4 : (γ1 ϑstar).re < (γ1 ϑ).re := h3
    have h5 := u.boundary_strictMono h4
    rw [hγre ϑ (by linarith) h2, Complex.ofReal_re, ← hbstar]
    exact h5
  have hϑminus0 : 0 < ϑminus := hwinb.1
  have hϑplus2π : ϑplus < 2*Real.pi := hwinb.2.2.2
  -- The lift at `s = 1` and the branch logarithms.
  have hH1 : ∀ ϑ : ℝ, H 1 ϑ = Λ ϑ - p := by
    intro ϑ
    change u.w (z₀ + (((1-1)*r + 1*rad ϑ : ℝ) : ℂ) * Complex.exp (↑ϑ * Complex.I)) - p
      = Λ ϑ - p
    have h1 : ((1-1)*r + 1*rad ϑ : ℝ) = rad ϑ := by ring
    rw [h1]
  have hΛcont : Continuous Λ := by
    change Continuous fun ϑ => u.w (γ1 ϑ)
    refine hwcont.comp ?_
    refine Continuous.add continuous_const ?_
    exact (Complex.continuous_ofReal.comp hradc).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
  have hL1cont : Continuous (fun ϑ => L 1 ϑ) :=
    hLc.comp (continuous_const.prodMk continuous_id)
  have hL1exp : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (L 1 ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    rw [hLe 1 h1mem1 ϑ hϑ, hH1 ϑ]
  have hΛne : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), Λ ϑ - p ≠ 0 := by
    intro ϑ hϑ
    rw [← hH1 ϑ]
    exact hHne 1 h1mem1 ϑ hϑ
  have hslit : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi), ϑ ≠ ϑstar →
      Complex.I * (Λ ϑ - p) ∈ Complex.slitPlane := by
    intro ϑ hϑ hne
    rw [Complex.mem_slitPlane_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h3 : (Complex.I * (Λ ϑ - p)).re = -(Λ ϑ - p).im := by
      rw [Complex.mul_re]
      simp
    have h4 : (Complex.I * (Λ ϑ - p)).im = (Λ ϑ - p).re := by
      rw [Complex.mul_im]
      simp
    refine honray ϑ hϑ hne ⟨?_, ?_⟩
    · rw [← h4]
      exact h2
    · rw [h3] at h1
      linarith
  set ℓb : ℝ → ℂ := fun ϑ =>
    Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I with hℓbdef
  set ℓp : ℝ → ℂ := fun ϑ =>
    Complex.log (-(Complex.I * (Λ ϑ - p))) + Real.pi * Complex.I
      - Complex.log Complex.I with hℓpdef
  set ℓm : ℝ → ℂ := fun ϑ =>
    Complex.log (-(Complex.I * (Λ ϑ - p))) - Real.pi * Complex.I
      - Complex.log Complex.I with hℓmdef
  have hexpℓb : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (ℓb ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    change Complex.exp (Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I)
      = Λ ϑ - p
    rw [Complex.exp_sub, Complex.exp_log (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ)),
      Complex.exp_log Complex.I_ne_zero]
    field_simp
  have hexpℓp : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (ℓp ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    change Complex.exp (Complex.log (-(Complex.I * (Λ ϑ - p))) + Real.pi * Complex.I
      - Complex.log Complex.I) = Λ ϑ - p
    rw [Complex.exp_sub, Complex.exp_add,
      Complex.exp_log (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ))),
      Complex.exp_log Complex.I_ne_zero]
    have h1 : Complex.exp (Real.pi * Complex.I) = -1 := by
      have := Complex.exp_pi_mul_I
      exact_mod_cast this
    rw [h1]
    field_simp
  have hexpℓm : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      Complex.exp (ℓm ϑ) = Λ ϑ - p := by
    intro ϑ hϑ
    change Complex.exp (Complex.log (-(Complex.I * (Λ ϑ - p))) - Real.pi * Complex.I
      - Complex.log Complex.I) = Λ ϑ - p
    rw [Complex.exp_sub, Complex.exp_sub,
      Complex.exp_log (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ))),
      Complex.exp_log Complex.I_ne_zero]
    have h1 : Complex.exp (Real.pi * Complex.I) = -1 := by
      have := Complex.exp_pi_mul_I
      exact_mod_cast this
    rw [h1]
    field_simp
  -- Branch matching on the two half-windows.
  have hbranchp : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      0 < (Complex.I * (Λ ϑ - p)).im → ℓb ϑ = ℓp ϑ := by
    intro ϑ hϑ him
    have h1 := log_branch_plus
      (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ)) him
    change Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I
      = Complex.log (-(Complex.I * (Λ ϑ - p))) + Real.pi * Complex.I
        - Complex.log Complex.I
    rw [h1]
  have hbranchm : ∀ ϑ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      (Complex.I * (Λ ϑ - p)).im < 0 → ℓb ϑ = ℓm ϑ := by
    intro ϑ hϑ him
    have h1 := log_branch_minus
      (mul_ne_zero Complex.I_ne_zero (hΛne ϑ hϑ)) him
    change Complex.log (Complex.I * (Λ ϑ - p)) - Complex.log Complex.I
      = Complex.log (-(Complex.I * (Λ ϑ - p))) - Real.pi * Complex.I
        - Complex.log Complex.I
    rw [h1]
  have hIim : ∀ ϑ : ℝ, (Complex.I * (Λ ϑ - p)).im = (Λ ϑ).re - p.re := by
    intro ϑ
    rw [Complex.mul_im]
    simp [Complex.sub_re]
  have hmIcc : ϑminus ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    ⟨le_of_lt hϑminus0, by linarith [hsw1, hsw2, hϑplus2π]⟩
  have hpIcc : ϑplus ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
    ⟨by linarith [hϑminus0, hsw1, hsw2], le_of_lt hϑplus2π⟩
  have hsubp : ℓb ϑplus = ℓp ϑplus := by
    refine hbranchp ϑplus hpIcc ?_
    rw [hIim]
    linarith [hxiright ϑplus hwinb.2.2.1 (le_refl ϑplus)]
  have hsubm : ℓb ϑminus = ℓm ϑminus := by
    refine hbranchm ϑminus hmIcc ?_
    rw [hIim]
    linarith [hxileft ϑminus (le_refl ϑminus) hwinb.2.1]
  -- Continuity of the branch pieces.
  have hℓbcont : ∀ (a b : ℝ), 0 ≤ a → b ≤ 2*Real.pi →
      (∀ ϑ, a ≤ ϑ → ϑ ≤ b → ϑ ≠ ϑstar) → ContinuousOn ℓb (Set.Icc a b) := by
    intro a b ha hb hne ϑ hϑ
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun ϑ => Complex.I * (Λ ϑ - p)) ϑ :=
      (continuous_const.mul (hΛcont.sub continuous_const)).continuousAt
    have h2 := ContinuousAt.clog h1
      (hslit ϑ ⟨le_trans ha hϑ.1, le_trans hϑ.2 hb⟩ (hne ϑ hϑ.1 hϑ.2))
    exact h2.sub continuousAt_const
  have hslitm : ∀ ϑ : ℝ, ϑminus ≤ ϑ → ϑ ≤ ϑplus →
      -(Complex.I * (Λ ϑ - p)) ∈ Complex.slitPlane := by
    intro ϑ h1 h2
    rw [Complex.mem_slitPlane_iff]
    left
    have h3 : (-(Complex.I * (Λ ϑ - p))).re = (Λ ϑ - p).im := by
      rw [Complex.neg_re, Complex.mul_re]
      simp
    rw [h3, Complex.sub_im, hΛwinim ϑ h1 h2]
    linarith [hpim]
  have hℓpcont : ContinuousOn ℓp (Set.Icc ϑstar ϑplus) := by
    intro ϑ hϑ
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun ϑ => -(Complex.I * (Λ ϑ - p))) ϑ :=
      ((continuous_const.mul (hΛcont.sub continuous_const)).neg).continuousAt
    have h2 := ContinuousAt.clog h1 (hslitm ϑ (le_trans hsw1 hϑ.1) hϑ.2)
    exact (h2.add continuousAt_const).sub continuousAt_const
  have hℓmcont : ContinuousOn ℓm (Set.Icc ϑminus ϑstar) := by
    intro ϑ hϑ
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun ϑ => -(Complex.I * (Λ ϑ - p))) ϑ :=
      ((continuous_const.mul (hΛcont.sub continuous_const)).neg).continuousAt
    have h2 := ContinuousAt.clog h1 (hslitm ϑ hϑ.1 (le_trans hϑ.2 hsw2))
    exact (h2.sub continuousAt_const).sub continuousAt_const
  -- Integer-valued quotients against the lift.
  have hint4 : ∀ (G : ℝ → ℂ) (a b : ℝ), 0 ≤ a → b ≤ 2*Real.pi →
      (∀ ϑ, a ≤ ϑ → ϑ ≤ b → Complex.exp (G ϑ) = Λ ϑ - p) →
      ∀ s ∈ Set.Icc a b, ∃ K : ℤ, L 1 s - G s = (K:ℂ) * (2 * Real.pi * Complex.I) := by
    intro G a b ha hb hG s hs
    have hsIcc : s ∈ Set.Icc (0:ℝ) (2*Real.pi) :=
      ⟨le_trans ha hs.1, le_trans hs.2 hb⟩
    have h1 : Complex.exp (L 1 s - G s) = 1 := by
      rw [Complex.exp_sub, hL1exp s hsIcc, hG s hs.1 hs.2]
      exact div_self (hΛne s hsIcc)
    exact Complex.exp_eq_one_iff.mp h1
  -- The four piece constancies.
  have hp1 : L 1 0 - ℓb 0 = L 1 ϑminus - ℓb ϑminus := by
    refine disc_const (le_of_lt hϑminus0)
      ((hL1cont.continuousOn).sub (hℓbcont 0 ϑminus (le_refl 0) hmIcc.2 ?_)) ?_
    · intro ϑ h1 h2 h3
      rw [h3] at h2
      linarith [hwinb.2.1]
    · exact hint4 ℓb 0 ϑminus (le_refl 0) hmIcc.2
        (fun ϑ h1 h2 => hexpℓb ϑ ⟨h1, by linarith [hmIcc.2]⟩)
  have hp2 : L 1 ϑminus - ℓm ϑminus = L 1 ϑstar - ℓm ϑstar := by
    refine disc_const hsw1 ((hL1cont.continuousOn).sub hℓmcont) ?_
    exact hint4 ℓm ϑminus ϑstar (le_of_lt hϑminus0)
      (by linarith [hϑstarmem.2])
      (fun ϑ h1 h2 => hexpℓm ϑ ⟨by linarith [hϑminus0], by linarith [hϑstarmem.2]⟩)
  have hp3 : L 1 ϑstar - ℓp ϑstar = L 1 ϑplus - ℓp ϑplus := by
    refine disc_const hsw2 ((hL1cont.continuousOn).sub hℓpcont) ?_
    exact hint4 ℓp ϑstar ϑplus (by linarith [hϑminus0, hsw1])
      (le_of_lt hϑplus2π)
      (fun ϑ h1 h2 => hexpℓp ϑ ⟨by linarith [hϑminus0, hsw1], by linarith [hϑplus2π]⟩)
  have hp4 : L 1 ϑplus - ℓb ϑplus = L 1 (2*Real.pi) - ℓb (2*Real.pi) := by
    refine disc_const (le_of_lt hϑplus2π)
      ((hL1cont.continuousOn).sub (hℓbcont ϑplus (2*Real.pi) hpIcc.1 (le_refl _) ?_)) ?_
    · intro ϑ h1 h2 h3
      rw [h3] at h1
      linarith [hwinb.2.2.1]
    · exact hint4 ℓb ϑplus (2*Real.pi) hpIcc.1 (le_refl _)
        (fun ϑ h1 h2 => hexpℓb ϑ ⟨le_trans hpIcc.1 h1, h2⟩)
  -- Periodicity of the base branch.
  have hΛper : Λ (2*Real.pi) = Λ 0 := by
    change u.w (γ1 (2*Real.pi)) = u.w (γ1 0)
    have h1 : γ1 (2*Real.pi) = γ1 0 := by
      change z₀ + (rad (2*Real.pi) : ℂ) * Complex.exp (((2*Real.pi:ℝ) : ℂ) * Complex.I)
        = z₀ + (rad 0 : ℂ) * Complex.exp (((0:ℝ) : ℂ) * Complex.I)
      rw [hexp02π, ← hradper]
    rw [h1]
  have hℓbper : ℓb (2*Real.pi) = ℓb 0 := by
    change Complex.log (Complex.I * (Λ (2*Real.pi) - p)) - Complex.log Complex.I
      = Complex.log (Complex.I * (Λ 0 - p)) - Complex.log Complex.I
    rw [hΛper]
  -- The endpoint increment at `s = 1`.
  have hInc1 : Inc 1 = -(2 * (Real.pi:ℂ) * Complex.I) := by
    have e5 : ℓm ϑstar - ℓp ϑstar = -(2*(Real.pi:ℂ)*Complex.I) := by
      change (Complex.log (-(Complex.I * (Λ ϑstar - p))) - Real.pi * Complex.I
          - Complex.log Complex.I)
        - (Complex.log (-(Complex.I * (Λ ϑstar - p))) + Real.pi * Complex.I
          - Complex.log Complex.I) = -(2*(Real.pi:ℂ)*Complex.I)
      ring
    have hIncdef1 : Inc 1 = L 1 (2*Real.pi) - L 1 0 := rfl
    rw [hIncdef1]
    linear_combination -hp4 - hp1 - hp3 - hp2 - hsubp + hℓbper + hsubm + e5
  -- The contradiction.
  have hcontra : (2 : ℂ) * Real.pi * Complex.I = -(2 * (Real.pi:ℂ) * Complex.I) := by
    calc (2 : ℂ) * Real.pi * Complex.I = Inc 0 := hI0.symm
      _ = Inc 1 := hIncconst
      _ = -(2 * (Real.pi:ℂ) * Complex.I) := hInc1
  have him2 := congrArg Complex.im hcontra
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_im, Complex.re_ofNat,
    Complex.im_ofNat] at him2
  nlinarith [hπ, him2]

/-- **Factorization.** If the normalized solution of a Teichmüller representative and an
upper-half-plane quasiconformal map solve the same Beltrami equation almost everywhere on
the upper half plane, they differ by a real Möbius map: their quotient is conformal by the
Weyl lemma and is a holomorphic self-homeomorphism of the upper half plane, hence Möbius. -/
theorem exists_sl2_factorization_of_eq_coeff
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (u : TeichRep Γ₀)
    {v vinv : ℂ → ℂ} {κ : ℝ} (_hκ : κ < 1) (hv : IsQCUpper v vinv κ)
    (hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar v z = u.b.μ z * dz v z) :
    ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → u.w z = moebiusMap R (v z) := by
  classical
  have hpos : ∀ z : ℂ, 0 < z.im → 0 < (u.w z).im := teichRep_w_im_pos u
  have hwqc : IsQCAnalytic u.w u.b := u.w_isQCAnalytic
  have hwcont : Continuous u.w := hwqc.1.1.continuous
  have hwinj : Function.Injective u.w := hwqc.injective
  set h : ℂ ≃ₜ ℂ := hwqc.1.1.homeomorph u.w with hhdef
  have hhap : ∀ z : ℂ, h z = u.w z := fun z =>
    IsHomeomorph.homeomorph_apply u.w hwqc.1.1 z
  set uinv : ℂ → ℂ := ⇑h.symm with huinvdef
  have huinvc : Continuous uinv := h.symm.continuous
  have hui2 : ∀ z : ℂ, u.w (uinv z) = z := by
    intro z
    rw [huinvdef, ← hhap (h.symm z)]
    exact h.apply_symm_apply z
  have hui1 : ∀ z : ℂ, uinv (u.w z) = z := by
    intro z
    refine hwinj ?_
    rw [hui2 (u.w z)]
  -- The inverse preserves the open upper half plane.
  have huinvpos : ∀ z : ℂ, 0 < z.im → 0 < (uinv z).im := by
    intro z hz
    rcases lt_trichotomy (uinv z).im 0 with hlt | heq | hgt
    · exfalso
      have h1 : 0 < (starRingEnd ℂ (uinv z)).im := by
        rw [Complex.conj_im]; linarith
      have h2 := hpos _ h1
      rw [u.w_conj, hui2 z, Complex.conj_im] at h2
      linarith
    · exfalso
      have h1 : ((uinv z).re : ℂ) = uinv z :=
        Complex.ext (by simp) (by simp [heq])
      have h4 := u.w_ofReal ((uinv z).re)
      rw [h1, hui2 z] at h4
      have h5 : z.im = 0 := by rw [h4]; simp
      linarith
    · exact hgt
  -- The composite `v ∘ uinv` is holomorphic on the upper half plane by the Weyl lemma.
  have hψholo : DifferentiableOn ℂ (fun w => v (uinv w)) {z : ℂ | 0 < z.im} :=
    composite_holomorphic u hv hcoeff hpos huinvc hui1 hui2
  have hψmaps : ∀ z : ℂ, 0 < z.im → 0 < (v (uinv z)).im := fun z hz =>
    hv.mapsTo _ (huinvpos z hz)
  have hθmaps : ∀ z : ℂ, 0 < z.im → 0 < (u.w (vinv z)).im := fun z hz =>
    hpos _ (hv.mapsTo' z hz)
  have hθψ : ∀ z : ℂ, 0 < z.im → u.w (vinv (v (uinv z))) = z := by
    intro z hz
    rw [hv.left_inv _ (huinvpos z hz), hui2 z]
  have hψθ : ∀ z : ℂ, 0 < z.im → v (uinv (u.w (vinv z))) = z := by
    intro z hz
    rw [hui1 (vinv z)]
    exact hv.right_inv z hz
  have hθcont : ContinuousOn (fun w => u.w (vinv w)) {z : ℂ | 0 < z.im} := by
    intro w hw
    exact (hwcont.continuousAt).comp_continuousWithinAt (hv.cont' w hw)
  obtain ⟨A, hA⟩ := holo_upper_selfmap_moebius (ψ := fun w => v (uinv w))
    (θ := fun w => u.w (vinv w)) hψholo hψmaps hθmaps hθψ hψθ hθcont
  refine ⟨A⁻¹, ?_⟩
  intro z hz
  have h1 : 0 < (u.w z).im := hpos z hz
  have h3 : v z = moebiusMap A (u.w z) := by
    have h4 := hA (u.w z) h1
    have h5 : (fun w => v (uinv w)) (u.w z) = v z := by
      change v (uinv (u.w z)) = v z
      rw [hui1 z]
    rw [← h5]
    exact h4
  have hden : moebiusDenom A (u.w z) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero A (ne_of_gt h1)
  rw [h3, moebiusMap_mul A⁻¹ A (u.w z) hden, inv_mul_cancel, moebiusMap_one]

end RiemannDynamics

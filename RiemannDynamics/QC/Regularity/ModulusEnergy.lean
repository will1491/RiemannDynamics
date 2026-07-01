/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.RingPotential
import RiemannDynamics.QC.Regularity.RingModulus
import RiemannDynamics.QC.Regularity.RhoDistance

/-!
# The conformal modulus as the Dirichlet energy of the harmonic potential

The connecting modulus of a ring domain equals the Dirichlet energy of its harmonic potential `u`
(the harmonic function that is `0` on the inner boundary continuum `E` and `1` on the outer `F`):

`curveModulus (connectingCurveFamily E F U) = ∫_U |∇u|²`.

The **upper bound** is the easy half: the density `|∇u|` is admissible for the connecting family
(a connecting curve runs from `E` (where `u = 0`) to `F` (where `u = 1`), so `∫_γ |∇u| ≥
|u(γ 1) − u(γ 0)| = 1`), and its area energy is exactly the Dirichlet energy. The **lower bound** is
the length–area / Dirichlet-principle direction (every admissible density has energy at least that
of the potential), obtained from the planar co-area formula `eilenberg_coarea_grad_le`.

This identity, with its separating-family counterpart, yields conjugate-modulus reciprocity
`M_connecting · M_separating = 1` for general ring domains.

## Main definitions

* `dirichletEnergy u U` — the Dirichlet energy `∫_U ‖∇u‖²` (as an `ℝ≥0∞`).

## Main statements

* `curveModulus_connecting_le_dirichletEnergy` — `M_connecting ≤ D(u)` (the easy direction);
* `dirichletEnergy_le_curveModulus_connecting` — `D(u) ≤ M_connecting` (the co-area direction).

## References

* L. V. Ahlfors, *Conformal Invariants*, Ch. 4 (extremal length, the modulus as a Dirichlet
  integral).
-/

open MeasureTheory Filter Metric Topology
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- The **Dirichlet energy** of `u` on `U`: the area integral `∫_U ‖∇u‖²` of the squared gradient
norm, as an extended nonnegative real (`‖fderiv ℝ u z‖` is the Euclidean gradient norm). -/
noncomputable def dirichletEnergy (u : ℂ → ℝ) (U : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in U, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2

/-- The Dirichlet energy is invariant under reflecting the potential `u ↦ 1 - u`: the Fréchet
derivative satisfies `fderiv ℝ (fun z => 1 - u z) z = -fderiv ℝ u z` pointwise, so the gradient
norm — hence the energy integrand — is unchanged. -/
theorem dirichletEnergy_one_sub (u : ℂ → ℝ) (U : Set ℂ) :
    dirichletEnergy (fun z => 1 - u z) U = dirichletEnergy u U := by
  unfold dirichletEnergy
  refine lintegral_congr fun z => ?_
  rw [fderiv_const_sub, nnnorm_neg]

/-- For a complex-differentiable `F` at `z`, the operator norm of the real Fréchet derivative of the
real part `w ↦ (F w).re` equals the modulus of the complex derivative `‖F′(z)‖`. The real derivative
is `Re ∘ (w ↦ F′(z) · w)`, and this rotation-projection has operator norm `‖F′(z)‖`. -/
theorem norm_fderiv_re_eq_norm_deriv {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℂ F z) :
    ‖fderiv ℝ (fun w => (F w).re) z‖ = ‖deriv F z‖ := by
  set c := deriv F z with hc
  -- The `ℝ`-linear Fréchet derivative of `F`, acting by `w ↦ c · w` (built directly to avoid the
  -- `restrictScalars` type-class search).
  have hFr : HasFDerivAt F (c • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)) z := by
    rw [hasFDerivAt_iff_isLittleO]
    refine hF.hasDerivAt.isLittleO.congr_left fun y => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- Chain rule: the real derivative of `Re ∘ F` is `reCLM ∘ (w ↦ c · w)`.
  have hcomp : HasFDerivAt (fun w => (F w).re)
      (Complex.reCLM.comp (c • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ))) z := by
    have := Complex.reCLM.hasFDerivAt.comp z hFr
    simpa [Function.comp] using this
  set L := Complex.reCLM.comp (c • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)) with hL
  rw [hcomp.fderiv]
  -- The map `L` acts by `w ↦ (c · w).re`.
  have hact : ∀ w : ℂ, L w = (c * w).re := by
    intro w
    simp only [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply]
  apply le_antisymm
  · -- Upper bound: `|(c · w).re| ≤ ‖c · w‖ = ‖c‖ · ‖w‖`.
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
    intro w
    rw [hact w]
    calc ‖(c * w).re‖ = |(c * w).re| := by rw [Real.norm_eq_abs]
      _ ≤ ‖c * w‖ := Complex.abs_re_le_norm _
      _ = ‖c‖ * ‖w‖ := by rw [norm_mul]
  · -- Lower bound: evaluate at the unit vector `w₀ = conj c / ‖c‖`, where `c · w₀ = ‖c‖`.
    by_cases hc0 : c = 0
    · simp [hc0]
    · set w₀ := (starRingEnd ℂ) c / (‖c‖ : ℂ) with hw₀
      have hcnorm_pos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc0
      have hw₀norm : ‖w₀‖ = 1 := by
        rw [hw₀, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hcnorm_pos, div_self (ne_of_gt hcnorm_pos)]
      have hprod : c * w₀ = (‖c‖ : ℂ) := by
        rw [hw₀, mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        rw [sq, mul_div_assoc, div_self (by exact_mod_cast ne_of_gt hcnorm_pos)]
        ring
      have hLval : L w₀ = ‖c‖ := by
        rw [hact w₀, hprod, Complex.ofReal_re]
      calc ‖c‖ = ‖L w₀‖ := by rw [hLval, Real.norm_eq_abs, abs_of_pos hcnorm_pos]
        _ ≤ ‖L‖ * ‖w₀‖ := L.le_opNorm w₀
        _ = ‖L‖ := by rw [hw₀norm, mul_one]

/-- **The Dirichlet energy of the real part of a holomorphic map.** For `F` holomorphic on the open
set `U`, the Dirichlet energy of the harmonic function `w ↦ (F w).re` is the area integral of the
squared modulus of the complex derivative: `dirichletEnergy (Re ∘ F) U = ∫_U ‖F′‖²`. Pointwise
`‖∇(Re ∘ F)‖ = ‖F′‖` by `norm_fderiv_re_eq_norm_deriv`. -/
theorem dirichletEnergy_re_eq_lintegral_normSq_deriv {F : ℂ → ℂ} {U : Set ℂ} (hUopen : IsOpen U)
    (hF : DifferentiableOn ℂ F U) :
    dirichletEnergy (fun w => (F w).re) U = ∫⁻ z in U, (‖deriv F z‖₊ : ℝ≥0∞) ^ 2 := by
  unfold dirichletEnergy
  refine setLIntegral_congr_fun hUopen.measurableSet (fun z hz => ?_)
  have hFz : DifferentiableAt ℂ F z := hF.differentiableAt (hUopen.mem_nhds hz)
  have hnn : ‖fderiv ℝ (fun w => (F w).re) z‖₊ = ‖deriv F z‖₊ :=
    NNReal.coe_injective (by rw [coe_nnnorm, coe_nnnorm]; exact norm_fderiv_re_eq_norm_deriv hFz)
  rw [hnn]

/-- **The holomorphic gradient of a harmonic function.** If `u` is harmonic on the open set `U`,
there is a function `f` holomorphic on `U` whose modulus is the gradient norm of `u` pointwise,
`‖∇u‖ = ‖f‖`, so the Dirichlet energy of `u` is the area integral of `‖f‖²`. Locally `u = (F).re`
for a holomorphic `F` and `f = F′ = u_x - i·u_y`. -/
theorem exists_holomorphicGradient {u : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ (∀ z ∈ U, ‖fderiv ℝ u z‖ = ‖f z‖) ∧
      dirichletEnergy u U = ∫⁻ z in U, (‖f z‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  -- The holomorphic gradient `f = u_x - i·u_y`, where `u_x = (fderiv ℝ u) 1`,
  -- `u_y = (fderiv ℝ u) I`.
  set f : ℂ → ℂ :=
    fun z => (((fderiv ℝ u z) 1 : ℝ) : ℂ) - Complex.I * (((fderiv ℝ u z) Complex.I : ℝ) : ℂ)
    with hf
  -- Around every point of `U`, `u` is the real part of a holomorphic `F`, and on the ball
  -- `f = F′` with the pointwise identity `‖∇u‖ = ‖f‖`.
  have key : ∀ z ∈ U, ∃ R > 0, ∃ F : ℂ → ℂ, ball z R ⊆ U ∧ AnalyticOnNhd ℂ F (ball z R) ∧
      (∀ w ∈ ball z R, f w = deriv F w) ∧ (∀ w ∈ ball z R, ‖fderiv ℝ u w‖ = ‖f w‖) := by
    intro z hz
    rw [Metric.isOpen_iff] at hUopen
    obtain ⟨R, hRpos, hBU⟩ := hUopen z hz
    have huball : InnerProductSpace.HarmonicOnNhd u (ball z R) := fun x hx => hu x (hBU hx)
    obtain ⟨F, hFan, hFeq⟩ :=
      InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq huball
    -- For each `w ∈ ball z R`, `f w = deriv F w` and `‖∇u w‖ = ‖f w‖`.
    have hpt : ∀ w ∈ ball z R, f w = deriv F w ∧ ‖fderiv ℝ u w‖ = ‖f w‖ := by
      intro w hw
      -- `u` agrees with `(F).re` near `w`, so their `ℝ`-Fréchet derivatives coincide at `w`.
      have haEq : u =ᶠ[𝓝 w] (fun x => (F x).re) :=
        hFeq.symm.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw)
      have hfdEq : fderiv ℝ u w = fderiv ℝ (fun x => (F x).re) w := haEq.fderiv_eq
      have hFdw : DifferentiableAt ℂ F w := (hFan w hw).differentiableAt
      -- The `ℝ`-Fréchet derivative of `F` acts by `w ↦ F′(w) · w` (built directly to avoid the
      -- `restrictScalars` type-class search).
      have hFr : HasFDerivAt F (deriv F w • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)) w := by
        rw [hasFDerivAt_iff_isLittleO]
        refine hFdw.hasDerivAt.isLittleO.congr_left fun y => ?_
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
        ring
      -- Chain rule: the real derivative of `(F).re` is `reCLM ∘ (w ↦ F′(w) · w)`.
      have hcomp : HasFDerivAt (fun x => (F x).re)
          (Complex.reCLM.comp (deriv F w • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ))) w := by
        have := Complex.reCLM.hasFDerivAt.comp w hFr
        simpa [Function.comp] using this
      have hfd2 : fderiv ℝ (fun x => (F x).re) w
          = Complex.reCLM.comp (deriv F w • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)) :=
        hcomp.fderiv
      -- Evaluate the real derivative at `1` and at `I`.
      have hval1 : (fderiv ℝ u w) 1 = (deriv F w).re := by
        rw [hfdEq, hfd2]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, Complex.reCLM_apply]
      have hvalI : (fderiv ℝ u w) Complex.I = -(deriv F w).im := by
        rw [hfdEq, hfd2]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply, Complex.mul_I_re]
      -- Hence `f w = ↑(F′ w).re + I·↑(F′ w).im = F′ w`.
      have hfvalw : f w = deriv F w := by
        rw [hf]
        simp only [hval1, hvalI]
        rw [show ((-(deriv F w).im : ℝ) : ℂ) = -((deriv F w).im : ℂ) by push_cast; ring]
        rw [mul_neg, sub_neg_eq_add, mul_comm]
        exact Complex.re_add_im (deriv F w)
      exact ⟨hfvalw, by rw [hfvalw, hfdEq, norm_fderiv_re_eq_norm_deriv hFdw]⟩
    exact ⟨R, hRpos, F, hBU, hFan, fun w hw => (hpt w hw).1, fun w hw => (hpt w hw).2⟩
  -- The pointwise norm identity on all of `U` (goal 2).
  have hnorm : ∀ z ∈ U, ‖fderiv ℝ u z‖ = ‖f z‖ := by
    intro z hz
    obtain ⟨R, hRpos, F, hBU, hFan, hfval, hnval⟩ := key z hz
    exact hnval z (mem_ball_self hRpos)
  refine ⟨f, ?_, hnorm, ?_⟩
  · -- Goal 1: `f` is holomorphic on `U`; near `z` it agrees with the holomorphic `deriv F`.
    intro z hz
    obtain ⟨R, hRpos, F, hBU, hFan, hfval, hnval⟩ := key z hz
    have hzball : z ∈ ball z R := mem_ball_self hRpos
    have hfeq : f =ᶠ[𝓝 z] deriv F :=
      Set.EqOn.eventuallyEq_of_mem (fun w hw => hfval w hw) (isOpen_ball.mem_nhds hzball)
    have hdF : DifferentiableAt ℂ (deriv F) z :=
      (hFan.deriv.differentiableOn z hzball).differentiableAt (isOpen_ball.mem_nhds hzball)
    exact ((hfeq.differentiableAt_iff).mpr hdF).differentiableWithinAt
  · -- Goal 3: the Dirichlet energy is the area integral of `‖f‖²`.
    unfold dirichletEnergy
    refine setLIntegral_congr_fun hUopen.measurableSet (fun z hz => ?_)
    have hnn : ‖fderiv ℝ u z‖₊ = ‖f z‖₊ :=
      NNReal.coe_injective (by rw [coe_nnnorm, coe_nnnorm]; exact hnorm z hz)
    rw [hnn]

/-- **The connecting modulus is at most the Dirichlet energy of the potential.** If `u` is
differentiable on the open set `U`, continuous up to the closure, equal to `0` on `E` and `1` on
`F`, then the gradient density `|∇u|` is admissible for the connecting family
`connectingCurveFamily E F U` (each connecting curve runs from `E` to `F`, so
`∫_γ |∇u| ≥ |u(γ 1) − u(γ 0)| = 1`), and its area
energy is the Dirichlet energy; hence the connecting modulus is at most `dirichletEnergy u U`. -/
theorem curveModulus_connecting_le_dirichletEnergy {u : ℂ → ℝ} {E F U : Set ℂ} (hUopen : IsOpen U)
    (hudiff : ContDiffOn ℝ 1 u U) (hucont : ContinuousOn u (closure U))
    (hE : ∀ z ∈ E, u z = 0) (hF : ∀ z ∈ F, u z = 1) :
    curveModulus (connectingCurveFamily E F U) ≤ dirichletEnergy u U := by
  classical
  -- The gradient density `ρ₀ = 1_U · ‖∇u‖`.
  set ρ₀ : ℂ → ℝ≥0∞ := Set.indicator U (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞)) with hρ₀
  -- Measurability of `ρ₀`.
  have hρ₀meas : Measurable ρ₀ := by
    refine Measurable.indicator ?_ hUopen.measurableSet
    exact (measurable_fderiv ℝ u).nnnorm.coe_nnreal_ennreal
  -- The energy of `ρ₀` is exactly the Dirichlet energy.
  have hρ₀energy : ∫⁻ z, (ρ₀ z) ^ 2 = dirichletEnergy u U := by
    have hsq : (fun z => (ρ₀ z) ^ 2)
        = Set.indicator U (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2) := by
      funext z
      by_cases hz : z ∈ U
      · simp only [hρ₀, Set.indicator_of_mem hz]
      · simp only [hρ₀, Set.indicator_of_notMem hz]; ring
    rw [hsq, lintegral_indicator hUopen.measurableSet]
    rfl
  rw [← hρ₀energy]
  -- It suffices to show `ρ₀` is admissible for the connecting family.
  refine iInf₂_le ρ₀ ⟨hρ₀meas, ?_⟩
  rintro γ ⟨hγcont, hγac, hγ0, hγ1, hγsub⟩
  -- The real composite `φ = u ∘ γ`.
  set φ : ℝ → ℝ := fun t => u (γ t) with hφ
  have hφ0 : φ 0 = 0 := hE (γ 0) hγ0
  have hφ1 : φ 1 = 1 := hF (γ 1) hγ1
  -- Reduce the line integral to the open interval `(0, 1)`.
  have hIccIoo : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm
  have hline : arcLengthLineIntegral ρ₀ γ
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral; rw [hIccIoo]
  rw [hline]
  -- a.e. differentiability of `γ`.
  have hγdiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ t :=
    hγac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  -- KEY pointwise a.e. bound on `(0, 1)`: `‖φ'‖₊ ≤ ρ₀(γ t) · ‖γ'(t)‖₊`.
  have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      (‖deriv φ t‖₊ : ℝ≥0∞) ≤ ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hγdiff] with t htγ
    intro htmem
    have htuIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
    have hγD : DifferentiableAt ℝ γ t := htγ htuIcc
    have hγtU : γ t ∈ U := hγsub t htmem
    -- Chain rule: `HasDerivAt φ (fderiv u (γ t) (γ'(t))) t`.
    have hUnhds : U ∈ 𝓝 (γ t) := hUopen.mem_nhds hγtU
    have hufd : HasFDerivAt u (fderiv ℝ u (γ t)) (γ t) :=
      (hudiff.differentiableOn (by norm_num)).hasFDerivAt hUnhds
    have hchain : HasDerivAt φ ((fderiv ℝ u (γ t)) (deriv γ t)) t :=
      hufd.comp_hasDerivAt t hγD.hasDerivAt
    have hderivφ : deriv φ t = (fderiv ℝ u (γ t)) (deriv γ t) := hchain.deriv
    -- `ρ₀(γ t) = ‖fderiv u (γ t)‖₊` since `γ t ∈ U`.
    have hρ₀val : ρ₀ (γ t) = (‖fderiv ℝ u (γ t)‖₊ : ℝ≥0∞) := by
      simp only [hρ₀, Set.indicator_of_mem hγtU]
    rw [hderivφ, hρ₀val, ← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr ((fderiv ℝ u (γ t)).le_opNNNorm (deriv γ t))
  -- The length-≥-chord (FTC) bound: `1 = |φ 1 - φ 0| ≤ ∫⁻_{(0,1)} ‖φ'‖₊`.
  -- This is the only remaining step. It requires `φ = u ∘ γ` to be absolutely continuous on
  -- `[ε, 1-ε]` (so that `φ(1-ε) - φ(ε) = ∫ deriv φ`, whence the chord ≤ length bound and the
  -- `ε → 0` limit). By the Marcus–Mizel characterisation, `u ∘ γ` is AC for *every* AC curve `γ`
  -- iff `u` is locally Lipschitz; mere `DifferentiableOn ℝ u U` does NOT suffice (a differentiable
  -- but non-locally-Lipschitz `u` admits an AC curve along which `u ∘ γ` is Cantor-like, so the
  -- FTC inequality fails and `ρ₀` is not admissible). The codebase's own chord bound
  -- `dist_comp_le_setIntegral_of_contDiff` (Mollification.lean) requires `ContDiff ℝ 1`. The
  -- missing hypothesis is therefore `ContDiffOn ℝ 1 u U` (equivalently
  -- `ContinuousOn (fderiv ℝ u) U` / `u` locally Lipschitz on `U`), which the realistic harmonic
  -- potential satisfies via `HarmonicOnNhd.contDiffOn`.
  have hchord : (1 : ℝ≥0∞) ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv φ t‖₊ : ℝ≥0∞) := by
    set I : ℝ≥0∞ := ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv φ t‖₊ : ℝ≥0∞) with hI
    -- For `ε ∈ (0, 1/2)`, the chord `|φ(1-ε) - φ(ε)|` is bounded by the length integral `I`.
    have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ENNReal.ofReal |φ (1 - ε) - φ ε| ≤ I := by
      intro ε hε hε2
      have hab : ε ≤ 1 - ε := by linarith
      -- The compact trace `S = γ '' [ε, 1-ε] ⊆ U`.
      set S : Set ℂ := γ '' Set.Icc ε (1 - ε) with hS
      have hScpt : IsCompact S := isCompact_Icc.image hγcont
      have hSU : S ⊆ U := by
        rintro z ⟨s, hs, rfl⟩
        exact hγsub s ⟨by linarith [hs.1], by linarith [hs.2]⟩
      -- `u` is locally Lipschitz on `S` (`C¹` at each point of the open `U ⊇ S`), hence Lipschitz.
      have hlocLip : LocallyLipschitzOn S u := by
        intro x hx
        have hcda : ContDiffAt ℝ 1 u x := hudiff.contDiffAt (hUopen.mem_nhds (hSU hx))
        obtain ⟨K, t, ht, hLip⟩ := hcda.exists_lipschitzOnWith
        exact ⟨K, t, nhdsWithin_le_nhds ht, hLip⟩
      obtain ⟨K, hK⟩ := hlocLip.exists_lipschitzOnWith_of_compact hScpt
      -- `γ` is AC on `[ε, 1-ε]`, mapping it into `S`.
      have hγε : AbsolutelyContinuousOnInterval γ ε (1 - ε) := by
        apply hγac.mono
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hmaps : ∀ t ∈ Set.uIcc ε (1 - ε), γ t ∈ S := by
        intro s hs; rw [Set.uIcc_of_le hab] at hs; exact ⟨s, hs, rfl⟩
      -- `φ = u ∘ γ` is AC on `[ε, 1-ε]` (Lipschitz-on-`S` ∘ AC is AC).
      have hφac : AbsolutelyContinuousOnInterval φ ε (1 - ε) := by
        rw [hφ]
        rw [absolutelyContinuousOnInterval_iff] at hγε ⊢
        intro δ hδpos
        obtain ⟨η, hη, hη'⟩ := hγε (δ / (K + 1)) (by positivity)
        refine ⟨η, hη, fun E hE hlen => ?_⟩
        have keyE := hη' E hE hlen
        have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
        have hmem : ∀ i ∈ Finset.range E.1,
            (E.2 i).1 ∈ Set.uIcc ε (1-ε) ∧ (E.2 i).2 ∈ Set.uIcc ε (1-ε) :=
          fun i hi => hE.1 i hi
        calc ∑ i ∈ Finset.range E.1, dist (u (γ (E.2 i).1)) (u (γ (E.2 i).2))
            ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) := by
              refine Finset.sum_le_sum (fun i hi => ?_)
              exact hK.dist_le_mul _ (hmaps _ (hmem i hi).1) _ (hmaps _ (hmem i hi).2)
          _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) := by
              rw [Finset.mul_sum]
          _ ≤ (K : ℝ) * (δ / (K + 1)) := mul_le_mul_of_nonneg_left keyE.le hKnn
          _ < δ := by
              rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hδpos.le, hKnn]
      -- FTC for AC functions: `φ(1-ε) - φ(ε) = ∫ deriv φ`.
      have hftc : ∫ t in ε..(1-ε), deriv φ t = φ (1-ε) - φ ε := hφac.integral_deriv_eq_sub
      -- The chord ≤ length bound (Bochner).
      have hchordR : |φ (1-ε) - φ ε| ≤ ∫ t in Set.Ioc ε (1-ε), ‖deriv φ t‖ := by
        rw [← hftc]
        have h1 : ‖∫ t in ε..(1-ε), deriv φ t‖ ≤ ∫ t in Set.uIoc ε (1-ε), ‖deriv φ t‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        rw [Set.uIoc_of_le hab] at h1
        simpa [Real.norm_eq_abs] using h1
      -- Integrability of `deriv φ` on the subinterval.
      have hint : IntegrableOn (deriv φ) (Set.Ioc ε (1-ε)) volume := by
        have := hφac.intervalIntegrable_deriv.def'; rwa [Set.uIoc_of_le hab] at this
      -- Convert the Bochner length to an `lintegral` of `‖deriv φ‖₊`, then enlarge to `I`.
      have hconv : ENNReal.ofReal (∫ t in Set.Ioc ε (1-ε), ‖deriv φ t‖)
          = ∫⁻ t in Set.Ioc ε (1-ε), (‖deriv φ t‖₊ : ℝ≥0∞) := by
        rw [ofReal_integral_norm_eq_lintegral_enorm hint]; simp only [enorm_eq_nnnorm]
      calc ENNReal.ofReal |φ (1-ε) - φ ε|
          ≤ ENNReal.ofReal (∫ t in Set.Ioc ε (1-ε), ‖deriv φ t‖) :=
            ENNReal.ofReal_le_ofReal hchordR
        _ = ∫⁻ t in Set.Ioc ε (1-ε), (‖deriv φ t‖₊ : ℝ≥0∞) := hconv
        _ = ∫⁻ t in Set.Ioo ε (1-ε), (‖deriv φ t‖₊ : ℝ≥0∞) := by
            rw [← restrict_Ioo_eq_restrict_Ioc]
        _ ≤ I := lintegral_mono_set
            (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    -- As `ε → 0⁺`, `φ(ε) → φ 0 = 0` and `φ(1-ε) → φ 1 = 1` (continuity into `closure U`).
    have hlim0 : Tendsto (fun ε => φ ε) (𝓝[>] (0:ℝ)) (𝓝 (φ 0)) := by
      rw [hφ]
      have hcl0 : γ 0 ∈ closure U := by
        have htg : Tendsto γ (𝓝[>] (0:ℝ)) (𝓝 (γ 0)) :=
          (hγcont.tendsto _).mono_left nhdsWithin_le_nhds
        apply mem_closure_of_tendsto htg
        filter_upwards [self_mem_nhdsWithin,
          (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))]
          with ε hε hε1 using hγsub ε ⟨hε, hε1⟩
      have hcw : ContinuousWithinAt u (closure U) (γ 0) := hucont.continuousWithinAt hcl0
      have hγtend : Tendsto γ (𝓝[>] (0:ℝ)) (𝓝[closure U] (γ 0)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨(hγcont.tendsto _).mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin,
          (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))]
          with ε hε hε1 using subset_closure (hγsub ε ⟨hε, hε1⟩)
      exact hcw.tendsto.comp hγtend
    have hlim1 : Tendsto (fun ε => φ (1 - ε)) (𝓝[>] (0:ℝ)) (𝓝 (φ 1)) := by
      rw [hφ]
      have h1e : Tendsto (fun ε : ℝ => (1 - ε)) (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
        have : Tendsto (fun ε : ℝ => (1 - ε)) (𝓝 (0:ℝ)) (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        simpa using this.mono_left nhdsWithin_le_nhds
      have htg : Tendsto (fun ε : ℝ => γ (1 - ε)) (𝓝[>] (0:ℝ)) (𝓝 (γ 1)) :=
        (hγcont.tendsto _).comp h1e
      have hcl1 : γ 1 ∈ closure U := by
        apply mem_closure_of_tendsto htg
        filter_upwards [self_mem_nhdsWithin,
          (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))]
          with ε hε hε1
        have hεp : 0 < ε := hε
        exact hγsub (1-ε) ⟨by linarith, by linarith⟩
      have hcw : ContinuousWithinAt u (closure U) (γ 1) := hucont.continuousWithinAt hcl1
      have hγtend : Tendsto (fun ε : ℝ => γ (1 - ε)) (𝓝[>] (0:ℝ)) (𝓝[closure U] (γ 1)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨htg, ?_⟩
        filter_upwards [self_mem_nhdsWithin,
          (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))]
          with ε hε hε1
        have hεp : 0 < ε := hε
        exact subset_closure (hγsub (1-ε) ⟨by linarith, by linarith⟩)
      exact hcw.tendsto.comp hγtend
    -- `ENNReal.ofReal |φ(1-ε) - φ ε| → ENNReal.ofReal |φ 1 - φ 0| = 1`.
    have hlimabs : Tendsto (fun ε => ENNReal.ofReal |φ (1 - ε) - φ ε|)
        (𝓝[>] (0:ℝ)) (𝓝 (ENNReal.ofReal |φ 1 - φ 0|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((continuous_abs.tendsto _).comp (hlim1.sub hlim0))
    have hval : ENNReal.ofReal |φ 1 - φ 0| = 1 := by rw [hφ0, hφ1]; norm_num
    rw [hval] at hlimabs
    -- Pass to the limit: `1 ≤ I` since the constant `I` dominates `ofReal |φ(1-ε) - φ ε|`.
    refine le_of_tendsto hlimabs ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2)))]
      with ε hε hε2 using key ε hε hε2
  calc (1 : ℝ≥0∞) ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv φ t‖₊ : ℝ≥0∞) := hchord
    _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := lintegral_mono_ae hpoint

/-- **The competitor energy bound** (the eikonal half of the modulus–energy lower bound). For a
bounded measurable density `ρ ≤ M` on the open set `U`, the truncated `ρ`-length distance
`w₀ z = min (rhoDistance ρ E U z).toReal 1` is an admissible competitor whose Dirichlet energy is at
most `∫ ρ²`. Pointwise a.e. the gradient of `w₀` is bounded by `ρ`: away from the level set
`{(rhoDistance).toReal = 1}` the truncation is locally either the `ρ`-length distance (eikonal
`‖∇(rhoDistance).toReal‖ ≤ ρ`) or constant `1`; on that level set `w₀` attains its global maximum,
so its gradient vanishes there. Integrating the squared bound and enlarging the domain to all of `ℂ`
gives the stated inequality. -/
theorem dirichletEnergy_min_rhoDistance_le {ρ : ℂ → ℝ≥0∞} {E U : Set ℂ} {M : ℝ≥0}
    (hUopen : IsOpen U) (hρmeas : Measurable ρ) (hρbdd : ∀ x, ρ x ≤ (M : ℝ≥0∞)) :
    dirichletEnergy (fun z => min (rhoDistance ρ E U z).toReal 1) U ≤ ∫⁻ z, (ρ z) ^ 2 := by
  classical
  set f : ℂ → ℝ := fun z => (rhoDistance ρ E U z).toReal with hf
  set w₀ : ℂ → ℝ := fun z => min (f z) 1 with hw₀
  -- `f` is continuous on `U`: the segment additive bound is two-sided and, on the infinite region,
  -- forces `f` to be locally constant `0`.
  have hfcont : ∀ z ∈ U, ContinuousAt f z := by
    intro z hz
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hUopen z hz
    by_cases hztop : rhoDistance ρ E U z = ⊤
    · -- infinite region: `f` is locally constant `0`.
      have hloc : f =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [Metric.ball_mem_nhds z hr] with w hw
        have hwU : w ∈ U := hrsub hw
        have hseg : openSegment ℝ w z ⊆ U :=
          ((convex_ball z r).openSegment_subset hw (Metric.mem_ball_self hr)).trans hrsub
        have hle := rhoDistance_le_add_mul_of_bounded (E := E) hρbdd hwU hseg
        rw [hztop] at hle
        have hfin : rhoDistance ρ E U w + (M : ℝ≥0∞) * (‖z - w‖₊ : ℝ≥0∞) ≠ ⊤ → False := by
          intro hcontra; exact hcontra (top_le_iff.mp hle)
        have hwtop : rhoDistance ρ E U w = ⊤ := by
          by_contra hwfin
          exact hfin (ENNReal.add_ne_top.mpr
            ⟨hwfin, ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩)
        rw [hf]; simp only; rw [hwtop, ENNReal.toReal_top]
      exact continuousAt_const.congr hloc.symm
    · -- finite region: `|f w - f z| ≤ M ‖w - z‖` on the ball, hence Lipschitz, hence continuous.
      have hlip : ∀ w ∈ Metric.ball z r, |f w - f z| ≤ (M : ℝ) * ‖w - z‖ := by
        intro w hw
        have hwU : w ∈ U := hrsub hw
        have hseg1 : openSegment ℝ z w ⊆ U :=
          ((convex_ball z r).openSegment_subset (Metric.mem_ball_self hr) hw).trans hrsub
        have hseg2 : openSegment ℝ w z ⊆ U :=
          ((convex_ball z r).openSegment_subset hw (Metric.mem_ball_self hr)).trans hrsub
        have hle1 := rhoDistance_le_add_mul_of_bounded (E := E) hρbdd hz hseg1
        have hle2 := rhoDistance_le_add_mul_of_bounded (E := E) hρbdd hwU hseg2
        have hmt1 : (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
        have hmt2 : (M : ℝ≥0∞) * (‖z - w‖₊ : ℝ≥0∞) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
        have hwtop : rhoDistance ρ E U w ≠ ⊤ :=
          ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hztop, hmt1⟩) hle1
        have hr1 : f w ≤ f z + (M : ℝ) * ‖w - z‖ := by
          have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hztop, hmt1⟩) hle1
          rw [ENNReal.toReal_add hztop hmt1, ENNReal.toReal_mul] at this
          simpa [hf, ENNReal.coe_toReal] using this
        have hr2 : f z ≤ f w + (M : ℝ) * ‖z - w‖ := by
          have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hwtop, hmt2⟩) hle2
          rw [ENNReal.toReal_add hwtop hmt2, ENNReal.toReal_mul] at this
          simpa [hf, ENNReal.coe_toReal] using this
        rw [abs_sub_le_iff]
        refine ⟨by linarith, ?_⟩
        rw [show ‖z - w‖ = ‖w - z‖ from norm_sub_rev z w] at hr2; linarith
      -- continuity from the pointwise bound.
      rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨min r (ε / (M + 1)), by positivity, fun w hwd => ?_⟩
      have hwr : w ∈ Metric.ball z r :=
        Metric.mem_ball.mpr (lt_of_lt_of_le hwd (min_le_left _ _))
      have hwd2 : dist w z < ε / (M + 1) := lt_of_lt_of_le hwd (min_le_right _ _)
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
      rw [Real.dist_eq]
      calc |f w - f z| ≤ (M : ℝ) * ‖w - z‖ := hlip w hwr
        _ = (M : ℝ) * dist w z := by rw [dist_eq_norm]
        _ ≤ (M : ℝ) * (ε / (M + 1)) := by
            apply mul_le_mul_of_nonneg_left hwd2.le hMnn
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hMnn]
  -- the a.e. gradient bound for the truncation.
  have hgrad : ∀ᵐ z ∂(volume.restrict U), (‖fderiv ℝ w₀ z‖₊ : ℝ≥0∞) ≤ ρ z := by
    have heik := rhoDistance_upperGradient_of_bounded (E := E) hUopen hρmeas hρbdd
    filter_upwards [heik, ae_restrict_mem hUopen.measurableSet] with z hz hzU
    -- pointwise: `‖fderiv w₀ z‖ ≤ ‖fderiv f z‖`.
    have hcont : ContinuousAt f z := hfcont z hzU
    have hkey : ‖fderiv ℝ w₀ z‖ ≤ ‖fderiv ℝ f z‖ := by
      rcases lt_trichotomy (f z) 1 with hlt | heq | hgt
      · -- `f z < 1`: `w₀ = f` near `z`.
        have hev : w₀ =ᶠ[nhds z] f := by
          filter_upwards [hcont (Iio_mem_nhds hlt)] with w hw using min_eq_left hw.le
        rw [hev.fderiv_eq]
      · -- `f z = 1`: global max of `w₀`, so `fderiv w₀ z = 0`.
        have hmax : IsMaxOn w₀ Set.univ z := by
          intro w _; simp only [hw₀]
          calc min (f w) 1 ≤ 1 := min_le_right _ _
            _ = min (f z) 1 := by rw [heq, min_self]
        have hlm : IsLocalMax w₀ z := hmax.isLocalMax Filter.univ_mem
        rw [hlm.fderiv_eq_zero, norm_zero]; exact norm_nonneg _
      · -- `f z > 1`: `w₀ = 1` near `z`.
        have hev : w₀ =ᶠ[nhds z] (fun _ => (1 : ℝ)) := by
          filter_upwards [hcont (Ioi_mem_nhds hgt)] with w hw using min_eq_right hw.le
        rw [hev.fderiv_eq, fderiv_const_apply, norm_zero]; exact norm_nonneg _
    have hnn : ‖fderiv ℝ w₀ z‖₊ ≤ ‖fderiv ℝ f z‖₊ := hkey
    calc (‖fderiv ℝ w₀ z‖₊ : ℝ≥0∞) ≤ (‖fderiv ℝ f z‖₊ : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hnn
      _ ≤ ρ z := hz
  -- integrate the squared bound.
  unfold dirichletEnergy
  calc ∫⁻ z in U, (‖fderiv ℝ w₀ z‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ z in U, (ρ z) ^ 2 := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgrad] with z hz; gcongr
    _ ≤ ∫⁻ z, (ρ z) ^ 2 := setLIntegral_le_lintegral U _

/-- **The Dirichlet energy of the potential is at most the connecting modulus** (the
Dirichlet-principle direction). For a density `ρ` admissible for the connecting family, the
`ρ`-distance `v z = ⨅ {∫_γ ρ : γ joins E to z inside U}` vanishes on `E`, is `≥ 1` on `F`, and
satisfies the eikonal upper-gradient inequality `‖∇v‖ ≤ ρ` almost everywhere; the truncation
`min v 1` is then a competitor sharing the potential's boundary values, so the Dirichlet principle
`∫_U |∇u|² ≤ ∫_U |∇(min v 1)|²` combined with `∫_U |∇(min v 1)|² ≤ ∫ ρ²` gives the bound after
taking the infimum over admissible `ρ`. The level sets of `u` are the *separating* curves, along
which an admissible connecting density is uncontrolled, so co-area applied to `u` bounds the
separating modulus rather than this one; the connecting lower bound genuinely proceeds through the
`ρ`-distance. The boundary sets `E`, `F` must be nondegenerate continua: for point sets the
connecting modulus is `0` while the energy is positive, so the bound requires that hypothesis. -/
theorem dirichletEnergy_le_curveModulus_connecting {u : ℂ → ℝ} {E F U : Set ℂ} (hUopen : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hucont : ContinuousOn u (closure U))
    (hE : ∀ z ∈ E, u z = 0) (hF : ∀ z ∈ F, u z = 1)
    (hbdd : Bornology.IsBounded U) :
    dirichletEnergy u U ≤ curveModulus (connectingCurveFamily E F U) := by
  sorry

end RiemannDynamics

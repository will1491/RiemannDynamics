/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.Deformation.SphereVectorField
import RiemannDynamics.QC.Calculus.WeylLocal
import RiemannDynamics.Sphere.OpenMapping
import RiemannDynamics.Sphere.Iterate
import RiemannDynamics.Dynamics.JuliaFatou.RepellingDensity

/-!
# The delta operator of a rational map and its finite-dimensional target

For a rational map `f` given by `r : RationalData`, a continuous vector field
`v` on the sphere determines the *deformation field*

`δv = f′·v − v ∘ f`

read in the finite chart (`deltaField`). Classically `δv = Df(v) − v ∘ f` is
a section of the pullback bundle `f*(T ℂ̂)`; here everything is chart-concrete:
`f′` is the finite-chart derivative `wronskian/denReduced²` (`fderivRational`)
and the composition point is the finite reading of `f(z)` (junk at the poles
of `f`, a finite — hence null — set).

The two main results stated here are the heart of Sullivan's finiteness
argument:

* **Invariance kills `∂̄`**: if `μ = ∂̄v` is `f`-invariant
  (`IsInvariantBeltrami`, the pullback law `f*μ = μ` in multiplied-out form),
  then `∂̄(δv) = f′·μ − (μ∘f)·conj(f′) = 0` weakly off the poles, so `δv` is
  holomorphic off the poles (open-set Weyl); chart analysis at each pole and
  at infinity then places `δv` in the concrete `(2d+1)`-dimensional space
  `SectionSpaceCarrier r = {A/denReduced² : A ∈ ℂ[X], natDegree A ≤ 2d}`
  (`exists_sectionSpace_rep_deltaField`, with `finrank_sectionSpaceCarrier`).
  Because Lean's junk value of `A/Q²` at a root of `Q` is `0` while
  `deltaField`'s junk value there is `−v(0)`, membership is stated as the
  existence of a carrier element agreeing with `δv` off the poles; such a
  representative is unique (`sectionSpaceCarrier_eqOn_nonpoles_eq`).

* **Trivial deformations vanish on the Julia set**: if `δv = 0` off the
  poles then `v(f z) = f′(z)·v(z)` there; iterating
  (`deltaField_zero_iterate`) and evaluating at a repelling periodic point
  `p` gives `v(p) = m·v(p)` with `|m| > 1`, so `v(p) = 0`; density of
  repelling cycles (`juliaSet_eq_closure_repelling`) and continuity give
  `v = 0` at every finite point of the Julia set
  (`sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero`). The finite-point
  statement is all downstream consumers need: the frontier of a Fatou
  component is consumed through its finite part, and behavior at `∞` is
  handled by the sphere-field decay built into the seed-triviality argument.
-/

open MeasureTheory Complex Metric Filter Topology Polynomial OnePoint

namespace RiemannDynamics

/-! ## The finite-chart derivative and the invariance law -/

/-- The finite-chart derivative of the rational map given by `r`: the
Wronskian of the reduced representation divided by the squared reduced
denominator. Away from the poles this equals the derivative of the
finite-chart reading (`RationalData.deriv_reading`); at a pole the value is
junk (`x/0 = 0` in Lean) and every downstream statement restricts to
non-poles or works almost everywhere. -/
noncomputable def fderivRational (r : RationalData) : ℂ → ℂ := fun z =>
  r.wronskian.eval z / (r.denReduced.eval z) ^ 2

/-- Away from poles, `fderivRational` is the derivative of the finite-chart
reading of the map. -/
theorem fderivRational_eq_deriv_reading (r : RationalData) {w : ℂ}
    (hden : r.denReduced.eval w ≠ 0) :
    fderivRational r w
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) w := by
  exact (r.deriv_reading hden).symm

/-- A coefficient `μ : ℂ → ℂ` is an **invariant Beltrami coefficient** for
the rational map given by `r` when the pullback law `f*μ = μ` holds almost
everywhere in the finite chart. The pullback convention is

`(f*μ)(z) = μ(f z) · conj(f′(z)) / f′(z)`,

and the law is stated in multiplied-out form to avoid division:

`μ(z) · f′(z) = μ(f z) · conj(f′(z))` for a.e. `z`,

with `f′ = fderivRational r` and `f z` read through `chartFiniteMap` (the
junk value `0` at the finitely many poles is harmless almost everywhere).
`Spreading.lean` *proves* this law for coefficients spread from a seed on a
wandering component; this file *consumes* it to kill the weak `∂̄` of the
deformation field. -/
def IsInvariantBeltrami (r : RationalData) (μ : ℂ → ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ),
    μ z * fderivRational r z
      = μ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
          * starRingEnd ℂ (fderivRational r z)

/-! ## The delta operator -/

/-- The **deformation field** `δv = f′·v − v∘f` of a vector field `v` along
the rational map given by `r`, read in the finite chart. Total: at a pole of
`f` the value is junk (`fderivRational` is junk there and the composition
point is the junk reading `0` of `∞`), and every statement about `deltaField`
restricts to non-poles. -/
noncomputable def deltaField (r : RationalData) (v : ℂ → ℂ) : ℂ → ℂ := fun z =>
  fderivRational r z * v z
    - v (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))

/-! ## The finite-dimensional section space -/

/-- The linear map sending a polynomial `A` to the function
`z ↦ A(z)/denReduced(z)²` — the concrete realization of "polynomial sections
over the squared denominator". -/
noncomputable def polyOverDenSq (r : RationalData) : ℂ[X] →ₗ[ℂ] (ℂ → ℂ) where
  toFun A := fun z => A.eval z / (r.denReduced.eval z) ^ 2
  map_add' A B := by
    funext z
    simp [Polynomial.eval_add, add_div]
  map_smul' c A := by
    funext z
    simp [Polynomial.eval_smul, smul_eq_mul, mul_div_assoc]

/-- The **section space** of the rational map given by `r`: the space of
functions `z ↦ A(z)/denReduced(z)²` with `A` a polynomial of degree at most
`2·degree r` — concretely, the image of `Polynomial.degreeLT ℂ (2d+1)` under
`polyOverDenSq`. This is the chart-concrete model of the space of holomorphic
sections of the pullback bundle `f*(T ℂ̂)`, of dimension `2d+1`. -/
noncomputable def SectionSpaceCarrier (r : RationalData) : Submodule ℂ (ℂ → ℂ) :=
  (Polynomial.degreeLT ℂ (2 * r.degree + 1)).map (polyOverDenSq r)

/-- Unfolding characterization of the section space: membership means being
the function `A/denReduced²` for some polynomial `A` with
`natDegree A ≤ 2·degree r`. -/
theorem mem_sectionSpaceCarrier_iff {r : RationalData} {s : ℂ → ℂ} :
    s ∈ SectionSpaceCarrier r
      ↔ ∃ A : ℂ[X], A.natDegree ≤ 2 * r.degree ∧
          s = fun z => A.eval z / (r.denReduced.eval z) ^ 2 := by
  unfold SectionSpaceCarrier
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨A, hA, hAs⟩
    rw [Polynomial.mem_degreeLT] at hA
    refine ⟨A, ?_, hAs.symm⟩
    by_cases h0 : A = 0
    · simp [h0]
    · have h1 := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hA
      omega
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, ?_, rfl⟩
    rw [Polynomial.mem_degreeLT]
    by_cases h0 : A = 0
    · rw [h0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (by omega)

/-- Two elements of the section space that agree off the (finitely many)
poles are equal: `A/Q²` determines `A` by polynomial function-agreement off a
finite set, and the junk values at the poles are `0` for both. This provides
the uniqueness of the carrier representative of a deformation field, which
makes the endgame's linear map into the carrier well defined. -/
theorem sectionSpaceCarrier_eqOn_nonpoles_eq {r : RationalData} {s₁ s₂ : ℂ → ℂ}
    (h₁ : s₁ ∈ SectionSpaceCarrier r) (h₂ : s₂ ∈ SectionSpaceCarrier r)
    (h : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → s₁ z = s₂ z) :
    s₁ = s₂ := by
  obtain ⟨A, -, rfl⟩ := mem_sectionSpaceCarrier_iff.mp h₁
  obtain ⟨B, -, hB⟩ := mem_sectionSpaceCarrier_iff.mp h₂
  subst hB
  have hden : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hAB : A = B := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := {x : ℂ | r.denReduced.IsRoot x}ᶜ)
    · intro z hz
      have hz' : r.denReduced.eval z ≠ 0 := hz
      have hq : (r.denReduced.eval z) ^ 2 ≠ 0 := pow_ne_zero _ hz'
      have hzz := h z hz'
      simp only at hzz
      exact mul_right_cancel₀ hq ((div_eq_div_iff hq hq).mp hzz)
    · exact (Polynomial.finite_setOf_isRoot hden).infinite_compl
  rw [hAB]

/-- The section space has dimension `2d+1`: the parametrization
`A ↦ A/denReduced²` is injective on `degreeLT ℂ (2d+1)` (a polynomial is
determined by its values off the finite root set of `denReduced`), and
`degreeLT ℂ (2d+1)` has dimension `2d+1`. -/
theorem finrank_sectionSpaceCarrier (r : RationalData) :
    Module.finrank ℂ (SectionSpaceCarrier r) = 2 * r.degree + 1 := by
  have hden : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hinj : Function.Injective (polyOverDenSq r) := by
    rw [injective_iff_map_eq_zero]
    intro A hA
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := {x : ℂ | r.denReduced.IsRoot x}ᶜ)
    · intro z hz
      have hz' : r.denReduced.eval z ≠ 0 := hz
      have h0 : A.eval z / (r.denReduced.eval z) ^ 2 = 0 := congrFun hA z
      have := div_eq_zero_iff.mp h0
      exact this.resolve_right (pow_ne_zero _ hz')
    · exact (Polynomial.finite_setOf_isRoot hden).infinite_compl
  have e := Submodule.equivMapOfInjective (polyOverDenSq r) hinj
    (Polynomial.degreeLT ℂ (2 * r.degree + 1))
  have h1 : Module.finrank ℂ (SectionSpaceCarrier r)
      = Module.finrank ℂ (Polynomial.degreeLT ℂ (2 * r.degree + 1)) :=
    e.finrank_eq.symm
  rw [h1, (Polynomial.degreeLTEquiv ℂ (2 * r.degree + 1)).finrank_eq,
    Module.finrank_fin_fun]

/-! ## Weak Wirtinger calculus: product and chain rules

The two generic transport rules feeding the holomorphy of the deformation
field. Both stay in the conformally invariant class `HasL2WeakDzbar`. -/

open scoped ContDiff ENNReal in
set_option maxHeartbeats 400000 in
/-- **Product rule with a holomorphic factor.** If `F` is holomorphic on the
open set `Ω` and `v` has weak `∂̄`-derivative `μ` (with `L²_loc` gradient) on
`Ω`, then `F·v` has weak `∂̄`-derivative `F·μ` on `Ω` — `∂̄(Fv) = F·∂̄v` since
`∂̄F = 0`. Local integrability of `v` on `Ω` feeds the Leibniz rule for weak
derivatives. -/
theorem hasL2WeakDzbar_holomorphic_mul {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F v μ : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hvloc : LocallyIntegrableOn v Ω)
    (hgrad : HasL2WeakDzbar v μ Ω) :
    HasL2WeakDzbar (fun z => F z * v z) (fun z => F z * μ z) Ω := by
  have d1_locInt : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : MemLpLocOn g 2 Ω), LocallyIntegrableOn g Ω := by
    intro Ω hΩ g hg
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk hkc
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    have h1le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    exact memLp_one_iff_integrable.mp ((hg k hk hkc).mono_exponent h1le)
  have d2_integ_real : ∀ {Ω : Set ℂ} (m : ℂ → ℝ) (hm : Continuous m)
    (hcsm : HasCompactSupport m) (htsuppm : tsupport m ⊆ Ω)
    {h : ℂ → ℂ} (hh : LocallyIntegrableOn h Ω), Integrable (fun z => m z • h z) volume := by
    intro Ω m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  have d4_locInt_mul : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {m h : ℂ → ℂ}
    (hm : ContinuousOn m Ω) (hh : LocallyIntegrableOn h Ω), LocallyIntegrableOn (fun z => m z * h z) Ω := by
    intro Ω hΩ m h hm hh
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk hkc
    exact (hh.integrableOn_compact_subset hk hkc).continuousOn_mul (hm.mono hk) hkc
  have d5_weak_mul : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F v : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hvloc : LocallyIntegrableOn v Ω)
    (e : ℂ) {gv : ℂ → ℂ} (hgv : HasWeakDirDeriv e gv v Ω)
    (hgvloc : LocallyIntegrableOn gv Ω), HasWeakDirDeriv e (fun z => F z * gv z + (deriv F z * e) * v z)
      (fun z => F z * v z) Ω := by
    intro Ω hΩ F v hF hvloc e gv hgv hgvloc
    -- Analyticity package for the holomorphic factor.
    have hFa : AnalyticOnNhd ℂ F Ω := hF.analyticOnNhd hΩ
    have hFcontOn : ContinuousOn F Ω := hF.continuousOn
    have hF'contOn : ContinuousOn (deriv F) Ω := hFa.deriv.continuousOn
    have hFAtR : ∀ z ∈ Ω, AnalyticAt ℝ F z := fun z hz =>
      @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
        IsScalarTower.right _ _ (hFa z hz)
    have hFAt : ∀ z ∈ Ω, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F z := fun z hz =>
      (hFAtR z hz).contDiffAt
    -- Real differentiability and the applied real Fréchet derivative on `Ω`.
    have hFdiffC : ∀ z ∈ Ω, DifferentiableAt ℂ F z := fun z hz =>
      hF.differentiableAt (hΩ.mem_nhds hz)
    have hFdiffR : ∀ z ∈ Ω, DifferentiableAt ℝ F z := fun z hz =>
      (differentiableAt_complex_iff_differentiableAt_real.mp (hFdiffC z hz)).1
    have hFapp : ∀ z ∈ Ω, ∀ e : ℂ, (fderiv ℝ F z) e = deriv F z * e := by
      intro z hz e
      obtain ⟨hr, hCR⟩ := differentiableAt_complex_iff_differentiableAt_real.mp (hFdiffC z hz)
      have h1 : (fderiv ℝ F z) 1 = deriv F z := by
        have hdz := dz_eq_deriv_of_differentiableAt (hFdiffC z hz)
        rw [dz, hCR, smul_eq_mul] at hdz
        linear_combination hdz + (1 / 2 : ℂ) * ((fderiv ℝ F z) 1) * Complex.I_mul_I
      have hI : (fderiv ℝ F z) Complex.I = Complex.I * deriv F z := by
        rw [hCR, smul_eq_mul, h1]
      have hdec : e = e.re • (1 : ℂ) + e.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      calc (fderiv ℝ F z) e
          = e.re • ((fderiv ℝ F z) 1) + e.im • ((fderiv ℝ F z) Complex.I) := by
            conv_lhs => rw [hdec]
            rw [map_add, _root_.map_smul, _root_.map_smul]
        _ = deriv F z * e := by
            rw [h1, hI]
            simp only [Complex.real_smul]
            linear_combination (deriv F z) * (Complex.re_add_im e)
    intro φ hφ hcs htsupp
    change ∫ z, ((fderiv ℝ φ z) e) • (F z * v z)
        = - ∫ z, φ z • (F z * gv z + (deriv F z * e) * v z)
    -- Every point is either in `Ω` or outside the support of the test function.
    have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport φ := fun z =>
      (em (z ∈ tsupport φ)).elim (fun h => Or.inl (htsupp h)) Or.inr
    -- The two real test functions `φ·Re F` and `φ·Im F`.
    set ψ₁ : ℂ → ℝ := fun z => φ z * (F z).re with hψ₁def
    set ψ₂ : ℂ → ℝ := fun z => φ z * (F z).im with hψ₂def
    have hψsm : ∀ (P : ℂ →L[ℝ] ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z * P (F z)) := by
      intro P
      rw [contDiff_iff_contDiffAt]
      intro z
      rcases hcover z with hz | hz
      · have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => P (F w)) z := by
          simpa [Function.comp] using (P.contDiff.contDiffAt).comp z (hFAt z hz)
        exact (hφ.contDiffAt).mul hcomp
      · have hev : (fun w => φ w * P (F w)) =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with y hy
          simp [image_eq_zero_of_notMem_tsupport hy]
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
    have hψ₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ := by
      simpa only [Complex.reCLM_apply] using hψsm Complex.reCLM
    have hψ₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₂ := by
      simpa only [Complex.imCLM_apply] using hψsm Complex.imCLM
    have hψ₁cs : HasCompactSupport ψ₁ := hcs.mul_right
    have hψ₂cs : HasCompactSupport ψ₂ := hcs.mul_right
    have hψ₁ts : tsupport ψ₁ ⊆ Ω := (tsupport_mul_subset_left).trans htsupp
    have hψ₂ts : tsupport ψ₂ ⊆ Ω := (tsupport_mul_subset_left).trans htsupp
    -- The pointwise directional-derivative identity.
    have hid : ∀ z : ℂ, (((fderiv ℝ ψ₁ z) e : ℝ) : ℂ)
          + Complex.I * (((fderiv ℝ ψ₂ z) e : ℝ) : ℂ)
        = (((fderiv ℝ φ z) e : ℝ) : ℂ) * F z + (φ z : ℂ) * (deriv F z * e) := by
      intro z
      rcases hcover z with hz | hz
      · -- Product rule on `Ω`.
        have hdφ : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
        have hre_fdeq : fderiv ℝ (fun w => (F w).re) z
            = Complex.reCLM.comp (fderiv ℝ F z) := by
          have h := fderiv_comp z (Complex.reCLM.differentiableAt) (hFdiffR z hz)
          rw [ContinuousLinearMap.fderiv] at h
          simpa [Function.comp, Complex.reCLM_apply] using h
        have him_fdeq : fderiv ℝ (fun w => (F w).im) z
            = Complex.imCLM.comp (fderiv ℝ F z) := by
          have h := fderiv_comp z (Complex.imCLM.differentiableAt) (hFdiffR z hz)
          rw [ContinuousLinearMap.fderiv] at h
          simpa [Function.comp, Complex.imCLM_apply] using h
        have hre_diff : DifferentiableAt ℝ (fun w => (F w).re) z := by
          simpa [Function.comp, Complex.reCLM_apply] using
            (Complex.reCLM.differentiableAt.comp z (hFdiffR z hz))
        have him_diff : DifferentiableAt ℝ (fun w => (F w).im) z := by
          simpa [Function.comp, Complex.imCLM_apply] using
            (Complex.imCLM.differentiableAt.comp z (hFdiffR z hz))
        have hx1 : (fderiv ℝ ψ₁ z) e
            = φ z * (deriv F z * e).re + (F z).re * ((fderiv ℝ φ z) e) := by
          rw [hψ₁def]
          rw [fderiv_fun_mul hdφ hre_diff]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul, hre_fdeq, ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
          rw [hFapp z hz e]
        have hx2 : (fderiv ℝ ψ₂ z) e
            = φ z * (deriv F z * e).im + (F z).im * ((fderiv ℝ φ z) e) := by
          rw [hψ₂def]
          rw [fderiv_fun_mul hdφ him_diff]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul, him_fdeq, ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
          rw [hFapp z hz e]
        rw [hx1, hx2]
        apply Complex.ext <;>
          simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring
      · -- Outside the support everything vanishes.
        have hop : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
        have hev1 : ψ₁ =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hz] with y hy
          simp [hψ₁def, image_eq_zero_of_notMem_tsupport hy]
        have hev2 : ψ₂ =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hz] with y hy
          simp [hψ₂def, image_eq_zero_of_notMem_tsupport hy]
        have hevφ : φ =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hz] with y hy
          simp [image_eq_zero_of_notMem_tsupport hy]
        have h1 : fderiv ℝ ψ₁ z = 0 := by rw [hev1.fderiv_eq]; exact fderiv_const_apply 0
        have h2 : fderiv ℝ ψ₂ z = 0 := by rw [hev2.fderiv_eq]; exact fderiv_const_apply 0
        have h3 : fderiv ℝ φ z = 0 := by rw [hevφ.fderiv_eq]; exact fderiv_const_apply 0
        have h4 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [h1, h2, h3, h4]
    -- Local integrability of the three products against `F`-data.
    have hFvloc : LocallyIntegrableOn (fun z => F z * v z) Ω := d4_locInt_mul hΩ hFcontOn hvloc
    have hFgvloc : LocallyIntegrableOn (fun z => F z * gv z) Ω := d4_locInt_mul hΩ hFcontOn hgvloc
    have hwvloc : LocallyIntegrableOn (fun z => (deriv F z * e) * v z) Ω :=
      d4_locInt_mul hΩ (hF'contOn.mul continuousOn_const) hvloc
    -- Continuity and support facts for the fderiv test weights.
    have hφcont : Continuous φ := hφ.continuous
    have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) e) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) e) :=
      HasCompactSupport.fderiv_apply ℝ hcs e
    have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) e) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ e).trans htsupp
    have hcont_dψ₁ : Continuous (fun z => (fderiv ℝ ψ₁ z) e) :=
      (hψ₁sm.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcont_dψ₂ : Continuous (fun z => (fderiv ℝ ψ₂ z) e) :=
      (hψ₂sm.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs_dψ₁ : HasCompactSupport (fun z => (fderiv ℝ ψ₁ z) e) :=
      HasCompactSupport.fderiv_apply ℝ hψ₁cs e
    have hcs_dψ₂ : HasCompactSupport (fun z => (fderiv ℝ ψ₂ z) e) :=
      HasCompactSupport.fderiv_apply ℝ hψ₂cs e
    have hts_dψ₁ : tsupport (fun z => (fderiv ℝ ψ₁ z) e) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ e).trans hψ₁ts
    have hts_dψ₂ : tsupport (fun z => (fderiv ℝ ψ₂ z) e) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ e).trans hψ₂ts
    -- Integrability of all pieces.
    have i_a1 : Integrable (fun z => ((fderiv ℝ ψ₁ z) e) • v z) volume :=
      d2_integ_real _ hcont_dψ₁ hcs_dψ₁ hts_dψ₁ hvloc
    have i_a2 : Integrable (fun z => ((fderiv ℝ ψ₂ z) e) • v z) volume :=
      d2_integ_real _ hcont_dψ₂ hcs_dψ₂ hts_dψ₂ hvloc
    have i_b1 : Integrable (fun z => ψ₁ z • gv z) volume :=
      d2_integ_real _ hψ₁sm.continuous hψ₁cs hψ₁ts hgvloc
    have i_b2 : Integrable (fun z => ψ₂ z • gv z) volume :=
      d2_integ_real _ hψ₂sm.continuous hψ₂cs hψ₂ts hgvloc
    have i_c : Integrable (fun z => φ z • ((deriv F z * e) * v z)) volume :=
      d2_integ_real _ hφcont hcs htsupp hwvloc
    have i_d : Integrable (fun z => φ z • (F z * gv z)) volume :=
      d2_integ_real _ hφcont hcs htsupp hFgvloc
    have i_e : Integrable (fun z => ((fderiv ℝ φ z) e) • (F z * v z)) volume :=
      d2_integ_real _ hcont_dφ hcs_dφ hts_dφ hFvloc
    -- The two tested identities from the hypothesis.
    have E₁ : ∫ z, ((fderiv ℝ ψ₁ z) e) • v z = - ∫ z, ψ₁ z • gv z :=
      hgv ψ₁ hψ₁sm hψ₁cs hψ₁ts
    have E₂ : ∫ z, ((fderiv ℝ ψ₂ z) e) • v z = - ∫ z, ψ₂ z • gv z :=
      hgv ψ₂ hψ₂sm hψ₂cs hψ₂ts
    -- Multiply the second identity by `I` and add.
    have hEI : (∫ z, Complex.I * (((fderiv ℝ ψ₂ z) e) • v z))
        = - ∫ z, Complex.I * (ψ₂ z • gv z) := by
      have h1 := integral_smul (μ := (volume : Measure ℂ)) Complex.I
        (fun z => ((fderiv ℝ ψ₂ z) e) • v z)
      have h2 := integral_smul (μ := (volume : Measure ℂ)) Complex.I
        (fun z => ψ₂ z • gv z)
      simp only [smul_eq_mul] at h1 h2
      rw [h1, h2, E₂, mul_neg]
    have hSUM : (∫ z, (((fderiv ℝ ψ₁ z) e) • v z + Complex.I * (((fderiv ℝ ψ₂ z) e) • v z)))
        = - ∫ z, (ψ₁ z • gv z + Complex.I * (ψ₂ z • gv z)) := by
      rw [integral_add i_a1 (i_a2.const_mul Complex.I),
        integral_add i_b1 (i_b2.const_mul Complex.I), E₁, hEI]
      ring
    -- Rewrite both integrands via the pointwise identities.
    have hLcong : (fun z => ((fderiv ℝ ψ₁ z) e) • v z + Complex.I * (((fderiv ℝ ψ₂ z) e) • v z))
        = fun z => ((fderiv ℝ φ z) e) • (F z * v z) + φ z • ((deriv F z * e) * v z) := by
      funext z
      simp only [Complex.real_smul]
      linear_combination (v z) * (hid z)
    have hRcong : (fun z => ψ₁ z • gv z + Complex.I * (ψ₂ z • gv z))
        = fun z => φ z • (F z * gv z) := by
      funext z
      simp only [hψ₁def, hψ₂def, Complex.real_smul]
      push_cast
      linear_combination ((φ z : ℂ) * gv z) * (Complex.re_add_im (F z))
    rw [hLcong, hRcong] at hSUM
    rw [integral_add i_e i_c] at hSUM
    -- Split the goal's right-hand side and conclude.
    have hgoalR : (∫ z, φ z • (F z * gv z + (deriv F z * e) * v z))
        = (∫ z, φ z • (F z * gv z)) + ∫ z, φ z • ((deriv F z * e) * v z) := by
      rw [← integral_add i_d i_c]
      apply integral_congr_ae
      filter_upwards with z
      exact smul_add _ _ _
    rw [hgoalR]
    linear_combination hSUM
  have d7_ext_univ : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) (e : ℂ) {f g : ℂ → ℂ}
    (hfts : tsupport f ⊆ Ω) (hgts : tsupport g ⊆ Ω)
    (hfcs : HasCompactSupport f) (hgcs : HasCompactSupport g)
    (h : HasWeakDirDeriv e g f Ω), HasWeakDirDeriv e g f Set.univ := by
    intro Ω hΩ e f g hfts hgts hfcs hgcs h
    intro φ hφ hcs _
    change ∫ z, ((fderiv ℝ φ z) e) • f z = - ∫ z, φ z • g z
    -- Compact set carrying both supports, and two nested compact collars in `Ω`.
    set Kfg : Set ℂ := tsupport f ∪ tsupport g with hKfg
    have hKfgc : IsCompact Kfg := hfcs.union hgcs
    have hKfgΩ : Kfg ⊆ Ω := Set.union_subset hfts hgts
    obtain ⟨T1, hT1c, hKT1, hT1Ω⟩ := exists_compact_between hKfgc hΩ hKfgΩ
    obtain ⟨T2, hT2c, hT1T2, hT2Ω⟩ := exists_compact_between hT1c hΩ hT1Ω
    -- Smooth Urysohn cutoff: `0` outside `interior T2`, `1` on `T1`.
    obtain ⟨χ0, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ ℂ) (n := (⊤ : ℕ∞))
      (isOpen_interior.isClosed_compl) hT1c.isClosed
      (Set.disjoint_left.mpr fun z hzs hzt => hzs (hT1T2 hzt))
    set χ : ℂ → ℝ := fun z => χ0 z with hχdef
    have hχ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := contMDiff_iff_contDiff.mp χ0.contMDiff
    have hχ_zero : ∀ z ∉ interior T2, χ z = 0 := fun z hz => by simpa using hχ0 hz
    have hχ_one : ∀ z ∈ T1, χ z = 1 := fun z hz => by simpa using hχ1 hz
    have hχ_supp : Function.support χ ⊆ T2 := by
      intro z hz
      by_contra hzT
      exact hz (hχ_zero z fun hzi => hzT (interior_subset hzi))
    have hχ_cs : HasCompactSupport χ := HasCompactSupport.of_support_subset_isCompact hT2c hχ_supp
    have hχ_ts : tsupport χ ⊆ Ω := (closure_minimal hχ_supp hT2c.isClosed).trans hT2Ω
    -- Test the `Ω`-hypothesis with `χ·φ`.
    have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ z * φ z) := hχ_cd.mul hφ
    have hΦcs : HasCompactSupport (fun z => χ z * φ z) := hcs.mul_left
    have hΦts : tsupport (fun z => χ z * φ z) ⊆ Ω := (tsupport_mul_subset_left).trans hχ_ts
    have hfΦ := h (fun z => χ z * φ z) hΦsm hΦcs hΦts
    -- `χ ≡ 1` on the open set `interior T1 ⊇ Kfg`, so `fderiv χ = 0` there.
    have hχ1int : ∀ z ∈ interior T1, χ z = 1 := fun z hz => hχ_one z (interior_subset hz)
    have hfd0 : ∀ z ∈ interior T1, fderiv ℝ χ z = 0 := by
      intro z hz
      have hloc : χ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_interior.mem_nhds hz] with y hy
        exact hχ1int y hy
      rw [hloc.fderiv_eq]
      simp
    -- Pointwise product rule for the modified test function.
    have hpr : ∀ z, (fderiv ℝ (fun y => χ y * φ y) z) e
        = χ z * ((fderiv ℝ φ z) e) + φ z * ((fderiv ℝ χ z) e) := by
      intro z
      have hdχ : DifferentiableAt ℝ χ z := (hχ_cd.differentiable (by norm_num)).differentiableAt
      have hdφ : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
      rw [fderiv_fun_mul hdχ hdφ]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    -- Both sides of the tested identity coincide with the goal's sides.
    have hLHS : (∫ z, ((fderiv ℝ (fun y => χ y * φ y) z) e) • f z)
        = ∫ z, ((fderiv ℝ φ z) e) • f z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport f
      · have hzi : z ∈ interior T1 := hKT1 (Or.inl hz)
        rw [hpr z, hfd0 z hzi]
        simp [hχ1int z hzi]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hRHS : (∫ z, (χ z * φ z) • g z) = ∫ z, φ z • g z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport g
      · have hzi : z ∈ interior T1 := hKT1 (Or.inr hz)
        simp [hχ1int z hzi]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    rw [← hLHS, ← hRHS]
    exact hfΦ
  have d8_young : ∀ (ρ : ℂ → ℝ) (g : ℂ → ℂ) (hρmem : MemLp ρ 1 volume)
    (hgmem : MemLp g 1 volume), eLpNorm (MeasureTheory.convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
      ≤ eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
    intro ρ g hρmem hgmem
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hpt : ∀ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ
        ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume := by
      intro z
      rw [MeasureTheory.convolution_def]
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine lintegral_mono (fun t => ?_)
      rw [hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    have hgsm : AEStronglyMeasurable g volume := hgmem.1
    have hρsm : AEStronglyMeasurable ρ volume := hρmem.1
    have hjoint : AEMeasurable (Function.uncurry
        (fun z t => ‖ρ t‖ₑ * ‖g (z - t)‖ₑ)) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable
          (fun p : ℂ × ℂ => (L (ρ p.2)) (g (p.1 - p.2))) (volume.prod volume) :=
        AEStronglyMeasurable.convolution_integrand L hρsm hgsm
      have h2 : AEMeasurable (fun p : ℂ × ℂ => ‖(L (ρ p.2)) (g (p.1 - p.2))‖ₑ)
          (volume.prod volume) := h1.enorm
      refine h2.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Function.uncurry, hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    calc ∫⁻ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ ∂volume
        ≤ ∫⁻ z, ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ z, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume :=
          lintegral_lintegral_swap hjoint
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g (z - t)‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          rw [lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g z‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          congr 1
          exact lintegral_sub_right_eq_self (fun z => ‖g z‖ₑ) t
      _ = (∫⁻ t, ‖ρ t‖ₑ ∂volume) * ∫⁻ z, ‖g z‖ₑ ∂volume := by
          rw [lintegral_mul_const'' _ hρsm.enorm]
      _ = eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  have d9_bump_mass : ∀ (b : ContDiffBump (0 : ℂ)), eLpNorm (b.normed (volume : Measure ℂ)) 1 volume = 1 := by
    intro b
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hnn : ∀ t, 0 ≤ b.normed (volume : Measure ℂ) t := b.nonneg_normed
    have hcongr : ∀ t : ℂ, ‖b.normed (volume : Measure ℂ) t‖ₑ
        = ENNReal.ofReal (b.normed (volume : Measure ℂ) t) := fun t =>
      Real.enorm_eq_ofReal (hnn t)
    rw [lintegral_congr hcongr]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal b.integrable_normed
      (Filter.Eventually.of_forall hnn)]
    rw [b.integral_normed]
    simp
  have d6_memL2loc : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {v gx gy : ℂ → ℂ}
    (hvloc : LocallyIntegrableOn v Ω)
    (hgrad : HasWeakGradient gx gy v Ω)
    (hgx2 : MemLpLocOn gx 2 Ω) (hgy2 : MemLpLocOn gy 2 Ω), MemLpLocOn v 2 Ω := by
    intro Ω hΩ v gx gy hvloc hgrad hgx2 hgy2
    classical
    have hgxloc : LocallyIntegrableOn gx Ω := d1_locInt hΩ hgx2
    have hgyloc : LocallyIntegrableOn gy Ω := d1_locInt hΩ hgy2
    intro K hKΩ hKc
    -- Cutoff `η`: smooth, compactly supported in `Ω`, `≡ 1` on `K`.
    obtain ⟨T1, hT1c, hKT1, hT1Ω⟩ := exists_compact_between hKc hΩ hKΩ
    obtain ⟨T2, hT2c, hT1T2, hT2Ω⟩ := exists_compact_between hT1c hΩ hT1Ω
    obtain ⟨η0, hη0, hη1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ ℂ) (n := (⊤ : ℕ∞))
      (isOpen_interior.isClosed_compl) hT1c.isClosed
      (Set.disjoint_left.mpr fun z hzs hzt => hzs (hT1T2 hzt))
    set η : ℂ → ℝ := fun z => η0 z with hηdef
    have hη_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := contMDiff_iff_contDiff.mp η0.contMDiff
    have hη_zero : ∀ z ∉ interior T2, η z = 0 := fun z hz => by simpa using hη0 hz
    have hη_one : ∀ z ∈ T1, η z = 1 := fun z hz => by simpa using hη1 hz
    have hη_supp : Function.support η ⊆ T2 := by
      intro z hz
      by_contra hzT
      exact hz (hη_zero z fun hzi => hzT (interior_subset hzi))
    have hη_cs : HasCompactSupport η := HasCompactSupport.of_support_subset_isCompact hT2c hη_supp
    have hη_ts : tsupport η ⊆ Ω := (closure_minimal hη_supp hT2c.isClosed).trans hT2Ω
    have hη_cont : Continuous η := hη_cd.continuous
    -- The localized function `u = η•v` and its weak partials on `Ω`.
    set u : ℂ → ℂ := fun z => η z • v z with hudef
    set Gx : ℂ → ℂ := fun z => η z • gx z + ((fderiv ℝ η z) 1) • v z with hGxdef
    set Gy : ℂ → ℂ := fun z => η z • gy z + ((fderiv ℝ η z) Complex.I) • v z with hGydef
    have hwx : HasWeakDirDeriv 1 Gx u Ω := hgrad.1.smul_smooth hη_cd hvloc hgxloc
    have hwy : HasWeakDirDeriv Complex.I Gy u Ω := hgrad.2.smul_smooth hη_cd hvloc hgyloc
    -- Support and integrability bookkeeping.
    have hηfd_cont : ∀ e : ℂ, Continuous fun z => (fderiv ℝ η z) e := fun e =>
      (hη_cd.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hηfd_ts : ∀ e : ℂ, tsupport (fun z => (fderiv ℝ η z) e) ⊆ Ω := fun e =>
      (tsupport_fderiv_apply_subset ℝ e).trans hη_ts
    have hηfd_cs : ∀ e : ℂ, HasCompactSupport fun z => (fderiv ℝ η z) e := fun e =>
      HasCompactSupport.fderiv_apply ℝ hη_cs e
    have hu_int : Integrable u volume := d2_integ_real η hη_cont hη_cs hη_ts hvloc
    have hGx_int : Integrable Gx volume :=
      (d2_integ_real η hη_cont hη_cs hη_ts hgxloc).add
        (d2_integ_real _ (hηfd_cont 1) (hηfd_cs 1) (hηfd_ts 1) hvloc)
    have hGy_int : Integrable Gy volume :=
      (d2_integ_real η hη_cont hη_cs hη_ts hgyloc).add
        (d2_integ_real _ (hηfd_cont Complex.I) (hηfd_cs Complex.I) (hηfd_ts Complex.I) hvloc)
    have hu_li : MeasureTheory.LocallyIntegrable u := hu_int.locallyIntegrable
    have hGx_li : MeasureTheory.LocallyIntegrable Gx := hGx_int.locallyIntegrable
    have hGy_li : MeasureTheory.LocallyIntegrable Gy := hGy_int.locallyIntegrable
    -- Supports inside `tsupport η`.
    have hu_supp : Function.support u ⊆ tsupport η := by
      intro z hz
      simp only [hudef, Function.mem_support] at hz
      by_contra hzη
      have h0 : η z = 0 := image_eq_zero_of_notMem_tsupport hzη
      apply hz; simp [h0]
    have hG_supp : ∀ (g' : ℂ → ℂ) (e : ℂ),
        Function.support (fun z => η z • g' z + ((fderiv ℝ η z) e) • v z) ⊆ tsupport η := by
      intro g' e z hz
      simp only [Function.mem_support] at hz
      by_contra hzη
      have h0 : η z = 0 := image_eq_zero_of_notMem_tsupport hzη
      have h1 : (fderiv ℝ η z) e = 0 := by
        have hnot : z ∉ tsupport (fun z => (fderiv ℝ η z) e) := fun hmem =>
          hzη ((tsupport_fderiv_apply_subset ℝ e) hmem)
        simpa using image_eq_zero_of_notMem_tsupport hnot
      apply hz; simp [h0, h1]
    have hu_ts : tsupport u ⊆ Ω :=
      (closure_minimal hu_supp (isClosed_tsupport η)).trans hη_ts
    have hu_cs : HasCompactSupport u :=
      HasCompactSupport.of_support_subset_isCompact hη_cs hu_supp
    have hGx_ts : tsupport Gx ⊆ Ω :=
      (closure_minimal (hG_supp gx 1) (isClosed_tsupport η)).trans hη_ts
    have hGx_cs : HasCompactSupport Gx :=
      HasCompactSupport.of_support_subset_isCompact hη_cs (hG_supp gx 1)
    have hGy_ts : tsupport Gy ⊆ Ω :=
      (closure_minimal (hG_supp gy Complex.I) (isClosed_tsupport η)).trans hη_ts
    have hGy_cs : HasCompactSupport Gy :=
      HasCompactSupport.of_support_subset_isCompact hη_cs (hG_supp gy Complex.I)
    -- Weak derivatives on all of `ℂ`.
    have hwx_univ : HasWeakDirDeriv 1 Gx u Set.univ :=
      d7_ext_univ hΩ 1 hu_ts hGx_ts hu_cs hGx_cs hwx
    have hwy_univ : HasWeakDirDeriv Complex.I Gy u Set.univ :=
      d7_ext_univ hΩ Complex.I hu_ts hGy_ts hu_cs hGy_cs hwy
    -- Mollifier sequence.
    set bumps : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
        rIn_pos := by positivity,
        rIn_lt_rOut := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hbumps
    have hrout : Tendsto (fun n => (bumps n).rOut) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [hbumps] using h2
    set ρ : ℕ → ℂ → ℝ := fun n => (bumps n).normed volume with hρdef
    have hρ_sm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
      (bumps n).contDiff_normed
    have hρ_cs : ∀ n, HasCompactSupport (ρ n) := fun n => (bumps n).hasCompactSupport_normed
    set w : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hwdef
    have hw_cd : ∀ n, ContDiff ℝ 1 (w n) := by
      intro n
      have h1 : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) (ρ n) :=
        (hρ_sm n).of_le (by exact_mod_cast le_top)
      exact HasCompactSupport.contDiff_convolution_left _ (hρ_cs n) h1 hu_li
    have hw_cs : ∀ n, HasCompactSupport (w n) := fun n =>
      HasCompactSupport.convolution _ (hρ_cs n) hu_cs
    -- Directional derivatives of the mollification are mollified weak partials.
    have hw_fd1 : ∀ n z, (fderiv ℝ (w n) z) 1
        = MeasureTheory.convolution (ρ n) Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwx_univ hu_li hGx_li
        (hρ_sm n) (hρ_cs n) z
    have hw_fdI : ∀ n z, (fderiv ℝ (w n) z) Complex.I
        = MeasureTheory.convolution (ρ n) Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwy_univ hu_li hGy_li
        (hρ_sm n) (hρ_cs n) z
    -- Uniform `L²` bound from the endpoint Sobolev inequality.
    obtain ⟨C, hC0, hP1⟩ := eLpNorm_two_le_eLpNorm_fderiv_one
    set M : ℝ≥0∞ := ENNReal.ofReal C * (eLpNorm Gx 1 volume + eLpNorm Gy 1 volume) with hMdef
    have hMlt : M < ⊤ := by
      rw [hMdef]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.mpr ⟨(memLp_one_iff_integrable.mpr hGx_int).2,
          (memLp_one_iff_integrable.mpr hGy_int).2⟩)
    have hwbd : ∀ n, eLpNorm (w n) 2 volume ≤ M := by
      intro n
      have h1 := hP1 (hw_cd n) (hw_cs n)
      have h2 := eLpNorm_fderiv_one_le_partials (hw_cd n)
      have h3 : eLpNorm (fun z => (fderiv ℝ (w n) z) 1) 1 volume ≤ eLpNorm Gx 1 volume := by
        rw [show (fun z => (fderiv ℝ (w n) z) 1)
            = MeasureTheory.convolution (ρ n) Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume from
          funext fun z => hw_fd1 n z]
        calc eLpNorm (MeasureTheory.convolution (ρ n) Gx
                (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
            ≤ eLpNorm (ρ n) 1 volume * eLpNorm Gx 1 volume :=
              d8_young (ρ n) Gx (memLp_one_iff_integrable.mpr (bumps n).integrable_normed)
                (memLp_one_iff_integrable.mpr hGx_int)
          _ = eLpNorm Gx 1 volume := by rw [d9_bump_mass (bumps n), one_mul]
      have h4 : eLpNorm (fun z => (fderiv ℝ (w n) z) Complex.I) 1 volume
          ≤ eLpNorm Gy 1 volume := by
        rw [show (fun z => (fderiv ℝ (w n) z) Complex.I)
            = MeasureTheory.convolution (ρ n) Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume from
          funext fun z => hw_fdI n z]
        calc eLpNorm (MeasureTheory.convolution (ρ n) Gy
                (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
            ≤ eLpNorm (ρ n) 1 volume * eLpNorm Gy 1 volume :=
              d8_young (ρ n) Gy (memLp_one_iff_integrable.mpr (bumps n).integrable_normed)
                (memLp_one_iff_integrable.mpr hGy_int)
          _ = eLpNorm Gy 1 volume := by rw [d9_bump_mass (bumps n), one_mul]
      calc eLpNorm (w n) 2 volume
          ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ (w n)) 1 volume := h1
        _ ≤ ENNReal.ofReal C * (eLpNorm Gx 1 volume + eLpNorm Gy 1 volume) := by
            gcongr
            exact h2.trans (add_le_add h3 h4)
        _ = M := rfl
    -- Almost-everywhere convergence of the mollifications.
    have hrr : ∀ᶠ n in atTop, (bumps n).rOut ≤ 2 * (bumps n).rIn :=
      Filter.Eventually.of_forall fun n => by
        simp only [hbumps]
        rw [mul_one_div]
    have hae : ∀ᵐ x ∂(volume : Measure ℂ),
        Tendsto (fun n => w n x) atTop (𝓝 (u x)) :=
      ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hrout hrr hu_li
    -- Fatou: the limit is in `L²` with the same bound.
    have heLp2 : ∀ h : ℂ → ℂ,
        eLpNorm h 2 volume = (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ) := by
      intro h
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
      rw [h2]
      congr 1
      apply lintegral_congr
      intro z
      rw [← ENNReal.rpow_natCast]
      norm_num
    have hcollapse : ∀ X : ℝ≥0∞, (X ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = X := by
      intro X
      rw [← ENNReal.rpow_mul]
      norm_num
    have hbdint : ∀ n, ∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume ≤ M ^ (2 : ℝ) := by
      intro n
      have h1 : (∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ) ≤ M := by
        rw [← heLp2 (w n)]; exact hwbd n
      calc ∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume
          = ((∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
            (hcollapse _).symm
        _ ≤ M ^ (2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    have hulim : ∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂volume ≤ M ^ (2 : ℝ) := by
      have hptw : ∀ᵐ z ∂(volume : Measure ℂ),
          (‖u z‖ₑ ^ (2 : ℕ)) = Filter.liminf (fun n => ‖w n z‖ₑ ^ (2 : ℕ)) atTop := by
        filter_upwards [hae] with z hz
        exact (((ENNReal.continuous_pow 2).tendsto _).comp hz.enorm).liminf_eq.symm
      calc ∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂volume
          = ∫⁻ z, Filter.liminf (fun n => ‖w n z‖ₑ ^ (2 : ℕ)) atTop ∂volume :=
            lintegral_congr_ae hptw
        _ ≤ Filter.liminf (fun n => ∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume) atTop :=
            lintegral_liminf_le' fun n =>
              ((ENNReal.continuous_pow 2).comp (hw_cd n).continuous.enorm).aemeasurable
        _ ≤ M ^ (2 : ℝ) := by
            refine Filter.liminf_le_of_le ?_ ?_
            · isBoundedDefault
            · intro b hb
              rcases (hb.and (Filter.Eventually.of_forall hbdint)).exists with ⟨n, hn1, hn2⟩
              exact hn1.trans hn2
    have hu2 : MemLp u 2 volume := by
      refine ⟨hu_int.aestronglyMeasurable, ?_⟩
      rw [heLp2 u]
      calc (∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ)
          ≤ (M ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hulim (by norm_num)
        _ = M := by rw [← ENNReal.rpow_mul]; norm_num
        _ < ⊤ := hMlt
    -- `v = u` on `K`, so `v ∈ L²(K)`.
    have huK : MemLp u 2 (volume.restrict K) := hu2.restrict K
    have hvu : u =ᵐ[volume.restrict K] v := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hKc.measurableSet]
      filter_upwards with z hz
      have h1 : η z = 1 := hη_one z (interior_subset (hKT1 hz))
      simp [hudef, h1]
    exact MemLp.ae_eq hvu huK
  have d10_memLp_mul : ∀ {Ω : Set ℂ} {m g : ℂ → ℂ}
    (hm : ContinuousOn m Ω) (hg : MemLpLocOn g 2 Ω), MemLpLocOn (fun z => m z * g z) 2 Ω := by
    intro Ω m g hm hg
    intro K hK hKc
    obtain ⟨Cb, hCb⟩ := hKc.exists_bound_of_continuousOn (hm.mono hK)
    refine MemLp.of_le_mul (c := Cb) (hg K hK hKc)
      (((hm.mono hK).aestronglyMeasurable hKc.measurableSet).mul (hg K hK hKc).1) ?_
    rw [ae_restrict_iff' hKc.measurableSet]
    filter_upwards with z hz
    calc ‖m z * g z‖ = ‖m z‖ * ‖g z‖ := norm_mul _ _
      _ ≤ Cb * ‖g z‖ := mul_le_mul_of_nonneg_right (hCb z hz) (norm_nonneg _)
  have d11_memLp_add : ∀ {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hf : MemLpLocOn f 2 Ω) (hg : MemLpLocOn g 2 Ω), MemLpLocOn (fun z => f z + g z) 2 Ω := by
    intro Ω f g hf hg
    exact fun K hK hKc =>
        (hf K hK hKc).add (hg K hK hKc)
  obtain ⟨gx, gy, hw, hgx2, hgy2, hcombo⟩ := hgrad
  have hgxloc : LocallyIntegrableOn gx Ω := d1_locInt hΩ hgx2
  have hgyloc : LocallyIntegrableOn gy Ω := d1_locInt hΩ hgy2
  have hv2 : MemLpLocOn v 2 Ω := d6_memL2loc hΩ hvloc hw hgx2 hgy2
  have hFcontOn : ContinuousOn F Ω := hF.continuousOn
  have hF'contOn : ContinuousOn (deriv F) Ω := (hF.analyticOnNhd hΩ).deriv.continuousOn
  refine ⟨fun z => F z * gx z + (deriv F z * 1) * v z,
    fun z => F z * gy z + (deriv F z * Complex.I) * v z,
    ⟨d5_weak_mul hΩ hF hvloc 1 hw.1 hgxloc,
      d5_weak_mul hΩ hF hvloc Complex.I hw.2 hgyloc⟩, ?_, ?_, ?_⟩
  · exact d11_memLp_add (d10_memLp_mul hFcontOn hgx2)
      (d10_memLp_mul (hF'contOn.mul continuousOn_const) hv2)
  · exact d11_memLp_add (d10_memLp_mul hFcontOn hgy2)
      (d10_memLp_mul (hF'contOn.mul continuousOn_const) hv2)
  · filter_upwards [hcombo] with z hz hzΩ
    have h := hz hzΩ
    linear_combination (F z) * h + (deriv F z * v z) * Complex.I_mul_I

open scoped ContDiff ENNReal in
set_option maxHeartbeats 400000 in
/-- **Chain rule under a holomorphic map.** If `φ` is holomorphic on the open
set `Ω` and `v` is continuous with weak `∂̄`-derivative `μ` (and `L²_loc`
gradient) on all of `ℂ`, then `v ∘ φ` has weak `∂̄`-derivative
`(μ∘φ)·conj(φ′)` on `Ω`:

`∂̄(v∘φ) = (∂̄v)(φ)·conj(φ′)` a.e. on `Ω`

(the `(∂v)(φ)·∂̄φ` term vanishes since `φ` is holomorphic). The `L²_loc`
class survives composition by the conformal invariance of the Dirichlet
integral together with local boundedness of the covering multiplicity of a
holomorphic map; critical points of `φ` are isolated and are absorbed by the
a.e. formulation. -/
theorem hasL2WeakDzbar_comp_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {φ v μ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ Ω)
    (hv : Continuous v)
    (hgrad : HasL2WeakDzbar v μ Set.univ) :
    HasL2WeakDzbar (fun z => v (φ z))
      (fun z => μ (φ z) * starRingEnd ℂ (deriv φ z)) Ω := by
  have d1_locInt : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : MemLpLocOn g 2 Ω), LocallyIntegrableOn g Ω := by
    intro Ω hΩ g hg
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk hkc
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    have h1le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    exact memLp_one_iff_integrable.mp ((hg k hk hkc).mono_exponent h1le)
  have d2_integ_real : ∀ {Ω : Set ℂ} (m : ℂ → ℝ) (hm : Continuous m)
    (hcsm : HasCompactSupport m) (htsuppm : tsupport m ⊆ Ω)
    {h : ℂ → ℂ} (hh : LocallyIntegrableOn h Ω), Integrable (fun z => m z • h z) volume := by
    intro Ω m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  have e2_conj_eq : ∀ (ζ : ℂ), (starRingEnd ℂ) ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    intro ζ
    apply Complex.ext <;> simp
  have e1_wirtinger_apply : ∀ (L : ℂ →L[ℝ] ℂ) (ζ : ℂ), L ζ = (1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I) * ζ
        + (1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I) * ((starRingEnd ℂ) ζ) := by
    intro L ζ
    have hdec : ζ = ζ.re • (1 : ℂ) + ζ.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    have hLdec : L ζ = (ζ.re : ℂ) * L 1 + (ζ.im : ℂ) * L Complex.I := by
      conv_lhs => rw [hdec]
      rw [map_add, _root_.map_smul, _root_.map_smul]
      simp only [Complex.real_smul]
    have h1 : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
    have h2 := e2_conj_eq ζ
    linear_combination hLdec + (-(1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I)) * h1
      + (-(1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) * h2
      + ((ζ.im : ℂ) * L Complex.I) * Complex.I_mul_I
  have e3_det : ∀ (c : ℂ), (ContinuousLinearMap.mul ℝ ℂ c).det = Complex.normSq c := by
    intro c
    have h := LinearMap.det_toMatrix Complex.basisOneI
      ((ContinuousLinearMap.mul ℝ ℂ c : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
    have hgoal : (ContinuousLinearMap.mul ℝ ℂ c).det
        = ((LinearMap.toMatrix Complex.basisOneI Complex.basisOneI)
            ((ContinuousLinearMap.mul ℝ ℂ c : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)).det := h.symm
    rw [hgoal, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply]
    rw [show Complex.basisOneI 0 = 1 by simp [Complex.coe_basisOneI],
      show Complex.basisOneI 1 = Complex.I by simp [Complex.coe_basisOneI]]
    simp only [Complex.coe_basisOneI_repr]
    show (c * 1).re * (c * Complex.I).im - (c * Complex.I).re * (c * 1).im
        = Complex.normSq c
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  have e4_inj_ball : ∀ {f : ℂ → ℂ} {a c : ℂ}
    (hf : HasStrictDerivAt f c a) (hc : c ≠ 0), ∃ r > 0, Set.InjOn f (Metric.ball a r) := by
    intro f a c hf hc
    have h := hf.eventually_left_inverse hc
    rw [Metric.eventually_nhds_iff_ball] at h
    obtain ⟨r, hr, hleft⟩ := h
    exact ⟨r, hr, fun x hx y hy hxy => by rw [← hleft x hx, ← hleft y hy, hxy]⟩
  have e5_fderiv_apply : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω), ∀ z ∈ Ω, ∀ e : ℂ, (fderiv ℝ φ z) e = deriv φ z * e := by
    intro Ω hΩ φ hφ
    intro z hz e
    have hdC : DifferentiableAt ℂ φ z := hφ.differentiableAt (hΩ.mem_nhds hz)
    obtain ⟨hr, hCR⟩ := differentiableAt_complex_iff_differentiableAt_real.mp hdC
    have h1 : (fderiv ℝ φ z) 1 = deriv φ z := by
      have hdz := dz_eq_deriv_of_differentiableAt hdC
      rw [dz, hCR, smul_eq_mul] at hdz
      linear_combination hdz + (1 / 2 : ℂ) * ((fderiv ℝ φ z) 1) * Complex.I_mul_I
    have hI : (fderiv ℝ φ z) Complex.I = Complex.I * deriv φ z := by
      rw [hCR, smul_eq_mul, h1]
    have hdec : e = e.re • (1 : ℂ) + e.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    calc (fderiv ℝ φ z) e
        = e.re • ((fderiv ℝ φ z) 1) + e.im • ((fderiv ℝ φ z) Complex.I) := by
          conv_lhs => rw [hdec]
          rw [map_add, _root_.map_smul, _root_.map_smul]
      _ = deriv φ z * e := by
          rw [h1, hI]
          simp only [Complex.real_smul]
          linear_combination (deriv φ z) * (Complex.re_add_im e)
  have e6_hasFDerivWithinAt : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {s : Set ℂ} (hs : s ⊆ Ω), ∀ z ∈ s, HasFDerivWithinAt φ (ContinuousLinearMap.mul ℝ ℂ (deriv φ z)) s z := by
    intro Ω hΩ φ hφ s hs
    intro z hz
    have hdC : DifferentiableAt ℂ φ z := hφ.differentiableAt (hΩ.mem_nhds (hs hz))
    have hdR : DifferentiableAt ℝ φ z :=
      (differentiableAt_complex_iff_differentiableAt_real.mp hdC).1
    have heq : fderiv ℝ φ z = ContinuousLinearMap.mul ℝ ℂ (deriv φ z) := by
      apply ContinuousLinearMap.ext
      intro w
      rw [e5_fderiv_apply hΩ hφ z (hs hz) w, ContinuousLinearMap.mul_apply']
    rw [← heq]
    exact hdR.hasFDerivAt.hasFDerivWithinAt
  have a_fiber_bound : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {p : ℂ} (hp : p ∈ Ω)
    (hnc : ¬ (∀ᶠ z in 𝓝 p, φ z = φ p)), ∃ r > 0, Metric.ball p r ⊆ Ω ∧ ∃ m : ℕ,
      ∀ w : ℂ, ({z ∈ Metric.ball p r | φ z = w}).Finite ∧
        ({z ∈ Metric.ball p r | φ z = w}).ncard ≤ m := by
    intro Ω hΩ φ hφ p hp hnc
    classical
    have hφa : AnalyticAt ℂ φ p := (hφ.analyticOnNhd hΩ) p hp
    have hg0a : AnalyticAt ℂ (fun z => φ z - φ p) p := hφa.sub analyticAt_const
    -- The order of vanishing of `φ - φ p` at `p` is a finite natural number.
    have hord_ne : analyticOrderAt (fun z => φ z - φ p) p ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      apply hnc
      filter_upwards [htop] with z hz
      exact sub_eq_zero.mp hz
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hord_ne
    obtain ⟨g, hga, hgp0, hfact⟩ :=
      (hg0a.analyticOrderAt_eq_natCast).mp hm.symm
    -- `m ≥ 1` because `φ p - φ p = 0` while `g p ≠ 0`.
    have hm1 : 1 ≤ m := by
      by_contra hm0
      have hm00 : m = 0 := by omega
      subst hm00
      have h0 := hfact.self_of_nhds
      simp at h0
      exact hgp0 h0.symm
    -- An `m`-th root `c` of `g p`.
    have hdeg : 0 < (Polynomial.X ^ m - Polynomial.C (g p) : Polynomial ℂ).degree := by
      rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < m) (g p)]
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    obtain ⟨c, hcroot⟩ := Complex.exists_root hdeg
    have hcm : c ^ m = g p := by
      have := hcroot
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at this
      exact sub_eq_zero.mp this
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega)] at hcm
      exact hgp0 hcm.symm
    -- The analytic `m`-th root `h` of `g` near `p`.
    set h : ℂ → ℂ := fun z => c * Complex.exp (Complex.log (g z / g p) / m) with hhdef
    have hgp_slit : g p / g p ∈ Complex.slitPlane := by
      rw [div_self hgp0]
      exact Complex.one_mem_slitPlane
    have hgdiv : AnalyticAt ℂ (fun z => g z / g p) p := hga.div analyticAt_const hgp0
    have hlog : AnalyticAt ℂ (fun z => Complex.log (g z / g p)) p := by
      have hclog : AnalyticAt ℂ Complex.log ((fun z => g z / g p) p) :=
        analyticAt_clog hgp_slit
      have := AnalyticAt.comp (g := Complex.log) (f := fun z => g z / g p) (x := p)
        hclog hgdiv
      simpa [Function.comp] using this
    have hm0C : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hh_a : AnalyticAt ℂ h p := by
      apply analyticAt_const.mul
      have hdivm : AnalyticAt ℂ (fun z => Complex.log (g z / g p) / m) p :=
        hlog.div analyticAt_const hm0C
      have := analyticAt_cexp.comp hdivm
      simpa [Function.comp] using this
    have hhp : h p = c := by
      rw [hhdef]
      simp only []
      rw [div_self hgp0, Complex.log_one, zero_div, Complex.exp_zero, mul_one]
    -- `h ^ m = g` near `p`.
    have hpow_ev : ∀ᶠ z in 𝓝 p, h z ^ m = g z := by
      have h1 : ∀ᶠ z in 𝓝 p, g z / g p ∈ Complex.slitPlane := by
        have hcont : ContinuousAt (fun z => g z / g p) p := hgdiv.continuousAt
        exact hcont.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hgp_slit)
      have h2 : ∀ᶠ z in 𝓝 p, g z ≠ 0 := hga.continuousAt.eventually_ne hgp0
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hhdef]
      simp only []
      rw [mul_pow, hcm]
      have hexp : Complex.exp (Complex.log (g z / g p) / m) ^ m
          = Complex.exp (Complex.log (g z / g p)) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        field_simp
      rw [hexp, Complex.exp_log (div_ne_zero hz2 hgp0)]
      field_simp
    -- The uniformizer `u = (z - p) · h` and its nonvanishing strict derivative.
    set u : ℂ → ℂ := fun z => (z - p) * h z with hudef
    have hu_a : AnalyticAt ℂ u p := (analyticAt_id.sub analyticAt_const).mul hh_a
    have hdu : HasDerivAt u (h p) p := by
      have hd1 : HasDerivAt (fun z : ℂ => z - p) 1 p := (hasDerivAt_id p).sub_const p
      have hd2 : HasDerivAt h (deriv h p) p := hh_a.differentiableAt.hasDerivAt
      have := hd1.mul hd2
      simpa using this
    have hu_strict : HasStrictDerivAt u (h p) p := by
      have hs := hu_a.hasStrictDerivAt
      rwa [hdu.deriv] at hs
    obtain ⟨r₁, hr₁, hinj⟩ := e4_inj_ball hu_strict (by rw [hhp]; exact hc0)
    -- Choose a ball where everything holds simultaneously.
    have hall : ∀ᶠ z in 𝓝 p, (φ z - φ p = (z - p) ^ m • g z ∧ h z ^ m = g z) ∧ z ∈ Ω :=
      (hfact.and hpow_ev).and
        (Filter.eventually_of_mem (hΩ.mem_nhds hp) (fun z hz => hz))
    rw [Metric.eventually_nhds_iff_ball] at hall
    obtain ⟨r₂, hr₂, hball⟩ := hall
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, m, ?_⟩
    · intro z hz
      exact (hball z (Metric.ball_subset_ball (min_le_right _ _) hz)).2
    intro w
    -- Fiber points solve `u z ^ m = w - φ p` and `u` is injective on the ball.
    set S : Set ℂ := {z ∈ Metric.ball p (min r₁ r₂) | φ z = w} with hSdef
    have hSsub : ∀ z ∈ S, u z ^ m = w - φ p := by
      rintro z ⟨hzball, hzw⟩
      have hz2 := hball z (Metric.ball_subset_ball (min_le_right _ _) hzball)
      have h1 : φ z - φ p = (z - p) ^ m * g z := by
        rw [hz2.1.1]; rw [smul_eq_mul]
      rw [hudef]
      simp only []
      rw [mul_pow, hz2.1.2, ← h1, hzw]
    -- The set of `m`-th roots of `w - φ p` has at most `m` elements.
    set R : Set ℂ := {ζ : ℂ | ζ ^ m = w - φ p} with hRdef
    have hpoly_ne : (Polynomial.X ^ m - Polynomial.C (w - φ p) : Polynomial ℂ) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (by omega) _
    have hRsub : R ⊆ ((Polynomial.X ^ m - Polynomial.C (w - φ p) :
        Polynomial ℂ).roots.toFinset : Set ℂ) := by
      intro ζ hζ
      simp only [Finset.coe_sort_coe, Multiset.mem_toFinset, Finset.mem_coe]
      rw [Polynomial.mem_roots hpoly_ne]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      rw [hζ]
      ring
    have hRfin : R.Finite :=
      Set.Finite.subset (Set.finite_coe_iff.mp (by infer_instance)) hRsub
    have hRcard : R.ncard ≤ m := by
      calc R.ncard ≤ ((Polynomial.X ^ m - Polynomial.C (w - φ p) :
            Polynomial ℂ).roots.toFinset : Set ℂ).ncard :=
            Set.ncard_le_ncard hRsub (Set.toFinite _)
        _ = (Polynomial.X ^ m - Polynomial.C (w - φ p) :
            Polynomial ℂ).roots.toFinset.card := Set.ncard_coe_finset _
        _ ≤ Multiset.card (Polynomial.X ^ m - Polynomial.C (w - φ p) :
            Polynomial ℂ).roots := Multiset.toFinset_card_le _
        _ ≤ (Polynomial.X ^ m - Polynomial.C (w - φ p) : Polynomial ℂ).natDegree :=
            Polynomial.card_roots' _
        _ = m := by
            rw [Polynomial.natDegree_X_pow_sub_C]
    -- Conclude via injectivity of `u`.
    have hinj' : Set.InjOn u S :=
      hinj.mono (fun z hz => Metric.ball_subset_ball (min_le_left _ _) hz.1)
    have himg : u '' S ⊆ R := by
      rintro ζ ⟨z, hz, rfl⟩
      exact hSsub z hz
    have hSfin : S.Finite :=
      Set.Finite.of_finite_image (hRfin.subset himg) hinj'
    refine ⟨hSfin, ?_⟩
    calc S.ncard = (u '' S).ncard := (Set.InjOn.ncard_image hinj').symm
      _ ≤ R.ncard := Set.ncard_le_ncard himg hRfin
      _ ≤ m := hRcard
  have b00_ncard_biUnion_le : ∀ {ι : Type} [DecidableEq ι] (t : Finset ι)
    (S : ι → Set ℂ) (hfin : ∀ i, (S i).Finite), (⋃ i ∈ t, S i).Finite ∧ (⋃ i ∈ t, S i).ncard ≤ ∑ i ∈ t, (S i).ncard := by
    intro ι _inst t S hfin
    classical
    induction t using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.set_biUnion_insert]
        refine ⟨(hfin a).union ih.1, ?_⟩
        calc (S a ∪ ⋃ i ∈ s, S i).ncard
            ≤ (S a).ncard + (⋃ i ∈ s, S i).ncard :=
              Set.ncard_union_le _ _
          _ ≤ (S a).ncard + ∑ i ∈ s, (S i).ncard := Nat.add_le_add_left ih.2 _
          _ = ∑ i ∈ insert a s, (S i).ncard :=
              (Finset.sum_insert (f := fun i => (S i).ncard) ha).symm
  have b0_count : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {K : Set ℂ} (hKΩ : K ⊆ Ω) (hKc : IsCompact K), ∃ N : ℕ, ∀ w : ℂ,
      ({z ∈ K | deriv φ z ≠ 0 ∧ φ z = w}).Finite ∧
      ({z ∈ K | deriv φ z ≠ 0 ∧ φ z = w}).ncard ≤ N := by
    intro Ω hΩ φ hφ K hKΩ hKc
    classical
    -- The open set where `φ` is locally constant.
    set C : Set ℂ := {z : ℂ | ∀ᶠ w in 𝓝 z, φ w = φ z} with hCdef
    have hCopen : IsOpen C := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      have hz' : ∀ᶠ w in 𝓝 z, φ w = φ z := hz
      rw [Metric.eventually_nhds_iff_ball] at hz'
      obtain ⟨r, hr, hconst⟩ := hz'
      rw [Metric.mem_nhds_iff]
      refine ⟨r, hr, ?_⟩
      intro y hy
      show ∀ᶠ w in 𝓝 y, φ w = φ y
      rw [Metric.eventually_nhds_iff_ball]
      obtain ⟨r', hr', hsub⟩ : ∃ r' > 0, Metric.ball y r' ⊆ Metric.ball z r :=
        ⟨r - dist y z, by simp [Metric.mem_ball.mp hy],
          Metric.ball_subset_ball' (by linarith)⟩
      exact ⟨r', hr', fun x hx => by rw [hconst x (hsub hx), hconst y hy]⟩
    -- Its complement traps all points with nonvanishing derivative.
    have hUC : ∀ z, deriv φ z ≠ 0 → z ∉ C := by
      intro z hd hzC
      apply hd
      have : deriv φ z = deriv (fun _ => φ z) z := Filter.EventuallyEq.deriv_eq hzC
      rw [this, deriv_const]
    -- Compactness of `K ∖ C` and the finite subcover of fiber-bounded balls.
    set Kd : Set ℂ := K ∩ Cᶜ with hKddef
    have hKdc : IsCompact Kd := hKc.inter_right hCopen.isClosed_compl
    have hmem : ∀ z : ℂ, z ∈ Kd → ¬ (∀ᶠ w in 𝓝 z, φ w = φ z) := by
      intro z hz
      exact hz.2
    by_cases hKdemp : Kd = ∅
    · refine ⟨0, fun w => ?_⟩
      have hsub : {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} ⊆ Kd := by
        rintro z ⟨hzK, hzd, _⟩
        exact ⟨hzK, hUC z hzd⟩
      rw [hKdemp] at hsub
      have : {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} = ∅ := Set.subset_empty_iff.mp hsub
      simp [this]
    -- Choose fiber-bounded balls at every point of `Kd`.
    have hchoice : ∀ z : Kd, ∃ r > 0, Metric.ball (z : ℂ) r ⊆ Ω ∧ ∃ m : ℕ,
        ∀ w : ℂ, ({x ∈ Metric.ball (z : ℂ) r | φ x = w}).Finite ∧
          ({x ∈ Metric.ball (z : ℂ) r | φ x = w}).ncard ≤ m := by
      intro z
      exact a_fiber_bound hΩ hφ (hKΩ z.2.1) (hmem z z.2)
    choose r hr hballΩ m hm using hchoice
    obtain ⟨t, ht⟩ := hKdc.elim_finite_subcover
      (fun z : Kd => Metric.ball (z : ℂ) (r z)) (fun z => Metric.isOpen_ball)
      (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hr ⟨z, hz⟩)⟩)
    refine ⟨∑ i ∈ t, m i, fun w => ?_⟩
    set fiber : Set ℂ := {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} with hfiberdef
    have hfibsub : fiber ⊆ ⋃ i ∈ t, {x ∈ Metric.ball (i : ℂ) (r i) | φ x = w} := by
      rintro z ⟨hzK, hzd, hzw⟩
      have hzKd : z ∈ Kd := ⟨hzK, hUC z hzd⟩
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hzKd)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hzi, hzw⟩
    obtain ⟨hUfin, hUcard⟩ := b00_ncard_biUnion_le t
      (fun i => {x ∈ Metric.ball (i : ℂ) (r i) | φ x = w}) (fun i => (hm i w).1)
    refine ⟨hUfin.subset hfibsub, ?_⟩
    calc fiber.ncard ≤ (⋃ i ∈ t, {x ∈ Metric.ball (i : ℂ) (r i) | φ x = w}).ncard :=
          Set.ncard_le_ncard hfibsub hUfin
      _ ≤ ∑ i ∈ t, ({x ∈ Metric.ball (i : ℂ) (r i) | φ x = w}).ncard := hUcard
      _ ≤ ∑ i ∈ t, m i := Finset.sum_le_sum (fun i _ => (hm i w).2)
  have b_cv : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {K : Set ℂ} (hKΩ : K ⊆ Ω) (hKc : IsCompact K), ∃ N : ℕ, ∀ q : ℂ → ℂ, Measurable q →
      (∫⁻ z in K, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        ≤ N * ∫⁻ w in φ '' K, ‖q w‖ₑ ^ (2 : ℕ) ∂volume := by
    intro Ω hΩ φ hφ K hKΩ hKc
    classical
    obtain ⟨N, hN⟩ := b0_count hΩ hφ hKΩ hKc
    have hφa : AnalyticOnNhd ℂ φ Ω := hφ.analyticOnNhd hΩ
    have hd'cont : ContinuousOn (deriv φ) Ω := hφa.deriv.continuousOn
    have hφcont : ContinuousOn φ Ω := hφ.continuousOn
    refine ⟨N, fun q hq => ?_⟩
    set G : ℂ → ℝ≥0∞ := fun w => ‖q w‖ₑ ^ (2 : ℕ) with hGdef
    have hGmeas : Measurable G := hq.enorm.pow_const 2
    -- The open set of noncritical points.
    set U : Set ℂ := Ω ∩ (deriv φ) ⁻¹' {(0 : ℂ)}ᶜ with hUdef
    have hUopen : IsOpen U := hd'cont.isOpen_inter_preimage hΩ isOpen_compl_singleton
    have hUsub : U ⊆ Ω := Set.inter_subset_left
    have hUne' : ∀ z ∈ U, deriv φ z ≠ 0 := by
      intro z hz
      have := hz.2
      simpa using this
    -- Step 1: the integrand vanishes off `U`.
    have hzeroKU : ∀ z ∈ K \ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) = 0 := by
      intro z hz
      have hzΩ : z ∈ Ω := hKΩ hz.1
      have hd0 : deriv φ z = 0 := by
        by_contra hne
        exact hz.2 ⟨hzΩ, by simpa using hne⟩
      rw [hd0]
      simp
    have hsplit : (∫⁻ z in K, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∫⁻ z in K ∩ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := by
      have hKeq : K = (K ∩ U) ∪ (K \ U) := (Set.inter_union_diff K U).symm
      conv_lhs => rw [hKeq]
      rw [lintegral_union (hKc.measurableSet.diff hUopen.measurableSet)
        (Set.disjoint_sdiff_right.mono_left Set.inter_subset_right)]
      have h0 : (∫⁻ z in K \ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume) = 0 := by
        rw [setLIntegral_congr_fun (hKc.measurableSet.diff hUopen.measurableSet)
          (fun z hz => hzeroKU z hz)]
        simp
      rw [h0, add_zero]
    rw [hsplit]
    -- Trivial case: `U` empty.
    rcases Set.eq_empty_or_nonempty U with hUemp | hUne
    · rw [hUemp]
      simp
    -- Injectivity balls inside `U` at every point of `U`.
    have hchoice : ∀ z : U, ∃ ρ > 0, Metric.ball (z : ℂ) ρ ⊆ U ∧
        Set.InjOn φ (Metric.ball (z : ℂ) ρ) := by
      intro z
      have hzU := z.2
      have hzΩ : (z : ℂ) ∈ Ω := hUsub hzU
      have hne : deriv φ (z : ℂ) ≠ 0 := hUne' _ hzU
      have hstrict : HasStrictDerivAt φ (deriv φ (z : ℂ)) (z : ℂ) :=
        (hφa _ hzΩ).hasStrictDerivAt
      obtain ⟨r₁, hr₁, hinj⟩ := e4_inj_ball hstrict hne
      obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp hUopen _ hzU
      exact ⟨min r₁ r₂, lt_min hr₁ hr₂,
        (Metric.ball_subset_ball (min_le_right _ _)).trans hball,
        hinj.mono (Metric.ball_subset_ball (min_le_left _ _))⟩
    choose ρ hρ hρU hρinj using hchoice
    -- Countable subcover of `U` by these balls.
    obtain ⟨T, hTcnt, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun z : U => Metric.ball (z : ℂ) (ρ z)) (fun z => Metric.isOpen_ball)
    have hUcover : U ⊆ ⋃ i ∈ T, Metric.ball ((i : U) : ℂ) (ρ i) := by
      intro z hz
      rw [hTeq]
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hρ _)⟩
    have hTne : T.Nonempty := by
      rcases hUne with ⟨z, hz⟩
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := hUcover hz
      simp [hemp] at this
    obtain ⟨f, hf⟩ := hTcnt.exists_eq_range hTne
    set B : ℕ → Set ℂ := fun n => Metric.ball ((f n : U) : ℂ) (ρ (f n)) with hBdef
    have hBmeas : ∀ n, MeasurableSet (B n) := fun n => Metric.isOpen_ball.measurableSet
    have hBU : ∀ n, B n ⊆ U := fun n => hρU (f n)
    have hBinj : ∀ n, Set.InjOn φ (B n) := fun n => hρinj (f n)
    have hUB : U ⊆ ⋃ n, B n := by
      intro z hz
      obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.mp (hUcover hz)
      have : i ∈ Set.range f := by rw [← hf]; exact hiT
      obtain ⟨n, rfl⟩ := this
      exact Set.mem_iUnion.mpr ⟨n, hzi⟩
    -- Disjointify.
    set D : ℕ → Set ℂ := disjointed B with hDdef
    have hDmeas : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hBmeas
    have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed B
    have hDB : ∀ n, D n ⊆ B n := fun n => disjointed_subset B n
    set E : ℕ → Set ℂ := fun n => (K ∩ U) ∩ D n with hEdef
    have hEmeas : ∀ n, MeasurableSet (E n) := fun n =>
      (hKc.measurableSet.inter hUopen.measurableSet).inter (hDmeas n)
    have hEdisj : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
      ((hDdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
    have hEB : ∀ n, E n ⊆ B n := fun n => (Set.inter_subset_right).trans (hDB n)
    have hEK : ∀ n, E n ⊆ K := fun n => (Set.inter_subset_left).trans Set.inter_subset_left
    have hEU : ∀ n, E n ⊆ U := fun n => (Set.inter_subset_left).trans Set.inter_subset_right
    have hEΩ : ∀ n, E n ⊆ Ω := fun n => (hEU n).trans hUsub
    have hEinj : ∀ n, Set.InjOn φ (E n) := fun n => (hBinj n).mono (hEB n)
    have hEunion : (⋃ n, E n) = K ∩ U := by
      rw [hEdef]
      rw [← Set.inter_iUnion]
      rw [iUnion_disjointed]
      exact Set.inter_eq_left.mpr (fun z hz => hUB hz.2)
    -- Step 2: decompose the integral.
    have hstep2 : (∫⁻ z in K ∩ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∑' n, ∫⁻ z in E n, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := by
      rw [← hEunion, lintegral_iUnion hEmeas hEdisj]
    -- Step 3: injective change of variables on each piece.
    have hstep3 : ∀ n, (∫⁻ z in E n, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∫⁻ w in φ '' E n, G w ∂volume := by
      intro n
      have hfd := e6_hasFDerivWithinAt hΩ hφ (hEΩ n)
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ)
        (hEmeas n) hfd (hEinj n) G
      rw [hcov]
      apply setLIntegral_congr_fun (hEmeas n)
      intro z _
      dsimp only
      rw [e3_det, abs_of_nonneg (Complex.normSq_nonneg _)]
      rw [show Complex.normSq (deriv φ z) = ‖deriv φ z‖ ^ 2 from Complex.normSq_eq_norm_sq _]
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      ring
    -- Step 4: sum the image integrals against the multiplicity bound.
    have hEimg_meas : ∀ n, MeasurableSet (φ '' E n) := fun n =>
      MeasurableSet.image_of_continuousOn_injOn (hEmeas n)
        (hφcont.mono (hEΩ n)) (hEinj n)
    have hKimg : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφcont.mono hKΩ)
    have hind : ∀ n, (∫⁻ w in φ '' E n, G w ∂volume)
        = ∫⁻ w, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w * G w ∂volume := by
      intro n
      rw [← lintegral_indicator (hEimg_meas n)]
      apply lintegral_congr
      intro w
      by_cases hw : w ∈ φ '' E n <;> simp [hw]
    -- Pointwise multiplicity bound.
    have hcount : ∀ w : ℂ, (∑' n, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w)
        ≤ (N : ℝ≥0∞) * (φ '' K).indicator (fun _ => (1 : ℝ≥0∞)) w := by
      intro w
      by_cases hw : w ∈ φ '' K
      · rw [Set.indicator_of_mem hw, mul_one]
        rw [ENNReal.tsum_eq_iSup_sum]
        apply iSup_le
        intro s
        obtain ⟨hfibfin, hfibcard⟩ := hN w
        set fib : Set ℂ := {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} with hfibdef
        set s' : Finset ℕ := s.filter (fun n => w ∈ φ '' E n) with hs'def
        have hsum : (∑ n ∈ s, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w)
            = (s'.card : ℝ≥0∞) := by
          rw [hs'def, Finset.card_filter]
          push_cast
          apply Finset.sum_congr rfl
          intro n _
          by_cases hn : w ∈ φ '' E n <;> simp [hn]
        rw [hsum]
        have hpick : ∀ n ∈ s', ∃ z, z ∈ E n ∧ φ z = w := by
          intro n hn
          obtain ⟨z, hz, hzw⟩ := (Finset.mem_filter.mp hn).2
          exact ⟨z, hz, hzw⟩
        choose pick hpick1 hpick2 using hpick
        have hmapsto : ∀ n (hn : n ∈ s'), pick n hn ∈ hfibfin.toFinset := by
          intro n hn
          rw [Set.Finite.mem_toFinset]
          have hzE := hpick1 n hn
          exact ⟨hEK n hzE, hUne' _ (hEU n hzE), hpick2 n hn⟩
        have hcardle : s'.card ≤ hfibfin.toFinset.card := by
          apply Finset.card_le_card_of_injOn (fun n => if hn : n ∈ s' then pick n hn else 0)
          · intro n hn
            dsimp only
            rw [dif_pos (Finset.mem_coe.mp hn)]
            exact hmapsto n (Finset.mem_coe.mp hn)
          · intro a ha b hb hab
            simp only [Finset.mem_coe] at ha hb
            dsimp only at hab
            rw [dif_pos ha, dif_pos hb] at hab
            by_contra hne
            have hdis := hEdisj hne
            have h1 := hpick1 a ha
            have h2 := hpick1 b hb
            rw [hab] at h1
            exact Set.disjoint_left.mp hdis h1 h2
        have hfibN : hfibfin.toFinset.card ≤ N := by
          rw [← Set.ncard_eq_toFinset_card fib hfibfin]
          exact hfibcard
        exact_mod_cast hcardle.trans hfibN
      · have hzero : ∀ n, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w = 0 := by
          intro n
          apply Set.indicator_of_notMem
          intro hmem
          exact hw (Set.image_mono (hEK n) hmem)
        simp only [hzero]
        simp
    calc (∫⁻ z in K ∩ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∑' n, ∫⁻ z in E n, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := hstep2
      _ = ∑' n, ∫⁻ w in φ '' E n, G w ∂volume := by
          apply tsum_congr
          intro n
          exact hstep3 n
      _ = ∑' n, ∫⁻ w, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w * G w ∂volume := by
          apply tsum_congr
          intro n
          exact hind n
      _ = ∫⁻ w, ∑' n, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w * G w ∂volume := by
          rw [← lintegral_tsum]
          intro n
          exact ((measurable_one.indicator (hEimg_meas n)).mul hGmeas).aemeasurable
      _ ≤ ∫⁻ w, ((N : ℝ≥0∞) * (φ '' K).indicator (fun _ => (1 : ℝ≥0∞)) w) * G w ∂volume := by
          apply lintegral_mono
          intro w
          dsimp only
          rw [ENNReal.tsum_mul_right]
          exact le_trans (mul_le_mul_right' (hcount w) (G w)) (le_of_eq (by ring))
      _ = N * ∫⁻ w in φ '' K, G w ∂volume := by
          rw [← lintegral_indicator hKimg.measurableSet]
          rw [← lintegral_const_mul (N : ℝ≥0∞) (hGmeas.indicator hKimg.measurableSet)]
          apply lintegral_congr
          intro w
          by_cases hw : w ∈ φ '' K <;> simp [hw, mul_assoc]
  have c_preimage_null : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {E : Set ℂ} (hE : volume E = 0), ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω → deriv φ z ≠ 0 → φ z ∉ E := by
    intro Ω hΩ φ hφ E hE
    classical
    obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
    have hd'cont : ContinuousOn (deriv φ) Ω := (hφ.analyticOnNhd hΩ).deriv.continuousOn
    -- The compact exhaustion of `Ω`.
    set Kn : ℕ → Set ℂ := fun n =>
      Metric.closedBall 0 n ∩ ⋂ y ∈ Ωᶜ, {z : ℂ | 1 / (n + 1 : ℝ) ≤ dist z y} with hKndef
    have hKn_closed : ∀ n, IsClosed (Kn n) := by
      intro n
      apply (Metric.isClosed_closedBall).inter
      apply isClosed_biInter
      intro y _
      exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    have hKn_compact : ∀ n, IsCompact (Kn n) := fun n =>
      (isCompact_closedBall (0 : ℂ) n).of_isClosed_subset (hKn_closed n)
        Set.inter_subset_left
    have hKn_sub : ∀ n, Kn n ⊆ Ω := by
      intro n z hz
      by_contra hzΩ
      have h1 := Set.mem_iInter₂.mp hz.2 z hzΩ
      simp only [Set.mem_setOf_eq, dist_self] at h1
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    have hKn_cover : ∀ z ∈ Ω, ∃ n, z ∈ Kn n := by
      intro z hz
      by_cases hcompl : Ωᶜ = ∅
      · obtain ⟨n, hn⟩ := exists_nat_ge (dist z 0)
        refine ⟨n, ⟨Metric.mem_closedBall.mpr hn, ?_⟩⟩
        rw [hcompl]
        simp
      · have hne : Ωᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hcompl
        have hzpos : 0 < Metric.infDist z Ωᶜ := by
          rw [← hΩ.isClosed_compl.notMem_iff_infDist_pos hne]
          simpa using hz
        obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hzpos
        obtain ⟨n₂, hn₂⟩ := exists_nat_ge (dist z 0)
        have hn2' : dist z 0 ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
          have hcast : ((n₂ : ℕ) : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
            exact_mod_cast le_max_right n₁ n₂
          linarith
        refine ⟨max n₁ n₂, ⟨Metric.mem_closedBall.mpr hn2', ?_⟩⟩
        apply Set.mem_iInter₂.mpr
        intro y hy
        simp only [Set.mem_setOf_eq]
        have h1 : 1 / ((max n₁ n₂ : ℕ) + 1 : ℝ) ≤ 1 / ((n₁ : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_left n₁ n₂
          linarith
        calc 1 / ((max n₁ n₂ : ℕ) + 1 : ℝ) ≤ 1 / ((n₁ : ℝ) + 1) := h1
          _ ≤ Metric.infDist z Ωᶜ := hn₁.le
          _ ≤ dist z y := Metric.infDist_le_dist_of_mem hy
    -- Per-compact vanishing of the transported indicator integrand.
    set q : ℂ → ℂ := E'.indicator (fun _ => 1) with hqdef
    have hqmeas : Measurable q := measurable_const.indicator hE'meas
    have hker : ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
        z ∈ Kn n → ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) = 0 := by
      intro n
      obtain ⟨N, hCV⟩ := b_cv hΩ hφ (hKn_sub n) (hKn_compact n)
      have himg0 : (∫⁻ w in φ '' Kn n, ‖q w‖ₑ ^ (2 : ℕ) ∂volume) = 0 := by
        have hpt : ∀ w, ‖q w‖ₑ ^ (2 : ℕ) = E'.indicator (fun _ => (1 : ℝ≥0∞)) w := by
          intro w
          by_cases hw : w ∈ E' <;> simp [hqdef, hw]
        apply le_antisymm _ (zero_le _)
        calc (∫⁻ w in φ '' Kn n, ‖q w‖ₑ ^ (2 : ℕ) ∂volume)
            = ∫⁻ w in φ '' Kn n, E'.indicator (fun _ => (1 : ℝ≥0∞)) w ∂volume := by
              apply lintegral_congr
              intro w
              exact hpt w
          _ ≤ ∫⁻ w, E'.indicator (fun _ => (1 : ℝ≥0∞)) w ∂volume :=
              setLIntegral_le_lintegral _ _
          _ = volume E' := by
              rw [lintegral_indicator hE'meas]
              simp
          _ = 0 := hE'null
      have hCV0 : (∫⁻ z in Kn n, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume) = 0 := by
        apply le_antisymm _ (zero_le _)
        calc (∫⁻ z in Kn n, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
            ≤ N * ∫⁻ w in φ '' Kn n, ‖q w‖ₑ ^ (2 : ℕ) ∂volume := hCV q hqmeas
          _ = 0 := by rw [himg0, mul_zero]
      -- Convert the vanishing integral to an a.e. statement.
      have hφae : AEMeasurable φ (volume.restrict (Kn n)) :=
        ((hφ.continuousOn.mono (hKn_sub n)).aemeasurable (hKn_compact n).measurableSet)
      have hd'ae : AEMeasurable (deriv φ) (volume.restrict (Kn n)) :=
        ((hd'cont.mono (hKn_sub n)).aemeasurable (hKn_compact n).measurableSet)
      have hint_meas : AEMeasurable
          (fun z => ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
          (volume.restrict (Kn n)) :=
        (((hqmeas.comp_aemeasurable hφae).enorm.pow_const 2).mul
          (hd'ae.enorm.pow_const 2))
      have hae0 := (lintegral_eq_zero_iff' hint_meas).mp hCV0
      rw [Filter.EventuallyEq, ae_restrict_iff' (hKn_compact n).measurableSet] at hae0
      filter_upwards [hae0] with z hz hzK
      exact hz hzK
    -- Combine over the exhaustion.
    have hall := (MeasureTheory.ae_all_iff).mpr hker
    filter_upwards [hall] with z hz hzΩ hzd hzE
    obtain ⟨n, hn⟩ := hKn_cover z hzΩ
    have h0 := hz n hn
    have hd_ne : ‖deriv φ z‖ₑ ^ (2 : ℕ) ≠ 0 := by
      apply pow_ne_zero
      rw [enorm_ne_zero]
      exact hzd
    have hq_ne : ‖q (φ z)‖ₑ ^ (2 : ℕ) ≠ 0 := by
      have hmem : φ z ∈ E' := hEE' hzE
      simp [hqdef, hmem]
    exact hq_ne (by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hd_ne)
  have p_conv2 : ∀ (h : ℂ → ℂ) (μ : Measure ℂ), eLpNorm h 2 μ = (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
    intro h μ
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
    rw [h2]
    congr 1
    apply lintegral_congr
    intro z
    rw [← ENNReal.rpow_natCast]
    norm_num
  have p_collapse : ∀ (X : ℝ≥0∞), (X ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = X := by
    intro X
    rw [← ENNReal.rpow_natCast (X ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
    norm_num
  have p_fin : ∀ {h : ℂ → ℂ} {μ : Measure ℂ} (hh : MemLp h 2 μ), (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) < ⊤ := by
    intro h μ hh
    have h1 := hh.2
    rw [p_conv2] at h1
    by_contra hX
    have hXtop : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) = ⊤ := by
      exact eq_top_iff.mpr (not_lt.mp hX)
    rw [hXtop, ENNReal.top_rpow_of_pos (by norm_num)] at h1
    exact (lt_irrefl _ h1).elim
  have p_mollify_L2 : ∀ {g : ℂ → ℂ} (hg_meas : Measurable g)
    (hg2 : MemLpLocOn g 2 Set.univ) {S : Set ℂ} (hSc : IsCompact S)
    (bumps : ℕ → ContDiffBump (0 : ℂ))
    (hrout : Tendsto (fun n => (bumps n).rOut) atTop (𝓝 0))
    (hrout1 : ∀ n, (bumps n).rOut ≤ 1), Tendsto (fun n => ∫⁻ w in S,
        ‖MeasureTheory.convolution ((bumps n).normed volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w - g w‖ₑ ^ (2 : ℕ) ∂volume)
      atTop (𝓝 0) := by
    intro g hg_meas hg2 S hSc bumps hrout hrout1
    classical
    set D' : Set ℂ := Metric.cthickening 2 S with hD'def
    have hD'c : IsCompact D' := hSc.cthickening
    have hSD' : S ⊆ D' := Metric.self_subset_cthickening S
    set gD : ℂ → ℂ := D'.indicator g with hgDdef
    have hgD_meas : Measurable gD := hg_meas.indicator hD'c.measurableSet
    have hgD2 : MemLp gD 2 volume := by
      refine ⟨hgD_meas.aestronglyMeasurable, ?_⟩
      rw [hgDdef, eLpNorm_indicator_eq_eLpNorm_restrict hD'c.measurableSet]
      exact (hg2 D' (Set.subset_univ _) hD'c).2
    -- The two mollifications agree on `S`, and so do the functions.
    have hagree : ∀ n, ∀ w ∈ S,
        MeasureTheory.convolution ((bumps n).normed volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w
        = MeasureTheory.convolution ((bumps n).normed volume) gD
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w := by
      intro n w hw
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      by_cases ht : t ∈ tsupport ((bumps n).normed volume)
      · have htball : ‖t‖ ≤ (bumps n).rOut := by
          have := (bumps n).tsupport_normed_eq (μ := volume) ▸ ht
          simpa [dist_eq_norm] using Metric.mem_closedBall.mp this
        have hwt : w - t ∈ D' := by
          apply Metric.mem_cthickening_of_dist_le (w - t) w 2 _ hw
          rw [dist_eq_norm]
          simpa using htball.trans ((hrout1 n).trans (by norm_num))
        rw [hgDdef]
        rw [Set.indicator_of_mem hwt]
      · have h0 : (bumps n).normed volume t = 0 := image_eq_zero_of_notMem_tsupport ht
        rw [h0]
        simp
    have hagree2 : ∀ w ∈ S, g w = gD w := fun w hw => by
      rw [hgDdef, Set.indicator_of_mem (hSD' hw)]
    -- Reduce to the global `L²` convergence for `gD`.
    have hglobal := eLpNorm_convolution_normed_sub_tendsto_zero hgD2 bumps hrout
    have hbound : ∀ n, (∫⁻ w in S,
        ‖MeasureTheory.convolution ((bumps n).normed volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w - g w‖ₑ ^ (2 : ℕ) ∂volume)
        ≤ (eLpNorm (MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) 2 volume) ^ (2 : ℕ) := by
      intro n
      have hstep : (∫⁻ w in S,
          ‖MeasureTheory.convolution ((bumps n).normed volume) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume w - g w‖ₑ ^ (2 : ℕ) ∂volume)
          = ∫⁻ w in S,
          ‖(MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) w‖ₑ ^ (2 : ℕ) ∂volume := by
        apply setLIntegral_congr_fun hSc.measurableSet
        intro w hw
        dsimp only
        rw [hagree n w hw, Pi.sub_apply, hagree2 w hw]
      rw [hstep]
      calc (∫⁻ w in S,
          ‖(MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) w‖ₑ ^ (2 : ℕ) ∂volume)
          ≤ ∫⁻ w, ‖(MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) w‖ₑ ^ (2 : ℕ) ∂volume :=
            setLIntegral_le_lintegral _ _
        _ = (eLpNorm (MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) 2 volume) ^ (2 : ℕ) := by
            rw [p_conv2, p_collapse]
    have hsq : Tendsto (fun n => (eLpNorm (MeasureTheory.convolution
        ((bumps n).normed volume) gD (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD)
        2 volume) ^ (2 : ℕ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_pow 2).tendsto 0).comp hglobal
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
      (fun n => zero_le _) hbound
  have e7_conj_enorm : ∀ (w : ℂ), ‖(starRingEnd ℂ) w‖ₑ = ‖w‖ₑ := by
    intro w
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    congr 1
    simp
  have e7_habs : ∀ (a b d e : ℂ), ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
      + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
    ≤ (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
    intro a b d e
    have hIb : ∀ x y : ℂ, ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
      intro x y
      calc ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := by
            rw [sub_eq_add_neg]
            exact (enorm_add_le _ _).trans (by rw [enorm_neg])
        _ = ‖x‖ₑ + ‖y‖ₑ := by
            rw [enorm_mul]
            congr 1
            rw [← ofReal_norm_eq_enorm, Complex.norm_I]
            simp
    have hIb' : ∀ x y : ℂ, ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
      intro x y
      calc ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := enorm_add_le _ _
        _ = ‖x‖ₑ + ‖y‖ₑ := by
            rw [enorm_mul]
            congr 1
            rw [← ofReal_norm_eq_enorm, Complex.norm_I]
            simp
    have hhalf : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2) := by
      rw [← ofReal_norm_eq_enorm]
      congr 1
      simp
    calc ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
        + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
        ≤ ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)‖ₑ
          + ‖(1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ :=
          enorm_add_le _ _
      _ = ‖(1 / 2 : ℂ)‖ₑ * ‖a - Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ)
          + ‖(1 / 2 : ℂ)‖ₑ * ‖a + Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ) := by
          simp only [enorm_mul, e7_conj_enorm]
      _ ≤ ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)
          + ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
          gcongr
          · exact hIb a b
          · exact hIb' a b
      _ = (‖(1 / 2 : ℂ)‖ₑ + ‖(1 / 2 : ℂ)‖ₑ) * ((‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)) := by ring
      _ = (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
          rw [hhalf, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have e8_sum_sq : ∀ (a b : ℝ≥0∞), (a + b) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    intro a b
    rcases le_total a b with h | h
    · calc (a + b) ^ (2 : ℕ) ≤ (b + b) ^ (2 : ℕ) := by gcongr
        _ = 4 * b ^ (2 : ℕ) := by ring
        _ ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
            gcongr
            exact le_add_self
    · calc (a + b) ^ (2 : ℕ) ≤ (a + a) ^ (2 : ℕ) := by gcongr
        _ = 4 * a ^ (2 : ℕ) := by ring
        _ ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
            gcongr
            exact le_self_add
  have d_comp_weak : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ v : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) (hv : Continuous v)
    {gx gy : ℂ → ℂ} (hgx_meas : Measurable gx) (hgy_meas : Measurable gy)
    (hwx : HasWeakDirDeriv 1 gx v Set.univ)
    (hwy : HasWeakDirDeriv Complex.I gy v Set.univ)
    (hgx2 : MemLpLocOn gx 2 Set.univ) (hgy2 : MemLpLocOn gy 2 Set.univ) (e : ℂ), HasWeakDirDeriv e
      (fun z => (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
        + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
          * (starRingEnd ℂ) (deriv φ z * e))
      (fun z => v (φ z)) Ω := by
    intro Ω hΩ φ v hφ hv gx gy hgx_meas hgy_meas hwx hwy hgx2 hgy2 e
    classical
    haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
    haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
    have hφa : AnalyticOnNhd ℂ φ Ω := hφ.analyticOnNhd hΩ
    have hφcont : ContinuousOn φ Ω := hφ.continuousOn
    have hd'cont : ContinuousOn (deriv φ) Ω := hφa.deriv.continuousOn
    have hφAtR : ∀ z ∈ Ω, AnalyticAt ℝ φ z := fun z hz =>
      @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
        IsScalarTower.right _ _ (hφa z hz)
    have hφdiffR : ∀ z ∈ Ω, DifferentiableAt ℝ φ z := fun z hz =>
      (hφAtR z hz).differentiableAt
    have hv_li : MeasureTheory.LocallyIntegrable v := hv.locallyIntegrable
    have hgx_li : MeasureTheory.LocallyIntegrable gx :=
      locallyIntegrableOn_univ.mp (d1_locInt isOpen_univ hgx2)
    have hgy_li : MeasureTheory.LocallyIntegrable gy :=
      locallyIntegrableOn_univ.mp (d1_locInt isOpen_univ hgy2)
    intro ψ hψ hcs htsupp
    change ∫ z, ((fderiv ℝ ψ z) e) • (v (φ z))
        = - ∫ z, ψ z • ((1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
          + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
            * (starRingEnd ℂ) (deriv φ z * e))
    -- The compact carrier of the test function and its image.
    have hKc : IsCompact (tsupport ψ) := hcs
    have hKΩ : tsupport ψ ⊆ Ω := htsupp
    have hKimgc : IsCompact (φ '' tsupport ψ) := hKc.image_of_continuousOn (hφcont.mono hKΩ)
    obtain ⟨N, hCV⟩ := b_cv hΩ hφ hKΩ hKc
    -- Mollifier sequence.
    set bumps : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
        rIn_pos := by positivity,
        rIn_lt_rOut := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hbumps
    have hrout : Tendsto (fun n => (bumps n).rOut) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [hbumps] using h2
    have hrout1 : ∀ n, (bumps n).rOut ≤ 1 := by
      intro n
      show 2 / ((n : ℝ) + 2) ≤ 1
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    set ρ : ℕ → ℂ → ℝ := fun n => (bumps n).normed volume with hρdef
    have hρ_sm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
      (bumps n).contDiff_normed
    have hρ_cs : ∀ n, HasCompactSupport (ρ n) := fun n => (bumps n).hasCompactSupport_normed
    set vn : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) v (ContinuousLinearMap.lsmul ℝ ℝ) volume with hvndef
    set cx : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcxdef
    set cy : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcydef
    have hvn_cd : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vn n) := fun n =>
      HasCompactSupport.contDiff_convolution_left _ (hρ_cs n) (hρ_sm n) hv_li
    have hvn_fd1 : ∀ n z, (fderiv ℝ (vn n) z) 1 = cx n z := fun n z =>
      fderiv_convolution_normed_apply_eq hwx hv_li hgx_li (hρ_sm n) (hρ_cs n) z
    have hvn_fdI : ∀ n z, (fderiv ℝ (vn n) z) Complex.I = cy n z := fun n z =>
      fderiv_convolution_normed_apply_eq hwy hv_li hgy_li (hρ_sm n) (hρ_cs n) z
    -- Chain rule for the mollified composition on `Ω`.
    have hchain : ∀ n, ∀ z ∈ Ω,
        (fderiv ℝ (fun y => vn n (φ y)) z) e
          = (1 / 2 : ℂ) * (cx n (φ z) - Complex.I * cy n (φ z)) * (deriv φ z * e)
            + (1 / 2 : ℂ) * (cx n (φ z) + Complex.I * cy n (φ z))
              * (starRingEnd ℂ) (deriv φ z * e) := by
      intro n z hz
      have hvdiff : DifferentiableAt ℝ (vn n) (φ z) :=
        ((hvn_cd n).differentiable (by norm_num)).differentiableAt
      have hcomp := fderiv_comp z hvdiff (hφdiffR z hz)
      have h1 : (fderiv ℝ (fun y => vn n (φ y)) z) e
          = (fderiv ℝ (vn n) (φ z)) ((fderiv ℝ φ z) e) := by
        have : (fun y => vn n (φ y)) = (vn n) ∘ φ := rfl
        rw [this, hcomp]
        rfl
      rw [h1, e5_fderiv_apply hΩ hφ z hz e,
        e1_wirtinger_apply (fderiv ℝ (vn n) (φ z)) (deriv φ z * e),
        hvn_fd1 n (φ z), hvn_fdI n (φ z)]
    -- Smoothness of the composition and the classical weak derivative.
    have hcomp_cd : ∀ n, ContDiffOn ℝ 1 (fun y => vn n (φ y)) Ω := by
      intro n
      intro z hz
      have h1 : ContDiffAt ℝ 1 φ z := (hφAtR z hz).contDiffAt
      have h2 : ContDiffAt ℝ 1 (vn n) (φ z) :=
        ((hvn_cd n).of_le (by exact_mod_cast le_top)).contDiffAt
      exact ((h2.comp z h1).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => rfl))).contDiffWithinAt
    have hweak_n : ∀ n, ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z))
        = - ∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) := by
      intro n
      exact HasWeakDirDeriv.of_contDiffOn hΩ (hcomp_cd n) ψ hψ hcs htsupp
    -- ==================== LHS convergence ====================
    have hvn_ptw : ∀ x, Tendsto (fun n => vn n x) atTop (𝓝 (v x)) := fun x =>
      ContDiffBump.convolution_tendsto_right_of_continuous hrout hv x
    -- Uniform bound of the mollifications on the image of the support.
    set D : Set ℂ := Metric.cthickening 1 (φ '' tsupport ψ) with hDdef
    have hDc : IsCompact D := hKimgc.cthickening
    obtain ⟨Cv, hCv⟩ := hDc.exists_bound_of_continuousOn hv.continuousOn
    have hvn_bd : ∀ n, ∀ x ∈ φ '' tsupport ψ, ‖vn n x‖ ≤ Cv := by
      intro n x hx
      rw [hvndef]
      simp only []
      rw [MeasureTheory.convolution_def]
      have hptbd : ∀ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (v (x - t))‖
          ≤ ρ n t * Cv := by
        intro t
        rw [ContinuousLinearMap.lsmul_apply]
        by_cases ht : t ∈ tsupport (ρ n)
        · have htball : ‖t‖ ≤ (bumps n).rOut := by
            have := (bumps n).tsupport_normed_eq (μ := volume) ▸ ht
            simpa [dist_eq_norm] using Metric.mem_closedBall.mp this
          have hxt : x - t ∈ D := by
            apply Metric.mem_cthickening_of_dist_le (x - t) x 1 _ hx
            rw [dist_eq_norm]
            simpa using htball.trans (hrout1 n)
          calc ‖ρ n t • v (x - t)‖ ≤ ‖ρ n t‖ * ‖v (x - t)‖ := norm_smul_le _ _
            _ = ρ n t * ‖v (x - t)‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg ((bumps n).nonneg_normed t)]
            _ ≤ ρ n t * Cv :=
                mul_le_mul_of_nonneg_left (hCv _ hxt) ((bumps n).nonneg_normed t)
        · have : ρ n t = 0 := image_eq_zero_of_notMem_tsupport ht
          rw [this]
          simp
      calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (v (x - t)) ∂volume‖
          ≤ ∫ t, ρ n t * Cv ∂volume := by
            apply norm_integral_le_of_norm_le
            · exact ((bumps n).integrable_normed).mul_const Cv
            · exact Filter.Eventually.of_forall hptbd
        _ = Cv := by
            rw [MeasureTheory.integral_mul_const, (bumps n).integral_normed, one_mul]
    -- Continuity of the truncated integrands.
    have hcont_dψe : Continuous (fun z => (fderiv ℝ ψ z) e) :=
      (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hts_dψe : tsupport (fun z => (fderiv ℝ ψ z) e) ⊆ tsupport ψ :=
      tsupport_fderiv_apply_subset ℝ e
    have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport ψ := fun z =>
      (em (z ∈ tsupport ψ)).elim (fun h => Or.inl (htsupp h)) Or.inr
    have hglue : ∀ (h : ℂ → ℂ), Continuous h →
        Continuous (fun z => ((fderiv ℝ ψ z) e) • h (φ z)) := by
      intro h hh
      rw [continuous_iff_continuousAt]
      intro z
      rcases hcover z with hz | hz
      · exact (hcont_dψe.continuousAt).smul
          ((hh.continuousAt).comp (hφcont.continuousAt (hΩ.mem_nhds hz)))
      · have hev : (fun z => ((fderiv ℝ ψ z) e) • h (φ z)) =ᶠ[𝓝 z] fun _ => 0 := by
          have hznot : z ∉ tsupport (fun z => (fderiv ℝ ψ z) e) := fun hmem => hz (hts_dψe hmem)
          filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hznot] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy]
          simp
        exact ContinuousAt.congr (continuousAt_const) hev.symm
    have hLHS : Tendsto (fun n => ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z))) atTop
        (𝓝 (∫ z, ((fderiv ℝ ψ z) e) • (v (φ z)))) := by
      apply MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun z => ‖(fderiv ℝ ψ z) e‖ * max Cv 0)
      · intro n
        exact (hglue (vn n) ((hvn_cd n).continuous)).aestronglyMeasurable
      · apply Continuous.integrable_of_hasCompactSupport
        · exact (hcont_dψe.norm).mul continuous_const
        · apply HasCompactSupport.mul_right
          exact (HasCompactSupport.fderiv_apply ℝ hcs e).norm
      · intro n
        apply Filter.Eventually.of_forall
        intro z
        by_cases hz : z ∈ tsupport ψ
        · calc ‖((fderiv ℝ ψ z) e) • vn n (φ z)‖
              ≤ ‖(fderiv ℝ ψ z) e‖ * ‖vn n (φ z)‖ := norm_smul_le _ _
            _ ≤ ‖(fderiv ℝ ψ z) e‖ * max Cv 0 :=
                mul_le_mul_of_nonneg_left
                  ((hvn_bd n (φ z) (Set.mem_image_of_mem φ hz)).trans (le_max_left _ _))
                  (norm_nonneg _)
        · have hznot : z ∉ tsupport (fun z => (fderiv ℝ ψ z) e) := fun hmem => hz (hts_dψe hmem)
          rw [image_eq_zero_of_notMem_tsupport hznot]
          simp
      · apply Filter.Eventually.of_forall
        intro z
        exact (hvn_ptw (φ z)).const_smul _
    -- ==================== RHS convergence ====================
    set Ge : ℂ → ℂ := fun z =>
      (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
        + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
          * (starRingEnd ℂ) (deriv φ z * e) with hGedef
    have hφae : AEMeasurable φ (volume.restrict (tsupport ψ)) :=
      (hφcont.mono hKΩ).aemeasurable hKc.measurableSet
    have hd'ae : AEMeasurable (deriv φ) (volume.restrict (tsupport ψ)) :=
      (hd'cont.mono hKΩ).aemeasurable hKc.measurableSet
    obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hcs
    -- Conjugation preserves the extended norm.
    have hconj_enorm : ∀ w : ℂ, ‖(starRingEnd ℂ) w‖ₑ = ‖w‖ₑ := by
      intro w
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      congr 1
      simp
    have henorm_smul_le : ∀ (r : ℝ) (x : ℂ), ‖r • x‖ₑ ≤ ‖r‖ₑ * ‖x‖ₑ := by
      intro r x
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (a := x),
        ← ofReal_norm_eq_enorm (a := r), ← ENNReal.ofReal_mul (norm_nonneg r)]
      exact ENNReal.ofReal_le_ofReal (norm_smul_le r x)
    -- The generic algebraic bound for the Wirtinger combination.
    have habs : ∀ a b d : ℂ,
        ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
          + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
        ≤ (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
      intro a b d
      have hIb : ∀ x y : ℂ, ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
        intro x y
        calc ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := by
              rw [sub_eq_add_neg]
              exact (enorm_add_le _ _).trans (by rw [enorm_neg])
          _ = ‖x‖ₑ + ‖y‖ₑ := by
              rw [enorm_mul]
              congr 1
              rw [← ofReal_norm_eq_enorm, Complex.norm_I]
              simp
      have hIb' : ∀ x y : ℂ, ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
        intro x y
        calc ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := enorm_add_le _ _
          _ = ‖x‖ₑ + ‖y‖ₑ := by
              rw [enorm_mul]
              congr 1
              rw [← ofReal_norm_eq_enorm, Complex.norm_I]
              simp
      have hhalf : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2) := by
        rw [← ofReal_norm_eq_enorm]
        congr 1
        simp
      calc ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
          + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
          ≤ ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)‖ₑ
            + ‖(1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ :=
            enorm_add_le _ _
        _ = ‖(1 / 2 : ℂ)‖ₑ * ‖a - Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ)
            + ‖(1 / 2 : ℂ)‖ₑ * ‖a + Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ) := by
            simp only [enorm_mul, hconj_enorm]
        _ ≤ ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)
            + ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
            gcongr
            · exact hIb a b
            · exact hIb' a b
        _ = (‖(1 / 2 : ℂ)‖ₑ + ‖(1 / 2 : ℂ)‖ₑ) * ((‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)) := by ring
        _ = (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
            rw [hhalf, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            norm_num
    -- The Cauchy–Schwarz + change-of-variables engine.
    have hCS : ∀ q : ℂ → ℂ, Measurable q →
        (∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume)
          ≤ (((N : ℝ≥0∞) * ∫⁻ w in φ '' tsupport ψ, ‖q w‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ))
            * (volume (tsupport ψ)) ^ (1 / 2 : ℝ) := by
      intro q hq
      have hHolder : (2 : ℝ).HolderConjugate 2 := by
        rw [Real.holderConjugate_iff]
        norm_num
      have hfae' : AEMeasurable (fun z => ‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ)
          (volume.restrict (tsupport ψ)) := by
        have h := (hq.comp_aemeasurable hφae).enorm.mul hd'ae.enorm
        simpa [Function.comp] using h
      have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (tsupport ψ))
        hHolder hfae' (aemeasurable_const (b := (1 : ℝ≥0∞)))
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one,
        Measure.restrict_apply_univ] at h
      refine h.trans ?_
      gcongr
      have hsq : (∫⁻ z in tsupport ψ, (‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ) ^ (2 : ℝ) ∂volume)
          = ∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := by
        apply lintegral_congr
        intro z
        conv_lhs => rw [show ((2 : ℝ)) = (((2 : ℕ) : ℝ)) by norm_num,
          ENNReal.rpow_natCast]
        rw [mul_pow]
      calc (∫⁻ z in tsupport ψ, (‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ) ^ (2 : ℝ) ∂volume)
          = ∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := hsq
        _ ≤ (N : ℝ≥0∞) * ∫⁻ w in φ '' tsupport ψ, ‖q w‖ₑ ^ (2 : ℕ) ∂volume := hCV q hq
    -- Finiteness of the limit integrand.
    have hIK_gx : (∫⁻ w in φ '' tsupport ψ, ‖gx w‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ :=
      p_fin (hgx2 (φ '' tsupport ψ) (Set.subset_univ _) hKimgc)
    have hIK_gy : (∫⁻ w in φ '' tsupport ψ, ‖gy w‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ :=
      p_fin (hgy2 (φ '' tsupport ψ) (Set.subset_univ _) hKimgc)
    have hCS_fin : ∀ q : ℂ → ℂ, Measurable q →
        (∫⁻ w in φ '' tsupport ψ, ‖q w‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ →
        (∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume) < ⊤ := by
      intro q hq hfin
      refine lt_of_le_of_lt (hCS q hq) ?_
      apply ENNReal.mul_lt_top
      · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        exact (ENNReal.mul_lt_top (by simp) hfin).ne
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKc.measure_lt_top.ne
    have hK_fin_x : (∫⁻ z in tsupport ψ, ‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume) < ⊤ :=
      hCS_fin gx hgx_meas hIK_gx
    have hK_fin_y : (∫⁻ z in tsupport ψ, ‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume) < ⊤ :=
      hCS_fin gy hgy_meas hIK_gy
    -- Integrability of the limit right-hand side.
    have hGe_int : Integrable (fun z => ψ z • Ge z) volume := by
      have hsupp : Function.support (fun z => ψ z • Ge z) ⊆ tsupport ψ := by
        intro z hz
        by_contra hzn
        apply hz
        show ψ z • Ge z = 0
        rw [image_eq_zero_of_notMem_tsupport hzn]
        simp
      rw [← integrableOn_iff_integrable_of_support_subset hsupp]
      constructor
      · apply AEMeasurable.aestronglyMeasurable
        have h1 : AEMeasurable (fun z => gx (φ z)) (volume.restrict (tsupport ψ)) :=
          hgx_meas.comp_aemeasurable hφae
        have h2 : AEMeasurable (fun z => gy (φ z)) (volume.restrict (tsupport ψ)) :=
          hgy_meas.comp_aemeasurable hφae
        have h3 : AEMeasurable (fun z => (starRingEnd ℂ) (deriv φ z * e))
            (volume.restrict (tsupport ψ)) :=
          (Complex.continuous_conj.measurable).comp_aemeasurable (hd'ae.mul_const e)
        have hGeae : AEMeasurable Ge (volume.restrict (tsupport ψ)) := by
          rw [hGedef]
          exact ((aemeasurable_const.mul (h1.sub (aemeasurable_const.mul h2))).mul
              (hd'ae.mul_const e)).add
            ((aemeasurable_const.mul (h1.add (aemeasurable_const.mul h2))).mul h3)
        exact (hψ.continuous.aemeasurable.restrict).smul hGeae
      · rw [hasFiniteIntegral_iff_enorm]
        have hptw : ∀ z ∈ tsupport ψ, ‖ψ z • Ge z‖ₑ
            ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
              * ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
          intro z _
          calc ‖ψ z • Ge z‖ₑ ≤ ‖ψ z‖ₑ * ‖Ge z‖ₑ := henorm_smul_le _ _
            _ ≤ ENNReal.ofReal Cψ * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ)
                * (‖deriv φ z‖ₑ * ‖e‖ₑ)) := by
                apply mul_le_mul'
                · rw [← ofReal_norm_eq_enorm]
                  exact ENNReal.ofReal_le_ofReal (hCψ z)
                · rw [hGedef]
                  exact habs _ _ _
            _ = ENNReal.ofReal Cψ * ‖e‖ₑ
                * ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
                ring
        calc (∫⁻ z in tsupport ψ, ‖ψ z • Ge z‖ₑ ∂volume)
            ≤ ∫⁻ z in tsupport ψ, ENNReal.ofReal Cψ * ‖e‖ₑ
              * ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume :=
              setLIntegral_mono' hKc.measurableSet hptw
          _ = ENNReal.ofReal Cψ * ‖e‖ₑ * ∫⁻ z in tsupport ψ,
              ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume := by
              rw [lintegral_const_mul' _ _ (by
                exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)]
          _ < ⊤ := by
              apply ENNReal.mul_lt_top
                (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)
              have hax : AEMeasurable (fun z => ‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
                  (volume.restrict (tsupport ψ)) := by
                have h := (hgx_meas.comp_aemeasurable hφae).enorm.mul hd'ae.enorm
                simpa [Function.comp] using h
              rw [lintegral_add_left' hax]
              exact ENNReal.add_lt_top.mpr ⟨hK_fin_x, hK_fin_y⟩
    -- Integrability of the mollified right-hand sides.
    have hloc_n : ∀ n, LocallyIntegrableOn
        (fun z => (fderiv ℝ (fun y => vn n (φ y)) z) e) Ω := fun n =>
      (((hcomp_cd n).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
        continuousOn_const).locallyIntegrableOn hΩ.measurableSet
    have i_n : ∀ n, Integrable
        (fun z => ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) volume := fun n =>
      d2_integ_real ψ hψ.continuous hcs htsupp (hloc_n n)
    -- The localized mollification convergence.
    have hXn := p_mollify_L2 hgx_meas hgx2 hKimgc bumps hrout hrout1
    have hYn := p_mollify_L2 hgy_meas hgy2 hKimgc bumps hrout hrout1
    -- The per-`n` difference bound.
    set Xn : ℕ → ℝ≥0∞ := fun n => ∫⁻ w in φ '' tsupport ψ,
      ‖cx n w - gx w‖ₑ ^ (2 : ℕ) ∂volume with hXndef
    set Yn : ℕ → ℝ≥0∞ := fun n => ∫⁻ w in φ '' tsupport ψ,
      ‖cy n w - gy w‖ₑ ^ (2 : ℕ) ∂volume with hYndef
    have hcx_cont : ∀ n, Continuous (cx n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρ_cs n)
        (hρ_sm n).continuous hgx_li
    have hcy_cont : ∀ n, Continuous (cy n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρ_cs n)
        (hρ_sm n).continuous hgy_li
    have hdiff_bd : ∀ n,
        ‖(∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) - ∫ z, ψ z • Ge z‖ₑ
        ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
          * ((((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
            + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) := by
      intro n
      rw [← integral_sub (i_n n) hGe_int]
      refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm _) ?_
      have hzero : ∀ z ∉ tsupport ψ,
          ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ = 0 := by
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport hz]
        simp
      have hred : (∫⁻ z, ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ ∂volume)
          = ∫⁻ z in tsupport ψ,
            ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ ∂volume := by
        rw [← lintegral_indicator hKc.measurableSet]
        apply lintegral_congr
        intro z
        by_cases hz : z ∈ tsupport ψ
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, hzero z hz]
      rw [hred]
      have hptw : ∀ z ∈ tsupport ψ,
          ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ
          ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
            * ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
              + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
        intro z hz
        have hzΩ : z ∈ Ω := htsupp hz
        have hdiff_eq : ((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z
            = (1 / 2 : ℂ) * ((cx n (φ z) - gx (φ z))
                - Complex.I * (cy n (φ z) - gy (φ z))) * (deriv φ z * e)
              + (1 / 2 : ℂ) * ((cx n (φ z) - gx (φ z))
                + Complex.I * (cy n (φ z) - gy (φ z)))
                * ((starRingEnd ℂ) (deriv φ z * e)) := by
          rw [hchain n z hzΩ, hGedef]
          ring
        calc ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ
            = ‖ψ z • (((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z)‖ₑ := by
              rw [show ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z
                = ψ z • (((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z) from
                  (smul_sub _ _ _).symm]
          _ ≤ ‖ψ z‖ₑ * ‖((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z‖ₑ :=
              henorm_smul_le _ _
          _ ≤ ENNReal.ofReal Cψ * ((‖cx n (φ z) - gx (φ z)‖ₑ + ‖cy n (φ z) - gy (φ z)‖ₑ)
              * (‖deriv φ z‖ₑ * ‖e‖ₑ)) := by
              apply mul_le_mul'
              · rw [← ofReal_norm_eq_enorm]
                exact ENNReal.ofReal_le_ofReal (hCψ z)
              · rw [hdiff_eq]
                exact habs _ _ _
          _ = ENNReal.ofReal Cψ * ‖e‖ₑ
              * ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
                + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
              ring
      calc (∫⁻ z in tsupport ψ,
          ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ ∂volume)
          ≤ ∫⁻ z in tsupport ψ, ENNReal.ofReal Cψ * ‖e‖ₑ
            * ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
              + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume :=
            setLIntegral_mono' hKc.measurableSet hptw
        _ = ENNReal.ofReal Cψ * ‖e‖ₑ * ∫⁻ z in tsupport ψ,
            ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
              + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume := by
            rw [lintegral_const_mul' _ _ (by
              exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)]
        _ ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
            * ((((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
              + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) := by
            apply mul_le_mul_left'
            have hax : AEMeasurable (fun z => ‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
                (volume.restrict (tsupport ψ)) := by
              have h := (((hcx_cont n).measurable.sub hgx_meas).comp_aemeasurable
                hφae).enorm.mul hd'ae.enorm
              simpa [Function.comp] using h
            rw [lintegral_add_left' hax]
            exact add_le_add
              (hCS (fun w => cx n w - gx w) ((hcx_cont n).measurable.sub hgx_meas))
              (hCS (fun w => cy n w - gy w) ((hcy_cont n).measurable.sub hgy_meas))
    -- The bound tends to zero.
    have hbound_tendsto : Tendsto (fun n => ENNReal.ofReal Cψ * ‖e‖ₑ
        * ((((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
          + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)))
        atTop (𝓝 0) := by
      have hX0 : Tendsto (fun n => (N : ℝ≥0∞) * Xn n) atTop (𝓝 0) := by
        have := (ENNReal.Tendsto.const_mul hXn (Or.inr (ENNReal.natCast_ne_top N)) :
          Tendsto (fun n => (N : ℝ≥0∞) * Xn n) atTop (𝓝 ((N : ℝ≥0∞) * 0)))
        simpa using this
      have hY0 : Tendsto (fun n => (N : ℝ≥0∞) * Yn n) atTop (𝓝 0) := by
        have := (ENNReal.Tendsto.const_mul hYn (Or.inr (ENNReal.natCast_ne_top N)) :
          Tendsto (fun n => (N : ℝ≥0∞) * Yn n) atTop (𝓝 ((N : ℝ≥0∞) * 0)))
        simpa using this
      have hrp0 : ((0 : ℝ≥0∞)) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      have hXr : Tendsto (fun n => ((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
        have h2 := hc.comp hX0
        rw [hrp0] at h2
        simpa [Function.comp] using h2
      have hYr : Tendsto (fun n => ((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
        have h2 := hc.comp hY0
        rw [hrp0] at h2
        simpa [Function.comp] using h2
      have hvol : (volume (tsupport ψ)) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKc.measure_lt_top.ne).ne
      have hXv : Tendsto (fun n => (((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hXr (Or.inr hvol)
        simpa using this
      have hYv : Tendsto (fun n => (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hYr (Or.inr hvol)
        simpa using this
      have hsum : Tendsto (fun n => (((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
          + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := hXv.add hYv
        simpa using this
      have hconst : (ENNReal.ofReal Cψ * ‖e‖ₑ) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
      have := ENNReal.Tendsto.const_mul hsum (Or.inr hconst)
      simpa using this
    -- Difference tends to zero in extended norm, hence the integrals converge.
    have henorm0 : Tendsto (fun n =>
        ‖(∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) - ∫ z, ψ z • Ge z‖ₑ)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto
        (fun n => zero_le _) hdiff_bd
    have hRHS : Tendsto (fun n => ∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e))
        atTop (𝓝 (∫ z, ψ z • Ge z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun n =>
          (‖(∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) - ∫ z, ψ z • Ge z‖ₑ).toReal)
          atTop (𝓝 ((0 : ℝ≥0∞)).toReal)  :=
        (ENNReal.tendsto_toReal (by simp)).comp henorm0
      simpa [toReal_enorm] using h1
    -- Conclude by uniqueness of limits.
    have hAn : Tendsto (fun n => ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z))) atTop
        (𝓝 (- ∫ z, ψ z • Ge z)) := by
      have heq : (fun n => ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z)))
          = fun n => - ∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) :=
        funext hweak_n
      rw [heq]
      exact hRHS.neg
    exact tendsto_nhds_unique hLHS hAn
  classical
  obtain ⟨gx0, gy0, hw0, hgx20, hgy20, hcombo0⟩ := hgrad
  have hφa : AnalyticOnNhd ℂ φ Ω := hφ.analyticOnNhd hΩ
  have hφcont : ContinuousOn φ Ω := hφ.continuousOn
  have hd'cont : ContinuousOn (deriv φ) Ω := hφa.deriv.continuousOn
  -- ================= measurable representatives of the witnesses =================
  have hUball : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨n, hn⟩ := exists_nat_ge (dist z 0)
    exact Set.mem_iUnion.mpr ⟨n, Metric.mem_closedBall.mpr hn⟩
  have hasm : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      AEStronglyMeasurable g volume := by
    intro g hg
    have h1 : ∀ n : ℕ, AEStronglyMeasurable g
        (volume.restrict (Metric.closedBall (0 : ℂ) n)) := fun n =>
      (hg _ (Set.subset_univ _) (isCompact_closedBall 0 n)).1
    have h2 : AEStronglyMeasurable g
        (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) :=
      aestronglyMeasurable_iUnion_iff.mpr h1
    rwa [hUball, Measure.restrict_univ] at h2
  have hgx_asm : AEStronglyMeasurable gx0 volume := hasm hgx20
  have hgy_asm : AEStronglyMeasurable gy0 volume := hasm hgy20
  set gx : ℂ → ℂ := hgx_asm.mk gx0 with hgxdef
  set gy : ℂ → ℂ := hgy_asm.mk gy0 with hgydef
  have hgx_meas : Measurable gx := hgx_asm.stronglyMeasurable_mk.measurable
  have hgy_meas : Measurable gy := hgy_asm.stronglyMeasurable_mk.measurable
  have haex : gx0 =ᵐ[volume] gx := hgx_asm.ae_eq_mk
  have haey : gy0 =ᵐ[volume] gy := hgy_asm.ae_eq_mk
  have hwd_congr : ∀ {g g' : ℂ → ℂ} {e : ℂ}, HasWeakDirDeriv e g v Set.univ →
      g =ᵐ[volume] g' → HasWeakDirDeriv e g' v Set.univ := by
    intro g g' e h hgg' ψ hψ hcs hts
    rw [h ψ hψ hcs hts]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hgg'] with z hz
    rw [hz]
  have hwx : HasWeakDirDeriv 1 gx v Set.univ := hwd_congr hw0.1 haex
  have hwy : HasWeakDirDeriv Complex.I gy v Set.univ := hwd_congr hw0.2 haey
  have hgx2 : MemLpLocOn gx 2 Set.univ := fun K hK hKc =>
    MemLp.ae_eq (ae_restrict_of_ae haex) (hgx20 K hK hKc)
  have hgy2 : MemLpLocOn gy 2 Set.univ := fun K hK hKc =>
    MemLp.ae_eq (ae_restrict_of_ae haey) (hgy20 K hK hKc)
  have hcombo : ∀ᵐ w ∂(volume : Measure ℂ), gx w + Complex.I * gy w = 2 * μ w := by
    filter_upwards [hcombo0, haex, haey] with w h1 h2 h3
    rw [← h2, ← h3]
    exact h1 (Set.mem_univ w)
  -- ================= L²loc membership, uniformly in the direction =================
  have hmem : ∀ e : ℂ, MemLpLocOn (fun z =>
      (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
      + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
        * (starRingEnd ℂ) (deriv φ z * e)) 2 Ω := by
    intro e K hK hKc
    obtain ⟨N, hCV⟩ := b_cv hΩ hφ hK hKc
    have hφae : AEMeasurable φ (volume.restrict K) :=
      (hφcont.mono hK).aemeasurable hKc.measurableSet
    have hd'ae : AEMeasurable (deriv φ) (volume.restrict K) :=
      (hd'cont.mono hK).aemeasurable hKc.measurableSet
    have hKimgc : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφcont.mono hK)
    have h1 : AEMeasurable (fun z => gx (φ z)) (volume.restrict K) :=
      hgx_meas.comp_aemeasurable hφae
    have h2 : AEMeasurable (fun z => gy (φ z)) (volume.restrict K) :=
      hgy_meas.comp_aemeasurable hφae
    have h3 : AEMeasurable (fun z => (starRingEnd ℂ) (deriv φ z * e))
        (volume.restrict K) :=
      (Complex.continuous_conj.measurable).comp_aemeasurable (hd'ae.mul_const e)
    constructor
    · exact (((aemeasurable_const.mul (h1.sub (aemeasurable_const.mul h2))).mul
          (hd'ae.mul_const e)).add
        ((aemeasurable_const.mul (h1.add (aemeasurable_const.mul h2))).mul
          h3)).aestronglyMeasurable
    · rw [p_conv2]
      apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      have hbd : ∀ z, ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
          + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
            * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ)
          ≤ 4 * ‖e‖ₑ ^ (2 : ℕ)
            * ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
              + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) := by
        intro z
        calc ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
            + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
              * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ)
            ≤ ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * (‖deriv φ z‖ₑ * ‖e‖ₑ)) ^ (2 : ℕ) := by
              gcongr
              exact e7_habs _ _ _ _
          _ = (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) ^ (2 : ℕ)
              * (‖deriv φ z‖ₑ ^ (2 : ℕ) * ‖e‖ₑ ^ (2 : ℕ)) := by
              rw [mul_pow, mul_pow]
          _ ≤ (4 * (‖gx (φ z)‖ₑ ^ (2 : ℕ) + ‖gy (φ z)‖ₑ ^ (2 : ℕ)))
              * (‖deriv φ z‖ₑ ^ (2 : ℕ) * ‖e‖ₑ ^ (2 : ℕ)) := by
              gcongr
              exact e8_sum_sq _ _
          _ = 4 * ‖e‖ₑ ^ (2 : ℕ)
              * ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
                + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) := by
              ring
      have haxsq : AEMeasurable
          (fun z => ‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
          (volume.restrict K) := by
        have h := (h1.enorm.pow_const 2).mul (hd'ae.enorm.pow_const 2)
        simpa using h
      have hfin : (∫⁻ z in K,
          ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
            + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) ∂volume) < ⊤ := by
        rw [lintegral_add_left' haxsq]
        apply ENNReal.add_lt_top.mpr
        constructor
        · refine lt_of_le_of_lt (hCV gx hgx_meas) ?_
          exact ENNReal.mul_lt_top (by simp)
            (p_fin (hgx2 (φ '' K) (Set.subset_univ _) hKimgc))
        · refine lt_of_le_of_lt (hCV gy hgy_meas) ?_
          exact ENNReal.mul_lt_top (by simp)
            (p_fin (hgy2 (φ '' K) (Set.subset_univ _) hKimgc))
      have htotal : (∫⁻ z in K,
          ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
          + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
            * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ := by
        calc (∫⁻ z in K, ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
            + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
              * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ) ∂volume)
            ≤ ∫⁻ z in K, 4 * ‖e‖ₑ ^ (2 : ℕ)
              * ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
                + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) ∂volume :=
              lintegral_mono (fun z => hbd z)
          _ = 4 * ‖e‖ₑ ^ (2 : ℕ) * ∫⁻ z in K,
              ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
                + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) ∂volume := by
              rw [lintegral_const_mul' _ _ (by
                exact ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top enorm_ne_top))]
          _ < ⊤ := by
              apply ENNReal.mul_lt_top _ hfin
              exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top enorm_lt_top)
      exact htotal.ne
  -- ================= the witnesses =================
  refine ⟨fun z => (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * 1)
      + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
        * (starRingEnd ℂ) (deriv φ z * 1),
    fun z => (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * Complex.I)
      + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
        * (starRingEnd ℂ) (deriv φ z * Complex.I),
    ⟨d_comp_weak hΩ hφ hv hgx_meas hgy_meas hwx hwy hgx2 hgy2 1,
      d_comp_weak hΩ hφ hv hgx_meas hgy_meas hwx hwy hgx2 hgy2 Complex.I⟩,
    hmem 1, hmem Complex.I, ?_⟩
  -- ================= the Wirtinger combination =================
  have hEnull : volume {w : ℂ | ¬ (gx w + Complex.I * gy w = 2 * μ w)} = 0 :=
    ae_iff.mp hcombo
  filter_upwards [c_preimage_null hΩ hφ hEnull] with z hz hzΩ
  by_cases hd : deriv φ z = 0
  · simp [hd]
  · have hφzE : φ z ∉ {w : ℂ | ¬ (gx w + Complex.I * gy w = 2 * μ w)} := hz hzΩ hd
    have hP : gx (φ z) + Complex.I * gy (φ z) = 2 * μ (φ z) := by
      by_contra hne
      exact hφzE hne
    have hconjI : (starRingEnd ℂ) (deriv φ z * Complex.I)
        = (starRingEnd ℂ) (deriv φ z) * (- Complex.I) := by
      rw [map_mul, Complex.conj_I]
    have hconj1 : (starRingEnd ℂ) (deriv φ z * 1) = (starRingEnd ℂ) (deriv φ z) := by
      rw [mul_one]
    rw [hconjI, hconj1]
    linear_combination ((starRingEnd ℂ) (deriv φ z)) * hP
      + ((1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z)
        - (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
          * ((starRingEnd ℂ) (deriv φ z))) * Complex.I_mul_I

/-! ## Invariance places the deformation field in the section space -/

/-- **Holomorphy of the deformation field off the poles.** If `v` is a sphere
vector field with weak `∂̄`-derivative `μ` and `μ` is `f`-invariant, then
`δv` is holomorphic on the complement of the pole set: its weak `∂̄` is
`f′·μ − (μ∘f)·conj(f′)`, which vanishes a.e. by the invariance law, and the
open-set Weyl lemma upgrades this to holomorphy. -/
theorem differentiableOn_deltaField {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ) :
    DifferentiableOn ℂ (deltaField r v)
      {z : ℂ | r.denReduced.eval z ≠ 0} := by
  -- The non-pole set is open (preimage of `{0}ᶜ` under the polynomial evaluation).
  have hΩ : IsOpen {z : ℂ | r.denReduced.eval z ≠ 0} :=
    isOpen_compl_singleton.preimage r.denReduced.continuous
  have hvcont : Continuous v := hv.1
  -- The finite-chart reading of the map is holomorphic off the poles: near a
  -- non-pole it agrees with the rational function `numReduced/denReduced`.
  have hφdiff : DifferentiableOn ℂ
      (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
      {z : ℂ | r.denReduced.eval z ≠ 0} := by
    intro w hw
    have hw' : r.denReduced.eval w ≠ 0 := hw
    have hev : (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
        =ᶠ[𝓝 w] fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x := by
      filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hw'] with x hx
      have hread : r.toSphereMap ↑x
          = if r.denReduced.eval x = 0 then (∞ : ℂ̂)
            else ((r.numReduced.eval x / r.denReduced.eval x : ℂ) : ℂ̂) := rfl
      rw [hread, if_neg hx]
      rfl
    have hdiv : DifferentiableAt ℂ
        (fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x) w :=
      ((r.numReduced.hasDerivAt w).div (r.denReduced.hasDerivAt w) hw').differentiableAt
    exact (hdiv.congr_of_eventuallyEq hev).differentiableWithinAt
  have hφcont : ContinuousOn
      (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
      {z : ℂ | r.denReduced.eval z ≠ 0} := hφdiff.continuousOn
  -- The finite-chart derivative is holomorphic off the poles (rational function
  -- with nonvanishing denominator).
  have hFdiff : DifferentiableOn ℂ (fderivRational r)
      {z : ℂ | r.denReduced.eval z ≠ 0} := by
    intro z hz
    have hz' : r.denReduced.eval z ≠ 0 := hz
    have hat : DifferentiableAt ℂ
        (fun z : ℂ => r.wronskian.eval z / (r.denReduced.eval z) ^ 2) z :=
      (r.wronskian.differentiableAt).div ((r.denReduced.differentiableAt).pow 2)
        (pow_ne_zero 2 hz')
    exact hat.differentiableWithinAt
  -- `L²_loc` on the non-pole set implies `L¹_loc` there.
  have hL2toLI : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 {z : ℂ | r.denReduced.eval z ≠ 0} →
      LocallyIntegrableOn g {z : ℂ | r.denReduced.eval z ≠ 0} := by
    intro g hg
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro K hK hKc
    have hmem : MemLp g 2 (volume.restrict K) := hg K hK hKc
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  -- Restrict the global weak-`∂̄` data of `v` to the non-pole set.
  have hgradΩ : HasL2WeakDzbar v μ {z : ℂ | r.denReduced.eval z ≠ 0} := by
    obtain ⟨gx, gy, hwg, hgx2, hgy2, hcomb⟩ := hgrad
    refine ⟨gx, gy, ⟨hwg.1.mono (Set.subset_univ _), hwg.2.mono (Set.subset_univ _)⟩,
      hgx2.mono (Set.subset_univ _), hgy2.mono (Set.subset_univ _), ?_⟩
    filter_upwards [hcomb] with z hz _
    exact hz (Set.mem_univ z)
  have hvloc : LocallyIntegrableOn v {z : ℂ | r.denReduced.eval z ≠ 0} :=
    hvcont.locallyIntegrable.locallyIntegrableOn _
  -- Weak `∂̄` of the product term `f′·v` is `f′·μ`.
  obtain ⟨gx1, gy1, hwg1, hgx1L2, hgy1L2, hcomb1⟩ :=
    hasL2WeakDzbar_holomorphic_mul hΩ hFdiff hvloc hgradΩ
  -- Weak `∂̄` of the composed term `v∘f` is `(μ∘f)·conj(f′)`.
  obtain ⟨gx2, gy2, hwg2, hgx2L2, hgy2L2, hcomb2⟩ :=
    hasL2WeakDzbar_comp_holomorphic hΩ hφdiff hvcont hgrad
  -- Local integrability of the two terms and the four weak-gradient witnesses.
  have hf1loc : LocallyIntegrableOn (fun z : ℂ => fderivRational r z * v z)
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    (hFdiff.continuousOn.mul hvcont.continuousOn).locallyIntegrableOn hΩ.measurableSet
  have hf2loc : LocallyIntegrableOn
      (fun z : ℂ => v (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))))
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    (hvcont.comp_continuousOn hφcont).locallyIntegrableOn hΩ.measurableSet
  have hgx1LI := hL2toLI hgx1L2
  have hgy1LI := hL2toLI hgy1L2
  have hgx2LI := hL2toLI hgx2L2
  have hgy2LI := hL2toLI hgy2L2
  -- Weak gradient of the difference `δv = f′·v − v∘f`.
  have hsubx : HasWeakDirDeriv 1 (fun z => gx1 z - gx2 z) (deltaField r v)
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    hwg1.1.sub hwg2.1 hf1loc hf2loc hgx1LI hgx2LI
  have hsuby : HasWeakDirDeriv Complex.I (fun z => gy1 z - gy2 z) (deltaField r v)
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    hwg1.2.sub hwg2.2 hf1loc hf2loc hgy1LI hgy2LI
  -- The Wirtinger combination of the difference vanishes a.e. on the non-pole
  -- set: it equals `2(f′·μ − (μ∘f)·conj(f′))`, killed by the invariance law.
  have hinv' : ∀ᵐ z ∂(volume : Measure ℂ),
      μ z * fderivRational r z
        = μ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
            * starRingEnd ℂ (fderivRational r z) := hinv
  have hcomb0 : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ {z : ℂ | r.denReduced.eval z ≠ 0} →
      (gx1 z - gx2 z) + Complex.I * (gy1 z - gy2 z) = 0 := by
    filter_upwards [hcomb1, hcomb2, hinv'] with z h1 h2 h3 hz
    have hz' : r.denReduced.eval z ≠ 0 := hz
    have e1 : gx1 z + Complex.I * gy1 z = 2 * (fderivRational r z * μ z) := h1 hz
    have e2 : gx2 z + Complex.I * gy2 z
        = 2 * (μ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
            * starRingEnd ℂ
              (deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) z)) := h2 hz
    rw [← fderivRational_eq_deriv_reading r hz'] at e2
    have hsplit : (gx1 z - gx2 z) + Complex.I * (gy1 z - gy2 z)
        = (gx1 z + Complex.I * gy1 z) - (gx2 z + Complex.I * gy2 z) := by ring
    rw [hsplit, e1, e2]
    linear_combination 2 * h3
  -- Continuity of `δv` on the non-pole set.
  have hδcont : ContinuousOn (deltaField r v) {z : ℂ | r.denReduced.eval z ≠ 0} := by
    have h1 : ContinuousOn (fun z : ℂ => fderivRational r z * v z)
        {z : ℂ | r.denReduced.eval z ≠ 0} :=
      hFdiff.continuousOn.mul hvcont.continuousOn
    have h2 : ContinuousOn
        (fun z : ℂ => v (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))))
        {z : ℂ | r.denReduced.eval z ≠ 0} :=
      hvcont.comp_continuousOn hφcont
    exact h1.sub h2
  -- Weyl's lemma on the open non-pole set.
  exact weyl_lemma_on hΩ hδcont ⟨hsubx, hsuby⟩ (hgx1LI.sub hgx2LI) (hgy1LI.sub hgy2LI) hcomb0

/-- **Pole-order bound.** At a root `p` of the reduced denominator of
multiplicity `k`, the deformation field has a pole of order at most `2k`:
there is a holomorphic `h` near `p` with `δv = h(z)/(z−p)^{2k}` off `p`.
Route: the transformed reading `−δv/f² = −(f′/f²)·v + u(1/f)` — where `u` is
the continuous infinity-chart reading `w ↦ w²·v(1/w)` of `v` and `f′/f²`,
`1/f` are holomorphic near `p` (coprimality of the reduced fraction) — is
continuous near `p` and weakly holomorphic (invariance transported through
the chain rule, essential boundedness of `μ` controlling the transported
gradient), hence holomorphic by the open-set Weyl lemma; then
`δv = −(that reading)·f²` and `f²` has a pole of order exactly `2k` at `p`. -/
theorem deltaField_pole_bound {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (hb : eLpNormEssSup μ volume < ⊤)
    {p : ℂ} (hp : r.denReduced.eval p = 0) :
    ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ p ∈ W ∧
      DifferentiableOn ℂ h W ∧
      ∀ z ∈ W, z ≠ p →
        deltaField r v z
          = h z / (z - p) ^ (2 * Polynomial.rootMultiplicity p r.denReduced) := by
  classical
  obtain ⟨hvcont, L, hL⟩ := hv
  -- The reduced denominator is a nonzero polynomial.
  have hQ0 : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  -- Coprimality of the reduced fraction: the numerator does not vanish at `p`.
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  have hNp : r.numReduced.eval p ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hcop
    intro hN0
    have heval := congrArg (Polynomial.eval p) hab
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hN0, hp,
      mul_zero, add_zero] at heval
    exact one_ne_zero heval.symm
  -- Factor out the root: `Q(z) = (z-p)^k · g(z)` with `g(p) ≠ 0`.
  obtain ⟨g, hgp, hfact⟩ : ∃ g : ℂ[X], g.eval p ≠ 0 ∧
      ∀ z : ℂ, r.denReduced.eval z
        = (z - p) ^ (Polynomial.rootMultiplicity p r.denReduced) * g.eval z := by
    refine ⟨r.denReduced /ₘ (Polynomial.X - Polynomial.C p)
        ^ (Polynomial.rootMultiplicity p r.denReduced),
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero p hQ0, fun z => ?_⟩
    conv_lhs => rw [← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq r.denReduced p]
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  set k : ℕ := Polynomial.rootMultiplicity p r.denReduced with hk
  -- The open neighborhood: both `g` and the numerator nonvanishing.
  set W : Set ℂ := {z : ℂ | g.eval z ≠ 0} ∩ {z : ℂ | r.numReduced.eval z ≠ 0} with hWdef
  have hWopen : IsOpen W :=
    (isOpen_compl_singleton.preimage g.continuous).inter
      (isOpen_compl_singleton.preimage r.numReduced.continuous)
  have hpW : p ∈ W := ⟨hgp, hNp⟩
  have hWnhds : W ∈ 𝓝 p := hWopen.mem_nhds hpW
  -- Off `p`, points of `W` are non-poles.
  have hQne : ∀ z ∈ W, z ≠ p → r.denReduced.eval z ≠ 0 := by
    intro z hz hzp
    rw [hfact z]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzp)) hz.1
  -- The finite reading of the map at non-poles.
  have hread : ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
      chartFiniteMap (r.toSphereMap ((z : ℂ̂)))
        = r.numReduced.eval z / r.denReduced.eval z := by
    intro z hz
    have h1 : r.toSphereMap ↑z
        = if r.denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := rfl
    rw [h1, if_neg hz]
    rfl
  have hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
      deltaField r v z = r.wronskian.eval z / (r.denReduced.eval z) ^ 2 * v z
        - v (r.numReduced.eval z / r.denReduced.eval z) := by
    intro z hz
    simp only [deltaField, fderivRational]
    rw [hread z hz]
  -- The limit value at `p` of `(z-p)^{2k} · δv`.
  set Lval : ℂ := r.wronskian.eval p * v p / (g.eval p) ^ 2
      - (r.numReduced.eval p) ^ 2 / (g.eval p) ^ 2 * L with hLval
  -- Eventual identity on the punctured neighborhood.
  have heq : (fun z => (z - p) ^ (2 * k) * deltaField r v z) =ᶠ[𝓝[≠] p]
      (fun z => r.wronskian.eval z * v z / (g.eval z) ^ 2
        - (r.numReduced.eval z) ^ 2 / (g.eval z) ^ 2
          * ((r.denReduced.eval z / r.numReduced.eval z) ^ 2
              * v ((r.denReduced.eval z / r.numReduced.eval z)⁻¹))) := by
    filter_upwards [nhdsWithin_le_nhds hWnhds, self_mem_nhdsWithin] with z hzW hzp
    have hzp' : z ≠ p := hzp
    have hgz : g.eval z ≠ 0 := hzW.1
    have hNz : r.numReduced.eval z ≠ 0 := hzW.2
    have htz : z - p ≠ 0 := sub_ne_zero.mpr hzp'
    have htzk : (z - p) ^ k ≠ 0 := pow_ne_zero _ htz
    have hQz0 : r.denReduced.eval z ≠ 0 := hQne z hzW hzp'
    rw [hδ z hQz0, inv_div, hfact z]
    field_simp
    ring
  -- Convergence of the right-hand side.
  have hcomp : Tendsto (fun z => r.denReduced.eval z / r.numReduced.eval z)
      (𝓝[≠] p) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun z => r.denReduced.eval z / r.numReduced.eval z) p :=
        (r.denReduced.continuous.continuousAt).div
          (r.numReduced.continuous.continuousAt) hNp
      have h0 : r.denReduced.eval p / r.numReduced.eval p = 0 := by
        rw [hp, zero_div]
      rw [← h0]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds hWnhds, self_mem_nhdsWithin] with z hzW hzp
      have hzp' : z ≠ p := hzp
      exact Set.mem_compl_singleton_iff.mpr
        (div_ne_zero (hQne z hzW hzp') hzW.2)
  have hL' : Tendsto (fun z => (r.denReduced.eval z / r.numReduced.eval z) ^ 2
      * v ((r.denReduced.eval z / r.numReduced.eval z)⁻¹)) (𝓝[≠] p) (𝓝 L) :=
    hL.comp hcomp
  have hT1 : Tendsto (fun z => r.wronskian.eval z * v z / (g.eval z) ^ 2)
      (𝓝 p) (𝓝 (r.wronskian.eval p * v p / (g.eval p) ^ 2)) :=
    ((r.wronskian.continuous.continuousAt.mul hvcont.continuousAt).div
      ((g.continuous.continuousAt).pow 2) (pow_ne_zero 2 hgp)).tendsto
  have hT2 : Tendsto (fun z => (r.numReduced.eval z) ^ 2 / (g.eval z) ^ 2)
      (𝓝 p) (𝓝 ((r.numReduced.eval p) ^ 2 / (g.eval p) ^ 2)) :=
    (((r.numReduced.continuous.continuousAt).pow 2).div
      ((g.continuous.continuousAt).pow 2) (pow_ne_zero 2 hgp)).tendsto
  have hlim : Tendsto (fun z => (z - p) ^ (2 * k) * deltaField r v z)
      (𝓝[≠] p) (𝓝 Lval) := by
    have hrhs : Tendsto (fun z => r.wronskian.eval z * v z / (g.eval z) ^ 2
        - (r.numReduced.eval z) ^ 2 / (g.eval z) ^ 2
          * ((r.denReduced.eval z / r.numReduced.eval z) ^ 2
              * v ((r.denReduced.eval z / r.numReduced.eval z)⁻¹)))
        (𝓝[≠] p) (𝓝 Lval) := by
      rw [hLval]
      exact (hT1.mono_left nhdsWithin_le_nhds).sub
        ((hT2.mono_left nhdsWithin_le_nhds).mul hL')
    exact Tendsto.congr' heq.symm hrhs
  -- The candidate holomorphic numerator.
  set H : ℂ → ℂ := Function.update
      (fun z => (z - p) ^ (2 * k) * deltaField r v z) p Lval with hH
  have hHcont : ContinuousAt H p := continuousAt_update_same.mpr hlim
  have hHdiff : DifferentiableOn ℂ H W := by
    rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff hWnhds]
    refine ⟨?_, hHcont⟩
    intro z hz
    have hzW : z ∈ W := hz.1
    have hzp : z ≠ p := hz.2
    have hQz0 : r.denReduced.eval z ≠ 0 := hQne z hzW hzp
    have hδdiff : DifferentiableAt ℂ (deltaField r v) z := by
      have h1 := differentiableOn_deltaField hd ⟨hvcont, L, hL⟩ hgrad hinv
      have h2 : IsOpen {z : ℂ | r.denReduced.eval z ≠ 0} :=
        isOpen_compl_singleton.preimage r.denReduced.continuous
      exact h1.differentiableAt (h2.mem_nhds hQz0)
    have hFdiff : DifferentiableAt ℂ
        (fun x => (x - p) ^ (2 * k) * deltaField r v x) z :=
      ((differentiableAt_id.sub (differentiableAt_const p)).pow _).mul hδdiff
    have hHeq : H =ᶠ[𝓝 z] fun x => (x - p) ^ (2 * k) * deltaField r v x := by
      filter_upwards [isOpen_ne.mem_nhds hzp] with x hx
      rw [hH]
      exact Function.update_of_ne hx _ _
    exact (hFdiff.congr_of_eventuallyEq hHeq).differentiableWithinAt
  refine ⟨W, H, hWopen, hpW, hHdiff, ?_⟩
  intro z hzW hzp
  have hne : (z - p) ^ (2 * k) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzp)
  have hHz : H z = (z - p) ^ (2 * k) * deltaField r v z := by
    rw [hH]
    exact Function.update_of_ne hzp _ _
  rw [hHz, mul_div_cancel_left₀ _ hne]

/-- **Growth bound at infinity.** Multiplied by the squared reduced
denominator, the deformation field grows at most like `|z|^{2d}` near
infinity — the two-chart bookkeeping: `v(z) = O(|z|²)` (sphere field), the
numerator and denominator have degree at most `d`, and the composed term
`v(f z)` is controlled by the infinity-chart reading of `v` when `f z` is
large. This is exactly the numerator-degree bound `natDegree A ≤ 2d` of the
section-space representation. -/
theorem deltaField_growth_at_infty {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (hb : eLpNormEssSup μ volume < ⊤) :
    ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      ‖(r.denReduced.eval z) ^ 2 * deltaField r v z‖
        ≤ C * ‖z‖ ^ (2 * r.degree) := by
  classical
  obtain ⟨hvcont, L, hL⟩ := hv
  -- The reduced denominator is a nonzero polynomial.
  have hQ0 : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  -- (1) Uniform quadratic bound for the sphere vector field.
  obtain ⟨B, hB0, hBv⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, ‖v w‖ ≤ B * (1 + ‖w‖ ^ 2) := by
    have h1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖w ^ 2 * v w⁻¹‖ ≤ ‖L‖ + 1 :=
      hL.norm.eventually_le_const (lt_add_one ‖L‖)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp h1
    have houter : ∀ u : ℂ, δ⁻¹ < ‖u‖ → ‖v u‖ ≤ (‖L‖ + 1) * ‖u‖ ^ 2 := by
      intro u hu
      have hu0 : u ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hu
        exact absurd hu (not_lt.mpr (inv_pos.mpr hδpos).le)
      have hw : u⁻¹ ∈ Metric.ball (0 : ℂ) δ ∩ {0}ᶜ := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_inv]
          exact inv_lt_of_inv_lt₀ hδpos hu
        · exact Set.mem_compl_singleton_iff.mpr (inv_ne_zero hu0)
      have hbd : ‖(u⁻¹) ^ 2 * v (u⁻¹)⁻¹‖ ≤ ‖L‖ + 1 := hδ hw
      rw [inv_inv, norm_mul, norm_pow, norm_inv] at hbd
      have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
      have hun' : ‖u‖ ≠ 0 := ne_of_gt hun
      have h3 : ‖v u‖ = ‖u‖ ^ 2 * ((‖u‖⁻¹) ^ 2 * ‖v u‖) := by
        field_simp
      rw [h3]
      calc ‖u‖ ^ 2 * ((‖u‖⁻¹) ^ 2 * ‖v u‖)
          ≤ ‖u‖ ^ 2 * (‖L‖ + 1) := mul_le_mul_of_nonneg_left hbd (sq_nonneg _)
        _ = (‖L‖ + 1) * ‖u‖ ^ 2 := mul_comm _ _
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) δ⁻¹).exists_bound_of_continuousOn
      hvcont.continuousOn
    have hM0 : 0 ≤ M :=
      le_trans (norm_nonneg (v 0)) (hM 0 (Metric.mem_closedBall_self (inv_pos.mpr hδpos).le))
    refine ⟨max M (‖L‖ + 1), le_trans hM0 (le_max_left _ _), fun w => ?_⟩
    have hmax0 : 0 ≤ max M (‖L‖ + 1) := le_trans hM0 (le_max_left _ _)
    by_cases hw : ‖w‖ ≤ δ⁻¹
    · have h1 := hM w (by rwa [Metric.mem_closedBall, dist_zero_right])
      have h2 : (1 : ℝ) ≤ 1 + ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
      calc ‖v w‖ ≤ M := h1
        _ ≤ max M (‖L‖ + 1) := le_max_left _ _
        _ = max M (‖L‖ + 1) * 1 := (mul_one _).symm
        _ ≤ max M (‖L‖ + 1) * (1 + ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hmax0
    · have hw' : δ⁻¹ < ‖w‖ := not_le.mp hw
      calc ‖v w‖ ≤ (‖L‖ + 1) * ‖w‖ ^ 2 := houter w hw'
        _ ≤ max M (‖L‖ + 1) * (1 + ‖w‖ ^ 2) :=
            mul_le_mul (le_max_right _ _) (by nlinarith [sq_nonneg ‖w‖])
              (sq_nonneg _) hmax0
  -- (2) Polynomial evaluations grow at most like the prescribed power.
  have hpolybound : ∀ (P : ℂ[X]) (n : ℕ), P.natDegree ≤ n →
      ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖P.eval z‖ ≤ Cp * ‖z‖ ^ n := by
    intro P n hn
    refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖,
      Finset.sum_nonneg (fun i _ => norm_nonneg _), fun z hz => ?_⟩
    rw [Polynomial.eval_eq_sum_range]
    calc ‖∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i * z ^ i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖z‖ ^ n := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul, norm_pow]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine pow_le_pow_right₀ hz ?_
          have := Finset.mem_range.mp hi
          omega
      _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * ‖z‖ ^ n := by
          rw [← Finset.sum_mul]
  -- (3) Wronskian degree bound: at most `2d - 2`.
  have hWrHelp : ∀ (A E : ℂ[X]) (d : ℕ), A.natDegree + 1 ≤ d → E.natDegree ≤ d →
      (Polynomial.derivative A * E - A * Polynomial.derivative E).natDegree
        ≤ 2 * d - 2 := by
    intro A E d hA hE
    have h1 : (Polynomial.derivative A * E).natDegree ≤ 2 * d - 2 := by
      by_cases h0 : A.natDegree = 0
      · obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
        rw [← ha, Polynomial.derivative_C, zero_mul, Polynomial.natDegree_zero]
        omega
      · have h2 : (Polynomial.derivative A).natDegree < A.natDegree :=
          Polynomial.natDegree_derivative_lt h0
        have h3 := Polynomial.natDegree_mul_le
          (p := Polynomial.derivative A) (q := E)
        omega
    have h2 : (A * Polynomial.derivative E).natDegree ≤ 2 * d - 2 := by
      by_cases h0 : E.natDegree = 0
      · obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
        rw [← ha, Polynomial.derivative_C, mul_zero, Polynomial.natDegree_zero]
        omega
      · have h2 : (Polynomial.derivative E).natDegree < E.natDegree :=
          Polynomial.natDegree_derivative_lt h0
        have h3 := Polynomial.natDegree_mul_le
          (p := A) (q := Polynomial.derivative E)
        omega
    have h3 := Polynomial.natDegree_sub_le
      (Polynomial.derivative A * E) (A * Polynomial.derivative E)
    omega
  have hNd : r.numReduced.natDegree ≤ r.degree := le_max_left _ _
  have hQd : r.denReduced.natDegree ≤ r.degree := le_max_right _ _
  have hWrdeg : r.wronskian.natDegree ≤ 2 * r.degree - 2 := by
    by_cases hcase : r.numReduced.natDegree < r.degree
    · exact hWrHelp r.numReduced r.denReduced r.degree (by omega) hQd
    · by_cases hcase2 : r.denReduced.natDegree < r.degree
      · have h := hWrHelp r.denReduced r.numReduced r.degree (by omega) hNd
        have hneg : r.wronskian
            = -(Polynomial.derivative r.denReduced * r.numReduced
                - r.denReduced * Polynomial.derivative r.numReduced) := by
          unfold RationalData.wronskian
          ring
        rw [hneg, Polynomial.natDegree_neg]
        exact h
      · -- both of full degree: cancel the leading terms
        have hn : r.numReduced.natDegree = r.degree := by omega
        have hq : r.denReduced.natDegree = r.degree := by omega
        have hN0 : r.numReduced ≠ 0 := by
          intro h0
          rw [h0, Polynomial.natDegree_zero] at hn
          omega
        have hlcQ : r.denReduced.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hQ0
        have hlcN : r.numReduced.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hN0
        set c : ℂ := r.numReduced.leadingCoeff / r.denReduced.leadingCoeff with hc
        have hc0 : c ≠ 0 := div_ne_zero hlcN hlcQ
        have hdegeq : r.numReduced.degree = (Polynomial.C c * r.denReduced).degree := by
          rw [Polynomial.degree_C_mul hc0, Polynomial.degree_eq_natDegree hQ0,
            Polynomial.degree_eq_natDegree hN0, hn, hq]
        have hlceq : r.numReduced.leadingCoeff
            = (Polynomial.C c * r.denReduced).leadingCoeff := by
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
            div_mul_cancel₀ _ hlcQ]
        have hsub := Polynomial.degree_sub_lt hdegeq hN0 hlceq
        have hdegN1 : (r.numReduced - Polynomial.C c * r.denReduced).natDegree + 1
            ≤ r.degree := by
          by_cases h0 : r.numReduced - Polynomial.C c * r.denReduced = 0
          · rw [h0, Polynomial.natDegree_zero]
            omega
          · have := Polynomial.natDegree_lt_natDegree h0 hsub
            omega
        have hWid : r.wronskian
            = Polynomial.derivative (r.numReduced - Polynomial.C c * r.denReduced)
                * r.denReduced
              - (r.numReduced - Polynomial.C c * r.denReduced)
                * Polynomial.derivative r.denReduced := by
          rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul]
          unfold RationalData.wronskian
          ring
        rw [hWid]
        exact hWrHelp _ _ r.degree hdegN1 hQd
  -- (4) Beyond a radius, the reduced denominator does not vanish.
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ z : ℂ, R0 < ‖z‖ → r.denReduced.eval z ≠ 0 := by
    have hfin : {z : ℂ | r.denReduced.IsRoot z}.Finite :=
      Polynomial.finite_setOf_isRoot hQ0
    obtain ⟨R0, hR0⟩ := hfin.isBounded.subset_closedBall 0
    refine ⟨R0, fun z hz h0 => ?_⟩
    have hmem : z ∈ Metric.closedBall (0 : ℂ) R0 := hR0 h0
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact absurd hz (not_lt.mpr hmem)
  -- (5) Assemble the growth bound.
  obtain ⟨C1, hC10, hC1⟩ := hpolybound r.wronskian (2 * r.degree - 2) hWrdeg
  obtain ⟨C2, hC20, hC2⟩ := hpolybound r.numReduced r.degree hNd
  obtain ⟨C3, hC30, hC3⟩ := hpolybound r.denReduced r.degree hQd
  refine ⟨2 * C1 * B + B * (C3 ^ 2 + C2 ^ 2), max R0 1, fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right R0 1) hz)
  have hzR : R0 < ‖z‖ := lt_of_le_of_lt (le_max_left R0 1) hz
  have hQz : r.denReduced.eval z ≠ 0 := hR0 z hzR
  -- Expand `deltaField` at the non-pole `z`.
  have hread : chartFiniteMap (r.toSphereMap ((z : ℂ̂)))
      = r.numReduced.eval z / r.denReduced.eval z := by
    have h1 : r.toSphereMap ↑z
        = if r.denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := rfl
    rw [h1, if_neg hQz]
    rfl
  have hexp : (r.denReduced.eval z) ^ 2 * deltaField r v z
      = r.wronskian.eval z * v z
        - (r.denReduced.eval z) ^ 2
          * v (r.numReduced.eval z / r.denReduced.eval z) := by
    simp only [deltaField, fderivRational]
    rw [hread]
    field_simp
  -- Bound the Wronskian term.
  have ht1 : ‖r.wronskian.eval z * v z‖ ≤ 2 * C1 * B * ‖z‖ ^ (2 * r.degree) := by
    rw [norm_mul]
    have e1 : ‖z‖ ^ (2 * r.degree - 2) * ‖z‖ ^ 2 = ‖z‖ ^ (2 * r.degree) := by
      rw [← pow_add]
      congr 1
      omega
    have e2 : ‖z‖ ^ (2 * r.degree - 2) ≤ ‖z‖ ^ (2 * r.degree) :=
      pow_le_pow_right₀ hz1 (by omega)
    calc ‖r.wronskian.eval z‖ * ‖v z‖
        ≤ (C1 * ‖z‖ ^ (2 * r.degree - 2)) * (B * (1 + ‖z‖ ^ 2)) :=
          mul_le_mul (hC1 z hz1) (hBv z) (norm_nonneg _)
            (by positivity)
      _ = C1 * B * (‖z‖ ^ (2 * r.degree - 2) + ‖z‖ ^ (2 * r.degree)) := by
          rw [← e1]
          ring
      _ ≤ C1 * B * (‖z‖ ^ (2 * r.degree) + ‖z‖ ^ (2 * r.degree)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ = 2 * C1 * B * ‖z‖ ^ (2 * r.degree) := by ring
  -- Bound the composed term.
  have ht2 : ‖(r.denReduced.eval z) ^ 2
        * v (r.numReduced.eval z / r.denReduced.eval z)‖
      ≤ B * (C3 ^ 2 + C2 ^ 2) * ‖z‖ ^ (2 * r.degree) := by
    rw [norm_mul, norm_pow]
    have hv2 := hBv (r.numReduced.eval z / r.denReduced.eval z)
    have hQn : ‖r.denReduced.eval z‖ ≠ 0 := norm_ne_zero_iff.mpr hQz
    calc ‖r.denReduced.eval z‖ ^ 2
          * ‖v (r.numReduced.eval z / r.denReduced.eval z)‖
        ≤ ‖r.denReduced.eval z‖ ^ 2
            * (B * (1 + ‖r.numReduced.eval z / r.denReduced.eval z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hv2 (sq_nonneg _)
      _ = B * (‖r.denReduced.eval z‖ ^ 2 + ‖r.numReduced.eval z‖ ^ 2) := by
          rw [norm_div]
          field_simp
      _ ≤ B * ((C3 * ‖z‖ ^ r.degree) ^ 2 + (C2 * ‖z‖ ^ r.degree) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          have b1 : ‖r.denReduced.eval z‖ ^ 2 ≤ (C3 * ‖z‖ ^ r.degree) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hC3 z hz1) 2
          have b2 : ‖r.numReduced.eval z‖ ^ 2 ≤ (C2 * ‖z‖ ^ r.degree) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hC2 z hz1) 2
          linarith
      _ = B * (C3 ^ 2 + C2 ^ 2) * ‖z‖ ^ (2 * r.degree) := by ring
  calc ‖(r.denReduced.eval z) ^ 2 * deltaField r v z‖
      = ‖r.wronskian.eval z * v z
          - (r.denReduced.eval z) ^ 2
            * v (r.numReduced.eval z / r.denReduced.eval z)‖ := by rw [hexp]
    _ ≤ ‖r.wronskian.eval z * v z‖
        + ‖(r.denReduced.eval z) ^ 2
            * v (r.numReduced.eval z / r.denReduced.eval z)‖ := norm_sub_le _ _
    _ ≤ 2 * C1 * B * ‖z‖ ^ (2 * r.degree)
        + B * (C3 ^ 2 + C2 ^ 2) * ‖z‖ ^ (2 * r.degree) := add_le_add ht1 ht2
    _ = (2 * C1 * B + B * (C3 ^ 2 + C2 ^ 2)) * ‖z‖ ^ (2 * r.degree) := by ring

/-- **Representation from pole and growth data** (pure function theory /
polynomial algebra). A function holomorphic off the roots of the reduced
denominator, with pole order at most twice the root multiplicity at each
root and with `Q²`-weighted growth `O(|z|^{2d})` at infinity, agrees off the
poles with an element of the section space: `Q²·g` extends to an entire
function of polynomial growth `O(|z|^{2d})`, hence is a polynomial of degree
at most `2d` by Liouville/Cauchy estimates. -/
theorem exists_sectionSpace_rep_of_pole_growth {r : RationalData} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {z : ℂ | r.denReduced.eval z ≠ 0})
    (hpole : ∀ p : ℂ, r.denReduced.eval p = 0 →
      ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ p ∈ W ∧
        DifferentiableOn ℂ h W ∧
        ∀ z ∈ W, z ≠ p →
          g z = h z / (z - p) ^ (2 * Polynomial.rootMultiplicity p r.denReduced))
    (hgrow : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      ‖(r.denReduced.eval z) ^ 2 * g z‖ ≤ C * ‖z‖ ^ (2 * r.degree)) :
    ∃ s ∈ SectionSpaceCarrier r,
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 → g z = s z := by
  classical
  obtain ⟨c₀, R, hCR⟩ := hgrow
  -- The reduced denominator is a nonzero polynomial.
  have hQ0 : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  -- The finite set of poles.
  set S : Finset ℂ := r.denReduced.roots.toFinset with hSdef
  have hmemS : ∀ z : ℂ, z ∈ S ↔ r.denReduced.eval z = 0 := fun z =>
    Multiset.mem_toFinset.trans (Polynomial.mem_roots hQ0)
  have hset : {z : ℂ | z ∉ S} = {z : ℂ | r.denReduced.eval z ≠ 0} :=
    Set.ext fun z => not_congr (hmemS z)
  -- ===== Generic removable-singularity extension over a finite set. =====
  have hremove : ∀ (T : Finset ℂ) (f : ℂ → ℂ),
      DifferentiableOn ℂ f {z : ℂ | z ∉ T} →
      (∀ p ∈ T, ∃ G : ℂ → ℂ, ContinuousAt G p ∧ ∀ᶠ z in 𝓝[≠] p, f z = G z) →
      ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ z ∉ T, E z = f z := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro f hf _
        have huniv : {z : ℂ | z ∉ (∅ : Finset ℂ)} = Set.univ := by
          ext z; simp
        rw [huniv] at hf
        exact ⟨f, differentiableOn_univ.mp hf, fun z _ => rfl⟩
    | insert p T hpT ih =>
        intro f hf hb
        -- The complement of the enlarged finite set is open.
        have hopen_ins : IsOpen {z : ℂ | z ∉ insert p T} := by
          have hcl : IsClosed (↑(insert p T) : Set ℂ) :=
            (insert p T).finite_toSet.isClosed
          have hco : {z : ℂ | z ∉ insert p T} = (↑(insert p T) : Set ℂ)ᶜ := by
            ext z; simp
          rw [hco]
          exact hcl.isOpen_compl
        -- The continuous comparison function at `p`.
        obtain ⟨G, hGc, hGev⟩ := hb p (Finset.mem_insert_self p T)
        -- A ball around `p` avoiding `T`.
        have hTcl : IsClosed (↑T : Set ℂ) := T.finite_toSet.isClosed
        have hpT' : p ∈ (↑T : Set ℂ)ᶜ := by simp [hpT]
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hTcl.isOpen_compl p hpT'
        -- A punctured ball around `p` on which `f` is bounded.
        have h1 : ∀ᶠ z in 𝓝 p, ‖G z‖ ≤ ‖G p‖ + 1 :=
          hGc.norm.eventually (eventually_le_nhds (lt_add_one ‖G p‖))
        have hfb : ∀ᶠ z in 𝓝[≠] p, ‖f z‖ ≤ ‖G p‖ + 1 := by
          filter_upwards [hGev, h1.filter_mono nhdsWithin_le_nhds] with z hz1 hz2
          rw [hz1]; exact hz2
        obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp
          (Filter.eventually_iff.mp hfb)
        set ρ : ℝ := min ε δ with hρdef
        have hρ : 0 < ρ := lt_min hε hδ
        -- Differentiability on the punctured ball.
        have hdiffU : DifferentiableOn ℂ f (Metric.ball p ρ \ {p}) := by
          intro z hz
          have hzp : z ≠ p := fun h => hz.2 (Set.mem_singleton_iff.mpr h)
          have hzT : z ∉ T := by
            have hmem := hball (Metric.ball_subset_ball (min_le_left ε δ) hz.1)
            simpa using hmem
          have hz' : z ∈ {w : ℂ | w ∉ insert p T} := by
            simp only [Set.mem_setOf_eq, Finset.mem_insert, not_or]
            exact ⟨hzp, hzT⟩
          exact ((hf z hz').differentiableAt
            (hopen_ins.mem_nhds hz')).differentiableWithinAt
        -- Boundedness on the punctured ball.
        have hbdd : BddAbove ((norm ∘ f) '' (Metric.ball p ρ \ {p})) := by
          refine ⟨‖G p‖ + 1, ?_⟩
          rintro x ⟨w, hw, rfl⟩
          have hw1 : w ∈ Metric.ball p δ :=
            Metric.ball_subset_ball (min_le_right ε δ) hw.1
          have hw2 : w ∈ ({p} : Set ℂ)ᶜ := hw.2
          simp only [Function.comp_apply]
          exact hδsub ⟨hw1, hw2⟩
        -- Remove the singularity at `p`.
        set f' : ℂ → ℂ := Function.update f p (Filter.limUnder (𝓝[≠] p) f)
          with hf'def
        have hf'U : DifferentiableOn ℂ f' (Metric.ball p ρ) :=
          Complex.differentiableOn_update_limUnder_of_bddAbove
            (Metric.ball_mem_nhds p hρ) hdiffU hbdd
        -- The updated function is differentiable off `T`.
        have hf'T : DifferentiableOn ℂ f' {z : ℂ | z ∉ T} := by
          intro z hz
          rcases eq_or_ne z p with rfl | hzp
          · exact (hf'U.differentiableAt
              (Metric.ball_mem_nhds z hρ)).differentiableWithinAt
          · have hz' : z ∈ {w : ℂ | w ∉ insert p T} := by
              simp only [Set.mem_setOf_eq, Finset.mem_insert, not_or]
              exact ⟨hzp, hz⟩
            have hfz : DifferentiableAt ℂ f z :=
              (hf z hz').differentiableAt (hopen_ins.mem_nhds hz')
            have hev : f' =ᶠ[𝓝 z] f := by
              filter_upwards [isOpen_ne.eventually_mem (hzp : z ≠ p)] with w hw
              exact Function.update_of_ne hw _ _
            exact (hev.differentiableAt_iff.mpr hfz).differentiableWithinAt
        -- The comparison data survives the update at the remaining points.
        have hb' : ∀ q ∈ T, ∃ G' : ℂ → ℂ, ContinuousAt G' q ∧
            ∀ᶠ z in 𝓝[≠] q, f' z = G' z := by
          intro q hq
          obtain ⟨G', hG'c, hG'ev⟩ := hb q (Finset.mem_insert_of_mem hq)
          refine ⟨G', hG'c, ?_⟩
          have hqp : q ≠ p := fun h => hpT (h ▸ hq)
          have hne : ∀ᶠ z in 𝓝[≠] q, z ≠ p :=
            (isOpen_ne.eventually_mem hqp).filter_mono nhdsWithin_le_nhds
          filter_upwards [hG'ev, hne] with z hz1 hz2
          exact (Function.update_of_ne hz2 _ _).trans hz1
        -- Conclude by the induction hypothesis.
        obtain ⟨E, hEdiff, hEeq⟩ := ih f' hf'T hb'
        refine ⟨E, hEdiff, ?_⟩
        intro z hz
        rw [Finset.mem_insert, not_or] at hz
        rw [hEeq z hz.2]
        exact Function.update_of_ne hz.1 _ _
  -- ===== `Q²·g` is differentiable off the poles. =====
  have hFdiff : DifferentiableOn ℂ (fun z => (r.denReduced.eval z) ^ 2 * g z)
      {z : ℂ | z ∉ S} := by
    rw [hset]
    exact ((r.denReduced.differentiable.pow 2).differentiableOn).mul hg
  -- ===== `Q²·g` agrees with a continuous function near each pole. =====
  have hFnear : ∀ p ∈ S, ∃ G : ℂ → ℂ, ContinuousAt G p ∧
      ∀ᶠ z in 𝓝[≠] p, (r.denReduced.eval z) ^ 2 * g z = G z := by
    intro p hp
    have hproot : r.denReduced.eval p = 0 := (hmemS p).mp hp
    obtain ⟨W, h, hWopen, hpW, hhdiff, hgeq⟩ := hpole p hproot
    set k : ℕ := Polynomial.rootMultiplicity p r.denReduced with hkdef
    set Q₁ : Polynomial ℂ :=
      r.denReduced /ₘ (Polynomial.X - Polynomial.C p) ^ k with hQ₁def
    have hfact : (Polynomial.X - Polynomial.C p) ^ k * Q₁ = r.denReduced :=
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq r.denReduced p
    have hevalfact : ∀ z : ℂ, r.denReduced.eval z = (z - p) ^ k * Q₁.eval z := by
      intro z
      conv_lhs => rw [← hfact]
      simp
    refine ⟨fun z => (Q₁.eval z) ^ 2 * h z, ?_, ?_⟩
    · exact ((Q₁.continuous.pow 2).continuousAt).mul
        ((hhdiff.differentiableAt (hWopen.mem_nhds hpW)).continuousAt)
    · have hWev : ∀ᶠ z in 𝓝[≠] p, z ∈ W :=
        Filter.eventually_mem_set.mpr (nhdsWithin_le_nhds (hWopen.mem_nhds hpW))
      have hne : ∀ᶠ z in 𝓝[≠] p, z ≠ p :=
        Filter.eventually_mem_set.mpr self_mem_nhdsWithin
      filter_upwards [hWev, hne] with z hzW hzp
      have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
      show (r.denReduced.eval z) ^ 2 * g z = (Q₁.eval z) ^ 2 * h z
      rw [hgeq z hzW hzp, hevalfact z]
      have hpow : ((z - p) ^ k) ^ 2 = (z - p) ^ (2 * k) := by
        rw [← pow_mul, mul_comm]
      calc ((z - p) ^ k * Q₁.eval z) ^ 2 * (h z / (z - p) ^ (2 * k))
          = (Q₁.eval z ^ 2 * h z) * ((z - p) ^ (2 * k) / (z - p) ^ (2 * k)) := by
            rw [mul_pow, hpow]; ring
        _ = Q₁.eval z ^ 2 * h z := by
            rw [div_self (pow_ne_zero _ hzp'), mul_one]
  -- ===== The entire extension of `Q²·g`. =====
  obtain ⟨E, hEdiff, hEeq⟩ :=
    hremove S (fun z => (r.denReduced.eval z) ^ 2 * g z) hFdiff hFnear
  have hEF : ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
      E z = (r.denReduced.eval z) ^ 2 * g z := by
    intro z hz
    have hzS : z ∉ S := fun hmem => hz ((hmemS z).mp hmem)
    exact hEeq z hzS
  -- ===== Growth bound for the entire extension. =====
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w ∈ S, ‖w‖ ≤ M := by
    obtain ⟨M, hM⟩ := (S.image fun w : ℂ => ‖w‖).exists_le
    exact ⟨M, fun w hw => hM _ (Finset.mem_image_of_mem _ hw)⟩
  set R₀ : ℝ := max (max R M) 0 + 1 with hR₀def
  have hR₀pos : 0 < R₀ := lt_of_le_of_lt (le_max_right (max R M) 0) (lt_add_one _)
  have hRR₀ : R < R₀ :=
    lt_of_le_of_lt ((le_max_left R M).trans (le_max_left _ 0)) (lt_add_one _)
  have hMR₀ : M < R₀ :=
    lt_of_le_of_lt ((le_max_right R M).trans (le_max_left _ 0)) (lt_add_one _)
  have hEgrow : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖E z‖ ≤ c₀ * ‖z‖ ^ (2 * r.degree) := by
    intro z hz
    have hzQ : r.denReduced.eval z ≠ 0 := by
      intro h0
      have h1 : ‖z‖ ≤ M := hM z ((hmemS z).mpr h0)
      have h2 : M < ‖z‖ := lt_of_lt_of_le hMR₀ hz
      linarith
    rw [hEF z hzQ]
    exact hCR z (lt_of_lt_of_le hRR₀ hz)
  -- ===== Cauchy estimates: Taylor coefficients above `2d` vanish. =====
  have hvanish : ∀ n : ℕ, 2 * r.degree < n → iteratedDeriv n E 0 = 0 := by
    intro n hn
    have key : ∀ ρ : ℝ, R₀ ≤ ρ →
        ‖iteratedDeriv n E 0‖
          ≤ (n.factorial : ℝ) * (c₀ * ρ ^ (2 * r.degree)) / ρ ^ n := by
      intro ρ hρ
      have hρpos : 0 < ρ := lt_of_lt_of_le hR₀pos hρ
      apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρpos
        hEdiff.diffContOnCl
      intro z hz
      rw [mem_sphere_iff_norm, sub_zero] at hz
      calc ‖E z‖ ≤ c₀ * ‖z‖ ^ (2 * r.degree) := hEgrow z (by rw [hz]; exact hρ)
        _ = c₀ * ρ ^ (2 * r.degree) := by rw [hz]
    have htend : Filter.Tendsto
        (fun ρ : ℝ => (n.factorial : ℝ) * (c₀ * ρ ^ (2 * r.degree)) / ρ ^ n)
        Filter.atTop (𝓝 0) := by
      have h0 : Filter.Tendsto
          (fun ρ : ℝ => ((n.factorial : ℝ) * c₀) * (ρ ^ (2 * r.degree) / ρ ^ n))
          Filter.atTop (𝓝 (((n.factorial : ℝ) * c₀) * 0)) :=
        (tendsto_pow_div_pow_atTop_zero hn).const_mul _
      rw [mul_zero] at h0
      exact h0.congr fun ρ => by ring
    have hle : ‖iteratedDeriv n E 0‖ ≤ 0 :=
      ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨R₀, key⟩)
    exact norm_le_zero_iff.mp hle
  -- ===== The entire extension is a polynomial of degree at most `2d`. =====
  set A : Polynomial ℂ := ∑ n ∈ Finset.range (2 * r.degree + 1),
    Polynomial.C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0) * Polynomial.X ^ n
    with hAdef
  have hEA : ∀ z : ℂ, E z = A.eval z := by
    intro z
    have htay : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0 * z ^ n
        = E z := by
      simpa using Complex.taylorSeries_eq_of_entire' 0 z hEdiff
    have hsum : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0 * z ^ n
        = ∑ n ∈ Finset.range (2 * r.degree + 1),
            (n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0 * z ^ n := by
      refine tsum_eq_sum fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      rw [hvanish n hn]
      ring
    rw [← htay, hsum, hAdef, Polynomial.eval_finset_sum]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  have hAdeg : A.natDegree ≤ 2 * r.degree := by
    rw [hAdef]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)
  -- ===== Package the carrier element `A/Q²`. =====
  refine ⟨fun z => A.eval z / (r.denReduced.eval z) ^ 2, ?_, ?_⟩
  · exact mem_sectionSpaceCarrier_iff.mpr ⟨A, hAdeg, rfl⟩
  · intro z hz
    have hQz : (r.denReduced.eval z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
    show g z = A.eval z / (r.denReduced.eval z) ^ 2
    rw [← hEA z, hEF z hz]
    exact (mul_div_cancel_left₀ _ hQz).symm

/-- **The deformation field of an invariant coefficient lies in the section
space** — the assembly of holomorphy off poles, the pole-order bound, the
growth bound at infinity, and the representation lemma. The carrier
representative agrees with `δv` off the poles and is unique by
`sectionSpaceCarrier_eqOn_nonpoles_eq`. -/
theorem exists_sectionSpace_rep_deltaField {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (hb : eLpNormEssSup μ volume < ⊤) :
    ∃ s ∈ SectionSpaceCarrier r,
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = s z := by
  exact exists_sectionSpace_rep_of_pole_growth
    (differentiableOn_deltaField hd hv hgrad hinv)
    (fun p hp => deltaField_pole_bound hd hv hgrad hinv hb hp)
    (deltaField_growth_at_infty hd hv hgrad hinv hb)

/-! ## Trivial deformations vanish on the Julia set -/

/-- **Iterated functional equation from a trivial deformation.** If
`δv = 0` off the poles — i.e. `v(f z) = f′(z)·v(z)` at every non-pole `z` —
then along any finite orbit segment that stays off `∞`,

`v(fⁿ z) = (fⁿ)′(z)·v(z)`,

with `(fⁿ)′` the derivative of the finite-chart reading of the iterate (the
chain rule telescopes the one-step law along the orbit). -/
theorem deltaField_zero_iterate {r : RationalData} {v : ℂ → ℂ}
    (hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = 0)
    (n : ℕ) (z : ℂ)
    (hfin : ∀ j : ℕ, j ≤ n → r.toSphereMap^[j] ((z : ℂ̂)) ≠ ∞) :
    v (chartFiniteMap (r.toSphereMap^[n] ((z : ℂ̂))))
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) z
          * v z := by
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  -- Combined induction: the reading of the `k`-th iterate has a derivative
  -- `D` at `w`, and the one-step law telescopes to `v(f^[k] w) = D · v w`.
  have key : ∀ (k : ℕ) (w : ℂ),
      (∀ j : ℕ, j ≤ k → r.toSphereMap^[j] ((w : ℂ̂)) ≠ ∞) →
      ∃ D : ℂ,
        HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂)))) D w ∧
        v (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂)))) = D * v w := by
    intro k
    induction k with
    | zero =>
        intro w _
        refine ⟨1, ?_, ?_⟩
        · have h2 : (fun x : ℂ => chartFiniteMap (r.toSphereMap^[0] ((x : ℂ̂))))
              = fun x : ℂ => x := funext fun x => rfl
          rw [h2]
          exact hasDerivAt_id w
        · rw [Function.iterate_zero_apply, cf, one_mul]
    | succ k ih =>
        intro w hw
        -- the derivative and the functional equation at time `k`
        obtain ⟨D, hD, hDval⟩ := ih w fun j hj => hw j (Nat.le_succ_of_le hj)
        -- the finite reading `u` of the `k`-th iterate at `w`
        obtain ⟨u, hu⟩ : ∃ u : ℂ, r.toSphereMap^[k] ((w : ℂ̂)) = ((u : ℂ̂)) := by
          cases hc : r.toSphereMap^[k] ((w : ℂ̂)) with
          | infty => exact absurd hc (hw k (Nat.le_succ k))
          | coe v' => exact ⟨v', rfl⟩
        have hhw : chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))) = u := by
          rw [hu, cf]
        -- `u` is not a pole: the `(k+1)`-st point is finite
        have hfu : r.toSphereMap ((u : ℂ̂)) ≠ ∞ := by
          have h1 : r.toSphereMap^[k + 1] ((w : ℂ̂)) ≠ ∞ := hw (k + 1) le_rfl
          rw [Function.iterate_succ_apply', hu] at h1
          exact h1
        have hden : r.denReduced.eval u ≠ 0 := by
          intro h0
          apply hfu
          have hread : r.toSphereMap ((u : ℂ̂))
              = if r.denReduced.eval u = 0 then (∞ : ℂ̂)
                else ((r.numReduced.eval u / r.denReduced.eval u : ℂ) : ℂ̂) := rfl
          rw [hread, if_pos h0]
        -- the derivative of the reading of `f` at the non-pole `u`
        have hg : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u) u := by
          have hdiv : HasDerivAt (fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x)
              (((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2) u :=
            (r.numReduced.hasDerivAt u).div (r.denReduced.hasDerivAt u) hden
          have hev' : (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              =ᶠ[𝓝 u] fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x := by
            filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with x hx
            have hread : r.toSphereMap ((x : ℂ̂))
                = if r.denReduced.eval x = 0 then (∞ : ℂ̂)
                  else ((r.numReduced.eval x / r.denReduced.eval x : ℂ) : ℂ̂) := rfl
            rw [hread, if_neg hx, cf]
          have hfd : fderivRational r u
              = ((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2 := by
            have hwr : r.wronskian.eval u
                = (Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u := by
              simp only [RationalData.wronskian, Polynomial.eval_sub, Polynomial.eval_mul]
            have hfd0 : fderivRational r u
                = r.wronskian.eval u / (r.denReduced.eval u) ^ 2 := rfl
            rw [hfd0, hwr]
          rw [hfd]
          exact hdiv.congr_of_eventuallyEq hev'
        -- the set where the `k`-th iterate stays finite is open
        have hopen : IsOpen {x : ℂ | r.toSphereMap^[k] ((x : ℂ̂)) ≠ ∞} := by
          have hc : Continuous fun x : ℂ => r.toSphereMap^[k] ((x : ℂ̂)) :=
            (r.toSphereMap_continuous.iterate k).comp OnePoint.continuous_coe
          exact OnePoint.isClosed_infty.isOpen_compl.preimage hc
        -- near `w`, the `(k+1)`-reading is the composite of the two readings
        have hev : ((fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              ∘ fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂))))
            =ᶠ[𝓝 w] fun x : ℂ => chartFiniteMap (r.toSphereMap^[k + 1] ((x : ℂ̂))) := by
          filter_upwards [hopen.mem_nhds (hw k (Nat.le_succ k))] with x hx
          obtain ⟨y, hy⟩ : ∃ y : ℂ, r.toSphereMap^[k] ((x : ℂ̂)) = ((y : ℂ̂)) := by
            cases hc : r.toSphereMap^[k] ((x : ℂ̂)) with
            | infty => exact absurd hc hx
            | coe y => exact ⟨y, rfl⟩
          simp only [Function.comp_apply]
          rw [Function.iterate_succ_apply', hy, cf]
        -- chain rule at the pair of matched points
        have hg2 : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u)
            ((fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂)))) w) := by
          show HasDerivAt _ _ (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))))
          rw [hhw]
          exact hg
        have hcomp := HasDerivAt.comp w hg2 hD
        refine ⟨fderivRational r u * D, hcomp.congr_of_eventuallyEq hev.symm, ?_⟩
        -- the one-step functional equation at `u`, from `δv = 0`
        have hδu : fderivRational r u * v u
            - v (chartFiniteMap (r.toSphereMap ((u : ℂ̂)))) = 0 := hδ u hden
        have h1 : v (chartFiniteMap (r.toSphereMap ((u : ℂ̂)))) = fderivRational r u * v u :=
          (sub_eq_zero.mp hδu).symm
        have h2 : v u = D * v w := by rw [← hhw]; exact hDval
        have hsucc : chartFiniteMap (r.toSphereMap^[k + 1] ((w : ℂ̂)))
            = chartFiniteMap (r.toSphereMap ((u : ℂ̂))) := by
          rw [Function.iterate_succ_apply', hu]
        rw [hsucc, h1, h2, mul_assoc]
  obtain ⟨D, hD, hval⟩ := key n z hfin
  rw [hD.deriv]
  exact hval

/-- **A trivial deformation vanishes on the Julia set** (at its finite
points). At a repelling periodic point `p` of period `n` whose cycle avoids
`∞`, the iterated functional equation gives `v(p) = m·v(p)` with
`m = multiplier (f^[n]) p`, `|m| > 1`, forcing `v(p) = 0`; repelling cycles
through `∞` are handled by discarding the at most one exceptional cycle
(density is preserved under removing finitely many points from a subset
dense in the perfect Julia set). Density of repelling cycles
(`juliaSet_eq_closure_repelling`, needing degree at least two) and
continuity of `v` conclude. -/
theorem sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero
    {r : RationalData} (hd : 2 ≤ r.degree) {v : ℂ → ℂ}
    (hv : IsSphereVectorField v)
    (hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = 0) :
    ∀ z : ℂ, ((z : ℂ̂) ∈ JuliaSet r.toSphereMap) → v z = 0 := by
  classical
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 2 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  -- The repelling set and its exceptional part (cycles through `∞`).
  set R : Set ℂ̂ := {p : ℂ̂ | ∃ n : ℕ, IsRepellingPeriodicPt r.toSphereMap n p}
    with hRdef
  set B : Set ℂ̂ := {p : ℂ̂ | p ∈ R ∧ ∃ j : ℕ, r.toSphereMap^[j] p = ∞}
    with hBdef
  -- ===== Step 0: the exceptional set is finite (at most one cycle). =====
  have hBfin : B.Finite := by
    rcases Set.eq_empty_or_nonempty B with hB | hB
    · rw [hB]; exact Set.finite_empty
    · obtain ⟨p₀, hp₀⟩ := hB
      obtain ⟨hp₀R, j₀, hj₀⟩ := hp₀
      obtain ⟨n₀, hn₀pos, hper₀, -⟩ := hp₀R
      have hper₀' : r.toSphereMap^[n₀] p₀ = p₀ := hper₀
      -- `∞` is a periodic point (of period `n₀`).
      have hinfper : r.toSphereMap^[n₀] (∞ : ℂ̂) = ∞ := by
        calc r.toSphereMap^[n₀] (∞ : ℂ̂)
            = r.toSphereMap^[n₀] (r.toSphereMap^[j₀] p₀) := by rw [hj₀]
          _ = r.toSphereMap^[n₀ + j₀] p₀ := (Function.iterate_add_apply _ _ _ _).symm
          _ = r.toSphereMap^[j₀ + n₀] p₀ := by rw [add_comm]
          _ = r.toSphereMap^[j₀] (r.toSphereMap^[n₀] p₀) :=
              Function.iterate_add_apply _ _ _ _
          _ = r.toSphereMap^[j₀] p₀ := by rw [hper₀']
          _ = ∞ := hj₀
      have hinfper' : Function.IsPeriodicPt r.toSphereMap n₀ (∞ : ℂ̂) := hinfper
      -- Every exceptional point lies on the (finite) orbit of `∞`.
      have hBsub : B ⊆ (fun k : ℕ => r.toSphereMap^[k] (∞ : ℂ̂)) '' (Set.Iio n₀) := by
        rintro p ⟨hpR, j, hj⟩
        obtain ⟨n, hnpos, hper, -⟩ := hpR
        have hper' : r.toSphereMap^[n] p = p := hper
        have hj' : r.toSphereMap^[j % n] p = ∞ := by
          rw [Function.IsPeriodicPt.iterate_mod_apply hper j]
          exact hj
        have hjn : j % n < n := Nat.mod_lt j hnpos
        have hp_orbit : r.toSphereMap^[n - j % n] (∞ : ℂ̂) = p := by
          calc r.toSphereMap^[n - j % n] (∞ : ℂ̂)
              = r.toSphereMap^[n - j % n] (r.toSphereMap^[j % n] p) := by rw [hj']
            _ = r.toSphereMap^[n - j % n + j % n] p :=
                (Function.iterate_add_apply _ _ _ _).symm
            _ = r.toSphereMap^[n] p := by rw [Nat.sub_add_cancel hjn.le]
            _ = p := hper'
        refine ⟨(n - j % n) % n₀, Nat.mod_lt _ hn₀pos, ?_⟩
        show r.toSphereMap^[(n - j % n) % n₀] (∞ : ℂ̂) = p
        rw [hinfper'.iterate_mod_apply]
        exact hp_orbit
      exact Set.Finite.subset ((Set.finite_Iio n₀).image _) hBsub
  -- ===== Step 1: `v` vanishes at finite repelling points off `B`. =====
  have hvanish : ∀ w : ℂ, ((w : ℂ̂)) ∈ R \ B → v w = 0 := by
    intro w hw
    obtain ⟨hwR, hwB⟩ := hw
    obtain ⟨n, hnpos, hper, hmul⟩ := hwR
    -- the full orbit of `w` avoids `∞`
    have hinf : ∀ j : ℕ, r.toSphereMap^[j] ((w : ℂ̂)) ≠ ∞ := by
      intro j hj
      exact hwB ⟨⟨n, hnpos, hper, hmul⟩, j, hj⟩
    -- the iterated functional equation at the period
    have hiter := deltaField_zero_iterate hδ n w (fun j _ => hinf j)
    have hper' : r.toSphereMap^[n] ((w : ℂ̂)) = ((w : ℂ̂)) := hper
    rw [hper', cf] at hiter
    -- the derivative of the return reading is the multiplier, of norm `> 1`
    have hmul' : 1 < ‖deriv (fun x : ℂ =>
        chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) w‖ := hmul
    have hm1 : deriv (fun x : ℂ =>
        chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) w ≠ 1 := by
      intro h1
      rw [h1] at hmul'
      simp at hmul'
    have h0 : (1 - deriv (fun x : ℂ =>
        chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) w) * v w = 0 := by
      linear_combination hiter
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hm1
    · exact h
  -- ===== Step 2: the Julia set lies in the closure of `R \ B`. =====
  have hJR : JuliaSet r.toSphereMap = closure R :=
    juliaSet_eq_closure_repelling hfr hdeg
  have hRB : JuliaSet r.toSphereMap ⊆ closure (R \ B) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro U hUopen hxU
    -- find a Julia point of `U` off `B` (perfectness beats the finite `B`)
    obtain ⟨y, hyU, hyJ, hyB⟩ : ∃ y, y ∈ U ∧ y ∈ JuliaSet r.toSphereMap ∧ y ∉ B := by
      by_cases hxB : x ∈ B
      · have hperf := juliaSet_perfect hfr hdeg
        have hacc := hperf.acc x hx
        rw [accPt_iff_nhds] at hacc
        have hBx_closed : IsClosed (B \ {x}) := (hBfin.subset Set.diff_subset).isClosed
        have hUx_open : IsOpen (U \ (B \ {x})) := hUopen.sdiff hBx_closed
        have hxUx : x ∈ U \ (B \ {x}) := ⟨hxU, fun h => h.2 rfl⟩
        obtain ⟨y, ⟨⟨hyU1, hyU2⟩, hyJ⟩, hyx⟩ := hacc _ (hUx_open.mem_nhds hxUx)
        exact ⟨y, hyU1, hyJ, fun hyB => hyU2 ⟨hyB, hyx⟩⟩
      · exact ⟨x, hxU, hx, hxB⟩
    -- near `y`, repelling points avoid the finite closed set `B`
    have hyR : y ∈ closure R := by rw [← hJR]; exact hyJ
    have hUB_open : IsOpen (U \ B) := hUopen.sdiff hBfin.isClosed
    have hyUB : y ∈ U \ B := ⟨hyU, hyB⟩
    obtain ⟨p, hpUB, hpR⟩ := _root_.mem_closure_iff.mp hyR _ hUB_open hyUB
    exact ⟨p, hpUB.1, hpR, hpUB.2⟩
  -- ===== Step 3: pull the closure back through the finite chart. =====
  intro z hz
  -- points of `R \ B` are finite (their orbits avoid `∞`, already at time `0`)
  have hGrange : R \ B ⊆ Set.range ((↑) : ℂ → ℂ̂) := by
    rintro p ⟨hpR, hpB⟩
    cases p with
    | infty => exact absurd ⟨hpR, 0, rfl⟩ hpB
    | coe w => exact ⟨w, rfl⟩
  have hzcl : (z : ℂ̂) ∈ closure (R \ B) := hRB hz
  have hpre : z ∈ closure {w : ℂ | ((w : ℂ̂)) ∈ R \ B} := by
    have hind : Topology.IsInducing ((↑) : ℂ → ℂ̂) :=
      OnePoint.isOpenEmbedding_coe.isInducing
    have h1 : closure {w : ℂ | ((w : ℂ̂)) ∈ R \ B}
        = ((↑) : ℂ → ℂ̂) ⁻¹' closure (((↑) : ℂ → ℂ̂) '' {w : ℂ | ((w : ℂ̂)) ∈ R \ B}) :=
      hind.closure_eq_preimage_closure_image _
    have h2 : ((↑) : ℂ → ℂ̂) '' {w : ℂ | ((w : ℂ̂)) ∈ R \ B} = R \ B := by
      have h3 : {w : ℂ | ((w : ℂ̂)) ∈ R \ B} = ((↑) : ℂ → ℂ̂) ⁻¹' (R \ B) := rfl
      rw [h3]
      exact Set.image_preimage_eq_of_subset hGrange
    rw [h1, h2]
    exact hzcl
  -- ===== Conclude by continuity of `v`. =====
  have hclosed : IsClosed {w : ℂ | v w = 0} := isClosed_eq hv.1 continuous_const
  have hsub : {w : ℂ | ((w : ℂ̂)) ∈ R \ B} ⊆ {w : ℂ | v w = 0} :=
    fun w hw => hvanish w hw
  exact closure_minimal hsub hclosed hpre

end RiemannDynamics

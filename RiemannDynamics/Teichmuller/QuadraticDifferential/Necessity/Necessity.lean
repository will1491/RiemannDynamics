/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Bergman
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Symmetrize
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Invariant
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Endgame
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Spread
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Deformation
import RiemannDynamics.Analysis.SingularIntegral.L1Duality

/-!
# Hamilton–Krushkal necessity

An extremal marked candidate has a Hamilton maximizer: the real part of the pairing of
its Beltrami coefficient with the unit ball of automorphic quadratic differentials of the
domain group attains the coefficient norm. The contrapositive is the variational step —
a gap between the pairing supremum and the coefficient norm produces, through the
Hahn–Banach extension of the pairing functional, its essentially bounded representative,
and the deformation of the candidate along the resulting infinitesimally trivial
direction, a competing marked candidate of strictly smaller dilatation.

* `exists_lt_dilatation_of_pairing_gap` — the variational step: a pairing gap defeats
  extremality.
* `hamilton_krushkal_necessity` — the attained Hamilton maximizer of an extremal
  candidate.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: one declaration chains the duality functional, the invariant
-- spreading, the trivial deformation, the reflection glue, and the chain-rule dilatation
-- estimate.
/-- **The variational step**: a symmetric marked candidate whose coefficient pairs with
the unit ball of automorphic quadratic differentials of the domain group strictly below
its norm is not extremal — some marked candidate for the pair has strictly smaller
dilatation. -/
theorem exists_lt_dilatation_of_pairing_gap (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {F : ℂ → ℂ} {b : BeltramiCoeff}
    (hmc : IsMarkedCandidate x y F) (hqa : IsQCAnalytic F b)
    (hsym : b.μ = symmExtension b.μ)
    (hFsym : ∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : QuadraticDifferential y.group, q.l1Norm ≤ 1 →
      (qdPairing b.μ q).re ≤ b.normInf - δ) :
    ∃ (G : ℂ → ℂ) (K : ℝ), IsQCGeometric G K ∧ IsMarkedCandidate x y G ∧ K < b.K := by
  classical
  have _ := hFsym
  -- ===== Stage 0: constants and basic facts =====
  set k : ℝ := b.normInf with hkdef
  have hk0 : 0 ≤ k := b.normInf_nonneg
  have hk1 : k < 1 := b.normInf_lt_one
  -- the gap at the zero differential forces `δ ≤ k`
  have hδk : δ ≤ k := by
    have h0 := hgap 0 (by
      have : (0 : QuadraticDifferential y.group).l1Norm = 0 := by
        unfold QuadraticDifferential.l1Norm
        simp
      rw [this]
      exact zero_le_one)
    have hz : qdPairing b.μ (0 : QuadraticDifferential y.group) = 0 := by
      unfold qdPairing
      simp
    rw [hz] at h0
    simp only [Complex.zero_re] at h0
    linarith
  have hkpos : 0 < k := lt_of_lt_of_le hδ hδk
  -- transport the Fuchsian triple to the range group
  have hΓy := TeichRep.isFuchsian_group hΓ₀ hfree y
  have hfy := y.group_free hfree
  have hccy := y.group_cocompact hcc
  -- the coefficient is a.e. bounded by its norm
  have hne : eLpNormEssSup b.μ volume ≠ ⊤ := b.bound.ne_top
  have hbd : ∀ᵐ z, ‖b.μ z‖ ≤ k := by
    filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with z hz
    have h := ENNReal.toReal_mono hne hz
    rwa [toReal_enorm] at h
  -- the pointwise-truncated representative of the coefficient
  set μ' : ℂ → ℂ := fun z => if ‖b.μ z‖ ≤ k then b.μ z else 0 with hμ'def
  have hμ'meas : Measurable μ' :=
    Measurable.ite (measurableSet_le b.measurable.norm measurable_const)
      b.measurable measurable_const
  have hμ'bd : ∀ z, ‖μ' z‖ ≤ k := by
    intro z
    by_cases h : ‖b.μ z‖ ≤ k
    · rw [hμ'def]
      simpa [if_pos h] using h
    · rw [hμ'def]
      simpa [if_neg h] using hk0
  have hμ'ae : ∀ᵐ z, μ' z = b.μ z := by
    filter_upwards [hbd] with z hz
    rw [hμ'def]
    simp [if_pos hz]
  -- ===== Stage 1: the Dirichlet domain and its finite measure =====
  set D : Set ℂ := UpperHalfPlane.coe '' dirichletDomain y.group UpperHalfPlane.I with hDdef
  obtain ⟨ε₁, hε₁, htr⟩ := exists_trace_gap hΓy hfy hccy
  obtain ⟨R₁, hR₁, hdense⟩ := exists_orbit_density_bound hΓy hε₁ htr hccy UpperHalfPlane.I
  have hDc : IsCompact D :=
    (isCompact_dirichletDomain hdense).image UpperHalfPlane.continuous_coe
  have hDmeas : MeasurableSet D := hDc.measurableSet
  have hDsub : D ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  haveI hDfin : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDc.measure_lt_top⟩
  -- ===== Stage 2: the Hölder bound with the gap constant =====
  have hpairμ' : ∀ q : QuadraticDifferential y.group, qdPairing μ' q = qdPairing b.μ q := by
    intro q
    unfold qdPairing
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hμ'ae] with z hz
    rw [hz]
  have hnorm_pair : ∀ q : QuadraticDifferential y.group, q.l1Norm ≠ ⊤ →
      ‖qdPairing b.μ q‖ ≤ (k - δ) * q.l1Norm.toReal := by
    intro q hqfin
    by_cases hq0 : q.l1Norm = 0
    · have hbd' : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖b.μ z‖ ≤ k :=
        ae_restrict_of_ae hbd
      have h := norm_qdPairing_le hk0 hbd' q hqfin
      rw [hq0] at h ⊢
      simpa using h
    · have hr0 : 0 < q.l1Norm.toReal := ENNReal.toReal_pos hq0 hqfin
      by_cases hp0 : qdPairing b.μ q = 0
      · rw [hp0, norm_zero]
        have hkδ : (0 : ℝ) ≤ k - δ := by linarith
        exact mul_nonneg hkδ ENNReal.toReal_nonneg
      · set p : ℂ := qdPairing b.μ q with hpdef
        set r : ℝ := q.l1Norm.toReal with hrdef
        set c : ℂ := (‖p‖ : ℂ) / p * ((r⁻¹ : ℝ) : ℂ) with hcdef
        have hnormc : ‖c‖ = r⁻¹ := by
          rw [hcdef, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (norm_nonneg p),
            Real.norm_of_nonneg (inv_nonneg.mpr hr0.le),
            div_self (norm_ne_zero_iff.mpr hp0), one_mul]
        have hcq : (c • q).l1Norm ≤ 1 := by
          rw [l1Norm_smul]
          have h1 : ‖c‖ₑ = ENNReal.ofReal r⁻¹ := by
            rw [← ofReal_norm_eq_enorm, hnormc]
          have h2 : q.l1Norm = ENNReal.ofReal r := by
            rw [hrdef, ENNReal.ofReal_toReal hqfin]
          rw [h1, h2, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le),
            inv_mul_cancel₀ hr0.ne']
          simp
        have hgapc := hgap (c • q) hcq
        rw [qdPairing_smul, ← hpdef] at hgapc
        have hcp : c * p = ((r⁻¹ * ‖p‖ : ℝ) : ℂ) := by
          rw [hcdef]
          have e : (‖p‖ : ℂ) / p * ((r⁻¹ : ℝ) : ℂ) * p
              = ((r⁻¹ : ℝ) : ℂ) * ((‖p‖ : ℂ) / p * p) := by ring
          rw [e, div_mul_cancel₀ _ hp0]
          push_cast
          ring
        rw [hcp, Complex.ofReal_re] at hgapc
        have h3 := mul_le_mul_of_nonneg_left hgapc hr0.le
        rw [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul] at h3
        linarith [h3]
  -- ===== Stage 3: duality — the annihilating density on the Dirichlet domain =====
  have hdual : ∃ ν₀ : ℂ → ℂ, Measurable ν₀ ∧ (∀ z, ‖ν₀ z‖ ≤ k - δ) ∧
      ∀ q : QuadraticDifferential y.group, q.l1Norm ≠ ⊤ →
        (∫ z in D, ν₀ z * q z) = qdPairing b.μ q := by
    -- the ambient bounded pairing functional on L¹ of the Dirichlet domain
    have hint : ∀ f : Lp ℂ 1 (volume.restrict D),
        Integrable (fun z => μ' z * f z) (volume.restrict D) := fun f =>
      Integrable.bdd_mul (L1.integrable_coeFn f) hμ'meas.aestronglyMeasurable
        (Filter.Eventually.of_forall hμ'bd)
    have hnorm_f : ∀ f : Lp ℂ 1 (volume.restrict D),
        ∫ z, ‖f z‖ ∂(volume.restrict D) = ‖f‖ := by
      intro f
      rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def,
        eLpNorm_one_eq_lintegral_enorm]
    have hΛbound : ∀ f : Lp ℂ 1 (volume.restrict D),
        ‖∫ z, μ' z * f z ∂(volume.restrict D)‖ ≤ k * ‖f‖ := by
      intro f
      have h1 : ‖∫ z, μ' z * f z ∂(volume.restrict D)‖
          ≤ ∫ z, ‖μ' z * f z‖ ∂(volume.restrict D) := norm_integral_le_integral_norm _
      have h2 : ∫ z, ‖μ' z * f z‖ ∂(volume.restrict D)
          ≤ ∫ z, k * ‖f z‖ ∂(volume.restrict D) := by
        refine integral_mono (hint f).norm ((L1.integrable_coeFn f).norm.const_mul k)
          fun z => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hμ'bd z) (norm_nonneg _)
      have h3 : ∫ z, k * ‖f z‖ ∂(volume.restrict D)
          = k * ∫ z, ‖f z‖ ∂(volume.restrict D) := integral_const_mul k _
      rw [h3, hnorm_f f] at h2
      linarith
    set Λ : Lp ℂ 1 (volume.restrict D) →L[ℂ] ℂ := LinearMap.mkContinuous
      { toFun := fun f => ∫ z, μ' z * f z ∂(volume.restrict D)
        map_add' := by
          intro f g
          have hcoe : ∀ᵐ z ∂(volume.restrict D),
              μ' z * ((f + g : Lp ℂ 1 (volume.restrict D)) : ℂ → ℂ) z
                = μ' z * f z + μ' z * g z := by
            filter_upwards [Lp.coeFn_add f g] with z hz
            rw [hz]
            simp [mul_add]
          rw [integral_congr_ae hcoe, integral_add (hint f) (hint g)]
        map_smul' := by
          intro a f
          have hcoe : ∀ᵐ z ∂(volume.restrict D),
              μ' z * ((a • f : Lp ℂ 1 (volume.restrict D)) : ℂ → ℂ) z
                = a • (μ' z * f z) := by
            filter_upwards [Lp.coeFn_smul a f] with z hz
            rw [hz]
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
          rw [integral_congr_ae hcoe, integral_smul]
          simp }
      k (fun f => hΛbound f) with hΛdef
    have hΛapp : ∀ f : Lp ℂ 1 (volume.restrict D),
        Λ f = ∫ z, μ' z * f z ∂(volume.restrict D) := fun f => rfl
    -- the subspace of classes of integrable quadratic differentials (algebraic only)
    set A : Submodule ℂ (Lp ℂ 1 (volume.restrict D)) :=
      { carrier := {f | ∃ q : QuadraticDifferential y.group,
          q.l1Norm ≠ ⊤ ∧ (f : ℂ → ℂ) =ᵐ[volume.restrict D] q}
        add_mem' := by
          rintro f g ⟨q, hq, hfq⟩ ⟨q', hq', hgq'⟩
          refine ⟨q + q', ?_, ?_⟩
          · have hle : (q + q').l1Norm ≤ q.l1Norm + q'.l1Norm := by
              unfold QuadraticDifferential.l1Norm
              rw [← lintegral_add_left (q.measurable.enorm)]
              refine lintegral_mono fun z => ?_
              rw [QuadraticDifferential.add_apply]
              exact enorm_add_le _ _
            exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hq, hq'⟩) hle
          · filter_upwards [Lp.coeFn_add f g, hfq, hgq'] with z h1 h2 h3
            rw [h1]
            simp only [Pi.add_apply, QuadraticDifferential.add_apply]
            rw [h2, h3]
        zero_mem' := by
          refine ⟨0, ?_, ?_⟩
          · unfold QuadraticDifferential.l1Norm
            simp
          · filter_upwards [Lp.coeFn_zero ℂ 1 (volume.restrict D)] with z hz
            rw [hz]
            simp
        smul_mem' := by
          rintro a f ⟨q, hq, hfq⟩
          refine ⟨a • q, ?_, ?_⟩
          · rw [l1Norm_smul]
            exact ENNReal.mul_ne_top enorm_ne_top hq
          · filter_upwards [Lp.coeFn_smul a f, hfq] with z h1 h2
            rw [h1]
            simp only [Pi.smul_apply, QuadraticDifferential.smul_apply, smul_eq_mul]
            rw [h2] } with hAdef
    have hval : ∀ (f : Lp ℂ 1 (volume.restrict D)) (q : QuadraticDifferential y.group),
        (f : ℂ → ℂ) =ᵐ[volume.restrict D] q → Λ f = qdPairing μ' q := by
      intro f q hfq
      rw [hΛapp]
      have hcongr : ∫ z, μ' z * f z ∂(volume.restrict D)
          = ∫ z, μ' z * q z ∂(volume.restrict D) := by
        refine integral_congr_ae ?_
        filter_upwards [hfq] with z hz
        rw [hz]
      rw [hcongr]
      unfold qdPairing
      rw [← hDdef]
    have hmass : ∀ (f : Lp ℂ 1 (volume.restrict D)) (q : QuadraticDifferential y.group),
        (f : ℂ → ℂ) =ᵐ[volume.restrict D] q → ‖f‖ = q.l1Norm.toReal := by
      intro f q hfq
      rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
      have hcongr : ∫⁻ z, ‖f z‖ₑ ∂(volume.restrict D)
          = ∫⁻ z, ‖q z‖ₑ ∂(volume.restrict D) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfq] with z hz
        rw [hz]
      rw [hcongr]
      congr 1
    -- the ambient bound on members of the subspace
    have hΛA : ∀ f : Lp ℂ 1 (volume.restrict D), f ∈ A → ‖Λ f‖ ≤ (k - δ) * ‖f‖ := by
      rintro f ⟨q, hqfin, hfq⟩
      rw [hval f q hfq, hmass f q hfq, hpairμ' q]
      exact hnorm_pair q hqfin
    -- the bridge between the real and complex scalar actions on L¹
    have hRC : ∀ (r : ℝ) (v : Lp ℂ 1 (volume.restrict D)), r • v = ((r : ℂ)) • v := by
      intro r v
      refine Lp.ext_iff.mpr ?_
      filter_upwards [Lp.coeFn_smul r v, Lp.coeFn_smul ((r : ℂ)) v] with z hz1 hz2
      rw [hz1, hz2]
      change r • (v z) = (r : ℂ) • (v z)
      simp [Complex.real_smul]
    -- the subspace as a real submodule and the real-part functional on it
    set Aℝ : Submodule ℝ (Lp ℂ 1 (volume.restrict D)) :=
      { carrier := {f | f ∈ A}
        add_mem' := fun hf hg => A.add_mem hf hg
        zero_mem' := A.zero_mem
        smul_mem' := by
          intro r f hf
          change r • f ∈ A
          rw [hRC]
          exact A.smul_mem _ hf } with hAℝdef
    set φ : (Lp ℂ 1 (volume.restrict D)) →ₗ.[ℝ] ℝ :=
      ⟨Aℝ, { toFun := fun x => (Λ (x : Lp ℂ 1 (volume.restrict D))).re
             map_add' := by
               intro a b
               simp only [Submodule.coe_add, map_add, Complex.add_re]
             map_smul' := by
               intro r a
               change (Λ ((r • a : Aℝ) : Lp ℂ 1 (volume.restrict D))).re = _
               have h1 : ((r • a : Aℝ) : Lp ℂ 1 (volume.restrict D))
                   = r • (a : Lp ℂ 1 (volume.restrict D)) := rfl
               rw [h1, hRC, map_smul]
               simp [smul_eq_mul, Complex.mul_re] }⟩ with hφdef
    have hφapp : ∀ x : φ.domain, φ x = (Λ (x : Lp ℂ 1 (volume.restrict D))).re :=
      fun x => rfl
    have hkδ0 : (0 : ℝ) ≤ k - δ := by linarith
    have hφle : ∀ x : φ.domain, φ x ≤ (k - δ) * ‖(x : Lp ℂ 1 (volume.restrict D))‖ := by
      intro x
      have hmem : (x : Lp ℂ 1 (volume.restrict D)) ∈ A := x.2
      calc φ x = (Λ (x : Lp ℂ 1 (volume.restrict D))).re := hφapp x
        _ ≤ ‖Λ (x : Lp ℂ 1 (volume.restrict D))‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ ≤ (k - δ) * ‖(x : Lp ℂ 1 (volume.restrict D))‖ := hΛA _ hmem
    obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear φ
      (fun x => (k - δ) * ‖x‖)
      (fun c hc x => by
        change (k - δ) * ‖c • x‖ = c * ((k - δ) * ‖x‖)
        rw [hRC, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le]
        ring)
      (fun x y => by
        change (k - δ) * ‖x + y‖ ≤ (k - δ) * ‖x‖ + (k - δ) * ‖y‖
        have h9 := norm_add_le x y
        nlinarith only [h9, hkδ0])
      hφle
    -- the complexification of the extension
    set fc : Lp ℂ 1 (volume.restrict D) → ℂ := fun x =>
      ((g x : ℝ) : ℂ) - Complex.I * ((g (Complex.I • x) : ℝ) : ℂ) with hfcdef
    have hfc_app : ∀ v, fc v = ((g v : ℝ) : ℂ)
        - Complex.I * ((g (Complex.I • v) : ℝ) : ℂ) := fun v => rfl
    have hfc_add : ∀ x y, fc (x + y) = fc x + fc y := by
      intro x y
      rw [hfc_app (x + y), hfc_app x, hfc_app y]
      simp only [smul_add, map_add]
      push_cast
      ring
    have hfc_key1 : ∀ x, fc (Complex.I • x) = Complex.I * fc x := by
      intro x
      rw [hfc_app (Complex.I • x), hfc_app x]
      have h1 : Complex.I • Complex.I • x = -x := by
        rw [smul_smul, Complex.I_mul_I, neg_one_smul]
      rw [h1, map_neg]
      push_cast
      linear_combination ((g (Complex.I • x) : ℝ) : ℂ) * Complex.I_mul_I
    have hfc_key2 : ∀ (r : ℝ) x, fc (((r : ℂ)) • x) = (r : ℂ) * fc x := by
      intro r x
      rw [hfc_app (((r : ℂ)) • x), hfc_app x]
      have h1 : ((r : ℂ)) • x = r • x := (hRC r x).symm
      have h2 : Complex.I • r • x = r • (Complex.I • x) := by
        rw [hRC r x, smul_smul, mul_comm Complex.I ((r : ℂ)), ← smul_smul,
          hRC r (Complex.I • x)]
      rw [h1, h2, map_smul, map_smul]
      simp only [smul_eq_mul]
      push_cast
      ring
    have hfc_smul : ∀ (c : ℂ) x, fc (c • x) = c * fc x := by
      intro c x
      have hdec : c • x = ((c.re : ℂ)) • x + ((c.im : ℂ)) • (Complex.I • x) := by
        rw [smul_smul]
        rw [← add_smul]
        congr 1
        exact (Complex.re_add_im c).symm
      rw [hdec, hfc_add, hfc_key2, hfc_key2, hfc_key1]
      have h := Complex.re_add_im c
      linear_combination (fc x) * h
    have hfc_re : ∀ x, (fc x).re = g x := by
      intro x
      rw [hfc_app x]
      simp [Complex.mul_re]
    have hfc_bound : ∀ x, ‖fc x‖ ≤ (k - δ) * ‖x‖ := by
      intro x
      by_cases h0 : fc x = 0
      · rw [h0, norm_zero]
        exact mul_nonneg hkδ0 (norm_nonneg _)
      · have hpos : 0 < ‖fc x‖ := norm_pos_iff.mpr h0
        have e1 : ‖fc x‖ ^ 2 = (starRingEnd ℂ (fc x) * fc x).re := by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]
        have e2 : starRingEnd ℂ (fc x) * fc x = fc (starRingEnd ℂ (fc x) • x) :=
          (hfc_smul _ x).symm
        have e3 : (fc (starRingEnd ℂ (fc x) • x)).re = g (starRingEnd ℂ (fc x) • x) :=
          hfc_re _
        have e4 : g (starRingEnd ℂ (fc x) • x) ≤ (k - δ) * ‖starRingEnd ℂ (fc x) • x‖ :=
          hg_le _
        have e5 : ‖starRingEnd ℂ (fc x) • x‖ = ‖fc x‖ * ‖x‖ := by
          rw [norm_smul, RCLike.norm_conj]
        have e6 : ‖fc x‖ ^ 2 ≤ (k - δ) * (‖fc x‖ * ‖x‖) := by
          rw [e1, e2, e3]
          rw [e5] at e4
          exact e4
        nlinarith only [e6, hpos]
    set Λe : Lp ℂ 1 (volume.restrict D) →L[ℂ] ℂ :=
      LinearMap.mkContinuous
        { toFun := fc
          map_add' := hfc_add
          map_smul' := fun c x => by rw [hfc_smul]; rfl }
        (k - δ) hfc_bound with hΛedef
    have hΛe_app : ∀ x, Λe x = fc x := fun x => rfl
    have hΛe_norm : ‖Λe‖ ≤ k - δ :=
      LinearMap.mkContinuous_norm_le _ hkδ0 hfc_bound
    -- the extension agrees with the pairing functional on the subspace
    have hgA : ∀ f : Lp ℂ 1 (volume.restrict D), f ∈ A → g f = (Λ f).re := by
      intro f hf
      have h := hg_ext ⟨f, hf⟩
      rw [h]
      exact hφapp ⟨f, hf⟩
    have hΛeA : ∀ f : Lp ℂ 1 (volume.restrict D), f ∈ A → Λe f = Λ f := by
      intro f hf
      have hIf : Complex.I • f ∈ A := A.smul_mem Complex.I hf
      rw [hΛe_app, hfc_app f]
      rw [hgA f hf, hgA _ hIf]
      have h2 : Λ (Complex.I • f) = Complex.I * Λ f := by
        rw [map_smul, smul_eq_mul]
      rw [h2]
      have h3 : (Complex.I * Λ f).re = -(Λ f).im := by
        simp [Complex.mul_re]
      rw [h3]
      simp [Complex.ext_iff]
    -- the essentially bounded representative
    obtain ⟨ν₀, hν₀meas, hν₀bd, hν₀rep⟩ :=
      exists_linfty_representative (volume.restrict D) Λe
    refine ⟨ν₀, hν₀meas, fun z => (hν₀bd z).trans hΛe_norm, ?_⟩
    intro q hqfin
    have hqmem : MemLp (q : ℂ → ℂ) 1 (volume.restrict D) := by
      refine ⟨q.measurable.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact lt_top_iff_ne_top.mpr hqfin
    have hfqmem : hqmem.toLp q ∈ A := ⟨q, hqfin, hqmem.coeFn_toLp⟩
    have h1 : Λe (hqmem.toLp q) = Λ (hqmem.toLp q) := hΛeA _ hfqmem
    have h2 : Λ (hqmem.toLp q) = qdPairing μ' q := hval _ q hqmem.coeFn_toLp
    have h3 : Λe (hqmem.toLp q) = ∫ z, ν₀ z * (hqmem.toLp q) z ∂(volume.restrict D) :=
      hν₀rep (hqmem.toLp q)
    have h4 : ∫ z, ν₀ z * (hqmem.toLp q) z ∂(volume.restrict D)
        = ∫ z in D, ν₀ z * q z := by
      refine integral_congr_ae ?_
      filter_upwards [hqmem.coeFn_toLp] with z hz
      rw [hz]
    rw [← h4, ← h3, h1, h2]
    exact hpairμ' q
  obtain ⟨ν₀, hν₀meas, hν₀bd, hν₀pair⟩ := hdual
  -- ===== Stage 4: invariant spreading of the density =====
  obtain ⟨ν, hνmeas, hνbd, hνsupp, hνinv, hνD⟩ :=
    exists_invariant_extension_of_dirichlet hΓy hfy hccy hν₀meas hν₀bd
  have hνpair : ∀ q : QuadraticDifferential y.group, q.l1Norm ≠ ⊤ →
      qdPairing ν q = qdPairing b.μ q := by
    intro q hq
    rw [← hν₀pair q hq]
    unfold qdPairing
    rw [← hDdef]
    refine integral_congr_ae ?_
    have hνD' : ∀ᵐ z ∂(volume.restrict D), ν z = ν₀ z := by
      rw [hDdef]
      exact hνD
    filter_upwards [hνD'] with z hz
    rw [hz]
  -- ===== Stage 5: the annihilating direction and the trivial deformation =====
  set η : ℂ → ℂ := fun z => if 0 < z.im then μ' z - ν z else 0 with hηdef
  have hηmeas : Measurable η :=
    Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im)
      (hμ'meas.sub hνmeas) measurable_const
  have hηbd : ∀ z, ‖η z‖ ≤ 2 * k - δ := by
    intro z
    rw [hηdef]
    by_cases h : 0 < z.im
    · simp only [if_pos h]
      calc ‖μ' z - ν z‖ ≤ ‖μ' z‖ + ‖ν z‖ := norm_sub_le _ _
        _ ≤ k + (k - δ) := add_le_add (hμ'bd z) (hνbd z)
        _ = 2 * k - δ := by ring
    · simp only [if_neg h, norm_zero]
      linarith
  have hηsupp : ∀ z : ℂ, z.im ≤ 0 → η z = 0 := by
    intro z hz
    rw [hηdef]
    simp only [if_neg (not_lt.mpr hz)]
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hηinv : ∀ W ∈ y.group, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      η (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = η z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2 := by
    intro W hW
    -- transport the truncation identity through the Möbius map
    have hN : volume {w : ℂ | ¬ μ' w = b.μ w} = 0 := ae_iff.mp hμ'ae
    have htrans : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
        μ' (moebiusMap W z) = b.μ (moebiusMap W z) := by
      set T : Set ℂ :=
        toMeasurable volume {w : ℂ | ¬ μ' w = b.μ w} ∩ {z : ℂ | 0 < z.im} with hTdef
      have hTmeas : MeasurableSet T := (measurableSet_toMeasurable _ _).inter hU
      have hTnull : volume T = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le _)
        rw [measure_toMeasurable]
        exact le_of_eq hN
      have hTsub : T ⊆ {z : ℂ | 0 < z.im} := Set.inter_subset_right
      have himg := volume_moebiusMap_image_eq_zero W⁻¹ hTsub hTmeas hTnull
      rw [ae_restrict_iff' hU, ae_iff]
      refine measure_mono_null ?_ himg
      intro z hz
      simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
      obtain ⟨hzup, hzbad⟩ := hz
      have hden : moebiusDenom W z ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero W hzup.ne'
      refine ⟨moebiusMap W z,
        ⟨subset_toMeasurable _ _ hzbad, moebiusMap_im_pos W hzup⟩, ?_⟩
      rw [moebiusMap_mul W⁻¹ W z hden, inv_mul_cancel, moebiusMap_one]
    have h1 := beltrami_invariant_of_isMarkedCandidate hmc hqa W hW
    have h2 := hνinv W hW
    have h4 : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), μ' z = b.μ z :=
      ae_restrict_of_ae hμ'ae
    rw [ae_restrict_iff' hU] at h1 h2 h4 htrans ⊢
    filter_upwards [h1, h2, h4, htrans] with z hz1 hz2 hz4 hz3 hzmem
    have hzup : 0 < z.im := hzmem
    have hWzup : 0 < (moebiusMap W z).im := moebiusMap_im_pos W hzup
    have hη1 : η (moebiusMap W z) = μ' (moebiusMap W z) - ν (moebiusMap W z) := by
      simp only [hηdef]
      rw [if_pos hWzup]
    have hη2 : η z = μ' z - ν z := by
      simp only [hηdef]
      rw [if_pos hzup]
    rw [hη1, hη2, hz3 hzmem, hz4 hzmem]
    linear_combination hz1 hzmem - hz2 hzmem
  have hηperp : ∀ q : QuadraticDifferential y.group, q.l1Norm ≠ ⊤ → qdPairing η q = 0 := by
    intro q hqfin
    have hqInt : Integrable (q : ℂ → ℂ) (volume.restrict D) := by
      refine ⟨q.measurable.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      exact lt_top_iff_ne_top.mpr hqfin
    have hIμ : Integrable (fun z => μ' z * q z) (volume.restrict D) :=
      Integrable.bdd_mul hqInt hμ'meas.aestronglyMeasurable
        (Filter.Eventually.of_forall hμ'bd)
    have hIν : Integrable (fun z => ν z * q z) (volume.restrict D) :=
      Integrable.bdd_mul hqInt hνmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall hνbd)
    have h1 : qdPairing η q = ∫ z in D, (μ' z * q z - ν z * q z) := by
      unfold qdPairing
      rw [← hDdef]
      refine setIntegral_congr_fun hDmeas fun z hz => ?_
      have hzup : 0 < z.im := hDsub hz
      simp only [hηdef]
      rw [if_pos hzup]
      ring
    rw [h1, integral_sub hIμ hIν]
    have h2 : ∫ z in D, μ' z * q z = qdPairing μ' q := by
      unfold qdPairing
      rw [← hDdef]
    have h3 : ∫ z in D, ν z * q z = qdPairing ν q := by
      unfold qdPairing
      rw [← hDdef]
    rw [h2, h3, hpairμ' q, hνpair q hqfin, sub_self]
  have hε4 : (0 : ℝ) < δ / 4 := by linarith
  obtain ⟨t₀, ht₀pos, hFVL⟩ :=
    exists_trivial_deformation hΓy hfy hccy hηmeas hηbd hηsupp hηinv hηperp hε4
  -- ===== Stage 6: the time parameter and its smallness certificates =====
  have h1k2 : 0 < 1 - k ^ 2 := by nlinarith only [hk0, hk1]
  set c₃ : ℝ := δ ^ 2 * (1 - k ^ 2) / 16 with hc₃def
  have hc₃pos : 0 < c₃ := by
    rw [hc₃def]
    positivity
  set t : ℝ := min (t₀ / 2) (min 1 (min (1 / (4 * k))
    (min (δ / 2 / (2 * k ^ 3 + c₃)) (δ ^ 2 * (1 - k ^ 2) / 8 / (4 * k ^ 2))))) with htdef
  have htpos : 0 < t := by
    rw [htdef]
    refine lt_min (by linarith) (lt_min one_pos (lt_min (by positivity) (lt_min ?_ ?_)))
    · have : 0 < 2 * k ^ 3 + c₃ := by positivity
      positivity
    · positivity
  have htt₀ : t < t₀ := by
    have h : t ≤ t₀ / 2 := by
      rw [htdef]
      exact min_le_left _ _
    linarith
  have ht1 : t ≤ 1 := by
    rw [htdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have ht2 : t ≤ 1 / (4 * k) := by
    rw [htdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : t * (2 * k ^ 3 + c₃) ≤ δ / 2 := by
    have h : t ≤ δ / 2 / (2 * k ^ 3 + c₃) := by
      rw [htdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have hpos : 0 < 2 * k ^ 3 + c₃ := by positivity
    rw [le_div_iff₀ hpos] at h
    linarith
  have ht4 : 4 * k ^ 2 * t ≤ δ ^ 2 * (1 - k ^ 2) / 8 := by
    have h : t ≤ δ ^ 2 * (1 - k ^ 2) / 8 / (4 * k ^ 2) := by
      rw [htdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have hpos : (0 : ℝ) < 4 * k ^ 2 := by positivity
    rw [le_div_iff₀ hpos] at h
    linarith
  set k' : ℝ := k - c₃ * t with hk'def
  have hc₃small : c₃ * t ≤ δ / 2 := by
    have h8 : (0 : ℝ) ≤ 2 * k ^ 3 * t := by positivity
    linarith only [ht3, h8]
  have hk'0 : 0 ≤ k' := by
    rw [hk'def]
    linarith
  have hk'k : k' < k := by
    rw [hk'def]
    linarith only [mul_pos hc₃pos htpos]
  have hk'1 : k' < 1 := by
    have h8 : k' ≤ k := by
      rw [hk'def]
      linarith only [mul_pos hc₃pos htpos]
    linarith only [h8, hk1]
  -- 2kt ≤ 1/2
  have h2kt : 2 * k * t ≤ 1 / 2 := by
    have h : 4 * k * t ≤ 1 := by
      have := mul_le_mul_of_nonneg_left ht2 (by positivity : (0:ℝ) ≤ 4 * k)
      calc 4 * k * t ≤ 4 * k * (1 / (4 * k)) := this
        _ = 1 := by field_simp
    linarith
  -- ===== Stage 7: the exactly trivial deformation at time t =====
  obtain ⟨σ, w, bσ, hσmeas, hσsupp, hσinv, hσclose, hbσ, hwqa, hwid, hwcomm⟩ :=
    hFVL t htpos htt₀
  have hσbd : ∀ z, ‖σ z‖ ≤ 2 * k * t := by
    intro z
    have h1 := hσclose z
    have h2 := hηbd z
    have h3 : ‖(t : ℂ) * η z‖ = t * ‖η z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
    calc ‖σ z‖ = ‖(σ z - (t : ℂ) * η z) + (t : ℂ) * η z‖ := by ring_nf
      _ ≤ ‖σ z - (t : ℂ) * η z‖ + ‖(t : ℂ) * η z‖ := norm_add_le _ _
      _ ≤ δ / 4 * t + t * (2 * k - δ) := by
          rw [h3]
          exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 htpos.le)
      _ ≤ 2 * k * t := by linarith only [mul_nonneg htpos.le hδ.le]
  -- ===== Stage 8: the reflection glue =====
  have hwreal : ∀ r : ℝ, (w (r : ℂ)).im = 0 := by
    intro r
    rw [hwid (r : ℂ) (by simp)]
    simp
  have hwinj : Function.Injective w := hwqa.1.1.injective
  have hwupper : ∀ z : ℂ, 0 < z.im → 0 < (w z).im := by
    intro z hz
    by_contra hle
    have hle' : (w z).im ≤ 0 := not_lt.mp hle
    have h1 : w (w z) = w z := hwid (w z) hle'
    have h2 : w z = z := hwinj h1
    rw [h2] at hle'
    linarith
  obtain ⟨H, bH, hHqa, hHup, hHsym, hbHμ⟩ := exists_reflectGlue hwqa hwreal hwupper
  -- basic properties of the glued map
  have hHid_real : ∀ r : ℝ, H (r : ℂ) = (r : ℂ) := by
    intro r
    rw [hHup (r : ℂ) (by simp)]
    exact hwid (r : ℂ) (by simp)
  have hHupper : ∀ z : ℂ, 0 < z.im → 0 < (H z).im := by
    intro z hz
    rw [hHup z hz.le]
    exact hwupper z hz
  have hHinj : Function.Injective H := hHqa.1.1.injective
  have hHsurj : Function.Surjective H := hHqa.1.1.bijective.surjective
  have hHleft : ∀ z : ℂ, Function.invFun H (H z) = z :=
    fun z => Function.leftInverse_invFun hHinj z
  have hHright : ∀ z : ℂ, H (Function.invFun H z) = z :=
    fun z => Function.rightInverse_invFun hHsurj z
  have hHinv_upper : ∀ z : ℂ, 0 < z.im → 0 < (Function.invFun H z).im := by
    intro z hz
    by_contra hle
    have hle' : (Function.invFun H z).im ≤ 0 := not_lt.mp hle
    rcases lt_or_eq_of_le hle' with hlt | heq
    · -- the inverse point is in the open lower half plane, so its H-image is too
      have hconj := hHsym (starRingEnd ℂ (Function.invFun H z))
      rw [Complex.conj_conj] at hconj
      have him : 0 < (starRingEnd ℂ (Function.invFun H z)).im := by
        simpa using hlt
      have h2 : 0 < (H (starRingEnd ℂ (Function.invFun H z))).im :=
        hHupper _ him
      have h3 : H (Function.invFun H z)
          = starRingEnd ℂ (H (starRingEnd ℂ (Function.invFun H z))) := by
        rw [← hconj]
      have h4 : (H (Function.invFun H z)).im < 0 := by
        rw [h3]
        simpa using h2
      rw [hHright z] at h4
      linarith
    · -- the inverse point is real, so its H-image is real
      have h2 : H (Function.invFun H z) = Function.invFun H z := by
        conv_lhs => rw [eq_ofReal_of_im_eq_zero heq]
        rw [hHid_real]
        exact (eq_ofReal_of_im_eq_zero heq).symm
      have h3 : z = Function.invFun H z := by
        have h4 := hHright z
        rw [h2] at h4
        exact h4.symm
      rw [h3] at hz
      linarith
  have hHinv_real : ∀ r : ℝ, Function.invFun H (r : ℂ) = (r : ℂ) := by
    intro r
    have h := hHleft (r : ℂ)
    rwa [hHid_real r] at h
  have hHcomm : ∀ γ ∈ y.group, ∀ z : ℂ, 0 < z.im →
      H (moebiusMap γ z) = moebiusMap γ (H z) := by
    intro γ hγ z hz
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    rw [hHup _ hγz.le, hHup z hz.le]
    exact hwcomm γ hγ z (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
  have hHinvconj : ∀ W ∈ y.group, ∀ z : ℂ, 0 < z.im →
      Function.invFun H (moebiusMap W z) = moebiusMap W (Function.invFun H z) := by
    intro W hW
    exact inv_conj_of_conj hHinv_upper (fun z _ => hHleft z) (fun z _ => hHright z)
      (fun z hz => hHcomm W hW z hz)
  -- ===== Stage 9: the competitor and its candidacy =====
  set G : ℂ → ℂ := F ∘ Function.invFun H with hGdef
  obtain ⟨bH₂, hHinvqa⟩ := isQCAnalytic_invFun hHqa
  obtain ⟨bG, -, hGqa⟩ := exists_isQCAnalytic_comp hqa hHinvqa
  rw [← hGdef] at hGqa
  have hGcand : IsMarkedCandidate x y G := by
    refine ⟨fun s => ?_, ?_, ?_⟩
    · have h1 : (y.w (s : ℂ)).im = 0 := y.w_real s
      have h2 : y.w (s : ℂ) = ((y.w (s : ℂ)).re : ℂ) := eq_ofReal_of_im_eq_zero h1
      change F (Function.invFun H (y.w (s : ℂ))) = x.w (s : ℂ)
      rw [h2, hHinv_real, ← h2]
      exact hmc.1 s
    · intro W hW
      obtain ⟨W', hW', hFW⟩ := hmc.2.1 W hW
      refine ⟨W', hW', fun z hz => ?_⟩
      have hzi : 0 < (Function.invFun H z).im := hHinv_upper z hz
      change F (Function.invFun H (moebiusMap W z))
        = moebiusMap W' (F (Function.invFun H z))
      rw [hHinvconj W hW z hz]
      exact hFW _ hzi
    · intro W' hW'
      obtain ⟨W, hW, hFW⟩ := hmc.2.2 W' hW'
      refine ⟨W, hW, fun z hz => ?_⟩
      have hzi : 0 < (Function.invFun H z).im := hHinv_upper z hz
      change F (Function.invFun H (moebiusMap W z))
        = moebiusMap W' (F (Function.invFun H z))
      rw [hHinvconj W hW z hz]
      exact hFW _ hzi
  -- ===== Stage 10: pointwise values of the glued coefficient =====
  have hbσfun : bσ.μ = σ := funext hbσ
  rw [hbσfun] at hbHμ
  have hbH_up : ∀ z : ℂ, 0 < z.im → bH.μ z = σ z := by
    intro z hz
    rw [hbHμ]
    exact if_pos hz
  have hbH_low : ∀ z : ℂ, ¬ 0 < z.im →
      bH.μ z = starRingEnd ℂ (σ (starRingEnd ℂ z)) := by
    intro z hz
    rw [hbHμ]
    exact if_neg hz
  have hbHbd : ∀ z : ℂ, ‖bH.μ z‖ ≤ 2 * k * t := by
    intro z
    by_cases hz : 0 < z.im
    · rw [hbH_up z hz]
      exact hσbd z
    · rw [hbH_low z hz, RCLike.norm_conj]
      exact hσbd _
  -- ===== Stage 11: the pointwise Gardiner–Hu estimate on the upper half plane =====
  have hclaim : ∀ ζ : ℂ, 0 < ζ.im → ‖b.μ ζ‖ ≤ k →
      ‖b.μ ζ - σ ζ‖ ≤ k' * ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖ := by
    intro ζ hζ hbζ
    have hμ'ζ : μ' ζ = b.μ ζ := by
      simp only [hμ'def]
      rw [if_pos hbζ]
    have hηζ : η ζ = b.μ ζ - ν ζ := by
      simp only [hηdef]
      rw [if_pos hζ, hμ'ζ]
    have heζ : ‖σ ζ - (t : ℂ) * η ζ‖ ≤ δ / 4 * t := hσclose ζ
    have hνζ : ‖ν ζ‖ ≤ k - δ := hνbd ζ
    have hsζ : ‖σ ζ‖ ≤ 2 * k * t := hσbd ζ
    have hx0 : 0 ≤ ‖b.μ ζ‖ := norm_nonneg _
    have hsplit : σ ζ = (t : ℂ) * (b.μ ζ - ν ζ) + (σ ζ - (t : ℂ) * η ζ) := by
      rw [hηζ]
      ring
    have hnum : b.μ ζ - σ ζ
        = (1 - (t : ℂ)) * b.μ ζ + (t : ℂ) * ν ζ - (σ ζ - (t : ℂ) * η ζ) := by
      rw [hηζ]
      ring
    have hden_ge : 1 - 2 * k ^ 2 * t ≤ ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖ := by
      have h1 : ‖starRingEnd ℂ (σ ζ) * b.μ ζ‖ ≤ 2 * k ^ 2 * t := by
        rw [norm_mul, RCLike.norm_conj]
        calc ‖σ ζ‖ * ‖b.μ ζ‖ ≤ 2 * k * t * k :=
              mul_le_mul hsζ hbζ hx0 (by positivity)
          _ = 2 * k ^ 2 * t := by ring
      have h2 := norm_sub_norm_le (1 : ℂ) (starRingEnd ℂ (σ ζ) * b.μ ζ)
      rw [norm_one] at h2
      linarith only [h1, h2]
    rcases le_or_gt ‖b.μ ζ‖ (k - δ / 2) with hxle | hxgt
    · -- the small-coefficient region
      have e1 : ‖(1 - (t : ℂ)) * b.μ ζ‖ = (1 - t) * ‖b.μ ζ‖ := by
        rw [norm_mul]
        congr 1
        have e : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
        rw [e, Complex.norm_real, Real.norm_of_nonneg (by linarith only [ht1])]
      have e2 : ‖(t : ℂ) * ν ζ‖ ≤ t * (k - δ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
        exact mul_le_mul_of_nonneg_left hνζ htpos.le
      have hnum_le : ‖b.μ ζ - σ ζ‖ ≤ (1 - t) * ‖b.μ ζ‖ + t * (k - δ) + δ / 4 * t := by
        rw [hnum]
        calc ‖(1 - (t : ℂ)) * b.μ ζ + (t : ℂ) * ν ζ - (σ ζ - (t : ℂ) * η ζ)‖
            ≤ ‖(1 - (t : ℂ)) * b.μ ζ + (t : ℂ) * ν ζ‖ + ‖σ ζ - (t : ℂ) * η ζ‖ :=
              norm_sub_le _ _
          _ ≤ ‖(1 - (t : ℂ)) * b.μ ζ‖ + ‖(t : ℂ) * ν ζ‖
              + ‖σ ζ - (t : ℂ) * η ζ‖ := by
              have h3 := norm_add_le ((1 - (t : ℂ)) * b.μ ζ) ((t : ℂ) * ν ζ)
              linarith only [h3]
          _ ≤ (1 - t) * ‖b.μ ζ‖ + t * (k - δ) + δ / 4 * t := by
              rw [e1]
              linarith only [e2, heζ]
      have hstep1 : ‖b.μ ζ - σ ζ‖ ≤ k - δ / 2 := by
        have h5 : (1 - t) * ‖b.μ ζ‖ ≤ (1 - t) * (k - δ / 2) :=
          mul_le_mul_of_nonneg_left hxle (by linarith only [ht1])
        linarith only [hnum_le, h5, mul_nonneg htpos.le hδ.le]
      have hstep2 : k - δ / 2 ≤ k' * (1 - 2 * k ^ 2 * t) := by
        have h6 : (0 : ℝ) ≤ 2 * k ^ 2 * c₃ * t ^ 2 := by positivity
        rw [hk'def]
        linarith only [ht3, h6]
      calc ‖b.μ ζ - σ ζ‖ ≤ k - δ / 2 := hstep1
        _ ≤ k' * (1 - 2 * k ^ 2 * t) := hstep2
        _ ≤ k' * ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖ :=
            mul_le_mul_of_nonneg_left hden_ge hk'0
    · -- the large-coefficient region: squared-norm expansion
      have hR_ge : t * δ ^ 2 / 8 ≤ (starRingEnd ℂ (b.μ ζ) * σ ζ).re := by
        have hre1 : (starRingEnd ℂ (b.μ ζ) * σ ζ).re
            = t * (starRingEnd ℂ (b.μ ζ) * (b.μ ζ - ν ζ)).re
              + (starRingEnd ℂ (b.μ ζ) * (σ ζ - (t : ℂ) * η ζ)).re := by
          conv_lhs => rw [hsplit]
          rw [mul_add, Complex.add_re]
          congr 1
          have e : starRingEnd ℂ (b.μ ζ) * ((t : ℂ) * (b.μ ζ - ν ζ))
              = (t : ℂ) * (starRingEnd ℂ (b.μ ζ) * (b.μ ζ - ν ζ)) := by ring
          rw [e]
          simp [Complex.mul_re]
        have hre2 : (starRingEnd ℂ (b.μ ζ) * b.μ ζ).re = ‖b.μ ζ‖ ^ 2 := by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]
        have hre3 : (starRingEnd ℂ (b.μ ζ) * ν ζ).re ≤ ‖b.μ ζ‖ * (k - δ) := by
          calc (starRingEnd ℂ (b.μ ζ) * ν ζ).re
              ≤ |(starRingEnd ℂ (b.μ ζ) * ν ζ).re| := le_abs_self _
            _ ≤ ‖starRingEnd ℂ (b.μ ζ) * ν ζ‖ := Complex.abs_re_le_norm _
            _ = ‖b.μ ζ‖ * ‖ν ζ‖ := by rw [norm_mul, RCLike.norm_conj]
            _ ≤ ‖b.μ ζ‖ * (k - δ) := mul_le_mul_of_nonneg_left hνζ hx0
        have hre4 : -(‖b.μ ζ‖ * (δ / 4 * t))
            ≤ (starRingEnd ℂ (b.μ ζ) * (σ ζ - (t : ℂ) * η ζ)).re := by
          have h5 : |(starRingEnd ℂ (b.μ ζ) * (σ ζ - (t : ℂ) * η ζ)).re|
              ≤ ‖b.μ ζ‖ * (δ / 4 * t) := by
            calc |(starRingEnd ℂ (b.μ ζ) * (σ ζ - (t : ℂ) * η ζ)).re|
                ≤ ‖starRingEnd ℂ (b.μ ζ) * (σ ζ - (t : ℂ) * η ζ)‖ :=
                  Complex.abs_re_le_norm _
              _ = ‖b.μ ζ‖ * ‖σ ζ - (t : ℂ) * η ζ‖ := by
                  rw [norm_mul, RCLike.norm_conj]
              _ ≤ ‖b.μ ζ‖ * (δ / 4 * t) := mul_le_mul_of_nonneg_left heζ hx0
          linarith only [h5, neg_abs_le
            ((starRingEnd ℂ (b.μ ζ) * (σ ζ - (t : ℂ) * η ζ)).re)]
        have hre5 : ‖b.μ ζ‖ ^ 2 - ‖b.μ ζ‖ * (k - δ)
            ≤ (starRingEnd ℂ (b.μ ζ) * (b.μ ζ - ν ζ)).re := by
          have e : (starRingEnd ℂ (b.μ ζ) * (b.μ ζ - ν ζ)).re
              = ‖b.μ ζ‖ ^ 2 - (starRingEnd ℂ (b.μ ζ) * ν ζ).re := by
            rw [mul_sub, Complex.sub_re, hre2]
          rw [e]
          linarith only [hre3]
        have hXlow : δ / 2 ≤ ‖b.μ ζ‖ := by linarith only [hxgt, hδk]
        have hfac : δ / 4 ≤ ‖b.μ ζ‖ - k + 3 * δ / 4 := by linarith only [hxgt]
        have h9 : δ / 2 * (δ / 4) ≤ ‖b.μ ζ‖ * (‖b.μ ζ‖ - k + 3 * δ / 4) :=
          mul_le_mul hXlow hfac (by linarith only [hδ]) hx0
        have h7 := mul_le_mul_of_nonneg_left hre5 htpos.le
        have h10 := mul_le_mul_of_nonneg_left h9 htpos.le
        rw [hre1]
        linarith only [h7, h10, hre4]
      have hnum_sq : ‖b.μ ζ - σ ζ‖ ^ 2
          = ‖b.μ ζ‖ ^ 2 - 2 * (starRingEnd ℂ (b.μ ζ) * σ ζ).re + ‖σ ζ‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_sub]
        have e1 : (b.μ ζ * starRingEnd ℂ (σ ζ)).re
            = (starRingEnd ℂ (b.μ ζ) * σ ζ).re := by
          have e : b.μ ζ * starRingEnd ℂ (σ ζ)
              = starRingEnd ℂ (starRingEnd ℂ (b.μ ζ) * σ ζ) := by
            rw [map_mul, Complex.conj_conj]
          rw [e, Complex.conj_re]
        rw [e1, ← Complex.sq_norm, ← Complex.sq_norm]
        ring
      have hden_sq : ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖ ^ 2
          = 1 - 2 * (starRingEnd ℂ (b.μ ζ) * σ ζ).re + ‖σ ζ‖ ^ 2 * ‖b.μ ζ‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
          Complex.normSq_conj]
        have e1 : ((1 : ℂ) * starRingEnd ℂ (starRingEnd ℂ (σ ζ) * b.μ ζ)).re
            = (starRingEnd ℂ (b.μ ζ) * σ ζ).re := by
          rw [one_mul, map_mul, Complex.conj_conj, mul_comm]
        rw [e1, ← Complex.sq_norm, ← Complex.sq_norm]
        ring
      have hXk2 : ‖b.μ ζ‖ ^ 2 ≤ k ^ 2 := by nlinarith only [hbζ, hx0]
      have hS2 : ‖σ ζ‖ ^ 2 ≤ 4 * k ^ 2 * t ^ 2 := by
        nlinarith only [hsζ, norm_nonneg (σ ζ)]
      have hk'2 : k' ^ 2 ≤ k ^ 2 := by nlinarith only [hk'0, hk'k.le]
      have hRpos : (0 : ℝ) ≤ (starRingEnd ℂ (b.μ ζ) * σ ζ).re := by
        linarith only [hR_ge, mul_nonneg htpos.le (sq_nonneg δ)]
      have hmain : k ^ 2 - 2 * (starRingEnd ℂ (b.μ ζ) * σ ζ).re + 4 * k ^ 2 * t ^ 2
          ≤ k' ^ 2 * (1 - 2 * (starRingEnd ℂ (b.μ ζ) * σ ζ).re) := by
        have hA : k ^ 2 - k' ^ 2 ≤ 2 * k * (c₃ * t) := by
          rw [hk'def]
          linarith only [sq_nonneg (c₃ * t)]
        have hB : 2 * k * (c₃ * t) ≤ t * δ ^ 2 * (1 - k ^ 2) / 8 := by
          rw [hc₃def]
          have h8 : (0 : ℝ) ≤ t * δ ^ 2 * (1 - k ^ 2) * (1 - k) :=
            mul_nonneg (mul_nonneg (mul_nonneg htpos.le (sq_nonneg δ)) h1k2.le)
              (by linarith only [hk1])
          linarith only [h8]
        have hC : 4 * k ^ 2 * t ^ 2 ≤ t * δ ^ 2 * (1 - k ^ 2) / 8 := by
          have h8 := mul_le_mul_of_nonneg_right ht4 htpos.le
          linarith only [h8]
        have h2' : 1 - k ^ 2 ≤ 1 - k' ^ 2 := by nlinarith only [hk'0, hk'k.le]
        have h1' : (0 : ℝ) ≤ 1 - k' ^ 2 := by nlinarith only [hk'0, hk'1]
        have hD : t * δ ^ 2 / 8 * (1 - k ^ 2)
            ≤ (starRingEnd ℂ (b.μ ζ) * σ ζ).re * (1 - k' ^ 2) :=
          mul_le_mul hR_ge h2' h1k2.le hRpos
        linarith only [hA, hB, hC, hD]
      have hfinal_sq : ‖b.μ ζ - σ ζ‖ ^ 2
          ≤ (k' * ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖) ^ 2 := by
        have h1' : k' ^ 2 * (1 - 2 * (starRingEnd ℂ (b.μ ζ) * σ ζ).re)
            ≤ k' ^ 2 * ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg k')
          rw [hden_sq]
          linarith only [mul_nonneg (sq_nonneg ‖σ ζ‖) (sq_nonneg ‖b.μ ζ‖)]
        calc ‖b.μ ζ - σ ζ‖ ^ 2
            ≤ k ^ 2 - 2 * (starRingEnd ℂ (b.μ ζ) * σ ζ).re + 4 * k ^ 2 * t ^ 2 := by
              rw [hnum_sq]
              linarith only [hXk2, hS2]
          _ ≤ k' ^ 2 * (1 - 2 * (starRingEnd ℂ (b.μ ζ) * σ ζ).re) := hmain
          _ ≤ k' ^ 2 * ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖ ^ 2 := h1'
          _ = (k' * ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖) ^ 2 := by ring
      have hden0 : 0 ≤ k' * ‖1 - starRingEnd ℂ (σ ζ) * b.μ ζ‖ :=
        mul_nonneg hk'0 (norm_nonneg _)
      by_contra hcon
      push Not at hcon
      have hnumpos : 0 < ‖b.μ ζ - σ ζ‖ := lt_of_le_of_lt hden0 hcon
      nlinarith only [hfinal_sq, hcon, hden0, hnumpos]
  -- ===== Stage 12: the almost-everywhere plane estimate =====
  have hEst : ∀ᵐ z, ‖b.μ z - bH.μ z‖ ≤ k' * ‖1 - starRingEnd ℂ (bH.μ z) * b.μ z‖ := by
    -- the real axis is Lebesgue-null
    have haxis : volume {z : ℂ | z.im = 0} = 0 := by
      have he : MeasurePreserving Complex.measurableEquivRealProd
          (volume : Measure ℂ) volume := Complex.volume_preserving_equiv_real_prod
      have heq : {z : ℂ | z.im = 0}
          = Complex.measurableEquivRealProd ⁻¹' {p : ℝ × ℝ | p.2 = 0} := by
        ext z
        simp [Complex.measurableEquivRealProd_apply]
      rw [heq, he.measure_preimage
        ((measurableSet_eq_fun measurable_snd measurable_const).nullMeasurableSet)]
      have hprod : {p : ℝ × ℝ | p.2 = 0} = (Set.univ : Set ℝ) ×ˢ {(0 : ℝ)} := by
        ext p
        simp
      rw [hprod, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    -- the reflected bad set is null
    have hNnull : volume {z : ℂ | ¬ ‖b.μ z‖ ≤ k} = 0 := ae_iff.mp hbd
    have hconj_null :
        volume ((fun z => starRingEnd ℂ z) '' {z : ℂ | ¬ ‖b.μ z‖ ≤ k}) = 0 := by
      have hmp : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) volume volume := by
        have h := Complex.conjLIE.measurePreserving
        have he : ⇑Complex.conjLIE = fun z : ℂ => starRingEnd ℂ z := by
          funext z
          simp [Complex.conjLIE_apply]
        rwa [he] at h
      have himg_pre : (fun z : ℂ => starRingEnd ℂ z) '' {z : ℂ | ¬ ‖b.μ z‖ ≤ k}
          = (fun z : ℂ => starRingEnd ℂ z) ⁻¹' {z : ℂ | ¬ ‖b.μ z‖ ≤ k} := by
        ext w
        constructor
        · rintro ⟨v, hv, rfl⟩
          simpa [Complex.conj_conj] using hv
        · intro hw
          exact ⟨starRingEnd ℂ w, hw, Complex.conj_conj w⟩
      rw [himg_pre]
      obtain ⟨T, hsub, hTmeas, hT0⟩ := exists_measurable_superset_of_null hNnull
      refine measure_mono_null (Set.preimage_mono hsub) ?_
      rw [hmp.measure_preimage hTmeas.nullMeasurableSet]
      exact hT0
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_)
      (measure_union_null (measure_union_null haxis hNnull) hconj_null)
    simp only [Set.mem_setOf_eq] at hz
    by_contra hnot
    apply hz
    simp only [Set.mem_union, Set.mem_setOf_eq] at hnot
    push Not at hnot
    obtain ⟨⟨him, hbz⟩, hcj⟩ := hnot
    rcases lt_or_gt_of_ne him with hlow | hup
    · -- the lower half plane: reflect to the upper estimate at the conjugate
      have hζ : 0 < (starRingEnd ℂ z).im := by
        simpa using hlow
      have hbζ : ‖b.μ (starRingEnd ℂ z)‖ ≤ k := by
        by_contra hb
        exact hcj ⟨starRingEnd ℂ z, not_le.mp hb, Complex.conj_conj z⟩
      have hcl := hclaim (starRingEnd ℂ z) hζ hbζ
      have hbμz : b.μ z = starRingEnd ℂ (b.μ (starRingEnd ℂ z)) := by
        have h := congrFun hsym z
        unfold symmExtension at h
        rw [if_neg (not_lt.mpr hlow.le)] at h
        exact h
      have hbHz : bH.μ z = starRingEnd ℂ (σ (starRingEnd ℂ z)) :=
        hbH_low z (not_lt.mpr hlow.le)
      have e1 : ‖b.μ z - bH.μ z‖
          = ‖b.μ (starRingEnd ℂ z) - σ (starRingEnd ℂ z)‖ := by
        rw [hbμz, hbHz, ← map_sub, RCLike.norm_conj]
      have e2 : ‖1 - starRingEnd ℂ (bH.μ z) * b.μ z‖
          = ‖1 - starRingEnd ℂ (σ (starRingEnd ℂ z)) * b.μ (starRingEnd ℂ z)‖ := by
        rw [hbμz, hbHz, Complex.conj_conj]
        have e : (1 : ℂ) - σ (starRingEnd ℂ z)
              * starRingEnd ℂ (b.μ (starRingEnd ℂ z))
            = starRingEnd ℂ (1 - starRingEnd ℂ (σ (starRingEnd ℂ z))
              * b.μ (starRingEnd ℂ z)) := by
          rw [map_sub, map_one, map_mul, Complex.conj_conj]
        rw [e, RCLike.norm_conj]
      rw [e1, e2]
      exact hcl
    · -- the upper half plane: the estimate applies directly
      have hcl := hclaim z hup hbz
      rw [hbH_up z hup]
      exact hcl
  -- ===== Stage 13: the coefficient bound of the competitor via the chain rule =====
  have hkey : ∀ᵐ w', ‖bG.μ w'‖ ≤ k' ∧ dzbar G w' = bG.μ w' * dz G w' := by
    -- Lusin (N) for the glued map
    have hHlusin : ∀ S : Set ℂ, volume S = 0 → volume (H '' S) = 0 := by
      obtain ⟨p, gx, gy, hp2, hgrad, hgxp, hgyp⟩ :=
        hHqa.exists_weakGradient_memLpLocOn_gt_two
      intro S hS
      exact lusinN_image_null_of_weakGradient hp2 hHqa.1.1.continuous hgrad hgxp hgyp hS
    -- the source-side good event
    set P : ℂ → Prop := fun z =>
      (0 < (fderiv ℝ F z).det ∧ dzbar F z = b.μ z * dz F z ∧ ‖b.μ z‖ ≤ k)
      ∧ (0 < (fderiv ℝ H z).det ∧ dzbar H z = bH.μ z * dz H z)
      ∧ ‖b.μ z - bH.μ z‖ ≤ k' * ‖1 - starRingEnd ℂ (bH.μ z) * b.μ z‖ with hPdef
    have hPae : ∀ᵐ z, P z := by
      filter_upwards [hqa.1.2, hqa.2.2, hbd, hHqa.1.2, hHqa.2.2, hEst]
        with z h1 h2 h3 h4 h5 h6
      simp only [hPdef]
      exact ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩
    have hPnull : volume {z | ¬ P z} = 0 := ae_iff.mp hPae
    have htrans : ∀ᵐ w', P (Function.invFun H w') := by
      rw [ae_iff]
      refine measure_mono_null (fun w' hw' => ?_) (hHlusin _ hPnull)
      exact ⟨Function.invFun H w', hw', hHright w'⟩
    filter_upwards [htrans, hHinvqa.1.2, hGqa.2.2] with w' hP' hdetinv hGbelt
    simp only [hPdef] at hP'
    obtain ⟨⟨hdetF, hbelF, hbndF⟩, ⟨hdetH, hbelH⟩, hest⟩ := hP'
    -- differentiability from the positive Jacobians
    have hdiffinv : DifferentiableAt ℝ (Function.invFun H) w' := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hdetinv
      simp [ContinuousLinearMap.det] at hdetinv
    have hdiffF : DifferentiableAt ℝ F (Function.invFun H w') := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hdetF
      simp [ContinuousLinearMap.det] at hdetF
    have hdiffH : DifferentiableAt ℝ H (Function.invFun H w') := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hdetH
      simp [ContinuousLinearMap.det] at hdetH
    -- nonvanishing of the holomorphic-direction derivatives
    have hdzinv_ne : dz (Function.invFun H) w' ≠ 0 := by
      intro h0
      rw [det_fderiv_eq_wirtinger, h0] at hdetinv
      simp only [norm_zero] at hdetinv
      linarith only [hdetinv, sq_nonneg ‖dzbar (Function.invFun H) w'‖]
    have hdzF_ne : dz F (Function.invFun H w') ≠ 0 := by
      intro h0
      rw [det_fderiv_eq_wirtinger, h0] at hdetF
      simp only [norm_zero] at hdetF
      linarith only [hdetF, sq_nonneg ‖dzbar F (Function.invFun H w')‖]
    have hdzH_ne : dz H (Function.invFun H w') ≠ 0 := by
      intro h0
      rw [det_fderiv_eq_wirtinger, h0] at hdetH
      simp only [norm_zero] at hdetH
      linarith only [hdetH, sq_nonneg ‖dzbar H (Function.invFun H w')‖]
    -- the composite with the inverse is the identity
    have hid : (fun v => H (Function.invFun H v)) = fun v : ℂ => v := funext hHright
    have hc1 := dzbar_comp hdiffinv hdiffH
    rw [hid] at hc1
    have hzero : dzbar (fun v : ℂ => v) w' = 0 :=
      dzbar_eq_zero_of_differentiableAt differentiableAt_fun_id
    rw [hzero, hbelH] at hc1
    -- the antiholomorphic derivative of the inverse
    have hX : dzbar (Function.invFun H) w'
        = -(bH.μ (Function.invFun H w'))
          * starRingEnd ℂ (dz (Function.invFun H) w') := by
      refine mul_left_cancel₀ hdzH_ne ?_
      linear_combination -hc1
    -- chain rule for the competitor
    have hc2 := dzbar_comp hdiffinv hdiffF
    have hc3 := dz_comp hdiffinv hdiffF
    have hGbar : dzbar G w'
        = dz F (Function.invFun H w') * starRingEnd ℂ (dz (Function.invFun H) w')
          * (b.μ (Function.invFun H w') - bH.μ (Function.invFun H w')) := by
      have e : dzbar G w' = dzbar (fun v => F (Function.invFun H v)) w' := rfl
      rw [e, hc2, hX, hbelF]
      ring
    have hGz : dz G w'
        = dz F (Function.invFun H w') * dz (Function.invFun H) w'
          * (1 - starRingEnd ℂ (bH.μ (Function.invFun H w'))
            * b.μ (Function.invFun H w')) := by
      have e : dz G w' = dz (fun v => F (Function.invFun H v)) w' := rfl
      rw [e, hc3, hX, hbelF]
      simp only [map_neg, map_mul, Complex.conj_conj]
      ring
    -- the norm bound
    have hnb : ‖dzbar G w'‖ ≤ k' * ‖dz G w'‖ := by
      rw [hGbar, hGz, norm_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_conj]
      have hab : (0 : ℝ) ≤ ‖dz F (Function.invFun H w')‖
          * ‖dz (Function.invFun H) w'‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      linarith only [mul_le_mul_of_nonneg_left hest hab]
    -- the factor in the holomorphic derivative does not vanish
    have hdzG_ne : dz G w' ≠ 0 := by
      rw [hGz]
      refine mul_ne_zero (mul_ne_zero hdzF_ne hdzinv_ne) ?_
      intro h0
      have h1 : ‖starRingEnd ℂ (bH.μ (Function.invFun H w'))
          * b.μ (Function.invFun H w')‖ ≤ 1 / 2 := by
        rw [norm_mul, RCLike.norm_conj]
        have h2 := mul_le_mul (hbHbd (Function.invFun H w')) hbndF
          (norm_nonneg _) (by positivity)
        nlinarith only [h2, h2kt, hk1, hk0,
          norm_nonneg (b.μ (Function.invFun H w')),
          norm_nonneg (bH.μ (Function.invFun H w'))]
      have h2 : (1 : ℂ) = starRingEnd ℂ (bH.μ (Function.invFun H w'))
          * b.μ (Function.invFun H w') := sub_eq_zero.mp h0
      rw [← h2, norm_one] at h1
      linarith only [h1]
    -- conclude the coefficient bound
    have hbGle : ‖bG.μ w'‖ ≤ k' := by
      have h1 : ‖bG.μ w'‖ * ‖dz G w'‖ ≤ k' * ‖dz G w'‖ := by
        rw [← norm_mul, ← hGbelt]
        exact hnb
      exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hdzG_ne)
    exact ⟨hbGle, hGbelt⟩
  -- ===== Stage 14: the improved Beltrami coefficient and the dilatation drop =====
  set μ₂ : ℂ → ℂ := fun w' => if ‖bG.μ w'‖ ≤ k' then bG.μ w' else 0 with hμ₂def
  have hμ₂meas : Measurable μ₂ :=
    Measurable.ite (measurableSet_le bG.measurable.norm measurable_const)
      bG.measurable measurable_const
  have hμ₂bd : ∀ w', ‖μ₂ w'‖ ≤ k' := by
    intro w'
    by_cases h : ‖bG.μ w'‖ ≤ k'
    · rw [hμ₂def]
      simpa [if_pos h] using h
    · rw [hμ₂def]
      simpa [if_neg h] using hk'0
  have hμ₂bound : eLpNormEssSup μ₂ volume < 1 := by
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall hμ₂bd)) ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hk'0 |>.mpr hk'1
  set b' : BeltramiCoeff := ⟨μ₂, hμ₂meas, hμ₂bound⟩ with hb'def
  have hb'qa : IsQCAnalytic G b' := by
    refine ⟨hGqa.1, hGqa.2.1, ?_⟩
    filter_upwards [hkey] with w' hw'
    have h1 : b'.μ w' = bG.μ w' := by
      change μ₂ w' = bG.μ w'
      rw [hμ₂def]
      simp [if_pos hw'.1]
    rw [h1]
    exact hw'.2
  have hb'inf : b'.normInf ≤ k' := by
    have h1 : eLpNormEssSup μ₂ volume ≤ ENNReal.ofReal k' :=
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hμ₂bd)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal hk'0] at h2
  have hKlt : b'.K < b.K := by
    have hn0 : 0 ≤ b'.normInf := b'.normInf_nonneg
    have hn1 : b'.normInf < 1 := b'.normInf_lt_one
    have hnk : b'.normInf < k := lt_of_le_of_lt hb'inf hk'k
    change (1 + b'.normInf) / (1 - b'.normInf) < (1 + k) / (1 - k)
    rw [div_lt_div_iff₀ (by linarith only [hn1]) (by linarith only [hk1])]
    linarith only [hnk]
  exact ⟨G, b'.K, hb'qa.isQCGeometric_K, hGcand, hKlt⟩

/-- **Hamilton–Krushkal necessity**: the coefficient of a symmetric extremal marked
candidate attains its norm as the real part of its pairing with a unit-mass automorphic
quadratic differential of the domain group. -/
theorem hamilton_krushkal_necessity (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {F : ℂ → ℂ} {b : BeltramiCoeff}
    (hmc : IsMarkedCandidate x y F) (hqa : IsQCAnalytic F b)
    (hsym : b.μ = symmExtension b.μ)
    (hFsym : ∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    (hext : b.K = sInf (gDilatationSet x y)) :
    ∃ q₀ : QuadraticDifferential y.group, q₀.l1Norm ≤ 1 ∧
      (qdPairing b.μ q₀).re = b.normInf := by
  -- transport the Fuchsian triple to the range group
  have hΓy := TeichRep.isFuchsian_group hΓ₀ hfree y
  have hfy := y.group_free hfree
  have hccy := y.group_cocompact hcc
  -- the coefficient is a.e. bounded by its norm on the upper half plane
  have hne : eLpNormEssSup b.μ volume ≠ ⊤ := b.bound.ne_top
  have hbd : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖b.μ z‖ ≤ b.normInf := by
    refine ae_restrict_of_ae ?_
    filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with z hz
    have h := ENNReal.toReal_mono hne hz
    rwa [toReal_enorm] at h
  -- the Hamilton maximizer over the unit ball
  obtain ⟨q₀, hq01, hq0max⟩ := exists_qdPairing_maximizer hΓy hfy hccy b.measurable hbd
  refine ⟨q₀, hq01, ?_⟩
  have hfin : q₀.l1Norm ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq01
  -- upper bound: the pairing never exceeds the coefficient norm
  have hub : (qdPairing b.μ q₀).re ≤ b.normInf := by
    have h1 : (qdPairing b.μ q₀).re ≤ ‖qdPairing b.μ q₀‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have h2 := norm_qdPairing_le b.normInf_nonneg hbd q₀ hfin
    have h3 : q₀.l1Norm.toReal ≤ 1 := by
      have h4 := ENNReal.toReal_mono ENNReal.one_ne_top hq01
      simpa using h4
    have h5 : b.normInf * q₀.l1Norm.toReal ≤ b.normInf * 1 :=
      mul_le_mul_of_nonneg_left h3 b.normInf_nonneg
    linarith
  -- lower bound: a strict gap would defeat extremality
  by_contra hv
  have hlt : (qdPairing b.μ q₀).re < b.normInf := lt_of_le_of_ne hub hv
  have hδ : 0 < b.normInf - (qdPairing b.μ q₀).re := sub_pos.mpr hlt
  have hgap : ∀ q : QuadraticDifferential y.group, q.l1Norm ≤ 1 →
      (qdPairing b.μ q).re ≤ b.normInf - (b.normInf - (qdPairing b.μ q₀).re) := by
    intro q hq
    have h := hq0max q hq
    linarith
  obtain ⟨G, K', hGgeo, hGmc, hK'⟩ :=
    exists_lt_dilatation_of_pairing_gap hΓ₀ hfree hcc hmc hqa hsym hFsym hδ hgap
  have hmem : K' ∈ gDilatationSet x y := ⟨G, hGgeo, hGmc⟩
  have hle : sInf (gDilatationSet x y) ≤ K' :=
    csInf_le (bddBelow_gDilatationSet x y) hmem
  rw [← hext] at hle
  linarith

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Matrix.Notation
import RiemannDynamics.Sphere.Basic

/-!
# Möbius transformations of the Riemann sphere

Mathlib provides the set-theoretic action of `GL (Fin 2) ℂ` on
`ℂ̂ = OnePoint ℂ` (via the identification with `ℙ¹(ℂ)`), together with the
explicit Möbius formulas `OnePoint.smul_some_eq_ite` and
`OnePoint.smul_infty_eq_ite`. This file supplies the topological layer that
Mathlib leaves open:

* `continuous_glSMul` : every Möbius transformation `g • ·` is continuous on
  `ℂ̂` (hence a homeomorphism, its inverse being the action of `g⁻¹`);
* `exists_glSMul_eq_zero_one_infty` : the action is transitive on ordered
  triples of distinct points — every triple can be sent to `(0, 1, ∞)`;
* `inversionGL` : the inversion `z ↦ 1/z` as a group element, which
  interchanges the two standard charts of `ℂ̂`.
-/

open OnePoint Matrix

namespace RiemannDynamics

/-- The inversion `z ↦ 1/z` (swapping `0 ↔ ∞`) as an element of
`GL (Fin 2) ℂ`. -/
noncomputable def inversionGL : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0]
    (by norm_num [Matrix.det_fin_two_of])

/-- The inversion acts on finite points by `z ↦ 1/z`, sending `0 ↦ ∞`. -/
theorem inversionGL_smul_coe (z : ℂ) :
    inversionGL • (z : ℂ̂) = if z = 0 then ∞ else ((z⁻¹ : ℂ) : ℂ̂) := by
  have hmat : (inversionGL : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] := rfl
  rw [OnePoint.smul_some_eq_ite, hmat]
  simp [one_div]

/-- The inversion sends `∞ ↦ 0`. -/
theorem inversionGL_smul_infty : inversionGL • (∞ : ℂ̂) = ((0 : ℂ) : ℂ̂) := by
  have hmat : (inversionGL : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] := rfl
  rw [OnePoint.smul_infty_eq_ite, hmat]
  norm_num

/-- On the source of the infinity chart, the inversion recovers a sphere point
from its `chartInftyMap` coordinate. -/
theorem inversionGL_smul_coe_chartInftyMap {z : ℂ̂} (hz : z ≠ ((0 : ℂ) : ℂ̂)) :
    inversionGL • ((chartInftyMap z : ℂ) : ℂ̂) = z := by
  cases z with
  | infty =>
    have hval : chartInftyMap (∞ : ℂ̂) = 0 := rfl
    rw [hval, inversionGL_smul_coe, if_pos rfl]
  | coe w =>
    have hw : w ≠ 0 := fun h => hz (OnePoint.coe_eq_coe.mpr h)
    have hval : chartInftyMap ((w : ℂ) : ℂ̂) = w⁻¹ := rfl
    rw [hval, inversionGL_smul_coe, if_neg (inv_ne_zero hw), inv_inv]

/-- **Möbius transformations are continuous** on the Riemann sphere. Since the
inverse transformation is the action of `g⁻¹`, every `g • ·` is in fact a
homeomorphism of `ℂ̂`. -/
theorem continuous_glSMul (g : GL (Fin 2) ℂ) : Continuous (fun z : ℂ̂ => g • z) := by
  -- The coercion `ℂ → ℂ̂` tends to `∞` along the cocompact filter.
  have hcoe_inf : Filter.Tendsto ((↑) : ℂ → ℂ̂) (Filter.cocompact ℂ) (nhds (∞ : ℂ̂)) := by
    rw [← Filter.coclosedCompact_eq_cocompact]
    exact OnePoint.tendsto_coe_infty
  -- Step (A): every "affine" element (lower-left entry zero) acts continuously.
  have haff : ∀ u : GL (Fin 2) ℂ, (u : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 →
      Continuous (fun z : ℂ̂ => u • z) := by
    intro u h10
    have hdet := u.det_ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    have ha : (u : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hd : (u : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hval_coe : ∀ x : ℂ,
        u • (x : ℂ̂) = (((u 0 0 * x + u 0 1) / u 1 1 : ℂ) : ℂ̂) := by
      intro x
      rw [OnePoint.smul_some_eq_ite, h10, zero_mul, zero_add, if_neg hd]
    have hval_infty : u • (∞ : ℂ̂) = ∞ := by
      rw [OnePoint.smul_infty_eq_ite, if_pos h10]
    rw [OnePoint.continuous_iff]
    refine ⟨?_, ?_⟩
    · -- the affine map sends the cocompact filter to itself, hence `∞ ↦ ∞`.
      have hphi : Filter.Tendsto (fun x : ℂ => (u 0 0 * x + u 0 1) / u 1 1)
          (Filter.cocompact ℂ) (Filter.cocompact ℂ) := by
        rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
        have ha' : (0 : ℝ) < ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ := norm_pos_iff.mpr ha
        have hd' : (0 : ℝ) < ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ := norm_pos_iff.mpr hd
        have hnum : Filter.Tendsto (fun x : ℂ => ‖u 0 0 * x + u 0 1‖)
            (Bornology.cobounded ℂ) Filter.atTop := by
          have hlow : Filter.Tendsto (fun x : ℂ => ‖u 0 0‖ * ‖x‖ + -‖u 0 1‖)
              (Bornology.cobounded ℂ) Filter.atTop :=
            Filter.tendsto_atTop_add_const_right _ _
              (Filter.Tendsto.const_mul_atTop ha' tendsto_norm_cobounded_atTop)
          refine Filter.tendsto_atTop_mono (fun x => ?_) hlow
          have h := norm_sub_norm_le (u 0 0 * x) (-(u 0 1))
          rw [norm_neg, sub_neg_eq_add, norm_mul] at h
          linarith
        exact (hnum.atTop_div_const hd').congr fun x => (norm_div _ _).symm
      have key : Filter.Tendsto (fun x : ℂ => u • (↑x : ℂ̂)) (Filter.coclosedCompact ℂ)
          (nhds (u • (∞ : ℂ̂))) := by
        rw [hval_infty, Filter.coclosedCompact_eq_cocompact]
        exact (hcoe_inf.comp hphi).congr fun x => (hval_coe x).symm
      exact key
    · have key : Continuous (fun x : ℂ => u • (↑x : ℂ̂)) := by
        have hcont : Continuous (fun x : ℂ => (u 0 0 * x + u 0 1) / u 1 1) :=
          ((continuous_const.mul continuous_id).add continuous_const).div_const _
        exact (OnePoint.continuous_coe.comp hcont).congr fun x => (hval_coe x).symm
      exact key
  -- Step (B): the inversion acts continuously.
  have hinvcont : Continuous (fun z : ℂ̂ => inversionGL • z) := by
    rw [OnePoint.continuous_iff]
    refine ⟨?_, ?_⟩
    · have key : Filter.Tendsto (fun x : ℂ => inversionGL • (↑x : ℂ̂))
          (Filter.coclosedCompact ℂ) (nhds (inversionGL • (∞ : ℂ̂))) := by
        rw [inversionGL_smul_infty, Filter.coclosedCompact_eq_cocompact]
        have hi : Filter.Tendsto (fun x : ℂ => x⁻¹) (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
          rw [← Metric.cobounded_eq_cocompact]
          exact Filter.tendsto_inv₀_cobounded
        have hbase : Filter.Tendsto (fun x : ℂ => ((x⁻¹ : ℂ) : ℂ̂)) (Filter.cocompact ℂ)
            (nhds (((0 : ℂ) : ℂ̂))) := (OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hi
        refine hbase.congr' ?_
        have h0ne : ∀ᶠ x : ℂ in Filter.cocompact ℂ, x ≠ 0 := by
          filter_upwards [(isCompact_singleton :
            IsCompact ({0} : Set ℂ)).compl_mem_cocompact] with x hx
          simpa using hx
        filter_upwards [h0ne] with x hx
        rw [inversionGL_smul_coe, if_neg hx]
      exact key
    · have key : Continuous (fun x : ℂ => inversionGL • (↑x : ℂ̂)) := by
        rw [continuous_iff_continuousAt]
        intro x₀
        by_cases hx₀ : x₀ = 0
        · subst hx₀
          have hv0 : inversionGL • ((0 : ℂ) : ℂ̂) = ∞ := by
            rw [inversionGL_smul_coe, if_pos rfl]
          have hT : Filter.Tendsto (fun x : ℂ => inversionGL • (↑x : ℂ̂)) (nhds 0)
              (nhds (inversionGL • ((0 : ℂ) : ℂ̂))) := by
            rw [hv0]
            rw [(OnePoint.hasBasis_nhds_infty (X := ℂ)).tendsto_right_iff]
            rintro K ⟨-, hKc⟩
            obtain ⟨M, hM_pos, hM⟩ := hKc.isBounded.exists_pos_norm_le
            have hev : ∀ᶠ x : ℂ in nhds 0, ‖x‖ < M⁻¹ := by
              have hn := continuous_norm.tendsto (0 : ℂ)
              rw [norm_zero] at hn
              exact hn.eventually (eventually_lt_nhds (by positivity))
            filter_upwards [hev] with x hx
            by_cases hx0 : x = 0
            · refine Set.mem_union_right _ ?_
              rw [inversionGL_smul_coe, if_pos hx0]
              exact Set.mem_singleton _
            · refine Set.mem_union_left _ ?_
              rw [inversionGL_smul_coe, if_neg hx0]
              refine ⟨x⁻¹, ?_, rfl⟩
              simp only [Set.mem_compl_iff]
              intro hmem
              have h1 : ‖x⁻¹‖ ≤ M := hM _ hmem
              rw [norm_inv] at h1
              have h2 : M⁻¹ ≤ ‖x‖ := inv_le_of_inv_le₀ (norm_pos_iff.mpr hx0) h1
              linarith
          exact hT
        · have hbase : ContinuousAt (fun x : ℂ => ((x⁻¹ : ℂ) : ℂ̂)) x₀ :=
            OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hx₀)
          refine hbase.congr ?_
          filter_upwards [eventually_ne_nhds hx₀] with x hx
          rw [inversionGL_smul_coe, if_neg hx]
      exact key
  -- Step (C): factor a general element through the two special cases.
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · exact haff g hc
  · obtain ⟨a, b, c, d, hg⟩ : ∃ a b c d : ℂ,
        (g : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; c, d] :=
      ⟨_, _, _, _, Matrix.eta_fin_two _⟩
    rw [hg] at hc
    have hc' : c ≠ 0 := by simpa using hc
    have hdet := g.det_ne_zero
    rw [hg, Matrix.det_fin_two_of] at hdet
    have hbcad : b * c - a * d ≠ 0 := by
      intro h0
      apply hdet
      linear_combination -h0
    have h1det : (!![(b * c - a * d) / c, a / c; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
      exact div_ne_zero hbcad hc'
    have h2det : (!![c, d; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
      exact hc'
    obtain ⟨A1, hA1⟩ : ∃ A1 : GL (Fin 2) ℂ,
        (A1 : Matrix (Fin 2) (Fin 2) ℂ) = !![(b * c - a * d) / c, a / c; 0, 1] :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h1det, rfl⟩
    obtain ⟨A2, hA2⟩ : ∃ A2 : GL (Fin 2) ℂ,
        (A2 : Matrix (Fin 2) (Fin 2) ℂ) = !![c, d; 0, 1] :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h2det, rfl⟩
    have hmatJ : (inversionGL : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] := rfl
    have hfact : g = A1 * inversionGL * A2 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hA1, hA2, hmatJ, hg,
        Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp
      ring
    have h1lower : (A1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [hA1]; simp
    have h2lower : (A2 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [hA2]; simp
    have hcomp : Continuous (fun z : ℂ̂ => A1 • (inversionGL • (A2 • z))) :=
      (haff A1 h1lower).comp (hinvcont.comp (haff A2 h2lower))
    have heq : ∀ z : ℂ̂, A1 • (inversionGL • (A2 • z)) = g • z := by
      intro z
      rw [hfact, SemigroupAction.mul_smul, SemigroupAction.mul_smul]
    exact hcomp.congr heq

/-- **Triple transitivity**: any three distinct points of `ℂ̂` can be sent to
`(0, 1, ∞)` by a Möbius transformation. -/
theorem exists_glSMul_eq_zero_one_infty {a b c : ℂ̂}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℂ, g • a = ((0 : ℂ) : ℂ̂) ∧ g • b = ((1 : ℂ) : ℂ̂) ∧ g • c = ∞ := by
  -- Step 1: a transformation `g₁` sending `c` to `∞`.
  obtain ⟨g₁, hg₁c⟩ : ∃ g₁ : GL (Fin 2) ℂ, g₁ • c = ∞ := by
    by_cases hc : c = ∞
    · exact ⟨1, by rw [one_smul, hc]⟩
    · obtain ⟨γ, hγ⟩ := OnePoint.ne_infty_iff_exists.mp hc
      have hdet : (!![(0 : ℂ), 1; 1, -γ]).det ≠ 0 := by
        norm_num [Matrix.det_fin_two_of]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
      have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = !![(0 : ℂ), 1; 1, -γ] := rfl
      rw [← hγ, OnePoint.smul_some_eq_ite, hcoe]
      have hcond : !![(0 : ℂ), 1; 1, -γ] 1 0 * γ + !![(0 : ℂ), 1; 1, -γ] 1 1 = 0 := by
        simp
      rw [if_pos hcond]
  -- Step 2: the images of `a` and `b` under `g₁` are finite and distinct.
  have ha' : g₁ • a ≠ ∞ := fun h => hac (MulAction.injective g₁ (h.trans hg₁c.symm))
  have hb' : g₁ • b ≠ ∞ := fun h => hbc (MulAction.injective g₁ (h.trans hg₁c.symm))
  obtain ⟨α, hα⟩ := OnePoint.ne_infty_iff_exists.mp ha'
  obtain ⟨β, hβ⟩ := OnePoint.ne_infty_iff_exists.mp hb'
  have hβα : β - α ≠ 0 :=
    sub_ne_zero.mpr fun h =>
      hab (MulAction.injective g₁ (hα.symm.trans ((OnePoint.coe_eq_coe.mpr h.symm).trans hβ)))
  -- Step 3: the affine map `z ↦ (z - α) / (β - α)` as a group element `g₂`.
  have hdet₂ : (!![(1 : ℂ), -α; 0, β - α]).det ≠ 0 := by
    simpa [Matrix.det_fin_two_of] using hβα
  have hcoe₂ : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet₂ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![(1 : ℂ), -α; 0, β - α] := rfl
  set g₂ : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet₂ with hg₂
  -- Step 4: `g := g₂ * g₁` does the job.
  refine ⟨g₂ * g₁, ?_, ?_, ?_⟩
  · -- `a ↦ α ↦ 0`
    rw [SemigroupAction.mul_smul, ← hα, OnePoint.smul_some_eq_ite, hcoe₂]
    have hcond : ¬(!![(1 : ℂ), -α; 0, β - α] 1 0 * α + !![(1 : ℂ), -α; 0, β - α] 1 1 = 0) := by
      simpa using hβα
    rw [if_neg hcond, OnePoint.coe_eq_coe]
    simp
  · -- `b ↦ β ↦ 1`
    rw [SemigroupAction.mul_smul, ← hβ, OnePoint.smul_some_eq_ite, hcoe₂]
    have hcond : ¬(!![(1 : ℂ), -α; 0, β - α] 1 0 * β + !![(1 : ℂ), -α; 0, β - α] 1 1 = 0) := by
      simpa using hβα
    rw [if_neg hcond, OnePoint.coe_eq_coe]
    have : !![(1 : ℂ), -α; 0, β - α] 1 0 * β + !![(1 : ℂ), -α; 0, β - α] 1 1 = β - α := by
      simp [sub_eq_add_neg]
    rw [this]
    have : !![(1 : ℂ), -α; 0, β - α] 0 0 * β + !![(1 : ℂ), -α; 0, β - α] 0 1 = β - α := by
      simp [sub_eq_add_neg]
    rw [this, div_self hβα]
  · -- `c ↦ ∞ ↦ ∞`
    rw [SemigroupAction.mul_smul, hg₁c, OnePoint.smul_infty_eq_ite]
    have hcond : ((g₂ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 : ℂ) = 0 := by
      rw [hg₂, hcoe₂]; simp
    rw [if_pos hcond]

end RiemannDynamics

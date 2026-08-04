/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.Interpolate.Basic

/-!
# Interpolation, II: chain machinery for the development

Auxiliary lemmas for the development of the corrected tile maps: the Euclidean-disc
characterization of hyperbolic balls, chain comparison and refinement along subdivided
paths in the upper half plane, existence of chains, chain homotopy invariance, the
matrix-valued development function, the telescoping of chain values, and entrywise
convergence of chain values along converging local data.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-! ## The development of the corrected tile maps: chain machinery -/

/-! Auxiliary lemmas for the development of the corrected tile maps. -/

/-- Euclidean-disc characterization of hyperbolic balls. -/
lemma zz_ball (w : UpperHalfPlane) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    z ∈ Metric.ball ((((w : ℂ).re : ℝ) : ℂ) + ((w.im * Real.cosh r : ℝ) : ℂ) * Complex.I)
      (w.im * Real.sinh r) ↔
    ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) w < r := by
  have hwim : 0 < w.im := w.im_pos
  have hsinh : 0 < Real.sinh r := by positivity
  have hch : Real.cosh r ^ 2 - Real.sinh r ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq r
  have hcosh1 : 1 < Real.cosh r := by
    nlinarith [hsinh, Real.cosh_pos r]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ,
      c = (((w : ℂ).re : ℝ) : ℂ) + ((w.im * Real.cosh r : ℝ) : ℂ) * Complex.I := ⟨_, rfl⟩
  have hcre : c.re = (w : ℂ).re := by
    rw [hcdef]
    simp [Complex.add_re, Complex.mul_re]
  have hcim : c.im = w.im * Real.cosh r := by
    rw [hcdef]
    simp [Complex.add_im, Complex.mul_im]
  have hnormsq : ∀ u v : ℂ, dist u v ^ 2 = (u.re - v.re) ^ 2 + (u.im - v.im) ^ 2 := by
    intro u v
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  -- membership in the euclidean ball as an inequality of squares
  have hmem_iff : z ∈ Metric.ball c (w.im * Real.sinh r) ↔
      (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im * Real.cosh r) ^ 2
        < (w.im * Real.sinh r) ^ 2 := by
    rw [Metric.mem_ball]
    constructor
    · intro h
      have h2 : dist z c ^ 2 < (w.im * Real.sinh r) ^ 2 := by
        have hd0 : 0 ≤ dist z c := dist_nonneg
        nlinarith [h]
      rw [hnormsq z c, hcre, hcim] at h2
      exact h2
    · intro h
      have h2 : dist z c ^ 2 < (w.im * Real.sinh r) ^ 2 := by
        rw [hnormsq z c, hcre, hcim]
        exact h
      have hd0 : 0 ≤ dist z c := dist_nonneg
      have hrp : 0 < w.im * Real.sinh r := mul_pos hwim hsinh
      nlinarith [h2]
  rw [← hcdef, hmem_iff]
  constructor
  · intro h
    -- positivity of the imaginary part
    have him2 : (z.im - w.im * Real.cosh r) ^ 2 < (w.im * Real.sinh r) ^ 2 := by
      nlinarith [sq_nonneg (z.re - (w : ℂ).re)]
    have hzim : 0 < z.im := by
      by_contra hcon
      push Not at hcon
      have hwc : (w.im * Real.cosh r) ^ 2 - (w.im * Real.sinh r) ^ 2 = w.im ^ 2 := by
        linear_combination w.im ^ 2 * hch
      have h1 : 0 ≤ -z.im * (w.im * Real.cosh r) := by
        refine mul_nonneg (by linarith) ?_
        positivity
      nlinarith [him2, hwc, h1, sq_nonneg z.im, sq_nonneg w.im, hwim]
    refine ⟨hzim, ?_⟩
    -- convert to the cosh comparison
    have hcd := UpperHalfPlane.cosh_dist (⟨z, hzim⟩ : UpperHalfPlane) w
    have him_eq : ((⟨z, hzim⟩ : UpperHalfPlane) : ℂ) = z := rfl
    have himz : (⟨z, hzim⟩ : UpperHalfPlane).im = z.im := rfl
    rw [him_eq, himz] at hcd
    have hdd : dist (z : ℂ) (w : ℂ) ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [hnormsq]
      simp [UpperHalfPlane.coe_im]
    have hden : 0 < 2 * z.im * w.im := by positivity
    have hkey : Real.cosh (dist (⟨z, hzim⟩ : UpperHalfPlane) w) < Real.cosh r := by
      rw [hcd, hdd]
      have hlt : (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2
          < (Real.cosh r - 1) * (2 * z.im * w.im) := by
        nlinarith [h, hch, sq_nonneg w.im]
      have h2 := (div_lt_iff₀ hden).mpr hlt
      linarith
    have h3 := Real.cosh_lt_cosh.mp hkey
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg hr.le] at h3
  · rintro ⟨hz, h⟩
    have hcd := UpperHalfPlane.cosh_dist (⟨z, hz⟩ : UpperHalfPlane) w
    have him_eq : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
    have himz : (⟨z, hz⟩ : UpperHalfPlane).im = z.im := rfl
    rw [him_eq, himz] at hcd
    have hkey : Real.cosh (dist (⟨z, hz⟩ : UpperHalfPlane) w) < Real.cosh r :=
      Real.cosh_lt_cosh.mpr (by rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg hr.le])
    rw [hcd] at hkey
    have hdd : dist (z : ℂ) (w : ℂ) ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [hnormsq]
      simp [UpperHalfPlane.coe_im]
    rw [hdd] at hkey
    have hden : 0 < 2 * z.im * w.im := by positivity
    have hkey2 : (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2
        < (Real.cosh r - 1) * (2 * z.im * w.im) := by
      have h2 : ((z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2) / (2 * z.im * w.im)
          < Real.cosh r - 1 := by linarith
      exact (div_lt_iff₀ hden).mp h2
    nlinarith [hkey2, hch, sq_nonneg w.im]

/-- Packing finiteness for a Fuchsian group. -/
lemma zz_fin {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) (τ τ₀ : UpperHalfPlane) (r : ℝ) :
    {γ : ↥Γ | dist τ (γ • τ₀) ≤ r}.Finite := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall τ r).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  refine hfin1.subset ?_
  intro γ hγ
  refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  exact hγ

/-- General composition law for matrix Möbius maps, with denominator hypotheses. -/
lemma zz_matmul (M N : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (hN : (N 1 0 : ℂ) * z + (N 1 1 : ℂ) ≠ 0)
    (_hMN : ((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ) ≠ 0) :
    matMoebius (M * N) z = matMoebius M (matMoebius N z) := by
  have hnum : ∀ i : Fin 2, ((M * N) i 0 : ℂ) * z + ((M * N) i 1 : ℂ)
      = (M i 0 : ℂ) * ((N 0 0 : ℂ) * z + (N 0 1 : ℂ))
        + (M i 1 : ℂ) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ)) := by
    intro i
    have h0 : (M * N) i 0 = M i 0 * N 0 0 + M i 1 * N 1 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : (M * N) i 1 = M i 0 * N 0 1 + M i 1 * N 1 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h0, h1]
    push_cast
    ring
  have hu : matMoebius N z * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = (N 0 0 : ℂ) * z + (N 0 1 : ℂ) := by
    rw [matMoebius, div_mul_cancel₀ _ hN]
  have hd : ((M 1 0 : ℂ) * matMoebius N z + (M 1 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = ((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ) := by
    rw [hnum 1, add_mul, mul_assoc, hu]
  have hn : ((M 0 0 : ℂ) * matMoebius N z + (M 0 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = ((M * N) 0 0 : ℂ) * z + ((M * N) 0 1 : ℂ) := by
    rw [hnum 0, add_mul, mul_assoc, hu]
  calc matMoebius (M * N) z
      = (((M * N) 0 0 : ℂ) * z + ((M * N) 0 1 : ℂ))
        / (((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ)) := rfl
    _ = (((M 0 0 : ℂ) * matMoebius N z + (M 0 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ)))
        / (((M 1 0 : ℂ) * matMoebius N z + (M 1 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))) := by
        rw [hn, hd]
    _ = matMoebius M (matMoebius N z) := by
        rw [mul_div_mul_right _ _ hN]
        rfl

/-- The cosh-distance formula as a plane expression. -/
lemma zz_cd_bridge (τ w : UpperHalfPlane) :
    1 + Complex.normSq ((τ : ℂ) - (w : ℂ)) / (2 * (τ : ℂ).im * (w : ℂ).im)
      = Real.cosh (dist τ w) := by
  have h := UpperHalfPlane.cosh_dist τ w
  have hd : dist (τ : ℂ) (w : ℂ) ^ 2 = Complex.normSq ((τ : ℂ) - (w : ℂ)) := by
    rw [dist_eq_norm, Complex.sq_norm]
  rw [h, hd, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]

/-- Differentiability of the cosh-distance expression on the upper half plane. -/
lemma zz_cd_contDiffAt (w : ℂ) (hw : 0 < w.im) (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    ContDiffAt ℝ 1 (fun z => 1 + Complex.normSq (z - w) / (2 * z.im * w.im)) z₀ := by
  have hre : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ 1 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hns : (fun z : ℂ => Complex.normSq (z - w))
      = fun z : ℂ => (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    funext z
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hnum : ContDiffAt ℝ 1 (fun z : ℂ => Complex.normSq (z - w)) z₀ := by
    rw [hns]
    exact (((hre.sub contDiff_const).pow 2).add
      ((him.sub contDiff_const).pow 2)).contDiffAt
  have hden : ContDiffAt ℝ 1 (fun z : ℂ => 2 * z.im * w.im) z₀ :=
    ((contDiff_const.mul him).mul contDiff_const).contDiffAt
  have hden0 : 2 * z₀.im * w.im ≠ 0 := by positivity
  exact (contDiffAt_const.add (hnum.div hden hden0))

/-- The elementary triple move for chain values. -/
private lemma zz_step {G : Type} [Group G] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b))
    (a b c : ↥Γ) (w : ℂ) (hwa : w ∈ V a) (hwb : w ∈ V b) (hwc : w ∈ V c) :
    f (a⁻¹ * b) * f (b⁻¹ * c) = f (a⁻¹ * c) := by
  have h1 : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V 1 := by
    have h := hVtrans a⁻¹ a w hwa
    rwa [inv_mul_cancel] at h
  have h2 : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V (a⁻¹ * b) := hVtrans a⁻¹ b w hwb
  have h3 : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V (a⁻¹ * c) := hVtrans a⁻¹ c w hwc
  have hmul : (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c := by group
  have h3' : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V ((a⁻¹ * b) * (b⁻¹ * c)) := by
    rwa [hmul]
  rw [htrip (a⁻¹ * b) (b⁻¹ * c) ⟨moebiusMap (↑(a⁻¹ : ↥Γ)) w, ⟨h1, h2⟩, h3'⟩, hmul]

/-- **Same-grid chain comparison**: two chains subordinate to the same path on the same
uniform grid have the same value. Induction on the grid size along a reparametrized path. -/
private lemma zz_compare {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b)) :
    ∀ (N : ℕ), 0 < N → ∀ (α : ℝ → ℂ) (γt : ↥Γ) (g g' : ℕ → ↥Γ),
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k)) →
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g' k)) →
      α 0 ∈ V 1 → α 1 ∈ V γt →
      f (g' 0) * ((List.range (N - 1)).map fun k => f ((g' k)⁻¹ * g' (k + 1))).prod
          * f ((g' (N - 1))⁻¹ * γt)
        = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
          * f ((g (N - 1))⁻¹ * γt) := by
  have hstep := zz_step V f hVtrans htrip
  intro N
  induction N with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ N ih =>
    intro _ α γt g g' hs hs' hb ht
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- base case: a single slot
      subst hN0
      simp only [List.range_zero, List.map_nil, List.prod_nil, mul_one, Nat.sub_self]
      have h00 : α 0 ∈ V (g 0) := by
        refine hs 0 (by norm_num) 0 (by norm_num) ?_
        norm_num
      have h00' : α 0 ∈ V (g' 0) := by
        refine hs' 0 (by norm_num) 0 (by norm_num) ?_
        norm_num
      have h10 : α 1 ∈ V (g 0) := by
        refine hs 0 (by norm_num) 1 (by norm_num) ?_
        norm_num
      have h10' : α 1 ∈ V (g' 0) := by
        refine hs' 0 (by norm_num) 1 (by norm_num) ?_
        norm_num
      -- head move at α 0 and junction move at α 1
      have hA : f ((g' 0)⁻¹ * g 0) * f ((g 0)⁻¹ * γt) = f ((g' 0)⁻¹ * γt) :=
        hstep (g' 0) (g 0) γt (α 1) h10' h10 ht
      have hB : f ((1 : ↥Γ)⁻¹ * g' 0) * f ((g' 0)⁻¹ * g 0) = f ((1 : ↥Γ)⁻¹ * g 0) :=
        hstep 1 (g' 0) (g 0) (α 0) hb h00' h00
      rw [inv_one, one_mul, one_mul] at hB
      calc f (g' 0) * f ((g' 0)⁻¹ * γt)
          = f (g' 0) * (f ((g' 0)⁻¹ * g 0) * f ((g 0)⁻¹ * γt)) := by rw [hA]
        _ = (f (g' 0) * f ((g' 0)⁻¹ * g 0)) * f ((g 0)⁻¹ * γt) := by rw [mul_assoc]
        _ = f (g 0) * f ((g 0)⁻¹ * γt) := by rw [hB]
    · -- inductive step: peel the last slot
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have hM2r : (0 : ℝ) < (M : ℝ) + 2 := by positivity
      have hM1r : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      obtain ⟨β, hβdef⟩ : ∃ β : ℝ → ℂ,
          β = fun t => α (t * ((M : ℝ) + 1) / ((M : ℝ) + 2)) := ⟨_, rfl⟩
      have hβval : ∀ t : ℝ, β t = α (t * ((M : ℝ) + 1) / ((M : ℝ) + 2)) := by
        intro t
        rw [hβdef]
      have hcast2 : ((M + 1 + 1 : ℕ) : ℝ) = (M : ℝ) + 2 := by push_cast; ring
      have hcast1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      -- grid transfer for the reparametrized path
      have htransfer : ∀ (h : ℕ → ↥Γ),
          (∀ k < M + 1 + 1, ∀ t : ℝ, (k : ℝ) / (M + 1 + 1 : ℕ) ≤ t →
            t ≤ ((k : ℝ) + 1) / (M + 1 + 1 : ℕ) → α t ∈ V (h k)) →
          ∀ k < M + 1, ∀ t : ℝ, (k : ℝ) / (M + 1 : ℕ) ≤ t →
            t ≤ ((k : ℝ) + 1) / (M + 1 : ℕ) → β t ∈ V (h k) := by
        intro h hsub k hk t ht1 ht2
        rw [hβval]
        rw [hcast1] at ht1 ht2
        refine hsub k (by omega) (t * ((M : ℝ) + 1) / ((M : ℝ) + 2)) ?_ ?_
        · rw [hcast2, div_le_div_iff_of_pos_right hM2r]
          rw [div_le_iff₀ hM1r] at ht1
          linarith
        · rw [hcast2, div_le_div_iff_of_pos_right hM2r]
          rw [le_div_iff₀ hM1r] at ht2
          linarith
      -- junction memberships at the peeling point
      have hqN : α (((M : ℝ) + 1) / ((M : ℝ) + 2)) ∈ V (g (M + 1)) := by
        refine hs (M + 1) (by omega) _ ?_ ?_
        · rw [hcast2, hcast1]
        · rw [hcast2, hcast1]
          rw [div_le_div_iff_of_pos_right hM2r]
          linarith
      have hq'N : α (((M : ℝ) + 1) / ((M : ℝ) + 2)) ∈ V (g' (M + 1)) := by
        refine hs' (M + 1) (by omega) _ ?_ ?_
        · rw [hcast2, hcast1]
        · rw [hcast2, hcast1]
          rw [div_le_div_iff_of_pos_right hM2r]
          linarith
      have hq'M : α (((M : ℝ) + 1) / ((M : ℝ) + 2)) ∈ V (g' M) := by
        refine hs' M (by omega) _ ?_ ?_
        · rw [hcast2]
          rw [div_le_div_iff_of_pos_right hM2r]
          linarith
        · rw [hcast2]
      -- endpoint memberships
      have heN : α 1 ∈ V (g (M + 1)) := by
        refine hs (M + 1) (by omega) 1 ?_ ?_
        · rw [hcast2, hcast1, div_le_one hM2r]
          linarith
        · rw [hcast2, hcast1, le_div_iff₀ hM2r]
          linarith
      have he'N : α 1 ∈ V (g' (M + 1)) := by
        refine hs' (M + 1) (by omega) 1 ?_ ?_
        · rw [hcast2, hcast1, div_le_one hM2r]
          linarith
        · rw [hcast2, hcast1, le_div_iff₀ hM2r]
          linarith
      -- endpoint conditions for the reparametrized path
      have hbβ : β 0 ∈ V 1 := by
        rw [hβval]
        rw [show (0 : ℝ) * ((M : ℝ) + 1) / ((M : ℝ) + 2) = 0 by rw [zero_mul, zero_div]]
        exact hb
      have htβ : β 1 ∈ V (g (M + 1)) := by
        rw [hβval]
        rw [show (1 : ℝ) * ((M : ℝ) + 1) / ((M : ℝ) + 2)
          = ((M : ℝ) + 1) / ((M : ℝ) + 2) by rw [one_mul]]
        exact hqN
      -- the two junction moves
      have hA : f ((g' (M + 1))⁻¹ * g (M + 1)) * f ((g (M + 1))⁻¹ * γt)
          = f ((g' (M + 1))⁻¹ * γt) :=
        hstep (g' (M + 1)) (g (M + 1)) γt (α 1) he'N heN ht
      have hB : f ((g' M)⁻¹ * g' (M + 1)) * f ((g' (M + 1))⁻¹ * g (M + 1))
          = f ((g' M)⁻¹ * g (M + 1)) :=
        hstep (g' M) (g' (M + 1)) (g (M + 1)) (α (((M : ℝ) + 1) / ((M : ℝ) + 2)))
          hq'M hq'N hqN
      -- the induction hypothesis for the peeled path
      have hIH := ih (by omega) β (g (M + 1)) g g' (htransfer g hs) (htransfer g' hs')
        hbβ htβ
      -- reassemble: split off the last factor of the products
      simp only [Nat.add_sub_cancel] at hIH ⊢
      rw [List.range_succ]
      simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
      rw [← hA]
      simp only [← mul_assoc]
      rw [mul_assoc _ (f ((g' M)⁻¹ * g' (M + 1))) (f ((g' (M + 1))⁻¹ * g (M + 1))), hB, hIH]

/-- **Refinement invariance of chain values**: refining every slot `m + 1`-fold does not
change the value. Pure algebra, by induction on the number of coarse slots. -/
private lemma zz_refine_val {G H : Type} [Group G] [Group H] (f : H → G) (hf1 : f 1 = 1)
    (mm : ℕ) :
    ∀ (A : ℕ) (g : ℕ → H) (γt : H),
      f (g 0) * ((List.range (A * (mm + 1) + mm)).map
          fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod
        * f ((g ((A * (mm + 1) + mm) / (mm + 1)))⁻¹ * γt)
      = f (g 0) * ((List.range A).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
        * f ((g A)⁻¹ * γt) := by
  have hdivA : ∀ A : ℕ, (A * (mm + 1) + mm) / (mm + 1) = A := by
    intro A
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have hdivlow : ∀ A j : ℕ, j ≤ mm → (A * (mm + 1) + j) / (mm + 1) = A := by
    intro A j hj
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  intro A
  induction A with
  | zero =>
    intro g γt
    have hprod : ((List.range mm).map
        fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod = 1 := by
      refine List.prod_eq_one ?_
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hk' : k < mm := List.mem_range.mp hk
      have h1 : k / (mm + 1) = 0 := Nat.div_eq_of_lt (by omega)
      have h2 : (k + 1) / (mm + 1) = 0 := Nat.div_eq_of_lt (by omega)
      rw [h1, h2, inv_mul_cancel, hf1]
    have hmm0 : mm / (mm + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp only [Nat.zero_mul, Nat.zero_add, hmm0, hprod, List.range_zero, List.map_nil,
      List.prod_nil]
  | succ A ih =>
    intro g γt
    have harg : (A + 1) * (mm + 1) + mm = (A * (mm + 1) + mm) + (mm + 1) := by ring
    rw [harg, List.range_add, List.map_append, List.prod_append]
    -- the new block of factors
    have hr1 : List.range (mm + 1) = [0] ++ List.map (fun x => 1 + x) (List.range mm) := by
      rw [← List.range_one, ← List.range_add, Nat.add_comm mm 1]
    have hblock : (((List.range (mm + 1)).map fun x => A * (mm + 1) + mm + x).map
        fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod
        = f ((g A)⁻¹ * g (A + 1)) := by
      rw [hr1, List.map_append, List.map_append, List.prod_append]
      have hsingle : ((([0] : List ℕ).map fun x => A * (mm + 1) + mm + x).map
          fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod
          = f ((g A)⁻¹ * g (A + 1)) := by
        simp only [List.map_singleton, List.prod_singleton, Nat.add_zero]
        rw [hdivA A]
        rw [show A * (mm + 1) + mm + 1 = (A + 1) * (mm + 1) from by ring,
          Nat.mul_div_cancel _ (by omega : 0 < mm + 1)]
      have hrest : ((((List.range mm).map fun x => 1 + x).map
          fun x => A * (mm + 1) + mm + x).map
          fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod = 1 := by
        refine List.prod_eq_one ?_
        intro y hy
        obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp hy
        obtain ⟨k2, hk2, rfl⟩ := List.mem_map.mp hk1
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk2
        have hx' : x < mm := List.mem_range.mp hx
        have ha : A * (mm + 1) + mm + (1 + x) = (A + 1) * (mm + 1) + x := by ring
        rw [ha, hdivlow (A + 1) x (by omega),
          show (A + 1) * (mm + 1) + x + 1 = (A + 1) * (mm + 1) + (x + 1) from by ring,
          hdivlow (A + 1) (x + 1) (by omega), inv_mul_cancel, hf1]
      rw [hsingle, hrest, mul_one]
    have htail : ((A * (mm + 1) + mm) + (mm + 1)) / (mm + 1) = A + 1 := by
      rw [show (A * (mm + 1) + mm) + (mm + 1) = (A + 1) * (mm + 1) + mm from by ring]
      exact hdivA (A + 1)
    rw [hblock, htail]
    -- reassemble with the induction hypothesis at target `g (A + 1)`
    have hIH := ih g (g (A + 1))
    rw [hdivA A] at hIH
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    simp only [← mul_assoc]
    rw [hIH]

/-- **Refinement transfer of subordination**: a chain subordinate on the coarse grid is
subordinate on the refined grid through slot division. -/
private lemma zz_refine_sub {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (α : ℝ → ℂ) (g : ℕ → ↥Γ)
    (hs : ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k)) :
    ∀ k < N * m, ∀ t : ℝ, (k : ℝ) / (N * m : ℕ) ≤ t → t ≤ ((k : ℝ) + 1) / (N * m : ℕ) →
      α t ∈ V (g (k / m)) := by
  intro k hk t ht1 ht2
  have hq : k / m < N := Nat.div_lt_iff_lt_mul hm |>.mpr hk
  obtain ⟨q, hq_def⟩ : ∃ q, q = k / m := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r, r = k % m := ⟨_, rfl⟩
  have hkqr : k = m * q + r := by
    rw [hq_def, hr_def]
    exact (Nat.div_add_mod k m).symm
  have hrm : r < m := by
    rw [hr_def]
    exact Nat.mod_lt _ hm
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNmr : (0 : ℝ) < ((N * m : ℕ) : ℝ) := by
    push_cast
    positivity
  rw [← hq_def]
  refine hs q (by rw [hq_def]; exact hq) t ?_ ?_
  · -- (q : ℝ) / N ≤ t
    refine le_trans ?_ ht1
    rw [div_le_div_iff₀ hNr hNmr]
    have h1 : (q : ℝ) * m ≤ (k : ℝ) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) hkqr
      push_cast at hc
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      nlinarith [hc, hr0]
    have h2 := mul_le_mul_of_nonneg_right h1 hNr.le
    push_cast
    nlinarith [h2]
  · -- t ≤ ((q : ℝ) + 1) / N
    refine le_trans ht2 ?_
    rw [div_le_div_iff₀ hNmr hNr]
    have hk1 : k + 1 ≤ m * (q + 1) := by
      have hmq : m * (q + 1) = m * q + m := by ring
      omega
    have h1 : (k : ℝ) + 1 ≤ (m : ℝ) * ((q : ℝ) + 1) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.le.dest hk1).choose_spec
      exact_mod_cast Nat.cast_le.mpr hk1
    have h2 := mul_le_mul_of_nonneg_right h1 hNr.le
    push_cast
    nlinarith [h2]

/-- **Cross-grid chain comparison**: chains along the same path on different uniform grids
have the same value, via refinement to a common grid. -/
private lemma zz_anychain {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b))
    (hf1 : f 1 = 1) :
    ∀ (N N' : ℕ), 0 < N → 0 < N' → ∀ (α : ℝ → ℂ) (γt : ↥Γ) (g h : ℕ → ↥Γ),
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k)) →
      (∀ k < N', ∀ t : ℝ, (k : ℝ) / N' ≤ t → t ≤ ((k : ℝ) + 1) / N' → α t ∈ V (h k)) →
      α 0 ∈ V 1 → α 1 ∈ V γt →
      f (h 0) * ((List.range (N' - 1)).map fun k => f ((h k)⁻¹ * h (k + 1))).prod
          * f ((h (N' - 1))⁻¹ * γt)
        = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
          * f ((g (N - 1))⁻¹ * γt) := by
  intro N N' hN hN' α γt g h hsg hsh hb ht
  obtain ⟨nn, rfl⟩ : ∃ nn, N = nn + 1 := ⟨N - 1, by omega⟩
  obtain ⟨mm, rfl⟩ : ∃ mm, N' = mm + 1 := ⟨N' - 1, by omega⟩
  -- refine both chains to the common grid (nn + 1) * (mm + 1)
  have hsub_g' := zz_refine_sub V (nn + 1) (mm + 1) (by omega) (by omega) α g hsg
  have hsub_h' := zz_refine_sub V (mm + 1) (nn + 1) (by omega) (by omega) α h hsh
  rw [Nat.mul_comm (mm + 1) (nn + 1)] at hsub_h'
  have hcmp := zz_compare V f hVtrans htrip ((nn + 1) * (mm + 1)) (by positivity) α γt
    (fun k => g (k / (mm + 1))) (fun k => h (k / (nn + 1))) hsub_g' hsub_h' hb ht
  have hval_g := zz_refine_val f hf1 mm nn g γt
  have hval_h := zz_refine_val f hf1 nn mm h γt
  -- align the grid arithmetic
  have hP1 : (nn + 1) * (mm + 1) - 1 = nn * (mm + 1) + mm := by
    have hx : (nn + 1) * (mm + 1) = nn * (mm + 1) + mm + 1 := by ring
    omega
  have hP2 : mm * (nn + 1) + nn = nn * (mm + 1) + mm := by ring
  rw [hP1] at hcmp
  rw [hP2] at hval_h
  have hdivg : (nn * (mm + 1) + mm) / (mm + 1) = nn := by
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have hdivh : (nn * (mm + 1) + mm) / (nn + 1) = mm := by
    rw [← hP2]
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  rw [hdivg] at hval_g
  rw [hdivh] at hval_h
  simp only [] at hcmp
  simp only [Nat.zero_div] at hcmp
  rw [hdivg, hdivh] at hcmp
  simp only [Nat.add_sub_cancel]
  rw [← hval_g, ← hval_h]
  exact hcmp

/-- Every parameter in `[0, 1]` lies in some slot of the uniform grid. -/
private lemma zz_findpiece (N : ℕ) (hN : 0 < N) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ k < N, (k : ℝ) / N ≤ s ∧ s ≤ ((k : ℝ) + 1) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hfl : ⌊s * N⌋₊ < N
  · refine ⟨⌊s * N⌋₊, hfl, ?_, ?_⟩
    · rw [div_le_iff₀ hNr]
      exact Nat.floor_le (by positivity)
    · rw [le_div_iff₀ hNr]
      have := Nat.lt_floor_add_one (s * N)
      linarith
  · push Not at hfl
    have hsN : (N : ℝ) ≤ s * N := by
      have h := Nat.le_floor_iff (α := ℝ) (by positivity : (0 : ℝ) ≤ s * N) |>.mp hfl
      exact h
    have hs1' : s = 1 := by
      have h2 : s * N ≤ N := by nlinarith
      have h3 : s * N = N := le_antisymm h2 hsN
      have := mul_right_cancel₀ hNr.ne' (by rw [h3, one_mul] : s * (N : ℝ) = 1 * N)
      exact this
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ N := hN
      push_cast [Nat.cast_sub h1]
      ring
    refine ⟨N - 1, by omega, ?_, ?_⟩
    · rw [hcast, hs1', div_le_one hNr]
      linarith
    · rw [hcast, hs1', le_div_iff₀ hNr]
      linarith

/-- **Chain existence** along a continuous path through an open cover by translates. -/
lemma zz_chain_exists {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (hVopen : ∀ γ, IsOpen (V γ)) (α : ℝ → ℂ) (hαc : Continuous α)
    (hcov : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ γ, α t ∈ V γ) :
    ∃ (N : ℕ) (g : ℕ → ↥Γ), 0 < N ∧
      ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k) := by
  have hopen : ∀ γ : ↥Γ, IsOpen (α ⁻¹' (V γ)) := fun γ => (hVopen γ).preimage hαc
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ ⋃ γ : ↥Γ, α ⁻¹' (V γ) := by
    intro t ht
    obtain ⟨γ, hγ⟩ := hcov t ht.1 ht.2
    exact Set.mem_iUnion.mpr ⟨γ, hγ⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen hsub
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < N := by
    have h0 : (0 : ℝ) < 1 / δ := by positivity
    have : (0 : ℝ) < N := lt_trans h0 hN
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1N : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hδpos] at hN
    nlinarith
  have hpick : ∀ k : ℕ, ∃ γ : ↥Γ, k < N → Metric.ball ((k : ℝ) / N) δ ⊆ α ⁻¹' (V γ) := by
    intro k
    by_cases hk : k < N
    · have hmem : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · rw [div_le_one hNr]
          exact_mod_cast hk.le
      obtain ⟨γ, hγ⟩ := hδ ((k : ℝ) / N) hmem
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose g hg using hpick
  refine ⟨N, g, hNpos, ?_⟩
  intro k hk t ht1 ht2
  refine hg k hk ?_
  rw [Metric.mem_ball, Real.dist_eq]
  have hsplit : ((k : ℝ) + 1) / N = (k : ℝ) / N + 1 / N := by ring
  rw [abs_of_nonneg (by linarith)]
  rw [hsplit] at ht2
  linarith

/-- **Homotopy invariance of chain values** for paths with the same endpoints, via the
straight-line homotopy and a Lebesgue grid of squares. -/
private lemma zz_homotopy {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVsub : ∀ γ, V γ ⊆ {z : ℂ | 0 < z.im})
    (hVopen : ∀ γ, IsOpen (V γ))
    (hVcov : ∀ z : ℂ, 0 < z.im → ∃ γ, z ∈ V γ)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b))
    (hf1 : f 1 = 1)
    (α β : ℝ → ℂ) (hαc : Continuous α) (hβc : Continuous β)
    (h0 : α 0 = β 0) (h1 : α 1 = β 1)
    (γt : ↥Γ) (N N' : ℕ) (g h : ℕ → ↥Γ) (hN : 0 < N) (hN' : 0 < N')
    (hsg : ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k))
    (hsh : ∀ k < N', ∀ t : ℝ, (k : ℝ) / N' ≤ t → t ≤ ((k : ℝ) + 1) / N' → β t ∈ V (h k))
    (hb : α 0 ∈ V 1) (ht : α 1 ∈ V γt) :
    f (h 0) * ((List.range (N' - 1)).map fun k => f ((h k)⁻¹ * h (k + 1))).prod
        * f ((h (N' - 1))⁻¹ * γt)
      = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
        * f ((g (N - 1))⁻¹ * γt) := by
  -- imaginary-part positivity along both paths
  have himα : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < (α s).im := by
    intro s hs0 hs1
    obtain ⟨k, hk, hk1, hk2⟩ := zz_findpiece N hN s hs0 hs1
    exact hVsub (g k) (hsg k hk s hk1 hk2)
  have himβ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < (β s).im := by
    intro s hs0 hs1
    obtain ⟨k, hk, hk1, hk2⟩ := zz_findpiece N' hN' s hs0 hs1
    exact hVsub (h k) (hsh k hk s hk1 hk2)
  -- the straight-line homotopy
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × ℝ → ℂ,
      H = fun p => ((1 - p.2 : ℝ) : ℂ) * α p.1 + ((p.2 : ℝ) : ℂ) * β p.1 := ⟨_, rfl⟩
  have hHval : ∀ s t : ℝ, H (s, t) = ((1 - t : ℝ) : ℂ) * α s + ((t : ℝ) : ℂ) * β s := by
    intro s t
    rw [hHdef]
  have hHc : Continuous H := by
    rw [hHdef]
    refine Continuous.add ?_ ?_
    · exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd)).mul
        (hαc.comp continuous_fst)
    · exact (Complex.continuous_ofReal.comp continuous_snd).mul (hβc.comp continuous_fst)
  have hHim : ∀ p : ℝ × ℝ, p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 → 0 < (H p).im := by
    rintro ⟨s, t⟩ ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩
    rw [hHval]
    have h1 := himα s hs0 hs1
    have h2 := himβ s hs0 hs1
    have him : (((1 - t : ℝ) : ℂ) * α s + ((t : ℝ) : ℂ) * β s).im
        = (1 - t) * (α s).im + t * (β s).im := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him]
    rcases le_or_gt t (1 / 2) with hc | hc
    · nlinarith
    · nlinarith
  -- Lebesgue number for the square
  have hopen : ∀ γ : ↥Γ, IsOpen (H ⁻¹' (V γ)) := fun γ => (hVopen γ).preimage hHc
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ γ : ↥Γ, H ⁻¹' (V γ) := by
    intro p hp
    obtain ⟨γ, hγ⟩ := hVcov (H p) (hHim p hp)
    exact Set.mem_iUnion.mpr ⟨γ, hγ⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc.prod isCompact_Icc) hopen hsub
  obtain ⟨P, hP⟩ := exists_nat_gt (1 / δ)
  have hPpos : 0 < P := by
    have h0' : (0 : ℝ) < 1 / δ := by positivity
    have : (0 : ℝ) < P := lt_trans h0' hP
    exact_mod_cast this
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have h1P : 1 / (P : ℝ) < δ := by
    rw [div_lt_iff₀ hPr]
    rw [div_lt_iff₀ hδpos] at hP
    nlinarith
  -- square choices
  have hpick : ∀ ij : ℕ × ℕ, ∃ γ : ↥Γ, ij.1 < P → ij.2 < P →
      Metric.ball (((ij.1 : ℝ) / P, (ij.2 : ℝ) / P) : ℝ × ℝ) δ ⊆ H ⁻¹' (V γ) := by
    rintro ⟨i, j⟩
    by_cases hij : i < P ∧ j < P
    · have hmem : (((i : ℝ) / P, (j : ℝ) / P) : ℝ × ℝ)
          ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
        constructor
        · constructor
          · positivity
          · rw [div_le_one hPr]
            exact_mod_cast hij.1.le
        · constructor
          · positivity
          · rw [div_le_one hPr]
            exact_mod_cast hij.2.le
      obtain ⟨γ, hγ⟩ := hδ _ hmem
      exact ⟨γ, fun _ _ => hγ⟩
    · exact ⟨1, fun hi hj => absurd ⟨hi, hj⟩ hij⟩
  choose w hw using hpick
  -- the two subordination properties of a square row
  have hrow1 : ∀ j : ℕ, j < P → ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      H (s, (j : ℝ) / P) ∈ V (w (i, j)) := by
    intro j hj i hi s hs1 hs2
    refine hw (i, j) hi hj ?_
    rw [Metric.mem_ball]
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    have hsplit : ((i : ℝ) + 1) / P = (i : ℝ) / P + 1 / P := by ring
    rw [hsplit] at hs2
    have habs1 : |s - (i : ℝ) / P| < δ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have habs2 : |(j : ℝ) / P - (j : ℝ) / P| < δ := by
      rw [sub_self, abs_zero]
      exact hδpos
    exact max_lt habs1 habs2
  have hrow2 : ∀ j : ℕ, j < P → ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      H (s, ((j : ℝ) + 1) / P) ∈ V (w (i, j)) := by
    intro j hj i hi s hs1 hs2
    refine hw (i, j) hi hj ?_
    rw [Metric.mem_ball]
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    have hsplit : ((i : ℝ) + 1) / P = (i : ℝ) / P + 1 / P := by ring
    rw [hsplit] at hs2
    have habs1 : |s - (i : ℝ) / P| < δ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have habs2 : |((j : ℝ) + 1) / P - (j : ℝ) / P| < δ := by
      rw [show ((j : ℝ) + 1) / P - (j : ℝ) / P = 1 / P by ring]
      rw [abs_of_nonneg (by positivity)]
      exact h1P
    exact max_lt habs1 habs2
  -- row endpoints
  have hrowa : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → H (0, t) = α 0 := by
    intro t _ _
    rw [hHval, h0]
    push_cast
    ring
  have hrowb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → H (1, t) = α 1 := by
    intro t _ _
    rw [hHval, h1]
    push_cast
    ring
  have htbound : ∀ j : ℕ, j < P → 0 ≤ (j : ℝ) / P ∧ (j : ℝ) / P ≤ 1 := by
    intro j hj
    constructor
    · positivity
    · rw [div_le_one hPr]
      exact_mod_cast hj.le
  have htbound1 : ∀ j : ℕ, j < P → 0 ≤ ((j : ℝ) + 1) / P ∧ ((j : ℝ) + 1) / P ≤ 1 := by
    intro j hj
    constructor
    · positivity
    · rw [div_le_one hPr]
      have : (j : ℝ) + 1 ≤ P := by exact_mod_cast hj
      linarith
  -- the row-invariance induction
  have hind : ∀ j : ℕ, j < P →
      f (w (0, j)) * ((List.range (P - 1)).map
          fun k => f ((w (k, j))⁻¹ * w (k + 1, j))).prod * f ((w (P - 1, j))⁻¹ * γt)
      = f (w (0, 0)) * ((List.range (P - 1)).map
          fun k => f ((w (k, 0))⁻¹ * w (k + 1, 0))).prod * f ((w (P - 1, 0))⁻¹ * γt) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ihj =>
      intro hj1
      have hj : j < P := by omega
      -- both row chains are subordinate to the row path at height (j + 1) / P
      have hpath0 : H (0, ((j : ℝ) + 1) / P) ∈ V 1 := by
        rw [hrowa _ (htbound1 j hj).1 (htbound1 j hj).2]
        exact hb
      have hpath1 : H (1, ((j : ℝ) + 1) / P) ∈ V γt := by
        rw [hrowb _ (htbound1 j hj).1 (htbound1 j hj).2]
        exact ht
      have hsubj : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
          (fun s => H (s, ((j : ℝ) + 1) / P)) s ∈ V ((fun i => w (i, j)) i) :=
        fun i hi s hs1 hs2 => hrow2 j hj i hi s hs1 hs2
      have hsubj1 : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
          (fun s => H (s, ((j : ℝ) + 1) / P)) s ∈ V ((fun i => w (i, j + 1)) i) := by
        intro i hi s hs1 hs2
        have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        have := hrow1 (j + 1) hj1 i hi s hs1 hs2
        rwa [hcast] at this
      have hcmp := zz_compare V f hVtrans htrip P hPpos
        (fun s => H (s, ((j : ℝ) + 1) / P)) γt
        (fun i => w (i, j)) (fun i => w (i, j + 1)) hsubj hsubj1 hpath0 hpath1
      simp only [] at hcmp
      rw [hcmp]
      exact ihj hj
  -- compare the given chains with the extreme rows
  have hrow0α : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      α s ∈ V ((fun i => w (i, 0)) i) := by
    intro i hi s hs1 hs2
    have := hrow1 0 hPpos i hi s hs1 hs2
    have hz : ((0 : ℕ) : ℝ) / P = 0 := by
      rw [Nat.cast_zero, zero_div]
    rw [hz] at this
    have hHα : H (s, 0) = α s := by
      rw [hHval]
      push_cast
      ring
    rwa [hHα] at this
  have hrowPβ : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      β s ∈ V ((fun i => w (i, P - 1)) i) := by
    intro i hi s hs1 hs2
    have hlt : P - 1 < P := by omega
    have := hrow2 (P - 1) hlt i hi s hs1 hs2
    have hcast : ((P - 1 : ℕ) : ℝ) + 1 = (P : ℝ) := by
      have h1' : (1 : ℕ) ≤ P := hPpos
      push_cast [Nat.cast_sub h1']
      ring
    rw [hcast, div_self hPr.ne'] at this
    have hHβ : H (s, 1) = β s := by
      rw [hHval]
      push_cast
      ring
    rwa [hHβ] at this
  have hbβ : β 0 ∈ V 1 := by
    rw [← h0]
    exact hb
  have htβ : β 1 ∈ V γt := by
    rw [← h1]
    exact ht
  have hα0 := zz_anychain V f hVtrans htrip hf1 N P hN hPpos α γt g
    (fun i => w (i, 0)) hsg hrow0α hb ht
  have hβP := zz_anychain V f hVtrans htrip hf1 N' P hN' hPpos β γt h
    (fun i => w (i, P - 1)) hsh hrowPβ hbβ htβ
  simp only [] at hα0 hβP
  rw [← hα0, ← hβP]
  have hfin := hind (P - 1) (by omega)
  simp only [] at hfin
  rw [hfin]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The monodromy extension develops chain values along paths, concatenations and homotopies
-- in a single declaration; the default heartbeat budget does not cover its elaboration.
/-- **Monodromy extension of a local multiplicative datum**: a function on a group of
Möbius translates satisfying the triple cocycle condition on an open covering family of the
upper half plane by translates of a convex base extends to a homomorphism computed by chain
values along paths from the base point. -/
lemma zz_mfunc {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (i₀ : ℂ)
    (hVsub : ∀ γ, V γ ⊆ {z : ℂ | 0 < z.im})
    (hVopen : ∀ γ, IsOpen (V γ))
    (hVcov : ∀ z : ℂ, 0 < z.im → ∃ γ, z ∈ V γ)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (hi₀ : i₀ ∈ V 1) (hV1conv : Convex ℝ (V 1))
    (f : ↥Γ → G)
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b)) :
    ∃ θ : ↥Γ → G,
      (∀ γ δ : ↥Γ, θ (γ * δ) = θ γ * θ δ) ∧
      (∀ γ : ↥Γ, (V 1 ∩ V γ).Nonempty → θ γ = f γ) ∧
      (∀ S : Subgroup G, (∀ x, f x ∈ S) → ∀ γ, θ γ ∈ S) ∧
      (∀ (γ : ↥Γ) (αp : ℝ → ℂ) (N : ℕ) (g : ℕ → ↥Γ), Continuous αp →
        αp 0 = i₀ → αp 1 = moebiusMap (↑γ) i₀ → 0 < N →
        (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → αp t ∈ V (g k)) →
        θ γ = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
          * f ((g (N - 1))⁻¹ * γ)) := by
  classical
  have hi₀im : 0 < i₀.im := hVsub 1 hi₀
  have hf1 : f 1 = 1 := by
    have hmem : (V 1 ∩ V 1 ∩ V ((1 : ↥Γ) * 1)).Nonempty := by
      refine ⟨i₀, ⟨hi₀, hi₀⟩, ?_⟩
      rw [mul_one]
      exact hi₀
    have h := htrip 1 1 hmem
    rw [mul_one] at h
    exact mul_right_cancel (h.trans (one_mul (f 1)).symm)
  have hqmem : ∀ γ : ↥Γ, moebiusMap (↑γ) i₀ ∈ V γ := by
    intro γ
    have h := hVtrans γ 1 i₀ hi₀
    rwa [mul_one] at h
  have hqim : ∀ γ : ↥Γ, 0 < (moebiusMap (↑γ) i₀).im := fun γ => hVsub γ (hqmem γ)
  -- continuity of Möbius maps on the upper half plane
  have hmoebc : ∀ (γ : ↥Γ) (α : ℝ → ℂ), Continuous α → (∀ t : ℝ, 0 < (α t).im) →
      Continuous (fun t => moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (α t)) := by
    intro γ α hαc hαim
    have hcOn : ContinuousOn (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        {z : ℂ | 0 < z.im} := by
      intro z hz
      exact ((hasDerivAt_moebiusMap (↑γ) (moebiusDenom_ne_zero_of_im_ne_zero (↑γ)
        (ne_of_gt hz))).continuousAt).continuousWithinAt
    exact hcOn.comp_continuous hαc hαim
  -- the canonical straight path to the translate of the base point
  obtain ⟨Pc, hPcdef⟩ : ∃ Pc : ↥Γ → ℝ → ℂ,
      Pc = fun (γ : ↥Γ) (t : ℝ) => i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀) :=
    ⟨fun (γ : ↥Γ) (t : ℝ) => i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀), rfl⟩
  have hPcval : ∀ γ t, Pc γ t = i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀) := by
    intro γ t
    rw [hPcdef]
  have hPccont : ∀ γ, Continuous (Pc γ) := by
    intro γ
    rw [hPcdef]
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hPc0 : ∀ γ, Pc γ 0 = i₀ := by
    intro γ
    rw [hPcval]
    push_cast
    ring
  have hPc1 : ∀ γ, Pc γ 1 = moebiusMap (↑γ) i₀ := by
    intro γ
    rw [hPcval]
    push_cast
    ring
  have hPcim : ∀ γ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 < (Pc γ t).im := by
    intro γ t ht0 ht1
    rw [hPcval]
    have h1 := hi₀im
    have h2 := hqim γ
    have him : (i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀)).im
        = (1 - t) * i₀.im + t * (moebiusMap (↑γ) i₀).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, zero_mul, add_zero]
      ring
    rw [him]
    rcases le_or_gt t (1 / 2) with hc | hc
    · nlinarith
    · nlinarith
  -- chains along the canonical paths
  have hch : ∀ γ : ↥Γ, ∃ (N : ℕ) (g : ℕ → ↥Γ), 0 < N ∧
      ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → Pc γ t ∈ V (g k) :=
    fun γ => zz_chain_exists V hVopen (Pc γ) (hPccont γ)
      (fun t ht0 ht1 => hVcov _ (hPcim γ t ht0 ht1))
  choose Nc gc hNc hsc using hch
  obtain ⟨θ, hθdef⟩ : ∃ θ : ↥Γ → G, θ = fun γ =>
      f (gc γ 0) * ((List.range (Nc γ - 1)).map
        fun k => f ((gc γ k)⁻¹ * gc γ (k + 1))).prod * f ((gc γ (Nc γ - 1))⁻¹ * γ) :=
    ⟨_, rfl⟩
  -- the chain-value export
  have hθval : ∀ (γ : ↥Γ) (αp : ℝ → ℂ) (N : ℕ) (g : ℕ → ↥Γ), Continuous αp →
      αp 0 = i₀ → αp 1 = moebiusMap (↑γ) i₀ → 0 < N →
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → αp t ∈ V (g k)) →
      θ γ = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
        * f ((g (N - 1))⁻¹ * γ) := by
    intro γ αp N g hαc hα0 hα1 hN hsub
    rw [hθdef]
    refine (zz_homotopy V f hVsub hVopen hVcov hVtrans htrip hf1 (Pc γ) αp (hPccont γ) hαc
      ?_ ?_ γ (Nc γ) N (gc γ) g (hNc γ) hN (hsc γ) hsub ?_ ?_).symm
    · rw [hPc0, hα0]
    · rw [hPc1, hα1]
    · rw [hPc0]
      exact hi₀
    · rw [hPc1]
      exact hqmem γ
  -- the clamp to the unit interval
  obtain ⟨cl, hcldef⟩ : ∃ cl : ℝ → ℝ, cl = fun t => max 0 (min 1 t) := ⟨_, rfl⟩
  have hclval : ∀ t, cl t = max 0 (min 1 t) := fun t => by rw [hcldef]
  have hclcont : Continuous cl := by
    rw [hcldef]
    exact continuous_const.max (continuous_const.min continuous_id)
  have hcl01 : ∀ t, 0 ≤ cl t ∧ cl t ≤ 1 := by
    intro t
    rw [hclval]
    constructor
    · exact le_max_left _ _
    · rcases le_total 1 t with h | h
      · rw [min_eq_left h]
        exact max_le zero_le_one le_rfl
      · rcases le_total 0 t with h2 | h2
        · rw [min_eq_right h]
          exact max_le zero_le_one h
        · rw [max_eq_left]
          · exact zero_le_one
          · rw [min_eq_right h]
            exact h2
  have hclid : ∀ t, 0 ≤ t → t ≤ 1 → cl t = t := by
    intro t ht0 ht1
    rw [hclval, min_eq_right ht1, max_eq_right ht0]
  refine ⟨θ, ?_, ?_, ?_, hθval⟩
  · -- multiplicativity via the concatenated path
    intro γ δ
    obtain ⟨NN, hNNdef⟩ : ∃ NN : ℕ, NN = Nc γ * Nc δ := ⟨_, rfl⟩
    have hNNpos : 0 < NN := by
      rw [hNNdef]
      exact Nat.mul_pos (hNc γ) (hNc δ)
    -- refine both canonical chains to the common grid
    obtain ⟨g1, hg1def⟩ : ∃ g1 : ℕ → ↥Γ, g1 = fun k => gc γ (k / Nc δ) := ⟨_, rfl⟩
    obtain ⟨h1, hh1def⟩ : ∃ h1 : ℕ → ↥Γ, h1 = fun k => gc δ (k / Nc γ) := ⟨_, rfl⟩
    have hsubg1 : ∀ k < NN, ∀ t : ℝ, (k : ℝ) / NN ≤ t → t ≤ ((k : ℝ) + 1) / NN →
        Pc γ t ∈ V (g1 k) := by
      intro k hk t ht1 ht2
      rw [hg1def]
      rw [hNNdef] at hk ht1 ht2
      exact zz_refine_sub V (Nc γ) (Nc δ) (hNc γ) (hNc δ) (Pc γ) (gc γ) (hsc γ) k hk t ht1 ht2
    have hsubh1 : ∀ k < NN, ∀ t : ℝ, (k : ℝ) / NN ≤ t → t ≤ ((k : ℝ) + 1) / NN →
        Pc δ t ∈ V (h1 k) := by
      intro k hk t ht1 ht2
      rw [hh1def]
      have h := zz_refine_sub V (Nc δ) (Nc γ) (hNc δ) (hNc γ) (Pc δ) (gc δ) (hsc δ)
      rw [Nat.mul_comm (Nc δ) (Nc γ), ← hNNdef] at h
      exact h k hk t ht1 ht2
    -- the concatenated path
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ → ℂ, Q = fun s => if s ≤ 1 / 2 then Pc γ (cl (2 * s))
        else moebiusMap (↑γ) (Pc δ (cl (2 * s - 1))) := ⟨_, rfl⟩
    have hQval : ∀ s, Q s = if s ≤ 1 / 2 then Pc γ (cl (2 * s))
        else moebiusMap (↑γ) (Pc δ (cl (2 * s - 1))) := fun s => by rw [hQdef]
    have hQcont : Continuous Q := by
      rw [hQdef]
      refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact (hPccont γ).comp (hclcont.comp (continuous_const.mul continuous_id))
      · refine hmoebc γ _ ?_ ?_
        · exact (hPccont δ).comp (hclcont.comp ((continuous_const.mul continuous_id).sub
            continuous_const))
        · intro t
          exact hPcim δ _ (hcl01 _).1 (hcl01 _).2
      · intro s hs
        subst hs
        norm_num
        rw [hclid 1 zero_le_one le_rfl, hclid 0 le_rfl zero_le_one, hPc1, hPc0]
    have hQ0 : Q 0 = i₀ := by
      rw [hQval]
      rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 0 = 0 by ring, hclid 0 le_rfl zero_le_one, hPc0]
    have hQ1 : Q 1 = moebiusMap (↑(γ * δ)) i₀ := by
      rw [hQval]
      rw [if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 1 - 1 = 1 by ring, hclid 1 zero_le_one le_rfl, hPc1]
      have hden : moebiusDenom (↑δ) i₀ ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero (↑δ) (ne_of_gt hi₀im)
      have h := moebiusMap_mul (↑γ) (↑δ) i₀ hden
      rw [h]
      rfl
    -- the concatenated chain
    obtain ⟨cch, hcchdef⟩ : ∃ c : ℕ → ↥Γ, c = fun k => if k < NN then g1 k
        else γ * h1 (k - NN) := ⟨_, rfl⟩
    have hcchval : ∀ k, cch k = if k < NN then g1 k else γ * h1 (k - NN) :=
      fun k => by rw [hcchdef]
    have hNN2r : (0 : ℝ) < ((2 * NN : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) < (NN : ℝ) := by exact_mod_cast hNNpos
      linarith
    have hNNr : (0 : ℝ) < (NN : ℝ) := by exact_mod_cast hNNpos
    -- subordination of the concatenated chain on the doubled grid
    have hsubc : ∀ k < 2 * NN, ∀ t : ℝ, (k : ℝ) / (2 * NN : ℕ) ≤ t →
        t ≤ ((k : ℝ) + 1) / (2 * NN : ℕ) → Q t ∈ V (cch k) := by
      intro k hk t ht1 ht2
      by_cases hkN : k < NN
      · -- first half
        rw [hcchval, if_pos hkN]
        have ht2' : t ≤ 1 / 2 := by
          have h1 : ((k : ℝ) + 1) / (2 * NN : ℕ) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ hNN2r (by norm_num : (0 : ℝ) < 2)]
            push_cast
            have : (k : ℝ) + 1 ≤ NN := by exact_mod_cast hkN
            nlinarith
          linarith
        rw [hQval, if_pos ht2']
        have ht0 : 0 ≤ t := le_trans (by positivity) ht1
        have h2t : cl (2 * t) = 2 * t := hclid _ (by linarith) (by linarith)
        rw [h2t]
        refine hsubg1 k hkN (2 * t) ?_ ?_
        · rw [div_le_iff₀ hNNr]
          rw [div_le_iff₀ hNN2r] at ht1
          push_cast at ht1
          linarith
        · rw [le_div_iff₀ hNNr]
          rw [le_div_iff₀ hNN2r] at ht2
          push_cast at ht2
          linarith
      · -- second half
        rw [hcchval, if_neg hkN]
        have hkN' : NN ≤ k := by omega
        have ht1' : 1 / 2 ≤ t := by
          have h1 : (1 : ℝ) / 2 ≤ (k : ℝ) / (2 * NN : ℕ) := by
            rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hNN2r]
            push_cast
            have : (NN : ℝ) ≤ k := by exact_mod_cast hkN'
            nlinarith
          linarith
        have hcast : ((k - NN : ℕ) : ℝ) = (k : ℝ) - NN := by
          push_cast [Nat.cast_sub hkN']
          ring
        have hmem : Pc δ (cl (2 * t - 1)) ∈ V (h1 (k - NN)) := by
          have h2t : cl (2 * t - 1) = 2 * t - 1 := by
            refine hclid _ ?_ ?_
            · linarith
            · have h2 : t ≤ ((k : ℝ) + 1) / (2 * NN : ℕ) := ht2
              have h3 : ((k : ℝ) + 1) / (2 * NN : ℕ) ≤ 1 := by
                rw [div_le_one hNN2r]
                push_cast
                have : (k : ℝ) + 1 ≤ 2 * NN := by exact_mod_cast hk
                linarith
              linarith
          rw [h2t]
          refine hsubh1 (k - NN) (by omega) (2 * t - 1) ?_ ?_
          · rw [hcast, div_le_iff₀ hNNr]
            rw [div_le_iff₀ hNN2r] at ht1
            push_cast at ht1
            linarith
          · rw [hcast, le_div_iff₀ hNNr]
            rw [le_div_iff₀ hNN2r] at ht2
            push_cast at ht2
            linarith
        have htrans := hVtrans γ (h1 (k - NN)) _ hmem
        by_cases hthalf : t ≤ 1 / 2
        · -- the boundary point: both branches have the same value
          have hteq : t = 1 / 2 := le_antisymm hthalf ht1'
          rw [hQval, if_pos hthalf]
          have hveq : Pc γ (cl (2 * t)) = moebiusMap (↑γ) (Pc δ (cl (2 * t - 1))) := by
            rw [hteq]
            norm_num
            rw [hclid 1 zero_le_one le_rfl, hclid 0 le_rfl zero_le_one, hPc1, hPc0]
          rw [hveq]
          exact htrans
        · rw [hQval, if_neg hthalf]
          exact htrans
    -- the three chain values
    have hval_gd := hθval (γ * δ) Q (2 * NN) cch hQcont hQ0 hQ1 (by omega) hsubc
    have hval_g := hθval γ (Pc γ) NN g1 (hPccont γ) (hPc0 γ) (hPc1 γ) hNNpos hsubg1
    have hval_h := hθval δ (Pc δ) NN h1 (hPccont δ) (hPc0 δ) (hPc1 δ) hNNpos hsubh1
    rw [hval_gd, hval_g, hval_h]
    -- endpoints of the concatenated chain
    obtain ⟨MM, hMM⟩ : ∃ MM, NN = MM + 1 := ⟨NN - 1, by omega⟩
    -- split the middle product
    have hsplit : (2 * NN - 1) = MM + (1 + MM) := by omega
    have hc0 : cch 0 = g1 0 := by
      rw [hcchval, if_pos hNNpos]
    have hclast : cch (MM + (1 + MM)) = γ * h1 MM := by
      rw [hcchval, if_neg (by omega)]
      congr 1
      congr 1
      omega
    have hcfirst : ∀ k, k < MM → cch k = g1 k ∧ cch (k + 1) = g1 (k + 1) := by
      intro k hkM
      constructor
      · rw [hcchval, if_pos (by omega)]
      · rw [hcchval, if_pos (by omega)]
    have hcmid : cch MM = g1 MM ∧ cch (MM + 1) = γ * h1 0 := by
      constructor
      · rw [hcchval, if_pos (by omega)]
      · rw [hcchval, if_neg (by omega)]
        congr 1
        congr 1
        omega
    have hcsecond : ∀ x, x < MM →
        cch (MM + (1 + x)) = γ * h1 x ∧ cch (MM + (1 + x) + 1) = γ * h1 (x + 1) := by
      intro x hxM
      constructor
      · rw [hcchval, if_neg (by omega)]
        congr 1
        congr 1
        omega
      · rw [hcchval, if_neg (by omega)]
        congr 1
        congr 1
        omega
    -- the product over the concatenated chain
    rw [hsplit, List.range_add, List.map_append, List.prod_append]
    have hprod1 : ((List.range MM).map fun k => f ((cch k)⁻¹ * cch (k + 1))).prod
        = ((List.range MM).map fun k => f ((g1 k)⁻¹ * g1 (k + 1))).prod := by
      refine congrArg List.prod (List.map_congr_left ?_)
      intro k hk
      have hkM := List.mem_range.mp hk
      rw [(hcfirst k hkM).1, (hcfirst k hkM).2]
    have hprod2 : ((List.map (fun k => f ((cch k)⁻¹ * cch (k + 1)))
        (List.map (fun x => MM + x) (List.range (1 + MM))))).prod
        = f ((g1 MM)⁻¹ * (γ * h1 0))
          * ((List.range MM).map fun k => f ((h1 k)⁻¹ * h1 (k + 1))).prod := by
      rw [show (1 + MM) = 1 + MM from rfl, List.range_add, List.map_append, List.map_append,
        List.prod_append, List.range_one]
      congr 1
      · simp only [List.map_singleton, List.prod_singleton, Nat.add_zero]
        rw [hcmid.1, hcmid.2]
      · refine congrArg List.prod ?_
        rw [List.map_map, List.map_map]
        refine List.map_congr_left ?_
        intro x hx
        have hxM := List.mem_range.mp hx
        simp only [Function.comp_apply]
        rw [(hcsecond x hxM).1, (hcsecond x hxM).2]
        rw [show (γ * h1 x)⁻¹ * (γ * h1 (x + 1)) = (h1 x)⁻¹ * h1 (x + 1) by group]
    rw [hprod1, hprod2, hc0, hclast]
    -- the junction identity
    have hjunc : f ((g1 MM)⁻¹ * (γ * h1 0)) = f ((g1 MM)⁻¹ * γ) * f (h1 0) := by
      have hmem1 : moebiusMap (↑γ) i₀ ∈ V (g1 MM) := by
        have hle1 : ((MM : ℝ)) / (NN : ℕ) ≤ 1 := by
          rw [div_le_one hNNr]
          have : (MM : ℝ) + 1 = NN := by exact_mod_cast hMM.symm
          linarith
        have hle2 : (1 : ℝ) ≤ ((MM : ℝ) + 1) / (NN : ℕ) := by
          rw [le_div_iff₀ hNNr]
          have : (MM : ℝ) + 1 = NN := by exact_mod_cast hMM.symm
          linarith
        have h := hsubg1 MM (by omega) 1 hle1 hle2
        rwa [hPc1] at h
      have hmem2 : moebiusMap (↑γ) i₀ ∈ V γ := hqmem γ
      have hmem3 : moebiusMap (↑γ) i₀ ∈ V (γ * h1 0) := by
        have h0m : Pc δ 0 ∈ V (h1 0) := by
          refine hsubh1 0 (by omega) 0 ?_ ?_
          · rw [Nat.cast_zero, zero_div]
          · rw [Nat.cast_zero, zero_add, le_div_iff₀ hNNr]
            linarith
        rw [hPc0] at h0m
        exact hVtrans γ (h1 0) i₀ h0m
      have h := zz_step V f hVtrans htrip (g1 MM) γ (γ * h1 0) (moebiusMap (↑γ) i₀)
        hmem1 hmem2 hmem3
      rw [show γ⁻¹ * (γ * h1 0) = h1 0 by group] at h
      exact h.symm
    rw [show (γ * h1 MM)⁻¹ * (γ * δ) = (h1 MM)⁻¹ * δ by group]
    rw [hjunc]
    -- final regrouping
    rw [show NN - 1 = MM by omega]
    simp only [← mul_assoc]
  · -- agreement with `f` on overlapping translates
    intro γ ⟨q, hq1, hqγ⟩
    have hqim' : 0 < q.im := hVsub 1 hq1
    have hq'mem : moebiusMap (↑(γ⁻¹ : ↥Γ)) q ∈ V 1 := by
      have h := hVtrans γ⁻¹ γ q hqγ
      rwa [inv_mul_cancel] at h
    -- two-leg path through the common point
    obtain ⟨L1, hL1def⟩ : ∃ L : ℝ → ℂ, L = fun (u : ℝ) => i₀ + (u : ℂ) * (q - i₀) :=
      ⟨fun (u : ℝ) => i₀ + (u : ℂ) * (q - i₀), rfl⟩
    obtain ⟨L2, hL2def⟩ : ∃ L : ℝ → ℂ,
        L = fun (u : ℝ) => moebiusMap (↑(γ⁻¹ : ↥Γ)) q
          + (u : ℂ) * (i₀ - moebiusMap (↑(γ⁻¹ : ↥Γ)) q) :=
      ⟨fun (u : ℝ) => moebiusMap (↑(γ⁻¹ : ↥Γ)) q
        + (u : ℂ) * (i₀ - moebiusMap (↑(γ⁻¹ : ↥Γ)) q), rfl⟩
    have hL1mem : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → L1 u ∈ V 1 := by
      intro u hu0 hu1
      rw [hL1def]
      have h := hV1conv hi₀ hq1 (by linarith : (0 : ℝ) ≤ 1 - u) hu0 (by ring)
      have heq : (1 - u) • i₀ + u • q = i₀ + (u : ℂ) * (q - i₀) := by
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rwa [heq] at h
    have hL2mem : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → L2 u ∈ V 1 := by
      intro u hu0 hu1
      rw [hL2def]
      have h := hV1conv hq'mem hi₀ (by linarith : (0 : ℝ) ≤ 1 - u) hu0 (by ring)
      have heq : (1 - u) • moebiusMap (↑(γ⁻¹ : ↥Γ)) q + u • i₀
          = moebiusMap (↑(γ⁻¹ : ↥Γ)) q + (u : ℂ) * (i₀ - moebiusMap (↑(γ⁻¹ : ↥Γ)) q) := by
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rwa [heq] at h
    have hL1cont : Continuous L1 := by
      rw [hL1def]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hL2cont : Continuous L2 := by
      rw [hL2def]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ → ℂ, Q = fun s => if s ≤ 1 / 2 then L1 (cl (2 * s))
        else moebiusMap (↑γ) (L2 (cl (2 * s - 1))) := ⟨_, rfl⟩
    have hQval : ∀ s, Q s = if s ≤ 1 / 2 then L1 (cl (2 * s))
        else moebiusMap (↑γ) (L2 (cl (2 * s - 1))) := fun s => by rw [hQdef]
    have hL10 : L1 0 = i₀ := by
      rw [hL1def]
      push_cast
      ring
    have hL11 : L1 1 = q := by
      rw [hL1def]
      push_cast
      ring
    have hL20 : L2 0 = moebiusMap (↑(γ⁻¹ : ↥Γ)) q := by
      rw [hL2def]
      push_cast
      ring
    have hL21 : L2 1 = i₀ := by
      rw [hL2def]
      push_cast
      ring
    have hglue : moebiusMap (↑γ) (L2 0) = q := by
      rw [hL20]
      have hden : moebiusDenom (↑(γ⁻¹ : ↥Γ)) q ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hqim')
      have h := moebiusMap_mul (↑γ) (↑(γ⁻¹ : ↥Γ)) q hden
      have hcoe : (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (↑(γ⁻¹ : ↥Γ)) = 1 := by
        push_cast
        group
      rw [hcoe] at h
      rw [h, moebiusMap_one]
    have hQcont : Continuous Q := by
      rw [hQdef]
      refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact hL1cont.comp (hclcont.comp (continuous_const.mul continuous_id))
      · refine hmoebc γ _ ?_ ?_
        · exact hL2cont.comp (hclcont.comp ((continuous_const.mul continuous_id).sub
            continuous_const))
        · intro t
          exact hVsub 1 (hL2mem _ (hcl01 _).1 (hcl01 _).2)
      · intro s hs
        subst hs
        norm_num
        rw [hclid 1 zero_le_one le_rfl, hclid 0 le_rfl zero_le_one, hL11, hglue]
    have hQ0 : Q 0 = i₀ := by
      rw [hQval, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 0 = 0 by ring, hclid 0 le_rfl zero_le_one, hL10]
    have hQ1 : Q 1 = moebiusMap (↑γ) i₀ := by
      rw [hQval, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 1 - 1 = 1 by ring, hclid 1 zero_le_one le_rfl, hL21]
    -- the two-slot chain
    obtain ⟨g2, hg2def⟩ : ∃ g : ℕ → ↥Γ, g = fun k => if k = 0 then 1 else γ := ⟨_, rfl⟩
    have hsub2 : ∀ k : ℕ, k < 2 → ∀ t : ℝ, (k : ℝ) / ((2 : ℕ) : ℝ) ≤ t →
        t ≤ ((k : ℝ) + 1) / ((2 : ℕ) : ℝ) → Q t ∈ V (g2 k) := by
      intro k hk t ht1 ht2
      have h20 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h20] at ht1 ht2
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [hg2def]
        simp only [reduceIte]
        push_cast at ht1 ht2
        have ht2' : t ≤ 1 / 2 := by linarith
        rw [hQval, if_pos ht2']
        exact hL1mem _ (hcl01 _).1 (hcl01 _).2
      · rw [hg2def]
        simp only [if_neg (by omega : ¬ (1 : ℕ) = 0)]
        push_cast at ht1 ht2
        by_cases hthalf : t ≤ 1 / 2
        · have hteq : t = 1 / 2 := le_antisymm hthalf (by linarith)
          rw [hQval, if_pos hthalf, hteq]
          norm_num
          rw [hclid 1 zero_le_one le_rfl, hL11]
          exact hqγ
        · rw [hQval, if_neg hthalf]
          have h := hL2mem (cl (2 * t - 1)) (hcl01 _).1 (hcl01 _).2
          have htr := hVtrans γ 1 _ h
          rwa [mul_one] at htr
    have hval := hθval γ Q 2 g2 hQcont hQ0 hQ1 (by omega) hsub2
    rw [hval, hg2def]
    norm_num
    rw [hf1, one_mul, mul_one]
  · -- membership
    intro S hfS γ
    rw [hθdef]
    refine mul_mem (mul_mem (hfS _) ?_) (hfS _)
    refine Subgroup.list_prod_mem S ?_
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact hfS _

/-- Chain values of a group homomorphism telescope to the target. -/
lemma zz_telescope {H K : Type} [Group H] [Group K] (c : H →* K)
    (N : ℕ) (hN : 0 < N) (g : ℕ → H) (γt : H) :
    c (g 0) * ((List.range (N - 1)).map fun k => c ((g k)⁻¹ * g (k + 1))).prod
      * c ((g (N - 1))⁻¹ * γt) = c γt := by
  have key : ∀ M : ℕ, c (g 0) * ((List.range M).map fun k => c ((g k)⁻¹ * g (k + 1))).prod
      = c (g M) := by
    intro M
    induction M with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.prod_nil, mul_one]
    | succ M ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, ← mul_assoc, ih, ← map_mul]
      congr 1
      group
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [key M, ← map_mul]
  congr 1
  group

/-- Two sequences in trace-gapped groups converging to a common limit in
`SL(2, ℝ)` are eventually equal: they are eventually equal up to sign, and the sign is
excluded by convergence at a nonvanishing entry of the limit. -/
lemma zz_ev_eq {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    {a b : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (ha : ∀ n, a n ∈ Γ n) (hb : ∀ n, b n ∈ Γ n)
    {L : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hla : Filter.Tendsto a Filter.atTop (nhds L))
    (hlb : Filter.Tendsto b Filter.atTop (nhds L)) :
    ∀ᶠ n in Filter.atTop, a n = b n := by
  -- a nonvanishing entry of the limit
  have hLne : ∃ i j : Fin 2, (L : Matrix (Fin 2) (Fin 2) ℝ) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hdet : (L : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := Matrix.SpecialLinearGroup.det_coe L
    rw [Matrix.det_fin_two, hcon 0 0, hcon 0 1] at hdet
    norm_num at hdet
  obtain ⟨i, j, hij⟩ := hLne
  have hev := eventually_eq_up_to_sign_of_tendsto hε Γ hgap ha hb hla hlb
  -- entrywise convergence at the distinguished entry
  have hentry : ∀ (c : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      Filter.Tendsto c Filter.atTop (nhds L) →
      ∀ᶠ n in Filter.atTop,
        |(c n : Matrix (Fin 2) (Fin 2) ℝ) i j - (L : Matrix (Fin 2) (Fin 2) ℝ) i j|
          < |(L : Matrix (Fin 2) (Fin 2) ℝ) i j| := by
    intro c hc
    have hmat : Filter.Tendsto (fun n => (c n : Matrix (Fin 2) (Fin 2) ℝ)) Filter.atTop
        (nhds (L : Matrix (Fin 2) (Fin 2) ℝ)) := tendsto_subtype_rng.mp hc
    have hent : Filter.Tendsto (fun n => (c n : Matrix (Fin 2) (Fin 2) ℝ) i j) Filter.atTop
        (nhds ((L : Matrix (Fin 2) (Fin 2) ℝ) i j)) := by
      have hcontinuous : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j :=
        continuous_apply_apply i j
      exact (hcontinuous.tendsto _).comp hmat
    have habs : Filter.Tendsto (fun n =>
        |(c n : Matrix (Fin 2) (Fin 2) ℝ) i j - (L : Matrix (Fin 2) (Fin 2) ℝ) i j|)
        Filter.atTop (nhds 0) := by
      have h := hent.sub (tendsto_const_nhds
        (x := (L : Matrix (Fin 2) (Fin 2) ℝ) i j) (f := Filter.atTop))
      rw [sub_self] at h
      have habs0 : |(0 : ℝ)| = 0 := abs_zero
      exact habs0 ▸ h.abs
    exact habs.eventually_lt_const (abs_pos.mpr hij)
  filter_upwards [hev, hentry a hla, hentry b hlb] with n hn hna hnb
  rcases hn with h | h
  · exact h
  · exfalso
    have hbij := congrFun (congrFun h i) j
    rw [Matrix.neg_apply] at hbij
    rcases lt_or_gt_of_ne hij with hL | hL
    · rw [abs_of_neg hL] at hna hnb
      have h1 := abs_lt.mp hna
      have h2 := abs_lt.mp hnb
      linarith [h1.1, h1.2, h2.1, h2.2, hbij]
    · rw [abs_of_pos hL] at hna hnb
      have h1 := abs_lt.mp hna
      have h2 := abs_lt.mp hnb
      linarith [h1.1, h1.2, h2.1, h2.2, hbij]

/-- Chain values converge entrywise along converging local data. -/
lemma zz_val_tendsto {H : Type} [Group H]
    (t : ℕ → H → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (c : H → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hconv : ∀ x : H, Filter.Tendsto (fun n => t n x) Filter.atTop (nhds (c x)))
    (N : ℕ) (g : ℕ → H) (γt : H) :
    Filter.Tendsto (fun n => t n (g 0) * ((List.range (N - 1)).map
        fun k => t n ((g k)⁻¹ * g (k + 1))).prod * t n ((g (N - 1))⁻¹ * γt))
      Filter.atTop (nhds (c (g 0) * ((List.range (N - 1)).map
        fun k => c ((g k)⁻¹ * g (k + 1))).prod * c ((g (N - 1))⁻¹ * γt))) := by
  have hprod : ∀ M : ℕ, Filter.Tendsto (fun n => ((List.range M).map
      fun k => t n ((g k)⁻¹ * g (k + 1))).prod) Filter.atTop
      (nhds (((List.range M).map fun k => c ((g k)⁻¹ * g (k + 1))).prod)) := by
    intro M
    induction M with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.prod_nil]
      exact tendsto_const_nhds
    | succ M ih =>
      simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton]
      exact ih.mul (hconv _)
  exact ((hconv (g 0)).mul (hprod (N - 1))).mul (hconv _)

end RiemannDynamics

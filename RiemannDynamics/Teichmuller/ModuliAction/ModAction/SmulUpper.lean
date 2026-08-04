/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.ModAction.UpperRemark

/-!
# The re-marked representative and the re-marking action

The re-marked Teichmüller representative, its Möbius factorization and
boundary behavior, and the induced re-marking action on Teichmüller space.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The **re-marked representative**: the representative whose coefficient is the
symmetric extension of the Beltrami datum of `x.w ∘ P.g` on the upper half plane. -/
noncomputable def TeichRep.smulUpper (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    TeichRep Γ₀ :=
  TeichRep.ofUpper Γ₀ (wirtingerQuotient (x.w ∘ P.g))
    (measurable_wirtingerQuotient_remark x P)
    (wirtingerQuotient_remark_bound x P)
    (wirtingerQuotient_remark_invariant x P)

/-- Plane Möbius maps of real matrices commute with complex conjugation. -/
theorem moebiusMap_conj (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    moebiusMap γ (starRingEnd ℂ z) = starRingEnd ℂ (moebiusMap γ z) := by
  simp [moebiusMap, moebiusDenom, map_div₀, map_add, map_mul, Complex.conj_ofReal]

/-- A real Möbius map sends real points to real points. -/
theorem moebiusMap_ofReal (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    ∃ r : ℝ, moebiusMap γ (t : ℂ) = (r : ℂ) := by
  have h := moebiusMap_conj γ (t : ℂ)
  rw [Complex.conj_ofReal] at h
  have him : (moebiusMap γ (t : ℂ)).im = 0 := Complex.conj_eq_iff_im.mp h.symm
  exact ⟨(moebiusMap γ (t : ℂ)).re, (Complex.ext (by simp) (by simp [him])).symm⟩

/-- The pole set of a plane Möbius map is a subsingleton. -/
theorem moebiusDenom_zero_subsingleton (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Set.Subsingleton {w : ℂ | moebiusDenom γ w = 0} := by
  intro w₁ hw₁ w₂ hw₂
  have h₁' : (γ 1 0 : ℂ) * w₁ + (γ 1 1 : ℂ) = 0 := hw₁
  have h₂' : (γ 1 0 : ℂ) * w₂ + (γ 1 1 : ℂ) = 0 := hw₂
  by_cases hc : γ 1 0 = 0
  · exfalso
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe γ
      rwa [Matrix.det_fin_two] at h
    have hcC : ((γ 1 0 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
    rw [hcC, zero_mul, zero_add] at h₁'
    have hd : γ 1 1 = 0 := by exact_mod_cast h₁'
    rw [hc, hd] at hdet
    simp at hdet
  · have hcC : ((γ 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have hmul : (γ 1 0 : ℂ) * w₁ = (γ 1 0 : ℂ) * w₂ := by linear_combination h₁' - h₂'
    exact mul_left_cancel₀ hcC hmul

/-- The normalized solution reflects upper-half-plane membership. -/
theorem w_im_pos_rev (x : TeichRep Γ₀) {z : ℂ} (h : 0 < (x.w z).im) : 0 < z.im := by
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · exfalso
    have h1 : 0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im]
      linarith
    have h2 := x.w_mapsTo_upper _ h1
    rw [x.w_conj, Complex.conj_im] at h2
    linarith
  · exfalso
    have hz : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hzero])
    have h4 := x.w_real z.re
    rw [hz] at h4
    linarith
  · exact hpos

/-- Boundary limit: a continuous plane map that factors through Möbius maps and a
real-fixing continuous map on the upper half plane extends the Möbius identity to a real
boundary point off the poles. -/
theorem moebius_boundary {Λ φ : ℂ → ℂ} (hΛc : Continuous Λ) (hφc : Continuous φ)
    (hφr : ∀ r : ℝ, φ (r : ℂ) = (r : ℂ)) (Rx Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hint : ∀ ζ : ℂ, 0 < ζ.im → Λ ζ = moebiusMap Rx (φ (moebiusMap Ry⁻¹ ζ)))
    {t : ℝ} (hd1 : moebiusDenom Ry⁻¹ (t : ℂ) ≠ 0)
    (hd2 : moebiusDenom Rx (moebiusMap Ry⁻¹ (t : ℂ)) ≠ 0) :
    Λ (t : ℂ) = moebiusMap Rx (moebiusMap Ry⁻¹ (t : ℂ)) := by
  obtain ⟨r, hr⟩ := moebiusMap_ofReal Ry⁻¹ t
  set z : ℕ → ℂ := fun n => (t : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hzdef
  have him' : ∀ s : ℝ, ((t : ℂ) + (s : ℂ) * Complex.I).im = s := by
    intro s
    simp [Complex.add_im, Complex.mul_im]
  have hzim : ∀ n : ℕ, 0 < (z n).im := by
    intro n
    have h1 : (z n).im = 1 / ((n : ℝ) + 1) := by
      rw [hzdef]
      exact him' (1 / ((n : ℝ) + 1))
    rw [h1]
    positivity
  have htend : Filter.Tendsto z Filter.atTop (nhds (t : ℂ)) := by
    rw [hzdef]
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (nhds ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    have h3 := (h2.mul_const Complex.I).const_add (t : ℂ)
    simpa using h3
  have hL : Filter.Tendsto (fun n => Λ (z n)) Filter.atTop (nhds (Λ (t : ℂ))) :=
    (hΛc.tendsto _).comp htend
  have hc1 : ContinuousAt (moebiusMap Ry⁻¹) (t : ℂ) :=
    (hasDerivAt_moebiusMap Ry⁻¹ hd1).continuousAt
  have hc2 : ContinuousAt φ (moebiusMap Ry⁻¹ (t : ℂ)) := hφc.continuousAt
  have hφpt : φ (moebiusMap Ry⁻¹ (t : ℂ)) = moebiusMap Ry⁻¹ (t : ℂ) := by
    rw [hr, hφr r]
  have hc3 : ContinuousAt (moebiusMap Rx) (φ (moebiusMap Ry⁻¹ (t : ℂ))) := by
    rw [hφpt]
    exact (hasDerivAt_moebiusMap Rx hd2).continuousAt
  have hR : Filter.Tendsto (fun n => moebiusMap Rx (φ (moebiusMap Ry⁻¹ (z n))))
      Filter.atTop (nhds (moebiusMap Rx (φ (moebiusMap Ry⁻¹ (t : ℂ))))) := by
    have s1 : Filter.Tendsto (fun n => moebiusMap Ry⁻¹ (z n)) Filter.atTop
        (nhds (moebiusMap Ry⁻¹ (t : ℂ))) := hc1.tendsto.comp htend
    have s2 : Filter.Tendsto (fun n => φ (moebiusMap Ry⁻¹ (z n))) Filter.atTop
        (nhds (φ (moebiusMap Ry⁻¹ (t : ℂ)))) := hc2.tendsto.comp s1
    exact hc3.tendsto.comp s2
  have hEqn : (fun n => Λ (z n)) = fun n => moebiusMap Rx (φ (moebiusMap Ry⁻¹ (z n))) :=
    funext fun n => hint (z n) (hzim n)
  rw [hEqn] at hL
  have hfin := tendsto_nhds_unique hL hR
  rw [hfin, hφpt]

/-- A plane homeomorphism agreeing with a real Möbius map on a cofinite set of the real
line forces the Möbius map to be affine: otherwise the Möbius values stay bounded along
large reals while the homeomorphism escapes every compact set. -/
theorem sl2_lower_left_eq_zero (Λ : ℂ ≃ₜ ℂ)
    (S : Matrix.SpecialLinearGroup (Fin 2) ℝ) {B : Set ℝ} (hB : B.Finite)
    (hEq : ∀ t : ℝ, t ∉ B → Λ (t : ℂ) = moebiusMap S (t : ℂ)) : S 1 0 = 0 := by
  by_contra hc
  have hcpos : 0 < |S 1 0| := abs_pos.mpr hc
  obtain ⟨M, hM⟩ := hB.bddAbove
  have hnorm : ∀ t : ℝ, ‖moebiusMap S (t : ℂ)‖
      = |S 0 0 * t + S 0 1| / |S 1 0 * t + S 1 1| := by
    intro t
    have hcast : moebiusMap S (t : ℂ)
        = ((S 0 0 * t + S 0 1 : ℝ) : ℂ) / ((S 1 0 * t + S 1 1 : ℝ) : ℂ) := by
      simp only [moebiusMap, moebiusDenom]
      push_cast
      ring
    rw [hcast, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  set C := 2 * (|S 0 0| + |S 0 1|) / |S 1 0| with hCdef
  set T := (2 * |S 1 1| + 2) / |S 1 0| with hTdef
  have hbound : ∀ t : ℝ, max T 1 ≤ t → ‖moebiusMap S (t : ℂ)‖ ≤ C := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hTt : 2 * |S 1 1| + 2 ≤ |S 1 0| * t := by
      rw [hTdef, div_le_iff₀ hcpos] at htT
      linarith [htT, mul_comm t |S 1 0|]
    have hup : |S 0 0 * t + S 0 1| ≤ (|S 0 0| + |S 0 1|) * t := by
      have h1 : |S 0 0 * t + S 0 1| ≤ |S 0 0 * t| + |S 0 1| := abs_add_le _ _
      have h2 : |S 0 0 * t| = |S 0 0| * t := by rw [abs_mul, abs_of_pos htpos]
      have h3 : |S 0 1| ≤ |S 0 1| * t := le_mul_of_one_le_right (abs_nonneg _) ht1
      nlinarith [h1, h2, h3]
    have hlow : |S 1 0| * t / 2 ≤ |S 1 0 * t + S 1 1| := by
      have h1 : |S 1 0 * t| ≤ |S 1 0 * t + S 1 1| + |S 1 1| := by
        have h := abs_add_le (S 1 0 * t + S 1 1) (-(S 1 1))
        simp only [add_neg_cancel_right, abs_neg] at h
        exact h
      have h2 : |S 1 0 * t| = |S 1 0| * t := by rw [abs_mul, abs_of_pos htpos]
      linarith [h1, h2, hTt]
    have hlowpos : 0 < |S 1 0 * t + S 1 1| := by
      have h4 : 0 < |S 1 0| * t / 2 := by positivity
      linarith
    rw [hnorm t, div_le_iff₀ hlowpos]
    have hCnn : 0 ≤ C := by
      rw [hCdef]
      positivity
    have hmid : (|S 0 0| + |S 0 1|) * t = C * (|S 1 0| * t / 2) := by
      rw [hCdef]
      field_simp
    calc |S 0 0 * t + S 0 1| ≤ (|S 0 0| + |S 0 1|) * t := hup
      _ = C * (|S 1 0| * t / 2) := hmid
      _ ≤ C * |S 1 0 * t + S 1 1| := mul_le_mul_of_nonneg_left hlow hCnn
  have hKc : IsCompact (⇑Λ.symm '' Metric.closedBall (0 : ℂ) C) :=
    (isCompact_closedBall _ _).image Λ.symm.continuous
  obtain ⟨M', hM'⟩ := hKc.isBounded.subset_closedBall 0
  set t0 := max (max T 1) (max M M') + 1 with ht0def
  have ht0T : max T 1 ≤ t0 := by
    rw [ht0def]
    linarith [le_max_left (max T 1) (max M M')]
  have ht0M : M < t0 := by
    rw [ht0def]
    linarith [le_max_left M M', le_max_right (max T 1) (max M M')]
  have ht0M' : M' < t0 := by
    rw [ht0def]
    linarith [le_max_right M M', le_max_right (max T 1) (max M M')]
  have hgood : t0 ∉ B := fun hmem => absurd (hM hmem) (not_le.mpr ht0M)
  have hmem : Λ ((t0 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) C := by
    rw [mem_closedBall_zero_iff, hEq t0 hgood]
    exact hbound t0 ht0T
  have himg : ((t0 : ℝ) : ℂ) ∈ ⇑Λ.symm '' Metric.closedBall (0 : ℂ) C :=
    ⟨Λ ((t0 : ℝ) : ℂ), hmem, Λ.symm_apply_apply _⟩
  have hnrm : ‖((t0 : ℝ) : ℂ)‖ ≤ M' := by
    have h := hM' himg
    rwa [mem_closedBall_zero_iff] at h
  rw [Complex.norm_real, Real.norm_eq_abs] at hnrm
  have hle : t0 ≤ M' := le_trans (le_abs_self t0) hnrm
  linarith

/-- A continuous plane map that fixes `0` and `1` and agrees on the real line off a
subsingleton with an affine real Möbius map fixes the whole real line. -/
theorem homeo_fix_real {Λ : ℂ → ℂ} (hΛc : Continuous Λ)
    (S : Matrix.SpecialLinearGroup (Fin 2) ℝ) {B : Set ℝ} (hB : B.Subsingleton)
    (hc : S 1 0 = 0) (hEq : ∀ t : ℝ, t ∉ B → Λ (t : ℂ) = moebiusMap S (t : ℂ))
    (h0 : Λ 0 = 0) (h1 : Λ 1 = 1) : ∀ t : ℝ, Λ (t : ℂ) = (t : ℂ) := by
  have hdet : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe S
    rwa [Matrix.det_fin_two] at h
  have hd : S 1 1 ≠ 0 := by
    intro h0'
    rw [hc, h0'] at hdet
    simp at hdet
  have hdC : ((S 1 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hval : ∀ s : ℝ, moebiusMap S (s : ℂ)
      = ((S 0 0 : ℂ) * (s : ℂ) + (S 0 1 : ℂ)) / (S 1 1 : ℂ) := by
    intro s
    simp only [moebiusMap, moebiusDenom, hc, Complex.ofReal_zero, zero_mul, zero_add]
  have hdense : Dense Bᶜ := by
    rcases hB.eq_empty_or_singleton with hB0 | ⟨p, hp⟩
    · rw [hB0, Set.compl_empty]
      exact dense_univ
    · rw [hp]
      exact dense_compl_singleton p
  have hf1 : Continuous fun s : ℝ => Λ (s : ℂ) := hΛc.comp Complex.continuous_ofReal
  have hf2 : Continuous fun s : ℝ => moebiusMap S (s : ℂ) := by
    have heq : (fun s : ℝ => moebiusMap S (s : ℂ))
        = fun s : ℝ => ((S 0 0 : ℂ) * (s : ℂ) + (S 0 1 : ℂ)) / (S 1 1 : ℂ) :=
      funext hval
    rw [heq]
    exact ((continuous_const.mul Complex.continuous_ofReal).add continuous_const).div_const _
  have hext : (fun s : ℝ => Λ (s : ℂ)) = fun s : ℝ => moebiusMap S (s : ℂ) :=
    Continuous.ext_on hdense hf1 hf2 fun s hs => hEq s hs
  have hall : ∀ s : ℝ, Λ (s : ℂ) = ((S 0 0 : ℂ) * (s : ℂ) + (S 0 1 : ℂ)) / (S 1 1 : ℂ) :=
    fun s => (congrFun hext s).trans (hval s)
  have hb0 : ((S 0 1 : ℝ) : ℂ) = 0 := by
    have h := hall 0
    rw [Complex.ofReal_zero, h0, mul_zero, zero_add] at h
    rcases div_eq_zero_iff.mp h.symm with h' | h'
    · exact h'
    · exact absurd h' hdC
  have ha : ((S 0 0 : ℝ) : ℂ) = ((S 1 1 : ℝ) : ℂ) := by
    have h := hall 1
    rw [Complex.ofReal_one, h1, mul_one, hb0, add_zero] at h
    have h2 := (eq_div_iff hdC).mp h
    rw [one_mul] at h2
    exact h2.symm
  intro t
  rw [hall t, hb0, add_zero, ha, mul_comm ((S 1 1 : ℝ) : ℂ) ((t : ℝ) : ℂ), mul_div_assoc,
    div_self hdC, mul_one]

/-- The Möbius endgame: a plane self-homeomorphism fixing `0` and `1` whose restriction to
the upper half plane is a Möbius conjugate of a continuous real-fixing map fixes the real
line pointwise. -/
theorem upper_factor_fix_real (Λ : ℂ ≃ₜ ℂ) {φ : ℂ → ℂ} (hφc : Continuous φ)
    (hφr : ∀ r : ℝ, φ (r : ℂ) = (r : ℂ)) (Rx Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hint : ∀ ζ : ℂ, 0 < ζ.im → Λ ζ = moebiusMap Rx (φ (moebiusMap Ry⁻¹ ζ)))
    (h0 : Λ 0 = 0) (h1 : Λ 1 = 1) : ∀ t : ℝ, Λ (t : ℂ) = (t : ℂ) := by
  classical
  set B1 : Set ℝ := {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) = 0} with hB1def
  set B2 : Set ℝ := {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0
    ∧ moebiusDenom Rx (moebiusMap Ry⁻¹ (s : ℂ)) = 0} with hB2def
  have hB1sub : B1.Subsingleton := by
    intro t₁ h₁ t₂ h₂
    have h₁' : moebiusDenom Ry⁻¹ ((t₁ : ℝ) : ℂ) = 0 := h₁
    have h₂' : moebiusDenom Ry⁻¹ ((t₂ : ℝ) : ℂ) = 0 := h₂
    have h := moebiusDenom_zero_subsingleton Ry⁻¹ h₁' h₂'
    exact_mod_cast h
  have hback : ∀ s : ℝ, moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 →
      moebiusMap Ry (moebiusMap Ry⁻¹ (s : ℂ)) = (s : ℂ) := by
    intro s hs
    rw [moebiusMap_mul Ry Ry⁻¹ _ hs, mul_inv_cancel, moebiusMap_one]
  have hB2sub : B2.Subsingleton := by
    intro t₁ h₁ t₂ h₂
    obtain ⟨h₁a, h₁b⟩ := h₁
    obtain ⟨h₂a, h₂b⟩ := h₂
    have h₁b' : moebiusDenom Rx (moebiusMap Ry⁻¹ ((t₁ : ℝ) : ℂ)) = 0 := h₁b
    have h₂b' : moebiusDenom Rx (moebiusMap Ry⁻¹ ((t₂ : ℝ) : ℂ)) = 0 := h₂b
    have hw := moebiusDenom_zero_subsingleton Rx h₁b' h₂b'
    have h := hback t₁ h₁a
    rw [hw, hback t₂ h₂a] at h
    exact_mod_cast h.symm
  have hEqGood : ∀ s : ℝ, s ∉ B1 ∪ B2 → Λ (s : ℂ) = moebiusMap (Rx * Ry⁻¹) (s : ℂ) := by
    intro s hs
    have hd1 : moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 := fun h => hs (Set.mem_union_left _ h)
    have hd2 : moebiusDenom Rx (moebiusMap Ry⁻¹ (s : ℂ)) ≠ 0 := fun h =>
      hs (Set.mem_union_right _ ⟨hd1, h⟩)
    rw [moebius_boundary Λ.continuous hφc hφr Rx Ry hint hd1 hd2,
      moebiusMap_mul Rx Ry⁻¹ _ hd1]
  have hc0 : (Rx * Ry⁻¹) 1 0 = 0 :=
    sl2_lower_left_eq_zero Λ (Rx * Ry⁻¹) (hB1sub.finite.union hB2sub.finite) hEqGood
  have hdet : (Rx * Ry⁻¹) 0 0 * (Rx * Ry⁻¹) 1 1
      - (Rx * Ry⁻¹) 0 1 * (Rx * Ry⁻¹) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (Rx * Ry⁻¹)
    rwa [Matrix.det_fin_two] at h
  have hd11 : (Rx * Ry⁻¹) 1 1 ≠ 0 := by
    intro h'
    rw [hc0, h'] at hdet
    simp at hdet
  have hEq1 : ∀ s : ℝ, s ∉ B1 → Λ (s : ℂ) = moebiusMap (Rx * Ry⁻¹) (s : ℂ) := by
    intro s hs
    have hd1 : moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 := hs
    have hSden : moebiusDenom (Rx * Ry⁻¹) (s : ℂ) ≠ 0 := by
      simp only [moebiusDenom, hc0, Complex.ofReal_zero, zero_mul, zero_add]
      exact Complex.ofReal_ne_zero.mpr hd11
    have hprod : moebiusDenom Rx (moebiusMap Ry⁻¹ (s : ℂ))
        * moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 := by
      rw [moebiusDenom_mul Rx Ry⁻¹ _ hd1]
      exact hSden
    have hd2 := left_ne_zero_of_mul hprod
    rw [moebius_boundary Λ.continuous hφc hφr Rx Ry hint hd1 hd2,
      moebiusMap_mul Rx Ry⁻¹ _ hd1]
  exact homeo_fix_real Λ.continuous (Rx * Ry⁻¹) hB1sub hc0 hEq1 h0 h1

/-- Factorization of the re-marked solution: on the upper half plane, the normalized
solution of the re-marked representative is a real Möbius map applied to `x.w ∘ P.g`, as
the two maps solve the same Beltrami equation there. -/
theorem TeichRep.smulUpper_w (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → (x.smulUpper P).w z = moebiusMap R (x.w (P.g z)) := by
  have hv := x.isQCUpper_remark P
  have hκ : (max P.κ 0 + x.b.normInf) / (1 + max P.κ 0 * x.b.normInf) < 1 := by
    have ha0 : (0 : ℝ) ≤ max P.κ 0 := le_max_right _ _
    have ha1 : max P.κ 0 < 1 := max_lt P.hκ one_pos
    have hb0 : (0 : ℝ) ≤ x.b.normInf := x.b.normInf_nonneg
    have hb1 : x.b.normInf < 1 := x.b.normInf_lt_one
    have hab : (0 : ℝ) < 1 + max P.κ 0 * x.b.normInf := by nlinarith [mul_nonneg ha0 hb0]
    rw [div_lt_one hab]
    nlinarith [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1)]
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar (x.w ∘ P.g) z = (x.smulUpper P).b.μ z * dz (x.w ∘ P.g) z := by
    filter_upwards [hv.belt, ae_restrict_mem hU] with z hbelt hzU
    have hμ : (x.smulUpper P).b.μ z = wirtingerQuotient (x.w ∘ P.g) z := by
      change symmExtension (wirtingerQuotient (x.w ∘ P.g)) z = wirtingerQuotient (x.w ∘ P.g) z
      simp only [symmExtension]
      rw [if_pos hzU]
    rw [hμ]
    simp only [wirtingerQuotient]
    by_cases hdz : dz (x.w ∘ P.g) z = 0
    · rw [hdz, mul_zero]
      rw [hdz, norm_zero, mul_zero] at hbelt
      exact norm_le_zero_iff.mp hbelt
    · rw [div_mul_cancel₀ _ hdz]
  obtain ⟨R, hR⟩ := exists_sl2_factorization_of_eq_coeff (x.smulUpper P) hκ hv hcoeff
  exact ⟨R, fun z hz => hR z hz⟩

/-- The boundary maps of two re-marked representatives agree when the original boundary
maps agree: the transition homeomorphism is a Möbius conjugate of a real-fixing map on the
upper half plane, hence fixes the real line. -/
theorem smulUpper_boundary_eq (P : ModGroupUpper Γ₀) (x y : TeichRep Γ₀)
    (hb : ∀ t : ℝ, x.w t = y.w t) :
    ∀ t : ℝ, (x.smulUpper P).w t = (y.smulUpper P).w t := by
  obtain ⟨Rx, hRx⟩ := TeichRep.smulUpper_w x P
  obtain ⟨Ry, hRy⟩ := TeichRep.smulUpper_w y P
  have hu11 : IsHomeomorph (x.smulUpper P).w := (x.smulUpper P).w_isQCAnalytic.1.1
  have hv11 : IsHomeomorph (y.smulUpper P).w := (y.smulUpper P).w_isQCAnalytic.1.1
  have hy11 : IsHomeomorph y.w := y.w_isQCAnalytic.1.1
  set Wu : ℂ ≃ₜ ℂ := hu11.homeomorph (x.smulUpper P).w with hWudef
  set Wv : ℂ ≃ₜ ℂ := hv11.homeomorph (y.smulUpper P).w with hWvdef
  set Wy : ℂ ≃ₜ ℂ := hy11.homeomorph y.w with hWydef
  have hWu_app : ∀ w : ℂ, Wu w = (x.smulUpper P).w w := by
    intro w
    rw [hWudef]
    exact IsHomeomorph.homeomorph_apply _ hu11 w
  have hWv_app : ∀ w : ℂ, Wv w = (y.smulUpper P).w w := by
    intro w
    rw [hWvdef]
    exact IsHomeomorph.homeomorph_apply _ hv11 w
  have hWy_app : ∀ w : ℂ, Wy w = y.w w := by
    intro w
    rw [hWydef]
    exact IsHomeomorph.homeomorph_apply _ hy11 w
  set Λ : ℂ ≃ₜ ℂ := Wv.symm.trans Wu with hΛdef
  have hΛ_app : ∀ w : ℂ, Λ ((y.smulUpper P).w w) = (x.smulUpper P).w w := by
    intro w
    have h1 : Wv.symm ((y.smulUpper P).w w) = w := by
      rw [← hWv_app w]
      exact Wv.symm_apply_apply w
    rw [hΛdef]
    simp only [Homeomorph.trans_apply]
    rw [h1]
    exact hWu_app w
  have hΛ0 : Λ 0 = 0 := by
    have h := hΛ_app 0
    rwa [(y.smulUpper P).w_zero, (x.smulUpper P).w_zero] at h
  have hΛ1 : Λ 1 = 1 := by
    have h := hΛ_app 1
    rwa [(y.smulUpper P).w_one, (x.smulUpper P).w_one] at h
  have hφc : Continuous fun s : ℂ => x.w (Wy.symm s) :=
    (x.w_isQCAnalytic.1.1.continuous).comp Wy.symm.continuous
  have hφr : ∀ r : ℝ, (fun s : ℂ => x.w (Wy.symm s)) (r : ℂ) = (r : ℂ) := by
    intro r
    change x.w (Wy.symm (r : ℂ)) = (r : ℂ)
    have hys : y.w (Wy.symm (r : ℂ)) = (r : ℂ) := by
      rw [← hWy_app]
      exact Wy.apply_symm_apply _
    have hconj : starRingEnd ℂ (Wy.symm (r : ℂ)) = Wy.symm (r : ℂ) := by
      apply y.w_injective
      rw [y.w_conj, hys, Complex.conj_ofReal]
    have him : (Wy.symm (r : ℂ)).im = 0 := Complex.conj_eq_iff_im.mp hconj
    have hre : (((Wy.symm (r : ℂ)).re : ℝ) : ℂ) = Wy.symm (r : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    rw [← hre, hb ((Wy.symm (r : ℂ)).re), hre]
    exact hys
  have hint : ∀ ζ : ℂ, 0 < ζ.im →
      Λ ζ = moebiusMap Rx ((fun s : ℂ => x.w (Wy.symm s)) (moebiusMap Ry⁻¹ ζ)) := by
    intro ζ hζ
    have hvz : (y.smulUpper P).w (Wv.symm ζ) = ζ := by
      rw [← hWv_app (Wv.symm ζ)]
      exact Wv.apply_symm_apply ζ
    have hzpos : 0 < (Wv.symm ζ).im := by
      apply w_im_pos_rev (y.smulUpper P)
      rw [hvz]
      exact hζ
    have hgz : 0 < (P.g (Wv.symm ζ)).im := P.qc.mapsTo _ hzpos
    have hwpos : 0 < (y.w (P.g (Wv.symm ζ))).im := y.w_mapsTo_upper _ hgz
    have hζval : ζ = moebiusMap Ry (y.w (P.g (Wv.symm ζ))) := by
      conv_lhs => rw [← hvz]
      exact hRy _ hzpos
    have hden : moebiusDenom Ry (y.w (P.g (Wv.symm ζ))) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero Ry (ne_of_gt hwpos)
    have hinvζ : moebiusMap Ry⁻¹ ζ = y.w (P.g (Wv.symm ζ)) := by
      conv_lhs => rw [hζval]
      rw [moebiusMap_mul Ry⁻¹ Ry _ hden, inv_mul_cancel, moebiusMap_one]
    have hWyinv : Wy.symm (y.w (P.g (Wv.symm ζ))) = P.g (Wv.symm ζ) := by
      rw [← hWy_app (P.g (Wv.symm ζ))]
      exact Wy.symm_apply_apply _
    have hLHS : Λ ζ = (x.smulUpper P).w (Wv.symm ζ) := by
      rw [hΛdef]
      simp only [Homeomorph.trans_apply]
      exact hWu_app _
    rw [hLHS, hRx _ hzpos]
    change moebiusMap Rx (x.w (P.g (Wv.symm ζ)))
      = moebiusMap Rx (x.w (Wy.symm (moebiusMap Ry⁻¹ ζ)))
    rw [hinvζ, hWyinv]
  have hfix := upper_factor_fix_real Λ hφc hφr Rx Ry hint hΛ0 hΛ1
  intro t
  have h1 : (x.smulUpper P).w (t : ℂ) = Λ ((y.smulUpper P).w (t : ℂ)) := (hΛ_app _).symm
  rw [h1, (y.smulUpper P).w_ofReal t]
  exact hfix ((y.smulUpper P).boundary t)

/-- Re-marking respects inseparability of representatives. -/
theorem smulUpper_mk_congr (P : ModGroupUpper Γ₀) :
    ∀ x y : TeichRep Γ₀, Inseparable x y →
      (Teich.mk (x.smulUpper P) : Teich Γ₀) = Teich.mk (y.smulUpper P) := by
  intro x y hxy
  exact Teich.mk_eq_mk_iff_boundary.mpr
    (smulUpper_boundary_eq P x y (inseparable_iff_boundary_eq.mp hxy))

/-- Upper-half-plane re-markings act on Teichmüller space through coefficients. -/
noncomputable instance : SMul (ModGroupUpper Γ₀) (Teich Γ₀) :=
  ⟨fun P ξ => SeparationQuotient.lift
    (fun x : TeichRep Γ₀ => (Teich.mk (x.smulUpper P) : Teich Γ₀))
    (smulUpper_mk_congr P) ξ⟩

/-- The re-marking action computed on classes of representatives. -/
theorem Teich.smulUpper_mk (P : ModGroupUpper Γ₀) (x : TeichRep Γ₀) :
    P • Teich.mk x = Teich.mk (x.smulUpper P) := by
  rfl

end RiemannDynamics

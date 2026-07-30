/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Extremal
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Coarea.Main

/-!
# Teichmüller's theorem over the Fuchsian base

A Teichmüller-form candidate is uniquely extremal in its marked class: every competing
marked candidate has dilatation at least `(1 + k)/(1 − k)`, the intrinsic distance of the
pair is `½ log ((1 + k)/(1 − k))`, and a competitor achieving it agrees with the candidate
on the upper half plane. The lower bound comes from the Reich–Strebel main inequality
applied to the conjugator `h = G⁻¹ ∘ F` of a competitor with the candidate, followed by
the pointwise Wirtinger algebra in the `q`-frame; the equality case forces the competitor
to solve the same Beltrami equation and the Möbius factor is trivial on three boundary
points. The existence half — every marked class contains a Teichmüller-form candidate — is
recorded as the open input of the campaign.

* `exists_upper_conjugator_of_candidates` — the reduction to a boundary-trivial
  equivariant self-map of the upper half plane.
* `isTeichmullerCandidate_le_dilatation`, `isTeichmullerCandidate_extremal` —
  extremality and the distance formula.
* `isTeichmullerCandidate_unique` — unique extremality on the upper half plane.
* `exists_extremal_unique_upper` — the conditional existence-and-uniqueness statement.
* `teichDistG_teichmullerCoeff`, `teichDistG_teichmullerCoeff_add` — the Teichmüller ray
  through the base point and its geodesic additivity.
* `exists_teichmuller_form` — the recorded existence input.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The reduction to a boundary-trivial equivariant conjugator -/

/-- The pole set of a real Möbius map is a subsingleton. -/
theorem pole_subsingleton (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Set.Subsingleton {u : ℂ | moebiusDenom V u = 0} := by
  intro w₁ hw₁ w₂ hw₂
  have h₁' : (V 1 0 : ℂ) * w₁ + (V 1 1 : ℂ) = 0 := hw₁
  have h₂' : (V 1 0 : ℂ) * w₂ + (V 1 1 : ℂ) = 0 := hw₂
  by_cases hc : V 1 0 = 0
  · exfalso
    have hdet : V 0 0 * V 1 1 - V 0 1 * V 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe V
      rwa [Matrix.det_fin_two] at h
    have hcC : ((V 1 0 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
    rw [hcC, zero_mul, zero_add] at h₁'
    have hd : V 1 1 = 0 := by exact_mod_cast h₁'
    rw [hc, hd] at hdet
    simp at hdet
  · have hcC : ((V 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have hmul : (V 1 0 : ℂ) * w₁ = (V 1 0 : ℂ) * w₂ := by
      linear_combination h₁' - h₂'
    exact mul_left_cancel₀ hcC hmul

/-- A conjugation identity between real Möbius maps intertwined by a continuous map
preserving the upper half plane extends from the open upper half plane to every non-pole
real point, and the image of the real point avoids the pole of the conjugating matrix. -/
theorem conj_boundary {F : ℂ → ℂ} (hfc : Continuous F)
    (hFup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im)
    {γ W : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hconj : ∀ z : ℂ, 0 < z.im → F (moebiusMap γ z) = moebiusMap W (F z))
    (t : ℝ) (ht : moebiusDenom γ (t : ℂ) ≠ 0) :
    moebiusDenom W (F (t : ℂ)) ≠ 0 ∧
      F (moebiusMap γ (t : ℂ)) = moebiusMap W (F (t : ℂ)) := by
  have him0 : ∀ z : ℂ, 0 < z.im → (F z).im ≠ 0 := fun z hz => ne_of_gt (hFup z hz)
  have hTcl : (t : ℂ) ∈ closure {z : ℂ | 0 < z.im} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(t : ℂ) + Complex.I * ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, one_mul, zero_add, mul_zero]
      linarith
    · rw [dist_eq_norm]
      have hsub : (t : ℂ) - ((t : ℂ) + Complex.I * ((ε / 2 : ℝ) : ℂ))
          = -(Complex.I * ((ε / 2 : ℝ) : ℂ)) := by ring
      rw [hsub, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
  have hNB : (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hTcl
  haveI := hNB
  have hLc : ContinuousAt (fun z : ℂ => F (moebiusMap γ z)) (t : ℂ) :=
    hfc.continuousAt.comp (hasDerivAt_moebiusMap γ ht).continuousAt
  have hL : Filter.Tendsto (fun z : ℂ => F (moebiusMap γ z))
      (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds (F (moebiusMap γ (t : ℂ)))) :=
    hLc.continuousWithinAt
  have hEq : (fun z : ℂ => F (moebiusMap γ z))
      =ᶠ[nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}] fun z : ℂ => moebiusMap W (F z) :=
    eventually_nhdsWithin_of_forall fun z hz => hconj z hz
  have hR : Filter.Tendsto (fun z : ℂ => moebiusMap W (F z))
      (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds (F (moebiusMap γ (t : ℂ)))) :=
    Filter.Tendsto.congr' hEq hL
  have hWden : moebiusDenom W (F (t : ℂ)) ≠ 0 := by
    intro h0
    have hdenC : Continuous (moebiusDenom W) := by
      unfold moebiusDenom
      fun_prop
    have hden0 : Filter.Tendsto (fun z : ℂ => moebiusDenom W (F z))
        (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds 0) := by
      have hc : Continuous fun z : ℂ => moebiusDenom W (F z) := hdenC.comp hfc
      have ht0 : Filter.Tendsto (fun z : ℂ => moebiusDenom W (F z))
          (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
          (nhds (moebiusDenom W (F (t : ℂ)))) :=
        (hc.tendsto (t : ℂ)).mono_left nhdsWithin_le_nhds
      rwa [h0] at ht0
    have hnumC : Continuous fun z : ℂ => (W 0 0 : ℂ) * F z + (W 0 1 : ℂ) :=
      (continuous_const.mul hfc).add continuous_const
    have hnum : Filter.Tendsto (fun z : ℂ => (W 0 0 : ℂ) * F z + (W 0 1 : ℂ))
        (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
        (nhds ((W 0 0 : ℂ) * F (t : ℂ) + (W 0 1 : ℂ))) :=
      (hnumC.tendsto (t : ℂ)).mono_left nhdsWithin_le_nhds
    have hEq2 : (fun z : ℂ => moebiusMap W (F z) * moebiusDenom W (F z))
        =ᶠ[nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}]
          fun z : ℂ => (W 0 0 : ℂ) * F z + (W 0 1 : ℂ) :=
      eventually_nhdsWithin_of_forall fun z hz => by
        have hdz : moebiusDenom W (F z) ≠ 0 :=
          moebiusDenom_ne_zero_of_im_ne_zero W (him0 z hz)
        simp only [moebiusMap]
        exact div_mul_cancel₀ _ hdz
    have hnum' : Filter.Tendsto (fun z : ℂ => (W 0 0 : ℂ) * F z + (W 0 1 : ℂ))
        (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
        (nhds (F (moebiusMap γ (t : ℂ)) * 0)) :=
      Filter.Tendsto.congr' hEq2 (hR.mul hden0)
    have hlim := tendsto_nhds_unique hnum hnum'
    rw [mul_zero] at hlim
    have hdet : W 0 0 * W 1 1 - W 0 1 * W 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe W
      rwa [Matrix.det_fin_two] at h
    have hdetC : (W 0 0 : ℂ) * (W 1 1 : ℂ) - (W 0 1 : ℂ) * (W 1 0 : ℂ) = 1 := by
      exact_mod_cast hdet
    have h0' : (W 1 0 : ℂ) * F (t : ℂ) + (W 1 1 : ℂ) = 0 := h0
    have hcontra : (1 : ℂ) = 0 := by
      linear_combination (W 0 0 : ℂ) * h0' - (W 1 0 : ℂ) * hlim - hdetC
    exact one_ne_zero hcontra
  have hRc : ContinuousAt (fun z : ℂ => moebiusMap W (F z)) (t : ℂ) :=
    (hasDerivAt_moebiusMap W hWden).continuousAt.comp hfc.continuousAt
  have hR2 : Filter.Tendsto (fun z : ℂ => moebiusMap W (F z))
      (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im}) (nhds (moebiusMap W (F (t : ℂ)))) :=
    hRc.continuousWithinAt
  exact ⟨hWden, tendsto_nhds_unique hR hR2⟩

/-- **The conjugator of two marked candidates**: two quasiconformal marked candidates of a
pair induce the same boundary transition and the same boundary-determined group
correspondence, so `h = G⁻¹ ∘ F` restricts to an upper-half-plane quasiconformal map
commuting with the domain group elementwise, with boundary limits the identity on `ℝ`, and
with `F = G ∘ h` on the upper half plane. -/
theorem exists_upper_conjugator_of_candidates {x y : TeichRep Γ₀} {F G : ℂ → ℂ}
    {K₀ K : ℝ} (hF : IsQCGeometric F K₀) (hFc : IsMarkedCandidate x y F)
    (hG : IsQCGeometric G K) (hGc : IsMarkedCandidate x y G) :
    ∃ (h hinv : ℂ → ℂ) (κ : ℝ), 0 ≤ κ ∧ κ < 1 ∧ IsQCUpper h hinv κ ∧
      (∀ γ ∈ y.group, ∀ z : ℂ, 0 < z.im → h (moebiusMap γ z) = moebiusMap γ (h z)) ∧
      (∀ t : ℝ, Filter.Tendsto h (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
        (nhds (t : ℂ))) ∧
      (∀ z : ℂ, 0 < z.im → F z = G (h z)) := by
  classical
  -- the two-sided inverse of the competitor
  set Ginv : ℂ → ℂ := ⇑(hG.2.1.isHomeomorph.homeomorph G).symm with hGinvdef
  have hGinvqc : IsQCGeometric Ginv K := isQCGeometric_inv_of_isQCGeometric hG
  have happG : ∀ z : ℂ, (hG.2.1.isHomeomorph.homeomorph G) z = G z := fun z =>
    IsHomeomorph.homeomorph_apply G hG.2.1.isHomeomorph z
  have hGiG : ∀ z : ℂ, Ginv (G z) = z := by
    intro z
    rw [← happG z]
    exact Homeomorph.symm_apply_apply _ z
  have hGGi : ∀ z : ℂ, G (Ginv z) = z := by
    intro z
    rw [← happG (Ginv z)]
    exact (hG.2.1.isHomeomorph.homeomorph G).apply_symm_apply z
  have hGinvb : ∀ t : ℝ, Ginv (x.w t) = y.w t := by
    intro t
    rw [← hGc.1 t]
    exact hGiG (y.w t)
  have hGinvup : ∀ z : ℂ, 0 < z.im → 0 < (Ginv z).im :=
    isMarkedCandidate_mapsTo_upper hGinvqc hGinvb
  have hFup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im :=
    isMarkedCandidate_mapsTo_upper hF hFc.1
  -- the conjugator, its dilatation, and its two-sided inverse
  set H : ℂ → ℂ := Ginv ∘ F with hHdef
  have hHqc : IsQCGeometric H (K * K₀) := hGinvqc.comp hF
  have hKH : 1 ≤ K * K₀ := hHqc.1
  have hHcont : Continuous H := hHqc.2.1.isHomeomorph.continuous
  -- the conjugator fixes the real line pointwise
  have hRfix : ∀ s : ℝ, H (s : ℂ) = (s : ℂ) := by
    intro s
    obtain ⟨t, ht⟩ := y.boundary_surjective s
    have hyw : y.w (t : ℂ) = (s : ℂ) := by rw [y.w_ofReal t, ht]
    change Ginv (F (s : ℂ)) = (s : ℂ)
    rw [← hyw, hFc.1 t, ← hGc.1 t, hGiG]
  have hbyw : ∀ t : ℝ, H (y.w t) = y.w t := by
    intro t
    rw [y.w_ofReal t]
    exact hRfix (y.boundary t)
  have hHup : ∀ z : ℂ, 0 < z.im → 0 < (H z).im :=
    isMarkedCandidate_mapsTo_upper hHqc hbyw
  set Hinv : ℂ → ℂ := ⇑(hHqc.2.1.isHomeomorph.homeomorph H).symm with hHinvdef
  have hHinvqc : IsQCGeometric Hinv (K * K₀) := isQCGeometric_inv_of_isQCGeometric hHqc
  have happH : ∀ z : ℂ, (hHqc.2.1.isHomeomorph.homeomorph H) z = H z := fun z =>
    IsHomeomorph.homeomorph_apply H hHqc.2.1.isHomeomorph z
  have hHiH : ∀ z : ℂ, Hinv (H z) = z := by
    intro z
    rw [← happH z]
    exact Homeomorph.symm_apply_apply _ z
  have hHHi : ∀ z : ℂ, H (Hinv z) = z := by
    intro z
    rw [← happH (Hinv z)]
    exact (hHqc.2.1.isHomeomorph.homeomorph H).apply_symm_apply z
  have hHinvb : ∀ t : ℝ, Hinv (y.w t) = y.w t := by
    intro t
    have h1 := hHiH (y.w t)
    rwa [hbyw t] at h1
  have hHinvup : ∀ z : ℂ, 0 < z.im → 0 < (Hinv z).im :=
    isMarkedCandidate_mapsTo_upper hHinvqc hHinvb
  -- the conjugator intertwines the domain group with itself through the candidates
  have hconjH : ∀ γ ∈ y.group, ∃ δ ∈ y.group,
      ∀ z : ℂ, 0 < z.im → H (moebiusMap γ z) = moebiusMap δ (H z) := by
    intro γ hγ
    obtain ⟨W', hW', hFconj⟩ := hFc.2.1 γ hγ
    obtain ⟨δ, hδ, hGconj⟩ := hGc.2.2 W' hW'
    have hGinvconj : ∀ z : ℂ, 0 < z.im →
        Ginv (moebiusMap W' z) = moebiusMap δ (Ginv z) :=
      inv_conj_of_conj hGinvup (fun z _ => hGiG z) (fun z _ => hGGi z) hGconj
    refine ⟨δ, hδ, fun z hz => ?_⟩
    change Ginv (F (moebiusMap γ z)) = moebiusMap δ (Ginv (F z))
    rw [hFconj z hz]
    exact hGinvconj (F z) (hFup z hz)
  -- boundary pinning upgrades the intertwining witness to the group element itself
  have hequiv : ∀ γ ∈ y.group, ∀ z : ℂ, 0 < z.im →
      H (moebiusMap γ z) = moebiusMap γ (H z) := by
    intro γ hγ
    obtain ⟨δ, hδ, hHc⟩ := hconjH γ hγ
    have hB1 : ({s : ℝ | moebiusDenom γ (s : ℂ) = 0}).Finite :=
      Set.Subsingleton.finite ((pole_subsingleton γ).preimage Complex.ofReal_injective)
    have hBc := hB1.infinite_compl
    obtain ⟨t₁, ht₁⟩ := hBc.nonempty
    obtain ⟨t₂, ht₂⟩ := (hBc.diff (Set.finite_singleton t₁)).nonempty
    obtain ⟨t₃, ht₃⟩ := (hBc.diff ((Set.finite_singleton t₂).insert t₁)).nonempty
    have hd1 : moebiusDenom γ (t₁ : ℂ) ≠ 0 := ht₁
    have hd2 : moebiusDenom γ (t₂ : ℂ) ≠ 0 := ht₂.1
    have hd3 : moebiusDenom γ (t₃ : ℂ) ≠ 0 := ht₃.1
    have ht21 : t₂ ≠ t₁ := fun hEq => ht₂.2 hEq
    have ht31 : t₃ ≠ t₁ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inl hEq))
    have ht32 : t₃ ≠ t₂ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inr hEq))
    have key : ∀ s : ℝ, moebiusDenom γ (s : ℂ) ≠ 0 →
        moebiusDenom δ (s : ℂ) ≠ 0 ∧ moebiusMap γ (s : ℂ) = moebiusMap δ (s : ℂ) := by
      intro s hs
      obtain ⟨hden, hval⟩ := conj_boundary hHcont hHup hHc s hs
      rw [hRfix s] at hden hval
      have hreal : (moebiusMap γ (s : ℂ)).im = 0 :=
        moebiusMap_im_eq_zero γ (by simp) hs
      have hfixed : H (moebiusMap γ (s : ℂ)) = moebiusMap γ (s : ℂ) := by
        rw [eq_ofReal_of_im_eq_zero hreal]
        exact hRfix _
      exact ⟨hden, hfixed.symm.trans hval⟩
    obtain ⟨hδ1, hag1⟩ := key t₁ hd1
    obtain ⟨hδ2, hag2⟩ := key t₂ hd2
    obtain ⟨hδ3, hag3⟩ := key t₃ hd3
    have hz12 : ((t₁ : ℝ) : ℂ) ≠ ((t₂ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht21.symm
    have hz13 : ((t₁ : ℝ) : ℂ) ≠ ((t₃ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht31.symm
    have hz23 : ((t₂ : ℝ) : ℂ) ≠ ((t₃ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht32.symm
    have hVden : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
        moebiusDenom γ u ≠ 0 := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hd1
      · exact hd2
      · exact hd3
    have hWden : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
        moebiusDenom δ u ≠ 0 := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hδ1
      · exact hδ2
      · exact hδ3
    have hagree : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
        moebiusMap γ u = moebiusMap δ u := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hag1
      · exact hag2
      · exact hag3
    have hcase := moebius_ext_three hz12 hz13 hz23 hVden hWden hagree
    have hmapeq : ∀ u : ℂ, moebiusMap γ u = moebiusMap δ u := by
      rcases hcase with heq | hneg
      · intro u
        rw [Subtype.ext heq]
      · exact fun u => moebiusMap_neg_matrix hneg u
    intro z hz
    rw [hHc z hz]
    exact (hmapeq (H z)).symm
  -- the analytic layer of the conjugator and the Beltrami bound
  obtain ⟨b, hbnd, hQCA⟩ := isQCAnalytic_of_isQCGeometric hHqc.1 hHqc
  refine ⟨H, Hinv, (K * K₀ - 1) / (K * K₀ + 1), ?_, ?_, ?_, hequiv, ?_, ?_⟩
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith
  · refine ⟨hHup, hHinvup, fun z _ => hHiH z, fun z _ => hHHi z,
      hHcont.continuousOn, hHinvqc.2.1.isHomeomorph.continuous.continuousOn,
      MemWklocP.mono hQCA.2.1 (Set.subset_univ _), ae_restrict_of_ae hQCA.1.2, ?_⟩
    have hbw_ae : ∀ᵐ w : ℂ, ‖b.μ w‖ ≤ b.normInf := by
      filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with w hw
      have h2 := ENNReal.toReal_mono (ne_top_of_lt b.bound) hw
      simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
    refine ae_restrict_of_ae ?_
    filter_upwards [hQCA.2.2, hbw_ae] with z hbel hbw
    calc ‖dzbar H z‖ = ‖b.μ z‖ * ‖dz H z‖ := by rw [hbel, norm_mul]
      _ ≤ b.normInf * ‖dz H z‖ := mul_le_mul_of_nonneg_right hbw (norm_nonneg _)
      _ ≤ (K * K₀ - 1) / (K * K₀ + 1) * ‖dz H z‖ :=
          mul_le_mul_of_nonneg_right hbnd (norm_nonneg _)
  · intro t
    have h1 : Filter.Tendsto H (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
        (nhds (H (t : ℂ))) :=
      (hHcont.tendsto (t : ℂ)).mono_left nhdsWithin_le_nhds
    rwa [hRfix t] at h1
  · intro z hz
    change F z = G (Ginv (F z))
    rw [hGGi (F z)]

/-! ## Extremality of Teichmüller-form candidates -/

/-- **The conjugator of two marked candidates, with plane-level data**: the boundary-trivial
equivariant upper-half-plane conjugator of two quasiconformal marked candidates, exported
together with its global geometric dilatation bound, its global two-sided inverse, and its
pointwise fixing of the real axis. -/
theorem exists_upper_conjugator_of_candidates₂ {x y : TeichRep Γ₀} {F G : ℂ → ℂ}
    {K₀ K : ℝ} (hF : IsQCGeometric F K₀) (hFc : IsMarkedCandidate x y F)
    (hG : IsQCGeometric G K) (hGc : IsMarkedCandidate x y G) :
    ∃ (h hinv : ℂ → ℂ) (κ : ℝ), 0 ≤ κ ∧ κ < 1 ∧ IsQCUpper h hinv κ ∧
      (∀ γ ∈ y.group, ∀ z : ℂ, 0 < z.im → h (moebiusMap γ z) = moebiusMap γ (h z)) ∧
      (∀ t : ℝ, Filter.Tendsto h (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
        (nhds (t : ℂ))) ∧
      (∀ z : ℂ, 0 < z.im → F z = G (h z)) ∧
      IsQCGeometric h (K * K₀) ∧
      (∀ z : ℂ, hinv (h z) = z) ∧ (∀ z : ℂ, h (hinv z) = z) ∧
      (∀ s : ℝ, h (s : ℂ) = (s : ℂ)) := by
  classical
  -- the two-sided inverse of the competitor
  set Ginv : ℂ → ℂ := ⇑(hG.2.1.isHomeomorph.homeomorph G).symm with hGinvdef
  have hGinvqc : IsQCGeometric Ginv K := isQCGeometric_inv_of_isQCGeometric hG
  have happG : ∀ z : ℂ, (hG.2.1.isHomeomorph.homeomorph G) z = G z := fun z =>
    IsHomeomorph.homeomorph_apply G hG.2.1.isHomeomorph z
  have hGiG : ∀ z : ℂ, Ginv (G z) = z := by
    intro z
    rw [← happG z]
    exact Homeomorph.symm_apply_apply _ z
  have hGGi : ∀ z : ℂ, G (Ginv z) = z := by
    intro z
    rw [← happG (Ginv z)]
    exact (hG.2.1.isHomeomorph.homeomorph G).apply_symm_apply z
  have hGinvb : ∀ t : ℝ, Ginv (x.w t) = y.w t := by
    intro t
    rw [← hGc.1 t]
    exact hGiG (y.w t)
  have hGinvup : ∀ z : ℂ, 0 < z.im → 0 < (Ginv z).im :=
    isMarkedCandidate_mapsTo_upper hGinvqc hGinvb
  have hFup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im :=
    isMarkedCandidate_mapsTo_upper hF hFc.1
  -- the conjugator, its dilatation, and its two-sided inverse
  set H : ℂ → ℂ := Ginv ∘ F with hHdef
  have hHqc : IsQCGeometric H (K * K₀) := hGinvqc.comp hF
  have hKH : 1 ≤ K * K₀ := hHqc.1
  have hHcont : Continuous H := hHqc.2.1.isHomeomorph.continuous
  -- the conjugator fixes the real line pointwise
  have hRfix : ∀ s : ℝ, H (s : ℂ) = (s : ℂ) := by
    intro s
    obtain ⟨t, ht⟩ := y.boundary_surjective s
    have hyw : y.w (t : ℂ) = (s : ℂ) := by rw [y.w_ofReal t, ht]
    change Ginv (F (s : ℂ)) = (s : ℂ)
    rw [← hyw, hFc.1 t, ← hGc.1 t, hGiG]
  have hbyw : ∀ t : ℝ, H (y.w t) = y.w t := by
    intro t
    rw [y.w_ofReal t]
    exact hRfix (y.boundary t)
  have hHup : ∀ z : ℂ, 0 < z.im → 0 < (H z).im :=
    isMarkedCandidate_mapsTo_upper hHqc hbyw
  set Hinv : ℂ → ℂ := ⇑(hHqc.2.1.isHomeomorph.homeomorph H).symm with hHinvdef
  have hHinvqc : IsQCGeometric Hinv (K * K₀) := isQCGeometric_inv_of_isQCGeometric hHqc
  have happH : ∀ z : ℂ, (hHqc.2.1.isHomeomorph.homeomorph H) z = H z := fun z =>
    IsHomeomorph.homeomorph_apply H hHqc.2.1.isHomeomorph z
  have hHiH : ∀ z : ℂ, Hinv (H z) = z := by
    intro z
    rw [← happH z]
    exact Homeomorph.symm_apply_apply _ z
  have hHHi : ∀ z : ℂ, H (Hinv z) = z := by
    intro z
    rw [← happH (Hinv z)]
    exact (hHqc.2.1.isHomeomorph.homeomorph H).apply_symm_apply z
  have hHinvb : ∀ t : ℝ, Hinv (y.w t) = y.w t := by
    intro t
    have h1 := hHiH (y.w t)
    rwa [hbyw t] at h1
  have hHinvup : ∀ z : ℂ, 0 < z.im → 0 < (Hinv z).im :=
    isMarkedCandidate_mapsTo_upper hHinvqc hHinvb
  -- the conjugator intertwines the domain group with itself through the candidates
  have hconjH : ∀ γ ∈ y.group, ∃ δ ∈ y.group,
      ∀ z : ℂ, 0 < z.im → H (moebiusMap γ z) = moebiusMap δ (H z) := by
    intro γ hγ
    obtain ⟨W', hW', hFconj⟩ := hFc.2.1 γ hγ
    obtain ⟨δ, hδ, hGconj⟩ := hGc.2.2 W' hW'
    have hGinvconj : ∀ z : ℂ, 0 < z.im →
        Ginv (moebiusMap W' z) = moebiusMap δ (Ginv z) :=
      inv_conj_of_conj hGinvup (fun z _ => hGiG z) (fun z _ => hGGi z) hGconj
    refine ⟨δ, hδ, fun z hz => ?_⟩
    change Ginv (F (moebiusMap γ z)) = moebiusMap δ (Ginv (F z))
    rw [hFconj z hz]
    exact hGinvconj (F z) (hFup z hz)
  -- boundary pinning upgrades the intertwining witness to the group element itself
  have hequiv : ∀ γ ∈ y.group, ∀ z : ℂ, 0 < z.im →
      H (moebiusMap γ z) = moebiusMap γ (H z) := by
    intro γ hγ
    obtain ⟨δ, hδ, hHc⟩ := hconjH γ hγ
    have hB1 : ({s : ℝ | moebiusDenom γ (s : ℂ) = 0}).Finite :=
      Set.Subsingleton.finite ((pole_subsingleton γ).preimage Complex.ofReal_injective)
    have hBc := hB1.infinite_compl
    obtain ⟨t₁, ht₁⟩ := hBc.nonempty
    obtain ⟨t₂, ht₂⟩ := (hBc.diff (Set.finite_singleton t₁)).nonempty
    obtain ⟨t₃, ht₃⟩ := (hBc.diff ((Set.finite_singleton t₂).insert t₁)).nonempty
    have hd1 : moebiusDenom γ (t₁ : ℂ) ≠ 0 := ht₁
    have hd2 : moebiusDenom γ (t₂ : ℂ) ≠ 0 := ht₂.1
    have hd3 : moebiusDenom γ (t₃ : ℂ) ≠ 0 := ht₃.1
    have ht21 : t₂ ≠ t₁ := fun hEq => ht₂.2 hEq
    have ht31 : t₃ ≠ t₁ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inl hEq))
    have ht32 : t₃ ≠ t₂ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inr hEq))
    have key : ∀ s : ℝ, moebiusDenom γ (s : ℂ) ≠ 0 →
        moebiusDenom δ (s : ℂ) ≠ 0 ∧ moebiusMap γ (s : ℂ) = moebiusMap δ (s : ℂ) := by
      intro s hs
      obtain ⟨hden, hval⟩ := conj_boundary hHcont hHup hHc s hs
      rw [hRfix s] at hden hval
      have hreal : (moebiusMap γ (s : ℂ)).im = 0 :=
        moebiusMap_im_eq_zero γ (by simp) hs
      have hfixed : H (moebiusMap γ (s : ℂ)) = moebiusMap γ (s : ℂ) := by
        rw [eq_ofReal_of_im_eq_zero hreal]
        exact hRfix _
      exact ⟨hden, hfixed.symm.trans hval⟩
    obtain ⟨hδ1, hag1⟩ := key t₁ hd1
    obtain ⟨hδ2, hag2⟩ := key t₂ hd2
    obtain ⟨hδ3, hag3⟩ := key t₃ hd3
    have hz12 : ((t₁ : ℝ) : ℂ) ≠ ((t₂ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht21.symm
    have hz13 : ((t₁ : ℝ) : ℂ) ≠ ((t₃ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht31.symm
    have hz23 : ((t₂ : ℝ) : ℂ) ≠ ((t₃ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht32.symm
    have hVden : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
        moebiusDenom γ u ≠ 0 := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hd1
      · exact hd2
      · exact hd3
    have hWden : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
        moebiusDenom δ u ≠ 0 := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hδ1
      · exact hδ2
      · exact hδ3
    have hagree : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
        moebiusMap γ u = moebiusMap δ u := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hag1
      · exact hag2
      · exact hag3
    have hcase := moebius_ext_three hz12 hz13 hz23 hVden hWden hagree
    have hmapeq : ∀ u : ℂ, moebiusMap γ u = moebiusMap δ u := by
      rcases hcase with heq | hneg
      · intro u
        rw [Subtype.ext heq]
      · exact fun u => moebiusMap_neg_matrix hneg u
    intro z hz
    rw [hHc z hz]
    exact (hmapeq (H z)).symm
  -- the analytic layer of the conjugator and the Beltrami bound
  obtain ⟨b, hbnd, hQCA⟩ := isQCAnalytic_of_isQCGeometric hHqc.1 hHqc
  refine ⟨H, Hinv, (K * K₀ - 1) / (K * K₀ + 1), ?_, ?_, ?_, hequiv, ?_, ?_,
    hHqc, hHiH, hHHi, hRfix⟩
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith
  · refine ⟨hHup, hHinvup, fun z _ => hHiH z, fun z _ => hHHi z,
      hHcont.continuousOn, hHinvqc.2.1.isHomeomorph.continuous.continuousOn,
      MemWklocP.mono hQCA.2.1 (Set.subset_univ _), ae_restrict_of_ae hQCA.1.2, ?_⟩
    have hbw_ae : ∀ᵐ w : ℂ, ‖b.μ w‖ ≤ b.normInf := by
      filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with w hw
      have h2 := ENNReal.toReal_mono (ne_top_of_lt b.bound) hw
      simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
    refine ae_restrict_of_ae ?_
    filter_upwards [hQCA.2.2, hbw_ae] with z hbel hbw
    calc ‖dzbar H z‖ = ‖b.μ z‖ * ‖dz H z‖ := by rw [hbel, norm_mul]
      _ ≤ b.normInf * ‖dz H z‖ := mul_le_mul_of_nonneg_right hbw (norm_nonneg _)
      _ ≤ (K * K₀ - 1) / (K * K₀ + 1) * ‖dz H z‖ :=
          mul_le_mul_of_nonneg_right hbnd (norm_nonneg _)
  · intro t
    have h1 : Filter.Tendsto H (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
        (nhds (H (t : ℂ))) :=
      (hHcont.tendsto (t : ℂ)).mono_left nhdsWithin_le_nhds
    rwa [hRfix t] at h1
  · intro z hz
    change F z = G (Ginv (F z))
    rw [hGGi (F z)]

set_option maxHeartbeats 400000 in
-- Heartbeats: the conjugated Reich–Strebel application carries a deep local tower.
/-- **The Teichmüller lower bound**: every dilatation of a marked candidate of the pair is
at least `(1 + k)/(1 − k)`; the Reich–Strebel main inequality for the conjugator of the
competitor with the Teichmüller-form candidate, with the pointwise Wirtinger identities in
the `q`-frame, gives `‖q‖₁ ≤ (K' (1 − k)/(1 + k)) ‖q‖₁` with `0 < ‖q‖₁ < ∞`. -/
theorem isTeichmullerCandidate_le_dilatation (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {q : QuadraticDifferential y.group} {k : ℝ} {F : ℂ → ℂ}
    (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsTeichmullerCandidate x y q k F) :
    ∀ K' ∈ gDilatationSet x y, (1 + k) / (1 - k) ≤ K' := by
  intro K' hK'
  obtain ⟨G, hGqc, hGc⟩ := hK'
  obtain ⟨hFc, hFqc, hFbel⟩ := hF
  have hK'1 : 1 ≤ K' := hGqc.1
  -- the group transports to the marked base of `q`
  have hΓy : IsFuchsianGroup y.group := TeichRep.isFuchsian_group hΓ₀ hfree y
  have hfreey := TeichRep.group_free hfree y
  have hccy := TeichRep.group_cocompact hcc y
  -- the boundary-trivial equivariant conjugator with its plane-level data
  obtain ⟨H, Hinv, κ, hκ0, hκ1, hHqc, hequiv, hbd, hFGH, hHgeo, hHiH, hHHi, hRfix⟩ :=
    exists_upper_conjugator_of_candidates₂ hFqc hFc hGqc hGc
  -- the Reich–Strebel main inequality for the conjugator
  have hRS := reich_strebel_main_inequality hΓy hfreey hccy q hκ1 hHqc hbd hequiv
  -- the competitor coefficient bound
  set c₀ : ℝ := (K' - 1) / (K' + 1) with hc₀def
  have hc₀0 : 0 ≤ c₀ := div_nonneg (by linarith) (by linarith)
  have hc₀1 : c₀ < 1 := by
    rw [hc₀def, div_lt_one (by linarith)]
    linarith
  -- the analytic layer of the competitor and its almost-everywhere package
  obtain ⟨bG, hbGn, hGA⟩ := isQCAnalytic_of_isQCGeometric hGqc.1 hGqc
  have hbw_ae : ∀ᵐ w : ℂ, ‖bG.μ w‖ ≤ bG.normInf := by
    filter_upwards [enorm_ae_le_eLpNormEssSup bG.μ volume] with w hw
    have h2 := ENNReal.toReal_mono (ne_top_of_lt bG.bound) hw
    simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
  have hGgood : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w ∧ dzbar G w = bG.μ w * dz G w ∧
      ‖bG.μ w‖ ≤ c₀ ∧ 0 < (fderiv ℝ G w).det := by
    filter_upwards [hGA.ae_differentiableAt, hGA.2.2, hbw_ae, hGA.1.2] with w h1 h2 h3 h4
    exact ⟨h1, h2, le_trans h3 hbGn, h4⟩
  -- the pullback of the package along the conjugator
  set N : Set ℂ := {w : ℂ | ¬ (DifferentiableAt ℝ G w ∧ dzbar G w = bG.μ w * dz G w ∧
      ‖bG.μ w‖ ≤ c₀ ∧ 0 < (fderiv ℝ G w).det)} with hNdef
  have hNnull : volume N = 0 := ae_iff.mp hGgood
  have hHpull : ∀ᵐ z : ℂ, H z ∉ N := preimage_conull hHgeo hNnull
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} := hUopen.measurableSet
  -- the almost-everywhere pointwise weight bound on the upper half plane
  have hptwise : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient H z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient H z‖ ^ 2))
      ≤ ‖q z‖ₑ * ENNReal.ofReal ((1 - k) / (1 + k) * ((1 + c₀) / (1 - c₀))) := by
    filter_upwards [q.ae_ne_zero hq0, hFbel, ae_restrict_of_ae hHpull,
      ae_differentiableAt hHqc, hHqc.jac, ae_qc_facts hHqc, ae_restrict_mem hUm]
      with z hqz hzbel hzN hzdiff hzjac hzfacts hzU
    simp only [hNdef, Set.mem_setOf_eq, not_not] at hzN
    obtain ⟨hGdiff, hGbel, hGbnd, hGjac⟩ := hzN
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    -- the frame at the point
    set θz : ℂ := q z / (‖q z‖ : ℂ) with hθzdef
    set α : ℂ := dz H z with hαdef
    set β : ℂ := dzbar H z with hβdef
    set p : ℂ := dz G (H z) with hpdef
    set b' : ℂ := dzbar G (H z) with hb'def
    have hqn0 : ‖q z‖ ≠ 0 := norm_ne_zero_iff.mpr hqz
    have hθ1 : ‖θz‖ = 1 := by
      rw [hθzdef, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self hqn0]
    have hθprod : θz * starRingEnd ℂ θz = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ1]
      norm_num
    -- the candidate coefficient is the aligned phase
    have htc : teichmullerCoeffFun (q : ℂ → ℂ) k z = (k : ℂ) * starRingEnd ℂ θz := by
      simp only [teichmullerCoeffFun, hθzdef, map_div₀, Complex.conj_ofReal,
        Complex.ofReal_inv]
      ring
    -- the chain rule of the factorization through the competitor
    have hev : F =ᶠ[nhds z] fun w => G (H w) :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hzU) fun w hw => hFGH w hw
    have hfeq : fderiv ℝ F z = fderiv ℝ (fun w => G (H w)) z := hev.fderiv_eq
    have hcomp1 : dz F z = p * α + b' * starRingEnd ℂ β := by
      rw [dz, hfeq, ← dz, dz_comp hzdiff hGdiff]
    have hcomp2 : dzbar F z = p * β + b' * starRingEnd ℂ α := by
      rw [dzbar, hfeq, ← dzbar, dzbar_comp hzdiff hGdiff]
    -- the pivot identity of the frame
    have hFrame : p * (β - (k : ℂ) * starRingEnd ℂ θz * α)
        = -(b' * starRingEnd ℂ (α - (k : ℂ) * θz * β)) := by
      have h1 := hzbel
      rw [hcomp1, hcomp2, htc] at h1
      simp only [map_sub, map_mul, Complex.conj_ofReal]
      linear_combination h1
    -- the geometric data of the frame
    have hα0 : α ≠ 0 := hzfacts.1
    have hjacr : ‖β‖ < ‖α‖ := by
      have h2 := hzjac
      rw [det_fderiv_eq_wirtinger] at h2
      nlinarith [norm_nonneg (dz H z), norm_nonneg (dzbar H z)]
    have hp0 : p ≠ 0 := by
      have h3 := hGjac
      rw [det_fderiv_eq_wirtinger] at h3
      intro h4
      rw [hpdef] at h4
      rw [h4, norm_zero] at h3
      nlinarith [sq_nonneg ‖dzbar G (H z)‖]
    have hbb : ‖b'‖ ≤ c₀ * ‖p‖ := by
      have h5 : dzbar G (H z) = bG.μ (H z) * dz G (H z) := hGbel
      change ‖dzbar G (H z)‖ ≤ c₀ * ‖dz G (H z)‖
      rw [h5, norm_mul]
      exact mul_le_mul_of_nonneg_right hGbnd (norm_nonneg _)
    have hkey := rs_weight_pointwise hk0 hk1 hc₀0 hc₀1 hθprod hjacr hp0 hbb hFrame
    -- conversion to the Wirtinger-quotient form
    have hwq : wirtingerQuotient H z = β / α := rfl
    have hnα : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα0
    have hJne : ‖α‖ ^ 2 - ‖β‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg (dzbar H z)]
    have hratio : ‖1 - wirtingerQuotient H z * θz‖ ^ 2
        / (1 - ‖wirtingerQuotient H z‖ ^ 2)
        = ‖α - θz * β‖ ^ 2 / (‖α‖ ^ 2 - ‖β‖ ^ 2) := by
      rw [hwq]
      have h5 : (1 : ℂ) - β / α * θz = (α - θz * β) / α := by
        field_simp
      rw [h5, norm_div, div_pow, norm_div, div_pow]
      have hden2 : (1 : ℝ) - (‖β‖ / ‖α‖) ^ 2 ≠ 0 := by
        have h6 : ‖β‖ / ‖α‖ < 1 := (div_lt_one (norm_pos_iff.mpr hα0)).mpr hjacr
        have h7 : 0 ≤ ‖β‖ / ‖α‖ := by positivity
        nlinarith
      field_simp
    rw [hratio]
    exact hkey
  -- integration over the Dirichlet domain and the mass cancellation
  set C : ℝ≥0∞ := ENNReal.ofReal ((1 - k) / (1 + k) * ((1 + c₀) / (1 - c₀))) with hCdef
  set D : Set ℂ := UpperHalfPlane.coe '' dirichletDomain y.group UpperHalfPlane.I
    with hDdef
  have hDsub : D ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hbound2 : (∫⁻ z in D, ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient H z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient H z‖ ^ 2)))
      ≤ ∫⁻ z in D, ‖q z‖ₑ * C :=
    lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset hDsub hptwise)
  have hconst : (∫⁻ z in D, ‖q z‖ₑ * C) = q.l1Norm * C := by
    rw [lintegral_mul_const C q.measurable.enorm]
    rfl
  have hchain2 : q.l1Norm ≤ q.l1Norm * C :=
    le_trans hRS (le_trans hbound2 (le_of_eq hconst))
  have hpos := l1Norm_pos hΓy hfreey hccy q hq0
  have hfin := q.l1Norm_ne_top hΓy hfreey hccy
  have h1C : 1 ≤ C := by
    nth_rewrite 1 [← mul_one q.l1Norm] at hchain2
    exact (ENNReal.mul_le_mul_iff_right hpos.ne' hfin).mp hchain2
  have h1Cr : 1 ≤ (1 - k) / (1 + k) * ((1 + c₀) / (1 - c₀)) :=
    ENNReal.one_le_ofReal.mp h1C
  have hCK : (1 + c₀) / (1 - c₀) = K' := by
    have hK1 : K' + 1 ≠ 0 := by linarith
    have h8 : (1 : ℝ) - (K' - 1) / (K' + 1) = 2 / (K' + 1) := by
      field_simp
      ring
    have h9 : (1 : ℝ) + (K' - 1) / (K' + 1) = 2 * K' / (K' + 1) := by
      field_simp
      ring
    rw [hc₀def, h9, h8, div_eq_iff (div_ne_zero two_ne_zero hK1)]
    field_simp
  rw [hCK] at h1Cr
  have h2 : (1 + k) * ((1 - k) / (1 + k) * K') = (1 - k) * K' := by
    have hk1p : (1 : ℝ) + k ≠ 0 := by linarith
    field_simp
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - k)]
  nlinarith [h1Cr, h2]

/-- **Teichmüller extremality and the distance formula**: a Teichmüller-form candidate
realizes the intrinsic distance, which equals `½ log ((1 + k)/(1 − k))`. -/
theorem isTeichmullerCandidate_extremal (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {q : QuadraticDifferential y.group} {k : ℝ} {F : ℂ → ℂ}
    (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsTeichmullerCandidate x y q k F) :
    (∀ K' ∈ gDilatationSet x y, (1 + k) / (1 - k) ≤ K') ∧
    teichDistG x y = (1 / 2) * Real.log ((1 + k) / (1 - k)) := by
  have hlb := isTeichmullerCandidate_le_dilatation hΓ₀ hfree hcc hq0 hk0 hk1 hF
  refine ⟨hlb, ?_⟩
  have hmem : (1 + k) / (1 - k) ∈ gDilatationSet x y := ⟨F, hF.2.1, hF.1⟩
  have hsinf : sInf (gDilatationSet x y) = (1 + k) / (1 - k) :=
    le_antisymm (csInf_le (bddBelow_gDilatationSet x y) hmem)
      (le_csInf ⟨_, hmem⟩ hlb)
  unfold teichDistG
  rw [hsinf]

/-- **Conformal rigidity of a boundary-fixing conjugator**: an upper-half-plane
quasiconformal map, continuous on the plane, fixing the real axis pointwise, with
`∂̄ = 0` almost everywhere on the upper half plane, is the identity there. -/
theorem upper_id_of_dzbar_zero {H Hinv : ℂ → ℂ} {κ K : ℝ} (hκ1 : κ < 1)
    (hqc : IsQCUpper H Hinv κ) (hHgeo : IsQCGeometric H K)
    (hRfix : ∀ s : ℝ, H (s : ℂ) = (s : ℂ))
    (h0 : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), dzbar H z = 0) :
    ∀ z : ℂ, 0 < z.im → H z = z := by
  -- the factorization against the identity solution at the trivial base
  have hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar H z
        = (TeichRep.zero (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))).b.μ z
          * dz H z := by
    filter_upwards [h0] with z hz
    rw [hz]
    simp [TeichRep.zero, BeltramiCoeff.zero]
  obtain ⟨R, hR⟩ := exists_sl2_factorization_of_eq_coeff
    (TeichRep.zero (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))) hκ1 hqc hcoeff
  have hzw : (TeichRep.zero (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))).w = id :=
    ((TeichRep.zero _).w_unique isQCAnalytic_id rfl rfl).symm
  have hRz : ∀ z : ℂ, 0 < z.im → z = moebiusMap R (H z) := by
    intro z hz
    have h1 := hR z hz
    rw [hzw] at h1
    simpa using h1
  -- boundary limit: the Möbius factor fixes every non-pole real point
  have hHcont : Continuous H := hHgeo.2.1.isHomeomorph.continuous
  have hlim : ∀ s : ℝ, moebiusDenom R (s : ℂ) ≠ 0 → moebiusMap R (s : ℂ) = (s : ℂ) := by
    intro s hden
    have hTcl : (s : ℂ) ∈ closure {z : ℂ | 0 < z.im} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(s : ℂ) + Complex.I * ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, one_mul, zero_add,
          mul_zero]
        linarith
      · rw [dist_eq_norm]
        have hsub : (s : ℂ) - ((s : ℂ) + Complex.I * ((ε / 2 : ℝ) : ℂ))
            = -(Complex.I * ((ε / 2 : ℝ) : ℂ)) := by ring
        rw [hsub, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
    haveI hNB : (nhdsWithin (s : ℂ) {z : ℂ | 0 < z.im}).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hTcl
    have hL : Filter.Tendsto (fun ζ : ℂ => ζ)
        (nhdsWithin (s : ℂ) {z : ℂ | 0 < z.im}) (nhds (s : ℂ)) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    have hdenH : moebiusDenom R (H (s : ℂ)) ≠ 0 := by rwa [hRfix s]
    have hRc : ContinuousAt (fun ζ : ℂ => moebiusMap R (H ζ)) (s : ℂ) :=
      (hasDerivAt_moebiusMap R hdenH).continuousAt.comp hHcont.continuousAt
    have hR2 : Filter.Tendsto (fun ζ : ℂ => moebiusMap R (H ζ))
        (nhdsWithin (s : ℂ) {z : ℂ | 0 < z.im})
        (nhds (moebiusMap R (H (s : ℂ)))) := hRc.continuousWithinAt
    have hEqf : (fun ζ : ℂ => ζ) =ᶠ[nhdsWithin (s : ℂ) {z : ℂ | 0 < z.im}]
        (fun ζ : ℂ => moebiusMap R (H ζ)) :=
      eventually_nhdsWithin_of_forall fun ζ hζ => hRz ζ hζ
    have hL2 : Filter.Tendsto (fun ζ : ℂ => moebiusMap R (H ζ))
        (nhdsWithin (s : ℂ) {z : ℂ | 0 < z.im}) (nhds (s : ℂ)) :=
      Filter.Tendsto.congr' hEqf hL
    have h4 := tendsto_nhds_unique hL2 hR2
    rw [hRfix s] at h4
    exact h4.symm
  -- three good real points force the Möbius factor to be the identity up to sign
  have hB1 : ({t : ℝ | moebiusDenom R (t : ℂ) = 0}).Finite :=
    Set.Subsingleton.finite ((pole_subsingleton R).preimage Complex.ofReal_injective)
  have hBc := hB1.infinite_compl
  obtain ⟨t₁, ht₁⟩ := hBc.nonempty
  obtain ⟨t₂, ht₂⟩ := (hBc.diff (Set.finite_singleton t₁)).nonempty
  obtain ⟨t₃, ht₃⟩ := (hBc.diff ((Set.finite_singleton t₂).insert t₁)).nonempty
  have hd1 : moebiusDenom R (t₁ : ℂ) ≠ 0 := ht₁
  have hd2 : moebiusDenom R (t₂ : ℂ) ≠ 0 := ht₂.1
  have hd3 : moebiusDenom R (t₃ : ℂ) ≠ 0 := ht₃.1
  have ht21 : t₂ ≠ t₁ := fun hEq => ht₂.2 hEq
  have ht31 : t₃ ≠ t₁ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inl hEq))
  have ht32 : t₃ ≠ t₂ := fun hEq => ht₃.2 (Set.mem_insert_iff.mpr (Or.inr hEq))
  have hz12 : ((t₁ : ℝ) : ℂ) ≠ ((t₂ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht21.symm
  have hz13 : ((t₁ : ℝ) : ℂ) ≠ ((t₃ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht31.symm
  have hz23 : ((t₂ : ℝ) : ℂ) ≠ ((t₃ : ℝ) : ℂ) := Complex.ofReal_injective.ne ht32.symm
  have hone : ∀ u : ℂ, moebiusDenom (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) u = 1 := by
    intro u
    simp [moebiusDenom]
  have hVden : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
      moebiusDenom R u ≠ 0 := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hd1
    · exact hd2
    · exact hd3
  have hWden : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
      moebiusDenom (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) u ≠ 0 := by
    intro u hu
    rw [hone u]
    exact one_ne_zero
  have hagree : ∀ u ∈ ({((t₁ : ℝ) : ℂ), ((t₂ : ℝ) : ℂ), ((t₃ : ℝ) : ℂ)} : Set ℂ),
      moebiusMap R u = moebiusMap (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) u := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · rw [hlim t₁ hd1, moebiusMap_one]
    · rw [hlim t₂ hd2, moebiusMap_one]
    · rw [hlim t₃ hd3, moebiusMap_one]
  have hcase := moebius_ext_three hz12 hz13 hz23 hVden hWden hagree
  have hmapeq : ∀ u : ℂ, moebiusMap R u
      = moebiusMap (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) u := by
    rcases hcase with heq | hneg
    · intro u
      rw [Subtype.ext heq]
    · exact fun u => moebiusMap_neg_matrix hneg u
  -- conclusion
  intro z hz
  have h5 := hRz z hz
  rw [hmapeq (H z), moebiusMap_one] at h5
  exact h5.symm

set_option maxHeartbeats 400000 in
-- Heartbeats: the equality-case Reich–Strebel application carries a deep local tower.
/-- **Unique extremality**: a marked competitor of the extremal dilatation agrees with the
Teichmüller-form candidate on the upper half plane — equality in Reich–Strebel forces the
same Beltrami coefficient almost everywhere, and the resulting Möbius factor fixes the
boundary values, hence is trivial. -/
theorem isTeichmullerCandidate_unique (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {q : QuadraticDifferential y.group} {k : ℝ} {F G : ℂ → ℂ}
    (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsTeichmullerCandidate x y q k F)
    (hG : IsQCGeometric G ((1 + k) / (1 - k))) (hGc : IsMarkedCandidate x y G) :
    ∀ z : ℂ, 0 < z.im → G z = F z := by
  obtain ⟨hFc, hFqc, hFbel⟩ := hF
  have hΓy : IsFuchsianGroup y.group := TeichRep.isFuchsian_group hΓ₀ hfree y
  have hfreey := TeichRep.group_free hfree y
  have hccy := TeichRep.group_cocompact hcc y
  obtain ⟨H, Hinv, κ, hκ0, hκ1, hHqc, hequiv, hbd, hFGH, hHgeo, hHiH, hHHi, hRfix⟩ :=
    exists_upper_conjugator_of_candidates₂ hFqc hFc hG hGc
  have hRS := reich_strebel_main_inequality hΓy hfreey hccy q hκ1 hHqc hbd hequiv
  -- the analytic layer of the competitor with the exact coefficient bound `k`
  obtain ⟨bG, hbGn, hGA⟩ := isQCAnalytic_of_isQCGeometric hG.1 hG
  have hbGk : bG.normInf ≤ k := by
    refine le_trans hbGn ?_
    have h1 : (1 : ℝ) - k ≠ 0 := by linarith
    have hks : ((1 + k) / (1 - k) - 1) / ((1 + k) / (1 - k) + 1) = k := by
      rw [show (1 + k) / (1 - k) - 1 = (2 * k) / (1 - k) by field_simp; ring,
        show (1 + k) / (1 - k) + 1 = 2 / (1 - k) by field_simp; ring,
        div_eq_iff (div_ne_zero two_ne_zero h1)]
      field_simp
    rw [hks]
  have hbw_ae : ∀ᵐ w : ℂ, ‖bG.μ w‖ ≤ bG.normInf := by
    filter_upwards [enorm_ae_le_eLpNormEssSup bG.μ volume] with w hw
    have h2 := ENNReal.toReal_mono (ne_top_of_lt bG.bound) hw
    simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
  have hGgood : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w ∧ dzbar G w = bG.μ w * dz G w ∧
      ‖bG.μ w‖ ≤ k ∧ 0 < (fderiv ℝ G w).det := by
    filter_upwards [hGA.ae_differentiableAt, hGA.2.2, hbw_ae, hGA.1.2] with w h1 h2 h3 h4
    exact ⟨h1, h2, le_trans h3 hbGk, h4⟩
  set N : Set ℂ := {w : ℂ | ¬ (DifferentiableAt ℝ G w ∧ dzbar G w = bG.μ w * dz G w ∧
      ‖bG.μ w‖ ≤ k ∧ 0 < (fderiv ℝ G w).det)} with hNdef
  have hNnull : volume N = 0 := ae_iff.mp hGgood
  have hHpull : ∀ᵐ z : ℂ, H z ∉ N := preimage_conull hHgeo hNnull
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} := hUopen.measurableSet
  -- the pointwise bound and its conditional equality extraction
  have hptwise : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z ≤ ‖q z‖ₑ ∧
      (‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z = ‖q z‖ₑ → dzbar H z = 0) := by
    filter_upwards [q.ae_ne_zero hq0, hFbel, ae_restrict_of_ae hHpull,
      ae_differentiableAt hHqc, hHqc.jac, ae_qc_facts hHqc, ae_restrict_mem hUm]
      with z hqz hzbel hzN hzdiff hzjac hzfacts hzU
    simp only [hNdef, Set.mem_setOf_eq, not_not] at hzN
    obtain ⟨hGdiff, hGbel, hGbnd, hGjac⟩ := hzN
    set θz : ℂ := q z / (‖q z‖ : ℂ) with hθzdef
    set α : ℂ := dz H z with hαdef
    set β : ℂ := dzbar H z with hβdef
    set p : ℂ := dz G (H z) with hpdef
    set b' : ℂ := dzbar G (H z) with hb'def
    have hqn0 : ‖q z‖ ≠ 0 := norm_ne_zero_iff.mpr hqz
    have hθ1 : ‖θz‖ = 1 := by
      rw [hθzdef, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self hqn0]
    have hθprod : θz * starRingEnd ℂ θz = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ1]
      norm_num
    have htc : teichmullerCoeffFun (q : ℂ → ℂ) k z = (k : ℂ) * starRingEnd ℂ θz := by
      simp only [teichmullerCoeffFun, hθzdef, map_div₀, Complex.conj_ofReal,
        Complex.ofReal_inv]
      ring
    have hev : F =ᶠ[nhds z] fun w => G (H w) :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hzU) fun w hw => hFGH w hw
    have hfeq : fderiv ℝ F z = fderiv ℝ (fun w => G (H w)) z := hev.fderiv_eq
    have hcomp1 : dz F z = p * α + b' * starRingEnd ℂ β := by
      rw [dz, hfeq, ← dz, dz_comp hzdiff hGdiff]
    have hcomp2 : dzbar F z = p * β + b' * starRingEnd ℂ α := by
      rw [dzbar, hfeq, ← dzbar, dzbar_comp hzdiff hGdiff]
    have hFrame : p * (β - (k : ℂ) * starRingEnd ℂ θz * α)
        = -(b' * starRingEnd ℂ (α - (k : ℂ) * θz * β)) := by
      have h1 := hzbel
      rw [hcomp1, hcomp2, htc] at h1
      simp only [map_sub, map_mul, Complex.conj_ofReal]
      linear_combination h1
    have hα0 : α ≠ 0 := hzfacts.1
    have hjacr : ‖β‖ < ‖α‖ := by
      have h2 := hzjac
      rw [det_fderiv_eq_wirtinger] at h2
      nlinarith [norm_nonneg (dz H z), norm_nonneg (dzbar H z)]
    have hp0 : p ≠ 0 := by
      have h3 := hGjac
      rw [det_fderiv_eq_wirtinger] at h3
      intro h4
      rw [hpdef] at h4
      rw [h4, norm_zero] at h3
      nlinarith [sq_nonneg ‖dzbar G (H z)‖]
    have hbb : ‖b'‖ ≤ k * ‖p‖ := by
      have h5 : dzbar G (H z) = bG.μ (H z) * dz G (H z) := hGbel
      change ‖dzbar G (H z)‖ ≤ k * ‖dz G (H z)‖
      rw [h5, norm_mul]
      exact mul_le_mul_of_nonneg_right hGbnd (norm_nonneg _)
    have hwq : wirtingerQuotient H z = β / α := rfl
    have hnα : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα0
    have hJne : ‖α‖ ^ 2 - ‖β‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg (dzbar H z)]
    have hratio : ‖1 - wirtingerQuotient H z * θz‖ ^ 2
        / (1 - ‖wirtingerQuotient H z‖ ^ 2)
        = ‖α - θz * β‖ ^ 2 / (‖α‖ ^ 2 - ‖β‖ ^ 2) := by
      rw [hwq]
      have h5 : (1 : ℂ) - β / α * θz = (α - θz * β) / α := by
        field_simp
      rw [h5, norm_div, div_pow, norm_div, div_pow]
      have hden2 : (1 : ℝ) - (‖β‖ / ‖α‖) ^ 2 ≠ 0 := by
        have h6 : ‖β‖ / ‖α‖ < 1 := (div_lt_one (norm_pos_iff.mpr hα0)).mpr hjacr
        have h7 : 0 ≤ ‖β‖ / ‖α‖ := by positivity
        nlinarith
      field_simp
    have hWform : rsWeight (q : ℂ → ℂ) H z
        = ENNReal.ofReal (‖α - θz * β‖ ^ 2 / (‖α‖ ^ 2 - ‖β‖ ^ 2)) := by
      rw [rsWeight, hratio]
    constructor
    · -- the bound conjunct
      have hkey := rs_weight_pointwise hk0 hk1 hk0 hk1 hθprod hjacr hp0 hbb hFrame
      have hone : (1 - k) / (1 + k) * ((1 + k) / (1 - k)) = 1 := by
        have h1 : (1 : ℝ) - k ≠ 0 := by linarith
        have h2 : (1 : ℝ) + k ≠ 0 := by linarith
        field_simp
      rw [hone] at hkey
      calc ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z
          ≤ ‖q z‖ₑ * ENNReal.ofReal 1 := by
            rw [hWform]
            exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hkey)
        _ = ‖q z‖ₑ := by rw [ENNReal.ofReal_one, mul_one]
    · -- the equality conjunct
      intro hprod
      have hq0' : ‖q z‖ₑ ≠ 0 := by
        rw [enorm_ne_zero]
        exact hqz
      have h6 : rsWeight (q : ℂ → ℂ) H z = 1 := by
        have h7 : ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z = ‖q z‖ₑ * 1 := by
          rw [mul_one]
          exact hprod
        exact (ENNReal.mul_right_inj hq0' enorm_ne_top).mp h7
      rw [hWform, ENNReal.ofReal_eq_one] at h6
      exact rs_weight_equality hk0 hk1 hθprod hjacr hp0 hbb hFrame h6
  -- the integral pinch over the Dirichlet domain
  set D : Set ℂ := UpperHalfPlane.coe '' dirichletDomain y.group UpperHalfPlane.I
    with hDdef
  have hDsub : D ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hfmeas : Measurable fun z : ℂ => ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z :=
    q.measurable.enorm.mul (measurable_rsWeight q.measurable H)
  have hgmeas : Measurable fun z : ℂ => ‖q z‖ₑ := q.measurable.enorm
  have hDae := ae_restrict_of_ae_restrict_of_subset hDsub hptwise
  have hle : (fun z : ℂ => ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z)
      ≤ᵐ[volume.restrict D] fun z : ℂ => ‖q z‖ₑ :=
    hDae.mono fun z hz => hz.1
  have hgfin : (∫⁻ z in D, ‖q z‖ₑ) ≠ ⊤ := q.l1Norm_ne_top hΓy hfreey hccy
  have hRS' : (∫⁻ z in D, ‖q z‖ₑ)
      ≤ ∫⁻ z in D, ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z := by
    have h1 : q.l1Norm = ∫⁻ z in D, ‖q z‖ₑ := by rw [hDdef]; rfl
    have h2 : (fun z : ℂ => ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z)
        = fun z : ℂ => ‖q z‖ₑ * ENNReal.ofReal
          (‖1 - wirtingerQuotient H z * (q z / (‖q z‖ : ℂ))‖ ^ 2
            / (1 - ‖wirtingerQuotient H z‖ ^ 2)) := by
      funext w
      rw [rsWeight]
    rw [← h1, h2]
    exact hRS
  have heqint : (∫⁻ z in D, ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z)
      = ∫⁻ z in D, ‖q z‖ₑ :=
    le_antisymm (lintegral_mono_ae hle) hRS'
  have hffin : (∫⁻ z in D, ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z) ≠ ⊤ := by
    rw [heqint]
    exact hgfin
  have hsub0 : (∫⁻ z in D, (‖q z‖ₑ - ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z)) = 0 := by
    rw [lintegral_sub hfmeas hffin hle, heqint, tsub_self]
  have hae0' : ∀ᵐ z ∂(volume.restrict D),
      ‖q z‖ₑ - ‖q z‖ₑ * rsWeight (q : ℂ → ℂ) H z = 0 :=
    (lintegral_eq_zero_iff (hgmeas.sub hfmeas)).mp hsub0
  have hD0 : ∀ᵐ z ∂(volume.restrict D), dzbar H z = 0 := by
    filter_upwards [hae0', hDae] with z h1 h2
    exact h2.2 (le_antisymm h2.1 (tsub_eq_zero_iff_le.mp h1))
  -- unfolding to the whole upper half plane and the conformal-rigidity endgame
  have hall0 := dzbar_zero_unfold hΓy hfreey hccy hHqc hequiv hD0
  have hHid := upper_id_of_dzbar_zero hκ1 hHqc hHgeo hRfix hall0
  intro z hz
  have h3 := hFGH z hz
  rw [hHid z hz] at h3
  exact h3.symm

/-! ## The conditional existence-and-uniqueness statement -/

/-- **Teichmüller's theorem on the upper half plane, conditional form**: if the marked
class of the pair contains a Teichmüller-form candidate, then it contains an extremal
marked candidate of dilatation `sInf (gDilatationSet x y)`, unique up to its values on
the upper half plane. -/
theorem exists_extremal_unique_upper (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀}
    (hex : ∃ (q : QuadraticDifferential y.group) (k : ℝ) (F : ℂ → ℂ),
      0 ≤ k ∧ k < 1 ∧ (∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) ∧
      IsTeichmullerCandidate x y q k F) :
    ∃ F : ℂ → ℂ, IsQCGeometric F (sInf (gDilatationSet x y)) ∧
      IsMarkedCandidate x y F ∧
      ∀ G : ℂ → ℂ, IsQCGeometric G (sInf (gDilatationSet x y)) →
        IsMarkedCandidate x y G → ∀ z : ℂ, 0 < z.im → G z = F z := by
  obtain ⟨q, k, F, hk0, hk1, hq0, hF⟩ := hex
  have hlb := isTeichmullerCandidate_le_dilatation hΓ₀ hfree hcc hq0 hk0 hk1 hF
  have hmem : (1 + k) / (1 - k) ∈ gDilatationSet x y := ⟨F, hF.2.1, hF.1⟩
  have hsinf : sInf (gDilatationSet x y) = (1 + k) / (1 - k) :=
    le_antisymm (csInf_le (bddBelow_gDilatationSet x y) hmem)
      (le_csInf ⟨_, hmem⟩ hlb)
  refine ⟨F, ?_, hF.1, ?_⟩
  · rw [hsinf]
    exact hF.2.1
  · intro G hGqc hGc z hz
    rw [hsinf] at hGqc
    exact isTeichmullerCandidate_unique hΓ₀ hfree hcc hq0 hk0 hk1 hF hGqc hGc z hz

/-- **The conformal degenerate case**: a candidate of dilatation `1` for a pair is
conformal, hence affine, and fixing `0` and `1` it is the identity; the pair has equal
boundary values. -/
theorem w_eq_on_real_of_candidate_one {x y : TeichRep Γ₀} {G : ℂ → ℂ}
    (hG : IsQCGeometric G 1) (hb : ∀ t : ℝ, G (y.w t) = x.w t) :
    ∀ t : ℝ, x.w t = y.w t := by
  obtain ⟨b₁, hbn, hbQC⟩ := isQCAnalytic_of_isQCGeometric le_rfl hG
  have hbn0 : b₁.normInf = 0 := by
    have h0 : b₁.normInf ≤ 0 := by
      have hb' := hbn
      norm_num at hb'
      exact hb'
    exact le_antisymm h0 b₁.normInf_nonneg
  have hbe : eLpNormEssSup b₁.μ volume = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hbn0 with h0 | htop
    · exact h0
    · exact absurd htop (ne_top_of_lt b₁.bound)
  have hmu : b₁.μ =ᵐ[volume] BeltramiCoeff.zero.μ := eLpNormEssSup_eq_zero_iff.mp hbe
  have hgz : IsQCAnalytic G BeltramiCoeff.zero := hbQC.congr_coeff hmu
  have hgdiff : Differentiable ℂ G := weyl_lemma hgz rfl
  have hginj : Function.Injective G := hgz.injective
  obtain ⟨a, c, -, hgeq⟩ := eq_affine_of_differentiable_of_injective hgdiff hginj
  have hg0 : G 0 = 0 := by
    have h0 := hb 0
    rwa [Complex.ofReal_zero, y.w_zero, x.w_zero] at h0
  have hg1' : G 1 = 1 := by
    have h1 := hb 1
    rwa [Complex.ofReal_one, y.w_one, x.w_one] at h1
  have hc : c = 0 := by
    have h0 := hg0
    rw [hgeq] at h0
    simpa using h0
  have ha1 : a = 1 := by
    have h1 := hg1'
    rw [hgeq, hc] at h1
    simpa using h1
  intro t
  have hgy := hb t
  rw [hgeq, ha1, hc] at hgy
  simpa using hgy.symm

/-- The normalized solution at the base point is the identity. -/
theorem zero_w_eq : (TeichRep.zero Γ₀).w = id :=
  ((TeichRep.zero Γ₀).w_unique isQCAnalytic_id rfl rfl).symm

/-- **The Möbius kernel**: an element fixing the upper half plane pointwise has constant
denominator equal to a sign. -/
theorem moebius_fix_pm {V : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hfix : ∀ z : ℂ, 0 < z.im → moebiusMap V z = z) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ z : ℂ, moebiusDenom V z = (e : ℂ) := by
  have hIim : (0:ℝ) < Complex.I.im := by simp
  have h2im : (0:ℝ) < ((2:ℂ) * Complex.I).im := by simp
  have hd1 : moebiusDenom V Complex.I ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt hIim)
  have hd2 : moebiusDenom V ((2:ℂ) * Complex.I) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt h2im)
  have h1 : ((V 0 0 : ℝ) : ℂ) * Complex.I + ((V 0 1 : ℝ) : ℂ)
      = Complex.I * (((V 1 0 : ℝ) : ℂ) * Complex.I + ((V 1 1 : ℝ) : ℂ)) := by
    have h := hfix Complex.I hIim
    unfold moebiusMap at h
    rw [div_eq_iff hd1] at h
    unfold moebiusDenom at h
    exact h
  have h2 : ((V 0 0 : ℝ) : ℂ) * ((2:ℂ) * Complex.I) + ((V 0 1 : ℝ) : ℂ)
      = (2:ℂ) * Complex.I * (((V 1 0 : ℝ) : ℂ) * ((2:ℂ) * Complex.I)
        + ((V 1 1 : ℝ) : ℂ)) := by
    have h := hfix ((2:ℂ) * Complex.I) h2im
    unfold moebiusMap at h
    rw [div_eq_iff hd2] at h
    unfold moebiusDenom at h
    exact h
  have hre1 := congrArg Complex.re h1
  have him1 := congrArg Complex.im h1
  have hre2 := congrArg Complex.re h2
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat] at hre1 him1 hre2
  -- entries: V01 = −V10 and V00 = V11 from z = i, V01 = −4·V10 from z = 2i
  have hc : (V 1 0 : ℝ) = 0 := by linarith
  have hb : (V 0 1 : ℝ) = 0 := by linarith
  have had : (V 0 0 : ℝ) = V 1 1 := by linarith
  have hdet := V.property
  rw [Matrix.det_fin_two] at hdet
  have he2 : (V 1 1 : ℝ) * V 1 1 = 1 := by
    have : (V 0 0 : ℝ) * V 1 1 - V 0 1 * V 1 0 = 1 := hdet
    rw [had, hb] at this
    linarith [this]
  refine ⟨V 1 1, mul_self_eq_one_iff.mp he2, fun z => ?_⟩
  unfold moebiusDenom
  rw [hc]
  push_cast
  ring

/-- **Membership at the base point**: an element of the base-point group agrees with a
base-group element as a Möbius map throughout the upper half plane. -/
theorem zero_group_mem {W : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hW : W ∈ (TeichRep.zero Γ₀).group) :
    ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im → moebiusMap W z = moebiusMap γ z := by
  obtain ⟨γ, hγ, heq⟩ := w_conj_of_mem_group (TeichRep.zero Γ₀) hW
  refine ⟨γ, hγ, fun z hz => ?_⟩
  have h := heq z hz
  rw [zero_w_eq] at h
  exact (h.symm : moebiusMap W z = moebiusMap γ z)

/-- **Weight-four sign cancellation**: elements with equal Möbius maps on the upper half
plane have equal fourth powers of denominators there. -/
theorem denom_pow {W γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hmap : ∀ z : ℂ, 0 < z.im → moebiusMap W z = moebiusMap γ z) :
    ∀ z : ℂ, 0 < z.im → moebiusDenom W z ^ 4 = moebiusDenom γ z ^ 4 := by
  set V := W⁻¹ * γ with hVdef
  have hWV : W * V = γ := by
    rw [hVdef, ← mul_assoc, mul_inv_cancel, one_mul]
  have hfix : ∀ z : ℂ, 0 < z.im → moebiusMap V z = z := by
    intro z hz
    have hdγ : moebiusDenom γ z ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz)
    have hdW : moebiusDenom W z ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero W (ne_of_gt hz)
    rw [hVdef, ← moebiusMap_mul W⁻¹ γ z hdγ, ← hmap z hz,
      moebiusMap_mul W⁻¹ W z hdW, inv_mul_cancel, moebiusMap_one]
  obtain ⟨e, hepm, hede⟩ := moebius_fix_pm hfix
  have hene : ((e : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    rcases hepm with h | h <;> rw [h] <;> norm_num
  have he4 : ((e : ℝ) : ℂ) ^ 4 = 1 := by
    rcases hepm with h | h <;> rw [h] <;> norm_num
  intro z hz
  have hdVz : moebiusDenom V z ≠ 0 := by
    rw [hede z]
    exact hene
  have hcoc := moebiusDenom_mul W V z hdVz
  rw [hfix z hz, hWV, hede z] at hcoc
  calc moebiusDenom W z ^ 4
      = moebiusDenom W z ^ 4 * ((e : ℝ) : ℂ) ^ 4 := by rw [he4, mul_one]
    _ = (moebiusDenom W z * ((e : ℝ) : ℂ)) ^ 4 := by ring
    _ = moebiusDenom γ z ^ 4 := by rw [hcoc]

/-- The transport of a quadratic differential from the base group to the base-point group:
the carrier is unchanged, and automorphy transfers along the Möbius-kernel matching since
the weight-four cocycle is insensitive to the sign. -/
noncomputable def qdToZeroGroup (q : QuadraticDifferential Γ₀) :
    QuadraticDifferential ((TeichRep.zero Γ₀).group) where
  toFun := q.toFun
  measurable := q.measurable
  holo := q.holo
  automorphy := by
    intro W hW z hz
    obtain ⟨γ, hγ, hmap⟩ := zero_group_mem hW
    have h4 := denom_pow hmap z hz
    rw [hmap z hz, q.automorphy γ hγ z hz, h4]

/-- The transported quadratic differential has the same carrier. -/
theorem qdToZeroGroup_coe (q : QuadraticDifferential Γ₀) :
    ⇑(qdToZeroGroup q) = ⇑q := rfl

/-- **The ray representative is its own Teichmüller-form candidate** against the base
point, in the direction of the transported differential. -/
theorem teichmullerCoeff_isTeichmullerCandidate (q : QuadraticDifferential Γ₀) {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    IsTeichmullerCandidate (teichmullerCoeff q k hk0 hk1) (TeichRep.zero Γ₀)
      (qdToZeroGroup q) k (teichmullerCoeff q k hk0 hk1).w := by
  set x : TeichRep Γ₀ := teichmullerCoeff q k hk0 hk1 with hxdef
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro t
    rw [zero_w_eq]
    rfl
  · intro W hW
    obtain ⟨γ, hγ, hmap⟩ := zero_group_mem hW
    obtain ⟨W', hW', hxc⟩ := w_conj_of_mem_base x hγ
    refine ⟨W', hW', fun z hz => ?_⟩
    rw [hmap z hz]
    exact hxc z hz
  · intro W' hW'
    obtain ⟨γ, hγ, hxc⟩ := w_conj_of_mem_group x hW'
    have hγmem : γ ∈ (TeichRep.zero Γ₀).group := by
      refine ⟨γ, hγ, ?_⟩
      rw [zero_w_eq]
      exact Filter.Eventually.of_forall fun z => rfl
    exact ⟨γ, hγmem, fun z hz => hxc z hz⟩
  · have hK := x.w_isQCAnalytic.isQCGeometric_K
    have hnk : x.b.normInf ≤ k := normInf_le_of_symmExtension hk0
      (fun z => norm_teichmullerCoeffFun_le hk0 z) rfl
    have hKle : x.b.K ≤ (1 + k) / (1 - k) := by
      have hn0 := x.b.normInf_nonneg
      have hn1 := x.b.normInf_lt_one
      rw [BeltramiCoeff.K, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith only [hnk, hn0, hn1, hk0, hk1]
    exact hK.mono hKle
  · have hbel := x.w_isQCAnalytic.2.2
    have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
      measurableSet_lt measurable_const Complex.measurable_im
    filter_upwards [ae_restrict_of_ae hbel, ae_restrict_mem hU] with z hz hmem
    rw [hz]
    congr 1
    change symmExtension (teichmullerCoeffFun (⇑q) k) z = teichmullerCoeffFun (⇑q) k z
    unfold symmExtension
    rw [if_pos hmem]

/-- **The Jacobian in Wirtinger form**: the determinant of a real-linear map of the plane
is the difference of the squared moduli of its complex-linear and conjugate-linear parts. -/
theorem det_clm_eq_normSq_sub (A : ℂ →L[ℝ] ℂ) :
    A.det = ‖(1 / 2 : ℂ) * (A 1 - Complex.I * A Complex.I)‖ ^ 2
      - ‖(1 / 2 : ℂ) * (A 1 + Complex.I * A Complex.I)‖ ^ 2 := by
  set a : ℝ := (A 1).re with ha
  set b : ℝ := (A 1).im with hb
  set c : ℝ := (A Complex.I).re with hc
  set d : ℝ := (A Complex.I).im with hd
  have hdet : A.det = a * d - b * c := by
    have key : ∀ M : ℂ →ₗ[ℝ] ℂ, LinearMap.det M
        = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI M).det := fun M =>
      (LinearMap.det_toMatrix Complex.basisOneI M).symm
    rw [ContinuousLinearMap.det, key]
    have hb0 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 0 = (1 : ℂ) := by
      simp [Complex.coe_basisOneI]
    have hb1 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 1 = Complex.I := by
      simp [Complex.coe_basisOneI]
    have c00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 0 = a := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]; rfl
    have c10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 0 = b := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]; rfl
    have c01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 1 = c := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]; rfl
    have c11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 1 = d := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]; rfl
    have h0 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) = !![a, c; b, d] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
          Matrix.cons_val_fin_one] <;>
        first | exact c00 | exact c01 | exact c10 | exact c11
    rw [h0, Matrix.det_fin_two_of]; ring
  have hp2 : ‖(1 / 2 : ℂ) * (A 1 - Complex.I * A Complex.I)‖ ^ 2
      = ((a + d) ^ 2 + (b - c) ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h12re : (1 / 2 : ℂ).re = 1 / 2 := by norm_num [Complex.div_re]
    have h12im : (1 / 2 : ℂ).im = 0 := by norm_num [Complex.div_im]
    have hre : ((1 / 2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).re = (a + d) / 2 := by
      rw [ha, hd]
      simp only [Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    have him : ((1 / 2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).im = (b - c) / 2 := by
      rw [hb, hc]
      simp only [Complex.mul_im, Complex.sub_re, Complex.mul_re, Complex.sub_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    rw [hre, him]; ring
  have hq2 : ‖(1 / 2 : ℂ) * (A 1 + Complex.I * A Complex.I)‖ ^ 2
      = ((a - d) ^ 2 + (b + c) ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h12re : (1 / 2 : ℂ).re = 1 / 2 := by norm_num [Complex.div_re]
    have h12im : (1 / 2 : ℂ).im = 0 := by norm_num [Complex.div_im]
    have hre : ((1 / 2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).re = (a - d) / 2 := by
      rw [ha, hd]
      simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    have him : ((1 / 2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).im = (b + c) / 2 := by
      rw [hb, hc]
      simp only [Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.add_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    rw [hre, him]; ring
  rw [hdet, hp2, hq2]; ring

/-- A positive Jacobian forces a nonvanishing complex-linear part. -/
theorem dz_ne_zero_of_det_pos {f : ℂ → ℂ} {z : ℂ} (hdet : 0 < (fderiv ℝ f z).det) :
    dz f z ≠ 0 := by
  have h := det_clm_eq_normSq_sub (fderiv ℝ f z)
  have hp : dz f z
      = (1 / 2 : ℂ) * ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I) := rfl
  have hq : dzbar f z
      = (1 / 2 : ℂ) * ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I) := rfl
  rw [← hp, ← hq] at h
  intro h0
  rw [h0, norm_zero] at h
  have h2 := sq_nonneg ‖dzbar f z‖
  rw [h] at hdet
  nlinarith only [hdet, h2]

/-- **The relative coefficient bound, pointwise**: solving the composition chain rule for
two Beltrami values proportional to a common unit-bounded direction bounds the relative
coefficient by the relative modulus. -/
theorem rel_coeff_pointwise {p a bb m1 m2 mr th Z W : ℂ} {k1 k2 : ℝ}
    (hp : p ≠ 0) (ha : a ≠ 0) (hth : ‖th‖ ≤ 1)
    (hm1 : m1 = (k1 : ℂ) * th) (hm2 : m2 = (k2 : ℂ) * th)
    (hk10 : 0 ≤ k1) (hk12 : k1 ≤ k2) (hk21 : k2 < 1)
    (hcz : Z = a * p + bb * starRingEnd ℂ (m1 * p))
    (hczb : W = a * (m1 * p) + bb * starRingEnd ℂ p)
    (hbel2 : W = m2 * Z) (hbelR : bb = mr * a) :
    ‖mr‖ ≤ (k2 - k1) / (1 - k1 * k2) := by
  have hk1k2 : k1 * k2 < 1 := by nlinarith only [hk10, hk12, hk21]
  set t : ℝ := ‖th‖ with htdef
  have ht0 : 0 ≤ t := norm_nonneg th
  have hkey : mr * starRingEnd ℂ p * (1 - m2 * starRingEnd ℂ m1) = p * (m2 - m1) := by
    have h1 : a * (m1 * p) + (mr * a) * starRingEnd ℂ p
        = m2 * (a * p + (mr * a) * (starRingEnd ℂ m1 * starRingEnd ℂ p)) := by
      rw [← hbelR, ← hczb]
      rw [hbel2, hcz, map_mul]
    have h2 : a * (mr * starRingEnd ℂ p * (1 - m2 * starRingEnd ℂ m1)
        - p * (m2 - m1)) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h ha
    · exact sub_eq_zero.mp h
  have hnorm := congrArg norm hkey
  rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj] at hnorm
  have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht0, hth]
  have hkk : 0 ≤ k1 * k2 := mul_nonneg hk10 (hk10.trans hk12)
  have hth2 : m2 * starRingEnd ℂ m1 = ((k1 * k2 * t ^ 2 : ℝ) : ℂ) := by
    rw [hm1, hm2, map_mul, Complex.conj_ofReal, htdef]
    rw [show ((k1 * k2 * ‖th‖ ^ 2 : ℝ) : ℂ)
        = (k1 : ℂ) * (k2 : ℂ) * ((‖th‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  have hone : ‖(1 : ℂ) - m2 * starRingEnd ℂ m1‖ = 1 - k1 * k2 * t ^ 2 := by
    rw [hth2, show (1 : ℂ) = ((1 : ℝ) : ℂ) from rfl, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    nlinarith only [hk1k2, ht2, hkk]
  have hdiff : ‖m2 - m1‖ = (k2 - k1) * t := by
    rw [hm1, hm2, show (k2 : ℂ) * th - (k1 : ℂ) * th = ((k2 - k1 : ℝ) : ℂ) * th by
      push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hk12])]
  rw [hone, hdiff] at hnorm
  have hpn : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have heqn : ‖mr‖ * (1 - k1 * k2 * t ^ 2) = (k2 - k1) * t := by
    have h3 : ‖mr‖ * ‖p‖ * (1 - k1 * k2 * t ^ 2) = ‖p‖ * ((k2 - k1) * t) := hnorm
    have h4 : ‖p‖ * (‖mr‖ * (1 - k1 * k2 * t ^ 2)) = ‖p‖ * ((k2 - k1) * t) := by
      linarith [h3]
    exact mul_left_cancel₀ (ne_of_gt hpn) h4
  have hD : (0 : ℝ) < 1 - k1 * k2 * t ^ 2 := by
    nlinarith only [hk1k2, ht2, hkk]
  have hden : (0 : ℝ) < 1 - k1 * k2 := by linarith [hk1k2]
  rw [le_div_iff₀ hden]
  have hfac : 0 ≤ (k2 - k1) * ((1 - t) * (1 + k1 * k2 * t)) := by
    have h5 : 0 ≤ 1 + k1 * k2 * t :=
      by nlinarith only [ht0, mul_nonneg hk10 (hk10.trans hk12)]
    exact mul_nonneg (by linarith [hk12])
      (mul_nonneg (by linarith [hth]) h5)
  have hstep : ‖mr‖ * (1 - k1 * k2) * (1 - k1 * k2 * t ^ 2)
      ≤ (k2 - k1) * (1 - k1 * k2 * t ^ 2) := by
    nlinarith only [heqn, hfac, hD, norm_nonneg mr, hden]
  exact le_of_mul_le_mul_right hstep hD

/-- **The common direction**: the Beltrami coefficients of the ray representatives are the
real moduli times one unit-bounded plane field. -/
theorem teichmullerCoeff_mu_factor (q : QuadraticDifferential Γ₀) :
    ∃ Th : ℂ → ℂ, (∀ z : ℂ, ‖Th z‖ ≤ 1) ∧
      ∀ (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) (z : ℂ),
        (teichmullerCoeff q k hk0 hk1).b.μ z = (k : ℂ) * Th z := by
  refine ⟨symmExtension (teichmullerCoeffFun q 1), fun z => ?_, fun k hk0 hk1 z => ?_⟩
  · unfold symmExtension
    split_ifs with h
    · exact norm_teichmullerCoeffFun_le zero_le_one z
    · rw [RCLike.norm_conj]
      exact norm_teichmullerCoeffFun_le zero_le_one _
  · have hb : (teichmullerCoeff q k hk0 hk1).b.μ z
        = symmExtension (teichmullerCoeffFun q k) z := rfl
    have hpt : ∀ w : ℂ, teichmullerCoeffFun q k w
        = (k : ℂ) * teichmullerCoeffFun q 1 w := by
      intro w
      unfold teichmullerCoeffFun
      push_cast
      ring
    rw [hb]
    unfold symmExtension
    split_ifs with h
    · exact hpt z
    · rw [hpt (starRingEnd ℂ z), map_mul, Complex.conj_ofReal]

/-! ## The Teichmüller ray through the base point -/

/-- **The ray formula**: the intrinsic distance from the Teichmüller representative of
modulus `k` in direction `q` to the base point is `½ log ((1 + k)/(1 − k))`. -/
theorem teichDistG_teichmullerCoeff (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (q : QuadraticDifferential Γ₀) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) :
    teichDistG (teichmullerCoeff q k hk0 hk1) (TeichRep.zero Γ₀)
      = (1 / 2) * Real.log ((1 + k) / (1 - k)) := by
  have hq0' : ∃ z : ℂ, 0 < z.im ∧ (qdToZeroGroup q) z ≠ 0 := hq0
  exact (isTeichmullerCandidate_extremal hΓ₀ hfree hcc hq0' hk0 hk1
    (teichmullerCoeff_isTeichmullerCandidate q hk0 hk1)).2

/-- **Pullback of null events**: a property holding almost everywhere holds almost
everywhere along a quasiconformal map, by the Lusin property of the inverse. -/
theorem qc_pullback_ae {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {P : ℂ → Prop} (hae : ∀ᵐ ζ, P ζ) : ∀ᵐ z, P (f z) := by
  set e := hf.2.1.isHomeomorph.homeomorph f with hedef
  have happ : ∀ z, e z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.2.1.isHomeomorph z
  rw [ae_iff] at hae ⊢
  have hsub : {z | ¬ P (f z)} = ⇑e.symm '' {ζ | ¬ P ζ} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨f z, h, ?_⟩
      rw [← happ z, Homeomorph.symm_apply_apply]
    · rintro ⟨ζ, hζ, rfl⟩
      have hval : f (e.symm ζ) = ζ := by
        rw [← happ]
        exact e.apply_symm_apply ζ
      rwa [hval]
  rw [hsub]
  exact hf.inverse_lusinN _ hae

/-- **Pushforward of null events**: a property holding almost everywhere along a
quasiconformal map holds almost everywhere, by the Lusin property of the map. -/
theorem qc_pushforward_ae {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {P : ℂ → Prop} (hae : ∀ᵐ z, P (f z)) : ∀ᵐ ζ, P ζ := by
  set e := hf.2.1.isHomeomorph.homeomorph f with hedef
  have happ : ∀ z, e z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.2.1.isHomeomorph z
  rw [ae_iff] at hae ⊢
  have hsub : {ζ | ¬ P ζ} ⊆ f '' {z | ¬ P (f z)} := by
    intro ζ hζ
    have hval : f (e.symm ζ) = ζ := by
      rw [← happ]
      exact e.apply_symm_apply ζ
    refine ⟨e.symm ζ, ?_, hval⟩
    simp only [Set.mem_setOf_eq, hval]
    exact hζ
  exact measure_mono_null hsub (hf.lusinN _ hae)

/-- **The relative coefficient of the ray transition**: the transition between two ray
representatives carries a Beltrami coefficient bounded by the relative modulus. -/
theorem ray_transition_coeff (q : QuadraticDifferential Γ₀) {k1 k2 : ℝ}
    (hk10 : 0 ≤ k1) (hk12 : k1 ≤ k2) (hk21 : k2 < 1) :
    ∃ b : BeltramiCoeff,
      IsQCAnalytic ((teichmullerCoeff q k2 (hk10.trans hk12) hk21).w
          ∘ Function.invFun (teichmullerCoeff q k1 hk10 (lt_of_le_of_lt hk12 hk21)).w) b
      ∧ b.normInf ≤ (k2 - k1) / (1 - k1 * k2) := by
  set x1 : TeichRep Γ₀ := teichmullerCoeff q k1 hk10 (lt_of_le_of_lt hk12 hk21) with hx1def
  set x2 : TeichRep Γ₀ := teichmullerCoeff q k2 (hk10.trans hk12) hk21 with hx2def
  set R : ℂ → ℂ := x2.w ∘ Function.invFun x1.w with hRdef
  have hx1K : IsQCGeometric x1.w x1.b.K := x1.w_isQCAnalytic.isQCGeometric_K
  have hx2K : IsQCGeometric x2.w x2.b.K := x2.w_isQCAnalytic.isQCGeometric_K
  have hinv : IsQCGeometric (Function.invFun x1.w) x1.b.K := by
    have h := isQCGeometric_inv_of_isQCGeometric hx1K
    rwa [← invFun_eq_homeoSymm hx1K.2.1.isHomeomorph] at h
  have hRgeo : IsQCGeometric R (x2.b.K * x1.b.K) := hx2K.comp hinv
  have hK1 : 1 ≤ x2.b.K * x1.b.K := le_trans x2.b.one_le_K
    (le_mul_of_one_le_right (le_trans zero_le_one x2.b.one_le_K) x1.b.one_le_K)
  obtain ⟨bR, hbn0, hbR⟩ := isQCAnalytic_of_isQCGeometric hK1 hRgeo
  refine ⟨bR, hbR, ?_⟩
  obtain ⟨Th, hTh1, hThf⟩ := teichmullerCoeff_mu_factor q
  have hRae : ∀ᵐ ζ, DifferentiableAt ℝ R ζ ∧ 0 < (fderiv ℝ R ζ).det
      ∧ dzbar R ζ = bR.μ ζ * dz R ζ :=
    (geometric_ae_differentiableAt hRgeo).and (hbR.1.2.and hbR.2.2)
  have hRz : ∀ᵐ z, DifferentiableAt ℝ R (x1.w z) ∧ 0 < (fderiv ℝ R (x1.w z)).det
      ∧ dzbar R (x1.w z) = bR.μ (x1.w z) * dz R (x1.w z) :=
    qc_pullback_ae hx1K hRae
  have hgood : ∀ᵐ z : ℂ, ‖bR.μ (x1.w z)‖ ≤ (k2 - k1) / (1 - k1 * k2) := by
    filter_upwards [geometric_ae_differentiableAt hx1K, x1.w_isQCAnalytic.1.2,
      x1.w_isQCAnalytic.2.2, geometric_ae_differentiableAt hx2K,
      x2.w_isQCAnalytic.2.2, hRz] with z h1 h2 h3 h4 h5 h6
    obtain ⟨hRd, hRdet, hRbel⟩ := h6
    have hcompf : (fun w => R (x1.w w)) = x2.w := by
      funext w
      change x2.w (Function.invFun x1.w (x1.w w)) = x2.w w
      rw [Function.leftInverse_invFun x1.w_injective]
    have hdzc : dz x2.w z = dz R (x1.w z) * dz x1.w z
        + dzbar R (x1.w z) * starRingEnd ℂ (dzbar x1.w z) := by
      rw [← hcompf]
      exact dz_comp h1 hRd
    have hdzbc : dzbar x2.w z = dz R (x1.w z) * dzbar x1.w z
        + dzbar R (x1.w z) * starRingEnd ℂ (dz x1.w z) := by
      rw [← hcompf]
      exact dzbar_comp h1 hRd
    rw [h3] at hdzc hdzbc
    have hp : dz x1.w z ≠ 0 := dz_ne_zero_of_det_pos h2
    have ha : dz R (x1.w z) ≠ 0 := dz_ne_zero_of_det_pos hRdet
    exact rel_coeff_pointwise hp ha (hTh1 z)
      (hThf k1 hk10 (lt_of_le_of_lt hk12 hk21) z) (hThf k2 (hk10.trans hk12) hk21 z)
      hk10 hk12 hk21 hdzc hdzbc h5 hRbel
  have hae : ∀ᵐ ζ : ℂ, ‖bR.μ ζ‖ ≤ (k2 - k1) / (1 - k1 * k2) :=
    qc_pushforward_ae hx1K hgood
  have hkr0 : 0 ≤ (k2 - k1) / (1 - k1 * k2) := by
    have hk1k2 : k1 * k2 < 1 := by nlinarith only [hk10, hk12, hk21]
    exact div_nonneg (by linarith [hk12]) (by linarith [hk1k2])
  have hess : eLpNormEssSup bR.μ volume
      ≤ ENNReal.ofReal ((k2 - k1) / (1 - k1 * k2)) :=
    eLpNormEssSup_le_of_ae_bound hae
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
  rwa [ENNReal.toReal_ofReal hkr0] at h

/-- **The relative distance bound**: two ray representatives are at intrinsic distance at
most the half-logarithm of the relative dilatation. -/
theorem ray_transition_dist (q : QuadraticDifferential Γ₀) {k1 k2 : ℝ}
    (hk10 : 0 ≤ k1) (hk12 : k1 ≤ k2) (hk21 : k2 < 1) :
    teichDistG (teichmullerCoeff q k2 (hk10.trans hk12) hk21)
        (teichmullerCoeff q k1 hk10 (lt_of_le_of_lt hk12 hk21))
      ≤ (1 / 2) * Real.log ((1 + (k2 - k1) / (1 - k1 * k2))
          / (1 - (k2 - k1) / (1 - k1 * k2))) := by
  set kr : ℝ := (k2 - k1) / (1 - k1 * k2) with hkrdef
  set x1 : TeichRep Γ₀ := teichmullerCoeff q k1 hk10 (lt_of_le_of_lt hk12 hk21) with hx1def
  set x2 : TeichRep Γ₀ := teichmullerCoeff q k2 (hk10.trans hk12) hk21 with hx2def
  obtain ⟨bR, hbR, hbn⟩ := ray_transition_coeff q hk10 hk12 hk21
  have hk1k2 : k1 * k2 < 1 := by nlinarith only [hk10, hk12, hk21]
  have hkr0 : 0 ≤ kr := div_nonneg (by linarith [hk12]) (by linarith [hk1k2])
  have hkr1 : kr < 1 := by
    rw [hkrdef, div_lt_one (by linarith [hk1k2])]
    nlinarith only [hk10, hk12, hk21]
  have hKle : bR.K ≤ (1 + kr) / (1 - kr) := by
    have hn0 := bR.normInf_nonneg
    have hn1 := bR.normInf_lt_one
    rw [BeltramiCoeff.K, div_le_div_iff₀ (by linarith [hn1]) (by linarith [hkr1])]
    nlinarith only [hbn, hn0, hn1, hkr0, hkr1]
  have hmc : IsMarkedCandidate x2 x1 (x2.w ∘ Function.invFun x1.w) := by
    refine ⟨fun t => ?_, ?_, ?_⟩
    · change x2.w (Function.invFun x1.w (x1.w (t : ℂ))) = x2.w (t : ℂ)
      rw [Function.leftInverse_invFun x1.w_injective]
    · intro W hW
      obtain ⟨γ, hγ, hyc⟩ := w_conj_of_mem_group x1 hW
      obtain ⟨W', hW', hxc⟩ := w_conj_of_mem_base x2 hγ
      exact ⟨W', hW', transition_conj hyc hxc⟩
    · intro W' hW'
      obtain ⟨γ, hγ, hxc⟩ := w_conj_of_mem_group x2 hW'
      obtain ⟨W, hW, hyc⟩ := w_conj_of_mem_base x1 hγ
      exact ⟨W, hW, transition_conj hyc hxc⟩
  exact teichDistG_le_of_candidate (hbR.isQCGeometric_K.mono hKle) hmc

/-- **Geodesic additivity of the Teichmüller ray**: for moduli `k₁ ≤ k₂` the distance
from the ray point of modulus `k₂` to the base splits through the ray point of modulus
`k₁`; the upper bound is the relative-coefficient candidate, the lower bound the triangle
inequality with the ray formula. -/
theorem teichDistG_teichmullerCoeff_add (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (q : QuadraticDifferential Γ₀) {k₁ k₂ : ℝ} (hk10 : 0 ≤ k₁) (hk12 : k₁ ≤ k₂)
    (hk21 : k₂ < 1) (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) :
    teichDistG (teichmullerCoeff q k₂ (hk10.trans hk12) hk21) (TeichRep.zero Γ₀)
      = teichDistG (teichmullerCoeff q k₂ (hk10.trans hk12) hk21)
          (teichmullerCoeff q k₁ hk10 (lt_of_le_of_lt hk12 hk21))
        + teichDistG (teichmullerCoeff q k₁ hk10 (lt_of_le_of_lt hk12 hk21))
          (TeichRep.zero Γ₀) := by
  have hd20 := teichDistG_teichmullerCoeff hΓ₀ hfree hcc q (hk10.trans hk12) hk21 hq0
  have hd10 := teichDistG_teichmullerCoeff hΓ₀ hfree hcc q hk10
    (lt_of_le_of_lt hk12 hk21) hq0
  have hrel := ray_transition_dist q hk10 hk12 hk21
  set kr : ℝ := (k₂ - k₁) / (1 - k₁ * k₂) with hkrdef
  have hk1k2 : k₁ * k₂ < 1 := by nlinarith only [hk10, hk12, hk21]
  have hd : (0:ℝ) < 1 - k₁ * k₂ := by linarith [hk1k2]
  have hkr0 : 0 ≤ kr := div_nonneg (by linarith [hk12]) (by linarith [hk1k2])
  have hkr1 : kr < 1 := by
    rw [hkrdef, div_lt_one hd]
    nlinarith only [hk10, hk12, hk21]
  have hKrpos : (0:ℝ) < (1 + kr) / (1 - kr) :=
    div_pos (by linarith [hkr0]) (by linarith [hkr1])
  have hK1pos : (0:ℝ) < (1 + k₁) / (1 - k₁) :=
    div_pos (by linarith [hk10]) (by linarith [hk12, hk21])
  have hKrK1 : (1 + kr) / (1 - kr) * ((1 + k₁) / (1 - k₁)) = (1 + k₂) / (1 - k₂) := by
    have h1 : (1:ℝ) - k₁ ≠ 0 := by nlinarith only [hk12, hk21]
    have h2 : (1:ℝ) - k₂ ≠ 0 := by nlinarith only [hk21]
    have h3 : (1:ℝ) - k₁ * k₂ ≠ 0 := ne_of_gt hd
    have hkrn : (1:ℝ) - kr ≠ 0 := by nlinarith only [hkr1]
    have h3' : (1:ℝ) - k₂ * k₁ ≠ 0 := by
      rw [mul_comm]
      exact h3
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hkrn h1) h2, hkrdef]
    field_simp
    ring
  have hKrne : (1 + kr) / (1 - kr) ≠ 0 := ne_of_gt hKrpos
  have hK1ne : (1 + k₁) / (1 - k₁) ≠ 0 := ne_of_gt hK1pos
  have hlogadd : (1/2) * Real.log ((1 + kr) / (1 - kr))
      + (1/2) * Real.log ((1 + k₁) / (1 - k₁))
      = (1/2) * Real.log ((1 + k₂) / (1 - k₂)) := by
    rw [← hKrK1, Real.log_mul hKrne hK1ne]
    ring
  refine le_antisymm (teichDistG_triangle _ _ _) ?_
  rw [hd10, hd20]
  linarith only [hrel, hlogadd]

/-! ## The recorded existence input -/

/-- **The existence half of Teichmüller's theorem — the open input of the equivariant
tier.** Every marked pair over a cocompact free Fuchsian base admits a Teichmüller-form
candidate in its class. The proof requires the Hamilton–Krushkal necessity of extremal
coefficients, the finite-dimensionality of the space of automorphic quadratic
differentials (the Riemann–Roch tier), and the variational dependence of the normalized
Beltrami solution on its coefficient; none of these tiers is available in this
development, and every consumer of form-existence must take this statement as a
hypothesis until they are. -/
theorem exists_teichmuller_form (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (x y : TeichRep Γ₀) :
    ∃ (q : QuadraticDifferential y.group) (k : ℝ) (F : ℂ → ℂ),
      0 ≤ k ∧ k < 1 ∧ IsTeichmullerCandidate x y q k F := by
  sorry

end RiemannDynamics

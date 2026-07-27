import RiemannDynamics.Teichmuller.QuadraticDifferential.Extremal
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

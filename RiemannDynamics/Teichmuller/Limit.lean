import RiemannDynamics.Teichmuller.Covolume
import RiemannDynamics.Teichmuller.ModAction

/-!
# Convergence of Mumford limits in the Teichmüller metric

The Mumford limit group of a thick sequence is realized as a point of Teichmüller space and
the sequence converges to it, modulo the moduli action, in the Teichmüller metric.

* `teichPseudoDist_le_of_candidate` — one candidate bounds the pseudodistance.
* `exists_teichRep_of_conjugating` — any normalized symmetric quasiconformal plane map
  conjugating `Γ₀` into Möbius transformations is the normalized solution of a Teichmüller
  representative.
* `exists_teichRep_pseudoDist_le_of_equivariant_qc` — a symmetric normalized
  `K`-quasiconformal map intertwining `y.group` with Möbius maps produces a representative
  `z` with `z.w = h ∘ y.w` and `d_T(z, y) ≤ ½ log K`.
* `tendsto_teichPseudoDist_zero_of_candidates` — dilatations `→ 1` give `d_T → 0`.
* `exists_equivariant_qc_conjugacy_K_to_one` — Marden stability: along the Mumford
  subsequence, for every `K > 1` the limit group is eventually conjugated onto the
  approximating groups by a symmetric `K`-quasiconformal plane map intertwining the
  generator tuples.
* `equivariant_on_group_of_equivariant_on_gens` — generator-level equivariance upgrades to
  group-level equivariance.
* `exists_limit_rep_of_equivariant_qc` — realization of the limit group as the Fuchsian
  group of a representative, up to real-affine Möbius conjugacy.
* `mumford_dT_subconvergence` — the endgame: thick sequences with a uniform area bound
  subconverge modulo the moduli action.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## Candidate and realization bricks -/

/-- A single quasiconformal candidate matching the boundary transition bounds the
Teichmüller pseudodistance by half the log of its dilatation. -/
theorem teichPseudoDist_le_of_candidate {x y : TeichRep Γ₀} {F : ℂ → ℂ} {K : ℝ}
    (hF : IsQCGeometric F K) (hb : ∀ t : ℝ, F (y.w t) = x.w t) :
    teichPseudoDist x y ≤ (1 / 2) * Real.log K := by
  have hmem : K ∈ dilatationSet x y := ⟨F, hF, hb⟩
  have hle : sInf (dilatationSet x y) ≤ K := csInf_le (bddBelow_dilatationSet x y) hmem
  have hpos : (0 : ℝ) < sInf (dilatationSet x y) :=
    lt_of_lt_of_le one_pos (one_le_sInf_dilatationSet x y)
  have hlog : Real.log (sInf (dilatationSet x y)) ≤ Real.log K :=
    Real.log_le_log hpos hle
  unfold teichPseudoDist
  linarith

/-- **Realization brick.** A normalized, conjugation-symmetric quasiconformal plane map that
conjugates every element of `Γ₀` to some Möbius transformation is the normalized solution of
a Teichmüller representative over `Γ₀`: its coefficient is symmetric and `Γ₀`-invariant. -/
theorem exists_teichRep_of_conjugating {g : ℂ → ℂ} {bg : BeltramiCoeff}
    (hg : IsQCAnalytic g bg) (hg0 : g 0 = 0) (hg1 : g 1 = 1)
    (hgsym : ∀ z : ℂ, g (starRingEnd ℂ z) = starRingEnd ℂ (g z))
    (hconj : ∀ γ ∈ Γ₀, ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, g (moebiusMap γ z) = moebiusMap W (g z)) :
    ∃ y : TeichRep Γ₀, y.w = g := by
  have hsymm : IsSymmetricBeltrami bg := by
    have hcc := isQCAnalytic_conj_conj hg
    have hfeq : (fun z => starRingEnd ℂ (g (starRingEnd ℂ z))) = g := by
      funext z
      rw [hgsym z, Complex.conj_conj]
    rw [hfeq] at hcc
    exact (isSymmetricBeltrami_iff_reflect bg).mpr (beltrami_coeff_unique_ae hcc hg)
  have hinv : IsInvariantBeltrami' Γ₀ bg := fun γ hγ =>
    isInvariantBeltrami'_single_of_moebius_conj hg γ (hconj γ hγ)
  exact ⟨⟨bg, hsymm, hinv⟩, ((⟨bg, hsymm, hinv⟩ : TeichRep Γ₀).w_unique hg hg0 hg1).symm⟩

/-- **Endgame brick.** A symmetric normalized `K`-quasiconformal plane map intertwining the
Fuchsian group of `y` with Möbius transformations produces a representative `z` whose
normalized solution is `h ∘ y.w`, at pseudodistance at most `½ log K` from `y`. Applied to a
sequence of Marden conjugacies with `K → 1` against the Mumford limit group this yields
`d_T`-convergence. -/
theorem exists_teichRep_pseudoDist_le_of_equivariant_qc {y : TeichRep Γ₀}
    {h : ℂ → ℂ} {bh : BeltramiCoeff} {K : ℝ}
    (hhqc : IsQCAnalytic h bh) (hK : IsQCGeometric h K)
    (hsym : ∀ z : ℂ, h (starRingEnd ℂ z) = starRingEnd ℂ (h z))
    (h0 : h 0 = 0) (h1 : h 1 = 1)
    (hequi : ∀ W ∈ y.group, ∃ W' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ u : ℂ, h (moebiusMap W u) = moebiusMap W' (h u)) :
    ∃ z : TeichRep Γ₀, z.w = h ∘ y.w ∧ teichPseudoDist z y ≤ (1 / 2) * Real.log K := by
  -- the composite is quasiconformal with some coefficient
  obtain ⟨bc, -, hbc⟩ := exists_isQCAnalytic_comp hhqc y.w_isQCAnalytic
  -- normalization of the composite
  have hc0 : (h ∘ y.w) 0 = 0 := by
    simp only [Function.comp_apply]
    rw [y.w_zero]
    exact h0
  have hc1 : (h ∘ y.w) 1 = 1 := by
    simp only [Function.comp_apply]
    rw [y.w_one]
    exact h1
  -- symmetry of the composite
  have hcsym : ∀ z : ℂ, (h ∘ y.w) (starRingEnd ℂ z) = starRingEnd ℂ ((h ∘ y.w) z) := by
    intro z
    simp only [Function.comp_apply]
    rw [y.w_conj z, hsym (y.w z)]
  -- null sets pull back through the quasiconformal `y.w`
  have hyg : IsQCGeometric y.w y.b.K := y.w_isQCAnalytic.isQCGeometric_K
  have hpre : ∀ N : Set ℂ, volume N = 0 → volume (y.w ⁻¹' N) = 0 := by
    intro N hN
    have hy := hyg.inverse_lusinN N hN
    have hset : ⇑(IsHomeomorph.homeomorph y.w hyg.2.1.isHomeomorph).symm '' N
        = y.w ⁻¹' N := by
      ext w
      constructor
      · rintro ⟨n, hn, rfl⟩
        have happ := (IsHomeomorph.homeomorph y.w hyg.2.1.isHomeomorph).apply_symm_apply n
        rw [IsHomeomorph.homeomorph_apply] at happ
        rw [Set.mem_preimage, happ]
        exact hn
      · intro hw
        refine ⟨y.w w, hw, ?_⟩
        have happ := (IsHomeomorph.homeomorph y.w hyg.2.1.isHomeomorph).symm_apply_apply w
        rwa [IsHomeomorph.homeomorph_apply] at happ
    rwa [hset] at hy
  -- the composite conjugates `Γ₀` into Möbius transformations
  have hcconj : ∀ γ ∈ Γ₀, ∃ W' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, (h ∘ y.w) (moebiusMap γ z) = moebiusMap W' ((h ∘ y.w) z) := by
    intro γ hγ
    obtain ⟨W, hWmem, haeW⟩ := y.mem_group_of hγ
    obtain ⟨W', haeW'⟩ := hequi W hWmem
    refine ⟨W', ?_⟩
    have haeW'' : ∀ᵐ z : ℂ, h (moebiusMap W (y.w z)) = moebiusMap W' (h (y.w z)) := by
      rw [ae_iff] at haeW' ⊢
      exact hpre _ haeW'
    filter_upwards [haeW, haeW''] with z hz1 hz2
    simp only [Function.comp_apply]
    rw [hz1]
    exact hz2
  -- realize the composite as a representative and use `h` itself as a candidate
  obtain ⟨z, hzw⟩ := exists_teichRep_of_conjugating hbc hc0 hc1 hcsym hcconj
  refine ⟨z, hzw, teichPseudoDist_le_of_candidate hK fun t => ?_⟩
  rw [hzw]
  rfl

/-- **Squeeze brick.** Candidates with dilatations tending to `1` give vanishing
pseudodistance in the limit. -/
theorem tendsto_teichPseudoDist_zero_of_candidates {x : ℕ → TeichRep Γ₀} {y : TeichRep Γ₀}
    {F : ℕ → ℂ → ℂ} {K : ℕ → ℝ} (hF : ∀ n, IsQCGeometric (F n) (K n))
    (hb : ∀ n, ∀ t : ℝ, F n (y.w t) = (x n).w t)
    (hK : Filter.Tendsto K Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => teichPseudoDist (x n) y) Filter.atTop (nhds 0) := by
  have hub : ∀ n, teichPseudoDist (x n) y ≤ (1 / 2) * Real.log (K n) := fun n =>
    teichPseudoDist_le_of_candidate (hF n) (hb n)
  have hlb : ∀ n, 0 ≤ teichPseudoDist (x n) y := fun n => teichPseudoDist_nonneg _ _
  have h1 : Filter.Tendsto (fun n => Real.log (K n)) Filter.atTop (nhds (Real.log 1)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto).comp hK
  rw [Real.log_one] at h1
  have h2 : Filter.Tendsto (fun n => (1 / 2 : ℝ) * Real.log (K n)) Filter.atTop
      (nhds ((1 / 2 : ℝ) * 0)) := h1.const_mul _
  rw [mul_zero] at h2
  exact squeeze_zero hlb hub h2

/-! ## Marden stability -/

/-- **Marden stability, generator form.** Along the Mumford subsequence, for every `K > 1`
the limit group is eventually conjugated onto the approximating groups by a symmetric
`K`-quasiconformal plane map intertwining the generator tuples. -/
theorem exists_equivariant_qc_conjugacy_K_to_one
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
    ∀ K : ℝ, 1 < K → ∀ᶠ n in Filter.atTop, ∃ H : ℂ → ℂ,
      IsQCGeometric H K ∧ (∀ z, H (starRingEnd ℂ z) = starRingEnd ℂ (H z)) ∧
      ∀ i, ∀ᵐ z : ℂ, H (moebiusMap (ρ i) z) = moebiusMap (gens n i) (H z) := by
  sorry

/-- Generator-level equivariance upgrades to group-level equivariance: products and
inverses compose the almost-everywhere identities, pulling null sets back through Möbius
maps and through the quasiconformal conjugacy. -/
theorem equivariant_on_group_of_equivariant_on_gens {ι : Type} [Finite ι]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {gens : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hmem : ∀ i, gens i ∈ Γ)
    {ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {H : ℂ → ℂ} {K : ℝ} (hH : IsQCGeometric H K)
    (hgen : ∀ i, ∀ᵐ z : ℂ, H (moebiusMap (ρ i) z) = moebiusMap (gens i) (H z)) :
    ∀ W ∈ Subgroup.closure (Set.range ρ), ∃ W' ∈ Γ,
      ∀ᵐ z : ℂ, H (moebiusMap W z) = moebiusMap W' (H z) := by
  -- a.e. facts transport through a plane Möbius map off its pole
  have haeMoeb : ∀ (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : ℂ → Prop),
      (∀ᵐ w : ℂ, P w) → ∀ᵐ z : ℂ, moebiusDenom δ z ≠ 0 → P (moebiusMap δ z) := by
    intro δ P hP
    have hopen : IsOpen {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom δ⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hP ⊢
    have himg : volume (moebiusMap δ⁻¹ ''
        (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le _)
        rw [measure_toMeasurable]
        exact hP.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap δ⁻¹) (fderiv ℝ (moebiusMap δ⁻¹) w)
            (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap δ⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap δ⁻¹)
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) := by
        intro a ha b hb hab
        have ha1 : moebiusMap δ (moebiusMap δ⁻¹ a) = a := by
          rw [moebiusMap_mul δ δ⁻¹ a ha.2, mul_inv_cancel, moebiusMap_one]
        have hb1 : moebiusMap δ (moebiusMap δ⁻¹ b) = b := by
          rw [moebiusMap_mul δ δ⁻¹ b hb.2, mul_inv_cancel, moebiusMap_one]
        rw [← ha1, ← hb1, hab]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom δ⁻¹ (moebiusMap δ z) * moebiusDenom δ z = 1 := by
      rw [moebiusDenom_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom δ⁻¹ (moebiusMap δ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap δ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusMap_one]
  -- a.e. avoidance of Möbius poles
  have haePole : ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, moebiusDenom δ z ≠ 0 := by
    intro δ
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact volume_moebiusDenom_zero δ
  -- a.e. avoidance of Möbius poles after the injective map `H`
  have hHinj : Function.Injective H := hH.2.1.isHomeomorph.bijective.injective
  have hpoleH : ∀ V : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, moebiusDenom V (H z) ≠ 0 := by
    intro V
    have hPsub : Set.Subsingleton {w : ℂ | moebiusDenom V w = 0} := by
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
        have hmul : (V 1 0 : ℂ) * w₁ = (V 1 0 : ℂ) * w₂ := by linear_combination h₁' - h₂'
        exact mul_left_cancel₀ hcC hmul
    have hpre : Set.Subsingleton (H ⁻¹' {w : ℂ | moebiusDenom V w = 0}) := by
      intro a ha b hb
      exact hHinj (hPsub ha hb)
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (hpre.measure_zero volume)
    simp only [Set.mem_setOf_eq, ne_eq, not_not] at hz
    exact hz
  intro W hW
  induction hW using Subgroup.closure_induction with
  | mem V hV =>
    obtain ⟨i, rfl⟩ := hV
    exact ⟨gens i, hmem i, hgen i⟩
  | one =>
    refine ⟨1, one_mem Γ, Filter.Eventually.of_forall fun z => ?_⟩
    rw [moebiusMap_one, moebiusMap_one]
  | mul u v _ _ ihu ihv =>
    obtain ⟨u', hu'm, haeU⟩ := ihu
    obtain ⟨v', hv'm, haeV⟩ := ihv
    refine ⟨u' * v', mul_mem hu'm hv'm, ?_⟩
    have hpull := haeMoeb v (fun w => H (moebiusMap u w) = moebiusMap u' (H w)) haeU
    filter_upwards [haePole v, haeV, hpull, hpoleH v'] with z hd2 h2 h1 hdV'
    rw [← moebiusMap_mul u v z hd2, h1 hd2, h2, moebiusMap_mul u' v' (H z) hdV']
  | inv u _ ihu =>
    obtain ⟨u', hu'm, hae⟩ := ihu
    refine ⟨u'⁻¹, inv_mem hu'm, ?_⟩
    have hpull := haeMoeb u⁻¹ (fun w => H (moebiusMap u w) = moebiusMap u' (H w)) hae
    have hWpull := haeMoeb u⁻¹ (fun w => moebiusDenom u' (H w) ≠ 0) (hpoleH u')
    filter_upwards [haePole u⁻¹, hpull, hWpull] with z hd hp hW2
    have hback : moebiusMap u (moebiusMap u⁻¹ z) = z := by
      rw [moebiusMap_mul u u⁻¹ z hd, mul_inv_cancel, moebiusMap_one]
    have hfz := hp hd
    rw [hback] at hfz
    rw [hfz, moebiusMap_mul u'⁻¹ u' (H (moebiusMap u⁻¹ z)) (hW2 hd), inv_mul_cancel,
      moebiusMap_one]

/-! ## Realization of the limit -/

/-- **Realization of the Mumford limit.** A symmetric quasiconformal plane map carrying the
Möbius action of the Fuchsian group of `x` into Möbius transformations produces a
representative `y` whose normalized solution renormalizes `H ∘ x.w` at its values over `0`
and `1`; the group of `y` is a real-affine Möbius conjugate of the image group. -/
theorem exists_limit_rep_of_equivariant_qc (x : TeichRep Γ₀)
    {H : ℂ → ℂ} {bH : BeltramiCoeff} (hH : IsQCAnalytic H bH)
    (hsym : ∀ z : ℂ, H (starRingEnd ℂ z) = starRingEnd ℂ (H z))
    (hequi : ∀ W ∈ x.group, ∃ V : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, H (moebiusMap W z) = moebiusMap V (H z)) :
    ∃ y : TeichRep Γ₀, y.w = fun z => (H (x.w z) - H 0) / (H 1 - H 0) := by
  obtain ⟨bc, -, hbc⟩ := exists_isQCAnalytic_comp hH x.w_isQCAnalytic
  -- symmetry of the coefficient of the composite `H ∘ x.w`
  have hsymm : IsSymmetricBeltrami bc := by
    have hcc := isQCAnalytic_conj_conj hbc
    have hfeq : (fun z => starRingEnd ℂ ((H ∘ x.w) (starRingEnd ℂ z))) = H ∘ x.w := by
      funext z
      simp only [Function.comp_apply]
      rw [x.w_conj z, hsym (x.w z), Complex.conj_conj]
    rw [hfeq] at hcc
    exact (isSymmetricBeltrami_iff_reflect bc).mpr (beltrami_coeff_unique_ae hcc hbc)
  -- null sets pull back through the quasiconformal `x.w`
  have hyg : IsQCGeometric x.w x.b.K := x.w_isQCAnalytic.isQCGeometric_K
  have hpre : ∀ N : Set ℂ, volume N = 0 → volume (x.w ⁻¹' N) = 0 := by
    intro N hN
    have hy := hyg.inverse_lusinN N hN
    have hset : ⇑(IsHomeomorph.homeomorph x.w hyg.2.1.isHomeomorph).symm '' N
        = x.w ⁻¹' N := by
      ext w
      constructor
      · rintro ⟨n, hn, rfl⟩
        have happ := (IsHomeomorph.homeomorph x.w hyg.2.1.isHomeomorph).apply_symm_apply n
        rw [IsHomeomorph.homeomorph_apply] at happ
        rw [Set.mem_preimage, happ]
        exact hn
      · intro hw
        refine ⟨x.w w, hw, ?_⟩
        have happ := (IsHomeomorph.homeomorph x.w hyg.2.1.isHomeomorph).symm_apply_apply w
        rwa [IsHomeomorph.homeomorph_apply] at happ
    rwa [hset] at hy
  -- invariance of the composite coefficient: chain the equivariance of `x.w` with `hequi`
  have hinv : IsInvariantBeltrami' Γ₀ bc := by
    intro γ hγ
    obtain ⟨W, hWmem, haeW⟩ := x.mem_group_of hγ
    obtain ⟨V, haeV⟩ := hequi W hWmem
    refine isInvariantBeltrami'_single_of_moebius_conj hbc γ ⟨V, ?_⟩
    have haeV' : ∀ᵐ z : ℂ, H (moebiusMap W (x.w z)) = moebiusMap V (H (x.w z)) := by
      rw [ae_iff] at haeV ⊢
      exact hpre _ haeV
    filter_upwards [haeW, haeV'] with z h1 h2
    simp only [Function.comp_apply]
    rw [h1]
    exact h2
  -- the renormalized composite is the normalized solution of the representative
  have hden : H 1 - H 0 ≠ 0 := sub_ne_zero.mpr fun hcon => one_ne_zero (hH.injective hcon)
  have haff : IsQCAnalytic (fun z => (H 1 - H 0)⁻¹ * (H ∘ x.w) z
      + -((H 1 - H 0)⁻¹ * H 0)) bc := hbc.affine_postcomp (inv_ne_zero hden) _
  have hfun : (fun z => (H 1 - H 0)⁻¹ * (H ∘ x.w) z + -((H 1 - H 0)⁻¹ * H 0))
      = fun z => (H (x.w z) - H 0) / (H 1 - H 0) := by
    funext z
    simp only [Function.comp_apply, div_eq_mul_inv]
    ring
  rw [hfun] at haff
  have h0 : (fun z => (H (x.w z) - H 0) / (H 1 - H 0)) 0 = 0 := by
    change (H (x.w 0) - H 0) / (H 1 - H 0) = 0
    rw [x.w_zero, sub_self, zero_div]
  have h1 : (fun z => (H (x.w z) - H 0) / (H 1 - H 0)) 1 = 1 := by
    change (H (x.w 1) - H 0) / (H 1 - H 0) = 1
    rw [x.w_one]
    exact div_self hden
  exact ⟨⟨bc, hsymm, hinv⟩, ((⟨bc, hsymm, hinv⟩ : TeichRep Γ₀).w_unique haff h0 h1).symm⟩

/-! ## The endgame -/

/-- **Mumford subconvergence in the Teichmüller metric.** A thick sequence with uniform area
bound subconverges, modulo the moduli action, to a point of Teichmüller space. -/
theorem mumford_dT_subconvergence (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {ε : ℝ} (hε : 0 < ε) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (x : ℕ → TeichRep Γ₀) (hthick : ∀ n, ε ≤ systoleRep (x n))
    (harea : ∀ n, HasAreaBound (x n).group A) :
    ∃ (φ : ℕ → ℕ) (F : ℕ → modGroup Γ₀) (y : TeichRep Γ₀), StrictMono φ ∧
      Filter.Tendsto (fun k => dist (F k • Teich.mk (x (φ k))) (Teich.mk y))
        Filter.atTop (nhds 0) := by
  classical
  -- §1 Thick Mumford subconvergence.
  obtain ⟨φ₀, gens, ρ, hφ₀, hgmem, hgclosure, hgconv, hgapρ, -, -, hccρ, -⟩ :=
    mumford_subconvergence_thick hΓ₀ hfree hcc hε hA x hthick harea
  -- §2 Marden stability along the subsequence.
  have hfuchn : ∀ k, IsFuchsianGroup (x (φ₀ k)).group := fun k =>
    TeichRep.isFuchsian_group hΓ₀ hfree (x (φ₀ k))
  have hgapn : ∀ k, ∀ γ ∈ (x (φ₀ k)).group, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| :=
    fun k γ hγ hnt => (trace_gap_of_systole hε (hthick (φ₀ k)) hγ hnt).1
  have hN4 := exists_equivariant_qc_conjugacy_K_to_one hε (fun k => (x (φ₀ k)).group)
    hfuchn hgapn gens hgmem ρ hgconv hgapρ hccρ
  -- §3 Diagonal extraction along dilatations `1 + 1/(j+1)`.
  have hKgt : ∀ j : ℕ, (1 : ℝ) < 1 + 1 / ((j : ℝ) + 1) := by
    intro j
    have h0 : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hNex : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ H : ℂ → ℂ,
      IsQCGeometric H (1 + 1 / ((j : ℝ) + 1)) ∧
      (∀ z, H (starRingEnd ℂ z) = starRingEnd ℂ (H z)) ∧
      ∀ i, ∀ᵐ z : ℂ, H (moebiusMap (ρ i) z) = moebiusMap (gens n i) (H z) := fun j =>
    Filter.eventually_atTop.mp (hN4 (1 + 1 / ((j : ℝ) + 1)) (hKgt j))
  choose N hN using hNex
  obtain ⟨ψ, hψ, hψge⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, N j ≤ ψ j := by
    refine ⟨fun j => Nat.rec (N 0) (fun k ih => max (N (k + 1)) (ih + 1)) j,
      strictMono_nat_of_lt_succ fun j => ?_, fun j => ?_⟩
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    · cases j with
      | zero => exact le_rfl
      | succ k => exact le_max_left _ _
  have hHex : ∀ j : ℕ, ∃ H : ℂ → ℂ, IsQCGeometric H (1 + 1 / ((j : ℝ) + 1)) ∧
      (∀ z, H (starRingEnd ℂ z) = starRingEnd ℂ (H z)) ∧
      ∀ i, ∀ᵐ z : ℂ, H (moebiusMap (ρ i) z) = moebiusMap (gens (ψ j) i) (H z) := fun j =>
    hN j (ψ j) (hψge j)
  choose H hHqc hHsym hHgen using hHex
  -- §4 Two-sided inverse packages for the conjugacies and the normalized solutions.
  have hInvPack : ∀ j : ℕ, ∃ G : ℂ → ℂ,
      (∀ z, G (H j z) = z) ∧ (∀ z, H j (G z) = z) ∧
      IsQCGeometric G (1 + 1 / ((j : ℝ) + 1)) ∧
      (∀ z, G (starRingEnd ℂ z) = starRingEnd ℂ (G z)) ∧
      (∀ N' : Set ℂ, volume N' = 0 → volume (G ⁻¹' N') = 0) ∧
      (∀ N' : Set ℂ, volume N' = 0 → volume (H j ⁻¹' N') = 0) := by
    intro j
    set G : ℂ → ℂ := ⇑((IsHomeomorph.homeomorph (H j) (hHqc j).2.1.isHomeomorph).symm)
      with hGdef
    have hL : ∀ z, G (H j z) = z := by
      intro z
      have h := (IsHomeomorph.homeomorph (H j) (hHqc j).2.1.isHomeomorph).symm_apply_apply z
      rwa [IsHomeomorph.homeomorph_apply] at h
    have hR : ∀ z, H j (G z) = z := by
      intro z
      have h := (IsHomeomorph.homeomorph (H j) (hHqc j).2.1.isHomeomorph).apply_symm_apply z
      rwa [IsHomeomorph.homeomorph_apply] at h
    have hinj : Function.Injective (H j) := Function.LeftInverse.injective hL
    have hsymG : ∀ z, G (starRingEnd ℂ z) = starRingEnd ℂ (G z) := by
      intro z
      apply hinj
      rw [hR, hHsym j (G z), hR]
    have hpreG : ∀ N' : Set ℂ, volume N' = 0 → volume (G ⁻¹' N') = 0 := by
      intro N' hN'
      have himg := (hHqc j).lusinN N' hN'
      have hset : H j '' N' = G ⁻¹' N' := by
        ext v
        constructor
        · rintro ⟨n', hn', rfl⟩
          rw [Set.mem_preimage, hL]
          exact hn'
        · intro hv
          exact ⟨G v, hv, hR v⟩
      rwa [hset] at himg
    have hpreH : ∀ N' : Set ℂ, volume N' = 0 → volume (H j ⁻¹' N') = 0 := by
      intro N' hN'
      have himg := (hHqc j).inverse_lusinN N' hN'
      rw [← hGdef] at himg
      have hset : G '' N' = H j ⁻¹' N' := by
        ext w
        constructor
        · rintro ⟨n', hn', rfl⟩
          rw [Set.mem_preimage, hR]
          exact hn'
        · intro hw
          exact ⟨H j w, hw, hL w⟩
      rwa [hset] at himg
    have hqcG : IsQCGeometric G (1 + 1 / ((j : ℝ) + 1)) := by
      rw [hGdef]
      exact isQCGeometric_inv_of_isQCGeometric (hHqc j)
    exact ⟨G, hL, hR, hqcG, hsymG, hpreG, hpreH⟩
  choose Hinv hHinvL hHinvR hHinvQC hHinvSym hHinvPre hHPre using hInvPack
  have hxPack : ∀ n : ℕ, ∃ G : ℂ → ℂ,
      (∀ z, G ((x n).w z) = z) ∧ (∀ z, (x n).w (G z) = z) ∧
      IsQCGeometric G ((x n).b.K) ∧
      (∀ z, G (starRingEnd ℂ z) = starRingEnd ℂ (G z)) ∧
      (∀ N' : Set ℂ, volume N' = 0 → volume (G ⁻¹' N') = 0) ∧
      (∀ N' : Set ℂ, volume N' = 0 → volume ((x n).w ⁻¹' N') = 0) := by
    intro n
    have hyg : IsQCGeometric (x n).w (x n).b.K := (x n).w_isQCAnalytic.isQCGeometric_K
    set G : ℂ → ℂ := ⇑((IsHomeomorph.homeomorph (x n).w hyg.2.1.isHomeomorph).symm)
      with hGdef
    have hL : ∀ z, G ((x n).w z) = z := by
      intro z
      have h := (IsHomeomorph.homeomorph (x n).w hyg.2.1.isHomeomorph).symm_apply_apply z
      rwa [IsHomeomorph.homeomorph_apply] at h
    have hR : ∀ z, (x n).w (G z) = z := by
      intro z
      have h := (IsHomeomorph.homeomorph (x n).w hyg.2.1.isHomeomorph).apply_symm_apply z
      rwa [IsHomeomorph.homeomorph_apply] at h
    have hsymG : ∀ z, G (starRingEnd ℂ z) = starRingEnd ℂ (G z) := by
      intro z
      apply (x n).w_injective
      rw [hR, (x n).w_conj (G z), hR]
    have hpreG : ∀ N' : Set ℂ, volume N' = 0 → volume (G ⁻¹' N') = 0 := by
      intro N' hN'
      have himg := hyg.lusinN N' hN'
      have hset : (x n).w '' N' = G ⁻¹' N' := by
        ext v
        constructor
        · rintro ⟨n', hn', rfl⟩
          rw [Set.mem_preimage, hL]
          exact hn'
        · intro hv
          exact ⟨G v, hv, hR v⟩
      rwa [hset] at himg
    have hpreW : ∀ N' : Set ℂ, volume N' = 0 → volume ((x n).w ⁻¹' N') = 0 := by
      intro N' hN'
      have himg := hyg.inverse_lusinN N' hN'
      rw [← hGdef] at himg
      have hset : G '' N' = (x n).w ⁻¹' N' := by
        ext w
        constructor
        · rintro ⟨n', hn', rfl⟩
          rw [Set.mem_preimage, hR]
          exact hn'
        · intro hw
          exact ⟨(x n).w w, hw, hL w⟩
      rwa [hset] at himg
    have hqcG : IsQCGeometric G ((x n).b.K) := by
      rw [hGdef]
      exact isQCGeometric_inv_of_isQCGeometric hyg
    exact ⟨G, hL, hR, hqcG, hsymG, hpreG, hpreW⟩
  choose xinv hxL hxR hxQC hxSym hxPreInv hxPre using hxPack
  -- §5 Inverted generator identities and group-level upgrades.
  have hHinvGen : ∀ j i, ∀ᵐ u : ℂ,
      Hinv j (moebiusMap (gens (ψ j) i) u) = moebiusMap (ρ i) (Hinv j u) := by
    intro j i
    have hup : ∀ᵐ u : ℂ, H j (moebiusMap (ρ i) (Hinv j u))
        = moebiusMap (gens (ψ j) i) (H j (Hinv j u)) := by
      have h := hHgen j i
      rw [ae_iff] at h ⊢
      exact hHinvPre j _ h
    filter_upwards [hup] with u hu
    rw [hHinvR j u] at hu
    calc Hinv j (moebiusMap (gens (ψ j) i) u)
        = Hinv j (H j (moebiusMap (ρ i) (Hinv j u))) := by rw [hu]
      _ = moebiusMap (ρ i) (Hinv j u) := hHinvL j _
  have hup_fwd : ∀ j, ∀ V ∈ Subgroup.closure (Set.range ρ), ∃ V' ∈ (x (φ₀ (ψ j))).group,
      ∀ᵐ z : ℂ, H j (moebiusMap V z) = moebiusMap V' (H j z) := fun j =>
    equivariant_on_group_of_equivariant_on_gens (fun i => hgmem (ψ j) i) (hHqc j)
      (hHgen j)
  have hup_bwd : ∀ j, ∀ V' ∈ (x (φ₀ (ψ j))).group, ∃ V ∈ Subgroup.closure (Set.range ρ),
      ∀ᵐ z : ℂ, Hinv j (moebiusMap V' z) = moebiusMap V (Hinv j z) := by
    intro j V' hV'
    refine equivariant_on_group_of_equivariant_on_gens
      (fun i => Subgroup.subset_closure (Set.mem_range_self i)) (hHinvQC j) (hHinvGen j)
      V' ?_
    rw [hgclosure (ψ j)]
    exact hV'
  -- §6 Realization of the limit as a representative.
  obtain ⟨b0, -, hb0⟩ := isQCAnalytic_of_isQCGeometric (hHinvQC 0).1 (hHinvQC 0)
  have hequi0 : ∀ W ∈ (x (φ₀ (ψ 0))).group, ∃ V : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, Hinv 0 (moebiusMap W z) = moebiusMap V (Hinv 0 z) := by
    intro W hW
    obtain ⟨V, -, hae⟩ := hup_bwd 0 W hW
    exact ⟨V, hae⟩
  obtain ⟨y, hyw⟩ := exists_limit_rep_of_equivariant_qc (x (φ₀ (ψ 0))) hb0
    (hHinvSym 0) hequi0
  -- §7 The connecting homeomorphisms.
  have hGpack : ∀ j : ℕ, ∃ G : ℂ ≃ₜ ℂ,
      ⇑G = fun z => xinv (φ₀ (ψ j)) (H j (Hinv 0 ((x (φ₀ (ψ 0))).w z))) := by
    intro j
    refine ⟨{ toFun := fun z => xinv (φ₀ (ψ j)) (H j (Hinv 0 ((x (φ₀ (ψ 0))).w z)))
              invFun := fun z => xinv (φ₀ (ψ 0)) (H 0 (Hinv j ((x (φ₀ (ψ j))).w z)))
              left_inv := fun z => by
                simp only []
                rw [hxR (φ₀ (ψ j)), hHinvL j, hHinvR 0, hxL (φ₀ (ψ 0))]
              right_inv := fun z => by
                simp only []
                rw [hxR (φ₀ (ψ 0)), hHinvL 0, hHinvR j, hxL (φ₀ (ψ j))]
              continuous_toFun := ((hxQC (φ₀ (ψ j))).2.1.isHomeomorph.continuous).comp
                (((hHqc j).2.1.isHomeomorph.continuous).comp
                  (((hHinvQC 0).2.1.isHomeomorph.continuous).comp
                    ((x (φ₀ (ψ 0))).w_isQCAnalytic.1.1.continuous)))
              continuous_invFun := ((hxQC (φ₀ (ψ 0))).2.1.isHomeomorph.continuous).comp
                (((hHqc 0).2.1.isHomeomorph.continuous).comp
                  (((hHinvQC j).2.1.isHomeomorph.continuous).comp
                    ((x (φ₀ (ψ j))).w_isQCAnalytic.1.1.continuous))) }, rfl⟩
  choose Gj hGjcoe using hGpack
  -- §8 The connecting maps are moduli-group elements.
  have hGmem : ∀ j : ℕ, Gj j ∈ modGroup Γ₀ := by
    intro j
    -- assembly of a chain of four conjugation identities into one for `Gj j`
    have hassemble : ∀ γ γ' W V V' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∀ᵐ z : ℂ, (x (φ₀ (ψ 0))).w (moebiusMap γ z)
          = moebiusMap W ((x (φ₀ (ψ 0))).w z)) →
        (∀ᵐ w : ℂ, Hinv 0 (moebiusMap W w) = moebiusMap V (Hinv 0 w)) →
        (∀ᵐ v : ℂ, H j (moebiusMap V v) = moebiusMap V' (H j v)) →
        (∀ᵐ w : ℂ, xinv (φ₀ (ψ j)) (moebiusMap V' w)
          = moebiusMap γ' (xinv (φ₀ (ψ j)) w)) →
        ∀ᵐ z : ℂ, (Gj j) (moebiusMap γ z) = moebiusMap γ' ((Gj j) z) := by
      intro γ γ' W V V' h1 h2 h3 h4
      have hT2 : ∀ᵐ z : ℂ, Hinv 0 (moebiusMap W ((x (φ₀ (ψ 0))).w z))
          = moebiusMap V (Hinv 0 ((x (φ₀ (ψ 0))).w z)) := by
        rw [ae_iff] at h2 ⊢
        exact hxPre (φ₀ (ψ 0)) _ h2
      have hT3 : ∀ᵐ z : ℂ, H j (moebiusMap V (Hinv 0 ((x (φ₀ (ψ 0))).w z)))
          = moebiusMap V' (H j (Hinv 0 ((x (φ₀ (ψ 0))).w z))) := by
        have hstep : ∀ᵐ u : ℂ, H j (moebiusMap V (Hinv 0 u))
            = moebiusMap V' (H j (Hinv 0 u)) := by
          rw [ae_iff] at h3 ⊢
          exact hHinvPre 0 _ h3
        rw [ae_iff] at hstep ⊢
        exact hxPre (φ₀ (ψ 0)) _ hstep
      have hT4 : ∀ᵐ z : ℂ,
          xinv (φ₀ (ψ j)) (moebiusMap V' (H j (Hinv 0 ((x (φ₀ (ψ 0))).w z))))
          = moebiusMap γ' (xinv (φ₀ (ψ j)) (H j (Hinv 0 ((x (φ₀ (ψ 0))).w z)))) := by
        have hs1 : ∀ᵐ u : ℂ, xinv (φ₀ (ψ j)) (moebiusMap V' (H j u))
            = moebiusMap γ' (xinv (φ₀ (ψ j)) (H j u)) := by
          rw [ae_iff] at h4 ⊢
          exact hHPre j _ h4
        have hs2 : ∀ᵐ u : ℂ, xinv (φ₀ (ψ j)) (moebiusMap V' (H j (Hinv 0 u)))
            = moebiusMap γ' (xinv (φ₀ (ψ j)) (H j (Hinv 0 u))) := by
          rw [ae_iff] at hs1 ⊢
          exact hHinvPre 0 _ hs1
        rw [ae_iff] at hs2 ⊢
        exact hxPre (φ₀ (ψ 0)) _ hs2
      filter_upwards [h1, hT2, hT3, hT4] with z g1 g2 g3 g4
      simp only [hGjcoe j]
      rw [g1, g2, g3, g4]
    -- inversion of an `(x (φ₀ (ψ j))).w`-conjugation identity through its inverse
    have hxinvert : ∀ γ' V' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∀ᵐ z : ℂ, (x (φ₀ (ψ j))).w (moebiusMap γ' z)
          = moebiusMap V' ((x (φ₀ (ψ j))).w z)) →
        ∀ᵐ w : ℂ, xinv (φ₀ (ψ j)) (moebiusMap V' w)
          = moebiusMap γ' (xinv (φ₀ (ψ j)) w) := by
      intro γ' V' h4'
      have htrans : ∀ᵐ w : ℂ, (x (φ₀ (ψ j))).w (moebiusMap γ' (xinv (φ₀ (ψ j)) w))
          = moebiusMap V' ((x (φ₀ (ψ j))).w (xinv (φ₀ (ψ j)) w)) := by
        rw [ae_iff] at h4' ⊢
        exact hxPreInv (φ₀ (ψ j)) _ h4'
      filter_upwards [htrans] with w hw
      rw [hxR (φ₀ (ψ j)) w] at hw
      calc xinv (φ₀ (ψ j)) (moebiusMap V' w)
          = xinv (φ₀ (ψ j)) ((x (φ₀ (ψ j))).w (moebiusMap γ' (xinv (φ₀ (ψ j)) w))) := by
            rw [hw]
        _ = moebiusMap γ' (xinv (φ₀ (ψ j)) w) := hxL (φ₀ (ψ j)) _
    have hcomp := (hxQC (φ₀ (ψ j))).comp ((hHqc j).comp ((hHinvQC 0).comp
      ((x (φ₀ (ψ 0))).w_isQCAnalytic.isQCGeometric_K)))
    have hqcGj : ∃ Kc : ℝ, IsQCGeometric (⇑(Gj j)) Kc := by
      rw [hGjcoe j]
      exact ⟨_, hcomp⟩
    refine mem_modGroup_iff.mpr ⟨hqcGj, ?_, ?_, ?_⟩
    · -- conjugation symmetry
      intro z
      simp only [hGjcoe j]
      rw [(x (φ₀ (ψ 0))).w_conj z, hHinvSym 0, hHsym j, hxSym (φ₀ (ψ j))]
    · -- Γ₀-compatibility, forward
      intro γ hγ
      obtain ⟨W, hWmem, h1⟩ := (x (φ₀ (ψ 0))).mem_group_of hγ
      obtain ⟨V, hVmem, h2⟩ := hup_bwd 0 W hWmem
      obtain ⟨V', hV'mem, h3⟩ := hup_fwd j V hVmem
      have hV'c : V' ∈ fuchsianImageCarrier Γ₀ (x (φ₀ (ψ j))).w := hV'mem
      obtain ⟨γ', hγ'Γ, h4'⟩ := hV'c
      exact ⟨γ', hγ'Γ, hassemble γ γ' W V V' h1 h2 h3 (hxinvert γ' V' h4')⟩
    · -- Γ₀-compatibility, backward
      intro γ' hγ'
      obtain ⟨V', hV'mem, h1'⟩ := (x (φ₀ (ψ j))).mem_group_of hγ'
      obtain ⟨V, hVmem, h2'⟩ := hup_bwd j V' hV'mem
      obtain ⟨W, hWmem, h3'⟩ := hup_fwd 0 V hVmem
      have hWc : W ∈ fuchsianImageCarrier Γ₀ (x (φ₀ (ψ 0))).w := hWmem
      obtain ⟨γ, hγΓ, h1⟩ := hWc
      -- invert the `Hinv j`-identity into an `H j`-identity
      have h3 : ∀ᵐ v : ℂ, H j (moebiusMap V v) = moebiusMap V' (H j v) := by
        have htrans : ∀ᵐ v : ℂ, Hinv j (moebiusMap V' (H j v))
            = moebiusMap V (Hinv j (H j v)) := by
          rw [ae_iff] at h2' ⊢
          exact hHPre j _ h2'
        filter_upwards [htrans] with v hv
        rw [hHinvL j v] at hv
        calc H j (moebiusMap V v) = H j (Hinv j (moebiusMap V' (H j v))) := by rw [← hv]
          _ = moebiusMap V' (H j v) := hHinvR j _
      -- invert the `H 0`-identity into an `Hinv 0`-identity
      have h2 : ∀ᵐ w : ℂ, Hinv 0 (moebiusMap W w) = moebiusMap V (Hinv 0 w) := by
        have htrans : ∀ᵐ w : ℂ, H 0 (moebiusMap V (Hinv 0 w))
            = moebiusMap W (H 0 (Hinv 0 w)) := by
          rw [ae_iff] at h3' ⊢
          exact hHinvPre 0 _ h3'
        filter_upwards [htrans] with w hw
        rw [hHinvR 0 w] at hw
        calc Hinv 0 (moebiusMap W w) = Hinv 0 (H 0 (moebiusMap V (Hinv 0 w))) := by
              rw [hw]
          _ = moebiusMap V (Hinv 0 w) := hHinvL 0 _
      exact ⟨γ, hγΓ, hassemble γ γ' W V V' h1 h2 h3 (hxinvert γ' V' h1')⟩
  -- §9 Boundary formulas of the pulled representatives and the candidate maps.
  have hd0ne : Hinv 0 1 - Hinv 0 0 ≠ 0 := by
    refine sub_ne_zero.mpr fun hcon => ?_
    have h := congrArg (H 0) hcon
    rw [hHinvR 0, hHinvR 0] at h
    exact one_ne_zero h
  have hdjne : ∀ j : ℕ, H j (Hinv 0 1) - H j (Hinv 0 0) ≠ 0 := by
    intro j
    refine sub_ne_zero.mpr fun hcon => ?_
    have h := congrArg (Hinv j) hcon
    rw [hHinvL j, hHinvL j] at h
    have h2 := congrArg (H 0) h
    rw [hHinvR 0, hHinvR 0] at h2
    exact one_ne_zero h2
  have hxG : ∀ j : ℕ, ∀ z : ℂ, (x (φ₀ (ψ j))).w ((Gj j) z)
      = H j (Hinv 0 ((x (φ₀ (ψ 0))).w z)) := by
    intro j z
    simp only [hGjcoe j]
    exact hxR (φ₀ (ψ j)) _
  have hxG0 : ∀ j : ℕ, (x (φ₀ (ψ j))).w ((Gj j) 0) = H j (Hinv 0 0) := by
    intro j
    rw [hxG j 0, (x (φ₀ (ψ 0))).w_zero]
  have hxG1 : ∀ j : ℕ, (x (φ₀ (ψ j))).w ((Gj j) 1) = H j (Hinv 0 1) := by
    intro j
    rw [hxG j 1, (x (φ₀ (ψ 0))).w_one]
  have hFqc : ∀ j : ℕ, IsQCGeometric
      (affineMap (H j (Hinv 0 1) - H j (Hinv 0 0))⁻¹
          (-((H j (Hinv 0 1) - H j (Hinv 0 0))⁻¹ * H j (Hinv 0 0)))
        ∘ (H j ∘ affineMap (Hinv 0 1 - Hinv 0 0) (Hinv 0 0)))
      (1 + 1 / ((j : ℝ) + 1)) := fun j =>
    isQCGeometric_affine_comp
      (isQCGeometric_comp_affine (hHqc j) hd0ne (Hinv 0 0)) (inv_ne_zero (hdjne j))
  have hFb : ∀ j : ℕ, ∀ t : ℝ,
      (affineMap (H j (Hinv 0 1) - H j (Hinv 0 0))⁻¹
          (-((H j (Hinv 0 1) - H j (Hinv 0 0))⁻¹ * H j (Hinv 0 0)))
        ∘ (H j ∘ affineMap (Hinv 0 1 - Hinv 0 0) (Hinv 0 0))) (y.w (t : ℂ))
      = ((x (φ₀ (ψ j))).pull (Gj j) (hGmem j)).w (t : ℂ) := by
    intro j t
    have hyt : y.w (t : ℂ) = (Hinv 0 ((x (φ₀ (ψ 0))).w (t : ℂ)) - Hinv 0 0)
        / (Hinv 0 1 - Hinv 0 0) := by
      rw [hyw]
    rw [hyt]
    simp only [TeichRep.pull_w' (x (φ₀ (ψ j))) (Gj j) (hGmem j), Function.comp_apply,
      affineMap_apply]
    rw [hxG j (t : ℂ), hxG0 j, hxG1 j]
    have hinner : (Hinv 0 1 - Hinv 0 0) * ((Hinv 0 ((x (φ₀ (ψ 0))).w (t : ℂ)) - Hinv 0 0)
        / (Hinv 0 1 - Hinv 0 0)) + Hinv 0 0 = Hinv 0 ((x (φ₀ (ψ 0))).w (t : ℂ)) := by
      field_simp
      ring
    rw [hinner, div_eq_mul_inv]
    ring
  -- §10 Squeeze in the Teichmüller metric.
  have hKlim : Filter.Tendsto (fun j : ℕ => 1 + 1 / ((j : ℝ) + 1)) Filter.atTop
      (nhds 1) := by
    have h0 : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop
        (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := h0.const_add (1 : ℝ)
    rwa [add_zero] at h1
  have hmain := tendsto_teichPseudoDist_zero_of_candidates hFqc hFb hKlim
  have hsmul : ∀ j : ℕ, ((⟨Gj j, hGmem j⟩ : modGroup Γ₀)⁻¹) • Teich.mk (x (φ₀ (ψ j)))
      = Teich.mk ((x (φ₀ (ψ j))).pull (Gj j) (hGmem j)) := by
    intro j
    rw [Teich.smul_mk, inv_inv]
  have hdist : ∀ j : ℕ,
      dist (((⟨Gj j, hGmem j⟩ : modGroup Γ₀)⁻¹) • Teich.mk (x (φ₀ (ψ j)))) (Teich.mk y)
      = teichPseudoDist ((x (φ₀ (ψ j))).pull (Gj j) (hGmem j)) y := by
    intro j
    rw [hsmul j]
    exact Teich.dist_mk _ _
  refine ⟨fun j => φ₀ (ψ j), fun j => (⟨Gj j, hGmem j⟩ : modGroup Γ₀)⁻¹, y,
    hφ₀.comp hψ, ?_⟩
  exact hmain.congr fun j => (hdist j).symm

end RiemannDynamics

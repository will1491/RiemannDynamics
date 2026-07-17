import RiemannDynamics.Teichmuller.Covolume
import RiemannDynamics.Teichmuller.ModAction
import RiemannDynamics.Teichmuller.UpperQC

/-!
# Convergence of Mumford limits in the Teichmüller metric

The Mumford limit group of a thick sequence is realized as a point of Teichmüller space and
the sequence converges to it, modulo upper-half-plane re-markings, in the Teichmüller
metric.

* `teichPseudoDist_le_of_candidate` — one candidate bounds the pseudodistance.
* `exists_teichRep_of_conjugating` — any normalized symmetric quasiconformal plane map
  conjugating `Γ₀` into Möbius transformations is the normalized solution of a Teichmüller
  representative.
* `exists_teichRep_pseudoDist_le_of_equivariant_qc` — a symmetric normalized
  `K`-quasiconformal map intertwining `y.group` with Möbius maps produces a representative
  `z` with `z.w = h ∘ y.w` and `d_T(z, y) ≤ ½ log K`.
* `tendsto_teichPseudoDist_zero_of_candidates` — dilatations `→ 1` give `d_T → 0`.
* `equivariant_on_group_of_equivariant_on_gens` — generator-level equivariance upgrades to
  group-level equivariance, almost everywhere on the plane.
* `equivariant_on_group_of_equivariant_on_gens_upper` — the pole-free upgrade on the upper
  half plane, with the inverse identities.
* `exists_teichRep_ofUpper_of_conjugating` — realization: an upper-half-plane
  quasiconformal map conjugating `Γ₀`-Möbius maps into Möbius maps is, up to coefficient,
  the solution of a Teichmüller representative.
* `exists_limit_rep_of_equivariant_qc` — realization of the limit group as the Fuchsian
  group of a representative, up to real-affine Möbius conjugacy.
* `isQCGeometric_K_of_upper_moebius_factor` — a symmetric plane quasiconformal map whose
  upper restriction factors as Möbius ∘ (κ-coefficient map) ∘ Möbius is
  `(1+κ)/(1−κ)`-quasiconformal.
* `mumford_dT_subconvergence` — the endgame: thick sequences with a uniform area bound
  subconverge, modulo upper-half-plane re-markings, in the Teichmüller metric.
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

/-! ## Group-level upgrades of generator equivariance -/

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

/-- **Group-level upgrade on the upper half plane.** Generator-level exact equivariance of
an upper-half-plane quasiconformal conjugacy upgrades to the closure of the generator
tuple, pole-free, together with the inverse identities: products and inverses compose the
pointwise identities through `moebiusMap_mul`, with denominators discharged off the real
axis. -/
theorem equivariant_on_group_of_equivariant_on_gens_upper {ι : Type}
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {gens : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hmem : ∀ i, gens i ∈ Γ)
    {ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (hgen : ∀ i, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap (ρ i) z) = moebiusMap (gens i) (h z)) :
    ∀ W ∈ Subgroup.closure (Set.range ρ), ∃ W' ∈ Γ,
      (∀ z : ℂ, 0 < z.im → h (moebiusMap W z) = moebiusMap W' (h z)) ∧
      (∀ z : ℂ, 0 < z.im → hinv (moebiusMap W' z) = moebiusMap W (hinv z)) := by
  sorry

/-- **Realization on the upper half plane.** An upper-half-plane quasiconformal map with
coefficient bound below `1` conjugating the `Γ₀`-Möbius action into Möbius maps on the
upper half plane solves the Beltrami equation of a Teichmüller representative there: its
Beltrami datum is invariant by the chain rule and extends symmetrically. -/
theorem exists_teichRep_ofUpper_of_conjugating
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {v vinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1) (hv : IsQCUpper v vinv κ)
    (hconj : ∀ γ ∈ Γ₀, ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → v (moebiusMap γ z) = moebiusMap W (v z)) :
    ∃ y : TeichRep Γ₀, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar v z = y.b.μ z * dz v z := by
  sorry

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

/-- **Dilatation of a Möbius-sandwiched candidate.** A conjugation-symmetric quasiconformal
plane homeomorphism whose restriction to the upper half plane factors as a real Möbius map,
an upper-half-plane quasiconformal map with Beltrami bound `κ`, and another real Möbius
map, is `(1 + κ)/(1 − κ)`-quasiconformal: pre- and post-composition by holomorphic maps
preserve the Beltrami quotient, symmetry transports the bound to the lower half plane, and
the real axis is null. -/
theorem isQCGeometric_K_of_upper_moebius_factor
    {C : ℂ → ℂ} {bC : BeltramiCoeff} (hC : IsQCAnalytic C bC)
    (hsym : ∀ z : ℂ, C (starRingEnd ℂ z) = starRingEnd ℂ (C z))
    {h hinv : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1) (hh : IsQCUpper h hinv κ)
    (R R₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hfac : ∀ z : ℂ, 0 < z.im → C z = moebiusMap R (h (moebiusMap R₀ z))) :
    IsQCGeometric C ((1 + κ) / (1 - κ)) := by
  sorry

/-- **Mumford subconvergence in the Teichmüller metric.** A thick sequence with uniform
area bound subconverges, modulo upper-half-plane re-markings, to a point of Teichmüller
space. -/
theorem mumford_dT_subconvergence (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {ε : ℝ} (hε : 0 < ε) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (x : ℕ → TeichRep Γ₀) (hthick : ∀ n, ε ≤ systoleRep (x n))
    (harea : ∀ n, HasAreaBound (x n).group A) :
    ∃ (φ : ℕ → ℕ) (F : ℕ → ModGroupUpper Γ₀) (y : TeichRep Γ₀), StrictMono φ ∧
      Filter.Tendsto (fun k => dist (F k • Teich.mk (x (φ k))) (Teich.mk y))
        Filter.atTop (nhds 0) := by
  sorry

end RiemannDynamics

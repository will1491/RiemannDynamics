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
  -- Möbius denominators of real matrices do not vanish off the real axis
  have hden : ∀ (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ), 0 < z.im →
      moebiusDenom V z ≠ 0 := fun V z hz =>
    moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt hz)
  -- the inverse identity is a formal consequence of the forward identity
  have hinv_of_fwd : ∀ U U' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ z : ℂ, 0 < z.im → h (moebiusMap U z) = moebiusMap U' (h z)) →
      ∀ z : ℂ, 0 < z.im → hinv (moebiusMap U' z) = moebiusMap U (hinv z) := by
    intro U U' hfwd z hz
    have hzin : 0 < (hinv z).im := hqc.mapsTo' z hz
    have hUin : 0 < (moebiusMap U (hinv z)).im := moebiusMap_im_pos U hzin
    calc hinv (moebiusMap U' z)
        = hinv (moebiusMap U' (h (hinv z))) := by rw [hqc.right_inv z hz]
      _ = hinv (h (moebiusMap U (hinv z))) := by rw [hfwd (hinv z) hzin]
      _ = moebiusMap U (hinv z) := hqc.left_inv _ hUin
  intro W hW
  induction hW using Subgroup.closure_induction with
  | mem V hV =>
    obtain ⟨i, rfl⟩ := hV
    exact ⟨gens i, hmem i, hgen i, hinv_of_fwd (ρ i) (gens i) (hgen i)⟩
  | one =>
    refine ⟨1, one_mem Γ, ?_⟩
    have hfwd : ∀ z : ℂ, 0 < z.im →
        h (moebiusMap (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) z) = moebiusMap 1 (h z) := by
      intro z _
      rw [moebiusMap_one, moebiusMap_one]
    exact ⟨hfwd, hinv_of_fwd 1 1 hfwd⟩
  | mul u v _ _ ihu ihv =>
    obtain ⟨u', hu'm, hfU, -⟩ := ihu
    obtain ⟨v', hv'm, hfV, -⟩ := ihv
    have hfwd : ∀ z : ℂ, 0 < z.im →
        h (moebiusMap (u * v) z) = moebiusMap (u' * v') (h z) := by
      intro z hz
      have hvz : 0 < (moebiusMap v z).im := moebiusMap_im_pos v hz
      have hhz : 0 < (h z).im := hqc.mapsTo z hz
      calc h (moebiusMap (u * v) z)
          = h (moebiusMap u (moebiusMap v z)) := by rw [moebiusMap_mul u v z (hden v z hz)]
        _ = moebiusMap u' (h (moebiusMap v z)) := hfU _ hvz
        _ = moebiusMap u' (moebiusMap v' (h z)) := by rw [hfV z hz]
        _ = moebiusMap (u' * v') (h z) := moebiusMap_mul u' v' (h z) (hden v' (h z) hhz)
    exact ⟨u' * v', mul_mem hu'm hv'm, hfwd, hinv_of_fwd (u * v) (u' * v') hfwd⟩
  | inv u _ ihu =>
    obtain ⟨u', hu'm, hfU, -⟩ := ihu
    have hfwd : ∀ z : ℂ, 0 < z.im →
        h (moebiusMap u⁻¹ z) = moebiusMap u'⁻¹ (h z) := by
      intro w hw
      have hzin : 0 < (moebiusMap u⁻¹ w).im := moebiusMap_im_pos u⁻¹ hw
      have hhin : 0 < (h (moebiusMap u⁻¹ w)).im := hqc.mapsTo _ hzin
      have hback : moebiusMap u (moebiusMap u⁻¹ w) = w := by
        rw [moebiusMap_mul u u⁻¹ w (hden u⁻¹ w hw), mul_inv_cancel, moebiusMap_one]
      have hfz := hfU (moebiusMap u⁻¹ w) hzin
      rw [hback] at hfz
      rw [hfz, moebiusMap_mul u'⁻¹ u' (h (moebiusMap u⁻¹ w)) (hden u' _ hhin),
        inv_mul_cancel, moebiusMap_one]
    exact ⟨u'⁻¹, inv_mem hu'm, hfwd, hinv_of_fwd u⁻¹ u'⁻¹ hfwd⟩

/-- The Wirtinger quotient of any plane map is measurable: both Wirtinger derivatives are
continuous linear images of the measurable full derivative. -/
theorem measurable_wirtingerQuotient (f : ℂ → ℂ) :
    Measurable (wirtingerQuotient f) := by
  have h1 : Measurable fun z : ℂ => (fderiv ℝ f z) 1 :=
    (measurable_fderiv ℝ f).apply_continuousLinearMap 1
  have hI : Measurable fun z : ℂ => (fderiv ℝ f z) Complex.I :=
    (measurable_fderiv ℝ f).apply_continuousLinearMap Complex.I
  have hdz : Measurable (dz f) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I)
    exact (h1.sub (hI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hdzbar : Measurable (dzbar f) := by
    change Measurable fun z : ℂ => (1 / 2 : ℂ)
      * ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I)
    exact (h1.add (hI.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  change Measurable fun z : ℂ => dzbar f z / dz f z
  exact hdzbar.div hdz

/-- Transport of an almost-everywhere plane statement along a real Möbius map: off the pole
of `γ`, the point `moebiusMap γ z` lies in the image of the full-measure set under the
inverse Möbius map, whose image of a null set is null by the change of variables. -/
theorem ae_moebius_transport (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (Q : ℂ → Prop)
    (hQ : ∀ᵐ w : ℂ, Q w) : ∀ᵐ z : ℂ, moebiusDenom γ z ≠ 0 → Q (moebiusMap γ z) := by
  have hopen : IsOpen {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0} := by
    have hc : Continuous (moebiusDenom γ⁻¹) := by
      unfold moebiusDenom
      fun_prop
    exact isOpen_compl_singleton.preimage hc
  rw [ae_iff] at hQ ⊢
  have himg : volume (moebiusMap γ⁻¹ ''
      (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0})) = 0 := by
    have hSmeas : MeasurableSet
        (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) :=
      (measurableSet_toMeasurable _ _).inter hopen.measurableSet
    have hSnull : volume
        (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) = 0 := by
      refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le _)
      rw [measure_toMeasurable]
      exact hQ.le
    have hfd : ∀ w ∈ toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0},
        HasFDerivWithinAt (moebiusMap γ⁻¹) (fderiv ℝ (moebiusMap γ⁻¹) w)
          (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) w := by
      intro w hw
      have hder := hasDerivAt_moebiusMap γ⁻¹ hw.2
      exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
    have hinjOn : Set.InjOn (moebiusMap γ⁻¹)
        (toMeasurable volume {w | ¬ Q w} ∩ {w : ℂ | moebiusDenom γ⁻¹ w ≠ 0}) := by
      intro a ha b hb hab
      have ha1 : moebiusMap γ (moebiusMap γ⁻¹ a) = a := by
        rw [moebiusMap_mul γ γ⁻¹ a ha.2, mul_inv_cancel, moebiusMap_one]
      have hb1 : moebiusMap γ (moebiusMap γ⁻¹ b) = b := by
        rw [moebiusMap_mul γ γ⁻¹ b hb.2, mul_inv_cancel, moebiusMap_one]
      rw [← ha1, ← hb1, hab]
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
      (fun _ => (1 : ℝ≥0∞))
    rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
    exact hcov
  refine measure_mono_null ?_ himg
  intro z hz
  simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
  obtain ⟨hden, hbad⟩ := hz
  have hd1 : moebiusDenom γ⁻¹ (moebiusMap γ z) * moebiusDenom γ z = 1 := by
    rw [moebiusDenom_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusDenom_one]
  have hdinv : moebiusDenom γ⁻¹ (moebiusMap γ z) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hd1
    exact zero_ne_one hd1
  refine ⟨moebiusMap γ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
  rw [moebiusMap_mul γ⁻¹ γ z hden, inv_mul_cancel, moebiusMap_one]

/-- The Wirtinger quotient of an upper-half-plane quasiconformal map with coefficient bound
`κ < 1` is essentially bounded below `1` on the upper half plane: the positive Jacobian
forces `‖∂v‖ > ‖∂̄v‖`, and the Beltrami bound divides out. -/
theorem wirtingerQuotient_bound_upper {v vinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hv : IsQCUpper v vinv κ) :
    eLpNormEssSup (wirtingerQuotient v) (volume.restrict {z : ℂ | 0 < z.im}) < 1 := by
  have hmax1 : max κ 0 < 1 := max_lt hκ zero_lt_one
  refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound ?_)
    (ENNReal.ofReal_lt_one.mpr hmax1)
  filter_upwards [hv.jac, hv.belt] with z hjac hbelt
  have hgs : ‖dzbar v z‖ < ‖dz v z‖ := by
    rw [det_fderiv_eq_wirtinger] at hjac
    nlinarith [norm_nonneg (dz v z), norm_nonneg (dzbar v z)]
  have hdzpos : 0 < ‖dz v z‖ := lt_of_le_of_lt (norm_nonneg _) hgs
  have hquot : ‖wirtingerQuotient v z‖ ≤ max κ 0 := by
    have hq : wirtingerQuotient v z = dzbar v z / dz v z := rfl
    rw [hq, norm_div, div_le_iff₀ hdzpos]
    calc ‖dzbar v z‖ ≤ κ * ‖dz v z‖ := hbelt
      _ ≤ max κ 0 * ‖dz v z‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal hquot

/-- The Wirtinger quotient of an upper-half-plane quasiconformal map conjugating the
`Γ₀`-Möbius action into Möbius maps satisfies the invariance cocycle on the upper half
plane: differentiate the exact conjugation identity through the holomorphic chain rules for
the Möbius pre- and post-compositions. -/
theorem wirtingerQuotient_invariant_upper
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {v vinv : ℂ → ℂ} {κ : ℝ} (hv : IsQCUpper v vinv κ)
    (hconj : ∀ γ ∈ Γ₀, ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → v (moebiusMap γ z) = moebiusMap W (v z)) :
    ∀ γ ∈ Γ₀, ∀ᵐ z : ℂ ∂(volume.restrict {z : ℂ | 0 < z.im}),
      wirtingerQuotient v (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = wirtingerQuotient v z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  intro γ hγ
  obtain ⟨W, hW⟩ := hconj γ hγ
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hUopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  -- almost-everywhere differentiability on the upper half plane from the positive Jacobian
  have hGood : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), DifferentiableAt ℝ v z := by
    filter_upwards [hv.jac] with z hjac
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hjac
    simp [ContinuousLinearMap.det] at hjac
  have hGoodG : ∀ᵐ z : ℂ, z ∈ {z : ℂ | 0 < z.im} → DifferentiableAt ℝ v z :=
    (ae_restrict_iff' hU).mp hGood
  have hGoodT := ae_moebius_transport γ
    (fun w : ℂ => w ∈ {z : ℂ | 0 < z.im} → DifferentiableAt ℝ v w) hGoodG
  -- differentiate the exact conjugation identity at a.e. point of the upper half plane
  filter_upwards [ae_restrict_of_ae hGoodT, ae_restrict_mem hU, ae_restrict_of_ae hGoodG]
    with z htrans hzU hgood
  have hz : 0 < z.im := hzU
  have hdenγ : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hz)
  have hγim : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
  have hDz : DifferentiableAt ℝ v z := hgood hzU
  have hDp : DifferentiableAt ℝ v (moebiusMap γ z) := htrans hdenγ hγim
  have hev : (fun w : ℂ => v (moebiusMap γ w))
      =ᶠ[nhds z] fun w : ℂ => moebiusMap W (v w) := by
    filter_upwards [hUopen.mem_nhds hz] with w hw
    exact hW w hw
  have hfde : fderiv ℝ (fun w : ℂ => v (moebiusMap γ w)) z
      = fderiv ℝ (fun w : ℂ => moebiusMap W (v w)) z := hev.fderiv_eq
  have hdzEq : dz (fun w : ℂ => v (moebiusMap γ w)) z
      = dz (fun w : ℂ => moebiusMap W (v w)) z := by
    unfold dz
    rw [hfde]
  have hdzbEq : dzbar (fun w : ℂ => v (moebiusMap γ w)) z
      = dzbar (fun w : ℂ => moebiusMap W (v w)) z := by
    unfold dzbar
    rw [hfde]
  have hγd := hasDerivAt_moebiusMap γ hdenγ
  have hFzim : (v z).im ≠ 0 := ne_of_gt (hv.mapsTo z hz)
  have hWd : moebiusDenom W (v z) ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero W hFzim
  have hWdd := hasDerivAt_moebiusMap W hWd
  have hLdz : dz (fun w : ℂ => v (moebiusMap γ w)) z
      = dz v (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹ := by
    have hcr := dz_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hLdzb : dzbar (fun w : ℂ => v (moebiusMap γ w)) z
      = dzbar v (moebiusMap γ z) * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹) := by
    have hcr := dzbar_comp_of_holomorphicAt hγd.differentiableAt hDp
    rw [hγd.deriv] at hcr
    simpa [Function.comp_def] using hcr
  have hWreal : DifferentiableAt ℝ (moebiusMap W) (v z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hWdd.differentiableAt).1
  have hdzW : dz (moebiusMap W) (v z) = ((moebiusDenom W (v z)) ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hWdd.differentiableAt, hWdd.deriv]
  have hdzbW : dzbar (moebiusMap W) (v z) = 0 :=
    dzbar_eq_zero_of_differentiableAt hWdd.differentiableAt
  have hRdz : dz (fun w : ℂ => moebiusMap W (v w)) z
      = ((moebiusDenom W (v z)) ^ 2)⁻¹ * dz v z := by
    have hcr := dz_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hRdzb : dzbar (fun w : ℂ => moebiusMap W (v w)) z
      = ((moebiusDenom W (v z)) ^ 2)⁻¹ * dzbar v z := by
    have hcr := dzbar_comp hDz hWreal
    rw [hdzW, hdzbW, zero_mul, add_zero] at hcr
    exact hcr
  have hEq1 : dz v (moebiusMap γ z) * ((moebiusDenom γ z) ^ 2)⁻¹
      = ((moebiusDenom W (v z)) ^ 2)⁻¹ * dz v z := by
    rw [← hLdz, ← hRdz]
    exact hdzEq
  have hEq2 : dzbar v (moebiusMap γ z) * starRingEnd ℂ (((moebiusDenom γ z) ^ 2)⁻¹)
      = ((moebiusDenom W (v z)) ^ 2)⁻¹ * dzbar v z := by
    rw [← hLdzb, ← hRdzb]
    exact hdzbEq
  -- divide out the two Wirtinger identities
  have hq1 : wirtingerQuotient v (moebiusMap γ z)
      = dzbar v (moebiusMap γ z) / dz v (moebiusMap γ z) := rfl
  have hq2 : wirtingerQuotient v z = dzbar v z / dz v z := rfl
  rw [hq1, hq2]
  have hD2 : (moebiusDenom γ z) ^ 2 ≠ 0 := pow_ne_zero 2 hdenγ
  have hE2 : (moebiusDenom W (v z)) ^ 2 ≠ 0 := pow_ne_zero 2 hWd
  have hcD : starRingEnd ℂ (moebiusDenom γ z) ≠ 0 := by simpa using hdenγ
  have hcD2 : (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 ≠ 0 := pow_ne_zero 2 hcD
  rw [map_inv₀, map_pow] at hEq2
  by_cases hdzz : dz v z = 0
  · have hA0 : dz v (moebiusMap γ z) = 0 := by
      have h5 := hEq1
      rw [hdzz, mul_zero] at h5
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact h6
      · exact absurd h6 (inv_ne_zero hD2)
    rw [hA0, hdzz, div_zero, div_zero, zero_mul, zero_mul]
  · have hAne : dz v (moebiusMap γ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hEq1
      rcases mul_eq_zero.mp hEq1.symm with h6 | h6
      · exact inv_ne_zero hE2 h6
      · exact hdzz h6
    have hAval : dz v (moebiusMap γ z)
        = ((moebiusDenom W (v z)) ^ 2)⁻¹ * dz v z * (moebiusDenom γ z) ^ 2 := by
      have h7 := congrArg (fun t : ℂ => t * (moebiusDenom γ z) ^ 2) hEq1
      simpa [inv_mul_cancel_right₀ hD2] using h7
    have hBval : dzbar v (moebiusMap γ z)
        = ((moebiusDenom W (v z)) ^ 2)⁻¹ * dzbar v z
          * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
      have h8 := congrArg (fun t : ℂ => t * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2) hEq2
      simpa [inv_mul_cancel_right₀ hcD2] using h8
    rw [hAval, hBval]
    field_simp

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
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  refine ⟨TeichRep.ofUpper Γ₀ (wirtingerQuotient v) (measurable_wirtingerQuotient v)
    (wirtingerQuotient_bound_upper hκ hv)
    (wirtingerQuotient_invariant_upper hv hconj), ?_⟩
  filter_upwards [hv.jac, ae_restrict_mem hU] with z hjac hzU
  have hdzne : dz v z ≠ 0 := by
    intro h0
    rw [det_fderiv_eq_wirtinger, h0] at hjac
    simp only [norm_zero] at hjac
    nlinarith [norm_nonneg (dzbar v z), sq_nonneg ‖dzbar v z‖]
  have hbμ : (TeichRep.ofUpper Γ₀ (wirtingerQuotient v) (measurable_wirtingerQuotient v)
      (wirtingerQuotient_bound_upper hκ hv)
      (wirtingerQuotient_invariant_upper hv hconj)).b.μ z = wirtingerQuotient v z := by
    change symmExtension (wirtingerQuotient v) z = wirtingerQuotient v z
    simp only [symmExtension]
    rw [if_pos hzU]
  rw [hbμ]
  change dzbar v z = dzbar v z / dz v z * dz v z
  rw [div_mul_cancel₀ _ hdzne]

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

/-- Almost-everywhere facts pull back through a plane Möbius map off its pole: the inverse
Möbius map is injective and differentiable off its own pole set, so it carries null sets to
null sets by the area formula, and points where the property fails at `moebiusMap δ z` land
in that image. -/
theorem ae_moebius_pullback (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : ℂ → Prop)
    (hP : ∀ᵐ w : ℂ, P w) :
    ∀ᵐ z : ℂ, moebiusDenom δ z ≠ 0 → P (moebiusMap δ z) := by
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

/-- Norm form of the sandwiched Wirtinger derivatives: multiplying a `κ`-bounded pair by
common holomorphic factors preserves the dilatation bound. -/
theorem norm_dilat {κ : ℝ} (A B X Y : ℂ) (h : ‖Y‖ ≤ κ * ‖X‖) :
    ‖A * (Y * starRingEnd ℂ B)‖ ≤ κ * ‖A * (X * B)‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_conj]
  calc ‖A‖ * (‖Y‖ * ‖B‖) ≤ ‖A‖ * ((κ * ‖X‖) * ‖B‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (norm_nonneg B))
          (norm_nonneg A)
    _ = κ * (‖A‖ * (‖X‖ * ‖B‖)) := by ring

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
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  -- the a.e. good set of `h` on the upper half plane, as a global implication
  have hgood : ∀ᵐ w : ℂ, 0 < w.im →
      (0 < (fderiv ℝ h w).det ∧ ‖dzbar h w‖ ≤ κ * ‖dz h w‖) :=
    (ae_restrict_iff' hUopen.measurableSet).mp (hh.jac.and hh.belt)
  -- pull the good set back through the Möbius map `R₀`
  have hpull := ae_moebius_pullback R₀
    (fun w => 0 < w.im → (0 < (fderiv ℝ h w).det ∧ ‖dzbar h w‖ ≤ κ * ‖dz h w‖)) hgood
  -- the dilatation bound on the upper half plane
  have hUp : ∀ᵐ z : ℂ, 0 < z.im → ‖dzbar C z‖ ≤ κ * ‖dz C z‖ := by
    filter_upwards [hpull] with z hz1
    intro hz
    have hden₀ : moebiusDenom R₀ z ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero R₀ (ne_of_gt hz)
    have hpz : 0 < (moebiusMap R₀ z).im := moebiusMap_im_pos R₀ hz
    obtain ⟨hdet_p, hbel_p⟩ := hz1 hden₀ hpz
    have hDp : DifferentiableAt ℝ h (moebiusMap R₀ z) := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hdet_p
      simp [ContinuousLinearMap.det] at hdet_p
    have hγd := hasDerivAt_moebiusMap R₀ hden₀
    have hhp : 0 < (h (moebiusMap R₀ z)).im := hh.mapsTo _ hpz
    have hdenR : moebiusDenom R (h (moebiusMap R₀ z)) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero R (ne_of_gt hhp)
    have hRd := hasDerivAt_moebiusMap R hdenR
    -- the factorization holds on a neighborhood, so the differentials agree
    have hev : C =ᶠ[nhds z] fun w => moebiusMap R (h (moebiusMap R₀ w)) := by
      filter_upwards [hUopen.mem_nhds hz] with w hw
      exact hfac w hw
    have hfd : fderiv ℝ C z = fderiv ℝ (fun w => moebiusMap R (h (moebiusMap R₀ w))) z :=
      hev.fderiv_eq
    have hdzE : dz C z = dz (fun w => moebiusMap R (h (moebiusMap R₀ w))) z := by
      unfold dz
      rw [hfd]
    have hdzbE : dzbar C z = dzbar (fun w => moebiusMap R (h (moebiusMap R₀ w))) z := by
      unfold dzbar
      rw [hfd]
    -- chain rule for the inner holomorphic precomposition
    have hudz : dz (fun w => h (moebiusMap R₀ w)) z
        = dz h (moebiusMap R₀ z) * ((moebiusDenom R₀ z) ^ 2)⁻¹ := by
      have hcr := dz_comp_of_holomorphicAt hγd.differentiableAt hDp
      rw [hγd.deriv] at hcr
      simp only [Function.comp_def] at hcr
      exact hcr
    have hudzb : dzbar (fun w => h (moebiusMap R₀ w)) z
        = dzbar h (moebiusMap R₀ z) * starRingEnd ℂ (((moebiusDenom R₀ z) ^ 2)⁻¹) := by
      have hcr := dzbar_comp_of_holomorphicAt hγd.differentiableAt hDp
      rw [hγd.deriv] at hcr
      simp only [Function.comp_def] at hcr
      exact hcr
    -- chain rule for the outer holomorphic postcomposition
    have hMreal : DifferentiableAt ℝ (moebiusMap R₀) z :=
      (differentiableAt_complex_iff_differentiableAt_real.mp hγd.differentiableAt).1
    have hu : DifferentiableAt ℝ (fun w => h (moebiusMap R₀ w)) z := by
      have hcomp := hDp.comp z hMreal
      simp only [Function.comp_def] at hcomp
      exact hcomp
    have hWreal : DifferentiableAt ℝ (moebiusMap R) (h (moebiusMap R₀ z)) :=
      (differentiableAt_complex_iff_differentiableAt_real.mp hRd.differentiableAt).1
    have hdzW : dz (moebiusMap R) (h (moebiusMap R₀ z))
        = ((moebiusDenom R (h (moebiusMap R₀ z))) ^ 2)⁻¹ := by
      rw [dz_eq_deriv_of_differentiableAt hRd.differentiableAt, hRd.deriv]
    have hdzbW : dzbar (moebiusMap R) (h (moebiusMap R₀ z)) = 0 :=
      dzbar_eq_zero_of_differentiableAt hRd.differentiableAt
    have hCdz : dz (fun w => moebiusMap R (h (moebiusMap R₀ w))) z
        = ((moebiusDenom R (h (moebiusMap R₀ z))) ^ 2)⁻¹
          * (dz h (moebiusMap R₀ z) * ((moebiusDenom R₀ z) ^ 2)⁻¹) := by
      have hcr := dz_comp hu hWreal
      rw [hdzW, hdzbW, zero_mul, add_zero, hudz] at hcr
      exact hcr
    have hCdzb : dzbar (fun w => moebiusMap R (h (moebiusMap R₀ w))) z
        = ((moebiusDenom R (h (moebiusMap R₀ z))) ^ 2)⁻¹
          * (dzbar h (moebiusMap R₀ z) * starRingEnd ℂ (((moebiusDenom R₀ z) ^ 2)⁻¹)) := by
      have hcr := dzbar_comp hu hWreal
      rw [hdzW, hdzbW, zero_mul, add_zero, hudzb] at hcr
      exact hcr
    rw [hdzbE, hCdzb, hdzE, hCdz]
    exact norm_dilat _ _ _ _ hbel_p
  -- conjugation symmetry rewrites the Wirtinger derivatives across the real axis
  have hCfix : (fun w => starRingEnd ℂ (C (starRingEnd ℂ w))) = C := by
    funext w
    rw [hsym w, Complex.conj_conj]
  have hdzconj : ∀ z : ℂ, dz C z = starRingEnd ℂ (dz C (starRingEnd ℂ z)) := by
    intro z
    conv_lhs => rw [← hCfix]
    exact dz_conj_conj C z
  have hdzbconj : ∀ z : ℂ, dzbar C z = starRingEnd ℂ (dzbar C (starRingEnd ℂ z)) := by
    intro z
    conv_lhs => rw [← hCfix]
    exact dzbar_conj_conj C z
  -- conjugation preserves null sets
  have hconjae : ∀ Q : ℂ → Prop, (∀ᵐ w : ℂ, Q w) → ∀ᵐ z : ℂ, Q (starRingEnd ℂ z) := by
    intro Q hQ
    have hmp : MeasurePreserving (fun z : ℂ => starRingEnd ℂ z) volume volume := by
      have hmp0 := Complex.conjLIE.measurePreserving
      have heq : (fun z : ℂ => starRingEnd ℂ z) = ⇑Complex.conjLIE := by
        funext z
        rw [Complex.conjLIE_apply]
      rw [heq]
      exact hmp0
    rw [ae_iff] at hQ ⊢
    exact hmp.preimage_null hQ
  -- the dilatation bound on the lower half plane, by symmetry transport
  have hLow : ∀ᵐ z : ℂ, z.im < 0 → ‖dzbar C z‖ ≤ κ * ‖dz C z‖ := by
    have htrans := hconjae (fun w => 0 < w.im → ‖dzbar C w‖ ≤ κ * ‖dz C w‖) hUp
    filter_upwards [htrans] with z hz1
    intro hz
    have him : 0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im]
      linarith
    have hb := hz1 him
    rw [hdzbconj z, hdzconj z, RCLike.norm_conj, RCLike.norm_conj]
    exact hb
  -- the real axis is null
  have hax : ∀ᵐ z : ℂ, z.im ≠ 0 := by
    rw [ae_iff]
    have hset : {a : ℂ | ¬ a.im ≠ 0} = {z : ℂ | z.im = 0} := by
      ext a
      simp
    rw [hset]
    exact volume_imZero
  -- the pointwise coefficient bound
  have hmu : ∀ᵐ z : ℂ, ‖bC.μ z‖ ≤ κ := by
    filter_upwards [hUp, hLow, hax, hC.1.2, hC.2.2] with z hup hlow hzim hdet hbel
    have hdil : ‖dzbar C z‖ ≤ κ * ‖dz C z‖ := by
      rcases lt_or_gt_of_ne hzim with hneg | hpos
      · exact hlow hneg
      · exact hup hpos
    rw [det_fderiv_eq_wirtinger] at hdet
    have hX0 : 0 ≤ ‖dz C z‖ := norm_nonneg _
    have hY0 : 0 ≤ ‖dzbar C z‖ := norm_nonneg _
    have hXpos : 0 < ‖dz C z‖ := by nlinarith
    have h1 : ‖bC.μ z‖ * ‖dz C z‖ ≤ κ * ‖dz C z‖ := by
      rw [← norm_mul, ← hbel]
      exact hdil
    exact le_of_mul_le_mul_right h1 hXpos
  -- essential supremum bound and the dilatation constant
  have hess : eLpNormEssSup bC.μ volume ≤ ENNReal.ofReal κ :=
    eLpNormEssSup_le_of_ae_bound hmu
  have hnorm : bC.normInf ≤ κ := by
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    rw [ENNReal.toReal_ofReal hκ0] at h2
    exact h2
  have hK1 : 1 ≤ (1 + κ) / (1 - κ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - κ)]
    linarith
  have hbnd : bC.normInf ≤ ((1 + κ) / (1 - κ) - 1) / ((1 + κ) / (1 - κ) + 1) := by
    have hd : (0 : ℝ) < (1 + κ) / (1 - κ) + 1 := by linarith
    have heq : ((1 + κ) / (1 - κ) - 1) / ((1 + κ) / (1 - κ) + 1) = κ := by
      rw [div_eq_iff (ne_of_gt hd)]
      have h1 : (1 : ℝ) - κ ≠ 0 := by linarith
      field_simp
      ring
    rw [heq]
    exact hnorm
  exact isQCGeometric_of_isQCAnalytic hK1 hbnd hC

/-! ## Arithmetic and choice-inverse helpers -/

/-- Composite coefficient bounds stay below `1`: for `0 ≤ a < 1` and `0 ≤ b < 1` the
composed bound `(a + b) / (1 + a b)` is below `1`. -/
theorem comb_lt_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (a + b) / (1 + a * b) < 1 := by
  have hden : 0 < 1 + a * b := by nlinarith
  rw [div_lt_one hden]
  nlinarith

/-- The choice inverse of a bijective conjugation-symmetric plane map is
conjugation-symmetric. -/
theorem invFun_conj {f : ℂ → ℂ} (hinj : Function.Injective f)
    (hsurj : Function.Surjective f)
    (hsym : ∀ z : ℂ, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) (z : ℂ) :
    Function.invFun f (starRingEnd ℂ z) = starRingEnd ℂ (Function.invFun f z) := by
  have h1 : f (Function.invFun f (starRingEnd ℂ z)) = starRingEnd ℂ z :=
    Function.rightInverse_invFun hsurj _
  have h2 : f (starRingEnd ℂ (Function.invFun f z)) = starRingEnd ℂ z := by
    rw [hsym, Function.rightInverse_invFun hsurj]
  exact hinj (h1.trans h2.symm)

/-- The choice inverse of the choice inverse of a bijection is the map itself. -/
theorem invFun_invFun {f : ℂ → ℂ} (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) :
    Function.invFun (Function.invFun f) = f := by
  funext z
  have hL : Function.LeftInverse (Function.invFun f) f := Function.leftInverse_invFun hinj
  have hR : Function.RightInverse (Function.invFun f) f := Function.rightInverse_invFun hsurj
  have hsurj' : Function.Surjective (Function.invFun f) := hL.surjective
  have hinj' : Function.Injective (Function.invFun f) := hR.injective
  have e1 : Function.invFun f (Function.invFun (Function.invFun f) z) = z :=
    Function.rightInverse_invFun hsurj' z
  have e2 : Function.invFun f (f z) = z := hL z
  exact hinj' (e1.trans e2.symm)

/-- The choice inverse of a plane homeomorphism agrees with the inverse homeomorphism. -/
theorem invFun_eq_homeoSymm {f : ℂ → ℂ} (hf : IsHomeomorph f) :
    Function.invFun f = ⇑(IsHomeomorph.homeomorph f hf).symm := by
  funext z
  apply hf.bijective.injective
  rw [Function.rightInverse_invFun hf.bijective.surjective]
  have h := (IsHomeomorph.homeomorph f hf).apply_symm_apply z
  rw [IsHomeomorph.homeomorph_apply] at h
  exact h.symm

/-- The choice inverse of a plane homeomorphism is continuous. -/
theorem continuous_invFun {f : ℂ → ℂ} (hf : IsHomeomorph f) :
    Continuous (Function.invFun f) := by
  rw [invFun_eq_homeoSymm hf]
  exact (IsHomeomorph.homeomorph f hf).symm.continuous

/-! ## Plane bricks: inverse analyticity, trivial-group representatives, images -/

/-- The choice inverse of an analytically quasiconformal plane map is analytically
quasiconformal with some coefficient. -/
theorem isQCAnalytic_invFun {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) :
    ∃ b' : BeltramiCoeff, IsQCAnalytic (Function.invFun f) b' := by
  have hg : IsQCGeometric f b.K := hf.isQCGeometric_K
  have hinvg := isQCGeometric_inv_of_isQCGeometric hg
  rw [← invFun_eq_homeoSymm hg.2.1.isHomeomorph] at hinvg
  obtain ⟨b', -, hb'⟩ := isQCAnalytic_of_isQCGeometric b.one_le_K hinvg
  exact ⟨b', hb'⟩

/-- Any conjugation-symmetric normalized analytically quasiconformal plane map is the
normalized solution of a Teichmüller representative over the trivial group. -/
theorem teichRepBot {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hsym : ∀ z : ℂ, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) :
    ∃ u : TeichRep (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)), u.w = f := by
  have hsymm : IsSymmetricBeltrami b := by
    have hcc := isQCAnalytic_conj_conj hf
    have hfeq : (fun z => starRingEnd ℂ (f (starRingEnd ℂ z))) = f := by
      funext z
      rw [hsym z, Complex.conj_conj]
    rw [hfeq] at hcc
    exact (isSymmetricBeltrami_iff_reflect b).mpr (beltrami_coeff_unique_ae hcc hf)
  have hinv : IsInvariantBeltrami' (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) b := by
    intro γ hγ
    have hγ1 : γ = 1 := Subgroup.mem_bot.mp hγ
    subst hγ1
    filter_upwards with z
    rw [moebiusMap_one, moebiusDenom_one, map_one]
  exact ⟨⟨b, hsymm, hinv⟩, ((⟨b, hsymm, hinv⟩ :
    TeichRep (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))).w_unique hf h0 h1).symm⟩

/-- The normalized solution maps the open upper half plane onto itself. -/
theorem w_image_upper (x : TeichRep Γ₀) :
    x.w '' {z : ℂ | 0 < z.im} = {z : ℂ | 0 < z.im} := by
  rcases x.w_halfPlane_dichotomy with ⟨-, himg⟩ | ⟨hneg, -⟩
  · exact himg
  · exfalso
    have h1 : (0 : ℝ) < (Complex.I).im := by simp
    have h2 := x.w_mapsTo_upper Complex.I h1
    have h3 := hneg Complex.I h1
    linarith

/-- The choice inverse of the normalized solution preserves the open upper half plane. -/
theorem invFun_w_mapsTo (x : TeichRep Γ₀) {z : ℂ} (hz : 0 < z.im) :
    0 < (Function.invFun x.w z).im := by
  have hzimg : z ∈ x.w '' {z : ℂ | 0 < z.im} := by
    rw [w_image_upper]
    exact hz
  obtain ⟨u, hu, huz⟩ := hzimg
  have heq : Function.invFun x.w z = u := by
    apply x.w_injective
    rw [Function.rightInverse_invFun x.w_isQCAnalytic.1.1.bijective.surjective, huz]
  rw [heq]
  exact hu

/-! ## Upper-half-plane bricks -/

/-- First-order local Sobolev membership restricts to subsets. -/
theorem memWklocP_one_mono {f : ℂ → ℂ} {p : ℝ≥0∞} {Ω Ω' : Set ℂ}
    (h : MemWklocP f 1 p Ω) (hsub : Ω' ⊆ Ω) : MemWklocP f 1 p Ω' := by
  obtain ⟨hlp, gx, gy, ⟨hgx, hgy⟩, hgxl, hgyl⟩ := h
  exact ⟨hlp.mono hsub, gx, gy, ⟨hgx.mono hsub, hgy.mono hsub⟩,
    hgxl.mono hsub, hgyl.mono hsub⟩

/-- A function continuous on a set is locally `Lᵖ` there. -/
theorem memLpLocOn_of_continuousOn {f : ℂ → ℂ} {p : ℝ≥0∞} {Ω : Set ℂ}
    (hf : ContinuousOn f Ω) : MemLpLocOn f p Ω := by
  intro K hK hKc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hfK : ContinuousOn f K := hf.mono hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hfK
  haveI : IsFiniteMeasure (volume.restrict K) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact hKc.measure_lt_top
  refine MemLp.of_bound (hfK.aestronglyMeasurable hKm) C ?_
  filter_upwards [ae_restrict_mem hKm] with z hz
  exact hC z hz

/-- The Möbius map of a real special linear matrix is continuously differentiable on the
open upper half plane. -/
theorem contDiffOn_moebiusMap (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ContDiffOn ℝ 1 (moebiusMap M) {z : ℂ | 0 < z.im} := by
  have hden0 : ∀ z ∈ {z : ℂ | 0 < z.im},
      ((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ) ≠ 0 := fun z hz =>
    moebiusDenom_ne_zero_of_im_ne_zero M (ne_of_gt hz)
  have hnum : ContDiffOn ℝ 1 (fun z : ℂ => ((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ))
      {z : ℂ | 0 < z.im} := (contDiffOn_const.mul contDiffOn_id).add contDiffOn_const
  have hdenc : ContDiffOn ℝ 1 (fun z : ℂ => ((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))
      {z : ℂ | 0 < z.im} := (contDiffOn_const.mul contDiffOn_id).add contDiffOn_const
  have hq := hnum.mul (hdenc.inv hden0)
  refine hq.congr ?_
  intro z hz
  rw [moebiusMap, moebiusDenom, div_eq_mul_inv]

/-- The Möbius map of a real special linear matrix restricts to an upper-half-plane
quasiconformal map with vanishing coefficient bound; its two-sided inverse on the upper
half plane is the Möbius map of the inverse matrix. -/
theorem isQCUpper_moebiusMap (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsQCUpper (moebiusMap M) (moebiusMap M⁻¹) 0 := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hU : MeasurableSet {z : ℂ | 0 < z.im} := hUopen.measurableSet
  have hden : ∀ (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ), 0 < z.im →
      moebiusDenom V z ≠ 0 := fun V z hz =>
    moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt hz)
  have hcd := contDiffOn_moebiusMap M
  have hcd' := contDiffOn_moebiusMap M⁻¹
  have hpt : ∀ z : ℂ, 0 < z.im → dz (moebiusMap M) z = ((moebiusDenom M z) ^ 2)⁻¹
      ∧ dzbar (moebiusMap M) z = 0 := by
    intro z hz
    have hd := hasDerivAt_moebiusMap M (hden M z hz)
    exact ⟨by rw [dz_eq_deriv_of_differentiableAt hd.differentiableAt, hd.deriv],
      dzbar_eq_zero_of_differentiableAt hd.differentiableAt⟩
  refine ⟨fun z hz => moebiusMap_im_pos M hz, fun z hz => moebiusMap_im_pos M⁻¹ hz,
    ?_, ?_, hcd.continuousOn, hcd'.continuousOn, ?_, ?_, ?_⟩
  · intro z hz
    rw [moebiusMap_mul M⁻¹ M z (hden M z hz), inv_mul_cancel, moebiusMap_one]
  · intro z hz
    rw [moebiusMap_mul M M⁻¹ z (hden M⁻¹ z hz), mul_inv_cancel, moebiusMap_one]
  · -- Sobolev membership: the classical derivative of a `C¹` map is a weak derivative
    have hfd : ContinuousOn (fderiv ℝ (moebiusMap M)) {z : ℂ | 0 < z.im} :=
      hcd.continuousOn_fderiv_of_isOpen hUopen le_rfl
    refine ⟨memLpLocOn_of_continuousOn hcd.continuousOn,
      fun z => (fderiv ℝ (moebiusMap M) z) 1, fun z => (fderiv ℝ (moebiusMap M) z) Complex.I,
      ⟨HasWeakDirDeriv.of_contDiffOn hUopen hcd, HasWeakDirDeriv.of_contDiffOn hUopen hcd⟩,
      memLpLocOn_of_continuousOn (hfd.clm_apply continuousOn_const),
      memLpLocOn_of_continuousOn (hfd.clm_apply continuousOn_const)⟩
  · rw [ae_restrict_iff' hU]
    filter_upwards with z hz
    have h1 := (hpt z hz).1
    have h2 := (hpt z hz).2
    rw [det_fderiv_eq_wirtinger, h1, h2, norm_zero]
    have hne : ((moebiusDenom M z) ^ 2)⁻¹ ≠ 0 :=
      inv_ne_zero (pow_ne_zero 2 (hden M z hz))
    have hpos : 0 < ‖((moebiusDenom M z) ^ 2)⁻¹‖ := norm_pos_iff.mpr hne
    nlinarith
  · rw [ae_restrict_iff' hU]
    filter_upwards with z hz
    rw [(hpt z hz).2, norm_zero, zero_mul]

/-! ## Equivariance upgrades -/

/-- Almost-everywhere Möbius conjugation identities of a continuous plane map upgrade to
every point of the open upper half plane. -/
theorem equivariant_upper_of_ae {F : ℂ → ℂ} (hFc : Continuous F)
    (hFim : ∀ z : ℂ, 0 < z.im → (F z).im ≠ 0)
    {γ W : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hae : ∀ᵐ z : ℂ, F (moebiusMap γ z) = moebiusMap W (F z)) :
    ∀ z : ℂ, 0 < z.im → F (moebiusMap γ z) = moebiusMap W (F z) := by
  intro z hz
  have hUopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have h1 : ContinuousOn (fun w => F (moebiusMap γ w)) {w : ℂ | 0 < w.im} := by
    intro w hw
    have hd := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hw)
    exact (hFc.continuousAt.comp (hasDerivAt_moebiusMap γ hd).continuousAt).continuousWithinAt
  have h2 : ContinuousOn (fun w => moebiusMap W (F w)) {w : ℂ | 0 < w.im} := by
    intro w hw
    have hd := moebiusDenom_ne_zero_of_im_ne_zero W (hFim w hw)
    exact ((hasDerivAt_moebiusMap W hd).continuousAt.comp hFc.continuousAt).continuousWithinAt
  have heq : Set.EqOn (fun w => F (moebiusMap γ w)) (fun w => moebiusMap W (F w))
      {w : ℂ | 0 < w.im} := by
    refine Measure.eqOn_of_ae_eq (ae_restrict_of_ae hae) h1 h2 ?_
    rw [hUopen.interior_eq]
    exact subset_closure
  exact heq hz

/-- Base-group elements of a Teichmüller representative conjugate exactly on the upper
half plane into the image group. -/
theorem w_conj_of_mem_base (x : TeichRep Γ₀)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) :
    ∃ W ∈ x.group, ∀ z : ℂ, 0 < z.im → x.w (moebiusMap γ z) = moebiusMap W (x.w z) := by
  obtain ⟨W, hWmem, hae⟩ := x.mem_group_of hγ
  exact ⟨W, hWmem, equivariant_upper_of_ae x.w_isQCAnalytic.1.1.continuous
    (fun z hz => ne_of_gt (x.w_mapsTo_upper z hz)) hae⟩

/-- Image-group elements of a Teichmüller representative are exact conjugates on the upper
half plane of base-group elements. -/
theorem w_conj_of_mem_group (x : TeichRep Γ₀)
    {W : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hW : W ∈ x.group) :
    ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im → x.w (moebiusMap γ z) = moebiusMap W (x.w z) := by
  have hmem : W ∈ fuchsianImageCarrier Γ₀ x.w := hW
  obtain ⟨γ, hγ, hae⟩ := hmem
  exact ⟨γ, hγ, equivariant_upper_of_ae x.w_isQCAnalytic.1.1.continuous
    (fun z hz => ne_of_gt (x.w_mapsTo_upper z hz)) hae⟩

/-- The inverse identity is a formal consequence of the forward conjugation identity for a
two-sided pair of upper-half-plane self-maps. -/
theorem inv_conj_of_conj {h hinv : ℂ → ℂ}
    (hm' : ∀ z : ℂ, 0 < z.im → 0 < (hinv z).im)
    (hli : ∀ z : ℂ, 0 < z.im → hinv (h z) = z)
    (hri : ∀ z : ℂ, 0 < z.im → h (hinv z) = z)
    {U U' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hfwd : ∀ z : ℂ, 0 < z.im → h (moebiusMap U z) = moebiusMap U' (h z)) :
    ∀ z : ℂ, 0 < z.im → hinv (moebiusMap U' z) = moebiusMap U (hinv z) := by
  intro z hz
  have hzin : 0 < (hinv z).im := hm' z hz
  have hUin : 0 < (moebiusMap U (hinv z)).im := moebiusMap_im_pos U hzin
  calc hinv (moebiusMap U' z)
      = hinv (moebiusMap U' (h (hinv z))) := by rw [hri z hz]
    _ = hinv (h (moebiusMap U (hinv z))) := by rw [hfwd (hinv z) hzin]
    _ = moebiusMap U (hinv z) := hli _ hUin

/-- Generator-level exact equivariance on the upper half plane upgrades to the closure of
the generator tuple, with the inverse identities; only the two-sided pointwise inverse and
half-plane preservation of the conjugating pair are used. -/
theorem equivariant_on_closure {ι : Type}
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {gens : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hmem : ∀ i, gens i ∈ Γ)
    {ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {h hinv : ℂ → ℂ}
    (hm : ∀ z : ℂ, 0 < z.im → 0 < (h z).im)
    (hm' : ∀ z : ℂ, 0 < z.im → 0 < (hinv z).im)
    (hli : ∀ z : ℂ, 0 < z.im → hinv (h z) = z)
    (hri : ∀ z : ℂ, 0 < z.im → h (hinv z) = z)
    (hgen : ∀ i, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap (ρ i) z) = moebiusMap (gens i) (h z)) :
    ∀ W ∈ Subgroup.closure (Set.range ρ), ∃ W' ∈ Γ,
      (∀ z : ℂ, 0 < z.im → h (moebiusMap W z) = moebiusMap W' (h z)) ∧
      (∀ z : ℂ, 0 < z.im → hinv (moebiusMap W' z) = moebiusMap W (hinv z)) := by
  have hden : ∀ (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ), 0 < z.im →
      moebiusDenom V z ≠ 0 := fun V z hz =>
    moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt hz)
  intro W hW
  induction hW using Subgroup.closure_induction with
  | mem V hV =>
    obtain ⟨i, rfl⟩ := hV
    exact ⟨gens i, hmem i, hgen i, inv_conj_of_conj hm' hli hri (hgen i)⟩
  | one =>
    refine ⟨1, one_mem Γ, ?_⟩
    have hfwd : ∀ z : ℂ, 0 < z.im →
        h (moebiusMap (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) z) = moebiusMap 1 (h z) := by
      intro z _
      rw [moebiusMap_one, moebiusMap_one]
    exact ⟨hfwd, inv_conj_of_conj hm' hli hri hfwd⟩
  | mul u v _ _ ihu ihv =>
    obtain ⟨u', hu'm, hfU, -⟩ := ihu
    obtain ⟨v', hv'm, hfV, -⟩ := ihv
    have hfwd : ∀ z : ℂ, 0 < z.im →
        h (moebiusMap (u * v) z) = moebiusMap (u' * v') (h z) := by
      intro z hz
      have hvz : 0 < (moebiusMap v z).im := moebiusMap_im_pos v hz
      have hhz : 0 < (h z).im := hm z hz
      calc h (moebiusMap (u * v) z)
          = h (moebiusMap u (moebiusMap v z)) := by rw [moebiusMap_mul u v z (hden v z hz)]
        _ = moebiusMap u' (h (moebiusMap v z)) := hfU _ hvz
        _ = moebiusMap u' (moebiusMap v' (h z)) := by rw [hfV z hz]
        _ = moebiusMap (u' * v') (h z) := moebiusMap_mul u' v' (h z) (hden v' (h z) hhz)
    exact ⟨u' * v', mul_mem hu'm hv'm, hfwd, inv_conj_of_conj hm' hli hri hfwd⟩
  | inv u _ ihu =>
    obtain ⟨u', hu'm, hfU, -⟩ := ihu
    have hfwd : ∀ z : ℂ, 0 < z.im →
        h (moebiusMap u⁻¹ z) = moebiusMap u'⁻¹ (h z) := by
      intro w hw
      have hzin : 0 < (moebiusMap u⁻¹ w).im := moebiusMap_im_pos u⁻¹ hw
      have hhin : 0 < (h (moebiusMap u⁻¹ w)).im := hm _ hzin
      have hback : moebiusMap u (moebiusMap u⁻¹ w) = w := by
        rw [moebiusMap_mul u u⁻¹ w (hden u⁻¹ w hw), mul_inv_cancel, moebiusMap_one]
      have hfz := hfU (moebiusMap u⁻¹ w) hzin
      rw [hback] at hfz
      rw [hfz, moebiusMap_mul u'⁻¹ u' (h (moebiusMap u⁻¹ w)) (hden u' _ hhin),
        inv_mul_cancel, moebiusMap_one]
    exact ⟨u'⁻¹, inv_mem hu'm, hfwd, inv_conj_of_conj hm' hli hri hfwd⟩

/-! ## The trivial-group re-marking and the inverse flip -/

/-- Any upper-half-plane quasiconformal pair with coefficient bound below `1` is an
upper-half-plane re-marking over the trivial group. -/
noncomputable def modGroupUpperBot {g ginv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper g ginv κ) :
    ModGroupUpper (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) where
  g := g
  ginv := ginv
  κ := κ
  hκ := hκ
  qc := hqc
  compat := by
    intro γ hγ
    have hγ1 : γ = 1 := Subgroup.mem_bot.mp hγ
    subst hγ1
    exact ⟨1, one_mem _, fun z _ => by rw [moebiusMap_one, moebiusMap_one]⟩
  compat' := by
    intro γ' hγ'
    have hγ1 : γ' = 1 := Subgroup.mem_bot.mp hγ'
    subst hγ1
    exact ⟨1, one_mem _, fun z _ => by rw [moebiusMap_one, moebiusMap_one]⟩

theorem modGroupUpperBot_g {g ginv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper g ginv κ) : (modGroupUpperBot hκ hqc).g = g := rfl

theorem modGroupUpperBot_ginv {g ginv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper g ginv κ) : (modGroupUpperBot hκ hqc).ginv = ginv := rfl

theorem modGroupUpperBot_κ {g ginv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper g ginv κ) : (modGroupUpperBot hκ hqc).κ = κ := rfl

/-- The normalized solution of a representative whose coefficient is essentially bounded
by `κ` on the upper half plane restricts to an upper-half-plane quasiconformal map with
coefficient bound `κ`, inverted by its choice inverse. -/
theorem isQCUpper_w_of_bound {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (u : TeichRep Γ) {κ : ℝ}
    (hbnd : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖u.b.μ z‖ ≤ κ) :
    IsQCUpper u.w (Function.invFun u.w) κ := by
  have hsurj : Function.Surjective u.w := u.w_isQCAnalytic.1.1.bijective.surjective
  refine ⟨u.w_mapsTo_upper, fun z hz => invFun_w_mapsTo u hz,
    fun z _ => Function.leftInverse_invFun u.w_injective z,
    fun z _ => Function.rightInverse_invFun hsurj z,
    u.w_isQCAnalytic.1.1.continuous.continuousOn,
    (continuous_invFun u.w_isQCAnalytic.1.1).continuousOn,
    memWklocP_one_mono u.w_isQCAnalytic.2.1 (Set.subset_univ _),
    ae_restrict_of_ae u.w_isQCAnalytic.1.2, ?_⟩
  filter_upwards [ae_restrict_of_ae u.w_isQCAnalytic.2.2, hbnd] with z h1 h2
  rw [h1, norm_mul]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- The Beltrami datum of an upper-half-plane quasiconformal map is realized by a
Teichmüller representative over the trivial group. -/
theorem flip_rep {u uinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1) (hqc : IsQCUpper u uinv κ) :
    ∃ Y : TeichRep (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), dzbar u z = Y.b.μ z * dz u z := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hinvb : ∀ γ ∈ (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
      ∀ᵐ z : ℂ ∂(volume.restrict {z : ℂ | 0 < z.im}),
      wirtingerQuotient u (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
        = wirtingerQuotient u z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
    intro γ hγ
    have h1 : γ = 1 := Subgroup.mem_bot.mp hγ
    subst h1
    filter_upwards with z
    rw [moebiusMap_one, moebiusDenom_one, map_one]
  refine ⟨TeichRep.ofUpper _ (wirtingerQuotient u) (measurable_wirtingerQuotient u)
    (wirtingerQuotient_bound_upper hκ hqc) hinvb, ?_⟩
  filter_upwards [hqc.jac, ae_restrict_mem hU] with z hjac hzU
  have hdzne : dz u z ≠ 0 := by
    intro h0
    rw [det_fderiv_eq_wirtinger, h0] at hjac
    simp only [norm_zero] at hjac
    nlinarith [norm_nonneg (dzbar u z), sq_nonneg ‖dzbar u z‖]
  have hbμ : (TeichRep.ofUpper _ (wirtingerQuotient u) (measurable_wirtingerQuotient u)
      (wirtingerQuotient_bound_upper hκ hqc) hinvb).b.μ z = wirtingerQuotient u z := by
    change symmExtension (wirtingerQuotient u) z = wirtingerQuotient u z
    simp only [symmExtension]
    rw [if_pos hzU]
  rw [hbμ]
  change dzbar u z = dzbar u z / dz u z * dz u z
  rw [div_mul_cancel₀ _ hdzne]

/-- Composite of the choice inverse of a normalized solution with a Möbius map: an
upper-half-plane quasiconformal map, with the corresponding Möbius-conjugated inverse. -/
theorem isQCUpper_invW_moebius {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (u : TeichRep Γ) (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ κ : ℝ, κ < 1 ∧
      IsQCUpper (Function.invFun u.w ∘ moebiusMap M) (moebiusMap M⁻¹ ∘ u.w) κ := by
  obtain ⟨b', hb'⟩ := isQCAnalytic_invFun u.w_isQCAnalytic
  have hinj := u.w_injective
  have hsurj : Function.Surjective u.w := u.w_isQCAnalytic.1.1.bijective.surjective
  have h0 : Function.invFun u.w 0 = 0 := by
    apply hinj
    rw [Function.rightInverse_invFun hsurj, u.w_zero]
  have h1 : Function.invFun u.w 1 = 1 := by
    apply hinj
    rw [Function.rightInverse_invFun hsurj, u.w_one]
  have hsym := fun z => invFun_conj hinj hsurj u.w_conj z
  obtain ⟨uInv, huInv⟩ := teichRepBot hb' h0 h1 hsym
  have hqcM := isQCUpper_moebiusMap M
  have hcomp := uInv.isQCUpper_remark (modGroupUpperBot one_pos hqcM)
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ,
    huInv, invFun_invFun hinj hsurj] at hcomp
  refine ⟨(max 0 0 + uInv.b.normInf) / (1 + max 0 0 * uInv.b.normInf),
    comb_lt_one (le_max_right _ _) (max_lt one_pos one_pos)
      uInv.b.normInf_nonneg uInv.b.normInf_lt_one, hcomp⟩

/-- **Inverse flip.** The inverse of an upper-half-plane quasiconformal map agrees on the
upper half plane with an upper-half-plane quasiconformal map, obtained by factoring
through the plane realization of its Beltrami datum. -/
theorem isQCUpper_flip {u uinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper u uinv κ) :
    ∃ (g ginv : ℂ → ℂ) (κ' : ℝ), κ' < 1 ∧ IsQCUpper g ginv κ' ∧
      ∀ z : ℂ, 0 < z.im → g z = uinv z := by
  obtain ⟨Y, hcoeff⟩ := flip_rep hκ hqc
  obtain ⟨R, hR⟩ := exists_sl2_factorization_of_eq_coeff Y hκ hqc hcoeff
  obtain ⟨κ', hκ'1, hqc'⟩ := isQCUpper_invW_moebius Y R
  refine ⟨Function.invFun Y.w ∘ moebiusMap R, moebiusMap R⁻¹ ∘ Y.w, κ', hκ'1, hqc', ?_⟩
  intro z hz
  have hzin : 0 < (uinv z).im := hqc.mapsTo' z hz
  have hu : u (uinv z) = z := hqc.right_inv z hz
  have hYw : Y.w (uinv z) = moebiusMap R z := by rw [hR (uinv z) hzin, hu]
  change Function.invFun Y.w (moebiusMap R z) = uinv z
  rw [← hYw]
  exact Function.leftInverse_invFun Y.w_injective (uinv z)

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: one declaration chains two remark composites, two flip
-- representatives with their factorizations, and the pointwise Möbius identity chains.
/-- **Per-index candidate.** An upper-half-plane conjugacy `h` carrying the limit tuple `ρ`
to the marked generators of `X` at Beltrami bound `κ`, together with a base conjugacy `v₀`
carrying `Γ₀` to the limit group both ways and a realization `y` of `v₀`, produces a
moduli re-marking `F` of `X` and a `(1 + κ)/(1 − κ)`-quasiconformal plane candidate
matching the boundary transition from `y` to the re-marked representative. -/
theorem candidate_of_upper_conjugacy {ι : Type}
    {ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (X : TeichRep Γ₀)
    {gensX : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hmemX : ∀ i, gensX i ∈ X.group)
    (hclosX : Subgroup.closure (Set.range gensX) = X.group)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (hgen : ∀ i, ∀ z : ℂ, 0 < z.im → h (moebiusMap (ρ i) z) = moebiusMap (gensX i) (h z))
    {v₀ v₀inv : ℂ → ℂ} {κᵥ : ℝ} (hκᵥ1 : κᵥ < 1) (hv₀qc : IsQCUpper v₀ v₀inv κᵥ)
    (hv₀fwd : ∀ γ ∈ Γ₀, ∃ W ∈ Subgroup.closure (Set.range ρ),
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z))
    (hv₀rev : ∀ W ∈ Subgroup.closure (Set.range ρ), ∃ γ ∈ Γ₀,
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z))
    (y : TeichRep Γ₀) (R₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hyfac : ∀ z : ℂ, 0 < z.im → y.w z = moebiusMap R₀ (v₀ z)) :
    ∃ (F : ModGroupUpper Γ₀) (C : ℂ → ℂ),
      IsQCGeometric C ((1 + κ) / (1 - κ)) ∧
      ∀ t : ℝ, C (y.w t) = (X.smulUpper F).w t := by
  classical
  have hden : ∀ (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ), 0 < z.im →
      moebiusDenom V z ≠ 0 := fun V z hz =>
    moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt hz)
  -- group-level upgrade of the generator equivariance and its reverse
  have hC1 := equivariant_on_closure hmemX hqc.mapsTo hqc.mapsTo' hqc.left_inv
    hqc.right_inv hgen
  have hgenInv : ∀ i, ∀ z : ℂ, 0 < z.im →
      hinv (moebiusMap (gensX i) z) = moebiusMap (ρ i) (hinv z) := fun i =>
    inv_conj_of_conj hqc.mapsTo' hqc.left_inv hqc.right_inv (hgen i)
  have hC1rev := equivariant_on_closure
    (Γ := Subgroup.closure (Set.range ρ)) (gens := ρ)
    (fun i => Subgroup.subset_closure ⟨i, rfl⟩) (ρ := gensX)
    hqc.mapsTo' hqc.mapsTo hqc.right_inv hqc.left_inv hgenInv
  rw [hclosX] at hC1rev
  -- flip representative of `h` and its Möbius normalization
  obtain ⟨Y, hcoeffY⟩ := flip_rep hκ1 hqc
  obtain ⟨P, hP⟩ := exists_sl2_factorization_of_eq_coeff Y hκ1 hqc hcoeffY
  -- the coefficient bound of `Y` on the upper half plane
  have hbndY : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖Y.b.μ z‖ ≤ κ := by
    filter_upwards [hcoeffY, hqc.jac, hqc.belt] with z hco hj hb
    have hdzne : dz h z ≠ 0 := by
      intro h0
      rw [det_fderiv_eq_wirtinger, h0] at hj
      simp only [norm_zero] at hj
      nlinarith [norm_nonneg (dzbar h z), sq_nonneg ‖dzbar h z‖]
    have hpos : 0 < ‖dz h z‖ := norm_pos_iff.mpr hdzne
    have heq : ‖Y.b.μ z‖ * ‖dz h z‖ = ‖dzbar h z‖ := by rw [← norm_mul, ← hco]
    have hle : ‖Y.b.μ z‖ * ‖dz h z‖ ≤ κ * ‖dz h z‖ := by
      rw [heq]
      exact hb
    exact le_of_mul_le_mul_right hle hpos
  have hmid : IsQCUpper Y.w (Function.invFun Y.w) κ := isQCUpper_w_of_bound Y hbndY
  -- the inner composite `Y.w ∘ v₀` and its flip representative
  have hqcA := Y.isQCUpper_remark (modGroupUpperBot hκᵥ1 hv₀qc)
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ] at hqcA
  have hκA1 : (max κᵥ 0 + Y.b.normInf) / (1 + max κᵥ 0 * Y.b.normInf) < 1 :=
    comb_lt_one (le_max_right _ _) (max_lt hκᵥ1 one_pos) Y.b.normInf_nonneg
      Y.b.normInf_lt_one
  obtain ⟨YA, hcoeffA⟩ := flip_rep hκA1 hqcA
  obtain ⟨RA, hRA⟩ := exists_sl2_factorization_of_eq_coeff YA hκA1 hqcA hcoeffA
  -- the Möbius correction and the double flip
  obtain ⟨κ₂, hκ₂1, hqc₂⟩ := isQCUpper_invW_moebius YA (P⁻¹ * RA⁻¹)⁻¹
  rw [inv_inv] at hqc₂
  obtain ⟨g₂, g₂inv, κ₃, hκ₃1, hqc₃, hg₂eq⟩ := isQCUpper_flip hκ₂1 hqc₂
  -- the outer inverse of the normalized solution of `X`
  obtain ⟨bX', hbX'⟩ := isQCAnalytic_invFun X.w_isQCAnalytic
  have hinjX := X.w_injective
  have hsurjX : Function.Surjective X.w := X.w_isQCAnalytic.1.1.bijective.surjective
  have h0X : Function.invFun X.w 0 = 0 := by
    apply hinjX
    rw [Function.rightInverse_invFun hsurjX, X.w_zero]
  have h1X : Function.invFun X.w 1 = 1 := by
    apply hinjX
    rw [Function.rightInverse_invFun hsurjX, X.w_one]
  obtain ⟨XI, hXI⟩ := teichRepBot hbX' h0X h1X
    (fun z => invFun_conj hinjX hsurjX X.w_conj z)
  have hqcF := XI.isQCUpper_remark (modGroupUpperBot hκ₃1 hqc₃)
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ,
    hXI, invFun_invFun hinjX hsurjX] at hqcF
  have hκF1 : (max κ₃ 0 + XI.b.normInf) / (1 + max κ₃ 0 * XI.b.normInf) < 1 :=
    comb_lt_one (le_max_right _ _) (max_lt hκ₃1 one_pos) XI.b.normInf_nonneg
      XI.b.normInf_lt_one
  -- pointwise identification of the re-marking composite on the upper half plane
  have hXw_g : ∀ z : ℂ, 0 < z.im →
      X.w ((Function.invFun X.w ∘ g₂) z) = h (v₀ z) := by
    intro z hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hYv : 0 < (Y.w (v₀ z)).im := Y.w_mapsTo_upper _ hv₀z
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    have e1 : X.w ((Function.invFun X.w ∘ g₂) z) = g₂ z :=
      Function.rightInverse_invFun hsurjX (g₂ z)
    have e2 : g₂ z = moebiusMap (P⁻¹ * RA⁻¹) (YA.w z) := hg₂eq z hz
    have e3 : YA.w z = moebiusMap RA (Y.w (v₀ z)) := hRA z hz
    have e4 : moebiusMap (P⁻¹ * RA⁻¹) (moebiusMap RA (Y.w (v₀ z)))
        = moebiusMap P⁻¹ (Y.w (v₀ z)) := by
      rw [moebiusMap_mul (P⁻¹ * RA⁻¹) RA _ (hden RA _ hYv), mul_assoc, inv_mul_cancel,
        mul_one]
    have e5 : Y.w (v₀ z) = moebiusMap P (h (v₀ z)) := hP _ hv₀z
    have e6 : moebiusMap P⁻¹ (Y.w (v₀ z)) = h (v₀ z) := by
      rw [e5, moebiusMap_mul P⁻¹ P _ (hden P _ hh), inv_mul_cancel, moebiusMap_one]
    rw [e1, e2, e3, e4, e6]
  have hgid : ∀ z : ℂ, 0 < z.im →
      (Function.invFun X.w ∘ g₂) z = Function.invFun X.w (h (v₀ z)) := by
    intro z hz
    have e := hXw_g z hz
    have e' : Function.invFun X.w (X.w ((Function.invFun X.w ∘ g₂) z))
        = (Function.invFun X.w ∘ g₂) z :=
      Function.leftInverse_invFun hinjX _
    rw [e] at e'
    exact e'.symm
  -- inverse equivariance of the choice inverse of the normalized solution
  have hXinvconj : ∀ (γ' W' : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ z : ℂ, 0 < z.im → X.w (moebiusMap γ' z) = moebiusMap W' (X.w z)) →
      ∀ z : ℂ, 0 < z.im →
        Function.invFun X.w (moebiusMap W' z) = moebiusMap γ' (Function.invFun X.w z) :=
    fun γ' W' hXid => inv_conj_of_conj (fun z hz => invFun_w_mapsTo X hz)
      (fun z _ => Function.leftInverse_invFun hinjX z)
      (fun z _ => Function.rightInverse_invFun hsurjX z) hXid
  -- forward compatibility of the re-marking composite
  have hcompat : ∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      (Function.invFun X.w ∘ g₂) (moebiusMap γ z)
        = moebiusMap γ' ((Function.invFun X.w ∘ g₂) z) := by
    intro γ hγ
    obtain ⟨W, hWmem, hWid⟩ := hv₀fwd γ hγ
    obtain ⟨W', hW'mem, hfwd', -⟩ := hC1 W hWmem
    obtain ⟨γ', hγ', hXid⟩ := w_conj_of_mem_group X hW'mem
    refine ⟨γ', hγ', fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    rw [hgid _ hγz, hWid z hz, hfwd' _ hv₀z, hXinvconj γ' W' hXid _ hh, ← hgid z hz]
  -- backward compatibility of the re-marking composite
  have hcompat' : ∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      (Function.invFun X.w ∘ g₂) (moebiusMap γ z)
        = moebiusMap γ' ((Function.invFun X.w ∘ g₂) z) := by
    intro γ' hγ'
    obtain ⟨W', hW'mem, hXid⟩ := w_conj_of_mem_base X hγ'
    obtain ⟨W, hWmem, -, hhid⟩ := hC1rev W' hW'mem
    obtain ⟨γ, hγ, hγid⟩ := hv₀rev W hWmem
    refine ⟨γ, hγ, fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    rw [hgid _ hγz, hγid z hz, hhid _ hv₀z, hXinvconj γ' W' hXid _ hh, ← hgid z hz]
  -- the moduli re-marking
  obtain ⟨F, hFg⟩ : ∃ F : ModGroupUpper Γ₀, F.g = Function.invFun X.w ∘ g₂ :=
    ⟨⟨Function.invFun X.w ∘ g₂, g₂inv ∘ X.w,
      (max κ₃ 0 + XI.b.normInf) / (1 + max κ₃ 0 * XI.b.normInf), hκF1, hqcF,
      hcompat, hcompat'⟩, rfl⟩
  -- the re-marked representative and its Möbius factorization through `Y.w ∘ v₀`
  obtain ⟨R', hR'⟩ := X.smulUpper_w F
  have hZfac : ∀ z : ℂ, 0 < z.im →
      (X.smulUpper F).w z = moebiusMap (R' * P⁻¹) (Y.w (v₀ z)) := by
    intro z hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    have hYv : 0 < (Y.w (v₀ z)).im := Y.w_mapsTo_upper _ hv₀z
    have e0 : X.w (F.g z) = h (v₀ z) := by
      rw [hFg]
      exact hXw_g z hz
    have e5 : Y.w (v₀ z) = moebiusMap P (h (v₀ z)) := hP _ hv₀z
    have e6 : moebiusMap P⁻¹ (Y.w (v₀ z)) = h (v₀ z) := by
      rw [e5, moebiusMap_mul P⁻¹ P _ (hden P _ hh), inv_mul_cancel, moebiusMap_one]
    rw [hR' z hz, e0, ← e6, moebiusMap_mul R' P⁻¹ _ (hden P⁻¹ _ hYv)]
  -- the plane candidate
  have hyinj := y.w_injective
  have hysurj : Function.Surjective y.w := y.w_isQCAnalytic.1.1.bijective.surjective
  obtain ⟨by', hy'⟩ := isQCAnalytic_invFun y.w_isQCAnalytic
  obtain ⟨bC, -, hbC⟩ := exists_isQCAnalytic_comp (X.smulUpper F).w_isQCAnalytic hy'
  have hCsym : ∀ z : ℂ, ((X.smulUpper F).w ∘ Function.invFun y.w) (starRingEnd ℂ z)
      = starRingEnd ℂ (((X.smulUpper F).w ∘ Function.invFun y.w) z) := by
    intro z
    have e1 : Function.invFun y.w (starRingEnd ℂ z)
        = starRingEnd ℂ (Function.invFun y.w z) :=
      invFun_conj hyinj hysurj y.w_conj z
    change (X.smulUpper F).w (Function.invFun y.w (starRingEnd ℂ z))
        = starRingEnd ℂ ((X.smulUpper F).w (Function.invFun y.w z))
    rw [e1, (X.smulUpper F).w_conj]
  have hCfac : ∀ z : ℂ, 0 < z.im →
      ((X.smulUpper F).w ∘ Function.invFun y.w) z
        = moebiusMap (R' * P⁻¹) (Y.w (moebiusMap R₀⁻¹ z)) := by
    intro z hz
    have hζ : 0 < (Function.invFun y.w z).im := invFun_w_mapsTo y hz
    have hv₀ζ : 0 < (v₀ (Function.invFun y.w z)).im := hv₀qc.mapsTo _ hζ
    have hyz : y.w (Function.invFun y.w z) = z := Function.rightInverse_invFun hysurj z
    have e2 : moebiusMap R₀⁻¹ (y.w (Function.invFun y.w z))
        = v₀ (Function.invFun y.w z) := by
      rw [hyfac _ hζ, moebiusMap_mul R₀⁻¹ R₀ _ (hden R₀ _ hv₀ζ), inv_mul_cancel,
        moebiusMap_one]
    have hval : v₀ (Function.invFun y.w z) = moebiusMap R₀⁻¹ z := by
      rw [← e2, hyz]
    change (X.smulUpper F).w (Function.invFun y.w z) = _
    rw [hZfac _ hζ, hval]
  have hgeo : IsQCGeometric ((X.smulUpper F).w ∘ Function.invFun y.w)
      ((1 + κ) / (1 - κ)) :=
    isQCGeometric_K_of_upper_moebius_factor hbC hCsym hκ0 hκ1 hmid (R' * P⁻¹) R₀⁻¹ hCfac
  refine ⟨F, (X.smulUpper F).w ∘ Function.invFun y.w, hgeo, fun t => ?_⟩
  change (X.smulUpper F).w (Function.invFun y.w (y.w t)) = (X.smulUpper F).w t
  rw [Function.leftInverse_invFun hyinj]

/-- Diagonal extraction from a family of eventual properties. -/
theorem diag {P : ℕ → ℕ → Prop} (h : ∀ j, ∀ᶠ n in Filter.atTop, P j n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, P j (ψ j) := by
  have hN : ∀ j, ∃ N, ∀ n ≥ N, P j n := fun j => Filter.eventually_atTop.mp (h j)
  choose N hNs using hN
  refine ⟨fun j => Nat.rec (N 0) (fun j ih => max (N (j + 1)) (ih + 1)) j, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  · intro j
    cases j with
    | zero => exact hNs 0 _ le_rfl
    | succ j => exact hNs (j + 1) _ (le_max_left _ _)

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: one declaration assembles the Mumford extraction, the Marden
-- diagonalization, the base-conjugacy flip with its two group upgrades, the realization
-- of the limit representative, and the per-index candidate squeeze.
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
  classical
  -- Mumford extraction: subsequence, marked generators, and the limit tuple
  obtain ⟨φ₀, gens, ρ, hφ₀mono, hmem, hclos, hconv, hgapρ, -, -, hccρ, -⟩ :=
    mumford_subconvergence_thick hΓ₀ hfree hcc hε hA x hthick harea
  -- Marden stability along the extracted subsequence
  have hΓf : ∀ n, IsFuchsianGroup ((x (φ₀ n)).group) := fun n =>
    TeichRep.isFuchsian_group hΓ₀ hfree (x (φ₀ n))
  have hgapf : ∀ n, ∀ γ ∈ (x (φ₀ n)).group, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| :=
    fun n γ hγ hnt => (trace_gap_of_systole hε (hthick (φ₀ n)) hγ hnt).1
  have hRS1 := exists_equivariant_upper_conjugacy_K_to_one hε
    (fun n => (x (φ₀ n)).group) hΓf hgapf gens hmem ρ hconv hgapρ hccρ
  -- diagonalization at the coefficient scales `1/(j+2)`
  have hκpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 2) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    positivity
  have hκ1 : ∀ j : ℕ, 1 / ((j : ℝ) + 2) < 1 := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨ψ, hψmono, hψP⟩ := diag (fun j => hRS1 (1 / ((j : ℝ) + 2)) (hκpos j))
  choose h hinv hqc hgen using hψP
  -- the base conjugacy `v₀`: the flipped composite at index `0`
  obtain ⟨b₀', hb₀'⟩ := isQCAnalytic_invFun (x (φ₀ (ψ 0))).w_isQCAnalytic
  have hinj₀ := (x (φ₀ (ψ 0))).w_injective
  have hsurj₀ : Function.Surjective (x (φ₀ (ψ 0))).w :=
    (x (φ₀ (ψ 0))).w_isQCAnalytic.1.1.bijective.surjective
  have h0₀ : Function.invFun (x (φ₀ (ψ 0))).w 0 = 0 := by
    apply hinj₀
    rw [Function.rightInverse_invFun hsurj₀, (x (φ₀ (ψ 0))).w_zero]
  have h1₀ : Function.invFun (x (φ₀ (ψ 0))).w 1 = 1 := by
    apply hinj₀
    rw [Function.rightInverse_invFun hsurj₀, (x (φ₀ (ψ 0))).w_one]
  obtain ⟨W0I, hW0I⟩ := teichRepBot hb₀' h0₀ h1₀
    (fun z => invFun_conj hinj₀ hsurj₀ (x (φ₀ (ψ 0))).w_conj z)
  have hqcu₀ := W0I.isQCUpper_remark (modGroupUpperBot (hκ1 0) (hqc 0))
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ,
    hW0I, invFun_invFun hinj₀ hsurj₀] at hqcu₀
  obtain ⟨v₀, v₀i, κᵥ, hκᵥ1, hv₀qc, hv₀eq⟩ := isQCUpper_flip
    (comb_lt_one (le_max_right _ _) (max_lt (hκ1 0) one_pos)
      W0I.b.normInf_nonneg W0I.b.normInf_lt_one) hqcu₀
  -- forward and reverse group upgrades at index `0`
  have hgenInv₀ : ∀ i, ∀ z : ℂ, 0 < z.im →
      hinv 0 (moebiusMap (gens (ψ 0) i) z) = moebiusMap (ρ i) (hinv 0 z) := fun i =>
    inv_conj_of_conj (hqc 0).mapsTo' (hqc 0).left_inv (hqc 0).right_inv (hgen 0 i)
  have hC1fwd₀ := equivariant_on_closure (hmem (ψ 0)) (hqc 0).mapsTo (hqc 0).mapsTo'
    (hqc 0).left_inv (hqc 0).right_inv (hgen 0)
  have hC1rev₀ := equivariant_on_closure
    (Γ := Subgroup.closure (Set.range ρ)) (gens := ρ)
    (fun i => Subgroup.subset_closure ⟨i, rfl⟩) (ρ := gens (ψ 0))
    (hqc 0).mapsTo' (hqc 0).mapsTo (hqc 0).right_inv (hqc 0).left_inv hgenInv₀
  rw [hclos (ψ 0)] at hC1rev₀
  -- the two-sided `Γ₀`-to-limit conjugation of `v₀`
  have hv₀fwd : ∀ γ ∈ Γ₀, ∃ W ∈ Subgroup.closure (Set.range ρ),
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z) := by
    intro γ hγ
    obtain ⟨W', hW'mem, hW'id⟩ := w_conj_of_mem_base (x (φ₀ (ψ 0))) hγ
    obtain ⟨W, hWmem, hIid, -⟩ := hC1rev₀ W' hW'mem
    refine ⟨W, hWmem, fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hwz : 0 < ((x (φ₀ (ψ 0))).w z).im := (x (φ₀ (ψ 0))).w_mapsTo_upper z hz
    have e1 : v₀ (moebiusMap γ z) = hinv 0 ((x (φ₀ (ψ 0))).w (moebiusMap γ z)) :=
      hv₀eq _ hγz
    have e2 : v₀ z = hinv 0 ((x (φ₀ (ψ 0))).w z) := hv₀eq z hz
    rw [e1, hW'id z hz, hIid _ hwz, ← e2]
  have hv₀rev : ∀ W ∈ Subgroup.closure (Set.range ρ), ∃ γ ∈ Γ₀,
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z) := by
    intro W hWmem
    obtain ⟨W', hW'mem, -, hIid⟩ := hC1fwd₀ W hWmem
    obtain ⟨γ, hγ, hγid⟩ := w_conj_of_mem_group (x (φ₀ (ψ 0))) hW'mem
    refine ⟨γ, hγ, fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hwz : 0 < ((x (φ₀ (ψ 0))).w z).im := (x (φ₀ (ψ 0))).w_mapsTo_upper z hz
    have e1 : v₀ (moebiusMap γ z) = hinv 0 ((x (φ₀ (ψ 0))).w (moebiusMap γ z)) :=
      hv₀eq _ hγz
    have e2 : v₀ z = hinv 0 ((x (φ₀ (ψ 0))).w z) := hv₀eq z hz
    rw [e1, hγid z hz, hIid _ hwz, ← e2]
  -- realization of the limit representative
  have hv₀conj : ∀ γ ∈ Γ₀, ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z) := by
    intro γ hγ
    obtain ⟨W, -, hid⟩ := hv₀fwd γ hγ
    exact ⟨W, hid⟩
  obtain ⟨y, hycoeff⟩ := exists_teichRep_ofUpper_of_conjugating hκᵥ1 hv₀qc hv₀conj
  obtain ⟨R₀, hyfac⟩ := exists_sl2_factorization_of_eq_coeff y hκᵥ1 hv₀qc hycoeff
  -- the per-index candidates
  have hcand : ∀ j : ℕ, ∃ (F : ModGroupUpper Γ₀) (C : ℂ → ℂ),
      IsQCGeometric C ((1 + 1 / ((j : ℝ) + 2)) / (1 - 1 / ((j : ℝ) + 2))) ∧
      ∀ t : ℝ, C (y.w t) = ((x (φ₀ (ψ j))).smulUpper F).w t := fun j =>
    candidate_of_upper_conjugacy (x (φ₀ (ψ j))) (hmem (ψ j)) (hclos (ψ j))
      (le_of_lt (hκpos j)) (hκ1 j) (hqc j) (hgen j) hκᵥ1 hv₀qc hv₀fwd hv₀rev y R₀ hyfac
  choose F C hgeo hbnd using hcand
  -- the dilatation squeeze
  have hKlim : Filter.Tendsto
      (fun j : ℕ => (1 + 1 / ((j : ℝ) + 2)) / (1 - 1 / ((j : ℝ) + 2)))
      Filter.atTop (nhds 1) := by
    have h2 : Filter.Tendsto (fun j : ℕ => ((j : ℝ) + 2)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h3 : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact h2.inv_tendsto_atTop
    have h4 : Filter.Tendsto (fun j : ℕ => 1 + 1 / ((j : ℝ) + 2)) Filter.atTop
        (nhds (1 + 0)) := tendsto_const_nhds.add h3
    have h5 : Filter.Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 2)) Filter.atTop
        (nhds (1 - 0)) := tendsto_const_nhds.sub h3
    have h6 := h4.div h5 (by norm_num)
    have h7 : (1 + 0 : ℝ) / (1 - 0) = 1 := by norm_num
    rwa [h7] at h6
  have htend := tendsto_teichPseudoDist_zero_of_candidates
    (x := fun j => (x (φ₀ (ψ j))).smulUpper (F j)) (y := y) (F := C)
    (K := fun j => (1 + 1 / ((j : ℝ) + 2)) / (1 - 1 / ((j : ℝ) + 2))) hgeo hbnd hKlim
  -- packaging along the composed extraction
  refine ⟨φ₀ ∘ ψ, F, y, hφ₀mono.comp hψmono, ?_⟩
  have hpt : ∀ k : ℕ, teichPseudoDist ((x (φ₀ (ψ k))).smulUpper (F k)) y
      = dist (F k • Teich.mk (x ((φ₀ ∘ ψ) k))) (Teich.mk y) := by
    intro k
    have h1 : F k • Teich.mk (x ((φ₀ ∘ ψ) k))
        = Teich.mk ((x (φ₀ (ψ k))).smulUpper (F k)) :=
      Teich.smulUpper_mk (F k) (x (φ₀ (ψ k)))
    rw [h1]
    exact (Teich.dist_mk _ _).symm
  exact htend.congr hpt

end RiemannDynamics

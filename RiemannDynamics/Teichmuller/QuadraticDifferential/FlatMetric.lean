/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Foliations

/-!
# The flat metric of a quadratic differential and the length–area kernel

The flat length `|q|^{1/2} |dz|` of curves in the upper half plane induces a distance by
infimizing over absolutely continuous connecting paths. For an automorphic `q` the
distance is deck-invariant, and an equivariant self-map of the upper half plane commuting
with a cocompact group moves points by a uniformly bounded flat distance.

The second half is the length–area kernel: along horizontal unit-speed segments the
horizontal transverse density takes its branch-free pointwise form, the heights-integral
of horizontal variations over a rectangle is the area integral of the density by Fubini,
and a per-slice lower bound integrates by Cauchy–Schwarz to the length–area inequality.

* `IsFlatPath`, `qdDist` — connecting paths and the flat distance.
* `qdDist_moebiusMap` — deck invariance.
* `exists_qdDist_displacement_bound` — the uniform displacement bound.
* `lintegral_horizontalVariation_eq_rect`, `lengthArea_kernel` — the Fubini and
  Cauchy–Schwarz layer.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace RiemannDynamics

/-! ## Flat paths and the flat distance -/

/-- A **flat path** from `z` to `w`: a curve on `[0, 1]`, continuous and absolutely
continuous there, with track in the upper half plane. -/
structure IsFlatPath (γ : ℝ → ℂ) (z w : ℂ) : Prop where
  init : γ 0 = z
  final : γ 1 = w
  cont : ContinuousOn γ (Set.Icc 0 1)
  ac : AbsolutelyContinuousOnInterval γ 0 1
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (γ t).im

/-- The **flat distance** of `q`: the infimum of the flat lengths of flat paths between
two points of the upper half plane. -/
noncomputable def qdDist (q : ℂ → ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → ℂ) (_ : IsFlatPath γ z w), qdLength q γ

/-- The flat distance is bounded by the flat length of any flat path. -/
theorem qdDist_le_qdLength {q : ℂ → ℂ} {γ : ℝ → ℂ} {z w : ℂ} (hγ : IsFlatPath γ z w) :
    qdDist q z w ≤ qdLength q γ :=
  iInf₂_le γ hγ

/-- Postcomposition with a map Lipschitz on a set containing the track preserves absolute
continuity on `[0, 1]`. -/
theorem lipschitzOnWith_comp_ac {l : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hl : LipschitzOnWith K l S) {γ : ℝ → ℂ}
    (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (htr : ∀ t ∈ Set.uIcc (0 : ℝ) 1, γ t ∈ S) :
    AbsolutelyContinuousOnInterval (l ∘ γ) 0 1 := by
  rw [absolutelyContinuousOnInterval_iff] at hac ⊢
  intro ε hε
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := hac (ε / ((K : ℝ) + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hkey := hδ' E hE hlen
  have hmem : ∀ i ∈ Finset.range E.1, γ (E.2 i).1 ∈ S ∧ γ (E.2 i).2 ∈ S := fun i hi =>
    ⟨htr _ (hE.1 i hi).1, htr _ (hE.1 i hi).2⟩
  simp only [Function.comp_apply]
  calc ∑ i ∈ Finset.range E.1, dist (l (γ (E.2 i).1)) (l (γ (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) :=
        Finset.sum_le_sum fun i hi => hl.dist_le_mul _ (hmem i hi).1 _ (hmem i hi).2
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * (ε / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hkey.le K.coe_nonneg
    _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := by field_simp

/-- The straight segment between two upper-half-plane points stays in the upper half
plane. -/
theorem segPath_im_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (segPath z w t).im := by
  have him : (segPath z w t).im = z.im + t * (w.im - z.im) := by
    simp [segPath, Complex.add_im, Complex.sub_im]
  rw [him]
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]; simpa using hz
  · nlinarith [mul_pos h0 hw, mul_nonneg (sub_nonneg.mpr ht.2) hz.le]

/-- Flat paths conjugate under Möbius deck transformations: the composed curve connects
the image points, stays in the upper half plane, and remains absolutely continuous. -/
theorem isFlatPath_moebiusMap_comp {γ : ℝ → ℂ} {z w : ℂ}
    (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : IsFlatPath γ z w) :
    IsFlatPath (moebiusMap γd ∘ γ) (moebiusMap γd z) (moebiusMap γd w) := by
  have hKc : IsCompact (γ '' Set.Icc 0 1) := isCompact_Icc.image_of_continuousOn hγ.cont
  have hKne : (γ '' Set.Icc 0 1).Nonempty :=
    ⟨γ 0, Set.mem_image_of_mem γ (Set.left_mem_Icc.mpr zero_le_one)⟩
  have hKH : ∀ x ∈ γ '' Set.Icc 0 1, 0 < x.im := by
    rintro x ⟨t, ht, rfl⟩; exact hγ.upper t ht
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hKc.exists_isMinOn hKne (Complex.continuous_im.continuousOn)
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
  set S : Set ℂ := {u : ℂ | x₀.im ≤ u.im} ∩ Metric.closedBall 0 R with hSdef
  have hKS : γ '' Set.Icc 0 1 ⊆ S := fun x hx => ⟨hx₀min hx, hR hx⟩
  have hSH : ∀ u ∈ S, 0 < u.im := fun u hu => lt_of_lt_of_le (hKH x₀ hx₀K) hu.1
  have hconv : Convex ℝ S := (convex_halfSpace_im_ge x₀.im).inter (convex_closedBall 0 R)
  have hScomp : IsCompact S :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const Complex.continuous_im)
  have hf : ∀ u ∈ S, HasDerivWithinAt (moebiusMap γd) ((moebiusDenom γd u ^ 2)⁻¹) S u :=
    fun u hu => (hasDerivAt_moebiusMap_of_im_pos γd (hSH u hu)).hasDerivWithinAt
  have hdercont : ContinuousOn (fun u : ℂ => (moebiusDenom γd u ^ 2)⁻¹) S := by
    have hden : Continuous fun u : ℂ => moebiusDenom γd u ^ 2 := by
      unfold moebiusDenom; fun_prop
    exact hden.continuousOn.inv₀ fun u hu =>
      pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γd (hSH u hu).ne')
  obtain ⟨C, hC⟩ := hScomp.exists_bound_of_continuousOn hdercont
  have hlip : LipschitzOnWith C.toNNReal (moebiusMap γd) S :=
    hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le hf fun u hu => by
      rw [← norm_toNNReal]; exact Real.toNNReal_mono (hC u hu)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.comp_apply, hγ.init]
  · rw [Function.comp_apply, hγ.final]
  · have hmcont : ContinuousOn (moebiusMap γd) {u : ℂ | 0 < u.im} := fun u hu =>
      (hasDerivAt_moebiusMap_of_im_pos γd hu).continuousAt.continuousWithinAt
    exact hmcont.comp hγ.cont fun t ht => hγ.upper t ht
  · exact lipschitzOnWith_comp_ac hlip hγ.ac fun t ht =>
      hKS (Set.mem_image_of_mem γ (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ ht))
  · exact fun t ht => moebiusMap_im_pos γd (hγ.upper t ht)

/-- The clamp `t ↦ max 0 (min 1 t)` lands in `[0, 1]`. -/
theorem clamp_mem (t : ℝ) : max 0 (min 1 t) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left 0 _, max_le zero_le_one (min_le_left 1 t)⟩

/-- The clamp `t ↦ max 0 (min 1 t)` fixes `[0, 1]`. -/
theorem clamp_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : max 0 (min 1 t) = t := by
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- The clamped reparametrization of a flat path is globally continuous. -/
theorem continuous_clamp {γ : ℝ → ℂ} {z w : ℂ} (hγ : IsFlatPath γ z w) :
    Continuous fun t => γ (max 0 (min 1 t)) :=
  hγ.cont.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    clamp_mem

/-- The clamped reparametrization of a flat path is a flat path with the same endpoints. -/
theorem isFlatPath_clamp {γ : ℝ → ℂ} {z w : ℂ} (hγ : IsFlatPath γ z w) :
    IsFlatPath (fun t => γ (max 0 (min 1 t))) z w := by
  refine ⟨?_, ?_, (continuous_clamp hγ).continuousOn, ?_, ?_⟩
  · rw [clamp_eq (Set.left_mem_Icc.mpr zero_le_one), hγ.init]
  · rw [clamp_eq (Set.right_mem_Icc.mpr zero_le_one), hγ.final]
  · refine absolutelyContinuousOnInterval_congr (fun x hx => ?_) hγ.ac
    rw [clamp_eq (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hx)]
  · intro t ht
    rw [clamp_eq ht]
    exact hγ.upper t ht

/-- The clamped reparametrization of a curve has the same flat length. -/
theorem qdLength_clamp (q : ℂ → ℂ) (γ : ℝ → ℂ) :
    qdLength q (fun t => γ (max 0 (min 1 t))) = qdLength q γ := by
  simp only [qdLength, arcLengthLineIntegral]
  have hIoo : ∀ f : ℝ → ℝ≥0∞,
      ∫⁻ t in Set.Icc (0 : ℝ) 1, f t = ∫⁻ t in Set.Ioo (0 : ℝ) 1, f t := fun f =>
    (setLIntegral_congr Ioo_ae_eq_Icc).symm
  rw [hIoo, hIoo]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hev : (fun s => γ (max 0 (min 1 s))) =ᶠ[nhds t] γ := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    rw [clamp_eq hs]
  rw [hev.deriv_eq, clamp_eq (Set.mem_Icc_of_Ioo ht)]

/-- The flat distance between points of the upper half plane is finite: the straight
segment is a flat path of finite flat length by continuity of `q` on its compact track. -/
theorem qdDist_lt_top {q : ℂ → ℂ} (hq : ContinuousOn q {z : ℂ | 0 < z.im})
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : qdDist q z w < ⊤ := by
  have hL : IsCompact (segPath z w '' Set.Icc 0 1) :=
    isCompact_Icc.image (segPath_continuous z w)
  have hLH : segPath z w '' Set.Icc 0 1 ⊆ {u : ℂ | 0 < u.im} := by
    rintro x ⟨t, ht, rfl⟩; exact segPath_im_pos hz hw ht
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hq.mono hLH)
  have hflat : IsFlatPath (segPath z w) z w :=
    ⟨segPath_zero z w, segPath_one z w, (segPath_continuous z w).continuousOn,
      segPath_ac z w, fun t ht => segPath_im_pos hz hw ht⟩
  have hlen : qdLength q (segPath z w)
      ≤ ENNReal.ofReal (Real.sqrt M) * (‖w - z‖₊ : ℝ≥0∞) := by
    unfold qdLength
    rw [arcLengthLineIntegral_segPath]
    calc ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt ‖q (segPath z w t)‖) * (‖w - z‖₊ : ℝ≥0∞)
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt M) * (‖w - z‖₊ : ℝ≥0∞) := by
          refine setLIntegral_mono_ae' measurableSet_Icc ?_
          filter_upwards with t ht
          gcongr
          exact hM _ (Set.mem_image_of_mem _ ht)
      _ = ENNReal.ofReal (Real.sqrt M) * (‖w - z‖₊ : ℝ≥0∞)
            * volume (Set.Icc (0 : ℝ) 1) := setLIntegral_const _ _
      _ = ENNReal.ofReal (Real.sqrt M) * (‖w - z‖₊ : ℝ≥0∞) := by
          rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  exact lt_of_le_of_lt (le_trans (qdDist_le_qdLength hflat) hlen)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top)

/-- The weight-4 automorphy law transfers to the inverse deck transformation. -/
theorem weight4_inv {q : ℂ → ℂ} (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γd z) = moebiusDenom γd z ^ 4 * q z) :
    ∀ z : ℂ, 0 < z.im → q (moebiusMap γd⁻¹ z) = moebiusDenom γd⁻¹ z ^ 4 * q z := by
  intro z hz
  have hd : moebiusDenom γd⁻¹ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γd⁻¹ hz.ne'
  have him : 0 < (moebiusMap γd⁻¹ z).im := moebiusMap_im_pos γd⁻¹ hz
  have hfix : moebiusMap γd (moebiusMap γd⁻¹ z) = z := by
    rw [moebiusMap_mul γd γd⁻¹ z hd, mul_inv_cancel, moebiusMap_one]
  have hden : moebiusDenom γd (moebiusMap γd⁻¹ z) * moebiusDenom γd⁻¹ z = 1 := by
    rw [moebiusDenom_mul γd γd⁻¹ z hd, mul_inv_cancel, moebiusDenom_one]
  have hkey := hq (moebiusMap γd⁻¹ z) him
  rw [hfix, eq_inv_of_mul_eq_one_left hden, inv_pow] at hkey
  have h4 : (moebiusDenom γd⁻¹ z) ^ 4 ≠ 0 := pow_ne_zero 4 hd
  rw [hkey, mul_inv_cancel_left₀ h4]

/-- One-sided deck monotonicity of the flat distance: postcomposing flat paths with a
Möbius deck transformation preserving the weight-4 law does not increase the infimum. -/
theorem qdDist_moebiusMap_le {q : ℂ → ℂ} (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γd z) = moebiusDenom γd z ^ 4 * q z)
    (z w : ℂ) : qdDist q (moebiusMap γd z) (moebiusMap γd w) ≤ qdDist q z w := by
  have key : ∀ γ : ℝ → ℂ, IsFlatPath γ z w →
      qdDist q (moebiusMap γd z) (moebiusMap γd w) ≤ qdLength q γ := by
    intro γ hγ
    have hflatc : IsFlatPath (fun t => γ (max 0 (min 1 t))) z w := isFlatPath_clamp hγ
    have hflat' := isFlatPath_moebiusMap_comp γd hflatc
    calc qdDist q (moebiusMap γd z) (moebiusMap γd w)
        ≤ qdLength q (moebiusMap γd ∘ fun t => γ (max 0 (min 1 t))) :=
          qdDist_le_qdLength hflat'
      _ = qdLength q (fun t => γ (max 0 (min 1 t))) :=
          qdLength_moebiusMap_comp γd hq (continuous_clamp hγ) hflatc.ac hflatc.upper
      _ = qdLength q γ := qdLength_clamp q γ
  exact le_iInf₂ key

set_option maxHeartbeats 400000 in
-- Heartbeats: unifying the two flat-path infima across the Möbius transport is whnf-heavy.
/-- **Deck invariance of the flat distance** for an automorphic density: precomposition
with a Möbius deck transformation is a bijection of flat paths preserving flat length. -/
theorem qdDist_moebiusMap {q : ℂ → ℂ} (γd : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hq : ∀ z : ℂ, 0 < z.im → q (moebiusMap γd z) = moebiusDenom γd z ^ 4 * q z)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    qdDist q (moebiusMap γd z) (moebiusMap γd w) = qdDist q z w := by
  refine le_antisymm (qdDist_moebiusMap_le γd hq z w) ?_
  have h2 := qdDist_moebiusMap_le γd⁻¹ (weight4_inv γd hq)
    (moebiusMap γd z) (moebiusMap γd w)
  have hzfix : moebiusMap γd⁻¹ (moebiusMap γd z) = z := by
    rw [moebiusMap_mul γd⁻¹ γd z (moebiusDenom_ne_zero_of_im_ne_zero γd hz.ne'),
      inv_mul_cancel, moebiusMap_one]
  have hwfix : moebiusMap γd⁻¹ (moebiusMap γd w) = w := by
    rw [moebiusMap_mul γd⁻¹ γd w (moebiusDenom_ne_zero_of_im_ne_zero γd hw.ne'),
      inv_mul_cancel, moebiusMap_one]
  rwa [hzfix, hwfix] at h2

/-- **The uniform displacement bound**: an upper-half-plane quasiconformal map commuting
elementwise with a cocompact free Fuchsian group moves every point of the upper half plane
by a uniformly bounded flat distance of any automorphic quadratic differential — the
displacement descends to a function on a compact quotient. -/
theorem exists_qdDist_displacement_bound
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ}
    (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im → h (moebiusMap γ z) = moebiusMap γ (h z)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ z : ℂ, 0 < z.im → qdDist q z (h z) ≤ C := by
  have _ := hΓ
  have _ := hfree
  obtain ⟨K, hK, hcov⟩ := exists_compact_covering Γ hcc
  set K' : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' K with hK'def
  have hK'c : IsCompact K' := hK.image UpperHalfPlane.continuous_coe
  have hK'H : ∀ x ∈ K', 0 < x.im := by rintro x ⟨τ, hτ, rfl⟩; exact τ.2
  have hhK : ContinuousOn (fun p : ℂ × ℝ => h p.1) (K' ×ˢ Set.Icc 0 1) :=
    hqc.cont.comp continuousOn_fst fun p hp => hK'H p.1 hp.1
  have hφc : ContinuousOn (fun p : ℂ × ℝ => segPath p.1 (h p.1) p.2)
      (K' ×ˢ Set.Icc 0 1) := by
    simp only [segPath]
    exact continuousOn_fst.add
      ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul
        (hhK.sub continuousOn_fst))
  set T : Set ℂ := (fun p : ℂ × ℝ => segPath p.1 (h p.1) p.2) '' (K' ×ˢ Set.Icc 0 1)
    with hTdef
  have hTc : IsCompact T := (hK'c.prod isCompact_Icc).image_of_continuousOn hφc
  have hTH : T ⊆ {u : ℂ | 0 < u.im} := by
    rintro x ⟨⟨u, t⟩, hp, rfl⟩
    exact segPath_im_pos (hK'H u hp.1) (hqc.mapsTo u (hK'H u hp.1)) hp.2
  obtain ⟨M, hM⟩ := hTc.exists_bound_of_continuousOn (q.continuousOn_upper.mono hTH)
  obtain ⟨R, hR⟩ := hK'c.exists_bound_of_continuousOn
    ((hqc.cont.mono fun x hx => hK'H x hx).sub continuousOn_id)
  refine ⟨ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal R,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, fun z hz => ?_⟩
  obtain ⟨γ, hγK⟩ := hcov ⟨z, hz⟩
  have hcoe : ((γ • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
      = moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) z :=
    coe_smul_eq_moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ⟨z, hz⟩
  set w : ℂ := moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) z with hwdef
  have hwK' : w ∈ K' := ⟨γ • (⟨z, hz⟩ : UpperHalfPlane), hγK, hcoe⟩
  have hwim : 0 < w.im := moebiusMap_im_pos _ hz
  have hinvar : qdDist q z (h z) = qdDist q w (h w) := by
    have hstep := qdDist_moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (q.automorphy (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) γ.2) hz (hqc.mapsTo z hz)
    rw [← hcomm (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) γ.2 z hz] at hstep
    exact hstep.symm
  have hseg : IsFlatPath (segPath w (h w)) w (h w) :=
    ⟨segPath_zero _ _, segPath_one _ _, (segPath_continuous _ _).continuousOn,
      segPath_ac _ _, fun t ht => segPath_im_pos hwim (hqc.mapsTo w hwim) ht⟩
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt ‖q (segPath w (h w) t)‖) * (‖h w - w‖₊ : ℝ≥0∞)
        ≤ ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal R := by
    intro t ht
    have hmem : segPath w (h w) t ∈ T := ⟨(w, t), ⟨hwK', ht⟩, rfl⟩
    have h1 : ENNReal.ofReal (Real.sqrt ‖q (segPath w (h w) t)‖)
        ≤ ENNReal.ofReal (Real.sqrt M) :=
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hM _ hmem))
    have h2 : (‖h w - w‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal R := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hR w hwK')
    exact mul_le_mul' h1 h2
  have hlen : qdLength q (segPath w (h w))
      ≤ ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal R := by
    unfold qdLength
    rw [arcLengthLineIntegral_segPath]
    calc ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt ‖q (segPath w (h w) t)‖) * (‖h w - w‖₊ : ℝ≥0∞)
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal R := by
          refine setLIntegral_mono_ae' measurableSet_Icc ?_
          filter_upwards with t ht using hbound t ht
      _ = ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal R
            * volume (Set.Icc (0 : ℝ) 1) := setLIntegral_const _ _
      _ = ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal R := by
          rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  calc qdDist q z (h z) = qdDist q w (h w) := hinvar
    _ ≤ qdLength q (segPath w (h w)) := qdDist_le_qdLength hseg
    _ ≤ ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal R := hlen

/-! ## The length–area kernel -/

/-- The horizontal unit-speed segment `s ↦ s + iy` has derivative `1`. -/
theorem hasDerivAt_horizontalSegment (y t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.mk s y) 1 t := by
  have h : (fun s : ℝ => Complex.mk s y)
      = fun s : ℝ => ((s : ℂ) + (y : ℝ) * Complex.I) := by
    funext s
    apply Complex.ext <;> simp
  rw [h]
  simpa using ((hasDerivAt_id t).ofReal_comp).add_const ((y : ℝ) * Complex.I)

/-- Along a horizontal unit-speed segment the horizontal density is the branch-free
pointwise form `√((|q| − Re q)/2)`. -/
theorem horizontalDensity_horizontalSegment (q : ℂ → ℂ) (y t : ℝ) :
    horizontalDensity q (fun s : ℝ => Complex.mk s y) t
      = ENNReal.ofReal
          (Real.sqrt ((‖q (Complex.mk t y)‖ - (q (Complex.mk t y)).re) / 2)) := by
  unfold horizontalDensity
  rw [(hasDerivAt_horizontalSegment y t).deriv]
  norm_num

/-- **Fubini for the horizontal density over a rectangle**: the heights-integral of the
horizontal variations of the unit-speed horizontal slices of `[0, 1] × [c, d]` is the area
integral of the pointwise density over the complex rectangle. -/
theorem lintegral_horizontalVariation_eq_rect {q : ℂ → ℂ} (hq : Measurable q) (c d : ℝ) :
    ∫⁻ y in Set.Icc c d, horizontalVariation q (fun s : ℝ => Complex.mk s y)
      = ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc c d},
          ENNReal.ofReal (Real.sqrt ((‖q z‖ - (q z).re) / 2)) := by
  set D : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt ((‖q z‖ - (q z).re) / 2)) with hD
  have hDmeas : Measurable D :=
    (((hq.norm.sub (Complex.measurable_re.comp hq)).div_const 2).sqrt).ennreal_ofReal
  have hpre : {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc c d}
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod]
  have hstep : ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc c d}, D z
      = ∫⁻ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d,
          D (Complex.measurableEquivRealProd.symm p) := by
    have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p => D (Complex.measurableEquivRealProd.symm p))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d)
    simp only [MeasurableEquiv.symm_apply_apply] at h
    rw [hpre, ← h]
  have hprod : ∫⁻ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d,
      D (Complex.measurableEquivRealProd.symm p)
      = ∫⁻ y in Set.Icc c d, ∫⁻ s in Set.Icc (0 : ℝ) 1, D (Complex.mk s y) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
    · simp only [Complex.measurableEquivRealProd_symm_apply]
    · exact (hDmeas.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable
  have hslice : ∀ y : ℝ, ∫⁻ s in Set.Icc (0 : ℝ) 1, D (Complex.mk s y)
      = horizontalVariation q (fun s : ℝ => Complex.mk s y) := by
    intro y
    unfold horizontalVariation
    exact lintegral_congr fun t => (horizontalDensity_horizontalSegment q y t).symm
  calc ∫⁻ y in Set.Icc c d, horizontalVariation q (fun s : ℝ => Complex.mk s y)
      = ∫⁻ y in Set.Icc c d, ∫⁻ s in Set.Icc (0 : ℝ) 1, D (Complex.mk s y) :=
        lintegral_congr fun y => (hslice y).symm
    _ = ∫⁻ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d,
          D (Complex.measurableEquivRealProd.symm p) := hprod.symm
    _ = ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc c d}, D z := hstep.symm

/-- **Cauchy–Schwarz on an interval**: a lower bound `L` on `∫ f` forces
`L² ≤ (b − a) · ∫ f²`. -/
theorem sq_le_lintegral_sq_of_le_lintegral {f : ℝ → ℝ≥0∞} {a b : ℝ} (_hab : a < b)
    (hmeas : Measurable f) {L : ℝ≥0∞} (hL : L ≤ ∫⁻ u in Set.Icc a b, f u) :
    L ^ 2 ≤ ENNReal.ofReal (b - a) * ∫⁻ u in Set.Icc a b, (f u) ^ 2 := by
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc a b)) hconj
    (f := f) (g := fun _ => (1 : ℝ≥0∞)) hmeas.aemeasurable aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow] at hcs
  have hvol : ∫⁻ (_ : ℝ) in Set.Icc a b, (1 : ℝ≥0∞) = ENNReal.ofReal (b - a) := by
    rw [setLIntegral_one, Real.volume_Icc]
  rw [hvol] at hcs
  have hpow : (∫⁻ u in Set.Icc a b, f u ^ (2 : ℝ)) = ∫⁻ u in Set.Icc a b, f u ^ 2 :=
    lintegral_congr fun u => ENNReal.rpow_two _
  rw [hpow] at hcs
  have h2 : L ≤ (∫⁻ u in Set.Icc a b, f u ^ 2) ^ (1 / 2 : ℝ)
      * ENNReal.ofReal (b - a) ^ (1 / 2 : ℝ) := le_trans hL hcs
  have hh := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hh
  norm_num at hh
  rw [mul_comm] at hh
  exact hh

/-- **The length–area kernel**: a uniform per-slice lower bound `L ≤ ∫ₐᵇ F(t, y) dt` over
`y ∈ [c, d]` integrates by Cauchy–Schwarz and Tonelli to the length–area inequality
`(d − c) L² ≤ (b − a) ∬ F²`. -/
theorem lengthArea_kernel {F : ℝ → ℝ → ℝ≥0∞} {a b c d : ℝ} (hab : a < b) (_hcd : c < d)
    (hmeas : ∀ y, Measurable fun t => F t y) {L : ℝ≥0∞}
    (hL : ∀ y ∈ Set.Icc c d, L ≤ ∫⁻ t in Set.Icc a b, F t y) :
    ENNReal.ofReal (d - c) * L ^ 2
      ≤ ENNReal.ofReal (b - a)
        * ∫⁻ y in Set.Icc c d, ∫⁻ t in Set.Icc a b, (F t y) ^ 2 := by
  have hper : ∀ y ∈ Set.Icc c d,
      L ^ 2 ≤ ENNReal.ofReal (b - a) * ∫⁻ t in Set.Icc a b, (F t y) ^ 2 := fun y hy =>
    sq_le_lintegral_sq_of_le_lintegral hab (hmeas y) (hL y hy)
  have hconst : ∫⁻ (_ : ℝ) in Set.Icc c d, L ^ 2 = ENNReal.ofReal (d - c) * L ^ 2 := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, mul_comm]
  calc ENNReal.ofReal (d - c) * L ^ 2
      = ∫⁻ (_ : ℝ) in Set.Icc c d, L ^ 2 := hconst.symm
    _ ≤ ∫⁻ y in Set.Icc c d,
          ENNReal.ofReal (b - a) * ∫⁻ t in Set.Icc a b, (F t y) ^ 2 := by
        refine setLIntegral_mono_ae' measurableSet_Icc ?_
        filter_upwards with y hy using hper y hy
    _ = ENNReal.ofReal (b - a)
          * ∫⁻ y in Set.Icc c d, ∫⁻ t in Set.Icc a b, (F t y) ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end RiemannDynamics

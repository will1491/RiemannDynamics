/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.Coarea.Assembly

/-!
# The planar co-area equality for the gradient weight

The planar co-area inequality `eilenberg_coarea_grad_le` (`Coarea.Assembly`) is one-sided:
`∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[1]) ≤ ∫⁻ z, g z * ‖∇u‖₊ ∂volume`. This file upgrades it to an
**equality** for the specific weight `g = ‖∇u‖₊`, both sides being the Dirichlet energy
`∫⁻ ‖∇u‖²`:

`∫⁻ c, (∫⁻ z in u⁻¹{c}, ‖∇u‖₊ ∂μH[1]) = ∫⁻ z, ‖∇u‖₊ ^ 2 ∂volume`.

The `≤` direction is `eilenberg_coarea_grad_le` with `g = ‖∇u‖₊`. The `≥` direction comprises:

* `lintegral_nnnorm_deriv_le_hausdorffMeasure_one_image` — the arc-length **lower** bound
  `∫⁻ t in I, ‖γ' t‖₊ ≤ μH[1] (γ '' I)` for an `InjOn` a.e.-differentiable curve `γ : ℝ → ℂ`, the
  mirror of `hausdorffMeasure_one_image_le`: the injective curve does not compress length, obtained
  from `AntilipschitzWith.le_hausdorffMeasure_image` on approximately-linear Lusin pieces (using the
  per-piece antilipschitz constant `(‖A 1‖₊ - δ)⁻¹`) summed over the disjoint injective images with
  `δ → 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace RiemannDynamics.Coarea

/-- **A curve piece antilipschitz constant from an approximately-linear model.**

If `γ : ℝ → ℂ` is `ApproximatesLinearOn` the linear map `A : ℝ →L[ℝ] ℂ` on `s` with tolerance
`c < ‖A 1‖₊`, then `γ` restricted to `s` is antilipschitz with constant `(‖A 1‖₊ - c)⁻¹` (the
one-dimensional domain has `‖A t‖ = |t| ‖A 1‖`, so the reverse triangle inequality forces
`‖γ x - γ y‖ ≥ (‖A 1‖ - c) |x - y|`). -/
theorem curve_antilipschitz (γ : ℝ → ℂ) (A : ℝ →L[ℝ] ℂ) (s : Set ℝ) (c : ℝ≥0)
    (hALO : ApproximatesLinearOn γ A s c) (hc : c < ‖A 1‖₊) :
    AntilipschitzWith (‖A 1‖₊ - c)⁻¹ (s.restrict γ) := by
  have hnormAt : ∀ t : ℝ, ‖A t‖ = |t| * ‖A 1‖ := by
    intro t
    have : A t = (t : ℂ) * A 1 := by
      rw [show A t = t • A 1 by rw [← map_smul]; congr 1; simp, Complex.real_smul]
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcpos : (0 : ℝ) < ‖A 1‖ - c := by
    have : (c : ℝ) < ‖A 1‖ := by exact_mod_cast hc
    linarith
  apply AntilipschitzWith.of_le_mul_dist
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [Set.domRestrict, Set.domRestrict, Subtype.dist_eq, Real.dist_eq, Complex.dist_eq]
  have hApprox : ‖γ x - γ y - A (x - y)‖ ≤ (c : ℝ) * |x - y| := by
    have := hALO x hx y hy; rwa [Real.norm_eq_abs] at this
  have hAxy : ‖A (x - y)‖ = |x - y| * ‖A 1‖ := hnormAt (x - y)
  have htri : ‖A (x - y)‖ - ‖γ x - γ y - A (x - y)‖ ≤ ‖γ x - γ y‖ :=
    calc ‖A (x - y)‖ - ‖γ x - γ y - A (x - y)‖
        = ‖A (x - y)‖ - ‖A (x - y) - (γ x - γ y)‖ := by rw [norm_sub_rev (γ x - γ y)]
      _ ≤ ‖A (x - y) - (A (x - y) - (γ x - γ y))‖ := norm_sub_norm_le _ _
      _ = ‖γ x - γ y‖ := by rw [sub_sub_cancel]
  have hlb : (‖A 1‖ - c) * |x - y| ≤ ‖γ x - γ y‖ := by
    rw [hAxy] at htri; nlinarith [abs_nonneg (x - y), hApprox, htri]
  rw [NNReal.coe_inv]
  have hcoe : ((‖A 1‖₊ - c : ℝ≥0) : ℝ) = ‖A 1‖ - c := by
    rw [NNReal.coe_sub (le_of_lt hc), coe_nnnorm]
  rw [hcoe, ← div_eq_inv_mul, le_div_iff₀ hcpos]; nlinarith [hlb]

/-- **Antilipschitz maps do not compress the one-dimensional Hausdorff measure of an image.**

If `γ` restricted to `P` is antilipschitz with constant `K`, then `μH[1] P ≤ K · μH[1] (γ '' P)`.
This is `AntilipschitzWith.le_hausdorffMeasure_image` transported from the subtype `P` (where the
inclusion is an isometry) to the ambient image. -/
theorem hausdorffMeasure_one_le_of_restrict_antilipschitz (γ : ℝ → ℂ) (K : ℝ≥0) (P : Set ℝ)
    (hanti : AntilipschitzWith K (P.restrict γ)) :
    μH[(1 : ℝ)] P ≤ (K : ℝ≥0∞) * μH[(1 : ℝ)] (γ '' P) := by
  have h := hanti.le_hausdorffMeasure_image zero_le_one (univ : Set P)
  rw [ENNReal.rpow_one] at h
  have himg : (P.restrict γ) '' univ = γ '' P := by
    rw [image_univ]; exact Set.range_domRestrict γ P
  have huniv : μH[(1 : ℝ)] (univ : Set P) = μH[(1 : ℝ)] P := by
    have h2 := (isometry_subtype_coe (s := P)).hausdorffMeasure_image
      (Or.inl zero_le_one) (univ : Set P)
    rw [Subtype.coe_image_univ] at h2; exact h2.symm
  rw [himg, huniv] at h; exact h

/-- **Per-piece lower bound on the image measure of an approximately-linear curve piece.**

If `γ` is `ApproximatesLinearOn A` on the measurable `t` with tolerance `ε`, then
`(‖A 1‖₊ - ε) · μH[1] t ≤ μH[1] (γ '' t)`. When `ε < ‖A 1‖₊` this is `curve_antilipschitz` fed
into `hausdorffMeasure_one_le_of_restrict_antilipschitz`; when `ε ≥ ‖A 1‖₊` the left side is `0`. -/
theorem expand_lb (γ : ℝ → ℂ) (A : ℝ →L[ℝ] ℂ) (ε : ℝ≥0) (t : Set ℝ)
    (htg : ApproximatesLinearOn γ A t ε) :
    ((‖A 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) * μH[(1 : ℝ)] t ≤ μH[(1 : ℝ)] (γ '' t) := by
  by_cases hlt : ε < ‖A 1‖₊
  · have hanti := curve_antilipschitz γ A t ε htg hlt
    have himg := hausdorffMeasure_one_le_of_restrict_antilipschitz γ (‖A 1‖₊ - ε)⁻¹ t hanti
    have hKpos : (0 : ℝ≥0) < ‖A 1‖₊ - ε := tsub_pos_of_lt hlt
    have hKne : ((‖A 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
      rw [Ne, ENNReal.coe_eq_zero]; exact ne_of_gt hKpos
    have hKtop : ((‖A 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    rw [ENNReal.coe_inv (ne_of_gt hKpos)] at himg
    calc ((‖A 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) * μH[(1 : ℝ)] t
        ≤ ((‖A 1‖₊ - ε : ℝ≥0) : ℝ≥0∞)
            * (((‖A 1‖₊ - ε : ℝ≥0) : ℝ≥0∞)⁻¹ * μH[(1 : ℝ)] (γ '' t)) := by gcongr
      _ = μH[(1 : ℝ)] (γ '' t) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hKne hKtop, one_mul]
  · have h0 : (‖A 1‖₊ - ε : ℝ≥0) = 0 := tsub_eq_zero_of_le (not_lt.mp hlt)
    rw [h0]; simp

/-- **The non-square analogue of `ApproximatesLinearOn.norm_fderiv_sub_le` for `ℝ →L[ℝ] ℂ`.**

If `γ : ℝ → ℂ` is `ApproximatesLinearOn A` on the measurable `s` with tolerance `δ` and has the
within-`s` derivative `f' x`, then `‖f' x - A‖₊ ≤ δ` for almost every `x ∈ s`. Mathlib's lemma is
stated only for square maps `E →L[ℝ] E`; its Lebesgue-density / Besicovitch proof is
dimension-agnostic and is replayed here for the non-square domain. -/
theorem approximatesLinearOn_norm_fderiv_sub_le
    {γ : ℝ → ℂ} {f' : ℝ → (ℝ →L[ℝ] ℂ)} (A : ℝ →L[ℝ] ℂ) (δ : ℝ≥0) (s : Set ℝ)
    (hs : MeasurableSet s) (hf : ApproximatesLinearOn γ A s δ)
    (hfd_s : ∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) :
    ∀ᵐ x ∂(volume : Measure ℝ).restrict s, ‖f' x - A‖₊ ≤ δ := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) s,
    ae_restrict_mem hs]
  intro x hx xs
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
    have hT : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at hT
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hT
    filter_upwards [self_mem_nhdsWithin]
    exact H
  intro ε εpos
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty :=
    Measure.eventually_nonempty_inter_smul_of_density_one (volume : Measure ℝ) s x hx _
      measurableSet_closedBall (Metric.measure_closedBall_pos (volume : Measure ℝ) z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
      ∃ ρ > 0, Metric.ball x ρ ∩ s ⊆ {y : ℝ | ‖γ y - γ x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    Metric.mem_nhdsWithin_iff.1 (((hfd_s x xs).isLittleO).def εpos)
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset Metric.isBounded_closedBall
      (Metric.ball_mem_nhds x ρpos)
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
      ∃ r : ℝ, (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty ∧
        {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ Metric.closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  have Iineq : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
          rw [map_smul, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg rpos.le]
      _ = ‖γ y - γ x - A (y - x) - (γ y - γ x - (f' x) (y - x))‖ := by
          congr 1
          simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left,
            FunLike.coe_sub, Pi.sub_apply, map_smul]
          module
      _ ≤ ‖γ y - γ x - A (y - x)‖ + ‖γ y - γ x - (f' x) (y - x)‖ := norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
          simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
          ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
        congr 1
        simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
        abel
    _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
        apply add_le_add
        · rw [mul_assoc] at Iineq; exact (mul_le_mul_iff_right₀ rpos).1 Iineq
        · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
        rw [mem_closedBall_iff_norm'] at az
        gcongr

/-- **Arc-length lower bound for an injective curve (mirror of `hausdorffMeasure_one_image_le`).**

For an `InjOn` curve `γ : ℝ → ℂ` that has the within-`I` derivative `γ' t` at each point of the
measurable set `I`, the integral of the speed is dominated by the one-dimensional Hausdorff measure
of the image:

`∫⁻ t in I, ‖γ' t‖₊ ≤ μH[1] (γ '' I)`.

Together with `hausdorffMeasure_one_image_le` (the reverse inequality, valid without injectivity)
this is the arc-length equality for injective a.e.-differentiable curves. The proof mirrors the
upper bound: on the approximately-linear Lusin pieces `γ` is antilipschitz with constant
`(‖A 1‖₊ - δ)⁻¹` (`curve_antilipschitz`), so each injective image expands by at least
`‖A 1‖₊ - δ` (`expand_lb`); injectivity makes the piece images disjoint and measurable
(Lusin–Souslin), so their measures sum to `μH[1] (γ '' I)`; taking `δ → 0` replaces `‖A 1‖₊` by
`‖γ'‖` (`approximatesLinearOn_norm_fderiv_sub_le`). -/
theorem lintegral_nnnorm_deriv_le_hausdorffMeasure_one_image
    {γ γ' : ℝ → ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) (hinj : InjOn γ I)
    (hγ' : ∀ t ∈ I, HasDerivWithinAt γ (γ' t) I t) :
    ∫⁻ t in I, (‖γ' t‖₊ : ℝ≥0∞) ≤ μH[1] (γ '' I) := by
  classical
  set f' : ℝ → (ℝ →L[ℝ] ℂ) := fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (γ' x) with hf'def
  have hfd : ∀ x ∈ I, HasFDerivWithinAt γ (f' x) I x := fun x hx => hγ' x hx
  have hf'1 : ∀ x, f' x 1 = γ' x := by
    intro x
    simp only [hf'def, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  have hHvol : (μH[(1 : ℝ)] : Measure ℝ) = volume := hausdorffMeasure_real
  have hcontI : ContinuousOn γ I := fun x hx => (hfd x hx).continuousWithinAt
  -- AUX1: a finite-error lower estimate on a measurable subset `s ⊆ I` on which `γ` is injective.
  have aux1 : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ I →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) → ∀ {ε : ℝ≥0}, 0 < ε →
      (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) ≤ μH[1] (γ '' s) + 2 * ε * (volume s) := by
    intro s hs hsI hfds ε εpos
    have hsinj : InjOn γ s := hinj.mono hsI
    obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hAy⟩ :
        ∃ (t : ℕ → Set ℝ) (A : ℕ → (ℝ →L[ℝ] ℂ)),
          Pairwise (Function.onFun Disjoint t) ∧
            (∀ n : ℕ, MeasurableSet (t n)) ∧
              (s ⊆ ⋃ n : ℕ, t n) ∧
                (∀ n : ℕ, ApproximatesLinearOn γ (A n) (s ∩ t n) ε) ∧
                  (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt γ s f' hfds (fun _ => ε)
        (fun _ => εpos.ne')
    have himg_meas : ∀ n, MeasurableSet (γ '' (s ∩ t n)) := fun n =>
      MeasurableSet.image_of_continuousOn_injOn (hs.inter (t_meas n))
        (hcontI.mono (Set.Subset.trans inter_subset_left hsI)) (hsinj.mono inter_subset_left)
    have himg_disj : Pairwise (Function.onFun Disjoint (fun n => γ '' (s ∩ t n))) := by
      intro i j hij
      simp only [Function.onFun]; rw [Set.disjoint_left]
      rintro w ⟨a, ⟨haS, hati⟩, rfl⟩ ⟨b, ⟨hbS, hbtj⟩, hab⟩
      have : a = b := hsinj haS hbS hab.symm
      subst this; exact (Set.disjoint_left.1 (t_disj hij)) hati hbtj
    have s_eq : s = ⋃ n, s ∩ t n := by
      rw [← inter_iUnion]; exact (inter_eq_self_of_subset_left t_cover).symm
    have hgimg_eq : γ '' s = ⋃ n, γ '' (s ∩ t n) := by rw [← image_iUnion, ← s_eq]
    have hpiece_le : ∀ n, (∫⁻ x in s ∩ t n, (‖γ' x‖₊ : ℝ≥0∞))
        ≤ ∫⁻ _ in s ∩ t n, ((‖A n 1‖₊ + ε : ℝ≥0) : ℝ≥0∞) := by
      intro n
      apply lintegral_mono_ae
      filter_upwards [approximatesLinearOn_norm_fderiv_sub_le (A n) ε (s ∩ t n)
          (hs.inter (t_meas n)) (ht n) (fun x hx => (hfds x hx.1).mono inter_subset_left)]
      intro x hx
      have hstep : (‖γ' x‖₊ : ℝ≥0) ≤ ‖A n 1‖₊ + ε := by
        have h1 : γ' x = A n 1 + (f' x - A n) 1 := by
          rw [sub_apply, hf'1]; ring
        calc (‖γ' x‖₊ : ℝ≥0) = ‖A n 1 + (f' x - A n) 1‖₊ := by rw [h1]
          _ ≤ ‖A n 1‖₊ + ‖(f' x - A n) 1‖₊ := nnnorm_add_le _ _
          _ ≤ ‖A n 1‖₊ + ‖f' x - A n‖₊ * ‖(1 : ℝ)‖₊ := by
                gcongr; exact ContinuousLinearMap.le_opNNNorm _ _
          _ ≤ ‖A n 1‖₊ + ε := by rw [nnnorm_one, mul_one]; gcongr
      rw [ENNReal.coe_le_coe]; exact hstep
    have hpiece_lb : ∀ n, ((‖A n 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n)
        ≤ μH[1] (γ '' (s ∩ t n)) := by
      intro n; have := expand_lb γ (A n) ε (s ∩ t n) (ht n); rwa [hHvol] at this
    have hvol_tsum : (∑' n, 2 * (ε : ℝ≥0∞) * volume (s ∩ t n)) = 2 * ε * (volume s) := by
      have hvol : (∑' n, volume (s ∩ t n)) = volume s := by
        rw [← measure_iUnion (pairwise_disjoint_mono t_disj fun n => inter_subset_right)
          (fun n => hs.inter (t_meas n)), ← s_eq]
      calc (∑' n, 2 * (ε : ℝ≥0∞) * volume (s ∩ t n))
          = 2 * ε * ∑' n, volume (s ∩ t n) := by rw [← ENNReal.tsum_mul_left]
        _ = 2 * ε * volume s := by rw [hvol]
    calc (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞))
        = ∑' n, ∫⁻ x in s ∩ t n, (‖γ' x‖₊ : ℝ≥0∞) := by
          conv_lhs => rw [s_eq]
          rw [lintegral_iUnion (fun n => hs.inter (t_meas n))
            (pairwise_disjoint_mono t_disj fun n => inter_subset_right)]
      _ ≤ ∑' n, ∫⁻ _ in s ∩ t n, ((‖A n 1‖₊ + ε : ℝ≥0) : ℝ≥0∞) := ENNReal.tsum_le_tsum hpiece_le
      _ = ∑' n, ((‖A n 1‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) := by
          simp only [setLIntegral_const]
      _ ≤ ∑' n, (μH[1] (γ '' (s ∩ t n)) + 2 * ε * volume (s ∩ t n)) := by
          apply ENNReal.tsum_le_tsum fun n => ?_
          have harith : ((‖A n 1‖₊ + ε : ℝ≥0) : ℝ≥0∞)
              ≤ ((‖A n 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) + 2 * ε := by
            rw [show ((2 : ℝ≥0∞) * ε) = ((2 * ε : ℝ≥0) : ℝ≥0∞) by push_cast; ring,
              ← ENNReal.coe_add, ENNReal.coe_le_coe]
            have h1 : (‖A n 1‖₊ : ℝ≥0) ≤ (‖A n 1‖₊ - ε) + ε := le_tsub_add
            calc (‖A n 1‖₊ + ε : ℝ≥0) ≤ ((‖A n 1‖₊ - ε) + ε) + ε := by gcongr
              _ = (‖A n 1‖₊ - ε) + 2 * ε := by ring
          calc ((‖A n 1‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n)
              ≤ (((‖A n 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) + 2 * ε) * volume (s ∩ t n) := by gcongr
            _ = ((‖A n 1‖₊ - ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n)
                + 2 * ε * volume (s ∩ t n) := by rw [add_mul]
            _ ≤ μH[1] (γ '' (s ∩ t n)) + 2 * ε * volume (s ∩ t n) := by
                  gcongr; exact hpiece_lb n
      _ = (∑' n, μH[1] (γ '' (s ∩ t n))) + ∑' n, 2 * ε * volume (s ∩ t n) := by
          rw [ENNReal.tsum_add]
      _ = μH[1] (γ '' s) + 2 * ε * (volume s) := by
          rw [hvol_tsum, hgimg_eq, measure_iUnion himg_disj himg_meas]
  -- AUX2: let `ε → 0` on finite-measure subsets.
  have aux2 : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ I → volume s ≠ ∞ →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) →
      (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) ≤ μH[1] (γ '' s) := by
    intro s hs hsI hsfin hfds
    have hlim : Tendsto (fun ε : ℝ≥0 =>
        μH[1] (γ '' s) + 2 * (ε : ℝ≥0∞) * (volume s)) (𝓝[>] 0)
        (𝓝 (μH[1] (γ '' s) + 2 * (0 : ℝ≥0) * (volume s))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      refine tendsto_const_nhds.add ?_
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr hsfin)
      exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr ENNReal.coe_ne_top)
    simp only [ENNReal.coe_zero, mul_zero, zero_mul, add_zero] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin]
    intro ε εpos
    rw [mem_Ioi] at εpos
    exact aux1 hs hsI hfds εpos
  -- Reduce `I` to finite-measure disjoint pieces via the spanning sets of `volume`.
  set u : ℕ → Set ℝ := fun n => disjointed (spanningSets (volume : Measure ℝ)) n with hu_def
  have u_meas : ∀ n, MeasurableSet (u n) := fun n =>
    MeasurableSet.disjointed (fun i => measurableSet_spanningSets (volume : Measure ℝ) i) n
  have hIcover : I = ⋃ n, I ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  have hIu_fin : ∀ n, volume (I ∩ u n) ≠ ∞ := by
    intro n
    have : volume (u n) < ∞ :=
      lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
        (measure_spanningSets_lt_top (volume : Measure ℝ) n)
    exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
  have himgU_meas : ∀ n, MeasurableSet (γ '' (I ∩ u n)) := fun n =>
    MeasurableSet.image_of_continuousOn_injOn (hI.inter (u_meas n))
      (hcontI.mono inter_subset_left) (hinj.mono inter_subset_left)
  have himgU_disj : Pairwise (Function.onFun Disjoint (fun n => γ '' (I ∩ u n))) := by
    intro i j hij
    simp only [Function.onFun]; rw [Set.disjoint_left]
    rintro w ⟨a, ⟨haI, hau⟩, rfl⟩ ⟨b, ⟨hbI, hbu⟩, hab⟩
    have : a = b := hinj haI hbI hab.symm
    subst this
    exact (Set.disjoint_left.1
      (disjoint_disjointed (spanningSets (volume : Measure ℝ)) hij)) hau hbu
  have hgimgI_eq : γ '' I = ⋃ n, γ '' (I ∩ u n) := by rw [← image_iUnion, ← hIcover]
  calc (∫⁻ x in I, (‖γ' x‖₊ : ℝ≥0∞))
      = ∑' n, ∫⁻ x in I ∩ u n, (‖γ' x‖₊ : ℝ≥0∞) := by
        conv_lhs => rw [hIcover]
        rw [lintegral_iUnion (fun n => hI.inter (u_meas n))
          (pairwise_disjoint_mono
            (disjoint_disjointed (spanningSets (volume : Measure ℝ)))
            (fun n => inter_subset_right))]
    _ ≤ ∑' n, μH[1] (γ '' (I ∩ u n)) := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        exact aux2 (hI.inter (u_meas n)) inter_subset_left (hIu_fin n)
          (fun x hx => (hfd x hx.1).mono inter_subset_left)
    _ = μH[1] (γ '' I) := by rw [hgimgI_eq, measure_iUnion himgU_disj himgU_meas]

/-- Set-form co-area lower bound on an approximately-linear injective piece. -/
theorem coarea_piece_ge {u : ℂ → ℝ} {Ψ : ℂ → ℂ} {Ψ' : ℂ → (ℂ →L[ℝ] ℂ)}
    {A : ℂ ≃L[ℝ] ℂ} {S : Set ℂ} {δ : ℝ≥0}
    (hS : MeasurableSet S) (_hSb : Bornology.IsBounded S)
    (hδ : δ < ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹)
    (hALO : ApproximatesLinearOn Ψ (A : ℂ →L[ℝ] ℂ) S δ)
    (hΨ' : ∀ z ∈ S, HasFDerivWithinAt Ψ (Ψ' z) S z)
    (hre : ∀ z ∈ S, (Ψ z).re = u z)
    (hdiff : ∀ z ∈ S, DifferentiableAt ℝ u z) :
    ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S) := by
  classical
  -- =================================================================
  -- (1)  Basic structure of `Ψ` and its inverse `g` on `T = Ψ '' S`.
  -- =================================================================
  have hinj : InjOn Ψ S := hALO.injOn (Or.inr hδ)
  set g : ℂ → ℂ := Function.invFunOn Ψ S with hg
  set T : Set ℂ := Ψ '' S with hT
  have hleft : ∀ z ∈ S, g (Ψ z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hright : ∀ w ∈ T, Ψ (g w) = w := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hleft z hz]
  have hgmem : ∀ w ∈ T, g w ∈ S := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hleft z hz]; exact hz
  have hgLip : LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹) g T := by
    rw [lipschitzOnWith_iff_restrict]
    exact (hALO.antilipschitz (Or.inr hδ)).to_rightInvOn'
      (fun w hw => hgmem w hw) (fun w hw => hright w hw)
  have hgCont : ContinuousOn g T := hgLip.continuousOn
  have hTmeas : MeasurableSet T := measurable_image_of_fderivWithin hS hΨ' hinj
  -- =================================================================
  -- (2)  `det (Ψ' z) ≠ 0` a.e. on `S` (small perturbation of `A`).
  -- =================================================================
  have hAne : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊ ≠ 0 := by
    intro h0; rw [h0, inv_zero] at hδ; exact absurd hδ (not_lt.mpr (zero_le))
  have hApos : (0 : ℝ≥0) < ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊ := pos_of_ne_zero hAne
  -- the perturbation lemma: ‖T₀ - A‖ ≤ δ ⟹ T₀.det ≠ 0
  have hdet_of_close : ∀ T₀ : ℂ →L[ℝ] ℂ, ‖T₀ - (A : ℂ →L[ℝ] ℂ)‖₊ ≤ δ → T₀.det ≠ 0 := by
    intro T₀ hT₀
    have hinjT : Function.Injective (T₀ : ℂ →ₗ[ℝ] ℂ) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      by_contra hvne
      have hvpos : (0 : ℝ≥0) < ‖v‖₊ := by rwa [nnnorm_pos]
      have hAv : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ * ‖v‖₊ ≤ ‖(A : ℂ →L[ℝ] ℂ) v‖₊ := by
        have hb := (A : ℂ →L[ℝ] ℂ).bound_of_antilipschitz A.antilipschitz v
        rw [← NNReal.coe_le_coe]; push_cast
        rw [inv_mul_le_iff₀ (by exact_mod_cast hApos)]
        rw [coe_nnnorm] at hb; exact hb
      have hTAv : ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ ≤ δ * ‖v‖₊ := by
        calc ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ ≤ ‖T₀ - (A : ℂ →L[ℝ] ℂ)‖₊ * ‖v‖₊ :=
              (T₀ - (A : ℂ →L[ℝ] ℂ)).le_opNNNorm v
          _ ≤ δ * ‖v‖₊ := by gcongr
      have hTeq : T₀ v = (A : ℂ →L[ℝ] ℂ) v + (T₀ - (A : ℂ →L[ℝ] ℂ)) v := by
        rw [sub_apply]; ring
      have hTv0 : (A : ℂ →L[ℝ] ℂ) v + (T₀ - (A : ℂ →L[ℝ] ℂ)) v = 0 := by rw [← hTeq]; exact hv
      have hAvnorm : ‖(A : ℂ →L[ℝ] ℂ) v‖₊ = ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ := by
        rw [eq_neg_of_add_eq_zero_left hTv0, nnnorm_neg]
      have hchain : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ * ‖v‖₊ ≤ δ * ‖v‖₊ :=
        le_trans hAv (le_trans (le_of_eq hAvnorm) hTAv)
      exact absurd (lt_of_le_of_lt (le_of_mul_le_mul_right hchain hvpos) hδ) (lt_irrefl _)
    intro hdet0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet0) (LinearMap.ker_eq_bot.mpr hinjT)
  have hdet_ne : ∀ᵐ z ∂(volume.restrict S), (Ψ' z).det ≠ 0 := by
    filter_upwards [hALO.norm_fderiv_sub_le volume hS Ψ' hΨ'] with z hz
    exact hdet_of_close (Ψ' z) hz
  -- =================================================================
  -- (3)  The inverse derivative `Dg` and the weight `Φ`.
  -- =================================================================
  set Dg : ℂ → (ℂ →L[ℝ] ℂ) := fun w =>
    if h : (Ψ' (g w)).det ≠ 0 then
      (((Ψ' (g w)).toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) else 0 with hDg
  set Φ : ℂ → ℝ≥0∞ := fun w => (‖Dg w Complex.I‖₊ : ℝ≥0∞) with hΦ
  have hinvderiv : ∀ z ∈ S, (h : (Ψ' z).det ≠ 0) →
      HasFDerivWithinAt g
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) T (Ψ z) := by
    intro z hz h
    have hgΨz : g (Ψ z) = z := hleft z hz
    have hfd : HasFDerivWithinAt Ψ
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero h) : ℂ →L[ℝ] ℂ) S (g (Ψ z)) := by
      rw [hgΨz, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]; exact hΨ' z hz
    have htend : Filter.Tendsto g (𝓝[T] (Ψ z)) (𝓝[S] (g (Ψ z))) :=
      (hgCont _ ⟨z, hz, rfl⟩).tendsto_nhdsWithin (fun w hw => hgmem w hw)
    have hev : ∀ᶠ y in 𝓝[T] (Ψ z), Ψ (g y) = y := by
      filter_upwards [self_mem_nhdsWithin] with y hy using hright y hy
    exact HasFDerivWithinAt.of_local_left_inverse htend hfd ⟨z, hz, rfl⟩ hev
  -- =================================================================
  -- (4)  The pointwise linear-algebra identity (`LA identity`):
  --      `ofReal |T₀.det| * ‖(T₀)⁻¹ I‖ = ‖reCLM ∘ T₀‖`  for invertible `T₀`.
  -- =================================================================
  have hLA : ∀ (T₀ : ℂ →L[ℝ] ℂ) (h : T₀.det ≠ 0),
      ENNReal.ofReal |T₀.det| *
          (‖((T₀.toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞)
        = (‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞) := by
    intro T₀ h
    set Te := T₀.toContinuousLinearEquivOfDetNeZero h with hTe
    set w : ℂ := (Te.symm : ℂ →L[ℝ] ℂ) Complex.I with hw
    have hTw : T₀ w = Complex.I := by
      have : (Te : ℂ →L[ℝ] ℂ) w = Complex.I := by
        rw [hw]; exact Te.apply_symm_apply Complex.I
      rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] at this
    set a := (T₀ 1).re with ha
    set b := (T₀ 1).im with hb
    set cc := (T₀ Complex.I).re with hcc
    set d := (T₀ Complex.I).im with hd
    have hdet : T₀.det = a * d - cc * b := by
      rw [show T₀.det = LinearMap.det (T₀ : ℂ →ₗ[ℝ] ℂ) from rfl,
        show LinearMap.det (T₀ : ℂ →ₗ[ℝ] ℂ)
          = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
              (T₀ : ℂ →ₗ[ℝ] ℂ)) from (LinearMap.det_toMatrix Complex.basisOneI _).symm]
      rw [Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    have hdecomp : T₀ w = w.re • (T₀ 1) + w.im • (T₀ Complex.I) := by
      have hwd : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      conv_lhs => rw [hwd]
      rw [map_add, map_smul, map_smul]
    have hre_eq : a * w.re + cc * w.im = 0 := by
      have h1 := congrArg Complex.re hTw
      rw [hdecomp] at h1
      simp only [Complex.add_re, Complex.smul_re, Complex.I_re, smul_eq_mul] at h1
      simp only [ha, hcc]; nlinarith [h1]
    have him_eq : b * w.re + d * w.im = 1 := by
      have h1 := congrArg Complex.im hTw
      rw [hdecomp] at h1
      simp only [Complex.add_im, Complex.smul_im, Complex.I_im, smul_eq_mul] at h1
      simp only [hb, hd]; nlinarith [h1]
    have hdetre : T₀.det * w.re = -cc := by
      rw [hdet]; linear_combination d * hre_eq - cc * him_eq
    have hdetim : T₀.det * w.im = a := by
      rw [hdet]; linear_combination (-b) * hre_eq + a * him_eq
    have hLval : ‖Complex.reCLM.comp T₀‖ = Real.sqrt (a ^ 2 + cc ^ 2) := by
      set L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp T₀ with hL
      set v := (InnerProductSpace.toDual ℝ ℂ).symm L with hv
      have hLnorm : ‖v‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
      have hriesz : ∀ z : ℂ, L z = inner ℝ v z := fun z => by
        rw [hv]; exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
      have hL1 : L 1 = a := by simp [hL, Complex.reCLM_apply, ha]
      have hLI : L Complex.I = cc := by simp [hL, Complex.reCLM_apply, hcc]
      have hvre : v.re = a := by
        have hh := (hriesz 1).symm; rw [hL1, Complex.inner] at hh; simpa using hh
      have hvim : v.im = cc := by
        have hh := (hriesz Complex.I).symm; rw [hLI, Complex.inner] at hh
        rw [Complex.mul_re] at hh; simp [Complex.conj_re, Complex.conj_im] at hh; linarith [hh]
      rw [← hLnorm, Complex.norm_eq_sqrt_sq_add_sq, hvre, hvim]
    have hprod : |T₀.det| * ‖w‖ = Real.sqrt (a ^ 2 + cc ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq w, ← Real.sqrt_sq (abs_nonneg T₀.det),
        ← Real.sqrt_mul (by positivity)]
      congr 1
      rw [sq_abs]
      have e1 : (T₀.det * w.re) ^ 2 = cc ^ 2 := by rw [hdetre, neg_pow, neg_one_sq, one_mul]
      have e2 : (T₀.det * w.im) ^ 2 = a ^ 2 := by rw [hdetim]
      nlinarith [e1, e2]
    have hwnn : ((‖(Te.symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖w‖ := by
      rw [← hw, ← enorm_eq_nnnorm, ← ofReal_norm]
    have hLnn : ((‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖Complex.reCLM.comp T₀‖ := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm]
    change ENNReal.ofReal |T₀.det| * ((‖(Te.symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞))
        = ((‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞))
    rw [hwnn, hLnn, ← ENNReal.ofReal_mul (abs_nonneg _), hprod, hLval]
  -- =================================================================
  -- (5)  a.e. on `S`:  `fderiv ℝ u z = reCLM ∘ Ψ' z`  (unique-diff points).
  -- =================================================================
  have hfderiv_eq : ∀ᵐ z ∂(volume.restrict S), fderiv ℝ u z = Complex.reCLM.comp (Ψ' z) := by
    filter_upwards [ae_uniqueDiffWithinAt_of_measurableSet hS,
      (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (fun z hz => hz))]
      with z hud hz
    have h1 : HasFDerivWithinAt (fun w => (Ψ w).re) (Complex.reCLM.comp (Ψ' z)) S z :=
      Complex.reCLM.hasFDerivAt.comp_hasFDerivWithinAt z (hΨ' z hz)
    have h2 : HasFDerivWithinAt u (Complex.reCLM.comp (Ψ' z)) S z :=
      h1.congr (fun w hw => (hre w hw).symm) (hre z hz).symm
    rw [← (hdiff z hz).fderivWithin hud, h2.fderivWithin hud]
  -- =================================================================
  -- (6)  AE-measurability of `Φ` on `T` (via the measurable embedding `Ψ|S`).
  -- =================================================================
  -- `Ψ'` is a.e.-measurable on `S`.
  have hΨ'meas : AEMeasurable Ψ' (volume.restrict S) := aemeasurable_fderivWithin volume hS hΨ'
  -- on `S`, a.e., `Φ (Ψ z) = ‖reCLM ∘ Ψ' z‖₊ / ofReal |det (Ψ' z)|`.
  have hΦΨ : ∀ᵐ z ∂(volume.restrict S),
      Φ (Ψ z) = (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞) / ENNReal.ofReal |(Ψ' z).det| := by
    filter_upwards [hdet_ne, (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (fun z hz => hz))]
      with z hdetz hz
    have hgΨ : g (Ψ z) = z := hleft z hz
    have hDgΨ : Dg (Ψ z) =
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero hdetz).symm : ℂ →L[ℝ] ℂ) := by
      rw [hDg]
      simp only [hgΨ]
      exact dif_pos hdetz
    have hΦval : Φ (Ψ z) =
        (‖(((Ψ' z).toContinuousLinearEquivOfDetNeZero hdetz).symm : ℂ →L[ℝ] ℂ)
            Complex.I‖₊ : ℝ≥0∞) := by
      rw [hΦ]; simp only [hDgΨ]
    rw [hΦval]
    have hdtop : ENNReal.ofReal |(Ψ' z).det| ≠ ⊤ := ENNReal.ofReal_ne_top
    have hd0 : ENNReal.ofReal |(Ψ' z).det| ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]; exact hdetz
    rw [ENNReal.eq_div_iff hd0 hdtop]
    exact hLA (Ψ' z) hdetz
  -- `‖reCLM ∘ Ψ' ·‖₊ / ofReal |det Ψ' ·|` is a.e.-measurable on `S`.
  have hmeas_aux : AEMeasurable
      (fun z => (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞) / ENNReal.ofReal |(Ψ' z).det|)
      (volume.restrict S) := by
    have hcompcont : Continuous (fun M : ℂ →L[ℝ] ℂ => Complex.reCLM.comp M) := by
      have := (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).continuous
      simpa only [ContinuousLinearMap.compL_apply] using! this
    have hc1 : AEMeasurable (fun z => (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞))
        (volume.restrict S) := by
      apply measurable_coe_nnreal_ennreal.comp_aemeasurable
      exact (continuous_nnnorm.comp hcompcont).measurable.comp_aemeasurable hΨ'meas
    have hc2 : AEMeasurable (fun z => ENNReal.ofReal |(Ψ' z).det|) (volume.restrict S) :=
      aemeasurable_ofReal_abs_det_fderivWithin volume hS hΨ'
    exact hc1.div hc2
  have hΦΨ_meas : AEMeasurable (fun z => Φ (Ψ z)) (volume.restrict S) :=
    hmeas_aux.congr (hΦΨ.mono (fun z hz => hz.symm))
  -- `Ψ` differentiable on `S`, hence images of null subsets are null.
  have hΨdiffOn : DifferentiableOn ℝ Ψ S := fun z hz => (hΨ' z hz).differentiableWithinAt
  -- `g` pushes `volume.restrict T` absolutely continuously onto `volume.restrict S`.
  have hgAC : (Measure.map g (volume.restrict T)) ≪ (volume.restrict S) := by
    have hgaem : AEMeasurable g (volume.restrict T) := hgCont.aemeasurable hTmeas
    refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
    -- volume (N ∩ S) = 0 ⟹ map g (restrict T) N = 0
    rw [Measure.restrict_apply hN] at hN0
    rw [Measure.map_apply_of_aemeasurable hgaem hN]
    -- g ⁻¹' N ∩ T ⊆ Ψ '' (N ∩ S)
    have hsub : g ⁻¹' N ∩ T ⊆ Ψ '' (N ∩ S) := by
      rintro w ⟨hwN, hwT⟩
      exact ⟨g w, ⟨hwN, hgmem w hwT⟩, hright w hwT⟩
    have himg0 : volume (Ψ '' (N ∩ S)) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (hΨdiffOn.mono inter_subset_right) hN0
    rw [Measure.restrict_apply' hTmeas]
    exact measure_mono_null hsub himg0
  -- transfer:  `Φ = (Φ ∘ Ψ) ∘ g` on `T`,  AEMeasurable via the change-of-variables.
  have hΦ_meas : AEMeasurable Φ (volume.restrict T) := by
    have hgaem : AEMeasurable g (volume.restrict T) := hgCont.aemeasurable hTmeas
    have hcomp : AEMeasurable (fun w => Φ (Ψ (g w))) (volume.restrict T) :=
      (hΦΨ_meas.mono' hgAC).comp_aemeasurable hgaem
    refine hcomp.congr ?_
    filter_upwards [(ae_restrict_iff' hTmeas).2 (Filter.Eventually.of_forall (fun w hw => hw))]
      with w hw
    rw [hright w hw]
  -- =================================================================
  -- (7)  STEP A:  `∫⁻ c, μH[1] (u⁻¹{c} ∩ S) ≤ ∫⁻ w in T, Φ w`.
  -- =================================================================
  -- A measurable null superset (within `S`) of the degenerate set, and its null image.
  obtain ⟨Z, hZsub, hZmeas, hZ0⟩ :
      ∃ Z : Set ℂ, ({z | ¬ (Ψ' z).det ≠ 0} ∩ S) ⊆ Z ∧ MeasurableSet Z ∧ volume Z = 0 := by
    have hh : volume.restrict S {z | ¬ (Ψ' z).det ≠ 0} = 0 := hdet_ne
    rw [Measure.restrict_apply₀' hS.nullMeasurableSet] at hh
    exact exists_measurable_superset_of_null hh
  -- `Ψ '' (Z ∩ S)` is `volume`-null.
  have hΨZ0 : volume (Ψ '' (Z ∩ S)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hΨdiffOn.mono inter_subset_right)
      (measure_mono_null inter_subset_left hZ0)
  -- a.e. `c`, the slice `{s | mk c s ∈ Ψ '' (Z ∩ S)}` is `volume`-null.
  set W : Set ℂ := Ψ '' (Z ∩ S) with hW
  have hslicenull : ∀ᵐ c : ℝ, volume {s : ℝ | Complex.mk c s ∈ W} = 0 := by
    -- transport nullity to `ℝ × ℝ` via `measurableEquivRealProd.symm`.
    set P : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' W with hP
    have hpre : (volume : Measure (ℝ × ℝ)) P = 0 := by
      rw [hP, (Complex.volume_preserving_equiv_real_prod.symm _).measure_preimage
        (NullMeasurableSet.of_null hΨZ0)]
      exact hΨZ0
    have hprod0 : ((volume : Measure ℝ).prod (volume : Measure ℝ)) P = 0 := by
      rw [← Measure.volume_eq_prod]; exact hpre
    have hslice := MeasureTheory.Measure.measure_ae_null_of_prod_null hprod0
    filter_upwards [hslice] with c hc
    have hseteq : {s : ℝ | Complex.mk c s ∈ W} = Prod.mk c ⁻¹' P := by
      ext s
      simp only [hP, Set.mem_preimage, Complex.measurableEquivRealProd_symm_apply, mem_setOf_eq]
    rw [hseteq]; exact hc
  -- The line map `s ↦ mk c s` and its derivative `I`.
  have hline : ∀ (c s : ℝ), HasDerivWithinAt (fun t : ℝ => Complex.mk c t) Complex.I
      {t : ℝ | Complex.mk c t ∈ T} s := by
    intro c s
    have hHA : HasDerivAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (1 * Complex.I) s :=
        (Complex.ofRealCLM.hasDerivAt).mul_const Complex.I
      have h3 := (h2.const_add (c : ℂ)); rwa [one_mul] at h3
    have hEq : (fun t : ℝ => Complex.mk c t)
        = (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
      funext t; rw [Complex.mk_eq_add_mul_I]
    rw [hEq]; exact hHA.hasDerivWithinAt
  -- the fiber slice curve and its derivative at good points.
  have hslicederiv : ∀ (c s : ℝ), Complex.mk c s ∈ T →
      (Ψ' (g (Complex.mk c s))).det ≠ 0 →
      HasDerivWithinAt (fun t : ℝ => g (Complex.mk c t)) (Dg (Complex.mk c s) Complex.I)
        {t : ℝ | Complex.mk c t ∈ T} s := by
    intro c s hsT hdetne
    obtain ⟨z, hz, hzeq⟩ := hsT
    have hgw : g (Complex.mk c s) ∈ S := hgmem _ ⟨z, hz, hzeq⟩
    have hDgval : Dg (Complex.mk c s)
        = (((Ψ' (g (Complex.mk c s))).toContinuousLinearEquivOfDetNeZero hdetne).symm
            : ℂ →L[ℝ] ℂ) := by rw [hDg]; exact dif_pos hdetne
    have hgfd : HasFDerivWithinAt g (Dg (Complex.mk c s)) T (Complex.mk c s) := by
      rw [hDgval]
      have := hinvderiv (g (Complex.mk c s)) hgw hdetne
      rwa [hright _ ⟨z, hz, hzeq⟩] at this
    exact hgfd.comp_hasDerivWithinAt s (hline c s) (fun t ht => ht)
  -- the fiber slice curve is Lipschitz on `T_c`.
  have hlineLip : ∀ c : ℝ, LipschitzOnWith 1 (fun t : ℝ => Complex.mk c t)
      {t : ℝ | Complex.mk c t ∈ T} := by
    intro c
    apply LipschitzWith.lipschitzOnWith
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Complex.dist_eq, Complex.mk_eq_add_mul_I, NNReal.coe_one, one_mul]
    rw [show (c : ℂ) + (x : ℂ) * Complex.I - ((c : ℂ) + (y : ℂ) * Complex.I)
        = ((x : ℂ) - (y : ℂ)) * Complex.I by ring, norm_mul, Complex.norm_I, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
  have hsliceLip : ∀ c : ℝ, LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹)
      (fun t : ℝ => g (Complex.mk c t)) {t : ℝ | Complex.mk c t ∈ T} := by
    intro c
    have hcomp : LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹ * 1)
        (g ∘ (fun t : ℝ => Complex.mk c t)) {t : ℝ | Complex.mk c t ∈ T} :=
      hgLip.comp (hlineLip c) (fun t ht => ht)
    rw [mul_one] at hcomp
    exact hcomp
  -- reversed per-`c` slice bound (a.e. c):  ∫⁻ s in T_c, Φ(mk c s) ≤ μH[1](u⁻¹{c} ∩ S).
  have hslicebound : ∀ᵐ c : ℝ,
      ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s) ≤ μH[1] (u ⁻¹' {c} ∩ S) := by
    filter_upwards [hslicenull] with c hcnull
    set Tc : Set ℝ := {t : ℝ | Complex.mk c t ∈ T} with hTc
    have hmkcont : Continuous (fun t : ℝ => Complex.mk c t) := by
      have : (fun t : ℝ => Complex.mk c t)
          = (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
        funext t; rw [Complex.mk_eq_add_mul_I]
      rw [this]; fun_prop
    have hTcmeas : MeasurableSet Tc := by
      rw [hTc]; exact hTmeas.preimage hmkcont.measurable
    set B : Set ℝ := toMeasurable volume {s : ℝ | Complex.mk c s ∈ W} with hB
    have hBmeas : MeasurableSet B := measurableSet_toMeasurable _ _
    have hB0 : volume B = 0 := by rw [hB, measure_toMeasurable]; exact hcnull
    have hBsup : {s : ℝ | Complex.mk c s ∈ W} ⊆ B := subset_toMeasurable _ _
    set Tgood : Set ℝ := Tc \ B with hTgood
    have hTgood_meas : MeasurableSet Tgood := hTcmeas.diff hBmeas
    have hgood_det : ∀ t ∈ Tgood, (Ψ' (g (Complex.mk c t))).det ≠ 0 := by
      intro t ht
      obtain ⟨htT, htB⟩ := ht
      intro hdet0
      apply htB
      obtain ⟨z, hz, hzeq⟩ := htT
      have hgS : g (Complex.mk c t) ∈ S := hgmem _ ⟨z, hz, hzeq⟩
      have hgZ : g (Complex.mk c t) ∈ Z :=
        hZsub ⟨by simp only [mem_setOf_eq, not_not]; exact hdet0, hgS⟩
      apply hBsup
      change Complex.mk c t ∈ W
      rw [hW, ← hright _ ⟨z, hz, hzeq⟩]
      exact ⟨g (Complex.mk c t), ⟨hgZ, hgS⟩, rfl⟩
    -- fiber set equality
    have hfiber : u ⁻¹' {c} ∩ S
        = (fun s : ℝ => g (Complex.mk c s)) '' Tc := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_image, mem_setOf_eq, hTc]
      constructor
      · rintro ⟨huc, hzS⟩
        have hΨze : Complex.mk c (Ψ z).im = Ψ z := by
          apply Complex.ext
          · simp [hre z hzS, huc]
          · simp
        exact ⟨(Ψ z).im, by rw [hΨze]; exact ⟨z, hzS, rfl⟩, by rw [hΨze, hleft z hzS]⟩
      · rintro ⟨s, hsT, rfl⟩
        have hgS : g (Complex.mk c s) ∈ S := hgmem _ hsT
        refine ⟨?_, hgS⟩
        rw [← hre _ hgS, hright _ hsT]
    -- γ_c is injective on Tc (g InjOn T + mk injective)
    have hgInjT : InjOn g T := Function.invFunOn_injOn_image Ψ S
    have hγc_inj : InjOn (fun s : ℝ => g (Complex.mk c s)) Tc := by
      intro s1 hs1 s2 hs2 heq
      have hmk : Complex.mk c s1 = Complex.mk c s2 := hgInjT hs1 hs2 heq
      have := congrArg Complex.im hmk; simpa using this
    -- Φ (mk c ·) = 0 outside good parameters is not needed; instead Tbad is null.
    -- ∫_{Tc} Φ = ∫_{Tgood} Φ  since Tbad = Tc ∩ B is null.
    have hTc_split : ∫⁻ s in Tc, Φ (Complex.mk c s) = ∫⁻ s in Tgood, Φ (Complex.mk c s) := by
      rw [hTgood]
      apply setLIntegral_congr
      refine (diff_ae_eq_self.2 ?_).symm
      exact measure_mono_null inter_subset_right hB0
    -- on Tgood, Φ (mk c s) = ‖(fun s => g (mk c s))' s‖₊ (deriv is Dg (mk c s) I)
    have hgoodbound : ∫⁻ s in Tgood, Φ (Complex.mk c s)
        ≤ μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood) := by
      have hderiv : ∀ t ∈ Tgood, HasDerivWithinAt (fun s : ℝ => g (Complex.mk c s))
          (Dg (Complex.mk c t) Complex.I) Tgood t := by
        intro t ht
        have hdetne := hgood_det t ht
        have htT : Complex.mk c t ∈ T := ht.1
        exact (hslicederiv c t htT hdetne).mono (fun s hs => hs.1)
      have hlb := lintegral_nnnorm_deriv_le_hausdorffMeasure_one_image
        (γ := fun s => g (Complex.mk c s))
        (γ' := fun t => Dg (Complex.mk c t) Complex.I) hTgood_meas
        (hγc_inj.mono (fun t ht => ht.1)) hderiv
      calc ∫⁻ s in Tgood, Φ (Complex.mk c s)
          = ∫⁻ s in Tgood, (‖Dg (Complex.mk c s) Complex.I‖₊ : ℝ≥0∞) := rfl
        _ ≤ μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood) := hlb
    calc ∫⁻ s in Tc, Φ (Complex.mk c s)
        = ∫⁻ s in Tgood, Φ (Complex.mk c s) := hTc_split
      _ ≤ μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood) := hgoodbound
      _ ≤ μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tc) :=
          measure_mono (image_mono (fun t ht => ht.1))
      _ = μH[1] (u ⁻¹' {c} ∩ S) := by rw [hfiber]
  -- ============================================================
  -- Fubini:  ∫⁻ c, ∫⁻ s in T_c, Φ(mk c s)  =  ∫⁻ w in T, Φ w.
  -- ============================================================
  have hmkmeas_all : ∀ c : ℝ, Measurable (fun t : ℝ => Complex.mk c t) := by
    intro c
    have hmcomp : Measurable (fun t : ℝ => Complex.measurableEquivRealProd.symm (c, t)) :=
      Complex.measurableEquivRealProd.symm.measurable.comp (by fun_prop)
    have he : (fun t : ℝ => Complex.mk c t)
        = (fun t : ℝ => Complex.measurableEquivRealProd.symm (c, t)) :=
      funext (fun t => (Complex.measurableEquivRealProd_symm_apply (c, t)).symm)
    exact he ▸ hmcomp
  have hFubini : ∫⁻ c : ℝ, ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s)
      = ∫⁻ w in T, Φ w := by
    -- rewrite each slice as a full integral of an indicator.
    have hslice_eq : ∀ c : ℝ,
        ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s)
          = ∫⁻ s : ℝ, (T.indicator Φ) (Complex.mk c s) := by
      intro c
      have hmkmeas : MeasurableSet {t : ℝ | Complex.mk c t ∈ T} :=
        hTmeas.preimage (hmkmeas_all c)
      rw [← lintegral_indicator hmkmeas]
      apply lintegral_congr
      intro s
      by_cases hmem : Complex.mk c s ∈ T
      · rw [indicator_of_mem hmem, indicator_of_mem (show s ∈ {t : ℝ | Complex.mk c t ∈ T}
          from hmem)]
      · rw [indicator_of_notMem hmem, indicator_of_notMem (show s ∉ {t : ℝ | Complex.mk c t ∈ T}
          from hmem)]
    simp_rw [hslice_eq]
    -- Tonelli through the volume-preserving equiv `ℂ ≃ᵐ ℝ × ℝ`.
    have hΦind_meas : AEMeasurable (T.indicator Φ) volume := by
      rw [aemeasurable_indicator_iff hTmeas]
      exact hΦ_meas
    have hsymm_mp : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) volume :=
      Complex.volume_preserving_equiv_real_prod.symm _
    have hcomp_meas : AEMeasurable
        (fun p : ℝ × ℝ => (T.indicator Φ) (Complex.measurableEquivRealProd.symm p))
        ((volume : Measure ℝ).prod volume) := by
      have : AEMeasurable
          (fun p : ℝ × ℝ => (T.indicator Φ) (Complex.measurableEquivRealProd.symm p))
          (volume : Measure (ℝ × ℝ)) := by
        apply AEMeasurable.comp_aemeasurable' _
          Complex.measurableEquivRealProd.symm.measurable.aemeasurable
        rw [hsymm_mp.map_eq]; exact hΦind_meas
      rwa [Measure.volume_eq_prod] at this
    calc ∫⁻ c : ℝ, ∫⁻ s : ℝ, (T.indicator Φ) (Complex.mk c s)
        = ∫⁻ p : ℝ × ℝ, (T.indicator Φ) (Complex.measurableEquivRealProd.symm p)
            ∂((volume : Measure ℝ).prod volume) := by
          rw [lintegral_prod _ hcomp_meas]
          apply lintegral_congr; intro c
          apply lintegral_congr; intro s
          rw [Complex.measurableEquivRealProd_symm_apply]
      _ = ∫⁻ w : ℂ, (T.indicator Φ) w := by
          rw [← Measure.volume_eq_prod]
          exact (Complex.volume_preserving_equiv_real_prod.symm _).lintegral_comp_emb
            Complex.measurableEquivRealProd.symm.measurableEmbedding _
      _ = ∫⁻ w in T, Φ w := lintegral_indicator hTmeas _
  -- ============================================================
  -- Area formula:  ∫⁻ w in T, Φ w  =  ∫⁻ z in S, ofReal |det Ψ'z| * Φ(Ψ z).
  -- ============================================================
  have hArea : ∫⁻ w in T, Φ w
      = ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z) := by
    rw [hT]
    exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hΨ' hinj Φ
  -- a.e. on S, the integrand equals `‖fderiv ℝ u z‖₊`.
  have hAreaInt : ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z)
      = ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    apply lintegral_congr_ae
    filter_upwards [hdet_ne, hΦΨ, hfderiv_eq] with z hdetz hΦz hfz
    rw [hΦz, hfz]
    have hdtop : ENNReal.ofReal |(Ψ' z).det| ≠ ⊤ := ENNReal.ofReal_ne_top
    have hd0 : ENNReal.ofReal |(Ψ' z).det| ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]; exact hdetz
    rw [ENNReal.mul_div_cancel hd0 hdtop]
  -- Combine (reversed).
  calc ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      = ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z) := hAreaInt.symm
    _ = ∫⁻ w in T, Φ w := hArea.symm
    _ = ∫⁻ c : ℝ, ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s) := hFubini.symm
    _ ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S) := lintegral_mono_ae hslicebound

theorem coarea_regular_ge {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ z in (A ∩ {z | fderiv ℝ u z ≠ 0}), (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
  classical
  have hucont : Continuous u := hu.continuous
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        rw [hc₀v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- reversed per-piece coordinate engine
  have hcoord_core : ∀ (Ψ : ℂ → ℂ) (Ψ' : ℂ → (ℂ →L[ℝ] ℂ)),
      (∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψ (Ψ' z) z) →
      (∀ z, (Ψ z).re = u z) →
      ∀ (s : Set ℂ), MeasurableSet s → Bornology.IsBounded s →
        (∀ z ∈ s, DifferentiableAt ℝ u z) → (∀ z ∈ s, (Ψ' z).det ≠ 0) →
        ∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ s) := by
    intro Ψ Ψ' hΨfd hΨre s hsmeas hsb hsdiff hsdet
    have hΨ'_s : ∀ z ∈ s, HasFDerivWithinAt Ψ (Ψ' z) s z :=
      fun z hz => (hΨfd z (hsdiff z hz)).hasFDerivWithinAt
    set r : (ℂ →L[ℝ] ℂ) → NNReal := fun A' =>
      if h : A'.det ≠ 0 then
        ‖((A'.toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
      else 1 with hr
    have hrpos : ∀ A', r A' ≠ 0 := by
      intro A'
      simp only [hr]
      split_ifs with h
      · set B := A'.toContinuousLinearEquivOfDetNeZero h
        have hBsymm : (B.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
          intro hz
          have h1 : B.symm (B 1) = 1 := B.symm_apply_apply 1
          rw [show B.symm (B 1) = (B.symm : ℂ →L[ℝ] ℂ) (B 1) from rfl, hz] at h1
          simp at h1
        have hnorm_pos : 0 < ‖(B.symm : ℂ →L[ℝ] ℂ)‖₊ := by
          rw [pos_iff_ne_zero]; simpa [nnnorm_eq_zero] using hBsymm
        positivity
      · exact one_ne_zero
    obtain ⟨t, A, hdisj, htmeas, hsub, happrox, hAval⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
        Ψ s Ψ' hΨ'_s r (fun A' => hrpos A')
    have hpiece_meas : ∀ n, MeasurableSet (s ∩ t n) := fun n => hsmeas.inter (htmeas n)
    have hpiece_bd : ∀ n, Bornology.IsBounded (s ∩ t n) :=
      fun n => hsb.subset Set.inter_subset_left
    have hpiece_bound : ∀ n,
        ∫⁻ z in s ∩ t n, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) := by
      intro n
      rcases Set.eq_empty_or_nonempty (s ∩ t n) with hempty | hne
      · rw [hempty]; simp
      · obtain ⟨y, hy, hAy⟩ := hAval ⟨hne.choose, hne.choose_spec.1⟩ n
        have hAdet : (A n).det ≠ 0 := by rw [hAy]; exact hsdet y hy
        set Bequiv := (A n).toContinuousLinearEquivOfDetNeZero hAdet
        have hAeq : ((A n) : ℂ →L[ℝ] ℂ) = (Bequiv : ℂ →L[ℝ] ℂ) :=
          ((A n).coe_toContinuousLinearEquivOfDetNeZero hAdet).symm
        have hrlt : r (A n) < ‖(Bequiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
          simp only [hr, dif_pos hAdet]
          have hBsymm : (Bequiv.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
            intro hz
            have h1 : Bequiv.symm (Bequiv 1) = 1 := Bequiv.symm_apply_apply 1
            rw [show Bequiv.symm (Bequiv 1) = (Bequiv.symm : ℂ →L[ℝ] ℂ) (Bequiv 1) from rfl, hz]
              at h1
            simp at h1
          have hnorm_pos : (0 : NNReal) < ‖(Bequiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
            rw [inv_pos, pos_iff_ne_zero]; simpa [nnnorm_eq_zero] using hBsymm
          exact NNReal.half_lt_self (ne_of_gt hnorm_pos)
        have happrox' : ApproximatesLinearOn Ψ (Bequiv : ℂ →L[ℝ] ℂ) (s ∩ t n) (r (A n)) := by
          rw [← hAeq]; exact happrox n
        exact coarea_piece_ge (hpiece_meas n) (hpiece_bd n) hrlt happrox'
          (fun z hz => (hΨfd z (hsdiff z hz.1)).hasFDerivWithinAt)
          (fun z _ => hΨre z)
          (fun z hz => hsdiff z hz.1)
    have hcvr : s = ⋃ n, (s ∩ t n) := by
      rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.2 hsub).symm
    have hslice_eq : ∀ c : ℝ,
        μH[1] (u ⁻¹' {c} ∩ s) = ∑' n, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) := by
      intro c
      have hcover_c : u ⁻¹' {c} ∩ s = ⋃ n, u ⁻¹' {c} ∩ (s ∩ t n) := by
        rw [← Set.inter_iUnion, ← hcvr]
      rw [hcover_c]
      refine measure_iUnion ?_ ?_
      · intro i j hij
        refine (hdisj hij).mono ?_ ?_ <;> exact fun z hz => hz.2.2
      · intro n
        exact (hucont.measurable (measurableSet_singleton c)).inter (hpiece_meas n)
    calc ∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
        = ∫⁻ z in ⋃ n, (s ∩ t n), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by rw [← hcvr]
      _ = ∑' n, ∫⁻ z in s ∩ t n, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
          rw [lintegral_iUnion (fun n => hpiece_meas n)
            (fun i j hij => (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right)]
      _ ≤ ∑' n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) := ENNReal.tsum_le_tsum hpiece_bound
      _ = ∫⁻ c, ∑' n, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) :=
          (lintegral_tsum (fun n => slice_aemeas (hpiece_meas n))).symm
      _ = ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ s) := by apply lintegral_congr; exact fun c => (hslice_eq c).symm
  -- reversed per-coordinate full bound
  have hcoord_full : ∀ (Ψ : ℂ → ℂ) (Ψ' : ℂ → (ℂ →L[ℝ] ℂ)),
      (∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψ (Ψ' z) z) →
      (∀ z, (Ψ z).re = u z) →
      ∀ (Q : Set ℂ), MeasurableSet Q →
        (∀ z ∈ A ∩ Q, DifferentiableAt ℝ u z) → (∀ z ∈ A ∩ Q, (Ψ' z).det ≠ 0) →
        ∫⁻ z in A ∩ Q, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Q)) := by
    intro Ψ Ψ' hΨfd hΨre Q hQmeas hAQdiff hAQdet
    set R : Set ℂ := A ∩ Q with hR_def
    have hRmeas : MeasurableSet R := hA.inter hQmeas
    set Rm : ℕ → Set ℂ := fun m => R ∩ Metric.closedBall (0:ℂ) m with hRm_def
    have hRm_meas : ∀ m, MeasurableSet (Rm m) := fun m => hRmeas.inter measurableSet_closedBall
    have hRm_bd : ∀ m, Bornology.IsBounded (Rm m) :=
      fun m => (Metric.isBounded_closedBall).subset Set.inter_subset_right
    have hball_mono : Monotone (fun m : ℕ => Metric.closedBall (0:ℂ) (m:ℝ)) :=
      fun a b hab => Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
    have hRm_mono : Monotone Rm :=
      fun a b hab => Set.inter_subset_inter_right _ (hball_mono hab)
    have hRcover : (⋃ m, Rm m) = R := by
      apply Set.Subset.antisymm (Set.iUnion_subset (fun m => Set.inter_subset_left))
      intro z hz
      obtain ⟨N, hN⟩ : ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
        exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
      exact Set.mem_iUnion.2 ⟨N, hz, hN⟩
    have hRm_diff : ∀ m, ∀ z ∈ Rm m, DifferentiableAt ℝ u z :=
      fun m z hz => hAQdiff z hz.1
    have hRm_det : ∀ m, ∀ z ∈ Rm m, (Ψ' z).det ≠ 0 :=
      fun m z hz => hAQdet z hz.1
    -- LHS integral is the monotone sup over Rm ↑ R.
    have hLHSint : ∫⁻ z in R, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
        = ⨆ m, ∫⁻ z in Rm m, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
      rw [← hRcover]
      exact setLIntegral_iUnion_of_directed _ hRm_mono.directed_le
    -- RHS is monotone in m as well.
    rw [hLHSint]
    apply iSup_le
    intro m
    calc ∫⁻ z in Rm m, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
        ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Rm m) :=
          hcoord_core Ψ Ψ' hΨfd hΨre (Rm m) (hRm_meas m) (hRm_bd m)
            (hRm_diff m) (hRm_det m)
      _ ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ R) := by
          apply lintegral_mono; intro c
          exact measure_mono (Set.inter_subset_inter_right _ Set.inter_subset_left)
  -- =====================================================================
  -- (3)  Build the two coordinate maps (`Ψ_im` over `∂u/∂x ≠ 0`, `Ψ_re` over
  --      `∂u/∂x = 0 ∧ ∂u/∂y ≠ 0`) and apply `hcoord_full`.
  -- =====================================================================
  set Diff : Set ℂ := {z | DifferentiableAt ℝ u z} with hDiff_def
  have hDiff_meas : MeasurableSet Diff := measurableSet_of_differentiableAt ℝ u
  set P1 : Set ℂ := {z | (fderiv ℝ u z) (1:ℂ) ≠ 0} with hP1_def
  set P2 : Set ℂ := {z | (fderiv ℝ u z) (1:ℂ) = 0 ∧ (fderiv ℝ u z) Complex.I ≠ 0} with hP2_def
  have hP1_meas : MeasurableSet P1 :=
    (measurableSet_singleton (0:ℝ)).compl.preimage
      ((measurable_fderiv ℝ u).apply_continuousLinearMap (1:ℂ))
  have hP2_meas : MeasurableSet P2 := by
    apply MeasurableSet.inter
    · exact (measurableSet_singleton (0:ℝ)).preimage
        ((measurable_fderiv ℝ u).apply_continuousLinearMap (1:ℂ))
    · exact (measurableSet_singleton (0:ℝ)).compl.preimage
        ((measurable_fderiv ℝ u).apply_continuousLinearMap Complex.I)
  have hNECrit_meas : MeasurableSet {z : ℂ | fderiv ℝ u z ≠ 0} :=
    (measurable_fderiv ℝ u) (measurableSet_singleton (0)).compl
  -- `Ψ_im z = u z • 1 + z.im • I`, derivative `(∇u).smulRight 1 + imCLM.smulRight I`,
  -- `det = ∂u/∂x = (∇u) 1`.
  set Ψim : ℂ → ℂ := fun w => (u w : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I with hΨim
  set Ψim' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    ((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I with hΨim'
  have hΨim_fd : ∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψim (Ψim' z) z := by
    intro z hu_z
    have hPG : HasFDerivAt (fun w : ℂ => u w) (fderiv ℝ u z) z := hu_z.hasFDerivAt
    set LP1 : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℂ) with hLP1
    have hcomp1 : HasFDerivAt (fun w : ℂ => (u w : ℝ) • (1 : ℂ))
        (LP1.comp (fderiv ℝ u z)) z := by
      have := LP1.hasFDerivAt.comp z hPG; convert this using 1
      all_goals exact rfl
    set LQI : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I with hLQI
    have hcomp2 : HasFDerivAt (fun w : ℂ => (w.im : ℝ) • Complex.I)
        (LQI.comp Complex.imCLM) z := by
      have := LQI.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt; convert this using 1
      all_goals exact rfl
    have hsum := hcomp1.add hcomp2
    rw [hΨim, hΨim']; convert hsum using 1
    all_goals exact rfl
  have hΨim_re : ∀ z, (Ψim z).re = u z := by
    intro z; rw [hΨim]; simp [Complex.real_smul]
  have hΨim_det : ∀ z, (Ψim' z).det = (fderiv ℝ u z) (1:ℂ) := by
    intro z
    rw [hΨim']
    set D : ℂ →L[ℝ] ℂ :=
      (((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I) with hD
    rw [show D.det
        = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (D : ℂ →ₗ[ℝ] ℂ)) from
      (LinearMap.det_toMatrix Complex.basisOneI _).symm]
    rw [Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : D 1 = ((fderiv ℝ u z) (1:ℂ) : ℂ) := by
      simp only [hD, add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.one_im, zero_smul,
        add_zero]
      change ((fderiv ℝ u z) (1:ℂ) : ℝ) • (1 : ℂ) = (((fderiv ℝ u z) (1:ℂ) : ℝ) : ℂ); simp
    have h2 : D Complex.I = ((fderiv ℝ u z) Complex.I : ℂ) + Complex.I := by
      simp only [hD, add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.I_im, one_smul]
      change ((fderiv ℝ u z) Complex.I : ℝ) • (1 : ℂ) + Complex.I
        = (((fderiv ℝ u z) Complex.I : ℝ) : ℂ) + Complex.I; simp
    change (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im = (fderiv ℝ u z) (1:ℂ)
    rw [h1, h2]; simp
  -- `Ψ_re z = u z • 1 + z.re • I`, derivative `(∇u).smulRight 1 + reCLM.smulRight I`,
  -- `det = -∂u/∂y = -(∇u) I`.
  set Ψre : ℂ → ℂ := fun w => (u w : ℝ) • (1 : ℂ) + (w.re : ℝ) • Complex.I with hΨre_def
  set Ψre' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    ((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.reCLM.smulRight Complex.I with hΨre'
  have hΨre_fd : ∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψre (Ψre' z) z := by
    intro z hu_z
    have hPG : HasFDerivAt (fun w : ℂ => u w) (fderiv ℝ u z) z := hu_z.hasFDerivAt
    set LP1 : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℂ) with hLP1
    have hcomp1 : HasFDerivAt (fun w : ℂ => (u w : ℝ) • (1 : ℂ))
        (LP1.comp (fderiv ℝ u z)) z := by
      have := LP1.hasFDerivAt.comp z hPG; convert this using 1
      all_goals exact rfl
    set LQI : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I with hLQI
    have hcomp2 : HasFDerivAt (fun w : ℂ => (w.re : ℝ) • Complex.I)
        (LQI.comp Complex.reCLM) z := by
      have := LQI.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt; convert this using 1
      all_goals exact rfl
    have hsum := hcomp1.add hcomp2
    rw [hΨre_def, hΨre']; convert hsum using 1
    all_goals exact rfl
  have hΨre_re : ∀ z, (Ψre z).re = u z := by
    intro z; rw [hΨre_def]; simp [Complex.real_smul]
  have hΨre_det : ∀ z, (Ψre' z).det = - (fderiv ℝ u z) Complex.I := by
    intro z
    rw [hΨre']
    set D : ℂ →L[ℝ] ℂ :=
      (((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.reCLM.smulRight Complex.I) with hD
    rw [show D.det
        = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (D : ℂ →ₗ[ℝ] ℂ)) from
      (LinearMap.det_toMatrix Complex.basisOneI _).symm]
    rw [Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : D 1 = ((fderiv ℝ u z) (1:ℂ) : ℂ) + Complex.I := by
      simp only [hD, add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.one_re, one_smul]
      change ((fderiv ℝ u z) (1:ℂ) : ℝ) • (1 : ℂ) + Complex.I
        = (((fderiv ℝ u z) (1:ℂ) : ℝ) : ℂ) + Complex.I; simp
    have h2 : D Complex.I = ((fderiv ℝ u z) Complex.I : ℂ) := by
      simp only [hD, add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.I_re, zero_smul, add_zero]
      change ((fderiv ℝ u z) Complex.I : ℝ) • (1 : ℂ) = (((fderiv ℝ u z) Complex.I : ℝ) : ℂ); simp
    change (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im = - (fderiv ℝ u z) Complex.I
    rw [h1, h2]; simp
  -- Membership in `P1`/`P2` (with nonzero partial) forces differentiability.
  have hP1diff : ∀ z ∈ A ∩ P1, DifferentiableAt ℝ u z := by
    rintro z ⟨_, hz1⟩
    by_contra hnd
    apply hz1
    rw [fderiv_zero_of_not_differentiableAt hnd]; simp
  have hP2diff : ∀ z ∈ A ∩ P2, DifferentiableAt ℝ u z := by
    rintro z ⟨_, _, hz2⟩
    by_contra hnd
    apply hz2
    rw [fderiv_zero_of_not_differentiableAt hnd]; simp
  have hP1det : ∀ z ∈ A ∩ P1, (Ψim' z).det ≠ 0 := by
    rintro z ⟨_, hz1⟩; rw [hΨim_det]; exact hz1
  have hP2det : ∀ z ∈ A ∩ P2, (Ψre' z).det ≠ 0 := by
    rintro z ⟨_, _, hz2⟩
    rw [hΨre_det]
    simp only [neg_ne_zero]; exact hz2
  have hbound_P1 : ∫⁻ z in A ∩ P1, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P1)) :=
    hcoord_full Ψim Ψim' hΨim_fd hΨim_re P1 hP1_meas hP1diff hP1det
  have hbound_P2 : ∫⁻ z in A ∩ P2, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P2)) :=
    hcoord_full Ψre Ψre' hΨre_fd hΨre_re P2 hP2_meas hP2diff hP2det
  have hdisjP : Disjoint (A ∩ P1) (A ∩ P2) := by
    rw [Set.disjoint_left]
    rintro z ⟨_, hz1⟩ ⟨_, hz2, _⟩
    exact hz1 hz2
  -- P1 ∪ P2 covers Reg ∩ Diff.
  have hP1P2cover : A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff = (A ∩ P1) ∪ (A ∩ P2) := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨hzA, hzne⟩, hzD⟩
      by_cases hp1 : (fderiv ℝ u z) (1:ℂ) ≠ 0
      · exact Or.inl ⟨hzA, hp1⟩
      · have hp1' : (fderiv ℝ u z) (1:ℂ) = 0 := not_not.mp hp1
        have hI : (fderiv ℝ u z) Complex.I ≠ 0 := by
          intro hI0
          apply hzne
          ext w
          have hw : w = w.re • (1:ℂ) + w.im • Complex.I := by
            apply Complex.ext <;> simp [Complex.real_smul]
          rw [hw, map_add, map_smul, map_smul, hp1', hI0]; simp
        exact Or.inr ⟨hzA, hp1', hI⟩
    · rintro z (⟨hzA, hz1⟩ | ⟨hzA, _, hz2I⟩)
      · refine ⟨⟨hzA, ?_⟩, ?_⟩
        · intro h0; apply hz1; rw [h0]; simp
        · by_contra hnd
          apply hz1; rw [fderiv_zero_of_not_differentiableAt hnd]; simp
      · refine ⟨⟨hzA, ?_⟩, ?_⟩
        · intro h0; apply hz2I; rw [h0]; simp
        · by_contra hnd
          apply hz2I; rw [fderiv_zero_of_not_differentiableAt hnd]; simp
  have hReg_meas : MeasurableSet {z : ℂ | fderiv ℝ u z ≠ 0} :=
    (measurable_fderiv ℝ u) (measurableSet_singleton (0)).compl
  -- On Diffᶜ the integrand vanishes, so restricting to the differentiable part is harmless.
  have hDiffc_zero :
      ∫⁻ z in (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) = 0 := by
    have hfg : ∀ z ∈ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ),
        (‖fderiv ℝ u z‖₊ : ℝ≥0∞) = (fun _ => (0 : ℝ≥0∞)) z := by
      rintro z ⟨_, hzD⟩
      simp only [hDiff_def, Set.mem_compl_iff, Set.mem_ofPred_eq] at hzD
      rw [fderiv_zero_of_not_differentiableAt hzD]; simp
    rw [setLIntegral_congr_fun ((hA.inter hReg_meas).inter hDiff_meas.compl) hfg, lintegral_zero]
  have hint_eq : ∫⁻ z in (A ∩ {z | fderiv ℝ u z ≠ 0}), (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      = ∫⁻ z in (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    conv_lhs => rw [show A ∩ {z | fderiv ℝ u z ≠ 0}
        = (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff) ∪ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ) from
      (Set.inter_union_compl _ _).symm]
    have hdisjD : Disjoint (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff)
        (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ) := by
      rw [Set.disjoint_left]; rintro z ⟨_, hzD⟩ ⟨_, hzDc⟩; exact hzDc hzD
    rw [lintegral_union ((hA.inter hReg_meas).inter hDiff_meas.compl) hdisjD, hDiffc_zero, add_zero]
  calc ∫⁻ z in (A ∩ {z | fderiv ℝ u z ≠ 0}), (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      = ∫⁻ z in (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := hint_eq
    _ = ∫⁻ z in ((A ∩ P1) ∪ (A ∩ P2)), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by rw [hP1P2cover]
    _ = (∫⁻ z in A ∩ P1, (‖fderiv ℝ u z‖₊ : ℝ≥0∞))
          + ∫⁻ z in A ∩ P2, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
        rw [lintegral_union (hA.inter hP2_meas) hdisjP]
    _ ≤ (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P1)))
          + ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P2)) := add_le_add hbound_P1 hbound_P2
    _ = ∫⁻ c, (μH[1] (u ⁻¹' {c} ∩ (A ∩ P1)) + μH[1] (u ⁻¹' {c} ∩ (A ∩ P2))) := by
        rw [lintegral_add_left' (slice_aemeas (hA.inter hP1_meas))]
    _ ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
        apply lintegral_mono; intro c
        simp only
        have hdisjslice : Disjoint (u ⁻¹' {c} ∩ (A ∩ P1)) (u ⁻¹' {c} ∩ (A ∩ P2)) :=
          hdisjP.mono Set.inter_subset_right Set.inter_subset_right
        rw [← measure_union hdisjslice
          ((hucont.measurable (measurableSet_singleton c)).inter (hA.inter hP2_meas))]
        apply measure_mono
        rw [← Set.inter_union_distrib_left]
        apply Set.inter_subset_inter_right
        rw [← hP1P2cover]
        exact fun z hz => hz.1



/-- Set-form co-area lower bound: `∫⁻ A ‖∇u‖ ≤ ∫⁻ c μH[1](u⁻¹{c} ∩ A)`. -/
theorem coarea_set_ge {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) := by
  have hReg_meas : MeasurableSet {z : ℂ | fderiv ℝ u z ≠ 0} :=
    (measurable_fderiv ℝ u) (measurableSet_singleton (0)).compl
  have hCrit_meas : MeasurableSet {z : ℂ | fderiv ℝ u z = 0} :=
    measurable_fderiv ℝ u (measurableSet_singleton _)
  -- restrict integrand to regular set (critical part integrand 0)
  have hint_reg : ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      = ∫⁻ z in (A ∩ {z | fderiv ℝ u z ≠ 0}), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    conv_lhs => rw [show A = (A ∩ {z | fderiv ℝ u z ≠ 0}) ∪ (A ∩ {z | fderiv ℝ u z = 0}) from by
      rw [← Set.inter_union_distrib_left]
      rw [show {z : ℂ | fderiv ℝ u z ≠ 0} ∪ {z | fderiv ℝ u z = 0} = Set.univ from by
        ext z; simp [em']]
      simp]
    have hdisj : Disjoint (A ∩ {z | fderiv ℝ u z ≠ 0}) (A ∩ {z | fderiv ℝ u z = 0}) := by
      rw [Set.disjoint_left]; rintro z ⟨_, hz1⟩ ⟨_, hz2⟩; exact hz1 hz2
    rw [lintegral_union (hA.inter hCrit_meas) hdisj]
    have hcrit0 : ∫⁻ z in (A ∩ {z | fderiv ℝ u z = 0}), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) = 0 := by
      have hfg : ∀ z ∈ (A ∩ {z | fderiv ℝ u z = 0}), (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
          = (fun _ => (0 : ℝ≥0∞)) z := by
        rintro z ⟨_, hz2⟩
        simp only [Set.mem_ofPred_eq] at hz2; rw [hz2]; simp
      rw [setLIntegral_congr_fun (hA.inter hCrit_meas) hfg, lintegral_zero]
    rw [hcrit0, add_zero]
  rw [hint_reg]
  refine le_trans (coarea_regular_ge hu hA) ?_
  apply lintegral_mono; intro c
  exact measure_mono (Set.inter_subset_inter_right _ Set.inter_subset_left)


/-- **Gradient-weighted co-area lower bound (companion to `eilenberg_coarea_grad_le`).**

For `K`-Lipschitz `u : ℂ → ℝ` and measurable `g : ℂ → ℝ≥0∞`,
`∫⁻ z, g z * ‖∇u‖₊ ≤ ∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[1])`. By the layer cake this reduces to the
set-form lower bound `coarea_set_ge`, exactly mirroring the reduction of `eilenberg_coarea_grad_le`
to `coarea_set_sharp`. -/
theorem eilenberg_coarea_grad_ge {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume
      ≤ ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ)) := by
  classical
  have hucont : Continuous u := hu.continuous
  set w : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) with hw_def
  have hw_meas : Measurable w := (measurable_fderiv ℝ u).nnnorm.coe_nnreal_ennreal
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        -- `μH[2] B = (c • volume) B = c * volume B < ∞` since `B` is compact.
        obtain ⟨c, hc, hcv⟩ := hausdorffMeasure_two_complex_smul_volume
        rw [hcv, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    -- Dynkin predicate.
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · -- empty
      simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · -- basic: closed `T`, `T ∩ B` compact
      intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · -- complement (a.e. by finiteness of `gB`)
      intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · -- countable disjoint union
      intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  -- (0b)  Full measurable `A'` via the closed-ball exhaustion.
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- A convenience: AEMeasurability of `c ↦ μH[1] (A' ∩ u⁻¹{c})` (intersection
  -- with the roles swapped), which is how the slices appear below.
  have slice_aemeas' : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (A' ∩ u ⁻¹' {c})) := by
    intro A' hA'
    refine (slice_aemeas hA').congr ?_
    filter_upwards with c
    rw [Set.inter_comm]
  -- (A) reversed for a SIMPLE function: ∫ w·s ≤ ∫⁻ c ∫_{u⁻¹c} s.
  have hsimple : ∀ s : SimpleFunc ℂ ℝ≥0∞,
      ∫⁻ z, w z * s z ∂volume
        ≤ ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, s z ∂(μH[1] : Measure ℂ)) := by
    intro s
    have hslice_sum : ∀ c : ℝ,
        (∫⁻ z in u ⁻¹' {c}, s z ∂(μH[1] : Measure ℂ))
          = ∑ x ∈ s.range, x * μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}) := by
      intro c
      rw [SimpleFunc.lintegral_eq_lintegral]
      show s.lintegral ((μH[1] : Measure ℂ).restrict (u ⁻¹' {c})) = _
      rw [SimpleFunc.lintegral]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Measure.restrict_apply (s.measurableSet_preimage {x})]
    rw [lintegral_congr hslice_sum, lintegral_finset_sum']
    · -- LHS `∫ w·s = ∑ x, x·∫_{s⁻¹x} w`, bound each term below by `coarea_set_ge`.
      have hLHS : ∫⁻ z, w z * s z ∂volume = ∑ x ∈ s.range, x * ∫⁻ z in s ⁻¹' {x}, w z ∂volume := by
        have hRHS : ∫⁻ z, w z * s z ∂volume = ∫⁻ z, s z ∂(volume.withDensity w) := by
          rw [lintegral_withDensity_eq_lintegral_mul volume hw_meas s.measurable]
          simp only [Pi.mul_apply]
        rw [hRHS, SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [withDensity_apply w (s.measurableSet_preimage {x})]
      rw [hLHS]
      refine Finset.sum_le_sum ?_
      intro x _
      rw [lintegral_const_mul'' x (slice_aemeas' (s.measurableSet_preimage {x}))]
      refine mul_le_mul' le_rfl ?_
      have hcomm : ∀ c : ℝ,
          μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}) = μH[1] (u ⁻¹' {c} ∩ s ⁻¹' {x}) := by
        intro c; rw [Set.inter_comm]
      rw [lintegral_congr hcomm]
      exact coarea_set_ge hu (s.measurableSet_preimage {x})
    · intro x _
      exact (slice_aemeas' (s.measurableSet_preimage {x})).const_mul x
  -- (B) MCT.  g = ⨆ n, eapprox g n.
  set sn : ℕ → SimpleFunc ℂ ℝ≥0∞ := fun n => SimpleFunc.eapprox g n with hsn_def
  -- LHS: ∫ w·g = ⨆ n, ∫ w·sn
  have hLHS_sup : ∫⁻ z, w z * g z ∂volume = ⨆ n, ∫⁻ z, w z * (sn n) z ∂volume := by
    rw [← lintegral_iSup]
    · refine lintegral_congr fun z => ?_
      rw [← ENNReal.mul_iSup]
      congr 1
      exact (SimpleFunc.iSup_eapprox_apply hg z).symm
    · intro n; exact hw_meas.mul (sn n).measurable
    · intro m n hmn z
      exact mul_le_mul' le_rfl (SimpleFunc.monotone_eapprox g hmn z)
  -- RHS ≥ each term.
  have hgoal_lhs : ∫⁻ z, g z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume
      = ∫⁻ z, w z * g z ∂volume := by
    apply lintegral_congr; intro z; rw [hw_def, mul_comm]
  rw [hgoal_lhs, hLHS_sup]
  refine iSup_le fun n => ?_
  refine le_trans (hsimple (sn n)) ?_
  apply lintegral_mono
  intro c
  apply lintegral_mono_ae
  filter_upwards with z
  calc (sn n) z ≤ ⨆ k, (sn k) z := le_iSup (fun k => (sn k) z) n
    _ = g z := SimpleFunc.iSup_eapprox_apply hg z


/-- **Planar co-area equality for the gradient weight (the Dirichlet-energy identity).**

For a `K`-Lipschitz `u : ℂ → ℝ`, the integrated level-set arc-length weighted by `‖∇u‖` equals the
Dirichlet energy:

`∫⁻ c, (∫⁻ z in u⁻¹{c}, ‖∇u‖₊ ∂μH[1]) = ∫⁻ z, ‖∇u‖₊ ^ 2 ∂volume`.

The `≤` direction is `eilenberg_coarea_grad_le` with `g = ‖∇u‖₊` (and `‖∇u‖ * ‖∇u‖ = ‖∇u‖²`); the
`≥` direction is `eilenberg_coarea_grad_ge` with the same weight. The critical set `{∇u = 0}`
contributes `0` to both sides (the integrand `‖∇u‖` vanishes there), which is why this specific
weight needs no Sard-type argument. -/
theorem eilenberg_coarea_normSq_eq {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂(μH[1] : Measure ℂ))
      = ∫⁻ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hg : Measurable (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞)) :=
    (measurable_fderiv ℝ u).nnnorm.coe_nnreal_ennreal
  have hsq : ∀ z, (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞)) z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      = (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 := fun z => by rw [sq]
  refine le_antisymm ?_ ?_
  · refine le_trans (eilenberg_coarea_grad_le hu hg) ?_
    exact le_of_eq (lintegral_congr fun z => hsq z)
  · refine le_trans (le_of_eq (lintegral_congr fun z => (hsq z).symm)) ?_
    exact eilenberg_coarea_grad_ge hu hg

/-- **Integrated inverse-gradient co-area identity.**

For a `K`-Lipschitz `u : ℂ → ℝ`, integrating the reciprocal gradient weight `‖∇u‖₊⁻¹` over the
fibers recovers the volume of the regular set:

`∫⁻ c, (∫⁻ z in u⁻¹{c}, ‖∇u‖₊⁻¹ ∂μH[1]) = volume {z | fderiv ℝ u z ≠ 0}`.

The `∫⁻ z in u⁻¹{c}, ‖∇u‖₊⁻¹` is (formally) the arclength of the fiber reweighted by the inverse
speed; summing over levels reconstructs the area of `{∇u ≠ 0}` (each regular point is visited by
exactly one fiber with Jacobian `‖∇u‖`, and `‖∇u‖⁻¹ · ‖∇u‖ = 1`). The two-sided co-area equality
(`eilenberg_coarea_grad_le` together with `eilenberg_coarea_grad_ge`) applied to the weight
`g = ‖∇u‖₊⁻¹` turns the left side into `∫⁻ z, ‖∇u‖₊⁻¹ · ‖∇u‖₊`, whose integrand is the indicator of
`{∇u ≠ 0}` (`a⁻¹ · a = 1` for `0 ≠ a ≠ ∞`, and `= 0` when `a = 0`). -/
theorem eilenberg_coarea_inv_grad {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)⁻¹ ∂(μH[1] : Measure ℂ))
      = volume {z : ℂ | fderiv ℝ u z ≠ 0} := by
  classical
  set S : Set ℂ := {z : ℂ | fderiv ℝ u z ≠ 0} with hS_def
  have hS_meas : MeasurableSet S := by
    have : S = fderiv ℝ u ⁻¹' {(0 : ℂ →L[ℝ] ℝ)}ᶜ := by
      ext z; simp [hS_def]
    rw [this]
    exact (measurable_fderiv ℝ u) (measurableSet_singleton (0 : ℂ →L[ℝ] ℝ)).compl
  have hg : Measurable (fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞)⁻¹) :=
    ((measurable_fderiv ℝ u).nnnorm.coe_nnreal_ennreal).inv
  -- Co-area equality with `g = ‖∇u‖₊⁻¹`: LHS = `∫⁻ z, ‖∇u‖₊⁻¹ · ‖∇u‖₊`.
  have hcoarea : ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)⁻¹ ∂(μH[1] : Measure ℂ))
      = ∫⁻ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)⁻¹ * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume :=
    le_antisymm (eilenberg_coarea_grad_le hu hg) (eilenberg_coarea_grad_ge hu hg)
  rw [hcoarea]
  -- Pointwise: `‖∇u‖₊⁻¹ · ‖∇u‖₊ = S.indicator 1 z`.
  have hpt : ∀ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)⁻¹ * (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
      = S.indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz : fderiv ℝ u z = 0
    · have hnorm : (‖fderiv ℝ u z‖₊ : ℝ≥0∞) = 0 := by
        simp [hz]
      have hzS : z ∉ S := by simp [hS_def, hz]
      rw [hnorm, Set.indicator_of_notMem hzS]
      simp
    · have hne : (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≠ 0 := by
        simpa [ENNReal.coe_eq_zero, nnnorm_eq_zero] using hz
      have hzS : z ∈ S := hz
      rw [ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, Set.indicator_of_mem hzS]
  rw [lintegral_congr hpt, lintegral_indicator hS_meas, lintegral_one,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- **Per-level Cauchy–Schwarz for the co-area (a Talenti-method building block).**

On a single fiber `u⁻¹{c}`, the length of the regular part is controlled by the product of the
integrated speed and the integrated inverse speed:

`(μH[1] (u⁻¹{c} ∩ {∇u ≠ 0}))² ≤ (∫⁻ ‖∇u‖₊ ∂μH[1]) · (∫⁻ ‖∇u‖₊⁻¹ ∂μH[1])`,

both integrals taken over the fiber. This is Cauchy–Schwarz with `f = √‖∇u‖`, `g = √(1/‖∇u‖)`:
off the critical set `f · g = 1`, so `(∫ 1)² ≤ (∫ ‖∇u‖)(∫ 1/‖∇u‖)`. The proof is the `ℝ≥0∞`
Hölder inequality `ENNReal.lintegral_mul_le_Lp_mul_Lq` with the conjugate pair `(2, 2)`, whose
left side dominates the length of the regular part and whose two factors are the speed and inverse
speed integrals. -/
theorem coarea_level_cauchySchwarz {u : ℂ → ℝ} (hu : Measurable (fderiv ℝ u)) (c : ℝ) :
    (μH[1] (u ⁻¹' {c} ∩ {z : ℂ | fderiv ℝ u z ≠ 0})) ^ 2
      ≤ (∫⁻ z in u ⁻¹' {c}, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂(μH[1] : Measure ℂ))
        * (∫⁻ z in u ⁻¹' {c}, (‖fderiv ℝ u z‖₊ : ℝ≥0∞)⁻¹ ∂(μH[1] : Measure ℂ)) := by
  classical
  set a : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) with ha_def
  set f : ℂ → ℝ≥0∞ := fun z => a z ^ (1 / 2 : ℝ) with hf_def
  set g : ℂ → ℝ≥0∞ := fun z => (a z)⁻¹ ^ (1 / 2 : ℝ) with hg_def
  set μ : Measure ℂ := (μH[1] : Measure ℂ).restrict (u ⁻¹' {c}) with hμ_def
  set R : Set ℂ := {z : ℂ | fderiv ℝ u z ≠ 0} with hR_def
  have ha_meas : Measurable a := hu.nnnorm.coe_nnreal_ennreal
  have hrpow : Measurable (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable
  have hf_meas : AEMeasurable f μ := (hrpow.comp ha_meas).aemeasurable
  have hg_meas : AEMeasurable g μ := (hrpow.comp ha_meas.inv).aemeasurable
  have haux : ∀ z, a z ≠ ⊤ := fun z => ENNReal.coe_ne_top
  -- The two Hölder factors are the speed and inverse-speed integrals.
  have hfsq : ∀ z, f z ^ (2 : ℝ) = a z := fun z => by
    rw [hf_def, ← ENNReal.rpow_mul]; norm_num
  have hgsq : ∀ z, g z ^ (2 : ℝ) = (a z)⁻¹ := fun z => by
    rw [hg_def, ← ENNReal.rpow_mul]; norm_num
  -- Hölder `(2, 2)`: `∫⁻ (f · g) ≤ (∫⁻ f²)^(1/2) (∫⁻ g²)^(1/2)`.
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf_meas hg_meas
  rw [lintegral_congr hfsq, lintegral_congr hgsq] at hhold
  -- Lower bound: `f · g ≥ R.indicator 1` pointwise (`= 1` off the critical set).
  have hpt : ∀ z, R.indicator (fun _ => (1 : ℝ≥0∞)) z ≤ (f * g) z := by
    intro z
    by_cases hz : z ∈ R
    · have hzR : fderiv ℝ u z ≠ 0 := hz
      have hane : a z ≠ 0 := by
        simpa [ha_def, ENNReal.coe_eq_zero, nnnorm_eq_zero] using hzR
      have : (f * g) z = 1 := by
        rw [Pi.mul_apply, hf_def, hg_def, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_inv_cancel hane (haux z), ENNReal.one_rpow]
      rw [Set.indicator_of_mem hz, this]
    · rw [Set.indicator_of_notMem hz]; exact zero_le
  -- Length of the regular part is an indicator integral, dominated by `∫⁻ (f · g)`.
  have hR_meas : MeasurableSet R := by
    have : R = fderiv ℝ u ⁻¹' {(0 : ℂ →L[ℝ] ℝ)}ᶜ := by ext z; simp [hR_def]
    rw [this]; exact hu (measurableSet_singleton (0 : ℂ →L[ℝ] ℝ)).compl
  have hlen : μH[1] (u ⁻¹' {c} ∩ R) ≤ ∫⁻ z, (f * g) z ∂μ := by
    calc μH[1] (u ⁻¹' {c} ∩ R)
        = ∫⁻ z in u ⁻¹' {c}, R.indicator (fun _ => (1 : ℝ≥0∞)) z ∂μH[1] := by
          rw [lintegral_indicator hR_meas, lintegral_one, Measure.restrict_restrict hR_meas,
            Measure.restrict_apply_univ, Set.inter_comm]
      _ ≤ ∫⁻ z, (f * g) z ∂μ := lintegral_mono hpt
  -- Chain and square.
  calc (μH[1] (u ⁻¹' {c} ∩ R)) ^ 2
      ≤ (∫⁻ z, (f * g) z ∂μ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ z, a z ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ z, (a z)⁻¹ ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ z, a z ∂μ) * (∫⁻ z, (a z)⁻¹ ∂μ) := by
        rw [mul_pow, ← ENNReal.rpow_natCast ((∫⁻ z, a z ∂μ) ^ (1 / 2 : ℝ)) 2,
          ← ENNReal.rpow_natCast ((∫⁻ z, (a z)⁻¹ ∂μ) ^ (1 / 2 : ℝ)) 2,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

end RiemannDynamics.Coarea

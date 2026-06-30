/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Defs.Geometric
import RiemannDynamics.QC.LengthArea.CurveModulus
import RiemannDynamics.Analysis.WeakCompactness
import RiemannDynamics.Analysis.ArcLengthVariation
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Function.Floor

/-!
# Lower semicontinuity of the image-family modulus

Under locally uniform convergence `fₙ → g` of homeomorphisms of the plane, the conformal
modulus of the image connecting family of a quadrilateral is lower semicontinuous:

`curveModulus (Q.imageCurveFamily g) ≤ liminf (fun n => curveModulus (Q.imageCurveFamily (fₙ n)))`.

This is the conformal-modulus form of Väisälä's lower-semicontinuity theorem and the substantive
analytic input to the closedness of geometric `K`-quasiconformality under locally uniform limits.

## Architecture

The top-level theorem `curveModulus_imageCurveFamily_lsc` is assembled by pure `ℝ≥0∞`
order theory from a single core reduction
`exists_admissibleDensity_imageCurveFamily_limit`, which produces — from a *tail* of the
approximating sequence — a density admissible for the `g`-image family with energy bounded by the
infimal tail energy.  The core reduction in turn rests on the following genuinely classical
sub-lemmas, each stated *without any derivative-control hypothesis* (uniform convergence of bare
homeomorphisms gives no convergence of derivatives, and the pushforward of a polygonal path by a
bare homeomorphism need not even be absolutely continuous):

* `arcLengthLineIntegral_le_liminf_of_tendstoUniformly` — **weighted line-integral lower
  semicontinuity** along a uniformly convergent sequence of curves.  This is the only place where
  the limiting curve and its approximants interact; it is phrased through
  `arcLengthLineIntegral` (no derivatives of the limit are referenced beyond the integral itself).

* `exists_imageCurveFamily_approx` — an **absolute-continuity-preserving approximation device**:
  every absolutely continuous curve in the `g`-image family is the uniform limit of absolutely
  continuous curves lying in the `fₙ`-image families along a tail.  No derivative control of the
  approximants is asserted.

* `exists_admissibleDensity_imageCurveFamily_limit` — the **weak-`L²` limit-density construction**:
  near-optimal `ℝ≥0∞` densities for the tail families are bridged to real `L²(ℂ)`, a weakly
  convergent subsequence and its Mazur convex combinations produce an a.e. limit density of
  controlled energy, and the two sub-lemmas above promote it to admissibility for the limit family.

The weighted line-integral lower-semicontinuity is proved; the two remaining foundational
sub-lemmas (the uniformly-quasiconformal curve approximation and the weak-`L²` density limit) carry
the `sorry`s and rest on the quasiconformal-regularity layer in `QC/Regularity/`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

namespace Quadrilateral

/-- **Weighted line-integral lower semicontinuity under uniform curve convergence.**
For a *lower semicontinuous* density `ρ : ℂ → ℝ≥0∞` and a sequence of curves `δ : ℕ → ℝ → ℂ`
converging uniformly on `[0, 1]` to a curve `δlim`, with every `δ k` and `δlim` continuous and
absolutely continuous on `[0, 1]`, the arc-length line integral of `ρ` along the limit is at most
the lower limit of the line integrals along the approximants:

`arcLengthLineIntegral ρ δlim ≤ liminf (fun k => arcLengthLineIntegral ρ (δ k)) atTop`.

Lower semicontinuity of `ρ` is essential: for a merely measurable (e.g. upper semicontinuous) `ρ`
the statement is false — with `ρ` the indicator of the real axis, `δlim t = t` (line integral `1`)
and `δ k t = t + i/k` (line integral `0`, converging uniformly) violate it. No convergence of
derivatives is assumed (and none holds for bare uniform convergence): the statement is in terms of
`arcLengthLineIntegral` only. Mathematically this is the standard fact that the length of a curve,
weighted by a fixed lower-semicontinuous density, is lower semicontinuous in the uniform topology —
proved by reducing the density to an increasing limit of continuous compactly-supported densities,
for which the weighted length is a supremum over finite polygonal inscriptions, each continuous
under uniform convergence. -/
theorem arcLengthLineIntegral_le_liminf_of_tendstoUniformly {ρ : ℂ → ℝ≥0∞}
    (hρ : LowerSemicontinuous ρ)
    {δ : ℕ → ℝ → ℂ} {δlim : ℝ → ℂ}
    (hδcont : ∀ k, Continuous (δ k)) (hδac : ∀ k, AbsolutelyContinuousOnInterval (δ k) 0 1)
    (hδlimcont : Continuous δlim) (hδlimac : AbsolutelyContinuousOnInterval δlim 0 1)
    (hunif : TendstoUniformlyOn δ δlim atTop (Set.Icc (0 : ℝ) 1)) :
    arcLengthLineIntegral ρ δlim
      ≤ liminf (fun k => arcLengthLineIntegral ρ (δ k)) atTop := by
  classical
  -- The lower-semicontinuous weighted length is approximated from below by *partition sums*
  -- `partSum γ n I = Σ_{i<n} (inf_{[Iᵢ,Iᵢ₊₁]} ρ∘γ) · eVariationOn γ (Icc Iᵢ Iᵢ₊₁)`.  Three
  -- pillars: (A) each `partSum ≤ arcLengthLineIntegral`; (B) each `partSum` is lower
  -- semicontinuous under uniform convergence; (C) the integral along `δlim` is the supremum
  -- of dyadic partition sums (Lebesgue monotone convergence of lower Darboux step functions).
  set partSum : (ℝ → ℂ) → ℕ → (ℕ → ℝ) → ℝ≥0∞ := fun γ n I =>
    ∑ i ∈ Finset.range n,
      (⨅ s ∈ Set.Icc (I i) (I (i + 1)), ρ (γ s)) * eVariationOn γ (Set.Icc (I i) (I (i + 1)))
    with hpartSum
  -- `ρ` is lower semicontinuous, hence measurable; so is `‖deriv γ‖₊`-weighted integrand.
  have hρmeas : Measurable ρ := hρ.measurable
  -- **Subinterval arc length = speed integral.**
  have hevSub : ∀ {γ : ℝ → ℂ}, AbsolutelyContinuousOnInterval γ 0 1 →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        eVariationOn γ (Set.Icc a b) = ∫⁻ t in Set.Icc a b, (‖deriv γ t‖₊ : ℝ≥0∞) := by
    intro γ hγac a b ha hab hb
    refine eVariationOn_eq_lintegral_norm_deriv hab ?_
    refine hγac.mono ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc ha hb
  -- ===========================================================================================
  -- **Pillar A: partition sums are dominated by the line integral.**
  -- ===========================================================================================
  -- Measurability helpers (curves here are continuous).
  have hmeasSpeed : ∀ (γ : ℝ → ℂ), Measurable (fun t => (‖deriv γ t‖₊ : ℝ≥0∞)) := by
    intro γ
    exact measurable_coe_nnreal_ennreal.comp (measurable_deriv γ).nnnorm
  have hmeasInt : ∀ {γ : ℝ → ℂ}, Continuous γ →
      Measurable (fun t => ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)) := by
    intro γ hγc
    exact (hρmeas.comp hγc.measurable).mul (hmeasSpeed γ)
  have pillarA : ∀ {γ : ℝ → ℂ}, Continuous γ → AbsolutelyContinuousOnInterval γ 0 1 →
      ∀ (n : ℕ) (I : ℕ → ℝ), Monotone I → (∀ i, i ≤ n → I i ∈ Set.Icc (0:ℝ) 1) →
        partSum γ n I ≤ arcLengthLineIntegral ρ γ := by
    intro γ hγc hγac n I hImono hImem
    rw [hpartSum]
    -- Each term is bounded by the integral over the subinterval's `Ioc`.
    have hterm : ∀ i, i < n →
        (⨅ s ∈ Set.Icc (I i) (I (i + 1)), ρ (γ s)) * eVariationOn γ (Set.Icc (I i) (I (i + 1)))
          ≤ ∫⁻ t in Set.Ioc (I i) (I (i + 1)), ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      intro i hi
      have hii : I i ≤ I (i + 1) := hImono (Nat.le_succ i)
      have hi0 : (0:ℝ) ≤ I i := (hImem i (le_of_lt hi)).1
      have hi1 : I (i + 1) ≤ 1 := (hImem (i + 1) hi).2
      set c := ⨅ s ∈ Set.Icc (I i) (I (i + 1)), ρ (γ s) with hc
      have hevIcc : eVariationOn γ (Set.Icc (I i) (I (i + 1)))
          = ∫⁻ t in Set.Icc (I i) (I (i + 1)), (‖deriv γ t‖₊ : ℝ≥0∞) := hevSub hγac _ _ hi0 hii hi1
      have hIccIoc : (∫⁻ t in Set.Icc (I i) (I (i + 1)), (‖deriv γ t‖₊ : ℝ≥0∞))
          = ∫⁻ t in Set.Ioc (I i) (I (i + 1)), (‖deriv γ t‖₊ : ℝ≥0∞) :=
        setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
      rw [hevIcc, hIccIoc]
      calc c * ∫⁻ t in Set.Ioc (I i) (I (i + 1)), (‖deriv γ t‖₊ : ℝ≥0∞)
          = ∫⁻ t in Set.Ioc (I i) (I (i + 1)), c * (‖deriv γ t‖₊ : ℝ≥0∞) := by
            rw [lintegral_const_mul _ (hmeasSpeed γ)]
        _ ≤ ∫⁻ t in Set.Ioc (I i) (I (i + 1)), ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
            refine setLIntegral_mono (hmeasInt hγc) ?_
            intro t ht
            gcongr
            refine iInf₂_le_of_le t ?_ le_rfl
            exact ⟨le_of_lt ht.1, ht.2⟩
    -- Sum over disjoint `Ioc`s contained in `Icc 0 1`.
    have hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint
        (fun i => Set.Ioc (I i) (I (i + 1))) :=
      (hImono.pairwise_disjoint_on_Ioc_succ).set_pairwise _
    have hunionsub : (⋃ i ∈ Finset.range n, Set.Ioc (I i) (I (i + 1))) ⊆ Set.Icc (0:ℝ) 1 := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨i, hi, hzi⟩ := hz
      rw [Finset.mem_range] at hi
      exact ⟨le_trans (hImem i (le_of_lt hi)).1 (le_of_lt hzi.1),
        le_trans hzi.2 (hImem (i + 1) hi).2⟩
    calc ∑ i ∈ Finset.range n,
          (⨅ s ∈ Set.Icc (I i) (I (i + 1)), ρ (γ s)) * eVariationOn γ (Set.Icc (I i) (I (i + 1)))
        ≤ ∑ i ∈ Finset.range n,
            ∫⁻ t in Set.Ioc (I i) (I (i + 1)), ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hterm i (Finset.mem_range.mp hi)
      _ = ∫⁻ t in ⋃ i ∈ Finset.range n, Set.Ioc (I i) (I (i + 1)),
            ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
          rw [lintegral_biUnion_finset hdisj (fun i _ => measurableSet_Ioc)]
      _ ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) :=
          lintegral_mono_set hunionsub
      _ = arcLengthLineIntegral ρ γ := rfl
  -- ===========================================================================================
  -- **Pillar B: each partition sum is lower semicontinuous under uniform convergence.**
  -- ===========================================================================================
  -- First: the per-edge infimum `γ ↦ ⨅_{[a,b]} ρ∘γ` is lower semicontinuous.
  have hinfLSC : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc (0:ℝ) 1 →
      (⨅ s ∈ Set.Icc a b, ρ (δlim s))
        ≤ liminf (fun k => ⨅ s ∈ Set.Icc a b, ρ (δ k s)) atTop := by
    intro a b hab habsub
    rw [le_liminf_iff]
    intro y hy
    -- `y < ⨅_{[a,b]} ρ∘δlim`, choose `y < y' < ⨅`.
    obtain ⟨y', hyy', hy'inf⟩ := exists_between hy
    -- `ρ ∘ δlim` is `> y'` on `[a,b]`, i.e. `δlim '' Icc a b ⊆ U := ρ⁻¹(Ioi y')`, open.
    have hUopen : IsOpen (ρ ⁻¹' Set.Ioi y') :=
      lowerSemicontinuous_iff_isOpen_preimage.mp hρ y'
    have hKcompact : IsCompact (δlim '' Set.Icc a b) :=
      (isCompact_Icc).image hδlimcont
    have hKsubU : δlim '' Set.Icc a b ⊆ ρ ⁻¹' Set.Ioi y' := by
      rintro _ ⟨s, hs, rfl⟩
      have : y' < ⨅ s ∈ Set.Icc a b, ρ (δlim s) := hy'inf
      exact Set.mem_preimage.mpr (lt_of_lt_of_le this (iInf₂_le s hs))
    obtain ⟨r, hr, hrsub⟩ := hKcompact.exists_thickening_subset_open hUopen hKsubU
    -- Uniform convergence: eventually `δ k s` lands in the thickening of `K`.
    have hev : ∀ᶠ k in atTop, ∀ s ∈ Set.Icc a b, y' < ρ (δ k s) := by
      -- `δ → δlim` uniformly on `Icc 0 1`; `Icc a b ⊆ Icc 0 1`.
      rw [Metric.tendstoUniformlyOn_iff] at hunif
      have hr2 : (0:ℝ) < r := hr
      filter_upwards [hunif r hr2] with k hk s hs
      have hsIcc01 : s ∈ Set.Icc (0:ℝ) 1 := habsub hs
      have hdist : dist (δlim s) (δ k s) < r := hk s hsIcc01
      have hmem : δ k s ∈ Metric.thickening r (δlim '' Set.Icc a b) := by
        rw [Metric.mem_thickening_iff]
        exact ⟨δlim s, ⟨s, hs, rfl⟩, by rw [dist_comm]; exact hdist⟩
      have : δ k s ∈ ρ ⁻¹' Set.Ioi y' := hrsub hmem
      exact this
    filter_upwards [hev] with k hk
    refine lt_of_lt_of_le hyy' ?_
    refine le_iInf₂ ?_
    intro s hs
    exact le_of_lt (hk s hs)
  -- Binary superadditivity of `liminf` in `ℝ≥0∞`.
  have hadd2 : ∀ u v : ℕ → ℝ≥0∞,
      liminf u atTop + liminf v atTop ≤ liminf (fun k => u k + v k) atTop := by
    intro u v
    rw [le_liminf_iff]
    intro c hc
    rcases eq_or_ne (liminf u atTop) 0 with hu0 | hu0
    · -- `liminf u = 0`, so `c < liminf v`.
      rw [hu0, zero_add] at hc
      filter_upwards [eventually_lt_of_lt_liminf hc] with k hk
      exact lt_of_lt_of_le hk le_add_self
    rcases eq_or_ne (liminf v atTop) 0 with hv0 | hv0
    · rw [hv0, add_zero] at hc
      filter_upwards [eventually_lt_of_lt_liminf hc] with k hk
      exact lt_of_lt_of_le hk (self_le_add_right _ _)
    · obtain ⟨a', ha', b', hb', hcab⟩ := ENNReal.exists_lt_add_of_lt_add hc hu0 hv0
      filter_upwards [eventually_lt_of_lt_liminf ha', eventually_lt_of_lt_liminf hb']
        with k hka hkb
      exact lt_of_lt_of_le hcab (add_le_add hka.le hkb.le)
  -- Finite-sum superadditivity of `liminf`.
  have haddsum : ∀ (m : ℕ) (g : ℕ → ℕ → ℝ≥0∞),
      ∑ i ∈ Finset.range m, liminf (fun k => g i k) atTop
        ≤ liminf (fun k => ∑ i ∈ Finset.range m, g i k) atTop := by
    intro m g
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      calc (∑ i ∈ Finset.range m, liminf (fun k => g i k) atTop) + liminf (fun k => g m k) atTop
          ≤ liminf (fun k => ∑ i ∈ Finset.range m, g i k) atTop + liminf (fun k => g m k) atTop :=
            add_le_add ih le_rfl
        _ ≤ liminf (fun k => (∑ i ∈ Finset.range m, g i k) + g m k) atTop :=
            hadd2 _ _
  -- **eVariationOn lower semicontinuity under uniform convergence on a subinterval.**
  have hevLSC : ∀ a b : ℝ, Set.Icc a b ⊆ Set.Icc (0:ℝ) 1 →
      eVariationOn δlim (Set.Icc a b)
        ≤ liminf (fun k => eVariationOn (δ k) (Set.Icc a b)) atTop := by
    intro a b habsub
    rw [le_liminf_iff]
    intro v hv
    -- Pointwise convergence on `Icc a b` (from uniform on `Icc 0 1`).
    have hptw : ∀ x ∈ Set.Icc a b, Filter.Tendsto (fun k => δ k x) atTop (𝓝 (δlim x)) := by
      intro x hx
      exact hunif.tendsto_at (habsub hx)
    exact eVariationOn.lowerSemicontinuous_aux hptw hv
  -- ===========================================================================================
  -- **Pillar B: partition sums are lower semicontinuous under uniform convergence.**
  -- ===========================================================================================
  have pillarB : ∀ (n : ℕ) (I : ℕ → ℝ), Monotone I → (∀ i, i ≤ n → I i ∈ Set.Icc (0:ℝ) 1) →
      partSum δlim n I ≤ liminf (fun k => partSum (δ k) n I) atTop := by
    intro n I hImono hImem
    rw [hpartSum]
    refine le_trans ?_ (haddsum n (fun i k =>
      (⨅ s ∈ Set.Icc (I i) (I (i + 1)), ρ (δ k s)) *
        eVariationOn (δ k) (Set.Icc (I i) (I (i + 1)))))
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hii : I i ≤ I (i + 1) := hImono (Nat.le_succ i)
    have hi0 : (0:ℝ) ≤ I i := (hImem i (le_of_lt hi)).1
    have hi1 : I (i + 1) ≤ 1 := (hImem (i + 1) hi).2
    have hsub : Set.Icc (I i) (I (i + 1)) ⊆ Set.Icc (0:ℝ) 1 := Set.Icc_subset_Icc hi0 hi1
    set J := Set.Icc (I i) (I (i + 1)) with hJ
    calc (⨅ s ∈ J, ρ (δlim s)) * eVariationOn δlim J
        ≤ liminf (fun k => ⨅ s ∈ J, ρ (δ k s)) atTop *
            liminf (fun k => eVariationOn (δ k) J) atTop :=
          mul_le_mul' (hinfLSC _ _ hii hsub) (hevLSC _ _ hsub)
      _ ≤ liminf (fun k => (⨅ s ∈ J, ρ (δ k s)) * eVariationOn (δ k) J) atTop :=
          ENNReal.le_liminf_mul
  -- ===========================================================================================
  -- **Pillar C: the line integral along `δlim` is a supremum of dyadic partition sums.**
  -- ===========================================================================================
  -- Dyadic partition points and the corresponding lower-Darboux step density.
  set Idy : ℕ → ℕ → ℝ := fun m i => (i : ℝ) / 2 ^ m with hIdy
  -- `G m n` is the infimum of `ρ ∘ δlim` over the level-`m` dyadic block with left index `n`.
  set Gstep : ℕ → ℤ → ℝ≥0∞ :=
    fun m n => ⨅ s ∈ Set.Icc ((n : ℝ) / 2 ^ m) ((n + 1) / 2 ^ m), ρ (δlim s) with hGstep
  set gdy : ℕ → ℝ → ℝ≥0∞ := fun m t => Gstep m ⌊(2 ^ m : ℝ) * t⌋ with hgdy
  -- `Idy m` is monotone with values in `[0,1]` up to index `2^m`.
  have hIdymono : ∀ m, Monotone (Idy m) := by
    intro m i j hij
    simp only [hIdy]
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    gcongr
  have hIdymem : ∀ m i, i ≤ 2 ^ m → Idy m i ∈ Set.Icc (0:ℝ) 1 := by
    intro m i hi
    simp only [hIdy, Set.mem_Icc]
    have h2m : (0:ℝ) < 2 ^ m := by positivity
    constructor
    · positivity
    · rw [div_le_one h2m]
      calc (i : ℝ) ≤ (2 ^ m : ℕ) := by exact_mod_cast hi
        _ = (2:ℝ) ^ m := by push_cast; ring
  -- `Idy m (i+1) = Idy m i + 1/2^m` and the successor relation for the block.
  have hgdy_meas : ∀ m, Measurable (gdy m) := by
    intro m
    apply Measurable.comp (measurable_from_top (f := Gstep m))
    exact Measurable.floor (measurable_id.const_mul ((2:ℝ) ^ m))
  -- **(C-step) the integral of the step density over a subinterval is the partition term.**
  have hgdy_block : ∀ m (i : ℕ), i < 2 ^ m →
      ∀ t ∈ Set.Ioo (Idy m i) (Idy m (i + 1)), gdy m t = Gstep m i := by
    intro m i _ t ht
    simp only [hgdy]
    congr 1
    -- `⌊2^m * t⌋ = i` for `t ∈ (i/2^m, (i+1)/2^m)`.
    have h2m : (0:ℝ) < 2 ^ m := by positivity
    have hlo : (i : ℝ) < 2 ^ m * t := by
      have := ht.1
      simp only [hIdy] at this
      rw [div_lt_iff₀ h2m] at this
      linarith [this]
    have hhi : 2 ^ m * t < (i : ℝ) + 1 := by
      have := ht.2
      simp only [hIdy] at this
      rw [lt_div_iff₀ h2m] at this
      push_cast at this
      linarith [this]
    have : ⌊(2 ^ m : ℝ) * t⌋ = (i : ℤ) := by
      rw [Int.floor_eq_iff]
      refine ⟨by push_cast; linarith [hlo], by push_cast; linarith [hhi]⟩
    rw [this]
  -- The dyadic `Ioc`s cover `Ioc 0 1`.
  have hcover : ∀ m, (⋃ i ∈ Finset.range (2 ^ m), Set.Ioc (Idy m i) (Idy m (i + 1)))
      = Set.Ioc (0:ℝ) 1 := by
    intro m
    have h2m : (0:ℝ) < 2 ^ m := by positivity
    apply Set.Subset.antisymm
    · intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨i, hi, hzi⟩ := hz
      rw [Finset.mem_range] at hi
      have hil : Idy m i ∈ Set.Icc (0:ℝ) 1 := hIdymem m i (le_of_lt hi)
      have hir : Idy m (i + 1) ∈ Set.Icc (0:ℝ) 1 := hIdymem m (i + 1) hi
      exact ⟨lt_of_le_of_lt hil.1 hzi.1, le_trans hzi.2 hir.2⟩
    · intro z hz
      -- `z ∈ (0,1]`; pick `i = ⌈2^m z⌉ - 1`.
      simp only [Set.mem_iUnion]
      have hz0 : (0:ℝ) < z := hz.1
      have hz1 : z ≤ 1 := hz.2
      set i : ℕ := ⌈(2 ^ m : ℝ) * z⌉.toNat - 1 with hi
      have hceil_pos : 0 < ⌈(2 ^ m : ℝ) * z⌉ := by
        rw [Int.lt_ceil]; push_cast; positivity
      have hceil_le : ⌈(2 ^ m : ℝ) * z⌉ ≤ (2 ^ m : ℤ) := by
        rw [Int.ceil_le]; push_cast
        rw [show ((2:ℝ) ^ m) = (2 ^ m : ℝ) from rfl]
        nlinarith [hz1, h2m]
      have htoNat : (⌈(2 ^ m : ℝ) * z⌉.toNat : ℤ) = ⌈(2 ^ m : ℝ) * z⌉ :=
        Int.toNat_of_nonneg hceil_pos.le
      have hipos : 1 ≤ ⌈(2 ^ m : ℝ) * z⌉.toNat := by
        omega
      have hicastZ : (i : ℤ) = ⌈(2 ^ m : ℝ) * z⌉ - 1 := by
        rw [hi, Nat.cast_sub hipos, htoNat]; norm_num
      have hicast : (i : ℝ) = (⌈(2 ^ m : ℝ) * z⌉ : ℝ) - 1 := by
        have := hicastZ
        have : ((i : ℤ) : ℝ) = ((⌈(2 ^ m : ℝ) * z⌉ - 1 : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at this; exact_mod_cast this
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_range]
        have : (i : ℤ) ≤ (2 ^ m : ℤ) - 1 := by rw [hicastZ]; omega
        have hcast : (i : ℤ) < (2 ^ m : ℤ) := by omega
        have : (i : ℕ) < 2 ^ m := by exact_mod_cast hcast
        exact this
      · constructor
        · -- `Idy m i < z`: `i/2^m < z`.
          simp only [hIdy]
          rw [div_lt_iff₀ h2m, hicast]
          have := Int.ceil_lt_add_one ((2 ^ m : ℝ) * z)
          linarith [this]
        · -- `z ≤ Idy m (i+1)`: `z ≤ (i+1)/2^m`.
          simp only [hIdy]
          rw [le_div_iff₀ h2m]
          have heq : ((i : ℝ) + 1) = (⌈(2 ^ m : ℝ) * z⌉ : ℝ) := by rw [hicast]; ring
          push_cast
          rw [heq]
          have := Int.le_ceil ((2 ^ m : ℝ) * z)
          linarith [this]
  -- `Gstep m i` identifies with the partition-term infimum.
  have hGstep_eq : ∀ m (i : ℕ),
      Gstep m (i : ℤ) = ⨅ s ∈ Set.Icc (Idy m i) (Idy m (i + 1)), ρ (δlim s) := by
    intro m i
    simp only [hGstep, hIdy]
    norm_num
  -- **(C-integral) the step-density integral equals the dyadic partition sum.**
  have hpartSumInt : ∀ m, ∫⁻ t in Set.Icc (0:ℝ) 1, gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞)
      = partSum δlim (2 ^ m) (Idy m) := by
    intro m
    -- Pass to `Ioc 0 1`, then split over the dyadic blocks.
    have hIccIoc : (∫⁻ t in Set.Icc (0:ℝ) 1, gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞))
        = ∫⁻ t in Set.Ioc (0:ℝ) 1, gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞) :=
      setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
    rw [hIccIoc, ← hcover m]
    -- Sum over the disjoint dyadic `Ioc`s.
    have hdisj : (Finset.range (2 ^ m) : Set ℕ).PairwiseDisjoint
        (fun i => Set.Ioc (Idy m i) (Idy m (i + 1))) :=
      ((hIdymono m).pairwise_disjoint_on_Ioc_succ).set_pairwise _
    rw [lintegral_biUnion_finset hdisj (fun i _ => measurableSet_Ioc)]
    rw [hpartSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    -- On each block, `gdy m = Gstep m i` a.e. (it agrees on the open interval).
    have hii : Idy m i ≤ Idy m (i + 1) := hIdymono m (Nat.le_succ i)
    have hi0 : (0:ℝ) ≤ Idy m i := (hIdymem m i (le_of_lt hi)).1
    have hi1 : Idy m (i + 1) ≤ 1 := (hIdymem m (i + 1) hi).2
    have hOooOc : (Set.Ioo (Idy m i) (Idy m (i + 1)) : Set ℝ)
        =ᵐ[volume] Set.Ioc (Idy m i) (Idy m (i + 1)) :=
      (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))
    have hgblock : ∀ t ∈ Set.Ioo (Idy m i) (Idy m (i + 1)),
        gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞) = Gstep m (i : ℤ) * (‖deriv δlim t‖₊ : ℝ≥0∞) := by
      intro t ht
      rw [hgdy_block m i hi t ht]
    -- Replace `Ioc` integral by `Ioo` integral and pull out the constant `Gstep m i`.
    have hstepIoc : (∫⁻ t in Set.Ioc (Idy m i) (Idy m (i + 1)),
          gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞))
        = ∫⁻ t in Set.Ioo (Idy m i) (Idy m (i + 1)),
          Gstep m (i : ℤ) * (‖deriv δlim t‖₊ : ℝ≥0∞) := by
      rw [setLIntegral_congr hOooOc.symm]
      apply setLIntegral_congr_fun measurableSet_Ioo
      exact fun t ht => hgblock t ht
    rw [hstepIoc, lintegral_const_mul _ (hmeasSpeed δlim)]
    -- The `Ioo` speed integral equals the `Icc` arc length.
    have hspeedIoo : (∫⁻ t in Set.Ioo (Idy m i) (Idy m (i + 1)), (‖deriv δlim t‖₊ : ℝ≥0∞))
        = eVariationOn δlim (Set.Icc (Idy m i) (Idy m (i + 1))) := by
      rw [hevSub hδlimac _ _ hi0 hii hi1]
      exact setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))
    rw [hspeedIoo, hGstep_eq m i]
  -- **(C-mono) the step density is monotone in `m` (nested dyadic blocks).**
  have hblock_mem : ∀ m (t : ℝ),
      t ∈ Set.Icc ((⌊(2 ^ m : ℝ) * t⌋ : ℝ) / 2 ^ m) (((⌊(2 ^ m : ℝ) * t⌋ : ℝ) + 1) / 2 ^ m) := by
    intro m t
    have h2m : (0:ℝ) < 2 ^ m := by positivity
    constructor
    · rw [div_le_iff₀ h2m, mul_comm]; exact Int.floor_le _
    · rw [le_div_iff₀ h2m, mul_comm]; exact le_of_lt (Int.lt_floor_add_one _)
  have hgdymono : ∀ t, Monotone (fun m => gdy m t) := by
    intro t
    apply monotone_nat_of_le_succ
    intro m
    simp only [hgdy, hGstep]
    -- The level-`(m+1)` block is contained in the level-`m` block.
    refine le_iInf₂ ?_
    intro s hs
    have h2m : (0:ℝ) < 2 ^ m := by positivity
    have h2m1 : (0:ℝ) < 2 ^ (m + 1) := by positivity
    have hpow : (2 ^ (m + 1) : ℝ) = 2 * 2 ^ m := by ring
    -- `s` is in the level-`m` block, so the infimum over the level-`m` block dominates.
    have hsmem : s ∈ Set.Icc ((⌊(2 ^ m : ℝ) * t⌋ : ℝ) / 2 ^ m)
        (((⌊(2 ^ m : ℝ) * t⌋ : ℝ) + 1) / 2 ^ m) := by
      set a : ℤ := ⌊(2 ^ m : ℝ) * t⌋ with ha
      set b : ℤ := ⌊(2 ^ (m + 1) : ℝ) * t⌋ with hb
      have hfloora : (a : ℝ) ≤ (2 ^ m : ℝ) * t := Int.floor_le _
      have hfloora' : (2 ^ m : ℝ) * t < (a : ℝ) + 1 := Int.lt_floor_add_one _
      have hfloorb : (b : ℝ) ≤ (2 ^ (m + 1) : ℝ) * t := Int.floor_le _
      have hfloorb' : (2 ^ (m + 1) : ℝ) * t < (b : ℝ) + 1 := Int.lt_floor_add_one _
      have hb_ge : (2 * a : ℝ) ≤ (b : ℝ) := by
        have hle : ((2 * a : ℤ) : ℝ) ≤ (2 ^ (m + 1) : ℝ) * t := by
          push_cast; rw [hpow]; nlinarith [hfloora]
        have hZ : (2 * a : ℤ) ≤ b := by
          rw [hb]; exact Int.le_floor.mpr hle
        have : ((2 * a : ℤ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hZ
        push_cast at this; linarith [this]
      have hb_lt : (b : ℝ) ≤ 2 * a + 1 := by
        have hlt : (2 ^ (m + 1) : ℝ) * t < 2 * a + 2 := by rw [hpow]; nlinarith [hfloora']
        have : (b : ℤ) ≤ 2 * a + 1 := by
          have hb2 : (b : ℝ) < 2 * a + 2 := lt_of_le_of_lt hfloorb hlt
          have : (b : ℤ) < 2 * a + 2 := by exact_mod_cast hb2
          omega
        exact_mod_cast this
      constructor
      · refine le_trans ?_ hs.1
        rw [div_le_div_iff₀ h2m h2m1, hpow]
        nlinarith [hb_ge, h2m]
      · refine le_trans hs.2 ?_
        rw [div_le_div_iff₀ h2m1 h2m, hpow]
        nlinarith [hb_lt, h2m]
    exact iInf₂_le s hsmem
  -- **(C-sup) the step density converges up to `ρ ∘ δlim` on the open interval.**
  have hρδ_lsc : LowerSemicontinuous (fun t => ρ (δlim t)) := hρ.comp hδlimcont
  have hgdysup : ∀ t ∈ Set.Ioo (0:ℝ) 1, ⨆ m, gdy m t = ρ (δlim t) := by
    intro t ht
    apply le_antisymm
    · -- Each `gdy m t ≤ ρ (δlim t)` since `t` lies in its own block.
      apply iSup_le
      intro m
      simp only [hgdy, hGstep]
      exact iInf₂_le t (hblock_mem m t)
    · -- `ρ (δlim t) ≤ ⨆ gdy m t` via lower semicontinuity.
      refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
      -- `y < ρ (δlim t)`; find `m` with `y ≤ gdy m t ≤ ⨆`.
      have hev : ∀ᶠ x' in 𝓝 t, y < ρ (δlim x') := hρδ_lsc t y hy
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      -- For large `m`, the block lies in the `ε`-ball around `t`.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 : ℝ) / 2 ^ m < ε := by
        obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1:ℝ) < 2)
        refine ⟨m, ?_⟩
        rw [div_lt_iff₀ hε, mul_comm] at hm
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hm, hε]
      have h2m : (0:ℝ) < 2 ^ m := by positivity
      have hblocklt : ∀ s ∈ Set.Icc ((⌊(2 ^ m : ℝ) * t⌋ : ℝ) / 2 ^ m)
          ((⌊(2 ^ m : ℝ) * t⌋ + 1) / 2 ^ m), y < ρ (δlim s) := by
        intro s hs
        apply hball
        rw [Real.dist_eq]
        have hlo : (⌊(2 ^ m : ℝ) * t⌋ : ℝ) / 2 ^ m ≥ t - 1 / 2 ^ m := by
          have h2 := Int.lt_floor_add_one ((2 ^ m : ℝ) * t)
          rw [ge_iff_le, sub_le_iff_le_add, ← add_div, le_div_iff₀ h2m]
          nlinarith [h2]
        have hhi : (⌊(2 ^ m : ℝ) * t⌋ + 1) / 2 ^ m ≤ t + 1 / 2 ^ m := by
          have hfl := Int.floor_le ((2 ^ m : ℝ) * t)
          rw [div_le_iff₀ h2m, add_mul, div_mul_cancel₀ _ (ne_of_gt h2m)]
          nlinarith [hfl]
        have hs1 : t - 1 / 2 ^ m ≤ s := le_trans hlo hs.1
        have hs2 : s ≤ t + 1 / 2 ^ m := le_trans hs.2 hhi
        rw [abs_lt]
        constructor <;> nlinarith [hs1, hs2, hm]
      -- Then `y ≤ gdy m t ≤ ⨆`.
      have hyle : y ≤ gdy m t := by
        simp only [hgdy, hGstep]
        exact le_iInf₂ (fun s hs => le_of_lt (hblocklt s hs))
      exact le_trans hyle (le_iSup (fun m => gdy m t) m)
  -- **(C) the line integral along `δlim` equals the supremum of dyadic partition sums.**
  have pillarC : arcLengthLineIntegral ρ δlim ≤ ⨆ m, partSum δlim (2 ^ m) (Idy m) := by
    -- Rewrite the integrand pointwise (a.e.) as a supremum and apply monotone convergence.
    have hcongr : arcLengthLineIntegral ρ δlim
        = ∫⁻ t in Set.Icc (0:ℝ) 1, ⨆ m, gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞) := by
      rw [arcLengthLineIntegral]
      -- a.e. on `Icc 0 1` (in fact on `Ioo 0 1`), the integrands agree.
      have hae : (Set.Ioo (0:ℝ) 1) =ᵐ[volume] Set.Icc 0 1 := MeasureTheory.Ioo_ae_eq_Icc
      apply setLIntegral_congr_fun_ae measurableSet_Icc
      filter_upwards [hae.mem_iff] with t htiff
      intro htIcc
      have htIoo : t ∈ Set.Ioo (0:ℝ) 1 := htiff.mpr htIcc
      rw [← hgdysup t htIoo, ENNReal.iSup_mul]
    rw [hcongr]
    -- Monotone convergence: `∫⁻ ⨆ = ⨆ ∫⁻`.
    have hfmeas : ∀ m, AEMeasurable (fun t => gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞))
        (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      fun m => ((hgdy_meas m).mul (hmeasSpeed δlim)).aemeasurable
    have hfmono : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
        Monotone fun m => gdy m t * (‖deriv δlim t‖₊ : ℝ≥0∞) := by
      filter_upwards with t
      intro p q hpq
      exact mul_le_mul' (hgdymono t hpq) le_rfl
    rw [lintegral_iSup' hfmeas hfmono]
    -- Each level is the partition sum.
    apply iSup_le
    intro m
    rw [hpartSumInt m]
    exact le_iSup (fun m => partSum δlim (2 ^ m) (Idy m)) m
  -- ===========================================================================================
  -- **Assembly: chain pillars C, B, A.**
  -- ===========================================================================================
  refine le_trans pillarC (iSup_le ?_)
  intro m
  -- Dyadic partition data is valid.
  have hImono : Monotone (Idy m) := hIdymono m
  have hImem : ∀ i, i ≤ 2 ^ m → Idy m i ∈ Set.Icc (0:ℝ) 1 := hIdymem m
  -- Pillar B then pillar A under the `liminf`.
  refine le_trans (pillarB (2 ^ m) (Idy m) hImono hImem) ?_
  refine liminf_le_liminf ?_
  filter_upwards with k
  exact pillarA (hδcont k) (hδac k) (2 ^ m) (Idy m) hImono hImem

/-- **Absolutely-continuous approximation in the image families (uniformly quasiconformal case).**
Let `fₙ → g` locally uniformly with `g` a homeomorphism and the `fₙ` uniformly `K`-quasiconformal.
Every absolutely continuous curve `δlim` in the `g`-image family of `Q` is the uniform limit, along
a strictly increasing tail `k ↦ fₙ (φ k)` with `n ≤ φ 0`, of absolutely continuous curves `δ k`
lying in the corresponding `fₙ (φ k)`-image families.

Uniform `K`-quasiconformality is essential. For bare homeomorphisms the statement is false: a
uniformly small homeomorphic crumpling of the square into an Osgood-type wild disk leaves no
rectifiable — hence no absolutely continuous — left-to-right crossing near the target curve, so no
such approximants exist. Under uniform `K`-quasiconformality the `fₙ` are uniformly quasisymmetric
(equicontinuous with equicontinuous inverses) and the image disks `fₙ '' Q.image` carry a uniform
quasiconformal structure in which nearby interior points are joined by short rectifiable arcs; the
approximants are then built by quasiconformal transport of a polygonal curve in the model square. -/
theorem exists_imageCurveFamily_approx {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K : ℝ}
    (hfK : ∀ n, IsQCGeometric (fₙ n) K)
    (hconv : TendstoLocallyUniformly fₙ g atTop) (hg : IsHomeomorph g) (Q : Quadrilateral)
    {δlim : ℝ → ℂ} (hδlim : δlim ∈ Q.imageCurveFamily g) (n : ℕ) :
    ∃ (φ : ℕ → ℕ) (δ : ℕ → ℝ → ℂ), StrictMono φ ∧ n ≤ φ 0 ∧
      (∀ k, δ k ∈ Q.imageCurveFamily (fₙ (φ k))) ∧
      TendstoUniformlyOn δ δlim atTop (Set.Icc (0 : ℝ) 1) := by
  sorry

/-- **Weak-`L²` limit density for the image families (core reduction).**
Under locally uniform convergence `fₙ → g` with `g` a homeomorphism, there is, for every tail
index `n`, a measurable density `ρlim : ℂ → ℝ≥0∞` that is admissible for the `g`-image family of `Q`
and whose energy is bounded by the infimum of the tail moduli:

`∫⁻ z, (ρlim z) ^ 2 ≤ ⨅ i ≥ n, curveModulus (Q.imageCurveFamily (fₙ i))`.

This is the heart of Väisälä's argument, valid for uniformly `K`-quasiconformal `fₙ`.  For each
`i ≥ n` extract a near-optimal `ℝ≥0∞` density admissible for `Q.imageCurveFamily (fₙ i)` with energy
within `1/(i+1)` of the modulus (`iInf_lt_iff`); restrict to a subsequence realizing the infimal
tail energy.  Bridge the finite-energy `ℝ≥0∞` densities to genuine real `L²(ℂ)` functions, apply
`exists_weak_subseq_of_bounded` to get a weak limit and `mem_closure_convexHull_of_weak_limit`
(Mazur) to obtain admissible convex combinations converging a.e. to a limit density `ρlim` of energy
`≤` the infimal tail energy.  Admissibility of `ρlim` for the `g`-image family follows because each
absolutely continuous curve in the `g`-image family is approximated, via
`exists_imageCurveFamily_approx` (which needs the uniform quasiconformality), by absolutely
continuous curves in the `fₙ`-image families along which the line integral is lower semicontinuous
(`arcLengthLineIntegral_le_liminf_of_tendstoUniformly`, applied to the lower-semicontinuous
envelope of `ρlim`). -/
theorem exists_admissibleDensity_imageCurveFamily_limit {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K : ℝ}
    (hfK : ∀ n, IsQCGeometric (fₙ n) K)
    (hconv : TendstoLocallyUniformly fₙ g atTop) (hg : IsHomeomorph g) (Q : Quadrilateral)
    (n : ℕ) :
    ∃ ρlim : ℂ → ℝ≥0∞, IsAdmissibleDensity ρlim (Q.imageCurveFamily g) ∧
      (∫⁻ z, (ρlim z) ^ 2) ≤ ⨅ i ≥ n, curveModulus (Q.imageCurveFamily (fₙ i)) := by
  sorry

end Quadrilateral

/-- **Lower semicontinuity of the image-family modulus.** Under locally uniform convergence
`fₙ → g` with `g` a homeomorphism, the modulus of the image connecting family of a quadrilateral is
at most the lower limit of the moduli of the approximating image families:

`curveModulus (Q.imageCurveFamily g) ≤ liminf (fun n => curveModulus (Q.imageCurveFamily (fₙ n)))`.

This is the conformal-modulus form of Väisälä's lower-semicontinuity theorem, valid for uniformly
`K`-quasiconformal `fₙ`. The hypothesis is essential: for bare homeomorphisms it is false (a
uniformly small homeomorphic crumpling collapses the modulus, `curveModulus (fₙ family) → 0` while
`curveModulus (g family) > 0`). Given the core reduction
`exists_admissibleDensity_imageCurveFamily_limit` — a density admissible for the limit family with
energy below each infimal tail modulus — the bound is pure `ℝ≥0∞` order theory:
`curveModulus (g family) ≤ energy ≤ ⨅ i ≥ n, curveModulus (fₙ i family)` for every `n`, and the
right-hand side suprema over `n` to `liminf`. -/
theorem curveModulus_imageCurveFamily_lsc {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K : ℝ}
    (hfK : ∀ n, IsQCGeometric (fₙ n) K)
    (hconv : TendstoLocallyUniformly fₙ g atTop) (hg : IsHomeomorph g) (Q : Quadrilateral) :
    curveModulus (Q.imageCurveFamily g)
      ≤ Filter.liminf (fun n => curveModulus (Q.imageCurveFamily (fₙ n))) atTop := by
  -- `liminf` of an `ℝ≥0∞` sequence is the supremum over `n` of the infimal tails.
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  -- It suffices to bound the left side by each infimal tail `⨅ i ≥ n, curveModulus (fₙ i family)`.
  refine le_iSup_of_le 0 ?_
  -- For the tail starting at `n = 0`, pick the admissible limit density and bound its energy.
  obtain ⟨ρlim, hρlimadm, hρlimenergy⟩ :=
    Quadrilateral.exists_admissibleDensity_imageCurveFamily_limit hfK hconv hg Q 0
  calc curveModulus (Q.imageCurveFamily g)
      ≤ ∫⁻ z, (ρlim z) ^ 2 := iInf₂_le ρlim hρlimadm
    _ ≤ ⨅ i ≥ 0, curveModulus (Q.imageCurveFamily (fₙ i)) := hρlimenergy

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The `L∞` representation of functionals on `L¹`

Over a finite measure, every continuous linear functional on `L¹` is integration against
an essentially bounded density: the functional's values on indicators form a complex
measure absolutely continuous with respect to the base, its Radon–Nikodym derivative is
bounded pointwise by the operator norm, and integration against it recovers the
functional first on simple functions and then on all of `L¹` by density. This is the
endpoint `p = 1` of the `Lᵖ` duality, which Mathlib provides only for `1 < p < ∞`.

* `ae_norm_le_of_forall_setIntegral_norm_le` — the almost-everywhere bound from bounds on
  all set averages.
* `exists_setIntegral_rep` — the density representing the functional on indicators.
* `exists_linfty_representative` — the full representation with the pointwise bound.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {α : Type*} [MeasurableSpace α]

/-- **The almost-everywhere bound from set averages**: an integrable function whose
integral over every measurable set is bounded in norm by `C` times the measure of the set
is bounded by `C` almost everywhere. -/
theorem ae_norm_le_of_forall_setIntegral_norm_le (μ : Measure α) [IsFiniteMeasure μ]
    {ν : α → ℂ} (hmeas : Measurable ν) (hint : Integrable ν μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ E : Set α, MeasurableSet E → ‖∫ x in E, ν x ∂μ‖ ≤ C * (μ E).toReal) :
    ∀ᵐ x ∂μ, ‖ν x‖ ≤ C := by
  have _ := hmeas
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have key : ∀ u : ℂ, ∀ᵐ x ∂μ, ((starRingEnd ℂ) u * ν x).re ≤ ‖u‖ * C := by
    intro u
    have hint' : Integrable (fun x => ((starRingEnd ℂ) u * ν x).re) μ := by
      have h1 := (hint.const_mul ((starRingEnd ℂ) u)).re
      simpa only [RCLike.re_eq_complex_re] using h1
    have hsub : Integrable (fun x => ‖u‖ * C - ((starRingEnd ℂ) u * ν x).re) μ :=
      (integrable_const _).sub hint'
    have hle : ∀ s : Set α, MeasurableSet s → μ s < ∞ →
        0 ≤ ∫ x in s, (‖u‖ * C - ((starRingEnd ℂ) u * ν x).re) ∂μ := by
      intro s hs hμs
      rw [integral_sub (integrable_const (‖u‖ * C)).integrableOn hint'.integrableOn,
        setIntegral_const, sub_nonneg, smul_eq_mul]
      have h2 : ∫ x in s, ((starRingEnd ℂ) u * ν x).re ∂μ
          = ((starRingEnd ℂ) u * ∫ x in s, ν x ∂μ).re := by
        rw [← RCLike.re_eq_complex_re]
        rw [integral_re (hint.const_mul _).integrableOn, integral_const_mul]
        rfl
      rw [h2]
      calc ((starRingEnd ℂ) u * ∫ x in s, ν x ∂μ).re
          ≤ ‖(starRingEnd ℂ) u * ∫ x in s, ν x ∂μ‖ := Complex.re_le_norm _
        _ = ‖u‖ * ‖∫ x in s, ν x ∂μ‖ := by rw [norm_mul, RCLike.norm_conj]
        _ ≤ ‖u‖ * (C * (μ s).toReal) := mul_le_mul_of_nonneg_left (h s hs) (norm_nonneg u)
        _ = μ.real s * (‖u‖ * C) := by rw [measureReal_def]; ring
    have h0 := ae_nonneg_of_forall_setIntegral_nonneg hsub hle
    filter_upwards [h0] with x hx
    exact sub_nonneg.mp hx
  have hD : ∀ᵐ x ∂μ, ∀ u ∈ D, ((starRingEnd ℂ) u * ν x).re ≤ ‖u‖ * C :=
    (ae_ball_iff hDc).mpr fun u _ => key u
  filter_upwards [hD] with x hx
  by_contra hgt
  push Not at hgt
  have hz : ν x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hgt
    exact absurd hgt (not_lt.mpr hC)
  have hnz : ‖ν x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  set u₀ : ℂ := ν x / (‖ν x‖ : ℂ) with hu₀
  obtain ⟨w, hwD, hwlim⟩ := mem_closure_iff_seq_limit.mp (hDd u₀)
  have hconj : Filter.Tendsto (fun n => (starRingEnd ℂ) (w n) * ν x) Filter.atTop
      (nhds ((starRingEnd ℂ) u₀ * ν x)) :=
    ((Complex.continuous_conj.tendsto u₀).comp hwlim).mul_const (ν x)
  have h1 : Filter.Tendsto (fun n => ((starRingEnd ℂ) (w n) * ν x).re) Filter.atTop
      (nhds (((starRingEnd ℂ) u₀ * ν x).re)) :=
    (Complex.continuous_re.tendsto _).comp hconj
  have h2 : Filter.Tendsto (fun n => ‖w n‖ * C) Filter.atTop (nhds (‖u₀‖ * C)) :=
    hwlim.norm.mul_const C
  have hle : (((starRingEnd ℂ) u₀ * ν x).re) ≤ ‖u₀‖ * C :=
    le_of_tendsto_of_tendsto' h1 h2 fun n => hx (w n) (hwD n)
  have hcu : (starRingEnd ℂ) u₀ * ν x = ((‖ν x‖ : ℝ) : ℂ) := by
    rw [hu₀, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div,
      mul_comm ((starRingEnd ℂ) (ν x)) (ν x), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [show ((‖ν x‖ ^ 2 : ℝ) : ℂ) = ((‖ν x‖ : ℝ) : ℂ) ^ 2 by push_cast; ring]
    rw [sq, mul_div_assoc, div_self (Complex.ofReal_ne_zero.mpr hnz), mul_one]
  have hn₀ : ‖u₀‖ = 1 := by
    rw [hu₀, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (ν x)), div_self hnz]
  rw [hcu, hn₀, one_mul, Complex.ofReal_re] at hle
  exact absurd hle (not_le.mpr hgt)

/-- **The representing density on indicators**: a continuous linear functional on `L¹` of
a finite measure is, on indicator classes, integration against a fixed integrable
density. -/
theorem exists_setIntegral_rep (μ : Measure α) [IsFiniteMeasure μ]
    (Λ : Lp ℂ 1 μ →L[ℂ] ℂ) :
    ∃ ν : α → ℂ, Measurable ν ∧ Integrable ν μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E),
        (∫ x in E, ν x ∂μ) = Λ (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ)) := by
  classical
  have hcongr : ∀ {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t), s = t →
      indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℂ)
        = indicatorConstLp 1 ht (measure_ne_top μ t) (1 : ℂ) := by
    rintro s t hs ht rfl; rfl
  have hnorm : ∀ (s : Set α) (hs : MeasurableSet s),
      ‖indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℂ)‖ = (μ s).toReal := by
    intro s hs
    rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
    simp [measureReal_def]
  obtain ⟨c, hc⟩ : ∃ c : ComplexMeasure α, ∀ (E : Set α) (hE : MeasurableSet E),
      c E = Λ (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ)) := by
    refine ⟨⟨fun E => if h : MeasurableSet E
        then Λ (indicatorConstLp 1 h (measure_ne_top μ E) (1 : ℂ)) else 0, ?_, ?_, ?_⟩,
      fun E hE => dif_pos hE⟩
    · dsimp only
      rw [dif_pos MeasurableSet.empty, indicatorConstLp_empty, map_zero]
    · exact fun i hi => dif_neg hi
    · intro f hf hd
      have hIU : HasSum
          (fun i => indicatorConstLp 1 (hf i) (measure_ne_top μ (f i)) (1 : ℂ))
          (indicatorConstLp 1 (MeasurableSet.iUnion hf)
            (measure_ne_top μ (⋃ i, f i)) (1 : ℂ)) := by
        set A : ℕ → Set α := fun N => ⋃ i ∈ Finset.range N, f i with hA
        have hAm : ∀ N, MeasurableSet (A N) := fun N =>
          (Finset.range N).measurableSet_biUnion fun i _ => hf i
        have hAsub : ∀ N, A N ⊆ ⋃ i, f i := fun N =>
          Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
        have hpartial : ∀ N,
            (∑ i ∈ Finset.range N,
              indicatorConstLp 1 (hf i) (measure_ne_top μ (f i)) (1 : ℂ))
            = indicatorConstLp 1 (hAm N) (measure_ne_top μ (A N)) (1 : ℂ) := by
          intro N
          induction N with
          | zero =>
            rw [Finset.sum_range_zero]
            have hA0 : (∅ : Set α) = A 0 := by simp [hA]
            exact ((hcongr (hAm 0) MeasurableSet.empty hA0.symm).trans
              indicatorConstLp_empty).symm
          | succ N ih =>
            rw [Finset.sum_range_succ, ih]
            have hdisj : Disjoint (A N) (f N) := by
              simp only [hA, Set.disjoint_iUnion_left]
              intro i hi
              exact hd (Finset.mem_range.mp hi).ne
            have hun : A N ∪ f N = A (N + 1) := by
              simp only [hA, Finset.range_add_one, Finset.set_biUnion_insert]
              exact Set.union_comm _ _
            exact ((indicatorConstLp_disjoint_union (hAm N) (hf N) (measure_ne_top _ _)
              (measure_ne_top _ _) hdisj (1 : ℂ)).symm).trans
              (hcongr ((hAm N).union (hf N)) (hAm (N + 1)) hun)
        have hsummable : Summable
            (fun i => indicatorConstLp 1 (hf i) (measure_ne_top μ (f i)) (1 : ℂ)) := by
          refine Summable.of_norm ?_
          have hs : Summable fun i => (μ (f i)).toReal := by
            refine ENNReal.summable_toReal ?_
            rw [← measure_iUnion hd hf]
            exact measure_ne_top μ _
          exact hs.congr fun i => (hnorm _ (hf i)).symm
        have htail : Filter.Tendsto (fun N => μ ((⋃ i, f i) \ A N))
            Filter.atTop (nhds 0) := by
          have hsubset : ∀ N, (⋃ i, f i) \ A N ⊆ ⋃ j, f (j + N) := by
            intro N x hx
            obtain ⟨hxU, hxA⟩ := hx
            obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
            have hiN : N ≤ i := by
              by_contra hlt
              push Not at hlt
              exact hxA (Set.mem_biUnion (Finset.mem_range.mpr hlt) hxi)
            exact Set.mem_iUnion.mpr ⟨i - N, by rwa [Nat.sub_add_cancel hiN]⟩
          have hbound : ∀ N, μ ((⋃ i, f i) \ A N) ≤ ∑' j, μ (f (j + N)) := fun N =>
            (measure_mono (hsubset N)).trans (measure_iUnion_le _)
          have hzero : Filter.Tendsto (fun N => ∑' j, μ (f (j + N)))
              Filter.atTop (nhds 0) := by
            refine ENNReal.tendsto_sum_nat_add (fun n => μ (f n)) ?_
            rw [← measure_iUnion hd hf]
            exact measure_ne_top μ _
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
            (fun N => zero_le _) hbound
        have hps : Filter.Tendsto
            (fun N => ∑ i ∈ Finset.range N,
              indicatorConstLp 1 (hf i) (measure_ne_top μ (f i)) (1 : ℂ))
            Filter.atTop (nhds (indicatorConstLp 1 (MeasurableSet.iUnion hf)
              (measure_ne_top μ (⋃ i, f i)) (1 : ℂ))) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          have heq : ∀ N, ‖(∑ i ∈ Finset.range N,
              indicatorConstLp 1 (hf i) (measure_ne_top μ (f i)) (1 : ℂ))
              - indicatorConstLp 1 (MeasurableSet.iUnion hf)
                (measure_ne_top μ (⋃ i, f i)) (1 : ℂ)‖
              = (μ ((⋃ i, f i) \ A N)).toReal := by
            intro N
            have hDm : MeasurableSet ((⋃ i, f i) \ A N) :=
              (MeasurableSet.iUnion hf).diff (hAm N)
            have hsplit : indicatorConstLp 1 (MeasurableSet.iUnion hf)
                (measure_ne_top μ (⋃ i, f i)) (1 : ℂ)
                = indicatorConstLp 1 (hAm N) (measure_ne_top μ (A N)) (1 : ℂ)
                  + indicatorConstLp 1 hDm (measure_ne_top μ ((⋃ i, f i) \ A N)) (1 : ℂ) :=
              (hcongr (MeasurableSet.iUnion hf) ((hAm N).union hDm)
                (Set.union_diff_cancel (hAsub N)).symm).trans
                (indicatorConstLp_disjoint_union (hAm N) hDm (measure_ne_top _ _)
                  (measure_ne_top _ _) Set.disjoint_sdiff_right (1 : ℂ))
            rw [hpartial N, hsplit, sub_add_cancel_left, norm_neg]
            exact hnorm _ hDm
          have htoReal : Filter.Tendsto (fun N => (μ ((⋃ i, f i) \ A N)).toReal)
              Filter.atTop (nhds 0) := by
            have h0 : Filter.Tendsto ENNReal.toReal (nhds 0) (nhds 0) := by
              simpa using ENNReal.tendsto_toReal (a := 0) (by simp)
            exact h0.comp htail
          exact htoReal.congr fun N => (heq N).symm
        have h1 := hsummable.hasSum.tendsto_sum_nat
        have h2 := tendsto_nhds_unique h1 hps
        rw [← h2]
        exact hsummable.hasSum
      have hpos : ∀ i, (if h : MeasurableSet (f i)
          then Λ (indicatorConstLp 1 h (measure_ne_top μ (f i)) (1 : ℂ)) else 0)
          = Λ (indicatorConstLp 1 (hf i) (measure_ne_top μ (f i)) (1 : ℂ)) :=
        fun i => dif_pos (hf i)
      simp only [hpos, dif_pos (MeasurableSet.iUnion hf)]
      exact hIU.mapL Λ
  have hzero : ∀ (E : Set α), MeasurableSet E → μ E = 0 → c E = 0 := by
    intro E hE hμE
    rw [hc E hE]
    have h0 : indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ) = 0 := by
      refine Lp.ext ?_
      have hne : ∀ᵐ x ∂μ, x ∉ E := measure_eq_zero_iff_ae_notMem.mp hμE
      filter_upwards [indicatorConstLp_coeFn (μ := μ) (hs := hE)
        (hμs := measure_ne_top μ E) (c := (1 : ℂ)), hne,
        Lp.coeFn_zero (E := ℂ) (p := 1) (μ := μ)] with x h1 h2 h3
      rw [h1, Set.indicator_of_notMem h2]
      exact h3.symm
    rw [h0, map_zero]
  have hre_ac : ComplexMeasure.re c ≪ᵥ μ.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hμE => ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hμE
    have hrE : ComplexMeasure.re c E = (c E).re := rfl
    rw [hrE, hzero E hE hμE, Complex.zero_re]
  have him_ac : ComplexMeasure.im c ≪ᵥ μ.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hμE => ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hμE
    have hiE : ComplexMeasure.im c E = (c E).im := rfl
    rw [hiE, hzero E hE hμE, Complex.zero_im]
  have hre := SignedMeasure.withDensityᵥ_rnDeriv_eq (ComplexMeasure.re c) μ hre_ac
  have him := SignedMeasure.withDensityᵥ_rnDeriv_eq (ComplexMeasure.im c) μ him_ac
  refine ⟨ComplexMeasure.rnDeriv c μ, ?_, ComplexMeasure.integrable_rnDeriv c μ, ?_⟩
  · have h1 : Measurable fun x => SignedMeasure.rnDeriv (ComplexMeasure.re c) μ x :=
      SignedMeasure.measurable_rnDeriv _ _
    have h2 : Measurable fun x => SignedMeasure.rnDeriv (ComplexMeasure.im c) μ x :=
      SignedMeasure.measurable_rnDeriv _ _
    have heq : ComplexMeasure.rnDeriv c μ = fun x =>
        ((SignedMeasure.rnDeriv (ComplexMeasure.re c) μ x : ℝ) : ℂ)
          + ((SignedMeasure.rnDeriv (ComplexMeasure.im c) μ x : ℝ) : ℂ) * Complex.I := by
      funext x
      exact Complex.mk_eq_add_mul_I _ _
    rw [heq]
    exact (Complex.measurable_ofReal.comp h1).add
      ((Complex.measurable_ofReal.comp h2).mul_const Complex.I)
  · intro E hE
    rw [← hc E hE]
    have hint : Integrable (ComplexMeasure.rnDeriv c μ) μ :=
      ComplexMeasure.integrable_rnDeriv c μ
    apply Complex.ext
    · calc (∫ x in E, ComplexMeasure.rnDeriv c μ x ∂μ).re
          = ∫ x in E, SignedMeasure.rnDeriv (ComplexMeasure.re c) μ x ∂μ := by
            exact (integral_re (hint.integrableOn (s := E))).symm
        _ = μ.withDensityᵥ (SignedMeasure.rnDeriv (ComplexMeasure.re c) μ) E :=
            (withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hE).symm
        _ = ComplexMeasure.re c E := by rw [hre]
        _ = (c E).re := rfl
    · calc (∫ x in E, ComplexMeasure.rnDeriv c μ x ∂μ).im
          = ∫ x in E, SignedMeasure.rnDeriv (ComplexMeasure.im c) μ x ∂μ := by
            exact (integral_im (hint.integrableOn (s := E))).symm
        _ = μ.withDensityᵥ (SignedMeasure.rnDeriv (ComplexMeasure.im c) μ) E :=
            (withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hE).symm
        _ = ComplexMeasure.im c E := by rw [him]
        _ = (c E).im := rfl

/-- **`L∞` representation of `L¹` functionals**: over a finite measure, every continuous
linear functional on `L¹` is integration against a measurable density bounded everywhere
by the operator norm. -/
theorem exists_linfty_representative (μ : Measure α) [IsFiniteMeasure μ]
    (Λ : Lp ℂ 1 μ →L[ℂ] ℂ) :
    ∃ ν : α → ℂ, Measurable ν ∧ (∀ x, ‖ν x‖ ≤ ‖Λ‖) ∧
      ∀ f : Lp ℂ 1 μ, Λ f = ∫ x, ν x * f x ∂μ := by
  obtain ⟨ν₀, hmeas₀, hint₀, hrep₀⟩ := exists_setIntegral_rep μ Λ
  have hbound : ∀ E : Set α, MeasurableSet E → ‖∫ x in E, ν₀ x ∂μ‖ ≤ ‖Λ‖ * (μ E).toReal := by
    intro E hE
    rw [hrep₀ E hE]
    calc ‖Λ (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ))‖
        ≤ ‖Λ‖ * ‖indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ)‖ := Λ.le_opNorm _
      _ = ‖Λ‖ * (μ E).toReal := by
          rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
          simp [measureReal_def]
  have hae : ∀ᵐ x ∂μ, ‖ν₀ x‖ ≤ ‖Λ‖ :=
    ae_norm_le_of_forall_setIntegral_norm_le μ hmeas₀ hint₀ (norm_nonneg Λ) hbound
  have hSm : MeasurableSet {y | ‖ν₀ y‖ ≤ ‖Λ‖} := measurableSet_le hmeas₀.norm measurable_const
  set ν : α → ℂ := ({y | ‖ν₀ y‖ ≤ ‖Λ‖}).indicator ν₀ with hν
  have hνmeas : Measurable ν := hmeas₀.indicator hSm
  have hνbdd : ∀ x, ‖ν x‖ ≤ ‖Λ‖ := by
    intro x
    rw [hν]
    by_cases hx : x ∈ {y | ‖ν₀ y‖ ≤ ‖Λ‖}
    · rw [Set.indicator_of_mem hx]
      exact hx
    · rw [Set.indicator_of_notMem hx]
      simp
  have hνae : ν =ᵐ[μ] ν₀ := by
    filter_upwards [hae] with x hx
    rw [hν]
    exact Set.indicator_of_mem (show x ∈ {y | ‖ν₀ y‖ ≤ ‖Λ‖} from hx) ν₀
  have hrep : ∀ (E : Set α) (hE : MeasurableSet E),
      (∫ x in E, ν x ∂μ) = Λ (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ)) := by
    intro E hE
    rw [← hrep₀ E hE]
    exact setIntegral_congr_ae hE (hνae.mono fun x hx _ => hx)
  refine ⟨ν, hνmeas, hνbdd, ?_⟩
  have hcont : Continuous fun f : Lp ℂ 1 μ => ∫ x, ν x * f x ∂μ := by
    have hlip : LipschitzWith ‖Λ‖₊ fun f : Lp ℂ 1 μ => ∫ x, ν x * f x ∂μ := by
      refine LipschitzWith.of_dist_le_mul fun f g => ?_
      have hif : Integrable (fun x => ν x * f x) μ :=
        (L1.integrable_coeFn f).bdd_mul hνmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall hνbdd)
      have hig : Integrable (fun x => ν x * g x) μ :=
        (L1.integrable_coeFn g).bdd_mul hνmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall hνbdd)
      have hsub : Integrable (fun x => f x - g x) μ :=
        (L1.integrable_coeFn f).sub (L1.integrable_coeFn g)
      have hmulsub : Integrable (fun x => ν x * (f x - g x)) μ :=
        hsub.bdd_mul hνmeas.aestronglyMeasurable (Filter.Eventually.of_forall hνbdd)
      rw [dist_eq_norm, dist_eq_norm, coe_nnnorm]
      calc ‖(∫ x, ν x * f x ∂μ) - ∫ x, ν x * g x ∂μ‖
          = ‖∫ x, ν x * (f x - g x) ∂μ‖ := by
            rw [← integral_sub hif hig]
            simp only [mul_sub]
        _ ≤ ∫ x, ‖ν x * (f x - g x)‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖Λ‖ * ‖f x - g x‖ ∂μ := by
            refine integral_mono hmulsub.norm (hsub.norm.const_mul ‖Λ‖) fun x => ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hνbdd x) (norm_nonneg _)
        _ = ‖Λ‖ * ∫ x, ‖f x - g x‖ ∂μ := integral_const_mul ‖Λ‖ _
        _ = ‖Λ‖ * ‖f - g‖ := by
            rw [L1.norm_eq_integral_norm (f - g)]
            congr 1
            refine integral_congr_ae ?_
            filter_upwards [Lp.coeFn_sub f g] with x hx
            rw [hx]
            rfl
    exact hlip.continuous
  refine Lp.induction (E := ℂ) (p := 1) (μ := μ) ENNReal.one_ne_top
    (motive := fun f => Λ f = ∫ x, ν x * f x ∂μ) ?_ ?_ ?_
  · intro d s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    have hsmul : indicatorConstLp 1 hs hμs.ne d
        = d • indicatorConstLp 1 hs hμs.ne (1 : ℂ) := by
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (μ := μ) (hs := hs) (hμs := hμs.ne) (c := d),
        Lp.coeFn_smul d (indicatorConstLp 1 hs hμs.ne (1 : ℂ)),
        indicatorConstLp_coeFn (μ := μ) (hs := hs) (hμs := hμs.ne) (c := (1 : ℂ))]
        with x h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    have hRHS : ∫ x, ν x * (indicatorConstLp 1 hs hμs.ne d) x ∂μ
        = ∫ x in s, ν x * d ∂μ := by
      rw [← integral_indicator hs]
      refine integral_congr_ae ?_
      filter_upwards [indicatorConstLp_coeFn (μ := μ) (hs := hs) (hμs := hμs.ne) (c := d)]
        with x h1
      rw [h1]
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    have hmc : (∫ x in s, ν x * d ∂μ) = (∫ x in s, ν x ∂μ) * d :=
      integral_mul_const d fun y => ν y
    rw [hRHS, hsmul, map_smul, smul_eq_mul, ← hrep s hs, hmc]
    ring
  · intro f g hf hg hdisj hPf hPg
    rw [map_add, hPf, hPg]
    have hif : Integrable (fun x => ν x * (hf.toLp f) x) μ :=
      (L1.integrable_coeFn _).bdd_mul hνmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall hνbdd)
    have hig : Integrable (fun x => ν x * (hg.toLp g) x) μ :=
      (L1.integrable_coeFn _).bdd_mul hνmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall hνbdd)
    rw [← integral_add hif hig]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add (hf.toLp f) (hg.toLp g)] with x h3
    rw [h3]
    simp [mul_add]
  · exact isClosed_eq Λ.continuous hcont

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Symmetry.Invariance

/-!
# Chart slicing, absolute continuity along leaves, and winding preliminaries

Localization of the Sobolev regularity to a chart, absolute continuity of the competitor
along almost every leaf, and the elementary winding-number lemmas of the argument
principle.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Leafwise absolute continuity from per-chart height slicing**: the pinned
hypothesis of `sym_hpath_of_acl`, discharged from absolute continuity of the
quasiconformal image along almost every developed height line of each atlas chart. -/
theorem sym_hacl_of_chart_slicing {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (h : ℂ → ℂ) (A : Atlas (q : ℂ → ℂ))
    (hACL : ∀ j : ℕ, A.active j → ∀ᵐ y : ℝ ∂(volume : Measure ℝ),
      ∀ a b : ℝ,
      (∀ x ∈ Set.uIcc a b,
        (x : ℂ) + (y : ℝ) * Complex.I
          ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) →
      AbsolutelyContinuousOnInterval
        (fun x => h (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j))
          ((x : ℂ) + (y : ℝ) * Complex.I))) a b) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      AbsolutelyContinuousOnInterval (fun s => h (σ (s * T))) 0 1 := by
  classical
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  set P : ℕ → ℝ → Prop := fun j y => ∀ a b : ℝ,
    (∀ x ∈ Set.uIcc a b,
      (x : ℂ) + (y : ℝ) * Complex.I
        ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) →
    AbsolutelyContinuousOnInterval
      (fun x => h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j))
        ((x : ℂ) + (y : ℝ) * Complex.I))) a b with hPdef
  set E : ℕ → Set ℝ := fun j => toMeasurable volume {y : ℝ | ¬ P j y} with hEdef
  have hEnull : ∀ j, A.active j → volume (E j) = 0 := by
    intro j hj
    rw [show E j = toMeasurable volume {y : ℝ | ¬ P j y} from rfl,
      measure_toMeasurable]
    exact ae_iff.mp (hACL j hj)
  set BP : Set ℂ := toMeasurable volume (⋃ j : ℕ,
    {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (2 * A.r j)
      ∧ (A.Φ j z).im ∈ E j}) with hBPdef
  have hBPm : MeasurableSet BP := measurableSet_toMeasurable _ _
  have hBP0 : volume BP = 0 := by
    rw [hBPdef, measure_toMeasurable]
    refine measure_iUnion_null fun j => ?_
    by_cases hj : A.active j
    · exact measure_mono_null
        (t := {z : ℂ | z ∈ Metric.ball (A.c j) (2 * A.r j)
          ∧ (A.Φ j z).im ∈ E j})
        (fun z hz => ⟨hz.2.1, hz.2.2⟩)
        (chartline_heights_null q.measurable A hj (hEnull j hj))
    · exact measure_mono_null (t := (∅ : Set ℂ))
        (fun z hz => (hj hz.1).elim) (measure_empty (μ := volume))
  have hBPsub := subset_toMeasurable volume (⋃ j : ℕ,
    {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (2 * A.r j)
      ∧ (A.Φ j z).im ∈ E j})
  have hsec : ∀ t : ℝ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      z ∈ good (q : ℂ → ℂ) A → A.flow t z ∉ BP := by
    intro t
    rcases lt_trichotomy t 0 with htn | ht0 | htp
    · have hminus : (0 : ℝ) < -t := by linarith
      have hb := flow_preimage_ae q A (mirrorAtlas A)
        (fun z => A.flow (-(-t)) z) hminus
        (fun n z hz => flow_eq_pos_bwd q.holo A hminus hz)
        (fun z hz => good_slegal_bwd q.holo A hminus hz) hBPm hBP0
      simpa only [neg_neg] using hb
    · subst ht0
      have hnotN : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∉ BP := by
        refine ae_iff.mpr ?_
        have hset : {a : ℂ | ¬ a ∉ BP} = BP := by
          ext a
          simp
        rw [hset, Measure.restrict_apply' hUm]
        exact measure_mono_null Set.inter_subset_left hBP0
      filter_upwards [hnotN, q.ae_ne_zero hq0, ae_restrict_mem hUm]
        with z hzN hqz hzU
      intro _ hflowN
      rw [flow_zero A hzU hqz] at hflowN
      exact hzN hflowN
    · exact flow_preimage_ae q A A (fun z => A.flow t z) htp
        (fun n z hz => flow_eq_pos_fwd q.holo A htp hz)
        (fun z hz => good_slegal_fwd q.holo A htp hz) hBPm hBP0
  have havoid : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      ∀ r : ℚ, z ∈ good (q : ℂ → ℂ) A → A.flow (r : ℝ) z ∉ BP :=
    ae_all_iff.mpr fun r => hsec (r : ℝ)
  filter_upwards [havoid] with z hz
  intro hzg T hT σ hσtraj hσev
  have hACfull : AbsolutelyContinuousOnInterval (fun u => h (σ u)) 0 T := by
    refine ac_of_local_windows hT fun v hv => ?_
    have hreg := traj_regular hσtraj hv
    have hact : A.active (A.sel (σ v)) := (A.sel_spec hreg.1 hreg.2).1
    have hin : σ v ∈ Metric.ball (A.c (A.sel (σ v))) (2 * A.r (A.sel (σ v))) :=
      Metric.ball_subset_ball (by linarith [A.hr _ hact])
        (A.sel_spec hreg.1 hreg.2).2
    have hyv : (A.Φ (A.sel (σ v)) (σ v)).im ∉ E (A.sel (σ v)) := by
      intro hbad
      obtain ⟨r, hr1, hr2, hr3⟩ := leaf_height_hit_rational hT hσtraj hv
        Metric.isOpen_ball (A.hd _ hact) (A.hsq _ hact) hin
      have hflow : A.flow (r : ℝ) z ∈ BP := by
        have hmem : A.flow (r : ℝ) z ∈ ⋃ j : ℕ,
            {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (2 * A.r j)
              ∧ (A.Φ j z).im ∈ E j} := by
          refine Set.mem_iUnion.mpr ⟨A.sel (σ v), hact, ?_, ?_⟩
          · rw [hσev _ hr1]
            exact hr2
          · rw [hσev _ hr1, hr3]
            exact hbad
        exact hBPsub hmem
      exact hz r hzg hflow
    have hP : P (A.sel (σ v)) ((A.Φ (A.sel (σ v)) (σ v)).im) := by
      by_contra hnP
      exact hyv (subset_toMeasurable volume _ hnP)
    obtain ⟨δ, hδ, hAC⟩ := leaf_window_ac hσtraj hv Metric.isOpen_ball
      (A.hd _ hact) (A.hinj _ hact) (A.hsq _ hact) hin hP
    exact ⟨δ, hδ, hAC⟩
  have hmaps : ∀ t ∈ Set.uIcc (0 : ℝ) 1, T * t + 0 ∈ Set.uIcc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Set.uIcc_of_le hT.le]
    rw [add_zero]
    exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hAC1 := AbsolutelyContinuousOnInterval.comp_affine hT hACfull hmaps
  refine AbsolutelyContinuousOnInterval.congr hAC1 fun t ht => ?_
  show h (σ (T * t + 0)) = h (σ (t * T))
  rw [add_zero, mul_comm]

/-- Almost-everywhere equal plane functions have almost-everywhere equal height
slices at almost every height. -/
theorem slice_agree_ae {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    ∀ᵐ y : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      f ((x : ℂ) + (y : ℝ) * Complex.I) = g ((x : ℂ) + (y : ℝ) * Complex.I) := by
  set N : Set ℂ := toMeasurable volume {w : ℂ | ¬ f w = g w} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.mp hfg
  have hNsub := subset_toMeasurable volume {w : ℂ | ¬ f w = g w}
  have hmp : MeasurePreserving (fun p : ℝ × ℝ =>
      ((p.2 : ℝ) : ℂ) + (p.1 : ℝ) * Complex.I)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) (volume : Measure ℂ) := by
    have h1 : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
      Measure.measurePreserving_swap
    have h2 : MeasurePreserving Complex.measurableEquivRealProd.symm
        ((volume : Measure ℝ).prod volume) (volume : Measure ℂ) := by
      have h3 := Complex.volume_preserving_equiv_real_prod.symm
        Complex.measurableEquivRealProd
      rwa [Measure.volume_eq_prod] at h3
    have h4 := h2.comp h1
    have hfun : (⇑Complex.measurableEquivRealProd.symm ∘ Prod.swap)
        = fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) + (p.1 : ℝ) * Complex.I := by
      funext p
      change Complex.measurableEquivRealProd.symm (p.2, p.1) = _
      rw [Complex.measurableEquivRealProd_symm_apply]
      exact Complex.mk_eq_add_mul_I _ _
    rwa [hfun] at h4
  have hS0 : ((volume : Measure ℝ).prod volume)
      ((fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) + (p.1 : ℝ) * Complex.I) ⁻¹' N) = 0 := by
    rw [hmp.measure_preimage hNm.nullMeasurableSet]
    exact hN0
  have hae : ∀ᵐ p ∂((volume : Measure ℝ).prod volume),
      ((p.2 : ℝ) : ℂ) + (p.1 : ℝ) * Complex.I ∉ N := by
    refine ae_iff.mpr ?_
    have hset : {p : ℝ × ℝ | ¬ ((p.2 : ℝ) : ℂ) + (p.1 : ℝ) * Complex.I ∉ N}
        = (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) + (p.1 : ℝ) * Complex.I) ⁻¹' N := by
      ext p
      simp
    rw [hset]
    exact hS0
  have h5 := Measure.ae_ae_of_ae_prod hae
  filter_upwards [h5] with y hy
  filter_upwards [hy] with x hx
  by_contra hne
  exact hx (hNsub hne)

/-- The chart inverse is continuous on the developed image. -/
theorem chart_invFunOn_continuousOn {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hne : ∀ w ∈ S, q w ≠ 0) (hsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w) :
    ContinuousOn (Function.invFunOn Φ S) (Φ '' S) := by
  have hinv_pre : ∀ U : Set ℂ,
      (Function.invFunOn Φ S) ⁻¹' U ∩ (Φ '' S) = Φ '' (U ∩ S) := by
    intro U
    ext w
    constructor
    · rintro ⟨hwU, a, haS, rfl⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, haS, rfl⟩
      have hval : Function.invFunOn Φ S (Φ a) = a :=
        hΦinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
      rw [Set.mem_preimage, hval] at hwU
      exact ⟨a, ⟨hwU, haS⟩, rfl⟩
    · rintro ⟨a, ⟨haU, haS⟩, rfl⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, haS, rfl⟩
      have hval : Function.invFunOn Φ S (Φ a) = a :=
        hΦinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
      exact ⟨by rw [Set.mem_preimage, hval]; exact haU, ⟨a, haS, rfl⟩⟩
  rw [continuousOn_iff']
  intro U hU
  refine ⟨Φ '' (U ∩ S), chart_image_open (hU.inter hS)
    (hΦd.mono Set.inter_subset_right) (fun w hw => hne w hw.2)
    (fun w hw => hsq w hw.2), ?_⟩
  rw [hinv_pre U]
  exact (Set.inter_eq_self_of_subset_left
    (Set.image_mono Set.inter_subset_right)).symm

/-- Continuous functions equal almost everywhere agree on a nondegenerate interval. -/
theorem eq_of_ae_eq_continuousOn {F G : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) (hG : ContinuousOn G (Set.Icc a b))
    (hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Icc a b → F x = G x) :
    ∀ t ∈ Set.Icc a b, F t = G t := by
  intro t ht
  have hclos : t ∈ closure {x | x ∈ Set.Icc a b ∧ F x = G x} := by
    rw [mem_closure_iff]
    intro U hUo htU
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUo t htU
    obtain ⟨u₁, u₂, hu12, hsub⟩ : ∃ u₁ u₂ : ℝ, u₁ < u₂ ∧
        Set.Ioo u₁ u₂ ⊆ Metric.ball t δ ∩ Set.Icc a b := by
      rcases lt_or_ge t b with htb | htb
      · refine ⟨t, min b (t + δ), lt_min htb (by linarith), fun u hu => ?_⟩
        have h1 := lt_of_lt_of_le hu.2 (min_le_left _ _)
        have h2 := lt_of_lt_of_le hu.2 (min_le_right _ _)
        refine ⟨?_, ⟨le_trans ht.1 hu.1.le, h1.le⟩⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.1]
      · have htb' : t = b := le_antisymm ht.2 htb
        refine ⟨max a (b - δ), b, ?_, fun u hu => ?_⟩
        · rcases le_or_gt a (b - δ) with h1 | h1
          · rw [max_eq_right h1]
            linarith
          · rw [max_eq_left h1.le]
            exact hab
        · have h1 := lt_of_le_of_lt (le_max_right a (b - δ)) hu.1
          have h2 := lt_of_le_of_lt (le_max_left a (b - δ)) hu.1
          refine ⟨?_, ⟨h2.le, hu.2.le⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, htb', abs_lt]
          constructor <;> linarith [hu.2]
    have hpos : (0 : ℝ≥0∞) < volume (Set.Ioo u₁ u₂) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    have hnn : ¬ Set.Ioo u₁ u₂ ⊆ {x : ℝ | ¬ (x ∈ Set.Icc a b → F x = G x)} := by
      intro hcon
      exact absurd (measure_mono_null hcon (ae_iff.mp hae)) (ne_of_gt hpos)
    obtain ⟨x, hxJ, hxeq⟩ := Set.not_subset.mp hnn
    exact ⟨x, hball (hsub hxJ).1, (hsub hxJ).2,
      (not_not.mp hxeq) (hsub hxJ).2⟩
  obtain ⟨seq, hseqmem, hseqlim⟩ := mem_closure_iff_seq_limit.mp hclos
  have hseqin : Filter.Tendsto seq Filter.atTop (nhdsWithin t (Set.Icc a b)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hseqlim, ?_⟩
    filter_upwards with n
    exact (hseqmem n).1
  have hFlim : Filter.Tendsto (fun n => F (seq n)) Filter.atTop (nhds (F t)) :=
    (hF t ht).tendsto.comp hseqin
  have hGlim : Filter.Tendsto (fun n => F (seq n)) Filter.atTop (nhds (G t)) := by
    refine Filter.Tendsto.congr (fun n => ((hseqmem n).2).symm) ?_
    exact (hG t ht).tendsto.comp hseqin
  exact tendsto_nhds_unique hFlim hGlim

/-- **Tube slicing**: a globally weakly differentiable extension of the chart-inverse
composite over a compact tube yields absolute continuity of the composite along almost
every height line of the tube. -/
theorem tube_height_slicing {q h : ℂ → ℂ} (A : Atlas q) {j : ℕ} (hj : A.active j)
    (hcont : ContinuousOn h {z : ℂ | 0 < z.im})
    {p qr c ρ : ℝ} (hpq : p < qr)
    (htube : (fun xy : ℝ × ℝ => ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) ''
        (Set.Icc p qr ×ˢ Set.Icc (c - ρ) (c + ρ))
      ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j))
    {G Gx : ℂ → ℂ} (hGint : LocallyIntegrable G) (hGxint : LocallyIntegrable Gx)
    (hGweak : HasWeakDirDeriv 1 Gx G Set.univ)
    {U : Set ℂ} (hKU : (fun xy : ℝ × ℝ => ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) ''
        (Set.Icc p qr ×ˢ Set.Icc (c - ρ) (c + ρ)) ⊆ U)
    (hGU : ∀ w ∈ U, G w = h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) w)) :
    ∀ᵐ y : ℝ ∂(volume : Measure ℝ), y ∈ Set.Icc (c - ρ) (c + ρ) →
      AbsolutelyContinuousOnInterval
        (fun x => h (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j)) ((x : ℂ) + (y : ℝ) * Complex.I)))
        p qr := by
  obtain ⟨G', hG'ae, hG'acl⟩ :=
    exists_aclHorizontal_of_hasWeakDirDeriv_one hGint hGxint hGweak
  have hslice := slice_agree_ae hG'ae
  filter_upwards [hG'acl, hslice] with y hy hyeq
  intro hymem
  have hseg : ∀ x ∈ Set.Icc p qr,
      (x : ℂ) + (y : ℝ) * Complex.I ∈ (fun xy : ℝ × ℝ =>
        ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) ''
        (Set.Icc p qr ×ˢ Set.Icc (c - ρ) (c + ρ)) :=
    fun x hx => ⟨(x, y), ⟨hx, hymem⟩, rfl⟩
  have hACG' : AbsolutelyContinuousOnInterval
      (fun x : ℝ => G' ((x : ℂ) + (y : ℝ) * Complex.I)) p qr := by
    refine AbsolutelyContinuousOnInterval.congr (hy.1 p qr) fun x _ => ?_
    exact congrArg G' (Complex.mk_eq_add_mul_I x y)
  have hcontG' : ContinuousOn
      (fun x : ℝ => G' ((x : ℂ) + (y : ℝ) * Complex.I)) (Set.Icc p qr) := by
    have h1 := AbsolutelyContinuousOnInterval.continuousOn hACG'
    rwa [Set.uIcc_of_le hpq.le] at h1
  have hψcont := chart_invFunOn_continuousOn Metric.isOpen_ball (A.hd j hj)
    (A.hinj j hj) (A.hne j hj) (A.hsq j hj)
  have hline : ContinuousOn (fun x : ℝ => (x : ℂ) + (y : ℝ) * Complex.I)
      (Set.Icc p qr) :=
    (Complex.continuous_ofReal.add continuous_const).continuousOn
  have hcontg : ContinuousOn
      (fun x : ℝ => h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)) ((x : ℂ) + (y : ℝ) * Complex.I)))
      (Set.Icc p qr) := by
    have hmaps1 : Set.MapsTo (fun x : ℝ => (x : ℂ) + (y : ℝ) * Complex.I)
        (Set.Icc p qr) (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) :=
      fun x hx => htube (hseg x hx)
    have hmaps2 : Set.MapsTo (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)))
        (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) {z : ℂ | 0 < z.im} := by
      rintro w ⟨a, haS, rfl⟩
      have hex : ∃ x ∈ Metric.ball (A.c j) (2 * A.r j), A.Φ j x = A.Φ j a :=
        ⟨a, haS, rfl⟩
      exact A.hH j hj (Function.invFunOn_mem hex)
    exact ContinuousOn.comp hcont (ContinuousOn.comp hψcont hline hmaps1)
      fun x hx => hmaps2 (hmaps1 hx)
  have haeslice : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Icc p qr →
      G' ((x : ℂ) + (y : ℝ) * Complex.I)
        = h (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
          ((x : ℂ) + (y : ℝ) * Complex.I)) := by
    filter_upwards [hyeq] with x hx
    intro hxmem
    rw [hx, hGU _ (hKU (hseg x hxmem))]
  have heq := eq_of_ae_eq_continuousOn hpq hcontG' hcontg haeslice
  refine AbsolutelyContinuousOnInterval.congr hACG' fun t ht => ?_
  refine heq t ?_
  rwa [Set.uIcc_of_le hpq.le] at ht

/-- **Chart slicing from compact weak differentiability**: the per-chart height
slicing hypothesis of `sym_hacl_of_chart_slicing`, from globally weakly
differentiable compactly-localized extensions of the chart-inverse composite. -/
theorem chart_slicing_of_w11loc {q h : ℂ → ℂ} (A : Atlas q)
    (hcont : ContinuousOn h {z : ℂ | 0 < z.im})
    (hpin : ∀ j : ℕ, A.active j → ∀ K : Set ℂ, IsCompact K →
      K ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j) →
      ∃ G Gx : ℂ → ℂ, LocallyIntegrable G ∧ LocallyIntegrable Gx ∧
        HasWeakDirDeriv 1 Gx G Set.univ ∧
        ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ ∀ w ∈ U,
          G w = h (Function.invFunOn (A.Φ j)
            (Metric.ball (A.c j) (2 * A.r j)) w)) :
    ∀ j : ℕ, A.active j → ∀ᵐ y : ℝ ∂(volume : Measure ℝ), ∀ a b : ℝ,
      (∀ x ∈ Set.uIcc a b, (x : ℂ) + (y : ℝ) * Complex.I
        ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) →
      AbsolutelyContinuousOnInterval
        (fun x => h (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j))
          ((x : ℂ) + (y : ℝ) * Complex.I))) a b := by
  intro j hj
  classical
  have hlinecont : Continuous (fun xy : ℝ × ℝ =>
      ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hkey : ∀ d : ℚ × ℚ × ℚ × ℚ, ∀ᵐ y : ℝ ∂(volume : Measure ℝ),
      (((d.1 : ℝ) < (d.2.1 : ℝ)) ∧
        (fun xy : ℝ × ℝ => ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) ''
          (Set.Icc (d.1 : ℝ) (d.2.1 : ℝ)
            ×ˢ Set.Icc ((d.2.2.1 : ℝ) - (d.2.2.2 : ℝ))
              ((d.2.2.1 : ℝ) + (d.2.2.2 : ℝ)))
          ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) →
      y ∈ Set.Icc ((d.2.2.1 : ℝ) - (d.2.2.2 : ℝ))
        ((d.2.2.1 : ℝ) + (d.2.2.2 : ℝ)) →
      AbsolutelyContinuousOnInterval
        (fun x => h (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j))
          ((x : ℂ) + (y : ℝ) * Complex.I))) (d.1 : ℝ) (d.2.1 : ℝ) := by
    intro d
    by_cases hC : ((d.1 : ℝ) < (d.2.1 : ℝ)) ∧
        (fun xy : ℝ × ℝ => ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) ''
          (Set.Icc (d.1 : ℝ) (d.2.1 : ℝ)
            ×ˢ Set.Icc ((d.2.2.1 : ℝ) - (d.2.2.2 : ℝ))
              ((d.2.2.1 : ℝ) + (d.2.2.2 : ℝ)))
          ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)
    · obtain ⟨hpq, htube⟩ := hC
      have hK : IsCompact ((fun xy : ℝ × ℝ =>
          ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) ''
          (Set.Icc (d.1 : ℝ) (d.2.1 : ℝ)
            ×ˢ Set.Icc ((d.2.2.1 : ℝ) - (d.2.2.2 : ℝ))
              ((d.2.2.1 : ℝ) + (d.2.2.2 : ℝ)))) :=
        (isCompact_Icc.prod isCompact_Icc).image hlinecont
      obtain ⟨G, Gx, hGint, hGxint, hGweak, U, hUo, hKU, hGU⟩ :=
        hpin j hj _ hK htube
      have h1 := tube_height_slicing A hj hcont hpq htube hGint hGxint
        hGweak hKU hGU
      filter_upwards [h1] with y hy
      intro _ hymem
      exact hy hymem
    · filter_upwards with y
      intro hC' _
      exact absurd hC' hC
  have hall := ae_all_iff.mpr hkey
  filter_upwards [hall] with y hy
  intro a b hcond
  suffices hs : AbsolutelyContinuousOnInterval
      (fun x => h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j))
        ((x : ℂ) + (y : ℝ) * Complex.I))) (min a b) (max a b) by
    rcases le_total a b with hab | hab
    · rwa [min_eq_left hab, max_eq_right hab] at hs
    · have h2 := hs.symm
      rwa [min_eq_right hab, max_eq_left hab] at h2
  rcases eq_or_lt_of_le (min_le_max (a := a) (b := b)) with heq | hlt
  · rw [← heq]
    exact acOn_self _ _
  have hWopen : IsOpen (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) :=
    chart_image_open Metric.isOpen_ball (A.hd j hj) (A.hne j hj) (A.hsq j hj)
  have hsegc : IsCompact ((fun x : ℝ => (x : ℂ) + (y : ℝ) * Complex.I) ''
      Set.Icc (min a b) (max a b)) :=
    isCompact_Icc.image (Complex.continuous_ofReal.add continuous_const)
  have hsegW : (fun x : ℝ => (x : ℂ) + (y : ℝ) * Complex.I) ''
      Set.Icc (min a b) (max a b)
      ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j) := by
    rintro w ⟨x, hx, rfl⟩
    exact hcond x hx
  obtain ⟨δ, hδ, hthick⟩ := hsegc.exists_thickening_subset_open hWopen hsegW
  obtain ⟨pr, hp1, hp2⟩ := exists_rat_btwn
    (show min a b - δ / 4 < min a b by linarith)
  obtain ⟨qr, hq1, hq2⟩ := exists_rat_btwn
    (show max a b < max a b + δ / 4 by linarith)
  obtain ⟨ρr, hρ1, hρ2⟩ := exists_rat_btwn (show (0 : ℝ) < δ / 4 by linarith)
  obtain ⟨cr, hc1, hc2⟩ := exists_rat_btwn (show y - (ρr : ℝ) < y by linarith)
  have hymem : y ∈ Set.Icc ((cr : ℝ) - (ρr : ℝ)) ((cr : ℝ) + (ρr : ℝ)) :=
    ⟨by linarith, by linarith⟩
  have htubesub : (fun xy : ℝ × ℝ => ((xy.1 : ℝ) : ℂ) + xy.2 * Complex.I) ''
      (Set.Icc (pr : ℝ) (qr : ℝ)
        ×ˢ Set.Icc ((cr : ℝ) - (ρr : ℝ)) ((cr : ℝ) + (ρr : ℝ)))
      ⊆ Metric.thickening δ ((fun x : ℝ => (x : ℂ) + (y : ℝ) * Complex.I) ''
        Set.Icc (min a b) (max a b)) := by
    rintro w ⟨⟨x', y'⟩, ⟨hx', hy'⟩, rfl⟩
    set x₀ : ℝ := max (min a b) (min (max a b) x') with hx₀def
    have hx₀mem : x₀ ∈ Set.Icc (min a b) (max a b) :=
      ⟨le_max_left _ _, max_le hlt.le (min_le_left _ _)⟩
    have hd1 : |x' - x₀| < δ / 4 := by
      rcases le_total x' (min a b) with h1 | h1
      · have hmin : min (max a b) x' = x' := min_eq_right (le_trans h1 hlt.le)
        have hmax : x₀ = min a b := by
          rw [hx₀def, hmin, max_eq_left h1]
        rw [hmax, abs_sub_comm, abs_of_nonneg (by linarith)]
        have := hx'.1
        linarith
      · rcases le_total x' (max a b) with h2 | h2
        · have hmin : min (max a b) x' = x' := min_eq_right h2
          have hmax : x₀ = x' := by
            rw [hx₀def, hmin, max_eq_right h1]
          rw [hmax, sub_self, abs_zero]
          linarith
        · have hmin : min (max a b) x' = max a b := min_eq_left h2
          have hmax : x₀ = max a b := by
            rw [hx₀def, hmin, max_eq_right hlt.le]
          rw [hmax, abs_of_nonneg (by linarith)]
          have := hx'.2
          linarith
    have hd2 : |y' - y| < δ / 2 := by
      have h1 : |y' - (cr : ℝ)| ≤ (ρr : ℝ) := abs_le.mpr
        ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
      have h2 : |(cr : ℝ) - y| < (ρr : ℝ) := abs_lt.mpr
        ⟨by linarith, by linarith⟩
      calc |y' - y| ≤ |y' - (cr : ℝ)| + |(cr : ℝ) - y| := abs_sub_le _ _ _
        _ < (ρr : ℝ) + (ρr : ℝ) := by linarith
        _ < δ / 2 := by linarith
    refine Metric.mem_thickening_iff.mpr
      ⟨(x₀ : ℂ) + (y : ℝ) * Complex.I, ⟨x₀, hx₀mem, rfl⟩, ?_⟩
    have hdiff : (((x' : ℝ) : ℂ) + (y' : ℝ) * Complex.I)
        - (((x₀ : ℝ) : ℂ) + (y : ℝ) * Complex.I)
        = ((x' - x₀ : ℝ) : ℂ) + ((y' - y : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [Complex.dist_eq, hdiff]
    calc ‖((x' - x₀ : ℝ) : ℂ) + ((y' - y : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((x' - x₀ : ℝ) : ℂ)‖ + ‖((y' - y : ℝ) : ℂ) * Complex.I‖ :=
          norm_add_le _ _
      _ = |x' - x₀| + |y' - y| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ < δ := by linarith
  have hd := hy (pr, qr, cr, ρr)
  have hpq' : (pr : ℝ) < (qr : ℝ) := by linarith
  have hAC := hd ⟨hpq', htubesub.trans hthick⟩ hymem
  refine AbsolutelyContinuousOnInterval.mono hAC ?_
  rw [Set.uIcc_of_le hlt.le, Set.uIcc_of_le hpq'.le]
  exact Set.Icc_subset_Icc (by linarith) (by linarith)

/-- The chart inverse maps the developed image onto the chart ball. -/
theorem chart_invFunOn_image {Φ : ℂ → ℂ} {S : Set ℂ} (hΦinj : Set.InjOn Φ S) :
    Function.invFunOn Φ S '' (Φ '' S) = S := by
  ext a
  constructor
  · rintro ⟨w, ⟨b, hbS, rfl⟩, rfl⟩
    have hex : ∃ x ∈ S, Φ x = Φ b := ⟨b, hbS, rfl⟩
    have hval : Function.invFunOn Φ S (Φ b) = b :=
      hΦinj (Function.invFunOn_mem hex) hbS (Function.invFunOn_eq hex)
    rw [hval]
    exact hbS
  · intro haS
    have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, haS, rfl⟩
    have hval : Function.invFunOn Φ S (Φ a) = a :=
      hΦinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
    exact ⟨Φ a, ⟨a, haS, rfl⟩, hval⟩

/-- The chart inverse is injective on the developed image. -/
theorem chart_invFunOn_injOn {Φ : ℂ → ℂ} {S : Set ℂ} :
    Set.InjOn (Function.invFunOn Φ S) (Φ '' S) := by
  rintro w₁ ⟨a₁, ha₁, rfl⟩ w₂ ⟨a₂, ha₂, rfl⟩ heq
  have hex₁ : ∃ x ∈ S, Φ x = Φ a₁ := ⟨a₁, ha₁, rfl⟩
  have hex₂ : ∃ x ∈ S, Φ x = Φ a₂ := ⟨a₂, ha₂, rfl⟩
  rw [← Function.invFunOn_eq hex₁, ← Function.invFunOn_eq hex₂, heq]

/-- **Differentiability of the chart inverse**: at every developed point the inverse of
an injective holomorphic chart with nonvanishing squared derivative has the reciprocal
derivative. -/
theorem chart_invFunOn_hasDerivAt {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hne : ∀ w ∈ S, q w ≠ 0) (hsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {x : ℂ} (hx : x ∈ Φ '' S) :
    HasDerivAt (Function.invFunOn Φ S)
      ((deriv Φ (Function.invFunOn Φ S x))⁻¹) x := by
  obtain ⟨a, haS, rfl⟩ := hx
  have hex : ∃ z ∈ S, Φ z = Φ a := ⟨a, haS, rfl⟩
  have hval : Function.invFunOn Φ S (Φ a) = a :=
    hΦinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
  have hΦan : AnalyticAt ℂ Φ a := (hΦd.analyticOnNhd hS) a haS
  have hΦ' : deriv Φ a ≠ 0 := by
    intro h0
    have h1 := hsq a haS
    rw [h0] at h1
    exact hne a haS (by simpa using h1.symm)
  have hstrict : HasStrictDerivAt Φ (deriv Φ a) a :=
    (hΦan.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  set ψ : ℂ → ℂ := hstrict.localInverse Φ (deriv Φ a) a hΦ' with hψdef
  have hψd : HasStrictDerivAt ψ (deriv Φ a)⁻¹ (Φ a) := hstrict.to_localInverse hΦ'
  have hright : ∀ᶠ w in nhds (Φ a), Φ (ψ w) = w :=
    hstrict.eventually_right_inverse hΦ'
  have hψball : ∀ᶠ w in nhds (Φ a), ψ w ∈ S := by
    have hψc : ContinuousAt ψ (Φ a) := hψd.hasDerivAt.continuousAt
    have h1 : ψ (Φ a) ∈ S := by
      have h2 := hstrict.eventually_left_inverse hΦ'
      have h3 : ψ (Φ a) = a := h2.self_of_nhds
      rw [h3]
      exact haS
    exact hψc.eventually (hS.mem_nhds h1)
  have hWopen : IsOpen (Φ '' S) := chart_image_open hS hΦd hne hsq
  have hgerm : ∀ᶠ w in nhds (Φ a), Function.invFunOn Φ S w = ψ w := by
    filter_upwards [hright, hψball, hWopen.mem_nhds ⟨a, haS, rfl⟩]
      with w hw1 hw2 hw3
    obtain ⟨b, hbS, rfl⟩ := hw3
    have hexb : ∃ z ∈ S, Φ z = Φ b := ⟨b, hbS, rfl⟩
    have hvalb : Function.invFunOn Φ S (Φ b) = b :=
      hΦinj (Function.invFunOn_mem hexb) hbS (Function.invFunOn_eq hexb)
    rw [hvalb]
    exact (hΦinj hw2 hbS hw1).symm
  have hmain : HasDerivAt (Function.invFunOn Φ S) ((deriv Φ a)⁻¹) (Φ a) :=
    hψd.hasDerivAt.congr_of_eventuallyEq hgerm
  rwa [hval]

/-- **Globalization of compactly supported weak derivatives**: a weak directional
derivative on an open set whose data are compactly supported inside the set is a weak
directional derivative on the plane. -/
theorem hasWeakDirDeriv_univ_of_compactSupport {v : ℂ} {g f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hfcs : HasCompactSupport f) (hgcs : HasCompactSupport g)
    (hfts : tsupport f ⊆ Ω) (hgts : tsupport g ⊆ Ω)
    (h : HasWeakDirDeriv v g f Ω) :
    HasWeakDirDeriv v g f Set.univ := by
  intro φ hφ hcs _
  set Kfg : Set ℂ := tsupport f ∪ tsupport g with hKfg
  have hKfgc : IsCompact Kfg := hfcs.union hgcs
  have hKfgΩ : Kfg ⊆ Ω := Set.union_subset hfts hgts
  obtain ⟨T1, hT1c, hKT1, hT1Ω⟩ := exists_compact_between hKfgc hΩ hKfgΩ
  obtain ⟨T2, hT2c, hT1T2, hT2Ω⟩ := exists_compact_between hT1c hΩ hT1Ω
  obtain ⟨χ0, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ ℂ) (n := (⊤ : ℕ∞))
    (isOpen_interior.isClosed_compl) hT1c.isClosed
    (Set.disjoint_left.mpr fun z hzs hzt => hzs (hT1T2 hzt))
  set χ : ℂ → ℝ := fun z => χ0 z with hχdef
  have hχ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    contMDiff_iff_contDiff.mp χ0.contMDiff
  have hχ_zero : ∀ z ∉ interior T2, χ z = 0 := fun z hz => by simpa using hχ0 hz
  have hχ_one : ∀ z ∈ T1, χ z = 1 := fun z hz => by simpa using hχ1 hz
  have hχ_supp : Function.support χ ⊆ T2 := by
    intro z hz
    by_contra hzT
    exact hz (hχ_zero z fun hzi => hzT (interior_subset hzi))
  have hχ_cs : HasCompactSupport χ :=
    HasCompactSupport.of_support_subset_isCompact hT2c hχ_supp
  have hχ_ts : tsupport χ ⊆ Ω := (closure_minimal hχ_supp hT2c.isClosed).trans hT2Ω
  have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ z * φ z) :=
    hχ_cd.mul hφ
  have hΦcs : HasCompactSupport (fun z => χ z * φ z) := hcs.mul_left
  have hΦts : tsupport (fun z => χ z * φ z) ⊆ Ω :=
    tsupport_mul_subset_left.trans hχ_ts
  have hfΦ := h (fun z => χ z * φ z) hΦsm hΦcs hΦts
  have hfd0 : ∀ z ∈ interior T1, fderiv ℝ χ z = 0 := by
    intro z hz
    have hloc : χ =ᶠ[nhds z] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_interior.mem_nhds hz] with y hy
      exact hχ_one y (interior_subset hy)
    rw [hloc.fderiv_eq]
    simp
  have hpr : ∀ z, (fderiv ℝ (fun y => χ y * φ y) z) v
      = χ z * ((fderiv ℝ φ z) v) + φ z * ((fderiv ℝ χ z) v) := by
    intro z
    have hdχ : DifferentiableAt ℝ χ z :=
      (hχ_cd.differentiable (by norm_num)).differentiableAt
    have hdφ : DifferentiableAt ℝ φ z :=
      (hφ.differentiable (by norm_num)).differentiableAt
    rw [fderiv_fun_mul hdχ hdφ]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
  have hL : ∀ z, ((fderiv ℝ (fun y => χ y * φ y) z) v) • f z
      = ((fderiv ℝ φ z) v) • f z := by
    intro z
    by_cases hz : f z = 0
    · rw [hz]
      simp
    · have hzT1 : z ∈ interior T1 :=
        hKT1 (Set.mem_union_left _ (subset_tsupport f hz))
      rw [hpr z, hχ_one z (interior_subset hzT1), hfd0 z hzT1]
      simp
  have hR : ∀ z, (χ z * φ z) • g z = φ z • g z := by
    intro z
    by_cases hz : g z = 0
    · rw [hz]
      simp
    · have hzT1 : z ∈ interior T1 :=
        hKT1 (Set.mem_union_right _ (subset_tsupport g hz))
      rw [hχ_one z (interior_subset hzT1), one_mul]
  calc ∫ z, ((fderiv ℝ φ z) v) • f z
      = ∫ z, ((fderiv ℝ (fun y => χ y * φ y) z) v) • f z :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => (hL z).symm)
    _ = - ∫ z, (χ z * φ z) • g z := hfΦ
    _ = - ∫ z, φ z • g z := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hR)]

/-- **Weak differentiability of the chart-inverse composite**: the quasiconformal map
composed with the inverse of a natural chart has a locally square-integrable weak
horizontal derivative on the developed window. -/
theorem chartInv_comp_hasWeakDirDeriv {q h hinv : ℂ → ℂ} {κ : ℝ} (A : Atlas q)
    (hqc : IsQCUpper h hinv κ) {j : ℕ} (hj : A.active j) :
    ∃ D : ℂ → ℂ,
      HasWeakDirDeriv 1 D (fun x => h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)) x))
        (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) ∧
      MemLpLocOn D 2 (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) := by
  have hWopen : IsOpen (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) :=
    chart_image_open Metric.isOpen_ball (A.hd j hj) (A.hne j hj) (A.hsq j hj)
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨hL2, gx, gy, hgrad, hgx2, hgy2⟩ := hqc.sobolev
  have hι : ∀ x ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j),
      HasDerivAt (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)))
        ((deriv (A.Φ j) (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j)) x))⁻¹) x :=
    fun x hx => chart_invFunOn_hasDerivAt Metric.isOpen_ball (A.hd j hj)
      (A.hinj j hj) (A.hne j hj) (A.hsq j hj) hx
  have hιmem : ∀ x ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j),
      Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) x
        ∈ Metric.ball (A.c j) (2 * A.r j) := by
    rintro x ⟨a, haS, rfl⟩
    exact Function.invFunOn_mem ⟨a, haS, rfl⟩
  have hι0 : ∀ x ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j),
      (deriv (A.Φ j) (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)) x))⁻¹ ≠ 0 := by
    intro x hx
    refine inv_ne_zero fun h0 => ?_
    have h1 := A.hsq j hj _ (hιmem x hx)
    rw [h0] at h1
    exact A.hne j hj _ (hιmem x hx) (by simpa using h1.symm)
  have hιim := chart_invFunOn_image (S := Metric.ball (A.c j) (2 * A.r j))
    (A.hinj j hj)
  have hid : ∀ u ∈ {z : ℂ | 0 < z.im},
      HasDerivAt (id : ℂ → ℂ) ((fun _ : ℂ => (1 : ℂ)) u) u :=
    fun u _ => hasDerivAt_id u
  have hmaps : Set.MapsTo h
      (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) ''
        (A.Φ j '' Metric.ball (A.c j) (2 * A.r j))) {z : ℂ | 0 < z.im} := by
    rw [hιim]
    exact fun z hz => hqc.mapsTo z (A.hH j hj hz)
  have hwc : ContinuousOn h
      (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) ''
        (A.Φ j '' Metric.ball (A.c j) (2 * A.r j))) := by
    rw [hιim]
    exact hqc.cont.mono (A.hH j hj)
  have hw : HasWeakGradient gx gy h
      (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) ''
        (A.Φ j '' Metric.ball (A.c j) (2 * A.r j))) := by
    rw [hιim]
    exact ⟨hgrad.1.mono (A.hH j hj), hgrad.2.mono (A.hH j hj)⟩
  have hgx' : MemLpLocOn gx 2
      (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) ''
        (A.Φ j '' Metric.ball (A.c j) (2 * A.r j))) := by
    rw [hιim]
    exact MemLpLocOn.mono hgx2 (A.hH j hj)
  have hgy' : MemLpLocOn gy 2
      (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) ''
        (A.Φ j '' Metric.ball (A.c j) (2 * A.r j))) := by
    rw [hιim]
    exact MemLpLocOn.mono hgy2 (A.hH j hj)
  have hfeq : Set.EqOn (fun x => h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) x))
      (fun z => id (h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)) z)))
      (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) := fun z _ => rfl
  obtain ⟨hwd, hDL2⟩ := hasWeakDirDeriv_comp_conformal hWopen hUopen hι hι0
    chart_invFunOn_injOn hid hmaps hwc hw hgx' hgy' hfeq 1
  exact ⟨_, hwd, hDL2⟩

/-- **The compact weak-differentiable localization**: the pinned hypothesis of
`chart_slicing_of_w11loc`, discharged from the quasiconformal Sobolev regularity. -/
theorem w11loc_localization {q h hinv : ℂ → ℂ} {κ : ℝ} (A : Atlas q)
    (hqc : IsQCUpper h hinv κ) {j : ℕ} (hj : A.active j)
    {K : Set ℂ} (hK : IsCompact K)
    (hKW : K ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) :
    ∃ G Gx : ℂ → ℂ, LocallyIntegrable G ∧ LocallyIntegrable Gx ∧
      HasWeakDirDeriv 1 Gx G Set.univ ∧
      ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ ∀ w ∈ U,
        G w = h (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j)) w) := by
  have : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
  have : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  have : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  obtain ⟨D, hwd, hDL2⟩ := chartInv_comp_hasWeakDirDeriv A hqc hj
  have hWopen : IsOpen (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) :=
    chart_image_open Metric.isOpen_ball (A.hd j hj) (A.hne j hj) (A.hsq j hj)
  have hψcont := chart_invFunOn_continuousOn Metric.isOpen_ball (A.hd j hj)
    (A.hinj j hj) (A.hne j hj) (A.hsq j hj)
  have hιmem : ∀ x ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j),
      Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) x
        ∈ Metric.ball (A.c j) (2 * A.r j) := by
    rintro x ⟨a, haS, rfl⟩
    exact Function.invFunOn_mem ⟨a, haS, rfl⟩
  have hgcont : ContinuousOn (fun x => h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) x))
      (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) :=
    ContinuousOn.comp hqc.cont hψcont fun x hx => A.hH j hj (hιmem x hx)
  have hfloc : LocallyIntegrableOn (fun x => h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) x))
      (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) :=
    hgcont.locallyIntegrableOn hWopen.measurableSet
  have hDloc : LocallyIntegrableOn D
      (A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) := by
    rw [MeasureTheory.locallyIntegrableOn_iff hWopen.isLocallyClosed]
    intro k hk hkc
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp ((hDL2 k hk hkc).mono_exponent (by norm_num))
  obtain ⟨T1, hT1c, hKT1, hT1W⟩ := exists_compact_between hK hWopen hKW
  obtain ⟨T2, hT2c, hT1T2, hT2W⟩ := exists_compact_between hT1c hWopen hT1W
  obtain ⟨χ0, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ ℂ) (n := (⊤ : ℕ∞))
    (isOpen_interior.isClosed_compl) hT1c.isClosed
    (Set.disjoint_left.mpr fun z hzs hzt => hzs (hT1T2 hzt))
  set χ : ℂ → ℝ := fun z => χ0 z with hχdef
  have hχ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    contMDiff_iff_contDiff.mp χ0.contMDiff
  have hχ_zero : ∀ z ∉ interior T2, χ z = 0 := fun z hz => by simpa using hχ0 hz
  have hχ_one : ∀ z ∈ T1, χ z = 1 := fun z hz => by simpa using hχ1 hz
  have hχ_supp : Function.support χ ⊆ T2 := by
    intro z hz
    by_contra hzT
    exact hz (hχ_zero z fun hzi => hzT (interior_subset hzi))
  have hχ_ts : tsupport χ ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j) :=
    (closure_minimal hχ_supp hT2c.isClosed).trans hT2W
  have hχfd0 : ∀ z ∉ tsupport χ, fderiv ℝ χ z = 0 := by
    intro z hz
    have hloc : χ =ᶠ[nhds z] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [hloc.fderiv_eq]
    simp
  have hlei := hwd.smul_smooth hχ_cd hfloc hDloc
  have hGsupp : Function.support (fun z => χ z • h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) z)) ⊆ T2 := by
    intro z hz
    refine hχ_supp fun h0 => hz ?_
    change χ z • _ = 0
    rw [h0]
    simp
  have hGxsupp : Function.support (fun z => χ z • D z
      + ((fderiv ℝ χ z) 1) • h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)) z)) ⊆ T2 := by
    intro z hz
    by_contra hzT
    have hzts : z ∉ tsupport χ := fun hc =>
      hzT ((closure_minimal hχ_supp hT2c.isClosed) hc)
    apply hz
    change χ z • D z + ((fderiv ℝ χ z) 1) • _ = 0
    rw [image_eq_zero_of_notMem_tsupport hzts, hχfd0 z hzts]
    simp
  have hGcs := HasCompactSupport.of_support_subset_isCompact hT2c hGsupp
  have hGxcs := HasCompactSupport.of_support_subset_isCompact hT2c hGxsupp
  have hGts : tsupport (fun z => χ z • h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) z))
      ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j) :=
    (closure_minimal hGsupp hT2c.isClosed).trans hT2W
  have hGxts : tsupport (fun z => χ z • D z
      + ((fderiv ℝ χ z) 1) • h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)) z))
      ⊆ A.Φ j '' Metric.ball (A.c j) (2 * A.r j) :=
    (closure_minimal hGxsupp hT2c.isClosed).trans hT2W
  have huniv := hasWeakDirDeriv_univ_of_compactSupport hWopen hGcs hGxcs hGts hGxts hlei
  have hGcont : Continuous (fun z => χ z • h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) z)) := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)
    · exact (ContinuousOn.smul (hχ_cd.continuous.continuousOn) hgcont).continuousAt
        (hWopen.mem_nhds hz)
    · have hzts : z ∉ tsupport χ := fun hc => hz (hχ_ts hc)
      have hloc : (fun z => χ z • h (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j)) z)) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hzts] with y hy
        show χ y • _ = 0
        rw [image_eq_zero_of_notMem_tsupport hy]
        simp
      exact hloc.continuousAt
  have hDT2 : IntegrableOn D T2 volume :=
    hDloc.integrableOn_compact_subset hT2W hT2c
  have hgT2 : IntegrableOn (fun x => h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) x)) T2 volume :=
    hfloc.integrableOn_compact_subset hT2W hT2c
  have hχfdcont : Continuous fun z => (fderiv ℝ χ z) 1 := by
    have h1 : Continuous fun p : ℂ × ℂ => (fderiv ℝ χ p.1) p.2 :=
      hχ_cd.continuous_fderiv_apply (by norm_num)
    exact h1.comp (continuous_id.prodMk continuous_const)
  have hGx1 : IntegrableOn (fun z => χ z • D z) T2 volume :=
    hDT2.continuousOn_smul (hχ_cd.continuous.continuousOn) hT2c
  have hGx2 : IntegrableOn (fun z => ((fderiv ℝ χ z) 1) • h (Function.invFunOn
      (A.Φ j) (Metric.ball (A.c j) (2 * A.r j)) z)) T2 volume :=
    hgT2.continuousOn_smul hχfdcont.continuousOn hT2c
  have hGxint : Integrable (fun z => χ z • D z
      + ((fderiv ℝ χ z) 1) • h (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j)) z)) volume :=
    (integrableOn_iff_integrable_of_support_subset hGxsupp).mp (hGx1.add hGx2)
  refine ⟨fun z => χ z • h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) z),
    fun z => χ z • D z + ((fderiv ℝ χ z) 1) • h (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) z),
    hGcont.locallyIntegrable, hGxint.locallyIntegrable, huniv,
    interior T1, isOpen_interior, hKT1, fun w hw => ?_⟩
  change χ w • _ = _
  rw [hχ_one w (interior_subset hw)]
  simp

/-- **Unconditional chart slicing**: the height-slicing hypothesis of
`sym_hacl_of_chart_slicing`, from the quasiconformal Sobolev regularity alone. -/
theorem sym_chart_slicing {q h hinv : ℂ → ℂ} {κ : ℝ} (A : Atlas q)
    (hqc : IsQCUpper h hinv κ) :
    ∀ j : ℕ, A.active j → ∀ᵐ y : ℝ ∂(volume : Measure ℝ), ∀ a b : ℝ,
      (∀ x ∈ Set.uIcc a b, (x : ℂ) + (y : ℝ) * Complex.I
        ∈ A.Φ j '' Metric.ball (A.c j) (2 * A.r j)) →
      AbsolutelyContinuousOnInterval
        (fun x => h (Function.invFunOn (A.Φ j)
          (Metric.ball (A.c j) (2 * A.r j))
          ((x : ℂ) + (y : ℝ) * Complex.I))) a b :=
  chart_slicing_of_w11loc A hqc.cont
    (fun _ hj _ hK hKW => w11loc_localization A hqc hj hK hKW)

/-- **Leafwise absolute continuity of the quasiconformal image**: the pinned
hypothesis of `sym_hpath_of_acl`, obtained in full from the Reich–Strebel hypotheses. -/
theorem sym_hacl {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      AbsolutelyContinuousOnInterval (fun s => h (σ (s * T))) 0 1 :=
  sym_hacl_of_chart_slicing q hq0 h A (sym_chart_slicing A hqc)

/-- **The flat-path field in full**: almost every regular start point carries the
flat-path structure of the image leaf for every horizon, unconditionally. -/
theorem sym_hpath_full {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)) :=
  sym_hpath_of_acl q A hqc (sym_hacl q hq0 hqc A)

/-- **Transversal regularity along the flow**: for almost every regular start point,
at almost every time the flow point is a regular start point of the rotated
differential. -/
theorem flow_good_neg_ae (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (A : Atlas (q : ℂ → ℂ)) (B : Atlas (qdNeg q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ᵐ t ∂(volume : Measure ℝ), A.flow t z ∈ good (qdNeg q : ℂ → ℂ) B := by
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hN0' : volume ({w : ℂ | ¬ w ∈ good (qdNeg q : ℂ → ℂ) B}
      ∩ {w : ℂ | 0 < w.im}) = 0 := by
    have h0 := ae_iff.mp (good_ae_neg hΓ hcc q hq0 B)
    rwa [Measure.restrict_apply' hUm] at h0
  set N : Set ℂ := toMeasurable volume
    ({w : ℂ | ¬ w ∈ good (qdNeg q : ℂ → ℂ) B} ∩ {w : ℂ | 0 < w.im}) with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact hN0'
  have hsub := subset_toMeasurable volume
    ({w : ℂ | ¬ w ∈ good (qdNeg q : ℂ → ℂ) B} ∩ {w : ℂ | 0 < w.im})
  have hsec : ∀ t : ℝ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      A.flow t z ∉ N := by
    intro t
    rcases lt_trichotomy t 0 with htn | ht0 | htp
    · have hminus : (0 : ℝ) < -t := by linarith
      have hb := flow_preimage_ae q A (mirrorAtlas A)
        (fun z => A.flow (-(-t)) z) hminus
        (fun n z hz => flow_eq_pos_bwd q.holo A hminus hz)
        (fun z hz => good_slegal_bwd q.holo A hminus hz) hNm hN0
      simp only [neg_neg] at hb
      filter_upwards [good_ae hΓ hcc q hq0 A, hb] with z hzg hzb
      exact hzb hzg
    · subst ht0
      have hnotN : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∉ N := by
        refine ae_iff.mpr ?_
        have hset : {a : ℂ | ¬ a ∉ N} = N := by
          ext a
          simp
        rw [hset, Measure.restrict_apply' hUm]
        exact measure_mono_null Set.inter_subset_left hN0
      filter_upwards [hnotN, q.ae_ne_zero hq0, ae_restrict_mem hUm]
        with z hzN hqz hzU
      intro hflowN
      rw [flow_zero A hzU hqz] at hflowN
      exact hzN hflowN
    · have hb := flow_preimage_ae q A A (fun z => A.flow t z) htp
        (fun n z hz => flow_eq_pos_fwd q.holo A htp hz)
        (fun z hz => good_slegal_fwd q.holo A htp hz) hNm hN0
      filter_upwards [good_ae hΓ hcc q hq0 A, hb] with z hzg hzb
      exact hzb hzg
  have hsec0 : ∀ t : ℝ, (volume.restrict {z : ℂ | 0 < z.im})
      {z : ℂ | A.flow t z ∈ N} = 0 := by
    intro t
    have h1 := ae_iff.mp (hsec t)
    have hset : {a : ℂ | ¬ A.flow t a ∉ N} = {a : ℂ | A.flow t a ∈ N} := by
      ext a
      simp
    rwa [hset] at h1
  set S : Set (ℝ × ℂ) := (fun p : ℝ × ℂ => A.flow p.1 p.2) ⁻¹' N with hSdef
  have hSm : MeasurableSet S := A.measurable_flow hNm
  have hprod : ((volume : Measure ℝ).prod
      (volume.restrict {z : ℂ | 0 < z.im})) S = 0 := by
    rw [Measure.prod_apply hSm]
    have hpt : ∀ t : ℝ, (volume.restrict {z : ℂ | 0 < z.im})
        (Prod.mk t ⁻¹' S) = 0 := fun t => hsec0 t
    simp [hpt]
  have hswap : ((volume.restrict {z : ℂ | 0 < z.im}).prod (volume : Measure ℝ))
      {p : ℂ × ℝ | A.flow p.2 p.1 ∈ N} = 0 := by
    have hXm : MeasurableSet {p : ℂ × ℝ | A.flow p.2 p.1 ∈ N} :=
      (A.measurable_flow.comp (measurable_snd.prodMk measurable_fst)) hNm
    rw [← Measure.prod_swap, Measure.map_apply measurable_swap hXm]
    exact hprod
  have hae2 : ∀ᵐ p ∂((volume.restrict {z : ℂ | 0 < z.im}).prod
      (volume : Measure ℝ)), A.flow p.2 p.1 ∉ N := by
    refine ae_iff.mpr ?_
    have hset : {p : ℂ × ℝ | ¬ A.flow p.2 p.1 ∉ N}
        = {p : ℂ × ℝ | A.flow p.2 p.1 ∈ N} := by
      ext p
      simp
    rw [hset]
    exact hswap
  have hae3 := Measure.ae_ae_of_ae_prod hae2
  filter_upwards [hae3] with z hz
  intro hzg
  have hne0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    refine ae_iff.mpr ?_
    have hset : {t : ℝ | ¬ t ≠ 0} = {(0 : ℝ)} := by
      ext t
      simp
    rw [hset]
    exact Real.volume_singleton
  filter_upwards [hz, hne0] with t htN htne
  have him : 0 < (A.flow t z).im := by
    rcases lt_or_gt_of_ne htne with hlt | hgt
    · have h2 := (flow_good_regular q.holo A hzg (by linarith : (0 : ℝ) < -t)).2
      simpa using h2
    · exact (flow_good_regular q.holo A hzg hgt).1
  by_contra hcon
  exact htN (hsub ⟨hcon, him⟩)

/-- **Imaginary segment bound**: in a chart developing the negated differential, the
imaginary displacement of a curve segment is dominated by its horizontal variation. -/
theorem im_segment_variation_lb {q Ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hΨd : DifferentiableOn ℂ Ψ V)
    (hΨsq : ∀ w ∈ V, deriv Ψ w ^ 2 = -(-q w))
    {p : ℝ → ℂ} {α β : ℝ} (hαβ : α < β)
    (hpc : ContinuousOn p (Set.Icc α β))
    (hpac : AbsolutelyContinuousOnInterval p α β)
    (htr : ∀ s ∈ Set.Icc α β, p s ∈ V) :
    ENNReal.ofReal |(Ψ (p β)).im - (Ψ (p α)).im|
      ≤ ∫⁻ s in Set.Icc α β, horizontalDensity q p s := by
  set Φ : ℂ → ℂ := fun w => Complex.I * Ψ w with hΦdef
  have hΦd : DifferentiableOn ℂ Φ V := by
    intro w hw
    exact ((hΨd w hw).const_smul (Complex.I)).congr (fun z _ => by simp [hΦdef]) rfl
  have hΦsq : ∀ w ∈ V, deriv Φ w ^ 2 = -q w := by
    intro w hw
    have hdif : DifferentiableAt ℂ Ψ w := hΨd.differentiableAt (hV.mem_nhds hw)
    have hder : deriv Φ w = Complex.I * deriv Ψ w := by
      rw [hΦdef]
      exact deriv_const_mul _ hdif
    have h1 : deriv Φ w ^ 2 = Complex.I ^ 2 * deriv Ψ w ^ 2 := by
      rw [hder]; ring
    rw [h1, hΨsq w hw, Complex.I_sq]
    ring
  have hre : ∀ z : ℂ, (Φ z).re = -(Ψ z).im := by
    intro z
    rw [hΦdef]
    simp [Complex.mul_re]
  have h2 := segment_variation_lb hV hΦd hΦsq hαβ hpc hpac htr
  rw [hre, hre] at h2
  refine le_trans (le_of_eq ?_) h2
  rw [show -(Ψ (p β)).im - -(Ψ (p α)).im = -((Ψ (p β)).im - (Ψ (p α)).im) by ring,
    abs_neg]

section WindingBricks

open unitInterval

/-- **Nonvanishing factors on a convex carrier do not wind**: the composition of a
closed curve in a convex set with a zero-free continuous function has winding number
zero about the origin. -/
theorem winding_comp_convex_zero {U : Set ℂ} (hU : Convex ℝ U)
    {g : ℂ → ℂ} (hgc : ContinuousOn g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (γ : C(I, ℂ)) (hcl : γ 0 = γ 1) (htr : ∀ t : I, γ t ∈ U) :
    windingNumber ⟨fun t => g (γ t),
      hgc.comp_continuous γ.continuous htr⟩ 0 = 0 := by
  set c : ℂ := γ 0 with hcdef
  have hcU : c ∈ U := htr 0
  have hmem : ∀ p : I × I,
      ((1 - (p.1 : ℝ) : ℝ) : ℂ) * γ p.2 + (((p.1 : ℝ) : ℝ) : ℂ) * c ∈ U := by
    intro p
    have h := hU (htr p.2) hcU (by linarith [p.1.2.2] : (0:ℝ) ≤ 1 - (p.1 : ℝ))
      p.1.2.1 (by ring)
    simpa [Complex.real_smul] using h
  have hHc : Continuous fun p : I × I =>
      ((1 - (p.1 : ℝ) : ℝ) : ℂ) * γ p.2 + (((p.1 : ℝ) : ℝ) : ℂ) * c := by
    refine Continuous.add (Continuous.mul ?_ (γ.continuous.comp continuous_snd))
      (Continuous.mul ?_ continuous_const)
    · exact Complex.continuous_ofReal.comp
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
    · exact Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp continuous_fst)
  set Hfun : I × I → ℂ := fun p =>
    g (((1 - (p.1 : ℝ) : ℝ) : ℂ) * γ p.2 + (((p.1 : ℝ) : ℝ) : ℂ) * c) with hHdef
  have hHfc : Continuous Hfun := hgc.comp_continuous hHc fun p => hmem p
  have hgone : (⟨fun t => g (γ t), hgc.comp_continuous γ.continuous htr⟩
      : C(I, ℂ)) 0 = (⟨fun t => g (γ t), hgc.comp_continuous γ.continuous htr⟩
      : C(I, ℂ)) 1 := by
    change g (γ 0) = g (γ 1)
    rw [← hcdef, hcl]
  have h0I : ((0 : I) : ℝ) = 0 := rfl
  have h1I : ((1 : I) : ℝ) = 1 := rfl
  have hmapzero : ∀ x : I, Hfun (0, x) = g (γ x) := by
    intro x
    simp only [hHdef]
    congr 1
    rw [h0I]
    push_cast
    ring
  have hmapone : ∀ x : I, Hfun (1, x) = g c := by
    intro x
    simp only [hHdef]
    congr 1
    rw [h1I]
    push_cast
    ring
  have hprop : ∀ t : I, ∀ x ∈ ({0, 1} : Set I), Hfun (t, x) = g (γ x) := by
    intro t x hx
    rcases hx with h | h
    · subst h
      show Hfun (t, 0) = g (γ 0)
      simp only [hHdef]
      rw [← hcdef]
      congr 1
      push_cast
      ring
    · rw [Set.mem_singleton_iff] at h
      subst h
      show Hfun (t, 1) = g (γ 1)
      simp only [hHdef]
      rw [← hcl]
      congr 1
      push_cast
      ring
  have hne : ∀ p : I × I, Hfun p ≠ (0 : ℂ) := fun p => hg0 _ (hmem p)
  have hkey := windingNumber_eq_of_homotopicRel (q := (0 : ℂ)) hgone
    (⟨⟨⟨Hfun, hHfc⟩, hmapzero, hmapone⟩, hprop⟩ :
      ContinuousMap.HomotopyRel _ (ContinuousMap.const I (g c)) {0, 1})
    (fun t s => hne (t, s))
  rw [hkey]
  exact windingNumber_const (g c) 0 (hg0 c hcU)

/-- **The factored argument principle**: a closed curve of values factored as a
polynomial part times a windingless part winds about the origin according to the
winding numbers of the curve about the polynomial roots. -/
theorem winding_factored {P : Polynomial ℂ} (hP : P ≠ 0) {g : ℂ → ℂ}
    (γ : C(I, ℂ)) (hcl : γ 0 = γ 1)
    (hgc : Continuous fun t => g (γ t))
    (hPne : ∀ t : I, P.eval (γ t) ≠ 0) (hgne : ∀ t : I, g (γ t) ≠ 0)
    (hgw : windingNumber ⟨fun t => g (γ t), hgc⟩ 0 = 0) :
    windingNumber ⟨fun t => P.eval (γ t) * g (γ t),
        ((P.continuous.comp γ.continuous).mul hgc)⟩ 0
      = (P.roots.map fun ζ => windingNumber γ ζ).sum := by
  have hclP : (⟨fun t => P.eval (γ t), P.continuous.comp γ.continuous⟩ : C(I, ℂ)) 0
      = (⟨fun t => P.eval (γ t), P.continuous.comp γ.continuous⟩ : C(I, ℂ)) 1 := by
    change P.eval (γ 0) = P.eval (γ 1)
    rw [hcl]
  have hclg : (⟨fun t => g (γ t), hgc⟩ : C(I, ℂ)) 0
      = (⟨fun t => g (γ t), hgc⟩ : C(I, ℂ)) 1 := by
    change g (γ 0) = g (γ 1)
    rw [hcl]
  have hmul : (⟨fun t => P.eval (γ t) * g (γ t),
        ((P.continuous.comp γ.continuous).mul hgc)⟩ : C(I, ℂ))
      = (⟨fun t => P.eval (γ t), P.continuous.comp γ.continuous⟩ : C(I, ℂ))
        * ⟨fun t => g (γ t), hgc⟩ := by
    ext t
    rfl
  rw [hmul, windingNumber_mul _ _ hclP hclg hPne hgne, hgw, add_zero,
    windingNumber_polynomial_comp P hP γ hcl hPne]

/-- **Winding nonnegativity from the factorization**: if the curve winds nonnegatively
about every root of the polynomial part, the factored value curve winds nonnegatively
about the origin. -/
theorem winding_factored_nonneg {P : Polynomial ℂ} (hP : P ≠ 0) {g : ℂ → ℂ}
    (γ : C(I, ℂ)) (hcl : γ 0 = γ 1)
    (hgc : Continuous fun t => g (γ t))
    (hPne : ∀ t : I, P.eval (γ t) ≠ 0) (hgne : ∀ t : I, g (γ t) ≠ 0)
    (hgw : windingNumber ⟨fun t => g (γ t), hgc⟩ 0 = 0)
    (hroots : ∀ ζ ∈ P.roots, 0 ≤ windingNumber γ ζ) :
    0 ≤ windingNumber ⟨fun t => P.eval (γ t) * g (γ t),
        ((P.continuous.comp γ.continuous).mul hgc)⟩ 0 := by
  rw [winding_factored hP γ hcl hgc hPne hgne hgw]
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
  exact hroots ζ hζ

/-- **Winding of an explicit exponential**: a curve presented as `exp ∘ L` winds about
the origin by the increment of `L` over the interval, measured in units of `2πi`. -/
theorem winding_of_exp (L : C(I, ℂ)) {m : ℤ}
    (hm : L 1 - L 0 = 2 * Real.pi * Complex.I * m) :
    windingNumber ⟨fun t => Complex.exp (L t),
      Complex.continuous_exp.comp L.continuous⟩ 0 = m := by
  set γ : C(I, ℂ) := ⟨fun t => Complex.exp (L t),
    Complex.continuous_exp.comp L.continuous⟩ with hγdef
  have hcl : γ 0 = γ 1 := by
    change Complex.exp (L 0) = Complex.exp (L 1)
    have h1 : L 1 = L 0 + 2 * Real.pi * Complex.I * m := by
      linear_combination hm
    rw [h1, Complex.exp_add]
    have h2 : Complex.exp (2 * Real.pi * Complex.I * m) = 1 := by
      rw [show (2 : ℂ) * Real.pi * Complex.I * m = m * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h2, mul_one]
  have hne : ∀ t : I, γ t ≠ (0 : ℂ) := fun t => Complex.exp_ne_zero _
  have hlift : IsLogLiftOf L (shiftedCurve γ 0) := by
    intro t
    change Complex.exp (L t) = shiftedCurve γ 0 t
    simp [shiftedCurve, hγdef]
  have hspec := windingNumber_spec hcl hne hlift
  rw [hm] at hspec
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have := mul_left_cancel₀ hπ hspec
  exact_mod_cast this.symm

/-- **The product count**: if a closed nonvanishing curve times the square of a closed
nonvanishing derivative loop is an explicit exponential, the winding of the curve plus
twice the winding of the loop equals the exponent increment in units of `2πi`. -/
theorem winding_product_exp {A d : C(I, ℂ)} (hclA : A 0 = A 1) (hcld : d 0 = d 1)
    (hAne : ∀ t : I, A t ≠ 0) (hdne : ∀ t : I, d t ≠ 0) {L : C(I, ℂ)} {m : ℤ}
    (hexp : ∀ t : I, A t * d t ^ 2 = Complex.exp (L t))
    (hm : L 1 - L 0 = 2 * Real.pi * Complex.I * m) :
    windingNumber A 0 + 2 * windingNumber d 0 = m := by
  have hprod : (A * (d * d) : C(I, ℂ))
      = ⟨fun t => Complex.exp (L t), Complex.continuous_exp.comp L.continuous⟩ := by
    ext t
    change A t * (d t * d t) = Complex.exp (L t)
    rw [← hexp t]
    ring
  have hcldd : (d * d : C(I, ℂ)) 0 = (d * d) 1 := by
    change d 0 * d 0 = d 1 * d 1
    rw [hcld]
  have hddne : ∀ t : I, (d * d : C(I, ℂ)) t ≠ 0 :=
    fun t => mul_ne_zero (hdne t) (hdne t)
  have h1 : windingNumber (A * (d * d)) 0
      = windingNumber A 0 + (windingNumber d 0 + windingNumber d 0) := by
    rw [windingNumber_mul A (d * d) hclA hcldd hAne hddne,
      windingNumber_mul d d hcld hcld hdne hdne]
  have h2 : windingNumber (A * (d * d)) 0 = m := by
    rw [hprod]
    exact winding_of_exp L hm
  rw [h1] at h2
  linarith

/-- The open upper half plane is convex. -/
theorem convex_upperHalf : Convex ℝ {z : ℂ | 0 < z.im} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    simp [Complex.add_im]
  rw [him]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · have h1 : 0 < a * x.im := mul_pos ha' hx
    have h2 : 0 ≤ b * y.im := mul_nonneg hb hy.le
    linarith
  · have hb1 : b = 1 := by linarith
    rw [← ha', hb1]
    simpa using hy

/-- **Finiteness of zeros on compacta**: a function holomorphic on the upper half plane
and not identically zero has finitely many zeros in any compact subset. -/
theorem zeros_finite_in_compact {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ {z : ℂ | 0 < z.im}) :
    {z ∈ C | q z = 0}.Finite := by
  by_contra hinf
  have hS : Set.Infinite {z ∈ C | q z = 0} := hinf
  obtain ⟨x, hxC, hacc⟩ := hS.exists_accPt_of_subset_isCompact hC (Set.sep_subset _ _)
  have hfreq : ∃ᶠ z in nhdsWithin x {x}ᶜ, q z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hacc
    exact hacc.mono fun y hy => hy.2
  have hHopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ q {z : ℂ | 0 < z.im} := hq.analyticOnNhd hHopen
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    convex_upperHalf.isPreconnected (hCH hxC) hfreq
  obtain ⟨z₀, hz₀, hne⟩ := hq0
  exact hne (by simpa using hzero hz₀)

/-- **The rectangle hull**: a nonempty compact subset of the upper half plane lies in a
convex open set whose closure is a compact subset of the upper half plane. -/
theorem rectangle_hull {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKH : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ K ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ {z : ℂ | 0 < z.im} := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨w, hwK, hwmin⟩ := hK.exists_isMinOn hKne Complex.continuous_im.continuousOn
  set m : ℝ := w.im with hmdef
  have hm : 0 < m := hKH hwK
  have hRw : ‖w‖ ≤ R := by simpa using hR hwK
  have hmR : m ≤ R :=
    le_trans (le_trans (le_abs_self _) (Complex.abs_im_le_norm w)) hRw
  have hR0 : 0 ≤ R := le_trans (norm_nonneg w) hRw
  set U : Set ℂ := Complex.re ⁻¹' Set.Ioo (-(R + 1)) (R + 1)
    ∩ Complex.im ⁻¹' Set.Ioo (m / 2) (R + 1) with hUdef
  have hUopen : IsOpen U :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  have hUconv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    constructor
    · have := (convex_Ioo (-(R + 1)) (R + 1)) hx1 hy1 ha hb hab
      simpa [Complex.add_re, Complex.smul_re, smul_eq_mul] using this
    · have := (convex_Ioo (m / 2) (R + 1)) hx2 hy2 ha hb hab
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using this
  have hKU : K ⊆ U := by
    intro z hz
    have hzn : ‖z‖ ≤ R := by simpa using hR hz
    have hre : |z.re| ≤ R := le_trans (Complex.abs_re_le_norm z) hzn
    have him : |z.im| ≤ R := le_trans (Complex.abs_im_le_norm z) hzn
    rw [abs_le] at hre him
    refine ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, ?_, by linarith [him.2]⟩
    have hzm : m ≤ z.im := isMinOn_iff.mp hwmin z hz
    linarith
  have hcls : closure U ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have h1 : closure U ⊆ Complex.im ⁻¹' closure (Set.Ioo (m / 2) (R + 1)) := by
      refine le_trans (closure_mono Set.inter_subset_right) ?_
      exact Complex.continuous_im.closure_preimage_subset _
    have h2 := h1 hz
    rw [closure_Ioo (by intro h; linarith [h] : (m / 2 : ℝ) ≠ R + 1)] at h2
    have := h2.1
    change (0 : ℝ) < z.im
    linarith
  have hbdd : Bornology.IsBounded U := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall
      (x := (0 : ℂ)) (r := 2 * R + 2)) ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im z) ?_
    rw [Set.mem_preimage, Set.mem_Ioo] at hz1 hz2
    have h1 : |z.re| ≤ R + 1 := abs_le.mpr ⟨hz1.1.le, hz1.2.le⟩
    have h2 : |z.im| ≤ R + 1 := by
      refine abs_le.mpr ⟨?_, hz2.2.le⟩
      have := hz2.1
      linarith
    linarith
  exact ⟨U, hUopen, hUconv, hKU,
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbdd.closure, hcls⟩

/-- **Peeling one zero**: a holomorphic function on the upper half plane, not
identically zero, factors at any zero `w` as `(z - w) ^ n` times a holomorphic function
that is nonzero at `w`, with `n` positive and the identity valid off the real axis. -/
theorem peel_zero {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {w : ℂ} (hw : 0 < w.im) (hqw : q w = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ q₁ : ℂ → ℂ,
      DifferentiableOn ℂ q₁ {z : ℂ | 0 < z.im} ∧ q₁ w ≠ 0 ∧
      ∀ z : ℂ, q z = (z - w) ^ n * q₁ z := by
  have hHopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ q {z : ℂ | 0 < z.im} := hq.analyticOnNhd hHopen
  have hanw : AnalyticAt ℂ q w := han w hw
  have horder : analyticOrderAt q w ≠ ⊤ := by
    intro htop
    have hev : q =ᶠ[nhds w] 0 := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      convex_upperHalf.isPreconnected hw hev
    obtain ⟨z₀, hz₀, hne⟩ := hq0
    exact hne (by simpa using hzero hz₀)
  obtain ⟨g, hgan, hgw, hev⟩ := hanw.analyticOrderAt_ne_top.mp horder
  set n : ℕ := analyticOrderNatAt q w with hndef
  have hn0 : n ≠ 0 := by
    intro h
    rcases ENat.toNat_eq_zero.mp h with h0 | h0
    · exact (hanw.analyticOrderAt_ne_zero.mpr hqw) h0
    · exact horder h0
  set q₁ : ℂ → ℂ := fun z => if z = w then g w else q z / (z - w) ^ n with hq₁def
  have hq₁w : q₁ w ≠ 0 := by
    rw [hq₁def]
    simpa using hgw
  have hglob : ∀ z : ℂ, q z = (z - w) ^ n * q₁ z := by
    intro z
    by_cases hzw : z = w
    · subst hzw
      rw [hqw, sub_self, zero_pow hn0, zero_mul]
    · rw [hq₁def]
      simp only [if_neg hzw]
      rw [mul_div_cancel₀]
      exact pow_ne_zero _ (sub_ne_zero.mpr hzw)
  have hq₁ev : q₁ =ᶠ[nhds w] g := by
    filter_upwards [hev] with z hz
    by_cases hzw : z = w
    · subst hzw
      rw [hq₁def]
      simp
    · rw [hq₁def]
      simp only [if_neg hzw]
      rw [hz, smul_eq_mul, mul_div_cancel_left₀]
      exact pow_ne_zero _ (sub_ne_zero.mpr hzw)
  have hq₁d : DifferentiableOn ℂ q₁ {z : ℂ | 0 < z.im} := by
    intro z hz
    by_cases hzw : z = w
    · subst hzw
      exact (hgan.differentiableAt.congr_of_eventuallyEq
        hq₁ev).differentiableWithinAt
    · have hopen : IsOpen ({z : ℂ | 0 < z.im} ∩ {w}ᶜ) :=
        hHopen.inter (isOpen_compl_singleton)
      have hd : DifferentiableAt ℂ (fun u => q u / (u - w) ^ n) z := by
        refine DifferentiableAt.div (hq.differentiableAt (hHopen.mem_nhds hz)) ?_ ?_
        · exact ((differentiableAt_id.sub_const w).pow n)
        · exact pow_ne_zero _ (sub_ne_zero.mpr hzw)
      have hcongr : q₁ =ᶠ[nhds z] fun u => q u / (u - w) ^ n := by
        filter_upwards [isOpen_compl_singleton.mem_nhds
          (by simpa using hzw : z ∈ ({w} : Set ℂ)ᶜ)] with u hu
        rw [hq₁def]
        exact if_neg hu
      exact (hd.congr_of_eventuallyEq hcongr).differentiableWithinAt
  exact ⟨n, Nat.pos_of_ne_zero hn0, q₁, hq₁d, hq₁w, hglob⟩

/-- **Factorization through the zeros**: a holomorphic function on the upper half
plane, not identically zero, with finitely many zeros in a subset `U` of the half
plane, factors on the half plane as a polynomial rooted in `U` times a holomorphic
function without zeros in `U`. -/
theorem factor_zeros {U : Set ℂ} (hUH : U ⊆ {z : ℂ | 0 < z.im}) :
    ∀ (N : ℕ) (q : ℂ → ℂ), DifferentiableOn ℂ q {z : ℂ | 0 < z.im} →
    (∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0) →
    ∀ hfin : {z ∈ U | q z = 0}.Finite, hfin.toFinset.card = N →
    ∃ P : Polynomial ℂ, P ≠ 0 ∧ (∀ ζ ∈ P.roots, ζ ∈ U) ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {z : ℂ | 0 < z.im} ∧
        (∀ z ∈ U, g z ≠ 0) ∧ ∀ z ∈ U, q z = Polynomial.eval z P * g z := by
  intro N
  induction N with
  | zero =>
    intro q hq hq0 hfin hcard
    have hempty : {z ∈ U | q z = 0} = ∅ := by
      rw [← Set.Finite.toFinset_eq_empty (h := hfin)]
      exact Finset.card_eq_zero.mp hcard
    refine ⟨1, one_ne_zero, by simp, q, hq, ?_, ?_⟩
    · intro z hz h0
      have : z ∈ {z ∈ U | q z = 0} := ⟨hz, h0⟩
      rw [hempty] at this
      exact this
    · intro z _
      rw [Polynomial.eval_one, one_mul]
  | succ N ih =>
    intro q hq hq0 hfin hcard
    have hne : hfin.toFinset.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨w, hwmem⟩ := hne
    rw [Set.Finite.mem_toFinset] at hwmem
    obtain ⟨hwU, hqw⟩ := hwmem
    obtain ⟨n, hn, q₁, hq₁d, hq₁w, hglob⟩ :=
      peel_zero hq hq0 (hUH hwU) hqw
    have hset : {z ∈ U | q₁ z = 0} = {z ∈ U | q z = 0} \ {w} := by
      ext z
      simp only [Set.mem_sep_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hzU, hz0⟩
        refine ⟨⟨hzU, by rw [hglob z, hz0, mul_zero]⟩, ?_⟩
        intro hzw
        rw [hzw] at hz0
        exact hq₁w hz0
      · rintro ⟨⟨hzU, hz0⟩, hzw⟩
        refine ⟨hzU, ?_⟩
        have h1 := hglob z
        rw [hz0] at h1
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact absurd h (pow_ne_zero _ (sub_ne_zero.mpr hzw))
        · exact h
    have hfin₁ : {z ∈ U | q₁ z = 0}.Finite := by
      rw [hset]
      exact hfin.sdiff
    have hcard₁ : hfin₁.toFinset.card = N := by
      have h1 : hfin₁.toFinset = hfin.toFinset.erase w := by
        ext z
        rw [Set.Finite.mem_toFinset, Finset.mem_erase, Set.Finite.mem_toFinset, hset]
        simp only [Set.mem_sdiff, Set.mem_singleton_iff]
        tauto
      have hwmem' : w ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hwU, hqw⟩
      rw [h1, Finset.card_erase_of_mem hwmem', hcard]
      omega
    obtain ⟨P₁, hP₁ne, hP₁roots, g, hgd, hgne, hgfac⟩ :=
      ih q₁ hq₁d ⟨w, hUH hwU, hq₁w⟩ hfin₁ hcard₁
    refine ⟨(Polynomial.X - Polynomial.C w) ^ n * P₁,
      mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero w)) hP₁ne, ?_, g, hgd,
      hgne, ?_⟩
    · intro ζ hζ
      rw [Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero w)) hP₁ne),
        Multiset.mem_add] at hζ
      rcases hζ with h | h
      · rw [Polynomial.roots_pow, Multiset.mem_nsmul, Polynomial.roots_X_sub_C,
          Multiset.mem_singleton] at h
        · rw [h.2]
          exact hwU
      · exact hP₁roots ζ h
    · intro z hzU
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, hglob z, hgfac z hzU]
      ring

/-- **Nonnegative winding of holomorphic value curves**: along a closed curve in a
convex subset of the upper half plane that winds nonnegatively about every point off
its track, the values of a holomorphic function without zeros on the track wind
nonnegatively about the origin. -/
theorem winding_holo_nonneg {q : ℂ → ℂ} {U : Set ℂ} (hUconv : Convex ℝ U)
    (hUH : U ⊆ {z : ℂ | 0 < z.im})
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hfin : {z ∈ U | q z = 0}.Finite)
    (γ : C(I, ℂ)) (hcl : γ 0 = γ 1) (htr : ∀ t : I, γ t ∈ U)
    (hqne : ∀ t : I, q (γ t) ≠ 0)
    (hnn : ∀ ζ : ℂ, (∀ t : I, γ t ≠ ζ) → 0 ≤ windingNumber γ ζ) :
    0 ≤ windingNumber ⟨fun t => q (γ t),
      hq.continuousOn.comp_continuous γ.continuous fun t => hUH (htr t)⟩ 0 := by
  obtain ⟨P, hPne, hProots, g, hgd, hgne, hgfac⟩ :=
    factor_zeros hUH hfin.toFinset.card q hq hq0 hfin rfl
  have hgcont : Continuous fun t => g (γ t) :=
    (hgd.continuousOn.mono hUH).comp_continuous γ.continuous htr
  have hPtr : ∀ t : I, Polynomial.eval (γ t) P ≠ 0 := by
    intro t h0
    refine hqne t ?_
    rw [hgfac _ (htr t), h0, zero_mul]
  have hgtr : ∀ t : I, g (γ t) ≠ 0 := fun t => hgne _ (htr t)
  have hgw : windingNumber ⟨fun t => g (γ t),
      (hgd.continuousOn.mono hUH).comp_continuous γ.continuous htr⟩ 0 = 0 :=
    winding_comp_convex_zero hUconv (hgd.continuousOn.mono hUH) hgne γ hcl htr
  have hroots : ∀ ζ ∈ P.roots, 0 ≤ windingNumber γ ζ := by
    intro ζ hζ
    refine hnn ζ fun t ht => ?_
    refine hqne t ?_
    rw [hgfac _ (htr t), ht, (Polynomial.isRoot_of_mem_roots hζ), zero_mul]
  have heq : (⟨fun t => q (γ t),
        hq.continuousOn.comp_continuous γ.continuous fun t => hUH (htr t)⟩ : C(I, ℂ))
      = ⟨fun t => Polynomial.eval (γ t) P * g (γ t),
        ((P.continuous.comp γ.continuous).mul hgcont)⟩ := by
    ext t
    exact hgfac _ (htr t)
  rw [heq]
  exact winding_factored_nonneg hPne γ hcl hgcont hPtr hgtr hgw hroots

/-- Four curves traversed on the four quarters of the interval. -/
noncomputable def quarterConcat (f₀ f₁ f₂ f₃ : C(I, ℂ)) : ℝ → ℂ := fun t =>
  if t ≤ 1 / 4 then f₀ (Set.projIcc 0 1 zero_le_one (4 * t))
  else if t ≤ 1 / 2 then f₁ (Set.projIcc 0 1 zero_le_one (4 * t - 1))
  else if t ≤ 3 / 4 then f₂ (Set.projIcc 0 1 zero_le_one (4 * t - 2))
  else f₃ (Set.projIcc 0 1 zero_le_one (4 * t - 3))

/-- The quarter concatenation of junction-matched pieces is continuous. -/
theorem quarterConcat_continuous (f₀ f₁ f₂ f₃ : C(I, ℂ))
    (h01 : f₀ 1 = f₁ 0) (h12 : f₁ 1 = f₂ 0) (h23 : f₂ 1 = f₃ 0) :
    Continuous (quarterConcat f₀ f₁ f₂ f₃) := by
  have hp : ∀ (f : C(I, ℂ)) (c : ℝ), Continuous fun t : ℝ =>
      f (Set.projIcc 0 1 zero_le_one (4 * t - c)) := by
    intro f c
    exact f.continuous.comp (continuous_projIcc.comp
      ((continuous_const.mul continuous_id).sub continuous_const))
  have hp0 : Continuous fun t : ℝ => f₀ (Set.projIcc 0 1 zero_le_one (4 * t)) := by
    have := hp f₀ 0
    simpa using this
  unfold quarterConcat
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
  · exact hp0
  · refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · exact hp f₁ 1
    · refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact hp f₂ 2
      · exact hp f₃ 3
      · intro t ht
        subst ht
        norm_num
        exact h23
    · intro t ht
      subst ht
      norm_num
      exact h12
  · intro t ht
    subst ht
    norm_num
    exact h01

end WindingBricks

end RiemannDynamics

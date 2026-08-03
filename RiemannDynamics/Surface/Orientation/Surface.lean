/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.Orientation.Degree

/-!
# Orientation on charted surfaces

Chart representatives of surface homeomorphisms, orientation preservation for
homeomorphisms of a charted surface, oriented atlases, and the groupoid laws
of orientation preservation.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval

namespace RiemannDynamics

/-! ## Orientation on charted surfaces -/

/-- The chart representative of a surface self-homeomorphism at a point:
read `f` in the preferred charts at `p` and `f p`. -/
noncomputable def homeoChartRep {S : Type*} [TopologicalSpace S]
    [ChartedSpace ℂ S] (f : S ≃ₜ S) (p : S) : OpenPartialHomeomorph ℂ ℂ :=
  (chartAt ℂ p).symm.trans
    ((Homeomorph.toOpenPartialHomeomorph f).trans (chartAt ℂ (f p)))

/-- A surface self-homeomorphism preserves orientation when each chart
representative does, at every point. -/
def _root_.Homeomorph.IsOrientationPreserving {S : Type*} [TopologicalSpace S]
    [ChartedSpace ℂ S] (f : S ≃ₜ S) : Prop :=
  ∀ p : S, IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p)

/-- A charted space has an oriented atlas when every atlas transition
preserves orientation at every point of its source. -/
def HasOrientedAtlas (S : Type*) [TopologicalSpace S] [ChartedSpace ℂ S] : Prop :=
  ∀ e ∈ atlas ℂ S, ∀ e' ∈ atlas ℂ S, ∀ z ∈ (e.symm.trans e').source,
    IsOrientationPreservingAt (e.symm.trans e') z

/-- The identity preserves orientation. -/
theorem _root_.Homeomorph.IsOrientationPreserving.refl (S : Type*) [TopologicalSpace S]
    [ChartedSpace ℂ S] : (Homeomorph.refl S).IsOrientationPreserving := by
  intro p
  have hsrcE : ∀ (F : S ≃ₜ S) (a : S) (w : ℂ),
      w ∈ (homeoChartRep F a).source ↔
        w ∈ (chartAt ℂ a).target ∧ F ((chartAt ℂ a).symm w) ∈ (chartAt ℂ (F a)).source := by
    intro F a w
    unfold homeoChartRep
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hEq : Set.EqOn (homeoChartRep (Homeomorph.refl S) p) id
      (homeoChartRep (Homeomorph.refl S) p).source := by
    intro w hw
    have h1 := ((hsrcE (Homeomorph.refl S) p w).mp hw).1
    exact (chartAt ℂ p).right_inv h1
  have hmem : chartAt ℂ p p ∈ (homeoChartRep (Homeomorph.refl S) p).source := by
    rw [hsrcE]
    refine ⟨(chartAt ℂ p).map_source (mem_chart_source ℂ p), ?_⟩
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact mem_chart_source ℂ p
  exact isOrientationPreservingAt_id hEq
    (homeoChartRep (Homeomorph.refl S) p).open_source hmem subset_rfl

/-- Orientation-preservation is closed under composition: the chart
representative of `f.trans g` at `p` agrees near the point with the
composite of the representatives of `f` at `p` and `g` at `f p`, which share
the middle chart. -/
theorem _root_.Homeomorph.IsOrientationPreserving.trans {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S] {f g : S ≃ₜ S}
    (hf : f.IsOrientationPreserving) (hg : g.IsOrientationPreserving) :
    (f.trans g).IsOrientationPreserving := by
  intro p
  have hsrcE : ∀ (F : S ≃ₜ S) (a : S) (w : ℂ),
      w ∈ (homeoChartRep F a).source ↔
        w ∈ (chartAt ℂ a).target ∧ F ((chartAt ℂ a).symm w) ∈ (chartAt ℂ (F a)).source := by
    intro F a w
    unfold homeoChartRep
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hbase : ∀ (F : S ≃ₜ S) (a : S),
      chartAt ℂ a a ∈ (homeoChartRep F a).source := by
    intro F a
    rw [hsrcE]
    refine ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), ?_⟩
    rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
    exact mem_chart_source ℂ (F a)
  have h1 := hf p
  have h2 := hg (f p)
  have hpt : homeoChartRep f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
    change chartAt ℂ (f p) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) = chartAt ℂ (f p) (f p)
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  rw [← hpt] at h2
  have h12 := isOrientationPreservingAt_trans h1 h2
  have hUopen : IsOpen (((homeoChartRep f p).trans (homeoChartRep g (f p))).source ∩
      (homeoChartRep (f.trans g) p).source) :=
    ((homeoChartRep f p).trans (homeoChartRep g (f p))).open_source.inter
      (homeoChartRep (f.trans g) p).open_source
  have hEq : Set.EqOn ((homeoChartRep f p).trans (homeoChartRep g (f p)))
      (homeoChartRep (f.trans g) p)
      (((homeoChartRep f p).trans (homeoChartRep g (f p))).source ∩
        (homeoChartRep (f.trans g) p).source) := by
    intro w hw
    obtain ⟨hwC, -⟩ := hw
    rw [OpenPartialHomeomorph.trans_source] at hwC
    obtain ⟨hw1, -⟩ := hwC
    have hx : f ((chartAt ℂ p).symm w) ∈ (chartAt ℂ (f p)).source :=
      ((hsrcE f p w).mp hw1).2
    change chartAt ℂ (g (f p)) (g ((chartAt ℂ (f p)).symm
        (chartAt ℂ (f p) (f ((chartAt ℂ p).symm w))))) =
      chartAt ℂ ((f.trans g) p) ((f.trans g) ((chartAt ℂ p).symm w))
    rw [(chartAt ℂ (f p)).left_inv hx]
    rfl
  have hz : chartAt ℂ p p ∈
      (((homeoChartRep f p).trans (homeoChartRep g (f p))).source ∩
        (homeoChartRep (f.trans g) p).source) := by
    constructor
    · rw [OpenPartialHomeomorph.trans_source]
      refine ⟨hbase f p, ?_⟩
      rw [Set.mem_preimage, hpt]
      exact hbase g (f p)
    · exact hbase (f.trans g) p
  exact (isOrientationPreservingAt_congr hEq hUopen hz
    Set.inter_subset_left Set.inter_subset_right).mp h12

/-- On a surface with an oriented atlas, orientation-preservation is closed
under inversion. -/
theorem _root_.Homeomorph.IsOrientationPreserving.symm {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S] (hS : HasOrientedAtlas S)
    {f : S ≃ₜ S} (hf : f.IsOrientationPreserving) :
    f.symm.IsOrientationPreserving := by
  have _ := hS
  intro q
  have hsrcE : ∀ (F : S ≃ₜ S) (a : S) (w : ℂ),
      w ∈ (homeoChartRep F a).source ↔
        w ∈ (chartAt ℂ a).target ∧ F ((chartAt ℂ a).symm w) ∈ (chartAt ℂ (F a)).source := by
    intro F a w
    unfold homeoChartRep
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hbase : ∀ (F : S ≃ₜ S) (a : S),
      chartAt ℂ a a ∈ (homeoChartRep F a).source := by
    intro F a
    rw [hsrcE]
    refine ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), ?_⟩
    rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
    exact mem_chart_source ℂ (F a)
  have h1 := hf (f.symm q)
  have h2 := isOrientationPreservingAt_symm h1
  have hfp : f (f.symm q) = q := f.apply_symm_apply q
  have hpt : homeoChartRep f (f.symm q) (chartAt ℂ (f.symm q) (f.symm q)) =
      chartAt ℂ q q := by
    change chartAt ℂ (f (f.symm q))
      (f ((chartAt ℂ (f.symm q)).symm (chartAt ℂ (f.symm q) (f.symm q)))) = chartAt ℂ q q
    rw [(chartAt ℂ (f.symm q)).left_inv (mem_chart_source ℂ (f.symm q)), hfp]
  rw [hpt] at h2
  have hchart : chartAt ℂ (f (f.symm q)) = chartAt ℂ q := by rw [hfp]
  have hUopen : IsOpen ((homeoChartRep f (f.symm q)).symm.source ∩
      (homeoChartRep f.symm q).source) :=
    (homeoChartRep f (f.symm q)).symm.open_source.inter
      (homeoChartRep f.symm q).open_source
  have hEq : Set.EqOn (homeoChartRep f (f.symm q)).symm (homeoChartRep f.symm q)
      ((homeoChartRep f (f.symm q)).symm.source ∩ (homeoChartRep f.symm q).source) := by
    intro w _
    change chartAt ℂ (f.symm q) (f.symm ((chartAt ℂ (f (f.symm q))).symm w)) =
      chartAt ℂ (f.symm q) (f.symm ((chartAt ℂ q).symm w))
    rw [hchart]
  have hz : chartAt ℂ q q ∈
      ((homeoChartRep f (f.symm q)).symm.source ∩ (homeoChartRep f.symm q).source) := by
    constructor
    · rw [OpenPartialHomeomorph.symm_source, ← hpt]
      exact (homeoChartRep f (f.symm q)).map_source (hbase f (f.symm q))
    · exact hbase f.symm q
  exact (isOrientationPreservingAt_congr hEq hUopen hz
    Set.inter_subset_left Set.inter_subset_right).mp h2

/-- The genus surface has an oriented atlas: its transitions are analytic
with nonvanishing derivative, hence of winding degree `1`. -/
theorem hasOrientedAtlas_genusSurface (g : ℕ) [NeZero g] :
    HasOrientedAtlas (GenusSurface g) := by
  intro e he e' he' z hz
  obtain ⟨hA, hd⟩ := transition_analyticAt g e he e' he' z hz
  exact isOrientationPreservingAt_of_analyticAt hA hd (fun w _ => rfl)
    (e.symm.trans e').open_source hz subset_rfl

/-- On a connected surface with oriented atlas, orientation-preservation at
one point propagates to all points: the locus of orientation-preservation
and its complement are both open. -/
theorem isOrientationPreserving_of_isOrientationPreservingAt_point {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S] [ConnectedSpace S]
    (h : HasOrientedAtlas S) (f : S ≃ₜ S) (p₀ : S)
    (hp : IsOrientationPreservingAt (homeoChartRep f p₀) (chartAt ℂ p₀ p₀)) :
    f.IsOrientationPreserving := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  -- source membership characterizations
  have hsrcT : ∀ (a b : OpenPartialHomeomorph S ℂ) (w : ℂ),
      w ∈ (a.symm.trans b).source ↔ w ∈ a.target ∧ a.symm w ∈ b.source := by
    intro a b w
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact Iff.rfl
  have hsrcE : ∀ (c d : OpenPartialHomeomorph S ℂ) (w : ℂ),
      w ∈ (c.symm.trans (f.toOpenPartialHomeomorph.trans d)).source ↔
        w ∈ c.target ∧ f (c.symm w) ∈ d.source := by
    intro c d w
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hbase : ∀ (a : S), chartAt ℂ a a ∈ (homeoChartRep f a).source := by
    intro a
    exact (hsrcE (chartAt ℂ a) (chartAt ℂ (f a)) (chartAt ℂ a a)).mpr
      ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), by
        rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
        exact mem_chart_source ℂ (f a)⟩
  -- one-sided chart transport through oriented transitions
  have hmove : ∀ c c' d d' : OpenPartialHomeomorph S ℂ, c ∈ atlas ℂ S → c' ∈ atlas ℂ S →
      d ∈ atlas ℂ S → d' ∈ atlas ℂ S → ∀ q : S, q ∈ c.source → q ∈ c'.source →
      f q ∈ d.source → f q ∈ d'.source →
      IsOrientationPreservingAt (c.symm.trans (f.toOpenPartialHomeomorph.trans d)) (c q) →
      IsOrientationPreservingAt (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')) (c' q) := by
    intro c c' d d' hc hc' hd hd' q hqc hqc' hfd hfd' hE
    have hτ₁mem : c' q ∈ (c'.symm.trans c).source := by
      rw [hsrcT]
      refine ⟨c'.map_source hqc', ?_⟩
      rw [c'.left_inv hqc']
      exact hqc
    have hτ₁ : IsOrientationPreservingAt (c'.symm.trans c) (c' q) := h c' hc' c hc _ hτ₁mem
    have hτ₁val : (c'.symm.trans c) (c' q) = c q := by
      change c (c'.symm (c' q)) = c q
      rw [c'.left_inv hqc']
    rw [← hτ₁val] at hE
    have hstep1 := isOrientationPreservingAt_trans hτ₁ hE
    have hτ₂mem : d (f q) ∈ (d.symm.trans d').source := by
      rw [hsrcT]
      refine ⟨d.map_source hfd, ?_⟩
      rw [d.left_inv hfd]
      exact hfd'
    have hτ₂ : IsOrientationPreservingAt (d.symm.trans d') (d (f q)) := h d hd d' hd' _ hτ₂mem
    have hval2 : ((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))) (c' q) = d (f q) := by
      change (c.symm.trans (f.toOpenPartialHomeomorph.trans d)) ((c'.symm.trans c) (c' q))
        = d (f q)
      rw [hτ₁val]
      change d (f (c.symm (c q))) = d (f q)
      rw [c.left_inv hqc]
    rw [← hval2] at hτ₂
    have hstep2 := isOrientationPreservingAt_trans hstep1 hτ₂
    have hUopen : IsOpen ((((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).source) :=
      (((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans
          (d.symm.trans d')).open_source.inter
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).open_source
    have hEq : Set.EqOn (((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d'))
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d'))
        ((((c'.symm.trans c).trans
          (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
          (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).source) := by
      intro w hw
      obtain ⟨hwC, -⟩ := hw
      rw [OpenPartialHomeomorph.trans_source] at hwC
      obtain ⟨hwC1, -⟩ := hwC
      rw [OpenPartialHomeomorph.trans_source] at hwC1
      obtain ⟨hw1, hw2⟩ := hwC1
      have hw1' := (hsrcT c' c w).mp hw1
      have hw2' : (c'.symm.trans c) w
          ∈ (c.symm.trans (f.toOpenPartialHomeomorph.trans d)).source := hw2
      have hw2'' := (hsrcE c d _).mp hw2'
      have hcan : c.symm ((c'.symm.trans c) w) = c'.symm w := by
        change c.symm (c (c'.symm w)) = c'.symm w
        exact c.left_inv hw1'.2
      have hfd2 : f (c'.symm w) ∈ d.source := by
        rw [← hcan]
        exact hw2''.2
      change d' (d.symm (d (f (c.symm (c (c'.symm w)))))) = d' (f (c'.symm w))
      rw [c.left_inv hw1'.2, d.left_inv hfd2]
    have hzmem : c' q ∈ ((((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).source) := by
      constructor
      · rw [OpenPartialHomeomorph.trans_source]
        constructor
        · rw [OpenPartialHomeomorph.trans_source]
          refine ⟨hτ₁mem, ?_⟩
          rw [Set.mem_preimage, hτ₁val, hsrcE]
          refine ⟨c.map_source hqc, ?_⟩
          rw [c.left_inv hqc]
          exact hfd
        · rw [Set.mem_preimage, hval2]
          exact hτ₂mem
      · rw [hsrcE]
        refine ⟨c'.map_source hqc', ?_⟩
        rw [c'.left_inv hqc']
        exact hfd'
    exact (isOrientationPreservingAt_congr hEq hUopen hzmem
      Set.inter_subset_left Set.inter_subset_right).mp hstep2
  -- winding number of the conjugated curve
  have hconj : ∀ (γ γc : C(I, ℂ)) (q : ℂ), γ 0 = γ 1 → (∀ t, γ t ≠ q) →
      (∀ t, γc t = (starRingEnd ℂ) (γ t)) →
      windingNumber γc ((starRingEnd ℂ) q) = - windingNumber γ q := by
    intro γ γc q hcl hne hcapp
    have hsub_ne : ∀ t : I, shiftedCurve γ q t ≠ 0 := by
      intro t
      have happ : shiftedCurve γ q t = γ t - q := by simp [shiftedCurve]
      rw [happ]
      exact sub_ne_zero.mpr (hne t)
    obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ q) hsub_ne
    have hspec := windingNumber_spec hcl hne hL
    obtain ⟨Lc, hLcapp⟩ : ∃ Lc : C(I, ℂ), ∀ t : I, Lc t = (starRingEnd ℂ) (L t) :=
      ⟨⟨fun t => (starRingEnd ℂ) (L t), by fun_prop⟩, fun t => rfl⟩
    have hclc : γc 0 = γc 1 := by rw [hcapp 0, hcapp 1, hcl]
    have hnec : ∀ t : I, γc t ≠ (starRingEnd ℂ) q := by
      intro t hct
      rw [hcapp t] at hct
      exact hne t (star_injective hct)
    have hliftc : IsLogLiftOf Lc (shiftedCurve γc ((starRingEnd ℂ) q)) := by
      intro t
      have happc : shiftedCurve γc ((starRingEnd ℂ) q) t = γc t - (starRingEnd ℂ) q := by
        simp [shiftedCurve]
      rw [hLcapp t, Complex.exp_conj, hL t, happc, hcapp t]
      have happ : shiftedCurve γ q t = γ t - q := by simp [shiftedCurve]
      rw [happ, map_sub]
    have hspecc := windingNumber_spec hclc hnec hliftc
    have hincr : Lc 1 - Lc 0 = 2 * Real.pi * Complex.I *
        ((- windingNumber γ q : ℤ) : ℂ) := by
      rw [hLcapp 1, hLcapp 0, ← map_sub, hspec]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
      push_cast
      ring
    rw [hincr] at hspecc
    have h2 := mul_left_cancel₀ Complex.two_pi_I_ne_zero hspecc
    exact_mod_cast h2.symm
  -- circle plumbing
  have hcirc_norm : ∀ (z : ℂ) (ρ : ℝ) (t : I), 0 < ρ → ‖circleLoop z ρ t - z‖ = ρ := by
    intro z ρ t hρ
    have hsub : circleLoop z ρ t - z =
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      have happ : circleLoop z ρ t = z +
          (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [happ]
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hρ]
  have hcirc_cl : ∀ (z : ℂ) (ρ : ℝ), circleLoop z ρ 0 = circleLoop z ρ 1 := by
    intro z ρ
    have h0 : circleLoop z ρ 0 = z +
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop z ρ 1 = z +
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  -- eventual constancy of degree −1 via the conjugation reflection
  have hnege : ∀ (e : OpenPartialHomeomorph ℂ ℂ) (z₀ : ℂ) (r : ℝ)
      (hb : Metric.closedBall z₀ r ⊆ e.source) (hr : 0 < r),
      windingDegreeAt e z₀ r hb hr = -1 →
      ∀ᶠ z in 𝓝 z₀, ∀ (r' : ℝ) (hb' : Metric.closedBall z r' ⊆ e.source) (hr' : 0 < r'),
        windingDegreeAt e z r' hb' hr' = -1 := by
    intro e z₀ r hb hr hdeg
    have hRsrc : (Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source = Set.univ :=
      Homeomorph.toOpenPartialHomeomorph_source _
    have hsrc' : (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source
        = e.source := by
      rw [OpenPartialHomeomorph.trans_source, hRsrc, Set.preimage_univ, Set.inter_univ]
    have hdeg' : ∀ (z : ℂ) (ρ : ℝ) (hb₁ : Metric.closedBall z ρ ⊆ e.source)
        (hb₂ : Metric.closedBall z ρ ⊆
          (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source)
        (hρ : 0 < ρ),
        windingDegreeAt (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph)
          z ρ hb₂ hρ = - windingDegreeAt e z ρ hb₁ hρ := by
      intro z ρ hb₁ hb₂ hρ
      have hmem : ∀ t : I, circleLoop z ρ t ∈ e.source := by
        intro t
        apply hb₁
        rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm z ρ t hρ]
      have hzsrc : z ∈ e.source := hb₁ (Metric.mem_closedBall_self hρ.le)
      have hγcont : Continuous fun t : I => e (circleLoop z ρ t) :=
        e.continuousOn.comp_continuous (circleLoop z ρ).continuous hmem
      have hγcl : (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ)) 0 =
          (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ)) 1 := by
        change e (circleLoop z ρ 0) = e (circleLoop z ρ 1)
        rw [hcirc_cl]
      have hγne : ∀ t : I,
          (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ)) t ≠ e z := by
        intro t heq
        have heq' : e (circleLoop z ρ t) = e z := heq
        have hcne : circleLoop z ρ t ≠ z := by
          intro h0
          have h1 := hcirc_norm z ρ t hρ
          rw [h0, sub_self, norm_zero] at h1
          exact hρ.ne h1
        exact hcne (e.injOn (hmem t) hzsrc heq')
      have hcalc := hconj (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ))
        (⟨fun t => (starRingEnd ℂ) (e (circleLoop z ρ t)),
          by exact Continuous.comp continuous_star hγcont⟩ : C(I, ℂ))
        (e z) hγcl hγne (fun t => rfl)
      unfold windingDegreeAt
      have hpt : (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph) z
          = (starRingEnd ℂ) (e z) := rfl
      rw [hpt]
      exact Eq.trans (hwn_ext _ _ _ (fun t => rfl)) hcalc
    have hb₂ : Metric.closedBall z₀ r ⊆
        (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source := by
      rw [hsrc']
      exact hb
    have hpos : IsOrientationPreservingAt
        (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph) z₀ := by
      refine ⟨r, hr, hb₂, ?_⟩
      rw [hdeg' z₀ r hb hb₂ hr, hdeg]
      norm_num
    have hEv := isOrientationPreservingAt_eventually hpos
    filter_upwards [hEv] with z hz
    intro r' hb' hr'
    have hb₂' : Metric.closedBall z r' ⊆
        (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source := by
      rw [hsrc']
      exact hb'
    have hall := (isOrientationPreservingAt_iff_forall _ z).mp hz
    have h1 := hall.2 r' hr' hb₂'
    have h2 := hdeg' z r' hb' hb₂' hr'
    rw [h1] at h2
    omega
  -- the locus of orientation-preservation is open
  have hAopen : IsOpen {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} := by
    rw [isOpen_iff_mem_nhds]
    intro p hpA
    have hpA' : IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p) := hpA
    have hEv := isOrientationPreservingAt_eventually hpA'
    have hcont : ContinuousAt (chartAt ℂ p) p :=
      (chartAt ℂ p).continuousOn.continuousAt
        ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hEv2 : ∀ᶠ p' in 𝓝 p, IsOrientationPreservingAt (homeoChartRep f p)
        (chartAt ℂ p p') := hcont.eventually hEv
    have hN1 : ∀ᶠ p' in 𝓝 p, p' ∈ (chartAt ℂ p).source :=
      (chartAt ℂ p).open_source.eventually_mem (mem_chart_source ℂ p)
    have hN2 : ∀ᶠ p' in 𝓝 p, f p' ∈ (chartAt ℂ (f p)).source :=
      f.continuous.continuousAt.eventually
        ((chartAt ℂ (f p)).open_source.eventually_mem (mem_chart_source ℂ (f p)))
    have hfinal : ∀ᶠ p' in 𝓝 p, p' ∈ {a : S |
        IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} := by
      filter_upwards [hEv2, hN1, hN2] with p' h1' h2' h3'
      exact hmove (chartAt ℂ p) (chartAt ℂ p') (chartAt ℂ (f p)) (chartAt ℂ (f p'))
        (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ p') (chart_mem_atlas ℂ (f p))
        (chart_mem_atlas ℂ (f p')) p' h2' (mem_chart_source ℂ p') h3'
        (mem_chart_source ℂ (f p')) h1'
    rwa [Filter.eventually_iff, Set.setOf_mem_eq] at hfinal
  -- the complement is open
  have hAcopen : IsOpen {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)}ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro p hpA
    have hpA' : ¬ IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p) := hpA
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (homeoChartRep f p).open_source _ (hbase p)
    have hr : 0 < ε / 2 := by positivity
    have hb : Metric.closedBall (chartAt ℂ p p) (ε / 2) ⊆ (homeoChartRep f p).source :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hdeg : windingDegreeAt (homeoChartRep f p) (chartAt ℂ p p) (ε / 2) hb hr = -1 := by
      rcases windingDegreeAt_eq_one_or_neg_one (homeoChartRep f p) hb hr with h1 | h1
      · exact absurd ⟨ε / 2, hr, hb, h1⟩ hpA'
      · exact h1
    have hEv := hnege (homeoChartRep f p) (chartAt ℂ p p) (ε / 2) hb hr hdeg
    have hcont : ContinuousAt (chartAt ℂ p) p :=
      (chartAt ℂ p).continuousOn.continuousAt
        ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hEv2 : ∀ᶠ p' in 𝓝 p, ∀ (r' : ℝ)
        (hb' : Metric.closedBall (chartAt ℂ p p') r' ⊆ (homeoChartRep f p).source)
        (hr' : 0 < r'),
        windingDegreeAt (homeoChartRep f p) (chartAt ℂ p p') r' hb' hr' = -1 :=
      hcont.eventually hEv
    have hN1 : ∀ᶠ p' in 𝓝 p, p' ∈ (chartAt ℂ p).source :=
      (chartAt ℂ p).open_source.eventually_mem (mem_chart_source ℂ p)
    have hN2 : ∀ᶠ p' in 𝓝 p, f p' ∈ (chartAt ℂ (f p)).source :=
      f.continuous.continuousAt.eventually
        ((chartAt ℂ (f p)).open_source.eventually_mem (mem_chart_source ℂ (f p)))
    have hfinal : ∀ᶠ p' in 𝓝 p, p' ∈ {a : S |
        IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)}ᶜ := by
      filter_upwards [hEv2, hN1, hN2] with p' h1' h2' h3'
      intro hcontra
      have hcontra' : IsOrientationPreservingAt (homeoChartRep f p')
          (chartAt ℂ p' p') := hcontra
      have hAtP : IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p') :=
        hmove (chartAt ℂ p') (chartAt ℂ p) (chartAt ℂ (f p')) (chartAt ℂ (f p))
          (chart_mem_atlas ℂ p') (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ (f p'))
          (chart_mem_atlas ℂ (f p)) p' (mem_chart_source ℂ p') h2'
          (mem_chart_source ℂ (f p')) h3' hcontra'
      obtain ⟨r', hr', hb', hdeg1⟩ := hAtP
      have hneg := h1' r' hb' hr'
      omega
    rwa [Filter.eventually_iff, Set.setOf_mem_eq] at hfinal
  -- clopen plus nonempty gives everything
  have hclopen : IsClopen {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} :=
    ⟨isOpen_compl_iff.mp hAcopen, hAopen⟩
  have huniv := hclopen.eq_univ ⟨p₀, hp⟩
  intro p
  have hmemA : p ∈ {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} := by
    rw [huniv]
    exact Set.mem_univ p
  exact hmemA

end RiemannDynamics

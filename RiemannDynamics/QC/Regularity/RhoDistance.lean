/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.LengthArea.CurveModulus
import RiemannDynamics.QC.LengthArea.CurveConcat
import RiemannDynamics.QC.Regularity.RingModulus
import RiemannDynamics.Analysis.LineLebesgue
import RiemannDynamics.Analysis.Sobolev.AbsolutelyContinuousLines
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The ρ-length distance and the eikonal upper-gradient inequality

For a density `ρ : ℂ → ℝ≥0∞`, a boundary set `E ⊆ ℂ`, and an open ring `U ⊆ ℂ`, the **ρ-length
distance** `rhoDistance ρ E U z` is the infimum of the ρ-arc-length `arcLengthLineIntegral ρ γ`
over the absolutely continuous curves `γ` in `U` joining `E` to the point `z`. It is the extremal
competitor `v` in the length–area lower bound for the connecting modulus of the ring: `v` vanishes
on the near boundary `E`, is at least `1` on the far boundary `F` for a density admissible for the
connecting family, and has upper gradient bounded by `ρ` almost everywhere.

## Main results

* `rhoDistance` — the ρ-length distance from `E` to `z` inside `U`;
* `rhoDistance_le_arcLength` — the infimum is at most the ρ-arc-length of any connecting curve;
* `rhoDistance_le_add_segment` — the segment triangle inequality: the ρ-length distance to `w` is at
  most the ρ-length distance to `z` plus the ρ-arc-length of the segment from `z` to `w`;
* `one_le_rhoDistance_of_mem_of_admissible` — for a density admissible for `connectingCurveFamily
  E F U` and a point `z ∈ F`, the ρ-length distance is at least `1`;
* `rhoDistance_antitone_density` — the ρ-length distance is monotone in the density `ρ`;
* `rhoDistance_upperGradient` — the eikonal upper-gradient inequality: the gradient norm of the
  ρ-length distance is bounded by `ρ` almost everywhere.
-/

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- The **ρ-length distance** from the set `E` to the point `z` inside `U`: the infimum of the
ρ-arc-length `arcLengthLineIntegral ρ γ` over absolutely continuous curves `γ` in `U` joining `E`
to `z`. This is the extremal competitor `v` in the length–area lower bound for the connecting
modulus (`v = 0` on `E`, `v ≥ 1` on the far boundary for an admissible density, and — the
research-grade eikonal — `‖∇v‖ ≤ ρ` a.e.). -/
noncomputable def rhoDistance (ρ : ℂ → ℝ≥0∞) (E U : Set ℂ) (z : ℂ) : ℝ≥0∞ :=
  ⨅ γ ∈ connectingCurveFamily E {z} U, arcLengthLineIntegral ρ γ

/-- **The ρ-length distance is a lower bound on connecting arc-lengths.** For any absolutely
continuous curve `γ` in `U` joining `E` to `z`, the ρ-length distance is at most the ρ-arc-length
of `γ`. -/
theorem rhoDistance_le_arcLength (ρ : ℂ → ℝ≥0∞) (E U : Set ℂ) (z : ℂ) {γ : ℝ → ℂ}
    (hγ : γ ∈ connectingCurveFamily E {z} U) :
    rhoDistance ρ E U z ≤ arcLengthLineIntegral ρ γ :=
  iInf₂_le γ hγ

/-- **Segment triangle inequality for the ρ-length distance.** If `z ∈ U` and the open segment from
`z` to `w` lies in `U`, then the ρ-length distance from `E` to `w` is at most the ρ-length distance
from `E` to `z` plus the ρ-arc-length of the segment `t ↦ (1 - t) • z + t • w`. Any near-optimal
connecting curve from `E` to `z` is concatenated with the segment to yield a connecting curve from
`E` to `w`; its interior stays in `U` because the curve's interior stays in `U`, the join point is
`z ∈ U`, and the segment interior lies in the open segment `⊆ U`. Arc-length additivity of the
concatenation and passing to the infimum give the bound. -/
theorem rhoDistance_le_add_segment {ρ : ℂ → ℝ≥0∞} {E U : Set ℂ} {z w : ℂ}
    (hz : z ∈ U) (hseg : openSegment ℝ z w ⊆ U) :
    rhoDistance ρ E U w
      ≤ rhoDistance ρ E U z + arcLengthLineIntegral ρ (fun t => (1 - t) • z + t • w) := by
  set σ : ℝ → ℂ := fun t => (1 - t) • z + t • w with hσ
  -- Basic properties of the segment curve `σ`.
  have hσcont : Continuous σ := by
    have : σ = fun θ : ℝ => ((1 - θ : ℝ) : ℂ) * z + (θ : ℂ) * w := by
      funext θ; rw [hσ]; simp only; rw [Complex.real_smul, Complex.real_smul]
    rw [this]; fun_prop
  have hσlip : LipschitzWith ‖w - z‖₊ σ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hσ]; simp only
    rw [dist_eq_norm, Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul,
      show ((1 - x : ℝ) : ℂ) * z + (x : ℂ) * w - (((1 - y : ℝ) : ℂ) * z + (y : ℂ) * w)
        = ((x - y : ℝ) : ℂ) * (w - z) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, coe_nnnorm, Real.dist_eq, mul_comm]
  have hσac : AbsolutelyContinuousOnInterval σ 0 1 :=
    (hσlip.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
  have hσ0 : σ 0 = z := by rw [hσ]; simp
  have hσ1 : σ 1 = w := by rw [hσ]; simp
  have hσseg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, σ t ∈ openSegment ℝ z w := by
    intro t ht
    have heq : openSegment ℝ z w = (fun θ : ℝ => (1 - θ) • z + θ • w) '' Set.Ioo 0 1 :=
      openSegment_eq_image ℝ z w
    rw [Set.ext_iff] at heq
    exact (heq _).mpr ⟨t, ht, rfl⟩
  have hσU : ∀ t ∈ Set.Ioo (0 : ℝ) 1, σ t ∈ U := fun t ht => hseg (hσseg t ht)
  -- If the ρ-length distance to `z` is `⊤` the bound is trivial.
  by_cases htop : rhoDistance ρ E U z = ⊤
  · rw [htop]; simp
  -- Otherwise approximate the infimum and concatenate.
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hlt : rhoDistance ρ E U z < rhoDistance ρ E U z + ε :=
    ENNReal.lt_add_right htop (by exact_mod_cast hε.ne')
  rw [rhoDistance, iInf_lt_iff] at hlt
  obtain ⟨γz, hγz⟩ := hlt
  rw [iInf_lt_iff] at hγz
  obtain ⟨hγzmem, hγzlt⟩ := hγz
  obtain ⟨hzc, hzac, hz0, hz1, hzsub⟩ := hγzmem
  rw [Set.mem_singleton_iff] at hz1
  -- Join `γz` (`E → z`) to `σ` (`z → w`).
  obtain ⟨γ, hγc, hγac, hγ0, hγ1, _hrange, hrange_open, hadd⟩ :=
    exists_concat_curve hzc hzac hσcont hσac (by rw [hz1, hσ0])
  have hγmem : γ ∈ connectingCurveFamily E {w} U := by
    refine ⟨hγc, hγac, ?_, ?_, ?_⟩
    · rw [hγ0]; exact hz0
    · rw [Set.mem_singleton_iff, hγ1, hσ1]
    · intro t ht
      rcases hrange_open t ht with (hin | hmid) | hin
      · obtain ⟨s, hs, hst⟩ := hin
        rw [← hst]; exact hzsub s hs
      · rw [Set.mem_singleton_iff] at hmid
        rw [hmid, hz1]; exact hz
      · obtain ⟨s, hs, hst⟩ := hin
        rw [← hst]; exact hσU s hs
  calc rhoDistance ρ E U w
      ≤ arcLengthLineIntegral ρ γ := rhoDistance_le_arcLength ρ E U w hγmem
    _ = arcLengthLineIntegral ρ γz + arcLengthLineIntegral ρ σ := hadd ρ
    _ ≤ (rhoDistance ρ E U z + ε) + arcLengthLineIntegral ρ σ := by gcongr; exact hγzlt.le
    _ = rhoDistance ρ E U z + arcLengthLineIntegral ρ σ + ε := by ring

/-- **The ρ-arc-length of a segment is bounded by the density bound times the length.** If `ρ ≤ M`
pointwise, then the ρ-arc-length of the segment `t ↦ (1 - t) • z + t • w` is at most `M ‖w - z‖`.
The segment has constant derivative `w - z`, so the integrand is bounded by `M ‖w - z‖`, and the
parameter interval `[0, 1]` has length `1`. -/
theorem arcLengthLineIntegral_segment_le {ρ : ℂ → ℝ≥0∞} {M : ℝ≥0}
    (hρ : ∀ x, ρ x ≤ (M : ℝ≥0∞)) (z w : ℂ) :
    arcLengthLineIntegral ρ (fun t => (1 - t) • z + t • w) ≤ (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) := by
  have hderiv : ∀ t : ℝ, deriv (fun t : ℝ => (1 - t) • z + t • w) t = w - z := by
    intro t
    have hfun : (fun t : ℝ => (1 - t) • z + t • w)
        = fun θ : ℝ => ((1 - θ : ℝ) : ℂ) * z + (θ : ℂ) * w := by
      funext θ; simp only [Complex.real_smul]
    have h1 : HasDerivAt (fun θ : ℝ => ((1 - θ : ℝ) : ℂ) * z) (-z) t := by
      have h0 : HasDerivAt (fun θ : ℝ => ((1 - θ : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) t :=
        ((hasDerivAt_id t).const_sub 1).ofReal_comp
      simpa using h0.mul_const z
    have h2 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * w) w t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const w
    have : HasDerivAt (fun t : ℝ => (1 - t) • z + t • w) (w - z) t := by
      rw [hfun]; simpa [sub_eq_neg_add] using h1.add h2
    exact this.deriv
  unfold arcLengthLineIntegral
  simp_rw [hderiv]
  calc ∫⁻ t in Set.Icc (0 : ℝ) 1, ρ ((1 - t) • z + t • w) * (‖w - z‖₊ : ℝ≥0∞)
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) := by
        refine lintegral_mono fun t => ?_; gcongr; exact hρ _
    _ = (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) * volume (Set.Icc (0 : ℝ) 1) := setLIntegral_const _ _
    _ = (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) := by
        rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **Local Lipschitz additive bound for the ρ-length distance.** If `ρ ≤ M` pointwise, `z ∈ U`, and
the open segment from `z` to `w` lies in `U`, then the ρ-length distance to `w` is at most the
ρ-length distance to `z` plus `M ‖w - z‖`. This combines the segment triangle inequality with the
segment arc-length bound. -/
theorem rhoDistance_le_add_mul_of_bounded {ρ : ℂ → ℝ≥0∞} {E U : Set ℂ} {M : ℝ≥0}
    (hρ : ∀ x, ρ x ≤ (M : ℝ≥0∞)) {z w : ℂ} (hz : z ∈ U) (hseg : openSegment ℝ z w ⊆ U) :
    rhoDistance ρ E U w ≤ rhoDistance ρ E U z + (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) :=
  le_trans (rhoDistance_le_add_segment hz hseg)
    (by gcongr; exact arcLengthLineIntegral_segment_le hρ z w)

/-- **The far-boundary bound for an admissible density.** If `ρ` is admissible for the connecting
family `connectingCurveFamily E F U` and `z ∈ F`, then the ρ-length distance from `E` to `z` is at
least `1`: every curve `γ` in `U` joining `E` to `z` also joins `E` to `F` (its endpoint `γ 1 = z`
lies in `F`), so admissibility gives `1 ≤ arcLengthLineIntegral ρ γ`. -/
theorem one_le_rhoDistance_of_mem_of_admissible {ρ : ℂ → ℝ≥0∞} {E F U : Set ℂ} {z : ℂ}
    (hadm : IsAdmissibleDensity ρ (connectingCurveFamily E F U)) (hz : z ∈ F) :
    1 ≤ rhoDistance ρ E U z := by
  rw [rhoDistance]
  refine le_iInf₂ ?_
  intro γ hγ
  obtain ⟨hcont, hac, h0, h1, hsub⟩ := hγ
  have h1' : γ 1 ∈ F := by
    rw [Set.mem_singleton_iff] at h1
    rw [h1]; exact hz
  exact hadm.2 γ ⟨hcont, hac, h0, h1', hsub⟩

/-- **Monotonicity of the ρ-length distance in the density.** A pointwise larger density yields a
larger ρ-length distance, since the ρ-arc-length of every connecting curve grows monotonically with
the density. -/
theorem rhoDistance_antitone_density {ρ₁ ρ₂ : ℂ → ℝ≥0∞} {E U : Set ℂ} {z : ℂ}
    (h : ρ₁ ≤ ρ₂) :
    rhoDistance ρ₁ E U z ≤ rhoDistance ρ₂ E U z := by
  rw [rhoDistance, rhoDistance]
  refine iInf₂_mono ?_
  intro γ _
  unfold arcLengthLineIntegral
  refine lintegral_mono fun t => ?_
  gcongr
  exact h (γ t)

/-- **The ρ-arc-length of an oriented segment as a one-dimensional interval integral.** For a
bounded nonnegative measurable real density `g` and a unit vector `u`, the ρ-arc-length of the
segment `t ↦ (1 - t) • z + t • (z + h • u)` (with `h ≥ 0`) taken for the density
`ENNReal.ofReal ∘ g` equals `ENNReal.ofReal (∫₀ʰ g (z + s • u) ds)`. The segment has constant
derivative `h • u` of norm `h`, so the arc-length lintegral is `∫₀¹ g (z + (t h) • u) · h dt`,
which becomes the stated line integral after the change of variables `s = t h`. -/
private theorem arcLengthLineIntegral_segment_toReal {g : ℂ → ℝ} (hgmeas : Measurable g)
    {M : ℝ≥0} (hgbdd : ∀ x, g x ≤ (M : ℝ)) (hgnn : ∀ x, 0 ≤ g x) {z u : ℂ} (hu : ‖u‖ = 1)
    {h : ℝ} (hh : 0 ≤ h) :
    arcLengthLineIntegral (fun w => ENNReal.ofReal (g w))
        (fun t => (1 - t) • z + t • (z + h • u))
      = ENNReal.ofReal (∫ s in (0:ℝ)..h, g (z + s • u)) := by
  have hderiv : ∀ t : ℝ, deriv (fun t : ℝ => (1 - t) • z + t • (z + h • u)) t = h • u := by
    intro t
    have heq : (fun t : ℝ => (1 - t) • z + t • (z + h • u))
        = fun t : ℝ => z + (t * h) • u := by funext t; module
    rw [heq]
    have hm : HasDerivAt (fun t : ℝ => (t * h)) h t := by
      simpa using (hasDerivAt_id t).mul_const h
    exact ((hm.smul_const u).const_add z).deriv
  have hnrm : (‖h • u‖₊ : ℝ≥0∞) = ENNReal.ofReal h := by
    have hn : ‖h • u‖ = h := by
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hh, hu, mul_one]
    have hc : (‖h • u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖h • u‖ := by
      rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; congr 1
    rw [hc, hn]
  have hpt : ∀ t : ℝ, (1 - t) • z + t • (z + h • u) = z + (t * h) • u := by
    intro t; module
  unfold arcLengthLineIntegral
  simp_rw [hderiv, hnrm, hpt]
  have hmerge : ∀ t : ℝ, ENNReal.ofReal (g (z + (t * h) • u)) * ENNReal.ofReal h
      = ENNReal.ofReal (g (z + (t * h) • u) * h) := fun t => by
    rw [← ENNReal.ofReal_mul (hgnn _)]
  simp_rw [hmerge]
  have hnn : ∀ t : ℝ, 0 ≤ g (z + (t * h) • u) * h := fun t => mul_nonneg (hgnn _) hh
  have hmeasf : Measurable (fun a : ℝ => z + (a * h) • u) := by
    have heq : (fun a : ℝ => z + (a * h) • u)
        = fun a : ℝ => z + ((a * h : ℝ) : ℂ) * u := by funext a; rw [Complex.real_smul]
    rw [heq]; fun_prop
  have hφmeas : Measurable (fun t => g (z + (t * h) • u) * h) :=
    (hgmeas.comp hmeasf).mul measurable_const
  have hφint : IntegrableOn (fun t => g (z + (t * h) • u) * h) (Set.Icc (0:ℝ) 1) volume := by
    apply Integrable.mono' (g := fun _ => (M:ℝ) * h)
      (integrableOn_const (by simp [Real.volume_Icc]))
      hφmeas.aestronglyMeasurable.restrict
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
    exact mul_le_mul_of_nonneg_right (hgbdd _) hh
  rw [← ofReal_integral_eq_lintegral_ofReal hφint (by filter_upwards with t using hnn t)]
  congr 1
  rcases eq_or_lt_of_le hh with hh0 | hhpos
  · rw [← hh0]; simp
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    have key := intervalIntegral.smul_integral_comp_mul_right
      (fun s => g (z + s • u)) h (a := 0) (b := 1)
    simp only [zero_mul, one_mul, smul_eq_mul] at key
    rw [← key, intervalIntegral.integral_mul_const, mul_comm]

/-- **A countable cover of an open set by balls contained in it.** Every open `S ⊆ ℂ` is the union
of a countable family of balls, each contained in `S`, centered at points of a countable subset of
`S`. This packages second countability: cover the subtype `↥S` by preimages of ambient balls. -/
private theorem exists_countable_ball_cover {S : Set ℂ} (hS : IsOpen S) :
    ∃ (T : Set ℂ) (rad : ℂ → ℝ), T.Countable ∧ (∀ z ∈ T, z ∈ S) ∧
      (∀ z ∈ T, 0 < rad z ∧ Metric.ball z (rad z) ⊆ S) ∧
      S ⊆ ⋃ z ∈ T, Metric.ball z (rad z) := by
  have hr : ∀ z ∈ S, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ S :=
    fun z hz => Metric.isOpen_iff.mp hS z hz
  choose! rad hrad_pos hrad_sub using hr
  set B' : ↥S → Set ↥S := fun p => (Subtype.val ⁻¹' Metric.ball (p : ℂ) (rad (p : ℂ))) with hB'
  have hB'nhds : ∀ p : ↥S, B' p ∈ nhds p := fun p =>
    IsOpen.mem_nhds (Metric.isOpen_ball.preimage continuous_subtype_val)
      (Metric.mem_ball_self (hrad_pos (p:ℂ) p.2))
  obtain ⟨t, ht_count, ht_cover⟩ := TopologicalSpace.countable_cover_nhds hB'nhds
  refine ⟨Subtype.val '' t, rad, ht_count.image _, ?_, ?_, ?_⟩
  · rintro z ⟨p, _, rfl⟩; exact p.2
  · rintro z ⟨p, _, rfl⟩; exact ⟨hrad_pos (p:ℂ) p.2, hrad_sub (p:ℂ) p.2⟩
  · intro w hw
    have hcov : (⟨w, hw⟩ : ↥S) ∈ (⋃ p ∈ t, B' p) := by rw [ht_cover]; trivial
    simp only [Set.mem_iUnion] at hcov
    obtain ⟨p, hp, hwp⟩ := hcov
    rw [hB'] at hwp; simp only [Set.mem_preimage] at hwp
    exact Set.mem_iUnion.mpr ⟨(p:ℂ), Set.mem_iUnion.mpr ⟨⟨p, hp, rfl⟩, hwp⟩⟩

/-- **The eikonal upper-gradient inequality for a bounded density.** If `ρ ≤ M` pointwise, then the
gradient of the ρ-length distance is bounded a.e. by `ρ`. Away from `E` the ρ-length distance is
locally `M`-Lipschitz (segment triangle inequality), hence differentiable a.e. (Rademacher). Its
directional derivative along a unit vector `u` is bounded by the density: taking the segment
triangle inequality along `u`, the difference quotient of the distance is dominated by the interval
average of `ρ` along the line, which converges a.e. to `ρ` by one-dimensional Lebesgue
differentiation. Ranging over a countable dense set of directions and using continuity bounds the
full gradient norm by `ρ` a.e.; where the distance is infinite it is locally constant, so its
gradient vanishes. -/
theorem rhoDistance_upperGradient_of_bounded {ρ : ℂ → ℝ≥0∞} {E U : Set ℂ} {M : ℝ≥0}
    (hUopen : IsOpen U) (hρmeas : Measurable ρ) (hρbdd : ∀ x, ρ x ≤ (M : ℝ≥0∞)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict U),
      (‖fderiv ℝ (fun w => (rhoDistance ρ E U w).toReal) z‖₊ : ℝ≥0∞) ≤ ρ z := by
  classical
  set v : ℂ → ℝ := fun w => (rhoDistance ρ E U w).toReal with hvdef
  set g : ℂ → ℝ := fun w => (ρ w).toReal with hgdef
  have hρtop : ∀ w, ρ w ≠ ⊤ := fun w => ne_top_of_le_ne_top ENNReal.coe_ne_top (hρbdd w)
  have hρofReal : ∀ w, ρ w = ENNReal.ofReal (g w) := fun w => by
    rw [hgdef]; simp only; rw [ENNReal.ofReal_toReal (hρtop w)]
  have hgmeas : Measurable g := hρmeas.ennreal_toReal
  have hgnn : ∀ x, 0 ≤ g x := fun _ => ENNReal.toReal_nonneg
  have hgbdd : ∀ x, g x ≤ (M:ℝ) := fun x => by
    rw [hgdef]; simp only
    calc (ρ x).toReal ≤ (M:ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.coe_ne_top (hρbdd x)
      _ = (M:ℝ) := by simp
  have hgloc : LocallyIntegrable g := by
    rw [locallyIntegrable_iff]
    intro K hK
    apply Integrable.mono' (g := fun _ => (M:ℝ))
      (integrableOn_const hK.measure_lt_top.ne) hgmeas.aestronglyMeasurable.restrict
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnn x)]; exact hgbdd x
  -- the finite / infinite split of `U`
  set Ufin : Set ℂ := {z | z ∈ U ∧ rhoDistance ρ E U z ≠ ⊤} with hUfin
  set Uinf : Set ℂ := {z | z ∈ U ∧ rhoDistance ρ E U z = ⊤} with hUinf
  have hUsplit : U = Ufin ∪ Uinf := by
    ext z; constructor
    · intro hz; by_cases htop : rhoDistance ρ E U z = ⊤
      · exact Or.inr ⟨hz, htop⟩
      · exact Or.inl ⟨hz, htop⟩
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  -- both regions are open
  have hUfin_open : IsOpen Ufin := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hztop⟩
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hUopen z hzU
    refine ⟨r, hr, ?_⟩
    rintro w hw
    have hseg : openSegment ℝ z w ⊆ U :=
      ((convex_ball z r).openSegment_subset (Metric.mem_ball_self hr) hw).trans hrsub
    have hle := rhoDistance_le_add_mul_of_bounded (E := E) hρbdd hzU hseg
    have hfin : rhoDistance ρ E U z + (M : ℝ≥0∞) * (‖w - z‖₊ : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hztop, ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩
    exact ⟨hrsub hw, ne_top_of_le_ne_top hfin hle⟩
  have hUinf_open : IsOpen Uinf := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hztop⟩
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hUopen z hzU
    refine ⟨r, hr, ?_⟩
    rintro w hw
    refine ⟨hrsub hw, ?_⟩
    by_contra hwfin
    have hseg : openSegment ℝ w z ⊆ U :=
      ((convex_ball z r).openSegment_subset hw (Metric.mem_ball_self hr)).trans hrsub
    have hle := rhoDistance_le_add_mul_of_bounded (E := E) hρbdd (hrsub hw) hseg
    rw [hztop] at hle
    have hfin : rhoDistance ρ E U w + (M : ℝ≥0∞) * (‖z - w‖₊ : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hwfin, ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩
    exact hfin (top_le_iff.mp hle)
  rw [hUsplit, MeasureTheory.ae_restrict_union_eq]
  refine ⟨?_, ?_⟩
  · -- the finite region
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict Ufin),
      (‖fderiv ℝ v z‖₊ : ℝ≥0∞) ≤ ρ z
    -- countable dense set of directions on the unit sphere
    obtain ⟨s, hs_count, hs_dense⟩ :=
      TopologicalSpace.exists_countable_dense (Metric.sphere (0:ℂ) 1)
    set D : Set ℂ := Subtype.val '' s with hDdef
    have hDcount : D.Countable := hs_count.image _
    have hDsub : ∀ u ∈ D, ‖u‖ = 1 := by
      rintro u ⟨p, _, rfl⟩; exact mem_sphere_zero_iff_norm.mp p.2
    have hDclosure : ∀ u : ℂ, ‖u‖ = 1 → u ∈ closure D := by
      intro u hu
      have huS : (⟨u, mem_sphere_zero_iff_norm.mpr hu⟩ : Metric.sphere (0:ℂ) 1) ∈ closure s :=
        hs_dense _
      exact image_closure_subset_closure_image continuous_subtype_val ⟨_, huS, rfl⟩
    -- ball cover of the (open) finite region
    obtain ⟨Tc, rad, hTc_count, hTc_memU, hTc_ball, hTc_cover⟩ :=
      exists_countable_ball_cover hUfin_open
    -- a.e. differentiability on `Ufin`
    have hae_diff : ∀ᵐ z ∂(MeasureTheory.volume.restrict Ufin), DifferentiableAt ℝ v z := by
      have hball_ae : ∀ c ∈ Tc,
          ∀ᵐ w ∂(MeasureTheory.volume.restrict (Metric.ball c (rad c))),
            DifferentiableAt ℝ v w := by
        intro c hc
        obtain ⟨_, hcsub⟩ := hTc_ball c hc
        have hlip : LipschitzOnWith M v (Metric.ball c (rad c)) := by
          rw [lipschitzOnWith_iff_dist_le_mul]
          intro w1 hw1 w2 hw2
          have hconv : Convex ℝ (Metric.ball c (rad c)) := convex_ball c (rad c)
          have hsU : Metric.ball c (rad c) ⊆ U := hcsub.trans (fun _ h => h.1)
          have hf1 : rhoDistance ρ E U w1 ≠ ⊤ := (hcsub hw1).2
          have hf2 : rhoDistance ρ E U w2 ≠ ⊤ := (hcsub hw2).2
          have hseg12 : openSegment ℝ w2 w1 ⊆ U :=
            (hconv.openSegment_subset hw2 hw1).trans hsU
          have hseg21 : openSegment ℝ w1 w2 ⊆ U :=
            (hconv.openSegment_subset hw1 hw2).trans hsU
          have hle12 := rhoDistance_le_add_mul_of_bounded (E := E) hρbdd (hsU hw2) hseg12
          have hle21 := rhoDistance_le_add_mul_of_bounded (E := E) hρbdd (hsU hw1) hseg21
          have hmt : (M:ℝ≥0∞) * (‖w1 - w2‖₊ : ℝ≥0∞) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
          have hmt' : (M:ℝ≥0∞) * (‖w2 - w1‖₊ : ℝ≥0∞) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
          have hr12 : v w1 ≤ v w2 + (M:ℝ) * ‖w1 - w2‖ := by
            rw [hvdef]; simp only
            have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf2, hmt⟩) hle12
            rw [ENNReal.toReal_add hf2 hmt, ENNReal.toReal_mul] at this
            simp only [ENNReal.coe_toReal] at this
            convert this using 2
          have hr21 : v w2 ≤ v w1 + (M:ℝ) * ‖w2 - w1‖ := by
            rw [hvdef]; simp only
            have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf1, hmt'⟩) hle21
            rw [ENNReal.toReal_add hf1 hmt', ENNReal.toReal_mul] at this
            simp only [ENNReal.coe_toReal] at this
            convert this using 2
          rw [Real.dist_eq, abs_sub_le_iff, dist_eq_norm]
          refine ⟨?_, ?_⟩
          · rw [hvdef] at hr12 ⊢; simp only at hr12 ⊢; nlinarith [hr12]
          · have hns : ‖w2 - w1‖ = ‖w1 - w2‖ := by rw [norm_sub_rev]
            rw [hvdef] at hr21 ⊢; simp only at hr21 ⊢; rw [hns] at hr21; nlinarith [hr21]
        have hmb : MeasurableSet (Metric.ball c (rad c)) := measurableSet_ball
        have hrad := hlip.ae_differentiableWithinAt (μ := volume) hmb
        filter_upwards [hrad, ae_restrict_mem hmb] with w hw hwmem
        exact hw.differentiableAt (Metric.isOpen_ball.mem_nhds hwmem)
      rw [MeasureTheory.ae_restrict_iff' hUfin_open.measurableSet,
        Filter.eventually_iff, mem_ae_iff]
      have hset : {w | (w ∈ Ufin → DifferentiableAt ℝ v w)}ᶜ
          = Ufin ∩ {w | ¬ DifferentiableAt ℝ v w} := by
        ext w
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_inter_iff, Classical.not_imp]
      rw [hset]
      have hbad : ∀ c ∈ Tc,
          volume ((Metric.ball c (rad c)) ∩ {w | ¬ DifferentiableAt ℝ v w}) = 0 := by
        intro c hc
        have hz' := hball_ae c hc
        rw [ae_restrict_iff' measurableSet_ball, Filter.eventually_iff, mem_ae_iff] at hz'
        have hc' : {w | (w ∈ Metric.ball c (rad c) → DifferentiableAt ℝ v w)}ᶜ
            = (Metric.ball c (rad c)) ∩ {w | ¬ DifferentiableAt ℝ v w} := by
          ext w
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_inter_iff, Classical.not_imp]
        rwa [hc'] at hz'
      refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc_count).mpr hbad)
      rintro w ⟨hwU, hwP⟩
      obtain ⟨c, hc, hwc⟩ := Set.mem_iUnion₂.mp (hTc_cover hwU)
      exact Set.mem_iUnion₂.mpr ⟨c, hc, hwc, hwP⟩
    -- a.e. line-average convergence, jointly over the countable direction set
    have hae_line : ∀ᵐ z : ℂ, ∀ u ∈ D,
        Filter.Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g (z + s • u))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (g z)) := by
      rw [MeasureTheory.ae_ball_iff hDcount]
      intro u hu
      exact LineLebesgue.ae_tendsto_lineAverage hgloc (hDsub u hu)
    have hae_line' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Ufin), ∀ u ∈ D,
        Filter.Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g (z + s • u))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (g z)) :=
      MeasureTheory.ae_restrict_of_ae hae_line
    -- combine and conclude pointwise
    filter_upwards [hae_diff, hae_line', ae_restrict_mem hUfin_open.measurableSet]
      with z hdiff htend hzUfin
    obtain ⟨hzU, hztop⟩ := hzUfin
    -- a radius `r0` with `ball z r0 ⊆ Ufin`
    obtain ⟨r0, hr0, hr0sub⟩ := Metric.isOpen_iff.mp hUfin_open z ⟨hzU, hztop⟩
    -- the directional bound for each `u ∈ D`
    have hdir : ∀ u ∈ D, (fderiv ℝ v z) u ≤ g z := by
      intro u hu
      have hunorm : ‖u‖ = 1 := hDsub u hu
      -- the small-`h` package
      have hsmall : ∀ h : ℝ, 0 < h → h < r0 →
          openSegment ℝ z (z + h • u) ⊆ U ∧ rhoDistance ρ E U (z + h • u) ≠ ⊤ ∧
          arcLengthLineIntegral ρ (fun t => (1 - t) • z + t • (z + h • u))
            = ENNReal.ofReal (∫ s in (0:ℝ)..h, g (z + s • u)) := by
        intro h hhpos hhlt
        have hend : z + h • u ∈ Metric.ball z r0 := by
          rw [Metric.mem_ball, dist_eq_norm]
          have : ‖z + h • u - z‖ = h := by
            rw [add_sub_cancel_left, Complex.real_smul, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hhpos.le, hunorm, mul_one]
          rw [this]; exact hhlt
        have hendUfin : z + h • u ∈ Ufin := hr0sub hend
        have hseg : openSegment ℝ z (z + h • u) ⊆ U := by
          refine ((convex_ball z r0).openSegment_subset
            (Metric.mem_ball_self hr0) hend).trans ?_
          exact hr0sub.trans (fun _ h => h.1)
        refine ⟨hseg, hendUfin.2, ?_⟩
        have hρeq : ρ = fun w => ENNReal.ofReal (g w) := funext hρofReal
        rw [hρeq]
        exact arcLengthLineIntegral_segment_toReal hgmeas hgbdd hgnn hunorm hhpos.le
      -- directional derivative from differentiability
      have hline : HasDerivAt (fun t : ℝ => z + t • u) u 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t • u) u 0 := by
          simpa using (hasDerivAt_id (0:ℝ)).smul_const u
        exact h1.const_add z
      have hfd0 : HasFDerivAt v (fderiv ℝ v z) ((fun t : ℝ => z + t • u) 0) := by
        simpa using hdiff.hasFDerivAt
      have hcomp : HasDerivAt (fun t : ℝ => v (z + t • u)) (fderiv ℝ v z u) 0 := by
        simpa using hfd0.comp_hasDerivAt 0 hline
      have hslope : Tendsto (fun h : ℝ => h⁻¹ * (v (z + h • u) - v z))
          (𝓝[>] 0) (𝓝 (fderiv ℝ v z u)) := by
        refine hcomp.tendsto_slope_zero_right.congr' ?_
        filter_upwards with t; simp [smul_eq_mul]
      have hev : ∀ᶠ h in 𝓝[>] 0,
          h⁻¹ * (v (z + h • u) - v z) ≤ h⁻¹ * ∫ s in (0:ℝ)..h, g (z + s • u) := by
        filter_upwards [Ioo_mem_nhdsGT hr0] with h hh
        obtain ⟨hseg, hfin, harc⟩ := hsmall h hh.1 hh.2
        have hle := rhoDistance_le_add_segment (ρ := ρ) (E := E) hzU hseg
        rw [harc] at hle
        have hofnn : (0:ℝ) ≤ ∫ s in (0:ℝ)..h, g (z + s • u) :=
          intervalIntegral.integral_nonneg hh.1.le (fun s _ => hgnn _)
        have hmono := ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨hztop, ENNReal.ofReal_ne_top⟩) hle
        rw [ENNReal.toReal_add hztop ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal hofnn] at hmono
        have hquot : v (z + h • u) - v z ≤ ∫ s in (0:ℝ)..h, g (z + s • u) := by
          rw [hvdef]; simp only; linarith
        exact mul_le_mul_of_nonneg_left hquot (le_of_lt (inv_pos.mpr hh.1))
      exact le_of_tendsto_of_tendsto hslope (htend u hu) hev
    -- pass from directions in `D` to the whole sphere, then to the operator norm
    have hsphere : ∀ u : ℂ, ‖u‖ = 1 → (fderiv ℝ v z) u ≤ g z := by
      intro u hu
      have hclosed : IsClosed {w : ℂ | (fderiv ℝ v z) w ≤ g z} :=
        isClosed_le (fderiv ℝ v z).continuous continuous_const
      exact hclosed.closure_subset_iff.mpr (fun w hw => hdir w hw) (hDclosure u hu)
    have hnorm : ‖fderiv ℝ v z‖ ≤ g z := by
      have habs : ∀ u : ℂ, ‖u‖ = 1 → |(fderiv ℝ v z) u| ≤ g z := by
        intro u hu
        rw [abs_le]
        refine ⟨?_, hsphere u hu⟩
        have := hsphere (-u) (by rw [norm_neg, hu]); rw [map_neg] at this; linarith
      apply (fderiv ℝ v z).opNorm_le_bound (hgnn z)
      intro w
      by_cases hw : w = 0
      · subst hw; simp
      · have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
        set uu := (‖w‖)⁻¹ • w with huu
        have hunorm : ‖uu‖ = 1 := by
          rw [huu, Complex.real_smul, norm_mul, Complex.norm_real, norm_inv,
            Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          field_simp
        have hLu : |(fderiv ℝ v z) uu| ≤ g z := habs uu hunorm
        have hwu : w = ‖w‖ • uu := (smul_inv_smul₀ hwn w).symm
        rw [Real.norm_eq_abs]
        calc |(fderiv ℝ v z) w| = |(fderiv ℝ v z) (‖w‖ • uu)| := by rw [← hwu]
          _ = |‖w‖ * (fderiv ℝ v z) uu| := by rw [map_smul, smul_eq_mul]
          _ = ‖w‖ * |(fderiv ℝ v z) uu| := by rw [abs_mul, abs_of_nonneg (norm_nonneg w)]
          _ ≤ g z * ‖w‖ := by
              rw [mul_comm ‖w‖ (|(fderiv ℝ v z) uu|)]
              exact mul_le_mul_of_nonneg_right hLu (norm_nonneg w)
    -- convert to `ℝ≥0∞`
    rw [hρofReal z]
    calc (‖fderiv ℝ v z‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖fderiv ℝ v z‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; congr 1
      _ ≤ ENNReal.ofReal (g z) := ENNReal.ofReal_le_ofReal hnorm
  · -- the infinite region: `v` is locally `0`, so its gradient vanishes
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict Uinf),
      (‖fderiv ℝ v z‖₊ : ℝ≥0∞) ≤ ρ z
    rw [MeasureTheory.ae_restrict_iff' hUinf_open.measurableSet]
    filter_upwards with z hz
    have hv0 : ∀ w ∈ Uinf, v w = 0 := by
      rintro w ⟨_, hwtop⟩; rw [hvdef]; simp only; rw [hwtop, ENNReal.toReal_top]
    have heq : v =ᶠ[nhds z] (fun _ => (0:ℝ)) := by
      filter_upwards [hUinf_open.mem_nhds hz] with w hw using hv0 w hw
    rw [heq.fderiv_eq]; simp

/-- **The eikonal upper-gradient inequality** (metric-Sobolev core): for a measurable density `ρ`
with locally integrable real part `w ↦ (ρ w).toReal` that is finite almost everywhere, the ρ-length
distance is `ρ`-Lipschitz in the upper-gradient sense — its gradient norm is bounded a.e. by the
density. Where the length distance is finite, the segment triangle inequality bounds its
difference quotient along a unit direction by the interval average of `(ρ ·).toReal`, which
converges a.e. to `(ρ z).toReal` by one-dimensional Lebesgue differentiation (hence the local
integrability hypothesis); where the length distance is infinite, it is locally infinite along
the line (using a.e.-finiteness of `ρ`) so the difference quotient vanishes; where the density is
`⊤` the bound is trivial. Ranging over a countable dense set of directions and using continuity of
the fixed derivative bounds the operator norm; at non-differentiability points the Fréchet
derivative is zero. -/
theorem rhoDistance_upperGradient {ρ : ℂ → ℝ≥0∞} {E U : Set ℂ} (hUopen : IsOpen U)
    (hρ : Measurable ρ)
    (hρint : MeasureTheory.LocallyIntegrable (fun w => (ρ w).toReal))
    (hρfin : ∀ᵐ w ∂(volume : Measure ℂ), ρ w ≠ ⊤) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict U),
      (‖fderiv ℝ (fun w => (rhoDistance ρ E U w).toReal) z‖₊ : ℝ≥0∞) ≤ ρ z := by
  classical
  set v : ℂ → ℝ := fun w => (rhoDistance ρ E U w).toReal with hvdef
  set g : ℂ → ℝ := fun w => (ρ w).toReal with hgdef
  have hgmeas : Measurable g := hρ.ennreal_toReal
  have hgnn : ∀ x, 0 ≤ g x := fun _ => ENNReal.toReal_nonneg
  have hgloc : LocallyIntegrable g := hρint
  -- `ρ = ENNReal.ofReal ∘ g` everywhere `ρ` is finite; `ENNReal.ofReal (g w) ≤ ρ w` always.
  have hρle : ∀ w, ENNReal.ofReal (g w) ≤ ρ w := fun w => ENNReal.ofReal_toReal_le
  have hρeqfin : ∀ w, ρ w ≠ ⊤ → ρ w = ENNReal.ofReal (g w) := fun w hw => by
    rw [hgdef]; simp only; rw [ENNReal.ofReal_toReal hw]
  -- countable dense set of directions on the unit sphere
  obtain ⟨s, hs_count, hs_dense⟩ :=
    TopologicalSpace.exists_countable_dense (Metric.sphere (0 : ℂ) 1)
  set D : Set ℂ := Subtype.val '' s with hDdef
  have hDcount : D.Countable := hs_count.image _
  have hDsub : ∀ u ∈ D, ‖u‖ = 1 := by
    rintro u ⟨p, _, rfl⟩; exact mem_sphere_zero_iff_norm.mp p.2
  have hDclosure : ∀ u : ℂ, ‖u‖ = 1 → u ∈ closure D := by
    intro u hu
    have huS : (⟨u, mem_sphere_zero_iff_norm.mpr hu⟩ : Metric.sphere (0 : ℂ) 1) ∈ closure s :=
      hs_dense _
    exact image_closure_subset_closure_image continuous_subtype_val ⟨_, huS, rfl⟩
  -- a.e. `z`, the line `s ↦ g (z + s • u)` is interval integrable, jointly over `u ∈ D`
  have hae_lineint : ∀ᵐ z : ℂ, ∀ u ∈ D, ∀ h : ℝ,
      IntervalIntegrable (fun s : ℝ => g (z + s • u)) volume 0 h := by
    rw [MeasureTheory.ae_ball_iff hDcount]
    intro u hu
    have hunorm : ‖u‖ = 1 := hDsub u hu
    set Φ := LineLebesgue.frame u hunorm with hΦ
    have hΦmp : MeasurePreserving Φ volume volume := LineLebesgue.frame_measurePreserving u hunorm
    set gp : ℝ × ℝ → ℝ := g ∘ Φ with hgp
    have hgploc : LocallyIntegrable gp (volume : Measure (ℝ × ℝ)) := by
      rw [hgp, locallyIntegrable_iff]
      intro K hK
      have himg : IntegrableOn g (Φ '' K) volume :=
        hgloc.integrableOn_isCompact (hK.image (LineLebesgue.frame_continuous u hunorm))
      have hpre : Φ ⁻¹' (Φ '' K) = K := Φ.injective.preimage_image K
      have := (hΦmp.integrableOn_comp_preimage Φ.measurableEmbedding (f := g)
        (s := Φ '' K)).mpr himg
      rwa [hpre] at this
    -- a.e. `b`, the horizontal slice `a ↦ gp (a, b)` is locally integrable
    have hslice : ∀ᵐ b : ℝ, LocallyIntegrable (fun a => gp (a, b)) volume :=
      LineLebesgue.ae_locallyIntegrable_slice gp hgploc
    -- lift to a.e. `p : ℝ × ℝ` via the second projection
    have hslice2 : ∀ᵐ p : ℝ × ℝ, LocallyIntegrable (fun a => gp (a, p.2)) volume := by
      rw [MeasureTheory.Measure.volume_eq_prod]
      exact MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hslice
    -- transport to a.e. `z : ℂ` through the frame
    have hmp : MeasurePreserving Φ.symm volume volume := hΦmp.symm _
    have hslicez := hmp.quasiMeasurePreserving.ae hslice2
    filter_upwards [hslicez] with z hz h
    -- `s ↦ g (z + s • u)` is a translate of the slice `a ↦ gp (a, (Φ.symm z).2)`
    have hΦsymm : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
    have hII0 : IntervalIntegrable (fun a => gp (a, (Φ.symm z).2)) volume
        ((Φ.symm z).1) ((Φ.symm z).1 + h) :=
      (hz.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    have hshift := hII0.comp_add_left ((Φ.symm z).1)
      (by simp only [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
    simp only [add_sub_cancel_left, sub_self] at hshift
    have hcongr : (fun x : ℝ => gp ((Φ.symm z).1 + x, (Φ.symm z).2))
        = fun s : ℝ => g (z + s • u) := by
      funext s
      simp only [hgp, Function.comp_apply]
      have hpt : Φ ((Φ.symm z).1 + s, (Φ.symm z).2)
          = Φ ((Φ.symm z).1, (Φ.symm z).2) + s • u := by
        rw [hΦ, ← LineLebesgue.frame_shift u hunorm]
      rw [show ((Φ.symm z).1, (Φ.symm z).2) = Φ.symm z from rfl, hΦsymm] at hpt
      rw [hpt]
    rwa [hcongr] at hshift
  -- a.e. `z`, the line `s ↦ ρ (z + s • u)` is finite a.e., jointly over `u ∈ D`
  have hae_linefin : ∀ᵐ z : ℂ, ∀ u ∈ D,
      ∀ᵐ s : ℝ, ρ (z + s • u) ≠ ⊤ := by
    rw [MeasureTheory.ae_ball_iff hDcount]
    intro u hu
    have hunorm : ‖u‖ = 1 := hDsub u hu
    set Φ := LineLebesgue.frame u hunorm with hΦ
    have hΦmp : MeasurePreserving Φ volume volume := LineLebesgue.frame_measurePreserving u hunorm
    -- pull `{ρ = ⊤}` back through the frame
    have hpull : ∀ᵐ p : ℝ × ℝ, ρ (Φ p) ≠ ⊤ := hΦmp.quasiMeasurePreserving.ae hρfin
    -- Fubini: a.e. horizontal slice is a.e. finite
    have hpull2 : ∀ᵐ b : ℝ, ∀ᵐ a : ℝ, ρ (Φ (a, b)) ≠ ⊤ := by
      have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
        rw [MeasureTheory.Measure.volume_eq_prod]
        exact MeasureTheory.Measure.measurePreserving_swap
      have hpullswap : ∀ᵐ p : ℝ × ℝ, ρ (Φ (p.2, p.1)) ≠ ⊤ := by
        have := hswap.quasiMeasurePreserving.ae hpull
        simpa [Prod.swap] using this
      have := MeasureTheory.Measure.ae_ae_of_ae_prod
        (p := fun p : ℝ × ℝ => ρ (Φ (p.2, p.1)) ≠ ⊤)
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (by rw [← MeasureTheory.Measure.volume_eq_prod]; exact hpullswap)
      exact this
    -- lift to a.e. `p`, then transport to a.e. `z` through the frame
    have hpull3 : ∀ᵐ p : ℝ × ℝ, ∀ᵐ a : ℝ, ρ (Φ (a, p.2)) ≠ ⊤ := by
      rw [MeasureTheory.Measure.volume_eq_prod]
      exact MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hpull2
    have hmp : MeasurePreserving Φ.symm volume volume := hΦmp.symm _
    have hslicez := hmp.quasiMeasurePreserving.ae hpull3
    filter_upwards [hslicez] with z hz
    have hΦsymm : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
    -- `s ↦ ρ (z + s • u)` is a translate of the a.e.-finite slice `a ↦ ρ (Φ (a, (Φ.symm z).2))`
    have hqmp : Measure.QuasiMeasurePreserving (fun s : ℝ => (Φ.symm z).1 + s)
        volume volume :=
      (measurePreserving_add_left volume ((Φ.symm z).1)).quasiMeasurePreserving
    have := hqmp.ae hz
    filter_upwards [this] with s hs
    have hpt : Φ ((Φ.symm z).1 + s, (Φ.symm z).2)
        = Φ ((Φ.symm z).1, (Φ.symm z).2) + s • u := by rw [hΦ, ← LineLebesgue.frame_shift u hunorm]
    rw [show ((Φ.symm z).1, (Φ.symm z).2) = Φ.symm z from rfl, hΦsymm] at hpt
    rwa [hpt] at hs
  -- a.e. line-average convergence, jointly over the countable direction set
  have hae_line : ∀ᵐ z : ℂ, ∀ u ∈ D,
      Filter.Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0 : ℝ)..h, g (z + s • u))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g z)) := by
    rw [MeasureTheory.ae_ball_iff hDcount]
    intro u hu
    exact LineLebesgue.ae_tendsto_lineAverage hgloc (hDsub u hu)
  -- move all a.e. conditions to the restricted measure and add `z ∈ U`
  rw [MeasureTheory.ae_restrict_iff' hUopen.measurableSet]
  filter_upwards [hae_lineint, hae_line, hae_linefin] with z hlineint htend hlinefinD hzU
  -- case split on differentiability of `v` at `z`
  by_cases hdiff : DifferentiableAt ℝ v z
  · -- differentiable case: bound the directional derivatives along `D`, then the operator norm
    -- a radius `r0` with `ball z r0 ⊆ U`
    obtain ⟨r0, hr0, hr0sub⟩ := Metric.isOpen_iff.mp hUopen z hzU
    -- the segment arc-length equals the interval integral of `g` (interval-integrable slices)
    have harc : ∀ u ∈ D, ∀ h : ℝ, 0 ≤ h →
        arcLengthLineIntegral (fun w => ENNReal.ofReal (g w))
            (fun t => (1 - t) • z + t • (z + h • u))
          = ENNReal.ofReal (∫ s in (0 : ℝ)..h, g (z + s • u)) := by
      intro u hu h hh
      have hunorm : ‖u‖ = 1 := hDsub u hu
      have hderiv : ∀ t : ℝ, deriv (fun t : ℝ => (1 - t) • z + t • (z + h • u)) t = h • u := by
        intro t
        have heq : (fun t : ℝ => (1 - t) • z + t • (z + h • u))
            = fun t : ℝ => z + (t * h) • u := by funext t; module
        rw [heq]
        have hm : HasDerivAt (fun t : ℝ => (t * h)) h t := by
          simpa using (hasDerivAt_id t).mul_const h
        exact ((hm.smul_const u).const_add z).deriv
      have hnrm : (‖h • u‖₊ : ℝ≥0∞) = ENNReal.ofReal h := by
        have hn : ‖h • u‖ = h := by
          rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hh, hunorm, mul_one]
        have hc : (‖h • u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖h • u‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; congr 1
        rw [hc, hn]
      have hpt : ∀ t : ℝ, (1 - t) • z + t • (z + h • u) = z + (t * h) • u := by
        intro t; module
      unfold arcLengthLineIntegral
      simp_rw [hderiv, hnrm, hpt]
      have hmerge : ∀ t : ℝ, ENNReal.ofReal (g (z + (t * h) • u)) * ENNReal.ofReal h
          = ENNReal.ofReal (g (z + (t * h) • u) * h) := fun t => by
        rw [← ENNReal.ofReal_mul (hgnn _)]
      simp_rw [hmerge]
      have hnn : ∀ t : ℝ, 0 ≤ g (z + (t * h) • u) * h := fun t => mul_nonneg (hgnn _) hh
      -- interval integrability of the affine reparametrisation on `[0, 1]`
      have hII : IntervalIntegrable (fun s : ℝ => g (z + s • u)) volume 0 h := hlineint u hu h
      have hφint : IntegrableOn (fun t => g (z + (t * h) • u) * h) (Set.Icc (0 : ℝ) 1) volume := by
        rcases eq_or_lt_of_le hh with hh0 | hhpos
        · -- `h = 0`: the integrand is identically zero
          have hz0 : (fun t : ℝ => g (z + (t * h) • u) * h) = fun _ : ℝ => (0 : ℝ) := by
            funext t; rw [← hh0]; simp
          rw [hz0]; exact integrableOn_const (by simp [Real.volume_Icc])
        · -- `h > 0`: change of variables `t ↦ t * h` from interval integrability along the line
          have hcm := hII.comp_mul_right (c := h)
            (by simp only [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
            (by simp only [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
          rw [zero_div, div_self hhpos.ne'] at hcm
          have hcompint : IntervalIntegrable (fun t : ℝ => g (z + (t * h) • u) * h) volume 0 1 := by
            simpa using hcm.mul_const h
          have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hcompint
          exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr hIoc
      rw [← ofReal_integral_eq_lintegral_ofReal hφint (by filter_upwards with t using hnn t)]
      congr 1
      rcases eq_or_lt_of_le hh with hh0 | hhpos
      · rw [← hh0]; simp
      · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num)]
        have key := intervalIntegral.smul_integral_comp_mul_right
          (fun s => g (z + s • u)) h (a := 0) (b := 1)
        simp only [zero_mul, one_mul, smul_eq_mul] at key
        rw [← key, intervalIntegral.integral_mul_const, mul_comm]
    -- the directional bound for each `u ∈ D`
    have hdir : ∀ u ∈ D, (fderiv ℝ v z) u ≤ g z := by
      intro u hu
      have hunorm : ‖u‖ = 1 := hDsub u hu
      -- directional derivative from differentiability
      have hline : HasDerivAt (fun t : ℝ => z + t • u) u 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t • u) u 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
        exact h1.const_add z
      have hfd0 : HasFDerivAt v (fderiv ℝ v z) ((fun t : ℝ => z + t • u) 0) := by
        simpa using hdiff.hasFDerivAt
      have hcomp : HasDerivAt (fun t : ℝ => v (z + t • u)) (fderiv ℝ v z u) 0 := by
        simpa using hfd0.comp_hasDerivAt 0 hline
      have hslope : Tendsto (fun h : ℝ => h⁻¹ * (v (z + h • u) - v z))
          (𝓝[>] 0) (𝓝 (fderiv ℝ v z u)) := by
        refine hcomp.tendsto_slope_zero_right.congr' ?_
        filter_upwards with t; simp [smul_eq_mul]
      -- line a.e.-finiteness of `ρ` in direction `u`
      have hlinefin : ∀ᵐ s : ℝ, ρ (z + s • u) ≠ ⊤ := hlinefinD u hu
      -- the eventual difference-quotient bound, uniform over finiteness of `rhoDistance`
      have hev : ∀ᶠ h in 𝓝[>] 0,
          h⁻¹ * (v (z + h • u) - v z) ≤ h⁻¹ * ∫ s in (0 : ℝ)..h, g (z + s • u) := by
        filter_upwards [Ioo_mem_nhdsGT hr0] with h hh
        have hhpos : 0 < h := hh.1
        have hend : z + h • u ∈ Metric.ball z r0 := by
          rw [Metric.mem_ball, dist_eq_norm]
          have hd : ‖z + h • u - z‖ = h := by
            rw [add_sub_cancel_left, Complex.real_smul, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hhpos.le, hunorm, mul_one]
          rw [hd]; exact hh.2
        have hseg : openSegment ℝ z (z + h • u) ⊆ U :=
          ((convex_ball z r0).openSegment_subset (Metric.mem_ball_self hr0) hend).trans hr0sub
        have hsegrev : openSegment ℝ (z + h • u) z ⊆ U :=
          ((convex_ball z r0).openSegment_subset hend (Metric.mem_ball_self hr0)).trans hr0sub
        have hofnn : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..h, g (z + s • u) :=
          intervalIntegral.integral_nonneg hhpos.le (fun s _ => hgnn _)
        -- `t ↦ t * h` is quasi-measure-preserving (`h > 0`), so line facts transport
        have hqmpmul : Measure.QuasiMeasurePreserving (fun s : ℝ => s * h) volume volume := by
          refine ⟨measurable_id.mul_const h, ?_⟩
          have hmapeq : Measure.map (fun s : ℝ => s * h) volume
              = ENNReal.ofReal |h⁻¹| • volume := Real.map_volume_mul_right hhpos.ne'
          rw [hmapeq]
          exact Measure.smul_absolutelyContinuous
        have hqmpsub : Measure.QuasiMeasurePreserving (fun t : ℝ => 1 - t) volume volume :=
          (volume.measurePreserving_sub_left 1).quasiMeasurePreserving
        -- along the (reparametrised) line, `ρ` agrees a.e. with `ENNReal.ofReal ∘ g`
        have hae_repar : ∀ᵐ t : ℝ, ρ (z + (t * h) • u) = ENNReal.ofReal (g (z + (t * h) • u)) := by
          filter_upwards [hqmpmul.ae hlinefin] with t ht
          exact hρeqfin _ ht
        -- forward-segment arc-length of `ρ` equals the interval integral of `g` (finite)
        have harcF := harc u hu h hhpos.le
        have harcρ : arcLengthLineIntegral ρ (fun t => (1 - t) • z + t • (z + h • u))
            = ENNReal.ofReal (∫ s in (0 : ℝ)..h, g (z + s • u)) := by
          rw [← harcF]
          unfold arcLengthLineIntegral
          refine lintegral_congr_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_of_ae hae_repar] with t ht
          have hσ : (1 - t) • z + t • (z + h • u) = z + (t * h) • u := by module
          simp only [hσ, ht]
        have harcρfin : arcLengthLineIntegral ρ (fun t => (1 - t) • z + t • (z + h • u)) ≠ ⊤ := by
          rw [harcρ]; exact ENNReal.ofReal_ne_top
        -- reverse-segment arc-length of `ρ` (same points) is finite
        have hae_repar' : ∀ᵐ t : ℝ,
            ρ (z + ((1 - t) * h) • u) = ENNReal.ofReal (g (z + ((1 - t) * h) • u)) := by
          have hcomp := (hqmpsub.ae (hqmpmul.ae hlinefin))
          filter_upwards [hcomp] with t ht
          exact hρeqfin _ ht
        -- the reverse segment traces the same line: `(1-t)•(z+h•u)+t•z = z + ((1-t)*h)•u`
        have hrevpt : ∀ t : ℝ, (1 - t) • (z + h • u) + t • z = z + ((1 - t) * h) • u := by
          intro t; module
        have hrevderiv : ∀ t : ℝ,
            deriv (fun t : ℝ => (1 - t) • (z + h • u) + t • z) t = (-h) • u := by
          intro t
          have heq : (fun t : ℝ => (1 - t) • (z + h • u) + t • z)
              = fun t : ℝ => z + ((1 - t) * h) • u := by funext t; module
          rw [heq]
          have hm : HasDerivAt (fun t : ℝ => (1 - t) * h) (-h) t := by
            have : HasDerivAt (fun t : ℝ => (1 - t) * h) ((-1) * h) t := by
              simpa using (((hasDerivAt_id t).const_sub 1)).mul_const h
            simpa using this
          exact ((hm.smul_const u).const_add z).deriv
        have hrevnrm : (‖(-h) • u‖₊ : ℝ≥0∞) = ENNReal.ofReal h := by
          have hn : ‖(-h) • u‖ = h := by
            rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_neg, abs_of_nonneg hhpos.le, hunorm, mul_one]
          have hc : (‖(-h) • u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖(-h) • u‖ := by
            rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; congr 1
          rw [hc, hn]
        have harcrevfin : arcLengthLineIntegral ρ (fun t => (1 - t) • (z + h • u) + t • z) ≠ ⊤ := by
          unfold arcLengthLineIntegral
          simp_rw [hrevderiv, hrevpt, hrevnrm]
          have hbound : ∫⁻ t in Set.Icc (0 : ℝ) 1,
                ρ (z + ((1 - t) * h) • u) * ENNReal.ofReal h
              = ∫⁻ t in Set.Icc (0 : ℝ) 1,
                ENNReal.ofReal (g (z + ((1 - t) * h) • u) * h) := by
            refine lintegral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_of_ae hae_repar'] with t ht
            rw [ht, ← ENNReal.ofReal_mul (hgnn _)]
          rw [hbound]
          -- integrability of `t ↦ g (z + ((1-t)*h) • u) * h` on `[0,1]`
          have hII : IntervalIntegrable (fun s : ℝ => g (z + s • u)) volume 0 h := hlineint u hu h
          have hcm := hII.comp_mul_right (c := h)
            (by simp only [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
            (by simp only [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
          rw [zero_div, div_self hhpos.ne'] at hcm
          have hrefl := hcm.comp_sub_left (1 : ℝ)
          simp only at hrefl
          have hcompint : IntervalIntegrable
              (fun t : ℝ => g (z + ((1 - t) * h) • u) * h) volume 1 0 := by
            simpa using hrefl.mul_const h
          have hint : IntegrableOn
              (fun t : ℝ => g (z + ((1 - t) * h) • u) * h) (Set.Icc (0 : ℝ) 1) volume := by
            have h01 : (0:ℝ) ≤ 1 := by norm_num
            have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp hcompint.symm
            exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr hIoc
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (by filter_upwards with t using mul_nonneg (hgnn _) hhpos.le)]
          exact ENNReal.ofReal_ne_top
        -- forward and reverse triangle inequalities for `ρ`
        have hfwd := rhoDistance_le_add_segment (ρ := ρ) (E := E) hzU hseg
        have hrev := rhoDistance_le_add_segment (ρ := ρ) (E := E) (hr0sub hend) hsegrev
        rw [harcρ] at hfwd
        by_cases htopz : rhoDistance ρ E U z = ⊤
        · -- infinite base point: both endpoints have infinite distance, so `v` is `0` there
          have htopw : rhoDistance ρ E U (z + h • u) = ⊤ := by
            by_contra hwfin
            rw [htopz] at hrev
            exact (ENNReal.add_ne_top.mpr ⟨hwfin, harcrevfin⟩) (top_le_iff.mp hrev)
          have hv0z : v z = 0 := by rw [hvdef]; simp only; rw [htopz, ENNReal.toReal_top]
          have hv0w : v (z + h • u) = 0 := by
            rw [hvdef]; simp only; rw [htopw, ENNReal.toReal_top]
          rw [hv0z, hv0w, sub_zero, mul_zero]
          exact mul_nonneg (le_of_lt (inv_pos.mpr hhpos)) hofnn
        · -- finite base point: the standard difference-quotient bound
          have hmono := ENNReal.toReal_mono
            (ENNReal.add_ne_top.mpr ⟨htopz, ENNReal.ofReal_ne_top⟩) hfwd
          rw [ENNReal.toReal_add htopz ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hofnn] at hmono
          have hquot : v (z + h • u) - v z ≤ ∫ s in (0 : ℝ)..h, g (z + s • u) := by
            rw [hvdef]; simp only; linarith
          exact mul_le_mul_of_nonneg_left hquot (le_of_lt (inv_pos.mpr hhpos))
      exact le_of_tendsto_of_tendsto hslope (htend u hu) hev
    -- pass from directions in `D` to the whole sphere, then to the operator norm
    have hsphere : ∀ u : ℂ, ‖u‖ = 1 → (fderiv ℝ v z) u ≤ g z := by
      intro u hu
      have hclosed : IsClosed {w : ℂ | (fderiv ℝ v z) w ≤ g z} :=
        isClosed_le (fderiv ℝ v z).continuous continuous_const
      exact hclosed.closure_subset_iff.mpr (fun w hw => hdir w hw) (hDclosure u hu)
    have hnorm : ‖fderiv ℝ v z‖ ≤ g z := by
      have habs : ∀ u : ℂ, ‖u‖ = 1 → |(fderiv ℝ v z) u| ≤ g z := by
        intro u hu
        rw [abs_le]
        refine ⟨?_, hsphere u hu⟩
        have := hsphere (-u) (by rw [norm_neg, hu]); rw [map_neg] at this; linarith
      apply (fderiv ℝ v z).opNorm_le_bound (hgnn z)
      intro w
      by_cases hw : w = 0
      · subst hw; simp
      · have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
        set uu := (‖w‖)⁻¹ • w with huu
        have hunorm : ‖uu‖ = 1 := by
          rw [huu, Complex.real_smul, norm_mul, Complex.norm_real, norm_inv,
            Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          field_simp
        have hLu : |(fderiv ℝ v z) uu| ≤ g z := habs uu hunorm
        have hwu : w = ‖w‖ • uu := (smul_inv_smul₀ hwn w).symm
        rw [Real.norm_eq_abs]
        calc |(fderiv ℝ v z) w| = |(fderiv ℝ v z) (‖w‖ • uu)| := by rw [← hwu]
          _ = |‖w‖ * (fderiv ℝ v z) uu| := by rw [map_smul, smul_eq_mul]
          _ = ‖w‖ * |(fderiv ℝ v z) uu| := by rw [abs_mul, abs_of_nonneg (norm_nonneg w)]
          _ ≤ g z * ‖w‖ := by
              rw [mul_comm ‖w‖ (|(fderiv ℝ v z) uu|)]
              exact mul_le_mul_of_nonneg_right hLu (norm_nonneg w)
    -- convert to `ℝ≥0∞`
    calc (‖fderiv ℝ v z‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖fderiv ℝ v z‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; congr 1
      _ ≤ ENNReal.ofReal (g z) := ENNReal.ofReal_le_ofReal hnorm
      _ ≤ ρ z := hρle z
  · -- non-differentiable case: the Fréchet derivative is zero
    rw [fderiv_zero_of_not_differentiableAt hdiff]
    simp

/-! ### The weak eikonal: `d_ρ` has a weak gradient bounded a.e. by `ρ`

The classical eikonal `rhoDistance_upperGradient` bounds the *Fréchet* gradient of `d_ρ` by `ρ`
almost everywhere, but at points where `d_ρ` fails to be (classically) differentiable — which can
have positive measure for a merely `L²` density `ρ` — the Fréchet derivative is set to `0` and so
*undercounts* the true first-order behaviour. The `W^{1,2}` energy is governed by the **weak**
gradient (the almost-everywhere line-derivatives on absolutely continuous lines), which exists and
is sharply bounded by `ρ` regardless of classical differentiability. This section proves that
weak-gradient bound.
-/

/-- The ρ-arc-length of the unit-direction segment `t ↦ z + (t h) • u` equals the interval integral
`∫₀ʰ (ρ (z + s • u)).toReal ds`, assuming that integrand is interval integrable on `[0, h]`, that
`ρ` is a.e. finite along the segment, and `ρ` is measurable. This is the unbounded-density analogue
of `arcLengthLineIntegral_segment_toReal`: the length integrand is `ρ · ‖h u‖ = ρ · h`, and the
change of variables `s = t h` turns the `[0,1]`-parametrisation into the `[0,h]` line integral. -/
private theorem arcLength_segment_eq_intervalIntegral {ρ : ℂ → ℝ≥0∞} (hρmeas : Measurable ρ)
    {z u : ℂ} (hu : ‖u‖ = 1) {h : ℝ} (hh : 0 < h)
    (hII : IntervalIntegrable (fun s : ℝ => (ρ (z + s • u)).toReal) volume 0 h)
    (hfin : ∀ᵐ s : ℝ, ρ (z + s • u) ≠ ⊤) :
    arcLengthLineIntegral ρ (fun t => (1 - t) • z + t • (z + h • u))
      = ENNReal.ofReal (∫ s in (0:ℝ)..h, (ρ (z + s • u)).toReal) := by
  set g : ℂ → ℝ := fun w => (ρ w).toReal with hgdef
  have hgnn : ∀ x, 0 ≤ g x := fun _ => ENNReal.toReal_nonneg
  have hderiv : ∀ t : ℝ, deriv (fun t : ℝ => (1 - t) • z + t • (z + h • u)) t = h • u := by
    intro t
    have heq : (fun t : ℝ => (1 - t) • z + t • (z + h • u))
        = fun t : ℝ => z + (t * h) • u := by funext t; module
    rw [heq]
    have hm : HasDerivAt (fun t : ℝ => (t * h)) h t := by
      simpa using (hasDerivAt_id t).mul_const h
    exact ((hm.smul_const u).const_add z).deriv
  have hnrm : (‖h • u‖₊ : ℝ≥0∞) = ENNReal.ofReal h := by
    have hn : ‖h • u‖ = h := by
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hh.le, hu, mul_one]
    have hc : (‖h • u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖h • u‖ := by
      rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; congr 1
    rw [hc, hn]
  have hpt : ∀ t : ℝ, (1 - t) • z + t • (z + h • u) = z + (t * h) • u := by
    intro t; module
  unfold arcLengthLineIntegral
  simp_rw [hderiv, hnrm, hpt]
  -- `t ↦ t h` transports the a.e.-finiteness along the segment.
  have hqmpmul : Measure.QuasiMeasurePreserving (fun t : ℝ => t * h) volume volume := by
    refine ⟨measurable_id.mul_const h, ?_⟩
    rw [Real.map_volume_mul_right hh.ne']
    exact Measure.smul_absolutelyContinuous
  have hae_repar : ∀ᵐ t : ℝ, ρ (z + (t * h) • u) = ENNReal.ofReal (g (z + (t * h) • u)) := by
    filter_upwards [hqmpmul.ae hfin] with t ht
    rw [hgdef]; simp only; rw [ENNReal.ofReal_toReal ht]
  -- Rewrite the lintegrand as `ENNReal.ofReal (g · h)` a.e.
  have hbound : ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (z + (t * h) • u) * ENNReal.ofReal h
      = ∫⁻ t in Set.Icc (0:ℝ) 1, ENNReal.ofReal (g (z + (t * h) • u) * h) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae hae_repar] with t ht
    rw [ht, ← ENNReal.ofReal_mul (hgnn _)]
  rw [hbound]
  -- integrability of `t ↦ g (z + (t h) • u) · h` on `[0,1]` from interval integrability along `u`.
  have hcm := hII.comp_mul_right (c := h)
    (by simp only [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
    (by simp only [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
  rw [zero_div, div_self hh.ne'] at hcm
  have hcompint : IntervalIntegrable (fun t : ℝ => g (z + (t * h) • u) * h) volume 0 1 := by
    simpa using hcm.mul_const h
  have hφint : IntegrableOn (fun t => g (z + (t * h) • u) * h) (Set.Icc (0:ℝ) 1) volume := by
    have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hcompint
    exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr hIoc
  have hnn : ∀ t : ℝ, 0 ≤ g (z + (t * h) • u) * h := fun t => mul_nonneg (hgnn _) hh.le
  rw [← ofReal_integral_eq_lintegral_ofReal hφint (by filter_upwards with t using hnn t)]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have key := intervalIntegral.smul_integral_comp_mul_right
    (fun s => g (z + s • u)) h (a := 0) (b := 1)
  simp only [zero_mul, one_mul, smul_eq_mul] at key
  rw [← key, intervalIntegral.integral_mul_const, mul_comm]

/-- **Far-boundary bound for the radial extremal density.** Any point on the outer circle has
`radialDensity`-length distance at least `1` from the inner circle inside the round annulus. This is
the round-annulus ↔ `rhoDistance` link underlying the crude equicontinuity estimate: an admissible
density's length distance from the near boundary is `≥ 1` on the far boundary. -/
theorem one_le_rhoDistance_radialDensity_outer {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {z : ℂ} (hz : z ∈ outerCircle z₀ R) :
    (1 : ℝ≥0∞) ≤ rhoDistance (radialDensity z₀ r R) (innerCircle z₀ r) (RoundAnnulus z₀ r R) z :=
  one_le_rhoDistance_of_mem_of_admissible
    (isAdmissibleDensity_radialDensity_roundAnnulus hr hrR) hz

end RiemannDynamics

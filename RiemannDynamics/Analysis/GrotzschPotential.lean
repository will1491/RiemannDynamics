/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.RingModulus
import RiemannDynamics.Analysis.RingPotential
import RiemannDynamics.Analysis.PolarizationDir
import RiemannDynamics.Analysis.BaernsteinComparison

/-!
# The harmonic potential of the Grötzsch ring

The Grötzsch ring `grotzschRing s` (`0 < s < 1`) is the open unit disk slit along the segment
`[0, s]` of the positive real axis. This file builds its harmonic potential: the harmonic function
on the ring, continuous up to the closure, equal to `0` on the slit `grotzschInner s` and `1` on
the unit circle `grotzschOuter`.

* `frontier_grotzschRing` — the frontier of the ring is the slit together with the unit circle.
* `isRegularBoundary_grotzschRing` — every frontier point carries a barrier: circle points via the
  linear barrier `Re (ζ̄ z) - 1`, slit points via a truncated logarithmic barrier
  `Re (1 / log ((z - a) / (z - b)))` associated with a subsegment `[a, b]` of the slit.
* `exists_grotzschPotential`, `grotzschPotential_unique` — existence (via `exists_ringPotential`)
  and uniqueness (via the maximum principle) of the potential.
* `grotzschPotential_conj` — the potential is invariant under complex conjugation.
* `grotzschPotential_reflection_le`, `grotzschPotential_monotone_arg` — the polarization
  inequality across a diameter and the resulting angular monotonicity: on each circle `|z| = r`
  the potential is nondecreasing in the angle `θ ∈ [0, π]`.
-/

open MeasureTheory Filter Metric Topology Complex Laplacian
open scoped Real Topology

namespace RiemannDynamics

/-! ## Harmonicity and precomposition with a linear isometry -/

/-- The Laplacian of a precomposition with a real-linear isometry equivalence of `ℂ`:
`Δ (f ∘ σ) = (Δ f) ∘ σ`. The Laplacian may be computed in any orthonormal basis, in particular in
the image under `σ` of the basis `![1, I]`. -/
theorem laplacian_comp_linearIsometryEquiv (σ : ℂ ≃ₗᵢ[ℝ] ℂ) (f : ℂ → ℝ) (x : ℂ) :
    Δ (f ∘ σ) x = Δ f (σ x) := by
  have hcomp : ∀ v : ℂ, iteratedFDeriv ℝ 2 (f ∘ σ) x ![v, v]
      = iteratedFDeriv ℝ 2 f (σ x) ![σ v, σ v] := by
    intro v
    have h := σ.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
      (Set.mem_univ (σ.toContinuousLinearEquiv x)) 2
    rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
    have hfun : (f ∘ σ.toContinuousLinearEquiv) = f ∘ σ := by
      funext z
      simp [LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [hfun] at h
    have happ := congrArg (fun T => T ![v, v]) h
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at happ
    rw [happ]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hL : Δ f (σ x) = ∑ i, iteratedFDeriv ℝ 2 f (σ x)
      ![(Complex.orthonormalBasisOneI.map σ) i, (Complex.orthonormalBasisOneI.map σ) i] := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (Complex.orthonormalBasisOneI.map σ)]
  have hLc : Δ (f ∘ σ) x = iteratedFDeriv ℝ 2 (f ∘ σ) x ![1, 1]
      + iteratedFDeriv ℝ 2 (f ∘ σ) x ![Complex.I, Complex.I] := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane (f ∘ σ)]
  rw [hLc, hL, Fin.sum_univ_two]
  simp only [OrthonormalBasis.map_apply, Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hcomp 1, hcomp Complex.I]

/-- Precomposition with a real-linear isometry equivalence of `ℂ` preserves harmonicity at a
point. -/
theorem harmonicAt_comp_linearIsometryEquiv {f : ℂ → ℝ} {x : ℂ} (σ : ℂ ≃ₗᵢ[ℝ] ℂ)
    (hf : InnerProductSpace.HarmonicAt f (σ x)) :
    InnerProductSpace.HarmonicAt (f ∘ σ) x := by
  refine ⟨hf.1.comp x (σ.contDiff.contDiffAt), ?_⟩
  have h0 : Δ f ∘ σ =ᶠ[𝓝 x] (0 : ℂ → ℝ) ∘ σ :=
    hf.2.comp_tendsto (σ.continuous.tendsto x)
  filter_upwards [h0] with y hy
  rw [laplacian_comp_linearIsometryEquiv σ f y]
  simpa using hy

/-! ## Topology of the Grötzsch ring -/

/-- A point of `ℂ` lies on the segment between two real numbers iff it is real, with real part
between them. -/
theorem mem_segment_ofReal {a b : ℝ} {z : ℂ} :
    z ∈ segment ℝ (a : ℂ) (b : ℂ) ↔ z.im = 0 ∧ z.re ∈ Set.uIcc a b := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨by simp [Complex.real_smul], ?_⟩
    rw [← segment_eq_uIcc]
    exact ⟨p, q, hp, hq, hpq, by simp [Complex.real_smul]⟩
  · rintro ⟨him, hre⟩
    rw [← segment_eq_uIcc] at hre
    obtain ⟨p, q, hp, hq, hpq, hx⟩ := hre
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hz, ← hx]
    push_cast [Complex.real_smul, smul_eq_mul]
    ring

/-- The slit of the Grötzsch ring is the set of real points with real part in `[0, s]`. -/
theorem grotzschInner_eq {s : ℝ} (hs : 0 ≤ s) :
    grotzschInner s = {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ s} := by
  ext z
  have h0 : (0 : ℂ) = ((0 : ℝ) : ℂ) := by norm_num
  rw [grotzschInner, h0, mem_segment_ofReal, Set.uIcc_of_le hs]
  simp [Set.mem_Icc]

/-- The slit `grotzschInner s` is closed. -/
theorem isClosed_grotzschInner {s : ℝ} (hs : 0 ≤ s) : IsClosed (grotzschInner s) := by
  rw [grotzschInner_eq hs, Set.setOf_and, Set.setOf_and]
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))

/-- The slit `grotzschInner s` lies inside the open unit disk when `s < 1`. -/
theorem grotzschInner_subset_ball {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    grotzschInner s ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  rw [grotzschInner_eq hs0] at hz
  obtain ⟨him, hre0, hres⟩ := hz
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [mem_ball_zero_iff, hz', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0]
  exact lt_of_le_of_lt hres hs1

/-- The Grötzsch ring is open. -/
theorem isOpen_grotzschRing {s : ℝ} (hs : 0 ≤ s) : IsOpen (grotzschRing s) :=
  Metric.isOpen_ball.sdiff (isClosed_grotzschInner hs)

/-- The Grötzsch ring is bounded. -/
theorem isBounded_grotzschRing (s : ℝ) : Bornology.IsBounded (grotzschRing s) :=
  Metric.isBounded_ball.subset Set.diff_subset

/-- The closure of the Grötzsch ring is the closed unit disk: the slit has empty interior, so
removing it does not shrink the closure of the disk. -/
theorem closure_grotzschRing {s : ℝ} (hs0 : 0 ≤ s) :
    closure (grotzschRing s) = closedBall (0 : ℂ) 1 := by
  apply Set.Subset.antisymm
  · calc closure (grotzschRing s) ⊆ closure (ball (0 : ℂ) 1) := closure_mono Set.diff_subset
      _ = closedBall 0 1 := closure_ball 0 one_ne_zero
  · have hdense : ball (0 : ℂ) 1 ⊆ closure (grotzschRing s) := by
      intro x hx
      rcases em (x ∈ grotzschInner s) with hxs | hxs
      · rw [Metric.mem_closure_iff]
        intro ε hε
        have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
        set δ : ℝ := min (ε / 2) ((1 - ‖x‖) / 2) with hδdef
        have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
        refine ⟨x + δ * Complex.I, ⟨?_, ?_⟩, ?_⟩
        · rw [mem_ball_zero_iff]
          have hnorm : ‖(δ : ℂ) * Complex.I‖ = δ := by
            rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hδpos, mul_one]
          calc ‖x + δ * Complex.I‖ ≤ ‖x‖ + ‖(δ : ℂ) * Complex.I‖ := norm_add_le _ _
            _ = ‖x‖ + δ := by rw [hnorm]
            _ < 1 := by
                have h2 : δ ≤ (1 - ‖x‖) / 2 := min_le_right _ _
                linarith
        · intro hmem
          have hmem' : x + δ * Complex.I ∈ grotzschInner s := hmem
          have him : (x + δ * Complex.I).im = 0 := by
            rw [grotzschInner_eq hs0] at hmem'
            exact hmem'.1
          have hxim : x.im = 0 := by
            rw [grotzschInner_eq hs0] at hxs
            exact hxs.1
          simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, hxim] at him
          simp only [mul_one, mul_zero, add_zero, zero_add] at him
          linarith
        · rw [dist_eq_norm]
          have hnorm : ‖x - (x + δ * Complex.I)‖ = δ := by
            rw [show x - (x + δ * Complex.I) = -(δ * Complex.I) by ring, norm_neg, norm_mul,
              Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos, mul_one]
          rw [hnorm]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · exact subset_closure ⟨hx, hxs⟩
    calc closedBall (0 : ℂ) 1 = closure (ball (0 : ℂ) 1) := (closure_ball 0 one_ne_zero).symm
      _ ⊆ closure (closure (grotzschRing s)) := closure_mono hdense
      _ = closure (grotzschRing s) := closure_closure

/-- **Frontier of the Grötzsch ring.** The boundary of the slit disk is the union of the slit and
the unit circle. -/
theorem frontier_grotzschRing {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    frontier (grotzschRing s) = grotzschInner s ∪ grotzschOuter := by
  rw [(isOpen_grotzschRing hs0.le).frontier_eq, closure_grotzschRing hs0.le, grotzschRing,
    Set.diff_diff_right, closedBall_diff_ball]
  have h1 : closedBall (0 : ℂ) 1 ∩ segment ℝ (0 : ℂ) (s : ℂ) = grotzschInner s :=
    Set.inter_eq_self_of_subset_right
      ((grotzschInner_subset_ball hs0.le hs1).trans ball_subset_closedBall)
  rw [h1, Set.union_comm]
  rfl

/-! ## The logarithmic barrier profile -/

/-- The profile of the logarithmic barrier: the real part of `1 / log w`, written in the real
coordinates `log ‖w‖ / ((log ‖w‖)² + arccos(Re w / ‖w‖)²)`. On the punctured open unit disk it is
strictly negative and tends to `0` as `w → 0`; the arccos form of `|arg w|²` makes the profile
continuous across the negative real axis. -/
noncomputable def logBarrierProfile (w : ℂ) : ℝ :=
  Real.log ‖w‖ / ((Real.log ‖w‖) ^ 2 + (Real.arccos (w.re / ‖w‖)) ^ 2)

theorem logBarrierProfile_zero : logBarrierProfile 0 = 0 := by
  simp [logBarrierProfile]

theorem logBarrierProfile_neg {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    logBarrierProfile w < 0 := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hlog : Real.log ‖w‖ < 0 := Real.log_neg hnorm hw1
  have h1 : 0 < (Real.log ‖w‖) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hlog.ne))
  have hden : 0 < (Real.log ‖w‖) ^ 2 + (Real.arccos (w.re / ‖w‖)) ^ 2 := by
    nlinarith [sq_nonneg (Real.arccos (w.re / ‖w‖))]
  exact div_neg_of_neg_of_pos hlog hden

/-- The barrier profile is dominated by `1 / |log ‖w‖|` inside the unit disk. -/
theorem abs_logBarrierProfile_le {w : ℂ} (hw1 : ‖w‖ < 1) :
    |logBarrierProfile w| ≤ 1 / |Real.log ‖w‖| := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [logBarrierProfile_zero]
  · have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hlog : Real.log ‖w‖ < 0 := Real.log_neg hnorm hw1
    have h1 : 0 < (Real.log ‖w‖) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hlog.ne))
    have hden : 0 < (Real.log ‖w‖) ^ 2 + (Real.arccos (w.re / ‖w‖)) ^ 2 := by
      nlinarith [sq_nonneg (Real.arccos (w.re / ‖w‖))]
    have habs : 0 < |Real.log ‖w‖| := abs_pos.mpr hlog.ne
    rw [logBarrierProfile, abs_div, abs_of_pos hden, div_le_div_iff₀ hden habs]
    have hsq : |Real.log ‖w‖| * |Real.log ‖w‖| = (Real.log ‖w‖) ^ 2 := by
      rw [abs_mul_abs_self]; ring
    nlinarith [sq_nonneg (Real.arccos (w.re / ‖w‖)), abs_nonneg (Real.log ‖w‖)]

/-- The barrier profile is continuous at the origin (with value `0`). -/
theorem continuousAt_logBarrierProfile_zero : ContinuousAt logBarrierProfile 0 := by
  rw [ContinuousAt, logBarrierProfile_zero, Metric.tendsto_nhds_nhds]
  intro ε hε
  refine ⟨min (Real.exp (-(2 / ε))) 1, lt_min (Real.exp_pos _) one_pos, fun {w} hw => ?_⟩
  rw [dist_zero_right] at hw
  have hw1 : ‖w‖ < 1 := lt_of_lt_of_le hw (min_le_right _ _)
  rw [Real.dist_eq, sub_zero]
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [logBarrierProfile_zero, abs_zero]; exact hε
  · have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hlt : Real.log ‖w‖ < -(2 / ε) := by
      calc Real.log ‖w‖ < Real.log (Real.exp (-(2 / ε))) :=
            Real.log_lt_log hnorm (lt_of_lt_of_le hw (min_le_left _ _))
        _ = -(2 / ε) := Real.log_exp _
    have h2ε : (0 : ℝ) < 2 / ε := by positivity
    have habs : 2 / ε < |Real.log ‖w‖| := by
      have hneg : Real.log ‖w‖ < 0 := hlt.trans (by linarith)
      rw [abs_of_neg hneg]
      linarith
    have hb : 1 / |Real.log ‖w‖| < ε / 2 := by
      rw [div_lt_iff₀ (lt_trans h2ε habs)]
      have hkey : ε / 2 * (2 / ε) = 1 := by field_simp
      calc (1 : ℝ) = ε / 2 * (2 / ε) := hkey.symm
        _ < ε / 2 * |Real.log ‖w‖| := by
            exact mul_lt_mul_of_pos_left habs (by positivity)
    calc |logBarrierProfile w| ≤ 1 / |Real.log ‖w‖| := abs_logBarrierProfile_le hw1
      _ < ε / 2 := hb
      _ < ε := by linarith

/-- The barrier profile is continuous away from the origin and the unit circle. -/
theorem continuousAt_logBarrierProfile {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ ≠ 1) :
    ContinuousAt logBarrierProfile w := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hlogcont : ContinuousAt (fun z : ℂ => Real.log ‖z‖) w :=
    (Real.continuousAt_log hnorm.ne').comp continuous_norm.continuousAt
  have harccont : ContinuousAt (fun z : ℂ => Real.arccos (z.re / ‖z‖)) w :=
    Real.continuous_arccos.continuousAt.comp
      (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt hnorm.ne')
  have hlogne : Real.log ‖w‖ ≠ 0 := by
    rcases lt_or_gt_of_ne hw1 with h | h
    · exact (Real.log_neg hnorm h).ne
    · exact (Real.log_pos h).ne'
  have hden : (Real.log ‖w‖) ^ 2 + (Real.arccos (w.re / ‖w‖)) ^ 2 ≠ 0 := by
    have h1 : 0 < (Real.log ‖w‖) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hlogne))
    nlinarith [sq_nonneg (Real.arccos (w.re / ‖w‖))]
  exact hlogcont.div ((hlogcont.pow 2).add (harccont.pow 2)) hden

/-- On the slit plane the barrier profile is the real part of `1 / log w`. -/
theorem logBarrierProfile_eq {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    logBarrierProfile w = (1 / Complex.log w).re := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have harg : Real.arccos (w.re / ‖w‖) = |Complex.arg w| := by
    rw [← Complex.cos_arg hw0, ← Real.cos_abs (Complex.arg w)]
    exact Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi w)
  have hnsq : Complex.normSq (Complex.log w)
      = (Real.log ‖w‖) ^ 2 + (Complex.arg w) ^ 2 := by
    rw [Complex.normSq_apply, Complex.log_re, Complex.log_im]; ring
  rw [one_div, Complex.inv_re, hnsq, Complex.log_re, logBarrierProfile, harg, sq_abs]

/-! ## The Möbius quotient of a real segment -/

/-- A segment between two real points of `ℂ` is closed. -/
theorem isClosed_segment_ofReal (a b : ℝ) : IsClosed (segment ℝ (a : ℂ) (b : ℂ)) := by
  have h : segment ℝ (a : ℂ) (b : ℂ) = {z : ℂ | z.im = 0 ∧ z.re ∈ Set.uIcc a b} :=
    Set.ext fun _ => mem_segment_ofReal
  rw [h, Set.setOf_and]
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_Icc.preimage Complex.continuous_re)

/-- The Möbius quotient `(z - a) / (z - b)` of a point `z` outside the real segment `[a, b]` lies
in the slit plane: the quotient is a nonpositive real number exactly on the segment. -/
theorem mobius_mem_slitPlane {a b : ℝ} {z : ℂ} (hz : z ∉ segment ℝ (a : ℂ) (b : ℂ)) :
    (z - a) / (z - b) ∈ Complex.slitPlane := by
  by_contra hcon
  apply hz
  rcases eq_or_ne z (b : ℂ) with rfl | hzb
  · exact right_mem_segment ℝ _ _
  have hzbne : z - (b : ℂ) ≠ 0 := sub_ne_zero.mpr hzb
  rw [Complex.mem_slitPlane_iff] at hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  set u : ℝ := ((z - a) / (z - b)).re with hu
  have hweq : (z - a) / (z - b) = (u : ℂ) := Complex.ext (by simp [hu]) (by simp [him])
  have hzeq : z - (a : ℂ) = (u : ℂ) * (z - b) := by
    rw [← hweq]
    exact (div_mul_cancel₀ _ hzbne).symm
  have hu0 : u ≤ 0 := hre
  have h1u : (0 : ℝ) < 1 - u := by linarith
  refine ⟨1 / (1 - u), -u / (1 - u), by positivity,
    div_nonneg (by linarith) (by linarith), ?_, ?_⟩
  · field_simp
    ring
  · rw [Complex.real_smul, Complex.real_smul]
    have h1 : z * ((1 : ℂ) - u) = ↑a - ↑u * ↑b := by linear_combination hzeq
    have hone' : ((1 : ℂ) - (u : ℂ)) ≠ 0 := by
      have h2 : ((1 - u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1u.ne'
      push_cast at h2
      exact h2
    push_cast
    field_simp
    linear_combination -h1

/-- The logarithmic barrier `z ↦ Re (1 / log ((z - a) / (z - b)))`, in its `logBarrierProfile`
form, is harmonic away from the segment `[a, b]`. -/
theorem harmonicAt_logBarrier {a b : ℝ} (hab : a ≠ b) {x : ℂ}
    (hx : x ∉ segment ℝ (a : ℂ) (b : ℂ)) :
    InnerProductSpace.HarmonicAt (fun z => logBarrierProfile ((z - a) / (z - b))) x := by
  have hxb : x ≠ (b : ℂ) := fun h => hx (h ▸ right_mem_segment ℝ _ _)
  have hxbne : x - (b : ℂ) ≠ 0 := sub_ne_zero.mpr hxb
  have hwx : (x - a) / (x - b) ∈ Complex.slitPlane := mobius_mem_slitPlane hx
  have hw0 : (x - a) / (x - b) ≠ 0 := Complex.slitPlane_ne_zero hwx
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - (a : ℂ)) x := analyticAt_id.sub analyticAt_const
  have h2 : AnalyticAt ℂ (fun z : ℂ => z - (b : ℂ)) x := analyticAt_id.sub analyticAt_const
  have hmob : AnalyticAt ℂ (fun z : ℂ => (z - a) / (z - b)) x := h1.div h2 hxbne
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log ((z - a) / (z - b))) x := by
    have hc := AnalyticAt.comp (g := Complex.log) (f := fun z : ℂ => (z - a) / (z - b))
      (analyticAt_clog hwx) hmob
    exact hc
  have hlogne : Complex.log ((x - a) / (x - b)) ≠ 0 := by
    intro h0
    have hexp := Complex.exp_log hw0
    rw [h0, Complex.exp_zero] at hexp
    have heq : x - (a : ℂ) = x - b := by
      have h3 : (x - a) / (x - b) = 1 := hexp.symm
      rw [div_eq_one_iff_eq hxbne] at h3
      exact h3
    exact hab (Complex.ofReal_inj.mp (sub_right_inj.mp heq))
  have hinv : AnalyticAt ℂ (fun z : ℂ => (Complex.log ((z - a) / (z - b)))⁻¹) x :=
    hlog.inv hlogne
  have hre : InnerProductSpace.HarmonicAt
      (fun z => ((Complex.log ((z - a) / (z - b)))⁻¹).re) x := hinv.harmonicAt_re
  have heq : (fun z => logBarrierProfile ((z - a) / (z - b)))
      =ᶠ[𝓝 x] fun z => ((Complex.log ((z - a) / (z - b)))⁻¹).re := by
    filter_upwards [(isClosed_segment_ofReal a b).isOpen_compl.mem_nhds hx] with y hy
    rw [logBarrierProfile_eq (mobius_mem_slitPlane hy), one_div]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr hre

/-! ## Barriers for the Grötzsch ring -/

/-- **Barrier at a slit point.** If `[a, b]` is a nondegenerate subsegment of the slit, the
truncated logarithmic barrier `max (Re (1 / log ((z - a) / (z - b)))) m` (extended by the
constant `m < 0` away from `a`) is a barrier for the Grötzsch ring at `a`. -/
theorem exists_barrier_grotzschRing_slit {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {a b : ℝ}
    (hab : a ≠ b) (hseg : segment ℝ (a : ℂ) (b : ℂ) ⊆ grotzschInner s) :
    ∃ β : ℂ → ℝ, IsBarrier β (grotzschRing s) a := by
  classical
  set β₁ : ℂ → ℝ := fun z => logBarrierProfile ((z - a) / (z - b)) with hβ₁def
  set ρ : ℝ := |a - b| / 3 with hρdef
  have hρpos : 0 < ρ := div_pos (abs_pos.mpr (sub_ne_zero.mpr hab)) (by norm_num)
  have hab3 : ‖(a : ℂ) - b‖ = 3 * ρ := by
    rw [hρdef, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; ring
  have hnorm_lt : ∀ z : ℂ, ‖z - (a : ℂ)‖ ≤ ρ → ‖z - (a : ℂ)‖ < ‖z - (b : ℂ)‖ := by
    intro z hz
    have htri : ‖(a : ℂ) - b‖ ≤ ‖(a : ℂ) - z‖ + ‖z - (b : ℂ)‖ := by
      calc ‖(a : ℂ) - b‖ = ‖((a : ℂ) - z) + (z - b)‖ := by congr 1; ring
        _ ≤ ‖(a : ℂ) - z‖ + ‖z - (b : ℂ)‖ := norm_add_le _ _
    have haz : ‖(a : ℂ) - z‖ = ‖z - (a : ℂ)‖ := norm_sub_rev _ _
    linarith [hab3 ▸ htri, hz]
  have haInner : (a : ℂ) ∈ grotzschInner s := hseg (left_mem_segment ℝ _ _)
  have haU : (a : ℂ) ∉ grotzschRing s := fun h => h.2 haInner
  have hsegU : ∀ z ∈ grotzschRing s, z ∉ segment ℝ (a : ℂ) (b : ℂ) :=
    fun z hz hzseg => hz.2 (hseg hzseg)
  have hβ₁harm : ∀ x ∈ grotzschRing s, InnerProductSpace.HarmonicAt β₁ x :=
    fun x hx => harmonicAt_logBarrier hab (hsegU x hx)
  have hβ₁cont : ∀ z : ℂ, ‖z - (a : ℂ)‖ ≤ ρ → ContinuousAt β₁ z := by
    intro z hz
    have hzblt : ‖z - (a : ℂ)‖ < ‖z - (b : ℂ)‖ := hnorm_lt z hz
    have hzb : z ≠ (b : ℂ) := by
      intro h
      rw [h, sub_self, norm_zero] at hzblt
      exact absurd hzblt (not_lt.mpr (norm_nonneg _))
    have hmobc : ContinuousAt (fun w : ℂ => (w - a) / (w - b)) z :=
      ContinuousAt.div ((continuous_id.sub continuous_const).continuousAt)
        ((continuous_id.sub continuous_const).continuousAt) (sub_ne_zero.mpr hzb)
    rcases eq_or_ne z (a : ℂ) with rfl | hza
    · have hφ : ContinuousAt logBarrierProfile (((a : ℂ) - a) / ((a : ℂ) - b)) := by
        rw [sub_self, zero_div]
        exact continuousAt_logBarrierProfile_zero
      exact ContinuousAt.comp (g := logBarrierProfile)
        (f := fun w : ℂ => (w - a) / (w - b)) hφ hmobc
    · have hwne : (z - (a : ℂ)) / (z - b) ≠ 0 :=
        div_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb)
      have hwlt : ‖(z - (a : ℂ)) / (z - b)‖ < 1 := by
        rw [norm_div, div_lt_one (lt_of_le_of_lt (norm_nonneg _) hzblt)]
        exact hzblt
      exact ContinuousAt.comp (g := logBarrierProfile)
        (f := fun w : ℂ => (w - a) / (w - b))
        (continuousAt_logBarrierProfile hwne hwlt.ne) hmobc
  have hβ₁neg : ∀ z : ℂ, ‖z - (a : ℂ)‖ ≤ ρ → z ≠ (a : ℂ) → β₁ z < 0 := by
    intro z hz hza
    have hzblt : ‖z - (a : ℂ)‖ < ‖z - (b : ℂ)‖ := hnorm_lt z hz
    have hzb : z ≠ (b : ℂ) := by
      intro h
      rw [h, sub_self, norm_zero] at hzblt
      exact absurd hzblt (not_lt.mpr (norm_nonneg _))
    apply logBarrierProfile_neg (div_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb))
    rw [norm_div, div_lt_one (lt_of_le_of_lt (norm_nonneg _) hzblt)]
    exact hzblt
  -- the maximum of `β₁` on the reference annulus is negative
  have hclosureU : closure (grotzschRing s) = closedBall (0 : ℂ) 1 := closure_grotzschRing hs0.le
  set K : Set ℂ := closure (grotzschRing s) ∩ {z | ρ / 2 ≤ ‖z - (a : ℂ)‖ ∧ ‖z - (a : ℂ)‖ ≤ ρ}
    with hKdef
  have hnormc : Continuous fun z : ℂ => ‖z - (a : ℂ)‖ := (continuous_id.sub continuous_const).norm
  have hKcl : IsClosed {z : ℂ | ρ / 2 ≤ ‖z - (a : ℂ)‖ ∧ ‖z - (a : ℂ)‖ ≤ ρ} := by
    rw [Set.setOf_and]
    exact (isClosed_le continuous_const hnormc).inter (isClosed_le hnormc continuous_const)
  have hKcompact : IsCompact K :=
    (isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_grotzschRing s).closure).inter_right hKcl
  have hKne : K.Nonempty := by
    have hd : ‖(((2 * a + b) / 3 : ℝ) : ℂ) - (a : ℂ)‖ = ρ := by
      rw [hρdef, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show (2 * a + b) / 3 - a = -((a - b) / 3) by ring, abs_neg, abs_div]
      norm_num
    refine ⟨(((2 * a + b) / 3 : ℝ) : ℂ), ?_, ?_, ?_⟩
    · have hc₀seg : (((2 * a + b) / 3 : ℝ) : ℂ) ∈ segment ℝ (a : ℂ) (b : ℂ) := by
        refine ⟨2 / 3, 1 / 3, by norm_num, by norm_num, by norm_num, ?_⟩
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rw [hclosureU]
      exact ball_subset_closedBall (grotzschInner_subset_ball hs0.le hs1 (hseg hc₀seg))
    · rw [hd]; linarith
    · rw [hd]
  have hβ₁Kcont : ContinuousOn β₁ K :=
    fun z hz => (hβ₁cont z hz.2.2).continuousWithinAt
  obtain ⟨x₀, hx₀K, hx₀max⟩ := hKcompact.exists_isMaxOn hKne hβ₁Kcont
  set m : ℝ := β₁ x₀ with hmdef
  have hmneg : m < 0 := by
    have hx₀ne : x₀ ≠ (a : ℂ) := by
      intro h
      have := hx₀K.2.1
      rw [h, sub_self, norm_zero] at this
      linarith
    exact hβ₁neg x₀ hx₀K.2.2 hx₀ne
  have hKle : ∀ z ∈ K, β₁ z ≤ m := fun z hz => hx₀max hz
  -- the truncated barrier
  set β : ℂ → ℝ := fun z => if ‖z - (a : ℂ)‖ < ρ then max (β₁ z) m else m with hβdef
  have hβ_ge : ∀ z, m ≤ β z := by
    intro z
    by_cases h : ‖z - (a : ℂ)‖ < ρ
    · simp only [hβdef, if_pos h]; exact le_max_right _ _
    · simp only [hβdef, if_neg h]; exact le_refl m
  have hβm : ∀ z ∈ closure (grotzschRing s), ρ / 2 < ‖z - (a : ℂ)‖ → β z = m := by
    intro z hzcl hz
    by_cases h : ‖z - (a : ℂ)‖ < ρ
    · have hzK : z ∈ K := ⟨hzcl, hz.le, h.le⟩
      simp only [hβdef, if_pos h]
      exact max_eq_right (hKle z hzK)
    · simp only [hβdef, if_neg h]
  have hβcont : ContinuousOn β (closure (grotzschRing s)) := by
    intro x hx
    by_cases hx1 : ‖x - (a : ℂ)‖ < ρ
    · have hopen : IsOpen {z : ℂ | ‖z - (a : ℂ)‖ < ρ} := isOpen_lt hnormc continuous_const
      have hcongr : β =ᶠ[𝓝 x] fun z => max (β₁ z) m := by
        filter_upwards [hopen.mem_nhds hx1] with y hy
        simp only [hβdef, if_pos hy]
      have hcontat : ContinuousAt (fun z => max (β₁ z) m) x :=
        (hβ₁cont x hx1.le).max continuousAt_const
      exact (hcontat.congr hcongr.symm).continuousWithinAt
    · have hx2 : ρ / 2 < ‖x - (a : ℂ)‖ := lt_of_lt_of_le (by linarith) (not_lt.mp hx1)
      have hopen : IsOpen {z : ℂ | ρ / 2 < ‖z - (a : ℂ)‖} := isOpen_lt continuous_const hnormc
      refine ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const ?_ (hβm x hx hx2)
      have hmem : closure (grotzschRing s) ∩ {z | ρ / 2 < ‖z - (a : ℂ)‖}
          ∈ 𝓝[closure (grotzschRing s)] x :=
        inter_mem_nhdsWithin _ (hopen.mem_nhds hx2)
      filter_upwards [hmem] with y hy using hβm y hy.1 hy.2
  refine ⟨β, ⟨hβcont.mono subset_closure, ?_⟩, hβcont, ?_, ?_⟩
  · -- sub-mean-value inequality
    intro c hc r hr hball
    have hsphereU : sphere c r ⊆ grotzschRing s := sphere_subset_closedBall.trans hball
    have hβci : CircleIntegrable β c r :=
      ((hβcont.mono subset_closure).mono hsphereU).circleIntegrable hr.le
    have hm_avg : m ≤ Real.circleAverage β c r := by
      have hmono := Real.circleAverage_mono (circleIntegrable_const m c r) hβci
        (fun z _ => hβ_ge z)
      rwa [Real.circleAverage_const] at hmono
    by_cases hcase : ‖c - (a : ℂ)‖ ≤ ρ / 2
    · have hrlt : r < ‖c - (a : ℂ)‖ := by
        by_contra hcon
        exact haU (hball (mem_closedBall.mpr (by
          rw [dist_eq_norm, norm_sub_rev]
          exact not_lt.mp hcon)))
      have hballs : ∀ z ∈ closedBall c r, ‖z - (a : ℂ)‖ < ρ := by
        intro z hz
        have h1 : ‖z - c‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
        calc ‖z - (a : ℂ)‖ = ‖(z - c) + (c - a)‖ := by congr 1; ring
          _ ≤ ‖z - c‖ + ‖c - (a : ℂ)‖ := norm_add_le _ _
          _ < ρ := by linarith [lt_of_lt_of_le hrlt hcase]
      have hβeq : ∀ z ∈ closedBall c r, β z = max (β₁ z) m := by
        intro z hz
        simp only [hβdef, if_pos (hballs z hz)]
      have hβ₁contsphere : ContinuousOn β₁ (sphere c r) := fun z hz =>
        (hβ₁cont z (hballs z (sphere_subset_closedBall hz)).le).continuousWithinAt
      have hβ₁ci : CircleIntegrable β₁ c r := hβ₁contsphere.circleIntegrable hr.le
      have hharm : InnerProductSpace.HarmonicOnNhd β₁ (closedBall c |r|) := by
        rw [abs_of_pos hr]
        exact fun x hx => hβ₁harm x (hball hx)
      have hmv : Real.circleAverage β₁ c r = β₁ c := HarmonicOnNhd.circleAverage_eq hharm
      have h1 : Real.circleAverage β₁ c r ≤ Real.circleAverage β c r := by
        apply Real.circleAverage_mono hβ₁ci hβci
        intro z hz
        rw [abs_of_pos hr] at hz
        rw [hβeq z (sphere_subset_closedBall hz)]
        exact le_max_left _ _
      rw [hβeq c (mem_closedBall_self hr.le)]
      exact max_le (hmv ▸ h1) hm_avg
    · rw [hβm c (subset_closure hc) (not_le.mp hcase)]
      exact hm_avg
  · -- vanishing at the slit point
    have h0 : ‖(a : ℂ) - a‖ < ρ := by rw [sub_self, norm_zero]; exact hρpos
    simp only [hβdef, if_pos h0]
    rw [hβ₁def]
    simp only [sub_self, zero_div, logBarrierProfile_zero]
    exact max_eq_left hmneg.le
  · -- strict negativity away from the slit point
    intro z _ hza
    by_cases h : ‖z - (a : ℂ)‖ < ρ
    · simp only [hβdef, if_pos h]
      exact max_lt (hβ₁neg z h.le hza) hmneg
    · simp only [hβdef, if_neg h]
      exact hmneg

/-- **Barrier at a circle point.** For `ζ` on the unit circle, the linear function
`z ↦ Re (ζ̄ z) - 1` is a barrier for the Grötzsch ring at `ζ`. -/
theorem exists_barrier_grotzschRing_circle {s : ℝ} (hs0 : 0 < s) {ζ : ℂ}
    (hζ : ζ ∈ grotzschOuter) : ∃ β : ℂ → ℝ, IsBarrier β (grotzschRing s) ζ := by
  have hζnorm : ‖ζ‖ = 1 := by
    have h : dist ζ 0 = 1 := hζ
    rwa [dist_zero_right] at h
  have hclosureU : closure (grotzschRing s) = closedBall (0 : ℂ) 1 := closure_grotzschRing hs0.le
  have hharm : InnerProductSpace.HarmonicOnNhd
      (fun z => ((starRingEnd ℂ) ζ * z).re - 1) (grotzschRing s) := by
    intro x _
    have h1 : AnalyticAt ℂ (fun z : ℂ => (starRingEnd ℂ) ζ * z) x :=
      analyticAt_const.mul analyticAt_id
    have h2 : InnerProductSpace.HarmonicAt (fun z => ((starRingEnd ℂ) ζ * z).re) x :=
      h1.harmonicAt_re
    have h3 : InnerProductSpace.HarmonicAt (fun _ : ℂ => (1 : ℝ)) x :=
      InnerProductSpace.harmonicAt_const 1
    exact h2.sub h3
  have hcont : ContinuousOn (fun z : ℂ => ((starRingEnd ℂ) ζ * z).re - 1)
      (closure (grotzschRing s)) :=
    ((Complex.continuous_re.comp (continuous_const.mul continuous_id)).sub
      continuous_const).continuousOn
  have hprodnorm : ∀ z : ℂ, ‖(starRingEnd ℂ) ζ * z‖ = ‖z‖ := by
    intro z
    rw [norm_mul, RCLike.norm_conj, hζnorm, one_mul]
  refine ⟨fun z => ((starRingEnd ℂ) ζ * z).re - 1, HarmonicOnNhd.subharmonicOn hharm, hcont,
    ?_, ?_⟩
  · change ((starRingEnd ℂ) ζ * ζ).re - 1 = 0
    have h : (starRingEnd ℂ) ζ * ζ = ((Complex.normSq ζ : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
    rw [h, Complex.ofReal_re, ← Complex.sq_norm, hζnorm]
    norm_num
  · intro z hzcl hzζ
    change ((starRingEnd ℂ) ζ * z).re - 1 < 0
    rw [hclosureU, mem_closedBall_zero_iff] at hzcl
    have hre : ((starRingEnd ℂ) ζ * z).re ≤ ‖z‖ := by
      have h := Complex.re_le_norm ((starRingEnd ℂ) ζ * z)
      rwa [hprodnorm z] at h
    rcases lt_or_eq_of_le hzcl with h1 | h1
    · linarith
    · have hwne : (starRingEnd ℂ) ζ * z ≠ 1 := by
        intro heq
        apply hzζ
        have h2 := congrArg (fun w => ζ * w) heq
        simp only [mul_one] at h2
        rw [← mul_assoc, Complex.mul_conj, ← Complex.sq_norm, hζnorm] at h2
        norm_num at h2
        exact h2
      by_contra hcon
      push Not at hcon
      have hre1 : ((starRingEnd ℂ) ζ * z).re = 1 := le_antisymm (h1 ▸ hre) (by linarith)
      have hnsq : Complex.normSq ((starRingEnd ℂ) ζ * z) = 1 := by
        rw [← Complex.sq_norm, hprodnorm z, h1]
        norm_num
      have him : ((starRingEnd ℂ) ζ * z).im = 0 := by
        have happ := Complex.normSq_apply ((starRingEnd ℂ) ζ * z)
        nlinarith [happ, hnsq, hre1]
      exact hwne (Complex.ext (by rw [hre1, Complex.one_re]) (by rw [him, Complex.one_im]))

/-- **Boundary regularity of the Grötzsch ring.** Every frontier point carries a barrier: slit
points via the truncated logarithmic barrier of a subsegment, circle points via the linear
barrier. -/
theorem isRegularBoundary_grotzschRing {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IsRegularBoundary (grotzschRing s) := by
  intro ζ hζ
  rw [frontier_grotzschRing hs0 hs1] at hζ
  rcases hζ with hζin | hζout
  · have hζmem := hζin
    rw [grotzschInner_eq hs0.le] at hζmem
    obtain ⟨him, hre0, hres⟩ := hζmem
    have hζre : ζ = ((ζ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hconv : Convex ℝ (grotzschInner s) := by
      rw [grotzschInner]
      exact convex_segment _ _
    have hmem0 : ((0 : ℝ) : ℂ) ∈ grotzschInner s := by
      rw [grotzschInner_eq hs0.le]
      refine ⟨by simp, by simp, by simp [hs0.le]⟩
    rcases eq_or_lt_of_le hre0 with h0 | h0
    · -- the origin: barrier along the segment `[0, s]`
      have hζ0 : ζ = ((0 : ℝ) : ℂ) := by rw [hζre, ← h0]
      rw [hζ0]
      have hmems : ((s : ℝ) : ℂ) ∈ grotzschInner s := by
        rw [grotzschInner_eq hs0.le]
        refine ⟨by simp, by simp [hs0.le], by simp⟩
      exact exists_barrier_grotzschRing_slit hs0 hs1 hs0.ne
        (hconv.segment_subset hmem0 hmems)
    · -- an interior slit point or the tip: barrier along the segment `[t, 0]`
      rw [hζre]
      exact exists_barrier_grotzschRing_slit hs0 hs1 h0.ne'
        (hconv.segment_subset (hζre ▸ hζin) hmem0)
  · exact exists_barrier_grotzschRing_circle hs0 hζout

/-! ## The Grötzsch potential: existence, uniqueness, conjugation symmetry -/

/-- The slit and the unit circle are disjoint. -/
theorem grotzschInner_disjoint_outer {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Disjoint (grotzschInner s) grotzschOuter := by
  rw [Set.disjoint_left]
  intro z hzin hzout
  have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (grotzschInner_subset_ball hs0 hs1 hzin)
  have h2 : dist z 0 = 1 := hzout
  rw [dist_zero_right] at h2
  rw [h2] at h1
  exact lt_irrefl 1 h1

/-- **Existence of the Grötzsch potential**: a harmonic function on the Grötzsch ring, continuous
up to the closed disk, equal to `0` on the slit, `1` on the unit circle, with values in
`[0, 1]`. -/
theorem exists_grotzschPotential {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (grotzschRing s) ∧
      ContinuousOn u (closure (grotzschRing s)) ∧
      (∀ z ∈ grotzschInner s, u z = 0) ∧ (∀ z ∈ grotzschOuter, u z = 1) ∧
      ∀ z ∈ grotzschRing s, 0 ≤ u z ∧ u z ≤ 1 :=
  exists_ringPotential (isOpen_grotzschRing hs0.le) (isBounded_grotzschRing s)
    (isRegularBoundary_grotzschRing hs0 hs1) (frontier_grotzschRing hs0 hs1)
    (grotzschInner_disjoint_outer hs0.le hs1) (isClosed_grotzschInner hs0.le)
    Metric.isClosed_sphere

/-- **Uniqueness of the Grötzsch potential**: two harmonic functions on the ring, continuous up
to the closure, with boundary data `0` on the slit and `1` on the circle, agree on the closed
disk. -/
theorem grotzschPotential_unique {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u v : ℂ → ℝ}
    (huh : InnerProductSpace.HarmonicOnNhd u (grotzschRing s))
    (huc : ContinuousOn u (closure (grotzschRing s)))
    (hu0 : ∀ z ∈ grotzschInner s, u z = 0) (hu1 : ∀ z ∈ grotzschOuter, u z = 1)
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    ∀ z ∈ closure (grotzschRing s), u z = v z := by
  have hfront : ∀ z ∈ frontier (grotzschRing s), u z = v z := by
    intro z hz
    rw [frontier_grotzschRing hs0 hs1] at hz
    rcases hz with h | h
    · rw [hu0 z h, hv0 z h]
    · rw [hu1 z h, hv1 z h]
  have hd1 : ∀ z ∈ grotzschRing s, u z - v z ≤ 0 := by
    have hh : InnerProductSpace.HarmonicOnNhd (fun z => u z - v z) (grotzschRing s) :=
      fun x hx => (huh x hx).sub (hvh x hx)
    exact SubharmonicOn.le_of_frontier_le (isOpen_grotzschRing hs0.le)
      (isBounded_grotzschRing s) (HarmonicOnNhd.subharmonicOn hh) (huc.sub hvc)
      fun z hz => le_of_eq (by rw [hfront z hz, sub_self])
  have hd2 : ∀ z ∈ grotzschRing s, v z - u z ≤ 0 := by
    have hh : InnerProductSpace.HarmonicOnNhd (fun z => v z - u z) (grotzschRing s) :=
      fun x hx => (hvh x hx).sub (huh x hx)
    exact SubharmonicOn.le_of_frontier_le (isOpen_grotzschRing hs0.le)
      (isBounded_grotzschRing s) (HarmonicOnNhd.subharmonicOn hh) (hvc.sub huc)
      fun z hz => le_of_eq (by rw [hfront z hz, sub_self])
  intro z hz
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hzU | hzfront
  · have h1 := hd1 z hzU
    have h2 := hd2 z hzU
    linarith
  · exact hfront z hzfront

/-- The slit is invariant under complex conjugation. -/
theorem conj_mem_grotzschInner {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ grotzschInner s) :
    (starRingEnd ℂ) z ∈ grotzschInner s := by
  rw [grotzschInner_eq hs] at hz ⊢
  exact ⟨by simp [hz.1], by simp [hz.2.1], by simp [hz.2.2]⟩

/-- The Grötzsch ring is invariant under complex conjugation. -/
theorem conj_mem_grotzschRing {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ grotzschRing s) :
    (starRingEnd ℂ) z ∈ grotzschRing s := by
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, RCLike.norm_conj]
    exact mem_ball_zero_iff.mp hz.1
  · intro hmem
    apply hz.2
    have hmem' : (starRingEnd ℂ) z ∈ grotzschInner s := hmem
    have h := conj_mem_grotzschInner hs hmem'
    rwa [Complex.conj_conj] at h

/-- **Conjugation symmetry of the Grötzsch potential.** Any harmonic function on the ring with
the potential boundary data is invariant under complex conjugation on the closed disk. -/
theorem grotzschPotential_conj {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u : ℂ → ℝ}
    (huh : InnerProductSpace.HarmonicOnNhd u (grotzschRing s))
    (huc : ContinuousOn u (closure (grotzschRing s)))
    (hu0 : ∀ z ∈ grotzschInner s, u z = 0) (hu1 : ∀ z ∈ grotzschOuter, u z = 1) :
    ∀ z ∈ closure (grotzschRing s), u ((starRingEnd ℂ) z) = u z := by
  have hvh : InnerProductSpace.HarmonicOnNhd (fun z => u ((starRingEnd ℂ) z))
      (grotzschRing s) := by
    intro x hx
    have hconjx : (starRingEnd ℂ) x ∈ grotzschRing s := conj_mem_grotzschRing hs0.le hx
    have hpt : InnerProductSpace.HarmonicAt u (Complex.conjLIE x) := by
      rw [show Complex.conjLIE x = (starRingEnd ℂ) x from Complex.conjLIE_apply x]
      exact huh _ hconjx
    have h := harmonicAt_comp_linearIsometryEquiv Complex.conjLIE hpt
    have heq : (u ∘ ⇑Complex.conjLIE) =ᶠ[𝓝 x] fun z => u ((starRingEnd ℂ) z) :=
      Filter.Eventually.of_forall fun y => by
        simp [Function.comp_apply, Complex.conjLIE_apply]
    exact (InnerProductSpace.harmonicAt_congr_nhds heq).mp h
  have hmaps : Set.MapsTo (starRingEnd ℂ) (closure (grotzschRing s))
      (closure (grotzschRing s)) := by
    intro z hz
    rw [closure_grotzschRing hs0.le, mem_closedBall_zero_iff] at hz ⊢
    rwa [RCLike.norm_conj]
  have hvc : ContinuousOn (fun z => u ((starRingEnd ℂ) z)) (closure (grotzschRing s)) :=
    huc.comp Complex.continuous_conj.continuousOn hmaps
  have hv0 : ∀ z ∈ grotzschInner s, u ((starRingEnd ℂ) z) = 0 :=
    fun z hz => hu0 _ (conj_mem_grotzschInner hs0.le hz)
  have hv1 : ∀ z ∈ grotzschOuter, u ((starRingEnd ℂ) z) = 1 := by
    intro z hz
    apply hu1
    have h : dist z 0 = 1 := hz
    rw [dist_zero_right] at h
    change dist ((starRingEnd ℂ) z) 0 = 1
    rw [dist_zero_right, RCLike.norm_conj]
    exact h
  exact grotzschPotential_unique hs0 hs1 hvh hvc hv0 hv1 huh huc hu0 hu1

/-! ## Polarization and angular monotonicity -/

/-- **Polarization inequality for the Grötzsch potential.** Let `σ z = e^{2iα} z̄` be the
reflection across the diameter at angle `α ∈ (0, π)`. If `z` and `σ z` both lie in the ring and
`z` lies strictly on the slit side of the diameter, then `u z ≤ u (σ z)`: the difference
`u - u ∘ σ` is harmonic on the σ-symmetric part of the ring on the slit side, and its boundary
values are `≤ 0` on every piece of the frontier. -/
theorem grotzschPotential_reflection_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u : ℂ → ℝ}
    (huh : InnerProductSpace.HarmonicOnNhd u (grotzschRing s))
    (huc : ContinuousOn u (closure (grotzschRing s)))
    (hu0 : ∀ z ∈ grotzschInner s, u z = 0) (hu1 : ∀ z ∈ grotzschOuter, u z = 1)
    (hub : ∀ z ∈ grotzschRing s, 0 ≤ u z ∧ u z ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {z : ℂ}
    (hz : z ∈ grotzschRing s)
    (hzr : Complex.exp ((2 * α : ℝ) * Complex.I) * (starRingEnd ℂ) z ∈ grotzschRing s)
    (hzS : (z * Complex.exp (-(α * Complex.I))).im < 0) :
    u z ≤ u (Complex.exp ((2 * α : ℝ) * Complex.I) * (starRingEnd ℂ) z) := by
  classical
  set σL : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans (rotLIE (2 * α)) with hσLdef
  have hσapp : ∀ w : ℂ,
      σL w = Complex.exp ((2 * α : ℝ) * Complex.I) * (starRingEnd ℂ) w := by
    intro w
    simp [hσLdef, LinearIsometryEquiv.trans_apply, rotLIE_apply, Complex.conjLIE_apply]
  have hσinv : ∀ w : ℂ, σL (σL w) = w := by
    intro w
    rw [hσapp, hσapp, map_mul, Complex.conj_conj, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I, ← mul_assoc, ← Complex.exp_add]
    have h : ((2 * α : ℝ) : ℂ) * Complex.I + (2 * α : ℝ) * -Complex.I = 0 := by ring
    rw [h, Complex.exp_zero, one_mul]
  have hσnorm : ∀ w : ℂ, ‖σL w‖ = ‖w‖ := fun w => σL.norm_map w
  set S : Set ℂ := {w : ℂ | (w * Complex.exp (-(α * Complex.I))).im < 0} with hSdef
  set W : Set ℂ := grotzschRing s ∩ (⇑σL) ⁻¹' grotzschRing s ∩ S with hWdef
  have hScont : Continuous fun w : ℂ => (w * Complex.exp (-(α * Complex.I))).im :=
    Complex.continuous_im.comp (continuous_mul_const _)
  have hSopen : IsOpen S := isOpen_lt hScont continuous_const
  have hWopen : IsOpen W :=
    ((isOpen_grotzschRing hs0.le).inter
      ((isOpen_grotzschRing hs0.le).preimage σL.continuous)).inter hSopen
  have hWbdd : Bornology.IsBounded W :=
    (isBounded_grotzschRing s).subset fun w hw => hw.1.1
  have hfharm : InnerProductSpace.HarmonicOnNhd (fun w => u w - u (σL w)) W := by
    intro x hx
    have h1 : InnerProductSpace.HarmonicAt u x := huh x hx.1.1
    have h2 : InnerProductSpace.HarmonicAt (u ∘ ⇑σL) x :=
      harmonicAt_comp_linearIsometryEquiv σL (huh _ hx.1.2)
    exact h1.sub h2
  have hclW1 : closure W ⊆ closure (grotzschRing s) := closure_mono fun w hw => hw.1.1
  have hclW2 : ∀ w ∈ closure W, σL w ∈ closure (grotzschRing s) := by
    have h1 : closure W ⊆ closure ((⇑σL) ⁻¹' grotzschRing s) :=
      closure_mono fun w hw => hw.1.2
    have h2 : closure ((⇑σL) ⁻¹' grotzschRing s)
        ⊆ (⇑σL) ⁻¹' closure (grotzschRing s) :=
      σL.continuous.closure_preimage_subset _
    intro w hw
    exact h2 (h1 hw)
  have hfcont : ContinuousOn (fun w => u w - u (σL w)) (closure W) := by
    have h1 : ContinuousOn u (closure W) := huc.mono hclW1
    have h2 : ContinuousOn (fun w => u (σL w)) (closure W) :=
      huc.comp σL.continuous.continuousOn hclW2
    exact h1.sub h2
  have hnn : ∀ w ∈ closure (grotzschRing s), 0 ≤ u w := by
    intro w hw
    rw [closure_eq_self_union_frontier] at hw
    rcases hw with hwU | hwF
    · exact (hub w hwU).1
    · rw [frontier_grotzschRing hs0 hs1] at hwF
      rcases hwF with h | h
      · rw [hu0 w h]
      · rw [hu1 w h]; norm_num
  have hfrontle : ∀ ζ ∈ frontier W, u ζ - u (σL ζ) ≤ 0 := by
    intro ζ hζ
    have hζcl : ζ ∈ closure (grotzschRing s) := hclW1 (frontier_subset_closure hζ)
    have hζclσ : σL ζ ∈ closure (grotzschRing s) := hclW2 ζ (frontier_subset_closure hζ)
    have hζclS : ζ ∈ closure S :=
      closure_mono (fun w hw => hw.2) (frontier_subset_closure hζ)
    have hsplit : ζ ∈ frontier (grotzschRing s)
        ∪ frontier ((⇑σL) ⁻¹' grotzschRing s) ∪ frontier S := by
      have h1 := frontier_inter_subset (grotzschRing s ∩ (⇑σL) ⁻¹' grotzschRing s) S
      rcases h1 hζ with ⟨hf, _⟩ | ⟨_, hf⟩
      · rcases frontier_inter_subset (grotzschRing s) ((⇑σL) ⁻¹' grotzschRing s) hf with
          ⟨hfa, _⟩ | ⟨_, hfb⟩
        · exact Or.inl (Or.inl hfa)
        · exact Or.inl (Or.inr hfb)
      · exact Or.inr hf
    rcases hsplit with (hfa | hfb) | hfS
    · rw [frontier_grotzschRing hs0 hs1] at hfa
      rcases hfa with hslit | hcirc
      · rw [hu0 ζ hslit]
        have h := hnn _ hζclσ
        linarith
      · have hσcirc : σL ζ ∈ grotzschOuter := by
          have h : dist ζ 0 = 1 := hcirc
          rw [dist_zero_right] at h
          change dist (σL ζ) 0 = 1
          rw [dist_zero_right, hσnorm]
          exact h
        rw [hu1 ζ hcirc, hu1 _ hσcirc]
        norm_num
    · have hσfront : σL ζ ∈ frontier (grotzschRing s) :=
        σL.continuous.frontier_preimage_subset _ hfb
      rw [frontier_grotzschRing hs0 hs1] at hσfront
      rcases hσfront with hslit | hcirc
      · -- the reflected slit meets the closed slit side only at the origin
        have hx := hslit
        rw [grotzschInner_eq hs0.le] at hx
        obtain ⟨him0, hre0, _⟩ := hx
        obtain ⟨x, hσζre⟩ : ∃ x : ℝ, σL ζ = ((x : ℝ) : ℂ) :=
          ⟨(σL ζ).re, Complex.ext (by simp) (by simp [him0])⟩
        have hxnn : 0 ≤ x := by
          have h := hre0
          rw [hσζre] at h
          simpa using h
        have hζeq : ζ = ((x : ℝ) : ℂ) * Complex.exp ((2 * α : ℝ) * Complex.I) := by
          conv_lhs => rw [← hσinv ζ]
          rw [hσapp (σL ζ), hσζre, Complex.conj_ofReal]
          ring
        have hSle : (ζ * Complex.exp (-(α * Complex.I))).im ≤ 0 := by
          have hsub : closure {w : ℂ | (w * Complex.exp (-(α * Complex.I))).im < 0}
              ⊆ {w : ℂ | (w * Complex.exp (-(α * Complex.I))).im ≤ 0} :=
            closure_lt_subset_le hScont continuous_const
          exact hsub hζclS
        have him : (ζ * Complex.exp (-(α * Complex.I))).im = x * Real.sin α := by
          rw [hζeq, mul_assoc, ← Complex.exp_add]
          have h : ((2 * α : ℝ) : ℂ) * Complex.I + -(α * Complex.I)
              = (α : ℝ) * Complex.I := by push_cast; ring
          rw [h]
          simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]
        have hsinpos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
        have hx0 : x = 0 := by
          rw [him] at hSle
          nlinarith
        have hσζ0 : σL ζ = 0 := by rw [hσζre, hx0]; norm_num
        have hζ0 : ζ = 0 := by rw [hζeq, hx0]; norm_num
        rw [hσζ0, hζ0]
        simp
      · have hζcirc : ζ ∈ grotzschOuter := by
          have h : dist (σL ζ) 0 = 1 := hcirc
          rw [dist_zero_right, hσnorm] at h
          change dist ζ 0 = 1
          rw [dist_zero_right]
          exact h
        rw [hu1 ζ hζcirc, hu1 _ hcirc]
        norm_num
    · -- on the symmetry line the reflection fixes `ζ`
      have hline : (ζ * Complex.exp (-(α * Complex.I))).im = 0 := by
        have hsub : frontier {w : ℂ | (w * Complex.exp (-(α * Complex.I))).im < 0}
            ⊆ {w : ℂ | (w * Complex.exp (-(α * Complex.I))).im = 0} :=
          frontier_lt_subset_eq hScont continuous_const
        exact hsub hfS
      have hσζ : σL ζ = ζ := by
        set c : ℂ := ζ * Complex.exp (-(α * Complex.I)) with hcdef
        have hcre : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hline])
        have hζc : ζ = c * Complex.exp ((α : ℝ) * Complex.I) := by
          rw [hcdef, mul_assoc, ← Complex.exp_add]
          simp
        rw [hσapp]
        conv_lhs => rw [hζc, hcre]
        conv_rhs => rw [hζc, hcre]
        rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
          Complex.conj_I, mul_left_comm, ← Complex.exp_add]
        have h : ((2 * α : ℝ) : ℂ) * Complex.I + (α : ℝ) * -Complex.I
            = ((α : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [h, mul_comm]
      rw [hσζ]
      simp
  have hle := SubharmonicOn.le_of_frontier_le hWopen hWbdd
    (HarmonicOnNhd.subharmonicOn hfharm) hfcont hfrontle
  have hzW : z ∈ W := by
    refine ⟨⟨hz, ?_⟩, hzS⟩
    rw [Set.mem_preimage, hσapp]
    exact hzr
  have h := hle z hzW
  rw [hσapp] at h
  linarith

/-- **Angular monotonicity of the Grötzsch potential.** On each circle `|z| = r` with
`s < r < 1`, the potential is nondecreasing in the angle `θ ∈ [0, π]`: the minimum is attained on
the slit axis and the maximum on the negative real axis. Obtained by polarization across the
diameter at the bisecting angle `α = (θ₁ + θ₂) / 2`. -/
theorem grotzschPotential_monotone_arg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u : ℂ → ℝ}
    (huh : InnerProductSpace.HarmonicOnNhd u (grotzschRing s))
    (huc : ContinuousOn u (closure (grotzschRing s)))
    (hu0 : ∀ z ∈ grotzschInner s, u z = 0) (hu1 : ∀ z ∈ grotzschOuter, u z = 1)
    (hub : ∀ z ∈ grotzschRing s, 0 ≤ u z ∧ u z ≤ 1)
    {r : ℝ} (hrs : s < r) (hr1 : r < 1) {θ₁ θ₂ : ℝ}
    (hθ1 : 0 ≤ θ₁) (hθ12 : θ₁ ≤ θ₂) (hθ2 : θ₂ ≤ π) :
    u (r * Complex.exp (θ₁ * Complex.I)) ≤ u (r * Complex.exp (θ₂ * Complex.I)) := by
  rcases eq_or_lt_of_le hθ12 with rfl | hlt
  · exact le_refl _
  have hr0 : 0 < r := lt_trans hs0 hrs
  set α : ℝ := (θ₁ + θ₂) / 2 with hαdef
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hαπ : α < π := by rw [hαdef]; linarith
  -- the two circle points lie in the ring
  have hmem : ∀ θ : ℝ, 0 ≤ θ → θ ≤ π →
      ((r : ℝ) : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) ∈ grotzschRing s := by
    intro θ h0 hπ
    constructor
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hr1
    · intro hmem'
      have hmem'' : ((r : ℝ) : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) ∈ grotzschInner s :=
        hmem'
      rw [grotzschInner_eq hs0.le] at hmem''
      obtain ⟨him, hre0, hres⟩ := hmem''
      have hsin : Real.sin θ = 0 := by
        have h : r * Real.sin θ = 0 := by
          simpa [Complex.mul_im, Complex.exp_ofReal_mul_I_im] using him
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hr0.ne'
        · exact h'
      have hθcase : θ = 0 ∨ θ = π := by
        by_contra hcon
        push Not at hcon
        exact absurd hsin (Real.sin_pos_of_pos_of_lt_pi
          (lt_of_le_of_ne h0 (Ne.symm hcon.1)) (lt_of_le_of_ne hπ hcon.2)).ne'
      rcases hθcase with rfl | rfl
      · -- the point `r` lies beyond the slit tip
        have h : r ≤ s := by simpa [Complex.mul_re] using hres
        linarith
      · -- the point `-r` has negative real part
        have h : 0 ≤ -r := by
          simpa [Complex.mul_re, Complex.exp_pi_mul_I] using hre0
        linarith
  -- the point at angle `θ₁` lies strictly on the slit side of the bisecting diameter
  have hzS : ((((r : ℝ) : ℂ) * Complex.exp ((θ₁ : ℝ) * Complex.I))
      * Complex.exp (-(α * Complex.I))).im < 0 := by
    rw [mul_assoc, ← Complex.exp_add]
    have heq : ((θ₁ : ℝ) : ℂ) * Complex.I + -(α * Complex.I)
        = ((θ₁ - α : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [heq]
    have him : ((((r : ℝ) : ℂ) * Complex.exp (((θ₁ - α : ℝ) : ℂ) * Complex.I))).im
        = r * Real.sin (θ₁ - α) := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.exp_ofReal_mul_I_im]
    rw [him]
    apply mul_neg_of_pos_of_neg hr0
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · rw [hαdef]; linarith
    · have hπpos : 0 < π := Real.pi_pos
      rw [hαdef]; linarith
  -- the reflection sends the point at angle `θ₁` to the point at angle `θ₂`
  have hσz : Complex.exp ((2 * α : ℝ) * Complex.I)
      * (starRingEnd ℂ) (((r : ℝ) : ℂ) * Complex.exp ((θ₁ : ℝ) * Complex.I))
      = ((r : ℝ) : ℂ) * Complex.exp ((θ₂ : ℝ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_left_comm, ← Complex.exp_add]
    have heq : ((2 * α : ℝ) : ℂ) * Complex.I + (θ₁ : ℝ) * -Complex.I
        = ((θ₂ : ℝ) : ℂ) * Complex.I := by
      rw [hαdef]; push_cast; ring
    rw [heq]
  have h := grotzschPotential_reflection_le hs0 hs1 huh huc hu0 hu1 hub hα0 hαπ
    (hmem θ₁ hθ1 (by linarith)) (by rw [hσz]; exact hmem θ₂ (by linarith) hθ2) hzS
  rw [hσz] at h
  exact h

/-- **Angular monotonicity on every circle inside the disk.** On each circle `|z| = r` with
`0 < r < 1` — including the radii `r ≤ s` where the circle meets the slit — the potential is
nondecreasing in the angle `θ ∈ [0, π]`. For `r > s` this is the polarization statement
`grotzschPotential_monotone_arg`; for `r ≤ s` the point at angle `0` lies on the slit where the
potential vanishes, and angles in `(0, π]` are handled by the same reflection across the
bisecting diameter. -/
theorem grotzschPotential_monotone_arg_ball {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u : ℂ → ℝ}
    (huh : InnerProductSpace.HarmonicOnNhd u (grotzschRing s))
    (huc : ContinuousOn u (closure (grotzschRing s)))
    (hu0 : ∀ z ∈ grotzschInner s, u z = 0) (hu1 : ∀ z ∈ grotzschOuter, u z = 1)
    (hub : ∀ z ∈ grotzschRing s, 0 ≤ u z ∧ u z ≤ 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {θ₁ θ₂ : ℝ}
    (hθ1 : 0 ≤ θ₁) (hθ12 : θ₁ ≤ θ₂) (hθ2 : θ₂ ≤ π) :
    u (r * Complex.exp (θ₁ * Complex.I)) ≤ u (r * Complex.exp (θ₂ * Complex.I)) := by
  rcases eq_or_lt_of_le hθ12 with rfl | hlt
  · exact le_refl _
  rcases lt_or_ge s r with hrs | hrs
  · exact grotzschPotential_monotone_arg hs0 hs1 huh huc hu0 hu1 hub hrs hr1 hθ1 hθ12 hθ2
  -- `r ≤ s`: circle points at angles in `(0, π]` lie in the ring
  have hmem : ∀ θ : ℝ, 0 < θ → θ ≤ π →
      ((r : ℝ) : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) ∈ grotzschRing s := by
    intro θ h0 hπ
    constructor
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hr1
    · intro hmem'
      have hmem'' : ((r : ℝ) : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) ∈ grotzschInner s :=
        hmem'
      rw [grotzschInner_eq hs0.le] at hmem''
      obtain ⟨him, hre0, _⟩ := hmem''
      have hsin : Real.sin θ = 0 := by
        have h : r * Real.sin θ = 0 := by
          simpa [Complex.mul_im, Complex.exp_ofReal_mul_I_im] using him
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hr0.ne'
        · exact h'
      have hθπ : θ = π := by
        by_contra hne
        exact absurd hsin
          (Real.sin_pos_of_pos_of_lt_pi h0 (lt_of_le_of_ne hπ hne)).ne'
      subst hθπ
      have h : (0 : ℝ) ≤ -r := by
        simpa [Complex.mul_re, Complex.exp_pi_mul_I] using hre0
      linarith
  rcases eq_or_lt_of_le hθ1 with hθ10 | hθ10
  · -- `θ₁ = 0`: the base point lies on the slit, where `u` vanishes
    have hpt1 : ((r : ℝ) : ℂ) * Complex.exp ((θ₁ : ℝ) * Complex.I) ∈ grotzschInner s := by
      rw [← hθ10]
      rw [grotzschInner_eq hs0.le]
      norm_num
      exact ⟨hr0.le, hrs⟩
    rw [hu0 _ hpt1]
    exact (hub _ (hmem θ₂ (lt_of_le_of_lt (hθ10 ▸ hθ1) hlt) hθ2)).1
  · -- `0 < θ₁`: reflection across the bisecting diameter
    set α : ℝ := (θ₁ + θ₂) / 2 with hαdef
    have hα0 : 0 < α := by rw [hαdef]; linarith
    have hαπ : α < π := by rw [hαdef]; linarith
    have hzS : ((((r : ℝ) : ℂ) * Complex.exp ((θ₁ : ℝ) * Complex.I))
        * Complex.exp (-(α * Complex.I))).im < 0 := by
      rw [mul_assoc, ← Complex.exp_add]
      have heq : ((θ₁ : ℝ) : ℂ) * Complex.I + -(α * Complex.I)
          = ((θ₁ - α : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [heq]
      have him : ((((r : ℝ) : ℂ) * Complex.exp (((θ₁ - α : ℝ) : ℂ) * Complex.I))).im
          = r * Real.sin (θ₁ - α) := by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im]
      rw [him]
      apply mul_neg_of_pos_of_neg hr0
      apply Real.sin_neg_of_neg_of_neg_pi_lt
      · rw [hαdef]; linarith
      · have hπpos : 0 < π := Real.pi_pos
        rw [hαdef]; linarith
    have hσz : Complex.exp ((2 * α : ℝ) * Complex.I)
        * (starRingEnd ℂ) (((r : ℝ) : ℂ) * Complex.exp ((θ₁ : ℝ) * Complex.I))
        = ((r : ℝ) : ℂ) * Complex.exp ((θ₂ : ℝ) * Complex.I) := by
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I, mul_left_comm, ← Complex.exp_add]
      have heq : ((2 * α : ℝ) : ℂ) * Complex.I + (θ₁ : ℝ) * -Complex.I
          = ((θ₂ : ℝ) : ℂ) * Complex.I := by
        rw [hαdef]; push_cast; ring
      rw [heq]
    have h := grotzschPotential_reflection_le hs0 hs1 huh huc hu0 hu1 hub hα0 hαπ
      (hmem θ₁ hθ10 (by linarith)) (by rw [hσz]; exact hmem θ₂ (by linarith) hθ2) hzS
    rw [hσz] at h
    exact h

/-! ## The Baernstein star function of the Grötzsch potential -/

open scoped ENNReal

/-- On the open unit disk the zero-extension of the potential agrees with the potential itself:
off the ring the disk point lies on the slit, where the potential vanishes. -/
private theorem indicator_grotzschRing_eq_of_mem_ball {s : ℝ} {v : ℂ → ℝ}
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) {z : ℂ} (hz : ‖z‖ < 1) :
    Set.indicator (grotzschRing s) v z = v z := by
  by_cases hzr : z ∈ grotzschRing s
  · exact Set.indicator_of_mem hzr v
  · have hzin : z ∈ grotzschInner s := by
      by_contra hno
      exact hzr ⟨mem_ball_zero_iff.mpr hz, hno⟩
    rw [Set.indicator_of_notMem hzr, hv0 z hzin]

/-- Circle points at angles in the open range `(0, 2π)` lie in the Grötzsch ring: the slit sits on
the angle-`0` ray, and the only real point of the arc is `-r`, which has negative real part. -/
private theorem circle_arc_mem_grotzschRing {s r x : ℝ} (hs : 0 ≤ s) (hr0 : 0 < r) (hr1 : r < 1)
    (hx0 : 0 < x) (hx2 : x < 2 * π) :
    (r : ℂ) * Complex.exp ((x : ℂ) * Complex.I) ∈ grotzschRing s := by
  constructor
  · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hr1
  · intro hmem'
    have hmem'' : (r : ℂ) * Complex.exp ((x : ℂ) * Complex.I) ∈ grotzschInner s := hmem'
    rw [grotzschInner_eq hs] at hmem''
    obtain ⟨him, hre0, _⟩ := hmem''
    have hsin : Real.sin x = 0 := by
      have h : r * Real.sin x = 0 := by
        simpa [Complex.mul_im, Complex.exp_ofReal_mul_I_im] using him
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr0.ne'
      · exact h'
    rcases lt_trichotomy x π with hcase | hcase | hcase
    · exact absurd hsin (Real.sin_pos_of_pos_of_lt_pi hx0 hcase).ne'
    · subst hcase
      have h : (0 : ℝ) ≤ -r := by
        simpa [Complex.mul_re, Complex.exp_pi_mul_I] using hre0
      linarith
    · have hneg : Real.sin x < 0 := by
        have h1 : Real.sin (x - 2 * π) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
        have h2 := Real.sin_add_two_pi (x - 2 * π)
        rw [show x - 2 * π + 2 * π = x by ring] at h2
        rw [h2]
        exact h1
      exact absurd hsin hneg.ne

/-- Conjugation symmetry of the potential on circles: the value at the angle `-ψ` equals the value
at `ψ`, since the two points are complex conjugates and the closed disk is the ring closure. -/
private theorem grotzschPotential_circle_neg_arg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ψ : ℝ) :
    v ((r : ℂ) * Complex.exp (((-ψ : ℝ) : ℂ) * Complex.I))
      = v ((r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) := by
  have hc : (starRingEnd ℂ) ((r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp (((-ψ : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring_nf
  have hmem : (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) ∈ closure (grotzschRing s) := by
    rw [closure_grotzschRing hs0.le, mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hr1
  rw [← hc]
  exact grotzschPotential_conj hs0 hs1 hvh hvc hv0 hv1 _ hmem

/-- **The star function of the Grötzsch potential is the centered-arc integral.** For the
zero-extension `ṽ = 1_{grotzschRing s}·v` of the potential, the Baernstein star value at radius
`e^ξ < 1` and half-aperture `θ ∈ (0, π)` is the integral of `v` over the arc of aperture `2θ`
centered on the negative real axis:

`(ṽ★(e^ξ, θ)).toReal = ∫_{(π−θ, π+θ)} v(e^ξ e^{iφ}) dφ`.

The angular profile of `ṽ` at any radius below `1` is symmetric about the angle `π` (conjugation
symmetry) with a central trough on the slit axis (angular monotonicity), so its symmetric-
decreasing rearrangement is the half-period translate and the star integral collapses to the
centered arc. -/
theorem starFunction_grotzsch_eq_arcIntegral {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvb : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1)
    {ξ θ : ℝ} (hξ : ξ < 0) (hθπ : θ < π) :
    (starFunction 0 (Set.indicator (grotzschRing s) v) (Real.exp ξ) θ).toReal
      = ∫ φ in Set.Ioo (π - θ) (π + θ),
          v ((Real.exp ξ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) := by
  set r : ℝ := Real.exp ξ with hrdef
  have hr0 : 0 < r := Real.exp_pos ξ
  have hr1 : r < 1 := by
    rw [hrdef, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hξ
  have hπθ : 0 < π - θ := by linarith
  set L : ℝ → ℝ≥0∞ :=
    fun φ => ENNReal.ofReal (v ((r : ℂ) * Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I)))
    with hLdef
  -- the profile stored inside the star function is `L`
  have hgeq : (fun φ : ℝ => ENNReal.ofReal
        (angularProfile 0
          (fun z => ENNReal.ofReal (Set.indicator (grotzschRing s) v z)) r φ).toReal) = L := by
    funext φ
    simp only [angularProfile, zero_add]
    rw [ofReal_toReal_ofReal, indicator_grotzschRing_eq_of_mem_ball hv0 (by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hr1)]
  -- symmetry of the profile about the center `π`
  have hsymm : ∀ t : ℝ, L (2 * π / 2 + t) = L (2 * π / 2 - t) := by
    intro t
    simp only [hLdef]
    rw [show (2 * π / 2 + t - π : ℝ) = t by ring, show (2 * π / 2 - t - π : ℝ) = -t by ring,
      grotzschPotential_circle_neg_arg hs0 hs1 hvh hvc hv0 hv1 hr0 hr1.le t]
  -- monotonicity of the profile on the right half-period
  have hmono : MonotoneOn L (Set.Icc (2 * π / 2) (2 * π)) := by
    intro φ₁ h1 φ₂ h2 h12
    simp only [hLdef]
    apply ENNReal.ofReal_le_ofReal
    exact grotzschPotential_monotone_arg_ball hs0 hs1 hvh hvc hv0 hv1 hvb hr0 hr1
      (θ₁ := φ₁ - π) (θ₂ := φ₂ - π) (by linarith [h1.1]) (by linarith) (by linarith [h2.2])
  -- continuity of the profile
  have hcont : ContinuousOn L (Set.Icc (2 * π / 2) (2 * π)) := by
    rw [hLdef]
    apply ENNReal.continuous_ofReal.comp_continuousOn
    have hpath : Continuous fun φ : ℝ =>
        (r : ℂ) * Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I) := by fun_prop
    apply hvc.comp hpath.continuousOn
    intro φ _
    rw [closure_grotzschRing hs0.le, mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hr1.le
  -- the rearranged profile on the centered arc is the direct circle sample
  have hpt : ∀ x ∈ Set.Icc (π - θ) (π + θ), decreasingRearrangeSymm (2 * π) L x
      = ENNReal.ofReal (v ((r : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hπθ hx.1
    have hx2 : x < 2 * π := by
      have := hx.2
      linarith
    rw [decreasingRearrangeSymm_symmetric_trough hsymm hmono hcont ⟨hx0, hx2⟩]
    rcases le_or_gt x π with hxle | hxgt
    · rw [show |x - 2 * π / 2| = π - x by rw [abs_of_nonpos (by linarith)]; ring]
      simp only [hLdef]
      rw [show (2 * π - (π - x) - π : ℝ) = x by ring]
    · rw [show |x - 2 * π / 2| = x - π by rw [abs_of_pos (by linarith)]; ring]
      simp only [hLdef]
      rw [show (2 * π - (x - π) - π : ℝ) = 2 * π - x by ring]
      have harg : ((2 * π - x : ℝ) : ℂ) * Complex.I
          = ((-x : ℝ) : ℂ) * Complex.I + 2 * ↑π * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one,
        grotzschPotential_circle_neg_arg hs0 hs1 hvh hvc hv0 hv1 hr0 hr1.le x]
  -- collapse the star function to the centered-arc lintegral
  have hstar0 : starFunction 0 (Set.indicator (grotzschRing s) v) r θ
      = ∫⁻ x in Set.Icc (π - θ) (π + θ),
          ENNReal.ofReal (v ((r : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) := by
    have hunf : starFunction 0 (Set.indicator (grotzschRing s) v) r θ
        = ∫⁻ x in Set.Icc (2 * π / 2 - θ) (2 * π / 2 + θ),
            decreasingRearrangeSymm (2 * π) L x := by
      unfold starFunction starProfile
      rw [hgeq]
    rw [hunf, show (2 * π / 2 - θ : ℝ) = π - θ by ring,
      show (2 * π / 2 + θ : ℝ) = π + θ by ring]
    exact setLIntegral_congr_fun measurableSet_Icc fun x hx => hpt x hx
  -- pass from the lintegral to the Bochner integral over the open arc
  have hnn : ∀ x ∈ Set.Ioo (π - θ) (π + θ),
      0 ≤ v ((r : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) := by
    intro x hx
    exact (hvb _ (circle_arc_mem_grotzschRing hs0.le hr0 hr1 (hπθ.trans hx.1)
      (by linarith [hx.2]))).1
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioo (π - θ) (π + θ))]
      fun x : ℝ => v ((r : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) :=
    ae_restrict_of_forall_mem measurableSet_Ioo hnn
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => v ((r : ℂ) * Complex.exp ((x : ℂ) * Complex.I)))
      (volume.restrict (Set.Ioo (π - θ) (π + θ))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    have hpath : Continuous fun x : ℝ => (r : ℂ) * Complex.exp ((x : ℂ) * Complex.I) := by
      fun_prop
    apply hvc.comp hpath.continuousOn
    intro x _
    rw [closure_grotzschRing hs0.le, mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hr1.le
  rw [hstar0, integral_eq_lintegral_of_nonneg_ae hae hmeas]
  congr 1
  exact (setLIntegral_congr Ioo_ae_eq_Icc).symm

/-! ## Primitives of holomorphic functions on products of intervals -/

/-- **Primitive of a holomorphic function on a product of intervals.** A function holomorphic on
an open set of the form `A ×ℂ B` (`A`, `B` order-connected open sets of reals) has a global
primitive there: the wedge integral from a base point — a horizontal then a vertical segment —
is well defined because both legs stay in the product, path independence on rectangles is the
Cauchy–Goursat theorem, and near any point the wedge integral agrees with a local primitive on a
ball up to a constant. -/
theorem exists_primitive_reProdIm {A B : Set ℝ} (hA : Set.OrdConnected A)
    (hB : Set.OrdConnected B) (hAo : IsOpen A) (hBo : IsOpen B) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (A ×ℂ B)) {c : ℂ} (hc : c ∈ A ×ℂ B) :
    ∃ Q : ℂ → ℂ, ∀ z ∈ A ×ℂ B, HasDerivAt Q (f z) z := by
  have hUopen : IsOpen (A ×ℂ B) := hAo.reProdIm hBo
  have hc' : c.re ∈ A ∧ c.im ∈ B := Complex.mem_reProdIm.mp hc
  -- integrability of `f` along horizontal and vertical segments in the product
  have hsegH : ∀ a₁ a₂ b : ℝ, a₁ ∈ A → a₂ ∈ A → b ∈ B →
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (b : ℂ) * Complex.I)) volume a₁ a₂ := by
    intro a₁ a₂ b ha₁ ha₂ hb
    apply ContinuousOn.intervalIntegrable
    apply hf.continuousOn.comp (Continuous.continuousOn (by fun_prop))
    intro x hx
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using hA.uIcc_subset ha₁ ha₂ hx, by simpa using hb⟩
  have hsegV : ∀ a b₁ b₂ : ℝ, a ∈ A → b₁ ∈ B → b₂ ∈ B →
      IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume b₁ b₂ := by
    intro a b₁ b₂ ha hb₁ hb₂
    apply ContinuousOn.intervalIntegrable
    apply hf.continuousOn.comp (Continuous.continuousOn (by fun_prop))
    intro y hy
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ha, by simpa using hB.uIcc_subset hb₁ hb₂ hy⟩
  -- Cauchy–Goursat on axis-parallel rectangles inside the product
  have hrect0 : ∀ a₁ a₂ b₁ b₂ : ℝ, a₁ ∈ A → a₂ ∈ A → b₁ ∈ B → b₂ ∈ B →
      (∫ x in a₁..a₂, f ((x : ℂ) + (b₁ : ℂ) * Complex.I))
        - (∫ x in a₁..a₂, f ((x : ℂ) + (b₂ : ℂ) * Complex.I))
        + Complex.I * (∫ y in b₁..b₂, f ((a₂ : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in b₁..b₂, f ((a₁ : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂
    have hsub : Set.uIcc a₁ a₂ ×ℂ Set.uIcc b₁ b₂ ⊆ A ×ℂ B := by
      intro p hp
      rw [Complex.mem_reProdIm] at hp ⊢
      exact ⟨hA.uIcc_subset ha₁ ha₂ hp.1, hB.uIcc_subset hb₁ hb₂ hp.2⟩
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a₁ : ℂ) + (b₁ : ℂ) * Complex.I) ((a₂ : ℂ) + (b₂ : ℂ) * Complex.I)
      (hf.mono (by simpa using hsub))
    simpa using h
  -- the wedge primitive from the base point `c`
  set Q : ℂ → ℂ := fun w => (∫ x in c.re..w.re, f ((x : ℂ) + (c.im : ℂ) * Complex.I))
      + Complex.I * ∫ y in c.im..w.im, f ((w.re : ℂ) + (y : ℂ) * Complex.I) with hQdef
  -- global identity: the wedge increment between any two points of the product
  have hkey : ∀ z ∈ A ×ℂ B, ∀ w ∈ A ×ℂ B,
      Q w - Q z = (∫ x in z.re..w.re, f ((x : ℂ) + (z.im : ℂ) * Complex.I))
        + Complex.I * ∫ y in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * Complex.I) := by
    intro z hz w hw
    have hz' : z.re ∈ A ∧ z.im ∈ B := Complex.mem_reProdIm.mp hz
    have hw' : w.re ∈ A ∧ w.im ∈ B := Complex.mem_reProdIm.mp hw
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hsegH c.re z.re c.im hc'.1 hz'.1 hc'.2) (hsegH z.re w.re c.im hz'.1 hw'.1 hc'.2)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hsegV w.re c.im z.im hw'.1 hc'.2 hz'.2) (hsegV w.re z.im w.im hw'.1 hz'.2 hw'.2)
    have h3 := hrect0 z.re w.re c.im z.im hz'.1 hw'.1 hc'.2 hz'.2
    simp only [hQdef]
    linear_combination -h1 - Complex.I * h2 + h3
  refine ⟨Q, fun z hz => ?_⟩
  have hz' : z.re ∈ A ∧ z.im ∈ B := Complex.mem_reProdIm.mp hz
  obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hUopen z hz
  obtain ⟨q, hq⟩ := (hf.mono hρsub).isExactOn_ball
  -- near `z` the wedge primitive agrees with the local ball primitive up to a constant
  have hloc : ∀ w ∈ Metric.ball z (ρ / 3), Q w = q w + (Q z - q z) := by
    intro w hw
    have hwz : ‖w - z‖ < ρ / 3 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have hwU : w ∈ A ×ℂ B := hρsub (Metric.ball_subset_ball (by linarith) hw)
    have hw' : w.re ∈ A ∧ w.im ∈ B := Complex.mem_reProdIm.mp hwU
    have hlegH : ∀ x ∈ Set.uIcc z.re w.re,
        ((x : ℂ) + (z.im : ℂ) * Complex.I) ∈ Metric.ball z ρ := by
      intro x hx
      have h1 : |x - z.re| ≤ |w.re - z.re| := Set.abs_sub_left_of_mem_uIcc hx
      have h2 : |w.re - z.re| ≤ ‖w - z‖ := by
        rw [show w.re - z.re = (w - z).re by simp]
        exact Complex.abs_re_le_norm _
      have hdiff : ((x : ℂ) + (z.im : ℂ) * Complex.I) - z = ((x - z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [Metric.mem_ball, dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hlegV : ∀ y ∈ Set.uIcc z.im w.im,
        ((w.re : ℂ) + (y : ℂ) * Complex.I) ∈ Metric.ball z ρ := by
      intro y hy
      have h1 : |y - z.im| ≤ |w.im - z.im| := Set.abs_sub_left_of_mem_uIcc hy
      have h2 : |w.im - z.im| ≤ ‖w - z‖ := by
        rw [show w.im - z.im = (w - z).im by simp]
        exact Complex.abs_im_le_norm _
      have h3 : |w.re - z.re| ≤ ‖w - z‖ := by
        rw [show w.re - z.re = (w - z).re by simp]
        exact Complex.abs_re_le_norm _
      have hdiff : ((w.re : ℂ) + (y : ℂ) * Complex.I) - z
          = ((w.re - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [Metric.mem_ball, dist_eq_norm, hdiff]
      calc ‖((w.re - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I‖
          ≤ ‖((w.re - z.re : ℝ) : ℂ)‖ + ‖((y - z.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |w.re - z.re| + |y - z.im| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
        _ < ρ := by linarith
    have hFTC1 : ∫ x in z.re..w.re, f ((x : ℂ) + (z.im : ℂ) * Complex.I)
        = q ((w.re : ℂ) + (z.im : ℂ) * Complex.I)
          - q ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => q ((x : ℂ) + (z.im : ℂ) * Complex.I))
      · intro x hx
        have houter : HasDerivAt (fun u : ℂ => q (u + (z.im : ℂ) * Complex.I))
            (f ((x : ℂ) + (z.im : ℂ) * Complex.I)) ((x : ℂ)) := by
          have h1 : HasDerivAt (fun u : ℂ => u + (z.im : ℂ) * Complex.I) 1 ((x : ℂ)) :=
            (hasDerivAt_id _).add_const _
          simpa using (hq _ (hlegH x hx)).comp ((x : ℂ)) h1
        exact houter.comp_ofReal
      · exact hsegH z.re w.re z.im hz'.1 hw'.1 hz'.2
    have hFTC2 : ∫ y in z.im..w.im, (f ((w.re : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
        = q ((w.re : ℂ) + (w.im : ℂ) * Complex.I)
          - q ((w.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => q ((w.re : ℂ) + (y : ℂ) * Complex.I))
      · intro y hy
        have houter : HasDerivAt (fun u : ℂ => q ((w.re : ℂ) + u * Complex.I))
            (f ((w.re : ℂ) + (y : ℂ) * Complex.I) * Complex.I) ((y : ℂ)) := by
          have h1 : HasDerivAt (fun u : ℂ => (w.re : ℂ) + u * Complex.I)
              Complex.I ((y : ℂ)) := by
            simpa using ((hasDerivAt_id ((y : ℂ))).mul_const Complex.I).const_add ((w.re : ℂ))
          simpa using (hq _ (hlegV y hy)).comp ((y : ℂ)) h1
        exact houter.comp_ofReal
      · exact (hsegV w.re z.im w.im hw'.1 hz'.2 hw'.2).mul_const Complex.I
    have hQdiff := hkey z hz w hwU
    have hImul : Complex.I * (∫ y in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * Complex.I))
        = ∫ y in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * Complex.I) * Complex.I := by
      rw [mul_comm]
      exact (intervalIntegral.integral_mul_const Complex.I fun y : ℝ =>
        f ((w.re : ℂ) + (y : ℂ) * Complex.I)).symm
    rw [hImul, hFTC1, hFTC2, Complex.re_add_im z, Complex.re_add_im w] at hQdiff
    linear_combination hQdiff
  have hev : Q =ᶠ[𝓝 z] fun w => q w + (Q z - q z) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z (by linarith)) hloc
  exact ((hq z (Metric.mem_ball_self hρ0)).add_const (Q z - q z)).congr_of_eventuallyEq hev

/-- The base point `-1` of the log-polar strip `{Re < 0} ×ℂ (-π, π)`. -/
private theorem neg_one_mem_strip : (-1 : ℂ) ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π := by
  rw [Complex.mem_reProdIm]
  constructor
  · simp
  · constructor <;> simp [Real.pi_pos]

/-- The shifted exponential `w ↦ exp (w + iπ) = -e^w` maps the log-polar strip
`{Re < 0} ×ℂ (-π, π)` into the Grötzsch ring: the modulus is `e^{Re w} < 1` and the image is real
only for `Im w = 0`, where it is negative, hence off the slit. -/
private theorem arcPoint_pi_mem_grotzschRing {s : ℝ} (hs : 0 ≤ s) {w : ℂ}
    (hw : w ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) :
    (0 : ℂ) + Complex.exp (w + (π : ℝ) * Complex.I) ∈ grotzschRing s := by
  rw [Complex.mem_reProdIm] at hw
  have hpt : (0 : ℂ) + Complex.exp (w + (π : ℝ) * Complex.I) = -Complex.exp w := by
    rw [zero_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hpt]
  constructor
  · rw [mem_ball_zero_iff, norm_neg, Complex.norm_exp]
    calc Real.exp w.re < Real.exp 0 := Real.exp_lt_exp.mpr hw.1
      _ = 1 := Real.exp_zero
  · intro hmem
    have hmem' : -Complex.exp w ∈ grotzschInner s := hmem
    rw [grotzschInner_eq hs] at hmem'
    obtain ⟨him, hre, _⟩ := hmem'
    have hsin : Real.sin w.im = 0 := by
      have h : (-Complex.exp w).im = -(Real.exp w.re * Real.sin w.im) := by
        rw [Complex.neg_im, Complex.exp_im]
      rw [h, neg_eq_zero] at him
      rcases mul_eq_zero.mp him with h' | h'
      · exact absurd h' (Real.exp_pos _).ne'
      · exact h'
    have him0 : w.im = 0 := by
      obtain ⟨h1, h2⟩ := hw.2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd hsin (Real.sin_neg_of_neg_of_neg_pi_lt hlt (by linarith)).ne
      · exact absurd hsin (Real.sin_pos_of_pos_of_lt_pi hgt h2).ne'
    have hre' : (-Complex.exp w).re = -Real.exp w.re := by
      rw [Complex.neg_re, Complex.exp_re, him0, Real.cos_zero, mul_one]
    rw [hre'] at hre
    linarith [Real.exp_pos w.re]

/-- **The pulled-back potential is the real part of a holomorphic function on the strip.** For
the Grötzsch potential `v`, there is a holomorphic `F` on the log-polar strip
`{Re < 0} ×ℂ (-π, π)` with `Re F(w) = v(exp(w + iπ))`: the complex gradient of the pull-back is
holomorphic and has a primitive on the strip, whose real part differs from the pull-back by a
constant. -/
private theorem exists_holomorphic_re_potential {s : ℝ} (hs : 0 ≤ s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) ∧
      ∀ z ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π,
        (F z).re = v (0 + Complex.exp (z + (π : ℝ) * Complex.I)) := by
  have hWo : IsOpen (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) := isOpen_Iio.reProdIm isOpen_Ioo
  -- the complex gradient of the pull-back is holomorphic on the strip
  have hgdiff : DifferentiableOn ℂ (fun w : ℂ =>
      gradC v (0 + Complex.exp (w + (π : ℝ) * Complex.I))
        * Complex.exp (w + (π : ℝ) * Complex.I)) (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) := by
    apply DifferentiableOn.mul
    · exact (gradC_differentiableOn hvh).comp
        (Differentiable.differentiableOn (by fun_prop))
        (fun w hw => arcPoint_pi_mem_grotzschRing hs hw)
    · exact Differentiable.differentiableOn (by fun_prop)
  obtain ⟨F₀, hF₀⟩ := exists_primitive_reProdIm Set.ordConnected_Iio Set.ordConnected_Ioo
    isOpen_Iio isOpen_Ioo hgdiff neg_one_mem_strip
  -- both the real part of the primitive and the pull-back have the same Fréchet derivative
  have hhFD : ∀ w ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π,
      HasFDerivAt (fun w : ℂ => v (0 + Complex.exp (w + (π : ℝ) * Complex.I)))
        (Complex.reCLM.comp ((gradC v (0 + Complex.exp (w + (π : ℝ) * Complex.I))
          * Complex.exp (w + (π : ℝ) * Complex.I)) • (ContinuousLinearMap.id ℝ ℂ))) w := by
    intro w hw
    exact hasFDerivAt_fibre (p := 0) (u := v) π
      ((hvh _ (arcPoint_pi_mem_grotzschRing hs hw)).1.differentiableAt (by norm_num))
  have hFFD : ∀ w ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π,
      HasFDerivAt (fun z => (F₀ z).re)
        (Complex.reCLM.comp ((gradC v (0 + Complex.exp (w + (π : ℝ) * Complex.I))
          * Complex.exp (w + (π : ℝ) * Complex.I)) • (ContinuousLinearMap.id ℝ ℂ))) w := by
    intro w hw
    have hFr : HasFDerivAt F₀ ((gradC v (0 + Complex.exp (w + (π : ℝ) * Complex.I))
        * Complex.exp (w + (π : ℝ) * Complex.I)) • (ContinuousLinearMap.id ℝ ℂ)) w := by
      rw [hasFDerivAt_iff_isLittleO]
      refine (hF₀ w hw).isLittleO.congr_left fun t => ?_
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      ring
    have h := Complex.reCLM.hasFDerivAt.comp w hFr
    simpa [Function.comp] using h
  -- convexity of the strip
  have hWconv : Convex ℝ (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) := by
    intro a ha b hb ta tb hta htb htab
    rw [Complex.mem_reProdIm] at ha hb ⊢
    constructor
    · have h := (convex_Iio (0 : ℝ)) ha.1 hb.1 hta htb htab
      simpa [Complex.add_re, Complex.smul_re, smul_eq_mul] using h
    · have h := (convex_Ioo (-π) π) ha.2 hb.2 hta htb htab
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using h
  -- normalize by the value at the base point
  set κ : ℝ := (F₀ (-1)).re - v (0 + Complex.exp (-1 + (π : ℝ) * Complex.I)) with hκdef
  refine ⟨fun z => F₀ z - (κ : ℂ), fun z hz =>
    ((hF₀ z hz).differentiableAt.sub_const _).differentiableWithinAt, ?_⟩
  have h1 : DifferentiableOn ℝ (fun z => (F₀ z).re - κ)
      (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) :=
    fun w hw => ((hFFD w hw).sub_const κ).differentiableAt.differentiableWithinAt
  have h2 : DifferentiableOn ℝ (fun z : ℂ => v (0 + Complex.exp (z + (π : ℝ) * Complex.I)))
      (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) :=
    fun w hw => (hhFD w hw).differentiableAt.differentiableWithinAt
  have heq : Set.EqOn (fun z => (F₀ z).re - κ)
      (fun z : ℂ => v (0 + Complex.exp (z + (π : ℝ) * Complex.I)))
      (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) := by
    refine hWconv.eqOn_of_fderivWithin_eq h1 h2 hWo.uniqueDiffOn ?_ neg_one_mem_strip ?_
    · intro w hw
      rw [fderivWithin_of_isOpen hWo hw, fderivWithin_of_isOpen hWo hw,
        ((hFFD w hw).sub_const κ).fderiv, (hhFD w hw).fderiv]
    · rw [hκdef]
      ring
  intro z hz
  rw [Complex.sub_re, Complex.ofReal_re]
  exact heq hz

/-- **The star surface of the Grötzsch potential is harmonic on the half-strip.** For the
zero-extension `ṽ = 1_{grotzschRing s}·v` of the Grötzsch potential, the log-polar star surface
`ṽ★(w) = (starFunction 0 ṽ (e^{Re w}) (Im w)).toReal` is harmonic (not merely subharmonic) on
`{Re w < 0, 0 < Im w < π}`. By `starFunction_grotzsch_eq_arcIntegral` the star value is the arc
integral `∫_{-Im w}^{Im w} Re F(Re w + it) dt` for a holomorphic `F` on the strip, which by the
fundamental theorem of calculus along the vertical segment equals `Im Q(w) - Im Q(w̄)` for a
primitive `Q` of `F` — a difference of harmonic functions. -/
theorem starPlane_harmonicOn_grotzsch {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvb : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    InnerProductSpace.HarmonicOnNhd (starPlane 0 (Set.indicator (grotzschRing s) v))
      {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} := by
  obtain ⟨F, hFdiff, hFre⟩ := exists_holomorphic_re_potential hs0.le hvh
  obtain ⟨Q, hQ⟩ := exists_primitive_reProdIm Set.ordConnected_Iio Set.ordConnected_Ioo
    isOpen_Iio isOpen_Ioo hFdiff neg_one_mem_strip
  have hQdiffOn : DifferentiableOn ℂ Q (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) :=
    fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt
  have hQanalytic : AnalyticOnNhd ℂ Q (Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π) :=
    hQdiffOn.analyticOnNhd (isOpen_Iio.reProdIm isOpen_Ioo)
  have hHopen : IsOpen {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} := by
    have h1 : IsOpen {w : ℂ | w.re < 0} := isOpen_lt Complex.continuous_re continuous_const
    have h2 : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have h3 : IsOpen {w : ℂ | w.im < π} := isOpen_lt Complex.continuous_im continuous_const
    have hset : {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}
        = {w : ℂ | w.re < 0} ∩ ({w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < π}) := by
      ext w
      simp [Set.mem_inter_iff]
    rw [hset]
    exact h1.inter (h2.inter h3)
  -- the star surface agrees with `Im Q(w) - Im Q(w̄)` on the half-strip
  have hEq : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π},
      starPlane 0 (Set.indicator (grotzschRing s) v) w
        = (Q w).im - (Q ((starRingEnd ℂ) w)).im := by
    intro w hw
    obtain ⟨hwre, hwim0, hwimπ⟩ := hw
    have hseg : ∀ t ∈ Set.uIcc (-w.im) w.im,
        ((w.re : ℂ) + (t : ℂ) * Complex.I) ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      rw [Complex.mem_reProdIm]
      constructor
      · simpa using hwre
      · have him : ((w.re : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
        rw [him]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hint : IntervalIntegrable (fun t : ℝ => F ((w.re : ℂ) + (t : ℂ) * Complex.I))
        volume (-w.im) w.im := by
      apply ContinuousOn.intervalIntegrable
      exact hFdiff.continuousOn.comp (Continuous.continuousOn (by fun_prop)) hseg
    have hFTC : ∫ t in (-w.im)..w.im, (F ((w.re : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        = Q ((w.re : ℂ) + (w.im : ℂ) * Complex.I)
          - Q ((w.re : ℂ) + ((-w.im : ℝ) : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => Q ((w.re : ℂ) + (t : ℂ) * Complex.I))
      · intro t ht
        have houter : HasDerivAt (fun u : ℂ => Q ((w.re : ℂ) + u * Complex.I))
            (F ((w.re : ℂ) + (t : ℂ) * Complex.I) * Complex.I) ((t : ℂ)) := by
          have h1 : HasDerivAt (fun u : ℂ => (w.re : ℂ) + u * Complex.I)
              Complex.I ((t : ℂ)) := by
            simpa using ((hasDerivAt_id ((t : ℂ))).mul_const Complex.I).const_add ((w.re : ℂ))
          simpa using (hQ _ (hseg t ht)).comp ((t : ℂ)) h1
        exact houter.comp_ofReal
      · exact hint.mul_const Complex.I
    have he1 : ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w := Complex.re_add_im w
    have he2 : ((w.re : ℂ) + ((-w.im : ℝ) : ℂ) * Complex.I) = (starRingEnd ℂ) w := by
      apply Complex.ext <;> simp
    calc starPlane 0 (Set.indicator (grotzschRing s) v) w
        = (starFunction 0 (Set.indicator (grotzschRing s) v) (Real.exp w.re) w.im).toReal := rfl
      _ = ∫ φ in Set.Ioo (π - w.im) (π + w.im),
            v ((Real.exp w.re : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) :=
          starFunction_grotzsch_eq_arcIntegral hs0 hs1 hvh hvc hv0 hv1 hvb hwre hwimπ
      _ = ∫ φ in (π - w.im)..(π + w.im),
            v ((Real.exp w.re : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) := by
          rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
      _ = ∫ t in (-w.im)..w.im,
            v ((Real.exp w.re : ℂ) * Complex.exp (((t + π : ℝ) : ℂ) * Complex.I)) := by
          rw [intervalIntegral.integral_comp_add_right
            (fun φ => v ((Real.exp w.re : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) π,
            show -w.im + π = π - w.im by ring, show w.im + π = π + w.im by ring]
      _ = ∫ t in (-w.im)..w.im, (F ((w.re : ℂ) + (t : ℂ) * Complex.I)).re := by
          apply intervalIntegral.integral_congr
          intro t ht
          have hpteq : (0 : ℂ) + Complex.exp (((w.re : ℂ) + (t : ℂ) * Complex.I)
              + (π : ℝ) * Complex.I)
              = (Real.exp w.re : ℂ) * Complex.exp (((t + π : ℝ) : ℂ) * Complex.I) := by
            rw [zero_add, show ((w.re : ℂ) + (t : ℂ) * Complex.I) + (π : ℝ) * Complex.I
                = (w.re : ℂ) + ((t + π : ℝ) : ℂ) * Complex.I by push_cast; ring,
              Complex.exp_add, Complex.ofReal_exp]
          simp only [hFre _ (hseg t ht), hpteq]
      _ = (∫ t in (-w.im)..w.im, F ((w.re : ℂ) + (t : ℂ) * Complex.I)).re := by
          simpa using Complex.reCLM.intervalIntegral_comp_comm hint
      _ = (Q w).im - (Q ((starRingEnd ℂ) w)).im := by
          rw [he1, he2] at hFTC
          have hmul : (∫ t in (-w.im)..w.im, F ((w.re : ℂ) + (t : ℂ) * Complex.I)) * Complex.I
              = Q w - Q ((starRingEnd ℂ) w) :=
            (intervalIntegral.integral_mul_const (a := -w.im) (b := w.im) Complex.I
              (fun t : ℝ => F ((w.re : ℂ) + (t : ℂ) * Complex.I))).symm.trans hFTC
          have hX : (∫ t in (-w.im)..w.im, F ((w.re : ℂ) + (t : ℂ) * Complex.I))
              = (Q w - Q ((starRingEnd ℂ) w)) * (-Complex.I) := by
            have h := congrArg (fun z => z * (-Complex.I)) hmul
            simpa [mul_assoc, mul_neg, Complex.I_mul_I] using h
          rw [hX]
          simp [Complex.mul_re]
  -- conclude: harmonic difference of imaginary parts of a holomorphic primitive
  intro w hw
  have hwW : w ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π := by
    rw [Complex.mem_reProdIm]
    exact ⟨hw.1, ⟨by linarith [hw.2.1, Real.pi_pos], hw.2.2⟩⟩
  have hconjW : (starRingEnd ℂ) w ∈ Set.Iio (0 : ℝ) ×ℂ Set.Ioo (-π) π := by
    rw [Complex.mem_reProdIm, Complex.conj_re, Complex.conj_im]
    exact ⟨hw.1, ⟨by linarith [hw.2.2], by linarith [hw.2.1, Real.pi_pos]⟩⟩
  have h1 : InnerProductSpace.HarmonicAt (fun z => (Q z).im) w :=
    (hQanalytic w hwW).harmonicAt_im
  have h2 : InnerProductSpace.HarmonicAt (fun z => (Q ((starRingEnd ℂ) z)).im) w := by
    have hpt : InnerProductSpace.HarmonicAt (fun z => (Q z).im) (Complex.conjLIE w) := by
      rw [show Complex.conjLIE w = (starRingEnd ℂ) w from Complex.conjLIE_apply w]
      exact (hQanalytic _ hconjW).harmonicAt_im
    have h := harmonicAt_comp_linearIsometryEquiv Complex.conjLIE hpt
    have heqf : ((fun z => (Q z).im) ∘ ⇑Complex.conjLIE)
        =ᶠ[𝓝 w] fun z => (Q ((starRingEnd ℂ) z)).im :=
      Filter.Eventually.of_forall fun y => by
        simp [Function.comp_apply, Complex.conjLIE_apply]
    exact (InnerProductSpace.harmonicAt_congr_nhds heqf).mp h
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (h1.sub h2)
  filter_upwards [hHopen.mem_nhds hw] with y hy using hEq y hy

end RiemannDynamics

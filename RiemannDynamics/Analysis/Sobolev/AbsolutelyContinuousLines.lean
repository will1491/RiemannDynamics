/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Absolute continuity on lines and weak derivatives

This file proves the **`ACL ⇒ Sobolev`** half of the absolutely-continuous-on-lines
characterization of `W^{1,p}_loc`: if `f : ℂ → ℂ` is absolutely continuous on
almost every horizontal line and on almost every vertical line, with the
classical line-derivatives given (almost everywhere) by locally integrable
functions `gx`, `gy`, then `gx`, `gy` are the weak partial derivatives of `f`,
so `f ∈ W^{1,p}_loc`.

This is the analytic input to the geometric ⇒ analytic direction of the
quasiconformal-map equivalence (`QC/Equivalence.lean`): a `K`-quasiconformal map
is shown by a length–area argument to be absolutely continuous on lines, and this
file converts that into the Sobolev membership `MemW12loc` and the weak Wirtinger
derivatives the analytic definition `IsQCAnalytic` speaks in.

## Main definitions

* `ACLHorizontal f g` — for almost every imaginary part `y`, the horizontal slice
  `x ↦ f ⟨x, y⟩` is absolutely continuous on every interval, and almost everywhere
  on the line its derivative is `g ⟨x, y⟩` (the `x`-partial of `f`);
* `ACLVertical f g` — the vertical analogue (the `y`-partial).

## Main results

* `hasWeakDirDeriv_one_of_aclHorizontal` — `ACLHorizontal f g` (with `f`, `g`
  locally integrable) gives the weak `x`-directional derivative
  `HasWeakDirDeriv 1 g f univ`;
* `hasWeakDirDeriv_I_of_aclVertical` — the vertical analogue, the weak
  `y`-directional derivative `HasWeakDirDeriv Complex.I g f univ`;
* `hasWeakGradient_of_acl` — packages the two directions into a weak gradient;
* `memWklocP_one_of_acl` — the Sobolev-membership conclusion `MemWklocP f 1 p univ`
  (in particular `MemW12loc f` for `p = 2`).

The proof of each direction is the classical Fubini + per-line integration by
parts: on each line, `∫ φ' · f = − ∫ φ · g` by the fundamental theorem of calculus
for absolutely continuous functions (`AbsolutelyContinuousOnInterval`,
boundary terms vanishing as `φ` has compact support), and Fubini assembles the
line identities into the two-dimensional weak-derivative identity.
-/

open MeasureTheory Complex
open scoped ENNReal ContDiff

namespace RiemannDynamics

variable {f g gx gy : ℂ → ℂ} {p : ℝ≥0∞}

/-- `f` is **absolutely continuous on almost every horizontal line**, with
`x`-partial `g`: for almost every imaginary part `y`, the horizontal slice
`x ↦ f ⟨x, y⟩` is absolutely continuous on every interval, and almost everywhere
on the line its classical derivative equals `g ⟨x, y⟩`. -/
def ACLHorizontal (f g : ℂ → ℂ) : Prop :=
  ∀ᵐ y : ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b) ∧
    (∀ᵐ x : ℝ, HasDerivAt (fun t : ℝ => f ⟨t, y⟩) (g ⟨x, y⟩) x)

/-- `f` is **absolutely continuous on almost every vertical line**, with
`y`-partial `g`: for almost every real part `x`, the vertical slice
`y ↦ f ⟨x, y⟩` is absolutely continuous on every interval, and almost everywhere
on the line its classical derivative equals `g ⟨x, y⟩`. -/
def ACLVertical (f g : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b) ∧
    (∀ᵐ y : ℝ, HasDerivAt (fun t : ℝ => f ⟨x, t⟩) (g ⟨x, y⟩) y)

set_option maxHeartbeats 400000 in
-- The Fubini transfer, the componentwise integration-by-parts, and the per-line
-- slice bookkeeping make this a long elaboration, so the heartbeat budget is raised.
/-- **Absolute continuity on horizontal lines yields the weak `x`-derivative.**
If `f` is absolutely continuous on almost every horizontal line with `x`-partial
`g`, and both `f` and `g` are locally integrable, then `g` is the weak
directional derivative of `f` in the real direction `1`. Proof: Fubini reduces
the two-dimensional integration-by-parts identity to the one-dimensional one on
each horizontal line, where the fundamental theorem of calculus for absolutely
continuous functions applies (the boundary terms vanish because the test function
has compact support). -/
theorem hasWeakDirDeriv_one_of_aclHorizontal
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hacl : ACLHorizontal f g) :
    HasWeakDirDeriv 1 g f Set.univ := by
  intro φ hφ_smooth hφ_cpt _
  -- **Composition of a Lipschitz map with an absolutely continuous function is AC.**
  have hLipComp : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F Y _ l K hl a b hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- **Per-line integration by parts** (the one-dimensional `∫ Φ' • F = − ∫ Φ • G`).
  -- Reduce to the `ℝ`-valued statement componentwise through `reCLM`/`imCLM`, where
  -- Mathlib's IBP for absolutely continuous functions applies; the boundary terms vanish
  -- since `Φ` has compact support.
  have lineIBP : ∀ (Φ : ℝ → ℝ) (F G : ℝ → ℂ),
      ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) →
      (∀ᵐ t : ℝ, HasDerivAt F (G t) t) →
      Integrable (fun t => deriv Φ t • F t) → Integrable (fun t => Φ t • G t) →
      (∫ t, (deriv Φ t) • F t) = - ∫ t, Φ t • G t := by
    intro Φ F G hΦ_smooth hΦ_cpt hF_ac hF_deriv hintL hintR
    obtain ⟨KΦ, hKΦ⟩ := hΦ_smooth.lipschitzWith_of_hasCompactSupport hΦ_cpt (by norm_num)
    have hΦ_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Φ a b :=
      fun a b => (hKΦ.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
    obtain ⟨R, hR, hRsupp⟩ := hΦ_cpt.exists_pos_le_norm
    have hΦa : Φ (-R) = 0 := hRsupp (-R) (by rw [norm_neg, Real.norm_eq_abs, abs_of_pos hR])
    have hΦb : Φ R = 0 := hRsupp R (by rw [Real.norm_eq_abs, abs_of_pos hR])
    have hΦ_zero : ∀ t ∉ Set.Icc (-R) R, Φ t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
    have hdΦ_zero : ∀ t ∉ Set.Icc (-R) R, deriv Φ t = 0 := by
      intro t ht
      have hne : Φ =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < -R from h)] with x hx
          rw [Set.mem_Iio] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
        · filter_upwards [Ioi_mem_nhds (show R < t from h)] with x hx
          rw [Set.mem_Ioi] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
      rw [Filter.EventuallyEq.deriv_eq hne]; simp
    -- The componentwise IBP, for any `ℝ`-linear projection `proj : ℂ →L[ℝ] ℝ`.
    have compIBP : ∀ proj : ℂ →L[ℝ] ℝ,
        (∫ t, deriv Φ t * proj (F t)) = - ∫ t, Φ t * proj (G t) := by
      intro proj
      have hab : (-R) ≤ R := by linarith
      set Fr : ℝ → ℝ := fun t => proj (F t) with hFr
      set Gr : ℝ → ℝ := fun t => proj (G t) with hGr
      have hFr_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Fr a b :=
        fun a b => hLipComp proj ‖proj‖₊ proj.lipschitz (hF_ac a b)
      have hFr_deriv : ∀ᵐ t : ℝ, deriv Fr t = Gr t := by
        filter_upwards [hF_deriv] with t ht
        have : HasDerivAt Fr (proj (G t)) t := by
          have := proj.hasFDerivAt.comp_hasDerivAt t ht; simpa [hFr] using this
        exact this.deriv
      have hIBP := (hΦ_ac (-R) R).integral_mul_deriv_eq_deriv_mul (hFr_ac (-R) R)
      rw [hΦa, hΦb] at hIBP
      simp only [zero_mul, sub_zero, zero_sub] at hIBP
      have hIBP2 : (∫ x in (-R)..R, Φ x * Gr x) = - ∫ x in (-R)..R, deriv Φ x * Fr x := by
        rw [← hIBP]; apply intervalIntegral.integral_congr_ae
        filter_upwards [hFr_deriv] with x hx _; rw [hx]
      have hconvL : (∫ x in (-R)..R, Φ x * Gr x) = ∫ x, Φ x * Gr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hΦ_zero t ht, zero_mul])
      have hconvR : (∫ x in (-R)..R, deriv Φ x * Fr x) = ∫ x, deriv Φ x * Fr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hdΦ_zero t ht, zero_mul])
      rw [hconvL, hconvR] at hIBP2
      change (∫ t, deriv Φ t * Fr t) = - ∫ t, Φ t * Gr t
      rw [hIBP2, neg_neg]
    apply Complex.ext
    · have hreL : (∫ t, (deriv Φ t) • F t).re = ∫ t, deriv Φ t * (F t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintL
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      have hreR : (∫ t, Φ t • G t).re = ∫ t, Φ t * (G t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintR
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      rw [hreL, Complex.neg_re, hreR]; exact compIBP Complex.reCLM
    · have himL : (∫ t, (deriv Φ t) • F t).im = ∫ t, deriv Φ t * (F t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintL
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      have himR : (∫ t, Φ t • G t).im = ∫ t, Φ t * (G t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintR
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      rw [himL, Complex.neg_im, himR]; exact compIBP Complex.imCLM
  -- **`(continuous, compactly supported real) • (locally integrable ℂ)` is integrable on `ℂ`.**
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m →
      ∀ {h : ℂ → ℂ}, LocallyIntegrable h → Integrable (fun z => m z • h z) := by
    intro m hm hcs h hh
    have hK : IsCompact (tsupport m) := hcs
    have hhon : IntegrableOn h (tsupport m) volume := hh.integrableOn_isCompact hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz; apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  set Lc : ℂ → ℂ := fun z => ((fderiv ℝ φ z) 1) • f z with hLc
  set Rc : ℂ → ℂ := fun z => φ z • g z with hRc
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) (1 : ℂ)) :=
    (hφ_smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) (1 : ℂ)) :=
    HasCompactSupport.fderiv_apply ℝ hφ_cpt 1
  have hintLc : Integrable Lc := integ _ hcont_dφ hcs_dφ hf
  have hintRc : Integrable Rc := integ _ hφ_smooth.continuous hφ_cpt hg
  -- **Transfer from `ℂ` to `ℝ × ℝ`** through the volume-preserving real-coordinate equivalence.
  have hemb := Complex.measurableEquivRealProd.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) := hmp.symm Complex.measurableEquivRealProd
  have transInt : ∀ (W : ℂ → ℂ), (∫ z : ℂ, W z) = ∫ p : ℝ × ℝ, W ⟨p.1, p.2⟩ := by
    intro W
    have key := hmp.integral_comp hemb (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩)
    rw [← key]; apply integral_congr_ae; filter_upwards with z; congr 1
  have transIntg : ∀ (W : ℂ → ℂ), Integrable W →
      Integrable (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩) (volume.prod volume) := by
    intro W hW
    rw [← Measure.volume_eq_prod]
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩) volume := by
      have := hW.aestronglyMeasurable.comp_quasiMeasurePreserving hmpsymm.quasiMeasurePreserving
      convert this using 1
    rw [← hmp.integrable_comp hmeas]; convert hW using 1
  change (∫ z, Lc z) = - ∫ z, Rc z
  rw [transInt Lc, transInt Rc]
  rw [Measure.volume_eq_prod] at *
  -- **Fubini** (inner integral over the first coordinate `x`, outer over `y`).
  rw [integral_prod_symm _ (transIntg Lc hintLc), integral_prod_symm _ (transIntg Rc hintRc)]
  rw [← integral_neg]
  apply integral_congr_ae
  -- Fubini also gives a.e.-`y` integrability of the inner slices.
  have hLslice := (transIntg Lc hintLc).prod_left_ae
  have hRslice := (transIntg Rc hintRc).prod_left_ae
  filter_upwards [hacl, hLslice, hRslice] with y hy_acl hy_Lint hy_Rint
  obtain ⟨hF_ac, hF_deriv⟩ := hy_acl
  -- The horizontal slice `t ↦ φ ⟨t, y⟩` of the test function is smooth and compactly supported.
  have hΦy_smooth : ContDiff ℝ ∞ (fun t : ℝ => φ ⟨t, y⟩) := by
    have hmap : ContDiff ℝ ∞ (fun t : ℝ => (⟨t, y⟩ : ℂ)) := by
      have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]; exact Complex.ofRealCLM.contDiff.add contDiff_const
    exact hφ_smooth.comp hmap
  have hΦy_cpt : HasCompactSupport (fun t : ℝ => φ ⟨t, y⟩) := by
    obtain ⟨R, hR, hRsupp⟩ := hφ_cpt.exists_pos_le_norm
    apply HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc
    intro t ht
    apply hRsupp
    have hle : ‖(t : ℝ)‖ ≤ ‖(⟨t, y⟩ : ℂ)‖ := by
      rw [Real.norm_eq_abs]; simpa using Complex.abs_re_le_norm (⟨t, y⟩ : ℂ)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
        _ ≤ _ := hle
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
        _ ≤ _ := hle
  -- The `x`-partial of `φ` is the derivative of the horizontal slice.
  have hsliceΦ : ∀ x : ℝ, HasDerivAt (fun t : ℝ => φ ⟨t, y⟩) ((fderiv ℝ φ ⟨x, y⟩) 1) x := by
    intro x
    have haff : HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
      have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]; simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
    have hfd : HasFDerivAt φ (fderiv ℝ φ ⟨x, y⟩) ⟨x, y⟩ :=
      (hφ_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    simpa using hfd.comp_hasDerivAt x haff
  have hLeq : (fun x => Lc ⟨x, y⟩) = fun x => deriv (fun t : ℝ => φ ⟨t, y⟩) x • f ⟨x, y⟩ := by
    funext x; rw [hLc, (hsliceΦ x).deriv]
  have hReq : (fun x => Rc ⟨x, y⟩) = fun x => (fun t : ℝ => φ ⟨t, y⟩) x • g ⟨x, y⟩ := by
    funext x; rw [hRc]
  change (∫ x, Lc ⟨x, y⟩) = -(∫ x, Rc ⟨x, y⟩)
  rw [hLeq, hReq]
  refine lineIBP (fun t => φ ⟨t, y⟩) (fun x => f ⟨x, y⟩) (fun x => g ⟨x, y⟩)
    hΦy_smooth hΦy_cpt hF_ac hF_deriv ?_ ?_
  · rw [← hLeq]; exact hy_Lint
  · rw [← hReq]; exact hy_Rint

set_option maxHeartbeats 400000 in
-- The Fubini transfer, the componentwise integration-by-parts, and the per-line
-- slice bookkeeping make this a long elaboration, so the heartbeat budget is raised.
/-- **Absolute continuity on vertical lines yields the weak `y`-derivative.**
The vertical analogue of `hasWeakDirDeriv_one_of_aclHorizontal`: if `f` is
absolutely continuous on almost every vertical line with `y`-partial `g`, and
both `f` and `g` are locally integrable, then `g` is the weak directional
derivative of `f` in the imaginary direction `Complex.I`. -/
theorem hasWeakDirDeriv_I_of_aclVertical
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hacl : ACLVertical f g) :
    HasWeakDirDeriv Complex.I g f Set.univ := by
  intro φ hφ_smooth hφ_cpt _
  -- **Composition of a Lipschitz map with an absolutely continuous function is AC.**
  have hLipComp : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F Y _ l K hl a b hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- **Per-line integration by parts** (the one-dimensional `∫ Φ' • F = − ∫ Φ • G`).
  have lineIBP : ∀ (Φ : ℝ → ℝ) (F G : ℝ → ℂ),
      ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) →
      (∀ᵐ t : ℝ, HasDerivAt F (G t) t) →
      Integrable (fun t => deriv Φ t • F t) → Integrable (fun t => Φ t • G t) →
      (∫ t, (deriv Φ t) • F t) = - ∫ t, Φ t • G t := by
    intro Φ F G hΦ_smooth hΦ_cpt hF_ac hF_deriv hintL hintR
    obtain ⟨KΦ, hKΦ⟩ := hΦ_smooth.lipschitzWith_of_hasCompactSupport hΦ_cpt (by norm_num)
    have hΦ_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Φ a b :=
      fun a b => (hKΦ.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
    obtain ⟨R, hR, hRsupp⟩ := hΦ_cpt.exists_pos_le_norm
    have hΦa : Φ (-R) = 0 := hRsupp (-R) (by rw [norm_neg, Real.norm_eq_abs, abs_of_pos hR])
    have hΦb : Φ R = 0 := hRsupp R (by rw [Real.norm_eq_abs, abs_of_pos hR])
    have hΦ_zero : ∀ t ∉ Set.Icc (-R) R, Φ t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
    have hdΦ_zero : ∀ t ∉ Set.Icc (-R) R, deriv Φ t = 0 := by
      intro t ht
      have hne : Φ =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < -R from h)] with x hx
          rw [Set.mem_Iio] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
        · filter_upwards [Ioi_mem_nhds (show R < t from h)] with x hx
          rw [Set.mem_Ioi] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
      rw [Filter.EventuallyEq.deriv_eq hne]; simp
    -- The componentwise IBP, for any `ℝ`-linear projection `proj : ℂ →L[ℝ] ℝ`.
    have compIBP : ∀ proj : ℂ →L[ℝ] ℝ,
        (∫ t, deriv Φ t * proj (F t)) = - ∫ t, Φ t * proj (G t) := by
      intro proj
      have hab : (-R) ≤ R := by linarith
      set Fr : ℝ → ℝ := fun t => proj (F t) with hFr
      set Gr : ℝ → ℝ := fun t => proj (G t) with hGr
      have hFr_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Fr a b :=
        fun a b => hLipComp proj ‖proj‖₊ proj.lipschitz (hF_ac a b)
      have hFr_deriv : ∀ᵐ t : ℝ, deriv Fr t = Gr t := by
        filter_upwards [hF_deriv] with t ht
        have : HasDerivAt Fr (proj (G t)) t := by
          have := proj.hasFDerivAt.comp_hasDerivAt t ht; simpa [hFr] using this
        exact this.deriv
      have hIBP := (hΦ_ac (-R) R).integral_mul_deriv_eq_deriv_mul (hFr_ac (-R) R)
      rw [hΦa, hΦb] at hIBP
      simp only [zero_mul, sub_zero, zero_sub] at hIBP
      have hIBP2 : (∫ x in (-R)..R, Φ x * Gr x) = - ∫ x in (-R)..R, deriv Φ x * Fr x := by
        rw [← hIBP]; apply intervalIntegral.integral_congr_ae
        filter_upwards [hFr_deriv] with x hx _; rw [hx]
      have hconvL : (∫ x in (-R)..R, Φ x * Gr x) = ∫ x, Φ x * Gr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hΦ_zero t ht, zero_mul])
      have hconvR : (∫ x in (-R)..R, deriv Φ x * Fr x) = ∫ x, deriv Φ x * Fr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hdΦ_zero t ht, zero_mul])
      rw [hconvL, hconvR] at hIBP2
      change (∫ t, deriv Φ t * Fr t) = - ∫ t, Φ t * Gr t
      rw [hIBP2, neg_neg]
    apply Complex.ext
    · have hreL : (∫ t, (deriv Φ t) • F t).re = ∫ t, deriv Φ t * (F t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintL
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      have hreR : (∫ t, Φ t • G t).re = ∫ t, Φ t * (G t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintR
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      rw [hreL, Complex.neg_re, hreR]; exact compIBP Complex.reCLM
    · have himL : (∫ t, (deriv Φ t) • F t).im = ∫ t, deriv Φ t * (F t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintL
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      have himR : (∫ t, Φ t • G t).im = ∫ t, Φ t * (G t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintR
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      rw [himL, Complex.neg_im, himR]; exact compIBP Complex.imCLM
  -- **`(continuous, compactly supported real) • (locally integrable ℂ)` is integrable on `ℂ`.**
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m →
      ∀ {h : ℂ → ℂ}, LocallyIntegrable h → Integrable (fun z => m z • h z) := by
    intro m hm hcs h hh
    have hK : IsCompact (tsupport m) := hcs
    have hhon : IntegrableOn h (tsupport m) volume := hh.integrableOn_isCompact hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz; apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  set Lc : ℂ → ℂ := fun z => ((fderiv ℝ φ z) Complex.I) • f z with hLc
  set Rc : ℂ → ℂ := fun z => φ z • g z with hRc
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) Complex.I) :=
    (hφ_smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) Complex.I) :=
    HasCompactSupport.fderiv_apply ℝ hφ_cpt Complex.I
  have hintLc : Integrable Lc := integ _ hcont_dφ hcs_dφ hf
  have hintRc : Integrable Rc := integ _ hφ_smooth.continuous hφ_cpt hg
  -- **Transfer from `ℂ` to `ℝ × ℝ`** through the volume-preserving real-coordinate equivalence.
  have hemb := Complex.measurableEquivRealProd.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) := hmp.symm Complex.measurableEquivRealProd
  have transInt : ∀ (W : ℂ → ℂ), (∫ z : ℂ, W z) = ∫ p : ℝ × ℝ, W ⟨p.1, p.2⟩ := by
    intro W
    have key := hmp.integral_comp hemb (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩)
    rw [← key]; apply integral_congr_ae; filter_upwards with z; congr 1
  have transIntg : ∀ (W : ℂ → ℂ), Integrable W →
      Integrable (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩) (volume.prod volume) := by
    intro W hW
    rw [← Measure.volume_eq_prod]
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩) volume := by
      have := hW.aestronglyMeasurable.comp_quasiMeasurePreserving hmpsymm.quasiMeasurePreserving
      convert this using 1
    rw [← hmp.integrable_comp hmeas]; convert hW using 1
  change (∫ z, Lc z) = - ∫ z, Rc z
  rw [transInt Lc, transInt Rc]
  rw [Measure.volume_eq_prod] at *
  -- **Fubini** (inner integral over the second coordinate `y`, outer over `x`).
  rw [integral_prod _ (transIntg Lc hintLc), integral_prod _ (transIntg Rc hintRc)]
  rw [← integral_neg]
  apply integral_congr_ae
  -- Fubini also gives a.e.-`x` integrability of the inner slices.
  have hLslice := (transIntg Lc hintLc).prod_right_ae
  have hRslice := (transIntg Rc hintRc).prod_right_ae
  filter_upwards [hacl, hLslice, hRslice] with x hx_acl hx_Lint hx_Rint
  obtain ⟨hF_ac, hF_deriv⟩ := hx_acl
  -- The vertical slice `t ↦ φ ⟨x, t⟩` of the test function is smooth and compactly supported.
  have hΦx_smooth : ContDiff ℝ ∞ (fun t : ℝ => φ ⟨x, t⟩) := by
    have hmap : ContDiff ℝ ∞ (fun t : ℝ => (⟨x, t⟩ : ℂ)) := by
      have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]; exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact hφ_smooth.comp hmap
  have hΦx_cpt : HasCompactSupport (fun t : ℝ => φ ⟨x, t⟩) := by
    obtain ⟨R, hR, hRsupp⟩ := hφ_cpt.exists_pos_le_norm
    apply HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc
    intro t ht
    apply hRsupp
    have hle : ‖(t : ℝ)‖ ≤ ‖(⟨x, t⟩ : ℂ)‖ := by
      rw [Real.norm_eq_abs]; simpa using Complex.abs_im_le_norm (⟨x, t⟩ : ℂ)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
        _ ≤ _ := hle
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
        _ ≤ _ := hle
  -- The `y`-partial of `φ` is the derivative of the vertical slice.
  have hsliceΦ : ∀ y : ℝ, HasDerivAt (fun t : ℝ => φ ⟨x, t⟩) ((fderiv ℝ φ ⟨x, y⟩) Complex.I) y := by
    intro y
    have haff : HasDerivAt (fun t : ℝ => (⟨x, t⟩ : ℂ)) Complex.I y := by
      have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      simpa using h1.const_add ((x : ℂ))
    have hfd : HasFDerivAt φ (fderiv ℝ φ ⟨x, y⟩) ⟨x, y⟩ :=
      (hφ_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    simpa using hfd.comp_hasDerivAt y haff
  have hLeq : (fun y => Lc ⟨x, y⟩) = fun y => deriv (fun t : ℝ => φ ⟨x, t⟩) y • f ⟨x, y⟩ := by
    funext y; rw [hLc, (hsliceΦ y).deriv]
  have hReq : (fun y => Rc ⟨x, y⟩) = fun y => (fun t : ℝ => φ ⟨x, t⟩) y • g ⟨x, y⟩ := by
    funext y; rw [hRc]
  change (∫ y, Lc ⟨x, y⟩) = -(∫ y, Rc ⟨x, y⟩)
  rw [hLeq, hReq]
  refine lineIBP (fun t => φ ⟨x, t⟩) (fun y => f ⟨x, y⟩) (fun y => g ⟨x, y⟩)
    hΦx_smooth hΦx_cpt hF_ac hF_deriv ?_ ?_
  · rw [← hLeq]; exact hx_Lint
  · rw [← hReq]; exact hx_Rint

/-- **A weak gradient from absolute continuity on lines.** If `f` is absolutely
continuous on almost every horizontal line with `x`-partial `gx` and on almost
every vertical line with `y`-partial `gy`, then `(gx, gy)` is a weak gradient of
`f`. -/
theorem hasWeakGradient_of_acl
    (hf : LocallyIntegrable f) (hgx : LocallyIntegrable gx) (hgy : LocallyIntegrable gy)
    (haclx : ACLHorizontal f gx) (hacly : ACLVertical f gy) :
    HasWeakGradient gx gy f Set.univ :=
  ⟨hasWeakDirDeriv_one_of_aclHorizontal hf hgx haclx,
    hasWeakDirDeriv_I_of_aclVertical hf hgy hacly⟩

/-- **`ACL ⇒ W^{1,p}_loc`.** If `f` is locally `Lᵖ`, absolutely continuous on
almost every horizontal and vertical line with `x`- and `y`-partials `gx`, `gy`
that are themselves locally `Lᵖ` (and locally integrable), then `f` lies in
`W^{1,p}_loc(ℂ)`. Specialized to `p = 2`, this is `MemW12loc f`, the Sobolev
class the analytic quasiconformal theory lives in. -/
theorem memWklocP_one_of_acl
    (hf : MemLpLocOn f p Set.univ)
    (hgx : MemLpLocOn gx p Set.univ) (hgy : MemLpLocOn gy p Set.univ)
    (hfli : LocallyIntegrable f) (hgxli : LocallyIntegrable gx) (hgyli : LocallyIntegrable gy)
    (haclx : ACLHorizontal f gx) (hacly : ACLVertical f gy) :
    MemWklocP f 1 p Set.univ :=
  ⟨hf, gx, gy, hasWeakGradient_of_acl hfli hgxli hgyli haclx hacly, hgx, hgy⟩

end RiemannDynamics

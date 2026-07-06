/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.MRMT.NeumannSeries
import RiemannDynamics.QC.MRMT.SmoothCase
import RiemannDynamics.QC.Calculus.AnalyticClosedness
import RiemannDynamics.QC.Calculus.Compactness

/-!
# Existence of quasiconformal solutions of the Beltrami equation

The measurable Riemann mapping theorem, existence half: every Beltrami coefficient
`b` (measurable `μ`, `‖μ‖∞ < 1`) admits a quasiconformal solution of `∂̄f = μ·∂f` —
`mrmt_exists : ∃ f, IsQCAnalytic f b`.

The compactly-vanishing case runs through the principal solution of
`QC/MRMT/NeumannSeries.lean` and three upgrades:

* **Injectivity** (`IsPrincipalSolution.injective`) — the exponential-quotient
  representation: for each `w` an auxiliary fixed-point solve produces `u_w` with
  `f z − f w = (z − w)·exp (u_w z)`, so `f` separates points.
* **Homeomorphism** (`IsPrincipalSolution.isHomeomorph`) — openness and surjectivity
  from injectivity, properness (`f − id → 0` at infinity), and the plane topology
  of sense data.
* **Orientation** (`IsPrincipalSolution.ae_det_pos`) — almost-everywhere positivity
  of the Jacobian, the nondegeneracy upgrade feeding `OrientationPreservingHomeo`.

The general (not compactly vanishing) coefficient reduces to the compact case by
splitting `μ` inside/outside a disk and conjugating the outer part by the inversion
`z ↦ 1/z`; the coefficient transformation rules under holomorphic pre- and
post-composition drive the reduction.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- **Injectivity of the principal solution** (Ahlfors–Bers 1960, Lemma 8 limit
argument). Truncate the coefficient to the support ball of the fixed-point field
(`f` is a principal solution of the truncated coefficient as well), mollify it
(`exists_contDiff_mollification_beltrami`), and solve the smooth cases
(`exists_contDiffOne_principalSolution`). The two-sided Hölder inequality
`‖z₁ − z₂‖ ≤ ‖fₙ z₁ − fₙ z₂‖ + c·‖fₙ z₁ − fₙ z₂‖^α` holds with constants uniform
over the smooth family (`isPrincipalSolution_two_sided_holder`); the smooth
solutions converge uniformly to `f`
(`isPrincipalSolution_tendstoUniformly_of_ae_tendsto`), so the inequality passes
to the limit and forces `f z₁ = f z₂ → z₁ = z₂`. -/
theorem IsPrincipalSolution.injective {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : Function.Injective f := by
  classical
  -- Step 0: unpack the principal-solution bundle and truncate the coefficient
  -- to the support ball of the fixed-point field `h`.
  obtain ⟨p, h, R, hp, hp', hmem, hsupp_h, heq, hrepr⟩ := hf
  have hμt_meas : Measurable fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    Measurable.ite (measurableSet_le measurable_norm measurable_const) b.measurable
      measurable_const
  have hμt_essSup :
      eLpNormEssSup (fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0) volume
        ≤ eLpNormEssSup b.μ volume := by
    rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hzR : ‖z‖ ≤ R
    · simp [hzR]
    · simp [hzR]
  obtain ⟨bt, hbtμ⟩ : ∃ bt : BeltramiCoeff,
      bt.μ = fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    ⟨⟨fun z => if ‖z‖ ≤ R then b.μ z else 0, hμt_meas,
      lt_of_le_of_lt hμt_essSup b.bound⟩, rfl⟩
  have hbt_le : eLpNormEssSup bt.μ volume ≤ eLpNormEssSup b.μ volume := by
    rw [hbtμ]; exact hμt_essSup
  have hbt_supp : ∀ z : ℂ, R < ‖z‖ → bt.μ z = 0 := by
    intro z hz
    rw [hbtμ]
    exact if_neg (not_le.mpr hz)
  -- `f` is also a principal solution of the truncated coefficient.
  have heq' : h =ᵐ[volume] fun z => bt.μ z * beurling h z + bt.μ z := by
    filter_upwards [heq] with z hzeq
    simp only [hbtμ]
    by_cases hzR : ‖z‖ ≤ R
    · rw [if_pos hzR]
      exact hzeq
    · rw [if_neg hzR, hsupp_h z (not_le.mp hzR), zero_mul, zero_add]
  have hf' : IsPrincipalSolution bt f := ⟨p, h, R, hp, hp', hmem, hsupp_h, heq', hrepr⟩
  -- Step 1: mollify the truncated coefficient.
  obtain ⟨bs, hbs_smooth, hbs_cpt, hbs_bnd, hbs_supp, hbs_tend⟩ :=
    exists_contDiff_mollification_beltrami bt hbt_supp
  -- Step 2: smooth-case principal solutions for the mollified coefficients.
  choose fs hfs _hfs1 _hfs2 _hfs3 using fun n =>
    exists_contDiffOne_principalSolution (bs n) (hbs_smooth n) (hbs_cpt n)
  -- Step 3: uniform dilatation bound `k = ‖μ‖∞ < 1` for the whole family.
  have hk0 : 0 ≤ b.normInf := b.normInf_nonneg
  have hk1 : b.normInf < 1 := b.normInf_lt_one
  have hofReal : ENNReal.ofReal b.normInf = eLpNormEssSup b.μ volume :=
    ENNReal.ofReal_toReal (ne_top_of_lt b.bound)
  have hbnd_n : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal b.normInf := by
    intro n
    rw [hofReal]
    exact (hbs_bnd n).trans hbt_le
  have hbnd' : eLpNormEssSup bt.μ volume ≤ ENNReal.ofReal b.normInf := by
    rw [hofReal]; exact hbt_le
  -- The uniform two-sided Hölder inequality over the smooth family.
  obtain ⟨c, α, hc0, hα, hholder⟩ :=
    isPrincipalSolution_two_sided_holder (R := R + 1) hk0 hk1
  have hineq : ∀ (n : ℕ) (z₁ z₂ : ℂ),
      ‖z₁ - z₂‖ ≤ ‖fs n z₁ - fs n z₂‖ + c * ‖fs n z₁ - fs n z₂‖ ^ α := fun n =>
    hholder (bs n) (fs n) (hbs_smooth n) (hbs_cpt n) (hbnd_n n) (hbs_supp n) (hfs n)
  -- Step 4: uniform convergence of the smooth solutions to `f`.
  have hbt_supp' : ∀ z : ℂ, R + 1 < ‖z‖ → bt.μ z = 0 := fun z hz =>
    hbt_supp z (by linarith)
  have hunif : TendstoUniformly fs f atTop :=
    isPrincipalSolution_tendstoUniformly_of_ae_tendsto hk0 hk1 hbnd_n hbnd'
      hbs_supp hbt_supp' hbs_tend hfs hf'
  -- Step 5: pass the Hölder inequality to the limit.
  intro z₁ z₂ hz
  have h1 : Tendsto (fun n => ‖fs n z₁ - fs n z₂‖) atTop (𝓝 0) := by
    have hsub := (hunif.tendsto_at z₁).sub (hunif.tendsto_at z₂)
    rw [hz, sub_self] at hsub
    simpa using hsub.norm
  have h2 : Tendsto (fun n => ‖fs n z₁ - fs n z₂‖ ^ α) atTop (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ α) 0 :=
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
    have hcomp := hcont.tendsto.comp h1
    simpa [Real.zero_rpow hα.ne'] using hcomp
  have h3 : Tendsto (fun n => ‖fs n z₁ - fs n z₂‖ + c * ‖fs n z₁ - fs n z₂‖ ^ α)
      atTop (𝓝 0) := by
    have := h1.add (h2.const_mul c)
    simpa using this
  have hle0 : ‖z₁ - z₂‖ ≤ 0 := ge_of_tendsto' h3 fun n => hineq n z₁ z₂
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle0)

/-- **The principal solution is a homeomorphism of the plane**: injective
(`IsPrincipalSolution.injective`), continuous, proper (`f − id → 0` at infinity),
with open image — hence a homeomorphism onto the connected plane. -/
theorem IsPrincipalSolution.isHomeomorph {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : IsHomeomorph f := by
  classical
  -- Continuity, injectivity, and normalization at infinity.
  have hcont : Continuous f := hf.continuous
  have hinj : Function.Injective f := hf.injective
  have hdecay : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0) :=
    hf.tendsto_sub_id_cocompact
  -- Properness: `‖f z‖ → ∞` as `‖z‖ → ∞`, since the displacement is eventually `< 1`.
  have hnormf : Tendsto (fun z : ℂ => ‖f z‖) (cocompact ℂ) atTop := by
    have h1 : Tendsto (fun z : ℂ => ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
      simpa using hdecay.norm
    have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖f z - z‖ < 1 :=
      h1.eventually_lt_const one_pos
    have hz1 : Tendsto (fun z : ℂ => ‖z‖ - 1) (cocompact ℂ) atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right (cocompact ℂ) (-1 : ℝ) tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono' (cocompact ℂ) ?_ hz1
    filter_upwards [hev] with z hz
    have h2 : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ := by
      simpa [sub_sub_cancel] using norm_sub_le (f z) (f z - z)
    linarith
  have hcoc : Tendsto f (cocompact ℂ) (cocompact ℂ) := by
    rw [Filter.hasBasis_cocompact.tendsto_right_iff]
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    filter_upwards [hnormf.eventually (eventually_gt_atTop r)] with z hz
    exact fun hmem => absurd (mem_closedBall_zero_iff.mp (hr hmem)) (not_le.mpr hz)
  have hproper : IsProperMap f := isProperMap_iff_tendsto_cocompact.mpr ⟨hcont, hcoc⟩
  have hclosedmap : IsClosedMap f := hproper.isClosedMap
  -- Reconstruct the Ahlfors–Bers approximation data (as in `injective`).
  obtain ⟨p, h, R, hp, hp', hmem, hsupp_h, heq, hrepr⟩ := hf
  have hμt_meas : Measurable fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    Measurable.ite (measurableSet_le measurable_norm measurable_const) b.measurable
      measurable_const
  have hμt_essSup :
      eLpNormEssSup (fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0) volume
        ≤ eLpNormEssSup b.μ volume := by
    rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hzR : ‖z‖ ≤ R
    · simp [hzR]
    · simp [hzR]
  obtain ⟨bt, hbtμ⟩ : ∃ bt : BeltramiCoeff,
      bt.μ = fun z : ℂ => if ‖z‖ ≤ R then b.μ z else 0 :=
    ⟨⟨fun z => if ‖z‖ ≤ R then b.μ z else 0, hμt_meas,
      lt_of_le_of_lt hμt_essSup b.bound⟩, rfl⟩
  have hbt_le : eLpNormEssSup bt.μ volume ≤ eLpNormEssSup b.μ volume := by
    rw [hbtμ]; exact hμt_essSup
  have hbt_supp : ∀ z : ℂ, R < ‖z‖ → bt.μ z = 0 := by
    intro z hz
    rw [hbtμ]
    exact if_neg (not_le.mpr hz)
  have heq' : h =ᵐ[volume] fun z => bt.μ z * beurling h z + bt.μ z := by
    filter_upwards [heq] with z hzeq
    simp only [hbtμ]
    by_cases hzR : ‖z‖ ≤ R
    · rw [if_pos hzR]
      exact hzeq
    · rw [if_neg hzR, hsupp_h z (not_le.mp hzR), zero_mul, zero_add]
  have hf' : IsPrincipalSolution bt f := ⟨p, h, R, hp, hp', hmem, hsupp_h, heq', hrepr⟩
  obtain ⟨bs, hbs_smooth, hbs_cpt, hbs_bnd, hbs_supp, hbs_tend⟩ :=
    exists_contDiff_mollification_beltrami bt hbt_supp
  choose fs hfs hfs1 hfs2 _hfs3 using fun n =>
    exists_contDiffOne_principalSolution (bs n) (hbs_smooth n) (hbs_cpt n)
  have hk0 : 0 ≤ b.normInf := b.normInf_nonneg
  have hk1 : b.normInf < 1 := b.normInf_lt_one
  have hofReal : ENNReal.ofReal b.normInf = eLpNormEssSup b.μ volume :=
    ENNReal.ofReal_toReal (ne_top_of_lt b.bound)
  have hbnd_n : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal b.normInf := by
    intro n
    rw [hofReal]
    exact (hbs_bnd n).trans hbt_le
  have hbnd' : eLpNormEssSup bt.μ volume ≤ ENNReal.ofReal b.normInf := by
    rw [hofReal]; exact hbt_le
  obtain ⟨c, α, hc0, hα, hholder⟩ :=
    isPrincipalSolution_two_sided_holder (R := R + 1) hk0 hk1
  have hineq : ∀ (n : ℕ) (z₁ z₂ : ℂ),
      ‖z₁ - z₂‖ ≤ ‖fs n z₁ - fs n z₂‖ + c * ‖fs n z₁ - fs n z₂‖ ^ α := fun n =>
    hholder (bs n) (fs n) (hbs_smooth n) (hbs_cpt n) (hbnd_n n) (hbs_supp n) (hfs n)
  have hbt_supp' : ∀ z : ℂ, R + 1 < ‖z‖ → bt.μ z = 0 := fun z hz =>
    hbt_supp z (by linarith)
  have hunif : TendstoUniformly fs f atTop :=
    isPrincipalSolution_tendstoUniformly_of_ae_tendsto hk0 hk1 hbnd_n hbnd'
      hbs_supp hbt_supp' hbs_tend hfs hf'
  -- Surjectivity: solve `fs n zₙ = w` (the smooth solutions are homeomorphisms),
  -- the two-sided Hölder inequality bounds `(zₙ)`, and a convergent subsequence
  -- produces a preimage of `w` under `f`.
  have hsurj : Function.Surjective f := by
    intro w
    have hsurj_n : ∀ n, Function.Surjective (fs n) := fun n =>
      (isHomeomorph_of_contDiffOne_principalSolution (hfs n) (hfs1 n) (hfs2 n)).bijective.2
    choose zs hzs using fun n => hsurj_n n w
    -- The displacement bound: `‖zₙ‖ ≤ ‖w − fs n 0‖ + c·‖w − fs n 0‖^α`.
    have hzs_bound : ∀ n, ‖zs n‖ ≤ ‖w - fs n 0‖ + c * ‖w - fs n 0‖ ^ α := by
      intro n
      have h := hineq n (zs n) 0
      rw [hzs n] at h
      simpa using h
    -- `fs n 0 → f 0`, so `‖w − fs n 0‖` is bounded by some `M`.
    have h0 : Tendsto (fun n => ‖w - fs n 0‖) atTop (𝓝 ‖w - f 0‖) :=
      (tendsto_const_nhds.sub (hunif.tendsto_at 0)).norm
    obtain ⟨M, hM⟩ := h0.bddAbove_range
    have hM' : ∀ n, ‖w - fs n 0‖ ≤ M := fun n => hM (Set.mem_range_self n)
    -- Hence `(zₙ)` lives in a fixed closed ball.
    have hzs_mem : ∀ n, zs n ∈ Metric.closedBall (0 : ℂ) (M + c * M ^ α) := by
      intro n
      rw [mem_closedBall_zero_iff]
      have h1 : ‖w - fs n 0‖ ^ α ≤ M ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) (hM' n) hα.le
      have h2 : c * ‖w - fs n 0‖ ^ α ≤ c * M ^ α := mul_le_mul_of_nonneg_left h1 hc0
      linarith [hzs_bound n, hM' n]
    -- Bolzano–Weierstrass and passage to the limit.
    obtain ⟨a, -, φ, hφ, hφtend⟩ :=
      (isCompact_closedBall (0 : ℂ) (M + c * M ^ α)).tendsto_subseq hzs_mem
    refine ⟨a, ?_⟩
    have hlim1 : Tendsto (fun k => f (zs (φ k))) atTop (𝓝 (f a)) :=
      (hcont.tendsto a).comp hφtend
    have hlim2 : Tendsto (fun k => f (zs (φ k))) atTop (𝓝 w) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hφ.tendsto_atTop.eventually
        (Metric.tendstoUniformly_iff.mp hunif ε hε)] with k hk
      have h := hk (zs (φ k))
      rwa [hzs (φ k)] at h
    exact tendsto_nhds_unique hlim1 hlim2
  -- Assembly: a closed continuous bijection is open, hence a homeomorphism.
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  have hopen : IsOpenMap f := by
    intro U hU
    have himg : f '' U = (f '' Uᶜ)ᶜ := by
      rw [← Set.image_compl_eq hbij, compl_compl]
    rw [himg]
    exact isOpen_compl_iff.mpr (hclosedmap _ hU.isClosed_compl)
  exact ⟨hcont, hopen, hbij⟩

/-- **Almost-everywhere positivity of the Jacobian of the principal solution** — the
orientation/nondegeneracy upgrade: `0 < det (Df)` a.e. -/
theorem IsPrincipalSolution.ae_det_pos {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : ∀ᵐ z : ℂ, 0 < (fderiv ℝ f z).det := by
  sorry

/-- **The principal solution is analytically quasiconformal**: assembly of the
homeomorphism, orientation, `W^{1,2}_loc`, and pointwise Beltrami data. The pointwise
Wirtinger equation follows from the weak one through almost-everywhere
differentiability (Gehring–Lehto) and the weak-to-pointwise bridge. -/
theorem IsPrincipalSolution.isQCAnalytic {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : IsQCAnalytic f b := by
  sorry

/-- **Existence for compactly vanishing coefficients**: the principal solution is a
quasiconformal solution. -/
theorem mrmt_exists_of_support (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ f : ℂ → ℂ, IsQCAnalytic f b := by
  sorry

/-- **The measurable Riemann mapping theorem, existence half.** Every Beltrami
coefficient admits a quasiconformal solution of the Beltrami equation. The general
coefficient splits as an inner (compactly vanishing) and an outer part; the outer
part is conjugated to a compactly vanishing coefficient by the inversion `z ↦ 1/z`,
and the two principal solutions compose to a solution for `μ` via the coefficient
transformation rules under holomorphic pre- and post-composition. -/
theorem mrmt_exists (b : BeltramiCoeff) :
    ∃ f : ℂ → ℂ, IsQCAnalytic f b := by
  sorry

end RiemannDynamics

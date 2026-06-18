/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.SingularIntegral.Cauchy
import RiemannDynamics.Analysis.SingularIntegral.Beurling.Kernel
import RiemannDynamics.Analysis.SingularIntegral.Beurling.Convolution
import RiemannDynamics.Analysis.SingularIntegral.Beurling.LpHighOpNorm
import RiemannDynamics.Analysis.SingularIntegral.GehringHigherIntegrability.Residual
import RiemannDynamics.Analysis.Sobolev.Wirtinger
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import RiemannDynamics.QC.LengthArea
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Bojarski higher integrability: the Beurling sub-decomposition

This file develops, as a **dependency-ordered chain**, the analytic core of
*Bojarski higher integrability*: a `W^{1,2}_loc` solution `f` of an elliptic
Beltrami equation `∂̄f = μ ∂f` with `‖μ‖∞ < 1` has its holomorphic Wirtinger
derivative `∂f` locally in `Lᵖ` for some `p > 2`. The assembled target `L6`
(`dz_memLpLocOn_of_beltrami`) matches the conclusion of `QC/InverseQC.lean`'s
`beltrami_higher_integrability` exactly, so the latter reduces to a call into this
file. `L6` in turn reduces to the Gehring reverse-Hölder / Caccioppoli
self-improvement residual living in
`Analysis/SingularIntegral/GehringHigherIntegrability.lean` (see the residual note
above `beltrami_fixedPoint_memLpLocOn_of_memLp_two`).

## The chain

* **L1** `dz_eq_beurling_dzbar` — the smooth identity `∂ω = T(∂̄ω)` for `C¹`
  compactly supported `ω`, from the Cauchy–Pompeiu formula `P(∂̄ω) = ω` and
  `T = ∂ ∘ P`.
* **L1'** `dz_aeeq_beurling_dzbar_of_compactW12` — the `W^{1,2}` compact-support
  lift of L1 (a.e. as `L²` functions). *(HARD; critical path.)*
* **L2** `exists_p_gt_two_beurling_contraction` — choose `p > 2` so that the
  Beurling `Lᵖ` bound `C` still satisfies `‖μ‖∞ · C < 1`, from operator-norm
  continuity at `p = 2`.
* **L3** `eLpNorm_mul_le_essSup_mul` — `‖μ · g‖_p ≤ ‖μ‖∞ · ‖g‖_p`, a wrapper of
  Mathlib's Hölder bound `eLpNorm_smul_le_mul_eLpNorm`.
* **L4'** `beurling_add_ae_lp` — Beurling additivity on `Lᵖ`, `p > 2`.
  *(HARD; load-bearing.)*
* **L4** `exists_memLp_solution_of_beltrami_fixedPoint` — the Neumann series: the
  fixed point `G = h + T(μ · G)` has an `Lᵖ` solution.
* **L5** `dz_cutoff_eq_beurling_repr` — the weak-Leibniz cutoff representation
  `∂(χ·f) = h + T(μ · ∂(χ·f))` for a smooth cutoff `χ`. *(HARDEST.)*
* **L6** `dz_memLpLocOn_of_beltrami` — the assembled target: `∂f ∈ Lᵖ_loc`,
  `p > 2`. Exactly `beltrami_higher_integrability`'s conclusion.
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology Real

namespace RiemannDynamics

/-! ## L1 — the smooth Beurling representation of `∂` -/

/-- **L1.** For a `C²` compactly supported `ω`, the holomorphic Wirtinger
derivative is the Beurling transform of the antiholomorphic one:
`∂ω = T(∂̄ω)` pointwise.

*Sketch.* `P(∂̄ω) = ω` (`cauchyTransform_dzbar`, Cauchy–Pompeiu), so
`∂ω = ∂(P(∂̄ω)) = T(∂̄ω)` by `T = ∂ ∘ P` (`beurling_eq_dz_cauchyTransform`); the
latter consumes `∂̄ω ∈ C¹`, which is why `ω` must be `C²`. *Dependency:*
`cauchyTransform_dzbar`, `beurling_eq_dz_cauchyTransform`. -/
theorem dz_eq_beurling_dzbar {w : ℂ → ℂ} (hw : ContDiff ℝ 2 w)
    (hwc : HasCompactSupport w) :
    ∀ z, dz w z = beurling (fun ζ => dzbar w ζ) z := by
  -- `dzbar w` is the outer (smooth, linear) map `Φ` applied to `fderiv ℝ w`.
  set Φ : (ℂ →L[ℝ] ℂ) → ℂ := fun D => (1 / 2 : ℂ) * (D 1 + I * D I) with hΦ
  have hdzbar_eq : (fun ζ => dzbar w ζ) = Φ ∘ (fun ζ => fderiv ℝ w ζ) := by
    funext ζ; rfl
  -- `fderiv ℝ w` is `C¹` since `w` is `C²`.
  have hfderiv_c1 : ContDiff ℝ 1 (fun ζ => fderiv ℝ w ζ) :=
    hw.fderiv_right (m := 1) (by norm_num)
  -- `Φ` is `C^∞`: it is a fixed continuous-linear functional of `D`.
  have hΦ_cd : ContDiff ℝ ⊤ Φ := by
    have hΦ_lin : Φ = (fun D : ℂ →L[ℝ] ℂ =>
        (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
          + I • ContinuousLinearMap.apply ℝ ℂ I D)) := by
      funext D; simp [hΦ, ContinuousLinearMap.apply_apply, smul_eq_mul]
    rw [hΦ_lin]
    exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).add
      ((ContinuousLinearMap.apply ℝ ℂ I).contDiff.const_smul I)).const_smul _
  -- Hence `dzbar w` is `C¹`.
  have hdzbar_c1 : ContDiff ℝ 1 (fun ζ => dzbar w ζ) := by
    rw [hdzbar_eq]
    exact (hΦ_cd.of_le le_top).comp hfderiv_c1
  -- `fderiv ℝ w` has compact support (since `w` does), hence so does `dzbar w`.
  have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ w ζ) := hwc.fderiv (𝕜 := ℝ)
  have hdzbar_cs : HasCompactSupport (fun ζ => dzbar w ζ) := by
    rw [hdzbar_eq]
    refine hfderiv_cs.comp_left ?_
    simp [hΦ]
  -- `w` is `C¹`.
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  -- Cauchy–Pompeiu, as a function equality: `P(∂̄w) = w`.
  have hP : cauchyTransform (fun ζ => dzbar w ζ) = w := by
    funext z; exact cauchyTransform_dzbar hw1 hwc z
  intro z
  -- `dz w z = dz (P(∂̄w)) z`, then `= T(∂̄w) z` via `T = ∂ ∘ P`.
  calc dz w z = dz (cauchyTransform (fun ζ => dzbar w ζ)) z := by rw [hP]
    _ = beurling (fun ζ => dzbar w ζ) z :=
        beurling_eq_dz_cauchyTransform hdzbar_c1 hdzbar_cs z

/-! ## L1' — the `W^{1,2}` compact-support lift -/

/-- **Helper for L1'.** A function that is locally `Lᵖ` and vanishes (a.e.) off a
compact set is globally `Lᵖ`. The single packaging step needed for L1': the weak
directional derivatives `gx`, `gy` of a compactly supported `f` are locally `L²`
(hypotheses `hgxLp`/`hgyLp`) and vanish off `tsupport f`, so they are globally `L²`,
which is what the mollification-convergence machinery
(`eLpNorm_convolution_normed_sub_tendsto_zero`) consumes. Stated for a general
exponent `p` (the proof is exponent-agnostic) so the higher-integrability cutoff
representation may reuse it at `p = 3`. -/
theorem memLp_of_memLpLocOn_compact_vanishing {p : ℝ≥0∞} {g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hgK : MemLp g p (volume.restrict K))
    (hg0 : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ K → g z = 0) :
    MemLp g p volume := by
  have hKmeas : MeasurableSet K := hK.measurableSet
  -- `g =ᵐ K.indicator g`, since `g = 0` a.e. off `K`.
  have hae : g =ᵐ[volume] K.indicator g := by
    filter_upwards [hg0] with z hz
    by_cases hzK : z ∈ K
    · rw [Set.indicator_of_mem hzK]
    · rw [Set.indicator_of_notMem hzK, hz hzK]
  -- The indicator is `Lᵖ` (its `Lᵖ` norm is the restricted norm of `g`), then transfer.
  have hind : MemLp (K.indicator g) p volume := (memLp_indicator_iff_restrict hKmeas).2 hgK
  exact hind.ae_eq hae.symm

/-- **L1'.** The `W^{1,2}` compact-support lift of L1, stated directly over the weak
*directional* derivatives. If `f` has compact support and `gx`, `gy` are weak
directional derivatives of `f` in the directions `1` and `I` (the weak partial
derivatives `∂ₓf`, `∂ᵧf`) that are locally `L²`, then the weak holomorphic Wirtinger
derivative `½(gx − i·gy)` equals the Beurling transform of the weak antiholomorphic
Wirtinger derivative `½(gx + i·gy)` a.e. (the identity `∂ = T(∂̄)` of L1 promoted from
the smooth pointwise statement to an a.e. identity of `L²` functions).

*Why directional witnesses.* L1' is stated over the directional witnesses `gx`, `gy`
rather than over abstract `HasWeakDz`/`HasWeakDzbar` witnesses `Df`, `Dfbar` together
with `MemLpLocOn` of the *combined* objects. The latter formulation is **false**: the
combined local-`L²` hypotheses do not pin down the *directional* witnesses, and non-integrable
junk re-enters at the level of `gx`, `gy` (the integration-by-parts identity defining
`HasWeakDirDeriv` is satisfied vacuously by such junk off `tsupport f`, where the
Bochner integral returns `0`). The mollification bridge needs the *directional*
witnesses themselves to be locally `L²` — only then are they (being supported, up to a
null set, in the compact `tsupport f`) globally `L²`, so that
`ρₙ ⋆ gx → gx` and `ρₙ ⋆ gy → gy` in `L²`. We therefore state L1' over `gx`, `gy`
directly with their loc-`L²` hypotheses. These are satisfiable by `f = χ·u` with `χ`
smooth compactly supported and `u ∈ W^{1,2}_loc`: `gx`, `gy` are then the weak
directional derivatives of `χ·u`, locally `L²` because `u` is.

*Sketch.* `gx`, `gy` vanish a.e. off `tsupport f` (where `f ≡ 0`, by
`HasWeakDirDeriv.ae_eq` against the zero weak derivative on the open complement),
hence are globally `L²` (`memLp_of_memLpLocOn_compact_vanishing`). Mollify
`fₙ := ρₙ ⋆ f` (`ρₙ = (φ n).normed`, `rOut → 0`); then
`(fderiv ℝ fₙ z) v = (ρₙ ⋆ gᵥ) z` (`fderiv_convolution_normed_apply_eq`), so
`dz fₙ = ½((ρₙ⋆gx) − i(ρₙ⋆gy))` and `dzbar fₙ = ½((ρₙ⋆gx) + i(ρₙ⋆gy))`. By
`ρₙ⋆gx → gx`, `ρₙ⋆gy → gy` in `L²`
(`eLpNorm_convolution_normed_sub_tendsto_zero`), `dz fₙ → ½(gx−i gy)` and
`dzbar fₙ → ½(gx+i gy)` in `L²`. Apply L1 (`dz_eq_beurling_dzbar`, each `fₙ` is
`C²` compactly supported) to get `dz fₙ = beurling (dzbar fₙ)` pointwise; pass to the
limit using the Beurling `L²` bound (`eLpNorm_beurling_sub_le`) and `L²`-limit
uniqueness. *(HARD; critical path.)* *Dependency:* `dz_eq_beurling_dzbar`,
`fderiv_convolution_normed_apply_eq`, `eLpNorm_convolution_normed_sub_tendsto_zero`,
`eLpNorm_beurling_sub_le`. -/
theorem dz_aeeq_beurling_dzbar_of_compactW12 {f gx gy : ℂ → ℂ}
    (hfc : HasCompactSupport f) (hfLp : MemLpLocOn f (2 : ℝ≥0∞) Set.univ)
    (hgx : HasWeakDirDeriv 1 gx f Set.univ) (hgy : HasWeakDirDeriv Complex.I gy f Set.univ)
    (hgxLp : MemLpLocOn gx (2 : ℝ≥0∞) Set.univ) (hgyLp : MemLpLocOn gy (2 : ℝ≥0∞) Set.univ) :
    (fun z => (1 / 2 : ℂ) * (gx z - Complex.I * gy z)) =ᵐ[volume]
      beurling (fun z => (1 / 2 : ℂ) * (gx z + Complex.I * gy z)) := by
  classical
  -- ===== (0) Preliminaries: `MemLpLocOn _ 2 univ` ⟹ `LocallyIntegrable`. =====
  have hLI : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h volume := by
    intro h hh x
    refine ⟨Metric.closedBall x 1, ?_, ?_⟩
    · exact Metric.closedBall_mem_nhds x one_pos
    · have hmem : MemLp h 2 (volume.restrict (Metric.closedBall x 1)) :=
        hh _ (Set.subset_univ _) (isCompact_closedBall x 1)
      haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall x 1)) :=
        isFiniteMeasure_restrict.2 (isCompact_closedBall x 1).measure_lt_top.ne
      exact hmem.integrable one_le_two
  have hfLI : LocallyIntegrable f volume := hLI hfLp
  have hgxLI : LocallyIntegrable gx volume := hLI hgxLp
  have hgyLI : LocallyIntegrable gy volume := hLI hgyLp
  -- ===== (1) `gx`, `gy` are globally `L²`. =====
  set K : Set ℂ := tsupport f with hKdef
  have hKcompact : IsCompact K := hfc
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  have hKopen : IsOpen Kᶜ := hKcompact.isClosed.isOpen_compl
  -- On the open set `Kᶜ`, `f ≡ 0`, so `0` is a weak directional derivative of `f` there.
  have hf0_on : ∀ z ∈ Kᶜ, f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hzero_weak : ∀ (v : ℂ), HasWeakDirDeriv v (fun _ => (0 : ℂ)) f Kᶜ := by
    intro v φ hφ hcs htsupp
    -- RHS `= -∫ φ • 0 = 0`. LHS `= ∫ (∂ᵥφ)•f = 0` since `f ≡ 0` on `tsupport φ ⊆ Kᶜ`
    -- and `∂ᵥφ ≡ 0` off `tsupport φ`.
    have hLHS : ∀ z, ((fderiv ℝ φ z) v) • f z = (0 : ℂ) := by
      intro z
      by_cases hz : z ∈ tsupport φ
      · rw [hf0_on z (htsupp hz)]; exact smul_zero _
      · have hfd0 : fderiv ℝ φ z = 0 := by
          have hzsupp : z ∉ tsupport (fderiv ℝ φ) := fun hmem => hz (tsupport_fderiv_subset ℝ hmem)
          simpa using image_eq_zero_of_notMem_tsupport hzsupp
        rw [hfd0]; simp
    have hRHS : ∀ z, φ z • (0 : ℂ) = 0 := fun z => smul_zero _
    simp only [hLHS, hRHS, integral_zero, neg_zero]
  -- Vanishing of `gx`, `gy` a.e. off `K`, via uniqueness of weak derivatives on `Kᶜ`.
  have hvanish : ∀ {g : ℂ → ℂ} {v : ℂ}, HasWeakDirDeriv v g f Set.univ →
      LocallyIntegrable g volume → ∀ᵐ z ∂(volume : Measure ℂ), z ∉ K → g z = 0 := by
    intro g v hg hgLI
    have hgon : HasWeakDirDeriv v g f Kᶜ := hg.mono (Set.subset_univ _)
    have key := HasWeakDirDeriv.ae_eq hKopen hgon (hzero_weak v)
      (hgLI.locallyIntegrableOn _) (locallyIntegrable_zero.locallyIntegrableOn _)
    filter_upwards [key] with z hz hzK
    exact hz hzK
  have hgx0 : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ K → gx z = 0 := hvanish hgx hgxLI
  have hgy0 : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ K → gy z = 0 := hvanish hgy hgyLI
  have hgxLp2 : MemLp gx 2 volume :=
    memLp_of_memLpLocOn_compact_vanishing hKcompact (hgxLp K (Set.subset_univ _) hKcompact) hgx0
  have hgyLp2 : MemLp gy 2 volume :=
    memLp_of_memLpLocOn_compact_vanishing hKcompact (hgyLp K (Set.subset_univ _) hKcompact) hgy0
  -- ===== (2) The mollifier sequence and the mollified functions. =====
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ
  have hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) := by
    have : (fun n : ℕ => (φ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [this]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- The normed mollifier `ρ n`, smooth and compactly supported.
  set ρ : ℕ → ℂ → ℝ := fun n => (φ n).normed MeasureTheory.volume with hρdef
  have hρ_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n => (φ n).contDiff_normed
  have hρ_supp : ∀ n, HasCompactSupport (ρ n) := fun n => (φ n).hasCompactSupport_normed
  -- The convolution operator `conv ρ g` used throughout.
  set conv : (ℂ → ℝ) → (ℂ → ℂ) → (ℂ → ℂ) :=
    fun r g => MeasureTheory.convolution r g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
    with hconvdef
  set fn : ℕ → ℂ → ℂ := fun n => conv (ρ n) f with hfndef
  -- Each `fn n` is `C²` and compactly supported.
  have hfn_C2 : ∀ n, ContDiff ℝ 2 (fn n) := fun n =>
    (hρ_supp n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := 2)
      ((hρ_smooth n).of_le (by exact_mod_cast le_top)) hfLI
  have hfn_cs : ∀ n, HasCompactSupport (fn n) := fun n =>
    (hρ_supp n).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfc
  -- ===== (3) `dz (fn n)` and `dzbar (fn n)` in terms of the mollified `gx`, `gy`. =====
  -- `Pn n := ρ n ⋆ gx`, `Qn n := ρ n ⋆ gy`.
  set Pn : ℕ → ℂ → ℂ := fun n => conv (ρ n) gx with hPndef
  set Qn : ℕ → ℂ → ℂ := fun n => conv (ρ n) gy with hQndef
  have hdz_fn : ∀ n z, dz (fn n) z = (1 / 2 : ℂ) * (Pn n z - Complex.I * Qn n z) := by
    intro n z
    unfold dz
    rw [show fn n = conv (ρ n) f from rfl,
        fderiv_convolution_normed_apply_eq hgx hfLI hgxLI (hρ_smooth n) (hρ_supp n) z,
        fderiv_convolution_normed_apply_eq hgy hfLI hgyLI (hρ_smooth n) (hρ_supp n) z]
  have hdzbar_fn : ∀ n z, dzbar (fn n) z = (1 / 2 : ℂ) * (Pn n z + Complex.I * Qn n z) := by
    intro n z
    unfold dzbar
    rw [show fn n = conv (ρ n) f from rfl,
        fderiv_convolution_normed_apply_eq hgx hfLI hgxLI (hρ_smooth n) (hρ_supp n) z,
        fderiv_convolution_normed_apply_eq hgy hfLI hgyLI (hρ_smooth n) (hρ_supp n) z]
  -- ===== (4) `Pn → gx`, `Qn → gy` in `L²`. =====
  have hPconv : Filter.Tendsto (fun n => eLpNorm (Pn n - gx) 2 volume) Filter.atTop (nhds 0) :=
    eLpNorm_convolution_normed_sub_tendsto_zero hgxLp2 φ hφrout
  have hQconv : Filter.Tendsto (fun n => eLpNorm (Qn n - gy) 2 volume) Filter.atTop (nhds 0) :=
    eLpNorm_convolution_normed_sub_tendsto_zero hgyLp2 φ hφrout
  -- `Pn n`, `Qn n` are continuous (convolution of smooth compactly supported with loc.-int.).
  have hPn_cont : ∀ n, Continuous (Pn n) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρ_supp n)
      ((hρ_smooth n).continuous) hgxLI
  have hQn_cont : ∀ n, Continuous (Qn n) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρ_supp n)
      ((hρ_smooth n).continuous) hgyLI
  -- AEStronglyMeasurability of `gx`, `gy` and the differences `Pn n - gx`, `Qn n - gy`.
  have hgx_meas : AEStronglyMeasurable gx volume := hgxLp2.1
  have hgy_meas : AEStronglyMeasurable gy volume := hgyLp2.1
  have hPdiff_meas : ∀ n, AEStronglyMeasurable (Pn n - gx) volume := fun n =>
    (hPn_cont n).aestronglyMeasurable.sub hgx_meas
  have hQdiff_meas : ∀ n, AEStronglyMeasurable (Qn n - gy) volume := fun n =>
    (hQn_cont n).aestronglyMeasurable.sub hgy_meas
  -- ===== (5) The two `L²` targets and their membership. =====
  set A : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gx z - Complex.I * gy z) with hAdef
  set B : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gx z + Complex.I * gy z) with hBdef
  have hA_mem : MemLp A 2 volume := by
    have hrw : A = (1 / 2 : ℂ) • gx + (-(1 / 2 : ℂ) * Complex.I) • gy := by
      funext z; simp only [hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hrw]
    exact (hgxLp2.const_smul _).add (hgyLp2.const_smul _)
  have hB_mem : MemLp B 2 volume := by
    have hrw : B = (1 / 2 : ℂ) • gx + ((1 / 2 : ℂ) * Complex.I) • gy := by
      funext z; simp only [hBdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hrw]
    exact (hgxLp2.const_smul _).add (hgyLp2.const_smul _)
  -- ===== (6) `dz fn → A` and `dzbar fn → B` in `L²`. =====
  -- General squeeze: a function whose `L²` norm is `≤ ‖Pn-gx‖ + ‖Qn-gy‖` tends to `0`.
  have hsqueeze : ∀ (S : ℕ → ℝ≥0∞),
      (∀ n, S n ≤ eLpNorm (Pn n - gx) 2 volume + eLpNorm (Qn n - gy) 2 volume) →
      Filter.Tendsto S Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    intro S hS
    have hsum : Filter.Tendsto
        (fun n => eLpNorm (Pn n - gx) 2 volume + eLpNorm (Qn n - gy) 2 volume)
        Filter.atTop (nhds (0 + 0)) := hPconv.add hQconv
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hsum (fun n => zero_le _) hS
  -- The three constant `enorm`s appearing in the coefficient bounds, computed once.
  have hhalf_real : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have henorm_half : ‖(1 / 2 : ℂ)‖ₑ = (1 / 2 : ℝ≥0∞) := by
    have h : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by norm_num)]
    rw [← ofReal_norm_eq_enorm, h, hhalf_real]
  have henorm_negHalfI : ‖(-(1 / 2 : ℂ) * Complex.I)‖ₑ = (1 / 2 : ℝ≥0∞) := by
    have h : ‖(-(1 / 2 : ℂ) * Complex.I)‖ = (1 / 2 : ℝ) := by
      rw [norm_mul, norm_neg, Complex.norm_I, mul_one,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by norm_num)]
    rw [← ofReal_norm_eq_enorm, h, hhalf_real]
  have henorm_halfI : ‖((1 / 2 : ℂ) * Complex.I)‖ₑ = (1 / 2 : ℝ≥0∞) := by
    have h : ‖((1 / 2 : ℂ) * Complex.I)‖ = (1 / 2 : ℝ) := by
      rw [norm_mul, Complex.norm_I, mul_one,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by norm_num)]
    rw [← ofReal_norm_eq_enorm, h, hhalf_real]
  -- The pointwise bound for `dz fn - A`.
  have hdz_bound : ∀ n, eLpNorm (fun z => dz (fn n) z - A z) 2 volume
      ≤ eLpNorm (Pn n - gx) 2 volume + eLpNorm (Qn n - gy) 2 volume := by
    intro n
    -- `dz fn z - A z = (1/2)•(Pn n - gx) z + (-(1/2)·I)•(Qn n - gy) z`.
    have heq : (fun z => dz (fn n) z - A z)
        = (1 / 2 : ℂ) • (Pn n - gx) + (-(1 / 2 : ℂ) * Complex.I) • (Qn n - gy) := by
      funext z
      simp only [hdz_fn n z, hAdef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [heq]
    refine le_trans (eLpNorm_add_le ((hPdiff_meas n).const_smul _)
      ((hQdiff_meas n).const_smul _) one_le_two) ?_
    refine add_le_add ?_ ?_
    · refine le_trans eLpNorm_const_smul_le ?_
      rw [henorm_half]
      calc (1 / 2 : ℝ≥0∞) * eLpNorm (Pn n - gx) 2 volume
          ≤ 1 * eLpNorm (Pn n - gx) 2 volume := by gcongr; norm_num
        _ = eLpNorm (Pn n - gx) 2 volume := one_mul _
    · refine le_trans eLpNorm_const_smul_le ?_
      rw [henorm_negHalfI]
      calc (1 / 2 : ℝ≥0∞) * eLpNorm (Qn n - gy) 2 volume
          ≤ 1 * eLpNorm (Qn n - gy) 2 volume := by gcongr; norm_num
        _ = eLpNorm (Qn n - gy) 2 volume := one_mul _
  have hdzbar_bound : ∀ n, eLpNorm (fun z => dzbar (fn n) z - B z) 2 volume
      ≤ eLpNorm (Pn n - gx) 2 volume + eLpNorm (Qn n - gy) 2 volume := by
    intro n
    have heq : (fun z => dzbar (fn n) z - B z)
        = (1 / 2 : ℂ) • (Pn n - gx) + ((1 / 2 : ℂ) * Complex.I) • (Qn n - gy) := by
      funext z
      simp only [hdzbar_fn n z, hBdef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [heq]
    refine le_trans (eLpNorm_add_le ((hPdiff_meas n).const_smul _)
      ((hQdiff_meas n).const_smul _) one_le_two) ?_
    refine add_le_add ?_ ?_
    · refine le_trans eLpNorm_const_smul_le ?_
      rw [henorm_half]
      calc (1 / 2 : ℝ≥0∞) * eLpNorm (Pn n - gx) 2 volume
          ≤ 1 * eLpNorm (Pn n - gx) 2 volume := by gcongr; norm_num
        _ = eLpNorm (Pn n - gx) 2 volume := one_mul _
    · refine le_trans eLpNorm_const_smul_le ?_
      rw [henorm_halfI]
      calc (1 / 2 : ℝ≥0∞) * eLpNorm (Qn n - gy) 2 volume
          ≤ 1 * eLpNorm (Qn n - gy) 2 volume := by gcongr; norm_num
        _ = eLpNorm (Qn n - gy) 2 volume := one_mul _
  have hdz_conv : Filter.Tendsto (fun n => eLpNorm (fun z => dz (fn n) z - A z) 2 volume)
      Filter.atTop (nhds 0) := hsqueeze _ hdz_bound
  have hdzbar_conv : Filter.Tendsto (fun n => eLpNorm (fun z => dzbar (fn n) z - B z) 2 volume)
      Filter.atTop (nhds 0) := hsqueeze _ hdzbar_bound
  -- ===== (7) L1 applied to each `fn n`: `dz fn = beurling (dzbar fn)` pointwise. =====
  have hL1 : ∀ n z, dz (fn n) z = beurling (fun ζ => dzbar (fn n) ζ) z := fun n =>
    dz_eq_beurling_dzbar (hfn_C2 n) (hfn_cs n)
  -- ===== (8) `beurling (dzbar fn) → beurling B` in `L²`. =====
  -- `dzbar fn ∈ L²` (it equals `dz`/`dzbar` of a `C²` compactly supported function).
  have hdzbar_fn_mem : ∀ n, MemLp (fun ζ => dzbar (fn n) ζ) 2 volume := by
    intro n
    -- `dzbar (fn n) = ½(Pn n + I Qn n)`, continuous with compact support, hence `L²`.
    have hcont : Continuous (fun ζ => dzbar (fn n) ζ) := by
      have : (fun ζ => dzbar (fn n) ζ)
          = (fun ζ => (1 / 2 : ℂ) * (Pn n ζ + Complex.I * Qn n ζ)) := by
        funext ζ; exact hdzbar_fn n ζ
      rw [this]
      exact (continuous_const.mul ((hPn_cont n).add (continuous_const.mul (hQn_cont n))))
    have hcs : HasCompactSupport (fun ζ => dzbar (fn n) ζ) := by
      have h1 : HasCompactSupport (fun ζ => fderiv ℝ (fn n) ζ) := (hfn_cs n).fderiv ℝ
      apply HasCompactSupport.comp_left (g := fun D : ℂ →L[ℝ] ℂ =>
        (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I)) (f := fun ζ => fderiv ℝ (fn n) ζ)
        (hf := h1)
      simp
    exact hcont.memLp_of_hasCompactSupport hcs
  have hbeurling_conv :
      Filter.Tendsto (fun n => eLpNorm (fun z => beurling (fun ζ => dzbar (fn n) ζ) z
        - beurling B z) 2 volume) Filter.atTop (nhds 0) := by
    -- `eLpNorm (beurling (dzbar fn) - beurling B) ≤ Cst · eLpNorm (dzbar fn - B) → 0`.
    set Cst : ℝ≥0∞ := (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ with hCst
    have hCfin : Cst ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (by simp [ENNReal.inv_lt_top, Real.pi_pos])).ne
    have hbound : ∀ n, eLpNorm (fun z => beurling (fun ζ => dzbar (fn n) ζ) z - beurling B z)
        2 volume ≤ Cst * eLpNorm (fun z => dzbar (fn n) z - B z) 2 volume := by
      intro n
      have h := eLpNorm_beurling_sub_le (hdzbar_fn_mem n) hB_mem
      have hcongr : (fun z => dzbar (fn n) z - B z) = ((fun ζ => dzbar (fn n) ζ) - B) := by
        funext z; rfl
      rw [hcongr]; exact h
    -- `Cst · eLpNorm (dzbar fn - B) → Cst · 0 = 0`.
    have hmul : Filter.Tendsto (fun n => Cst * eLpNorm (fun z => dzbar (fn n) z - B z) 2 volume)
        Filter.atTop (nhds (Cst * 0)) :=
      ENNReal.Tendsto.const_mul hdzbar_conv (Or.inr hCfin)
    rw [mul_zero] at hmul
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hmul (fun n => zero_le _) hbound
  -- `dz fn = beurling (dzbar fn)` pointwise, so `dz fn → beurling B` in `L²`.
  have hdz_conv' : Filter.Tendsto (fun n => eLpNorm (fun z => dz (fn n) z - beurling B z) 2 volume)
      Filter.atTop (nhds 0) := by
    have hcongr : ∀ n, (fun z => dz (fn n) z - beurling B z)
        = (fun z => beurling (fun ζ => dzbar (fn n) ζ) z - beurling B z) := by
      intro n; funext z; rw [hL1 n z]
    simp only [hcongr]
    exact hbeurling_conv
  -- ===== (9) `L²`-limit uniqueness: `A =ᵐ beurling B`. =====
  have hbeurlingB_meas : AEStronglyMeasurable (beurling B) volume := (memLp_beurling hB_mem).1
  -- `dz (fn n)` is continuous (`fn n` is `C²`), hence AEStronglyMeasurable.
  have hdzfn_meas : ∀ n, AEStronglyMeasurable (fun z => dz (fn n) z) volume := by
    intro n
    have hcont : Continuous (fun z => dz (fn n) z) := by
      have : (fun z => dz (fn n) z)
          = (fun z => (1 / 2 : ℂ) * (Pn n z - Complex.I * Qn n z)) := by
        funext z; exact hdz_fn n z
      rw [this]
      exact (continuous_const.mul ((hPn_cont n).sub (continuous_const.mul (hQn_cont n))))
    exact hcont.aestronglyMeasurable
  have hbd : ∀ n, eLpNorm (fun z => A z - beurling B z) 2 volume
      ≤ eLpNorm (fun z => dz (fn n) z - A z) 2 volume
        + eLpNorm (fun z => dz (fn n) z - beurling B z) 2 volume := by
    intro n
    have heq : (fun z => A z - beurling B z)
        = (fun z => (A z - dz (fn n) z) + (dz (fn n) z - beurling B z)) := by funext z; ring
    rw [heq]
    refine le_trans (eLpNorm_add_le (hA_mem.1.sub (hdzfn_meas n))
      ((hdzfn_meas n).sub hbeurlingB_meas) one_le_two) ?_
    have hcomm : eLpNorm (fun z => A z - dz (fn n) z) 2 volume
        = eLpNorm (fun z => dz (fn n) z - A z) 2 volume :=
      eLpNorm_sub_comm A (fun z => dz (fn n) z) 2 volume
    rw [hcomm]
  have hsum : Filter.Tendsto (fun n => eLpNorm (fun z => dz (fn n) z - A z) 2 volume
      + eLpNorm (fun z => dz (fn n) z - beurling B z) 2 volume) Filter.atTop (nhds 0) := by
    have := hdz_conv.add hdz_conv'; rwa [add_zero] at this
  have hle : eLpNorm (fun z => A z - beurling B z) 2 volume ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsum hbd
  have hzero : eLpNorm (fun z => A z - beurling B z) 2 volume = 0 := le_antisymm hle (zero_le _)
  have hmeasAB : AEStronglyMeasurable (fun z => A z - beurling B z) volume :=
    hA_mem.1.sub hbeurlingB_meas
  have hae := (eLpNorm_eq_zero_iff hmeasAB (by norm_num)).1 hzero
  filter_upwards [hae] with z hz
  exact sub_eq_zero.1 hz

/-! ## L2 — choosing the contraction exponent -/

/-- **L2.** From operator-norm continuity at `p = 2`, choose `p > 2` (finite) and
a Beurling `Lᵖ` bound `C` such that `‖μ‖∞ · C < 1` — the Neumann-series
contraction condition.

*Sketch.* Set `ε > 0` with `(‖μ‖∞ + ε)(1 + ε) < 1` (possible since `‖μ‖∞ < 1`),
then feed `ε` to `beurling_opNorm_continuous` to get `p ∈ (2, ∞)` with bound
`C < 1 + ε`; conclude `‖μ‖∞ · C < 1`. *Dependency:* `beurling_opNorm_continuous`. -/
theorem exists_p_gt_two_beurling_contraction {μ : ℂ → ℂ} (_hμmeas : Measurable μ)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ p : ℝ≥0∞, 2 < p ∧ p ≠ ⊤ ∧ ∃ C : ℝ, IsCalderonZygmundBound beurling p C ∧
      (eLpNormEssSup μ volume).toReal * C < 1 := by
  -- `k := ‖μ‖∞` is finite (`< 1 < ⊤`) and `0 ≤ k < 1`.
  set k : ℝ := (eLpNormEssSup μ volume).toReal with hk
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hk1 : k < 1 := by
    rw [hk, show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hμbound.ne_top ENNReal.one_ne_top).2 hμbound
  -- Choose `ε := (1 - k)/2 > 0`; then `k·(1+ε) < 1`.
  set ε : ℝ := (1 - k) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hkε : k * (1 + ε) < 1 := by
    rw [hε]; nlinarith [hk0, hk1]
  -- Operator-norm continuity yields `p ∈ (2, ∞)` with a CZ bound `C < 1 + ε`.
  obtain ⟨p, hp2, hptop, C, hClt, hCb⟩ := beurling_opNorm_continuous ε hεpos
  refine ⟨p, hp2, hptop, C, hCb, ?_⟩
  -- `k · C ≤ k · (1+ε) < 1`, using `0 ≤ C` (from the CZ bound) and `0 ≤ k`.
  calc k * C ≤ k * (1 + ε) := by
        apply mul_le_mul_of_nonneg_left hClt.le hk0
    _ < 1 := hkε

/-! ## L3 — the pointwise-multiplier Hölder bound -/

/-- **L3.** Multiplication by an `L∞` function contracts the `Lᵖ` norm:
`‖μ · g‖_p ≤ ‖μ‖∞ · ‖g‖_p`.

*Sketch.* `μ · g = μ • g`; apply Mathlib's `eLpNorm_smul_le_mul_eLpNorm` with
the Hölder triple `(∞, p, p)` and `eLpNorm μ ∞ = eLpNormEssSup μ`.
*Dependency:* `eLpNorm_smul_le_mul_eLpNorm`. -/
theorem eLpNorm_mul_le_essSup_mul {μ g : ℂ → ℂ} {p : ℝ≥0∞}
    (hμ : AEStronglyMeasurable μ volume) (hg : MemLp g p volume) :
    eLpNorm (fun z => μ z * g z) p volume
      ≤ eLpNormEssSup μ volume * eLpNorm g p volume := by
  -- `μ z * g z = μ z • g z` (the ring `ℂ` acting on itself).
  have hsmul : (fun z => μ z * g z) = (fun z => μ z • g z) := by
    funext z; rw [smul_eq_mul]
  rw [hsmul]
  -- Hölder triple `(∞, p, p)`: `1/p = 1/∞ + 1/p`. The exponents and ring/module
  -- instances are pinned explicitly (`ℂ` acting on itself) to avoid an expensive
  -- typeclass/exponent search.
  have hbd := @eLpNorm_smul_le_mul_eLpNorm ℂ ℂ ℂ _ volume _ _ _ _ ⊤ p p g
    hg.aestronglyMeasurable μ hμ inferInstance
  rwa [eLpNorm_exponent_top] at hbd

/-! ## L4' — Beurling additivity on `Lᵖ` -/

/-- **L4'.** The Beurling transform is additive a.e. on `Lᵖ`, `2 < p < ∞`:
`T(f + g) =ᵐ T f + T g`. The `p = ⊤` case is excluded by hypothesis — it is a
different, principal-value theory and is never needed (the Neumann series L4/L6 only
ever consume a finite `p` delivered by L2).

*Sketch.* Replicate `beurling_add_ae` (the `L² ∪ L⁴` additivity) using the `Lᵖ`-high
truncation a.e. convergence (`czOperator_beurling_ae_tendsto_neg_pi_Lp_high`) and the
`Lᵖ`/`Lᵖ'` Hölder integrability of the truncated integrand
(`integrableOn_beurlingKernel_mul_Lp`), both available for `p ≠ ⊤`.
*Dependency:* `czOperator_beurling_add`, the Beurling `Lᵖ`-high machinery. -/
theorem beurling_add_ae_lp {p : ℝ≥0∞} (hp : 2 < p) (hptop : p ≠ ⊤) {f g : ℂ → ℂ}
    (hf : MemLp f p volume) (hg : MemLp g p volume) :
    beurling (f + g) =ᵐ[volume] beurling f + beurling g := by
  -- `2 < p < ∞`. Replicate `beurling_add_ae`, with the `Lᵖ`-high a.e. convergence and
  -- the `Lᵖ`/`Lᵖ'` Hölder integrability of the truncated integrand.
  have hp1 : 1 < p := lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp
  -- The Hölder conjugate exponent `p' = (1 - p⁻¹)⁻¹` and its instance.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'_def
  have hpinv_le_one : p⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; exact hp1.le
  haveI hHC : ENNReal.HolderConjugate p p' := by
    rw [hp'_def, ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  -- Truncated-integrand integrability for `Lᵖ` inputs.
  have hint : ∀ {h : ℂ → ℂ}, MemLp h p volume → ∀ {r : ℝ}, 0 < r → ∀ x : ℂ,
      IntegrableOn (fun y => beurlingKernel x y * h y) (Metric.ball x r)ᶜ volume :=
    fun {h} hh {r} hr x =>
      integrableOn_beurlingKernel_mul_Lp (p := p) (p' := p') hr x hp1 hptop hh
  -- The a.e. convergence of the truncations to `-π · beurling`.
  filter_upwards [czOperator_beurling_ae_tendsto_neg_pi_Lp_high hp hptop hf,
    czOperator_beurling_ae_tendsto_neg_pi_Lp_high hp hptop hg] with z hzf hzg
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hconv : Tendsto (fun r => czOperator beurlingKernel r (f + g) z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π:ℂ) * beurling f z + -(π:ℂ) * beurling g z)) := by
    refine (hzf.add hzg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (czOperator_beurling_add (hint hf hr z) (hint hg hr z)).symm
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z)
      = -(π:ℂ) * beurling f z + -(π:ℂ) * beurling g z := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z
        = czOperator beurlingKernel r (f + g) z := fun r => rfl
    simpa only [hcz] using hconv
  have hbfg : beurling (f + g) z = -(1 / (π:ℂ)) * limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z) := rfl
  have : beurling (f + g) z = beurling f z + beurling g z := by
    rw [hbfg, hlim]; field_simp; ring
  simpa [Pi.add_apply] using this

/-- **Beurling preserves `Lᵖ` for `p > 2`.** For `2 < p < ∞` the Beurling transform
sends `Lᵖ` to `Lᵖ`: measurability from `aestronglyMeasurable_beurling_Lp_high`, finite
`Lᵖ` norm from the Calderón–Zygmund `Lᵖ` bound `beurling_lp_bound`. This is the named
form of the inline fact used inside L4, reused by the cutoff representation's `δ = 1`
higher-integrability conclusion (`h = beurling R ∈ L³`). -/
theorem memLp_beurling_of_memLp {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤) {u : ℂ → ℂ}
    (hu : MemLp u p volume) : MemLp (beurling u) p volume := by
  obtain ⟨C, hC0, hCbound⟩ := beurling_lp_bound (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp) hp'
  refine ⟨aestronglyMeasurable_beurling_Lp_high hp hp' hu, ?_⟩
  calc eLpNorm (beurling u) p volume ≤ ENNReal.ofReal C * eLpNorm u p volume :=
        hCbound u hu
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2

/-! ## L4 — the Neumann series fixed point -/

/-- **L4.** The Beltrami fixed-point equation `G = h + T(μ · G)` has an `Lᵖ`
solution, `p > 2`, whenever `‖μ‖∞ · C < 1` for the Beurling `Lᵖ` bound `C`.

*Sketch.* Iterate `G ↦ h + T(μ · G)`; the map is a contraction on `Lᵖ` with
factor `‖μ‖∞ · C < 1` (L3 + the `Lᵖ` bound), so the Neumann series
`∑ₙ (T ∘ (μ · ·))ⁿ h` converges (`tsum_geometric_of_norm_lt_one`) to a fixed point
`G ∈ Lᵖ`. *Dependency:* `eLpNorm_mul_le_essSup_mul`, `beurling_add_ae_lp`,
`IsCalderonZygmundBound`, `tsum_geometric_of_norm_lt_one`. -/
theorem exists_memLp_solution_of_beltrami_fixedPoint {μ h : ℂ → ℂ} {p : ℝ≥0∞}
    {C : ℝ} (hp : 2 < p) (hp' : p ≠ ⊤) (hμmeas : Measurable μ)
    (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hcontr : (eLpNormEssSup μ volume).toReal * C < 1) (hh : MemLp h p volume) :
    ∃ G, MemLp G p volume ∧ G =ᵐ[volume] h + beurling (fun z => μ z * G z) := by
  classical
  -- Basic facts about `p` and the CZ constant.
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp)
  haveI : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨hC0, hCbound⟩ := hCb
  set k : ℝ := (eLpNormEssSup μ volume).toReal with hk_def
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  -- `μ ∈ L∞` (finite essential supremum) — the hypothesis `hμfin`. This is the regime
  -- in which the Neumann-series multiplier `μ · ·` is bounded on `Lᵖ`; every caller (via
  -- L2) supplies `eLpNormEssSup μ < 1 < ⊤`. (The `(eLpNormEssSup μ).toReal · C < 1` bound
  -- alone does not rule out `eLpNormEssSup μ = ⊤`, since `(⊤).toReal = 0`.)
  have hμtop : eLpNormEssSup μ volume ≠ ⊤ := hμfin
  -- `μ` is bounded: `μ ∈ Lᵖ_loc`-free, just `MemLp μ ⊤`.
  have hμLinf : MemLp μ ⊤ volume := by
    refine ⟨hμmeas.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_exponent_top]
    exact lt_of_le_of_ne le_top hμtop
  -- The multiplier preserves `Lᵖ`, with the Hölder bound `‖μ·g‖_p ≤ ‖μ‖∞ ‖g‖_p`.
  have hμmul : ∀ {g : ℂ → ℂ}, MemLp g p volume → MemLp (fun z => μ z * g z) p volume :=
    fun {g} hg => hg.mul' hμLinf
  -- Beurling sends `Lᵖ` to `Lᵖ`.
  have hbeurLp : ∀ {g : ℂ → ℂ}, MemLp g p volume → MemLp (beurling g) p volume := by
    intro g hg
    refine ⟨aestronglyMeasurable_beurling_Lp_high hp hp' hg, ?_⟩
    calc eLpNorm (beurling g) p volume ≤ ENNReal.ofReal C * eLpNorm g p volume :=
          hCbound g hg
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2
  -- The operator `S g := beurling (μ · g)` sends `Lᵖ` to `Lᵖ` (`MemLp`).
  have hSmem : ∀ {g : ℂ → ℂ}, MemLp g p volume →
      MemLp (beurling (fun z => μ z * g z)) p volume :=
    fun {g} hg => hbeurLp (hμmul hg)
  -- `eLpNormEssSup μ = ENNReal.ofReal k`.
  have hessSup_eq : eLpNormEssSup μ volume = ENNReal.ofReal k := by
    rw [hk_def, ENNReal.ofReal_toReal hμtop]
  -- Quantitative contraction estimate on functions, for the operator `S u = beurling (μ·u)`:
  -- `eLpNorm (beurling (μ · u)) p ≤ ofReal (k*C) * eLpNorm u p`.
  have hSeLp : ∀ {u : ℂ → ℂ}, MemLp u p volume →
      eLpNorm (beurling (fun z => μ z * u z)) p volume
        ≤ ENNReal.ofReal (k * C) * eLpNorm u p volume := by
    intro u hu
    calc eLpNorm (beurling (fun z => μ z * u z)) p volume
        ≤ ENNReal.ofReal C * eLpNorm (fun z => μ z * u z) p volume :=
          hCbound _ (hμmul hu)
      _ ≤ ENNReal.ofReal C * (eLpNormEssSup μ volume * eLpNorm u p volume) := by
          gcongr; exact eLpNorm_mul_le_essSup_mul hμmeas.aestronglyMeasurable hu
      _ = ENNReal.ofReal C * (ENNReal.ofReal k * eLpNorm u p volume) := by rw [hessSup_eq]
      _ = ENNReal.ofReal (k * C) * eLpNorm u p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC0, mul_comm C k]
  -- Beurling subtractivity on `Lᵖ` (a corollary of additivity L4').
  have hbeurling_sub : ∀ {u v : ℂ → ℂ}, MemLp u p volume → MemLp v p volume →
      beurling (fun w => u w - v w) =ᵐ[volume] beurling u - beurling v := by
    intro u v hu hv
    have hadd := beurling_add_ae_lp hp hp' hv (show MemLp (fun w => u w - v w) p volume from
      hu.sub hv)
    -- `v + (u - v) = u`.
    have hvuv : ((v : ℂ → ℂ) + fun w => u w - v w) = u := by funext w; simp
    rw [hvuv] at hadd
    -- so `beurling u =ᵐ beurling v + beurling (u - v)`.
    filter_upwards [hadd] with z hz
    simp only [Pi.add_apply, Pi.sub_apply] at hz ⊢
    rw [hz]; ring
  -- The contraction factor `K := (k·C).toNNReal < 1`.
  set K : ℝ≥0 := (k * C).toNNReal with hK_def
  have hkC0 : 0 ≤ k * C := mul_nonneg hk0 hC0
  have hKlt : K < 1 := by rw [hK_def, Real.toNNReal_lt_one]; exact hcontr
  have hKcoe : (K : ℝ≥0∞) = ENNReal.ofReal (k * C) := rfl
  -- The affine self-map `Φ` of `Lᵖ` whose fixed point solves the equation.
  set Φ : Lp ℂ p volume → Lp ℂ p volume :=
    fun G => MemLp.toLp h hh + MemLp.toLp _ (hSmem (Lp.memLp G)) with hΦ_def
  -- `Φ` is `K`-Lipschitz: pass through `coeFn` and the contraction estimate.
  have hΦlip : LipschitzWith K Φ := by
    intro x y
    -- `Φ x - Φ y =  (μ·beurling x).toLp - (μ·beurling y).toLp` (the constant cancels).
    have hdiff : ⇑(Φ x) - ⇑(Φ y)
        =ᵐ[volume] ⇑(MemLp.toLp _ (hSmem (Lp.memLp x)))
          - ⇑(MemLp.toLp _ (hSmem (Lp.memLp y))) := by
      simp only [hΦ_def]
      filter_upwards [Lp.coeFn_add (MemLp.toLp h hh) (MemLp.toLp _ (hSmem (Lp.memLp x))),
        Lp.coeFn_add (MemLp.toLp h hh) (MemLp.toLp _ (hSmem (Lp.memLp y)))] with z h1 h2
      simp only [Pi.sub_apply, h1, h2, Pi.add_apply]; ring
    -- a.e. identity: this difference equals `beurling (μ · (x - y))` a.e.
    have hcoe : (⇑(MemLp.toLp _ (hSmem (Lp.memLp x)))
          - ⇑(MemLp.toLp _ (hSmem (Lp.memLp y))) : ℂ → ℂ)
        =ᵐ[volume]
          beurling (fun w => μ w * ((x : ℂ → ℂ) w - (y : ℂ → ℂ) w)) := by
      -- `beurling (μ·x) - beurling (μ·y) =ᵐ beurling (μ·x - μ·y) =ᵐ beurling (μ·(x-y))`.
      have hbsub := hbeurling_sub (hμmul (Lp.memLp x)) (hμmul (Lp.memLp y))
      have hcongr : (fun w => μ w * (x : ℂ → ℂ) w - μ w * (y : ℂ → ℂ) w)
          = fun w => μ w * ((x : ℂ → ℂ) w - (y : ℂ → ℂ) w) := by funext w; ring
      rw [hcongr] at hbsub
      filter_upwards [MemLp.coeFn_toLp (hSmem (Lp.memLp x)),
        MemLp.coeFn_toLp (hSmem (Lp.memLp y)), hbsub] with z hzx hzy hzb
      simp only [Pi.sub_apply] at hzx hzy ⊢
      rw [hzx, hzy, hzb]
      simp only [Pi.sub_apply]
    -- Compute the `edist`s as `eLpNorm`s and apply the contraction estimate.
    rw [Lp.edist_def, Lp.edist_def, eLpNorm_congr_ae hdiff, eLpNorm_congr_ae hcoe, hKcoe]
    calc eLpNorm (beurling (fun w => μ w * ((x : ℂ → ℂ) w - (y : ℂ → ℂ) w))) p volume
        ≤ ENNReal.ofReal (k * C)
            * eLpNorm (fun w => (x : ℂ → ℂ) w - (y : ℂ → ℂ) w) p volume :=
          hSeLp ((Lp.memLp x).sub (Lp.memLp y))
      _ = ENNReal.ofReal (k * C) * eLpNorm (⇑x - ⇑y) p volume := rfl
  -- The contraction `Φ` has a fixed point `G₀ ∈ Lᵖ` in the complete space `Lᵖ`.
  have hΦcontr : ContractingWith K Φ := ⟨hKlt, hΦlip⟩
  set G₀ : Lp ℂ p volume := hΦcontr.fixedPoint Φ with hG₀_def
  have hfix : Φ G₀ = G₀ := hΦcontr.fixedPoint_isFixedPt
  -- Extract the function `G := ⇑G₀` and verify the equation.
  refine ⟨⇑G₀, Lp.memLp G₀, ?_⟩
  -- From `Φ G₀ = G₀`: `G₀ =ᵐ h + (μ·beurling G₀)`.
  have hG₀eq : (G₀ : ℂ → ℂ) =ᵐ[volume]
      ⇑(MemLp.toLp h hh) + ⇑(MemLp.toLp _ (hSmem (Lp.memLp G₀))) := by
    have hval : (MemLp.toLp h hh + MemLp.toLp _ (hSmem (Lp.memLp G₀)) : Lp ℂ p volume) = G₀ :=
      hfix
    calc (G₀ : ℂ → ℂ) =ᵐ[volume]
          ⇑(MemLp.toLp h hh + MemLp.toLp _ (hSmem (Lp.memLp G₀))) := by
            rw [hval]
      _ =ᵐ[volume] ⇑(MemLp.toLp h hh) + ⇑(MemLp.toLp _ (hSmem (Lp.memLp G₀))) :=
            Lp.coeFn_add _ _
  -- Replace `toLp`'s by their function representatives.
  filter_upwards [hG₀eq, MemLp.coeFn_toLp hh, MemLp.coeFn_toLp (hSmem (Lp.memLp G₀))]
    with z hzeq hzh hzS
  simp only [Pi.add_apply] at hzeq ⊢
  rw [hzeq, hzh, hzS]

/-! ## Soundness note: there is no pointwise/weak Wirtinger bridge for bare `W^{1,2}_loc`

One might attempt to phrase L5/L6 through the **pointwise** Wirtinger derivatives
`dz f`, `dzbar f` (built from `fderiv ℝ f`) and reconcile them with the **weak**
gradient `(gx, gy)` of `MemW12loc f` through a lemma asserting `(fderiv ℝ f ·) 1 =ᵐ gx`
and `(fderiv ℝ f ·) I =ᵐ gy`. That assertion is **false** for a bare `W^{1,2}_loc`
function: planar `W^{1,2}` functions need not be a.e. classically differentiable, and
even when they are, the a.e. classical partials need not equal the weak partials
(Cantor-type counterexamples). The genuine Bojarski statement is about the **weak**
gradient, and L5/L6 below are re-anchored accordingly. The pointwise-to-weak passage
is performed only at the *quasiconformal* consumer
(`IsQCAnalytic.dz_higher_integrability` in `QC/InverseQC.lean`), where the extra
orientation/Jacobian datum of `IsQCAnalytic` makes it sound. -/

/-! ## Helpers for L5 -/

/-- `MemLpLocOn _ 2 univ` upgrades to `LocallyIntegrable`. -/
theorem locallyIntegrable_of_memLpLocOn_two {h : ℂ → ℂ}
    (hh : MemLpLocOn h (2 : ℝ≥0∞) Set.univ) : LocallyIntegrable h volume := by
  intro x
  refine ⟨Metric.closedBall x 1, ?_, ?_⟩
  · exact Metric.closedBall_mem_nhds x one_pos
  · have hmem : MemLp h 2 (volume.restrict (Metric.closedBall x 1)) :=
      hh _ (Set.subset_univ _) (isCompact_closedBall x 1)
    haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall x 1)) :=
      isFiniteMeasure_restrict.2 (isCompact_closedBall x 1).measure_lt_top.ne
    exact hmem.integrable one_le_two

/-- A continuous compactly supported real function times a loc-`L²` function is
globally `L²` (the product is compactly supported and `L²` on its support, the
bounded factor coming from continuity on the compact support). -/
theorem memLp_two_smul_of_continuous_compactSupport_memLpLocOn
    {ψ : ℂ → ℝ} (hψcont : Continuous ψ) (hψcs : HasCompactSupport ψ)
    {u : ℂ → ℂ} (hu : MemLpLocOn u (2 : ℝ≥0∞) Set.univ) :
    MemLp (fun z => (ψ z : ℂ) * u z) 2 volume := by
  classical
  set K : Set ℂ := tsupport ψ with hKdef
  have hKcompact : IsCompact K := hψcs
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  -- Off `K`, `ψ = 0`, so the product is `0` everywhere off `K`.
  have hvanish : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ K → (ψ z : ℂ) * u z = 0 := by
    filter_upwards with z hz
    rw [show ψ z = 0 from image_eq_zero_of_notMem_tsupport hz]; simp
  -- On `K`, `ψ` is bounded (continuous on a compact set), and `u ∈ L²(K)`.
  have hψtop : MemLp (fun z => (ψ z : ℂ)) ⊤ (volume.restrict K) := by
    obtain ⟨C, hC⟩ := (hKcompact.bddAbove_image (hψcont.norm).continuousOn)
    refine memLp_top_of_bound ?_ C ?_
    · exact (Complex.continuous_ofReal.comp hψcont).aestronglyMeasurable
    · refine (ae_restrict_iff' hKmeas).2 ?_
      filter_upwards with z hz
      rw [Complex.norm_real]
      exact hC ⟨z, hz, rfl⟩
  have huK : MemLp u 2 (volume.restrict K) := hu _ (Set.subset_univ _) hKcompact
  have hprodK : MemLp (fun z => (ψ z : ℂ) * u z) 2 (volume.restrict K) := by
    have := huK.smul (φ := fun z => (ψ z : ℂ)) hψtop (p := ⊤) (q := 2) (r := 2)
    simpa only [smul_eq_mul] using this
  exact memLp_of_memLpLocOn_compact_vanishing hKcompact hprodK hvanish

/-- A continuous compactly supported real function times a loc-`Lᵖ` function is
globally `Lᵖ` (the product is compactly supported and `Lᵖ` on its support, the
bounded factor coming from continuity on the compact support). The general-exponent
generalisation of `memLp_two_smul_of_continuous_compactSupport_memLpLocOn`, used by the
higher-integrability cutoff representation at `p = 3`. -/
theorem memLp_smul_of_continuous_compactSupport_memLpLocOn {p : ℝ≥0∞} (_hp : p ≠ ⊤)
    (_hp0 : p ≠ 0) {ψ : ℂ → ℝ} (hψcont : Continuous ψ) (hψcs : HasCompactSupport ψ)
    {u : ℂ → ℂ} (hu : MemLpLocOn u p Set.univ) :
    MemLp (fun z => (ψ z : ℂ) * u z) p volume := by
  classical
  set K : Set ℂ := tsupport ψ with hKdef
  have hKcompact : IsCompact K := hψcs
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  -- Off `K`, `ψ = 0`, so the product is `0` everywhere off `K`.
  have hvanish : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ K → (ψ z : ℂ) * u z = 0 := by
    filter_upwards with z hz
    rw [show ψ z = 0 from image_eq_zero_of_notMem_tsupport hz]; simp
  -- On `K`, `ψ` is bounded (continuous on a compact set), and `u ∈ Lᵖ(K)`.
  have hψtop : MemLp (fun z => (ψ z : ℂ)) ⊤ (volume.restrict K) := by
    obtain ⟨C, hC⟩ := (hKcompact.bddAbove_image (hψcont.norm).continuousOn)
    refine memLp_top_of_bound ?_ C ?_
    · exact (Complex.continuous_ofReal.comp hψcont).aestronglyMeasurable
    · refine (ae_restrict_iff' hKmeas).2 ?_
      filter_upwards with z hz
      rw [Complex.norm_real]
      exact hC ⟨z, hz, rfl⟩
  have huK : MemLp u p (volume.restrict K) := hu _ (Set.subset_univ _) hKcompact
  have hprodK : MemLp (fun z => (ψ z : ℂ) * u z) p (volume.restrict K) := by
    have := huK.smul (φ := fun z => (ψ z : ℂ)) hψtop (p := ⊤) (q := p) (r := p)
    simpa only [smul_eq_mul] using this
  exact memLp_of_memLpLocOn_compact_vanishing hKcompact hprodK hvanish

/-- A continuous compactly supported function is globally bounded, hence in `L∞`. -/
theorem memLp_top_of_continuous_hasCompactSupport {g : ℂ → ℂ}
    (hcont : Continuous g) (hcs : HasCompactSupport g) : MemLp g ⊤ volume := by
  obtain ⟨C, hC⟩ := (hcs.isCompact.bddAbove_image hcont.norm.continuousOn)
  refine memLp_top_of_bound hcont.aestronglyMeasurable (max C 0) (Filter.Eventually.of_forall ?_)
  intro z
  by_cases hz : z ∈ tsupport g
  · exact le_trans (hC ⟨z, hz, rfl⟩) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]; exact le_max_right _ _

/-- The Beurling transform respects a.e. equality of `L²` inputs. -/
theorem beurling_congr_ae {a b : ℂ → ℂ} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume)
    (hab : a =ᵐ[volume] b) : beurling a =ᵐ[volume] beurling b := by
  have hmeas : AEStronglyMeasurable (fun z => beurling a z - beurling b z) volume :=
    (memLp_beurling ha).1.sub (memLp_beurling hb).1
  have hzero : eLpNorm (fun z => beurling a z - beurling b z) 2 volume = 0 := by
    refine le_antisymm ?_ (zero_le _)
    refine le_trans (eLpNorm_beurling_sub_le ha hb) ?_
    have : eLpNorm (a - b) 2 volume = 0 := by
      rw [eLpNorm_eq_zero_iff (ha.1.sub hb.1) (by norm_num)]
      filter_upwards [hab] with z hz; simp [Pi.sub_apply, hz]
    rw [this, mul_zero]
  have hae := (eLpNorm_eq_zero_iff hmeas (by norm_num)).1 hzero
  filter_upwards [hae] with z hz
  exact sub_eq_zero.1 hz

/-! ## L5 — the cutoff representation of `∂(χ·f)` -/

/-- **L5 (weak-gradient form).** The weak-Leibniz cutoff representation, phrased
entirely on the **weak gradient**. Let `f` be loc-`L²` with weak partials `gx, gy`
(direction `1`, `I`), loc-`L²`, solving the Beltrami equation in its *weak* Wirtinger
form `½(gx + i gy) = μ · ½(gx − i gy)` a.e. (i.e. `∂̄f = μ ∂f` for the weak gradient),
and let `χ` be a smooth compactly supported real cutoff. Writing
`Gx := χ·gx + (∂₁χ)·f`, `Gy := χ·gy + (∂_I χ)·f` (the weak partials of `χ·f` from the
smooth Leibniz rule) and `WG := ½(Gx − i Gy)` for the weak `∂`-field of `χ·f`, there
is an `L²` remainder `h` with `WG =ᵐ h + T(μ · WG)`.

This is the **sound** restatement: it makes no claim about the pointwise Fréchet
derivative `fderiv ℝ f`. The previous form spoke of `dz (χ·f)` (built from `fderiv`)
and reconciled it with `WG` through a planar-Stepanov bridge that is false for a bare
`W^{1,2}_loc` function; here the conclusion lives on `WG` directly.

*Sketch.* `χ·f` is `W^{1,2}` with compact support, so L1'
(`dz_aeeq_beurling_dzbar_of_compactW12`) gives `WG =ᵐ T(WbarG)` with
`WbarG := ½(Gx + i Gy)` the weak `∂̄`-field. By the (pointwise, purely algebraic) weak
Leibniz identities `WG = χ·Wf + (∂χ)·f`, `WbarG = χ·Wbarf + (∂̄χ)·f`, and the weak
Beltrami equation `Wbarf = μ · Wf`, split `WbarG = μ · WG + R` with the
cutoff-commutator remainder `R = f·(∂̄χ − μ·∂χ)` compactly supported in `L²`; take
`h := T R`.

*Hypothesis note.* `R` contains the term `μ·(∂χ)·f`, which is `L²` only when
`μ ∈ L∞`; with a merely measurable `μ` it can fail to be integrable. We therefore
keep the (always available) finiteness hypothesis `hμfin : eLpNormEssSup μ volume ≠ ⊤`.
*Dependency:* `dz_aeeq_beurling_dzbar_of_compactW12`, the weak Leibniz rule. -/
theorem dz_cutoff_eq_beurling_repr {f gx gy : ℂ → ℂ}
    (hfcont : Continuous f)
    (hfLp : MemLpLocOn f (2 : ℝ≥0∞) Set.univ)
    (hgx : HasWeakDirDeriv 1 gx f Set.univ) (hgy : HasWeakDirDeriv Complex.I gy f Set.univ)
    (hgxLp : MemLpLocOn gx (2 : ℝ≥0∞) Set.univ) (hgyLp : MemLpLocOn gy (2 : ℝ≥0∞) Set.univ)
    {μ : ℂ → ℂ} (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hbel : ∀ᵐ z, (1 / 2 : ℂ) * (gx z + Complex.I * gy z)
      = μ z * ((1 / 2 : ℂ) * (gx z - Complex.I * gy z)))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ (F Gx Gy h R : ℂ → ℂ),
      HasCompactSupport F ∧ MemLp F 2 volume ∧ MemLp Gx 2 volume ∧ MemLp Gy 2 volume ∧
      HasWeakDirDeriv 1 Gx F Set.univ ∧ HasWeakDirDeriv Complex.I Gy F Set.univ ∧
      (∀ z, (fun z => (1 / 2 : ℂ) *
          ((χ z • gx z + ((fderiv ℝ χ z) 1) • f z)
            - Complex.I * (χ z • gy z + ((fderiv ℝ χ z) Complex.I) • f z))) z
        = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) ∧
      MemLp h 2 volume ∧ MemLp h 3 volume ∧
      MemLp (fun z => (1 / 2 : ℂ) *
        ((χ z • gx z + ((fderiv ℝ χ z) 1) • f z)
          - Complex.I * (χ z • gy z + ((fderiv ℝ χ z) Complex.I) • f z))) 2 volume ∧
      (fun z => (1 / 2 : ℂ) *
        ((χ z • gx z + ((fderiv ℝ χ z) 1) • f z)
          - Complex.I * (χ z • gy z + ((fderiv ℝ χ z) Complex.I) • f z))) =ᵐ[volume]
        h + beurling (fun z => μ z * ((1 / 2 : ℂ) *
          ((χ z • gx z + ((fderiv ℝ χ z) 1) • f z)
            - Complex.I * (χ z • gy z + ((fderiv ℝ χ z) Complex.I) • f z)))) ∧
      -- The **antiholomorphic relation**, surfaced from the proof's internal `L1` split:
      -- `R` is the cutoff-commutator remainder (compactly supported, `L²` and `L³`) and the
      -- weak `∂̄`-field `½(Gx + I·Gy)` of `χ·f` equals `μ·WG + R` a.e., where
      -- `WG = ½(Gx − I·Gy)` is the weak `∂`-field. This is what lets the Gehring reverse-Hölder
      -- node convert the full gradient `‖Gx‖ + ‖Gy‖` back to `‖WG‖` (plus the `L²`/`L³` forcing
      -- `‖R‖`) via the Wirtinger identities.
      MemLp R 2 volume ∧ MemLp R 3 volume ∧
      (∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z)
        = μ z * ((1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) + R z) := by
  classical
  -- ===== (0) Local integrability of the weak gradient and of `f`. =====
  have hfLI : LocallyIntegrable f volume := locallyIntegrable_of_memLpLocOn_two hfLp
  have hgxLI : LocallyIntegrable gx volume := locallyIntegrable_of_memLpLocOn_two hgxLp
  have hgyLI : LocallyIntegrable gy volume := locallyIntegrable_of_memLpLocOn_two hgyLp
  -- `χ` viewed in `ℂ`, and the cutoff product `F := χ·f`.
  set χc : ℂ → ℂ := fun w => (χ w : ℂ) with hχc_def
  set F : ℂ → ℂ := fun w => (χ w : ℂ) * f w with hF_def
  -- ===== (1) The cast `fderiv (χ:ℂ) v = ((fderiv χ) v : ℂ)`. =====
  have hχdiff : ∀ z, DifferentiableAt ℝ χ z :=
    fun z => (hχ.differentiable (by norm_num)).differentiableAt
  have hcast : ∀ z v, (fderiv ℝ χc z) v = ((fderiv ℝ χ z) v : ℂ) := by
    intro z v
    have hcomp : HasFDerivAt χc (Complex.ofRealCLM.comp (fderiv ℝ χ z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (hχdiff z).hasFDerivAt
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  -- ===== (2) Weak gradient of `F` via the smooth-multiplication Leibniz rule. =====
  have hgxon : LocallyIntegrableOn gx Set.univ := hgxLI.locallyIntegrableOn _
  have hgyon : LocallyIntegrableOn gy Set.univ := hgyLI.locallyIntegrableOn _
  have hfon : LocallyIntegrableOn f Set.univ := hfLI.locallyIntegrableOn _
  -- `Gx`, `Gy` are the weak `x`/`y` partials of `F = χ • f`.
  set Gx : ℂ → ℂ := fun z => χ z • gx z + ((fderiv ℝ χ z) 1) • f z with hGx_def
  set Gy : ℂ → ℂ := fun z => χ z • gy z + ((fderiv ℝ χ z) Complex.I) • f z with hGy_def
  have hGxweak : HasWeakDirDeriv 1 Gx F Set.univ := by
    have := hgx.smul_smooth hχ hfon hgxon
    simpa only [hF_def, hGx_def] using this
  have hGyweak : HasWeakDirDeriv Complex.I Gy F Set.univ := by
    have := hgy.smul_smooth hχ hfon hgyon
    simpa only [hF_def, hGy_def] using this
  -- ===== (3) `Gx`, `Gy` are loc-`L²` (in fact globally `L²`; here loc suffices). =====
  -- `χ • gx`, `(∂₁χ) • f` etc. are smooth(-coeff) · loc-`L²`, compactly supported, so `L²`.
  have hχ1cont : Continuous (fun z => (fderiv ℝ χ z) 1) :=
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hχIcont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hχ1cs : HasCompactSupport (fun z => (fderiv ℝ χ z) 1) :=
    HasCompactSupport.fderiv_apply ℝ hχc 1
  have hχIcs : HasCompactSupport (fun z => (fderiv ℝ χ z) Complex.I) :=
    HasCompactSupport.fderiv_apply ℝ hχc Complex.I
  -- Global `L²` membership of the four product pieces.
  have hχgx_mem : MemLp (fun z => (χ z : ℂ) * gx z) 2 volume :=
    memLp_two_smul_of_continuous_compactSupport_memLpLocOn hχ.continuous hχc hgxLp
  have hχgy_mem : MemLp (fun z => (χ z : ℂ) * gy z) 2 volume :=
    memLp_two_smul_of_continuous_compactSupport_memLpLocOn hχ.continuous hχc hgyLp
  have hχ1f_mem : MemLp (fun z => ((fderiv ℝ χ z) 1 : ℝ) • f z) 2 volume := by
    have := memLp_two_smul_of_continuous_compactSupport_memLpLocOn hχ1cont hχ1cs hfLp
    simpa only [Complex.real_smul] using this
  have hχIf_mem : MemLp (fun z => ((fderiv ℝ χ z) Complex.I : ℝ) • f z) 2 volume := by
    have := memLp_two_smul_of_continuous_compactSupport_memLpLocOn hχIcont hχIcs hfLp
    simpa only [Complex.real_smul] using this
  -- `Gx`, `Gy` globally `L²` (sums of `L²` pieces).
  have hGx_mem : MemLp Gx 2 volume := by
    have heq : Gx = (fun z => (χ z : ℂ) * gx z) + (fun z => ((fderiv ℝ χ z) 1 : ℝ) • f z) := by
      funext z; simp only [hGx_def, Pi.add_apply, Complex.real_smul]
    rw [heq]; exact hχgx_mem.add hχ1f_mem
  have hGy_mem : MemLp Gy 2 volume := by
    have heq : Gy = (fun z => (χ z : ℂ) * gy z)
        + (fun z => ((fderiv ℝ χ z) Complex.I : ℝ) • f z) := by
      funext z; simp only [hGy_def, Pi.add_apply, Complex.real_smul]
    rw [heq]; exact hχgy_mem.add hχIf_mem
  have hGxLp : MemLpLocOn Gx 2 Set.univ := fun K _ hK => (hGx_mem.restrict K)
  have hGyLp : MemLpLocOn Gy 2 Set.univ := fun K _ hK => (hGy_mem.restrict K)
  -- ===== (4) `F` has compact support and is loc-`L²`. =====
  have hF_cs : HasCompactSupport F := by
    apply HasCompactSupport.intro (hχc.isCompact) (fun z hz => ?_)
    have : χ z = 0 := by
      by_contra h
      exact hz (subset_tsupport χ (by simp [Function.mem_support, h]))
    simp [hF_def, this]
  have hF_Lp : MemLpLocOn F 2 Set.univ := by
    intro K _ hK
    have := memLp_two_smul_of_continuous_compactSupport_memLpLocOn hχ.continuous hχc hfLp
    exact this.restrict K
  -- ===== (5) L1' applied to `F`: `½(Gx − iGy) =ᵐ beurling (½(Gx + iGy))`. =====
  have hL1' := dz_aeeq_beurling_dzbar_of_compactW12 hF_cs hF_Lp hGxweak hGyweak hGxLp hGyLp
  -- The two `L²` Wirtinger objects of `F` in weak form.
  set WG : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z) with hWG_def
  set WbarG : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) with hWbarG_def
  have hWG_mem : MemLp WG 2 volume := by
    have hrw : WG = (1 / 2 : ℂ) • Gx + (-(1 / 2 : ℂ) * Complex.I) • Gy := by
      funext z; simp only [hWG_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hrw]; exact (hGx_mem.const_smul _).add (hGy_mem.const_smul _)
  have hWbarG_mem : MemLp WbarG 2 volume := by
    have hrw : WbarG = (1 / 2 : ℂ) • Gx + ((1 / 2 : ℂ) * Complex.I) • Gy := by
      funext z; simp only [hWbarG_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hrw]; exact (hGx_mem.const_smul _).add (hGy_mem.const_smul _)
  -- ===== (6) The weak `∂`/`∂̄`-fields of `f` (no pointwise `fderiv` of `f`/`F`). =====
  -- `Wf := ½(gx − igy)`, `Wbarf := ½(gx + igy)` are the weak Wirtinger derivatives of `f`.
  set Wf : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gx z - Complex.I * gy z) with hWf_def
  set Wbarf : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gx z + Complex.I * gy z) with hWbarf_def
  -- ===== (7) The pointwise weak Leibniz identities (pure algebra, no `f`-differentiability). =====
  -- `WG = χ·Wf + (dz χc)·f`, `WbarG = χ·Wbarf + (dzbar χc)·f`.
  have hdzχc : ∀ z, dz χc z = (1 / 2 : ℂ) * (((fderiv ℝ χ z) 1 : ℂ)
      - Complex.I * ((fderiv ℝ χ z) Complex.I : ℂ)) := by
    intro z; simp only [dz, hcast]
  have hdzbarχc : ∀ z, dzbar χc z = (1 / 2 : ℂ) * (((fderiv ℝ χ z) 1 : ℂ)
      + Complex.I * ((fderiv ℝ χ z) Complex.I : ℂ)) := by
    intro z; simp only [dzbar, hcast]
  have hWG_leibniz : ∀ z, WG z = (χ z : ℂ) * Wf z + dz χc z * f z := by
    intro z
    simp only [hWG_def, hGx_def, hGy_def, hWf_def, hdzχc, Complex.real_smul]
    ring
  have hWbarG_leibniz : ∀ z, WbarG z = (χ z : ℂ) * Wbarf z + dzbar χc z * f z := by
    intro z
    simp only [hWbarG_def, hGx_def, hGy_def, hWbarf_def, hdzbarχc, Complex.real_smul]
    ring
  -- ===== (8) The remainder `R := f·(dzbar χc − μ·dz χc)` is compactly supported `L²`. =====
  set R : ℂ → ℂ := fun z => f z * (dzbar χc z - μ z * dz χc z) with hR_def
  -- `dz χc`, `dzbar χc` are continuous with compact support ⊆ `tsupport (fderiv χ)`.
  have hdzχc_cont : Continuous (fun z => dz χc z) := by
    simp only [hdzχc]
    exact continuous_const.mul ((Complex.continuous_ofReal.comp hχ1cont).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp hχIcont)))
  have hdzbarχc_cont : Continuous (fun z => dzbar χc z) := by
    simp only [hdzbarχc]
    exact continuous_const.mul ((Complex.continuous_ofReal.comp hχ1cont).add
      (continuous_const.mul (Complex.continuous_ofReal.comp hχIcont)))
  have hdzχc_cs : HasCompactSupport (fun z => dz χc z) := by
    apply HasCompactSupport.of_support_subset_isCompact (hχc.fderiv ℝ)
    intro z hz
    simp only [Function.mem_support, hdzχc] at hz
    have hfd : fderiv ℝ χ z ≠ 0 := fun h => hz (by simp [h])
    exact subset_tsupport (fun z => fderiv ℝ χ z) hfd
  have hdzbarχc_cs : HasCompactSupport (fun z => dzbar χc z) := by
    apply HasCompactSupport.of_support_subset_isCompact (hχc.fderiv ℝ)
    intro z hz
    simp only [Function.mem_support, hdzbarχc] at hz
    have hfd : fderiv ℝ χ z ≠ 0 := fun h => hz (by simp [h])
    exact subset_tsupport (fun z => fderiv ℝ χ z) hfd
  -- `R` is `L²`: it is `f` (loc-`L²`) times the globally bounded coefficient
  -- `c = dzbar χc − μ·dz χc ∈ L∞` (using `hμfin` to bound `μ`).
  set Kc : Set ℂ := tsupport (fun z => fderiv ℝ χ z) with hKc_def
  have hKc_compact : IsCompact Kc := hχc.fderiv ℝ
  set c : ℂ → ℂ := fun z => dzbar χc z - μ z * dz χc z with hc_def
  -- `μ ∈ L∞(volume)`, `dz χc`, `dzbar χc ∈ L∞(volume)`, hence `c ∈ L∞(volume)`.
  have hμtop : MemLp μ ⊤ volume := by
    refine ⟨hμmeas.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_exponent_top]; exact lt_of_le_of_ne le_top hμfin
  have hdzχc_top : MemLp (fun z => dz χc z) ⊤ volume :=
    memLp_top_of_continuous_hasCompactSupport hdzχc_cont hdzχc_cs
  have hdzbarχc_top : MemLp (fun z => dzbar χc z) ⊤ volume :=
    memLp_top_of_continuous_hasCompactSupport hdzbarχc_cont hdzbarχc_cs
  have hμdz_top : MemLp (fun z => μ z * dz χc z) ⊤ volume := by
    have := hdzχc_top.smul (φ := μ) hμtop (p := ⊤) (q := ⊤) (r := ⊤)
    simpa only [smul_eq_mul] using this
  have hc_top : MemLp c ⊤ volume := by
    have hsub := hdzbarχc_top.sub hμdz_top
    simpa only [hc_def, Pi.sub_apply] using hsub
  have hKcmeas : MeasurableSet Kc := hKc_compact.measurableSet
  have hR_mem : MemLp R 2 volume := by
    -- `R` vanishes off `Kc`, and equals `f · c` (`L²(Kc)`) on `Kc`.
    have hRvanish : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ Kc → R z = 0 := by
      filter_upwards with z hz
      have hfd0 : fderiv ℝ χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have h1 : dz χc z = 0 := by simp [hdzχc, hfd0]
      have h2 : dzbar χc z = 0 := by simp [hdzbarχc, hfd0]
      simp [hR_def, h1, h2]
    have hfKc : MemLp f 2 (volume.restrict Kc) := hfLp _ (Set.subset_univ _) hKc_compact
    have hcKc : MemLp c ⊤ (volume.restrict Kc) := hc_top.restrict Kc
    -- `R = c • f` is `L²(Kc)` (`L∞ · L²`).
    have hRKc : MemLp R 2 (volume.restrict Kc) := by
      have hprod := hfKc.smul (φ := c) hcKc (p := ⊤) (q := 2) (r := 2)
      have heq : (c • f : ℂ → ℂ) = R := by
        funext z
        change c z • f z = R z
        simp only [hR_def, hc_def, smul_eq_mul]; ring
      rw [heq] at hprod; exact hprod
    exact memLp_of_memLpLocOn_compact_vanishing hKc_compact hRKc hRvanish
  -- `R` is in fact `L³` (`δ = 1` higher integrability): on the compact `Kc`, `f` is
  -- bounded (continuous on a compact set), so `f ∈ L∞(Kc)`, hence `R = c·f ∈ L∞(Kc)`,
  -- which on the finite-measure set `Kc` lies in `L³(Kc)`; `R` vanishes off `Kc`, so
  -- it is globally `L³`. (Uses continuity of `f`, the new hypothesis.)
  have hR3_mem : MemLp R 3 volume := by
    have hRvanish : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ Kc → R z = 0 := by
      filter_upwards with z hz
      have hfd0 : fderiv ℝ χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have h1 : dz χc z = 0 := by simp [hdzχc, hfd0]
      have h2 : dzbar χc z = 0 := by simp [hdzbarχc, hfd0]
      simp [hR_def, h1, h2]
    -- `f ∈ L∞(Kc)` from continuity (bounded on the compact `Kc`).
    have hfKc_top : MemLp f ⊤ (volume.restrict Kc) := by
      obtain ⟨C, hC⟩ := hKc_compact.bddAbove_image hfcont.norm.continuousOn
      refine memLp_top_of_bound hfcont.aestronglyMeasurable.restrict C ?_
      refine (ae_restrict_iff' hKcmeas).2 ?_
      filter_upwards with z hz
      exact hC ⟨z, hz, rfl⟩
    have hcKc : MemLp c ⊤ (volume.restrict Kc) := hc_top.restrict Kc
    haveI : IsFiniteMeasure (volume.restrict Kc) :=
      isFiniteMeasure_restrict.2 hKc_compact.measure_lt_top.ne
    -- `R = c • f ∈ L∞(Kc)`, then drop to `L³(Kc)` (finite measure).
    have hRKc_top : MemLp R ⊤ (volume.restrict Kc) := by
      have hprod := hfKc_top.smul (φ := c) hcKc (p := ⊤) (q := ⊤) (r := ⊤)
      have heq : (c • f : ℂ → ℂ) = R := by
        funext z
        change c z • f z = R z
        simp only [hR_def, hc_def, smul_eq_mul]; ring
      rw [heq] at hprod; exact hprod
    have hRKc3 : MemLp R 3 (volume.restrict Kc) := hRKc_top.mono_exponent le_top
    exact memLp_of_memLpLocOn_compact_vanishing hKc_compact hRKc3 hRvanish
  -- ===== (9) Assemble the representation. =====
  -- `WbarG =ᵐ μ · WG + R` (using the *weak* Beltrami equation `Wbarf = μ · Wf` and the
  -- pointwise weak Leibniz forms; no `fderiv` of `f`/`F` enters).
  have hsplit : WbarG =ᵐ[volume] (fun z => μ z * WG z) + R := by
    filter_upwards [hbel] with z hbelz
    -- pointwise: `WbarG z = χ·Wbarf z + dzbar χc·f`, and `WG z = χ·Wf z + dz χc·f`.
    have hWbarG := hWbarG_leibniz z
    have hWG := hWG_leibniz z
    -- `Wbarf z = μ z · Wf z` is exactly the weak Beltrami hypothesis `hbel`.
    have hWbarf_val : Wbarf z = μ z * Wf z := hbelz
    simp only [Pi.add_apply, hR_def]
    rw [hWbarG, hWbarf_val, hWG]
    ring
  -- `beurling WbarG =ᵐ beurling (μ·WG) + beurling R`.
  have hμWG_mem : MemLp (fun z => μ z * WG z) 2 volume := by
    have := hWG_mem.smul (φ := μ) hμtop (p := ⊤) (q := 2) (r := 2)
    simpa only [smul_eq_mul] using this
  have hbeur_split : beurling WbarG =ᵐ[volume]
      beurling (fun z => μ z * WG z) + beurling R := by
    have h1 : beurling WbarG =ᵐ[volume] beurling ((fun z => μ z * WG z) + R) :=
      beurling_congr_ae hWbarG_mem (hμWG_mem.add hR_mem) hsplit
    have h2 : beurling ((fun z => μ z * WG z) + R) =ᵐ[volume]
        beurling (fun z => μ z * WG z) + beurling R :=
      beurling_add_ae (Or.inl hμWG_mem) (Or.inl hR_mem)
    exact h1.trans h2
  -- Final chain: `WG =ᵐ beurling WbarG =ᵐ beurling (μ·WG) + beurling R`.
  -- We additionally hand back the primitive bundle `(F, Gx, Gy)` and its already-proven
  -- facts (compact support, `L²`, weak partials, and `WG = ½(Gx − I·Gy)`).
  refine ⟨F, Gx, Gy, beurling R, R, hF_cs, ?_, hGx_mem, hGy_mem, hGxweak, hGyweak, ?_,
    memLp_beurling hR_mem, memLp_beurling_of_memLp (by norm_num) (by norm_num) hR3_mem,
    hWG_mem, ?_, hR_mem, hR3_mem, ?_⟩
  · -- `F = χ·f ∈ L²`: `χ` is continuous with compact support, `f` is loc-`L²`.
    exact memLp_two_smul_of_continuous_compactSupport_memLpLocOn hχ.continuous hχc hfLp
  · -- `WG = ½(Gx − I·Gy)` is the definition of `WG`.
    intro z; rw [hWG_def]
  · -- The `L²` Beltrami representation `WG =ᵐ beurling R + beurling (μ·WG)`.
    calc WG =ᵐ[volume] beurling WbarG := hL1'
      _ =ᵐ[volume] beurling (fun z => μ z * WG z) + beurling R := hbeur_split
      _ =ᵐ[volume] beurling R + beurling (fun z => μ z * WG z) := by
            filter_upwards with z; simp only [Pi.add_apply]; ring
  · -- The antiholomorphic relation `WbarG =ᵐ μ·WG + R`, i.e. `½(Gx + I·Gy) =ᵐ μ·WG + R`,
    -- is exactly the internal split `hsplit` (in the explicit `Gx`/`Gy` notation, which is
    -- definitionally the `set`-bound `WbarG`/`WG`).
    filter_upwards [hsplit] with z hz
    simpa only [hWbarG_def, hWG_def, hGx_def, hGy_def, Pi.add_apply] using hz

/-! ## The inhomogeneity higher-integrability residual (Gehring / Stoilow)

L4 (`exists_memLp_solution_of_beltrami_fixedPoint`) produces an `Lᵖ` solution of the
Beltrami fixed-point equation `G = h + T(μ·G)` **only when the inhomogeneity is already
`Lᵖ`** (`hh : MemLp h p`, `p > 2`). L5 (`dz_cutoff_eq_beurling_repr`) delivers an `L²`
solution `dz(χ·f) =ᵐ h + T(μ·dz(χ·f))` whose inhomogeneity `h = T R`, `R = f·(∂̄χ − μ∂χ)`,
is compactly supported **`L²`** — and `R ∈ Lᵖ` is *precisely the higher integrability we
are trying to prove* (on the transition annulus `supp ∇χ`), so feeding L4 directly is
circular. The classical resolution is the **Gehring reverse-Hölder / Caccioppoli
self-improvement** (or, equivalently, reduction to the **Stoilow principal solution**):
an `L²` Beltrami fixed point with `‖μ‖∞ < 1` is automatically `Lᵖ_loc` for some `p > 2`,
without an `Lᵖ` hypothesis on `h`.

The Gehring reverse-Hölder / Caccioppoli self-improvement lives in
`Analysis/SingularIntegral/GehringHigherIntegrability.lean`, at the
**`f`-level**: the reverse-Hölder node `reverseHolder_of_weakGradient` (S1) consumes the
primitive bundle `(F, Gx, Gy)` of which `G = ½(Gx − I·Gy)` is the weak holomorphic
gradient, and reduces to the genuinely analytic nodes `sobolevPoincare_ball` (N1),
`weakIBP_against_W12` (N2), `caccioppoli_of_beltrami` (N3), together with the abstract
Gehring lemma `gehring_selfImprovement` (S2). L6 below reduces — by a
fully compiled argument — to that file's residual `beltrami_fixedPoint_memLpLocOn`,
which is the **decoupled** statement (no external exponent `p`, constant `C`, or `Lᵖ`
hypothesis on `h`): it needs the `L²` fixed-point data, its primitive bundle, and the
contraction `‖μ‖∞ < 1`, and concludes `∃ q > 2, G ∈ Lᵠ_loc`.

This wrapper exposes that conclusion in the per-fixed-point existential form L6 consumes;
its proof forwards into S3 (`beltrami_fixedPoint_memLpLocOn`, whose exponent is uniform
over fixed points) and discharges the per-fixed-point clause with the present data, threading
the primitive bundle `(F, Gx, Gy)` supplied by L5. -/
theorem beltrami_fixedPoint_memLpLocOn_of_memLp_two {μ F G Gx Gy h R : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1)
    (hFcs : HasCompactSupport F) (hFmem : MemLp F 2 volume)
    (hGmem : MemLp G 2 volume) (hhmem : MemLp h 2 volume) (hhmem3 : MemLp h 3 volume)
    (hGxmem : MemLp Gx 2 volume) (hGymem : MemLp Gy 2 volume)
    (hGxweak : HasWeakDirDeriv 1 Gx F Set.univ)
    (hGyweak : HasWeakDirDeriv Complex.I Gy F Set.univ)
    (hGdef : ∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z))
    (hGeq : G =ᵐ[volume] h + beurling (fun z => μ z * G z))
    (hRmem : MemLp R 2 volume) (hRmem3 : MemLp R 3 volume)
    (hRrel : ∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z) :
    ∃ q : ℝ, 2 < q ∧ MemLpLocOn G (ENNReal.ofReal q) Set.univ := by
  obtain ⟨q, hq2, hloc⟩ := beltrami_fixedPoint_memLpLocOn hμmeas hμfin hμbound
  exact ⟨q, hq2,
    hloc hFcs hFmem hGmem hhmem hhmem3 hGxmem hGymem hGxweak hGyweak hGdef hGeq
      hRmem hRmem3 hRrel⟩

/-! ## L6 — the assembled higher-integrability target -/

/-- **L6 (assembled target, weak-gradient form).** Let `f` be loc-`L²` with loc-`L²`
weak partials `gx, gy` (direction `1`, `I`) solving the Beltrami equation in its weak
Wirtinger form `½(gx + i gy) = μ · ½(gx − i gy)` a.e., with `‖μ‖∞ < 1`. Then the weak
holomorphic Wirtinger derivative `Wdz := ½(gx − i gy)` is locally in `Lᵖ` for some
`p > 2`.

This is the **sound** Bojarski conclusion: it speaks of the weak gradient, never of
`fderiv ℝ f`. `QC/InverseQC.lean`'s `beltrami_higher_integrability` reduces to this,
and the *quasiconformal* consumer there bridges from `Wdz` back to the pointwise
`dz f` using `IsQCAnalytic` data.

*Sketch (as implemented).* Choose `p > 2` with contraction `‖μ‖∞ · C < 1` (L2). A
compact `K` lies in some open ball `ball 0 r`; pick the cutoff `χ` from a
`ContDiffBump` with inner radius `> r`, so `χ ≡ 1` on a neighborhood of `K`. On the
open `ball 0 r`, `χ ≡ 1` so `fderiv ℝ χ = 0`, hence the weak `∂`-field of `χ·f`,
`WG := ½(Gx − i Gy)` with `Gx = χ·gx + (∂₁χ)·f` etc., equals `Wdz` pointwise on the
ball. L5 (`dz_cutoff_eq_beurling_repr`) represents `WG` as an `L²` Beltrami fixed
point `= h + T(μ·WG)` with `h ∈ L²`; the inhomogeneity higher-integrability residual
(`beltrami_fixedPoint_memLpLocOn_of_memLp_two`) upgrades this to `WG ∈ Lᵖ_loc`.
Restricting to `K` and transporting along `WG = Wdz` on `ball 0 r ⊇ K` gives
`Wdz ∈ Lᵖ(K)`. *Dependency:* L2 (`exists_p_gt_two_beurling_contraction`), L5, the
residual lemma. -/
theorem dz_memLpLocOn_of_beltrami {μ : ℂ → ℂ} (hμmeas : Measurable μ)
    (hμbound : eLpNormEssSup μ volume < 1) {f gx gy : ℂ → ℂ}
    (hfcont : Continuous f)
    (hfLp : MemLpLocOn f (2 : ℝ≥0∞) Set.univ)
    (hgx : HasWeakDirDeriv 1 gx f Set.univ) (hgy : HasWeakDirDeriv Complex.I gy f Set.univ)
    (hgxLp : MemLpLocOn gx (2 : ℝ≥0∞) Set.univ) (hgyLp : MemLpLocOn gy (2 : ℝ≥0∞) Set.univ)
    (hbel : ∀ᵐ z, (1 / 2 : ℂ) * (gx z + Complex.I * gy z)
      = μ z * ((1 / 2 : ℂ) * (gx z - Complex.I * gy z))) :
    ∃ p : ℝ, 2 < p ∧
      MemLpLocOn (fun z => (1 / 2 : ℂ) * (gx z - Complex.I * gy z)) (ENNReal.ofReal p)
        Set.univ := by
  classical
  have hμfin : eLpNormEssSup μ volume ≠ ⊤ := hμbound.ne_top
  -- ===== S3: the uniform Gehring exponent `q > 2` for *all* `L²` fixed points. =====
  -- The exponent is chosen *before* fixing the compact set `K`; the residual is
  -- quantified over fixed points, so the cutoff field for each `K` reuses this `q`.
  obtain ⟨q, hq2, hqloc⟩ :=
    beltrami_fixedPoint_memLpLocOn hμmeas hμfin hμbound
  refine ⟨q, hq2, ?_⟩
  -- The weak `∂`-field of `f`, the conclusion target.
  set Wdz : ℂ → ℂ := fun z => (1 / 2 : ℂ) * (gx z - Complex.I * gy z) with hWdz_def
  -- ===== The local claim on a compact `K`. =====
  intro K hKuniv hKcompact
  -- `K ⊆ ball 0 r` for some `r > 0`.
  obtain ⟨r, hr0, hKr⟩ := hKcompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  -- The cutoff `χ` from a `ContDiffBump` centered at `0` with `rIn = r + 1 > r`,
  -- `rOut = r + 2`; smooth, real, compactly supported, and `≡ 1` near `K`.
  set bump : ContDiffBump (0 : ℂ) :=
    ⟨r + 1, r + 2, by linarith, by linarith⟩ with hbump_def
  set χ : ℂ → ℝ := fun z => bump z with hχ_def
  have hχsmooth : ContDiff ℝ ∞ χ := bump.contDiff
  have hχcs : HasCompactSupport χ := bump.hasCompactSupport
  -- On the open `ball 0 r ⊇ K`, `χ ≡ 1`.
  have hballopen : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hχone : ∀ z ∈ Metric.ball (0 : ℂ) r, χ z = 1 := by
    intro z hz
    refine bump.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Metric.mem_ball] at *
    simp only [hbump_def]; exact le_of_lt (lt_of_lt_of_le hz (by linarith))
  -- On `ball 0 r`, `χ ≡ 1` on an open neighborhood, hence `fderiv ℝ χ = 0` there.
  have hχfderiv0 : ∀ z ∈ Metric.ball (0 : ℂ) r, fderiv ℝ χ z = 0 := by
    intro z hz
    have hEq : χ =ᶠ[nhds z] (fun _ => (1 : ℝ)) := by
      filter_upwards [hballopen.mem_nhds hz] with w hw using hχone w hw
    rw [hEq.fderiv_eq]; simp
  -- The weak `∂`-field `WG := ½(Gx − i Gy)` of the cutoff `χ·f`, with
  -- `Gx = χ·gx + (∂₁χ)·f`, `Gy = χ·gy + (∂_I χ)·f`.
  set WG : ℂ → ℂ := fun z => (1 / 2 : ℂ) *
    ((χ z • gx z + ((fderiv ℝ χ z) 1) • f z)
      - Complex.I * (χ z • gy z + ((fderiv ℝ χ z) Complex.I) • f z)) with hWG_def
  -- On `ball 0 r`, `WG = Wdz`: `χ = 1`, `fderiv ℝ χ = 0` collapse `Gx → gx`, `Gy → gy`.
  have hWG_eq_Wdz : ∀ z ∈ Metric.ball (0 : ℂ) r, WG z = Wdz z := by
    intro z hz
    simp only [hWG_def, hWdz_def, hχone z hz, hχfderiv0 z hz, ContinuousLinearMap.zero_apply]
    simp
  -- ===== L5: the `L²` Beltrami representation of `WG`, with `WG ∈ L²`, plus the
  -- primitive bundle `(F, Gx, Gy)` and its `W^{1,2}` facts that the Gehring residual needs.
  obtain ⟨F, Gx, Gy, h, R, hF_cs, hF_mem, hGx_mem, hGy_mem, hGxweak, hGyweak, hWG_leibniz,
      hhmem, hhmem3, hWG_mem2, hrepr, hRmem, hRmem3, hRrel⟩ :=
    dz_cutoff_eq_beurling_repr hfcont hfLp hgx hgy hgxLp hgyLp hμmeas hμfin hbel hχsmooth hχcs
  -- Apply the uniform Gehring residual to *this* cutoff fixed point: `WG ∈ Lᵠ_loc`,
  -- with the *same* exponent `q` committed above (the residual is uniform over the
  -- fixed-point bundle `(F, G, Gx, Gy, h, R)`), threading the primitive bundle from L5, the
  -- `δ = 1` higher integrability `h, R ∈ L³` it now carries, and the antiholomorphic relation
  -- `½(Gx + I·Gy) =ᵐ μ·WG + R` that lets the reverse-Hölder node convert the full gradient.
  -- Fold the explicit `½(Gx − I·Gy)` on the relation's RHS into the `set`-bound `WG`, so the
  -- relation matches the form S3 expects (`½(Gx + I·Gy) =ᵐ μ·WG + R`).
  have hRrel' : ∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * WG z + R z := by
    filter_upwards [hRrel] with z hz
    have hWGz : WG z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z) := hWG_leibniz z
    rw [hz, hWGz]
  have hlocp : MemLpLocOn WG (ENNReal.ofReal q) Set.univ :=
    hqloc hF_cs hF_mem hWG_mem2 hhmem hhmem3 hGx_mem hGy_mem hGxweak hGyweak hWG_leibniz hrepr
      hRmem hRmem3 hRrel'
  -- Transport from `WG` to `Wdz` on `K` via the equality on `ball 0 r ⊇ K`.
  have hKsubBall : K ⊆ Metric.ball (0 : ℂ) r := hKr
  have hWGK : MemLp WG (ENNReal.ofReal q) (volume.restrict K) :=
    hlocp K (Set.subset_univ _) hKcompact
  have hcongrK : WG =ᵐ[volume.restrict K] Wdz := by
    refine (ae_restrict_iff' hKcompact.measurableSet).2 ?_
    filter_upwards with z hzK
    exact hWG_eq_Wdz z (hKsubBall hzK)
  exact hWGK.ae_eq hcongrK

end RiemannDynamics

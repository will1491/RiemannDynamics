/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.DirichletPrinciple
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The Dirichlet principle for boundary-vanishing Lipschitz competitors

The Dirichlet principle for competitors that merely vanish on `∂U` — the form the extremal
ρ-distance competitor takes in the reciprocity lower bound — follows from the compact-support
**Lipschitz**
Dirichlet principle (`dirichletEnergy_le_of_compactSupport_lipschitz`) by a boundary cutoff, with no
mollification needed.

Given `φ := w − u` Lipschitz and vanishing outside `U`, multiply by a cutoff `χₙ` (equal to `1`
where `dist(·, Uᶜ) ≥ 2/n`, `0` on the shell `dist ≤ 1/n`) to get `φₙ := φ·χₙ`, Lipschitz with
compact
support inside `U`. The compact-support Lipschitz principle gives `dirichletEnergy u U ≤
dirichletEnergy (u + φₙ) U`, and the cutoff energy converges, `dirichletEnergy (u + φₙ) U →
dirichletEnergy w U`: the removed energy `∫ |∇(φ(1 − χₙ))|²` vanishes because `|φ| ≤ K·dist(·, Uᶜ)`
(Lipschitz plus `φ = 0` off `U`) bounds `∫ φ²|∇χₙ|²` by a constant times the shell measure, which
tends to `0` (the shells decrease to `∅` in the finite-measure `U`). Passing to the limit yields the
claim.

The eikonal → `M₀` assembly needs the competitor `w − u` only **locally** Lipschitz on `U` — the
harmonic potential `u` is singular at the slit tips, so `w − u` is Lipschitz on compact subsets of
`U` but not globally. The variant `dirichletEnergy_le_of_hardy_boundaryVanishing` replaces the
global-Lipschitz hypothesis with a Hardy bound `∫_U (w−u)²/dist(·, Uᶜ)² < ∞`: the shell energy
`∫ φ²|∇χₙ|²` is now dominated by `4∫_{shell} φ²/d²` (on the shell `d < 2/(n+1)` so `|∇χₙ| ≤ n+1 <
2/d`), a tail of the finite Hardy integral, and each cutoff `φ·χₙ` is globally Lipschitz because it
is supported in a compact subset of `U` on which `φ` is Lipschitz and tapers to `0` at the boundary.

## Main statements

* `dirichletEnergy_le_of_lipschitz_boundaryVanishing` — the Dirichlet principle for a boundary-
  vanishing Lipschitz competitor.
* `dirichletEnergy_le_of_hardy_boundaryVanishing` — the same for a boundary-vanishing *locally*
  Lipschitz competitor with a finite Hardy integral.

## References

* L. C. Evans, *Partial Differential Equations*, §5.3–5.5 (Sobolev spaces, `H¹₀`).
-/

open MeasureTheory Filter Metric Topology
open scoped ENNReal NNReal Topology Manifold Convolution

namespace RiemannDynamics

/-- **The Dirichlet principle for a compact-support `W¹²` perturbation.** The Lipschitz hypothesis
of `dirichletEnergy_le_of_compactSupport_lipschitz` can be relaxed: if `u` is harmonic on `U` and
`φ := w − u` is continuous, compactly supported inside `U`, a.e. differentiable, its classical
`fderiv` is the weak directional derivative of the complex embedding `(φ ·)` in the coordinate
directions (ACL), and `∫_{tsupport φ} ‖∇φ‖² < ∞`, then `dirichletEnergy u U ≤ dirichletEnergy w U`.
Green's first identity `∫_U ⟪∇u, ∇φ⟫ = −∫_U φ·Δu = 0` holds with `φ` merely `W¹²` — its weak
derivative pairs against the smooth `∇u` by compact-support integration by parts — and `Δu = 0`. -/
theorem dirichletEnergy_le_of_compactSupport_weakDeriv {u w : ℂ → ℝ} {U : Set ℂ}
    (hUopen : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcont : Continuous (fun z => w z - u z))
    (hcs : HasCompactSupport (fun z => w z - u z))
    (hsub : tsupport (fun z => w z - u z) ⊆ U)
    (haediff : ∀ᵐ z : ℂ, DifferentiableAt ℝ (fun z => w z - u z) z)
    (hweakACL : ∀ v : ℂ, ‖v‖ = 1 →
      HasWeakDirDeriv v (fun z => ((fderiv ℝ (fun y => w y - u y) z v : ℝ) : ℂ))
        (fun z => ((w z - u z : ℝ) : ℂ)) Set.univ)
    (hφ2 : IntegrableOn (fun z => ‖fderiv ℝ (fun y => w y - u y) z‖ ^ 2)
      (tsupport (fun z => w z - u z)) volume) :
    dirichletEnergy u U ≤ dirichletEnergy w U := by
  classical
  set φ : ℂ → ℝ := fun z => w z - u z with hφ
  set Kc : Set ℂ := tsupport φ with hKc
  have hKcc : IsCompact Kc := hcs
  have hKcU : Kc ⊆ U := hsub
  have hKcmeas : MeasurableSet Kc := (isClosed_tsupport φ).measurableSet
  haveI : Fact (volume Kc < ⊤) := ⟨hKcc.measure_lt_top⟩
  -- `φ` continuous, locally integrable, a.e. differentiable.
  have hcont_φ : Continuous φ := hcont
  have hφloc : LocallyIntegrable φ := hcont_φ.locallyIntegrable
  have hφ_aediff : ∀ᵐ z : ℂ, DifferentiableAt ℝ φ z := haediff
  -- `u` is real-analytic (harmonic ⟹ analytic), hence `C^∞`, on `U`.
  have huanal : ∀ z ∈ U, AnalyticAt ℝ u z := fun z hz => HarmonicAt.analyticAt (hu z hz)
  have hu_cd : ∀ z ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) u z := fun z hz => (huanal z hz).contDiffAt
  have hu2 : ContDiffOn ℝ 2 u U := hu.contDiffOn
  have hudiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
    fun z hz => (hu2.differentiableOn (by norm_num)).differentiableAt (hUopen.mem_nhds hz)
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu2.fderiv_of_isOpen hUopen (by norm_num)
  have hucont1 : ContinuousOn (fderiv ℝ u) U := hfd1.continuousOn
  -- The complex embedding `φℂ` of the real perturbation.
  set φℂ : ℂ → ℂ := fun z => (φ z : ℂ) with hφℂ
  have hcont_φℂ : Continuous φℂ := Complex.continuous_ofReal.comp hcont_φ
  have hφℂloc : LocallyIntegrable φℂ := hcont_φℂ.locallyIntegrable
  -- **A smooth cutoff `χ`**: `χ ≡ 1` on a neighbourhood of `Kc`, compact support inside `U`.
  obtain ⟨T, hTc, hKcT, hTU⟩ := exists_compact_between hKcc hUopen hKcU
  have hTcl : IsClosed T := hTc.isClosed
  obtain ⟨χ0, hχ1, hχ0, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞))
      (isClosed_tsupport φ) hKcT
  set χ : ℂ → ℝ := fun z => χ0 z with hχ
  have hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ := contMDiff_iff_contDiff.mp χ0.contMDiff
  have hχ0T : ∀ z ∉ T, χ z = 0 := hχ0
  have hχ_supp : Function.support χ ⊆ T := by
    intro z hz; by_contra hzT; exact hz (hχ0T z hzT)
  have hχ_cs : HasCompactSupport χ :=
    HasCompactSupport.of_support_subset_isCompact hTc hχ_supp
  have hχ_tsupp : tsupport χ ⊆ U := (closure_minimal hχ_supp hTcl).trans hTU
  -- `χ ≡ 1` on the open neighbourhood `W ⊇ Kc`.
  have hχ1nhds : ∀ᶠ z in 𝓝ˢ Kc, χ z = 1 := hχ1
  obtain ⟨W, hWopen, hKcW, hχ1W⟩ : ∃ W, IsOpen W ∧ Kc ⊆ W ∧ ∀ z ∈ W, χ z = 1 := by
    rw [Filter.eventually_iff, mem_nhdsSet_iff_exists] at hχ1nhds
    obtain ⟨W, hWopen, hKcW, hW⟩ := hχ1nhds
    exact ⟨W, hWopen, hKcW, fun z hz => hW hz⟩
  -- `fderiv ℝ φ z = 0` off `Kc` (there `φ ≡ 0` on the open `Kcᶜ`).
  have hφfd0 : ∀ z ∉ Kc, fderiv ℝ φ z = 0 := by
    intro z hz
    have hopen : IsOpen Kcᶜ := (isClosed_tsupport φ).isOpen_compl
    have hloc : φ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [hloc.fderiv_eq]; simp
  -- **Green's first identity, per direction (`W¹²` form).**
  -- `∫ (∂ᵥu)(∂ᵥφ) = − ∫ (∂ᵥ∂ᵥu) φ`, via the weak derivative of `φℂ` tested against `χ·∂ᵥu`.
  have ibp : ∀ v : ℂ, ‖v‖ = 1 → ∫ z, (fderiv ℝ u z v) * (fderiv ℝ φ z v)
      = - ∫ z, (fderiv ℝ (fun y => fderiv ℝ u y v) z v) * φ z := by
    intro v hv
    -- The smooth directional derivative `a = ∂ᵥu`, defined and `C^∞` on `U`.
    set a : ℂ → ℝ := fun z => fderiv ℝ u z v with ha
    have ha_cd : ∀ z ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) a z := by
      intro z hz
      have : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ u) z :=
        ((hu_cd z hz).fderiv_right (m := (⊤ : ℕ∞)) le_rfl)
      exact this.clm_apply contDiffAt_const
    -- The globally smooth test function `ψ = χ · a`.
    set ψ : ℂ → ℝ := fun z => χ z * a z with hψ
    have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z ∈ tsupport χ
      · exact (hχ_cd.contDiffAt).mul (ha_cd z (hχ_tsupp hz))
      · have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
        have heq : ψ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [hopen.mem_nhds hz] with y hy
          simp only [hψ, image_eq_zero_of_notMem_tsupport hy, zero_mul]
        exact contDiffAt_const.congr_of_eventuallyEq heq
    have hψ_cs : HasCompactSupport ψ := hχ_cs.mul_right
    have hψ_tsupp : tsupport ψ ⊆ Set.univ := Set.subset_univ _
    -- The weak identity for `φℂ` in direction `v` (ACL form), tested with `ψ`.
    have hW := hweakACL v hv ψ hψ_cd hψ_cs hψ_tsupp
    -- Turn the two `ℂ`-integrals into `ofReal` of real integrals.
    have hLHS : (∫ z, ((fderiv ℝ ψ z) v) • φℂ z)
        = ((∫ z, (fderiv ℝ ψ z v) * φ z : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with z
      simp only [hφℂ, Complex.real_smul, Complex.ofReal_mul]
    have hRHS : (∫ z, ψ z • ((fderiv ℝ φ z v : ℝ) : ℂ))
        = ((∫ z, ψ z * (fderiv ℝ φ z v) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with z
      simp only [Complex.real_smul, Complex.ofReal_mul]
    rw [hLHS, hRHS] at hW
    have hWreal : (∫ z, (fderiv ℝ ψ z v) * φ z) = - ∫ z, ψ z * (fderiv ℝ φ z v) := by
      have := hW
      rw [← Complex.ofReal_neg] at this
      exact Complex.ofReal_injective this
    -- Replace `ψ` by `a` in both integrands (they agree on `Kc`, and off `Kc` both vanish).
    have hL_eq : (∫ z, (fderiv ℝ ψ z v) * φ z)
        = ∫ z, (fderiv ℝ (fun y => fderiv ℝ u y v) z v) * φ z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Kc
      · have hzW : z ∈ W := hKcW hz
        have hψa : ψ =ᶠ[𝓝 z] a := by
          filter_upwards [hWopen.mem_nhds hzW] with y hy
          simp only [hψ, hχ1W y hy, one_mul]
        rw [hψa.fderiv_eq]
      · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
    have hR_eq : (∫ z, ψ z * (fderiv ℝ φ z v))
        = ∫ z, (fderiv ℝ u z v) * (fderiv ℝ φ z v) := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Kc
      · have hzW : z ∈ W := hKcW hz
        simp only [hψ, hχ1W z hzW, one_mul, ha]
      · rw [hφfd0 z hz]; simp
    rw [hL_eq] at hWreal
    rw [hR_eq] at hWreal
    linarith [hWreal]
  -- **The pointwise Laplacian identity** (verbatim from the `C¹` proof).
  have hlap0 : ∀ z, (fderiv ℝ (fun y => fderiv ℝ u y 1) z 1
      + fderiv ℝ (fun y => fderiv ℝ u y Complex.I) z Complex.I) * φ z = 0 := by
    intro z
    by_cases hz : z ∈ Kc
    · have hzU : z ∈ U := hKcU hz
      have hharm : InnerProductSpace.HarmonicAt u z := hu z hzU
      have hfdd : DifferentiableAt ℝ (fderiv ℝ u) z :=
        (hharm.1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have e1 : fderiv ℝ (fun y => fderiv ℝ u y 1) z 1 = iteratedFDeriv ℝ 2 u z ![1, 1] := by
        rw [iteratedFDeriv_two_apply]
        have hcl := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ u) (u := fun _ : ℂ => (1 : ℂ))
          hfdd (differentiableAt_const _)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hcl]; simp
      have e2 : fderiv ℝ (fun y => fderiv ℝ u y Complex.I) z Complex.I
          = iteratedFDeriv ℝ 2 u z ![Complex.I, Complex.I] := by
        rw [iteratedFDeriv_two_apply]
        have hcl := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ u) (u := fun _ : ℂ => Complex.I)
          hfdd (differentiableAt_const _)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hcl]; simp
      have hlap : Laplacian.laplacian u z = 0 := hharm.2.self_of_nhds
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hlap
      simp only at hlap
      rw [e1, e2, hlap, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  -- `fderiv ℝ φ` is measurable.
  have hφfd_meas : Measurable (fderiv ℝ φ) := measurable_fderiv ℝ φ
  -- **The cross term** `cross = ⟪∇u, ∇φ⟫` in the `{1, I}` basis.
  set cross : ℂ → ℝ := fun z => (fderiv ℝ u z 1) * (fderiv ℝ φ z 1)
    + (fderiv ℝ u z Complex.I) * (fderiv ℝ φ z Complex.I) with hcross
  -- Integrability of `(∂ᵥ∂ᵥu)·φ` (continuous on `U`, support in `Kc`).
  have integ_of : ∀ g : ℂ → ℝ, ContinuousOn g U → Function.support g ⊆ Kc →
      Integrable g volume := by
    intro g hgU hgsupp
    exact (integrableOn_iff_integrable_of_support_subset hgsupp).mp
      ((hgU.mono hKcU).integrableOn_compact hKcc)
  have hI : ∀ v : ℂ,
      Integrable (fun z => (fderiv ℝ (fun y => fderiv ℝ u y v) z v) * φ z) volume := by
    intro v
    have haU : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z v) U :=
      hfd1.clm_apply (contDiffOn_const (c := v))
    have hcont_fdav_on : ContinuousOn (fun z => (fderiv ℝ (fun y => fderiv ℝ u y v) z) v) U :=
      (haU.continuousOn_fderiv_of_isOpen hUopen le_rfl).clm_apply continuousOn_const
    exact integ_of _ (hcont_fdav_on.mul hcont_φ.continuousOn)
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport φ))
  -- **`‖∇φ‖` is `L²` on the finite-measure compact `Kc`.**
  have hgradφ_L2 : MemLp (fun z => ‖fderiv ℝ φ z‖) 2 (volume.restrict Kc) := by
    rw [memLp_two_iff_integrable_sq (hφfd_meas.norm.aestronglyMeasurable.restrict)]
    have : (fun z => ‖fderiv ℝ φ z‖ ^ 2) = (fun z => ‖fderiv ℝ φ z‖ ^ 2) := rfl
    exact hφ2
  -- **`∂ᵥφ` is `L²`, hence `L¹`, on the finite-measure compact `Kc`** (for `‖v‖ ≤ 1`).
  have hφfdv_L2 : ∀ v : ℂ, ‖v‖ ≤ 1 →
      MemLp (fun z => fderiv ℝ φ z v) 2 (volume.restrict Kc) := by
    intro v hv
    refine hgradφ_L2.mono' ((measurable_fderiv_apply_const ℝ φ v).aestronglyMeasurable.restrict) ?_
    filter_upwards with z
    calc ‖fderiv ℝ φ z v‖ ≤ ‖fderiv ℝ φ z‖ * ‖v‖ := (fderiv ℝ φ z).le_opNorm v
      _ ≤ ‖fderiv ℝ φ z‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = ‖fderiv ℝ φ z‖ := mul_one _
  -- **Integrability of `(∂ᵥu)·(∂ᵥφ)`**: `∂ᵥu` continuous (bounded) on `Kc`, `∂ᵥφ ∈ L¹(Kc)`.
  have hIab : ∀ v : ℂ, ‖v‖ = 1 →
      Integrable (fun z => (fderiv ℝ u z v) * (fderiv ℝ φ z v)) volume := by
    intro v hv
    have hacont : ContinuousOn (fun z => (fderiv ℝ u z) v) U :=
      hucont1.clm_apply continuousOn_const
    have hsupp : Function.support (fun z => (fderiv ℝ u z v) * (fderiv ℝ φ z v)) ⊆ Kc := by
      intro z hz
      by_contra hzKc
      simp only [Function.mem_support, hφfd0 z hzKc, ContinuousLinearMap.zero_apply,
        mul_zero, ne_eq, not_true] at hz
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    obtain ⟨C, hC⟩ :=
      IsCompact.exists_bound_of_continuousOn hKcc (hacont.mono hKcU)
    have hφv_int : Integrable (fun z => fderiv ℝ φ z v) (volume.restrict Kc) :=
      (hφfdv_L2 v (le_of_eq hv)).integrable (by norm_num)
    have hbnd : ∀ᵐ z ∂(volume.restrict Kc), ‖fderiv ℝ u z v‖ ≤ C := by
      refine ae_restrict_of_forall_mem hKcmeas (fun z hz => ?_)
      exact hC z hz
    have hasm_u : AEStronglyMeasurable (fun z => fderiv ℝ u z v) (volume.restrict Kc) :=
      (measurable_fderiv_apply_const ℝ u v).aestronglyMeasurable.restrict
    exact hφv_int.bdd_mul hasm_u hbnd
  -- **The cross term integrates to zero**: `∫ cross = 0` (Green + `Δu = 0`).
  have hcross0 : ∫ z, cross z = 0 := by
    have hnorm1 : ‖(1 : ℂ)‖ = 1 := by simp
    have hnormI : ‖Complex.I‖ = 1 := by simp
    rw [hcross, integral_add (hIab 1 hnorm1) (hIab Complex.I hnormI),
      ibp 1 hnorm1, ibp Complex.I hnormI, ← neg_add, ← integral_add (hI 1) (hI Complex.I)]
    have hz0 : ∀ z, (fderiv ℝ (fun y => fderiv ℝ u y 1) z 1) * φ z
        + (fderiv ℝ (fun y => fderiv ℝ u y Complex.I) z Complex.I) * φ z = 0 := by
      intro z; rw [← add_mul]; exact hlap0 z
    rw [integral_congr_ae (by filter_upwards with z using hz0 z)]; simp
  -- The pointwise norm-square identity for a real functional on `ℂ` (the `{1, I}` basis).
  have normsq_dual : ∀ L : ℂ →L[ℝ] ℝ, ‖L‖ ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
    intro L
    have h := Complex.orthonormalBasisOneI.norm_dual L
    rw [Fin.sum_univ_two] at h
    rw [h]; congr 1 <;> congr 1
    · rw [show (Complex.orthonormalBasisOneI 0 : ℂ) = 1 by
        rw [Complex.coe_orthonormalBasisOneI]; rfl]
    · rw [show (Complex.orthonormalBasisOneI 1 : ℂ) = Complex.I by
        rw [Complex.coe_orthonormalBasisOneI]; rfl]
  -- `fderiv w = fderiv u` off `Kc` (there `w = u` locally, since `φ = 0`).
  have hfdeq : ∀ z ∈ U \ Kc, fderiv ℝ w z = fderiv ℝ u z := by
    intro z hz
    have hzc : z ∈ Kcᶜ := hz.2
    have hopen : IsOpen Kcᶜ := (isClosed_tsupport φ).isOpen_compl
    have heq : w =ᶠ[𝓝 z] u := by
      filter_upwards [hopen.mem_nhds hzc] with y hy
      have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp only [hφ] at hφy; linarith [hφy]
    exact heq.fderiv_eq
  -- `fderiv w = fderiv u + fderiv φ` a.e. on `U` (wherever `φ` is differentiable).
  have hfdadd_ae : ∀ᵐ z, z ∈ U → fderiv ℝ w z = fderiv ℝ u z + fderiv ℝ φ z := by
    filter_upwards [hφ_aediff] with z hzd hzU
    have hw' : HasFDerivAt w (fderiv ℝ u z + fderiv ℝ φ z) z := by
      refine (((hudiffU z hzU).hasFDerivAt).add (hzd.hasFDerivAt)).congr_of_eventuallyEq ?_
      filter_upwards with y; simp only [Pi.add_apply, hφ]; ring
    exact hw'.fderiv
  -- `‖fderiv ℝ u‖²` integrable on `Kc` (`u` continuous), `fderiv w = fderiv u + fderiv φ` a.e. on
  -- `Kc`.
  have hu_int : IntegrableOn (fun z => ‖fderiv ℝ u z‖ ^ 2) Kc volume :=
    ((hucont1.norm.pow 2).mono hKcU).integrableOn_compact hKcc
  have hfdadd_res : ∀ᵐ z ∂(volume.restrict Kc),
      fderiv ℝ w z = fderiv ℝ u z + fderiv ℝ φ z := by
    rw [ae_restrict_iff' hKcmeas]
    filter_upwards [hfdadd_ae] with z hz hzKc
    exact hz (hKcU hzKc)
  -- `‖fderiv ℝ φ‖²` integrable on `Kc` (the `L²` hypothesis).
  have hφ2_int : IntegrableOn (fun z => ‖fderiv ℝ φ z‖ ^ 2) Kc volume := hφ2
  -- `‖fderiv ℝ w‖²` integrable on `Kc`: `‖∇w‖² ≤ 2‖∇u‖² + 2‖∇φ‖²` a.e. on `Kc`.
  have hw_int : IntegrableOn (fun z => ‖fderiv ℝ w z‖ ^ 2) Kc volume := by
    have hdom : IntegrableOn (fun z => 2 * ‖fderiv ℝ u z‖ ^ 2 + 2 * ‖fderiv ℝ φ z‖ ^ 2) Kc
        volume := (hu_int.const_mul 2).add (hφ2_int.const_mul 2)
    have hmeas : AEStronglyMeasurable (fun z => ‖fderiv ℝ w z‖ ^ 2) (volume.restrict Kc) :=
      (((measurable_fderiv ℝ w).norm).pow_const 2).aestronglyMeasurable
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards [hfdadd_res] with z hz
    have hnn : (0 : ℝ) ≤ ‖fderiv ℝ w z‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg hnn, hz]
    have h1 : ‖fderiv ℝ u z + fderiv ℝ φ z‖ ≤ ‖fderiv ℝ u z‖ + ‖fderiv ℝ φ z‖ := norm_add_le _ _
    nlinarith [h1, norm_nonneg (fderiv ℝ u z), norm_nonneg (fderiv ℝ φ z),
      norm_nonneg (fderiv ℝ u z + fderiv ℝ φ z),
      sq_nonneg (‖fderiv ℝ u z‖ - ‖fderiv ℝ φ z‖)]
  have hcross_int : IntegrableOn cross Kc volume := by
    have h1 := (hIab 1 (by simp)).integrableOn (s := Kc)
    have h2 := (hIab Complex.I (by simp)).integrableOn (s := Kc)
    simpa only [hcross] using h1.add h2
  -- **The `Kc`-part energy inequality**: `∫⁻_Kc ‖∇u‖² ≤ ∫⁻_Kc ‖∇w‖²`.
  have hKpart : ∫⁻ z in Kc, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ z in Kc, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 := by
    have conv_u : ∫⁻ z in Kc, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal (∫ z in Kc, ‖fderiv ℝ u z‖ ^ 2) := by
      have hi : Integrable (fun z => ((‖fderiv ℝ u z‖₊ ^ 2 : ℝ≥0) : ℝ)) (volume.restrict Kc) := by
        simpa [NNReal.coe_pow, coe_nnnorm] using hu_int
      simp_rw [← ENNReal.coe_pow]
      rw [lintegral_coe_eq_integral (fun z => ‖fderiv ℝ u z‖₊ ^ 2) hi]
      simp [NNReal.coe_pow, coe_nnnorm]
    have conv_w : ∫⁻ z in Kc, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal (∫ z in Kc, ‖fderiv ℝ w z‖ ^ 2) := by
      have hi : Integrable (fun z => ((‖fderiv ℝ w z‖₊ ^ 2 : ℝ≥0) : ℝ)) (volume.restrict Kc) := by
        simpa [NNReal.coe_pow, coe_nnnorm] using hw_int
      simp_rw [← ENNReal.coe_pow]
      rw [lintegral_coe_eq_integral (fun z => ‖fderiv ℝ w z‖₊ ^ 2) hi]
      simp [NNReal.coe_pow, coe_nnnorm]
    rw [conv_u, conv_w]
    apply ENNReal.ofReal_le_ofReal
    have hexp_ae : ∀ᵐ z ∂(volume.restrict Kc), ‖fderiv ℝ w z‖ ^ 2
        = ‖fderiv ℝ u z‖ ^ 2 + (2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) := by
      filter_upwards [hfdadd_res] with z hz
      rw [normsq_dual (fderiv ℝ w z), normsq_dual (fderiv ℝ u z), normsq_dual (fderiv ℝ φ z),
        hz]
      simp only [ContinuousLinearMap.add_apply, hcross]; ring
    have hint_extra : IntegrableOn (fun z => 2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) Kc volume :=
      (hcross_int.const_mul 2).add hφ2_int
    have hstep : ∫ z in Kc, ‖fderiv ℝ w z‖ ^ 2
        = (∫ z in Kc, ‖fderiv ℝ u z‖ ^ 2) + ∫ z in Kc, (2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) := by
      rw [← integral_add hu_int hint_extra]
      exact integral_congr_ae hexp_ae
    rw [hstep]
    have hcrossKc : ∫ z in Kc, cross z = 0 := by
      rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
      · exact hcross0
      · filter_upwards with z hz
        have hfd0 : (fderiv ℝ φ z) = 0 := hφfd0 z hz
        simp only [hcross, hfd0]; simp
    have hextra_nonneg : 0 ≤ ∫ z in Kc, (2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) := by
      rw [integral_add (hcross_int.const_mul 2) hφ2_int, integral_const_mul, hcrossKc]
      simp only [mul_zero, zero_add]
      exact setIntegral_nonneg hKcmeas (fun z _ => by positivity)
    linarith
  -- Split each energy over `U = Kc ∪ (U \ Kc)`; the `U \ Kc` parts agree.
  have hsplit : ∀ f : ℂ → ℝ, dirichletEnergy f U
      = (∫⁻ z in Kc, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
        + ∫⁻ z in U \ Kc, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2 := by
    intro f
    unfold dirichletEnergy
    rw [← lintegral_inter_add_diff (B := Kc) _ U hKcmeas, Set.inter_eq_self_of_subset_right hKcU]
  rw [hsplit u, hsplit w]
  have hUKeq : ∫⁻ z in U \ Kc, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z in U \ Kc, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 := by
    apply setLIntegral_congr_fun (hUopen.measurableSet.diff hKcmeas)
    intro z hz; simp only [hfdeq z hz]
  rw [hUKeq]
  gcongr

/-- `Real.smoothTransition` is globally Lipschitz, with a uniform bound on its derivative: its
derivative is continuous and supported in `[0, 1]` (the function is constant off `[0, 1]`), hence
bounded, so the mean value inequality gives a global Lipschitz constant. -/
private theorem exists_lipschitz_smoothTransition :
    ∃ D : ℝ≥0, LipschitzWith D Real.smoothTransition ∧
      ∀ x, ‖deriv Real.smoothTransition x‖ ≤ (D : ℝ) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hdiff : Differentiable ℝ Real.smoothTransition := hcd.differentiable (by norm_num)
  have hderiv0 : ∀ x : ℝ, x < 0 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isOpen_Iio (a := (0 : ℝ))).mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [heq.deriv_eq]; simp
  have hderiv1 : ∀ x : ℝ, 1 < x → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      filter_upwards [(isOpen_Ioi (a := (1 : ℝ))).mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [heq.deriv_eq]; simp
  have hcs : HasCompactSupport (deriv Real.smoothTransition) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h; exact hx (hderiv0 x (by linarith [not_le.mp h]))
    · by_contra h; exact hx (hderiv1 x (by linarith [not_le.mp h]))
  have hcont : Continuous (deriv Real.smoothTransition) := hcd.continuous_deriv (by norm_num)
  obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support hcs
  have hDnn : (0 : ℝ) ≤ D := le_trans (norm_nonneg _) (hD 0)
  refine ⟨Real.toNNReal D, lipschitzWith_of_nnnorm_deriv_le hdiff (fun x => ?_), fun x => ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal D hDnn]; exact hD x
  · rw [Real.coe_toNNReal D hDnn]; exact hD x

/-- **A smooth boundary cutoff with distance-controlled gradient.** On a bounded open `U` (with
`Uᶜ` nonempty), writing `d z := infDist z Uᶜ`, for each `n` there is a `C^∞` cutoff `χ : ℂ → ℝ`,
valued in `[0, 1]`, with `χ = 0` where `d ≤ 1/(n+1)` (near `∂U`), `χ = 1` where `d ≥ 2/(n+1)`, a
uniform gradient bound `‖∇χ‖ ≤ 4·D·(n+1)`, and gradient supported inside the shell `d < 2/(n+1)`.
Built by mollifying `d` to a smooth `1`-Lipschitz `dₑ` within `1/(4(n+1))` of `d`
(`ContDiffBump` convolution) and composing with `Real.smoothTransition` of the affine
`4(n+1)·dₑ − 5`. -/
private theorem exists_smooth_boundaryCutoff {U : Set ℂ} (D : ℝ≥0)
    (hDderiv : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ (D : ℝ)) (n : ℕ) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z, Metric.infDist z Uᶜ ≤ 1 / ((n : ℝ) + 1) → χ z = 0) ∧
      (∀ z, 2 / ((n : ℝ) + 1) ≤ Metric.infDist z Uᶜ → χ z = 1) ∧
      (∀ z, ‖fderiv ℝ χ z‖ ≤ 4 * (D : ℝ) * ((n : ℝ) + 1)) ∧
      (∀ z, fderiv ℝ χ z ≠ 0 → Metric.infDist z Uᶜ < 2 / ((n : ℝ) + 1)) := by
  classical
  set d : ℂ → ℝ := fun z => Metric.infDist z Uᶜ with hd
  have hdlip : LipschitzWith 1 d := lipschitz_infDist_pt _
  have hdcont : Continuous d := hdlip.continuous
  set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  set φb : ContDiffBump (0 : ℂ) :=
    { rIn := ε / 2, rOut := ε, rIn_pos := by positivity, rIn_lt_rOut := by linarith } with hφb
  set de : ℂ → ℝ := fun x => (φb.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] d) x
    with hde
  have hde_cd : ContDiff ℝ (⊤ : ℕ∞) de :=
    HasCompactSupport.contDiff_convolution_left _ φb.hasCompactSupport_normed
      φb.contDiff_normed hdcont.locallyIntegrable
  have hde_diff : Differentiable ℝ de := hde_cd.differentiable (by norm_num)
  -- `dₑ` is `1`-Lipschitz: `dₑ x − dₑ y = ∫ φ(t)(d(x−t) − d(y−t))`, `|d(x−t)−d(y−t)| ≤ |x−y|`,
  -- `∫ φ = 1`.
  have hde_lip : LipschitzWith 1 de := by
    have hform : ∀ x : ℂ, de x = ∫ t, (φb.normed volume t) * d (x - t) := by
      intro x; rw [hde]; simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hex : ∀ x : ℂ, ConvolutionExistsAt (φb.normed volume) d x
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      HasCompactSupport.convolutionExists_left_of_continuous_right _ φb.hasCompactSupport_normed
        φb.continuous_normed.locallyIntegrable hdcont
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, hform x, hform y]
    have hsub : (∫ t, φb.normed volume t * d (x - t)) - ∫ t, φb.normed volume t * d (y - t)
        = ∫ t, φb.normed volume t * (d (x - t) - d (y - t)) := by
      rw [← integral_sub]
      · exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
      · have h1 := (hex x).integrable
        simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h1
      · have h2 := (hex y).integrable
        simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h2
    rw [hsub]
    calc |∫ t, φb.normed volume t * (d (x - t) - d (y - t))|
        ≤ ∫ t, |φb.normed volume t * (d (x - t) - d (y - t))| := abs_integral_le_integral_abs
      _ ≤ ∫ t, φb.normed volume t * dist x y := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _)
          · exact (φb.integrable_normed).mul_const _
          · refine Filter.Eventually.of_forall fun t => ?_
            simp only
            rw [abs_mul, abs_of_nonneg (φb.nonneg_normed t)]
            apply mul_le_mul_of_nonneg_left _ (φb.nonneg_normed t)
            have hdl := hdlip.dist_le_mul (x - t) (y - t)
            rw [Real.dist_eq] at hdl; simp only [NNReal.coe_one, one_mul] at hdl
            refine hdl.trans ?_
            rw [dist_eq_norm, dist_eq_norm]; apply le_of_eq; congr 1; abel
      _ = 1 * dist x y := by rw [integral_mul_const, φb.integral_normed, one_mul]
  have hde_fd1 : ∀ z, ‖fderiv ℝ de z‖ ≤ 1 := by
    intro z; simpa using norm_fderiv_le_of_lipschitz ℝ hde_lip (x₀ := z)
  -- `|dₑ − d| ≤ ε` since `d` varies by at most `ε` on balls of radius `ε = φb.rOut`.
  have hde_close : ∀ x, |de x - d x| ≤ ε := by
    intro x
    have hball : ∀ y ∈ Metric.ball x φb.rOut, dist (d y) (d x) ≤ ε := by
      intro y hy
      have hle : dist (d y) (d x) ≤ (1 : ℝ) * dist y x := by simpa using hdlip.dist_le_mul y x
      rw [one_mul] at hle
      exact hle.trans (le_of_lt (Metric.mem_ball.mp hy))
    have hd := ContDiffBump.dist_normed_convolution_le (φ := φb) (μ := volume)
      hdcont.aestronglyMeasurable hball
    rwa [Real.dist_eq] at hd
  -- The smooth cutoff `χ z = smoothTransition(4(n+1)·dₑ z − 5)`.
  set sc : ℝ := 4 * ((n : ℝ) + 1) with hsc
  have hscpos : 0 < sc := by rw [hsc]; positivity
  set χ : ℂ → ℝ := fun z => Real.smoothTransition (sc * de z - 5) with hχ
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hscε : sc * ε = 1 := by rw [hε, hsc]; field_simp
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul hde_cd).sub contDiff_const)
  · exact fun z => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · -- `d z ≤ 1/(n+1) ⟹ sc·dₑ z ≤ sc·(d z + ε) = sc·d z + 1 ≤ 4 + 1 = 5`.
    intro z hz
    have h1 : de z ≤ d z + ε := by linarith [abs_le.mp (hde_close z) |>.2]
    have hscd : sc * d z ≤ 4 := by rw [hsc]; rw [le_div_iff₀ hn1] at hz; nlinarith [hz, hn1]
    have hle0 : sc * de z - 5 ≤ 0 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hscpos); nlinarith [this, hscd, hscε]
    rw [hχ]; exact Real.smoothTransition.zero_of_nonpos hle0
  · -- `d z ≥ 2/(n+1) ⟹ sc·dₑ z ≥ sc·(d z − ε) = sc·d z − 1 ≥ 8 − 1 = 7 ≥ 5 + 1`.
    intro z hz
    have h1 : d z - ε ≤ de z := by linarith [abs_le.mp (hde_close z) |>.1]
    have hscd : 8 ≤ sc * d z := by rw [hsc]; rw [div_le_iff₀ hn1] at hz; nlinarith [hz, hn1]
    have h1le : (1 : ℝ) ≤ sc * de z - 5 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hscpos); nlinarith [this, hscd, hscε]
    rw [hχ]; exact Real.smoothTransition.one_of_one_le h1le
  · -- Chain rule: `∇χ = smoothTransition'(·) • (sc • ∇dₑ)`, so `‖∇χ‖ ≤ D·sc·1 = 4·D·(n+1)`.
    intro z
    have hchain : fderiv ℝ χ z
        = (deriv Real.smoothTransition (sc * de z - 5)) • (sc • fderiv ℝ de z) := by
      have h1 : HasFDerivAt (fun w => sc * de w - 5) (sc • fderiv ℝ de z) z := by
        have := ((hde_diff z).hasFDerivAt.const_mul sc).sub_const 5; simpa using this
      have h2 : HasDerivAt Real.smoothTransition
          (deriv Real.smoothTransition (sc * de z - 5)) (sc * de z - 5) :=
        (Real.smoothTransition.contDiff.differentiable (n := (⊤ : ℕ∞)) (by norm_num)
          ).differentiableAt.hasDerivAt
      exact (h2.comp_hasFDerivAt z h1).fderiv
    rw [hchain, norm_smul, norm_smul]
    have hb2 : ‖sc‖ * ‖fderiv ℝ de z‖ ≤ sc * 1 := by
      rw [Real.norm_of_nonneg (le_of_lt hscpos)]
      exact mul_le_mul_of_nonneg_left (hde_fd1 z) (le_of_lt hscpos)
    calc ‖deriv Real.smoothTransition (sc * de z - 5)‖ * (‖sc‖ * ‖fderiv ℝ de z‖)
        ≤ (D : ℝ) * (sc * 1) := mul_le_mul (hDderiv _) hb2 (by positivity) (by positivity)
      _ = 4 * (D : ℝ) * ((n : ℝ) + 1) := by rw [hsc]; ring
  · -- Gradient supported in `d < 2/(n+1)`: off it, `d z ≥ 2/(n+1) ⟹ sc·dₑ z − 5 > 1`, and `χ`
    -- is locally constant `= 1`, so `∇χ = 0`.
    intro z hz
    by_contra hge
    push Not at hge
    apply hz
    have hcont : Continuous (fun w : ℂ => sc * de w - 5) :=
      (continuous_const.mul hde_cd.continuous).sub continuous_const
    have h1 : d z - ε ≤ de z := by linarith [abs_le.mp (hde_close z) |>.1]
    have hscd : 8 ≤ sc * d z := by rw [hsc]; rw [div_le_iff₀ hn1] at hge; nlinarith [hge, hn1]
    have hzstrict : 1 < sc * de z - 5 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hscpos); nlinarith [this, hscd, hscε]
    have hopen : IsOpen {w : ℂ | 1 < sc * de w - 5} := isOpen_lt continuous_const hcont
    have heq : χ =ᶠ[nhds z] fun _ => (1 : ℝ) := by
      filter_upwards [hopen.mem_nhds (show z ∈ _ from hzstrict)] with w hw
      rw [hχ]; exact Real.smoothTransition.one_of_one_le (le_of_lt hw)
    rw [heq.fderiv_eq]; simp

/-- **The Dirichlet principle for a boundary-vanishing Lipschitz competitor.** If `u` is harmonic on
a bounded open `U` and `w − u` is Lipschitz and vanishes outside `U` (hence on `∂U`), then
`dirichletEnergy u U ≤ dirichletEnergy w U`. A boundary cutoff reduces this to the compact-support
Lipschitz Dirichlet principle: the cutoffs `u + (w−u)·χₙ` are compact-support-perturbation
competitors with energies converging to `dirichletEnergy w U` (the removed shell energy vanishes
since
`|w − u| ≤ K·dist(·, Uᶜ)` and the shells have measure tending to `0`). -/
theorem dirichletEnergy_le_of_lipschitz_boundaryVanishing {u w : ℂ → ℝ} {U : Set ℂ} {K : ℝ≥0}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hwulip : LipschitzWith K (fun z => w z - u z)) (hwu0 : ∀ z ∉ U, w z - u z = 0) :
    dirichletEnergy u U ≤ dirichletEnergy w U := by
  classical
  -- The Lipschitz perturbation `φ = w − u`, the boundary distance `d`, and the cutoffs.
  set φ : ℂ → ℝ := fun z => w z - u z with hφ
  set d : ℂ → ℝ := fun z => Metric.infDist z Uᶜ with hd
  have hdcont : Continuous d := (lipschitz_infDist_pt _).continuous
  have hdnn : ∀ z, 0 ≤ d z := fun z => Metric.infDist_nonneg
  have hUccl : IsClosed (Uᶜ : Set ℂ) := hUopen.isClosed_compl
  -- `Uᶜ` is nonempty because `U` is bounded (the whole plane is not).
  have hUc : (Uᶜ : Set ℂ).Nonempty := by
    obtain ⟨r, hr⟩ := hUbdd.subset_ball (0 : ℂ)
    refine ⟨((|r| + 1 : ℝ) : ℂ), fun hmem => ?_⟩
    have hb : ((|r| + 1 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := hr hmem
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |r| + 1)] at hb
    linarith [le_abs_self r]
  -- `z ∈ U ↔ d z > 0`.
  have hdU : ∀ z, z ∈ U ↔ 0 < d z := by
    intro z
    rw [hd, ← hUccl.notMem_iff_infDist_pos hUc]; simp
  -- `|φ z| ≤ K · d z` everywhere (Lipschitz plus `φ = 0` off `U`).
  have hφabs : ∀ z, |φ z| ≤ (K:ℝ) * d z := by
    intro z
    have hle : ∀ y ∈ (Uᶜ:Set ℂ), |φ z| ≤ (K:ℝ) * dist z y := by
      intro y hy
      have := hwulip.dist_le_mul z y
      rw [Real.dist_eq, show φ y = 0 from hwu0 y hy, sub_zero] at this
      exact this
    rcases eq_or_lt_of_le K.coe_nonneg with hK0 | hKpos
    · obtain ⟨y0, hy0⟩ := hUc
      have h := hle y0 hy0
      rw [← hK0, zero_mul] at h ⊢
      exact h
    · rw [hd, ← div_le_iff₀' hKpos, le_infDist hUc]
      intro y hy; rw [div_le_iff₀' hKpos]; exact hle y hy
  -- `φ` is Lipschitz, continuous, a.e. differentiable, with `‖∇φ‖ ≤ K`.
  have hφlip : LipschitzWith K φ := hwulip
  have hφ_aediff : ∀ᵐ z : ℂ, DifferentiableAt ℝ φ z := hφlip.ae_differentiableAt
  have hφfd_le : ∀ z, ‖fderiv ℝ φ z‖ ≤ (K:ℝ) := fun z => norm_fderiv_le_of_lipschitz ℝ hφlip
  -- `w = u + φ` everywhere.
  have hw_eq : ∀ z, w z = u z + φ z := by intro z; simp only [hφ]; ring
  -- `u` is `C²` on `U`, hence differentiable on `U`.
  have hu2 : ContDiffOn ℝ 2 u U := hu.contDiffOn
  have hudiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
    fun z hz => (hu2.differentiableOn (by norm_num)).differentiableAt (hUopen.mem_nhds hz)
  -- **The cutoff family.**  `χ n z = max 0 (min ((n+1)·d z − 1) 1)`, and `g n = χ n · φ`.
  set χ : ℕ → ℂ → ℝ := fun n z => max 0 (min (((n:ℝ)+1) * d z - 1) 1) with hχ
  set g : ℕ → ℂ → ℝ := fun n z => χ n z * φ z with hg
  set wn : ℕ → ℂ → ℝ := fun n z => u z + g n z with hwn
  have hKnn : (0:ℝ) ≤ (K:ℝ) := K.coe_nonneg
  -- Basic cutoff facts: `χ n ∈ [0,1]`, Lipschitz constant `n+1`, `χ n < 1 ⟹ d z < 2/(n+1)`.
  have hn1 : ∀ n : ℕ, (0:ℝ) < (n:ℝ)+1 := fun n => by positivity
  have hχ01 : ∀ n z, 0 ≤ χ n z ∧ χ n z ≤ 1 := by
    intro n z
    refine ⟨le_max_left _ _, ?_⟩
    rw [hχ]; simp only
    rcases le_or_gt (min (((n:ℝ)+1) * d z - 1) 1) 0 with h | h
    · rw [max_eq_left h]; norm_num
    · rw [max_eq_right (le_of_lt h)]; exact min_le_right _ _
  have hχlip : ∀ n : ℕ, LipschitzWith ((n:ℝ≥0)+1) (χ n) := by
    intro n
    have haff : LipschitzWith ((n:ℝ≥0)+1) (fun z : ℂ => ((n:ℝ)+1) * d z - 1) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq]
      have heq : ((n:ℝ)+1) * d x - 1 - (((n:ℝ)+1) * d y - 1)
          = ((n:ℝ)+1) * (d x - d y) := by ring
      rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
      have h1 : |d x - d y| ≤ dist x y := by
        have := (lipschitz_infDist_pt (Uᶜ : Set ℂ)).dist_le_mul x y
        simpa [hd, Real.dist_eq] using this
      push_cast
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    exact (haff.min_const 1).const_max 0
  have hχdsmall : ∀ n z, χ n z < 1 → d z < 2 / ((n:ℝ)+1) := by
    intro n z hz
    by_contra hge
    push Not at hge
    have haff : (1:ℝ) ≤ ((n:ℝ)+1) * d z - 1 := by
      rw [div_le_iff₀ (hn1 n)] at hge; nlinarith
    have : χ n z = 1 := by
      rw [hχ]; simp only
      rw [min_eq_right haff, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    linarith
  have hdsmallχ : ∀ (n : ℕ) z, d z < 2 / ((n:ℝ)+1) → χ n z < 1 := by
    intro n z hz
    have haff : ((n:ℝ)+1) * d z - 1 < 1 := by
      rw [lt_div_iff₀ (hn1 n)] at hz; nlinarith
    rw [hχ]; simp only
    rw [min_eq_left (le_of_lt haff)]
    exact max_lt (by norm_num) haff
  have hφsmall : ∀ (n : ℕ) z, d z < 2 / ((n:ℝ)+1) → |φ z| ≤ 2 * (K:ℝ) / ((n:ℝ)+1) := by
    intro n z hz
    calc |φ z| ≤ (K:ℝ) * d z := hφabs z
      _ ≤ (K:ℝ) * (2 / ((n:ℝ)+1)) := mul_le_mul_of_nonneg_left (le_of_lt hz) hKnn
      _ = 2 * K / ((n:ℝ)+1) := by ring
  -- **`g n` is `LipschitzWith (3·K)`** (globally).
  have hglip : ∀ n : ℕ, LipschitzWith (3 * K) (g n) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have key : ∀ p q : ℂ, d p ≤ d q →
        |χ n p * φ p - χ n q * φ q| ≤ (3 * (K:ℝ)) * dist p q := by
      intro p q hpq
      have hdecomp : χ n p * φ p - χ n q * φ q
          = χ n q * (φ p - φ q) + φ p * (χ n p - χ n q) := by ring
      rw [hdecomp]
      have ht1 : |χ n q * (φ p - φ q)| ≤ (K:ℝ) * dist p q := by
        rw [abs_mul]
        have h1 : |χ n q| ≤ 1 := by rw [abs_of_nonneg (hχ01 n q).1]; exact (hχ01 n q).2
        have h2 : |φ p - φ q| ≤ (K:ℝ) * dist p q := by
          have := hφlip.dist_le_mul p q; rwa [Real.dist_eq] at this
        calc |χ n q| * |φ p - φ q| ≤ 1 * ((K:ℝ) * dist p q) :=
              mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
          _ = (K:ℝ) * dist p q := one_mul _
      have ht2 : |φ p * (χ n p - χ n q)| ≤ (2 * (K:ℝ)) * dist p q := by
        rcases eq_or_ne (χ n p) (χ n q) with heq | hne
        · rw [heq, sub_self, mul_zero, abs_zero]; positivity
        · have hχplt : χ n p < 1 := by
            rcases lt_or_eq_of_le (hχ01 n p).2 with h | h
            · exact h
            · exfalso; apply hne
              have hdp2 : 2 / ((n:ℝ)+1) ≤ d p := by
                by_contra hlt; push Not at hlt
                exact absurd (hdsmallχ n p hlt) (by rw [h]; exact lt_irrefl _)
              have hdq2 : 2 / ((n:ℝ)+1) ≤ d q := le_trans hdp2 hpq
              have haffq : (1:ℝ) ≤ ((n:ℝ)+1) * d q - 1 := by
                rw [div_le_iff₀ (hn1 n)] at hdq2; nlinarith
              have hχq1 : χ n q = 1 := by
                rw [hχ]; simp only
                rw [min_eq_right haffq, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
              rw [h, hχq1]
          have hφp : |φ p| ≤ 2 * (K:ℝ) / ((n:ℝ)+1) := hφsmall n p (hχdsmall n p hχplt)
          rw [abs_mul]
          have hχdiff : |χ n p - χ n q| ≤ ((n:ℝ)+1) * dist p q := by
            have := (hχlip n).dist_le_mul p q
            rw [Real.dist_eq] at this
            calc |χ n p - χ n q| ≤ ((n:ℝ≥0)+1 : ℝ) * dist p q := this
              _ = ((n:ℝ)+1) * dist p q := by push_cast; ring
          calc |φ p| * |χ n p - χ n q|
              ≤ (2 * (K:ℝ) / ((n:ℝ)+1)) * (((n:ℝ)+1) * dist p q) :=
                mul_le_mul hφp hχdiff (abs_nonneg _) (by positivity)
            _ = (2 * (K:ℝ)) * dist p q := by field_simp
      calc |χ n q * (φ p - φ q) + φ p * (χ n p - χ n q)|
          ≤ |χ n q * (φ p - φ q)| + |φ p * (χ n p - χ n q)| := abs_add_le _ _
        _ ≤ (K:ℝ) * dist p q + (2 * (K:ℝ)) * dist p q := add_le_add ht1 ht2
        _ = (3 * (K:ℝ)) * dist p q := by ring
    have hcast : ((3 * K : ℝ≥0) : ℝ) = 3 * (K:ℝ) := by push_cast; ring
    rw [hcast]
    rcases le_total (d x) (d y) with h | h
    · exact key x y h
    · have hk := key y x h; rw [dist_comm] at hk; rw [abs_sub_comm]; exact hk
  -- **`g n` has compact support inside `U`.**
  set Kn : ℕ → Set ℂ := fun n => {z : ℂ | 1/((n:ℝ)+1) ≤ d z} with hKn
  have hKncl : ∀ n, IsClosed (Kn n) := fun n => isClosed_le continuous_const hdcont
  have hKnU : ∀ n, Kn n ⊆ U := by
    intro n z hz
    have hpos : 0 < d z := lt_of_lt_of_le (by positivity) hz
    exact (hdU z).mpr hpos
  have hKncpt : ∀ n, IsCompact (Kn n) := fun n =>
    Metric.isCompact_of_isClosed_isBounded (hKncl n) (hUbdd.subset (hKnU n))
  have hgsupp : ∀ n, Function.support (g n) ⊆ Kn n := by
    intro n z hz
    simp only [hg, Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
    obtain ⟨hχ0, _⟩ := hz
    simp only [hKn, Set.mem_setOf_eq]
    by_contra hlt
    push Not at hlt
    apply hχ0
    have haff : ((n:ℝ)+1) * d z - 1 < 0 := by
      rw [lt_div_iff₀ (hn1 n)] at hlt; nlinarith
    rw [hχ]; simp only
    rw [min_eq_left (by linarith : ((n:ℝ)+1)*d z - 1 ≤ 1), max_eq_left (le_of_lt haff)]
  have hgcs : ∀ n, HasCompactSupport (g n) := fun n =>
    HasCompactSupport.of_support_subset_isCompact (hKncpt n) (hgsupp n)
  have hgtsupp : ∀ n, tsupport (g n) ⊆ U := fun n =>
    (closure_minimal (hgsupp n) (hKncl n)).trans (hKnU n)
  -- **Step 1: the compact-support Lipschitz principle for each `wn n`.**
  have hstep1 : ∀ n, dirichletEnergy u U ≤ dirichletEnergy (wn n) U := by
    intro n
    have hlip : LipschitzWith (3 * K) (fun z => wn n z - u z) := by
      have : (fun z => wn n z - u z) = g n := by funext z; simp only [hwn]; ring
      rw [this]; exact hglip n
    have hcs : HasCompactSupport (fun z => wn n z - u z) := by
      have : (fun z => wn n z - u z) = g n := by funext z; simp only [hwn]; ring
      rw [this]; exact hgcs n
    have hsub : tsupport (fun z => wn n z - u z) ⊆ U := by
      have : (fun z => wn n z - u z) = g n := by funext z; simp only [hwn]; ring
      rw [this]; exact hgtsupp n
    exact dirichletEnergy_le_of_compactSupport_lipschitz hUopen hu hlip hcs hsub
  -- **Step 2: energy convergence `dirichletEnergy (wn n) U → dirichletEnergy w U`.**
  -- We use dominated convergence; if the target energy is infinite the bound is trivial.
  rcases eq_or_lt_of_le (le_top (a := dirichletEnergy w U)) with hinf | hfin
  · rw [hinf]; exact le_top
  · -- The DCT integrands over the indicator of `U`.
    set F : ℕ → ℂ → ℝ≥0∞ := fun n => U.indicator (fun z => (‖fderiv ℝ (wn n) z‖₊ : ℝ≥0∞) ^ 2)
      with hF
    set f : ℂ → ℝ≥0∞ := U.indicator (fun z => (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2) with hf
    -- `∫⁻ F n = dirichletEnergy (wn n) U`, `∫⁻ f = dirichletEnergy w U`.
    have hFint : ∀ n, ∫⁻ z, F n z = dirichletEnergy (wn n) U := by
      intro n; rw [hF]; rw [lintegral_indicator hUopen.measurableSet]; rfl
    have hfint : ∫⁻ z, f z = dirichletEnergy w U := by
      rw [hf, lintegral_indicator hUopen.measurableSet]; rfl
    -- Measurability of the integrands.
    have hFmeas : ∀ n, Measurable (F n) := by
      intro n
      refine Measurable.indicator ?_ hUopen.measurableSet
      exact (((measurable_fderiv ℝ (wn n)).nnnorm).pow_const 2).coe_nnreal_ennreal
    -- **The a.e. gradient-difference bound `‖∇(g n) − ∇φ‖ ≤ 3K`.**
    have hχ_aediff : ∀ n, ∀ᵐ z : ℂ, DifferentiableAt ℝ (χ n) z :=
      fun n => (hχlip n).ae_differentiableAt
    have hχfd_le : ∀ n z, ‖fderiv ℝ (χ n) z‖ ≤ ((n:ℝ)+1) := by
      intro n z
      have := norm_fderiv_le_of_lipschitz ℝ (hχlip n) (x₀ := z)
      calc ‖fderiv ℝ (χ n) z‖ ≤ ((n:ℝ≥0)+1 : ℝ) := this
        _ = ((n:ℝ)+1) := by push_cast; ring
    have hgraddiff : ∀ n, ∀ᵐ z : ℂ,
        ‖fderiv ℝ (g n) z - fderiv ℝ φ z‖ ≤ 3 * (K:ℝ) := by
      intro n
      filter_upwards [hφ_aediff, hχ_aediff n] with z hφd hχd
      -- Product rule at `z`.
      have hgeq : g n = (χ n) * φ := by funext y; simp only [hg, Pi.mul_apply]
      have hgfd : fderiv ℝ (g n) z = χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z := by
        rw [hgeq, fderiv_mul (𝕜 := ℝ) (c := χ n) (d := φ) hχd hφd]
      rw [hgfd]
      have hrw : χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z - fderiv ℝ φ z
          = (χ n z - 1) • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z := by
        module
      rw [hrw]
      have htri : ‖(χ n z - 1) • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z‖
          ≤ |χ n z - 1| * ‖fderiv ℝ φ z‖ + |φ z| * ‖fderiv ℝ (χ n) z‖ := by
        calc ‖(χ n z - 1) • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z‖
            ≤ ‖(χ n z - 1) • fderiv ℝ φ z‖ + ‖φ z • fderiv ℝ (χ n) z‖ := norm_add_le _ _
          _ = |χ n z - 1| * ‖fderiv ℝ φ z‖ + |φ z| * ‖fderiv ℝ (χ n) z‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine htri.trans ?_
      have hterm1 : |χ n z - 1| * ‖fderiv ℝ φ z‖ ≤ (K:ℝ) := by
        have h1 : |χ n z - 1| ≤ 1 := by
          rw [abs_le]; exact ⟨by linarith [(hχ01 n z).1], by linarith [(hχ01 n z).2]⟩
        calc |χ n z - 1| * ‖fderiv ℝ φ z‖ ≤ 1 * (K:ℝ) :=
              mul_le_mul h1 (hφfd_le z) (norm_nonneg _) (by norm_num)
          _ = (K:ℝ) := one_mul _
      have hterm2 : |φ z| * ‖fderiv ℝ (χ n) z‖ ≤ 2 * (K:ℝ) := by
        rcases le_or_gt (((n:ℝ)+1) * d z - 1) 1 with hcase | hcase
        · have hdle : ((n:ℝ)+1) * d z ≤ 2 := by linarith
          calc |φ z| * ‖fderiv ℝ (χ n) z‖ ≤ ((K:ℝ) * d z) * ((n:ℝ)+1) :=
                mul_le_mul (hφabs z) (hχfd_le n z) (norm_nonneg _)
                  (mul_nonneg hKnn (hdnn z))
            _ = (K:ℝ) * (((n:ℝ)+1) * d z) := by ring
            _ ≤ (K:ℝ) * 2 := mul_le_mul_of_nonneg_left hdle hKnn
            _ = 2 * (K:ℝ) := by ring
        · have heq : χ n =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
            have hcont : Continuous (fun w : ℂ => ((n:ℝ)+1) * d w - 1) :=
              (continuous_const.mul hdcont).sub continuous_const
            have hopen : IsOpen {w : ℂ | 1 < ((n:ℝ)+1) * d w - 1} :=
              isOpen_lt continuous_const hcont
            filter_upwards [hopen.mem_nhds (show z ∈ _ from hcase)] with w hw
            have hw' : 1 < ((n:ℝ)+1) * d w - 1 := hw
            rw [hχ]; simp only
            rw [min_eq_right (le_of_lt hw'), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
          have hfd0 : fderiv ℝ (χ n) z = 0 := by rw [heq.fderiv_eq]; simp
          rw [hfd0, norm_zero, mul_zero]; positivity
      linarith
    -- `∇w = ∇u + ∇φ` a.e. on `U`; `∇(wn n) = ∇u + ∇(g n)` a.e. on `U`.
    have hfd_w : ∀ᵐ z : ℂ, z ∈ U → fderiv ℝ w z = fderiv ℝ u z + fderiv ℝ φ z := by
      filter_upwards [hφ_aediff] with z hzd hzU
      have hwd : HasFDerivAt w (fderiv ℝ u z + fderiv ℝ φ z) z := by
        refine (((hudiffU z hzU).hasFDerivAt).add hzd.hasFDerivAt).congr_of_eventuallyEq ?_
        filter_upwards with y; simp only [Pi.add_apply, hw_eq y]
      exact hwd.fderiv
    have hfd_wn : ∀ n, ∀ᵐ z : ℂ, z ∈ U →
        fderiv ℝ (wn n) z = fderiv ℝ u z + fderiv ℝ (g n) z := by
      intro n
      filter_upwards [(hφ_aediff), (hχ_aediff n)] with z hφd hχd hzU
      have hgd : DifferentiableAt ℝ (g n) z := hχd.mul hφd
      have hwd : HasFDerivAt (wn n) (fderiv ℝ u z + fderiv ℝ (g n) z) z := by
        refine (((hudiffU z hzU).hasFDerivAt).add hgd.hasFDerivAt).congr_of_eventuallyEq ?_
        filter_upwards with y; simp only [Pi.add_apply, hwn]
      exact hwd.fderiv
    -- **Domination `F n ≤ bound` a.e.** with `bound = 1_U · (2‖∇w‖² + 2(3K)²)`.
    set C : ℝ≥0 := (3 * K) with hC
    set bound : ℂ → ℝ≥0∞ :=
      U.indicator (fun z => 2 * (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 + 2 * ((C:ℝ≥0∞) ^ 2)) with hbound
    have hFbound : ∀ n, F n ≤ᵐ[volume] bound := by
      intro n
      filter_upwards [hgraddiff n, hfd_w, hfd_wn n] with z hgd hwd hwnd
      rcases Classical.em (z ∈ U) with hzU | hzU
      · simp only [hF, hbound, Set.indicator_of_mem hzU]
        -- `‖∇(wn n) z‖ ≤ ‖∇w z‖ + 3K`.
        have hdiff : fderiv ℝ (wn n) z - fderiv ℝ w z = fderiv ℝ (g n) z - fderiv ℝ φ z := by
          rw [hwnd hzU, hwd hzU]; abel
        have hnorm : ‖fderiv ℝ (wn n) z‖ ≤ ‖fderiv ℝ w z‖ + 3 * (K:ℝ) := by
          have hle : ‖fderiv ℝ (wn n) z‖ ≤ ‖fderiv ℝ w z‖ + ‖fderiv ℝ (wn n) z - fderiv ℝ w z‖ :=
            norm_le_norm_add_norm_sub' _ _
          rw [hdiff] at hle; linarith [hle, hgd]
        -- The NNReal bound `‖∇wₙ‖₊ ≤ ‖∇w‖₊ + C`, then AM-GM.
        have hnn : ‖fderiv ℝ (wn n) z‖₊ ≤ ‖fderiv ℝ w z‖₊ + C := by
          rw [← NNReal.coe_le_coe]; push_cast [hC]; exact hnorm
        have hsq : ‖fderiv ℝ (wn n) z‖₊ ^ 2
            ≤ 2 * ‖fderiv ℝ w z‖₊ ^ 2 + 2 * C ^ 2 := by
          calc ‖fderiv ℝ (wn n) z‖₊ ^ 2 ≤ (‖fderiv ℝ w z‖₊ + C) ^ 2 := by gcongr
            _ = (‖fderiv ℝ w z‖₊ ^ 2 + C ^ 2) + 2 * ‖fderiv ℝ w z‖₊ * C := by ring
            _ ≤ (‖fderiv ℝ w z‖₊ ^ 2 + C ^ 2) + (‖fderiv ℝ w z‖₊ ^ 2 + C ^ 2) :=
                add_le_add le_rfl (two_mul_le_add_sq (‖fderiv ℝ w z‖₊) C)
            _ = 2 * ‖fderiv ℝ w z‖₊ ^ 2 + 2 * C ^ 2 := by ring
        calc (‖fderiv ℝ (wn n) z‖₊ : ℝ≥0∞) ^ 2
            = ((‖fderiv ℝ (wn n) z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_pow]
          _ ≤ ((2 * ‖fderiv ℝ w z‖₊ ^ 2 + 2 * C ^ 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hsq
          _ = 2 * (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 + 2 * ((C:ℝ≥0∞) ^ 2) := by push_cast; ring
      · simp only [hF, hbound, Set.indicator_of_notMem hzU, le_refl]
    -- **The bound is integrable.**
    have hboundint : ∫⁻ z, bound z ≠ ∞ := by
      rw [hbound, lintegral_indicator hUopen.measurableSet]
      have hsplit : ∫⁻ z in U, (2 * (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 + 2 * ((C:ℝ≥0∞) ^ 2))
          = 2 * dirichletEnergy w U + 2 * ((C:ℝ≥0∞) ^ 2) * volume U := by
        rw [lintegral_add_right _ (by fun_prop), lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp), setLIntegral_const]
        rw [dirichletEnergy]; ring
      rw [hsplit]
      apply ENNReal.add_ne_top.mpr
      refine ⟨ENNReal.mul_ne_top (by simp) hfin.ne, ?_⟩
      refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) ?_
      exact hUbdd.measure_lt_top.ne
    -- **Pointwise convergence `F n z → f z`** (eventually equal for each `z`).
    have hconv_pt : ∀ᵐ z : ℂ, Tendsto (fun n => F n z) atTop (𝓝 (f z)) := by
      filter_upwards with z
      rcases Classical.em (z ∈ U) with hzU | hzU
      · -- eventually `wn n = w` near `z`, so `F n z = f z`.
        have hdz : 0 < d z := (hdU z).mp hzU
        have hev : ∀ᶠ n : ℕ in atTop, F n z = f z := by
          obtain ⟨N, hN⟩ := exists_nat_gt (2 / d z)
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have hdz2 : 2 / ((n:ℝ)+1) < d z := by
            have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            have hlt : 2 / d z < (n:ℝ)+1 := by linarith [hN, hNn]
            rw [div_lt_iff₀ hdz] at hlt; rw [div_lt_iff₀ (hn1 n)]; linarith
          have hfeq : wn n =ᶠ[𝓝 z] w := by
            have hcont : Continuous (fun x : ℂ => ((n:ℝ)+1) * d x - 1) :=
              (continuous_const.mul hdcont).sub continuous_const
            have hopen : IsOpen {x : ℂ | 1 < ((n:ℝ)+1) * d x - 1} :=
              isOpen_lt continuous_const hcont
            have hzmem : z ∈ {x : ℂ | 1 < ((n:ℝ)+1) * d x - 1} := by
              simp only [Set.mem_setOf_eq]; rw [div_lt_iff₀ (hn1 n)] at hdz2; nlinarith
            filter_upwards [hopen.mem_nhds hzmem] with x hx
            have hx' : 1 < ((n:ℝ)+1) * d x - 1 := hx
            simp only [hwn, hg, hχ]
            rw [min_eq_right (le_of_lt hx'), max_eq_right (by norm_num : (0:ℝ) ≤ 1), one_mul,
              ← hw_eq x]
          simp only [hF, hf, Set.indicator_of_mem hzU, hfeq.fderiv_eq]
        exact Tendsto.congr' (hev.mono (fun n h => h.symm)) tendsto_const_nhds
      · have : ∀ n, F n z = f z := by
          intro n; simp only [hF, hf, Set.indicator_of_notMem hzU]
        simp only [this]; exact tendsto_const_nhds
    -- **Dominated convergence** finishes energy convergence.
    have hconv : Tendsto (fun n => dirichletEnergy (wn n) U) atTop (𝓝 (dirichletEnergy w U)) := by
      have := tendsto_lintegral_of_dominated_convergence bound hFmeas hFbound hboundint hconv_pt
      rw [hfint] at this
      simpa only [hFint] using this
    -- **Step 3: pass to the limit.**
    exact ge_of_tendsto hconv (Filter.Eventually.of_forall hstep1)

/-- **A tapered product `χ·φ` is globally Lipschitz.** If `χ` is globally Lipschitz, `[0,1]`-valued,
and vanishes wherever `d < a`, and `φ` is Lipschitz and bounded on the closed set `{d ≥ b}` with
`0 < b < a`, then (since `χ` tapers to `0` on the margin `b ≤ d < a`) the product `χ·φ` is globally
Lipschitz. Here `d` is `1`-Lipschitz, which supplies the lower bound `dist ≥ a − b` on the margin
where the value of `χ·φ` can jump from `0` to its bound. -/
private theorem lipschitzWith_tapered_prod {χ φ dd : ℂ → ℝ} {Lχ Lφ : ℝ≥0} {B a b : ℝ}
    (hba : b < a) (hB : 0 ≤ B) (hχlip : LipschitzWith Lχ χ)
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) (hχ0 : ∀ z, dd z < a → χ z = 0)
    (hφT : LipschitzOnWith Lφ φ {z | b ≤ dd z}) (hφB : ∀ z, b ≤ dd z → |φ z| ≤ B)
    (hd1 : ∀ x y, |dd x - dd y| ≤ dist x y) :
    ∃ M : ℝ≥0, LipschitzWith M (fun z => χ z * φ z) := by
  set g : ℂ → ℝ := fun z => χ z * φ z with hg
  have hg0 : ∀ z, dd z < a → g z = 0 := fun z hz => by simp [hg, hχ0 z hz]
  set M1 : ℝ := (Lχ : ℝ) * B + (Lφ : ℝ) with hM1
  set M2 : ℝ := B / (a - b) with hM2
  have hab : 0 < a - b := by linarith
  have hM1nn : 0 ≤ M1 := by positivity
  have hM2nn : 0 ≤ M2 := by rw [hM2]; positivity
  refine ⟨Real.toNNReal (M1 + M2), ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq]
  have hMcast : ((Real.toNNReal (M1 + M2) : ℝ≥0) : ℝ) = M1 + M2 :=
    Real.coe_toNNReal _ (by positivity)
  rw [hMcast]
  have key : ∀ x y : ℂ, dd y ≤ dd x → |g x - g y| ≤ (M1 + M2) * dist x y := by
    intro x y hxy
    by_cases hxb : b ≤ dd x
    · by_cases hyb : b ≤ dd y
      · have hφdiff : |φ x - φ y| ≤ (Lφ : ℝ) * dist x y := by
          have := hφT.dist_le_mul x (show x ∈ {z | b ≤ dd z} from hxb) y
            (show y ∈ {z | b ≤ dd z} from hyb)
          rwa [Real.dist_eq] at this
        have hχdiff : |χ x - χ y| ≤ (Lχ : ℝ) * dist x y := by
          have := hχlip.dist_le_mul x y; rwa [Real.dist_eq] at this
        have hdecomp : g x - g y = χ x * (φ x - φ y) + φ y * (χ x - χ y) := by simp [hg]; ring
        rw [hdecomp]
        have hb1 : |χ x * (φ x - φ y)| ≤ 1 * ((Lφ : ℝ) * dist x y) := by
          rw [abs_mul]
          exact mul_le_mul (by rw [abs_of_nonneg (hχ01 x).1]; exact (hχ01 x).2) hφdiff
            (abs_nonneg _) (by norm_num)
        have hb2 : |φ y * (χ x - χ y)| ≤ B * ((Lχ : ℝ) * dist x y) := by
          rw [abs_mul]; exact mul_le_mul (hφB y hyb) hχdiff (abs_nonneg _) hB
        calc |χ x * (φ x - φ y) + φ y * (χ x - χ y)|
            ≤ |χ x * (φ x - φ y)| + |φ y * (χ x - χ y)| := abs_add_le _ _
          _ ≤ 1 * ((Lφ : ℝ) * dist x y) + B * ((Lχ : ℝ) * dist x y) := add_le_add hb1 hb2
          _ ≤ (M1 + M2) * dist x y := by
              rw [hM1]; nlinarith [dist_nonneg (x := x) (y := y), hM2nn]
      · push Not at hyb
        have hgy0 : g y = 0 := hg0 y (lt_trans hyb hba)
        rw [hgy0, sub_zero]
        by_cases hxa : dd x < a
        · rw [hg0 x hxa, abs_zero]; positivity
        · push Not at hxa
          have hdist : a - b ≤ dist x y := by
            calc a - b ≤ dd x - dd y := by linarith
              _ = |dd x - dd y| := (abs_of_nonneg (by linarith)).symm
              _ ≤ dist x y := hd1 x y
          have hgxb : |g x| ≤ B := by
            rw [hg, abs_mul]
            calc |χ x| * |φ x| ≤ 1 * B :=
                  mul_le_mul (by rw [abs_of_nonneg (hχ01 x).1]; exact (hχ01 x).2)
                    (hφB x hxb) (abs_nonneg _) (by norm_num)
              _ = B := one_mul _
          calc |g x| ≤ B := hgxb
            _ = M2 * (a - b) := by rw [hM2]; field_simp
            _ ≤ M2 * dist x y := mul_le_mul_of_nonneg_left hdist hM2nn
            _ ≤ (M1 + M2) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y), hM1nn]
    · push Not at hxb
      have hgx0 : g x = 0 := hg0 x (lt_trans hxb hba)
      have hgy0 : g y = 0 := hg0 y (lt_of_le_of_lt hxy (lt_trans hxb hba))
      rw [hgx0, hgy0, sub_zero, abs_zero]; positivity
  rcases le_total (dd q) (dd p) with h | h
  · exact key p q h
  · have hk := key q p h; rw [dist_comm] at hk; rw [abs_sub_comm]; exact hk

/-- **The Dirichlet principle for a boundary-vanishing *locally* Lipschitz competitor with a Hardy
bound.** If `u` is harmonic on a bounded open `U`, `φ := w − u` is continuous, vanishes outside `U`,
is Lipschitz on every compact subset of `U`, lies in `W¹²(U)` (`∫_U ‖∇φ‖² < ∞`), and satisfies the
Hardy bound `∫_U φ²/dist(·, Uᶜ)² < ∞`, then `dirichletEnergy u U ≤ dirichletEnergy w U`. The
harmonic `u` is *not* assumed Lipschitz — this is the form needed when `u` is singular at slit tips
so `w − u` is only locally Lipschitz. A boundary cutoff `φₙ := φ·χₙ` (Lipschitz by
`lipschitzWith_tapered_prod`, compact support in `U`) reduces to the compact-support Lipschitz
principle; the cutoff energies
converge by dominated convergence, the shell term `∫ φ²|∇χₙ|²` being bounded by `4∫_{shell} φ²/d²`,
a tail of the finite Hardy integral. -/
theorem dirichletEnergy_le_of_hardy_boundaryVanishing {u w : ℂ → ℝ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hφloc : ∀ K ⊆ U, IsCompact K → ∃ L : ℝ≥0, LipschitzOnWith L (fun z => w z - u z) K)
    (hφcont : Continuous (fun z => w z - u z)) (_hφ0 : ∀ z ∉ U, w z - u z = 0)
    (hφW12 : ∫⁻ z in U, (‖fderiv ℝ (fun z => w z - u z) z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤)
    (hHardy : ∫⁻ z in U, ENNReal.ofReal ((w z - u z) ^ 2 / (Metric.infDist z Uᶜ) ^ 2) ≠ ⊤) :
    dirichletEnergy u U ≤ dirichletEnergy w U := by
  classical
  set φ : ℂ → ℝ := fun z => w z - u z with hφ
  set d : ℂ → ℝ := fun z => Metric.infDist z Uᶜ with hd
  have hdcont : Continuous d := (lipschitz_infDist_pt _).continuous
  have hdnn : ∀ z, 0 ≤ d z := fun z => Metric.infDist_nonneg
  have hd1 : ∀ x y : ℂ, |d x - d y| ≤ dist x y := by
    intro x y; have := (lipschitz_infDist_pt (Uᶜ : Set ℂ)).dist_le_mul x y
    simpa [hd, Real.dist_eq] using this
  have hUccl : IsClosed (Uᶜ : Set ℂ) := hUopen.isClosed_compl
  have hUc : (Uᶜ : Set ℂ).Nonempty := by
    obtain ⟨r, hr⟩ := hUbdd.subset_ball (0 : ℂ)
    refine ⟨((|r| + 1 : ℝ) : ℂ), fun hmem => ?_⟩
    have hb : ((|r| + 1 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := hr hmem
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |r| + 1)] at hb
    linarith [le_abs_self r]
  have hdU : ∀ z, z ∈ U ↔ 0 < d z := by
    intro z; rw [hd, ← hUccl.notMem_iff_infDist_pos hUc]; simp
  have hφcont' : Continuous φ := hφcont
  have hn1 : ∀ n : ℕ, (0:ℝ) < (n:ℝ)+1 := fun n => by positivity
  -- **Compact exhaustion `Tc m = {d ≥ 1/(m+1)}`** (compact `⊆ U`) on which `φ` is Lipschitz.
  set Tc : ℕ → Set ℂ := fun m => {z : ℂ | 1/((m:ℝ)+1) ≤ d z} with hTc
  have hTccl : ∀ m, IsClosed (Tc m) := fun m => isClosed_le continuous_const hdcont
  have hTcU : ∀ m, Tc m ⊆ U := by
    intro m z hz; exact (hdU z).mpr (lt_of_lt_of_le (by positivity) hz)
  have hTccpt : ∀ m, IsCompact (Tc m) := fun m =>
    Metric.isCompact_of_isClosed_isBounded (hTccl m) (hUbdd.subset (hTcU m))
  have hφTlip : ∀ m, ∃ L : ℝ≥0, LipschitzOnWith L φ (Tc m) :=
    fun m => hφloc (Tc m) (hTcU m) (hTccpt m)
  have hφTbd : ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ Tc m, |φ z| ≤ B := by
    intro m
    rcases (Tc m).eq_empty_or_nonempty with he | hne
    · exact ⟨0, le_refl _, by simp [he]⟩
    · obtain ⟨x, hx, hxmax⟩ := (hTccpt m).exists_isMaxOn hne
        (continuous_abs.comp hφcont').continuousOn
      exact ⟨|φ x|, abs_nonneg _, fun z hz => hxmax hz⟩
  -- **a.e. differentiability of `φ` on `U`** (Rademacher on the open cover `{1/(m+1) < d}`).
  have hφ_aediffU : ∀ᵐ z : ℂ, z ∈ U → DifferentiableAt ℝ φ z := by
    have hcover : U = ⋃ m : ℕ, {z | 1/((m:ℝ)+1) < d z} := by
      ext z; simp only [Set.mem_iUnion, Set.mem_setOf_eq, hdU z]
      refine ⟨fun hz => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := exists_nat_gt (1 / d z)
        refine ⟨m, ?_⟩
        rw [div_lt_iff₀ (hn1 m)]; rw [div_lt_iff₀ hz] at hm
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      · rintro ⟨m, hm⟩; exact lt_of_lt_of_le (by positivity) (le_of_lt hm)
    have hVopen : ∀ m : ℕ, IsOpen {z | 1/((m:ℝ)+1) < d z} :=
      fun m => isOpen_lt continuous_const hdcont
    have hVsub : ∀ m : ℕ, {z | 1/((m:ℝ)+1) < d z} ⊆ Tc m := by
      intro m z hz; simp only [Set.mem_setOf_eq] at hz ⊢; exact le_of_lt hz
    have hstep : ∀ m : ℕ, ∀ᵐ z : ℂ, z ∈ {z | 1/((m:ℝ)+1) < d z} → DifferentiableAt ℝ φ z := by
      intro m
      obtain ⟨L, hL⟩ := hφTlip m
      have hLV : LipschitzOnWith L φ {z | 1/((m:ℝ)+1) < d z} := hL.mono (hVsub m)
      filter_upwards [hLV.ae_differentiableWithinAt_of_mem] with z hz hzV
      exact (hz hzV).differentiableAt ((hVopen m).mem_nhds hzV)
    rw [hcover]
    have hall : ∀ᵐ z : ℂ, ∀ m : ℕ, z ∈ {z | 1/((m:ℝ)+1) < d z} → DifferentiableAt ℝ φ z :=
      (ae_all_iff (ι := ℕ)).mpr hstep
    filter_upwards [hall] with z hz hzU
    simp only [Set.mem_iUnion] at hzU
    obtain ⟨m, hm⟩ := hzU; exact hz m hm
  have hw_eq : ∀ z, w z = u z + φ z := by intro z; simp only [hφ]; ring
  have hu2 : ContDiffOn ℝ 2 u U := hu.contDiffOn
  have hudiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
    fun z hz => (hu2.differentiableOn (by norm_num)).differentiableAt (hUopen.mem_nhds hz)
  -- **The cutoff family** as in the global-Lipschitz proof.
  set χ : ℕ → ℂ → ℝ := fun n z => max 0 (min (((n:ℝ)+1) * d z - 1) 1) with hχ
  set g : ℕ → ℂ → ℝ := fun n z => χ n z * φ z with hg
  set wn : ℕ → ℂ → ℝ := fun n z => u z + g n z with hwn
  have hχ01 : ∀ n z, 0 ≤ χ n z ∧ χ n z ≤ 1 := by
    intro n z
    refine ⟨le_max_left _ _, ?_⟩
    rw [hχ]; simp only
    rcases le_or_gt (min (((n:ℝ)+1) * d z - 1) 1) 0 with h | h
    · rw [max_eq_left h]; norm_num
    · rw [max_eq_right (le_of_lt h)]; exact min_le_right _ _
  have hχlip : ∀ n : ℕ, LipschitzWith ((n:ℝ≥0)+1) (χ n) := by
    intro n
    have haff : LipschitzWith ((n:ℝ≥0)+1) (fun z : ℂ => ((n:ℝ)+1) * d z - 1) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq]
      have heq : ((n:ℝ)+1) * d x - 1 - (((n:ℝ)+1) * d y - 1) = ((n:ℝ)+1) * (d x - d y) := by ring
      rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
      push_cast
      exact mul_le_mul_of_nonneg_left (hd1 x y) (by positivity)
    exact (haff.min_const 1).const_max 0
  -- `χ n = 0` where `d < 1/(n+1)`, `= 1` where `d > 2/(n+1)`, `∇χ n = 0` off the shell.
  have hχ0 : ∀ (n : ℕ) z, d z < 1/((n:ℝ)+1) → χ n z = 0 := by
    intro n z hz
    have haff : ((n:ℝ)+1) * d z - 1 < 0 := by rw [lt_div_iff₀ (hn1 n)] at hz; nlinarith
    rw [hχ]; simp only
    rw [min_eq_left (by linarith : ((n:ℝ)+1)*d z - 1 ≤ 1), max_eq_left (le_of_lt haff)]
  have hχfd_le : ∀ (n : ℕ) z, ‖fderiv ℝ (χ n) z‖ ≤ ((n:ℝ)+1) := by
    intro n z
    calc ‖fderiv ℝ (χ n) z‖ ≤ ((n:ℝ≥0)+1 : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hχlip n) (x₀ := z)
      _ = ((n:ℝ)+1) := by push_cast; ring
  have hχfd0_lo : ∀ (n : ℕ) z, d z < 1/((n:ℝ)+1) → fderiv ℝ (χ n) z = 0 := by
    intro n z hz
    have heq : χ n =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
      have hcont : Continuous (fun w : ℂ => ((n:ℝ)+1) * d w - 1) :=
        (continuous_const.mul hdcont).sub continuous_const
      have hopen : IsOpen {w : ℂ | ((n:ℝ)+1) * d w - 1 < 0} := isOpen_lt hcont continuous_const
      have hzmem : z ∈ {w : ℂ | ((n:ℝ)+1) * d w - 1 < 0} := by
        simp only [Set.mem_setOf_eq]; rw [lt_div_iff₀ (hn1 n)] at hz; nlinarith
      filter_upwards [hopen.mem_nhds hzmem] with w hw
      have hw' : ((n:ℝ)+1) * d w - 1 < 0 := hw
      rw [hχ]; simp only
      rw [min_eq_left (by linarith : ((n:ℝ)+1)*d w - 1 ≤ 1), max_eq_left (le_of_lt hw')]
    rw [heq.fderiv_eq]; simp
  have hχfd0_hi : ∀ (n : ℕ) z, 2/((n:ℝ)+1) < d z → fderiv ℝ (χ n) z = 0 := by
    intro n z hz
    have heq : χ n =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
      have hcont : Continuous (fun w : ℂ => ((n:ℝ)+1) * d w - 1) :=
        (continuous_const.mul hdcont).sub continuous_const
      have hopen : IsOpen {w : ℂ | 1 < ((n:ℝ)+1) * d w - 1} := isOpen_lt continuous_const hcont
      have hzmem : z ∈ {w : ℂ | 1 < ((n:ℝ)+1) * d w - 1} := by
        simp only [Set.mem_setOf_eq]; rw [div_lt_iff₀ (hn1 n)] at hz; nlinarith
      filter_upwards [hopen.mem_nhds hzmem] with w hw
      have hw' : 1 < ((n:ℝ)+1) * d w - 1 := hw
      rw [hχ]; simp only
      rw [min_eq_right (le_of_lt hw'), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    rw [heq.fderiv_eq]; simp
  -- **Each `g n` has compact support inside `U` and is globally Lipschitz.**
  set Kn : ℕ → Set ℂ := fun n => {z : ℂ | 1/((n:ℝ)+1) ≤ d z} with hKn
  have hKncl : ∀ n, IsClosed (Kn n) := fun n => isClosed_le continuous_const hdcont
  have hKnU : ∀ n, Kn n ⊆ U := fun n z hz => (hdU z).mpr (lt_of_lt_of_le (by positivity) hz)
  have hKncpt : ∀ n, IsCompact (Kn n) := fun n =>
    Metric.isCompact_of_isClosed_isBounded (hKncl n) (hUbdd.subset (hKnU n))
  have hgsupp : ∀ n, Function.support (g n) ⊆ Kn n := by
    intro n z hz
    simp only [hg, Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
    obtain ⟨hχ0z, _⟩ := hz
    by_contra hlt
    simp only [hKn, Set.mem_setOf_eq, not_le] at hlt
    exact hχ0z (hχ0 n z hlt)
  have hgcs : ∀ n, HasCompactSupport (g n) := fun n =>
    HasCompactSupport.of_support_subset_isCompact (hKncpt n) (hgsupp n)
  have hgtsupp : ∀ n, tsupport (g n) ⊆ U := fun n =>
    (closure_minimal (hgsupp n) (hKncl n)).trans (hKnU n)
  have hglip : ∀ n, ∃ M : ℝ≥0, LipschitzWith M (g n) := by
    intro n
    -- `φ` is Lipschitz on `Tc (2n+1) = {d ≥ 1/(2n+2)}`, `χ n` vanishes for `d < 1/(n+1)`.
    obtain ⟨L, hL⟩ := hφTlip (2 * n + 1)
    obtain ⟨B, hBnn, hB⟩ := hφTbd (2 * n + 1)
    have hab : 1/(2*(n:ℝ)+2) < 1/((n:ℝ)+1) := by
      rw [div_lt_div_iff₀ (by positivity) (hn1 n)]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hTeq : {z | 1/(2*(n:ℝ)+2) ≤ d z} = Tc (2 * n + 1) := by
      rw [hTc, hKn]; ext z; simp only [Set.mem_setOf_eq]
      rw [show ((2 * n + 1 : ℕ):ℝ) + 1 = 2 * (n:ℝ) + 2 by push_cast; ring]
    refine lipschitzWith_tapered_prod (dd := d) (Lφ := L) (a := 1/((n:ℝ)+1))
      (b := 1/(2*(n:ℝ)+2)) hab hBnn (hχlip n) (hχ01 n) (fun z hz => hχ0 n z hz) ?_ ?_ hd1
    · rw [hTeq]; exact hL
    · intro z hz; exact hB z (by rw [← hTeq]; exact hz)
  -- **Step 1: the compact-support Lipschitz principle for each `wn n`.**
  have hstep1 : ∀ n, dirichletEnergy u U ≤ dirichletEnergy (wn n) U := by
    intro n
    obtain ⟨M, hM⟩ := hglip n
    have heq : (fun z => wn n z - u z) = g n := by funext z; simp only [hwn]; ring
    exact dirichletEnergy_le_of_compactSupport_lipschitz hUopen hu (by rw [heq]; exact hM)
      (by rw [heq]; exact hgcs n) (by rw [heq]; exact hgtsupp n)
  -- **Step 2: energy convergence `dirichletEnergy (wn n) U → dirichletEnergy w U`.**
  rcases eq_or_lt_of_le (le_top (a := dirichletEnergy w U)) with hinf | hfin
  · rw [hinf]; exact le_top
  · set F : ℕ → ℂ → ℝ≥0∞ := fun n => U.indicator (fun z => (‖fderiv ℝ (wn n) z‖₊ : ℝ≥0∞) ^ 2)
      with hF
    set f : ℂ → ℝ≥0∞ := U.indicator (fun z => (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2) with hf
    have hFint : ∀ n, ∫⁻ z, F n z = dirichletEnergy (wn n) U := by
      intro n; rw [hF, lintegral_indicator hUopen.measurableSet]; rfl
    have hfint : ∫⁻ z, f z = dirichletEnergy w U := by
      rw [hf, lintegral_indicator hUopen.measurableSet]; rfl
    have hFmeas : ∀ n, Measurable (F n) := by
      intro n
      exact (((measurable_fderiv ℝ (wn n)).nnnorm).pow_const 2).coe_nnreal_ennreal.indicator
        hUopen.measurableSet
    -- `∇w = ∇u + ∇φ`, `∇(wn n) = ∇u + ∇(g n)` a.e. on `U`.
    have hfd_w : ∀ᵐ z : ℂ, z ∈ U → fderiv ℝ w z = fderiv ℝ u z + fderiv ℝ φ z := by
      filter_upwards [hφ_aediffU] with z hzd hzU
      have hwd : HasFDerivAt w (fderiv ℝ u z + fderiv ℝ φ z) z := by
        refine (((hudiffU z hzU).hasFDerivAt).add (hzd hzU).hasFDerivAt).congr_of_eventuallyEq ?_
        filter_upwards with y; simp only [Pi.add_apply, hw_eq y]
      exact hwd.fderiv
    have hχ_aediff : ∀ n, ∀ᵐ z : ℂ, DifferentiableAt ℝ (χ n) z :=
      fun n => (hχlip n).ae_differentiableAt
    have hfd_wn : ∀ n, ∀ᵐ z : ℂ, z ∈ U →
        fderiv ℝ (wn n) z = fderiv ℝ u z + fderiv ℝ (g n) z := by
      intro n
      filter_upwards [hφ_aediffU, hχ_aediff n] with z hφd hχd hzU
      have hgd : DifferentiableAt ℝ (g n) z := hχd.mul (hφd hzU)
      have hwd : HasFDerivAt (wn n) (fderiv ℝ u z + fderiv ℝ (g n) z) z := by
        refine (((hudiffU z hzU).hasFDerivAt).add hgd.hasFDerivAt).congr_of_eventuallyEq ?_
        filter_upwards with y; simp only [Pi.add_apply, hwn]
      exact hwd.fderiv
    -- **Domination `‖∇(g n) z‖ ≤ ‖∇φ z‖ + 2|φ z|/d z` a.e. on `U`** (product rule + shell bound).
    have hgfd_bound : ∀ n, ∀ᵐ z : ℂ, z ∈ U →
        ‖fderiv ℝ (g n) z‖ ≤ ‖fderiv ℝ φ z‖ + 2 * |φ z| / d z := by
      intro n
      filter_upwards [hφ_aediffU, hχ_aediff n] with z hφd hχd hzU
      have hdz : 0 < d z := (hdU z).mp hzU
      have hgeq : g n = (χ n) * φ := by funext y; simp only [hg, Pi.mul_apply]
      have hgfd : fderiv ℝ (g n) z = χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z := by
        rw [hgeq, fderiv_mul (𝕜 := ℝ) (c := χ n) (d := φ) hχd (hφd hzU)]
      rw [hgfd]
      have hshellbd : |φ z| * ‖fderiv ℝ (χ n) z‖ ≤ 2 * |φ z| / d z := by
        by_cases hnab : fderiv ℝ (χ n) z = 0
        · rw [hnab, norm_zero, mul_zero]; positivity
        · have hd2 : d z ≤ 2/((n:ℝ)+1) := by
            by_contra hge; push Not at hge; exact hnab (hχfd0_hi n z hge)
          have hle : ((n:ℝ)+1) ≤ 2/d z := by
            rw [le_div_iff₀ hdz]; rw [le_div_iff₀ (hn1 n)] at hd2; nlinarith
          calc |φ z| * ‖fderiv ℝ (χ n) z‖ ≤ |φ z| * ((n:ℝ)+1) :=
                mul_le_mul_of_nonneg_left (hχfd_le n z) (abs_nonneg _)
            _ ≤ |φ z| * (2/d z) := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
            _ = 2 * |φ z| / d z := by ring
      calc ‖χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z‖
          ≤ ‖χ n z • fderiv ℝ φ z‖ + ‖φ z • fderiv ℝ (χ n) z‖ := norm_add_le _ _
        _ = |χ n z| * ‖fderiv ℝ φ z‖ + |φ z| * ‖fderiv ℝ (χ n) z‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ‖fderiv ℝ φ z‖ + 2 * |φ z| / d z := by
            gcongr
            · rw [abs_of_nonneg (hχ01 n z).1]; exact (hχ01 n z).2
        _ = ‖fderiv ℝ φ z‖ + 2 * |φ z| / d z := by ring
    -- **The domination `F n ≤ bound`** with `bound = 1_U·3(‖∇u‖²+‖∇φ‖²+4φ²/d²)`.
    set bound : ℂ → ℝ≥0∞ := U.indicator (fun z => 3 * ((‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
      + (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (4 * φ z ^ 2 / d z ^ 2))) with hbound
    have hFbound : ∀ n, F n ≤ᵐ[volume] bound := by
      intro n
      filter_upwards [hgfd_bound n, hfd_wn n] with z hgfd hwnd
      rcases Classical.em (z ∈ U) with hzU | hzU
      · simp only [hF, hbound, Set.indicator_of_mem hzU]
        have hdz : 0 < d z := (hdU z).mp hzU
        -- `‖∇(wn n) z‖ ≤ ‖∇u z‖ + ‖∇φ z‖ + 2|φ z|/d z`.
        have hnorm : ‖fderiv ℝ (wn n) z‖ ≤ ‖fderiv ℝ u z‖ + (‖fderiv ℝ φ z‖ + 2 * |φ z| / d z) := by
          rw [hwnd hzU]
          calc ‖fderiv ℝ u z + fderiv ℝ (g n) z‖ ≤ ‖fderiv ℝ u z‖ + ‖fderiv ℝ (g n) z‖ :=
                norm_add_le _ _
            _ ≤ ‖fderiv ℝ u z‖ + (‖fderiv ℝ φ z‖ + 2 * |φ z| / d z) := by gcongr; exact hgfd hzU
        -- Transfer to `ℝ≥0` and apply `(a+b+c)² ≤ 3(a²+b²+c²)`.
        set a1 : ℝ≥0 := ‖fderiv ℝ u z‖₊ with ha1
        set b1 : ℝ≥0 := ‖fderiv ℝ φ z‖₊ with hb1
        set c1 : ℝ≥0 := Real.toNNReal (2 * |φ z| / d z) with hc1
        have hnn : ‖fderiv ℝ (wn n) z‖₊ ≤ a1 + b1 + c1 := by
          rw [← NNReal.coe_le_coe]
          push_cast [ha1, hb1, hc1, Real.coe_toNNReal _ (show (0:ℝ) ≤ 2*|φ z|/d z by positivity)]
          linarith [hnorm]
        have hcsq : (‖fderiv ℝ (wn n) z‖₊) ^ 2 ≤ 3 * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) := by
          refine le_trans (pow_le_pow_left₀ (zero_le _) hnn 2) ?_
          rw [← NNReal.coe_le_coe]; push_cast
          nlinarith [sq_nonneg ((a1:ℝ)-b1), sq_nonneg ((b1:ℝ)-c1), sq_nonneg ((a1:ℝ)-c1)]
        have hc1sq : ((c1 : ℝ≥0∞) ^ 2) = ENNReal.ofReal (4 * φ z ^ 2 / d z ^ 2) := by
          rw [hc1, show ((2 * |φ z| / d z).toNNReal : ℝ≥0∞) = ENNReal.ofReal (2 * |φ z| / d z)
            from rfl, ← ENNReal.ofReal_pow (by positivity)]
          congr 1
          rw [div_pow, mul_pow, sq_abs]; ring
        calc (‖fderiv ℝ (wn n) z‖₊ : ℝ≥0∞) ^ 2
            = ((‖fderiv ℝ (wn n) z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_pow]
          _ ≤ ((3 * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hcsq
          _ = 3 * ((a1 : ℝ≥0∞) ^ 2 + (b1 : ℝ≥0∞) ^ 2 + (c1 : ℝ≥0∞) ^ 2) := by push_cast; ring
          _ = 3 * ((‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 + (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2
                + ENNReal.ofReal (4 * φ z ^ 2 / d z ^ 2)) := by rw [ha1, hb1, hc1sq]
      · simp only [hF, hbound, Set.indicator_of_notMem hzU, le_refl]
    -- **The bound is integrable** (`∫_U ‖∇u‖² < ∞`, `∫_U ‖∇φ‖² < ∞`, `∫_U 4φ²/d² < ∞`).
    have hu_int : ∫⁻ z in U, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := by
      have hle : ∫⁻ z in U, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
          ≤ ∫⁻ z in U, (2 * (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2) := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' hUopen.measurableSet]
        filter_upwards [hfd_w] with z hwd hzU
        have hnn : ‖fderiv ℝ u z‖₊ ≤ ‖fderiv ℝ w z‖₊ + ‖fderiv ℝ φ z‖₊ := by
          rw [← NNReal.coe_le_coe]; push_cast
          calc ‖fderiv ℝ u z‖ = ‖fderiv ℝ w z - fderiv ℝ φ z‖ := by rw [hwd hzU]; congr 1; abel
            _ ≤ ‖fderiv ℝ w z‖ + ‖fderiv ℝ φ z‖ := norm_sub_le _ _
        have hnn' : ‖fderiv ℝ u z‖ ≤ ‖fderiv ℝ w z‖ + ‖fderiv ℝ φ z‖ := by
          have := NNReal.coe_le_coe.mpr hnn; push_cast at this; exact this
        have hsq : ‖fderiv ℝ u z‖₊ ^ 2 ≤ 2 * ‖fderiv ℝ w z‖₊ ^ 2 + 2 * ‖fderiv ℝ φ z‖₊ ^ 2 := by
          rw [← NNReal.coe_le_coe]; push_cast
          nlinarith [sq_nonneg (‖fderiv ℝ w z‖ - ‖fderiv ℝ φ z‖), hnn',
            norm_nonneg (fderiv ℝ w z), norm_nonneg (fderiv ℝ φ z), norm_nonneg (fderiv ℝ u z)]
        calc (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
            = ((‖fderiv ℝ u z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_pow]
          _ ≤ ((2 * ‖fderiv ℝ w z‖₊ ^ 2 + 2 * ‖fderiv ℝ φ z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.coe_le_coe.mpr hsq
          _ = 2 * (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2 := by
              push_cast; ring
      refine ne_top_of_le_ne_top ?_ hle
      rw [lintegral_add_right _ (by fun_prop), lintegral_const_mul' _ _ (by simp),
        lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hfin.ne,
        ENNReal.mul_ne_top (by simp) hφW12⟩
    have hhardy4 : ∫⁻ z in U, ENNReal.ofReal (4 * φ z ^ 2 / d z ^ 2) ≠ ⊤ := by
      have heq : ∫⁻ z in U, ENNReal.ofReal (4 * φ z ^ 2 / d z ^ 2)
          = 4 * ∫⁻ z in U, ENNReal.ofReal (φ z ^ 2 / d z ^ 2) := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        refine lintegral_congr fun z => ?_
        rw [show 4 * φ z ^ 2 / d z ^ 2 = 4 * (φ z ^ 2 / d z ^ 2) by ring,
          ENNReal.ofReal_mul (by norm_num), show (4:ℝ≥0∞) = ENNReal.ofReal 4 by
            rw [ENNReal.ofReal_ofNat]]
      rw [heq]; exact ENNReal.mul_ne_top (by simp) hHardy
    have hmb : Measurable (fun z => (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2) :=
      ((measurable_fderiv ℝ φ).nnnorm.pow_const 2).coe_nnreal_ennreal
    have hmc : Measurable (fun z => ENNReal.ofReal (4 * φ z ^ 2 / d z ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        (((hφcont'.measurable.pow_const 2).const_mul 4).div (hdcont.measurable.pow_const 2))
    have hboundint : ∫⁻ z, bound z ≠ ∞ := by
      rw [hbound, lintegral_indicator hUopen.measurableSet, lintegral_const_mul' _ _ (by simp),
        lintegral_add_right _ hmc, lintegral_add_right _ hmb]
      exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
        ⟨hu_int, hφW12⟩, hhardy4⟩)
    -- **Pointwise convergence `F n z → f z`** (eventually equal for each `z`, as before).
    have hconv_pt : ∀ᵐ z : ℂ, Tendsto (fun n => F n z) atTop (𝓝 (f z)) := by
      filter_upwards with z
      rcases Classical.em (z ∈ U) with hzU | hzU
      · have hdz : 0 < d z := (hdU z).mp hzU
        have hev : ∀ᶠ n : ℕ in atTop, F n z = f z := by
          obtain ⟨N, hN⟩ := exists_nat_gt (2 / d z)
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have hdz2 : 2 / ((n:ℝ)+1) < d z := by
            have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            have hlt : 2 / d z < (n:ℝ)+1 := by linarith [hN, hNn]
            rw [div_lt_iff₀ hdz] at hlt; rw [div_lt_iff₀ (hn1 n)]; linarith
          have hfeq : wn n =ᶠ[𝓝 z] w := by
            have hcont : Continuous (fun x : ℂ => ((n:ℝ)+1) * d x - 1) :=
              (continuous_const.mul hdcont).sub continuous_const
            have hopen : IsOpen {x : ℂ | 1 < ((n:ℝ)+1) * d x - 1} :=
              isOpen_lt continuous_const hcont
            have hzmem : z ∈ {x : ℂ | 1 < ((n:ℝ)+1) * d x - 1} := by
              simp only [Set.mem_setOf_eq]; rw [div_lt_iff₀ (hn1 n)] at hdz2; nlinarith
            filter_upwards [hopen.mem_nhds hzmem] with x hx
            have hx' : 1 < ((n:ℝ)+1) * d x - 1 := hx
            simp only [hwn, hg, hχ]
            rw [min_eq_right (le_of_lt hx'), max_eq_right (by norm_num : (0:ℝ) ≤ 1), one_mul,
              ← hw_eq x]
          simp only [hF, hf, Set.indicator_of_mem hzU, hfeq.fderiv_eq]
        exact Tendsto.congr' (hev.mono (fun n h => h.symm)) tendsto_const_nhds
      · have : ∀ n, F n z = f z := fun n => by
          simp only [hF, hf, Set.indicator_of_notMem hzU]
        simp only [this]; exact tendsto_const_nhds
    have hconv : Tendsto (fun n => dirichletEnergy (wn n) U) atTop (𝓝 (dirichletEnergy w U)) := by
      have := tendsto_lintegral_of_dominated_convergence bound hFmeas hFbound hboundint hconv_pt
      rw [hfint] at this
      simpa only [hFint] using this
    exact ge_of_tendsto hconv (Filter.Eventually.of_forall hstep1)

/-- **A.e. congruence for the weak-derivative slot.** Since `HasWeakDirDeriv` only pairs `g`
against smooth compactly supported test functions through the integral `∫ φ • g`, replacing `g`
by an almost-everywhere-equal `g'` preserves the property. -/
private theorem HasWeakDirDeriv.congr_ae {f g g' : ℂ → ℂ} {v : ℂ} {Ω : Set ℂ}
    (h : HasWeakDirDeriv v g f Ω) (hgg' : g =ᵐ[volume] g') :
    HasWeakDirDeriv v g' f Ω := by
  intro φ hφ hcs htsupp
  rw [h φ hφ hcs htsupp]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hgg'] with z hz
  rw [hz]

/-- **Extension of a weak directional derivative from `U` to `ℂ`.** If both `f` and `g` are
compactly supported inside the open `U`, then a weak directional derivative on `U` is one on the
whole plane (test functions are cut down to `U` by a smooth bump that is `1` near the supports). -/
private theorem HasWeakDirDeriv_univ_of_U {v : ℂ} {g f : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hf_tsupp : tsupport f ⊆ U) (hg_tsupp : tsupport g ⊆ U)
    (hfcs : HasCompactSupport f) (hgcs : HasCompactSupport g)
    (_hfcont : Continuous f) (_hgloc : LocallyIntegrable g)
    (h : HasWeakDirDeriv v g f U) : HasWeakDirDeriv v g f Set.univ := by
  intro φ hφ hcs htsupp
  classical
  -- Compact set `K := tsupport f ∪ tsupport g ⊆ U`.
  set K : Set ℂ := tsupport f ∪ tsupport g with hK
  have hKc : IsCompact K := hfcs.union hgcs
  have hKcl : IsClosed K := hKc.isClosed
  have hKU : K ⊆ U := Set.union_subset hf_tsupp hg_tsupp
  -- Cutoff `η`: `η ≡ 1` on a neighbourhood of `K`, compact support inside `U`.
  obtain ⟨T, hTc, hKT, hTU⟩ := exists_compact_between hKc hUopen hKU
  have hTcl : IsClosed T := hTc.isClosed
  obtain ⟨η0, hη1, hη0, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) hKcl hKT
  set η : ℂ → ℝ := fun z => η0 z with hη
  have hη_cd : ContDiff ℝ (⊤ : ℕ∞) η := contMDiff_iff_contDiff.mp η0.contMDiff
  have hη0T : ∀ z ∉ T, η z = 0 := hη0
  have hη_supp : Function.support η ⊆ T := by
    intro z hz; by_contra hzT; exact hz (hη0T z hzT)
  have hη_cs : HasCompactSupport η := HasCompactSupport.of_support_subset_isCompact hTc hη_supp
  have hη_tsupp : tsupport η ⊆ U := (closure_minimal hη_supp hTcl).trans hTU
  -- `η ≡ 1` on an open neighbourhood `W ⊇ K`.
  have hη1nhds : ∀ᶠ z in 𝓝ˢ K, η z = 1 := hη1
  obtain ⟨W, hWopen, hKW, hη1W⟩ : ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ z ∈ W, η z = 1 := by
    rw [Filter.eventually_iff, mem_nhdsSet_iff_exists] at hη1nhds
    obtain ⟨W, hWopen, hKW, hW⟩ := hη1nhds
    exact ⟨W, hWopen, hKW, fun z hz => hW hz⟩
  -- The test function `Φ = η * φ` for `h` on `U`.
  set Φ : ℂ → ℝ := fun z => η z * φ z with hΦ
  have hΦsmooth : ContDiff ℝ (⊤ : ℕ∞) Φ := hη_cd.mul hφ
  have hΦcs : HasCompactSupport Φ := hcs.mul_left
  have hΦtsupp : tsupport Φ ⊆ U := subset_trans tsupport_mul_subset_left hη_tsupp
  have hfΦ := h Φ hΦsmooth hΦcs hΦtsupp
  -- Product rule for the directional derivative of `Φ`.
  have hpr : ∀ z, (fderiv ℝ Φ z) v = η z * ((fderiv ℝ φ z) v) + φ z * ((fderiv ℝ η z) v) := by
    intro z
    have hdη : DifferentiableAt ℝ η z := (hη_cd.differentiable (by norm_num)).differentiableAt
    have hdφ : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
    change (fderiv ℝ (fun y => η y * φ y) z) v = _
    rw [fderiv_fun_mul hdη hdφ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- RHS: `∫ Φ • g = ∫ φ • g` (where `g ≠ 0` we have `η = 1`; elsewhere `g = 0`).
  have hRHS : (∫ z, Φ z • g z) = ∫ z, φ z • g z := by
    apply integral_congr_ae
    filter_upwards with z
    change (η z * φ z) • g z = φ z • g z
    by_cases hz : z ∈ tsupport g
    · simp [hη1W z (hKW (Or.inr hz))]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  -- LHS: `∫ (∂ᵥΦ) • f = ∫ (∂ᵥφ) • f`; `fderiv η = 0` on `W ⊇ K` (η locally constant `= 1`).
  have hηfd0 : ∀ z ∈ W, (fderiv ℝ η z) v = 0 := by
    intro z hz
    have hloc : η =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
      filter_upwards [hWopen.mem_nhds hz] with y hy; exact hη1W y hy
    rw [hloc.fderiv_eq]; simp
  have hLHS : (∫ z, ((fderiv ℝ Φ z) v) • f z) = ∫ z, ((fderiv ℝ φ z) v) • f z := by
    apply integral_congr_ae
    filter_upwards with z
    rw [hpr z]
    by_cases hz : z ∈ tsupport f
    · have hzW : z ∈ W := hKW (Or.inl hz)
      simp [hη1W z hzW, hηfd0 z hzW]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hLHS, hRHS] at hfΦ
  exact hfΦ

/-- **The Dirichlet principle for a boundary-vanishing, a.e.-differentiable (ACL) competitor with a
Hardy bound.** If `u` is harmonic on a bounded open `U`, `φ := w − u` is continuous, vanishes
outside `U`, is differentiable a.e. on `U` with its classical `fderiv` serving as the weak
directional derivative of the complex embedding `(φ ·)` in the coordinate directions (ACL), lies in
`W¹²(U)`, and satisfies the Hardy bound `∫_U φ²/dist(·, Uᶜ)² < ∞`, then
`dirichletEnergy u U ≤ dirichletEnergy w U`. This drops the *local Lipschitz* hypothesis of
`dirichletEnergy_le_of_hardy_boundaryVanishing`: a **smooth** boundary cutoff `χₙ`
(`exists_smooth_boundaryCutoff`, built by mollifying the boundary distance) multiplies `φ`; the
product's weak directional derivative is `χₙ · ∇φ + (∇χₙ) · φ` by the smooth Leibniz rule
(`HasWeakDirDeriv.smul_smooth`), matching the classical `fderiv` of `χₙ · φ` almost everywhere. Each
`χₙ · φ` is a compact-support `W¹²` perturbation, so the compact-support weak-derivative principle
`dirichletEnergy_le_of_compactSupport_weakDeriv` gives `dirichletEnergy u U ≤
dirichletEnergy (u + χₙ·φ) U`; the cutoff energies converge by dominated convergence, the shell term
`∫ φ²‖∇χₙ‖²` bounded by a tail of the finite Hardy integral. -/
theorem dirichletEnergy_le_of_hardy_boundaryVanishing_aeDiff {u w : ℂ → ℝ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hφaediff : ∀ᵐ z : ℂ, z ∈ U → DifferentiableAt ℝ (fun z => w z - u z) z)
    (hφACL : ∀ v : ℂ, ‖v‖ = 1 →
      HasWeakDirDeriv v (fun z => ((fderiv ℝ (fun y => w y - u y) z v : ℝ) : ℂ))
        (fun z => ((w z - u z : ℝ) : ℂ)) Set.univ)
    (hφcont : Continuous (fun z => w z - u z)) (_hφ0 : ∀ z ∉ U, w z - u z = 0)
    (hφW12 : ∫⁻ z in U, (‖fderiv ℝ (fun z => w z - u z) z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤)
    (hHardy : ∫⁻ z in U, ENNReal.ofReal ((w z - u z) ^ 2 / (Metric.infDist z Uᶜ) ^ 2) ≠ ⊤) :
    dirichletEnergy u U ≤ dirichletEnergy w U := by
  classical
  set φ : ℂ → ℝ := fun z => w z - u z with hφ
  set d : ℂ → ℝ := fun z => Metric.infDist z Uᶜ with hd
  have hdcont : Continuous d := (lipschitz_infDist_pt _).continuous
  have hdnn : ∀ z, 0 ≤ d z := fun z => Metric.infDist_nonneg
  have hUccl : IsClosed (Uᶜ : Set ℂ) := hUopen.isClosed_compl
  have hUc : (Uᶜ : Set ℂ).Nonempty := by
    obtain ⟨r, hr⟩ := hUbdd.subset_ball (0 : ℂ)
    refine ⟨((|r| + 1 : ℝ) : ℂ), fun hmem => ?_⟩
    have hb : ((|r| + 1 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := hr hmem
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |r| + 1)] at hb
    linarith [le_abs_self r]
  have hdU : ∀ z, z ∈ U ↔ 0 < d z := by
    intro z; rw [hd, ← hUccl.notMem_iff_infDist_pos hUc]; simp
  have hφcont' : Continuous φ := hφcont
  have hφloc : LocallyIntegrable φ := hφcont'.locallyIntegrable
  have hφℂloc : LocallyIntegrable (fun z => (φ z : ℂ)) :=
    (Complex.continuous_ofReal.comp hφcont').locallyIntegrable
  have hn1 : ∀ n : ℕ, (0:ℝ) < (n:ℝ)+1 := fun n => by positivity
  -- `u` is `C²` on `U`, hence differentiable on `U`.
  have hu2 : ContDiffOn ℝ 2 u U := hu.contDiffOn
  have hudiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
    fun z hz => (hu2.differentiableOn (by norm_num)).differentiableAt (hUopen.mem_nhds hz)
  have hw_eq : ∀ z, w z = u z + φ z := by intro z; simp only [hφ]; ring
  -- **`∇φ` (complex embedding) is locally integrable on `U`** (from `∫_U ‖∇φ‖² < ∞`).
  have hφfd_meas : Measurable (fun z => fderiv ℝ φ z) := measurable_fderiv ℝ φ
  have hgradφ_L2U : ∀ K ⊆ U, IsCompact K →
      MemLp (fun z => ‖fderiv ℝ φ z‖) 2 (volume.restrict K) := by
    intro K hKU hKcpt
    rw [memLp_two_iff_integrable_sq hφfd_meas.norm.aestronglyMeasurable.restrict]
    have hle : ∫⁻ z in K, (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2
        ≤ ∫⁻ z in U, (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2 := lintegral_mono_set hKU
    have hfin : ∫⁻ z in K, (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := ne_top_of_le_ne_top hφW12 hle
    have hmeas : AEStronglyMeasurable (fun z => ‖fderiv ℝ φ z‖ ^ 2) (volume.restrict K) :=
      (hφfd_meas.norm.pow_const 2).aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.mpr hfin)
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal (by positivity),
      show ‖fderiv ℝ φ z‖ ^ 2 = ((‖fderiv ℝ φ z‖₊ : ℝ) ^ 2) by rw [coe_nnnorm],
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal]
  have hgradφℂ_locU : ∀ v : ℂ, ‖v‖ = 1 →
      LocallyIntegrableOn (fun z => ((fderiv ℝ φ z v : ℝ) : ℂ)) U := by
    intro v hv
    rw [locallyIntegrableOn_iff hUopen.isLocallyClosed]
    intro K hKU hKcpt
    have hL2v : MemLp (fun z => fderiv ℝ φ z v) 2 (volume.restrict K) := by
      refine (hgradφ_L2U K hKU hKcpt).mono'
        (measurable_fderiv_apply_const ℝ φ v).aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall fun z => ?_)
      calc ‖fderiv ℝ φ z v‖ ≤ ‖fderiv ℝ φ z‖ * ‖v‖ := (fderiv ℝ φ z).le_opNorm v
        _ = ‖fderiv ℝ φ z‖ := by rw [hv, mul_one]
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKcpt.measure_lt_top⟩
    have hintv : IntegrableOn (fun z => fderiv ℝ φ z v) K volume := hL2v.integrable (by norm_num)
    exact hintv.ofReal
  -- The Lipschitz bound on `Real.smoothTransition` used to build the cutoffs.
  obtain ⟨Dst, _hDlip, hDderiv⟩ := exists_lipschitz_smoothTransition
  -- **The smooth cutoff family** `χ n` from `exists_smooth_boundaryCutoff`.
  choose χ hχcd hχ01 hχ0 hχ1 hχfd_le hχfd_supp using
    fun n => exists_smooth_boundaryCutoff (U := U) Dst hDderiv n
  set g : ℕ → ℂ → ℝ := fun n z => χ n z * φ z with hg
  set wn : ℕ → ℂ → ℝ := fun n z => u z + g n z with hwn
  have hχfd0_lo : ∀ (n : ℕ) z, d z < 1/((n:ℝ)+1) → χ n z = 0 :=
    fun n z hz => hχ0 n z (le_of_lt hz)
  -- `χ n` differentiable everywhere (smooth).
  have hχdiff : ∀ n z, DifferentiableAt ℝ (χ n) z :=
    fun n z => (hχcd n).differentiable (by norm_num) |>.differentiableAt
  -- **Each `g n` has compact support inside `U`.**
  set Kn : ℕ → Set ℂ := fun n => {z : ℂ | 1/((n:ℝ)+1) ≤ d z} with hKn
  have hKncl : ∀ n, IsClosed (Kn n) := fun n => isClosed_le continuous_const hdcont
  have hKnU : ∀ n, Kn n ⊆ U := fun n z hz => (hdU z).mpr (lt_of_lt_of_le (by positivity) hz)
  have hKncpt : ∀ n, IsCompact (Kn n) := fun n =>
    Metric.isCompact_of_isClosed_isBounded (hKncl n) (hUbdd.subset (hKnU n))
  have hgsupp : ∀ n, Function.support (g n) ⊆ Kn n := by
    intro n z hz
    simp only [hg, Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
    obtain ⟨hχ0z, _⟩ := hz
    by_contra hlt
    simp only [hKn, Set.mem_setOf_eq, not_le] at hlt
    exact hχ0z (hχfd0_lo n z hlt)
  have hgcs : ∀ n, HasCompactSupport (g n) := fun n =>
    HasCompactSupport.of_support_subset_isCompact (hKncpt n) (hgsupp n)
  have hgtsupp : ∀ n, tsupport (g n) ⊆ U := fun n =>
    (closure_minimal (hgsupp n) (hKncl n)).trans (hKnU n)
  have hgcont : ∀ n, Continuous (g n) := fun n => (hχcd n).continuous.mul hφcont'
  -- **Step 1: the compact-support weak-derivative principle for each `wn n`.**
  have hstep1 : ∀ n, dirichletEnergy u U ≤ dirichletEnergy (wn n) U := by
    intro n
    have heqfun : (fun z => wn n z - u z) = g n := by funext z; simp only [hwn]; ring
    -- `g n = χ n · φ` is a.e. differentiable: off the closed `Kn n` it is locally `0`
    -- (`χ n = 0` where `d < 1/(n+1)`), and on `Kn n ⊆ U` we use `φ`'s a.e. differentiability.
    -- The pointwise product-rule identity for `∇(g n)`, valid a.e. (where `φ` is differentiable),
    -- and everywhere off the closed `Kn n` (there `g n = 0` and `χ n`, `∇χ n` vanish).
    have hgfd_ae : ∀ᵐ z : ℂ, fderiv ℝ (g n) z
        = χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z := by
      filter_upwards [hφaediff] with z hz
      by_cases hzK : (1:ℝ)/((n:ℝ)+1) ≤ d z
      · have hzU : z ∈ U := (hdU z).mpr (lt_of_lt_of_le (by positivity) hzK)
        have hgmul : g n = (χ n) * φ := by funext y; simp only [hg, Pi.mul_apply]
        rw [hgmul, fderiv_mul (𝕜 := ℝ) (c := χ n) (d := φ) (hχdiff n z) (hz hzU)]
      · push Not at hzK
        have hopen : IsOpen {y : ℂ | d y < 1/((n:ℝ)+1)} := isOpen_lt hdcont continuous_const
        have hmem : z ∈ {y : ℂ | d y < 1/((n:ℝ)+1)} := hzK
        have heqg : g n =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
          filter_upwards [hopen.mem_nhds hmem] with y hy
          simp only [hg, hχfd0_lo n y hy, zero_mul]
        have heqχ : χ n =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
          filter_upwards [hopen.mem_nhds hmem] with y hy
          exact hχfd0_lo n y hy
        rw [heqg.fderiv_eq, heqχ.fderiv_eq, heqχ.eq_of_nhds]; simp
    have hgn_aediff : ∀ᵐ z : ℂ, DifferentiableAt ℝ (g n) z := by
      filter_upwards [hφaediff] with z hz
      by_cases hzK : (1:ℝ)/((n:ℝ)+1) ≤ d z
      · have hzU : z ∈ U := (hdU z).mpr (lt_of_lt_of_le (by positivity) hzK)
        exact (hχdiff n z).mul (hz hzU)
      · push Not at hzK
        have hopen : IsOpen {y : ℂ | d y < 1/((n:ℝ)+1)} := isOpen_lt hdcont continuous_const
        have heq : g n =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
          filter_upwards [hopen.mem_nhds (show z ∈ _ from hzK)] with y hy
          simp only [hg, hχfd0_lo n y hy, zero_mul]
        exact (differentiableAt_const (0:ℝ)).congr_of_eventuallyEq heq
    -- `∇(g n)` (complex embedding) vanishes off the compact `Kn n`, hence is loc integrable.
    have hgnfd_supp : ∀ z, z ∉ Kn n → fderiv ℝ (g n) z = 0 := by
      intro z hz
      simp only [hKn, Set.mem_setOf_eq, not_le] at hz
      have hopen : IsOpen {y : ℂ | d y < 1/((n:ℝ)+1)} := isOpen_lt hdcont continuous_const
      have heq : g n =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
        filter_upwards [hopen.mem_nhds (show z ∈ _ from hz)] with y hy
        simp only [hg, hχfd0_lo n y hy, zero_mul]
      rw [heq.fderiv_eq]; simp
    -- ACL weak derivative of `g n = χ n · φ` from the smooth Leibniz rule on `U`, extended to
    -- `univ` via `HasWeakDirDeriv_univ_of_U` (both `g n` and its weak derivative have compact
    -- support inside `U`).
    have hgn_ACL : ∀ v : ℂ, ‖v‖ = 1 →
        HasWeakDirDeriv v (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ))
          (fun z => ((g n z : ℝ) : ℂ)) Set.univ := by
      intro v hv
      -- Smooth Leibniz on `U`: weak deriv of `χ n • φℂ` is `χ n • ∇φ + (∇χ n) • φℂ`.
      have hL := ((hφACL v hv).mono (Set.subset_univ U)).smul_smooth (ψ := χ n) (hχcd n)
        (hφℂloc.locallyIntegrableOn _) (hgradφℂ_locU v hv)
      have hfeq : (fun z => χ n z • ((φ z : ℝ) : ℂ)) = (fun z => ((g n z : ℝ) : ℂ)) := by
        funext z; simp only [hg, Complex.real_smul, Complex.ofReal_mul]
      have hgeq_ae : (fun z => χ n z • ((fderiv ℝ φ z v : ℝ) : ℂ)
          + ((fderiv ℝ (χ n) z) v) • ((φ z : ℝ) : ℂ))
          =ᵐ[volume] (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ)) := by
        filter_upwards [hgfd_ae] with z hzfd
        rw [hzfd]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          Complex.ofReal_add, Complex.ofReal_mul, Complex.real_smul, smul_eq_mul]
        ring
      rw [hfeq] at hL
      have hLU := hL.congr_ae hgeq_ae
      -- `∇(g n)v ℂ` has compact support in `U` and is locally integrable (globally).
      have hgnfdℂ_supp : Function.support (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ)) ⊆ Kn n := by
        intro z hz
        by_contra hzK
        simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hz
        exact hz (by rw [hgnfd_supp z hzK]; simp)
      have hgnfdℂ_cs : HasCompactSupport (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ)) :=
        HasCompactSupport.of_support_subset_isCompact (hKncpt n) hgnfdℂ_supp
      have hgnfdℂ_tsupp : tsupport (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ)) ⊆ U :=
        (closure_minimal hgnfdℂ_supp (hKncl n)).trans (hKnU n)
      have hgnℂ_tsupp : tsupport (fun z => ((g n z : ℝ) : ℂ)) ⊆ U := by
        refine (closure_minimal (fun z hz => ?_) (hKncl n)).trans (hKnU n)
        simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hz
        exact hgsupp n hz
      have hgnℂ_cs : HasCompactSupport (fun z => ((g n z : ℝ) : ℂ)) :=
        (hgcs n).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
      -- Local integrability of `∇(g n)v ℂ`: integrable on the compact `Kn n` (dominated by the
      -- `L¹` bound `‖∇φ‖ + |φ|·‖∇χ‖`), and supported there.
      have hgnfdℂ_loc : LocallyIntegrable (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ)) := by
        have hmeas : Measurable (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp (measurable_fderiv_apply_const ℝ (g n) v)
        -- `∇(g n)v` is `IntegrableOn (Kn n)`, dominated by `‖∇φ‖ + |φ|·4D(n+1)`.
        have hbnd : IntegrableOn (fun z => ‖fderiv ℝ φ z‖
            + |φ z| * (4 * (Dst:ℝ) * ((n:ℝ)+1))) (Kn n) volume := by
          have h1 : IntegrableOn (fun z => ‖fderiv ℝ φ z‖) (Kn n) volume := by
            haveI : IsFiniteMeasure (volume.restrict (Kn n)) :=
              ⟨by rw [Measure.restrict_apply_univ]; exact (hKncpt n).measure_lt_top⟩
            exact (hgradφ_L2U (Kn n) (hKnU n) (hKncpt n)).integrable (by norm_num)
          have h2 : IntegrableOn (fun z => |φ z| * (4 * (Dst:ℝ) * ((n:ℝ)+1))) (Kn n) volume :=
            (((hφcont'.abs).continuousOn).integrableOn_compact (hKncpt n)).mul_const _
          exact h1.add h2
        have hintOn : IntegrableOn (fun z => ((fderiv ℝ (g n) z v : ℝ) : ℂ)) (Kn n) volume := by
          rw [IntegrableOn, ← integrable_norm_iff (hmeas.aestronglyMeasurable.restrict)]
          refine hbnd.mono' ((hmeas.norm).aestronglyMeasurable.restrict) ?_
          rw [ae_restrict_iff' (hKncl n).measurableSet]
          filter_upwards [hgfd_ae] with z hzfd _
          rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
          -- `|∂ᵥφ| ≤ ‖∇φ‖`, `|∂ᵥχ| ≤ ‖∇χ‖ ≤ 4D(n+1)`, `0 ≤ χ ≤ 1`.
          have hφv : |fderiv ℝ φ z v| ≤ ‖fderiv ℝ φ z‖ := by
            rw [← Real.norm_eq_abs]
            exact le_trans ((fderiv ℝ φ z).le_opNorm v) (by rw [hv, mul_one])
          have hχv : |fderiv ℝ (χ n) z v| ≤ 4 * (Dst:ℝ) * ((n:ℝ)+1) := by
            rw [← Real.norm_eq_abs]
            exact le_trans ((fderiv ℝ (χ n) z).le_opNorm v) (by rw [hv, mul_one]) |>.trans
              (hχfd_le n z)
          rw [hzfd]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
          calc |χ n z * fderiv ℝ φ z v + φ z * fderiv ℝ (χ n) z v|
              ≤ |χ n z * fderiv ℝ φ z v| + |φ z * fderiv ℝ (χ n) z v| := abs_add_le _ _
            _ = |χ n z| * |fderiv ℝ φ z v| + |φ z| * |fderiv ℝ (χ n) z v| := by
                rw [abs_mul, abs_mul]
            _ ≤ 1 * ‖fderiv ℝ φ z‖ + |φ z| * (4 * (Dst:ℝ) * ((n:ℝ)+1)) := by
                gcongr
                · rw [abs_of_nonneg (hχ01 n z).1]; exact (hχ01 n z).2
            _ = ‖fderiv ℝ φ z‖ + |φ z| * (4 * (Dst:ℝ) * ((n:ℝ)+1)) := by rw [one_mul]
        exact ((integrableOn_iff_integrable_of_support_subset hgnfdℂ_supp).mp
          hintOn).locallyIntegrable
      exact HasWeakDirDeriv_univ_of_U hUopen hgnℂ_tsupp hgnfdℂ_tsupp hgnℂ_cs hgnfdℂ_cs
        (Complex.continuous_ofReal.comp (hgcont n)) hgnfdℂ_loc hLU
    -- `‖∇(g n)‖²` is integrable on `tsupport (g n) ⊆ Kn n`: dominated by
    -- `2‖∇φ‖² + 2(|φ|·4D(n+1))²`, both `L¹` on the compact `Kn n`.
    have hgn2 : IntegrableOn (fun z => ‖fderiv ℝ (g n) z‖ ^ 2) (tsupport (g n)) volume := by
      have hts : tsupport (g n) ⊆ Kn n := (closure_minimal (hgsupp n) (hKncl n))
      refine (IntegrableOn.mono_set ?_ hts)
      set B : ℝ := 4 * (Dst:ℝ) * ((n:ℝ)+1) with hB
      have hBnn : 0 ≤ B := by rw [hB]; positivity
      -- The dominating function on `Kn n`.
      have hdom : IntegrableOn (fun z => 2 * ‖fderiv ℝ φ z‖ ^ 2 + 2 * (|φ z| * B) ^ 2)
          (Kn n) volume := by
        have h1 : IntegrableOn (fun z => ‖fderiv ℝ φ z‖ ^ 2) (Kn n) volume := by
          haveI : IsFiniteMeasure (volume.restrict (Kn n)) :=
            ⟨by rw [Measure.restrict_apply_univ]; exact (hKncpt n).measure_lt_top⟩
          exact (memLp_two_iff_integrable_sq hφfd_meas.norm.aestronglyMeasurable.restrict).mp
            (hgradφ_L2U (Kn n) (hKnU n) (hKncpt n))
        have h2 : IntegrableOn (fun z => (|φ z| * B) ^ 2) (Kn n) volume :=
          ((((hφcont'.abs.mul continuous_const).pow 2)).continuousOn).integrableOn_compact
            (hKncpt n)
        exact (h1.const_mul 2).add (h2.const_mul 2)
      refine hdom.mono'
        (((measurable_fderiv ℝ (g n)).norm.pow_const 2).aestronglyMeasurable.restrict) ?_
      rw [ae_restrict_iff' (hKncl n).measurableSet]
      filter_upwards [hgfd_ae] with z hzfd _
      have hnn : (0:ℝ) ≤ ‖fderiv ℝ (g n) z‖ ^ 2 := by positivity
      rw [Real.norm_of_nonneg hnn, hzfd]
      -- `‖χ • ∇φ + φ • ∇χ‖ ≤ ‖∇φ‖ + |φ|·B`.
      have htri : ‖χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z‖ ≤ ‖fderiv ℝ φ z‖ + |φ z| * B := by
        calc ‖χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z‖
            ≤ ‖χ n z • fderiv ℝ φ z‖ + ‖φ z • fderiv ℝ (χ n) z‖ := norm_add_le _ _
          _ = |χ n z| * ‖fderiv ℝ φ z‖ + |φ z| * ‖fderiv ℝ (χ n) z‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 1 * ‖fderiv ℝ φ z‖ + |φ z| * B := by
              gcongr
              · rw [abs_of_nonneg (hχ01 n z).1]; exact (hχ01 n z).2
              · exact hχfd_le n z
          _ = ‖fderiv ℝ φ z‖ + |φ z| * B := by rw [one_mul]
      have hpos1 : (0:ℝ) ≤ ‖fderiv ℝ φ z‖ := norm_nonneg _
      have hpos2 : (0:ℝ) ≤ |φ z| * B := by positivity
      nlinarith [htri, norm_nonneg (χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z),
        sq_nonneg (‖fderiv ℝ φ z‖ - |φ z| * B)]
    have hfun_eq : (fun z => wn n z - u z) = g n := heqfun
    exact dirichletEnergy_le_of_compactSupport_weakDeriv hUopen hu (by rw [hfun_eq]; exact hgcont n)
      (by rw [hfun_eq]; exact hgcs n) (by rw [hfun_eq]; exact hgtsupp n)
      (by rw [hfun_eq]; exact hgn_aediff)
      (by simp only [show ∀ z, wn n z - u z = g n z from fun z => by rw [hwn]; ring]
          exact hgn_ACL)
      (by rw [hfun_eq]; exact hgn2)
  -- **Step 2: energy convergence `dirichletEnergy (wn n) U → dirichletEnergy w U`** by dominated
  -- convergence; the shell term `∫ φ²‖∇χₙ‖²` is a constant times a tail of the Hardy integral.
  set Bc : ℝ := 4 * (Dst:ℝ) with hBc
  have hBcnn : 0 ≤ Bc := by rw [hBc]; positivity
  rcases eq_or_lt_of_le (le_top (a := dirichletEnergy w U)) with hinf | hfin
  · rw [hinf]; exact le_top
  · set F : ℕ → ℂ → ℝ≥0∞ := fun n => U.indicator (fun z => (‖fderiv ℝ (wn n) z‖₊ : ℝ≥0∞) ^ 2)
      with hF
    set f : ℂ → ℝ≥0∞ := U.indicator (fun z => (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2) with hf
    have hFint : ∀ n, ∫⁻ z, F n z = dirichletEnergy (wn n) U := by
      intro n; rw [hF, lintegral_indicator hUopen.measurableSet]; rfl
    have hfint : ∫⁻ z, f z = dirichletEnergy w U := by
      rw [hf, lintegral_indicator hUopen.measurableSet]; rfl
    have hFmeas : ∀ n, Measurable (F n) := by
      intro n
      exact (((measurable_fderiv ℝ (wn n)).nnnorm).pow_const 2).coe_nnreal_ennreal.indicator
        hUopen.measurableSet
    have hfd_w : ∀ᵐ z : ℂ, z ∈ U → fderiv ℝ w z = fderiv ℝ u z + fderiv ℝ φ z := by
      filter_upwards [hφaediff] with z hzd hzU
      have hwd : HasFDerivAt w (fderiv ℝ u z + fderiv ℝ φ z) z := by
        refine (((hudiffU z hzU).hasFDerivAt).add (hzd hzU).hasFDerivAt).congr_of_eventuallyEq ?_
        filter_upwards with y; simp only [Pi.add_apply, hw_eq y]
      exact hwd.fderiv
    have hfd_wn : ∀ n, ∀ᵐ z : ℂ, z ∈ U →
        fderiv ℝ (wn n) z = fderiv ℝ u z + fderiv ℝ (g n) z := by
      intro n
      filter_upwards [hφaediff] with z hφd hzU
      have hgd : DifferentiableAt ℝ (g n) z := (hχdiff n z).mul (hφd hzU)
      have hwd : HasFDerivAt (wn n) (fderiv ℝ u z + fderiv ℝ (g n) z) z := by
        refine (((hudiffU z hzU).hasFDerivAt).add hgd.hasFDerivAt).congr_of_eventuallyEq ?_
        filter_upwards with y; simp only [Pi.add_apply, hwn]
      exact hwd.fderiv
    -- **Domination `‖∇(g n) z‖ ≤ ‖∇φ z‖ + 2·Bc·|φ z|/d z` a.e. on `U`** (product rule + shell).
    have hgfd_bound : ∀ n, ∀ᵐ z : ℂ, z ∈ U →
        ‖fderiv ℝ (g n) z‖ ≤ ‖fderiv ℝ φ z‖ + 2 * Bc * |φ z| / d z := by
      intro n
      filter_upwards [hφaediff] with z hφd hzU
      have hdz : 0 < d z := (hdU z).mp hzU
      have hgeq : g n = (χ n) * φ := by funext y; simp only [hg, Pi.mul_apply]
      have hgfd : fderiv ℝ (g n) z = χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z := by
        rw [hgeq, fderiv_mul (𝕜 := ℝ) (c := χ n) (d := φ) (hχdiff n z) (hφd hzU)]
      rw [hgfd]
      have hshellbd : |φ z| * ‖fderiv ℝ (χ n) z‖ ≤ 2 * Bc * |φ z| / d z := by
        by_cases hnab : fderiv ℝ (χ n) z = 0
        · rw [hnab, norm_zero, mul_zero]; positivity
        · have hd2 : d z < 2/((n:ℝ)+1) := hχfd_supp n z hnab
          have hle : Bc * ((n:ℝ)+1) ≤ 2 * Bc / d z := by
            rw [le_div_iff₀ hdz]
            have : ((n:ℝ)+1) * d z ≤ 2 := by rw [lt_div_iff₀ (hn1 n)] at hd2; nlinarith
            nlinarith [this, hBcnn]
          calc |φ z| * ‖fderiv ℝ (χ n) z‖ ≤ |φ z| * (4 * (Dst:ℝ) * ((n:ℝ)+1)) :=
                mul_le_mul_of_nonneg_left (hχfd_le n z) (abs_nonneg _)
            _ = |φ z| * (Bc * ((n:ℝ)+1)) := by rw [hBc]
            _ ≤ |φ z| * (2 * Bc / d z) := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
            _ = 2 * Bc * |φ z| / d z := by ring
      calc ‖χ n z • fderiv ℝ φ z + φ z • fderiv ℝ (χ n) z‖
          ≤ ‖χ n z • fderiv ℝ φ z‖ + ‖φ z • fderiv ℝ (χ n) z‖ := norm_add_le _ _
        _ = |χ n z| * ‖fderiv ℝ φ z‖ + |φ z| * ‖fderiv ℝ (χ n) z‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ‖fderiv ℝ φ z‖ + 2 * Bc * |φ z| / d z := by
            gcongr
            · rw [abs_of_nonneg (hχ01 n z).1]; exact (hχ01 n z).2
        _ = ‖fderiv ℝ φ z‖ + 2 * Bc * |φ z| / d z := by ring
    -- **The domination `F n ≤ bound`** with `bound = 1_U·3(‖∇u‖²+‖∇φ‖²+(2Bc)²φ²/d²)`.
    set bound : ℂ → ℝ≥0∞ := U.indicator (fun z => 3 * ((‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
      + (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal ((2 * Bc) ^ 2 * φ z ^ 2 / d z ^ 2)))
      with hbound
    have hFbound : ∀ n, F n ≤ᵐ[volume] bound := by
      intro n
      filter_upwards [hgfd_bound n, hfd_wn n] with z hgfd hwnd
      rcases Classical.em (z ∈ U) with hzU | hzU
      · simp only [hF, hbound, Set.indicator_of_mem hzU]
        have hdz : 0 < d z := (hdU z).mp hzU
        have hnorm : ‖fderiv ℝ (wn n) z‖
            ≤ ‖fderiv ℝ u z‖ + (‖fderiv ℝ φ z‖ + 2 * Bc * |φ z| / d z) := by
          rw [hwnd hzU]
          calc ‖fderiv ℝ u z + fderiv ℝ (g n) z‖ ≤ ‖fderiv ℝ u z‖ + ‖fderiv ℝ (g n) z‖ :=
                norm_add_le _ _
            _ ≤ ‖fderiv ℝ u z‖ + (‖fderiv ℝ φ z‖ + 2 * Bc * |φ z| / d z) := by
                gcongr; exact hgfd hzU
        set a1 : ℝ≥0 := ‖fderiv ℝ u z‖₊ with ha1
        set b1 : ℝ≥0 := ‖fderiv ℝ φ z‖₊ with hb1
        set c1 : ℝ≥0 := Real.toNNReal (2 * Bc * |φ z| / d z) with hc1
        have hnn : ‖fderiv ℝ (wn n) z‖₊ ≤ a1 + b1 + c1 := by
          rw [← NNReal.coe_le_coe]
          push_cast [ha1, hb1, hc1,
            Real.coe_toNNReal _ (show (0:ℝ) ≤ 2 * Bc * |φ z|/d z by positivity)]
          linarith [hnorm]
        have hcsq : (‖fderiv ℝ (wn n) z‖₊) ^ 2 ≤ 3 * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) := by
          refine le_trans (pow_le_pow_left₀ (zero_le _) hnn 2) ?_
          rw [← NNReal.coe_le_coe]; push_cast
          nlinarith [sq_nonneg ((a1:ℝ)-b1), sq_nonneg ((b1:ℝ)-c1), sq_nonneg ((a1:ℝ)-c1)]
        have hc1sq : ((c1 : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((2 * Bc) ^ 2 * φ z ^ 2 / d z ^ 2) := by
          rw [hc1, show ((2 * Bc * |φ z| / d z).toNNReal : ℝ≥0∞)
              = ENNReal.ofReal (2 * Bc * |φ z| / d z) from rfl,
            ← ENNReal.ofReal_pow (by positivity)]
          congr 1
          rw [div_pow, mul_pow, mul_pow, sq_abs]
        calc (‖fderiv ℝ (wn n) z‖₊ : ℝ≥0∞) ^ 2
            = ((‖fderiv ℝ (wn n) z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_pow]
          _ ≤ ((3 * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hcsq
          _ = 3 * ((a1 : ℝ≥0∞) ^ 2 + (b1 : ℝ≥0∞) ^ 2 + (c1 : ℝ≥0∞) ^ 2) := by push_cast; ring
          _ = 3 * ((‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 + (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2
                + ENNReal.ofReal ((2 * Bc) ^ 2 * φ z ^ 2 / d z ^ 2)) := by rw [ha1, hb1, hc1sq]
      · simp only [hF, hbound, Set.indicator_of_notMem hzU, le_refl]
    -- **The bound is integrable.**
    have hu_int : ∫⁻ z in U, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := by
      have hle : ∫⁻ z in U, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
          ≤ ∫⁻ z in U, (2 * (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2) := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' hUopen.measurableSet]
        filter_upwards [hfd_w] with z hwd hzU
        have hnn : ‖fderiv ℝ u z‖₊ ≤ ‖fderiv ℝ w z‖₊ + ‖fderiv ℝ φ z‖₊ := by
          rw [← NNReal.coe_le_coe]; push_cast
          calc ‖fderiv ℝ u z‖ = ‖fderiv ℝ w z - fderiv ℝ φ z‖ := by rw [hwd hzU]; congr 1; abel
            _ ≤ ‖fderiv ℝ w z‖ + ‖fderiv ℝ φ z‖ := norm_sub_le _ _
        have hnn' : ‖fderiv ℝ u z‖ ≤ ‖fderiv ℝ w z‖ + ‖fderiv ℝ φ z‖ := by
          have := NNReal.coe_le_coe.mpr hnn; push_cast at this; exact this
        have hsq : ‖fderiv ℝ u z‖₊ ^ 2 ≤ 2 * ‖fderiv ℝ w z‖₊ ^ 2 + 2 * ‖fderiv ℝ φ z‖₊ ^ 2 := by
          rw [← NNReal.coe_le_coe]; push_cast
          nlinarith [sq_nonneg (‖fderiv ℝ w z‖ - ‖fderiv ℝ φ z‖), hnn',
            norm_nonneg (fderiv ℝ w z), norm_nonneg (fderiv ℝ φ z), norm_nonneg (fderiv ℝ u z)]
        calc (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
            = ((‖fderiv ℝ u z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_pow]
          _ ≤ ((2 * ‖fderiv ℝ w z‖₊ ^ 2 + 2 * ‖fderiv ℝ φ z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.coe_le_coe.mpr hsq
          _ = 2 * (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2 := by
              push_cast; ring
      refine ne_top_of_le_ne_top ?_ hle
      rw [lintegral_add_right _ (by fun_prop), lintegral_const_mul' _ _ (by simp),
        lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hfin.ne,
        ENNReal.mul_ne_top (by simp) hφW12⟩
    have hhardyC : ∫⁻ z in U, ENNReal.ofReal ((2 * Bc) ^ 2 * φ z ^ 2 / d z ^ 2) ≠ ⊤ := by
      have heq : ∫⁻ z in U, ENNReal.ofReal ((2 * Bc) ^ 2 * φ z ^ 2 / d z ^ 2)
          = ENNReal.ofReal ((2 * Bc) ^ 2) * ∫⁻ z in U, ENNReal.ofReal (φ z ^ 2 / d z ^ 2) := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        refine lintegral_congr fun z => ?_
        rw [show (2 * Bc) ^ 2 * φ z ^ 2 / d z ^ 2 = (2 * Bc) ^ 2 * (φ z ^ 2 / d z ^ 2) by ring,
          ENNReal.ofReal_mul (by positivity)]
      rw [heq]; exact ENNReal.mul_ne_top (by simp) hHardy
    have hmb : Measurable (fun z => (‖fderiv ℝ φ z‖₊ : ℝ≥0∞) ^ 2) :=
      ((measurable_fderiv ℝ φ).nnnorm.pow_const 2).coe_nnreal_ennreal
    have hmc : Measurable (fun z => ENNReal.ofReal ((2 * Bc) ^ 2 * φ z ^ 2 / d z ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        ((((hφcont'.measurable.pow_const 2).const_mul _)).div (hdcont.measurable.pow_const 2))
    have hboundint : ∫⁻ z, bound z ≠ ∞ := by
      rw [hbound, lintegral_indicator hUopen.measurableSet, lintegral_const_mul' _ _ (by simp),
        lintegral_add_right _ hmc, lintegral_add_right _ hmb]
      exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
        ⟨hu_int, hφW12⟩, hhardyC⟩)
    -- **Pointwise convergence `F n z → f z`** (eventually equal for each `z`).
    have hconv_pt : ∀ᵐ z : ℂ, Tendsto (fun n => F n z) atTop (𝓝 (f z)) := by
      filter_upwards with z
      rcases Classical.em (z ∈ U) with hzU | hzU
      · have hdz : 0 < d z := (hdU z).mp hzU
        have hev : ∀ᶠ n : ℕ in atTop, F n z = f z := by
          obtain ⟨N, hN⟩ := exists_nat_gt (2 / d z)
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have hdz2 : 2 / ((n:ℝ)+1) < d z := by
            have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            have hlt : 2 / d z < (n:ℝ)+1 := by linarith [hN, hNn]
            rw [div_lt_iff₀ hdz] at hlt; rw [div_lt_iff₀ (hn1 n)]; linarith
          have hfeq : wn n =ᶠ[𝓝 z] w := by
            have hopen : IsOpen {x : ℂ | 2 / ((n:ℝ)+1) < d x} := isOpen_lt continuous_const hdcont
            filter_upwards [hopen.mem_nhds (show z ∈ _ from hdz2)] with x hx
            have hx' : 2 / ((n:ℝ)+1) ≤ d x := le_of_lt hx
            simp only [hwn, hg, hχ1 n x hx', one_mul, ← hw_eq x]
          simp only [hF, hf, Set.indicator_of_mem hzU, hfeq.fderiv_eq]
        exact Tendsto.congr' (hev.mono (fun n h => h.symm)) tendsto_const_nhds
      · have hcst : ∀ n, F n z = f z := fun n => by
          simp only [hF, hf, Set.indicator_of_notMem hzU]
        simp only [hcst]; exact tendsto_const_nhds
    have hconv : Tendsto (fun n => dirichletEnergy (wn n) U) atTop (𝓝 (dirichletEnergy w U)) := by
      have := tendsto_lintegral_of_dominated_convergence bound hFmeas hFbound hboundint hconv_pt
      rw [hfint] at this
      simpa only [hFint] using this
    exact ge_of_tendsto hconv (Filter.Eventually.of_forall hstep1)

open Classical in
/-- **The modulus–energy lower bound for a bounded admissible density.** For a bounded measurable
density `ρ ≤ M` on the open bounded set `U` with harmonic potential `u`, the Dirichlet energy of `u`
is at most `∫ ρ²`. The competitor `w z = min (rhoDistance ρ E U z).toReal 1` inside `U` (and `u`
outside) shares the potential's boundary values, so the boundary-vanishing Hardy Dirichlet principle
`dirichletEnergy_le_of_hardy_boundaryVanishing` gives `dirichletEnergy u U ≤ dirichletEnergy w U`;
since `w` agrees with the truncated `ρ`-distance on the open `U`, its Dirichlet energy equals that
of `min (rhoDistance ρ E U ·).toReal 1`, which `dirichletEnergy_min_rhoDistance_le` bounds by
`∫ ρ²`.
The boundary/Hardy regularity of the competitor difference `w − u` (continuity, local Lipschitz
constants on compacts, finite squared-gradient integral, finite Hardy integral) is taken as a
hypothesis. -/
theorem dirichletEnergy_le_lintegral_sq_of_bounded_admissible {ρ : ℂ → ℝ≥0∞} {u : ℂ → ℝ}
    {E U : Set ℂ} {M : ℝ≥0}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hρmeas : Measurable ρ)
    (hρbdd : ∀ x, ρ x ≤ (M : ℝ≥0∞))
    (hcompcont : Continuous (fun z =>
        (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z))
    (hcomploc : ∀ K ⊆ U, IsCompact K → ∃ L : ℝ≥0, LipschitzOnWith L (fun z =>
        (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) K)
    (hcompW12 : ∫⁻ z in U, (‖fderiv ℝ (fun z =>
        (if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) z‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤)
    (hHardy : ∫⁻ z in U, ENNReal.ofReal
        (((if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z) - u z) ^ 2
          / (Metric.infDist z Uᶜ) ^ 2) ≠ ⊤) :
    dirichletEnergy u U ≤ ∫⁻ z, (ρ z) ^ 2 := by
  classical
  set w : ℂ → ℝ := fun z => if z ∈ U then min (rhoDistance ρ E U z).toReal 1 else u z with hw
  -- `w − u` vanishes off `U`: for `z ∉ U`, `w z = u z`.
  have hφ0 : ∀ z ∉ U, w z - u z = 0 := by
    intro z hz
    simp only [hw, if_neg hz, sub_self]
  -- The boundary-vanishing Hardy Dirichlet principle: `dirichletEnergy u U ≤ dirichletEnergy w U`.
  have hstep2 : dirichletEnergy u U ≤ dirichletEnergy w U :=
    dirichletEnergy_le_of_hardy_boundaryVanishing hUopen hUbdd hu hcomploc hcompcont hφ0
      hcompW12 hHardy
  -- On the open `U`, `w` agrees with the truncated `ρ`-distance, so the energies coincide.
  have hstep3 : dirichletEnergy w U
      = dirichletEnergy (fun z => min (rhoDistance ρ E U z).toReal 1) U := by
    unfold dirichletEnergy
    refine setLIntegral_congr_fun hUopen.measurableSet (fun z hz => ?_)
    have hev : w =ᶠ[𝓝 z] (fun z => min (rhoDistance ρ E U z).toReal 1) := by
      filter_upwards [hUopen.mem_nhds hz] with x hx
      simp only [hw, if_pos hx]
    rw [hev.fderiv_eq]
  -- Chain with the competitor energy bound `dirichletEnergy_min_rhoDistance_le`.
  calc dirichletEnergy u U ≤ dirichletEnergy w U := hstep2
    _ = dirichletEnergy (fun z => min (rhoDistance ρ E U z).toReal 1) U := hstep3
    _ ≤ ∫⁻ z, (ρ z) ^ 2 := dirichletEnergy_min_rhoDistance_le hUopen hρmeas hρbdd

end RiemannDynamics

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.ModulusEnergy
import RiemannDynamics.Analysis.Sobolev.WeakDeriv
import RiemannDynamics.Analysis.Sobolev.DifferenceQuotient
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The Dirichlet principle: harmonic functions minimize Dirichlet energy

The harmonic potential of a ring domain minimizes the Dirichlet energy among all functions with the
same boundary values — this is the extremal (lower-bound) half of the modulus–energy identity
`curveModulus (connectingCurveFamily E F U) = dirichletEnergy u U`.

This file provides the **compact-support core** of the Dirichlet principle: if `w` differs from a
harmonic `u` by a function compactly supported inside `U`, then `dirichletEnergy u U ≤
dirichletEnergy w U`. The proof is Green's first identity for the compactly supported perturbation
`φ = w − u`: `∫_U ⟪∇u, ∇φ⟫ = −∫_U φ · Δu = 0` (the boundary term vanishes by compact support,
`Δu = 0` by harmonicity), whence `D(w) = D(u) + D(w − u) ≥ D(u)`.

The general Dirichlet principle for competitors that merely vanish on `∂U` (not compactly supported)
requires extending this by density of compactly supported functions in `H¹₀(U)` — the next brick of
the reciprocity layer.

## Main statements

* `dirichletEnergy_le_of_compactSupport` — the compact-support Dirichlet principle.

## References

* T. Ransford, *Potential Theory in the Complex Plane*, Ch. 4 (the Dirichlet principle).
-/

open MeasureTheory Filter Metric Topology
open scoped ENNReal NNReal Topology Manifold ContDiff

namespace RiemannDynamics

/-- **The Dirichlet principle (compact-support core).** If `u` is harmonic on the open set `U` and
`w` differs from `u` by a function compactly supported inside `U` (and `w` is `C¹` on `U`), then the
harmonic `u` has the smaller Dirichlet energy: `dirichletEnergy u U ≤ dirichletEnergy w U`. Green's
first identity gives `∫_U ⟪∇u, ∇(w − u)⟫ = 0` (compact support kills the boundary term, `Δu = 0`
kills the interior term), so `D(w) = D(u) + D(w − u) ≥ D(u)`. -/
theorem dirichletEnergy_le_of_compactSupport {u w : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hw : ContDiffOn ℝ 1 w U)
    (hcs : HasCompactSupport (fun z => w z - u z))
    (hsub : tsupport (fun z => w z - u z) ⊆ U) :
    dirichletEnergy u U ≤ dirichletEnergy w U := by
  classical
  -- The compactly supported perturbation `φ = w − u`, and the compact set `K = tsupport φ ⊆ U`.
  set φ : ℂ → ℝ := fun z => w z - u z with hφ
  set K : Set ℂ := tsupport φ with hK
  have hKc : IsCompact K := hcs
  have hKU : K ⊆ U := hsub
  -- Basic regularity: `u` is `C²` on `U`, `φ` is `C¹` on `U`, and `φ` is differentiable everywhere.
  have hu2 : ContDiffOn ℝ 2 u U := hu.contDiffOn
  have hφU : ContDiffOn ℝ 1 φ U := hw.sub (hu2.of_le (by norm_num))
  have hwdiffU : ∀ z ∈ U, DifferentiableAt ℝ w z :=
    fun z hz => (hw.differentiableOn one_ne_zero).differentiableAt (hUopen.mem_nhds hz)
  have hudiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
    fun z hz => (hu2.differentiableOn (by norm_num)).differentiableAt (hUopen.mem_nhds hz)
  have hφdiff : ∀ z, DifferentiableAt ℝ φ z := by
    intro z
    by_cases hz : z ∈ K
    · exact (hφU.differentiableOn one_ne_zero).differentiableAt (hUopen.mem_nhds (hKU hz))
    · have hopen : IsOpen Kᶜ := (isClosed_tsupport φ).isOpen_compl
      have heq : φ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hz] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      exact (differentiableAt_const 0).congr_of_eventuallyEq heq
  have hφdiff' : Differentiable ℝ φ := fun z => hφdiff z
  have hcont_φ : Continuous φ := hφdiff'.continuous
  -- `fderiv ℝ u` is `C¹` on `U`.
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu2.fderiv_of_isOpen hUopen (by norm_num)
  -- A reusable integrability fact: continuous on `U` with support in `K` ⇒ integrable on `ℂ`.
  have integ_of : ∀ g : ℂ → ℝ, ContinuousOn g U → Function.support g ⊆ K →
      Integrable g volume := by
    intro g hgU hgsupp
    exact (integrableOn_iff_integrable_of_support_subset hgsupp).mp
      ((hgU.mono hKU).integrableOn_compact hKc)
  -- **Green's first identity, per direction.** For every real direction `v`,
  -- `∫ (∂ᵥu)(∂ᵥφ) = − ∫ (∂ᵥ∂ᵥu) φ` (compact-support integration by parts, no boundary term).
  have ibp : ∀ v : ℂ, ∫ z, (fderiv ℝ u z v) * (fderiv ℝ φ z v)
      = - ∫ z, (fderiv ℝ (fun y => fderiv ℝ u y v) z v) * φ z := by
    intro v
    set a : ℂ → ℝ := fun z => fderiv ℝ u z v with ha
    have haU : ContDiffOn ℝ 1 a U := hfd1.clm_apply (contDiffOn_const (c := v))
    have hacont : ContinuousOn a U := haU.continuousOn
    have hfdacont : ContinuousOn (fderiv ℝ a) U :=
      haU.continuousOn_fderiv_of_isOpen hUopen le_rfl
    have hadiffU : ∀ z ∈ U, DifferentiableAt ℝ a z :=
      fun z hz => (haU.differentiableOn one_ne_zero).differentiableAt (hUopen.mem_nhds hz)
    have hda : ∀ x ∈ tsupport φ, DifferentiableAt ℝ a x := fun x hx => hadiffU x (hKU hx)
    have hdφ : ∀ x ∈ tsupport a, DifferentiableAt ℝ φ x := fun x _ => hφdiff x
    have hcont_fdav_on : ContinuousOn (fun x => (fderiv ℝ a x) v) U :=
      hfdacont.clm_apply continuousOn_const
    have hcont_dφv_on : ContinuousOn (fun z => (fderiv ℝ φ z) v) U :=
      (hφU.continuousOn_fderiv_of_isOpen hUopen le_rfl).clm_apply continuousOn_const
    have hsupp_dφ : Function.support (fun z => fderiv ℝ φ z v) ⊆ K :=
      (subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v)
    have hsupp_φ : Function.support φ ⊆ K := subset_tsupport φ
    have h1 : Integrable (fun x => (fderiv ℝ a x) v * φ x) volume :=
      integ_of _ (hcont_fdav_on.mul hcont_φ.continuousOn)
        ((Function.support_mul_subset_right _ _).trans hsupp_φ)
    have h2 : Integrable (fun x => a x * (fderiv ℝ φ x) v) volume :=
      integ_of _ (hacont.mul hcont_dφv_on)
        ((Function.support_mul_subset_right _ _).trans hsupp_dφ)
    have h3 : Integrable (fun x => a x * φ x) volume :=
      integ_of _ (hacont.mul hcont_φ.continuousOn)
        ((Function.support_mul_subset_right _ _).trans hsupp_φ)
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := a) (g := φ) (v := v)
      h1 h2 h3 hda hdφ
  -- **The pointwise Laplacian identity.** For every `z`, `(∂₁∂₁u + ∂ᵢ∂ᵢu)(z)·φ(z) = 0`:
  -- on `K` because `Δu = 0` by harmonicity, off `K` because `φ = 0`.
  have hlap0 : ∀ z, (fderiv ℝ (fun y => fderiv ℝ u y 1) z 1
      + fderiv ℝ (fun y => fderiv ℝ u y Complex.I) z Complex.I) * φ z = 0 := by
    intro z
    by_cases hz : z ∈ K
    · have hzU : z ∈ U := hKU hz
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
  -- Continuity of the first derivatives on `U`.
  have hucont1 : ContinuousOn (fderiv ℝ u) U := hfd1.continuousOn
  have hwcont1 : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hUopen le_rfl
  have hφcont1 : ContinuousOn (fderiv ℝ φ) U := hφU.continuousOn_fderiv_of_isOpen hUopen le_rfl
  -- **The cross term integrates to zero.** `∫ (∇u · ∇φ) = 0` (Green + `Δu = 0`).
  set cross : ℂ → ℝ := fun z => (fderiv ℝ u z 1) * (fderiv ℝ φ z 1)
    + (fderiv ℝ u z Complex.I) * (fderiv ℝ φ z Complex.I) with hcross
  -- Integrability of the two second-derivative-times-`φ` integrands (for combining the IBP RHS).
  have hI : ∀ v : ℂ,
      Integrable (fun z => (fderiv ℝ (fun y => fderiv ℝ u y v) z v) * φ z) volume := by
    intro v
    have haU : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z v) U :=
      hfd1.clm_apply (contDiffOn_const (c := v))
    have hcont_fdav_on : ContinuousOn (fun z => (fderiv ℝ (fun y => fderiv ℝ u y v) z) v) U :=
      (haU.continuousOn_fderiv_of_isOpen hUopen le_rfl).clm_apply continuousOn_const
    exact integ_of _ (hcont_fdav_on.mul hcont_φ.continuousOn)
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport φ))
  have hcross0 : ∫ z, cross z = 0 := by
    have hIab : ∀ v : ℂ, Integrable (fun z => (fderiv ℝ u z v) * (fderiv ℝ φ z v)) volume := by
      intro v
      have hacont : ContinuousOn (fun z => (fderiv ℝ u z) v) U :=
        hucont1.clm_apply continuousOn_const
      have hbcont : ContinuousOn (fun z => (fderiv ℝ φ z) v) U :=
        hφcont1.clm_apply continuousOn_const
      exact integ_of _ (hacont.mul hbcont)
        ((Function.support_mul_subset_right _ _).trans
          ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v)))
    rw [hcross, integral_add (hIab 1) (hIab Complex.I), ibp 1, ibp Complex.I, ← neg_add,
      ← integral_add (hI 1) (hI Complex.I)]
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
  -- `fderiv w = fderiv u` off `K` (there `w = u` locally, since `φ = 0`).
  have hfdeq : ∀ z ∈ U \ K, fderiv ℝ w z = fderiv ℝ u z := by
    intro z hz
    have hzc : z ∈ Kᶜ := hz.2
    have hopen : IsOpen Kᶜ := (isClosed_tsupport φ).isOpen_compl
    have heq : w =ᶠ[𝓝 z] u := by
      filter_upwards [hopen.mem_nhds hzc] with y hy
      have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp only [hφ] at hφy; linarith [hφy]
    exact heq.fderiv_eq
  -- `fderiv w = fderiv u + fderiv φ` on `U`.
  have hfdadd : ∀ z ∈ U, fderiv ℝ w z = fderiv ℝ u z + fderiv ℝ φ z := by
    intro z hz
    have hw' : HasFDerivAt w (fderiv ℝ u z + fderiv ℝ φ z) z := by
      refine (((hudiffU z hz).hasFDerivAt).add ((hφdiff z).hasFDerivAt)).congr_of_eventuallyEq ?_
      filter_upwards with y; simp only [Pi.add_apply, hφ]; ring
    exact hw'.fderiv
  have hKmeas : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  -- **The `K`-part energy inequality.** `∫⁻_K ‖∇u‖² ≤ ∫⁻_K ‖∇w‖²` via the real expansion.
  have hKpart : ∫⁻ z in K, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ z in K, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 := by
    have hint_u : IntegrableOn (fun z => ‖fderiv ℝ u z‖ ^ 2) K volume :=
      ((hucont1.norm.pow 2).mono hKU).integrableOn_compact hKc
    have hint_w : IntegrableOn (fun z => ‖fderiv ℝ w z‖ ^ 2) K volume :=
      ((hwcont1.norm.pow 2).mono hKU).integrableOn_compact hKc
    have conv_u : ∫⁻ z in K, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal (∫ z in K, ‖fderiv ℝ u z‖ ^ 2) := by
      have hi : Integrable (fun z => ((‖fderiv ℝ u z‖₊ ^ 2 : ℝ≥0) : ℝ)) (volume.restrict K) := by
        simpa [NNReal.coe_pow, coe_nnnorm] using hint_u
      simp_rw [← ENNReal.coe_pow]
      rw [lintegral_coe_eq_integral (fun z => ‖fderiv ℝ u z‖₊ ^ 2) hi]
      simp [NNReal.coe_pow, coe_nnnorm]
    have conv_w : ∫⁻ z in K, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal (∫ z in K, ‖fderiv ℝ w z‖ ^ 2) := by
      have hi : Integrable (fun z => ((‖fderiv ℝ w z‖₊ ^ 2 : ℝ≥0) : ℝ)) (volume.restrict K) := by
        simpa [NNReal.coe_pow, coe_nnnorm] using hint_w
      simp_rw [← ENNReal.coe_pow]
      rw [lintegral_coe_eq_integral (fun z => ‖fderiv ℝ w z‖₊ ^ 2) hi]
      simp [NNReal.coe_pow, coe_nnnorm]
    rw [conv_u, conv_w]
    apply ENNReal.ofReal_le_ofReal
    have hexp : ∀ z ∈ U, ‖fderiv ℝ w z‖ ^ 2
        = ‖fderiv ℝ u z‖ ^ 2 + (2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) := by
      intro z hz
      rw [normsq_dual (fderiv ℝ w z), normsq_dual (fderiv ℝ u z), normsq_dual (fderiv ℝ φ z),
        hfdadd z hz]
      simp only [ContinuousLinearMap.add_apply, hcross]; ring
    have hcont_cross : ContinuousOn cross U := by
      have h1 : ContinuousOn (fun z => (fderiv ℝ u z) 1) U := hucont1.clm_apply continuousOn_const
      have h2 : ContinuousOn (fun z => (fderiv ℝ φ z) 1) U := hφcont1.clm_apply continuousOn_const
      have h3 : ContinuousOn (fun z => (fderiv ℝ u z) Complex.I) U :=
        hucont1.clm_apply continuousOn_const
      have h4 : ContinuousOn (fun z => (fderiv ℝ φ z) Complex.I) U :=
        hφcont1.clm_apply continuousOn_const
      exact (h1.mul h2).add (h3.mul h4)
    have hint_cross : IntegrableOn cross K volume :=
      (hcont_cross.mono hKU).integrableOn_compact hKc
    have hint_φ2 : IntegrableOn (fun z => ‖fderiv ℝ φ z‖ ^ 2) K volume :=
      (((hφcont1.norm.pow 2).mono hKU)).integrableOn_compact hKc
    have hint_extra : IntegrableOn (fun z => 2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) K volume :=
      (hint_cross.const_mul 2).add hint_φ2
    have hstep : ∫ z in K, ‖fderiv ℝ w z‖ ^ 2
        = (∫ z in K, ‖fderiv ℝ u z‖ ^ 2) + ∫ z in K, (2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) := by
      rw [← integral_add hint_u hint_extra]
      exact setIntegral_congr_fun hKmeas (fun z hz => hexp z (hKU hz))
    rw [hstep]
    have hcrossK : ∫ z in K, cross z = 0 := by
      rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
      · exact hcross0
      · filter_upwards with z hz
        have hopen : IsOpen Kᶜ := (isClosed_tsupport φ).isOpen_compl
        have hfd0 : (fderiv ℝ φ z) = 0 := by
          have hφloc : φ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
            filter_upwards [hopen.mem_nhds (show z ∈ Kᶜ from hz)] with y hy
            exact image_eq_zero_of_notMem_tsupport hy
          rw [hφloc.fderiv_eq]; simp
        simp only [hcross, hfd0]; simp
    have hextra_nonneg : 0 ≤ ∫ z in K, (2 * cross z + ‖fderiv ℝ φ z‖ ^ 2) := by
      rw [integral_add (hint_cross.const_mul 2) hint_φ2, integral_const_mul, hcrossK]
      simp only [mul_zero, zero_add]
      exact setIntegral_nonneg hKmeas (fun z _ => by positivity)
    linarith
  -- Split each energy over `U = K ∪ (U \ K)`; the `U \ K` parts agree, leaving the `K`-part.
  have hsplit : ∀ f : ℂ → ℝ, dirichletEnergy f U
      = (∫⁻ z in K, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
        + ∫⁻ z in U \ K, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2 := by
    intro f
    unfold dirichletEnergy
    rw [← lintegral_inter_add_diff (B := K) _ U hKmeas, Set.inter_eq_self_of_subset_right hKU]
  rw [hsplit u, hsplit w]
  have hUKeq : ∫⁻ z in U \ K, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z in U \ K, (‖fderiv ℝ w z‖₊ : ℝ≥0∞) ^ 2 := by
    apply setLIntegral_congr_fun (hUopen.measurableSet.diff hKmeas)
    intro z hz; simp only [hfdeq z hz]
  rw [hUKeq]
  gcongr

/-- **The Dirichlet principle by energy approximation.** If `u` is harmonic on `U` and a sequence of
competitors `wₙ`, each differing from `u` by a function compactly supported inside `U`, has
Dirichlet energies converging to `dirichletEnergy w U`, then
`dirichletEnergy u U ≤ dirichletEnergy w U`. Each `wₙ` satisfies the compact-support principle, and
the bound passes to the limit — extending the principle to any competitor `w` approximable in energy
by compact-support perturbations of `u` (e.g. members of `H¹₀(U) + u`). -/
theorem dirichletEnergy_le_of_tendsto {u w : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) {wn : ℕ → ℂ → ℝ}
    (hwn_diff : ∀ n, ContDiffOn ℝ 1 (wn n) U)
    (hwn_cs : ∀ n, HasCompactSupport (fun z => wn n z - u z))
    (hwn_sub : ∀ n, tsupport (fun z => wn n z - u z) ⊆ U)
    (hconv : Tendsto (fun n => dirichletEnergy (wn n) U) atTop (𝓝 (dirichletEnergy w U))) :
    dirichletEnergy u U ≤ dirichletEnergy w U :=
  ge_of_tendsto hconv (Filter.Eventually.of_forall fun n =>
    dirichletEnergy_le_of_compactSupport hUopen hu (hwn_diff n) (hwn_cs n) (hwn_sub n))

/-- **The Dirichlet principle for a Lipschitz compact-support perturbation.** The `C¹`-competitor
hypothesis of `dirichletEnergy_le_of_compactSupport` can be relaxed to a Lipschitz one: if `u` is
harmonic on `U` and `w − u` is Lipschitz and compactly supported inside `U`, then still
`dirichletEnergy u U ≤ dirichletEnergy w U`. The orthogonality `∫_U ⟪∇u, ∇(w − u)⟫ = −∫_U (w−u)·Δu
= 0` holds with `w − u` merely Lipschitz — its a.e. (weak) derivative pairs against the smooth `∇u`
by compact-support integration by parts — and `Δu = 0`; then `D(w) = D(u) + D(w − u) ≥ D(u)`. This
is the form consumed by the boundary-vanishing (`H¹₀`) competitors built from the eikonal distance,
which are Lipschitz but not `C¹`. -/
theorem dirichletEnergy_le_of_compactSupport_lipschitz {u w : ℂ → ℝ} {U : Set ℂ} {K : ℝ≥0}
    (hUopen : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hwlip : LipschitzWith K (fun z => w z - u z))
    (hcs : HasCompactSupport (fun z => w z - u z))
    (hsub : tsupport (fun z => w z - u z) ⊆ U) :
    dirichletEnergy u U ≤ dirichletEnergy w U := by
  classical
  -- The compactly supported Lipschitz perturbation `φ = w − u`, and the compact `Kc = tsupport φ`.
  set φ : ℂ → ℝ := fun z => w z - u z with hφ
  set Kc : Set ℂ := tsupport φ with hKc
  have hKcc : IsCompact Kc := hcs
  have hKcU : Kc ⊆ U := hsub
  have hKcmeas : MeasurableSet Kc := (isClosed_tsupport φ).measurableSet
  -- `φ` is Lipschitz, continuous, a.e. differentiable (Rademacher), with `‖∇φ‖ ≤ K` everywhere.
  have hcont_φ : Continuous φ := hwlip.continuous
  have hφloc : LocallyIntegrable φ := hcont_φ.locallyIntegrable
  have hφ_aediff : ∀ᵐ z : ℂ, DifferentiableAt ℝ φ z := hwlip.ae_differentiableAt
  have hφfd_le : ∀ z, ‖fderiv ℝ φ z‖ ≤ (K : ℝ) := fun z => norm_fderiv_le_of_lipschitz ℝ hwlip
  -- `u` is real-analytic (harmonic ⟹ analytic), hence `C^∞`, on `U`.
  have huanal : ∀ z ∈ U, AnalyticAt ℝ u z := fun z hz => HarmonicAt.analyticAt (hu z hz)
  have hu_cd : ∀ z ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) u z := fun z hz => (huanal z hz).contDiffAt
  have hu2 : ContDiffOn ℝ 2 u U := hu.contDiffOn
  have hudiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
    fun z hz => (hu2.differentiableOn (by norm_num)).differentiableAt (hUopen.mem_nhds hz)
  -- `fderiv ℝ u` is `C¹` on `U`.
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu2.fderiv_of_isOpen hUopen (by norm_num)
  have hucont1 : ContinuousOn (fderiv ℝ u) U := hfd1.continuousOn
  -- The complex embedding `φℂ` of the real perturbation, and its Rademacher a.e. derivative.
  set φℂ : ℂ → ℂ := fun z => (φ z : ℂ) with hφℂ
  have hcont_φℂ : Continuous φℂ := Complex.continuous_ofReal.comp hcont_φ
  have hφℂloc : LocallyIntegrable φℂ := hcont_φℂ.locallyIntegrable
  -- Where `φ` is differentiable, `fderiv ℝ φℂ z v = (fderiv ℝ φ z v : ℂ)`.
  have hfdφℂ : ∀ z, DifferentiableAt ℝ φ z →
      ∀ v : ℂ, fderiv ℝ φℂ z v = ((fderiv ℝ φ z v : ℝ) : ℂ) := by
    intro z hz v
    have hcomp : HasFDerivAt φℂ (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z :=
      (Complex.ofRealCLM.hasFDerivAt).comp z hz.hasFDerivAt
    rw [hcomp.fderiv]; simp [Complex.ofRealCLM_apply]
  have hφℂ_aediff : ∀ᵐ z : ℂ, DifferentiableAt ℝ φℂ z := by
    filter_upwards [hφ_aediff] with z hz
    exact (Complex.ofRealCLM.hasFDerivAt).comp z hz.hasFDerivAt |>.differentiableAt
  -- **The weak directional derivative of `φℂ` via the difference-quotient bridge.**
  have hweak : ∀ v : ℂ, ‖v‖ = 1 →
      HasWeakDirDeriv v (fun w => (fderiv ℝ φℂ w) v) φℂ Set.univ := by
    intro v hv
    refine hasWeakDirDeriv_of_ae_differentiable_of_differenceQuotient_L2 hv hcont_φℂ hφℂloc
      hφℂ_aediff ?_
    intro Kd hKd
    refine ⟨ENNReal.ofReal ((K : ℝ) ^ 2) * volume Kd, ?_, ?_⟩
    · exact ENNReal.mul_lt_top (by simp) hKd.measure_lt_top
    · intro h hh0 hh1
      -- Each difference quotient of the `K`-Lipschitz `φℂ` is bounded by `K` in norm.
      have hquot : ∀ z, ‖(φℂ (z + h • v) - φℂ z) / (h : ℂ)‖ ≤ (K : ℝ) := by
        intro z
        have hnum : ‖φℂ (z + h • v) - φℂ z‖ ≤ (K : ℝ) * |h| := by
          have hlip : ‖φ (z + h • v) - φ z‖ ≤ (K : ℝ) * ‖(z + h • v) - z‖ := by
            simpa [φ, dist_eq_norm] using hwlip.dist_le_mul (z + h • v) z
          have hsub : ‖(z + h • v) - z‖ = |h| := by
            have hzz : (z + h • v) - z = h • v := by abel
            rw [hzz, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hv,
              mul_one]
          calc ‖φℂ (z + h • v) - φℂ z‖
              = ‖φ (z + h • v) - φ z‖ := by
                simp only [hφℂ, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            _ ≤ (K : ℝ) * ‖(z + h • v) - z‖ := hlip
            _ = (K : ℝ) * |h| := by rw [hsub]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          div_le_iff₀ (by positivity : (0:ℝ) < |h|)]
        linarith [hnum]
      have hpt : ∀ z, (‖(φℂ (z + h • v) - φℂ z) / (h : ℂ)‖₊ : ℝ≥0∞) ^ 2
          ≤ ENNReal.ofReal ((K : ℝ) ^ 2) := by
        intro z
        have h1 : (‖(φℂ (z + h • v) - φℂ z) / (h : ℂ)‖₊ : ℝ≥0∞)
            ≤ ENNReal.ofReal (K : ℝ) := by
          rw [ENNReal.le_ofReal_iff_toReal_le (by simp) (by positivity)]
          simpa using hquot z
        calc (‖(φℂ (z + h • v) - φℂ z) / (h : ℂ)‖₊ : ℝ≥0∞) ^ 2
            ≤ (ENNReal.ofReal (K : ℝ)) ^ 2 := by gcongr
          _ = ENNReal.ofReal ((K : ℝ) ^ 2) := by
              rw [← ENNReal.ofReal_pow (by positivity)]
      calc ∫⁻ z in Kd, ‖(φℂ (z + h • v) - φℂ z) / (h : ℂ)‖₊ ^ 2
          ≤ ∫⁻ _ in Kd, ENNReal.ofReal ((K : ℝ) ^ 2) := lintegral_mono hpt
        _ = ENNReal.ofReal ((K : ℝ) ^ 2) * volume Kd := by
            rw [setLIntegral_const]
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
  -- **Green's first identity, per direction (Lipschitz form).**
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
    -- The weak identity for `φℂ` in direction `v`, tested with `ψ`.
    have hW := hweak v hv ψ hψ_cd hψ_cs hψ_tsupp
    -- Turn the two `ℂ`-integrals into `ofReal` of real integrals.
    -- LHS integrand: `(fderiv ℝ ψ z v) • φℂ z = ((fderiv ℝ ψ z v * φ z : ℝ) : ℂ)`.
    have hLHS : (∫ z, ((fderiv ℝ ψ z) v) • φℂ z)
        = ((∫ z, (fderiv ℝ ψ z v) * φ z : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with z
      simp only [hφℂ, Complex.real_smul, Complex.ofReal_mul]
    -- RHS integrand: `ψ z • (fderiv ℝ φℂ z v) = ((ψ z * fderiv ℝ φ z v : ℝ) : ℂ)` a.e.
    have hRHS : (∫ z, ψ z • (fderiv ℝ φℂ z v))
        = ((∫ z, ψ z * (fderiv ℝ φ z v) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [hφ_aediff] with z hz
      rw [hfdφℂ z hz v]
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
  -- Continuity of `∇u`, `∇w` on `U` (`∇w = ∇u` on `U \ Kc`).
  have hucont1' : ContinuousOn (fderiv ℝ u) U := hucont1
  -- `fderiv ℝ φ` is measurable and everywhere norm-bounded by `K`.
  have hφfd_meas : Measurable (fderiv ℝ φ) := measurable_fderiv ℝ φ
  have hφfd_asm : AEStronglyMeasurable (fderiv ℝ φ) volume := hφfd_meas.aestronglyMeasurable
  -- **The cross term** `cross = ⟪∇u, ∇φ⟫` in the `{1, I}` basis, and its integral is `0`.
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
  -- `‖fderiv ℝ φ z v‖ ≤ K` for a unit direction `v` (pointwise, everywhere).
  have hφfdv_le : ∀ v : ℂ, ‖v‖ = 1 → ∀ z, |fderiv ℝ φ z v| ≤ (K : ℝ) := by
    intro v hv z
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ φ z v‖ ≤ ‖fderiv ℝ φ z‖ * ‖v‖ := (fderiv ℝ φ z).le_opNorm v
      _ = ‖fderiv ℝ φ z‖ := by rw [hv, mul_one]
      _ ≤ (K : ℝ) := hφfd_le z
  -- Integrability of `(∂ᵥu)·(∂ᵥφ)`: supported in `Kc`, `AEStronglyMeasurable`, bounded by `C·K`.
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
    have hbdd : ∀ᵐ z ∂(volume.restrict Kc), ‖(fderiv ℝ u z v) * (fderiv ℝ φ z v)‖
        ≤ C * (K : ℝ) := by
      refine ae_restrict_of_forall_mem hKcmeas (fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |fderiv ℝ u z v| ≤ C := by rw [← Real.norm_eq_abs]; exact hC z hz
      have h2 : |fderiv ℝ φ z v| ≤ (K : ℝ) := hφfdv_le v hv z
      have hCn : 0 ≤ C := le_trans (abs_nonneg _) h1
      exact mul_le_mul h1 h2 (abs_nonneg _) hCn
    have hasm : AEStronglyMeasurable
        (fun z => (fderiv ℝ u z v) * (fderiv ℝ φ z v)) volume := by
      have hm1 : Measurable (fun z => fderiv ℝ u z v) := measurable_fderiv_apply_const ℝ u v
      have hm2 : Measurable (fun z => fderiv ℝ φ z v) := measurable_fderiv_apply_const ℝ φ v
      exact (hm1.mul hm2).aestronglyMeasurable
    exact Measure.integrableOn_of_bounded hKcc.measure_lt_top.ne hasm hbdd
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
  -- `fderiv ℝ u`, `fderiv ℝ w` are norm-bounded on `Kc` (`u` continuous, `w` via `≤ ‖∇u‖ + K`).
  have hwcont1 : ContinuousOn (fderiv ℝ u) U := hucont1
  have hu_int : IntegrableOn (fun z => ‖fderiv ℝ u z‖ ^ 2) Kc volume :=
    ((hucont1.norm.pow 2).mono hKcU).integrableOn_compact hKcc
  -- `‖fderiv ℝ w z‖² ` is integrable on `Kc`: measurable and a.e.-bounded by `(‖∇u‖ + K)²`.
  -- `fderiv w = fderiv u + fderiv φ` a.e. on `volume.restrict Kc`.
  have hfdadd_res : ∀ᵐ z ∂(volume.restrict Kc),
      fderiv ℝ w z = fderiv ℝ u z + fderiv ℝ φ z := by
    rw [ae_restrict_iff' hKcmeas]
    filter_upwards [hfdadd_ae] with z hz hzKc
    exact hz (hKcU hzKc)
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hw_int : IntegrableOn (fun z => ‖fderiv ℝ w z‖ ^ 2) Kc volume := by
    obtain ⟨Cu, hCu⟩ := IsCompact.exists_bound_of_continuousOn (E := ℂ →L[ℝ] ℝ) hKcc
      (hucont1.mono hKcU)
    have hmeas : AEStronglyMeasurable (fun z => ‖fderiv ℝ w z‖ ^ 2) volume :=
      (((measurable_fderiv ℝ w).norm).pow_const 2).aestronglyMeasurable
    have hbdd : ∀ᵐ z ∂(volume.restrict Kc), ‖‖fderiv ℝ w z‖ ^ 2‖ ≤ (Cu + (K : ℝ)) ^ 2 := by
      have hmem : ∀ᵐ z ∂(volume.restrict Kc), z ∈ Kc := ae_restrict_mem hKcmeas
      filter_upwards [hfdadd_res, hmem] with z hz hzKc
      rw [hz]
      have hCn : 0 ≤ Cu := le_trans (norm_nonneg _) (hCu z hzKc)
      have h1 : ‖fderiv ℝ u z + fderiv ℝ φ z‖ ≤ Cu + (K : ℝ) :=
        le_trans (norm_add_le _ _) (add_le_add (hCu z hzKc) (hφfd_le z))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hnn : 0 ≤ ‖fderiv ℝ u z + fderiv ℝ φ z‖ := norm_nonneg _
      nlinarith [h1, hnn, hCn, hKnn]
    exact Measure.integrableOn_of_bounded hKcc.measure_lt_top.ne hmeas hbdd
  have hφ2_int : IntegrableOn (fun z => ‖fderiv ℝ φ z‖ ^ 2) Kc volume := by
    have hmeas : AEStronglyMeasurable (fun z => ‖fderiv ℝ φ z‖ ^ 2) volume :=
      (((measurable_fderiv ℝ φ).norm).pow_const 2).aestronglyMeasurable
    have hbdd : ∀ᵐ z ∂(volume.restrict Kc), ‖‖fderiv ℝ φ z‖ ^ 2‖ ≤ (K : ℝ) ^ 2 := by
      refine ae_restrict_of_forall_mem hKcmeas (fun z _ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hφfd_le z, norm_nonneg (fderiv ℝ φ z), hKnn]
    exact Measure.integrableOn_of_bounded hKcc.measure_lt_top.ne hmeas hbdd
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
    -- Real expansion `‖∇w‖² = ‖∇u‖² + (2·cross + ‖∇φ‖²)` a.e. on `Kc`.
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

end RiemannDynamics
